from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import os
import re
import sqlite3
import sys
import urllib.error
import urllib.request
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, AsyncIterator, Iterable, Sequence, Optional, Set

import aiohttp
import aiosqlite
import websockets
from aiohttp import web
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

# =============================================================================
# CONSTANTS
# =============================================================================

COINBASE_SENDER = "COINBASE"          # pseudo-sender of block-reward transactions
MAX_AMOUNT = 2**63 - 1                # upper bound on a single transfer
MAX_TXS_PER_BLOCK = 10_000            # sanity cap against oversized blocks
ZERO_HASH = "0" * 64                  # prev_hash of the genesis block
GENESIS_TIMESTAMP = datetime(2024, 1, 1, tzinfo=timezone.utc)

_HEX64 = re.compile(r"[0-9a-f]{64}")  # canonical lowercase 32-byte hex


def utc_now() -> datetime:
    """Current time as a timezone-aware UTC datetime."""
    return datetime.now(timezone.utc)


# =============================================================================
# CANONICAL JSON SERIALIZATION (bytes + datetime aware)
# =============================================================================
# Wire format:
#   bytes    -> {"__bytes__": "<lowercase hex>"}
#   datetime -> {"__datetime__": "<ISO-8601 UTC, microsecond precision>"}
# Output is canonical (sorted keys, no whitespace) so the same object always
# produces the same string. That property is what makes hashing/signing safe.


class SerializationError(ValueError):
    """Raised when incoming JSON is malformed or contains invalid typed values."""


class _Encoder(json.JSONEncoder):
    """JSON encoder that understands bytes, datetime and objects with to_dict()."""

    def default(self, o: Any) -> Any:
        if isinstance(o, (bytes, bytearray)):
            return {"__bytes__": bytes(o).hex()}
        if isinstance(o, datetime):
            if o.tzinfo is None or o.utcoffset() is None:
                raise ValueError("naive datetime cannot be serialized; use UTC-aware values")
            return {
                "__datetime__": o.astimezone(timezone.utc).isoformat(timespec="microseconds")
            }
        if hasattr(o, "to_dict"):
            return o.to_dict()
        return super().default(o)


def _reject_constant(name: str) -> Any:
    """json.loads hook: refuse NaN / Infinity / -Infinity."""
    raise ValueError(f"invalid JSON constant: {name}")


def _decode_hook(obj: dict[str, Any]) -> Any:
    """json.loads object_hook: turn tagged dicts back into bytes / datetime."""
    if len(obj) == 1:
        if "__bytes__" in obj:
            raw = obj["__bytes__"]
            if not isinstance(raw, str):
                raise ValueError("__bytes__ value must be a string")
            data = bytes.fromhex(raw)
            if data.hex() != raw:  # enforce canonical lowercase hex, no whitespace
                raise ValueError("non-canonical hex in __bytes__")
            return data
        if "__datetime__" in obj:
            raw = obj["__datetime__"]
            if not isinstance(raw, str):
                raise ValueError("__datetime__ value must be a string")
            dt = datetime.fromisoformat(raw)
            if dt.tzinfo is None or dt.utcoffset() is None:
                raise ValueError("__datetime__ must carry a timezone")
            return dt.astimezone(timezone.utc)
    return obj


def dumps(obj: Any) -> str:
    """Serialize ``obj`` to canonical JSON (sorted keys, compact separators)."""
    return json.dumps(
        obj,
        cls=_Encoder,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def loads(text: str | bytes) -> Any:
    """Parse JSON produced by :func:`dumps`. Raises :class:`SerializationError`."""
    try:
        return json.loads(text, object_hook=_decode_hook, parse_constant=_reject_constant)
    except (ValueError, TypeError, RecursionError) as exc:
        raise SerializationError(f"invalid JSON payload: {exc}") from exc


# =============================================================================
# CRYPTOGRAPHIC PRIMITIVES
# =============================================================================


def sha256(data: bytes) -> bytes:
    """SHA-256 digest as raw bytes."""
    return hashlib.sha256(data).digest()


def sha256_hex(data: bytes) -> str:
    """SHA-256 digest as a lowercase hex string."""
    return hashlib.sha256(data).hexdigest()


def is_valid_address(value: object) -> bool:
    """True if ``value`` is a canonical address: 64 lowercase hex chars.

    An address *is* the raw 32-byte Ed25519 public key in hex, so a receiver
    of a signature can verify it without any extra lookup.
    """
    return isinstance(value, str) and _HEX64.fullmatch(value) is not None


def verify_signature(public_key_hex: str, signature: bytes, message: bytes) -> bool:
    """Verify an Ed25519 signature. Never raises; returns False on any failure."""
    if not is_valid_address(public_key_hex) or not isinstance(signature, bytes):
        return False
    try:
        public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(public_key_hex))
        public_key.verify(signature, message)
        return True
    except (InvalidSignature, ValueError, TypeError):
        return False


class KeyPair:
    """An Ed25519 key pair. The public key (hex) doubles as the wallet address."""

    __slots__ = ("_private",)

    def __init__(self, private_key: Ed25519PrivateKey) -> None:
        self._private = private_key

    @classmethod
    def generate(cls) -> "KeyPair":
        """Create a fresh random key pair."""
        return cls(Ed25519PrivateKey.generate())

    @classmethod
    def from_private_hex(cls, value: str) -> "KeyPair":
        """Rebuild a key pair from a 32-byte private key in hex."""
        try:
            raw = bytes.fromhex(value.strip())
        except (ValueError, AttributeError) as exc:
            raise ValueError("private key must be a hex string") from exc
        if len(raw) != 32:
            raise ValueError("private key must be exactly 32 bytes")
        return cls(Ed25519PrivateKey.from_private_bytes(raw))

    @property
    def private_hex(self) -> str:
        """Raw private key as hex. Treat as a secret."""
        return self._private.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        ).hex()

    @property
    def address(self) -> str:
        """Public key as 64 hex chars (used as the account address)."""
        return (
            self._private.public_key()
            .public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw,
            )
            .hex()
        )

    def sign(self, message: bytes) -> bytes:
        """Sign ``message``; returns a 64-byte Ed25519 signature."""
        return self._private.sign(message)

    def save(self, path: str | os.PathLike[str]) -> None:
        """Write the wallet to ``path`` (owner-only permissions). Never overwrites."""
        payload = json.dumps({"address": self.address, "private_key": self.private_hex}, indent=2)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(payload)

    @classmethod
    def load(cls, path: str | os.PathLike[str]) -> "KeyPair":
        """Load a wallet file written by :meth:`save`."""
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        pair = cls.from_private_hex(data["private_key"])
        if "address" in data and data["address"] != pair.address:
            raise ValueError("wallet file is corrupt: address does not match private key")
        return pair

    def __repr__(self) -> str:  # never leak the private key
        return f"KeyPair(address={self.address})"


class MerkleTree:
    """Binary Merkle tree built from scratch over a list of byte strings.

    * Leaves and inner nodes use different prefixes (0x00 / 0x01) to prevent
      second-preimage attacks that pass an inner node off as a leaf.
    * An unpaired node at the end of a level is promoted unchanged rather than
      duplicated, so appending a copy of the last item always changes the root.
    * The root of an empty tree is ``sha256(b"")``.
    """

    def __init__(self, items: Sequence[bytes]) -> None:
        self._size = len(items)
        leaves = [self.hash_leaf(item) for item in items]
        self._levels: list[list[bytes]] = self._build(leaves)

    @staticmethod
    def hash_leaf(data: bytes) -> bytes:
        return sha256(b"\x00" + data)

    @staticmethod
    def hash_node(left: bytes, right: bytes) -> bytes:
        return sha256(b"\x01" + left + right)

    @classmethod
    def _build(cls, leaves: list[bytes]) -> list[list[bytes]]:
        if not leaves:
            return [[sha256(b"")]]
        levels = [leaves]
        current = leaves
        while len(current) > 1:
            nxt = [
                cls.hash_node(current[i], current[i + 1])
                for i in range(0, len(current) - 1, 2)
            ]
            if len(current) % 2 == 1:
                nxt.append(current[-1])  # promote the unpaired node
            levels.append(nxt)
            current = nxt
        return levels

    @property
    def root(self) -> bytes:
        return self._levels[-1][0]

    @property
    def root_hex(self) -> str:
        return self.root.hex()

    def get_proof(self, index: int) -> list[tuple[bytes, bool]]:
        """Inclusion proof for leaf ``index``: list of (sibling_hash, sibling_is_left)."""
        if not 0 <= index < self._size:
            raise IndexError("leaf index out of range")
        proof: list[tuple[bytes, bool]] = []
        i = index
        for level in self._levels[:-1]:
            if i % 2 == 1:
                proof.append((level[i - 1], True))
            elif i + 1 < len(level):
                proof.append((level[i + 1], False))
            # else: unpaired node, promoted without a sibling
            i //= 2
        return proof

    @classmethod
    def verify_proof(cls, item: bytes, proof: Sequence[tuple[bytes, bool]], root: bytes) -> bool:
        """Check that ``item`` is included under ``root`` according to ``proof``."""
        current = cls.hash_leaf(item)
        for sibling, sibling_is_left in proof:
            current = (
                cls.hash_node(sibling, current)
                if sibling_is_left
                else cls.hash_node(current, sibling)
            )
        return current == root


# =============================================================================
# CORE DATA MODELS
# =============================================================================


def _require(data: dict[str, Any], key: str) -> Any:
    try:
        return data[key]
    except KeyError:
        raise ValueError(f"missing field: {key!r}") from None


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_aware(value: object) -> bool:
    return isinstance(value, datetime) and value.tzinfo is not None and value.utcoffset() is not None


@dataclass
class Transaction:
    

    sender: str
    receiver: str
    amount: int
    signature: bytes = b""
    timestamp: datetime = field(default_factory=utc_now)
    nonce: int = 0

    # ---- construction -----------------------------------------------------

    @classmethod
    def coinbase(cls, receiver: str, amount: int, timestamp: datetime | None = None) -> "Transaction":
        """Create a block-reward transaction (kept uniform with the nonce field, always 0)."""
        return cls(COINBASE_SENDER, receiver, amount, b"", timestamp or utc_now(), nonce=0)

    @property
    def is_coinbase(self) -> bool:
        return self.sender == COINBASE_SENDER

    # ---- hashing & signing ------------------------------------------------

    def signing_payload(self) -> bytes:
        """Canonical bytes covered by the signature (everything except it)."""
        return dumps(
            {
                "sender": self.sender,
                "receiver": self.receiver,
                "amount": self.amount,
                "timestamp": self.timestamp,
                "nonce": self.nonce,
            }
        ).encode("utf-8")

    def tx_hash(self) -> bytes:
        """Transaction id (raw). Commits to the signature as well."""
        return sha256(dumps(self.to_dict()).encode("utf-8"))

    @property
    def tx_id(self) -> str:
        return self.tx_hash().hex()

    def sign(self, keypair: KeyPair) -> "Transaction":
        """Sign in place with ``keypair`` (must own ``sender``). Returns self."""
        if self.is_coinbase:
            raise ValueError("coinbase transactions are not signed")
        if keypair.address != self.sender:
            raise ValueError("keypair does not match transaction sender")
        self.signature = keypair.sign(self.signing_payload())
        return self

    # ---- validation -------------------------------------------------------

    def check_structure(self) -> None:
        """Validate field types and formats. Raises ValueError if malformed."""
        if not self.is_coinbase and not is_valid_address(self.sender):
            raise ValueError("invalid sender address")
        if not is_valid_address(self.receiver):
            raise ValueError("invalid receiver address")
        if not _is_int(self.amount) or not 0 < self.amount <= MAX_AMOUNT:
            raise ValueError("amount must be an integer in [1, MAX_AMOUNT]")
        if not _is_int(self.nonce) or self.nonce < 0:
            raise ValueError("nonce must be a non-negative integer")
        if self.is_coinbase and self.nonce != 0:
            raise ValueError("coinbase transaction must have nonce 0")
        if not isinstance(self.signature, bytes):
            raise ValueError("signature must be bytes")
        if self.is_coinbase:
            if self.signature:
                raise ValueError("coinbase transaction must not carry a signature")
        elif len(self.signature) != 64:
            raise ValueError("signature must be 64 bytes")
        if not _is_aware(self.timestamp):
            raise ValueError("timestamp must be timezone-aware")

    def verify(self) -> bool:
        """True if the transaction is well-formed and (unless coinbase) correctly signed."""
        try:
            self.check_structure()
        except ValueError:
            return False
        if self.is_coinbase:
            return True
        return verify_signature(self.sender, self.signature, self.signing_payload())

    # ---- (de)serialization ------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        return {
            "sender": self.sender,
            "receiver": self.receiver,
            "amount": self.amount,
            "signature": self.signature,
            "timestamp": self.timestamp,
            "nonce": self.nonce,
        }

    @classmethod
    def from_dict(cls, data: Any) -> "Transaction":
        """Build from decoded data. Raises ValueError on malformed input."""
        if not isinstance(data, dict):
            raise ValueError("transaction must be an object")
        tx = cls(
            sender=_require(data, "sender"),
            receiver=_require(data, "receiver"),
            amount=_require(data, "amount"),
            signature=_require(data, "signature"),
            timestamp=_require(data, "timestamp"),
            nonce=_require(data, "nonce"),
        )
        if not isinstance(tx.sender, str):
            raise ValueError("sender must be a string")
        tx.check_structure()
        return tx

    def to_json(self) -> str:
        return dumps(self.to_dict())

    @classmethod
    def from_json(cls, text: str | bytes) -> "Transaction":
        return cls.from_dict(loads(text))


@dataclass
class Block:
    """A block: header fields + transactions.

    ``hash`` is SHA-256 over the canonical header (index, timestamp, prev_hash,
    merkle_root, nonce, difficulty). ``difficulty`` is the number of leading
    hex zeros required of the hash; it lives in the header so every node can
    verify a block against the target it claims (and check that claim in the
    consensus stage).
    """

    index: int
    timestamp: datetime
    transactions: list[Transaction]
    prev_hash: str
    merkle_root: str
    nonce: int = 0
    hash: str = ""
    difficulty: int = 0

    # ---- hashing ----------------------------------------------------------

    @staticmethod
    def compute_merkle_root(transactions: Sequence[Transaction]) -> str:
        """Merkle root (hex) over the transaction ids."""
        return MerkleTree([tx.tx_hash() for tx in transactions]).root_hex

    def header_bytes(self) -> bytes:
        """Canonical bytes of the header, the input of the block hash."""
        return dumps(
            {
                "index": self.index,
                "timestamp": self.timestamp,
                "prev_hash": self.prev_hash,
                "merkle_root": self.merkle_root,
                "nonce": self.nonce,
                "difficulty": self.difficulty,
            }
        ).encode("utf-8")

    def compute_hash(self) -> str:
        return sha256_hex(self.header_bytes())

    def meets_difficulty(self) -> bool:
        """True if ``hash`` starts with ``difficulty`` zero hex digits."""
        return self.hash.startswith("0" * self.difficulty)

    # ---- construction -----------------------------------------------------

    @classmethod
    def create(
        cls,
        index: int,
        prev_hash: str,
        transactions: Sequence[Transaction],
        difficulty: int = 0,
        timestamp: datetime | None = None,
    ) -> "Block":
        """Build a block with merkle root and hash filled in (nonce = 0)."""
        txs = list(transactions)
        block = cls(
            index=index,
            timestamp=timestamp or utc_now(),
            transactions=txs,
            prev_hash=prev_hash,
            merkle_root=cls.compute_merkle_root(txs),
            nonce=0,
            hash="",
            difficulty=difficulty,
        )
        block.hash = block.compute_hash()
        return block

    @classmethod
    def genesis(cls) -> "Block":
        """The deterministic genesis block, identical on every node."""
        return cls.create(0, ZERO_HASH, [], difficulty=0, timestamp=GENESIS_TIMESTAMP)

    # ---- validation -------------------------------------------------------

    def check_structure(self) -> None:
        """Validate field types/formats (not hashes or signatures). Raises ValueError."""
        if not _is_int(self.index) or self.index < 0:
            raise ValueError("index must be a non-negative integer")
        if not _is_aware(self.timestamp):
            raise ValueError("timestamp must be timezone-aware")
        for name in ("prev_hash", "merkle_root", "hash"):
            if not is_valid_address(getattr(self, name)):
                raise ValueError(f"{name} must be 64 lowercase hex characters")
        if not _is_int(self.nonce) or self.nonce < 0:
            raise ValueError("nonce must be a non-negative integer")
        if not _is_int(self.difficulty) or not 0 <= self.difficulty <= 64:
            raise ValueError("difficulty must be an integer in [0, 64]")
        if not isinstance(self.transactions, list) or len(self.transactions) > MAX_TXS_PER_BLOCK:
            raise ValueError("invalid transaction list")
        seen: set[bytes] = set()
        for position, tx in enumerate(self.transactions):
            if not isinstance(tx, Transaction):
                raise ValueError("transactions must be Transaction objects")
            tx.check_structure()
            if tx.is_coinbase and position != 0:
                raise ValueError("coinbase transaction is only allowed first in a block")
            digest = tx.tx_hash()
            if digest in seen:
                raise ValueError("duplicate transaction in block")
            seen.add(digest)

    def verify_integrity(self, check_pow: bool = True) -> bool:
        """Self-contained checks: structure, merkle root, hash, PoW, tx signatures.

        Does NOT check chain context (prev_hash linkage, balances, expected
        difficulty); that is the job of the chain/ledger stages.
        """
        try:
            self.check_structure()
        except ValueError:
            return False
        if self.merkle_root != self.compute_merkle_root(self.transactions):
            return False
        if self.hash != self.compute_hash():
            return False
        if check_pow and not self.meets_difficulty():
            return False
        return all(tx.verify() for tx in self.transactions)

    # ---- (de)serialization ------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        return {
            "index": self.index,
            "timestamp": self.timestamp,
            "transactions": [tx.to_dict() for tx in self.transactions],
            "prev_hash": self.prev_hash,
            "merkle_root": self.merkle_root,
            "nonce": self.nonce,
            "hash": self.hash,
            "difficulty": self.difficulty,
        }

    @classmethod
    def from_dict(cls, data: Any) -> "Block":
        """Build from decoded data. Checks structure only; call verify_integrity() next."""
        if not isinstance(data, dict):
            raise ValueError("block must be an object")
        raw_txs = _require(data, "transactions")
        if not isinstance(raw_txs, list) or len(raw_txs) > MAX_TXS_PER_BLOCK:
            raise ValueError("invalid transaction list")
        block = cls(
            index=_require(data, "index"),
            timestamp=_require(data, "timestamp"),
            transactions=[Transaction.from_dict(item) for item in raw_txs],
            prev_hash=_require(data, "prev_hash"),
            merkle_root=_require(data, "merkle_root"),
            nonce=_require(data, "nonce"),
            hash=_require(data, "hash"),
            difficulty=_require(data, "difficulty"),
        )
        block.check_structure()
        return block

    def to_json(self) -> str:
        return dumps(self.to_dict())

    @classmethod
    def from_json(cls, text: str | bytes) -> "Block":
        return cls.from_dict(loads(text))


# =============================================================================
# SELF-TEST (STAGE 1)
# =============================================================================


def _expect_error(exc_type: type[BaseException], func: Any, *args: Any) -> None:
    try:
        func(*args)
    except exc_type:
        return
    raise AssertionError(f"{func.__name__}{args!r} should have raised {exc_type.__name__}")


def _self_test() -> None:
    import tempfile
    from datetime import timedelta

    # --- hashing -----------------------------------------------------------
    assert sha256_hex(b"abc") == (
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    )
    print("[ok] sha256 known-answer test")

    # --- keys & signatures ---------------------------------------------------
    alice, bob = KeyPair.generate(), KeyPair.generate()
    assert is_valid_address(alice.address) and alice.address != bob.address
    msg = b"hello chain"
    sig = alice.sign(msg)
    assert len(sig) == 64 and verify_signature(alice.address, sig, msg)
    assert not verify_signature(alice.address, sig, b"tampered")
    assert not verify_signature(bob.address, sig, msg)
    assert not verify_signature("zz", sig, msg) and not verify_signature(alice.address, b"", msg)
    assert "private" not in repr(alice).lower() and alice.private_hex not in repr(alice)
    with tempfile.TemporaryDirectory() as tmp:
        wallet_path = Path(tmp) / "wallet.json"
        alice.save(wallet_path)
        assert KeyPair.load(wallet_path).address == alice.address
        _expect_error(FileExistsError, alice.save, wallet_path)
    assert KeyPair.from_private_hex(alice.private_hex).address == alice.address
    print("[ok] Ed25519 keys, signing, wallet save/load")

    # --- merkle tree ---------------------------------------------------------
    assert MerkleTree([]).root == sha256(b"")
    for n in range(1, 18):
        items = [f"item-{i}".encode() for i in range(n)]
        tree = MerkleTree(items)
        for i, item in enumerate(items):
            proof = tree.get_proof(i)
            assert MerkleTree.verify_proof(item, proof, tree.root), (n, i)
            assert not MerkleTree.verify_proof(b"forged", proof, tree.root)
    a = MerkleTree([b"a", b"b", b"c"]).root
    assert a != MerkleTree([b"a", b"b", b"c", b"c"]).root       # no duplicate-leaf collision
    assert a != MerkleTree([b"a", b"b", b"d"]).root
    assert MerkleTree([b"a", b"b"]).root != MerkleTree([b"b", b"a"]).root
    _expect_error(IndexError, MerkleTree([b"a"]).get_proof, 1)
    print("[ok] Merkle tree roots and inclusion proofs (1..17 leaves)")

    # --- serialization ---------------------------------------------------------
    stamp = datetime(2026, 5, 17, 12, 30, 45, 123456, tzinfo=timezone(timedelta(hours=5, minutes=30)))
    wire = dumps({"b": b"\x00\xff", "t": stamp, "n": [1, 2]})
    back = loads(wire)
    assert back["b"] == b"\x00\xff" and back["t"] == stamp and back["n"] == [1, 2]
    assert dumps(loads(wire)) == wire                            # canonical & stable
    for bad in ('{"__bytes__":"zz"}', '{"__bytes__":"AB"}', '{"__bytes__":5}',
                '{"__datetime__":"2026-01-01T00:00:00"}', '{"__datetime__":"nope"}',
                "NaN", "{", ""):
        _expect_error(SerializationError, loads, bad)
    _expect_error(ValueError, dumps, datetime(2026, 1, 1))       # naive datetime refused
    print("[ok] JSON codec: bytes/datetime round-trip and malformed-input rejection")

    # --- transactions ------------------------------------------------------------
    tx = Transaction(alice.address, bob.address, 25).sign(alice)
    assert tx.verify() and len(tx.signature) == 64
    clone = Transaction.from_json(tx.to_json())
    assert clone == tx and clone.verify() and clone.tx_id == tx.tx_id
    forged = Transaction(alice.address, bob.address, 26, tx.signature, tx.timestamp)
    assert not forged.verify()                                   # amount tampering
    stolen = Transaction(alice.address, bob.address, 25, tx.signature, tx.timestamp + timedelta(seconds=1))
    assert not stolen.verify()                                   # timestamp tampering
    assert not Transaction(alice.address, bob.address, 25).verify()      # unsigned
    _expect_error(ValueError, Transaction(alice.address, bob.address, 1).sign, bob)
    for amount in (0, -5, 1.5, True, MAX_AMOUNT + 1, "9"):
        assert not Transaction(alice.address, bob.address, amount, tx.signature, tx.timestamp).verify()
    bad = tx.to_dict()
    bad["receiver"] = "not-an-address"
    _expect_error(ValueError, Transaction.from_dict, bad)
    _expect_error(ValueError, Transaction.from_dict, {"sender": alice.address})
    _expect_error(ValueError, Transaction.from_dict, [])
    reward = Transaction.coinbase(alice.address, 50)
    assert reward.verify() and Transaction.from_json(reward.to_json()) == reward
    assert reward.nonce == 0
    reward.signature = b"\x01" * 64
    assert not reward.verify()
    # nonce: signed, serialized, validated
    seven = Transaction(alice.address, bob.address, 25, nonce=7).sign(alice)
    assert seven.verify() and Transaction.from_json(seven.to_json()) == seven
    assert seven.tx_id != tx.tx_id and seven.signing_payload() != tx.signing_payload()
    renonced = Transaction(alice.address, bob.address, 25, seven.signature, seven.timestamp, nonce=8)
    assert not renonced.verify()                                 # nonce is covered by the signature
    for bad_nonce in (-1, 1.5, True, "0", None):
        assert not Transaction(alice.address, bob.address, 25, tx.signature, tx.timestamp, nonce=bad_nonce).verify()
    assert not Transaction(COINBASE_SENDER, alice.address, 50, nonce=1).verify()   # coinbase nonce must be 0
    no_nonce = tx.to_dict()
    del no_nonce["nonce"]
    _expect_error(ValueError, Transaction.from_dict, no_nonce)
    print("[ok] Transaction signing, verification, tamper detection, coinbase, nonce")

    # --- blocks ------------------------------------------------------------------
    genesis = Block.genesis()
    assert genesis == Block.genesis() and genesis.verify_integrity()
    assert genesis.prev_hash == ZERO_HASH and genesis.merkle_root == MerkleTree([]).root_hex

    txs = [Transaction.coinbase(alice.address, 50), tx]
    block = Block.create(1, genesis.hash, txs, difficulty=2)
    assert block.merkle_root == Block.compute_merkle_root(txs)
    while not block.meets_difficulty():                          # tiny PoW, demo only
        block.nonce += 1
        block.hash = block.compute_hash()
    assert block.hash.startswith("00") and block.verify_integrity()

    wire_block = block.to_json()
    restored = Block.from_json(wire_block)
    assert restored == block and restored.verify_integrity() and restored.to_json() == wire_block

    tampered = Block.from_json(wire_block)
    tampered.transactions[1] = Transaction(alice.address, bob.address, 9999, tx.signature, tx.timestamp)
    assert not tampered.verify_integrity()                       # merkle root mismatch
    tampered = Block.from_json(wire_block)
    tampered.nonce += 1
    assert not tampered.verify_integrity()                       # hash mismatch
    weak = Block.create(1, genesis.hash, txs, difficulty=2)
    weak.hash = weak.compute_hash()
    if weak.meets_difficulty():                                  # ~1/256 chance; force a miss
        weak.nonce = 1
        weak.hash = weak.compute_hash()
    if not weak.meets_difficulty():
        assert not weak.verify_integrity() and weak.verify_integrity(check_pow=False)
    dup = Block.create(1, genesis.hash, [tx, tx])
    assert not dup.verify_integrity()                            # duplicate tx
    late_reward = Block.create(1, genesis.hash, [tx, Transaction.coinbase(bob.address, 50)])
    assert not late_reward.verify_integrity()                    # coinbase not first
    for field_name, value in (("index", -1), ("nonce", "0"), ("prev_hash", "abc"), ("difficulty", 65)):
        broken = block.to_dict()
        broken[field_name] = value
        _expect_error(ValueError, Block.from_dict, broken)
    _expect_error(ValueError, Block.from_dict, {**block.to_dict(), "transactions": "nope"})
    _expect_error(SerializationError, Block.from_json, "not json")
    print("[ok] Block creation, mining demo, integrity checks, serialization, tamper detection")

    print("\nAll stage-1 self-tests passed.")


# =============================================================================
# STAGE 2: LEDGER, WORLD STATE AND CHAIN REORGANIZATION
# =============================================================================

BLOCK_REWARD = 50  # default cap on the coinbase amount a single block may claim

AccountState = dict[str, int]  # {"balance": int, "nonce": int}


class LedgerError(ValueError):
    """Raised internally when a block or chain is rejected; the message says why."""


def mine_block(
    index: int,
    prev_hash: str,
    transactions: Sequence[Transaction],
    difficulty: int = 0,
    timestamp: datetime | None = None,
) -> Block:
    """Build a block and grind its nonce until the hash meets ``difficulty``.

    Demo-grade single-threaded mining; the dedicated mining stage replaces it.
    """
    block = Block.create(index, prev_hash, transactions, difficulty, timestamp)
    while not block.meets_difficulty():
        block.nonce += 1
        block.hash = block.compute_hash()
    return block


class Ledger:
    def __init__(
        self,
        genesis: Block | None = None,
        block_reward: int | None = BLOCK_REWARD,
    ) -> None:
        """Start from ``genesis`` (default: the canonical genesis block).

        ``block_reward`` is the maximum coinbase amount per block; ``None``
        disables the cap (not recommended outside tests).
        """
        genesis = Block.genesis() if genesis is None else genesis
        if not isinstance(genesis, Block) or not genesis.verify_integrity():
            raise ValueError("genesis block failed integrity verification")
        if genesis.index != 0 or genesis.prev_hash != ZERO_HASH or genesis.transactions:
            raise ValueError("genesis must have index 0, a zero prev_hash and no transactions")
        if block_reward is not None and (not _is_int(block_reward) or block_reward < 1):
            raise ValueError("block_reward must be a positive integer or None")

        self.block_reward: int | None = block_reward
        self.last_error: str | None = None
        self._state: dict[str, AccountState] = {}
        self._chain: list[Block] = [genesis]
        # _undo[i] restores the accounts touched by _chain[i]: address -> previous
        # state, or None if the account did not exist before that block.
        self._undo: list[dict[str, AccountState | None]] = [{}]

    # ---- read access ------------------------------------------------------

    @property
    def tip_hash(self) -> str:
        """Hash of the newest block on the active chain."""
        return self._chain[-1].hash

    @property
    def tip_index(self) -> int:
        """Index (height) of the newest block on the active chain."""
        return self._chain[-1].index

    @property
    def chain(self) -> list[Block]:
        """Copy of the active chain, genesis first."""
        return list(self._chain)

    @property
    def state(self) -> dict[str, AccountState]:
        """Deep copy of the world state (mutating it does not affect the ledger)."""
        return {addr: dict(acct) for addr, acct in self._state.items()}

    def get_balance(self, address: str) -> int:
        """Current balance of ``address`` (0 if the account is unknown)."""
        account = self._state.get(address)
        return 0 if account is None else account["balance"]

    def get_nonce(self, address: str) -> int:
        """Nonce the next transaction from ``address`` must carry (0 if unknown)."""
        account = self._state.get(address)
        return 0 if account is None else account["nonce"]

    def total_supply(self) -> int:
        """Sum of all balances (handy invariant: equals the sum of applied coinbases)."""
        return sum(acct["balance"] for acct in self._state.values())

    def __repr__(self) -> str:
        return f"Ledger(tip_index={self.tip_index}, tip_hash={self.tip_hash[:12]}..., accounts={len(self._state)})"

    # ---- block application ------------------------------------------------

    def apply_block(self, block: Block) -> bool:
        
        try:
            changes, undo = self._stage_block(block)
        except LedgerError as exc:
            self.last_error = str(exc)
            return False
        # Commit. Nothing below can fail, which is what makes application atomic.
        self._state.update(changes)
        self._chain.append(block)
        self._undo.append(undo)
        self.last_error = None
        return True

    def _stage_block(
        self, block: Block
    ) -> tuple[dict[str, AccountState], dict[str, AccountState | None]]:
        """Validate ``block`` against the current state without modifying it.

        Returns ``(changes, undo)``: the new value of every touched account and
        the values needed to roll them back. Raises :class:`LedgerError`.
        """
        if not isinstance(block, Block):
            raise LedgerError("not a Block")
        if not block.verify_integrity():
            raise LedgerError("block failed integrity verification")
        if block.index != self.tip_index + 1:
            raise LedgerError(f"block index {block.index} does not follow tip index {self.tip_index}")
        if block.prev_hash != self.tip_hash:
            raise LedgerError("prev_hash does not match the ledger tip")

        changes: dict[str, AccountState] = {}
        undo: dict[str, AccountState | None] = {}

        def touch(address: str) -> AccountState:
            """Working copy of an account, recording its original value once."""
            account = changes.get(address)
            if account is None:
                original = self._state.get(address)
                undo[address] = None if original is None else dict(original)
                account = dict(original) if original is not None else {"balance": 0, "nonce": 0}
                changes[address] = account
            return account

        for position, tx in enumerate(block.transactions):
            if tx.is_coinbase:
                if position != 0:
                    raise LedgerError(f"tx #{position}: coinbase is only allowed first in a block")
                if self.block_reward is not None and tx.amount > self.block_reward:
                    raise LedgerError(
                        f"tx #{position}: coinbase amount {tx.amount} exceeds block reward {self.block_reward}"
                    )
                touch(tx.receiver)["balance"] += tx.amount
                continue

            sender = touch(tx.sender)
            if sender["balance"] < tx.amount:
                raise LedgerError(
                    f"tx #{position}: insufficient balance ({sender['balance']} < {tx.amount})"
                )
            if tx.nonce != sender["nonce"]:
                raise LedgerError(
                    f"tx #{position}: bad nonce (expected {sender['nonce']}, got {tx.nonce})"
                )
            # Defence in depth: verify_integrity() already checked this, but the
            # ledger should not depend on what the caller did beforehand.
            if not verify_signature(tx.sender, tx.signature, tx.signing_payload()):
                raise LedgerError(f"tx #{position}: invalid signature")
            sender["balance"] -= tx.amount
            sender["nonce"] += 1
            touch(tx.receiver)["balance"] += tx.amount  # touch after debit: self-sends stay correct

        return changes, undo

    def _pop_tip(self) -> Block:
        """Undo the newest block (never the genesis block) and return it."""
        if len(self._chain) <= 1:
            raise LedgerError("cannot revert the genesis block")
        block = self._chain.pop()
        for address, previous in self._undo.pop().items():
            if previous is None:
                self._state.pop(address, None)
            else:
                self._state[address] = dict(previous)
        return block

    # ---- chain reorganization ---------------------------------------------

    def reorganize(self, new_chain: list[Block]) -> bool:
        """Switch to ``new_chain`` if it is valid and longer than the active chain.

        ``new_chain`` must be a contiguous run of blocks whose first block is
        already on the active chain: either the genesis block (a full chain) or
        any later known block that acts as the common ancestor. The common
        ancestor is the last leading block that matches our chain; the blocks
        after it are validated one by one on a scratch copy of the ledger rolled
        back to that ancestor. Only if all of them apply and the new tip index is
        strictly higher than ours is the scratch state adopted. Otherwise the
        ledger is untouched and ``False`` is returned (reason in ``last_error``).
        """
        try:
            candidate = self._build_candidate(new_chain)
        except LedgerError as exc:
            self.last_error = str(exc)
            return False
        self._state = candidate._state
        self._chain = candidate._chain
        self._undo = candidate._undo
        self.last_error = None
        return True

    def _build_candidate(self, new_chain: list[Block]) -> "Ledger":
        """Return a fully validated ledger for ``new_chain``. Raises LedgerError."""
        if (
            not isinstance(new_chain, (list, tuple))
            or not new_chain
            or not all(isinstance(block, Block) for block in new_chain)
        ):
            raise LedgerError("new chain must be a non-empty list of Block objects")

        base = new_chain[0]
        if (
            not _is_int(base.index)
            or not 0 <= base.index <= self.tip_index
            or self._chain[base.index].hash != base.hash
        ):
            raise LedgerError("new chain does not start at a block on the current chain (unknown ancestor)")

        # Skip the prefix we already have; the last shared block is the common ancestor.
        shared = 0
        while (
            shared < len(new_chain)
            and base.index + shared <= self.tip_index
            and new_chain[shared].hash == self._chain[base.index + shared].hash
        ):
            shared += 1
        ancestor_index = base.index + shared - 1
        fork_blocks = new_chain[shared:]

        if not fork_blocks or fork_blocks[-1].index <= self.tip_index:
            raise LedgerError("new chain is not longer than the current chain")

        candidate = self._clone_at(ancestor_index)
        for block in fork_blocks:
            if not candidate.apply_block(block):
                raise LedgerError(f"block {block.index} rejected: {candidate.last_error}")
        return candidate

    # ---- persistence support (Stage 5) --------------------------------------

    def load_chain(self, blocks: Sequence[Block]) -> None:
        """Rebuild this ledger by replaying a previously stored chain.

        ``blocks`` must start with this ledger's genesis block, and the ledger
        must still be at genesis. Every block is fully re-validated on a scratch
        ledger (so a tampered database is detected) and the result is adopted
        only if all of them apply, which also reconstructs the per-block undo
        records needed for later reorganizations. Raises :class:`LedgerError`
        and leaves this ledger untouched on failure.
        """
        if self.tip_index != 0:
            raise LedgerError("a stored chain can only be loaded into a ledger that is at genesis")
        if not blocks or blocks[0].hash != self._chain[0].hash:
            raise LedgerError("stored chain does not start at this ledger's genesis block")
        scratch = Ledger(self._chain[0], self.block_reward)
        for block in blocks[1:]:
            if not scratch.apply_block(block):
                raise LedgerError(f"stored block {block.index} is invalid: {scratch.last_error}")
        self._state = scratch._state
        self._chain = scratch._chain
        self._undo = scratch._undo
        self.last_error = None

    def _snapshot(self) -> tuple[dict[str, AccountState], list[Block], list[dict[str, AccountState | None]]]:
        """References to the current state/chain/undo, for :meth:`_restore`.

        Only valid across :meth:`reorganize`, which *replaces* these objects
        rather than mutating them, so the references stay intact.
        """
        return self._state, self._chain, self._undo

    def _restore(
        self, snapshot: tuple[dict[str, AccountState], list[Block], list[dict[str, AccountState | None]]]
    ) -> None:
        """Go back to a state captured by :meth:`_snapshot`."""
        self._state, self._chain, self._undo = snapshot

    def _clone_at(self, height: int) -> "Ledger":
        """Independent copy of this ledger rolled back to the block at ``height``."""
        clone = Ledger.__new__(Ledger)
        clone.block_reward = self.block_reward
        clone.last_error = None
        clone._state = {addr: dict(acct) for addr, acct in self._state.items()}
        clone._chain = list(self._chain)
        clone._undo = list(self._undo)
        while clone.tip_index > height:
            clone._pop_tip()
        return clone


# =============================================================================
# STAGE 2 SELF-TEST
# =============================================================================


def _self_test_stage_2() -> None:
    difficulty = 2  # ~256 hashes per block on average: real PoW, still instant

    def make_tx(sender: KeyPair, receiver: str, amount: int, nonce: int) -> Transaction:
        return Transaction(sender.address, receiver, amount, nonce=nonce).sign(sender)

    def reward(address: str) -> Transaction:
        return Transaction.coinbase(address, BLOCK_REWARD)

    def mine(index: int, prev_hash: str, txs: list[Transaction]) -> Block:
        return mine_block(index, prev_hash, txs, difficulty)

    genesis = Block.genesis()
    ledger = Ledger(genesis)
    alice, bob, charlie = KeyPair.generate(), KeyPair.generate(), KeyPair.generate()
    A, B, C = alice.address, bob.address, charlie.address

    def expect_rejected(block: Block, reason: str) -> None:
        """Apply must fail with ``reason`` in last_error and leave the ledger untouched."""
        before = (ledger.state, ledger.tip_hash, ledger.tip_index, len(ledger.chain))
        assert not ledger.apply_block(block), "block should have been rejected"
        assert reason in (ledger.last_error or ""), ledger.last_error
        assert (ledger.state, ledger.tip_hash, ledger.tip_index, len(ledger.chain)) == before

    def expect_reorg_rejected(chain: list[Block], reason: str) -> None:
        before = (ledger.state, ledger.tip_hash, ledger.tip_index, len(ledger.chain))
        assert not ledger.reorganize(chain), "reorganization should have been rejected"
        assert reason in (ledger.last_error or ""), ledger.last_error
        assert (ledger.state, ledger.tip_hash, ledger.tip_index, len(ledger.chain)) == before

    # --- setup & block 1 -------------------------------------------------------
    assert ledger.tip_hash == genesis.hash and ledger.tip_index == 0 and ledger.state == {}
    assert ledger.get_balance(A) == 0 and ledger.get_nonce(A) == 0
    _expect_error(ValueError, Ledger, Block.create(1, ZERO_HASH, []))     # not a genesis block
    _expect_error(ValueError, Ledger, genesis, 0)                         # bad block_reward

    block1 = mine(1, genesis.hash, [reward(A)])
    assert ledger.apply_block(block1), ledger.last_error
    assert ledger.last_error is None
    assert ledger.get_balance(A) == 50 and ledger.get_nonce(A) == 0
    assert ledger.tip_hash == block1.hash and ledger.tip_index == 1
    snapshot = ledger.state
    snapshot[A]["balance"] = 10**9                                         # a copy: no effect
    assert ledger.get_balance(A) == 50
    print("[ok] Ledger initialised from genesis; block 1 credits Alice's coinbase")

    # --- block 2: Alice pays Bob -------------------------------------------------
    payment = make_tx(alice, B, 20, nonce=0)
    block2 = mine(2, block1.hash, [reward(A), payment])
    assert ledger.apply_block(block2), ledger.last_error
    assert ledger.get_balance(A) == 80 and ledger.get_nonce(A) == 1       # 50 + 50 - 20
    assert ledger.get_balance(B) == 20 and ledger.get_nonce(B) == 0
    assert ledger.get_balance(C) == 0 and ledger.total_supply() == 100
    assert ledger.tip_hash == block2.hash and ledger.tip_index == 2
    print("[ok] Block 2 transfer: balances updated, sender nonce incremented")

    # --- negative tests (each must leave the ledger untouched) ---------------------
    overspend = make_tx(alice, B, 1000, nonce=1)
    expect_rejected(mine(3, block2.hash, [reward(C), overspend]), "insufficient balance")

    # in-block double spend: 50 + 50 > 80. The first transfer is fine on its own,
    # so this also proves that a failing block is not partially applied.
    double_spend = [reward(C), make_tx(alice, B, 50, nonce=1), make_tx(alice, C, 50, nonce=2)]
    expect_rejected(mine(3, block2.hash, double_spend), "insufficient balance")
    assert ledger.get_balance(C) == 0 and ledger.get_balance(B) == 20      # coinbase + 1st transfer rolled back

    expect_rejected(mine(3, block2.hash, [reward(C), payment]), "bad nonce")           # replay of block 2's tx
    expect_rejected(mine(3, block2.hash, [reward(C), make_tx(alice, B, 1, 5)]), "bad nonce")  # nonce gap
    expect_rejected(mine(3, genesis.hash, [reward(C)]), "prev_hash")                   # wrong parent
    expect_rejected(mine(5, block2.hash, [reward(C)]), "index")                        # wrong height
    forged = Transaction(A, B, 1, bytes(64), payment.timestamp, nonce=1)
    expect_rejected(mine(3, block2.hash, [reward(C), forged]), "integrity")            # bad signature
    inflated = Transaction.coinbase(C, BLOCK_REWARD + 1)
    expect_rejected(mine(3, block2.hash, [inflated]), "block reward")                  # minting too much
    assert not ledger.apply_block(block2) and ledger.tip_hash == block2.hash           # re-applying a block
    print("[ok] Rejected: overspend, in-block double spend (atomic), replay, nonce gap, "
          "bad prev_hash/index/signature, inflated coinbase")

    # --- fork test -------------------------------------------------------------------
    # Fork branches off block 1: block 2' pays Charlie instead of Alice, and block 3'
    # builds on it. Honest chain: genesis, 1, 2, tip=2. Fork: genesis, 1, 2', 3'.
    fork2 = mine(2, block1.hash, [reward(C)])
    fork3 = mine(3, fork2.hash, [reward(C), make_tx(charlie, B, 10, nonce=0)])
    main_state = ledger.state

    expect_reorg_rejected([genesis, block1, fork2], "not longer")                       # equal height: keep ours
    expect_reorg_rejected([genesis], "not longer")
    bad3 = mine(3, fork2.hash, [reward(C), make_tx(charlie, B, 1000, nonce=0)])
    expect_reorg_rejected([genesis, block1, fork2, bad3], "insufficient balance")      # longer but invalid
    expect_reorg_rejected([fork2, fork3], "unknown ancestor")                          # ancestor not on our chain
    expect_reorg_rejected([genesis, block1, fork3], "block 3 rejected")                # gap: fork2 missing
    assert ledger.state == main_state and ledger.tip_hash == block2.hash
    other_genesis = mine_block(0, ZERO_HASH, [], 0, GENESIS_TIMESTAMP.replace(year=2023))
    expect_reorg_rejected([other_genesis, mine(1, other_genesis.hash, [reward(C)])], "unknown ancestor")

    assert ledger.reorganize([genesis, block1, fork2, fork3]), ledger.last_error
    assert ledger.last_error is None
    assert ledger.tip_hash == fork3.hash and ledger.tip_index == 3
    assert ledger.get_balance(A) == 50 and ledger.get_nonce(A) == 0                    # Alice's payment undone
    assert ledger.get_balance(B) == 10 and ledger.get_nonce(B) == 0                    # only Charlie's 10 remains
    assert ledger.get_balance(C) == 90 and ledger.get_nonce(C) == 1                    # 50 + 50 - 10
    assert ledger.total_supply() == 150 and [b.hash for b in ledger.chain] == [
        genesis.hash, block1.hash, fork2.hash, fork3.hash
    ]
    assert not ledger.apply_block(block2) and ledger.get_balance(A) == 50              # old branch is stale now
    print("[ok] Reorganization: longer valid fork adopted, balances and nonces switched")

    # --- reorganize from a common ancestor (partial chain) ---------------------------------
    alt2 = mine(2, block1.hash, [reward(B)])
    alt3 = mine(3, alt2.hash, [reward(B), make_tx(bob, C, 30, nonce=0)])
    alt4 = mine(4, alt3.hash, [reward(C)])
    expect_reorg_rejected([block1, alt2, alt3], "not longer")                           # same height as ours
    expect_reorg_rejected([alt2, alt3, alt4], "unknown ancestor")                       # must start on our chain
    assert ledger.reorganize([block1, alt2, alt3, alt4]), ledger.last_error             # block 1 is the ancestor
    assert ledger.tip_hash == alt4.hash and ledger.tip_index == 4
    assert (ledger.get_balance(A), ledger.get_nonce(A)) == (50, 0)
    assert (ledger.get_balance(B), ledger.get_nonce(B)) == (70, 1)                     # 50 + 50 - 30
    assert (ledger.get_balance(C), ledger.get_nonce(C)) == (80, 0)                     # 30 + 50; fork's tx undone
    assert ledger.total_supply() == 200
    print("[ok] Reorganization from a common ancestor (no genesis in the submitted chain)")

    # --- the ledger keeps working after a reorganization -----------------------------------
    block5 = mine(5, alt4.hash, [reward(A), make_tx(bob, A, 5, nonce=1)])
    assert ledger.apply_block(block5), ledger.last_error
    assert ledger.get_balance(A) == 105 and ledger.get_balance(B) == 65 and ledger.get_nonce(B) == 2
    assert ledger.total_supply() == 250
    # reverting all the way and re-applying must reproduce the same state
    fresh = Ledger(genesis)
    for block in ledger.chain[1:]:
        assert fresh.apply_block(block), fresh.last_error
    assert fresh.state == ledger.state and fresh.tip_hash == ledger.tip_hash
    print("[ok] Ledger extends normally after reorg; replay from genesis reproduces the same state")

    print("\nAll stage-2 self-tests passed.")


# =============================================================================
# STAGE 3: P2P NETWORKING & MEMPOOL  (+ STAGE 4: HTTP API hosted by the Node)
# =============================================================================

DEFAULT_API_HOST = "127.0.0.1"
DEFAULT_API_PORT = 8080
DEFAULT_DB_PATH = "miniblock.db"   # database used by the CLI ``serve`` command
DEFAULT_MINE_DIFFICULTY = 0   # difficulty used by POST /v1/mine when none is given
MAX_API_DIFFICULTY = 6        # PoW runs in a worker thread that cannot be cancelled; cap what the API accepts


class Mempool:
    """A simple in-memory pool of pending, unmined transactions."""

    def __init__(self) -> None:
        self._txs: dict[str, Transaction] = {}

    def add(self, tx: Transaction) -> bool:
        """Add a transaction to the mempool. Returns True if added, False if duplicate/invalid."""
        if not tx.verify():
            return False
        if tx.tx_id in self._txs:
            return False
        self._txs[tx.tx_id] = tx
        return True

    def remove(self, tx_ids: Set[str]) -> None:
        """Remove transactions by their IDs (e.g., after they are mined into a block)."""
        for tx_id in tx_ids:
            self._txs.pop(tx_id, None)

    def get_all(self) -> list[Transaction]:
        """Return a list of all pending transactions."""
        return list(self._txs.values())

    def __contains__(self, tx_id: object) -> bool:
        return tx_id in self._txs

    def __len__(self) -> int:
        return len(self._txs)


def _json_response(data: Any, status: int = 200) -> web.Response:
    """JSON response encoded with the canonical codec (bytes/datetime aware)."""
    return web.json_response(data, status=status, dumps=dumps)


def _error_response(message: str, status: int = 400) -> web.Response:
    """Uniform ``{"error": ...}`` body for every failed API call."""
    return _json_response({"error": message}, status)


@web.middleware
async def _api_error_middleware(
    request: web.Request, handler: Any
) -> web.StreamResponse:
    """Render every failure (unknown route, bad method, crash) as a JSON error body."""
    try:
        return await handler(request)
    except web.HTTPException as exc:
        response = _error_response(exc.reason or "error", exc.status)
        if "Allow" in exc.headers:  # keep the 405 Allow header
            response.headers["Allow"] = exc.headers["Allow"]
        return response
    except Exception as exc:  # noqa: BLE001 - last line of defence, never leak a traceback
        print(f"[API] Unhandled error on {request.method} {request.path}: {exc!r}")
        return _error_response("internal server error", 500)


class Node:
    def __init__(
        self,
        ledger: Ledger,
        host: str = "127.0.0.1",
        port: int = 8765,
        bootstrap_peers: list[str] | None = None,
        api_host: str = DEFAULT_API_HOST,
        api_port: int | None = DEFAULT_API_PORT,
        db_path: str | os.PathLike[str] | None = None,
    ) -> None:
        self.ledger = ledger
        self.host = host
        self.port = port
        self.api_host = api_host
        self.api_port = api_port
        self.bootstrap_peers = bootstrap_peers or []
        self.mempool = Mempool()
        self._server: Optional[websockets.WebSocketServer] = None
        self._connections: Set[websockets.WebSocketServerProtocol | websockets.WebSocketClientProtocol] = set()
        self._running = False
        self._api_runner: Optional[web.AppRunner] = None
        self._mine_lock = asyncio.Lock()  # one mining job at a time
        self.db_path = db_path
        self._db: Optional[Database] = None  # Database class: see the Stage 5 section below
        # Held while the ledger/mempool change *and* the matching database write happens,
        # so memory and disk are updated in the same order and can be rolled back together.
        self._chain_lock = asyncio.Lock()
        self._tasks: Set[asyncio.Task[Any]] = set()  # background tasks, cancelled on stop()

    @property
    def uri(self) -> str:
        return f"ws://{self.host}:{self.port}"

    @property
    def api_url(self) -> str | None:
        """Base URL of the HTTP API, or ``None`` if it is disabled."""
        return None if self.api_port is None else f"http://{self.api_host}:{self.api_port}"

    def _spawn(self, coro: Any) -> None:
        """Run ``coro`` as a background task that is tracked and cancelled on :meth:`stop`."""
        task = asyncio.create_task(coro)
        self._tasks.add(task)
        task.add_done_callback(self._tasks.discard)

    async def start(self) -> None:
        """Open the database, start the P2P server and HTTP API, and connect to bootstrap peers.

        The stored chain is restored *before* any server accepts a connection.
        If any step fails, everything already started is shut down again.
        """
        self._running = True
        try:
            await self._open_database()
            self._server = await websockets.serve(self._handle_connection, self.host, self.port)
            print(f"[Node] Listening on {self.uri}")
            await self._start_api()
        except BaseException:
            await self.stop()  # leave nothing running (servers, database) after a failed start
            raise

        for peer_uri in self.bootstrap_peers:
            self._spawn(self._connect_to_peer(peer_uri))

        # Request chain from peers to sync up on startup
        self._spawn(self._request_chain_from_peers())

    async def stop(self) -> None:
        """Shutdown the HTTP API, the P2P server and all peer connections."""
        self._running = False
        if self._api_runner is not None:
            runner, self._api_runner = self._api_runner, None
            await runner.cleanup()
            print(f"[Node] API stopped {self.api_url}")
        tasks = list(self._tasks)
        for task in tasks:
            task.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)
        if self._server:
            self._server.close()
            await self._server.wait_closed()
            self._server = None
        for conn in list(self._connections):  # copy: handlers discard themselves while closing
            await conn.close()
        self._connections.clear()
        if self._db is not None:
            async with self._chain_lock:  # let an in-flight block commit finish first
                await self._db.close()
        print(f"[Node] Stopped {self.uri}")

    async def _handle_connection(self, websocket: websockets.WebSocketServerProtocol) -> None:
        """Handle an incoming WebSocket connection."""
        self._connections.add(websocket)
        print(f"[Node] Peer connected: {websocket.remote_address}")
        try:
            async for message in websocket:
                await self._process_message(message, source_ws=websocket)
        except websockets.ConnectionClosed:
            pass
        finally:
            self._connections.discard(websocket)
            print(f"[Node] Peer disconnected: {websocket.remote_address}")

    async def _connect_to_peer(self, peer_uri: str) -> None:
        """Establish an outgoing WebSocket connection to a peer."""
        websocket = None
        try:
            websocket = await websockets.connect(peer_uri)
            self._connections.add(websocket)
            print(f"[Node] Connected to peer: {peer_uri}")
            async for message in websocket:
                await self._process_message(message, source_ws=websocket)
        except Exception as e:
            print(f"[Node] Failed to connect to {peer_uri}: {e}")
        finally:
            if websocket is not None:
                self._connections.discard(websocket)

    async def broadcast(self, msg: dict) -> None:
        """Broadcast a JSON message to all connected peers."""
        payload = dumps(msg)
        disconnected = set()
        for conn in list(self._connections):  # copy: the set may change while we await
            try:
                await conn.send(payload)
            except websockets.ConnectionClosed:
                disconnected.add(conn)
        self._connections -= disconnected

    async def _process_message(
        self,
        raw_msg: str,
        source_ws: Optional[websockets.WebSocketServerProtocol | websockets.WebSocketClientProtocol] = None
    ) -> None:
        """Route and handle incoming network messages."""
        try:
            msg = loads(raw_msg)
        except SerializationError:
            return  # Ignore malformed messages

        msg_type = msg.get("type")
        data = msg.get("data")

        if msg_type == "tx":
            try:
                tx = Transaction.from_json(data)
                # _add_to_mempool returns False if invalid or duplicate (prevents echo loops)
                if await self._add_to_mempool(tx):
                    print(f"[Node] Added tx {tx.tx_id[:8]}... to mempool")
                    await self.broadcast({"type": "tx", "data": data})
            except ValueError:
                pass  # Ignore invalid transactions
            except DatabaseError as exc:
                print(f"[Node] Could not store tx in the database, dropped: {exc}")

        elif msg_type == "block":
            try:
                block = Block.from_json(data)
                if block.hash == self.ledger.tip_hash:
                    return  # Already have this block, ignore echo

                if await self._apply_block_persisted(block):
                    print(f"[Node] Applied block {block.index} (hash: {block.hash[:8]}...)")
                    await self.broadcast({"type": "block", "data": data})
                else:
                    # If application fails, it might be a fork. Request the full chain to reorganize.
                    print(f"[Node] Block {block.index} rejected ({self.ledger.last_error}), requesting chain sync...")
                    await self._request_chain_from_peers()
            except ValueError:
                pass  # Ignore invalid blocks

        elif msg_type == "get_chain":
            # Respond with our current chain
            chain_data = [b.to_json() for b in self.ledger.chain]
            await self.broadcast({"type": "chain", "data": chain_data})

        elif msg_type == "chain":
            try:
                chain = [Block.from_json(item) for item in data]
                # Only reorganize if the received chain is valid and longer
                if chain and await self._reorganize_persisted(chain):
                    print(f"[Node] Reorganized to new chain, tip is now index {self.ledger.tip_index}")
            except (ValueError, TypeError):
                pass  # Ignore invalid chain data

    async def _request_chain_from_peers(self) -> None:
        """Ask all peers for their chain to check for forks or sync."""
        await self.broadcast({"type": "get_chain", "data": None})

    # ---- pending-state helpers (used by mining and by the API) --------------

    def _simulate_pending(self) -> tuple[list[Transaction], dict[str, AccountState]]:
        
        scratch: dict[str, AccountState] = {}

        def account(address: str) -> AccountState:
            acct = scratch.get(address)
            if acct is None:
                acct = {
                    "balance": self.ledger.get_balance(address),
                    "nonce": self.ledger.get_nonce(address),
                }
                scratch[address] = acct
            return acct

        limit = MAX_TXS_PER_BLOCK - 1  # leave room for the coinbase transaction
        pending = [tx for tx in self.mempool.get_all() if not tx.is_coinbase]
        selected: list[Transaction] = []
        progress = True
        while pending and progress and len(selected) < limit:
            progress = False
            remaining: list[Transaction] = []
            for tx in pending:
                sender = account(tx.sender)
                if (
                    len(selected) < limit
                    and tx.nonce == sender["nonce"]
                    and sender["balance"] >= tx.amount
                ):
                    sender["balance"] -= tx.amount
                    sender["nonce"] += 1
                    account(tx.receiver)["balance"] += tx.amount  # after the debit: self-sends stay correct
                    selected.append(tx)
                    progress = True
                else:
                    remaining.append(tx)
            pending = remaining
        return selected, scratch

    def projected_account(self, address: str) -> AccountState:
        """Balance and next usable nonce of ``address`` once all valid pending txs are applied."""
        _, scratch = self._simulate_pending()
        acct = scratch.get(address)
        if acct is None:
            return {"balance": self.ledger.get_balance(address), "nonce": self.ledger.get_nonce(address)}
        return dict(acct)

    def validate_transaction(self, tx: Transaction) -> None:
        
        if tx.is_coinbase:
            raise ValueError("coinbase transactions cannot be submitted")
        if not tx.verify():
            raise ValueError("invalid transaction: malformed or bad signature")
        if tx.tx_id in self.mempool:
            raise ValueError("transaction already in mempool")
        projected = self.projected_account(tx.sender)
        if tx.nonce != projected["nonce"]:
            raise ValueError(f"bad nonce (expected {projected['nonce']}, got {tx.nonce})")
        if tx.amount > projected["balance"]:
            raise ValueError(f"insufficient balance ({projected['balance']} < {tx.amount})")

    def _mempool_ids_to_drop(self, mined: Iterable[Transaction] = ()) -> set[str]:
        """Ids to evict from the mempool after the ledger changed.

        That is every transaction in ``mined`` plus every pending transaction that
        can never apply again (coinbase, or a nonce the sender has already used).
        """
        drop = {tx.tx_id for tx in mined}
        for tx in self.mempool.get_all():
            if tx.is_coinbase or tx.nonce < self.ledger.get_nonce(tx.sender):
                drop.add(tx.tx_id)
        return drop

    def _touched_accounts(self, txs: Iterable[Transaction]) -> dict[str, AccountState]:
        """Current ledger values of every account that ``txs`` credit or debit."""
        addresses: set[str] = set()
        for tx in txs:
            addresses.add(tx.receiver)
            if not tx.is_coinbase:
                addresses.add(tx.sender)
        return {
            address: {"balance": self.ledger.get_balance(address), "nonce": self.ledger.get_nonce(address)}
            for address in addresses
        }

    async def _open_database(self) -> None:
        """Open ``db_path`` and restore chain + mempool from it (or initialise it from the ledger)."""
        if self.db_path is None:
            return
        db = Database(self.db_path)
        await db.open()
        try:
            stored = await db.load()
            if stored.blocks:
                self.ledger.load_chain(stored.blocks)  # full replay: re-validates every stored block
                if self.ledger.state != stored.state:
                    raise DatabaseError("state table does not match the stored chain (database is corrupt)")
            else:
                await db.initialize(self.ledger.chain, self.ledger.state)

            invalid = set(stored.invalid_mempool_ids)
            for tx in stored.mempool:
                if not self.mempool.add(tx):
                    invalid.add(tx.tx_id)
            stale = self._mempool_ids_to_drop()
            if invalid or stale:
                await db.remove_mempool(invalid | stale)
                self.mempool.remove(stale)
        except BaseException:
            await db.close()
            raise
        self._db = db
        print(
            f"[Node] Database {self.db_path}: chain at index {self.ledger.tip_index}, "
            f"{len(self.mempool)} pending transaction(s)"
        )

    async def _add_to_mempool(self, tx: Transaction, validate: bool = False) -> bool:
        
        async with self._chain_lock:
            if validate:
                self.validate_transaction(tx)
            if not self.mempool.add(tx):
                return False
            if self._db is not None:
                try:
                    await self._db.add_mempool_tx(tx)
                except DatabaseError:
                    self.mempool.remove({tx.tx_id})
                    raise
            return True

    async def _apply_block_persisted(self, block: Block) -> bool:
        
        async with self._chain_lock:
            if not self.ledger.apply_block(block):
                return False
            drop = self._mempool_ids_to_drop(block.transactions)
            if self._db is not None:
                accounts = self._touched_accounts(block.transactions)  # snapshot before any await
                try:
                    await self._db.commit_block(block, accounts, drop)
                except DatabaseError as exc:
                    self.ledger._pop_tip()
                    self.ledger.last_error = f"database write failed: {exc}"
                    print(f"[Node] {self.ledger.last_error}; block {block.index} rolled back")
                    return False
            self.mempool.remove(drop)
            return True

    async def _reorganize_persisted(self, chain: list[Block]) -> bool:
        
        async with self._chain_lock:
            old_chain = self.ledger.chain
            snapshot = self.ledger._snapshot()
            if not self.ledger.reorganize(chain):
                return False
            new_chain = self.ledger.chain
            shared = 0  # number of leading blocks both chains have in common (genesis always)
            while (
                shared < min(len(old_chain), len(new_chain))
                and old_chain[shared].hash == new_chain[shared].hash
            ):
                shared += 1
            ancestor, fork_blocks = new_chain[shared - 1], new_chain[shared:]
            drop = self._mempool_ids_to_drop(tx for block in fork_blocks for tx in block.transactions)
            if self._db is not None:
                try:
                    await self._db.commit_reorg(ancestor.index, ancestor.hash, fork_blocks, self.ledger.state, drop)
                except DatabaseError as exc:
                    self.ledger._restore(snapshot)
                    self.ledger.last_error = f"database write failed: {exc}"
                    print(f"[Node] {self.ledger.last_error}; reorganization rolled back")
                    return False
            self.mempool.remove(drop)
            return True

    async def mine_pending(self, difficulty: int = 0, reward_address: str | None = None) -> Optional[Block]:
        
        async with self._mine_lock:
            txs, _ = self._simulate_pending()
            if not txs and reward_address is None:
                return None  # Nothing to mine

            reward_tx = [Transaction.coinbase(reward_address, BLOCK_REWARD)] if reward_address else []
            block_txs = reward_tx + txs

            # Create and mine the block (nonce grinding is CPU-bound: keep it off the event loop)
            block = await asyncio.to_thread(
                mine_block,
                self.ledger.tip_index + 1,
                self.ledger.tip_hash,
                block_txs,
                difficulty,
            )

            # If a peer's block arrived while we were mining, ours is stale and the apply is rejected.
            if await self._apply_block_persisted(block):
                print(f"[Node] Mined and applied block {block.index}")
                await self.broadcast({"type": "block", "data": block.to_json()})
                return block
            return None

    async def submit_transaction(self, tx: Transaction) -> None:
        """Validate ``tx`` against the ledger, store it in the mempool (and database) and broadcast it.

        Raises ``ValueError`` if the transaction is invalid and :class:`DatabaseError`
        if it could not be stored.
        """
        if not await self._add_to_mempool(tx, validate=True):
            raise ValueError("transaction rejected by mempool")
        print(f"[Node] Accepted tx {tx.tx_id[:8]}... via API")
        await self.broadcast({"type": "tx", "data": tx.to_json()})

    # ---- HTTP API (Stage 4) ---------------------------------------------------

    def _build_api_app(self) -> web.Application:
        """Create the aiohttp application with all ``/v1`` routes."""
        app = web.Application(middlewares=[_api_error_middleware])
        app.add_routes(
            [
                web.get("/v1/status", self._api_status),
                web.get("/v1/balance/{address}", self._api_balance),
                web.get("/v1/block/{identifier}", self._api_block),
                web.post("/v1/transaction", self._api_transaction),
                web.post("/v1/mine", self._api_mine),
            ]
        )
        return app

    async def _start_api(self) -> None:
        """Bind the HTTP server on the running event loop (no-op if ``api_port`` is None)."""
        if self.api_port is None:
            return
        runner = web.AppRunner(self._build_api_app(), access_log=None)
        await runner.setup()
        try:
            site = web.TCPSite(runner, self.api_host, self.api_port)
            await site.start()
        except BaseException:
            await runner.cleanup()
            raise
        self._api_runner = runner
        print(f"[Node] API listening on {self.api_url}")

    async def _api_status(self, request: web.Request) -> web.Response:
        """``GET /v1/status``: chain tip, peer count and mempool size."""
        return _json_response(
            {
                "tip_index": self.ledger.tip_index,
                "tip_hash": self.ledger.tip_hash,
                "peer_count": len(self._connections),
                "mempool_size": len(self.mempool),
            }
        )

    async def _api_balance(self, request: web.Request) -> web.Response:
        
        address = request.match_info["address"]
        if not is_valid_address(address):
            return _error_response("address must be 64 lowercase hex characters")
        if request.query.get("pending", "").lower() in ("1", "true", "yes"):
            account = self.projected_account(address)
        else:
            account = {"balance": self.ledger.get_balance(address), "nonce": self.ledger.get_nonce(address)}
        return _json_response({"address": address, "balance": account["balance"], "nonce": account["nonce"]})

    async def _api_block(self, request: web.Request) -> web.Response:
        """``GET /v1/block/{identifier}``: a block by index (digits) or by hash (64 hex)."""
        identifier = request.match_info["identifier"]
        chain = self.ledger.chain
        block: Block | None = None
        if is_valid_address(identifier):  # a 64-char hex string is always a hash
            block = next((b for b in chain if b.hash == identifier), None)
        elif identifier.isascii() and identifier.isdigit() and len(identifier) <= 18:
            index = int(identifier)
            if index < len(chain):
                block = chain[index]  # chain position == block index
        if block is None:
            return _error_response("block not found", 404)
        return _json_response(block.to_dict())

    async def _api_transaction(self, request: web.Request) -> web.Response:
        """``POST /v1/transaction``: validate, add to the mempool, broadcast to peers."""
        raw = await request.read()
        try:
            tx = Transaction.from_dict(loads(raw))
            await self.submit_transaction(tx)
        except ValueError as exc:  # includes SerializationError
            return _error_response(str(exc))
        except DatabaseError as exc:
            print(f"[API] Could not store transaction: {exc}")
            return _error_response("database write failed", 500)
        return _json_response({"tx_id": tx.tx_id, "status": "accepted"})

    async def _api_mine(self, request: web.Request) -> web.Response:

        raw = await request.read()
        params: Any = {}
        if raw.strip():
            try:
                params = loads(raw)
            except SerializationError as exc:
                return _error_response(str(exc))
            if not isinstance(params, dict):
                return _error_response("request body must be a JSON object")

        difficulty = params.get("difficulty", DEFAULT_MINE_DIFFICULTY)
        if not _is_int(difficulty) or not 0 <= difficulty <= MAX_API_DIFFICULTY:
            return _error_response(f"difficulty must be an integer in [0, {MAX_API_DIFFICULTY}]")
        reward_address = params.get("reward_address")
        if reward_address is not None and not is_valid_address(reward_address):
            return _error_response("reward_address must be 64 lowercase hex characters")

        if reward_address is None and not self._simulate_pending()[0]:
            return _error_response("mempool is empty: nothing to mine")

        block = await self.mine_pending(difficulty, reward_address)
        if block is None:
            reason = self.ledger.last_error or "chain tip changed while mining"
            return _error_response(f"mining failed: {reason}")
        return _json_response(block.to_dict())


# =============================================================================
# STAGE 3 SELF-TEST
# =============================================================================

async def _self_test_stage_3() -> None:
    # Setup two nodes on different local ports
    ledger_a = Ledger()
    ledger_b = Ledger()
    
    node_a = Node(ledger_a, port=8765, api_port=None)  # P2P only: Stage 4 tests the API
    node_b = Node(ledger_b, port=8766, bootstrap_peers=["ws://127.0.0.1:8765"], api_port=None)
    
    alice, bob = KeyPair.generate(), KeyPair.generate()
    A, B = alice.address, bob.address

    try:
        # Start nodes
        await node_a.start()
        await asyncio.sleep(0.1)  # Give server time to bind
        await node_b.start()
        await asyncio.sleep(0.2)  # Give time for handshake and initial chain sync

        # 1. Test Block Propagation (Simulate Node A mining Block 1)
        block1 = mine_block(1, ledger_a.tip_hash, [Transaction.coinbase(A, BLOCK_REWARD)], difficulty=0)
        assert ledger_a.apply_block(block1)
        await node_a.broadcast({"type": "block", "data": block1.to_json()})
        await asyncio.sleep(0.2)
        
        assert ledger_b.tip_index == 1, "Node B should have synced block 1"
        assert ledger_b.get_balance(A) == BLOCK_REWARD

        # 2. Test Transaction Propagation
        # Node B creates a transaction and broadcasts it
        tx1 = Transaction(A, B, 20, nonce=0).sign(alice)
        await node_b.broadcast({"type": "tx", "data": tx1.to_json()})
        await asyncio.sleep(0.2)
        
        # Node A should have received it in its mempool
        assert len(node_a.mempool) == 1, "Node A should have the tx in mempool"
        assert node_a.mempool.get_all()[0].tx_id == tx1.tx_id

        # 3. Test Block Mining and Propagation from Mempool
        # Node A mines the pending transaction
        mined_block = await node_a.mine_pending(difficulty=0, reward_address=A)
        assert mined_block is not None
        assert len(node_a.mempool) == 0, "Mempool should be cleared after mining"
        
        await asyncio.sleep(0.2)
        
        # Node B should have received and applied the mined block
        assert ledger_b.tip_index == 2, "Node B should have synced block 2"
        assert ledger_b.get_balance(A) == (BLOCK_REWARD * 2) - 20  # 50 + 50 - 20
        assert ledger_b.get_balance(B) == 20
        assert len(ledger_b.chain) == 3  # genesis + 2 blocks

        print("[ok] Stage 3: P2P transaction propagation, block mining, and chain sync")

    finally:
        await node_a.stop()
        await node_b.stop()


# =============================================================================
# STAGE 4: COMMAND-LINE INTERFACE
# =============================================================================

DEFAULT_NODE_URL = "http://127.0.0.1:8080"
DEFAULT_WALLET_PATH = "wallet.json"
HTTP_TIMEOUT = 10.0  # seconds, for CLI calls to a node


class CLIError(Exception):
    """A user-facing CLI failure; the message is printed and the exit code is 1."""


def _normalize_node_url(url: str) -> str:
    """``host:port`` or ``http://host:port/`` -> ``http://host:port``."""
    url = url.strip().rstrip("/")
    if not url:
        raise CLIError("node URL must not be empty")
    return url if "://" in url else f"http://{url}"


def _normalize_peer(peer: str) -> str:
    """``host:port`` -> ``ws://host:port``; full ``ws://`` / ``wss://`` URIs pass through."""
    peer = peer.strip()
    return peer if "://" in peer else f"ws://{peer}"


def _http_request(
    method: str, url: str, payload: str | None = None, timeout: float = HTTP_TIMEOUT
) -> tuple[int, Any]:
    """Blocking JSON call to a node. Returns ``(status, decoded body)``.

    HTTP error statuses are returned, not raised, so callers can show the
    node's ``{"error": ...}`` message. Network failures raise :class:`CLIError`.
    """
    request = urllib.request.Request(
        url,
        data=None if payload is None else payload.encode("utf-8"),
        method=method,
        headers={"Content-Type": "application/json", "Accept": "application/json"},
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status, body = response.status, response.read()
    except urllib.error.HTTPError as exc:  # must precede URLError (its base class)
        status, body = exc.code, exc.read()
    except (urllib.error.URLError, OSError, ValueError) as exc:
        raise CLIError(f"cannot reach node at {url}: {exc}") from exc
    try:
        return status, loads(body)
    except SerializationError as exc:
        raise CLIError(f"node returned a non-JSON response (HTTP {status}): {exc}") from exc


def _error_text(status: int, body: Any) -> str:
    """Best-effort human-readable message for a failed API call."""
    if isinstance(body, dict) and "error" in body:
        return f"{body['error']} (HTTP {status})"
    return f"unexpected response (HTTP {status})"


def _load_wallet(path: str) -> KeyPair:
    """Load a wallet file, converting every failure into a :class:`CLIError`."""
    try:
        return KeyPair.load(path)
    except FileNotFoundError:
        raise CLIError(f"wallet file not found: {path}") from None
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise CLIError(f"cannot read wallet {path}: {exc}") from exc


def _cmd_serve(args: argparse.Namespace) -> int:
    async def run() -> None:
        node = Node(
            Ledger(),
            host=args.host,
            port=args.p2p_port,
            bootstrap_peers=[_normalize_peer(peer) for peer in args.peer],
            api_host=args.api_host,
            api_port=args.api_port,
            db_path=args.db,
        )
        await node.start()
        print("[Node] Running. Press Ctrl+C to stop.")
        try:
            await asyncio.Event().wait()  # until cancelled
        finally:
            await node.stop()

    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print("\n[Node] Interrupted, shut down.")
    except (OSError, DatabaseError, LedgerError) as exc:  # port in use, unreadable/corrupt database, ...
        raise CLIError(f"cannot start node: {exc}") from exc
    return 0


def _cmd_wallet_create(args: argparse.Namespace) -> int:
    keypair = KeyPair.generate()
    try:
        keypair.save(args.path)
    except FileExistsError:
        raise CLIError(f"{args.path} already exists; refusing to overwrite it") from None
    except OSError as exc:
        raise CLIError(f"cannot write wallet {args.path}: {exc}") from exc
    print(f"Wallet saved to {args.path}")
    print(f"Address: {keypair.address}")
    return 0


def _cmd_wallet_show(args: argparse.Namespace) -> int:
    keypair = _load_wallet(args.path)
    node = _normalize_node_url(args.node)
    status, body = _http_request("GET", f"{node}/v1/balance/{keypair.address}")
    if status != 200 or not isinstance(body, dict):
        raise CLIError(f"balance lookup failed: {_error_text(status, body)}")
    print(f"Address: {keypair.address}")
    print(f"Balance: {body['balance']}")
    print(f"Nonce:   {body['nonce']}")
    return 0


def _cmd_tx_send(args: argparse.Namespace) -> int:
    keypair = _load_wallet(args.wallet_path)
    if not is_valid_address(args.to):
        raise CLIError("--to must be a 64-character lowercase hex address")
    node = _normalize_node_url(args.node)

    # pending=true: the nonce after any of our own still-unmined transactions
    status, body = _http_request("GET", f"{node}/v1/balance/{keypair.address}?pending=true")
    if status != 200 or not isinstance(body, dict) or not _is_int(body.get("nonce")):
        raise CLIError(f"could not fetch nonce: {_error_text(status, body)}")

    try:
        tx = Transaction(keypair.address, args.to, args.amount, nonce=body["nonce"]).sign(keypair)
        tx.check_structure()
    except ValueError as exc:
        raise CLIError(f"invalid transaction: {exc}") from exc

    status, body = _http_request("POST", f"{node}/v1/transaction", tx.to_json())
    if status != 200 or not isinstance(body, dict) or "tx_id" not in body:
        raise CLIError(f"transaction rejected: {_error_text(status, body)}")
    print(f"tx_id: {body['tx_id']}")
    return 0


def _port(value: str) -> int:
    """argparse type: a TCP port in [1, 65535]."""
    try:
        port = int(value)
    except ValueError:
        raise argparse.ArgumentTypeError(f"invalid port: {value!r}") from None
    if not 1 <= port <= 65535:
        raise argparse.ArgumentTypeError(f"port must be in [1, 65535], got {port}")
    return port


def _positive_int(value: str) -> int:
    """argparse type: an integer in [1, MAX_AMOUNT]."""
    try:
        number = int(value)
    except ValueError:
        raise argparse.ArgumentTypeError(f"invalid integer: {value!r}") from None
    if not 1 <= number <= MAX_AMOUNT:
        raise argparse.ArgumentTypeError(f"amount must be in [1, {MAX_AMOUNT}], got {number}")
    return number


def _build_parser() -> argparse.ArgumentParser:
    """Build the ``serve`` / ``wallet`` / ``tx`` command-line parser."""
    parser = argparse.ArgumentParser(prog="miniblock", description="Mini-blockchain node and wallet.")
    commands = parser.add_subparsers(dest="command", required=True, metavar="<command>")

    serve = commands.add_parser("serve", help="run a node (P2P server + HTTP API)")
    serve.add_argument("--p2p-port", type=_port, default=8765, help="WebSocket P2P port (default: 8765)")
    serve.add_argument("--api-port", type=_port, default=DEFAULT_API_PORT, help="HTTP API port (default: 8080)")
    serve.add_argument("--peer", action="append", default=[], metavar="URI",
                       help="bootstrap peer, e.g. ws://127.0.0.1:8766 (repeatable)")
    serve.add_argument("--db", default=DEFAULT_DB_PATH, metavar="PATH",
                       help="SQLite database file for the chain, state and mempool (default: miniblock.db)")
    serve.add_argument("--host", default="127.0.0.1", help="P2P bind address (default: 127.0.0.1)")
    serve.add_argument("--api-host", default=DEFAULT_API_HOST, help="API bind address (default: 127.0.0.1)")
    serve.set_defaults(func=_cmd_serve)

    wallet = commands.add_parser("wallet", help="create or inspect a wallet")
    wallet_cmds = wallet.add_subparsers(dest="wallet_command", required=True, metavar="<action>")
    create = wallet_cmds.add_parser("create", help="generate a new key pair and save it")
    create.add_argument("--path", default=DEFAULT_WALLET_PATH, help="wallet file (default: wallet.json)")
    create.set_defaults(func=_cmd_wallet_create)
    show = wallet_cmds.add_parser("show", help="print the address, balance and nonce")
    show.add_argument("--path", default=DEFAULT_WALLET_PATH, help="wallet file (default: wallet.json)")
    show.add_argument("--node", default=DEFAULT_NODE_URL, help="node API URL (default: http://127.0.0.1:8080)")
    show.set_defaults(func=_cmd_wallet_show)

    tx = commands.add_parser("tx", help="create and send transactions")
    tx_cmds = tx.add_subparsers(dest="tx_command", required=True, metavar="<action>")
    send = tx_cmds.add_parser("send", help="sign a transfer and submit it to a node")
    send.add_argument("--from", dest="wallet_path", required=True, metavar="WALLET",
                      help="path of the sender's wallet file")
    send.add_argument("--to", required=True, metavar="ADDRESS", help="receiver address")
    send.add_argument("--amount", type=_positive_int, required=True, help="amount to send (integer)")
    send.add_argument("--node", default=DEFAULT_NODE_URL, help="node API URL (default: http://127.0.0.1:8080)")
    send.set_defaults(func=_cmd_tx_send)
    return parser


def _cli_main(argv: Sequence[str]) -> int:
    """Run the CLI with ``argv`` (without the program name). Returns the exit code."""
    args = _build_parser().parse_args(list(argv))
    try:
        return int(args.func(args))
    except CLIError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


# =============================================================================
# STAGE 4 SELF-TEST
# =============================================================================


async def _self_test_stage_4() -> None:
    ledger = Ledger()
    alice, bob, miner = KeyPair.generate(), KeyPair.generate(), KeyPair.generate()
    A, B, M = alice.address, bob.address, miner.address

    # Fund Alice directly on the ledger so the API test starts from a known balance.
    seed = mine_block(1, ledger.tip_hash, [Transaction.coinbase(A, BLOCK_REWARD)], difficulty=0)
    assert ledger.apply_block(seed), ledger.last_error

    node = Node(ledger, port=8765, api_host="127.0.0.1", api_port=8080)
    base = "http://127.0.0.1:8080"
    json_header = {"Content-Type": "application/json"}

    await node.start()
    try:
        async with aiohttp.ClientSession() as session:

            async def get(path: str) -> tuple[int, Any]:
                async with session.get(base + path) as resp:
                    return resp.status, loads(await resp.text())

            async def post(path: str, body: str = "") -> tuple[int, Any]:
                async with session.post(base + path, data=body.encode("utf-8"), headers=json_header) as resp:
                    return resp.status, loads(await resp.text())

            async def mempool_size() -> int:
                status, body = await get("/v1/status")
                assert status == 200
                return body["mempool_size"]

            # --- GET /v1/status ------------------------------------------------
            status, body = await get("/v1/status")
            assert status == 200
            assert body == {"tip_index": 1, "tip_hash": seed.hash, "peer_count": 0, "mempool_size": 0}, body
            print("[ok] Stage 4: GET /v1/status")

            # --- GET /v1/balance/{address} ---------------------------------------
            status, body = await get(f"/v1/balance/{A}")
            assert status == 200 and body == {"address": A, "balance": BLOCK_REWARD, "nonce": 0}, body
            status, body = await get(f"/v1/balance/{B}")
            assert status == 200 and body == {"address": B, "balance": 0, "nonce": 0}, body
            status, body = await get("/v1/balance/not-an-address")
            assert status == 400 and "error" in body
            print("[ok] Stage 4: GET /v1/balance/{address} (known, unknown, malformed)")

            # --- GET /v1/block/{identifier} ----------------------------------------
            status, body = await get("/v1/block/1")
            assert status == 200 and Block.from_dict(body) == seed
            status, body = await get(f"/v1/block/{seed.hash}")
            assert status == 200 and Block.from_dict(body) == seed
            status, body = await get("/v1/block/0")
            assert status == 200 and Block.from_dict(body) == Block.genesis()
            for missing in ("99", "f" * 64, "nonsense"):
                status, body = await get(f"/v1/block/{missing}")
                assert status == 404 and "error" in body, (missing, status)
            status, body = await get("/v1/nope")
            assert status == 404 and "error" in body
            print("[ok] Stage 4: GET /v1/block/{identifier} by index and by hash, 404 when missing")

            # --- POST /v1/transaction (valid) ----------------------------------------
            tx1 = Transaction(A, B, 20, nonce=0).sign(alice)
            status, body = await post("/v1/transaction", tx1.to_json())
            assert status == 200 and body == {"tx_id": tx1.tx_id, "status": "accepted"}, body
            assert await mempool_size() == 1
            assert tx1 in node.mempool.get_all()

            # confirmed state is unchanged; the pending view accounts for tx1
            status, body = await get(f"/v1/balance/{A}")
            assert body["balance"] == BLOCK_REWARD and body["nonce"] == 0
            status, body = await get(f"/v1/balance/{A}?pending=true")
            assert status == 200 and body["balance"] == BLOCK_REWARD - 20 and body["nonce"] == 1, body

            # a second transaction chains on the pending nonce
            tx2 = Transaction(A, B, 5, nonce=1).sign(alice)
            status, body = await post("/v1/transaction", tx2.to_json())
            assert status == 200 and body["tx_id"] == tx2.tx_id, body
            assert await mempool_size() == 2
            print("[ok] Stage 4: POST /v1/transaction accepted; visible in mempool; pending nonce chaining")

            # --- POST /v1/transaction (invalid) -> 400, mempool untouched ---------------
            tampered = Transaction(A, B, 21, tx1.signature, tx1.timestamp, nonce=0)
            invalid_bodies = {
                "tampered amount (bad signature)": tampered.to_json(),
                "unsigned": Transaction(A, B, 1, nonce=2).to_json(),
                "wrong nonce": Transaction(A, B, 1, nonce=7).sign(alice).to_json(),
                "overspend": Transaction(A, B, 1000, nonce=2).sign(alice).to_json(),
                "duplicate": tx1.to_json(),
                "coinbase": Transaction.coinbase(A, BLOCK_REWARD).to_json(),
                "bad receiver": dumps({**tx1.to_dict(), "receiver": "nope"}),
                "missing fields": dumps({"sender": A}),
                "not an object": "[]",
                "not json": "this is not json",
                "empty body": "",
            }
            for label, payload in invalid_bodies.items():
                status, body = await post("/v1/transaction", payload)
                assert status == 400 and isinstance(body.get("error"), str), (label, status, body)
            assert await mempool_size() == 2
            print(f"[ok] Stage 4: {len(invalid_bodies)} kinds of invalid transaction rejected with HTTP 400")

            # --- POST /v1/mine: bad parameters ------------------------------------------
            for label, payload in {
                "difficulty is a string": dumps({"difficulty": "2"}),
                "difficulty is a bool": dumps({"difficulty": True}),
                "difficulty too high": dumps({"difficulty": MAX_API_DIFFICULTY + 1}),
                "negative difficulty": dumps({"difficulty": -1}),
                "bad reward address": dumps({"reward_address": "nope"}),
                "body not an object": "[1]",
                "body not json": "{",
            }.items():
                status, body = await post("/v1/mine", payload)
                assert status == 400 and "error" in body, (label, status, body)
            assert await mempool_size() == 2 and node.ledger.tip_index == 1

            # --- POST /v1/mine -------------------------------------------------------------
            status, body = await post("/v1/mine", dumps({"difficulty": 2, "reward_address": M}))
            assert status == 200, body
            mined = Block.from_dict(body)
            assert mined.verify_integrity() and mined.index == 2 and mined.prev_hash == seed.hash
            assert mined.difficulty == 2 and mined.hash.startswith("00")
            assert [t.tx_id for t in mined.transactions] == [mined.transactions[0].tx_id, tx1.tx_id, tx2.tx_id]
            assert mined.transactions[0].is_coinbase and mined.transactions[0].receiver == M

            status, body = await get("/v1/status")
            assert body["tip_index"] == 2 and body["tip_hash"] == mined.hash and body["mempool_size"] == 0, body
            status, body = await get(f"/v1/balance/{A}")
            assert body == {"address": A, "balance": BLOCK_REWARD - 25, "nonce": 2}, body
            status, body = await get(f"/v1/balance/{B}")
            assert body["balance"] == 25 and body["nonce"] == 0, body
            status, body = await get(f"/v1/balance/{M}")
            assert body["balance"] == BLOCK_REWARD, body
            status, body = await get("/v1/block/2")
            assert status == 200 and Block.from_dict(body) == mined
            print("[ok] Stage 4: POST /v1/mine created a valid block; mempool cleared; balances updated")

            # --- POST /v1/mine: nothing to mine ---------------------------------------------
            status, body = await post("/v1/mine")
            assert status == 400 and "empty" in body["error"], body
            assert node.ledger.tip_index == 2
            print("[ok] Stage 4: POST /v1/mine with an empty mempool returns HTTP 400")

    finally:
        await node.stop()

    assert node._api_runner is None and not node._connections
    print("[ok] Stage 4: node and client session shut down cleanly")


SCHEMA_VERSION = "1"

_SCHEMA_STATEMENTS = (
    'CREATE TABLE IF NOT EXISTS blocks ('
    ' "index" INTEGER PRIMARY KEY,'
    ' hash TEXT NOT NULL UNIQUE,'
    ' prev_hash TEXT NOT NULL,'
    ' data TEXT NOT NULL)',
    "CREATE TABLE IF NOT EXISTS state ("
    " address TEXT PRIMARY KEY,"
    " balance INTEGER NOT NULL,"
    " nonce INTEGER NOT NULL)",
    "CREATE TABLE IF NOT EXISTS mempool ("
    " tx_id TEXT PRIMARY KEY,"
    " data TEXT NOT NULL)",
    "CREATE TABLE IF NOT EXISTS metadata ("
    " key TEXT PRIMARY KEY,"
    " value TEXT NOT NULL)",
)


class DatabaseError(Exception):
    """Raised when the database cannot be opened/read/written or its contents are inconsistent."""


@dataclass
class StoredData:
    """Everything :meth:`Database.load` read from disk."""

    blocks: list[Block]                      # contiguous, genesis first (empty for a new database)
    state: dict[str, AccountState]           # contents of the ``state`` table
    mempool: list[Transaction]               # readable pending transactions
    invalid_mempool_ids: set[str] = field(default_factory=set)  # unreadable/mismatched mempool rows


class Database:
    """Async SQLite store for the chain, the account state and the mempool."""

    def __init__(self, path: str | os.PathLike[str]) -> None:
        self.path = os.fspath(path)
        self._conn: Optional[aiosqlite.Connection] = None
        self._lock = asyncio.Lock()  # one transaction at a time on the shared connection

    # ---- lifecycle ----------------------------------------------------------

    @property
    def is_open(self) -> bool:
        return self._conn is not None

    async def open(self) -> None:
        """Open (creating if needed) the database file and make sure the schema exists."""
        if self._conn is not None:
            return
        try:
            # isolation_level=None: autocommit mode, so BEGIN/COMMIT below are fully explicit.
            self._conn = await aiosqlite.connect(self.path, isolation_level=None)
        except (sqlite3.Error, OSError) as exc:
            raise DatabaseError(f"cannot open database {self.path}: {exc}") from exc
        try:
            try:
                await self._conn.execute("PRAGMA busy_timeout = 5000")
            except sqlite3.Error as exc:
                raise DatabaseError(f"cannot open database {self.path}: {exc}") from exc
            async with self._transaction() as conn:
                for statement in _SCHEMA_STATEMENTS:
                    await conn.execute(statement)
                await conn.execute(
                    "INSERT OR IGNORE INTO metadata (key, value) VALUES ('schema_version', ?)",
                    (SCHEMA_VERSION,),
                )
        except BaseException:
            await self.close()
            raise

    async def close(self) -> None:
        """Close the connection (waiting for any running transaction). Safe to call twice."""
        async with self._lock:
            conn, self._conn = self._conn, None
            if conn is not None:
                await conn.close()

    def _require_conn(self) -> aiosqlite.Connection:
        if self._conn is None:
            raise DatabaseError("database is closed")
        return self._conn

    @asynccontextmanager
    async def _transaction(self) -> AsyncIterator[aiosqlite.Connection]:
        """Run the body inside one SQLite transaction: COMMIT on success, ROLLBACK on any error."""
        async with self._lock:
            conn = self._require_conn()
            try:
                await conn.execute("BEGIN IMMEDIATE")
            except sqlite3.Error as exc:
                raise DatabaseError(f"cannot begin transaction: {exc}") from exc
            try:
                yield conn
                await conn.execute("COMMIT")
            except BaseException as exc:
                try:
                    await conn.execute("ROLLBACK")
                except Exception:  # noqa: BLE001 - nothing left to roll back / connection already broken
                    pass
                # OverflowError: a Python int too large for SQLite's 64-bit INTEGER
                if isinstance(exc, (sqlite3.Error, OverflowError)):
                    raise DatabaseError(f"database write failed: {exc}") from exc
                raise

    # ---- reading ------------------------------------------------------------

    async def load(self) -> StoredData:
        async with self._lock:
            conn = self._require_conn()
            try:
                async with conn.execute(
                    'SELECT "index", hash, prev_hash, data FROM blocks ORDER BY "index"'
                ) as cursor:
                    block_rows = await cursor.fetchall()
                async with conn.execute("SELECT address, balance, nonce FROM state") as cursor:
                    state_rows = await cursor.fetchall()
                async with conn.execute("SELECT tx_id, data FROM mempool ORDER BY rowid") as cursor:
                    mempool_rows = await cursor.fetchall()
                async with conn.execute("SELECT key, value FROM metadata") as cursor:
                    metadata = {key: value for key, value in await cursor.fetchall()}
            except sqlite3.Error as exc:
                raise DatabaseError(f"cannot read database {self.path}: {exc}") from exc

        if metadata.get("schema_version") != SCHEMA_VERSION:
            raise DatabaseError(f"unsupported database schema version: {metadata.get('schema_version')!r}")

        blocks: list[Block] = []
        for expected_index, (index, block_hash, prev_hash, data) in enumerate(block_rows):
            try:
                block = Block.from_json(data)
            except ValueError as exc:
                raise DatabaseError(f"stored block {index} is corrupt: {exc}") from exc
            if (
                index != expected_index
                or block.index != index
                or block.hash != block_hash
                or block.prev_hash != prev_hash
            ):
                raise DatabaseError(f"stored block row {expected_index} is inconsistent or the chain has a gap")
            blocks.append(block)
        if blocks and (
            metadata.get("tip_index") != str(blocks[-1].index) or metadata.get("tip_hash") != blocks[-1].hash
        ):
            raise DatabaseError("metadata tip does not match the last stored block")

        state = {address: {"balance": balance, "nonce": nonce} for address, balance, nonce in state_rows}

        mempool: list[Transaction] = []
        invalid: set[str] = set()
        for tx_id, data in mempool_rows:
            try:
                tx = Transaction.from_json(data)
            except ValueError:
                invalid.add(tx_id)
                continue
            if tx.tx_id != tx_id:
                invalid.add(tx_id)
            else:
                mempool.append(tx)
        return StoredData(blocks, state, mempool, invalid)

    # ---- writing (each method is one atomic transaction) --------------------------

    @staticmethod
    def _block_row(block: Block) -> tuple[int, str, str, str]:
        return block.index, block.hash, block.prev_hash, block.to_json()

    @staticmethod
    async def _write_accounts(conn: aiosqlite.Connection, accounts: dict[str, AccountState]) -> None:
        await conn.executemany(
            "INSERT OR REPLACE INTO state (address, balance, nonce) VALUES (?, ?, ?)",
            [(address, acct["balance"], acct["nonce"]) for address, acct in accounts.items()],
        )

    @staticmethod
    async def _set_tip(conn: aiosqlite.Connection, tip: Block) -> None:
        await conn.executemany(
            "INSERT OR REPLACE INTO metadata (key, value) VALUES (?, ?)",
            [("tip_index", str(tip.index)), ("tip_hash", tip.hash)],
        )

    @staticmethod
    async def _delete_mempool(conn: aiosqlite.Connection, tx_ids: Iterable[str]) -> None:
        await conn.executemany("DELETE FROM mempool WHERE tx_id = ?", [(tx_id,) for tx_id in tx_ids])

    async def initialize(self, chain: Sequence[Block], state: dict[str, AccountState]) -> None:
        """Write ``chain`` (genesis first) and ``state`` into an *empty* database."""
        if not chain:
            raise ValueError("chain must contain at least the genesis block")
        async with self._transaction() as conn:
            async with conn.execute("SELECT COUNT(*) FROM blocks") as cursor:
                row = await cursor.fetchone()
            if row is not None and row[0] != 0:
                raise DatabaseError("cannot initialise a database that already contains blocks")
            await conn.executemany(
                'INSERT INTO blocks ("index", hash, prev_hash, data) VALUES (?, ?, ?, ?)',
                [self._block_row(block) for block in chain],
            )
            await conn.execute("DELETE FROM state")
            await self._write_accounts(conn, state)
            await self._set_tip(conn, chain[-1])

    async def commit_block(
        self, block: Block, accounts: dict[str, AccountState], drop_tx_ids: Iterable[str]
    ) -> None:
        """Append ``block``, upsert the accounts it touched, move the tip, evict mempool rows.

        All or nothing. Fails (and changes nothing) if ``block`` does not extend
        the stored tip, which would mean memory and disk have diverged.
        """
        async with self._transaction() as conn:
            async with conn.execute('SELECT "index", hash FROM blocks ORDER BY "index" DESC LIMIT 1') as cursor:
                tip = await cursor.fetchone()
            if tip is None or tip[0] != block.index - 1 or tip[1] != block.prev_hash:
                raise DatabaseError(f"block {block.index} does not extend the stored chain tip")
            await conn.execute(
                'INSERT INTO blocks ("index", hash, prev_hash, data) VALUES (?, ?, ?, ?)',
                self._block_row(block),
            )
            await self._write_accounts(conn, accounts)
            await self._set_tip(conn, block)
            await self._delete_mempool(conn, drop_tx_ids)

    async def commit_reorg(
        self,
        ancestor_index: int,
        ancestor_hash: str,
        new_blocks: Sequence[Block],
        state: dict[str, AccountState],
        drop_tx_ids: Iterable[str],
    ) -> None:
        """Switch the stored chain to a fork, atomically.

        Deletes every block above the common ancestor, inserts ``new_blocks``,
        replaces the whole ``state`` table with ``state`` (the ledger state at the
        new tip), moves the tip and evicts ``drop_tx_ids`` from the mempool.
        """
        if not new_blocks or new_blocks[0].index != ancestor_index + 1:
            raise ValueError("new_blocks must be a non-empty run starting right after the ancestor")
        async with self._transaction() as conn:
            async with conn.execute('SELECT hash FROM blocks WHERE "index" = ?', (ancestor_index,)) as cursor:
                row = await cursor.fetchone()
            if row is None or row[0] != ancestor_hash:
                raise DatabaseError(f"common ancestor {ancestor_index} is not in the stored chain")
            await conn.execute('DELETE FROM blocks WHERE "index" > ?', (ancestor_index,))
            await conn.executemany(
                'INSERT INTO blocks ("index", hash, prev_hash, data) VALUES (?, ?, ?, ?)',
                [self._block_row(block) for block in new_blocks],
            )
            await conn.execute("DELETE FROM state")
            await self._write_accounts(conn, state)
            await self._set_tip(conn, new_blocks[-1])
            await self._delete_mempool(conn, drop_tx_ids)

    async def add_mempool_tx(self, tx: Transaction) -> None:
        """Store a pending transaction (no-op if it is already stored)."""
        async with self._transaction() as conn:
            await conn.execute(
                "INSERT OR IGNORE INTO mempool (tx_id, data) VALUES (?, ?)", (tx.tx_id, tx.to_json())
            )

    async def remove_mempool(self, tx_ids: Iterable[str]) -> None:
        """Delete pending transactions by id."""
        async with self._transaction() as conn:
            await self._delete_mempool(conn, tx_ids)


# =============================================================================
# STAGE 5 SELF-TEST
# =============================================================================


async def _self_test_stage_5() -> None:
    import tempfile

    difficulty = 0
    alice, bob, miner = KeyPair.generate(), KeyPair.generate(), KeyPair.generate()
    A, B, M = alice.address, bob.address, miner.address
    genesis = Block.genesis()

    def reward(address: str) -> Transaction:
        return Transaction.coinbase(address, BLOCK_REWARD)

    def pay(sender: KeyPair, receiver: str, amount: int, nonce: int) -> Transaction:
        return Transaction(sender.address, receiver, amount, nonce=nonce).sign(sender)

    def read_db(path: Path) -> dict[str, Any]:
        """Look at the file with plain sqlite3, independently of the Database class."""
        con = sqlite3.connect(path)
        try:
            return {
                "blocks": [row[0] for row in con.execute('SELECT hash FROM blocks ORDER BY "index"')],
                "state": {a: {"balance": b, "nonce": n} for a, b, n in con.execute("SELECT * FROM state")},
                "mempool": {row[0] for row in con.execute("SELECT tx_id FROM mempool")},
                "meta": dict(con.execute("SELECT key, value FROM metadata")),
            }
        finally:
            con.close()

    with tempfile.TemporaryDirectory() as tmp:
        db_path = Path(tmp) / "miniblock.db"

        def assert_disk_matches(node: Node) -> None:
            """The file must mirror the node's memory exactly (chain, state, mempool, tip)."""
            disk = read_db(db_path)
            assert disk["blocks"] == [b.hash for b in node.ledger.chain], "blocks table differs from chain"
            assert disk["state"] == node.ledger.state, "state table differs from ledger state"
            assert disk["mempool"] == {tx.tx_id for tx in node.mempool.get_all()}, "mempool table differs"
            assert disk["meta"]["tip_index"] == str(node.ledger.tip_index)
            assert disk["meta"]["tip_hash"] == node.ledger.tip_hash

        def new_node() -> Node:
            return Node(Ledger(), port=8765, api_port=None, db_path=db_path)

        # ---- run 1: build a chain, leave transactions pending, stop ---------------------
        assert not db_path.exists()
        node = new_node()
        await node.start()
        try:
            assert db_path.exists() and read_db(db_path)["blocks"] == [genesis.hash]   # initialised
            assert_disk_matches(node)

            block1 = await node.mine_pending(difficulty, reward_address=A)
            assert block1 is not None and block1.index == 1
            assert_disk_matches(node)

            tx1 = pay(alice, B, 20, 0)
            await node.submit_transaction(tx1)                         # API path -> mempool table
            assert tx1.tx_id in read_db(db_path)["mempool"]
            assert_disk_matches(node)

            block2 = await node.mine_pending(difficulty, reward_address=A)
            assert block2 is not None and tx1.tx_id in {t.tx_id for t in block2.transactions}
            assert read_db(db_path)["mempool"] == set()                # mined tx evicted from the table
            assert_disk_matches(node)

            tx2 = pay(bob, A, 5, 0)                                    # block 3 arrives from a "peer"
            block3 = mine_block(3, block2.hash, [reward(M), tx2], difficulty)
            await node._process_message(dumps({"type": "block", "data": block3.to_json()}))
            assert node.ledger.tip_hash == block3.hash
            assert_disk_matches(node)

            tx3 = pay(alice, B, 7, 1)                                  # pending, via the API path
            await node.submit_transaction(tx3)
            tx4 = pay(bob, M, 1, 1)                                    # pending, via the P2P path
            await node._process_message(dumps({"type": "tx", "data": tx4.to_json()}))
            assert {t.tx_id for t in node.mempool.get_all()} == {tx3.tx_id, tx4.tx_id}
            assert_disk_matches(node)

            expected_hashes = [b.hash for b in node.ledger.chain]
            expected_state = node.ledger.state
            assert node.ledger.tip_index == 3 and len(expected_hashes) == 4        # genesis + 3 blocks
            assert expected_state == {
                A: {"balance": 85, "nonce": 1},     # 50 + 50 - 20 + 5
                B: {"balance": 15, "nonce": 1},     # 20 - 5
                M: {"balance": 50, "nonce": 0},
            }
        finally:
            await node.stop()
        print("[ok] Stage 5: blocks, state, tip and mempool written to disk as they change")

        # ---- run 2: brand-new node, same file, no peers: everything must come back -------
        node = new_node()
        await node.start()
        try:
            assert node.ledger.tip_index == 3 and len(node.ledger.chain) == 4
            assert [b.hash for b in node.ledger.chain] == expected_hashes
            assert node.ledger.state == expected_state
            assert (node.ledger.get_balance(A), node.ledger.get_balance(B), node.ledger.get_balance(M)) == (85, 15, 50)
            assert {t.tx_id for t in node.mempool.get_all()} == {tx3.tx_id, tx4.tx_id}
            assert not node.bootstrap_peers and not node._connections            # nothing was synced
            assert_disk_matches(node)
            print("[ok] Stage 5: restarted node restored 3 blocks, balances and the pending mempool from disk")

            # reorganization: a longer fork off block 1. Fork block 3' mines tx3's rival (same
            # nonce), so tx3 becomes stale and must be pruned from memory *and* disk.
            fork2 = mine_block(2, block1.hash, [reward(M), pay(alice, M, 10, 0)], difficulty)
            fork3 = mine_block(3, fork2.hash, [reward(M), pay(alice, M, 3, 1)], difficulty)
            fork4 = mine_block(4, fork3.hash, [reward(M)], difficulty)

            def chain_message(blocks: list[Block]) -> str:
                return dumps({"type": "chain", "data": [b.to_json() for b in blocks]})

            await node._process_message(chain_message([block1, fork2, fork3]))      # same height: rejected
            assert node.ledger.tip_hash == block3.hash and node.ledger.tip_index == 3
            assert_disk_matches(node)

            await node._process_message(chain_message([block1, fork2, fork3, fork4]))   # longer: adopted
            assert node.ledger.tip_hash == fork4.hash and node.ledger.tip_index == 4
            assert [b.hash for b in node.ledger.chain] == [genesis.hash, block1.hash, fork2.hash, fork3.hash, fork4.hash]
            assert {t.tx_id for t in node.mempool.get_all()} == {tx4.tx_id}         # tx3 pruned (stale nonce)
            assert_disk_matches(node)
            disk = read_db(db_path)
            assert block2.hash not in disk["blocks"] and block3.hash not in disk["blocks"]   # orphans deleted
            assert disk["state"] == {
                A: {"balance": 37, "nonce": 2},     # 50 - 10 - 3
                M: {"balance": 163, "nonce": 0},    # 3 rewards + 10 + 3
            }
            assert disk["mempool"] == {tx4.tx_id}
        finally:
            await node.stop()
        print("[ok] Stage 5: reorganization deleted orphaned blocks, rewrote state and pruned the mempool on disk")

        # ---- run 3: the forked chain survives a restart; failure handling -----------------
        node = new_node()
        await node.start()
        try:
            assert node.ledger.tip_hash == fork4.hash and node.ledger.tip_index == 4
            assert {t.tx_id for t in node.mempool.get_all()} == {tx4.tx_id}
            assert_disk_matches(node)
            print("[ok] Stage 5: restarted node resumes on the forked chain")

            async def failing_write(*args: Any, **kwargs: Any) -> None:
                raise DatabaseError("simulated disk failure")

            # a failed reorg write must roll the in-memory ledger back too (and the undo data
            # rebuilt on startup must be good enough for the successful retry below)
            h4 = mine_block(4, fork3.hash, [reward(A)], difficulty)
            h5 = mine_block(5, h4.hash, [reward(A)], difficulty)
            before = (node.ledger.state, node.ledger.tip_hash, [b.hash for b in node.ledger.chain])
            node._db.commit_reorg = failing_write  # type: ignore[method-assign]
            await node._process_message(chain_message([fork3, h4, h5]))
            del node._db.commit_reorg
            assert (node.ledger.state, node.ledger.tip_hash, [b.hash for b in node.ledger.chain]) == before
            assert "database write failed" in (node.ledger.last_error or "")
            assert_disk_matches(node)
            await node._process_message(chain_message([fork3, h4, h5]))
            assert node.ledger.tip_hash == h5.hash and node.ledger.tip_index == 5
            assert node.ledger.get_balance(A) == 137 and node.ledger.get_balance(M) == 113
            assert_disk_matches(node)

            # a failed block write: mining returns None, the ledger and the file are unchanged
            node._db.commit_block = failing_write  # type: ignore[method-assign]
            assert await node.mine_pending(difficulty, reward_address=M) is None
            del node._db.commit_block
            assert node.ledger.tip_hash == h5.hash and "database write failed" in (node.ledger.last_error or "")
            assert_disk_matches(node)
            block6 = await node.mine_pending(difficulty, reward_address=M)
            assert block6 is not None and block6.index == 6
            assert_disk_matches(node)

            # the transaction really is atomic: the block INSERT succeeds, then a later statement
            # in the same transaction fails (balance too large for SQLite) -> nothing persists
            tip = node.ledger.chain[-1]
            phantom = mine_block(tip.index + 1, tip.hash, [reward(M)], difficulty)
            try:
                await node._db.commit_block(phantom, {M: {"balance": 2**70, "nonce": 0}}, set())
            except DatabaseError:
                pass
            else:
                raise AssertionError("an oversized balance should have failed the transaction")
            assert phantom.hash not in read_db(db_path)["blocks"]
            assert_disk_matches(node)
            gap = mine_block(tip.index + 2, phantom.hash, [reward(M)], difficulty)   # does not extend the tip
            try:
                await node._db.commit_block(gap, {}, set())
            except DatabaseError:
                pass
            else:
                raise AssertionError("a block that does not extend the stored tip must be refused")
            assert_disk_matches(node)
            # the failed transactions must have been rolled back, leaving the connection usable:
            # a normal write right afterwards succeeds and the phantom block never appears
            block7 = await node.mine_pending(difficulty, reward_address=M)
            assert block7 is not None and block7.index == 7 and block7.prev_hash == block6.hash
            assert phantom.hash not in read_db(db_path)["blocks"]
            assert_disk_matches(node)

            final_hashes = [b.hash for b in node.ledger.chain]
            final_state = node.ledger.state
            final_pending = {t.tx_id for t in node.mempool.get_all()}
            assert final_pending == {tx4.tx_id}
        finally:
            await node.stop()
        print("[ok] Stage 5: failed disk writes roll back memory; each write is a single atomic transaction")

        # ---- a tampered database is detected, and a failed start releases everything -------
        con = sqlite3.connect(db_path)
        con.execute("UPDATE state SET balance = balance + 1 WHERE address = ?", (M,))
        con.commit()
        con.close()
        node = new_node()
        try:
            await node.start()
        except DatabaseError as exc:
            assert "state table" in str(exc), exc
        else:
            await node.stop()
            raise AssertionError("a tampered state table must prevent start-up")
        assert node._server is None and node._db is None and not node._tasks
        con = sqlite3.connect(db_path)
        con.execute("UPDATE state SET balance = balance - 1 WHERE address = ?", (M,))
        con.commit()
        con.close()

        # ---- run 4: after repairing the file the node starts again, with everything intact ---
        node = new_node()
        await node.start()
        try:
            assert [b.hash for b in node.ledger.chain] == final_hashes
            assert node.ledger.state == final_state
            assert {t.tx_id for t in node.mempool.get_all()} == final_pending
            assert_disk_matches(node)
        finally:
            await node.stop()
        print("[ok] Stage 5: tampered database refused at start-up; repaired database loads cleanly")

        # ---- CLI wiring ------------------------------------------------------------------
        parser = _build_parser()
        assert parser.parse_args(["serve"]).db == DEFAULT_DB_PATH == "miniblock.db"
        assert parser.parse_args(["serve", "--db", "x.db"]).db == "x.db"
        print("[ok] Stage 5: `serve --db` argument")

    print("\nAll stage-5 self-tests passed.")


# =============================================================================
# MAIN ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    if len(sys.argv) > 1:
        sys.exit(_cli_main(sys.argv[1:]))

    print("Running Stage 1 Tests...")
    _self_test()

    print("\nRunning Stage 2 Tests...")
    _self_test_stage_2()

    print("\nRunning Stage 3 Tests (P2P Networking)...")
    asyncio.run(_self_test_stage_3())

    print("\nRunning Stage 4 Tests (HTTP API)...")
    asyncio.run(_self_test_stage_4())

    print("\nRunning Stage 5 Tests (Persistent Storage)...")
    asyncio.run(_self_test_stage_5())

    print("\nAll stages passed successfully! Your mini-blockchain node is fully functional.")