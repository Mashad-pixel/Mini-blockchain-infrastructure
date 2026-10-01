# miniblock

A complete, single-file mini-blockchain node written in Python. Built from scratch across 5 stages, it demonstrates cryptographic primitives, state management, P2P networking, a RESTful HTTP API, and persistent storage.

## Features

- **Stage 1: Cryptography & Data Models**: SHA-256 hashing, Ed25519 signatures, secure Merkle trees, and a canonical JSON codec that safely handles bytes and timezone-aware datetimes.
- **Stage 2: Ledger & State Management**: Account-based state tracking (balances and nonces), atomic block application, and robust chain reorganization (fork handling) with undo logs.
- **Stage 3: P2P Networking**: WebSocket-based gossip protocol for propagating transactions and blocks, with automatic chain synchronization.
- **Stage 4: HTTP REST API & CLI**: An `aiohttp` REST API served on the same async event loop as the P2P server, plus a command-line interface for wallet management and transaction submission.
- **Stage 5: Persistent Storage**: SQLite integration via `aiosqlite` to persist the blockchain, account state, and mempool, allowing the node to resume exactly where it left off after a restart.

## Prerequisites

- Python 3.10 or higher
