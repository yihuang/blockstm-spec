# Copilot Instructions

## Repository Overview

This repository contains TLA+ formal specifications for [BlockSTM](https://arxiv.org/abs/2203.06871), a parallel transaction execution engine. The specs model and verify the correctness of the multi-version memory approach used in BlockSTM.

## Specification Structure

- **`Store.tla`** — Base definitions: `Store` (total map Key → Val), `Overlay` (partial map Key → Val ∪ {NoVal}), and merge/apply helpers.
- **`Mem.tla`** — Multi-version memory: each transaction `i` has its own overlay `mem[i]`; reads find the nearest prior version.
- **`Tx.tla`** — Naive parallel model: all transactions run concurrently with re-execution on validation failure. Proves eventual consistency against sequential execution.
- **`Executor.tla`** — Concrete executor/scheduler model: shared `execution_idx` and `validation_idx` counters, per-executor task queues, and a commit phase.
- **`Tx_anim.tla`** / **`Executor_anim.tla`** — Animation helpers for the [Spectacle](https://github.com/will62794/spectacle) visualizer.
- **`Tx.cfg`** / **`Executor.cfg`** — TLC model checker configuration files (constants and properties).

## Key Concepts

- `NoVal` is a sentinel constant (not in `Val`) that represents deletion/absence of a key in an overlay.
- `Overlay` is a partial function `Key → Val ∪ {NoVal}`, modelled via `PFun` (partial functions as a union of total functions over subsets).
- `TxIndex == 1..BlockSize` — transactions are indexed starting at 1.
- Sequential execution state `SeqState(txn)` is the ground truth used for consistency checks.
- `CommittedTxn` is the largest index such that every transaction up to and including it has been cleanly executed and validated.

## Tooling

- **TLC model checker** via the `tla-bin` CLI (`tlc`) or the Nix package `nixpkgs#tlaplus`.
- Check a spec:
  ```
  tlc Tx.tla      # uses Tx.cfg
  tlc Executor.tla  # uses Executor.cfg
  ```
- **Spectacle** visualizer for live animation:
  ```
  git clone https://github.com/will62794/spectacle.git
  cd spectacle
  python3 serve.py --local_dir /path/to/blockstm-spec
  ```

## Conventions

- All module names match their file names exactly (TLA+ requirement).
- Use `INSTANCE` to compose modules (e.g., `Executor.tla` instantiates `Tx`, which in turn instantiates `Mem` and `Store`).
- Comments use the `\*` (single-line) and `(* ... *)` (block) TLA+ syntax.
- Properties are collected in a `Properties` operator and referenced in the `.cfg` file.
- Invariants and liveness properties are separated: invariants use `[]`, liveness uses `<>[]` or `~>`.
- Avoid introducing new CONSTANTS without updating the corresponding `.cfg` file.
