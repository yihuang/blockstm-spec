### CLI
https://github.com/pmer/tla-bin

For nix users:

```
$ nix profile install nixpkgs#tlaplus
```

Check model with tlc:
```
$ tlc Tx.tla
$ tlc -config MCTxAbort.cfg MCTx.tla
$ tlc -config MCTxAbortAlt.cfg MCTx.tla
$ tlc -config MCTxCommitFriendly.cfg MCTx.tla
```

### Specs

* `Tx.tla`

  naive model of running all transactions in parallel, prove eventual consistency.

  [live visualization](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FTx.tla&initPred=Init&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5)

* `MCTx.tla`

  deterministic scenario wrapper for focused model-checking.

  Single init modes: [InitAbortWitness](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCTx.tla&initPred=InitAbortWitness&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5) [InitAbortWitnessAlt](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCTx.tla&initPred=InitAbortWitnessAlt&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5) [InitCommitFriendly](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCTx.tla&initPred=InitCommitFriendly&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5)

* `Executor.tla`

  executor and scheduler

  [live visualization](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FExecutor.tla&initPred=Init&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BNoTask%5D=NoTask&constants%5BBlockSize%5D=5&constants%5BExecutors%5D=%7Be1%2Ce2%7D)

### Visualize

```
$ git clone https://github.com/will62794/spectacle.git
$ cd spectacle
$ python3 serve.py --local_dir /path/to/blockstm-spec
```

