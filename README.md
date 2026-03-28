### CLI
https://github.com/pmer/tla-bin

For nix users:

```
$ nix profile install nixpkgs#tlaplus
```

Check model with tlc:
```
$ tlc Tx.tla
$ tlc -config MCDependencyAbort.cfg MCDependency.tla
$ tlc -config MCDependencyAbortAlt.cfg MCDependency.tla
$ tlc -config MCDependencyNoConflict.cfg MCDependency.tla
```

### Specs

* `Tx.tla`

  naive model of running all transactions in parallel, prove eventual consistenccy.

  [live visualization](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FTx.tla&initPred=Init&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5)

* `Executor.tla`

  executor and scheduler

  [live visualization](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FExecutor.tla&initPred=Init&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BNoTask%5D=NoTask&constants%5BBlockSize%5D=5&constants%5BExecutors%5D=%7Be1%2Ce2%7D)

* `Dependency.tla`

  push validation model with dependency tracking and scheduling.

  Single init modes via `MCDependency.tla`: [InitAbortWitness](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCDependency.tla&initPred=InitAbortWitness&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5) [InitAbortWitnessAlt](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCDependency.tla&initPred=InitAbortWitnessAlt&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5) [InitNoConflict](https://mmsqe.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fyihuang%2Fblockstm-spec%2Frefs%2Fheads%2Fmain%2FMCDependency.tla&initPred=InitNoConflict&nextPred=Next&constants%5BKey%5D=%7Bk1%7D&constants%5BNoVal%5D=NoVal&constants%5BBlockSize%5D=5)

### Visualize

```
$ git clone https://github.com/will62794/spectacle.git
$ cd spectacle
$ python3 serve.py --local_dir /path/to/blockstm-spec
```

