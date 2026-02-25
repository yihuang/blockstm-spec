---------------------------- MODULE Executor_anim ----------------------------
EXTENDS TLC, FiniteSets, Executor

Merge(r1, r2) ==
    LET D1 == DOMAIN r1
        D2 == DOMAIN r2
    IN [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) ==
    [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText]

Rect(x, y, width, height, attrs) ==
    LET svgAttrs == [x |-> x, y |-> y, width |-> width, height |-> height]
    IN SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Text(x, y, txt, attrs) ==
    LET svgAttrs == [x |-> x, y |-> y]
    IN SVGElem("text", Merge(svgAttrs, attrs), <<>>, txt)

Group(children, attrs) == SVGElem("g", attrs, children, "")

TxStatusColor(st) ==
    IF st = "ReadyToExecute" THEN "#d1d5db"
    ELSE IF st = "Executed" THEN "#86efac"
    ELSE "#fca5a5"

TaskLabel(t) ==
    IF t = NoTask THEN
        "idle"
    ELSE
        t.kind \o " tx=" \o ToString(t.txn)

ExecutorCardColor(e) == IF terminated[e] THEN "#bbf7d0" ELSE "#e5e7eb"

ExecCols ==
    IF Executors <= 2 THEN Executors
    ELSE IF Executors <= 6 THEN 3
    ELSE 4

ExecCardWidth == 230
ExecCardHeight == 70
ExecColStep == 242
ExecRowStep == 82
ExecGridLeft == 16
ExecGridTop == 62

ExecRows == IF Executors = 0 THEN 0 ELSE ((Executors + ExecCols - 1) \div ExecCols)

TxCols ==
    IF BlockSize <= 4 THEN BlockSize
    ELSE IF BlockSize <= 12 THEN 6
    ELSE 8

TxBoxWidth == 100
TxBoxHeight == 48
TxColStep == 108
TxRowStep == 58
TxGridLeft == 16
TxGridTop == ExecGridTop + ExecRows * ExecRowStep + 84

LegendY == TxGridTop - 18

HeaderElems ==
    <<
        Text(16, 20, "Executor state", ("fill" :> "black" @@ "font-size" :> "14" @@ "font-family" :> "monospace")),
        Text(16, 40,
             "exec_idx=" \o ToString(execution_idx)
                \o "  val_idx=" \o ToString(validation_idx)
                \o "  active=" \o ToString(active_tasks)
                \o "  wave=" \o ToString(validation_wave),
             ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace"))
    >>

ExecutorCard(e) ==
    Group(
        <<
            Rect(0, 0, 230, 70, [fill |-> ExecutorCardColor(e), stroke |-> "black", rx |-> 8]),
            Text(10, 20, "Executor " \o ToString(e), ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace")),
            Text(10, 40, "task: " \o TaskLabel(tasks[e]), ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace")),
            Text(10, 58, "terminated: " \o ToString(terminated[e]), ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(" \o ToString(ExecGridLeft + ExecColStep * ((e - 1) % ExecCols)) \o "," \o ToString(ExecGridTop + ExecRowStep * ((e - 1) \div ExecCols)) \o ")"]
    )

ExecutorCards == [e \in 1..Executors |-> ExecutorCard(e)]

TxStatusBox(txn) ==
    Group(
        <<
            Rect(0, 0, 100, 48, [fill |-> TxStatusColor(execStatus[txn]), stroke |-> "black", rx |-> 6]),
            Text(8, 18, "tx=" \o ToString(txn), ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace")),
            Text(8, 34, execStatus[txn], ("fill" :> "black" @@ "font-size" :> "10" @@ "font-family" :> "monospace")),
            Text(8, 46, "inc=" \o ToString(incarnation[txn]), ("fill" :> "black" @@ "font-size" :> "10" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(" \o ToString(TxGridLeft + TxColStep * ((txn - 1) % TxCols)) \o "," \o ToString(TxGridTop + TxRowStep * ((txn - 1) \div TxCols)) \o ")"]
    )

TxStatusBoxes == [txn \in Tx!TxIndex |-> TxStatusBox(txn)]

Legend ==
    Group(
        <<
            Text(16, LegendY, "Tx status colors: gray=Ready, green=Executed, red=Aborting", ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(0,0)"]
    )

AnimView == Group(HeaderElems \o ExecutorCards \o <<Legend>> \o TxStatusBoxes, [transform |-> "scale(1.0)"])

=============================================================================