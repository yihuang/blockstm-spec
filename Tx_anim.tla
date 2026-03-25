------------------------------- MODULE Tx_anim -------------------------------
EXTENDS TLC, FiniteSets, Tx

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

StatusColor(st) ==
    IF st = "ReadyToExecute" THEN "#d1d5db"
    ELSE IF st = "Executed" THEN "#9ae6b4"
    ELSE "#fca5a5"

StatusLabel(st) ==
    IF st = "ReadyToExecute" THEN "Ready"
    ELSE IF st = "Executed" THEN "Executed"
    ELSE "Aborting"

PhaseLabel(i) ==
    IF i < commit_idx THEN "committed"
    ELSE IF i = commit_idx THEN "at-commit"
    ELSE "pending"

PhaseColor(i) ==
    IF i < commit_idx THEN "#86efac"
    ELSE IF i = commit_idx THEN "#fcd34d"
    ELSE "#bfdbfe"

TxNode(i) ==
    Group(
        <<
            Rect(0, 0, 120, 56, [fill |-> StatusColor(execStatus[i]), stroke |-> "black", rx |-> 8]),
            Text(8, 18, "Tx " \o ToString(i), ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace")),
            Rect(60, 6, 56, 12, [fill |-> PhaseColor(i), stroke |-> "black", rx |-> 3]),
            Text(63, 15, PhaseLabel(i), ("fill" :> "black" @@ "font-size" :> "8" @@ "font-family" :> "monospace")),
            Text(8, 34, StatusLabel(execStatus[i]), ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace")),
            Text(8, 50, "inc=" \o ToString(incarnation[i]), ("fill" :> "black" @@ "font-size" :> "11" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(" \o ToString(16 + 132 * (i - 1)) \o ",52)"]
    )

TxNodes == [i \in TxIndex |-> TxNode(i)]

Header ==
    Group(
        <<
            Text(16, 10, "commit_idx=" \o ToString(commit_idx), ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace")),
            Text(170, 10, "committed=" \o ToString(commit_idx - 1), ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace")),
            Text(340, 10, IF commit_idx = BlockSize + 1 THEN "terminal" ELSE "in-flight", ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(0,0)"]
    )

Legend ==
    Group(
        <<
            Text(16, 10, "Tx execution status", ("fill" :> "black" @@ "font-size" :> "12" @@ "font-family" :> "monospace")),
            Rect(16, 18, 10, 10, [fill |-> "#86efac", stroke |-> "black", rx |-> 2]),
            Text(30, 27, "committed", ("fill" :> "black" @@ "font-size" :> "10" @@ "font-family" :> "monospace")),
            Rect(116, 18, 10, 10, [fill |-> "#fcd34d", stroke |-> "black", rx |-> 2]),
            Text(130, 27, "at-commit", ("fill" :> "black" @@ "font-size" :> "10" @@ "font-family" :> "monospace")),
            Rect(222, 18, 10, 10, [fill |-> "#bfdbfe", stroke |-> "black", rx |-> 2]),
            Text(236, 27, "pending", ("fill" :> "black" @@ "font-size" :> "10" @@ "font-family" :> "monospace"))
        >>,
        [transform |-> "translate(0,16)"]
    )

AnimView ==
    Group(<<Header, Legend>> \o TxNodes, [transform |-> "scale(1.0)"])

=============================================================================