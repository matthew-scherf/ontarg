# The Ontological Argument of Becoming

One argument, machine-checked, with no premise at any link. An
ontological argument derives an existence verdict from a concept
alone, a priori. The classical ones start from the fullest concept — a
maximally perfect being — and reach for a necessary substance. This one
starts from the emptiest, the concept of *presuppositionlessness* (a
specification that imports no structure), and reaches a becoming rather
than a being: any tokening of a claim already draws a distinction, and
the denial of that is unsayable; the arena of a drawn distinction is
two-valued by theorem, not by choice; on it exactly one structureless
specification has content, `x = ¬x`; read as an equation it has no
solution (no being), read as a recursion it has exactly one solution
per seed, the two-tick clock (unique becoming); these two are provably
one fact; and the seed itself is a label, not an assumption. The engine
throughout is Lawvere's diagonal at its fixed-point-free instance —
the wall of Cantor, Russell, Gödel and Turing — read for once as a
motor. The core is assembled, axiom-free, in
[`lean/Becoming.lean`](lean/Becoming.lean); the argument in full is in
[`ARGUMENT.md`](ARGUMENT.md) and [`paper/becoming.tex`](paper/becoming.tex).

## Contents

| Path | What it is |
|---|---|
| `ARGUMENT.md` | The argument in repository form: the eight steps, each tagged and cited; the running-diagonal table; the graded ladder of actuality; why there are no premises; how to check it |
| `paper/becoming.tex` | *The Ontological Argument of Becoming* — the paper, with the classical lineage (Anselm to Gödel), the objections, and the literature |
| `lean/` | Twenty-one standalone Lean 4 proof files — prelude only, no imports, no dependencies. `Becoming.lean` assembles the argument; the other twenty are the corpus results it cites |
| `lean-toolchain` | The pinned toolchain (`leanprover/lean4:v4.31.0`) |

## Checking the proofs

Each file is self-contained and checks with plain `lean`:

```sh
lean lean/Becoming.lean                              # the assembled argument
for f in lean/*.lean; do lean "$f" || break; done    # all twenty-one files
```

Every file ends with `#print axioms` for its main results.
`Becoming.lean`'s assembled theorem `ontological_argument` is
axiom-free — its audit prints "does not depend on any axioms". No file
in the set goes beyond the classical envelope
`[propext, Classical.choice, Quot.sound]`; the footprint is stated in
each file header.

## Conventions

Every claim carries one of three tags, so its status is never implicit:

1. **forced** — carried by a machine-checked theorem, cited by file and name.
2. **free** — proved undecidable in the relevant vocabulary; the open
   status is itself the theorem.
3. **interpretation** — a suggested reading of a theorem, severable
   from the mathematics.

Earlier versions carried a fourth tag, **premise**, and used it four
times (R1–R4), plus a residue on the reading of the classification.
No claim carries it now: each former premise is a theorem, a hypothesis
the result is stronger without, or a condition whose denial cannot be
tokened. The criterion under which that is claimed — and the one place
to press on it — is set out in *Why there are no premises* in
[`ARGUMENT.md`](ARGUMENT.md).

The seven core steps (Steps 1–7) are *forced* and assembled axiom-free.
The step to actuality (Step 8) is graded, and each grade carries its
price: a premise-free grade about articulations and demand chains, a
tokened grade any denial refutes in the act, and an enacted grade
resting on a marked reading of the kernel's own check. The claim is not
that becoming is proved actual without remainder — it is that the
remainder is made exact.

## The wider corpus

These twenty-one files are drawn from a larger machine-checked process
metaphysics — space, causation, records, mind, modality, free will, and
a companion ethics — in the sibling `metaphys` repository. This
repository carries only what the Ontological Argument of Becoming
cites.
