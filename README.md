# The Ontological Argument of Becoming

One argument, machine-checked. An ontological argument derives an
existence verdict from a concept alone, a priori. The classical ones
start from the fullest concept — a maximally perfect being — and reach
for a necessary substance. This one starts from the emptiest, the
concept of *presuppositionlessness* (a specification that imports no
structure), and reaches a becoming rather than a being: on the bare
distinction exactly one structureless specification has content,
`x = ¬x`; read as an equation it has no solution (no being), read as a
recursion it has exactly one solution per seed, the two-tick clock
(unique becoming), and these two are provably one fact. The engine
throughout is Lawvere's diagonal at its fixed-point-free instance —
the wall of Cantor, Russell, Gödel and Turing — read for once as a
motor. The core is assembled, axiom-free, in
[`lean/Becoming.lean`](lean/Becoming.lean); the argument in full is in
[`ARGUMENT.md`](ARGUMENT.md) and [`paper/becoming.tex`](paper/becoming.tex).

## Contents

| Path | What it is |
|---|---|
| `ARGUMENT.md` | The argument in repository form: the five steps, each tagged and cited; the running-diagonal table; the graded ladder of actuality; how to check it |
| `paper/becoming.tex` | *The Ontological Argument of Becoming* — the paper, with the classical lineage (Anselm to Gödel), the objections, and the literature |
| `lean/` | Fifteen standalone Lean 4 proof files — prelude only, no imports, no dependencies. `Becoming.lean` assembles the argument; the other fourteen are the corpus results it cites |
| `reference/` | Read-only excerpts from the parent corpus (`TREATISE.md`, `paper.tex`) — context, not part of this argument |
| `lean-toolchain` | The pinned toolchain (`leanprover/lean4:v4.31.0`) |
| `SKILL.md` | Writing conventions used for the prose deliverables |

## Checking the proofs

Each file is self-contained and checks with plain `lean`:

```sh
lean lean/Becoming.lean                              # the assembled argument
for f in lean/*.lean; do lean "$f" || break; done    # all fifteen files
```

Every file ends with `#print axioms` for its main results.
`Becoming.lean` is axiom-free — its audit prints "does not depend on
any axioms" for every result. No file in the set goes beyond the
classical envelope `[propext, Classical.choice, Quot.sound]`; the
footprint is stated in each file header.

## Conventions

Every claim carries one of four tags, so its status is never implicit:

1. **forced** — carried by a machine-checked theorem, cited by file and name.
2. **free** — proved undecidable in the relevant vocabulary; the open
   status is itself the theorem.
3. **premise** — a named assumption joining a theorem to a reading,
   listed with what depends on it.
4. **interpretation** — a suggested reading of a theorem, severable
   from the mathematics.

The four core steps (Steps 1–4) are *forced* and axiom-free. The step
to actuality (Step 5) is graded, and each grade carries its price: a
conditional grade under four named premises, a tokened grade any denial
refutes in the act, and an enacted grade resting on a marked reading of
the kernel's own check. The claim is not that becoming is proved actual
without remainder — it is that the remainder is made exact.

## The wider corpus

These fifteen files are drawn from a larger machine-checked process
metaphysics — space, causation, records, mind, modality, free will, and
a companion ethics — in the sibling `metaphys` repository. This
repository carries only what the Ontological Argument of Becoming
cites, plus read-only excerpts of the parent under `reference/`.
