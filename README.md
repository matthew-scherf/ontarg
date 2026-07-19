# An Ontological Proof of Becoming

*in the manner of Gödel's ontological proof (1970)*

One argument, machine-checked, with no premise at any link. An
ontological argument derives an existence verdict from a concept
alone, a priori. The classical ones start from the fullest concept — a
maximally perfect being — and reach for a necessary substance. This one
starts from the emptiest, the concept of *presuppositionlessness*, and
reaches a becoming rather than a being. The core is assembled,
axiom-free, in [`lean/Becoming.lean`](lean/Becoming.lean); the full
statement is [`paper/becoming.tex`](paper/becoming.tex), reproduced
below.

## The argument

**Primitive.** A *law* is a map `m` on a carrier. Write `Fix m` for "`m`,
read as an equation, has a solution" (∃x. x = mx), and `Run m` for "`m`,
read as a recursion, has a solution from every seed and none of them
is stationary" (for all x the sequence x, mx, m(mx), … is infinite and
no term equals the next).
<!--  -->
**Df. 1.** `m` is *structureless* iff `m` is definable from a bare
two-valued distinction alone, naming neither value: equivalently, `m`
commutes with the exchange of the two values.

**Df. 2.** A tokening is *absolute* iff its mark admits no outside: no
second locus, at the one time of the tokening, for its contrast to be
realized in.

**Df. 3.** `m` is *the ground* iff `m` is structureless and
non-trivial (not the identity).

**Ax. 1 (Arena).** A carrier admits a non-trivial structureless law
only if it has exactly two values. *(one value marks nothing; three or
more collapse every relabeling-invariant law to the identity)*

**Ax. 2 (Uniqueness).** On two values the only structureless laws are
the identity and the negation ¬; the identity is satisfied by
everything and so asserts nothing. Hence the ground, if it exists,
is ¬.

**Ax. 3 (Retorsion).** The tokening of "no distinction is drawn," as
against its own denial, itself draws one. The premise of Df. 2 cannot
be coherently refused — its negation is unsayable, not false.

**Ax. 4 (No margin).** An absolute tokening (Df. 2) has no outside at
its own moment; if its contrast is realized at all, it is realized at
another time.

**Th. 1 (No being).** ¬Fix(¬). *(the two values are distinct and each
fails its own negation; no state is identical to its own negation)*

**Th. 2 (Becoming, uniquely).** Run(¬), and the orbit from every seed
is the same period-two alternation, unique up to which value opens
it. *(write down x, ¬x, x, ¬x, …; uniqueness is induction on the
step)*

**Th. 3 (Equivalence).** For the ground, ¬Fix(¬) ↔ Run(¬). *(a fixed
point is a one-state orbit that never moves; a stalled orbit is a
fixed point: refusing to be and being unable to stop running are one
hypothesis, read in two frames)*

**Th. 4 (Actuality).** Let a tokening deny that ¬ runs. By Ax. 3 it is
tokened as against its own denial, hence is a tokening in the sense of
Df. 2, hence absolute; by Ax. 4 its contrast is realized at another
time; by Ax. 1–2 the only realizable contrast on two values is ¬
itself. So the tokened denial of Th. 2 is, at two times, an instance
of Th. 2.

**Corollary.** Necessarily, a becoming exists; by Th. 1 no being
answers to the ground concept; by Th. 3 these are one theorem; and by
Th. 4 the becoming cannot be coherently denied without the denial
itself being one of its ticks.

---

All of the above is a named theorem or definition of a Lean 4
development that is axiom-free at its core (`lean/Becoming.lean`,
theorem `Becoming.ontological_argument`) — Ax. 1–2 are theorems about
relabeling-invariant maps on finite carriers (`Arena.lean`,
`Structureless.lean`); Ax. 3–4 are theorems about what a totalizing
tokening can and cannot stand next to (`Tokening.lean`, `Event.lean`).
Where Gödel's proof needs the possibility of a maximally great being,
this proof needs only that some distinction, once denied, was thereby
drawn.

## Contents

| Path | What it is |
|---|---|
| `paper/becoming.tex` | *An Ontological Proof of Becoming* — the argument above, typeset |
| `lean/` | Twenty-five standalone Lean 4 proof files — prelude only, no imports, no dependencies. `Becoming.lean` assembles the argument; the other twenty-four are the corpus results it cites |
| `lean-toolchain` | The pinned toolchain (`leanprover/lean4:v4.31.0`) |

## Checking the proofs

Each file is self-contained and checks with plain `lean`:

```sh
lean lean/Becoming.lean                             # the assembled argument
for f in lean/*.lean; do lean "$f" || break; done   # every file
```

Every file ends with `#print axioms` for its main results.
`Becoming.lean`'s assembled theorem `ontological_argument` is
axiom-free — its audit prints "does not depend on any axioms". No file
in the set goes beyond the classical envelope
`[propext, Classical.choice, Quot.sound]`.

