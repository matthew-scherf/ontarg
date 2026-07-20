# Ontology of Becoming

> the formal core is a set of Lean 4 theorems with no axioms; the
> regimentation, the empirical discharge, and the one premise per
> realized step are stated in prose

[![DOI](https://zenodo.org/badge/1302552048.svg)](https://doi.org/10.5281/zenodo.21449017)

An ontological argument analyzes a concept and derives an existence
verdict. The concept here is the bare capacity of a medium to mark one
proposition differently from another. The verdict has two parts with
different price tags: the structure of a two-state alternation, derived
as verified conditionals, and its realization in succession, which
costs a stated premise, proved independent.

## Argument

**Primitive.** A *law* is a map `m` on a carrier. `Fix m`: the equation
`x = m x` has a solution. `Run m`: the recursion is solved from every
seed and every term of every solution differs from its successor.

**Df.** `m` is *structureless* iff `m` commutes with every relabeling of
its carrier's values; on two values, with the exchange. On the
two-valued carrier this reading of "definable from a bare distinction"
coincides with definability, and the coincidence is a theorem.

**L1 (Arena, proved).** A carrier with decidable equality admits a
structureless law beyond the identity only when it has exactly two
values. *(one value admits one
map; three or more force the identity; a moved point and its image
exhaust the carrier)*

**L2 (Uniqueness, proved).** On two values the structureless laws are
the identity and negation; the identity holds of everything and singles
out nothing. A structureless law that excludes anything is `¬`.

**L3 (Retorsion, proved).** A tokening that marks "no distinction is
drawn" differently from its denial draws one. A discriminated tokening
of the denial makes the denial false.

**Th. 1 (No being).** `¬Fix(¬)`: each value differs from its own
negation, and `X = ¬X` has no solution.

**Th. 2 (Alternation).** `Run(¬)`; the orbit from each seed is the
period-two alternation, unique given the seed, and the two orbits are
relabelings of each other.

**Th. 3 (Equivalence).** `¬Fix(¬) ↔ Run(¬)`. *(the two sides quantify
over the same instances; each direction is instantiation)*

**Th. 4 (Discrimination).** A tokening that marks the denial of
occurrence differently from its assertion witnesses occurrence, and the
two tokens are distinct. On two values, "one negation apart" restates
"distinct," so occurrence is the theorem's whole yield.

**P (Succession: the premise).** The tokening of the denial and the
tokening of the assertion stand in succession. One instance per
realized step; the full run costs an infinite family of instances over
pairwise-distinct loci, and the orientation of the chain is part of
the premise. `P` is independent
of Th. 1–4: a still structure and a running one share one underlying
world and all tokening facts, with `P` false throughout one and true
throughout the other.

**Th. 5 (Actuality, from P).** Given discrimination and `P`, the
successor's value is the negation of its predecessor's: one realized
step of the alternation. A chain of instances realizes the run.

**Th. 6 (Obstruction).** Regiment claims as properties of
succession-free worlds. A claim true wherever its denial is
discriminated holds at still worlds that discriminate it; given any
such still world, the entailment from the claim to running fails.
Temporal realization rests on `P`, and, given such a world, an
undeniable substitute for `P` is unavailable.

**Corollary.** The alternation exists and is unique up to relabeling of
its seed, and nothing static answers to the ground concept (Th. 1–3). A
discriminated denial witnesses occurrence (Th. 4). Given `P`, each such
denial realizes a step of the alternation (Th. 5), and `P` is the exact
price of the temporal reading (Th. 6).

---

L1–L3 and Th. 1–4 are named theorems of `lean/Becoming.lean`, assembled
in `Becoming.ontological_argument`: L1 as `bare_one_is_mute`,
`bare_three_is_mute`, `two_at_most`, `two_speaks`; L2 as
`one_candidate`, `constants_not_structureless`; L3 as `retorsion`,
`no_undrawn_denial`; Th. 1 as `no_static_instance`, `no_being`; Th. 2
as `becoming_exists`, `becoming_unique`, `two_tick_clock`,
`seed_is_relabel`; Th. 3 as `refusal_is_running`; Th. 4 as
`event_retorsion`, `discrimination`.
Th. 5–6 and `P` live in `lean/Obstruction.lean`: `P` as the definition
`Successive`, hypothesized and never asserted; Th. 5 as
`actuality_tick`, `chain_runs`; Th. 6 as `obstruction`,
`no_undeniable_bridge`; independence as `premise_independent` and
`chain_premise_independent`.

## Contents

| Path | What it is |
|---|---|
| `paper/becoming.tex` | *Ontology of Becoming*: the full paper: regimentation, formal development, scope, obstruction, literature, verification notes |
| `paper/argument.tex` | *Ontology of Becoming*: the argument on one page |
| `lean/Becoming.lean` | The conditional core: standalone Lean 4, prelude only, no imports |
| `lean/Obstruction.lean` | The obstruction, the premise, its independence, and rigidity: same discipline |
| `lean-toolchain` | The pinned toolchain (`leanprover/lean4:v4.31.0`) |

## Checking the proofs

Both files are self-contained and check with plain `lean`:

```sh
lean lean/Becoming.lean
lean lean/Obstruction.lean
```

Each file ends with a `#print axioms` audit of its main results, 30
lines in the first file and 17 in the second. Every line prints "does
not depend on any axioms": the development declares no axiom and uses
none of Lean's three standard ones (`propext`, `Classical.choice`,
`Quot.sound`). The material is finite case analysis
and induction over decidable types, for which the empty footprint is
the expected outcome; the audit records it.
