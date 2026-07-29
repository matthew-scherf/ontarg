# Ontology of Becoming

> the formal core is a set of Lean 4 theorems with no axioms; the
> regimentation, the empirical discharge, and the one premise per
> realized step are stated in prose

[![DOI](https://zenodo.org/badge/1302552048.svg)](https://doi.org/10.5281/zenodo.21449017)

An ontological argument analyzes a concept and derives an existence
verdict. The concept here is the bare capacity of a medium to mark one
proposition differently from another. The verdict has two parts with
separate prices: the structure of a two-state alternation, derived as
verified conditionals, and its realization in succession, which costs a
stated premise of proved independence.

## Argument

**Primitive.** A *law* is a map `m` on a carrier. `Fix m`: the equation
`x = m x` has a solution. `Run m`: the recursion is solved from every
seed, and every term of every solution differs from its successor.

**Df.** `m` is *structureless* when `m` commutes with every relabeling of
its carrier's values; on two values, with the exchange. On the
two-valued carrier this reading of "definable from a bare distinction"
coincides with definability, and the coincidence is a theorem.

**L1 (Arena, proved).** A carrier with decidable equality admits a
structureless law beyond the identity exactly when it holds two values.
*(one value admits one map; three pairwise-distinct values force the
identity; a moved point and its image exhaust the carrier; on two, the
exchange is structureless and moves both)* Marking one value leaves the
relabelings that fix it, and the same equivalence holds under that
weaker demand: a mark-respecting law moves the mark, or moves every
value, exactly on two.

**L2 (Uniqueness, proved).** On two values the structureless laws are
the identity and complement. The graph of the identity excludes nothing.
A structureless law that excludes anything is complement.

**L3 (Retorsion, proved).** A tokening that marks "no distinction is
drawn" differently from its denial draws one. The conjunction of a
discriminated tokening of the denial with the denial is refuted.

**Th. 1 (No being).** `¬Fix(¬)`: each value differs from its own
complement, and `X ↔ ¬X` has no solution in `Prop`.

**Th. 2 (Alternation).** `Run(¬)`; the orbit from each seed is the
period-two alternation, unique given the seed, and the two orbits are
relabelings of each other.

**Th. 3 (Equivalence).** `¬Fix(¬) ↔ Run(¬)`. *(the two sides quantify
over the same instances; each direction is instantiation)*

**Th. 4 (Discrimination).** A tokening that marks the denial of
occurrence differently from its assertion witnesses occurrence, and the
two tokenings are distinct. On two values, "one complement apart"
restates "distinct," so occurrence is the theorem's whole yield.

**P (the premise).** The tokening of the denial and the tokening of the
assertion stand in oriented succession, the first succeeded by the
second and the reverse failing. One instance per realized step; the full
run adds an infinite supply of pairwise-distinct loci and a
discrimination at every step. `P` is independent of Th. 1-4: two
structures over one world satisfy exactly the same claims, with `P`
false throughout one and true in the other, so no claim entails `P` and
no claim refutes `P`. The independence holds relative to the world
signature `(T, h, tok)`.

**Th. 5 (Actuality, from P).** Given discrimination and one oriented
instance, the two loci are distinct, the successor's value is the
complement of its predecessor's, and the structure fails to be still. A
chain of oriented instances realizes the run.

**Th. 6 (Obstruction).** Regiment claims as properties of
succession-free worlds. A claim true wherever its denial is
discriminated holds at still worlds that discriminate that denial; given
any such still world, the entailment from the claim to running fails.
Temporal realization rests on `P`, and, given such a world, an
undeniable substitute for `P` is unavailable. A still world that does
discriminate is exhibited by ostension.

**Th. 7 (Orientation).** On loci with decidable equality, every
relabeling-invariant succession is symmetric, so no invariant succession
holds of a pair while failing of the reverse pair. Direction is
unavailable from invariance, which is where the orientation clause of
`P` earns its place.

**Corollary.** The alternation exists and is unique up to relabeling of
its seed, and nothing static answers to the ground concept (Th. 1-3). A
discriminated denial witnesses occurrence (Th. 4). Given `P`, each such
denial realizes a step of the alternation (Th. 5), and `P` is the exact
price of the temporal reading (Th. 6-7).

## Ledger

1. **Verified conditionals**: the formal results, with an empty axiom
   footprint.
2. **Five regimentation choices**: ground as law, structureless as
   equivariant, groundhood as exclusion, satisfaction as objectual or
   processual, claims as properties of succession-free worlds.
3. **One empirical input**: the actual world contains a tokening that
   discriminates the pair, discharged once by ostension; the
   discrimination at every step in item 4 is empirical too, and it is
   counted there with the premise.
4. **The premise `P`**: one oriented instance per realized step; the
   full run adds an infinite supply of pairwise-distinct loci and a
   discrimination at every step.
5. **A consistent constructive metalogic.**

## Where the results live

L1-L3 and Th. 1-4 are named theorems of `lean/Becoming.lean`: L1 as
`bare_one_is_mute`, `bare_three_is_mute`, `three_gives_third`,
`three_values_are_still`,
`two_at_most`, `two_swaps`, `two_speaks`, `moves_iff_two`, with the
marked route as `marked_three_moves`, `marked_two_at_most`,
`mark_is_fixed`, `mark_orbit_still`, `two_moves_the_mark`,
`two_swaps_marked`, `mark_moves_iff_two`, `marked_refuses_iff_two`; L2
as `one_candidate`, `constants_not_structureless`, `id_says_nothing`,
`id_graph_says_nothing`, with the coincidence of equivariance and
structurelessness as `equivariant_iff_structureless` and the
definability classification as `defble_classified`,
`invariant_extends_defble`, `defble_extends_invariant`; L3 as
`retorsion`, `no_undrawn_denial`; Th. 1 as `no_being`, `no_being_eq`,
with the Boolean fixed-point facts as `no_static_instance`,
`no_fixpoint`; Th. 2 as `becoming_exists`, `becoming_unique`,
`two_tick_clock`, `seed_is_relabel`; Th. 3 as `refusal_is_running`;
Th. 4 as `event_retorsion`, `discrimination`.

`Becoming.ontological_argument` is one term whose type is a conjunction
assembled from those results. Of the declarations listed above, these
are named, proved, and audited in the file outside that term:
`three_gives_third`, `three_values_are_still`, `two_at_most`,
`two_swaps`, `marked_two_at_most`, `two_swaps_marked`,
`equivariant_iff_structureless`, `defble_classified`,
`invariant_extends_defble`, `defble_extends_invariant`,
`no_undrawn_denial`, `no_being_eq`, `event_retorsion`. The rest are
conjuncts of it.

Th. 5-7 and `P` live in `lean/Obstruction.lean`: `P` as the definitions
`Successive` and `OrientedSuccessive`, hypothesized and never asserted;
Th. 5 as `oriented_tick`, `oriented_chain_runs`, with the undirected
unpackings `actuality_tick`, `chain_runs`; Th. 6 as `obstruction`,
`no_undeniable_bridge`, with the tensed horn as `obstruction_tensed` and
the second horn as `horn_two_is_premise`, `horn_two`; Th. 7 as
`invariant_succ_symm`, `no_invariant_orientation`,
`invariant_never_oriented`, `symmetric_never_oriented`; independence as
`premise_independent`, `chain_premise_independent`,
`no_claim_settles_premise`, `oriented_premise_independent`. Running
costs loci before it costs succession: `two_loci_never_run`,
`running_witness_never_runs`. On loci with decidable equality, a
succession blind to which locus is which is one of four relations, and
disagreement once it excludes anything: `invariant_succ_classified`,
`invariant_says_is_ne`.

## Contents

| Path | What it is |
|---|---|
| `paper/becoming.tex` | *Ontology of Becoming*: the full paper: regimentation, formal development, scope, obstruction, the regimentation dilemma, literature, verification notes |
| `paper/argument.tex` | *Ontology of Becoming*: the argument in brief |
| `lean/Becoming.lean` | The conditional core: standalone Lean 4, prelude only, no imports |
| `lean/Obstruction.lean` | The obstruction, the premise, its independence, orientation, and rigidity: same discipline |
| `lean-toolchain` | The pinned toolchain (`leanprover/lean4:v4.31.0`) |

## Checking the proofs

Both files are self-contained and check with plain `lean`:

```sh
lean lean/Becoming.lean
lean lean/Obstruction.lean
```

Each file ends with a `#print axioms` audit of its results, 52 lines in
the first file and 47 in the second. Every line prints "does not depend
on any axioms": the development declares no axiom and uses none of
Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`).
The material is finite case analysis and induction over decidable types,
for which the empty footprint is the expected outcome; the audit records
it. The two files are standalone, so shared material is duplicated
deliberately: `transp` with its lemmas and `ne_eq_not` appear in both.
