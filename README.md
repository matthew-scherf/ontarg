# Ontology of Becoming

[![DOI](https://zenodo.org/badge/1302552048.svg)](https://doi.org/10.5281/zenodo.21449017)

Lean 4 formalization of an ontological argument whose ground concept is
discrimination on a carrier. The conditional core (L1–L3, Th. 1–4) is
proved in `lean/Becoming.lean`. The succession premise `P`, its
independence, the obstruction, orientation, and rigidity results
(Th. 5–7) are proved in `lean/Obstruction.lean`. Both files are
standalone (prelude only), declare no axioms, and end with
`#print axioms` audits.

## Results

| Claim | Lean |
|---|---|
| L1 Arena | `bare_one_is_mute`, `bare_three_is_mute`, `three_gives_third`, `three_values_are_still`, `two_at_most`, `two_swaps`, `two_speaks`, `moves_iff_two`; marked route: `marked_three_moves`, `marked_two_at_most`, `mark_is_fixed`, `mark_orbit_still`, `two_moves_the_mark`, `two_swaps_marked`, `mark_moves_iff_two`, `marked_refuses_iff_two` |
| L2 Uniqueness | `one_candidate`, `constants_not_structureless`, `id_says_nothing`, `id_graph_says_nothing`, `equivariant_iff_structureless`, `defble_classified`, `invariant_extends_defble`, `defble_extends_invariant` |
| L3 Retorsion | `retorsion`, `no_undrawn_denial` |
| Th. 1 | `no_being`, `no_being_eq`, `no_static_instance`, `no_fixpoint` |
| Th. 2 | `becoming_exists`, `becoming_unique`, `two_tick_clock`, `seed_is_relabel` |
| Th. 3 | `refusal_is_running` |
| Th. 4 | `event_retorsion`, `discrimination` |
| Th. 5 (from `P`) | `Successive`, `OrientedSuccessive`; `oriented_tick`, `oriented_chain_runs`, `actuality_tick`, `chain_runs` |
| Th. 6 | `obstruction`, `no_undeniable_bridge`, `obstruction_tensed`, `horn_two_is_premise`, `horn_two` |
| Th. 7 | `invariant_succ_symm`, `no_invariant_orientation`, `invariant_never_oriented`, `symmetric_never_oriented` |
| Independence of `P` | `premise_independent`, `chain_premise_independent`, `no_claim_settles_premise`, `oriented_premise_independent` |

`Becoming.ontological_argument` packages the principal conjuncts of the
conditional core.

## Contents

| Path | Description |
|---|---|
| `paper/becoming.tex` | Full paper |
| `paper/argument.tex` | One-page argument |
| `lean/Becoming.lean` | Conditional core |
| `lean/Obstruction.lean` | Premise, obstruction, orientation, rigidity |
| `lean-toolchain` | `leanprover/lean4:v4.31.0` |

## Checking

```sh
lean lean/Becoming.lean
lean lean/Obstruction.lean
```

Each `#print axioms` line reports no axiom dependencies (`propext`,
`Classical.choice`, `Quot.sound` unused). Shared helpers (`transp`,
`ne_eq_not`) are duplicated deliberately so the files remain standalone.
