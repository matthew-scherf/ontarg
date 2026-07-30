# Ontology of Becoming

[![DOI](https://zenodo.org/badge/1302552048.svg)](https://doi.org/10.5281/zenodo.21449017)

Lean~4 formalization of an ontological argument whose ground is discrimination
on a carrier. The **complete picture** is one two-part argument; the
**machine-checked spine** is three standalone Lean files.

## The picture

| Part | Claim | Lean | Does it use premise `P`? |
|---|---|---|---|
| **I — Limit** | Discrimination yields occurrence, not succession. Under a succession-blind claim language, no undeniable claim entails running; oriented succession premise `P` is independent of every claim. | `Becoming.lean` (L1–L3, Th.~1–4), `Obstruction.lean` (Th.~5–7, independence) | `P` is the priced joint for tensed succession |
| **II — Cut** | Absolute := cut := Boolean `not` (unique self-dual excluding law). Absolute models are runs of `not`. Still/world structure remains as non-absolute. | `Cut.lean` | No — packages `Run(¬)` under the cut identification |

Part~II does **not** overcome Part~I. It changes the type of absolute status.
Public language is **absolute** / **cut** (not deity-names). The named stance of
Part~II is: absolute = cut = `not`.

### Cut conclusion (posterity)

Under that identification: the cut is self-dual, involutive, and fixed-point-free;
`X ↔ ¬X` is unsatisfiable; every seed determines a unique period-2 absolute
model; no constant sequence is an absolute model. Still tensed structures can
exist as a different kind. Not concluded: succession from claims, oriented
time, or that a deity exists.

## How to present

| Form | Use |
|---|---|
| **One narrative paper** | Preferred complete picture: limit then cut (`paper/becoming.tex` is the natural home; fold in cut material as Part~II) |
| **Short extracts** | `paper/undeniability.tex` (limit only), `paper/cut.tex` (cut only) |
| **One-pager** | `paper/argument.tex` |
| **Lean** | Keep three files — do not merge; separation mirrors the two parts |

## Lean spine

All three files are **standalone** (prelude only, no imports, no axioms).
Helpers are duplicated on purpose. Check each file on its own:

```sh
lean lean/Becoming.lean
lean lean/Obstruction.lean
lean lean/Cut.lean
```

Toolchain: `leanprover/lean4:v4.31.0` (`lean-toolchain`).

## Results (Part I — limit)

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
conditional core (Th.~1–4 side).

## Results (Part II — cut)

| Claim | Lean |
|---|---|
| Self-duality | `SelfDual`, `not_selfDual`, `selfDual_dichotomy` |
| Absolute = cut = `not` | `absolute`, `absolute_selfDual`, `absolute_involutive`, `absolute_no_fixpoint` |
| Unique self-dual excluder | `absolute_unique_excluding` |
| Absolute models | `AbsoluteModel`, `absoluteModel_orbit`, `absoluteModel_unique`, `absolute_period_two` |
| No static absolute | `no_static_absoluteModel` |
| Package | `absolute_as_cut` |

## Contents

| Path | Description |
|---|---|
| `paper/becoming.tex` | Full narrative (target home for Parts I–II) |
| `paper/undeniability.tex` | Limit extract |
| `paper/cut.tex` | Cut extract |
| `paper/argument.tex` | One-page summary (both tracks) |
| `lean/Becoming.lean` | Conditional core (L1–L3, Th.~1–4) |
| `lean/Obstruction.lean` | Premise `P`, obstruction, orientation, rigidity (Th.~5–7) |
| `lean/Cut.lean` | Process-first absolute package |
| `lean-toolchain` | `leanprover/lean4:v4.31.0` |

## Still priced (outside the cut package)

Oriented succession, infinite injective runs beyond the Bool clock, felt
passage, and physics / measurement dictionaries. Orientation theorems remain
in `Obstruction.lean` (Th.~7).
