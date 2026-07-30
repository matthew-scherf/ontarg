# Undeniability Does Not Yield Succession

[![DOI](https://zenodo.org/badge/1302552048.svg)](https://doi.org/10.5281/zenodo.21449017)

A tokening that marks the denial of occurrence differently from its
assertion witnesses occurrence. Temporal succession is another matter:
if claims are properties of succession-free worlds, no undeniable claim
can entail running. An oriented succession premise `P` is independent of
every claim true at a two-model witness, and on loci with decidable
equality every relabeling-invariant succession is symmetric.

Lead paper: `paper/undeniability.tex`. Formal results live in two
standalone Lean 4 files (prelude only; no imports; no axioms; `#print
axioms` audits at the end of each).

## Results

| Claim | Lean |
|---|---|
| Discrimination | `event_retorsion`, `discrimination` |
| Freeze / two models | `freeze`, `two_models` |
| Obstruction | `obstruction`, `still_never_runs`, `no_undeniable_bridge` |
| Premise `P` | `Successive`, `OrientedSuccessive`; `oriented_tick`, `oriented_chain_runs` |
| Independence of `P` | `premise_independent`, `premise_fails_still`, `premise_holds_running`, `no_claim_settles_premise`, `oriented_premise_independent` |
| Orientation | `invariant_succ_symm`, `no_invariant_orientation`, `invariant_never_oriented` |
| Regimentation dilemma | `obstruction_tensed`, `horn_two_is_premise`, `horn_two` |

Structural background (two-valued arena, uniqueness of complement, fixed-point
freeness, period-two alternation) is in `lean/Becoming.lean` and is summarized
in the paper; it does not yield succession.

## Contents

| Path | Description |
|---|---|
| `paper/undeniability.tex` | Limit paper (lead) |
| `paper/becoming.tex` | Longer companion: structural development |
| `paper/argument.tex` | One-page summary of the structural argument |
| `lean/Becoming.lean` | Conditional structural core |
| `lean/Obstruction.lean` | Worlds, obstruction, `P`, independence, orientation |
| `lean-toolchain` | `leanprover/lean4:v4.31.0` |

## Checking

```sh
lean lean/Becoming.lean
lean lean/Obstruction.lean
```

Each `#print axioms` line reports no axiom dependencies (`propext`,
`Classical.choice`, `Quot.sound` unused). Shared helpers (`transp`,
`ne_eq_not`) are duplicated deliberately so the files remain standalone.
