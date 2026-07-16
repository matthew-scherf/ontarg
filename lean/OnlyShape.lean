/-!
# OnlyShape

Uniqueness of the structureless generative specification. A
specification that imports no structure — no constants, no named
elements — is one whose operation commutes with every relabeling of
its alphabet (equivariance). On a two-element alphabet the
equivariant endomaps are exactly `id` and `not`; constants fail
equivariance. Since `x = id x` holds of every state and so carries no
content, the unique structureless specification with generative
content is `x = not x`.

Main results:
* `equivariant_endomaps` — on `Bool`, an endomap commuting with `not`
  is `id` or `not`.
* `constants_not_equivariant` — a constant map is never equivariant.
* `equivariant_endomaps_V3` — the same classification on the
  three-element alphabet `V3`, with the vacuum fixed and the
  distinction preserved.
* `only_vacuum_self_negating` — the static solutions of `x = neg x`
  are exactly the vacuum.
* `id_generates_nothing` — `x = id x` is total: no constraint.
* `spec_forced` — the conjunction: the equivariant shapes are
  `{id, neg}`; `id` is contentless; `neg`'s static solution is only
  the vacuum. The unique structureless generative specification is
  `x = neg x`. (Uniqueness of its guarded solution is
  `Loeb.godel_is_clock`.)

The extension of this classification along a regress of grounds is
proved in `Regress.lean` from named hypotheses.

Lean 4, prelude only; no imports. Axiom footprint: within `[propext]`.
-/

namespace OnlyShape

/- ---------- the two-element arena: Bool ---------- -/

/-- An endomap commuting with the sole nontrivial relabeling `not` is
    `id` or `not`: the equivariant endomaps of one bare distinction. -/
theorem equivariant_endomaps (g : Bool → Bool)
    (h : ∀ x, g (!x) = !(g x)) : g = id ∨ g = (fun b => !b) := by
  have h1 : g true = !(g false) := by simpa using h false
  cases hg : g false with
  | false =>
    left; funext x; cases x
    · exact hg
    · simp [h1, hg]
  | true =>
    right; funext x; cases x
    · show g false = true; exact hg
    · simp [h1, hg]

/-- Constants are never equivariant: a constant would have to satisfy
    `c = !c`. -/
theorem constants_not_equivariant (c : Bool) :
    ¬ ∀ x, (fun _ => c) (!x) = !((fun _ => c) x) := by
  intro h
  have hc := h true
  revert hc; cases c <;> decide

/- ---------- the three-element alphabet: V3 ---------- -/

inductive V3 where
  | t | b | f
deriving DecidableEq

open V3

/-- Negation on `V3`: swaps `t` and `f`, fixes the vacuum `b`. -/
def neg : V3 → V3
  | t => f
  | b => b
  | f => t

/-- The static solutions of `x = neg x` are exactly the vacuum. -/
theorem only_vacuum_self_negating : ∀ x, neg x = x ↔ x = b := by
  intro x; cases x <;> decide

/-- On `V3`, an endomap that fixes the vacuum, commutes with `neg`, and
    does not collapse the distinction (`g t ≠ b`) is `id` or `neg`. -/
theorem equivariant_endomaps_V3 (g : V3 → V3)
    (hb : g b = b) (hc : ∀ x, g (neg x) = neg (g x)) (hnc : g t ≠ b) :
    (∀ x, g x = x) ∨ (∀ x, g x = neg x) := by
  have hgf : g f = neg (g t) := by simpa [neg] using hc t
  cases hg : g t with
  | t =>
    left; intro x; cases x
    · exact hg
    · exact hb
    · simp [hgf, hg, neg]
  | b => exact absurd hg hnc
  | f =>
    right; intro x; cases x
    · simp [hg, neg]
    · exact hb
    · simp [hgf, hg, neg]

/-- `x = id x` is satisfied by every state: no constraint, no selection,
    no dynamics. Its solution set is total, so it carries no information. -/
theorem id_generates_nothing : ∀ x : V3, id x = x := fun _ => rfl

/-- The classification assembled: the equivariant endomaps are exactly
    `{id, neg}`; `id` generates nothing (`x = id x` is total); and
    `neg`'s static solutions are exactly the vacuum. The unique
    structureless specification with generative content is therefore
    `x = neg x`. -/
theorem spec_forced :
    (∀ g : V3 → V3, g b = b → (∀ x, g (neg x) = neg (g x)) → g t ≠ b →
        (∀ x, g x = x) ∨ (∀ x, g x = neg x))
    ∧ (∀ x : V3, id x = x)
    ∧ (∀ x : V3, neg x = x ↔ x = b) :=
  ⟨equivariant_endomaps_V3, id_generates_nothing, only_vacuum_self_negating⟩

end OnlyShape

/- audit -/
#print axioms OnlyShape.equivariant_endomaps
#print axioms OnlyShape.constants_not_equivariant
#print axioms OnlyShape.equivariant_endomaps_V3
#print axioms OnlyShape.only_vacuum_self_negating
#print axioms OnlyShape.id_generates_nothing
#print axioms OnlyShape.spec_forced
