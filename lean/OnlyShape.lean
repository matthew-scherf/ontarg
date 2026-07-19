/-!
# OnlyShape

Classification of equivariant endomaps on a two- and three-element
alphabet.
-/

namespace OnlyShape

/-- An endomap of `Bool` commuting with `not` is `id` or `not`. -/
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

theorem constants_not_equivariant (c : Bool) :
    ¬ ∀ x, (fun _ => c) (!x) = !((fun _ => c) x) := by
  intro h
  have hc := h true
  revert hc; cases c <;> decide

inductive V3 where
  | t | b | f
deriving DecidableEq

open V3

/-- Swaps `t` and `f`, fixes `b`. -/
def neg : V3 → V3
  | t => f
  | b => b
  | f => t

theorem only_vacuum_self_negating : ∀ x, neg x = x ↔ x = b := by
  intro x; cases x <;> decide

/-- On `V3`, an endomap fixing `b`, commuting with `neg`, and not collapsing
    `t` to `b` is `id` or `neg`. -/
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

theorem id_generates_nothing : ∀ x : V3, id x = x := fun _ => rfl

theorem spec_forced :
    (∀ g : V3 → V3, g b = b → (∀ x, g (neg x) = neg (g x)) → g t ≠ b →
        (∀ x, g x = x) ∨ (∀ x, g x = neg x))
    ∧ (∀ x : V3, id x = x)
    ∧ (∀ x : V3, neg x = x ↔ x = b) :=
  ⟨equivariant_endomaps_V3, id_generates_nothing, only_vacuum_self_negating⟩

end OnlyShape

#print axioms OnlyShape.equivariant_endomaps
#print axioms OnlyShape.constants_not_equivariant
#print axioms OnlyShape.equivariant_endomaps_V3
#print axioms OnlyShape.only_vacuum_self_negating
#print axioms OnlyShape.id_generates_nothing
#print axioms OnlyShape.spec_forced
