/-!
# OneDiagonal

The Lawvere fixed-point theorem and its negative instance.

Main results:
* `lawvere` — a point-surjective self-enumeration gives every endomap
  a fixed point (Lawvere 1969).
* `diagonal_no_go` — no self-enumeration into `Bool` is point-surjective.
* `impossibilities_identical` — any two false propositions are equal.

Lean 4, prelude only; no imports. Axiom footprint: at most `propext`.
-/

namespace OneDiagonal

/-- Lawvere (1969). If a carrier `A` enumerates its own maps into `Y`
    point-surjectively, then every endomap of `Y` has a fixed point,
    witnessed by the diagonal `g a := f (e a a)`. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) :
    ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

/-- The instance at `f = not`, which is fixed-point-free: no
    self-enumeration into `Bool` is point-surjective. This is the
    common core of the Cantor, Russell, Tarski, and halting arguments. -/
theorem diagonal_no_go {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

/-- Any two false propositions are equal (`propext`). -/
theorem impossibilities_identical (P Q : Prop) (hp : ¬P) (hq : ¬Q) :
    P = Q := propext ⟨fun p => (hp p).elim, fun q => (hq q).elim⟩

end OneDiagonal
#print axioms OneDiagonal.lawvere
#print axioms OneDiagonal.diagonal_no_go
#print axioms OneDiagonal.impossibilities_identical
