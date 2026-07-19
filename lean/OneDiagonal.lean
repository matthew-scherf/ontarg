/-!
# OneDiagonal

The Lawvere fixed-point theorem and its negative instance.
-/

namespace OneDiagonal

/-- If `e : A → A → Y` is point-surjective, every endomap of `Y` has a fixed point. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) :
    ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

/-- No self-enumeration into `Bool` is point-surjective. -/
theorem diagonal_no_go {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

theorem impossibilities_identical (P Q : Prop) (hp : ¬P) (hq : ¬Q) :
    P = Q := propext ⟨fun p => (hp p).elim, fun q => (hq q).elim⟩

end OneDiagonal
#print axioms OneDiagonal.lawvere
#print axioms OneDiagonal.diagonal_no_go
#print axioms OneDiagonal.impossibilities_identical
