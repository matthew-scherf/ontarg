/-!
# Cogito

`Occurs a := ∃ x, x = a`. Existence is contingent; validity of
occurrence, for any occupant of any type, is necessary.
-/

namespace Cogito

/-- Lawvere: if `e : A → A → Y` is point-surjective, every `f : Y → Y` has a fixed point. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) : ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

theorem doubt_has_no_fixpoint : ∀ b : Bool, not b ≠ b := by
  intro b; cases b <;> decide

theorem affirmation_is_fixed : ∀ b : Bool, id b = b := fun _ => rfl

/-- No total consistent self-doubt. -/
theorem the_gap {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

def Occurs {A : Type} (a : A) : Prop := ∃ x : A, x = a

theorem cogito {A : Type} (a : A) : Occurs a := ⟨a, rfl⟩

theorem no_self_denial {A : Type} (a : A) : ¬ ¬ Occurs a :=
  fun h => h (cogito a)

theorem existence_is_contingent : ∃ A : Type, A → False :=
  ⟨Empty, fun e => nomatch e⟩

theorem cogito_valid_necessarily {A : Type} (a : A) : Occurs a ∧ ¬ ¬ Occurs a :=
  ⟨cogito a, no_self_denial a⟩

theorem cogito_ergo_sum {A : Type} (a : A) :
    Occurs a
    ∧ ¬ ¬ Occurs a
    ∧ (∀ b : Bool, id b = b)
    ∧ (∀ b : Bool, not b ≠ b) :=
  ⟨cogito a, no_self_denial a, affirmation_is_fixed, doubt_has_no_fixpoint⟩

end Cogito

#print axioms Cogito.lawvere
#print axioms Cogito.the_gap
#print axioms Cogito.cogito
#print axioms Cogito.no_self_denial
#print axioms Cogito.existence_is_contingent
#print axioms Cogito.cogito_valid_necessarily
#print axioms Cogito.cogito_ergo_sum
