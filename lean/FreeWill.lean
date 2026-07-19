/-!
# FreeWill

A choice is a Boolean coordinate whose actual next value is
`not` of the system's own prediction of it.

Axiom footprint: none.
-/

namespace FreeWill

/-- Lawvere: if `e : A → A → Y` is point-surjective, every `f : Y → Y` has a fixed point. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) : ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

theorem no_total_self_prediction {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

/-- Next choice as a function of the predicted value: `act p = not p`. -/
def act (predicted : Bool) : Bool := not predicted

theorem determined : ∀ p a b, act p = a → act p = b → a = b :=
  fun _ _ _ ha hb => ha.symm.trans hb

/-- The system's own prediction is never correct: `act p ≠ p`. -/
theorem interior_openness : ∀ p, act p ≠ p := by
  intro p; cases p <;> decide

/-- Actual next choice at state `a`: negation of `e a a`, the system's own prediction. -/
def nextChoice {A : Type} (e : A → A → Bool) (a : A) : Bool := not (e a a)

theorem never_foreknown {A : Type} (e : A → A → Bool) (a : A) :
    e a a ≠ nextChoice e a := by
  unfold nextChoice
  exact (by decide : ∀ b : Bool, b ≠ not b) (e a a)

theorem free_will_is_the_diagonal :
    (∀ p a b, act p = a → act p = b → a = b)
    ∧ (∀ p, act p ≠ p)
    ∧ (∀ {A : Type} (e : A → A → Bool), ¬ ∀ g : A → Bool, ∃ a, e a = g) :=
  ⟨determined, interior_openness, fun {_} e => no_total_self_prediction e⟩

end FreeWill

#print axioms FreeWill.lawvere
#print axioms FreeWill.no_total_self_prediction
#print axioms FreeWill.determined
#print axioms FreeWill.interior_openness
#print axioms FreeWill.never_foreknown
#print axioms FreeWill.free_will_is_the_diagonal
