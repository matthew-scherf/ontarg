/-!
# TwoReadings

One specification `f : S → S`, two readings: the object frame's
equation `x = f x`, and the process frame's recursion
`x (n+1) = f (x n)`. Restlessness in the first is perpetual motion in
the second.
-/

namespace TwoReadings

variable {S : Type u}

/-- Refuses every static state. -/
def Restless (f : S → S) : Prop := ∀ x, f x ≠ x

/-- A state solving `x = f x`. -/
def ObjectSolution (f : S → S) : Prop := ∃ x, x = f x

/-- A trajectory solving the recursion. -/
def Solves (f : S → S) (x : Nat → S) : Prop := ∀ n, x (n + 1) = f (x n)

/-- The canonical trajectory from a seed. -/
def orbit (f : S → S) (seed : S) : Nat → S
  | 0     => seed
  | n + 1 => f (orbit f seed n)

theorem object_reading_empty (f : S → S) (h : Restless f) :
    ¬ ObjectSolution f := by
  intro hx
  cases hx with
  | intro x hfix => exact h x hfix.symm

theorem process_reading_inhabited (f : S → S) (seed : S) :
    Solves f (orbit f seed) ∧ orbit f seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

theorem process_reading_unique (f : S → S) (x y : Nat → S)
    (hx : Solves f x) (hy : Solves f y) (h0 : x 0 = y 0) :
    ∀ n, x n = y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, hy k, ih]

theorem object_solution_iff_fixed_orbit (f : S → S) :
    ObjectSolution f ↔ ∃ seed, ∀ n, orbit f seed n = seed := by
  constructor
  · intro hx
    cases hx with
    | intro x hfix =>
      refine ⟨x, ?_⟩
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
        show f (orbit f x k) = x
        rw [ih, hfix.symm]
  · intro hs
    cases hs with
    | intro seed hconst =>
      refine ⟨seed, ?_⟩
      have h1 : orbit f seed 1 = seed := hconst 1
      show seed = f seed
      exact h1.symm

theorem frames_one_fact (f : S → S) :
    Restless f ↔ ∀ seed n, orbit f seed (n + 1) ≠ orbit f seed n := by
  constructor
  · intro h seed n
    exact h (orbit f seed n)
  · intro h x
    exact h x 0

/-- The instance at `x = ¬x`: object reading empty, process reading the
    two-tick clock. -/
theorem founding_two_readings :
    (¬ ObjectSolution not)
    ∧ (∀ seed n, orbit not seed (n + 1) ≠ orbit not seed n)
    ∧ (∀ seed n, orbit not seed (n + 2) = orbit not seed n) := by
  have hrestless : Restless not := by
    intro b
    cases b with
    | true  => intro hb; cases hb
    | false => intro hb; cases hb
  refine ⟨object_reading_empty not hrestless, ?_, ?_⟩
  · exact (frames_one_fact not).mp hrestless
  · intro seed n
    show (!(!(orbit not seed n))) = orbit not seed n
    cases orbit not seed n with
    | true  => rfl
    | false => rfl

end TwoReadings

#print axioms TwoReadings.object_reading_empty
#print axioms TwoReadings.process_reading_inhabited
#print axioms TwoReadings.process_reading_unique
#print axioms TwoReadings.object_solution_iff_fixed_orbit
#print axioms TwoReadings.frames_one_fact
#print axioms TwoReadings.founding_two_readings
