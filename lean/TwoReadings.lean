/-!
# TwoReadings

One specification `f : S → S`, two readings. The object frame reads
it as an equation over states: find `x` with `x = f x`. The process
frame reads it as a recursion over ticks: find a trajectory with
`x (n+1) = f (x n)`. The object frame's emptiness and the process
frame's perpetual motion are the same hypothesis — an equivalence,
not an analogy.

Main results:
* `object_reading_empty` — a restless specification has no solution
  among states.
* `process_reading_inhabited` — every seed starts a solution of the
  recursion.
* `process_reading_unique` — the solution is unique given the seed.
* `object_solution_iff_fixed_orbit` — object solutions are exactly
  the constant orbits.
* `frames_one_fact` — `f` is restless iff every orbit moves at every
  tick: the object-frame absence of solutions is the process-frame
  dynamics, one hypothesis read in two frames.
* `founding_two_readings` — the instance at `x = ¬x` on the bare
  distinction: object reading empty; process reading the two-tick
  clock, period exactly two.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace TwoReadings

variable {S : Type u}

/-- Restless: the specification refuses every static state. -/
def Restless (f : S → S) : Prop := ∀ x, f x ≠ x

/-- The object frame: a state solving the equation x = f x. -/
def ObjectSolution (f : S → S) : Prop := ∃ x, x = f x

/-- The process frame: a trajectory solving the recursion. -/
def Solves (f : S → S) (x : Nat → S) : Prop := ∀ n, x (n + 1) = f (x n)

/-- The canonical trajectory from a seed. -/
def orbit (f : S → S) (seed : S) : Nat → S
  | 0     => seed
  | n + 1 => f (orbit f seed n)

/-- If `f` is restless, the object frame is empty: the equation has
    no solution among states. -/
theorem object_reading_empty (f : S → S) (h : Restless f) :
    ¬ ObjectSolution f := by
  intro hx
  cases hx with
  | intro x hfix => exact h x hfix.symm

/-- The process frame is inhabited: every seed starts a solution. -/
theorem process_reading_inhabited (f : S → S) (seed : S) :
    Solves f (orbit f seed) ∧ orbit f seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

/-- And uniquely: a solution is determined by its seed. -/
theorem process_reading_unique (f : S → S) (x y : Nat → S)
    (hx : Solves f x) (hy : Solves f y) (h0 : x 0 = y 0) :
    ∀ n, x n = y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, hy k, ih]

/-- Fixed points are exactly the constant orbits. -/
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

/-- One hypothesis, two frames: the specification is restless — the
    object frame's emptiness — if and only if every orbit moves at
    every tick — the process frame's perpetual motion. -/
theorem frames_one_fact (f : S → S) :
    Restless f ↔ ∀ seed n, orbit f seed (n + 1) ≠ orbit f seed n := by
  constructor
  · intro h seed n
    exact h (orbit f seed n)
  · intro h x
    exact h x 0

/-- The instance at `x = ¬x` on the bare distinction. Object reading:
    empty. Process reading: the two-tick clock — every orbit moves at
    every tick and returns at every second tick. -/
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

/- audit -/
#print axioms TwoReadings.object_reading_empty
#print axioms TwoReadings.process_reading_inhabited
#print axioms TwoReadings.process_reading_unique
#print axioms TwoReadings.object_solution_iff_fixed_orbit
#print axioms TwoReadings.frames_one_fact
#print axioms TwoReadings.founding_two_readings
