/-!
# FreeWill

Determinism and interior openness as two faces of one operator. A
"choice" is a Boolean coordinate whose actual next value is a fixed
function of the system's own prediction of it. Determinism: that next
value is a total function — nothing is random. Openness: the system's
own prediction of its next choice is necessarily falsified, at
exactly the self-referential coordinate, because the actual value is
the negation of whatever it predicts.

Main results:
* `no_total_self_prediction` — no describer completes its own
  self-prediction (the Lawvere diagonal at `not`).
* `determined` — the next-choice map is single-valued.
* `interior_openness` — the system's prediction of its own next
  choice is never correct: `act p ≠ p`.
* `never_foreknown` — the general form: for every state, the system's
  self-prediction of its next choice is wrong.
* `free_will_is_the_diagonal` — the conjunction: determined, open
  from inside, and globally uncompletable.

The reading of these results as an account of free will is an
interpretation; what is proved is that determinism and interior
openness are consistent and meet at the diagonal. No ontology of
agency is claimed.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace FreeWill

/- ---------- the diagonal (re-declared, = OneDiagonal.lawvere) ---------- -/

/-- Lawvere (1969). If a carrier enumerates its own maps into `Y`
    point-surjectively, every endomap of `Y` has a fixed point. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) : ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

/-- No describer completes its own self-prediction: at the
    fixed-point-free `f = not`, no self-enumeration of Boolean
    self-predicates is point-surjective. -/
theorem no_total_self_prediction {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

/- ---------- the concrete choice coordinate ---------- -/

/-- The system's next choice, as a function of the prediction it emits
    about that choice: actual = not(predicted). A total, deterministic
    function. -/
def act (predicted : Bool) : Bool := not predicted

/-- The next choice is single-valued — a function of the current
    (predicted) state: any two outcomes of `act p` coincide. -/
theorem determined : ∀ p a b, act p = a → act p = b → a = b :=
  fun _ _ _ ha hb => ha.symm.trans hb

/-- Yet the system's own prediction of its next choice is never
    correct: actual = not(predicted) ≠ predicted. From within, the
    choice cannot be foreknown, though it is fixed to an outside view. -/
theorem interior_openness : ∀ p, act p ≠ p := by
  intro p; cases p <;> decide

/- ---------- the general form ---------- -/

/-- The actual next choice at a state: the negation of the state's own
    self-prediction (`e a a` is what the system, in state `a`, predicts
    of its own choice). -/
def nextChoice {A : Type} (e : A → A → Bool) (a : A) : Bool := not (e a a)

/-- For every state `a`, the system's own prediction `e a a` of its
    next choice is wrong: `e a a ≠ nextChoice e a`. `nextChoice` is a
    total function of `a` (determinism intact); the interior openness
    is also total. -/
theorem never_foreknown {A : Type} (e : A → A → Bool) (a : A) :
    e a a ≠ nextChoice e a := by
  unfold nextChoice
  exact (by decide : ∀ b : Bool, b ≠ not b) (e a a)

/- ---------- the conjunction ---------- -/

/-- The same deterministic operator is (1) fully determined — exactly
    one next outcome; (2) open from inside — the system's prediction of
    its own next choice is always wrong; and (3) globally uncompletable
    — no describer holds a total correct self-theory. -/
theorem free_will_is_the_diagonal :
    (∀ p a b, act p = a → act p = b → a = b)
    ∧ (∀ p, act p ≠ p)
    ∧ (∀ {A : Type} (e : A → A → Bool), ¬ ∀ g : A → Bool, ∃ a, e a = g) :=
  ⟨determined, interior_openness, fun {_} e => no_total_self_prediction e⟩

end FreeWill

/- audit -/
#print axioms FreeWill.lawvere
#print axioms FreeWill.no_total_self_prediction
#print axioms FreeWill.determined
#print axioms FreeWill.interior_openness
#print axioms FreeWill.never_foreknown
#print axioms FreeWill.free_will_is_the_diagonal
