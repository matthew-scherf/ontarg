/-!
# Becoming

The ontological argument of becoming, assembled in one theorem. An
ontological argument derives an existence claim from a concept alone,
a priori. The concept here is presuppositionlessness — a specification
that imports no structure. The derivation: exactly one such
specification has content (`x = ¬x`); it has, necessarily, no static
instance — the diagonal refuses the fixed point — and, necessarily,
exactly one running instance per seed — the two-tick clock; and the
two verdicts are one fact, since the absence of static solutions is
equivalent to the perpetual motion of every orbit. What the concept
forces into existence is not a being (that is refuted) but a becoming
(that is constructed, and unique).

Each step is proved in fuller generality elsewhere in the corpus:
the classification in `OnlyShape.lean` and `Structureless.lean`, the
two frames in `TwoReadings.lean`, the guarded fixed point in
`Loeb.lean` (`godel_is_clock`), the propositional diagonal in
`Aseity.lean`, the tokened denial in `Cogito.lean`, the conditional
actuality (given R1–R4) in `Regress.lean`, and the enacted instance in
`Instantiation.lean`. This file re-proves what it needs so that the
argument stands alone.

Main results:
* `one_candidate` — a structureless law on the bare distinction is
  the identity or the negation; constants are not structureless
  (`constants_not_structureless`); the identity is satisfied by
  everything and so says nothing (`id_says_nothing`).
* `no_being` — a proposition equal to its own negation is absurd; the
  candidate has no static instance (`no_static_instance`).
* `becoming_exists`, `becoming_unique`, `two_tick_clock` — the same
  candidate, read as a recursion, has exactly one solution per seed:
  the alternating clock, period exactly two.
* `refusal_is_running` — the object frame's emptiness and the process
  frame's perpetual motion are one hypothesis, as a biconditional.
* `denial_self_refutes` — tokening the denial of any token's
  occurrence refutes itself.
* `ontological_argument` — the conjunction.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Becoming

/- ---------- the candidate ---------- -/

/-- Structureless on the bare distinction: the law commutes with the
    relabeling, so it names no element. (Grounded as definability from
    the distinction alone in `Structureless.lean`.) -/
def Structureless (g : Bool → Bool) : Prop := ∀ b, g (!b) = !(g b)

/-- The classification: a structureless law on the bare distinction is
    the identity or the negation. -/
theorem one_candidate (g : Bool → Bool) (h : Structureless g) :
    (∀ b, g b = b) ∨ (∀ b, g b = !b) := by
  cases htrue : g true with
  | true =>
    left
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := h true
      rw [htrue] at hf
      exact hf
  | false =>
    right
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := h true
      rw [htrue] at hf
      exact hf

/-- Constants are not structureless: naming a value imports structure. -/
theorem constants_not_structureless (c : Bool) :
    ¬ Structureless (fun _ => c) := by
  intro h
  have hc := h true
  revert hc
  cases c <;> decide

/-- The identity is satisfied by everything: no constraint, no content. -/
theorem id_says_nothing : ∀ b : Bool, id b = b := fun _ => rfl

/- ---------- no necessary being ---------- -/

/-- The contentful candidate has no static instance: negation is
    fixed-point-free. -/
theorem no_static_instance : ∀ b : Bool, not b ≠ b := by
  intro b
  cases b <;> decide

/-- At the level of propositions: a proposition equal to its own
    negation is absurd. Whatever `x = ¬x` demands, no state — and no
    truth value — supplies it. -/
theorem no_being (X : Prop) (h : X = ¬ X) : False :=
  have hiff : X ↔ ¬ X := Iff.of_eq h
  have hn : ¬ X := fun hx => hiff.mp hx hx
  hn (hiff.mpr hn)

/- ---------- necessary becoming ---------- -/

variable {S : Type u}

/-- The process frame: a trajectory solving the recursion. -/
def Solves (f : S → S) (x : Nat → S) : Prop := ∀ n, x (n + 1) = f (x n)

/-- The canonical trajectory from a seed. -/
def orbit (f : S → S) (seed : S) : Nat → S
  | 0     => seed
  | n + 1 => f (orbit f seed n)

/-- The recursion has a solution from every seed: existence is a
    construction, not a predicate. -/
theorem becoming_exists (f : S → S) (seed : S) :
    Solves f (orbit f seed) ∧ orbit f seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

/-- And exactly one: any solution agreeing at the seed agrees at
    every tick. -/
theorem becoming_unique (f : S → S) (x : Nat → S)
    (hx : Solves f x) (seed : S) (h0 : x 0 = seed) :
    ∀ n, x n = orbit f seed n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, ih]; rfl

/-- The candidate's run is the two-tick clock: period exactly two. -/
theorem two_tick_clock (seed : Bool) :
    ∀ n, orbit not seed (n + 2) = orbit not seed n := by
  intro n
  show (!(!(orbit not seed n))) = orbit not seed n
  cases orbit not seed n with
  | true  => rfl
  | false => rfl

/- ---------- one fact, two frames ---------- -/

/-- The refusal is the running: a specification has no static solution
    if and only if every orbit moves at every tick. The wall of the
    object frame and the motor of the process frame are one hypothesis. -/
theorem refusal_is_running (f : S → S) :
    (∀ x, f x ≠ x) ↔ ∀ seed n, orbit f seed (n + 1) ≠ orbit f seed n := by
  constructor
  · intro h seed n
    exact h (orbit f seed n)
  · intro h x
    exact h x 0

/- ---------- the token ---------- -/

/-- Tokening the denial of any token's occurrence refutes itself: to
    token "`a` does not occur", `a` must be given. (`Cogito.lean`.) -/
theorem denial_self_refutes {A : Type} (a : A) : ¬ ¬ (∃ x : A, x = a) :=
  fun h => h ⟨a, rfl⟩

/- ---------- the conjunction ---------- -/

/-- The ontological argument of becoming. (1) On the bare distinction
    the structureless laws are exactly the identity and the negation,
    and constants are excluded; (2) the identity says nothing, so the
    one contentful candidate is `x = ¬x`; (3) the candidate has no
    static instance; (4) it has exactly one running instance per seed,
    the two-tick clock; (5) the absence of static solutions and the
    perpetual motion of every orbit are the same fact. What the
    presuppositionless concept forces to exist is a becoming, not a
    being. -/
theorem ontological_argument :
    (∀ g : Bool → Bool, Structureless g →
        (∀ b, g b = b) ∨ (∀ b, g b = !b))
    ∧ (∀ c : Bool, ¬ Structureless (fun _ => c))
    ∧ (∀ b : Bool, id b = b)
    ∧ (∀ b : Bool, not b ≠ b)
    ∧ (∀ seed : Bool,
        (Solves not (orbit not seed) ∧ orbit not seed 0 = seed)
        ∧ (∀ x, Solves not x → x 0 = seed →
            ∀ n, x n = orbit not seed n)
        ∧ (∀ n, orbit not seed (n + 2) = orbit not seed n))
    ∧ ((∀ b : Bool, not b ≠ b) ↔
        ∀ seed n, orbit not seed (n + 1) ≠ orbit not seed n) :=
  ⟨one_candidate,
   constants_not_structureless,
   id_says_nothing,
   no_static_instance,
   fun seed =>
     ⟨becoming_exists not seed,
      fun x hx h0 => becoming_unique not x hx seed h0,
      two_tick_clock seed⟩,
   refusal_is_running not⟩

end Becoming

/- audit -/
#print axioms Becoming.one_candidate
#print axioms Becoming.constants_not_structureless
#print axioms Becoming.id_says_nothing
#print axioms Becoming.no_static_instance
#print axioms Becoming.no_being
#print axioms Becoming.becoming_exists
#print axioms Becoming.becoming_unique
#print axioms Becoming.two_tick_clock
#print axioms Becoming.refusal_is_running
#print axioms Becoming.denial_self_refutes
#print axioms Becoming.ontological_argument
