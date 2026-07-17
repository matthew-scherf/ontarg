/-!
# Becoming

The ontological argument of becoming, assembled in one theorem, with no
premise at any link. An ontological argument derives an existence claim
from a concept alone, a priori. The concept here is
presuppositionlessness — a specification that imports no structure. The
derivation: any tokening of a claim already draws a distinction, and
the denial of that is unsayable rather than false; the arena of a drawn
distinction is two-valued — not by choice, but because one value is
mute and three or more are mute; on that arena exactly one
structureless specification has content (`x = ¬x`); it has,
necessarily, no static instance — no structureless specification could
have had one — and, necessarily, exactly one running instance per seed
— the two-tick clock; the two verdicts are one fact, since the absence
of static solutions is equivalent to the perpetual motion of every
orbit; and the seed the run is unique up to is a label, not a premise —
the two runs are one run relabelled. What the concept forces into
existence is not a being (that is refuted) but a becoming (that is
constructed, and unique).

Each link is proved in fuller generality elsewhere in the corpus: the
retorsion in `Tokening.lean`, the arena in `Arena.lean`, the
classification in `OnlyShape.lean` and `Structureless.lean`, the
relational classification in `Articulation.lean`, the two frames in
`TwoReadings.lean`, the regress without well-foundedness in
`Eternal.lean`, the seed in `Seed.lean`, the guarded fixed point in
`Loeb.lean` (`godel_is_clock`), the propositional diagonal in
`Aseity.lean`, the tokened denial in `Cogito.lean`, and the enacted
instance in `Instantiation.lean`. (The superseded conditional route to
actuality, given R1–R4, survives in `Regress.lean` and still checks.)
This file re-proves what it needs so that the argument stands alone.

Main results:
* `retorsion`, `no_undrawn_denial` — the entry: a medium that tokens
  "no distinction is drawn" as opposed to its denial has thereby drawn
  one. There is no seat from which the denial can be said.
* `bare_one_is_mute`, `bare_three_is_mute`, `two_speaks` — the arena:
  on one bare value every law is the identity, on three or more every
  equivariant law is the identity, and only on two is there a
  structureless law that moves anything.
* `one_candidate` — a structureless law on the bare distinction is
  the identity or the negation; constants are not structureless
  (`constants_not_structureless`); the identity is satisfied by
  everything and so says nothing (`id_says_nothing`).
* `diagonal_uniform` — no structureless specification singles out a
  state: read of itself, it holds of every state or of none.
* `no_being` — a proposition equal to its own negation is absurd; the
  candidate has no static instance (`no_static_instance`).
* `becoming_exists`, `becoming_unique`, `two_tick_clock` — the same
  candidate, read as a recursion, has exactly one solution per seed:
  the alternating clock, period exactly two.
* `absolute_articulation` — the relational assembly: a specification
  that imports nothing and articulates is the negation graph, its
  object frame is empty, its process frame is inhabited, and its run
  is the clock, unique given a seed.
* `refusal_is_running` — the object frame's emptiness and the process
  frame's perpetual motion are one hypothesis, as a biconditional.
* `seed_is_relabel` — the two runs are one run relabelled; so no
  structureless proposition separates them (`seed_is_invisible`).
* `denial_self_refutes` — tokening the denial of any token's
  occurrence refutes itself.
* `ontological_argument` — the conjunction.

Lean 4, prelude only; no imports. Axiom footprint: none —
`ontological_argument` and every link it assembles are axiom-free. The
sole exception in the file is the corollary `seed_is_invisible`, within
`[Quot.sound]` (function extensionality, to transport a proposition
across two pointwise equal runs); the assembled theorem carries the
seed link in its pointwise form, which needs nothing.
-/

namespace Becoming

/- ---------- link 1: the distinction is drawn ---------- -/

/-- A distinction is drawn in `M`: two of its states differ. This is
    the whole content of "there is a distinction" — nothing is named,
    no state is preferred. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b

/-- A one-state medium marks every claim alike: it tokens nothing.
    Silence and assertion are the same event. -/
theorem subsingleton_tokens_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Prop → M) : ∀ P Q : Prop, t P = t Q :=
  fun P Q => h (t P) (t Q)

/-- The retorsion. Any medium that marks "no distinction is drawn"
    differently from its denial has two distinct marks — and so draws
    the distinction it denies. The denial is not refuted by argument;
    it is refuted by being tokened. -/
theorem retorsion {M : Type} (t : Prop → M)
    (h : t (¬ Draws M) ≠ t (Draws M)) : Draws M :=
  ⟨t (¬ Draws M), t (Draws M), h⟩

/-- The same as the impossibility it is: there is no seat from which
    the denial can be said. -/
theorem no_undrawn_denial {M : Type} (t : Prop → M) :
    ¬ (t (¬ Draws M) ≠ t (Draws M) ∧ ¬ Draws M) :=
  fun ⟨hd, hn⟩ => hn (retorsion t hd)

/- ---------- link 2: the arena is two ---------- -/

/-- The transposition of two values: the simplest relabeling. -/
def transp {V : Type u} [DecidableEq V] (a b : V) : V → V :=
  fun x => if x = a then b else if x = b then a else x

theorem transp_left {V : Type u} [DecidableEq V] (a b : V) :
    transp a b a = b := by
  show (if a = a then b else if a = b then a else a) = b
  rw [if_pos rfl]

theorem transp_fixes {V : Type u} [DecidableEq V] {a b x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) : transp a b x = x := by
  show (if x = a then b else if x = b then a else x) = x
  rw [if_neg hxa, if_neg hxb]

/-- Structurelessness on a bare carrier: the law commutes with every
    relabeling. No value is named, so every transposition is a
    symmetry. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

/-- Three or more values are mute. If `f` moves `x` to `y ≠ x`, a
    third value `z` gives a transposition of `y` and `z` that fixes `x`
    — forcing `f x` to be both `y` and `z`. So `f` moves nothing. There
    is no negation on a bare three-element arena. -/
theorem bare_three_is_mute {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f)
    (h3 : ∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) :
    ∀ x, f x = x := by
  intro x
  by_cases hfx : f x = x
  · exact hfx
  · obtain ⟨z, hzx, hzf⟩ := h3 x (f x)
    have hxfix : transp (f x) z x = x :=
      transp_fixes (fun h => hfx h.symm) (fun h => hzx h.symm)
    have h := hequiv (f x) z x
    rw [hxfix, transp_left] at h
    exact absurd h.symm hzf

/-- One value is mute too, and draws no distinction. -/
theorem bare_one_is_mute {V : Type u} (f : V → V)
    (h1 : ∀ x y : V, x = y) : ∀ x, f x = x :=
  fun x => h1 (f x) x

/-- Two speaks. On exactly two bare values there is a structureless
    law that is not the identity. The count of values is not a premise;
    it is the unique count at which a structureless law moves anything
    (`Arena.speaks_needs_exactly_two` for the converse). -/
theorem two_speaks :
    Equivariant (fun x : Bool => !x) ∧ (∀ x : Bool, !x ≠ x) := by
  constructor
  · intro a b x; cases a <;> cases b <;> cases x <;> rfl
  · intro x; cases x <;> decide

/- ---------- link 3: the candidate ---------- -/

/-- Structureless on the bare distinction: the law commutes with the
    relabeling, so it names no element. (Grounded as definability from
    the distinction alone in `Structureless.lean`; and closed against a
    rival reading in `Articulation.lean` — a law that fails to commute
    is a constant, the maximally structured case.) -/
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

/- ---------- link 3, relational: no structureless spec singles out a state ---------- -/

/-- Relations on the bare distinction definable from the distinction
    alone: the equality atom, closed under negation, conjunction, and
    disjunction. Nothing is named. (As `Structureless.Defble`.) -/
inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

theorem defble_invariant {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a b ↔ R (!a) (!b) := by
  induction h with
  | eq => decide
  | neg _ ih =>
    intro a b
    exact ⟨fun hn hr => hn ((ih a b).mpr hr),
           fun hn hr => hn ((ih a b).mp hr)⟩
  | conj _ _ ih1 ih2 =>
    intro a b
    exact ⟨fun ⟨h1, h2⟩ => ⟨(ih1 a b).mp h1, (ih2 a b).mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨(ih1 a b).mpr h1, (ih2 a b).mpr h2⟩⟩
  | disj _ _ ih1 ih2 =>
    intro a b
    exact ⟨fun h => h.elim (fun h1 => Or.inl ((ih1 a b).mp h1))
                           (fun h2 => Or.inr ((ih2 a b).mp h2)),
           fun h => h.elim (fun h1 => Or.inl ((ih1 a b).mpr h1))
                           (fun h2 => Or.inr ((ih2 a b).mpr h2))⟩

/-- No structureless specification singles out a state. Read of
    itself, it holds of every state or of none: the diagonal is
    uniform. The absolute cannot be a thing — not because the founding
    law happens to lack a solution, but because no structureless
    specification could have had one. -/
theorem diagonal_uniform {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a a ↔ R b b := by
  intro a b
  cases a <;> cases b
  · exact Iff.rfl
  · exact defble_invariant h false false
  · exact defble_invariant h true true
  · exact Iff.rfl

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

/- ---------- link 4: so it runs, and the law is negation ---------- -/

/-- No value survives its own relabeling. -/
theorem no_fixpoint : ∀ x : Bool, x ≠ !x := by
  intro x; cases x <;> decide

/-- On two values, differing is being the other. -/
theorem ne_eq_not : ∀ a b : Bool, a ≠ b → b = !a := by
  intro a b h
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

/-- `R` excludes the state `x`: read of itself, it fails there. -/
def Excludes (R : Bool → Bool → Prop) (x : Bool) : Prop := ¬ R x x

/-- `R` says something: it excludes some state. An articulation that
    excludes nothing distinguishes nothing. -/
def Says (R : Bool → Bool → Prop) : Prop := ∃ x, Excludes R x

/-- The object frame: a state that satisfies `R` read of itself. -/
def ObjSat (R : Bool → Bool → Prop) : Prop := ∃ x, R x x

/-- The process frame: an unending run each of whose steps satisfies
    `R`. -/
def ProcSat (R : Bool → Bool → Prop) : Prop :=
  ∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1))

/-- `R` is satisfied in some frame. An articulation nothing satisfies
    in any frame is not a rival absolute; it is silence. -/
def Sat (R : Bool → Bool → Prop) : Prop := ObjSat R ∨ ProcSat R

/-- To articulate is to exclude something and not everything. The two
    conditions are not premises about a ground: their denial is
    self-refuting rather than false (`Tokening.lean`), since any
    tokening of a denial excludes something and is satisfied by
    something. -/
def Articulates (R : Bool → Bool → Prop) : Prop := Says R ∧ Sat R

/-- Saying anything at all costs the whole object frame: a
    structureless specification that excludes any state excludes every
    state. -/
theorem says_kills_the_object {R : Bool → Bool → Prop}
    (hD : Defble R) (hS : Says R) : ¬ ObjSat R := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hS
  exact hy ((diagonal_uniform hD x y).mp hx)

/-- The clock runs the negation graph: consecutive values differ at
    every tick. -/
theorem clock_runs (b : Bool) :
    ∀ n, orbit not b n ≠ orbit not b (n + 1) :=
  fun n => no_fixpoint (orbit not b n)

/-- A run of the negation graph is the clock on its seed: the process
    reading is unique given a seed. -/
theorem run_unique {t : Nat → Bool} (ht : ∀ n, t n ≠ t (n + 1)) :
    ∀ n, t n = orbit not (t 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show t (n + 1) = !(orbit not (t 0) n)
    rw [← ih]
    exact ne_eq_not (t n) (t (n + 1)) (ht n)

/-- The absolute law. A structureless specification that says
    something and is satisfied in some frame is the negation graph:
    `R a b ↔ a ≠ b`. No premise selects it; excluding-something and
    being-satisfiable do all the work. -/
theorem absolute_law {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) : ∀ a b, R a b ↔ a ≠ b := by
  obtain ⟨hS, hSat⟩ := hA
  have hdiag : ∀ x, ¬ R x x := by
    intro x
    obtain ⟨y, hy⟩ := hS
    intro hx
    exact hy ((diagonal_uniform hD x y).mp hx)
  have hproc : ProcSat R := by
    cases hSat with
    | inl hobj => exact absurd hobj (says_kills_the_object hD hS)
    | inr hproc => exact hproc
  obtain ⟨s, hs⟩ := hproc
  have hstep : R (s 0) (s 1) := hs 0
  have hne : s 0 ≠ s 1 := fun he => hdiag (s 0) (he ▸ hstep)
  have hoff : ∀ a, R a (!a) := by
    intro a
    cases h0 : s 0 <;> cases h1 : s 1
    · exact absurd (h0.trans h1.symm) hne
    · have hft : R false true := h0 ▸ h1 ▸ hstep
      cases a
      · exact hft
      · exact (defble_invariant hD false true).mp hft
    · have htf : R true false := h0 ▸ h1 ▸ hstep
      cases a
      · exact (defble_invariant hD true false).mp htf
      · exact htf
    · exact absurd (h0.trans h1.symm) hne
  intro a b
  constructor
  · intro hab he; exact hdiag a (he ▸ hab)
  · intro hab; exact (ne_eq_not a b hab) ▸ hoff a

/-- The Absolute Articulation. Let `R` be a specification that imports
    nothing (`Defble`) and that articulates — excludes something
    (`Says`), and is satisfied in some frame (`Sat`). Then:

    1. its law is negation;
    2. its object frame is empty — it is not a thing, and cannot be;
    3. its process frame is inhabited — it runs;
    4. its run is unique given a seed — the two-tick clock.

    No premise is discharged anywhere in this statement. `Defble` is
    the demand for zero premises; `Says` and `Sat` are what
    articulating is; the rest is a theorem. -/
theorem absolute_articulation {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) :
    (∀ a b, R a b ↔ a ≠ b)
    ∧ (¬ ∃ x, R x x)
    ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
    ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
        ∀ n, t n = orbit not (t 0) n) := by
  have hlaw := absolute_law hD hA
  refine ⟨hlaw, says_kills_the_object hD hA.1, ⟨orbit not true, ?_⟩, ?_⟩
  · intro n
    exact (hlaw (orbit not true n) (orbit not true (n + 1))).mpr
      (clock_runs true n)
  · intro t ht
    exact run_unique (fun n => (hlaw (t n) (t (n + 1))).mp (ht n))

/-- The antecedent is inhabited. A conditional whose antecedent
    nothing satisfies proves nothing, so this is checked rather than
    assumed: the negation graph *is* structureless, and it *does*
    articulate — it excludes a state, and the clock satisfies it. So
    `absolute_articulation` is not vacuously true, and by
    `absolute_law` what it is about is unique. -/
theorem absolute_is_inhabited :
    Defble (fun a b => ¬ (a = b)) ∧ Articulates (fun a b => ¬ (a = b)) := by
  refine ⟨Defble.neg Defble.eq, ⟨true, fun h => h rfl⟩,
    Or.inr ⟨orbit not true, ?_⟩⟩
  intro n
  exact clock_runs true n

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

/- ---------- link 5: the seed is a label, not a premise ---------- -/

/-- Relabelling a run: apply the sole nontrivial relabeling of the
    bare distinction at every tick. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => !(s n)

/-- The seed is a label. The run from `false` is the run from `true`,
    relabelled. They are not two histories; they are one history read
    two ways. -/
theorem seed_is_relabel :
    ∀ n, orbit not false n = relabel (orbit not true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show not (orbit not false n) = not (orbit not true (n + 1))
    rw [ih]
    rfl

/-- A proposition about runs is *structureless* when it survives the
    relabeling — when it names no value, only shape. -/
def StructurelessProp (P : (Nat → Bool) → Prop) : Prop :=
  ∀ s, P s ↔ P (relabel s)

/-- The seed is invisible. No structureless proposition separates the
    two runs: whatever it says of the run from `true`, it says of the
    run from `false`. The seed is not assumed and not derived; it is
    read — a record, not a premise (`Seed.lean`). -/
theorem seed_is_invisible {P : (Nat → Bool) → Prop}
    (hP : StructurelessProp P) :
    P (orbit not true) ↔ P (orbit not false) := by
  have h : (orbit not false) = relabel (orbit not true) := by
    funext n; exact seed_is_relabel n
  constructor
  · intro hp; rw [h]; exact (hP (orbit not true)).mp hp
  · intro hp; rw [h] at hp; exact (hP (orbit not true)).mpr hp

/- ---------- the token ---------- -/

/-- Tokening the denial of any token's occurrence refutes itself: to
    token "`a` does not occur", `a` must be given. (`Cogito.lean`.) -/
theorem denial_self_refutes {A : Type} (a : A) : ¬ ¬ (∃ x : A, x = a) :=
  fun h => h ⟨a, rfl⟩

/- ---------- the conjunction ---------- -/

/-- The ontological argument of becoming, with no premise at any link.

    (1) Any medium that tokens "no distinction is drawn" as opposed to
    its denial thereby draws one: the denial is unsayable, not false.
    (2) The arena of a drawn distinction is two-valued — one value is
    mute, three or more are mute, two speaks — so the count of values
    is a consequence, not a choice. (3) On the bare distinction the
    structureless laws are exactly the identity and the negation,
    constants are excluded, and the identity says nothing; and no
    structureless specification singles out a state, so the absolute
    cannot be a thing. (4) A specification that imports nothing and
    articulates — excludes something, and is satisfied in some frame —
    is the negation graph: its object frame is empty, its process frame
    is inhabited, and its run is the two-tick clock, unique given a
    seed, with period exactly two. (5) The absence of static solutions
    and the perpetual motion of every orbit are the same fact. (6) The
    seed is a label: the two runs are one run relabelled, so nothing
    structureless separates them — the last choice the mathematics
    leaves open is a record, not a premise. What the
    presuppositionless concept forces to exist is a becoming, not a
    being. -/
theorem ontological_argument :
    -- 1. the distinction is drawn: its denial cannot be tokened
    (∀ (M : Type) (t : Prop → M), t (¬ Draws M) ≠ t (Draws M) → Draws M)
    -- 2. the arena is two: one is mute, three or more are mute, two speaks
    ∧ (∀ (V : Type) (f : V → V), (∀ x y : V, x = y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, !x ≠ x)
    -- 3. one candidate: the structureless laws are {id, not}, constants
    --    are excluded, the identity says nothing, and nothing
    --    structureless singles out a state
    ∧ (∀ g : Bool → Bool, Structureless g →
        (∀ b, g b = b) ∨ (∀ b, g b = !b))
    ∧ (∀ c : Bool, ¬ Structureless (fun _ => c))
    ∧ (∀ b : Bool, id b = b)
    ∧ (∀ R : Bool → Bool → Prop, Defble R → ∀ a b, R a a ↔ R b b)
    -- 4. so the absolute runs, and can only run: no being, unique becoming
    ∧ (∀ R : Bool → Bool → Prop, Defble R → Articulates R →
        (∀ a b, R a b ↔ a ≠ b)
        ∧ (¬ ∃ x, R x x)
        ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
        ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
            ∀ n, t n = orbit not (t 0) n))
    ∧ (∀ seed : Bool,
        (Solves not (orbit not seed) ∧ orbit not seed 0 = seed)
        ∧ (∀ x, Solves not x → x 0 = seed →
            ∀ n, x n = orbit not seed n)
        ∧ (∀ n, orbit not seed (n + 2) = orbit not seed n))
    -- 5. the refusal is the running
    ∧ ((∀ b : Bool, not b ≠ b) ↔
        ∀ seed n, orbit not seed (n + 1) ≠ orbit not seed n)
    -- 6. and the seed is a label, not a premise
    ∧ (∀ n, orbit not false n = relabel (orbit not true) n) :=
  ⟨fun _ t h => retorsion t h,
   fun _ f h1 => bare_one_is_mute f h1,
   fun _ _ f he h3 => bare_three_is_mute f he h3,
   two_speaks,
   one_candidate,
   constants_not_structureless,
   id_says_nothing,
   fun _ hD => diagonal_uniform hD,
   fun _ hD hA => absolute_articulation hD hA,
   fun seed =>
     ⟨becoming_exists not seed,
      fun x hx h0 => becoming_unique not x hx seed h0,
      two_tick_clock seed⟩,
   refusal_is_running not,
   seed_is_relabel⟩

end Becoming

/- audit -/
#print axioms Becoming.retorsion
#print axioms Becoming.no_undrawn_denial
#print axioms Becoming.bare_one_is_mute
#print axioms Becoming.bare_three_is_mute
#print axioms Becoming.two_speaks
#print axioms Becoming.one_candidate
#print axioms Becoming.constants_not_structureless
#print axioms Becoming.id_says_nothing
#print axioms Becoming.diagonal_uniform
#print axioms Becoming.no_static_instance
#print axioms Becoming.no_being
#print axioms Becoming.becoming_exists
#print axioms Becoming.becoming_unique
#print axioms Becoming.two_tick_clock
#print axioms Becoming.says_kills_the_object
#print axioms Becoming.absolute_law
#print axioms Becoming.absolute_articulation
#print axioms Becoming.absolute_is_inhabited
#print axioms Becoming.refusal_is_running
#print axioms Becoming.seed_is_relabel
#print axioms Becoming.seed_is_invisible
#print axioms Becoming.denial_self_refutes
#print axioms Becoming.ontological_argument
