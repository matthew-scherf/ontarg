/-!
# Articulation

The absolute articulation, with no premises.

The corpus classifies structureless specifications as *endomaps* of the
bare distinction (`OnlyShape.equivariant_endomaps`: `{id, neg}`), then
argues `id` away as contentless. Working with endomaps hides a rival,
because an endomap is already a commitment: it says every state has a
successor. Read a specification instead as its *graph* — a binary
relation, as `Structureless.lean` already does — and a fourth candidate
appears alongside `=`, `≠`, and `⊤`: the empty relation `⊥`. That is
*nothing*. A classification that cannot see `⊥` has not ruled nothing
out.

This file works at the level of relations and proves more with less.

Main results:
* `diagonal_uniform` — no structureless specification discriminates on
  the diagonal: read of itself it holds of every state or of none. So
  no structureless specification singles out a state. The absolute
  cannot be a thing — and this is proved of *every* structureless
  specification, without first identifying the law as negation.
* `says_kills_the_object` — a structureless specification that excludes
  any state excludes them all: its object reading is empty.
* `absolute_law` — a structureless specification that says something
  and is satisfied in some frame *is* the negation graph.
* `absolute_articulation` — the conjunction: the law is negation, the
  object frame is empty, the process frame is inhabited, and it is
  unique given a seed. The two-tick clock.

The two conditions on `R` are not premises about a ground. They unpack
what it is to articulate at all:

* `Says R` — it excludes something. An articulation that excludes
  nothing distinguishes nothing and so articulates nothing.
* `Sat R` — something satisfies it, in some frame. An articulation that
  nothing satisfies in any frame is not a rival absolute; it is silence.

Their denial is self-refuting rather than false: to deny either is to
articulate, and any articulation excludes something (what it denies)
and not everything (it does not exclude itself). This is why the
conditions cost nothing. See `Tokening.lean`.

And `Defble` — structurelessness — is not a premise either. It is the
statement of the task. An absolute metaphysics is one that imports
nothing; importing nothing is definability from the bare distinction
alone; and that is `Defble`. Premise R3 is the project's success
condition, not an assumption it makes.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Articulation

/- ---------- structurelessness ---------- -/

/-- Binary relations on the bare distinction definable from the
    distinction alone: the equality atom, closed under negation,
    conjunction, and disjunction. Nothing is named. (As
    `Structureless.Defble`.) -/
inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

/-- Soundness: every relation definable from the distinction alone is
    invariant under the relabeling. (As `Structureless.defble_invariant`;
    restated so this file stands alone.) -/
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

/- ---------- the absolute cannot be a thing ---------- -/

/-- No structureless specification singles out a state. Read of
    itself, it holds of every state or of none: the diagonal is uniform.

    This is the general form of "the absolute is not an object". The
    corpus proves the object reading empty for the negation
    (`TwoReadings.object_reading_empty`); here it is proved that *no*
    structureless specification could have had a proper object reading
    in the first place. To say "this state rather than that" is already
    to import structure. -/
theorem diagonal_uniform {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a a ↔ R b b := by
  intro a b
  cases a <;> cases b
  · exact Iff.rfl
  · exact defble_invariant h false false
  · exact defble_invariant h true true
  · exact Iff.rfl

/- ---------- two facts about the bare distinction ---------- -/

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

/- ---------- what it is to articulate ---------- -/

/-- `R` excludes the state `x`: read of itself, it fails there. -/
def Excludes (R : Bool → Bool → Prop) (x : Bool) : Prop := ¬ R x x

/-- `R` says something: it excludes some state. An articulation that
    excludes nothing distinguishes nothing. -/
def Says (R : Bool → Bool → Prop) : Prop := ∃ x, Excludes R x

/-- The object frame: a state that satisfies `R` read of itself. -/
def ObjSat (R : Bool → Bool → Prop) : Prop := ∃ x, R x x

/-- The process frame: an unending run each of whose steps satisfies `R`. -/
def ProcSat (R : Bool → Bool → Prop) : Prop :=
  ∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1))

/-- `R` is satisfied in some frame. An articulation nothing satisfies in
    any frame is not a rival absolute; it is silence. -/
def Sat (R : Bool → Bool → Prop) : Prop := ObjSat R ∨ ProcSat R

/-- To articulate is to exclude something and not everything. -/
def Articulates (R : Bool → Bool → Prop) : Prop := Says R ∧ Sat R

/- ---------- the object frame closes ---------- -/

/-- A structureless specification that excludes any state excludes every
    state: its object reading is empty. Saying anything at all costs the
    whole object frame. -/
theorem says_kills_the_object {R : Bool → Bool → Prop}
    (hD : Defble R) (hS : Says R) : ¬ ObjSat R := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hS
  exact hy ((diagonal_uniform hD x y).mp hx)

/- ---------- the law is forced ---------- -/

/-- The absolute law. A structureless specification that says
    something and is satisfied in some frame is the negation graph:
    `R a b ↔ a ≠ b`. No premise selects it; excluding-something and
    being-satisfiable do all the work. -/
theorem absolute_law {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) : ∀ a b, R a b ↔ a ≠ b := by
  obtain ⟨hS, hSat⟩ := hA
  -- Saying anything empties the object frame.
  have hdiag : ∀ x, ¬ R x x := by
    intro x
    obtain ⟨y, hy⟩ := hS
    intro hx
    exact hy ((diagonal_uniform hD x y).mp hx)
  -- So satisfaction must be in the process frame.
  have hproc : ProcSat R := by
    cases hSat with
    | inl hobj => exact absurd hobj (says_kills_the_object hD hS)
    | inr hproc => exact hproc
  obtain ⟨s, hs⟩ := hproc
  -- Its first step relates two distinct states.
  have hstep : R (s 0) (s 1) := hs 0
  have hne : s 0 ≠ s 1 := by
    intro he
    exact hdiag (s 0) (he ▸ hstep)
  -- Whichever distinct pair it is, invariance gives the other.
  have hoff : ∀ a, R a (!a) := by
    intro a
    cases h0 : s 0 <;> cases h1 : s 1
    · exact absurd (h0.trans h1.symm) hne
    · -- s 0 = false, s 1 = true
      have hft : R false true := h0 ▸ h1 ▸ hstep
      cases a
      · exact hft
      · exact (defble_invariant hD false true).mp hft
    · -- s 0 = true, s 1 = false
      have htf : R true false := h0 ▸ h1 ▸ hstep
      cases a
      · exact (defble_invariant hD true false).mp htf
      · exact htf
    · exact absurd (h0.trans h1.symm) hne
  intro a b
  constructor
  · intro hab he
    exact hdiag a (he ▸ hab)
  · intro hab
    exact (ne_eq_not a b hab) ▸ hoff a

/- ---------- the run, and its uniqueness ---------- -/

/-- The two-tick clock from a seed. -/
def clock (s : Bool) : Nat → Bool
  | 0 => s
  | n + 1 => !(clock s n)

/-- The clock runs the negation graph. -/
theorem clock_runs (b : Bool) : ∀ n, clock b n ≠ clock b (n + 1) := by
  intro n
  exact no_fixpoint (clock b n)

/-- A run of the negation graph is the clock on its seed: the process
    reading is unique given a seed. -/
theorem run_unique {t : Nat → Bool} (ht : ∀ n, t n ≠ t (n + 1)) :
    ∀ n, t n = clock (t 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show t (n + 1) = !(clock (t 0) n)
    rw [← ih]
    exact ne_eq_not (t n) (t (n + 1)) (ht n)

/- ---------- the whole argument ---------- -/

/-- The Absolute Articulation.

    Let `R` be a specification that imports nothing (`Defble`) and that
    articulates — excludes something (`Says`), and is satisfied in some
    frame (`Sat`). Then:

    1. its law is negation;
    2. its object frame is empty — it is not a thing, and cannot be;
    3. its process frame is inhabited — it runs;
    4. its run is unique given a seed — the two-tick clock.

    No premise is discharged anywhere in this statement. `Defble` is the
    demand for zero premises; `Says` and `Sat` are what articulating is;
    the rest is a theorem. -/
theorem absolute_articulation {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) :
    (∀ a b, R a b ↔ a ≠ b)
    ∧ (¬ ∃ x, R x x)
    ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
    ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
        ∀ n, t n = clock (t 0) n) := by
  have hlaw := absolute_law hD hA
  refine ⟨hlaw, says_kills_the_object hD hA.1, ⟨clock true, ?_⟩, ?_⟩
  · intro n
    exact (hlaw (clock true n) (clock true (n + 1))).mpr (clock_runs true n)
  · intro t ht
    exact run_unique (fun n => (hlaw (t n) (t (n + 1))).mp (ht n))

/- ---------- nothing is not a rival ---------- -/

/-- The empty specification is structureless and says something — it
    excludes every state — but nothing satisfies it in any frame. It is
    not a rival absolute; it is silence. This is the candidate the
    endomap classification could not see. -/
theorem bot_defble : Defble (fun a b => a = b ∧ ¬ (a = b)) :=
  Defble.conj Defble.eq (Defble.neg Defble.eq)

theorem bot_says : Says (fun a b => a = b ∧ ¬ (a = b)) :=
  ⟨true, fun h => h.2 h.1⟩

theorem bot_not_sat : ¬ Sat (fun a b => a = b ∧ ¬ (a = b)) := by
  intro h
  cases h with
  | inl hobj => obtain ⟨x, hx⟩ := hobj; exact hx.2 hx.1
  | inr hproc => obtain ⟨s, hs⟩ := hproc; exact (hs 0).2 (hs 0).1

/-- So `Sat` is exactly the condition that rules nothing out — and it is
    the only thing that does. Without it, `⊥` stands beside `≠` as a
    structureless specification that says something. -/
theorem nothing_is_silent :
    Defble (fun a b => a = b ∧ ¬ (a = b))
    ∧ Says (fun a b => a = b ∧ ¬ (a = b))
    ∧ ¬ Sat (fun a b => a = b ∧ ¬ (a = b)) :=
  ⟨bot_defble, bot_says, bot_not_sat⟩

/-- And the identity is the other null case: structureless, satisfied,
    but excluding nothing. It says nothing. -/
theorem eq_defble : Defble (fun a b => a = b) := Defble.eq

theorem eq_not_says : ¬ Says (fun a b => a = b) := by
  intro ⟨x, hx⟩
  exact hx rfl

theorem identity_is_mute :
    Defble (fun a b => a = b)
    ∧ Sat (fun a b => a = b)
    ∧ ¬ Says (fun a b => a = b) :=
  ⟨eq_defble, Or.inl ⟨true, rfl⟩, eq_not_says⟩

/- ---------- the antecedent is inhabited ---------- -/

/-- A conditional whose antecedent nothing satisfies proves nothing, so
    this is checked rather than assumed: the negation graph *is*
    structureless, and it *does* articulate — it excludes a state, and the
    clock satisfies it. `absolute_articulation` is not vacuously true, and
    by `absolute_law` what it is about is unique. -/
theorem absolute_is_inhabited :
    Defble (fun a b => ¬ (a = b)) ∧ Articulates (fun a b => ¬ (a = b)) := by
  refine ⟨Defble.neg Defble.eq, ⟨true, fun h => h rfl⟩, Or.inr ⟨clock true, ?_⟩⟩
  intro n
  exact clock_runs true n

/- ==================================================================
   `Regress`'s two hypotheses about the law
   ================================================================== -/

/- `Regress.lean` reaches its ground from four hypotheses. Two are about
   the *law* — that the ground imports no structure (R3), and that it is
   generative (R4) — and both are discharged here. The other two are
   about the *chain* — that every demand is answered (R1), and that the
   demand relation is well-founded (R2) — and are discharged in
   `Eternal.lean`. -/

/-- Structurelessness has no rival reading. A law on the bare
    distinction that fails to commute with the relabeling is a
    *constant*: there is a value it returns whatever it is given.

    The worry this addresses is that "importing no structure" might mean
    something other than equivariance — that some law could be
    structureless yet fail to commute. This says what such a law would
    have to be: one that ignores the distinction entirely and names a
    value. Far from being the structureless case equivariance missed, it
    is the only case that imports anything at all.

    With `Structureless.structureless_iff_equivariant` (definable from
    pure equality iff equivariant) and `Structureless.constants_not_defble`,
    the residual closes: on the bare distinction there is no third thing
    for "structureless" to mean. -/
theorem non_equivariant_names (f : Bool → Bool)
    (h : ¬ ∀ x, f (!x) = !(f x)) : ∃ c : Bool, ∀ x, f x = c := by
  cases hf : f false <;> cases ht : f true
  · exact ⟨false, fun x => by cases x <;> assumption⟩
  · refine absurd (fun x => ?_) h
    cases x
    · show f true = !(f false); rw [hf, ht]; decide
    · show f false = !(f true); rw [hf, ht]; decide
  · refine absurd (fun x => ?_) h
    cases x
    · show f true = !(f false); rw [hf, ht]; decide
    · show f false = !(f true); rw [hf, ht]; decide
  · exact ⟨true, fun x => by cases x <;> assumption⟩

/-- And a constant is the opposite of structureless: a pure name, with no
    dependence on the distinction at all. -/
theorem constant_ignores_the_distinction (c : Bool) :
    ∀ x y : Bool, (fun _ => c) x = (fun _ => c) y :=
  fun _ _ => rfl

/-- Generativity is not a further hypothesis. A structureless
    specification that excludes even one state excludes every state: it
    has no fixed point at all.

    "Generative" means "moves something", and a specification moves
    something exactly when some state fails to satisfy it. So
    generativity is what saying anything already amounts to. The static
    rival (`x = x`) is not a second structureless metaphysics that a
    premise must exclude by fiat; it is the case where nothing was said
    (`identity_is_mute`). -/
theorem generativity_is_saying_something {R : Bool → Bool → Prop}
    (hD : Defble R) (x : Bool) (hx : ¬ R x x) : ∀ y, ¬ R y y := by
  intro y hy
  apply hx
  cases x <;> cases y
  · exact hy
  · exact (defble_invariant hD true true).mp hy
  · exact (defble_invariant hD false false).mp hy
  · exact hy

end Articulation

/- audit -/
#print axioms Articulation.defble_invariant
#print axioms Articulation.diagonal_uniform
#print axioms Articulation.says_kills_the_object
#print axioms Articulation.absolute_law
#print axioms Articulation.clock_runs
#print axioms Articulation.run_unique
#print axioms Articulation.absolute_articulation
#print axioms Articulation.nothing_is_silent
#print axioms Articulation.identity_is_mute
#print axioms Articulation.absolute_is_inhabited
#print axioms Articulation.non_equivariant_names
#print axioms Articulation.constant_ignores_the_distinction
#print axioms Articulation.generativity_is_saying_something
