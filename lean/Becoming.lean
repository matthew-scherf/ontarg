/-!
# Becoming

The ontological argument of becoming, assembled in one theorem:
`ontological_argument`.
-/

namespace Becoming

/- link 1: the distinction is drawn -/

/-- Two states of `M` differ. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b

theorem subsingleton_tokens_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Prop → M) : ∀ P Q : Prop, t P = t Q :=
  fun P Q => h (t P) (t Q)

/-- A medium marking `¬ Draws M` differently from `Draws M` draws a distinction. -/
theorem retorsion {M : Type} (t : Prop → M)
    (h : t (¬ Draws M) ≠ t (Draws M)) : Draws M :=
  ⟨t (¬ Draws M), t (Draws M), h⟩

theorem no_undrawn_denial {M : Type} (t : Prop → M) :
    ¬ (t (¬ Draws M) ≠ t (Draws M) ∧ ¬ Draws M) :=
  fun ⟨hd, hn⟩ => hn (retorsion t hd)

/- link 2: the arena is two -/

/-- Transposition of two values. -/
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

/-- `f` commutes with every transposition. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

/-- On three or more values, no equivariant map moves anything. -/
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

theorem bare_one_is_mute {V : Type u} (f : V → V)
    (h1 : ∀ x y : V, x = y) : ∀ x, f x = x :=
  fun x => h1 (f x) x

/-- On `Bool`, negation is equivariant and fixed-point-free. -/
theorem two_speaks :
    Equivariant (fun x : Bool => !x) ∧ (∀ x : Bool, !x ≠ x) := by
  constructor
  · intro a b x; cases a <;> cases b <;> cases x <;> rfl
  · intro x; cases x <;> decide

/- link 3: the candidate -/

/-- `g` commutes with negation. -/
def Structureless (g : Bool → Bool) : Prop := ∀ b, g (!b) = !(g b)

/-- A structureless `g : Bool → Bool` is `id` or `not`. -/
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

theorem constants_not_structureless (c : Bool) :
    ¬ Structureless (fun _ => c) := by
  intro h
  have hc := h true
  revert hc
  cases c <;> decide

theorem id_says_nothing : ∀ b : Bool, id b = b := fun _ => rfl

/- link 3, relational: no structureless spec singles out a state -/

/-- Relations on `Bool` generated from equality by negation, conjunction, disjunction. -/
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

/-- `Defble R` gives `R a a ↔ R b b` for all `a b`. -/
theorem diagonal_uniform {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a a ↔ R b b := by
  intro a b
  cases a <;> cases b
  · exact Iff.rfl
  · exact defble_invariant h false false
  · exact defble_invariant h true true
  · exact Iff.rfl

/- no necessary being -/

theorem no_static_instance : ∀ b : Bool, not b ≠ b := by
  intro b
  cases b <;> decide

/-- `X = ¬X` has no solution. -/
theorem no_being (X : Prop) (h : X = ¬ X) : False :=
  have hiff : X ↔ ¬ X := Iff.of_eq h
  have hn : ¬ X := fun hx => hiff.mp hx hx
  hn (hiff.mpr hn)

/- necessary becoming -/

variable {S : Type u}

/-- `x` solves the recursion `f`. -/
def Solves (f : S → S) (x : Nat → S) : Prop := ∀ n, x (n + 1) = f (x n)

/-- Trajectory of `f` from `seed`. -/
def orbit (f : S → S) (seed : S) : Nat → S
  | 0     => seed
  | n + 1 => f (orbit f seed n)

theorem becoming_exists (f : S → S) (seed : S) :
    Solves f (orbit f seed) ∧ orbit f seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

theorem becoming_unique (f : S → S) (x : Nat → S)
    (hx : Solves f x) (seed : S) (h0 : x 0 = seed) :
    ∀ n, x n = orbit f seed n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, ih]; rfl

/-- `orbit not seed` has period 2. -/
theorem two_tick_clock (seed : Bool) :
    ∀ n, orbit not seed (n + 2) = orbit not seed n := by
  intro n
  show (!(!(orbit not seed n))) = orbit not seed n
  cases orbit not seed n with
  | true  => rfl
  | false => rfl

/- link 4: so it runs, and the law is negation -/

theorem no_fixpoint : ∀ x : Bool, x ≠ !x := by
  intro x; cases x <;> decide

theorem ne_eq_not : ∀ a b : Bool, a ≠ b → b = !a := by
  intro a b h
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

/-- `R` excludes `x`: read of itself, it fails there. -/
def Excludes (R : Bool → Bool → Prop) (x : Bool) : Prop := ¬ R x x

/-- `R` excludes some state. -/
def Says (R : Bool → Bool → Prop) : Prop := ∃ x, Excludes R x

/-- A state satisfies `R` read of itself. -/
def ObjSat (R : Bool → Bool → Prop) : Prop := ∃ x, R x x

/-- An unending run each of whose steps satisfies `R`. -/
def ProcSat (R : Bool → Bool → Prop) : Prop :=
  ∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1))

/-- `R` is satisfied in some frame. -/
def Sat (R : Bool → Bool → Prop) : Prop := ObjSat R ∨ ProcSat R

/-- `R` excludes something and is satisfied somewhere. -/
def Articulates (R : Bool → Bool → Prop) : Prop := Says R ∧ Sat R

theorem says_kills_the_object {R : Bool → Bool → Prop}
    (hD : Defble R) (hS : Says R) : ¬ ObjSat R := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hS
  exact hy ((diagonal_uniform hD x y).mp hx)

theorem clock_runs (b : Bool) :
    ∀ n, orbit not b n ≠ orbit not b (n + 1) :=
  fun n => no_fixpoint (orbit not b n)

theorem run_unique {t : Nat → Bool} (ht : ∀ n, t n ≠ t (n + 1)) :
    ∀ n, t n = orbit not (t 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show t (n + 1) = !(orbit not (t 0) n)
    rw [← ih]
    exact ne_eq_not (t n) (t (n + 1)) (ht n)

/-- A `Defble`, `Articulates` relation is `R a b ↔ a ≠ b`. -/
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

/-- `Defble`, `Articulates` `R`: its law is negation, its object frame is
    empty, its process frame is inhabited, and its run is unique given a seed.
    The general route to actuality: holds for any such `R`, independently of
    the concrete tokening argument in `denial_ticks_the_clock` below. -/
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

theorem absolute_is_inhabited :
    Defble (fun a b => ¬ (a = b)) ∧ Articulates (fun a b => ¬ (a = b)) := by
  refine ⟨Defble.neg Defble.eq, ⟨true, fun h => h rfl⟩,
    Or.inr ⟨orbit not true, ?_⟩⟩
  intro n
  exact clock_runs true n

/- link 5: one fact, two frames -/

theorem refusal_is_running (f : S → S) :
    (∀ x, f x ≠ x) ↔ ∀ seed n, orbit f seed (n + 1) ≠ orbit f seed n := by
  constructor
  · intro h seed n
    exact h (orbit f seed n)
  · intro h x
    exact h x 0

/- link 6: the seed is a label, not a premise -/

/-- Relabelling a run: negate every value. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => !(s n)

theorem seed_is_relabel :
    ∀ n, orbit not false n = relabel (orbit not true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show not (orbit not false n) = not (orbit not true (n + 1))
    rw [ih]
    rfl


/- the token -/

theorem denial_self_refutes {A : Type} (a : A) : ¬ ¬ (∃ x : A, x = a) :=
  fun h => h ⟨a, rfl⟩

/- link 7: the tokening is an event -/

/-- The configuration of `h` differs at two times. -/
def Occurs {T : Type} (h : T → Bool) : Prop := ∃ t₁ t₂ : T, h t₁ ≠ h t₂

theorem event_retorsion {T : Type} (h : T → Bool) (tok : Prop → T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) : Occurs h :=
  ⟨tok (¬ Occurs h), tok (Occurs h), hd⟩

/-- The concrete route to actuality: the tokening of the denial that `h`
    runs is itself a tick of it. Independent of `absolute_articulation`
    above: this argues the specific case directly, without `Defble` or
    `Articulates`. -/
theorem denial_ticks_the_clock {T : Type} (h : T → Bool)
    (tok : Prop → T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) :
    Occurs h
    ∧ tok (¬ Occurs h) ≠ tok (Occurs h)
    ∧ h (tok (Occurs h)) = orbit not (h (tok (¬ Occurs h))) 1 :=
  ⟨event_retorsion h tok hd,
   fun he => hd (congrArg h he),
   ne_eq_not _ _ hd⟩

/- the conjunction -/

/-- The ontological argument of becoming, with no premise at any link. -/
theorem ontological_argument :
    -- 1. the distinction is drawn
    (∀ (M : Type) (t : Prop → M), t (¬ Draws M) ≠ t (Draws M) → Draws M)
    -- 2. the arena is two
    ∧ (∀ (V : Type) (f : V → V), (∀ x y : V, x = y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, !x ≠ x)
    -- 3. one candidate: structureless laws are {id, not}
    ∧ (∀ g : Bool → Bool, Structureless g →
        (∀ b, g b = b) ∨ (∀ b, g b = !b))
    ∧ (∀ c : Bool, ¬ Structureless (fun _ => c))
    ∧ (∀ b : Bool, id b = b)
    ∧ (∀ R : Bool → Bool → Prop, Defble R → ∀ a b, R a a ↔ R b b)
    -- 4. so the absolute runs, and can only run
    ∧ (∀ R : Bool → Bool → Prop, Defble R → Articulates R →
        (∀ a b, R a b ↔ a ≠ b)
        ∧ (¬ ∃ x, R x x)
        ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
        ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
            ∀ n, t n = orbit not (t 0) n))
    -- no necessary being: nothing static answers to the ground
    ∧ (∀ b : Bool, not b ≠ b)
    ∧ (∀ X : Prop, X = ¬ X → False)
    -- necessary becoming: the run exists, is unique, has period two
    ∧ (∀ seed : Bool,
        (Solves not (orbit not seed) ∧ orbit not seed 0 = seed)
        ∧ (∀ x, Solves not x → x 0 = seed →
            ∀ n, x n = orbit not seed n)
        ∧ (∀ n, orbit not seed (n + 2) = orbit not seed n))
    -- 5. the refusal is the running
    ∧ ((∀ b : Bool, not b ≠ b) ↔
        ∀ seed n, orbit not seed (n + 1) ≠ orbit not seed n)
    -- 6. the seed is a label, not a premise
    ∧ (∀ n, orbit not false n = relabel (orbit not true) n)
    -- 7. the tokening is an event
    ∧ (∀ (T : Type) (h : T → Bool) (tok : Prop → T),
        h (tok (¬ Occurs h)) ≠ h (tok (Occurs h)) →
        Occurs h
        ∧ tok (¬ Occurs h) ≠ tok (Occurs h)
        ∧ h (tok (Occurs h)) = orbit not (h (tok (¬ Occurs h))) 1) :=
  ⟨fun _ t h => retorsion t h,
   fun _ f h1 => bare_one_is_mute f h1,
   fun _ _ f he h3 => bare_three_is_mute f he h3,
   two_speaks,
   one_candidate,
   constants_not_structureless,
   id_says_nothing,
   fun _ hD => diagonal_uniform hD,
   fun _ hD hA => absolute_articulation hD hA,
   no_static_instance,
   no_being,
   fun seed =>
     ⟨becoming_exists not seed,
      fun x hx h0 => becoming_unique not x hx seed h0,
      two_tick_clock seed⟩,
   refusal_is_running not,
   seed_is_relabel,
   fun _ h tok hd => denial_ticks_the_clock h tok hd⟩

end Becoming

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
#print axioms Becoming.denial_self_refutes
#print axioms Becoming.event_retorsion
#print axioms Becoming.denial_ticks_the_clock
#print axioms Becoming.ontological_argument
