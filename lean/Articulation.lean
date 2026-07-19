/-!
# Articulation
-/

namespace Articulation

/-- Relations on `Bool` definable from equality alone. -/
inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

/-- Every `Defble` relation is invariant under negation of both arguments. -/
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

/-- A `Defble` relation holds of every state read of itself, or of none. -/
theorem diagonal_uniform {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a a ↔ R b b := by
  intro a b
  cases a <;> cases b
  · exact Iff.rfl
  · exact defble_invariant h false false
  · exact defble_invariant h true true
  · exact Iff.rfl

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

/-- A state satisfying `R` read of itself. -/
def ObjSat (R : Bool → Bool → Prop) : Prop := ∃ x, R x x

/-- An unending run each of whose steps satisfies `R`. -/
def ProcSat (R : Bool → Bool → Prop) : Prop :=
  ∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1))

def Sat (R : Bool → Bool → Prop) : Prop := ObjSat R ∨ ProcSat R

def Articulates (R : Bool → Bool → Prop) : Prop := Says R ∧ Sat R

/-- A `Defble` relation excluding any state excludes every state. -/
theorem says_kills_the_object {R : Bool → Bool → Prop}
    (hD : Defble R) (hS : Says R) : ¬ ObjSat R := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hS
  exact hy ((diagonal_uniform hD x y).mp hx)

/-- A `Defble` `R` that articulates is the negation graph: `R a b ↔ a ≠ b`. -/
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
  have hne : s 0 ≠ s 1 := by
    intro he
    exact hdiag (s 0) (he ▸ hstep)
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
  · intro hab he
    exact hdiag a (he ▸ hab)
  · intro hab
    exact (ne_eq_not a b hab) ▸ hoff a

/-- The two-tick clock from a seed. -/
def clock (s : Bool) : Nat → Bool
  | 0 => s
  | n + 1 => !(clock s n)

theorem clock_runs (b : Bool) : ∀ n, clock b n ≠ clock b (n + 1) := by
  intro n
  exact no_fixpoint (clock b n)

/-- Any run of the negation graph is the clock on its seed. -/
theorem run_unique {t : Nat → Bool} (ht : ∀ n, t n ≠ t (n + 1)) :
    ∀ n, t n = clock (t 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show t (n + 1) = !(clock (t 0) n)
    rw [← ih]
    exact ne_eq_not (t n) (t (n + 1)) (ht n)

/-- For `Defble` `R` that articulates: its law is negation, its object frame
    is empty, its process frame is inhabited, and its run is the clock. -/
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

theorem bot_defble : Defble (fun a b => a = b ∧ ¬ (a = b)) :=
  Defble.conj Defble.eq (Defble.neg Defble.eq)

theorem bot_says : Says (fun a b => a = b ∧ ¬ (a = b)) :=
  ⟨true, fun h => h.2 h.1⟩

theorem bot_not_sat : ¬ Sat (fun a b => a = b ∧ ¬ (a = b)) := by
  intro h
  cases h with
  | inl hobj => obtain ⟨x, hx⟩ := hobj; exact hx.2 hx.1
  | inr hproc => obtain ⟨s, hs⟩ := hproc; exact (hs 0).2 (hs 0).1

/-- `⊥` is `Defble` and `Says` but not `Sat`. -/
theorem nothing_is_silent :
    Defble (fun a b => a = b ∧ ¬ (a = b))
    ∧ Says (fun a b => a = b ∧ ¬ (a = b))
    ∧ ¬ Sat (fun a b => a = b ∧ ¬ (a = b)) :=
  ⟨bot_defble, bot_says, bot_not_sat⟩

theorem eq_defble : Defble (fun a b => a = b) := Defble.eq

theorem eq_not_says : ¬ Says (fun a b => a = b) := by
  intro ⟨x, hx⟩
  exact hx rfl

/-- Equality is `Defble` and `Sat` but not `Says`. -/
theorem identity_is_mute :
    Defble (fun a b => a = b)
    ∧ Sat (fun a b => a = b)
    ∧ ¬ Says (fun a b => a = b) :=
  ⟨eq_defble, Or.inl ⟨true, rfl⟩, eq_not_says⟩

/-- The negation graph is `Defble` and `Articulates`. -/
theorem absolute_is_inhabited :
    Defble (fun a b => ¬ (a = b)) ∧ Articulates (fun a b => ¬ (a = b)) := by
  refine ⟨Defble.neg Defble.eq, ⟨true, fun h => h rfl⟩, Or.inr ⟨clock true, ?_⟩⟩
  intro n
  exact clock_runs true n

/-- A non-equivariant law on `Bool` is constant. -/
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

theorem constant_ignores_the_distinction (c : Bool) :
    ∀ x y : Bool, (fun _ => c) x = (fun _ => c) y :=
  fun _ _ => rfl

/-- A `Defble` relation excluding one state excludes every state. -/
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
