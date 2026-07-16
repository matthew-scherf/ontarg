/-!
# Modality

The verdict calculus is a modal logic, and this file says which one.
`W` is a class of admissible worlds, as in `Ledger.lean`; necessity is
truth at every admissible world, possibility truth at some. With every
world seeing every world — no accessibility structure assumed or
available — the logic is S5: K and T hold, iteration is flat, and the
possible is necessarily possible. Contingency is `Ledger`'s `Free`;
the three verdicts exhaust classically; and necessity is a fact about
the class, not about any world in it.

Main results:
* `axiom_K` — necessity distributes over implication.
* `axiom_T` — the necessary holds at every (hence any actual) world.
* `axiom_four`, `axiom_five` — `Nec P → Nec (Nec P)` and
  `Poss P → Nec (Poss P)`: iterated modality adds nothing.
* `modality_is_S5` — the conjunction.
* `nec_dual` — necessity and possibility are duals (classical in one
  direction).
* `verdict_trichotomy` — every proposition is necessary, impossible,
  or contingent over the class (classical).
* `nec_of_subclass` — necessity survives restriction of the class:
  what is necessary over a class is necessary over any subclass.
  Modal status is class-relative, not world-intrinsic.

Lean 4, prelude only; no imports. Axiom footprint: within
`[propext, Classical.choice, Quot.sound]` (`nec_dual`,
`verdict_trichotomy`); `axiom_K`–`modality_is_S5` and
`nec_of_subclass` axiom-free.
-/

namespace Modality

variable {W : Type u}

/-- Necessary: true at every admissible world (`Ledger.Forced`). -/
def Nec (P : W → Prop) : Prop := ∀ w, P w

/-- Possible: true at some admissible world. -/
def Poss (P : W → Prop) : Prop := ∃ w, P w

/-- Impossible: false at every admissible world (`Ledger.Refuted`). -/
def Impossible (P : W → Prop) : Prop := ∀ w, ¬ P w

/-- Contingent: both values occur (`Ledger.Free`). -/
def Contingent (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

/-- K: necessity distributes over implication. -/
theorem axiom_K (P Q : W → Prop)
    (hpq : Nec (fun w => P w → Q w)) (hp : Nec P) : Nec Q :=
  fun w => hpq w (hp w)

/-- T: the necessary is true — at every world, hence at whichever one
    is actual. -/
theorem axiom_T (P : W → Prop) (h : Nec P) (w : W) : P w := h w

/-- 4: the necessary is necessarily necessary. Iteration is flat
    because necessity is a fact about the class, the same seen from
    every world. -/
theorem axiom_four (P : W → Prop) (h : Nec P) :
    Nec (fun _ : W => Nec P) := fun _ => h

/-- 5: the possible is necessarily possible, for the same reason. -/
theorem axiom_five (P : W → Prop) (h : Poss P) :
    Nec (fun _ : W => Poss P) := fun _ => h

/-- The conjunction: over an admissible class with no accessibility
    structure, the modal logic of the verdicts is S5. -/
theorem modality_is_S5 :
    (∀ P Q : W → Prop, Nec (fun w => P w → Q w) → Nec P → Nec Q)
    ∧ (∀ (P : W → Prop), Nec P → ∀ w, P w)
    ∧ (∀ P : W → Prop, Nec P → Nec (fun _ : W => Nec P))
    ∧ (∀ P : W → Prop, Poss P → Nec (fun _ : W => Poss P)) :=
  ⟨axiom_K, axiom_T, axiom_four, axiom_five⟩

/-- Necessity and possibility are duals. The right-to-left direction
    is classical: from "no world refutes `P`" to "every world holds
    `P`". -/
theorem nec_dual (P : W → Prop) :
    Nec P ↔ ¬ Poss (fun w => ¬ P w) := by
  constructor
  · intro h hp
    match hp with
    | ⟨w, hnw⟩ => exact hnw (h w)
  · intro h w
    exact Classical.byContradiction (fun hn => h ⟨w, hn⟩)

/-- Every proposition is necessary, impossible, or contingent over
    the class (classical case split; over an empty class the first
    two both hold vacuously). -/
theorem verdict_trichotomy (P : W → Prop) :
    Nec P ∨ Impossible P ∨ Contingent P := by
  cases Classical.em (∃ w, P w) with
  | inr hno =>
      exact Or.inr (Or.inl (fun w hw => hno ⟨w, hw⟩))
  | inl hyes =>
      cases Classical.em (∃ w, ¬ P w) with
      | inl hneg => exact Or.inr (Or.inr ⟨hyes, hneg⟩)
      | inr hnoneg =>
          exact Or.inl (fun w =>
            Classical.byContradiction (fun hn => hnoneg ⟨w, hn⟩))

/-- Necessity survives restriction: necessary over the class,
    necessary over any subclass. Modal status is relative to the
    admissible class — there is no world-intrinsic necessity to
    outrun it. -/
theorem nec_of_subclass (P : W → Prop) (C : W → Prop)
    (h : Nec P) : ∀ w : {x : W // C x}, P w.1 :=
  fun w => h w.1

end Modality

/- audit -/
#print axioms Modality.axiom_K
#print axioms Modality.axiom_T
#print axioms Modality.axiom_four
#print axioms Modality.axiom_five
#print axioms Modality.modality_is_S5
#print axioms Modality.nec_dual
#print axioms Modality.verdict_trichotomy
#print axioms Modality.nec_of_subclass
