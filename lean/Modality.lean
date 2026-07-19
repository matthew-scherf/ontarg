/-!
# Modality

`W` a class of worlds, all mutually accessible: the resulting modal
logic is S5.
-/

namespace Modality

variable {W : Type u}

/-- True at every world. -/
def Nec (P : W → Prop) : Prop := ∀ w, P w

/-- True at some world. -/
def Poss (P : W → Prop) : Prop := ∃ w, P w

/-- False at every world. -/
def Impossible (P : W → Prop) : Prop := ∀ w, ¬ P w

/-- Both values occur. -/
def Contingent (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

/-- K. -/
theorem axiom_K (P Q : W → Prop)
    (hpq : Nec (fun w => P w → Q w)) (hp : Nec P) : Nec Q :=
  fun w => hpq w (hp w)

/-- T. -/
theorem axiom_T (P : W → Prop) (h : Nec P) (w : W) : P w := h w

/-- 4. -/
theorem axiom_four (P : W → Prop) (h : Nec P) :
    Nec (fun _ : W => Nec P) := fun _ => h

/-- 5. -/
theorem axiom_five (P : W → Prop) (h : Poss P) :
    Nec (fun _ : W => Poss P) := fun _ => h

theorem modality_is_S5 :
    (∀ P Q : W → Prop, Nec (fun w => P w → Q w) → Nec P → Nec Q)
    ∧ (∀ (P : W → Prop), Nec P → ∀ w, P w)
    ∧ (∀ P : W → Prop, Nec P → Nec (fun _ : W => Nec P))
    ∧ (∀ P : W → Prop, Poss P → Nec (fun _ : W => Poss P)) :=
  ⟨axiom_K, axiom_T, axiom_four, axiom_five⟩

/-- Necessity and possibility are duals. -/
theorem nec_dual (P : W → Prop) :
    Nec P ↔ ¬ Poss (fun w => ¬ P w) := by
  constructor
  · intro h hp
    match hp with
    | ⟨w, hnw⟩ => exact hnw (h w)
  · intro h w
    exact Classical.byContradiction (fun hn => h ⟨w, hn⟩)

/-- Every proposition is necessary, impossible, or contingent over the class. -/
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

/-- Necessity is relative to the class: it survives restriction to any subclass. -/
theorem nec_of_subclass (P : W → Prop) (C : W → Prop)
    (h : Nec P) : ∀ w : {x : W // C x}, P w.1 :=
  fun w => h w.1

end Modality

#print axioms Modality.axiom_K
#print axioms Modality.axiom_T
#print axioms Modality.axiom_four
#print axioms Modality.axiom_five
#print axioms Modality.modality_is_S5
#print axioms Modality.nec_dual
#print axioms Modality.verdict_trichotomy
#print axioms Modality.nec_of_subclass
