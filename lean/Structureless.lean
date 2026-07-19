/-!
# Structureless

On the bare distinction, a law is definable from pure equality alone
iff it is equivariant.
-/

namespace Structureless

/-- Binary relations on `Bool` definable from the equality atom, closed
    under negation, conjunction, disjunction. -/
inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

/-- `R` is the graph of `f`. -/
def Graph (f : Bool → Bool) (R : Bool → Bool → Prop) : Prop :=
  ∀ a b, R a b ↔ f a = b

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

theorem graph_equivariant (f : Bool → Bool) {R : Bool → Bool → Prop}
    (hR : Defble R) (hg : Graph f R) :
    ∀ x, f (!x) = !(f x) := by
  intro x
  have h1 : R x (f x) := (hg x (f x)).mpr rfl
  have h2 : R (!x) (!(f x)) := (defble_invariant hR x (f x)).mp h1
  exact (hg (!x) (!(f x))).mp h2

/-- As `OnlyShape.lean`, restated pointwise. -/
theorem equivariant_id_or_not (f : Bool → Bool)
    (h : ∀ x, f (!x) = !(f x)) :
    (∀ x, f x = x) ∨ (∀ x, f x = !x) := by
  have h1 : f true = !(f false) := h false
  cases hf : f false with
  | false =>
    left; intro x; cases x
    · exact hf
    · rw [h1, hf]; rfl
  | true =>
    right; intro x; cases x
    · rw [hf]; rfl
    · rw [h1, hf]

theorem equivariant_graph_defble (f : Bool → Bool)
    (h : ∀ x, f (!x) = !(f x)) :
    ∃ R, Defble R ∧ Graph f R := by
  cases equivariant_id_or_not f h with
  | inl hid =>
    refine ⟨fun a b => a = b, Defble.eq, ?_⟩
    intro a b
    rw [hid a]
  | inr hnot =>
    refine ⟨fun a b => ¬ (a = b), Defble.neg Defble.eq, ?_⟩
    intro a b
    rw [hnot a]
    cases a <;> cases b <;> decide

theorem constants_not_defble (c : Bool) :
    ¬ ∃ R, Defble R ∧ Graph (fun _ => c) R := by
  intro h
  cases h with
  | intro R hR =>
    have h1 : R true c := (hR.2 true c).mpr rfl
    have h2 : R false (!c) := (defble_invariant hR.1 true c).mp h1
    have h3 : c = !c := (hR.2 false (!c)).mp h2
    cases c <;> exact Bool.noConfusion h3

theorem structureless_iff_equivariant (f : Bool → Bool) :
    (∃ R, Defble R ∧ Graph f R) ↔ (∀ x, f (!x) = !(f x)) := by
  constructor
  · intro h
    cases h with
    | intro R hR => exact graph_equivariant f hR.1 hR.2
  · exact equivariant_graph_defble f

end Structureless

#print axioms Structureless.defble_invariant
#print axioms Structureless.graph_equivariant
#print axioms Structureless.equivariant_id_or_not
#print axioms Structureless.equivariant_graph_defble
#print axioms Structureless.constants_not_defble
#print axioms Structureless.structureless_iff_equivariant
