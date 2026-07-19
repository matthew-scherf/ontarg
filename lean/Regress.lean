/-!
# Regress

Every well-founded, answered chain of grounding demands terminates in
an unseeded ground; an unseeded, structureless, generative ground has
the shape classified in `OnlyShape.lean`.
-/

namespace Regress

variable {S : Type u}

/-- `Desc dem a s`: from `s`, following answered demands downward, reach `a`. -/
inductive Desc (dem : S → S → Prop) : S → S → Prop
  | refl (s : S) : Desc dem s s
  | head {s g a : S} : dem g s → Desc dem a g → Desc dem a s

theorem regress_terminates (Seeded : S → Prop) (dem : S → S → Prop)
    (wf : WellFounded dem)
    (answered : ∀ s, Seeded s → ∃ g, dem g s) :
    ∀ s, ∃ g, Desc dem g s ∧ ¬ Seeded g := by
  intro s
  refine WellFounded.induction (C := fun t => ∃ g, Desc dem g t ∧ ¬ Seeded g)
    wf s ?_
  intro x ih
  refine Classical.byCases (fun hx : Seeded x => ?_) (fun hx : ¬ Seeded x => ?_)
  · match answered x hx with
    | ⟨g, hgx⟩ =>
      match ih g hgx with
      | ⟨g', hdesc, hns⟩ => exact ⟨g', Desc.head hgx hdesc, hns⟩
  · exact ⟨x, Desc.refl x, hx⟩

/-- Equivariance on the bare distinction (as `OnlyShape.lean`). -/
def Equivariant (h : Bool → Bool) : Prop := ∀ b, h (!b) = !(h b)

theorem equivariant_id_or_not (h : Bool → Bool) (he : Equivariant h) :
    (∀ b, h b = b) ∨ (∀ b, h b = !b) := by
  cases htrue : h true with
  | true =>
    left
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := he true
      rw [htrue] at hf
      exact hf
  | false =>
    right
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := he true
      rw [htrue] at hf
      exact hf

theorem ground_has_one_shape (Seeded : S → Prop) (dem : S → S → Prop)
    (law : S → Bool → Bool)
    (wf : WellFounded dem)
    (answered : ∀ s, Seeded s → ∃ g, dem g s)
    (structureless : ∀ s, ¬ Seeded s → Equivariant (law s))
    (generative : ∀ s, ¬ Seeded s → ∃ b, law s b ≠ b)
    (s : S) :
    ∃ g, Desc dem g s ∧ ¬ Seeded g ∧ (∀ b, law g b = !b) := by
  match regress_terminates Seeded dem wf answered s with
  | ⟨g, hdesc, hns⟩ =>
    refine ⟨g, hdesc, hns, ?_⟩
    cases equivariant_id_or_not (law g) (structureless g hns) with
    | inl hid =>
      match generative g hns with
      | ⟨b, hb⟩ => exact absurd (hid b) hb
    | inr hneg => exact hneg

theorem time_selects_the_shape (Seeded : S → Prop) (dem : S → S → Prop)
    (law : S → Bool → Bool)
    (wf : WellFounded dem)
    (answered : ∀ s, Seeded s → ∃ g, dem g s)
    (structureless : ∀ s, ¬ Seeded s → Equivariant (law s))
    (generative : ∀ s, ¬ Seeded s → ∃ b, law s b ≠ b)
    (occurrent : S) :
    ∃ g, Desc dem g occurrent ∧ ¬ Seeded g ∧ (∀ b, law g b = !b) :=
  ground_has_one_shape Seeded dem law wf answered structureless
    generative occurrent

end Regress

#print axioms Regress.regress_terminates
#print axioms Regress.equivariant_id_or_not
#print axioms Regress.ground_has_one_shape
#print axioms Regress.time_selects_the_shape
