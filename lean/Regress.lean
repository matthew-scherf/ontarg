/-!
# Regress

Every well-founded, answered chain of grounding demands terminates in
an unseeded ground, and an unseeded generative ground has the one
shape classified in `OnlyShape.lean`. Every residual assumption is a
named hypothesis in the theorem signatures:

* `answered` — every seeded specification's demand for a ground is
  answered by some ground.
* `wf` — no infinite regress: the demand relation is well-founded.
* `structureless` — an unseeded ground imports no structure: its law
  on the bare distinction commutes with relabeling (equivariance, as
  in `OnlyShape.lean`).
* `generative` — the ground's law moves something.

Main results:
* `equivariant_id_or_not` — the classification on the Bool arena,
  re-proved locally.
* `regress_terminates` — under `answered` and `wf`, every
  specification's demand chain reaches an unseeded ground.
* `ground_has_one_shape` — adding `structureless` and `generative`,
  the reached ground's law is negation.
* `time_selects_the_shape` — the corollary at an occurrent
  specification: if something runs, its demand chain grounds in a
  specification whose law is `x = ¬x`.

Lean 4, prelude only; no imports. Axiom footprint:
`regress_terminates` and its dependents use `Classical.choice`
(`Classical.byCases` on `Seeded`); the whole file is within
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Regress

variable {S : Type u}

/- ---------- descent along answered demands ---------- -/

/-- Desc dem a s: from s, following answered demands downward,
    reach a. `head` prepends one demand step at the top. -/
inductive Desc (dem : S → S → Prop) : S → S → Prop
  | refl (s : S) : Desc dem s s
  | head {s g a : S} : dem g s → Desc dem a g → Desc dem a s

/-- Under `answered` and `wf`, every specification's demand chain
    terminates in an unseeded ground. Proof: well-founded induction on
    the demand relation; at each seeded point the answered demand
    descends, and descent cannot continue forever. -/
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

/- ---------- the one shape (as in OnlyShape.lean) ---------- -/

/-- Structurelessness on the bare distinction: the law commutes with
    the relabeling — it can name no element (`OnlyShape.lean`'s
    equivariance, re-declared so the file stands alone). -/
def Equivariant (h : Bool → Bool) : Prop := ∀ b, h (!b) = !(h b)

/-- The classification, re-proved locally: an equivariant law on the
    bare distinction is the identity or the negation
    (`OnlyShape.equivariant_endomaps`). -/
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

/- ---------- the ground's shape ---------- -/

/-- Under the named hypotheses — demands answered, no infinite
    regress, unseeded grounds structureless — and excluding the
    contentless identity, every specification's demand chain
    terminates in a ground whose law on the bare distinction is
    negation: `x = ¬x`. -/
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

/-- The corollary at an occurrent specification: if a specification
    is running, its demand chain grounds in a specification whose law
    is `x = ¬x`. The hypotheses are carried, by name, in the
    signature. -/
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

/- audit -/
#print axioms Regress.regress_terminates
#print axioms Regress.equivariant_id_or_not
#print axioms Regress.ground_has_one_shape
#print axioms Regress.time_selects_the_shape
