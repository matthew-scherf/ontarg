/-!
# Ledger

`W` a class of admissible worlds, `P : W → Prop`. `Forced`: true in
every world. `Refuted`: false in every world. `Free`: both values
occur. A vocabulary `v : W → Obs`; `P` is expressible in `v` when it
factors through `v`.

Axiom footprint: none.
-/

namespace Ledger

variable {W : Type u} {Obs : Type v}

def Forced (P : W → Prop) : Prop := ∀ w, P w

def Refuted (P : W → Prop) : Prop := ∀ w, ¬ P w

def Free (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

def Expressible (v : W → Obs) (P : W → Prop) : Prop :=
  ∃ q : Obs → Prop, ∀ w, P w ↔ q (v w)

/-- `Forced`, `Refuted`, `Free` are pairwise exclusive. -/
theorem ledger_consistent (P : W → Prop) :
    (¬ (Forced P ∧ Free P))
    ∧ (¬ (Refuted P ∧ Free P))
    ∧ (∀ _w : W, ¬ (Forced P ∧ Refuted P)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    match h with
    | ⟨hf, _, ⟨w, hnw⟩⟩ => exact hnw (hf w)
  · intro h
    match h with
    | ⟨hr, ⟨w, hw⟩, _⟩ => exact hr w hw
  · intro w h
    match h with
    | ⟨hf, hr⟩ => exact hr w (hf w)

/-- Coarsening a vocabulary only loses expressibility. -/
theorem expressible_monotone (v : W → Obs) {Obs' : Type w'}
    (r : Obs → Obs') (P : W → Prop)
    (h : Expressible (fun w => r (v w)) P) : Expressible v P := by
  match h with
  | ⟨q, hq⟩ => exact ⟨fun o => q (r o), hq⟩

theorem inexpressible_of_free_unseparated (v : W → Obs) (P : W → Prop)
    (w₁ w₂ : W) (h₁ : P w₁) (h₂ : ¬ P w₂) (hsame : v w₁ = v w₂) :
    ¬ Expressible v P := by
  intro he
  match he with
  | ⟨q, hq⟩ =>
    have hq₁ : q (v w₁) := (hq w₁).mp h₁
    have hq₂ : q (v w₂) := hsame ▸ hq₁
    exact h₂ ((hq w₂).mpr hq₂)

theorem settling_needs_new_primitive (v : W → Obs) (P : W → Prop)
    (he : Expressible v P) :
    ∀ w₁ w₂, P w₁ → ¬ P w₂ → v w₁ ≠ v w₂ := by
  intro w₁ w₂ h₁ h₂ hsame
  exact inexpressible_of_free_unseparated v P w₁ w₂ h₁ h₂ hsame he

/-- Under freedom with identified witnesses, no expressible `Q` decides `P`. -/
theorem debate_interminable (v : W → Obs) (P : W → Prop)
    (w₁ w₂ : W) (h₁ : P w₁) (h₂ : ¬ P w₂) (hsame : v w₁ = v w₂) :
    ¬ ∃ Q : W → Prop, Expressible v Q
        ∧ (∀ w, Q w → P w) ∧ (∀ w, ¬ Q w → ¬ P w) := by
  intro h
  match h with
  | ⟨Q, ⟨q, hq⟩, hQP, hnQnP⟩ =>
    have hnQ₂ : ¬ Q w₂ := fun hQ₂ => h₂ (hQP w₂ hQ₂)
    have hnq₂ : ¬ q (v w₂) := fun hqv => hnQ₂ ((hq w₂).mpr hqv)
    have hnq₁ : ¬ q (v w₁) := fun hqv => hnq₂ (hsame ▸ hqv)
    have hnQ₁ : ¬ Q w₁ := fun hQ₁ => hnq₁ ((hq w₁).mp hQ₁)
    exact hnQnP w₁ hnQ₁ h₁

end Ledger

#print axioms Ledger.ledger_consistent
#print axioms Ledger.expressible_monotone
#print axioms Ledger.inexpressible_of_free_unseparated
#print axioms Ledger.settling_needs_new_primitive
#print axioms Ledger.debate_interminable
