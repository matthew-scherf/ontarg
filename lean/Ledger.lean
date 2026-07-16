/-!
# Ledger

Meta-theorems of the verdict calculus. `W` is a class of admissible
worlds; a proposition is `P : W → Prop`. `Forced` means true in every
admissible world; `Refuted` false in every one; `Free` means both
values occur. A vocabulary is a map `v : W → Obs` — what a theory can
see of a world; `P` is expressible in `v` when it factors through `v`.

Main results:
* `ledger_consistent` — `Forced`, `Refuted`, `Free` are pairwise
  exclusive.
* `expressible_monotone` — coarsening a vocabulary only loses
  expressibility, so inexpressibility verdicts are monotone under
  vocabulary restriction.
* `inexpressible_of_free_unseparated` — a free proposition whose
  witness pair the vocabulary identifies is expressible in no such
  vocabulary.
* `settling_needs_new_primitive` — any vocabulary that expresses `P`
  separates every free witness pair: settling a free question requires
  distinguishing worlds the given vocabulary identifies, i.e. a new
  primitive.
* `debate_interminable` — under freedom with identified witnesses, no
  expressible proposition decides `P` in either direction: a debate
  conducted entirely inside the vocabulary cannot terminate in a
  verdict on `P`.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Ledger

variable {W : Type u} {Obs : Type v}

/-- True in every admissible world. -/
def Forced (P : W → Prop) : Prop := ∀ w, P w

/-- False in every admissible world. -/
def Refuted (P : W → Prop) : Prop := ∀ w, ¬ P w

/-- Both values occur across the admissible class. -/
def Free (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

/-- A vocabulary sees `v w` of the world `w`; `P` is expressible when
    its truth is a function of what the vocabulary sees. -/
def Expressible (v : W → Obs) (P : W → Prop) : Prop :=
  ∃ q : Obs → Prop, ∀ w, P w ↔ q (v w)

/-- `Forced`, `Refuted`, `Free` are pairwise exclusive (a world is
    needed for the `Forced`/`Refuted` clash — an empty class forces
    everything vacuously). -/
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

/-- Coarsening only loses: if `P` is expressible through a coarsened
    vocabulary `r ∘ v`, it was expressible through `v`.
    Contrapositive: inexpressibility is monotone under vocabulary
    restriction. -/
theorem expressible_monotone (v : W → Obs) {Obs' : Type w'}
    (r : Obs → Obs') (P : W → Prop)
    (h : Expressible (fun w => r (v w)) P) : Expressible v P := by
  match h with
  | ⟨q, hq⟩ => exact ⟨fun o => q (r o), hq⟩

/-- A free proposition whose witness pair the vocabulary identifies
    is expressible in no such vocabulary. -/
theorem inexpressible_of_free_unseparated (v : W → Obs) (P : W → Prop)
    (w₁ w₂ : W) (h₁ : P w₁) (h₂ : ¬ P w₂) (hsame : v w₁ = v w₂) :
    ¬ Expressible v P := by
  intro he
  match he with
  | ⟨q, hq⟩ =>
    have hq₁ : q (v w₁) := (hq w₁).mp h₁
    have hq₂ : q (v w₂) := hsame ▸ hq₁
    exact h₂ ((hq w₂).mpr hq₂)

/-- Any vocabulary that expresses `P` separates every free witness
    pair: to settle a free question is to distinguish worlds the
    given vocabulary identifies — a new primitive, by definition. -/
theorem settling_needs_new_primitive (v : W → Obs) (P : W → Prop)
    (he : Expressible v P) :
    ∀ w₁ w₂, P w₁ → ¬ P w₂ → v w₁ ≠ v w₂ := by
  intro w₁ w₂ h₁ h₂ hsame
  exact inexpressible_of_free_unseparated v P w₁ w₂ h₁ h₂ hsame he

/-- Under freedom with identified witnesses, no expressible
    proposition decides `P` either way: no expressible `Q` with
    `Q → P` and `¬Q → ¬P` everywhere exists. A debate conducted
    entirely inside the vocabulary cannot terminate in a verdict on
    `P`. -/
theorem debate_interminable (v : W → Obs) (P : W → Prop)
    (w₁ w₂ : W) (h₁ : P w₁) (h₂ : ¬ P w₂) (hsame : v w₁ = v w₂) :
    ¬ ∃ Q : W → Prop, Expressible v Q
        ∧ (∀ w, Q w → P w) ∧ (∀ w, ¬ Q w → ¬ P w) := by
  intro h
  match h with
  | ⟨Q, ⟨q, hq⟩, hQP, hnQnP⟩ =>
    -- Q fails at w₂ (it would force P w₂); the vocabulary carries
    -- that failure to w₁; then ¬Q w₁ forces ¬P w₁ — contradiction.
    have hnQ₂ : ¬ Q w₂ := fun hQ₂ => h₂ (hQP w₂ hQ₂)
    have hnq₂ : ¬ q (v w₂) := fun hqv => hnQ₂ ((hq w₂).mpr hqv)
    have hnq₁ : ¬ q (v w₁) := fun hqv => hnq₂ (hsame ▸ hqv)
    have hnQ₁ : ¬ Q w₁ := fun hQ₁ => hnq₁ ((hq w₁).mp hQ₁)
    exact hnQnP w₁ hnQ₁ h₁

end Ledger

/- audit -/
#print axioms Ledger.ledger_consistent
#print axioms Ledger.expressible_monotone
#print axioms Ledger.inexpressible_of_free_unseparated
#print axioms Ledger.settling_needs_new_primitive
#print axioms Ledger.debate_interminable
