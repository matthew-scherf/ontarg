/-!
# SelfDerivation

The diagonal no-go for interior self-derivation. `ValueForm.lean`
leaves one escape open: a describer unbounded in depth, knowing the
law, might hope to derive the seat-indexed quantity map itself and
read off its own coordinate. This file closes it. A self-inclusive
describer's repertoire is `e : S → S → Bool` — its procedures are
quantities over seats because the describer is in the world it
describes — and its self-reading at `s` is the diagonal `e s s`.

Main results:
* `repertoire_incomplete` — no self-inclusive repertoire is complete.
* `no_self_derivation` — no seat self-derives the anti-diagonal
  record `r s = !(e s s)`.
* `repertoire_escape` — no seat's procedure computes that record
  anywhere.
* `formclass_miss_benign` / `valueclass_miss_structural` /
  `two_obstructions` — the two failure modes are different in kind: a
  form-class anti-diagonal is still law-derivable in principle; a
  value-class one is underivable in principle.

Bool-valued quantities suffice: one bit is all the no-go needs.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace SelfDerivation

/-- Form-class, as in `ValueForm.lean` (re-declared, standalone). -/
def FormClass {S : Type u} {B : Type v} (q : S → B) : Prop :=
  ∀ s t : S, q s = q t

/-- Value-class, as in `ValueForm.lean` (re-declared, standalone). -/
def ValueClass {S : Type u} {B : Type v} (q : S → B) : Prop :=
  ∃ s t : S, q s ≠ q t

/-- A law-side derivation, as in `ValueForm.lean`. -/
def LawDerivation {S : Type u} {B : Type v} (q : S → B) (b : B) : Prop :=
  ∀ s, q s = b

/-- The anti-diagonal record: what each seat's record holds is the
    negation of what that seat's procedure says about itself. -/
def antidiagonal {S : Type u} (e : S → S → Bool) : S → Bool :=
  fun s => !(e s s)

/-- No self-inclusive repertoire is complete (the Lawvere argument in
    this vocabulary). -/
theorem repertoire_incomplete {S : Type u} (e : S → S → Bool) :
    ¬ ∀ q : S → Bool, ∃ s, e s = q := by
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj (antidiagonal e)
  have h := congrFun hs s
  simp [antidiagonal] at h

/-- No seat self-derives the anti-diagonal record. -/
theorem no_self_derivation {S : Type u} (e : S → S → Bool) (s : S) :
    e s s ≠ antidiagonal e s := by
  simp [antidiagonal]

/-- The anti-diagonal record escapes the whole repertoire: no seat's
    procedure computes it anywhere. -/
theorem repertoire_escape {S : Type u} (e : S → S → Bool) (t : S) :
    e t ≠ antidiagonal e := by
  intro h
  exact no_self_derivation e t (congrFun h t)

/-- First failure mode: a form-class anti-diagonal is still
    law-derivable in principle — the miss is the repertoire's, and it
    is benign for the split. -/
theorem formclass_miss_benign {S : Type u} [Inhabited S]
    (e : S → S → Bool) (h : FormClass (antidiagonal e)) :
    ∃ b, LawDerivation (antidiagonal e) b :=
  ⟨antidiagonal e default, fun s => h s default⟩

/-- Second failure mode: a value-class anti-diagonal is underivable in
    principle — the structural failure. -/
theorem valueclass_miss_structural {S : Type u} (e : S → S → Bool)
    (h : ValueClass (antidiagonal e)) :
    ¬ ∃ b, LawDerivation (antidiagonal e) b := by
  intro ⟨b, hb⟩
  obtain ⟨s, t, hst⟩ := h
  exact hst (by rw [hb s, hb t])

/-- Assembled: either way, no seat self-derives the record —
    self-reference and seat-relativity are distinct obstructions and
    both stand under self-inclusion. -/
theorem two_obstructions {S : Type u} [Inhabited S] (e : S → S → Bool) :
    (∀ s, e s s ≠ antidiagonal e s) ∧
    (FormClass (antidiagonal e) →
      ∃ b, LawDerivation (antidiagonal e) b) ∧
    (ValueClass (antidiagonal e) →
      ¬ ∃ b, LawDerivation (antidiagonal e) b) :=
  ⟨no_self_derivation e, formclass_miss_benign e,
   valueclass_miss_structural e⟩

end SelfDerivation

/- audit -/
#print axioms SelfDerivation.repertoire_incomplete
#print axioms SelfDerivation.no_self_derivation
#print axioms SelfDerivation.repertoire_escape
#print axioms SelfDerivation.formclass_miss_benign
#print axioms SelfDerivation.valueclass_miss_structural
#print axioms SelfDerivation.two_obstructions
