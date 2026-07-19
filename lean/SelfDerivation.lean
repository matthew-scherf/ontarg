/-!
# SelfDerivation

A self-inclusive describer's repertoire `e : S → S → Bool` cannot
compute its own anti-diagonal record.
-/

namespace SelfDerivation

/-- As `ValueForm.lean`. -/
def FormClass {S : Type u} {B : Type v} (q : S → B) : Prop :=
  ∀ s t : S, q s = q t

/-- As `ValueForm.lean`. -/
def ValueClass {S : Type u} {B : Type v} (q : S → B) : Prop :=
  ∃ s t : S, q s ≠ q t

/-- As `ValueForm.lean`. -/
def LawDerivation {S : Type u} {B : Type v} (q : S → B) (b : B) : Prop :=
  ∀ s, q s = b

def antidiagonal {S : Type u} (e : S → S → Bool) : S → Bool :=
  fun s => !(e s s)

theorem repertoire_incomplete {S : Type u} (e : S → S → Bool) :
    ¬ ∀ q : S → Bool, ∃ s, e s = q := by
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj (antidiagonal e)
  have h := congrFun hs s
  simp [antidiagonal] at h

theorem no_self_derivation {S : Type u} (e : S → S → Bool) (s : S) :
    e s s ≠ antidiagonal e s := by
  simp [antidiagonal]

theorem repertoire_escape {S : Type u} (e : S → S → Bool) (t : S) :
    e t ≠ antidiagonal e := by
  intro h
  exact no_self_derivation e t (congrFun h t)

/-- A form-class anti-diagonal is still law-derivable. -/
theorem formclass_miss_benign {S : Type u} [Inhabited S]
    (e : S → S → Bool) (h : FormClass (antidiagonal e)) :
    ∃ b, LawDerivation (antidiagonal e) b :=
  ⟨antidiagonal e default, fun s => h s default⟩

/-- A value-class anti-diagonal is underivable. -/
theorem valueclass_miss_structural {S : Type u} (e : S → S → Bool)
    (h : ValueClass (antidiagonal e)) :
    ¬ ∃ b, LawDerivation (antidiagonal e) b := by
  intro ⟨b, hb⟩
  obtain ⟨s, t, hst⟩ := h
  exact hst (by rw [hb s, hb t])

theorem two_obstructions {S : Type u} [Inhabited S] (e : S → S → Bool) :
    (∀ s, e s s ≠ antidiagonal e s) ∧
    (FormClass (antidiagonal e) →
      ∃ b, LawDerivation (antidiagonal e) b) ∧
    (ValueClass (antidiagonal e) →
      ¬ ∃ b, LawDerivation (antidiagonal e) b) :=
  ⟨no_self_derivation e, formclass_miss_benign e,
   valueclass_miss_structural e⟩

end SelfDerivation

#print axioms SelfDerivation.repertoire_incomplete
#print axioms SelfDerivation.no_self_derivation
#print axioms SelfDerivation.repertoire_escape
#print axioms SelfDerivation.formclass_miss_benign
#print axioms SelfDerivation.valueclass_miss_structural
#print axioms SelfDerivation.two_obstructions
