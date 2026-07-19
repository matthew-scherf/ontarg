/-!
# RichAlphabet

A reading invariant under a relabeling that reaches every value is
constant, hence separates nothing — on the bare distinction and on a
four-element product alphabet.
-/

namespace RichAlphabet

variable {A : Type u}

/-- `P` is invariant under relabeling `σ`. -/
def InvariantUnder (P : A → Prop) (σ : A → A) : Prop :=
  ∀ x, P x ↔ P (σ x)

def iter (σ : A → A) : Nat → A → A
  | 0,     x => x
  | k + 1, x => σ (iter σ k x)

theorem invariant_iter {P : A → Prop} {σ : A → A}
    (h : InvariantUnder P σ) : ∀ k x, (P x ↔ P (iter σ k x)) := by
  intro k
  induction k with
  | zero => intro x; exact Iff.rfl
  | succ k ih => intro x; exact (ih x).trans (h (iter σ k x))

/-- Every value is some iterate of `x0`. -/
def ReachesAll (σ : A → A) (x0 : A) : Prop := ∀ y, ∃ k, iter σ k x0 = y

theorem invariant_transitive_constant {P : A → Prop} {σ : A → A} {x0 : A}
    (hinv : InvariantUnder P σ) (htrans : ReachesAll σ x0) :
    ∀ y, (P y ↔ P x0) := by
  intro y
  obtain ⟨k, hk⟩ := htrans y
  have h := invariant_iter hinv k x0
  rw [hk] at h
  exact h.symm

theorem no_rich_separation {P : A → Prop} {σ : A → A} {x0 : A}
    (hinv : InvariantUnder P σ) (htrans : ReachesAll σ x0) :
    ¬ ∃ x y, P x ∧ ¬ P y := by
  intro hsep
  obtain ⟨x, y, hx, hy⟩ := hsep
  have hxx0 := invariant_transitive_constant hinv htrans x
  have hyx0 := invariant_transitive_constant hinv htrans y
  exact hy (hyx0.mpr (hxx0.mp hx))

theorem not_reaches_all : ReachesAll (fun b => !b) false := by
  intro y
  cases y
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- 4-cycle on `Bool × Bool`: `(F,F) → (F,T) → (T,T) → (T,F) → (F,F)`. -/
def rot (p : Bool × Bool) : Bool × Bool := (p.2, !p.1)

theorem rot_reaches_all : ReachesAll rot (false, false) := by
  intro y
  obtain ⟨a, b⟩ := y
  cases a <;> cases b
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩

theorem escape_closed :
    (∀ P : Bool → Prop, InvariantUnder P (fun b => !b) →
        ¬ ∃ x y, P x ∧ ¬ P y)
    ∧ (∀ P : Bool × Bool → Prop, InvariantUnder P rot →
        ¬ ∃ x y, P x ∧ ¬ P y) := by
  refine ⟨?_, ?_⟩
  · intro P hinv; exact no_rich_separation hinv not_reaches_all
  · intro P hinv; exact no_rich_separation hinv rot_reaches_all

end RichAlphabet

#print axioms RichAlphabet.invariant_iter
#print axioms RichAlphabet.invariant_transitive_constant
#print axioms RichAlphabet.no_rich_separation
#print axioms RichAlphabet.not_reaches_all
#print axioms RichAlphabet.rot_reaches_all
#print axioms RichAlphabet.escape_closed
