/-!
# RichAlphabet
Main results:
* `invariant_iter` — invariance under `σ` propagates along its iterates.
* `invariant_transitive_constant` — a reading invariant under a
  relabeling that reaches every value is constant.
* `no_rich_separation` — hence such a reading separates nothing: no
  `x, y` with `P x` and `¬ P y`.
* `not_reaches_all`, `rot_reaches_all` — the relabelings `not` (on
  `Bool`) and `rot` (a 4-cycle on `Bool × Bool`) are transitive.
* `escape_closed` — the conjunction: on both the two-element and the
  four-element structureless alphabet, a single structureless locus
  presents nothing. The second locus of `Multiplicity` is irreducible.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace RichAlphabet

variable {A : Type u}

/-- A single-locus reading `P` is invariant under a relabeling `σ` of
    its alphabet when relabeling the value it reads changes nothing. -/
def InvariantUnder (P : A → Prop) (σ : A → A) : Prop :=
  ∀ x, P x ↔ P (σ x)

/-- Iterated relabeling. -/
def iter (σ : A → A) : Nat → A → A
  | 0,     x => x
  | k + 1, x => σ (iter σ k x)

/-- Invariance propagates along the iterates of the relabeling. -/
theorem invariant_iter {P : A → Prop} {σ : A → A}
    (h : InvariantUnder P σ) : ∀ k x, (P x ↔ P (iter σ k x)) := by
  intro k
  induction k with
  | zero => intro x; exact Iff.rfl
  | succ k ih => intro x; exact (ih x).trans (h (iter σ k x))

/-- A relabeling *reaches every value* from a base point `x0` when
    every value is some iterate of `x0`. This is what it is for the
    alphabet to name no element: the relabeling group acts
    transitively. -/
def ReachesAll (σ : A → A) (x0 : A) : Prop := ∀ y, ∃ k, iter σ k x0 = y

/-- A reading invariant under a relabeling that reaches every value is
    constant: it takes the same truth value at every value. -/
theorem invariant_transitive_constant {P : A → Prop} {σ : A → A} {x0 : A}
    (hinv : InvariantUnder P σ) (htrans : ReachesAll σ x0) :
    ∀ y, (P y ↔ P x0) := by
  intro y
  obtain ⟨k, hk⟩ := htrans y
  have h := invariant_iter hinv k x0
  rw [hk] at h
  exact h.symm

/-- Hence such a reading separates nothing: there is no pair it tells
    apart. A structureless single locus, whatever its alphabet,
    presents no mark. -/
theorem no_rich_separation {P : A → Prop} {σ : A → A} {x0 : A}
    (hinv : InvariantUnder P σ) (htrans : ReachesAll σ x0) :
    ¬ ∃ x y, P x ∧ ¬ P y := by
  intro hsep
  obtain ⟨x, y, hx, hy⟩ := hsep
  have hxx0 := invariant_transitive_constant hinv htrans x
  have hyx0 := invariant_transitive_constant hinv htrans y
  exact hy (hyx0.mpr (hxx0.mp hx))

/- ===== instance 1: the bare distinction ===== -/

/-- On `Bool`, negation reaches both values from `false`. -/
theorem not_reaches_all : ReachesAll (fun b => !b) false := by
  intro y
  cases y
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/- ===== instance 2: a four-element product alphabet ===== -/

/-- A 4-cycle on the two-bit alphabet `Bool × Bool`:
    `(F,F) → (F,T) → (T,T) → (T,F) → (F,F)`. A structureless relabeling
    of the smallest genuinely richer alphabet. -/
def rot (p : Bool × Bool) : Bool × Bool := (p.2, !p.1)

/-- The 4-cycle reaches every value of the two-bit alphabet. -/
theorem rot_reaches_all : ReachesAll rot (false, false) := by
  intro y
  obtain ⟨a, b⟩ := y
  cases a <;> cases b
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩

/- ===== the escape is closed ===== -/

/-- No structureless single locus presents the mark — neither over the
    bare distinction nor over the four-element product alphabet. The
    second locus forced by `Multiplicity.multiplicity_forced` cannot be
    absorbed into a richer alphabet at one locus: any alphabet that
    would absorb it names an element the ground cannot relabel, i.e.
    imports structure. The second locus is irreducible. -/
theorem escape_closed :
    (∀ P : Bool → Prop, InvariantUnder P (fun b => !b) →
        ¬ ∃ x y, P x ∧ ¬ P y)
    ∧ (∀ P : Bool × Bool → Prop, InvariantUnder P rot →
        ¬ ∃ x y, P x ∧ ¬ P y) := by
  refine ⟨?_, ?_⟩
  · intro P hinv; exact no_rich_separation hinv not_reaches_all
  · intro P hinv; exact no_rich_separation hinv rot_reaches_all

end RichAlphabet

/- audit -/
#print axioms RichAlphabet.invariant_iter
#print axioms RichAlphabet.invariant_transitive_constant
#print axioms RichAlphabet.no_rich_separation
#print axioms RichAlphabet.not_reaches_all
#print axioms RichAlphabet.rot_reaches_all
#print axioms RichAlphabet.escape_closed
