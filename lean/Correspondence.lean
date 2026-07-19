/-!
# Correspondence

`Compatible A` is the class of worlds an assertion `A` does not exclude.
Over that class, every proposition is forced, refuted, or free
(`richness_divides`), and this trichotomy is equivalent to the class
having more than one point (`articulation_fork`). No describer's
holdings enumerate every verdict-assignment (`no_full_inventory`). Two
runs of one law from one seed agree at every tick (`law_and_records_settle`),
and naming which run you're in is exactly the free proposition that
settles it (`seed_settles_the_world`).
-/

namespace Correspondence

variable {W : Type u}

/-- The class of worlds an assertion does not exclude. -/
def Compatible (A : W → Prop) : Type u := {w // A w}

/-- True in every compatible world. -/
def Forced {V : Type v} (P : V → Prop) : Prop := ∀ v, P v

/-- False in every compatible world. -/
def Refuted {V : Type v} (P : V → Prop) : Prop := ∀ v, ¬ P v

/-- Both values occur. -/
def Free {V : Type v} (P : V → Prop) : Prop := (∃ v, P v) ∧ (∃ v, ¬ P v)

/-- Over the class `A` induces: it has more than one point iff some proposition is free over it. -/
theorem articulation_fork (A : W → Prop) :
    (∃ w₁ w₂ : Compatible A, w₁ ≠ w₂)
    ↔ (∃ P : Compatible A → Prop, Free P) := by
  constructor
  · intro ⟨w₁, w₂, hne⟩
    exact ⟨fun w => w = w₁, ⟨w₁, rfl⟩, ⟨w₂, fun h => hne h.symm⟩⟩
  · intro ⟨P, ⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩
    exact ⟨w₁, w₂, fun he => h₂ (he ▸ h₁)⟩

/-- Every proposition over any type is forced, refuted, or free. -/
theorem richness_divides {V : Type v} (P : V → Prop) :
    Forced P ∨ Refuted P ∨ Free P := by
  cases Classical.em (∃ v, P v) with
  | inr hno =>
    exact Or.inr (Or.inl (fun v hv => hno ⟨v, hv⟩))
  | inl hyes =>
    cases Classical.em (∃ v, ¬ P v) with
    | inr hall =>
      exact Or.inl (fun v =>
        Classical.byContradiction (fun hn => hall ⟨v, hn⟩))
    | inl hsome =>
      exact Or.inr (Or.inr ⟨hyes, hsome⟩)

theorem bool_no_fixpoint : ∀ b : Bool, b ≠ !b := by
  intro b
  cases b <;> decide

/-- For any `hold : D → D → Bool`, some column `q` disagrees with every `hold x` at `x`. -/
theorem no_full_inventory {D : Type v} (hold : D → D → Bool) :
    ∃ q : D → Bool, ∀ x : D, hold x ≠ q :=
  ⟨fun x => !(hold x x),
   fun x he => bool_no_fixpoint (hold x x) (congrFun he x)⟩

/-- `x` solves the recursion `f` from tick to tick. -/
def Solves {S : Type v} (f : S → S) (x : Nat → S) : Prop :=
  ∀ n, x (n + 1) = f (x n)

/-- Two solutions of the same recursion agreeing at 0 agree everywhere. -/
theorem law_and_records_settle {S : Type v} (f : S → S)
    (x y : Nat → S) (hx : Solves f x) (hy : Solves f y)
    (h0 : x 0 = y 0) : ∀ n, x n = y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, hy k, ih]

/-- If two solutions of `f` start at different values, "starts at `w₁`'s value" is a free
    proposition over the solution space, and it determines the solution. -/
theorem seed_settles_the_world {S : Type v} (f : S → S)
    (w₁ w₂ : {x : Nat → S // Solves f x}) (hne : w₁.1 0 ≠ w₂.1 0) :
    Free (fun w : {x : Nat → S // Solves f x} => w.1 0 = w₁.1 0)
    ∧ ∀ w : {x : Nat → S // Solves f x}, w.1 0 = w₁.1 0 → w = w₁ :=
  ⟨⟨⟨w₁, rfl⟩, ⟨w₂, hne.symm⟩⟩,
   fun w hw => Subtype.ext (funext (law_and_records_settle f w.1 w₁.1 w.2 w₁.2 hw))⟩

theorem the_ceiling :
    (∀ A : W → Prop,
      (∃ w₁ w₂ : Compatible A, w₁ ≠ w₂)
      ↔ (∃ P : Compatible A → Prop, Free P))
    ∧ (∀ (D : Type v) (hold : D → D → Bool),
        ∃ q : D → Bool, ∀ x : D, hold x ≠ q)
    ∧ (∀ (S : Type w) (f : S → S) (x y : Nat → S),
        Solves f x → Solves f y → x 0 = y 0 → ∀ n, x n = y n) :=
  ⟨articulation_fork,
   fun _ hold => no_full_inventory hold,
   fun _ f x y hx hy h0 => law_and_records_settle f x y hx hy h0⟩

end Correspondence

#print axioms Correspondence.articulation_fork
#print axioms Correspondence.richness_divides
#print axioms Correspondence.bool_no_fixpoint
#print axioms Correspondence.no_full_inventory
#print axioms Correspondence.law_and_records_settle
#print axioms Correspondence.seed_settles_the_world
#print axioms Correspondence.the_ceiling
