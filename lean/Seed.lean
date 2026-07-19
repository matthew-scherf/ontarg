/-!
# Seed

The two runs of `Articulation.absolute_articulation` (seeds `true`,
`false`) are one run related by relabeling: no structureless
proposition separates them.
-/

namespace Seed

/-- Two-tick clock from a seed (as `Articulation.clock`). -/
def clock (s : Bool) : Nat → Bool
  | 0 => s
  | n + 1 => !(clock s n)

/-- Apply the sole nontrivial relabeling at every tick. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => !(s n)

theorem seed_is_relabel : ∀ n, clock false n = relabel (clock true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Bool.not (clock false n) = Bool.not (clock true (n + 1))
    rw [ih]
    rfl

/-- Survives the relabeling. -/
def Structureless (P : (Nat → Bool) → Prop) : Prop :=
  ∀ s, P s ↔ P (relabel s)

theorem structureless_blind_to_seed {P : (Nat → Bool) → Prop}
    (hP : Structureless P) : P (clock true) ↔ P (clock false) := by
  have h : (fun n => clock false n) = (fun n => relabel (clock true) n) := by
    funext n; exact seed_is_relabel n
  constructor
  · intro hp
    have : P (relabel (clock true)) := (hP (clock true)).mp hp
    show P (clock false)
    rw [show (clock false) = relabel (clock true) from h]
    exact this
  · intro hp
    rw [show (clock false) = relabel (clock true) from h] at hp
    exact (hP (clock true)).mpr hp

theorem absolute_class_is_a_point :
    ∀ P : (Nat → Bool) → Prop, Structureless P →
      (P (clock true) ↔ P (clock false)) :=
  fun _ hP => structureless_blind_to_seed hP

/-- Contrapositive: a proposition separating the two runs is not structureless. -/
theorem naming_the_seed_imports {P : (Nat → Bool) → Prop}
    (hsep : P (clock true) ∧ ¬ P (clock false)) : ¬ Structureless P := by
  intro hP
  exact hsep.2 ((structureless_blind_to_seed hP).mp hsep.1)

theorem starts_true_is_not_structureless :
    ¬ Structureless (fun s => s 0 = true) := by
  apply naming_the_seed_imports
  exact ⟨rfl, fun h => Bool.noConfusion h⟩

end Seed

#print axioms Seed.seed_is_relabel
#print axioms Seed.structureless_blind_to_seed
#print axioms Seed.absolute_class_is_a_point
#print axioms Seed.naming_the_seed_imports
#print axioms Seed.starts_true_is_not_structureless
