/-!
# Seed

The last place a premise could hide.

`Articulation.absolute_articulation` forces the run *given a seed*. Two
seeds, two runs. So the absolute articulation appears to leave a choice
open — and a choice left open by the mathematics and closed by the
world is exactly what a premise is. If the seed were a premise, the
count would be one, not zero.

It is not. The two runs are related by the relabeling, and the
relabeling is the whole symmetry of the bare distinction. So no
structureless proposition separates them: to the only vocabulary the
absolute allows itself, `clock true` and `clock false` are one world,
not two. The seed is a *label*, and a label carries information only
against a convention that has already been imported.

That is not to say the seed is nothing. It is to say what kind of
something it is. By `Instantiation.no_seam_when_generated`, a class of
width one needs no bridge; by `Ledger.settling_needs_new_primitive`, any
vocabulary that expressed "the seed is `true`" would have to separate
worlds the structureless vocabulary identifies — which is to import a
name. So the seed is not assumed and not derived: it is *read*. It is
the argument's own value-class record (`SelfDerivation.lean`'s
underivable records are the general case) arriving at the first tick —
the first record, not the last premise.

Main results:
* `seed_is_relabel` — the two runs are one run relabelled.
* `structureless_blind_to_seed` — every relabel-invariant proposition
  about runs gives the two seeds the same verdict.
* `absolute_class_is_a_point` — so in the structureless vocabulary the
  admissible class of the absolute articulation has width one. There is
  nothing left for a premise to price.
* `naming_the_seed_imports` — and a vocabulary that *did* separate the
  seeds would fail to be relabel-invariant: naming a seed is importing
  structure. The seed cannot be premised without ceasing to be absolute.

Lean 4, prelude only; no imports. Axiom footprint: `seed_is_relabel`
none; the rest within `[Quot.sound]` (function extensionality, to
transport a proposition across two pointwise equal runs).
-/

namespace Seed

/-- The two-tick clock from a seed (as `Articulation.clock`). -/
def clock (s : Bool) : Nat → Bool
  | 0 => s
  | n + 1 => !(clock s n)

/-- Relabelling a run: apply the sole nontrivial relabeling of the bare
    distinction at every tick. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => !(s n)

/-- The seed is a label. The run from `false` is the run from `true`,
    relabelled. They are not two histories; they are one history read
    two ways. -/
theorem seed_is_relabel : ∀ n, clock false n = relabel (clock true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Bool.not (clock false n) = Bool.not (clock true (n + 1))
    rw [ih]
    rfl

/-- A proposition about runs is *structureless* when it survives the
    relabeling — when it names no value, only shape. -/
def Structureless (P : (Nat → Bool) → Prop) : Prop :=
  ∀ s, P s ↔ P (relabel s)

/-- No structureless proposition sees the seed. Whatever it says of
    the run from `true`, it says of the run from `false`. -/
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

/-- The class is a point. Both runs of the absolute articulation
    receive the same verdict from every structureless proposition. In
    the vocabulary the absolute allows itself, its admissible class has
    width one — and by `Instantiation.no_seam_when_generated`, a class of
    width one needs no bridge and prices no premise. -/
theorem absolute_class_is_a_point :
    ∀ P : (Nat → Bool) → Prop, Structureless P →
      (P (clock true) ↔ P (clock false)) :=
  fun _ hP => structureless_blind_to_seed hP

/-- Naming the seed imports structure. Contrapositive, and the point
    of the file: a proposition that *did* separate the two runs — that
    said "the seed is `true`" — would not survive the relabeling. To
    premise the seed is to name a value, and to name a value is to stop
    being absolute.

    So the seed is not a premise of this position. It is the first thing
    the position says cannot be derived: a record. -/
theorem naming_the_seed_imports {P : (Nat → Bool) → Prop}
    (hsep : P (clock true) ∧ ¬ P (clock false)) : ¬ Structureless P := by
  intro hP
  exact hsep.2 ((structureless_blind_to_seed hP).mp hsep.1)

/-- The witness: "the run starts `true`" is such a proposition. It
    separates the seeds, so it is not structureless — it is a record
    read from a seat, not derived from the law, exactly as
    `SelfDerivation.lean` says a value-class record must be. -/
theorem starts_true_is_not_structureless :
    ¬ Structureless (fun s => s 0 = true) := by
  apply naming_the_seed_imports
  exact ⟨rfl, fun h => Bool.noConfusion h⟩

end Seed

/- audit -/
#print axioms Seed.seed_is_relabel
#print axioms Seed.structureless_blind_to_seed
#print axioms Seed.absolute_class_is_a_point
#print axioms Seed.naming_the_seed_imports
#print axioms Seed.starts_true_is_not_structureless
