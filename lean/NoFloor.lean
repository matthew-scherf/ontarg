/-!
# NoFloor

Why zero premises is not excluded in principle.

The natural objection to an argument that claims no premises is that
some theorem forbids the claim — that any position joining mathematics
to an interpretation must keep at least one bridge row, so the count
can be narrowed but never reaches zero. The candidate theorem is the
fork:

    Expressible v P ∨ ¬ ∃ Q, Expressible v Q ∧ Decides Q P

That is a disjunction, and its *left* horn is live. The fork says: for
each proposition, either it factors through the vocabulary, or nothing
in the vocabulary decides it. It does not say that some proposition
fails to factor. To get "the count never reaches zero" one needs the
existential — *there is* a metaphysical proposition inexpressible in the
mathematical vocabulary — and the fork never supplies it. The fork holds
just as well of a position with no bridges at all, as
`fork_is_not_a_floor` below shows by exhibiting one.

The corpus already contains the positive result.
`Instantiation.no_seam_when_generated` proves that where the class is a
point, *every* proposition is expressible in *every* vocabulary,
"including the vocabulary that sees nothing" — so settling never needs a
new primitive and no bridge is ever required.

The mechanism is more general than a point class, and that generality is
what this file adds: a proposition need not be the *only* proposition —
it need only be *constant on the class*. A constant proposition factors
through every vocabulary, the blind one included. And by `Seed.lean`,
every structureless proposition about the absolute articulation's runs
is constant on its class. So each one stands on the fork's left horn,
and the fork's right horn — the horn where premises live — is empty.

Main results:
* `constant_is_expressible_everywhere` — a proposition constant on the
  class factors through every vocabulary, including the blind one.
* `fork_is_not_a_floor` — the fork is satisfied, on its left horn, by a
  position in which nothing whatever needs a bridge. So the fork
  establishes no lower bound on the number of premises. It is excluded
  middle wearing a metaphysical hat.
* `blind_vocabulary_suffices` — the sharpest form: where propositions are
  constant, even the vocabulary that observes nothing at all expresses
  every one of them.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace NoFloor

variable {W : Type u} {Obs : Type v}

/-- Expressibility (as `Ledger.Expressible`). -/
def Expressible (v : W → Obs) (P : W → Prop) : Prop :=
  ∃ q : Obs → Prop, ∀ w, P w ↔ q (v w)

/-- `Q` decides `P`. -/
def Decides (Q P : W → Prop) : Prop :=
  (∀ w, Q w → P w) ∧ (∀ w, ¬ Q w → ¬ P w)

/-- A proposition is *constant on the class* when it gives every world
    the same verdict. -/
def ConstantOn (P : W → Prop) : Prop := ∀ w w', P w ↔ P w'

/-- A constant proposition needs no bridge. If `P` gives every world
    the same verdict, it factors through every vocabulary — there is
    nothing for a vocabulary to fail to see.

    This is `Instantiation.no_seam_when_generated` with its hypothesis
    weakened from "the class is a point" to "the proposition is constant
    on the class". The weakening is what lets it reach the foundation:
    the absolute articulation's class is not a point (there are two
    seeds), but every structureless proposition about it is constant
    (`Seed.absolute_class_is_a_point`). -/
theorem constant_is_expressible_everywhere (w₀ : W) (v : W → Obs)
    (P : W → Prop) (hc : ConstantOn P) : Expressible v P :=
  ⟨fun _ => P w₀, fun w => hc w w₀⟩

/-- The blind vocabulary suffices. The sharpest form: a vocabulary
    that maps every world to the same observation — that sees nothing —
    still expresses every proposition constant on the class.

    Expressibility, at this width, has stopped discriminating. It is not
    that the bridge is short; it is that there is no gap. -/
theorem blind_vocabulary_suffices (w₀ : W) (P : W → Prop)
    (hc : ConstantOn P) : Expressible (fun _ : W => ()) P :=
  ⟨fun _ => P w₀, fun w => hc w w₀⟩

/-- The fork itself, proved here so the file stands alone — note that
    it needs no case split when the left horn is available. -/
theorem fork_left {v : W → Obs} {P : W → Prop} (h : Expressible v P) :
    Expressible v P ∨ ¬ ∃ Q : W → Prop, Expressible v Q ∧ Decides Q P :=
  Or.inl h

/-- The fork is not a floor.

    Here is a position on which *every* proposition, against *every*
    vocabulary, satisfies the fork on its left horn: the position whose
    propositions are constant on the class. Nothing in it needs a
    bridge; its premise table has no rows.

    The fork is true of this position. So the fork does not entail that
    any position has a premise. It cannot be what makes the table
    unemptiable, because it is satisfied by an empty table.

    What the fork does establish is conditional and worth keeping: *if*
    a position holds a proposition its vocabulary cannot express, *then*
    no argument conducted in that vocabulary will decide it. That is a
    real result about a real predicament. It is not a proof that the
    predicament is unavoidable. -/
theorem fork_is_not_a_floor (w₀ : W) :
    ∀ (v : W → Obs) (P : W → Prop), ConstantOn P →
      Expressible v P
      ∧ (Expressible v P ∨ ¬ ∃ Q : W → Prop, Expressible v Q ∧ Decides Q P) :=
  fun v P hc =>
    ⟨constant_is_expressible_everywhere w₀ v P hc,
     fork_left (constant_is_expressible_everywhere w₀ v P hc)⟩

/- ---------- the same, at the absolute articulation's class ---------- -/

/-- The class of the absolute articulation: its two seeds. -/
abbrev SeedClass : Type := Bool

/-- By `Seed.structureless_blind_to_seed`, a structureless proposition
    about the runs gives both seeds the same verdict — it is constant on
    this class. Given that, it is expressible in every vocabulary. -/
theorem structureless_needs_no_bridge (P : SeedClass → Prop)
    (hblind : P true ↔ P false) :
    ∀ (Ob : Type v) (v : SeedClass → Ob), Expressible v P := by
  intro Ob v
  refine constant_is_expressible_everywhere true v P ?_
  intro w w'
  cases w <;> cases w'
  · exact Iff.rfl
  · exact hblind.symm
  · exact hblind
  · exact Iff.rfl

end NoFloor

/- audit -/
#print axioms NoFloor.constant_is_expressible_everywhere
#print axioms NoFloor.blind_vocabulary_suffices
#print axioms NoFloor.fork_left
#print axioms NoFloor.fork_is_not_a_floor
#print axioms NoFloor.structureless_needs_no_bridge
