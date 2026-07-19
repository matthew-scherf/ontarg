/-!
# NoFloor

A proposition constant on the class needs no bridge: it is expressible
in every vocabulary, including the blind one.
-/

namespace NoFloor

variable {W : Type u} {Obs : Type v}

/-- Expressibility (as `Ledger.Expressible`). -/
def Expressible (v : W → Obs) (P : W → Prop) : Prop :=
  ∃ q : Obs → Prop, ∀ w, P w ↔ q (v w)

/-- `Q` decides `P`. -/
def Decides (Q P : W → Prop) : Prop :=
  (∀ w, Q w → P w) ∧ (∀ w, ¬ Q w → ¬ P w)

/-- Same verdict at every world. -/
def ConstantOn (P : W → Prop) : Prop := ∀ w w', P w ↔ P w'

theorem constant_is_expressible_everywhere (w₀ : W) (v : W → Obs)
    (P : W → Prop) (hc : ConstantOn P) : Expressible v P :=
  ⟨fun _ => P w₀, fun w => hc w w₀⟩

/-- Even the vocabulary mapping every world to the same observation expresses it. -/
theorem blind_vocabulary_suffices (w₀ : W) (P : W → Prop)
    (hc : ConstantOn P) : Expressible (fun _ : W => ()) P :=
  ⟨fun _ => P w₀, fun w => hc w w₀⟩

theorem fork_left {v : W → Obs} {P : W → Prop} (h : Expressible v P) :
    Expressible v P ∨ ¬ ∃ Q : W → Prop, Expressible v Q ∧ Decides Q P :=
  Or.inl h

/-- A position whose propositions are constant on the class satisfies the
    fork on its left horn throughout. -/
theorem fork_is_not_a_floor (w₀ : W) :
    ∀ (v : W → Obs) (P : W → Prop), ConstantOn P →
      Expressible v P
      ∧ (Expressible v P ∨ ¬ ∃ Q : W → Prop, Expressible v Q ∧ Decides Q P) :=
  fun v P hc =>
    ⟨constant_is_expressible_everywhere w₀ v P hc,
     fork_left (constant_is_expressible_everywhere w₀ v P hc)⟩

abbrev SeedClass : Type := Bool

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

#print axioms NoFloor.constant_is_expressible_everywhere
#print axioms NoFloor.blind_vocabulary_suffices
#print axioms NoFloor.fork_left
#print axioms NoFloor.fork_is_not_a_floor
#print axioms NoFloor.structureless_needs_no_bridge
