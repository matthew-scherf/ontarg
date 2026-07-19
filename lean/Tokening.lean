/-!
# Tokening

A one-state medium tokens nothing; any medium that discriminates a
claim from its denial thereby draws a distinction. Applied to the
denial of `Draws`, and to the scope of an articulation.
-/

namespace Tokening

/-- Two of `M`'s states differ. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b

/-- An assignment of a mark to each claim. -/
def Tok (M : Type) : Type := Prop → M

/-- `t` marks `P` and `Q` differently. -/
def Discriminates {M : Type} (t : Tok M) (P Q : Prop) : Prop := t P ≠ t Q

theorem subsingleton_tokens_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Tok M) : ∀ P Q : Prop, ¬ Discriminates t P Q :=
  fun P Q hd => hd (h (t P) (t Q))

theorem discrimination_draws {M : Type} {t : Tok M} {P Q : Prop}
    (h : Discriminates t P Q) : Draws M :=
  ⟨t P, t Q, h⟩

theorem denial_draws_the_distinction {M : Type} (t : Tok M)
    (h : Discriminates t (¬ Draws M) (Draws M)) : Draws M :=
  discrimination_draws h

theorem no_undrawn_denial {M : Type} (t : Tok M) :
    ¬ (Discriminates t (¬ Draws M) (Draws M) ∧ ¬ Draws M) :=
  fun ⟨hd, hn⟩ => hn (denial_draws_the_distinction t hd)

/-- A discriminating tokening instantiates `Articulation.Says` and `.Sat`
    in its own medium. -/
theorem discrimination_says_and_sat {M : Type} (t : Tok M) (P Q : Prop)
    (h : Discriminates t P Q) :
    (∃ m : M, ¬ (m = t P)) ∧ (∃ m : M, m = t P) :=
  ⟨⟨t Q, fun he => h he.symm⟩, ⟨t P, rfl⟩⟩

theorem mute_excludes_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Tok M) (P : Prop) : ¬ ∃ m : M, ¬ (m = t P) :=
  fun ⟨m, hm⟩ => hm (h m (t P))

/-- What an articulation speaks of. -/
def Scope (M : Type) : Type := M → Prop

/-- Scope leaves nothing out. -/
def AbsoluteScope {M : Type} (s : Scope M) : Prop := ∀ m, s m

theorem no_outside {M : Type} (s : Scope M) (habs : AbsoluteScope s)
    (mark : M) : s mark := habs mark

/-- An articulation whose scope omits some `m` is not absolute. -/
theorem the_outside_is_the_premise {M : Type} (s : Scope M)
    (h : ∃ m, ¬ s m) : ¬ AbsoluteScope s := by
  intro habs
  obtain ⟨m, hm⟩ := h
  exact hm (habs m)

end Tokening

#print axioms Tokening.subsingleton_tokens_nothing
#print axioms Tokening.discrimination_draws
#print axioms Tokening.denial_draws_the_distinction
#print axioms Tokening.no_undrawn_denial
#print axioms Tokening.discrimination_says_and_sat
#print axioms Tokening.mute_excludes_nothing


#print axioms Tokening.no_outside
#print axioms Tokening.the_outside_is_the_premise
