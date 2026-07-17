/-!
# Tokening

Why the conditions of `Articulation.lean` are not premises.

A premise is a claim that could be denied. The conditions `Says` and
`Sat` cannot be denied, because a denial is a tokening, and a tokening
already satisfies them. This file makes that mechanical rather than
rhetorical.

The engine is one observation. A tokening is a mark that is *this* and
not *that*. A medium with one state cannot be this-rather-than-that, so
it tokens nothing: the same mark stands for every claim, which is to
stand for none. Hence any medium that tokens two claims distinctly has
two distinct states — a distinction is drawn. Now let the claim be *that
no distinction is drawn*. To token it as opposed to its denial is to
draw one.

Main results:
* `subsingleton_tokens_nothing` — a one-state medium assigns the same
  mark to every claim: it discriminates nothing.
* `discrimination_draws` — a medium that marks two claims differently
  has two distinct states.
* `denial_draws_the_distinction` — the retorsion: any medium that
  distinguishes "a distinction is drawn" from its denial thereby draws
  one. The denial cannot be tokened as the denial it is.
* `discrimination_says_and_sat` — a discriminating tokening exhibits,
  in its own medium, the two conditions `Articulation.Says` and
  `Articulation.Sat` impose: the mark of a claim excludes something and
  is satisfied by something.
* `mute_excludes_nothing` — and where nothing is discriminated, nothing
  is excluded: saying nothing and being unable to say coincide.
* `the_outside_is_the_premise` — the dichotomy that makes the retorsion
  bind only in the absolute case: the argument goes through exactly
  when the articulation's scope includes the medium of its own
  tokening. An articulation with an outside is not absolute, and the
  outside is the premise it imports.

The last result is the honest boundary. One can truly write "this page
is blank" — on another page. A retorsion never binds a claim that has
somewhere else to stand. It binds only a claim that has claimed
everything, which is what "absolute" means. The premises earlier
versions of this argument carried (R1–R4, and R3's residue on the
reading of Step 1) were, each of them, places the argument's claims
stood outside themselves; see ARGUMENT.md, *Why there are no
premises*.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Tokening

/- ---------- the medium ---------- -/

/-- A distinction is drawn in `M`: two of its states differ. This is the
    whole content of "there is a distinction" — nothing is named, no
    state is preferred. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b

/-- A tokening: an assignment of a mark to each claim. -/
def Tok (M : Type) : Type := Prop → M

/-- `t` discriminates `P` from `Q` when it marks them differently. A
    tokening that fails to discriminate `P` from `Q` has not tokened `P`
    *as opposed to* `Q`. -/
def Discriminates {M : Type} (t : Tok M) (P Q : Prop) : Prop := t P ≠ t Q

/- ---------- a one-state medium tokens nothing ---------- -/

/-- A one-state medium discriminates nothing. Every claim gets the
    same mark, so no claim is tokened rather than another. Silence and
    assertion are the same event. -/
theorem subsingleton_tokens_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Tok M) : ∀ P Q : Prop, ¬ Discriminates t P Q :=
  fun P Q hd => hd (h (t P) (t Q))

/-- Discrimination draws the distinction. Conversely: a medium that
    marks two claims differently has two distinct states. -/
theorem discrimination_draws {M : Type} {t : Tok M} {P Q : Prop}
    (h : Discriminates t P Q) : Draws M :=
  ⟨t P, t Q, h⟩

/- ---------- the retorsion ---------- -/

/-- The denial draws the distinction. Let the claim be that no
    distinction is drawn in `M`. Any tokening in `M` that marks that
    claim differently from its denial has two distinct marks — and so
    draws the distinction it denies.

    The denial is not refuted by argument. It is refuted by being
    tokened. -/
theorem denial_draws_the_distinction {M : Type} (t : Tok M)
    (h : Discriminates t (¬ Draws M) (Draws M)) : Draws M :=
  discrimination_draws h

/-- The same, put as the impossibility it is: no medium tokens the
    denial of distinction as distinct from its affirmation *and* lacks
    the distinction. There is no seat from which the denial can be
    said. -/
theorem no_undrawn_denial {M : Type} (t : Tok M) :
    ¬ (Discriminates t (¬ Draws M) (Draws M) ∧ ¬ Draws M) :=
  fun ⟨hd, hn⟩ => hn (denial_draws_the_distinction t hd)

/- ---------- Says and Sat are instantiated by the act ---------- -/

/-- The act of tokening exhibits the pattern of articulation.

    Let `t` discriminate `P` from `Q`. Consider the predicate on marks
    "is the mark of `P`". It *excludes* something — the mark of `Q` is
    not it — and it *is satisfied* by something: the mark of `P`. So a
    discriminating tokening instantiates, in its own medium, exactly the
    pair of conditions `Articulation.Says` and `Articulation.Sat` impose
    on a specification: exclude something, exclude not everything.

    This is the content behind the claim that those two conditions are
    not premises. They are not further things assumed about a ground;
    they are the shape of any act that could assume, deny, or state
    anything at all — including the act of denying them. -/
theorem discrimination_says_and_sat {M : Type} (t : Tok M) (P Q : Prop)
    (h : Discriminates t P Q) :
    (∃ m : M, ¬ (m = t P)) ∧ (∃ m : M, m = t P) :=
  ⟨⟨t Q, fun he => h he.symm⟩, ⟨t P, rfl⟩⟩

/-- And the degenerate case, for contrast: where nothing is
    discriminated, the predicate "is the mark of `P`" excludes nothing.
    Saying nothing and being unable to say are the same condition. -/
theorem mute_excludes_nothing {M : Type} (h : ∀ a b : M, a = b)
    (t : Tok M) (P : Prop) : ¬ ∃ m : M, ¬ (m = t P) :=
  fun ⟨m, hm⟩ => hm (h m (t P))

/- ---------- the honest boundary: the outside ---------- -/

/-- The scope of an articulation: what it speaks of. -/
def Scope (M : Type) : Type := M → Prop

/-- An articulation is *absolute* when its scope leaves nothing out. -/
def AbsoluteScope {M : Type} (s : Scope M) : Prop := ∀ m, s m

/-- The tokening of an absolute articulation falls under it. There
    is no seat outside. Trivial as mathematics, and the whole hinge as
    metaphysics: it is what makes the retorsion bind. -/
theorem no_outside {M : Type} (s : Scope M) (habs : AbsoluteScope s)
    (mark : M) : s mark := habs mark

/-- The outside is the premise. The contrapositive, and the honest
    limit of this file's method: an articulation whose scope omits some
    `m` is not absolute — and that omitted `m` is exactly what it must
    assume rather than say.

    A retorsion never binds a claim with somewhere else to stand: one
    writes "this page is blank" on another page. It binds only a claim
    that has claimed everything. Every premise earlier versions of this
    argument carried was such an elsewhere. -/
theorem the_outside_is_the_premise {M : Type} (s : Scope M)
    (h : ∃ m, ¬ s m) : ¬ AbsoluteScope s := by
  intro habs
  obtain ⟨m, hm⟩ := h
  exact hm (habs m)

end Tokening

/- audit -/
#print axioms Tokening.subsingleton_tokens_nothing
#print axioms Tokening.discrimination_draws
#print axioms Tokening.denial_draws_the_distinction
#print axioms Tokening.no_undrawn_denial
#print axioms Tokening.discrimination_says_and_sat
#print axioms Tokening.mute_excludes_nothing


#print axioms Tokening.no_outside
#print axioms Tokening.the_outside_is_the_premise
