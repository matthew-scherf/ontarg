/-!
# Cogito

The cogito split into two propositions that must be kept apart:
existence (contingent — some carriers are empty, so "there is a
doubter" is not provable in general) and validity (necessary — for
any occupant of any type, its occurrence is certain and its denial
self-refuting, provable with no instance in hand).

Self-reference has two signs. Doubt is self-negation, which is
fixed-point-free: a total self-doubt is inconsistent. Affirmation is
the identity, which is fixed-point-full: self-affirmation is
consistent. Both are the Lawvere diagonal at opposite choices of
endomap.

Main results:
* `doubt_has_no_fixpoint` / `affirmation_is_fixed` — the two signs.
* `the_gap` — no total self-doubt is consistent.
* `cogito` / `no_self_denial` — any token occurs, and the denial of
  its own occurrence self-refutes.
* `existence_is_contingent` — not every carrier is inhabited.
* `cogito_valid_necessarily` — occurrence and its undeniability, for
  every occupant of every type.
* `cogito_ergo_sum` — the conjunction.

`Occurs a := ∃ x, x = a` is deliberately trivial: occurrence is
nothing over and above being-given — the cogito is read as the
presupposition of any tokening rather than an inference (Hintikka's
performative reading). What is proved is the validity of the seat,
not that any seat is occupied by a knower; that further step is
proved undecidable in `InteriorExperience.other_minds_free` and is
not taken here.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Cogito

/- ---------- the diagonal (re-declared, = OneDiagonal.lawvere) ---------- -/

/-- Lawvere (1969). If a carrier enumerates its own maps into `Y`
    point-surjectively, every endomap of `Y` has a fixed point. -/
theorem lawvere {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g) (f : Y → Y) : ∃ y, f y = y := by
  obtain ⟨a₀, ha⟩ := surj (fun a => f (e a a))
  exact ⟨e a₀ a₀, (congrFun ha a₀).symm⟩

/- ---------- the two signs of self-reference ---------- -/

/-- Doubt has no fixed point: no value survives its own negation. -/
theorem doubt_has_no_fixpoint : ∀ b : Bool, not b ≠ b := by
  intro b; cases b <;> decide

/-- Affirmation is fixed: every value survives self-affirmation. -/
theorem affirmation_is_fixed : ∀ b : Bool, id b = b := fun _ => rfl

/-- No total consistent self-doubt: at the fixed-point-free `not`, no
    self-enumeration is point-surjective. The negating sign of the same
    diagonal whose affirming sign is the cogito. -/
theorem the_gap {A : Type} (e : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, e a = g := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere e surj not
  cases y <;> exact absurd hy (by decide)

/- ---------- the cogito proper ---------- -/

/-- To occur is to be given: `a`'s occurrence is nothing over and above
    there being an `a`. Deliberately trivial — occurrence is presupposed
    by any tokening, not inferred from it. -/
def Occurs {A : Type} (a : A) : Prop := ∃ x : A, x = a

/-- Any token `a` occurs: the being-given of a self-affirmation
    guarantees the occurrence it affirms. -/
theorem cogito {A : Type} (a : A) : Occurs a := ⟨a, rfl⟩

/-- The denial of one's own occurrence refutes itself: to token
    "`a` does not occur", `a` must be given, which is `a`'s occurring. -/
theorem no_self_denial {A : Type} (a : A) : ¬ ¬ Occurs a :=
  fun h => h (cogito a)

/- ---------- the asymmetry: valid necessarily, existent contingently ------ -/

/-- Existence is contingent: not every carrier is inhabited (`Empty` is
    not), so "there is a doubter" cannot be proved in general. The
    antecedent of the cogito is a contingent fact, not a theorem. -/
theorem existence_is_contingent : ∃ A : Type, A → False :=
  ⟨Empty, fun e => nomatch e⟩

/-- Yet for any occupant `a` of any type, its occurrence is certain and
    undeniable — provable with no instance in hand. The validity
    transfers between minds; the existence does not. (Whether the seat
    is occupied by a knower is undecidable —
    `InteriorExperience.other_minds_free` — and is not asserted.) -/
theorem cogito_valid_necessarily {A : Type} (a : A) : Occurs a ∧ ¬ ¬ Occurs a :=
  ⟨cogito a, no_self_denial a⟩

/- ---------- the conjunction ---------- -/

/-- For any token `a`: it occurs, the denial of its occurrence
    self-refutes, self-affirmation is the consistent fixed-point sign,
    and self-doubt is the inconsistent one. Not claimed: that the seat
    feels, or that any seat exists — only that, where there is one, its
    self-affirmation is valid. -/
theorem cogito_ergo_sum {A : Type} (a : A) :
    Occurs a
    ∧ ¬ ¬ Occurs a
    ∧ (∀ b : Bool, id b = b)
    ∧ (∀ b : Bool, not b ≠ b) :=
  ⟨cogito a, no_self_denial a, affirmation_is_fixed, doubt_has_no_fixpoint⟩

end Cogito

/- audit -/
#print axioms Cogito.lawvere
#print axioms Cogito.the_gap
#print axioms Cogito.cogito
#print axioms Cogito.no_self_denial
#print axioms Cogito.existence_is_contingent
#print axioms Cogito.cogito_valid_necessarily
#print axioms Cogito.cogito_ergo_sum
