/-!
# Structureless

The identification "structureless = equivariant" (premise R3), backed
by a definability theorem. `OnlyShape.lean` identifies a specification
that imports no structure with one whose law commutes with every
relabeling of its alphabet. This file grounds that identification: on
the bare distinction, the laws whose graphs are definable from the
distinction alone — from equality, with no constants and no further
vocabulary — are exactly the equivariant ones. "Importing no
structure" as a syntactic fact (nothing is named) and as a semantic
fact (nothing is broken by relabeling) coincide.

Main results:
* `defble_invariant` — soundness: every relation definable from pure
  equality is invariant under the relabeling.
* `graph_equivariant` — a law whose graph is definable from pure
  equality commutes with the relabeling.
* `equivariant_graph_defble` — completeness: every equivariant law's
  graph is definable from pure equality.
* `constants_not_defble` — no constant law has an equality-definable
  graph.
* `structureless_iff_equivariant` — the conjunction: a law on the
  bare distinction is definable from the distinction alone iff it is
  equivariant.

Definability is the Boolean closure of the equality atom
(quantifier-free). On a two-element alphabet this loses nothing:
quantifiers range over the two elements reachable from the free
variables by equality and its negation, so first-order pure-equality
definability coincides with this closure. What remains of R3 after
this file is the identification of "importing no structure" with
"having no vocabulary beyond the distinction itself".

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Structureless

/- ---------- definability from the distinction alone ---------- -/

/-- Binary relations on the bare distinction definable from pure
    equality: the equality atom, closed under negation, conjunction,
    and disjunction. No constant appears; nothing is named. -/
inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

/-- The graph reading: `R` is the graph of the law `f`. -/
def Graph (f : Bool → Bool) (R : Bool → Bool → Prop) : Prop :=
  ∀ a b, R a b ↔ f a = b

/- ---------- soundness: definable implies invariant ---------- -/

/-- Every relation definable from pure equality is invariant under
    the relabeling: relabeling both arguments changes nothing. -/
theorem defble_invariant {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a b ↔ R (!a) (!b) := by
  induction h with
  | eq => decide
  | neg _ ih =>
    intro a b
    exact ⟨fun hn hr => hn ((ih a b).mpr hr),
           fun hn hr => hn ((ih a b).mp hr)⟩
  | conj _ _ ih1 ih2 =>
    intro a b
    exact ⟨fun ⟨h1, h2⟩ => ⟨(ih1 a b).mp h1, (ih2 a b).mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨(ih1 a b).mpr h1, (ih2 a b).mpr h2⟩⟩
  | disj _ _ ih1 ih2 =>
    intro a b
    exact ⟨fun h => h.elim (fun h1 => Or.inl ((ih1 a b).mp h1))
                           (fun h2 => Or.inr ((ih2 a b).mp h2)),
           fun h => h.elim (fun h1 => Or.inl ((ih1 a b).mpr h1))
                           (fun h2 => Or.inr ((ih2 a b).mpr h2))⟩

/-- A law whose graph is definable from pure equality commutes with
    the relabeling. -/
theorem graph_equivariant (f : Bool → Bool) {R : Bool → Bool → Prop}
    (hR : Defble R) (hg : Graph f R) :
    ∀ x, f (!x) = !(f x) := by
  intro x
  have h1 : R x (f x) := (hg x (f x)).mpr rfl
  have h2 : R (!x) (!(f x)) := (defble_invariant hR x (f x)).mp h1
  exact (hg (!x) (!(f x))).mp h2

/- ---------- completeness: equivariant implies definable ---------- -/

/-- The classification of `OnlyShape.lean`, restated pointwise so the
    file stands alone: an equivariant endomap of the bare distinction
    is the identity or the negation. -/
theorem equivariant_id_or_not (f : Bool → Bool)
    (h : ∀ x, f (!x) = !(f x)) :
    (∀ x, f x = x) ∨ (∀ x, f x = !x) := by
  have h1 : f true = !(f false) := h false
  cases hf : f false with
  | false =>
    left; intro x; cases x
    · exact hf
    · rw [h1, hf]; rfl
  | true =>
    right; intro x; cases x
    · rw [hf]; rfl
    · rw [h1, hf]

/-- Every equivariant law's graph is definable from pure equality:
    the identity's graph is the equality atom, the negation's graph
    is its negation. -/
theorem equivariant_graph_defble (f : Bool → Bool)
    (h : ∀ x, f (!x) = !(f x)) :
    ∃ R, Defble R ∧ Graph f R := by
  cases equivariant_id_or_not f h with
  | inl hid =>
    refine ⟨fun a b => a = b, Defble.eq, ?_⟩
    intro a b
    rw [hid a]
  | inr hnot =>
    refine ⟨fun a b => ¬ (a = b), Defble.neg Defble.eq, ?_⟩
    intro a b
    rw [hnot a]
    cases a <;> cases b <;> decide

/- ---------- constants are not definable ---------- -/

/-- No constant law has an equality-definable graph: a definable
    graph is invariant, and invariance would force `c = !c`. This is
    `OnlyShape.constants_not_equivariant` on the syntactic side. -/
theorem constants_not_defble (c : Bool) :
    ¬ ∃ R, Defble R ∧ Graph (fun _ => c) R := by
  intro h
  cases h with
  | intro R hR =>
    have h1 : R true c := (hR.2 true c).mpr rfl
    have h2 : R false (!c) := (defble_invariant hR.1 true c).mp h1
    have h3 : c = !c := (hR.2 false (!c)).mp h2
    cases c <;> exact Bool.noConfusion h3

/- ---------- the identification, both directions ---------- -/

/-- The identification behind premise R3, as a theorem: a law on the
    bare distinction is definable from the distinction alone — from
    pure equality, naming nothing — if and only if it commutes with
    the relabeling. Structureless-as-syntax and
    structureless-as-equivariance are one class. -/
theorem structureless_iff_equivariant (f : Bool → Bool) :
    (∃ R, Defble R ∧ Graph f R) ↔ (∀ x, f (!x) = !(f x)) := by
  constructor
  · intro h
    cases h with
    | intro R hR => exact graph_equivariant f hR.1 hR.2
  · exact equivariant_graph_defble f

end Structureless

/- audit -/
#print axioms Structureless.defble_invariant
#print axioms Structureless.graph_equivariant
#print axioms Structureless.equivariant_id_or_not
#print axioms Structureless.equivariant_graph_defble
#print axioms Structureless.constants_not_defble
#print axioms Structureless.structureless_iff_equivariant
