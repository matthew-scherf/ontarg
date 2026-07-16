/-!
# Aseity

No faithful self-model, and its corollary: no consistent system
decides its own ground from inside. A description type `D` models
facts about descriptions via `decode : D → (D → Prop)`; `encode`
names each predicate. A faithful self-model (`decode ∘ encode = id`)
would let the interior hold a complete internal model of every fact
about itself, including whether it is fundamental or derived. The
diagonal forbids this.

Main results:
* `founding_diagonal` — `X = ¬X` has no solution: a proposition equal
  to its own negation is absurd.
* `no_self_model` — no faithful self-model exists (Cantor's theorem,
  run on the predicate of self-denial).
* `aseity` — hence no consistent system certifies, from inside,
  whether it is the fundamental ground or the image of a deeper
  level: the question is interior-undecidable.

The cosmological reading — the interior-undecidability of a world's
own ground — is an interpretation; the mathematics is Cantor's
theorem driven by self-negation.

Lean 4, prelude only; no imports. Axiom footprint: none.
-/

namespace Aseity

/-- `X = ¬X` has no solution: a proposition equal to its own negation
    is absurd. -/
theorem founding_diagonal (X : Prop) (h : X = ¬ X) : False :=
  have hiff : X ↔ ¬ X := Iff.of_eq h
  have hn : ¬ X := fun hx => hiff.mp hx hx
  hn (hiff.mpr hn)

/-- No description type names and decides every predicate about
    itself: `decode ∘ encode = id` is impossible. The proof applies
    `founding_diagonal` to the predicate of self-denial. -/
theorem no_self_model {D : Type u}
    (decode : D → (D → Prop)) (encode : (D → Prop) → D)
    (faithful : ∀ p, decode (encode p) = p) : False := by
  -- the liar: descriptions that deny themselves
  have hd : decode (encode (fun v => ¬ decode v v))
              = (fun v => ¬ decode v v) := faithful _
  -- self-application makes the named liar equal its own negation
  have key : decode (encode (fun v => ¬ decode v v))
                    (encode (fun v => ¬ decode v v))
           = ¬ decode (encode (fun v => ¬ decode v v))
                      (encode (fun v => ¬ decode v v)) :=
    congrFun hd (encode (fun v => ¬ decode v v))
  exact founding_diagonal _ key

/-- There is no complete interior self-model. Hence no consistent
    system can certify, from inside, that it is its own fundamental
    ground: whether the ground is the bottom or the image of a deeper
    level cannot be decided from within. -/
theorem aseity {D : Type u} :
    ¬ ∃ (decode : D → (D → Prop)) (encode : (D → Prop) → D),
        ∀ p, decode (encode p) = p := by
  intro ⟨decode, encode, faithful⟩
  exact no_self_model decode encode faithful

end Aseity

/- audit -/
#print axioms Aseity.founding_diagonal
#print axioms Aseity.no_self_model
#print axioms Aseity.aseity
