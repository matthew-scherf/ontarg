/-!
# Aseity

`D` with `decode : D → (D → Prop)` and `encode : (D → Prop) → D`.
No faithful self-model (`decode ∘ encode = id`) exists.
-/

namespace Aseity

/-- `X = ¬X` has no solution. -/
theorem founding_diagonal (X : Prop) (h : X = ¬ X) : False :=
  have hiff : X ↔ ¬ X := Iff.of_eq h
  have hn : ¬ X := fun hx => hiff.mp hx hx
  hn (hiff.mpr hn)

/-- No faithful self-model: applies `founding_diagonal` to the self-denial predicate. -/
theorem no_self_model {D : Type u}
    (decode : D → (D → Prop)) (encode : (D → Prop) → D)
    (faithful : ∀ p, decode (encode p) = p) : False := by
  have hd : decode (encode (fun v => ¬ decode v v))
              = (fun v => ¬ decode v v) := faithful _
  have key : decode (encode (fun v => ¬ decode v v))
                    (encode (fun v => ¬ decode v v))
           = ¬ decode (encode (fun v => ¬ decode v v))
                      (encode (fun v => ¬ decode v v)) :=
    congrFun hd (encode (fun v => ¬ decode v v))
  exact founding_diagonal _ key

theorem aseity {D : Type u} :
    ¬ ∃ (decode : D → (D → Prop)) (encode : (D → Prop) → D),
        ∀ p, decode (encode p) = p := by
  intro ⟨decode, encode, faithful⟩
  exact no_self_model decode encode faithful

end Aseity

#print axioms Aseity.founding_diagonal
#print axioms Aseity.no_self_model
#print axioms Aseity.aseity
