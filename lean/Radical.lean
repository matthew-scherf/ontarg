/-!
# Radical

The claim "every self-map of every carrier is fixed-point-free at
every point" fails unrestricted (`id`), fails restricted to
non-identity maps (a constant map), and fails restricted to
equivariant ("structureless") maps: on three or more values every
equivariant map is the identity (`bare_three_is_mute`); only on
exactly two values does an equivariant fixed-point-free map exist
(`not` on `Bool`).
-/

namespace Radical

def RadicalClaimUnrestricted : Prop :=
  ∀ (C : Type) (f : C → C) (x : C), f x ≠ x

theorem radical_unrestricted_false : ¬ RadicalClaimUnrestricted :=
  fun h => h Bool id true rfl

def RadicalClaimNontrivial : Prop :=
  ∀ (C : Type) (f : C → C), f ≠ id → ∀ x : C, f x ≠ x

def constTrue : Bool → Bool := fun _ => true

theorem constTrue_ne_id : constTrue ≠ (id : Bool → Bool) := by
  intro h
  have h2 : constTrue false = id false := congrFun h false
  exact Bool.noConfusion h2

theorem radical_nontrivial_false : ¬ RadicalClaimNontrivial :=
  fun h => absurd rfl (h Bool constTrue constTrue_ne_id true)

/-- The simplest relabeling. -/
def transp {V : Type u} [DecidableEq V] (a b : V) : V → V :=
  fun x => if x = a then b else if x = b then a else x

theorem transp_left {V : Type u} [DecidableEq V] (a b : V) :
    transp a b a = b := by
  show (if a = a then b else if a = b then a else a) = b
  rw [if_pos rfl]

theorem transp_fixes {V : Type u} [DecidableEq V] {a b x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) : transp a b x = x := by
  show (if x = a then b else if x = b then a else x) = x
  rw [if_neg hxa, if_neg hxb]

/-- Commutes with every relabeling. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

theorem bare_three_is_mute {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f)
    (h3 : ∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) :
    ∀ x, f x = x := by
  intro x
  by_cases hfx : f x = x
  · exact hfx
  · obtain ⟨z, hzx, hzf⟩ := h3 x (f x)
    have hxfix : transp (f x) z x = x :=
      transp_fixes (fun h => hfx h.symm) (fun h => hzx h.symm)
    have h := hequiv (f x) z x
    rw [hxfix, transp_left] at h
    exact absurd h.symm hzf

theorem no_total_instability_beyond_two {V : Type u} [DecidableEq V]
    (f : V → V) (hequiv : Equivariant f)
    (h3 : ∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) (v : V) :
    ¬ (∀ x, f x ≠ x) :=
  fun htot => htot v (bare_three_is_mute f hequiv h3 v)

theorem two_is_totally_unstable :
    Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x := by
  refine ⟨?_, ?_⟩
  · intro a b x; cases a <;> cases b <;> cases x <;> rfl
  · intro x; cases x <;> decide

theorem instability_is_singular :
    ¬ RadicalClaimUnrestricted
    ∧ ¬ RadicalClaimNontrivial
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ _v : V, ¬ (∀ x, f x ≠ x))
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨radical_unrestricted_false, radical_nontrivial_false,
   fun _ _ f he h3 v => no_total_instability_beyond_two f he h3 v,
   two_is_totally_unstable⟩

end Radical

#print axioms Radical.radical_unrestricted_false
#print axioms Radical.constTrue_ne_id
#print axioms Radical.radical_nontrivial_false
#print axioms Radical.transp_left
#print axioms Radical.transp_fixes
#print axioms Radical.bare_three_is_mute
#print axioms Radical.no_total_instability_beyond_two
#print axioms Radical.two_is_totally_unstable
#print axioms Radical.instability_is_singular
