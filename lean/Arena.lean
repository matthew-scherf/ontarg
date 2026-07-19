/-!
# Arena
-/

namespace Arena

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

/-- `f` commutes with every transposition. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

/-- On three or more values, the only equivariant endomap is the identity. -/
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

/-- On one value, every endomap is the identity. -/
theorem bare_one_is_mute {V : Type u} (f : V → V)
    (h1 : ∀ x y : V, x = y) : ∀ x, f x = x :=
  fun x => h1 (f x) x

theorem not_equivariant : Equivariant (fun x : Bool => !x) := by
  intro a b x
  cases a <;> cases b <;> cases x <;> rfl

theorem not_moves : ∀ x : Bool, (fun x : Bool => !x) x ≠ x := by
  intro x; cases x <;> decide

theorem two_speaks :
    Equivariant (fun x : Bool => !x) ∧ (∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨not_equivariant, not_moves⟩

theorem arena_is_forced :
    (∀ (V : Type) (f : V → V), (∀ x y : V, x = y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨fun _ f h1 => bare_one_is_mute f h1,
   fun _ _ f he h3 => bare_three_is_mute f he h3,
   two_speaks⟩

/-- Converse of `bare_three_is_mute`: any nontrivial equivariant endomap forces exactly two values. -/
theorem speaks_needs_exactly_two {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f) (hne : ∃ x, f x ≠ x) :
    ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b := by
  obtain ⟨x₀, hx₀⟩ := hne
  have h3 : ¬ (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) := by
    intro h
    exact hx₀ (bare_three_is_mute f hequiv h x₀)
  have key : ∃ x y : V, ∀ z : V, z = x ∨ z = y := by
    apply Classical.byContradiction
    intro hc
    apply h3
    intro x y
    apply Classical.byContradiction
    intro hz
    apply hc
    refine ⟨x, y, fun z => ?_⟩
    apply Classical.byContradiction
    intro hzz
    exact hz ⟨z, fun h => hzz (Or.inl h), fun h => hzz (Or.inr h)⟩
  obtain ⟨a, b, hab⟩ := key
  refine ⟨a, b, ?_, hab⟩
  intro he
  apply hx₀
  apply bare_one_is_mute f
  intro u v
  rcases hab u with hu | hu <;> rcases hab v with hv | hv
  · rw [hu, hv]
  · rw [hu, hv, he]
  · rw [hu, hv, he]
  · rw [hu, hv]

theorem arena_iff_two :
    (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∃ x, f x ≠ x) → ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨fun _ _ f he h3 => bare_three_is_mute f he h3,
   fun _ _ f he hne => speaks_needs_exactly_two f he hne,
   two_speaks⟩

inductive V3 where
  | t | b | f
  deriving DecidableEq

open V3

def neg3 : V3 → V3
  | t => f
  | b => b
  | f => t

theorem v3_vacuum_is_static : neg3 b = b := rfl

/-- `neg3` is not equivariant: it names the vacuum `b`. -/
theorem v3_negation_names_the_vacuum : ¬ Equivariant neg3 := by
  intro h
  have hb := h b t b
  rw [transp_left] at hb
  exact absurd hb (by decide)

theorem escape_costs_a_name :
    neg3 b = b ∧ ¬ Equivariant neg3 :=
  ⟨v3_vacuum_is_static, v3_negation_names_the_vacuum⟩

/-- Relations on `V3` definable from equality alone. -/
inductive Defble3 : (V3 → V3 → Prop) → Prop where
  | eq : Defble3 (fun x y => x = y)
  | neg {R} : Defble3 R → Defble3 (fun x y => ¬ R x y)
  | conj {R S} : Defble3 R → Defble3 S → Defble3 (fun x y => R x y ∧ S x y)
  | disj {R S} : Defble3 R → Defble3 S → Defble3 (fun x y => R x y ∨ S x y)

theorem ne_defble3 : Defble3 (fun x y : V3 => ¬ (x = y)) :=
  Defble3.neg Defble3.eq

def flipTB : V3 → V3
  | t => b
  | _ => t

def runTB : Nat → V3
  | 0 => t
  | n + 1 => flipTB (runTB n)

def flipTF : V3 → V3
  | t => f
  | _ => t

def runTF : Nat → V3
  | 0 => t
  | n + 1 => flipTF (runTF n)

theorem runTB_mem : ∀ n, runTB n = t ∨ runTB n = b := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    cases ih with
    | inl h =>
      right
      show flipTB (runTB n) = b
      rw [h]; decide
    | inr h =>
      left
      show flipTB (runTB n) = t
      rw [h]; decide

theorem runTF_mem : ∀ n, runTF n = t ∨ runTF n = f := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    cases ih with
    | inl h =>
      right
      show flipTF (runTF n) = f
      rw [h]; decide
    | inr h =>
      left
      show flipTF (runTF n) = t
      rw [h]; decide

theorem runTB_runs : ∀ n, runTB n ≠ runTB (n + 1) := by
  intro n
  cases runTB_mem n with
  | inl h =>
    show runTB n ≠ flipTB (runTB n)
    rw [h]; decide
  | inr h =>
    show runTB n ≠ flipTB (runTB n)
    rw [h]; decide

theorem runTF_runs : ∀ n, runTF n ≠ runTF (n + 1) := by
  intro n
  cases runTF_mem n with
  | inl h =>
    show runTF n ≠ flipTF (runTF n)
    rw [h]; decide
  | inr h =>
    show runTF n ≠ flipTF (runTF n)
    rw [h]; decide

theorem v3_runs_diverge : runTB 0 = runTF 0 ∧ runTB 1 ≠ runTF 1 :=
  ⟨rfl, fun h => nomatch h⟩

theorem v3_no_structureless_realizer (g : V3 → V3) (hequiv : Equivariant g) :
    ¬ ∀ x : V3, g x ≠ x := by
  intro h
  have h3 : ∀ x y : V3, ∃ z : V3, z ≠ x ∧ z ≠ y := by
    intro x y
    cases x <;> cases y
    · exact ⟨b, by decide, by decide⟩
    · exact ⟨f, by decide, by decide⟩
    · exact ⟨b, by decide, by decide⟩
    · exact ⟨f, by decide, by decide⟩
    · exact ⟨t, by decide, by decide⟩
    · exact ⟨t, by decide, by decide⟩
    · exact ⟨b, by decide, by decide⟩
    · exact ⟨t, by decide, by decide⟩
    · exact ⟨b, by decide, by decide⟩
  exact h t (bare_three_is_mute g hequiv h3 t)

theorem three_does_not_determine :
    Defble3 (fun x y : V3 => ¬ (x = y))
    ∧ (∀ n, runTB n ≠ runTB (n + 1))
    ∧ (∀ n, runTF n ≠ runTF (n + 1))
    ∧ (runTB 0 = runTF 0 ∧ runTB 1 ≠ runTF 1)
    ∧ (∀ g : V3 → V3, Equivariant g → ¬ ∀ x, g x ≠ x) :=
  ⟨ne_defble3, runTB_runs, runTF_runs, v3_runs_diverge,
   fun g hg => v3_no_structureless_realizer g hg⟩

end Arena

#print axioms Arena.transp_left
#print axioms Arena.transp_fixes
#print axioms Arena.bare_three_is_mute
#print axioms Arena.bare_one_is_mute
#print axioms Arena.two_speaks
#print axioms Arena.arena_is_forced
#print axioms Arena.speaks_needs_exactly_two
#print axioms Arena.arena_iff_two
#print axioms Arena.v3_negation_names_the_vacuum
#print axioms Arena.escape_costs_a_name
#print axioms Arena.v3_runs_diverge
#print axioms Arena.v3_no_structureless_realizer
#print axioms Arena.three_does_not_determine
