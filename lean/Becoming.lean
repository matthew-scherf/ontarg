/-!
# Becoming

-/

namespace Becoming



/-- Two states of `M` differ. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b


theorem retorsion {M : Type} (t : Prop → M)
    (h : t (¬ Draws M) ≠ t (Draws M)) : Draws M :=
  ⟨t (¬ Draws M), t (Draws M), h⟩

theorem no_undrawn_denial {M : Type} (t : Prop → M) :
    ¬ (t (¬ Draws M) ≠ t (Draws M) ∧ ¬ Draws M) :=
  fun ⟨hd, hn⟩ => hn (retorsion t hd)



/-- Transposition of two values. -/
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

theorem transp_right {V : Type u} [DecidableEq V] {a b : V} (hab : a ≠ b) :
    transp a b b = a := by
  show (if b = a then b else if b = b then a else b) = a
  rw [if_neg (fun h => hab h.symm), if_pos rfl]

theorem transp_same {V : Type u} [DecidableEq V] (a x : V) :
    transp a a x = x := by
  show (if x = a then a else if x = a then a else x) = x
  by_cases h : x = a
  · rw [if_pos h]; exact h.symm
  · rw [if_neg h, if_neg h]

/-- `f` commutes with every transposition. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

/-- On three or more values, no equivariant map moves anything. -/
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

theorem bare_one_is_mute {V : Type u} (f : V → V)
    (h1 : ∀ x y : V, x = y) : ∀ x, f x = x :=
  fun x => h1 (f x) x

/-- A third value stills the arena: with three points, no equivariant law
moves anything. -/
theorem third_value_stills {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f)
    (h3 : ∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) :
    ¬ ∃ x, f x ≠ x :=
  fun ⟨x, hx⟩ => hx (bare_three_is_mute f hequiv h3 x)

/-- Three pairwise-distinct values supply a third value beside any two:
two points exclude at most two of the three. -/
theorem three_gives_third {V : Type u} [DecidableEq V] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : V) :
    ∃ z : V, z ≠ x ∧ z ≠ y := by
  by_cases hax : a = x
  · by_cases hby : b = y
    · exact ⟨c, fun h => hac (hax.trans h.symm),
        fun h => hbc (hby.trans h.symm)⟩
    · exact ⟨b, fun h => hab (hax.trans h.symm), hby⟩
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · exact ⟨c, fun h => hbc (hbx.trans h.symm),
          fun h => hac (hay.trans h.symm)⟩
      · exact ⟨b, hbx, fun h => hab (hay.trans h.symm)⟩
    · exact ⟨a, hax, hay⟩

/-- Three values still the arena. A carrier holding three pairwise-distinct
values admits no equivariant law beyond the identity, so adding a third
value to the two-valued arena costs every motion. -/
theorem three_values_are_still {V : Type u} [DecidableEq V] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : V → V) (hf : Equivariant f) : ∀ x, f x = x :=
  bare_three_is_mute f hf (three_gives_third hab hac hbc)

theorem two_at_most {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f) {x : V} (hfx : f x ≠ x) :
    ∀ z : V, z = x ∨ z = f x := by
  intro z
  by_cases hzx : z = x
  · exact Or.inl hzx
  · by_cases hzf : z = f x
    · exact Or.inr hzf
    · have hxfix : transp (f x) z x = x :=
        transp_fixes (fun h => hfx h.symm) (fun h => hzx h.symm)
      have h := hequiv (f x) z x
      rw [hxfix, transp_left] at h
      exact absurd h.symm hzf

/-- On a two-element carrier the transposition is equivariant and moves
its points. -/
theorem two_swaps {V : Type u} [DecidableEq V] {a b : V} (hab : a ≠ b)
    (h2 : ∀ z : V, z = a ∨ z = b) :
    Equivariant (transp a b) ∧ transp a b a ≠ a := by
  constructor
  · intro c d y
    obtain rfl | rfl := h2 c
    · obtain rfl | rfl := h2 d
      · rw [transp_same, transp_same]
      · rfl
    · obtain rfl | rfl := h2 d
      · obtain rfl | rfl := h2 y
        · rw [transp_right (Ne.symm hab), transp_right hab, transp_left,
            transp_left]
        · rw [transp_left, transp_right hab, transp_left,
            transp_right (Ne.symm hab)]
      · rw [transp_same, transp_same]
  · rw [transp_left]
    exact Ne.symm hab

/-- The arena is two: an equivariant map displaces a point exactly when
the carrier has two elements. -/
theorem moves_iff_two {V : Type u} [DecidableEq V] :
    (∃ f : V → V, Equivariant f ∧ ∃ x : V, f x ≠ x)
      ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b := by
  constructor
  · intro ⟨f, hf, x, hx⟩
    exact ⟨x, f x, Ne.symm hx, two_at_most f hf hx⟩
  · intro ⟨a, b, hab, h2⟩
    exact ⟨transp a b, (two_swaps hab h2).1, a, (two_swaps hab h2).2⟩


theorem two_speaks :
    Equivariant (fun x : Bool => !x) ∧ (∀ x : Bool, !x ≠ x) := by
  constructor
  · intro a b x; cases a <;> cases b <;> cases x <;> rfl
  · intro x; cases x <;> decide


def Structureless (g : Bool → Bool) : Prop := ∀ b, g (!b) = !(g b)

/-- A structureless `g : Bool → Bool` is `id` or `not`. -/
theorem one_candidate (g : Bool → Bool) (h : Structureless g) :
    (∀ b, g b = b) ∨ (∀ b, g b = !b) := by
  cases htrue : g true with
  | true =>
    left
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := h true
      rw [htrue] at hf
      exact hf
  | false =>
    right
    intro b
    cases b with
    | true  => exact htrue
    | false =>
      have hf := h true
      rw [htrue] at hf
      exact hf

theorem constants_not_structureless (c : Bool) :
    ¬ Structureless (fun _ => c) := by
  intro h
  have hc := h true
  revert hc
  cases c <;> decide

theorem id_says_nothing : ∀ b : Bool, id b = b := fun _ => rfl

theorem id_structureless : Structureless (fun b => b) := fun _ => rfl

theorem transp_true_false : ∀ x : Bool, transp true false x = !x := by
  intro x; cases x <;> decide

theorem transp_false_true : ∀ x : Bool, transp false true x = !x := by
  intro x; cases x <;> decide

/-- On `Bool` the two notions coincide: commuting with every transposition
is commuting with the swap, which is commuting with complement. -/
theorem equivariant_iff_structureless (g : Bool → Bool) :
    Equivariant g ↔ Structureless g := by
  constructor
  · intro he b
    have h := he true false b
    rw [transp_true_false, transp_true_false] at h
    exact h
  · intro hs a b x
    cases a <;> cases b
    · rw [transp_same, transp_same]
    · rw [transp_false_true, transp_false_true]
      exact hs x
    · rw [transp_true_false, transp_true_false]
      exact hs x
    · rw [transp_same, transp_same]

inductive Defble : (Bool → Bool → Prop) → Prop where
  | eq : Defble (fun a b => a = b)
  | neg {R} : Defble R → Defble (fun a b => ¬ R a b)
  | conj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∧ S a b)
  | disj {R S} : Defble R → Defble S → Defble (fun a b => R a b ∨ S a b)

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

/-- `Defble R` gives `R a a ↔ R b b` for all `a b`. -/
theorem diagonal_uniform {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a a ↔ R b b := by
  intro a b
  cases a <;> cases b
  · exact Iff.rfl
  · exact defble_invariant h false false
  · exact defble_invariant h true true
  · exact Iff.rfl

theorem invariant_binary_classified (f : Bool → Bool → Bool)
    (hinv : ∀ a b, f (!a) (!b) = f a b) :
    (∀ a b, f a b = (a == b)) ∨ (∀ a b, f a b = (a != b))
    ∨ (∀ a b, f a b = true) ∨ (∀ a b, f a b = false) := by
  have hff : f false false = f true true := hinv true true
  have hft : f false true = f true false := hinv true false
  cases htt : f true true <;> cases htf : f true false
  · right; right; right
    intro a b
    cases a <;> cases b
    · exact hff.trans htt
    · exact hft.trans htf
    · exact htf
    · exact htt
  · right; left
    intro a b
    cases a <;> cases b
    · exact hff.trans htt
    · exact hft.trans htf
    · exact htf
    · exact htt
  · left
    intro a b
    cases a <;> cases b
    · exact hff.trans htt
    · exact hft.trans htf
    · exact htf
    · exact htt
  · right; right; left
    intro a b
    cases a <;> cases b
    · exact hff.trans htt
    · exact hft.trans htf
    · exact htf
    · exact htt

/-- Definable relations are decidable, as a disjunction in `Prop`. -/
theorem defble_decidable {R : Bool → Bool → Prop} (h : Defble R) :
    ∀ a b, R a b ∨ ¬ R a b := by
  induction h with
  | eq =>
    intro a b
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr hab
  | neg _ ih =>
    intro a b
    cases ih a b with
    | inl hr => exact Or.inr (fun hn => hn hr)
    | inr hn => exact Or.inl hn
  | conj _ _ ih1 ih2 =>
    intro a b
    cases ih1 a b with
    | inl h1 =>
      cases ih2 a b with
      | inl h2 => exact Or.inl ⟨h1, h2⟩
      | inr h2 => exact Or.inr (fun hc => h2 hc.2)
    | inr h1 => exact Or.inr (fun hc => h1 hc.1)
  | disj _ _ ih1 ih2 =>
    intro a b
    cases ih1 a b with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h1 =>
      cases ih2 a b with
      | inl h2 => exact Or.inl (Or.inr h2)
      | inr h2 => exact Or.inr (fun hd => hd.elim h1 h2)

/-- The `Defble` classification: a definable relation is extensionally
equality, disagreement, the full relation, or the empty one. -/
theorem defble_classified {R : Bool → Bool → Prop} (h : Defble R) :
    (∀ a b, R a b ↔ a = b) ∨ (∀ a b, R a b ↔ a ≠ b)
    ∨ (∀ a b, R a b) ∨ (∀ a b, ¬ R a b) := by
  have hinv := defble_invariant h
  cases defble_decidable h true true with
  | inl htt =>
    cases defble_decidable h true false with
    | inl htf =>
      right; right; left
      intro a b
      cases a <;> cases b
      · exact (hinv true true).mp htt
      · exact (hinv true false).mp htf
      · exact htf
      · exact htt
    | inr hntf =>
      left
      intro a b
      cases a <;> cases b
      · exact ⟨fun _ => rfl, fun _ => (hinv true true).mp htt⟩
      · exact ⟨fun hr => absurd ((hinv false true).mp hr) hntf,
               fun he => Bool.noConfusion he⟩
      · exact ⟨fun hr => absurd hr hntf, fun he => Bool.noConfusion he⟩
      · exact ⟨fun _ => rfl, fun _ => htt⟩
  | inr hntt =>
    cases defble_decidable h true false with
    | inl htf =>
      right; left
      intro a b
      cases a <;> cases b
      · exact ⟨fun hr => absurd ((diagonal_uniform h false true).mp hr) hntt,
               fun hne => absurd rfl hne⟩
      · exact ⟨fun _ he => Bool.noConfusion he, fun _ => (hinv true false).mp htf⟩
      · exact ⟨fun _ he => Bool.noConfusion he, fun _ => htf⟩
      · exact ⟨fun hr => absurd hr hntt, fun hne => absurd rfl hne⟩
    | inr hntf =>
      right; right; right
      intro a b
      cases a <;> cases b
      · exact fun hr => hntt ((diagonal_uniform h false true).mp hr)
      · exact fun hr => hntf ((hinv false true).mp hr)
      · exact hntf
      · exact hntt

/-- Bool-to-Prop bridge: every invariant Boolean-valued binary function is
the extension of a definable relation. -/
theorem invariant_extends_defble (f : Bool → Bool → Bool)
    (hinv : ∀ a b, f (!a) (!b) = f a b) :
    ∃ S, Defble S ∧ ∀ a b, (f a b = true ↔ S a b) := by
  cases invariant_binary_classified f hinv with
  | inl heq =>
    refine ⟨fun a b => a = b, Defble.eq, ?_⟩
    intro a b
    rw [heq]
    cases a <;> cases b <;> decide
  | inr rest =>
    cases rest with
    | inl hne =>
      refine ⟨fun a b => ¬ (a = b), Defble.neg Defble.eq, ?_⟩
      intro a b
      rw [hne]
      cases a <;> cases b <;> decide
    | inr rest2 =>
      cases rest2 with
      | inl hfull =>
        refine ⟨fun a b => a = b ∨ ¬ (a = b),
          Defble.disj Defble.eq (Defble.neg Defble.eq), ?_⟩
        intro a b
        rw [hfull]
        cases a <;> cases b <;> decide
      | inr hempty =>
        refine ⟨fun a b => a = b ∧ ¬ (a = b),
          Defble.conj Defble.eq (Defble.neg Defble.eq), ?_⟩
        intro a b
        rw [hempty]
        cases a <;> cases b <;> decide

/-- Prop-to-Bool bridge: every definable relation is the extension of an
invariant Boolean-valued binary function. -/
theorem defble_extends_invariant {R : Bool → Bool → Prop} (h : Defble R) :
    ∃ f : Bool → Bool → Bool,
      (∀ a b, f (!a) (!b) = f a b) ∧ ∀ a b, (f a b = true ↔ R a b) := by
  cases defble_classified h with
  | inl hcl =>
    refine ⟨fun a b => a == b, ?_, ?_⟩
    · intro a b; cases a <;> cases b <;> decide
    · intro a b
      exact (show (a == b) = true ↔ a = b by cases a <;> cases b <;> decide).trans
        (hcl a b).symm
  | inr rest =>
    cases rest with
    | inl hcl =>
      refine ⟨fun a b => a != b, ?_, ?_⟩
      · intro a b; cases a <;> cases b <;> decide
      · intro a b
        exact (show (a != b) = true ↔ a ≠ b by cases a <;> cases b <;> decide).trans
          (hcl a b).symm
    | inr rest2 =>
      cases rest2 with
      | inl hfull =>
        exact ⟨fun _ _ => true, fun _ _ => rfl,
          fun a b => ⟨fun _ => hfull a b, fun _ => rfl⟩⟩
      | inr hempty =>
        exact ⟨fun _ _ => false, fun _ _ => rfl,
          fun a b => ⟨fun he => Bool.noConfusion he,
            fun hr => absurd hr (hempty a b)⟩⟩

/- no necessary being -/

theorem no_static_instance : ∀ b : Bool, not b ≠ b := by
  intro b
  cases b <;> decide

/-- `X ↔ ¬X` has no solution. -/
theorem no_being (X : Prop) (h : X ↔ ¬ X) : False :=
  have hn : ¬ X := fun hx => h.mp hx hx
  hn (h.mpr hn)

/-- The equality form, derived from the biconditional. -/
theorem no_being_eq (X : Prop) (h : X = ¬ X) : False :=
  no_being X (Iff.of_eq h)

/- necessary becoming -/

variable {S : Type u}

/-- `x` solves the recursion `f`. -/
def Solves (f : S → S) (x : Nat → S) : Prop := ∀ n, x (n + 1) = f (x n)

/-- Trajectory of `f` from `seed`. -/
def orbit (f : S → S) (seed : S) : Nat → S
  | 0     => seed
  | n + 1 => f (orbit f seed n)

theorem becoming_exists (f : S → S) (seed : S) :
    Solves f (orbit f seed) ∧ orbit f seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

theorem becoming_unique (f : S → S) (x : Nat → S)
    (hx : Solves f x) (seed : S) (h0 : x 0 = seed) :
    ∀ n, x n = orbit f seed n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hx k, ih]; rfl

/-- `orbit not seed` has period 2. -/
theorem two_tick_clock (seed : Bool) :
    ∀ n, orbit not seed (n + 2) = orbit not seed n := by
  intro n
  show (!(!(orbit not seed n))) = orbit not seed n
  cases orbit not seed n with
  | true  => rfl
  | false => rfl

/- link 4:  -/

theorem no_fixpoint : ∀ x : Bool, x ≠ !x := by
  intro x; cases x <;> decide

theorem ne_eq_not : ∀ a b : Bool, a ≠ b → b = !a := by
  intro a b h
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

/-- `R` excludes `x`: read of itself, it fails there. -/
def Excludes (R : Bool → Bool → Prop) (x : Bool) : Prop := ¬ R x x

/-- `R` excludes some state. -/
def Says (R : Bool → Bool → Prop) : Prop := ∃ x, Excludes R x

/-- The graph of the identity excludes nothing. -/
theorem id_graph_says_nothing : ¬ Says (fun a b : Bool => a = b) :=
  fun ⟨_, hx⟩ => hx rfl

/-- A state satisfies `R` read of itself. -/
def ObjSat (R : Bool → Bool → Prop) : Prop := ∃ x, R x x

/-- An unending run each of whose steps satisfies `R`. -/
def ProcSat (R : Bool → Bool → Prop) : Prop :=
  ∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1))

/-- `R` is satisfied in some frame. -/
def Sat (R : Bool → Bool → Prop) : Prop := ObjSat R ∨ ProcSat R

/-- `R` excludes something and is satisfied somewhere. -/
def Articulates (R : Bool → Bool → Prop) : Prop := Says R ∧ Sat R

theorem says_kills_the_object {R : Bool → Bool → Prop}
    (hD : Defble R) (hS : Says R) : ¬ ObjSat R := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hS
  exact hy ((diagonal_uniform hD x y).mp hx)

theorem clock_runs (b : Bool) :
    ∀ n, orbit not b n ≠ orbit not b (n + 1) :=
  fun n => no_fixpoint (orbit not b n)

theorem run_unique {t : Nat → Bool} (ht : ∀ n, t n ≠ t (n + 1)) :
    ∀ n, t n = orbit not (t 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show t (n + 1) = !(orbit not (t 0) n)
    rw [← ih]
    exact ne_eq_not (t n) (t (n + 1)) (ht n)

/-- A `Defble`, `Articulates` relation is `R a b ↔ a ≠ b`. -/
theorem absolute_law {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) : ∀ a b, R a b ↔ a ≠ b := by
  obtain ⟨hS, hSat⟩ := hA
  have hdiag : ∀ x, ¬ R x x := by
    intro x
    obtain ⟨y, hy⟩ := hS
    intro hx
    exact hy ((diagonal_uniform hD x y).mp hx)
  have hproc : ProcSat R := by
    cases hSat with
    | inl hobj => exact absurd hobj (says_kills_the_object hD hS)
    | inr hproc => exact hproc
  obtain ⟨s, hs⟩ := hproc
  have hstep : R (s 0) (s 1) := hs 0
  have hne : s 0 ≠ s 1 := fun he => hdiag (s 0) (he ▸ hstep)
  have hoff : ∀ a, R a (!a) := by
    intro a
    cases h0 : s 0 <;> cases h1 : s 1
    · exact absurd (h0.trans h1.symm) hne
    · have hft : R false true := h0 ▸ h1 ▸ hstep
      cases a
      · exact hft
      · exact (defble_invariant hD false true).mp hft
    · have htf : R true false := h0 ▸ h1 ▸ hstep
      cases a
      · exact (defble_invariant hD true false).mp htf
      · exact htf
    · exact absurd (h0.trans h1.symm) hne
  intro a b
  constructor
  · intro hab he; exact hdiag a (he ▸ hab)
  · intro hab; exact (ne_eq_not a b hab) ▸ hoff a

theorem absolute_articulation {R : Bool → Bool → Prop}
    (hD : Defble R) (hA : Articulates R) :
    (∀ a b, R a b ↔ a ≠ b)
    ∧ (¬ ∃ x, R x x)
    ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
    ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
        ∀ n, t n = orbit not (t 0) n) := by
  have hlaw := absolute_law hD hA
  refine ⟨hlaw, says_kills_the_object hD hA.1, ⟨orbit not true, ?_⟩, ?_⟩
  · intro n
    exact (hlaw (orbit not true n) (orbit not true (n + 1))).mpr
      (clock_runs true n)
  · intro t ht
    exact run_unique (fun n => (hlaw (t n) (t (n + 1))).mp (ht n))

theorem absolute_is_inhabited :
    Defble (fun a b => ¬ (a = b)) ∧ Articulates (fun a b => ¬ (a = b)) := by
  refine ⟨Defble.neg Defble.eq, ⟨true, fun h => h rfl⟩,
    Or.inr ⟨orbit not true, ?_⟩⟩
  intro n
  exact clock_runs true n

/- link 5: -/

theorem refusal_is_running (f : S → S) :
    (∀ x, f x ≠ x) ↔ ∀ seed n, orbit f seed (n + 1) ≠ orbit f seed n := by
  constructor
  · intro h seed n
    exact h (orbit f seed n)
  · intro h x
    exact h x 0

/- link 6: -/

/-- Relabelling a run: negate every value. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => !(s n)

theorem seed_is_relabel :
    ∀ n, orbit not false n = relabel (orbit not true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show not (orbit not false n) = not (orbit not true (n + 1))
    rw [ih]
    rfl


/- link 7: discrimination -/

/-- `h` takes different values at two loci of `T`. -/
def Occurs {T : Type} (h : T → Bool) : Prop := ∃ t₁ t₂ : T, h t₁ ≠ h t₂

theorem event_retorsion {T : Type} (h : T → Bool) (tok : Prop → T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) : Occurs h :=
  ⟨tok (¬ Occurs h), tok (Occurs h), hd⟩

theorem discrimination {T : Type} (h : T → Bool)
    (tok : Prop → T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) :
    Occurs h
    ∧ tok (¬ Occurs h) ≠ tok (Occurs h)
    ∧ h (tok (Occurs h)) = !(h (tok (¬ Occurs h))) :=
  ⟨event_retorsion h tok hd,
   fun he => hd (congrArg h he),
   ne_eq_not _ _ hd⟩

/- link 8: the mark -/

/-- `f` commutes with the transpositions fixing the mark `m`. -/
def MarkedEquivariant {V : Type u} [DecidableEq V] (m : V) (f : V → V) : Prop :=
  ∀ a b x : V, a ≠ m → b ≠ m → f (transp a b x) = transp a b (f x)

/-- Marking one point releases the stillness of `bare_three_is_mute`: the
map sending everything to the mark respects every symmetry fixing the mark
and displaces each other point. The minimal draw is the price of dynamics. -/
theorem marked_three_moves {V : Type u} [DecidableEq V] (m x : V)
    (hx : x ≠ m) :
    ∃ f : V → V, MarkedEquivariant m f ∧ f x ≠ x := by
  refine ⟨fun _ => m, ?_, ?_⟩
  · intro a b y ha hb
    show m = transp a b m
    unfold transp
    rw [if_neg (fun h => ha h.symm), if_neg (fun h => hb h.symm)]
  · intro h
    exact hx h.symm

/-- Given two points beside the mark, every mark-respecting map fixes the
mark: the motion released by the first distinction leaves it standing. -/
theorem mark_is_fixed {V : Type u} [DecidableEq V] (m : V) (f : V → V)
    (hf : MarkedEquivariant m f)
    (h2 : ∀ c : V, c ≠ m → ∃ b : V, b ≠ m ∧ b ≠ c) :
    f m = m := by
  by_cases hc : f m = m
  · exact hc
  · obtain ⟨b, hbm, hbc⟩ := h2 (f m) hc
    have hfix : transp (f m) b m = m :=
      transp_fixes (fun h => hc h.symm) (fun h => hbm h.symm)
    have h := hf (f m) b m hc hbm
    rw [hfix, transp_left] at h
    exact absurd h.symm hbc

/-- On the dyad, negation respects the mark vacuously and moves it. The
hypothesis of `mark_is_fixed` is sharp: stillness of the mark begins at
the third point. -/
theorem two_moves_the_mark :
    MarkedEquivariant true (fun x : Bool => !x)
    ∧ (fun x : Bool => !x) true ≠ true := by
  constructor
  · intro a b x ha hb
    cases a with
    | true  => exact absurd rfl ha
    | false =>
      cases b with
      | true  => exact absurd rfl hb
      | false => cases x <;> decide
  · decide

/-- Under mark-respecting dynamics with two witnesses beside the mark, the
whole orbit of the mark is the mark: it holds at every tick. -/
theorem mark_orbit_still {V : Type u} [DecidableEq V] (m : V) (f : V → V)
    (hf : MarkedEquivariant m f)
    (h2 : ∀ c : V, c ≠ m → ∃ b : V, b ≠ m ∧ b ≠ c) :
    ∀ n, orbit f m n = m := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show f (orbit f m k) = m
    rw [ih]
    exact mark_is_fixed m f hf h2

/-- The mark as pivot: a mark-respecting map that moves the mark leaves
the carrier at the mark and its image. -/
theorem marked_two_at_most {V : Type u} [DecidableEq V] (m : V) (f : V → V)
    (hf : MarkedEquivariant m f) (hm : f m ≠ m) :
    ∀ z : V, z = m ∨ z = f m := by
  intro z
  by_cases hzm : z = m
  · exact Or.inl hzm
  · by_cases hzf : z = f m
    · exact Or.inr hzf
    · have hfix : transp (f m) z m = m :=
        transp_fixes (fun h => hm h.symm) (fun h => hzm h.symm)
      have h := hf (f m) z m hm hzm
      rw [hfix, transp_left] at h
      exact absurd h.symm hzf

/-- Two points hold one point beside the mark. -/
theorem two_off_mark_eq {V : Type u} {a b m : V}
    (h2 : ∀ z : V, z = a ∨ z = b) {c d : V} (hc : c ≠ m) (hd : d ≠ m) :
    c = d := by
  cases h2 m with
  | inl hm =>
    cases h2 c with
    | inl hca => exact absurd (hca.trans hm.symm) hc
    | inr hcb =>
      cases h2 d with
      | inl hda => exact absurd (hda.trans hm.symm) hd
      | inr hdb => exact hcb.trans hdb.symm
  | inr hm =>
    cases h2 c with
    | inl hca =>
      cases h2 d with
      | inl hda => exact hca.trans hda.symm
      | inr hdb => exact absurd (hdb.trans hm.symm) hd
    | inr hcb => exact absurd (hcb.trans hm.symm) hc

/-- On two points the transposition respects every mark and refuses
everywhere. -/
theorem two_swaps_marked {V : Type u} [DecidableEq V] (m : V) {a b : V}
    (hab : a ≠ b) (h2 : ∀ z : V, z = a ∨ z = b) :
    MarkedEquivariant m (transp a b) ∧ ∀ x : V, transp a b x ≠ x := by
  constructor
  · intro c d x hc hd
    rw [two_off_mark_eq h2 hc hd, transp_same, transp_same]
  · intro x
    cases h2 x with
    | inl hx => rw [hx, transp_left]; exact Ne.symm hab
    | inr hx => rw [hx, transp_right hab]; exact hab

/-- A mark-respecting map moves the mark exactly when the carrier is
two. -/
theorem mark_moves_iff_two {V : Type u} [DecidableEq V] (m : V) :
    (∃ f : V → V, MarkedEquivariant m f ∧ f m ≠ m)
      ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b := by
  constructor
  · intro ⟨f, hf, hm⟩
    exact ⟨m, f m, Ne.symm hm, marked_two_at_most m f hf hm⟩
  · intro ⟨a, b, hab, h2⟩
    exact ⟨transp a b, (two_swaps_marked m hab h2).1,
      (two_swaps_marked m hab h2).2 m⟩

/-- Refusal everywhere under a mark-respecting map holds exactly on two:
the marked route to the arena, matching `moves_iff_two`. -/
theorem marked_refuses_iff_two {V : Type u} [DecidableEq V] (m : V) :
    (∃ f : V → V, MarkedEquivariant m f ∧ ∀ x : V, f x ≠ x)
      ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b := by
  constructor
  · intro ⟨f, hf, href⟩
    exact (mark_moves_iff_two m).mp ⟨f, hf, href m⟩
  · intro ⟨a, b, hab, h2⟩
    exact ⟨transp a b, (two_swaps_marked m hab h2).1,
      (two_swaps_marked m hab h2).2⟩

/- the conjunction -/

/-- formal core: one conjunction of conditionals. -/
theorem ontological_argument :
    -- 1. the distinction is drawn
    (∀ (M : Type) (t : Prop → M), t (¬ Draws M) ≠ t (Draws M) → Draws M)
    -- 2. the arena is two
    ∧ (∀ (V : Type) (f : V → V), (∀ x y : V, x = y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V],
        (∃ f : V → V, Equivariant f ∧ ∃ x : V, f x ≠ x)
          ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, !x ≠ x)
    -- 3. one candidate: structureless laws are {id, not}
    ∧ (∀ g : Bool → Bool, Structureless g →
        (∀ b, g b = b) ∨ (∀ b, g b = !b))
    ∧ (∀ c : Bool, ¬ Structureless (fun _ => c))
    ∧ (∀ b : Bool, id b = b)
    ∧ ¬ Says (fun a b : Bool => a = b)
    ∧ (∀ R : Bool → Bool → Prop, Defble R → ∀ a b, R a a ↔ R b b)
    -- 4. so the absolute runs, and can only run
    ∧ (∀ R : Bool → Bool → Prop, Defble R → Articulates R →
        (∀ a b, R a b ↔ a ≠ b)
        ∧ (¬ ∃ x, R x x)
        ∧ (∃ s : Nat → Bool, ∀ n, R (s n) (s (n + 1)))
        ∧ (∀ t : Nat → Bool, (∀ n, R (t n) (t (n + 1))) →
            ∀ n, t n = orbit not (t 0) n))
    -- no necessary being: nothing static answers to the ground
    ∧ (∀ b : Bool, not b ≠ b)
    ∧ (∀ x : Bool, x ≠ !x)
    ∧ (∀ X : Prop, (X ↔ ¬ X) → False)
    -- necessary becoming: the run exists, is unique, has period two
    ∧ (∀ seed : Bool,
        (Solves not (orbit not seed) ∧ orbit not seed 0 = seed)
        ∧ (∀ x, Solves not x → x 0 = seed →
            ∀ n, x n = orbit not seed n)
        ∧ (∀ n, orbit not seed (n + 2) = orbit not seed n))
    -- 5. the refusal is the running
    ∧ ((∀ b : Bool, not b ≠ b) ↔
        ∀ seed n, orbit not seed (n + 1) ≠ orbit not seed n)
    -- 6. the seed is a label
    ∧ (∀ n, orbit not false n = relabel (orbit not true) n)
    -- 7. discrimination
    ∧ (∀ (T : Type) (h : T → Bool) (tok : Prop → T),
        h (tok (¬ Occurs h)) ≠ h (tok (Occurs h)) →
        Occurs h
        ∧ tok (¬ Occurs h) ≠ tok (Occurs h)
        ∧ h (tok (Occurs h)) = !(h (tok (¬ Occurs h))))
    -- 8. the mark moves the mute arena and stays fixed
    ∧ (∀ (V : Type) [DecidableEq V] (m x : V), x ≠ m →
        ∃ f : V → V, MarkedEquivariant m f ∧ f x ≠ x)
    ∧ (∀ (V : Type) [DecidableEq V] (m : V) (f : V → V),
        MarkedEquivariant m f →
        (∀ c : V, c ≠ m → ∃ b : V, b ≠ m ∧ b ≠ c) →
        f m = m ∧ ∀ n, orbit f m n = m)
    ∧ (MarkedEquivariant true (fun x : Bool => !x)
        ∧ (fun x : Bool => !x) true ≠ true)
    ∧ (∀ (V : Type) [DecidableEq V] (m : V),
        ((∃ f : V → V, MarkedEquivariant m f ∧ f m ≠ m)
          ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b)
        ∧ ((∃ f : V → V, MarkedEquivariant m f ∧ ∀ x : V, f x ≠ x)
          ↔ ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b)) :=
  ⟨fun _ t h => retorsion t h,
   fun _ f h1 => bare_one_is_mute f h1,
   fun _ _ f he h3 => bare_three_is_mute f he h3,
   fun _ _ => moves_iff_two,
   two_speaks,
   one_candidate,
   constants_not_structureless,
   id_says_nothing,
   id_graph_says_nothing,
   fun _ hD => diagonal_uniform hD,
   fun _ hD hA => absolute_articulation hD hA,
   no_static_instance,
   no_fixpoint,
   no_being,
   fun seed =>
     ⟨becoming_exists not seed,
      fun x hx h0 => becoming_unique not x hx seed h0,
      two_tick_clock seed⟩,
   refusal_is_running not,
   seed_is_relabel,
   fun _ h tok hd => discrimination h tok hd,
   fun _ _ m x hx => marked_three_moves m x hx,
   fun _ _ m f hf h2 => ⟨mark_is_fixed m f hf h2, mark_orbit_still m f hf h2⟩,
   two_moves_the_mark,
   fun _ _ m => ⟨mark_moves_iff_two m, marked_refuses_iff_two m⟩⟩

end Becoming

#print axioms Becoming.retorsion
#print axioms Becoming.no_undrawn_denial
#print axioms Becoming.bare_one_is_mute
#print axioms Becoming.bare_three_is_mute
#print axioms Becoming.two_at_most
#print axioms Becoming.two_swaps
#print axioms Becoming.moves_iff_two
#print axioms Becoming.two_speaks
#print axioms Becoming.one_candidate
#print axioms Becoming.constants_not_structureless
#print axioms Becoming.id_says_nothing
#print axioms Becoming.id_structureless
#print axioms Becoming.id_graph_says_nothing
#print axioms Becoming.transp_true_false
#print axioms Becoming.transp_false_true
#print axioms Becoming.equivariant_iff_structureless
#print axioms Becoming.third_value_stills
#print axioms Becoming.three_gives_third
#print axioms Becoming.three_values_are_still
#print axioms Becoming.diagonal_uniform
#print axioms Becoming.invariant_binary_classified
#print axioms Becoming.defble_decidable
#print axioms Becoming.defble_classified
#print axioms Becoming.invariant_extends_defble
#print axioms Becoming.defble_extends_invariant
#print axioms Becoming.no_static_instance
#print axioms Becoming.no_being
#print axioms Becoming.no_being_eq
#print axioms Becoming.no_fixpoint
#print axioms Becoming.ne_eq_not
#print axioms Becoming.becoming_exists
#print axioms Becoming.becoming_unique
#print axioms Becoming.two_tick_clock
#print axioms Becoming.clock_runs
#print axioms Becoming.run_unique
#print axioms Becoming.says_kills_the_object
#print axioms Becoming.absolute_law
#print axioms Becoming.absolute_articulation
#print axioms Becoming.absolute_is_inhabited
#print axioms Becoming.refusal_is_running
#print axioms Becoming.seed_is_relabel
#print axioms Becoming.event_retorsion
#print axioms Becoming.discrimination
#print axioms Becoming.marked_three_moves
#print axioms Becoming.mark_is_fixed
#print axioms Becoming.two_moves_the_mark
#print axioms Becoming.mark_orbit_still
#print axioms Becoming.marked_two_at_most
#print axioms Becoming.two_swaps_marked
#print axioms Becoming.mark_moves_iff_two
#print axioms Becoming.marked_refuses_iff_two
#print axioms Becoming.ontological_argument
