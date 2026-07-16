/-!
# Loeb

Löb's rule over discrete time, and guarded recursion. The `later`
modality over `Nat`; streams over `A`; the guarded map
`z ↦ prepend c (lift f z)`.

Main results:
* `loeb`, `loeb_iff_induction` — `(∀ n, later P n → P n) → ∀ n, P n`,
  interderivable with induction over `Nat`.
* `guard_is_later` — `Agree (n+1) (prepend c x) (prepend c y) ↔ Agree n x y`.
* `unique_by_loeb` — fixed points of contractive maps are unique.
* `deJonghSambin` — every contractive map has exactly one fixed point
  (the de Jongh–Sambin fixed-point shape, in this setting).
* `godel_is_clock` — `z = prepend true (lift not z)` has exactly one
  solution, satisfying `z 0 = true`, `z 1 = false`, `z (n+2) = z n`.

Lean 4, prelude only; no imports. Axiom footprint: within
`[propext, Quot.sound]`.
-/

namespace Loeb

/- ---------- the rule over Nat ---------- -/

/-- The later modality ▷ over discrete time. -/
def later (P : Nat → Prop) : Nat → Prop
  | 0     => True
  | n + 1 => P n

/-- Löb's rule over `Nat`: what follows from its own predecessor
    holds always. -/
theorem loeb {P : Nat → Prop} (h : ∀ n, later P n → P n) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h 0 trivial
  | succ k ih => exact h (k + 1) ih

/-- Löb's rule over Nat and induction over Nat are
    interderivable. -/
theorem loeb_iff_induction :
    (∀ P : Nat → Prop, (∀ n, later P n → P n) → ∀ n, P n)
    ↔ (∀ P : Nat → Prop, P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n) := by
  constructor
  · intro hl P h0 hs
    exact hl P (fun n => match n with
      | 0 => fun _ => h0
      | k + 1 => fun hk => hs k hk)
  · intro hi P h
    exact hi P (h 0 trivial) (fun n hn => h (n + 1) hn)

/- ---------- streams ---------- -/

abbrev Stream (A : Type u) := Nat → A

def tail {A : Type u} (z : Stream A) : Stream A := fun n => z (n + 1)

def prepend {A : Type u} (c : A) (z : Stream A) : Stream A :=
  fun n => if n = 0 then c else z (n - 1)

def lift {A : Type u} (f : A → A) (z : Stream A) : Stream A :=
  fun n => f (z n)

def orbit {A : Type u} (f : A → A) (c : A) : Stream A
  | 0     => c
  | n + 1 => f (orbit f c n)

def Agree {A : Type u} (n : Nat) (x y : Stream A) : Prop :=
  ∀ i, i < n → x i = y i

def Contractive {A : Type u} (Φ : Stream A → Stream A) : Prop :=
  ∀ n x y, Agree n x y → Agree (n + 1) (Φ x) (Φ y)

theorem eq_of_agree_all {A : Type u} {x y : Stream A}
    (h : ∀ n, Agree n x y) : x = y := by
  funext n
  exact h (n + 1) n (Nat.lt_succ_self n)

/- ---------- prepend and later ---------- -/

/-- One application of prepend converts depth-n agreement into
    depth-(n+1) agreement. -/
theorem guard_is_later {A : Type u} (c : A) (x y : Stream A) (n : Nat) :
    Agree (n + 1) (prepend c x) (prepend c y) ↔ Agree n x y := by
  constructor
  · intro h i hi
    have hh := h (i + 1) (by omega)
    have ex : prepend c x (i + 1) = x i := by
      show (if i + 1 = 0 then c else x (i + 1 - 1)) = x i
      rw [if_neg (Nat.succ_ne_zero i)]
      congr 1
    have ey : prepend c y (i + 1) = y i := by
      show (if i + 1 = 0 then c else y (i + 1 - 1)) = y i
      rw [if_neg (Nat.succ_ne_zero i)]
      congr 1
    rw [← ex, ← ey, hh]
  · intro h i hi
    show (if i = 0 then c else x (i - 1)) = (if i = 0 then c else y (i - 1))
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      exact h (i - 1) (by omega)

/-- Fixed points of contractive maps are unique; proved by
    applying loeb with P n := Agree n x y. -/
theorem unique_by_loeb {A : Type u} {Φ : Stream A → Stream A}
    (hΦ : Contractive Φ) {x y : Stream A}
    (hx : Φ x = x) (hy : Φ y = y) : x = y := by
  apply eq_of_agree_all
  refine loeb (P := fun n => Agree n x y) ?_
  intro n hn
  cases n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ k =>
    have hk : Agree k x y := hn
    have := hΦ k x y hk
    rwa [hx, hy] at this

/- ---------- de Jongh–Sambin ---------- -/

def iter {A : Type u} (Φ : Stream A → Stream A) : Nat → Stream A → Stream A
  | 0,     z => z
  | k + 1, z => Φ (iter Φ k z)

theorem iter_shift {A : Type u} (Φ : Stream A → Stream A) (k : Nat)
    (z : Stream A) : iter Φ (k + 1) z = iter Φ k (Φ z) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    show Φ (iter Φ (k + 1) z) = iter Φ (k + 1) (Φ z)
    rw [ih z]
    rfl

theorem iter_add {A : Type u} (Φ : Stream A → Stream A) (a b : Nat)
    (z : Stream A) : iter Φ (a + b) z = iter Φ a (iter Φ b z) := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, iter_shift, ih (Φ z),
        iter_shift]

theorem iter_agree {A : Type u} {Φ : Stream A → Stream A}
    (hΦ : Contractive Φ) (k : Nat) (x y : Stream A) :
    Agree k (iter Φ k x) (iter Φ k y) := by
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih => exact hΦ k _ _ ih

/-- Guarded recursion: the ▷-fixpoint, built digit by digit. -/
def gfix {A : Type u} (Φ : Stream A → Stream A) (z₀ : Stream A) : Stream A :=
  fun n => iter Φ (n + 1) z₀ n

theorem gfix_agree {A : Type u} {Φ : Stream A → Stream A}
    (hΦ : Contractive Φ) (z₀ : Stream A) (n : Nat) :
    Agree n (gfix Φ z₀) (iter Φ n z₀) := by
  intro i hi
  show iter Φ (i + 1) z₀ i = iter Φ n z₀ i
  calc iter Φ (i + 1) z₀ i
      = iter Φ (i + 1) (iter Φ (n - (i + 1)) z₀) i :=
        iter_agree hΦ (i + 1) z₀ (iter Φ (n - (i + 1)) z₀) i
          (Nat.lt_succ_self i)
    _ = iter Φ ((i + 1) + (n - (i + 1))) z₀ i :=
        congrFun (iter_add Φ (i + 1) (n - (i + 1)) z₀).symm i
    _ = iter Φ n z₀ i := by
        rw [show (i + 1) + (n - (i + 1)) = n by omega]

theorem gfix_fixed {A : Type u} {Φ : Stream A → Stream A}
    (hΦ : Contractive Φ) (z₀ : Stream A) : Φ (gfix Φ z₀) = gfix Φ z₀ := by
  funext n
  exact hΦ n _ _ (gfix_agree hΦ z₀ n) n (Nat.lt_succ_self n)

/-- Every contractive Φ has exactly one fixed point: existence
    by gfix, uniqueness by unique_by_loeb. -/
theorem deJonghSambin {A : Type u} [Inhabited A]
    {Φ : Stream A → Stream A} (hΦ : Contractive Φ) :
    ∃ z, Φ z = z ∧ ∀ y, Φ y = y → y = z :=
  ⟨gfix Φ (fun _ => default), gfix_fixed hΦ _,
   fun y hy => unique_by_loeb hΦ hy (gfix_fixed hΦ _)⟩

/- ---------- the guarded liar over Bool ---------- -/

theorem guard_contractive {A : Type u} (f : A → A) (c : A) :
    Contractive (fun z => prepend c (lift f z)) := by
  intro n x y h
  exact (guard_is_later c (lift f x) (lift f y) n).mpr
    (fun i hi => congrArg f (h i hi))

/-- z = prepend true (lift not z) has exactly one solution;
    it satisfies z 0 = true, z 1 = false, z (n+2) = z n. -/
theorem godel_is_clock :
    (∃ z : Stream Bool, prepend true (lift not z) = z
      ∧ ∀ y, prepend true (lift not y) = y → y = z)
    ∧ (∀ z : Stream Bool, prepend true (lift not z) = z →
        z 0 = true ∧ z 1 = false ∧ ∀ n, z (n + 2) = z n) := by
  constructor
  · exact ⟨gfix (fun z => prepend true (lift not z)) (fun _ => true),
      gfix_fixed (guard_contractive not true) _,
      fun y hy => unique_by_loeb (guard_contractive not true) hy
        (gfix_fixed (guard_contractive not true) _)⟩
  · intro z hz
    have h0 : z 0 = true := (congrFun hz 0).symm
    have hs : ∀ n, z (n + 1) = not (z n) :=
      fun n => (congrFun hz (n + 1)).symm
    refine ⟨h0, ?_, ?_⟩
    · rw [hs 0, h0]
      rfl
    · intro n
      rw [hs (n + 1), hs n, Bool.not_not]

end Loeb

/- audit -/
#print axioms Loeb.loeb
#print axioms Loeb.loeb_iff_induction
#print axioms Loeb.guard_is_later
#print axioms Loeb.unique_by_loeb
#print axioms Loeb.deJonghSambin
#print axioms Loeb.godel_is_clock
