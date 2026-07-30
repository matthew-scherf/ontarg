/-!
# Cut

Process-first absolute: the absolute is the cut, and the cut is `not`.

Stance (named, not proved): “absolute” / “cut” denotes the unique structureless
excluding law on the forced two-valued arena — Boolean complement. Among other
things it is self-dual (`Structureless`), involutive, and fixed-point-free; its
only realization is a run.

World / Still / Claim structure is not denied: it is non-absolute
(see `Obstruction.lean` and `paper/undeniability.tex`). This file packages the
positive half only.

Standalone Lean 4; prelude only; no imports; no axioms.
-/

namespace Cut

/-! ## Self-duality = structurelessness on `Bool` -/

/-- Unary self-duality: `g` intertwines with complement.
    On `Bool` this is the standard self-duality equation for a unary operation,
    and coincides with `Becoming.Structureless`. -/
def SelfDual (g : Bool → Bool) : Prop := ∀ b, g (!b) = !(g b)

/-- Alias used in the companion `Becoming` development. -/
def Structureless (g : Bool → Bool) : Prop := SelfDual g

theorem not_selfDual : SelfDual not := fun _ => rfl

theorem id_selfDual : SelfDual id := fun _ => rfl

theorem constants_not_selfDual (c : Bool) : ¬ SelfDual (fun _ => c) := by
  intro h
  have hc := h true
  revert hc
  cases c <;> decide

/-- A self-dual unary `Bool` map is identity or complement. -/
theorem selfDual_dichotomy (g : Bool → Bool) (h : SelfDual g) :
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

/-! ## The absolute cut is `not` -/

/-- The cut: Boolean complement. -/
def absolute : Bool → Bool := not

theorem absolute_eq_not : absolute = not := rfl

theorem absolute_selfDual : SelfDual absolute := not_selfDual

/-- Involution / period-2 generator. -/
theorem absolute_involutive : ∀ b, absolute (absolute b) = b := by
  intro b; cases b <;> decide

/-- No static fixed point: the cut refuses being. -/
theorem absolute_no_fixpoint : ∀ b, absolute b ≠ b := by
  intro b; cases b <;> decide

/-- Among self-dual laws, only complement excludes every diagonal. -/
theorem absolute_unique_excluding (g : Bool → Bool) (h : SelfDual g)
    (hex : ∀ b, g b ≠ b) : ∀ b, g b = absolute b := by
  cases selfDual_dichotomy g h with
  | inl hid =>
    exact absurd (hid true) (hex true)
  | inr hnot =>
    exact hnot

/-- Identity is self-dual but excludes nothing. -/
theorem id_excludes_nothing : ∀ b : Bool, id b = b := fun _ => rfl

/-! ## Process realization -/

/-- Recursion solution. -/
def Solves (f : Bool → Bool) (x : Nat → Bool) : Prop :=
  ∀ n, x (n + 1) = f (x n)

/-- Orbit of `f` from `seed`. -/
def orbit (f : Bool → Bool) (seed : Bool) : Nat → Bool
  | 0     => seed
  | n + 1 => f (orbit f seed n)

/-- An absolute model: a run of the cut. -/
def AbsoluteModel (x : Nat → Bool) : Prop :=
  Solves absolute x ∧ ∀ n, x (n + 1) ≠ x n

theorem orbit_solves (seed : Bool) :
    Solves absolute (orbit absolute seed) ∧
      orbit absolute seed 0 = seed :=
  ⟨fun _ => rfl, rfl⟩

theorem orbit_runs (seed : Bool) :
    ∀ n, orbit absolute seed (n + 1) ≠ orbit absolute seed n :=
  fun n => absolute_no_fixpoint (orbit absolute seed n)

theorem absoluteModel_orbit (seed : Bool) :
    AbsoluteModel (orbit absolute seed) :=
  ⟨(orbit_solves seed).1, orbit_runs seed⟩

theorem absoluteModel_unique {x : Nat → Bool} (hx : AbsoluteModel x)
    (seed : Bool) (h0 : x 0 = seed) :
    ∀ n, x n = orbit absolute seed n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
    have hs := hx.1 k
    rw [hs, ih]
    rfl

/-- Period two. -/
theorem absolute_period_two (seed : Bool) :
    ∀ n, orbit absolute seed (n + 2) = orbit absolute seed n := by
  intro n
  show absolute (absolute (orbit absolute seed n)) = orbit absolute seed n
  exact absolute_involutive (orbit absolute seed n)

/-- Pointwise complement of a sequence. -/
def relabel (s : Nat → Bool) : Nat → Bool := fun n => absolute (s n)

theorem seeds_are_relabelings :
    ∀ n, orbit absolute false n = relabel (orbit absolute true) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show absolute (orbit absolute false n) =
      absolute (orbit absolute true (n + 1))
    rw [ih]
    rfl

/-- No static absolute: a constant sequence is never an `AbsoluteModel`. -/
theorem no_static_absoluteModel (b : Bool) :
    ¬ AbsoluteModel (fun _ => b) := by
  intro ⟨_, hrun⟩
  exact hrun 0 rfl

/-- Fixed-point freeness of the cut iff every orbit runs. -/
theorem refusal_iff_running :
    (∀ b, absolute b ≠ b) ↔
      ∀ seed n, orbit absolute seed (n + 1) ≠ orbit absolute seed n := by
  constructor
  · intro h seed n
    exact h (orbit absolute seed n)
  · intro h b
    exact h b 0

/-! ## Still is not absolute -/

/-- A tensed foil: succession on an underlying carrier. -/
structure Tensed where
  T : Type
  succ : T → T → Prop

def Still (s : Tensed) : Prop := ∀ t t' : s.T, ¬ s.succ t t'

/-- Stillness is incompatible with any successive step — hence with any
    absolute run read as successive ticks on loci. Thin negative lemma:
    absolute models are process sequences, not still tensed structures. -/
theorem still_has_no_step (s : Tensed) (hs : Still s) (t t' : s.T) :
    ¬ s.succ t t' :=
  hs t t'

/-- Absolute models exist; still structures are a different kind. -/
theorem absolute_realized :
    (∃ x, AbsoluteModel x) ∧
      (∃ s : Tensed, Still s) :=
  ⟨⟨orbit absolute true, absoluteModel_orbit true⟩,
   ⟨⟨Unit, fun _ _ => False⟩, fun _ _ h => h⟩⟩

/-! ## Summary: process-first absolute package -/

/-- Positive half of the cut OA (empty of succession-from-claims).
    Identification “absolute := cut := `not`” is the named stance of this file. -/
theorem absolute_as_cut :
    -- the cut is complement
    (absolute = not)
    -- self-dual / structureless
    ∧ SelfDual absolute
    -- involutive
    ∧ (∀ b, absolute (absolute b) = b)
    -- no being
    ∧ (∀ b, absolute b ≠ b)
    ∧ (∀ X : Prop, (X ↔ ¬ X) → False)
    -- unique self-dual excluder
    ∧ (∀ g, SelfDual g → (∀ b, g b ≠ b) → ∀ b, g b = absolute b)
    -- process realization
    ∧ (∀ seed, AbsoluteModel (orbit absolute seed))
    ∧ (∀ seed, ∀ n, orbit absolute seed (n + 2) = orbit absolute seed n)
    ∧ (∀ n, orbit absolute false n = relabel (orbit absolute true) n)
    -- no static absolute model
    ∧ (∀ b, ¬ AbsoluteModel (fun _ => b))
    -- refusal ↔ running
    ∧ ((∀ b, absolute b ≠ b) ↔
        ∀ seed n, orbit absolute seed (n + 1) ≠ orbit absolute seed n)
    -- absolute and still both inhabit their kinds; still ≠ absolute package
    ∧ (∃ x, AbsoluteModel x)
    ∧ (∃ s : Tensed, Still s) := by
  refine ⟨rfl, absolute_selfDual, absolute_involutive, absolute_no_fixpoint, ?_,
    absolute_unique_excluding, absoluteModel_orbit, absolute_period_two,
    seeds_are_relabelings, no_static_absoluteModel, refusal_iff_running,
    absolute_realized.1, absolute_realized.2⟩
  intro X h
  have hn : ¬ X := fun hx => h.mp hx hx
  exact hn (h.mpr hn)

/-- Propositional unsatisfiability of the static equation, re-exported. -/
theorem no_being (X : Prop) (h : X ↔ ¬ X) : False :=
  (absolute_as_cut).2.2.2.2.1 X h

end Cut

/- Axiom audit -/
#print axioms Cut.not_selfDual
#print axioms Cut.selfDual_dichotomy
#print axioms Cut.absolute_selfDual
#print axioms Cut.absolute_involutive
#print axioms Cut.absolute_no_fixpoint
#print axioms Cut.absolute_unique_excluding
#print axioms Cut.absoluteModel_orbit
#print axioms Cut.absoluteModel_unique
#print axioms Cut.absolute_period_two
#print axioms Cut.seeds_are_relabelings
#print axioms Cut.no_static_absoluteModel
#print axioms Cut.refusal_iff_running
#print axioms Cut.absolute_realized
#print axioms Cut.absolute_as_cut
#print axioms Cut.no_being
