/-!
# Instantiation

`W` a class of admissible worlds. Over a *generated* class — one
world, given by evaluating a known law from a known seed — nothing
is free, every proposition is forced or refuted, and every
proposition is expressible in every vocabulary.

Axiom footprint: `freedom_needs_width`, `generated_no_freedom`,
`no_seam_when_generated` none; `run_class_generated` within
`[Quot.sound]`; `generated_dichotomy` and `map_is_territory` within
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Instantiation

variable {W : Type u} {Obs : Type v}

def Forced (P : W → Prop) : Prop := ∀ w, P w

def Refuted (P : W → Prop) : Prop := ∀ w, ¬ P w

def Free (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

def Expressible (v : W → Obs) (P : W → Prop) : Prop :=
  ∃ q : Obs → Prop, ∀ w, P w ↔ q (v w)

/-- A free proposition yields two distinct worlds. -/
theorem freedom_needs_width (P : W → Prop) (h : Free P) :
    ∃ w₁ w₂ : W, w₁ ≠ w₂ := by
  match h with
  | ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩ =>
    exact ⟨w₁, w₂, fun he => h₂ (he ▸ h₁)⟩

theorem generated_no_freedom (point : ∀ w w' : W, w = w')
    (P : W → Prop) : ¬ Free P := by
  intro h
  match freedom_needs_width P h with
  | ⟨w₁, w₂, hne⟩ => exact hne (point w₁ w₂)

theorem generated_dichotomy (w₀ : W) (point : ∀ w : W, w = w₀)
    (P : W → Prop) : Forced P ∨ Refuted P := by
  cases Classical.em (P w₀) with
  | inl hp =>
      exact Or.inl (by intro w; rw [point w]; exact hp)
  | inr hn =>
      exact Or.inr (by intro w hw; rw [point w] at hw; exact hn hw)

theorem no_seam_when_generated (w₀ : W) (point : ∀ w : W, w = w₀)
    (v : W → Obs) (P : W → Prop) : Expressible v P := by
  refine ⟨fun _ => P w₀, ?_⟩
  intro w
  rw [point w]

variable {A : Type u}

def run (f : A → A) (s : A) : Nat → A
  | 0 => s
  | n + 1 => f (run f s n)

/-- Worlds compatible with a known law and a known seed. -/
def RunClass (f : A → A) (s : A) : Type u :=
  {g : Nat → A // g 0 = s ∧ ∀ n, g (n + 1) = f (g n)}

def canonical (f : A → A) (s : A) : RunClass f s :=
  ⟨run f s, rfl, fun _ => rfl⟩

/-- The run class is one world. -/
theorem run_class_generated (f : A → A) (s : A) :
    ∀ w w' : RunClass f s, w = w' := by
  intro w w'
  apply Subtype.ext
  funext n
  induction n with
  | zero => rw [w.2.1, w'.2.1]
  | succ n ih => rw [w.2.2 n, w'.2.2 n, ih]

theorem map_is_territory (f : A → A) (s : A) :
    (∀ P : RunClass f s → Prop, ¬ Free P)
    ∧ (∀ (v : RunClass f s → Obs) (P : RunClass f s → Prop),
        Expressible v P)
    ∧ (∀ P : RunClass f s → Prop, Forced P ∨ Refuted P) :=
  have point : ∀ w : RunClass f s, w = canonical f s :=
    fun w => run_class_generated f s w (canonical f s)
  ⟨fun P =>
      generated_no_freedom
        (fun w w' => (point w).trans (point w').symm) P,
   fun v P => no_seam_when_generated (canonical f s) point v P,
   fun P => generated_dichotomy (canonical f s) point P⟩

end Instantiation

#print axioms Instantiation.freedom_needs_width
#print axioms Instantiation.generated_no_freedom
#print axioms Instantiation.generated_dichotomy
#print axioms Instantiation.no_seam_when_generated
#print axioms Instantiation.run_class_generated
#print axioms Instantiation.map_is_territory
