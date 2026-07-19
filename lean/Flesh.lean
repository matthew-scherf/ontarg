/-!
# Flesh

A class is richer than a point iff some proposition over it is free
(`Free P := (∃ w, P w) ∧ (∃ w, ¬P w)`). Then a coupled pair of the
ground shape (`dstep`) on `Bool × Bool`, equivariant and restless,
with period four; the uncoupled pair (`solo`) has period two; and a
three-locus ring (`ring3`) with period six.
-/

namespace Flesh

variable {W : Type u}

def Free (P : W → Prop) : Prop := (∃ w, P w) ∧ (∃ w, ¬ P w)

theorem freedom_gives_width (P : W → Prop) (h : Free P) :
    ∃ w₁ w₂ : W, w₁ ≠ w₂ := by
  obtain ⟨⟨w₁, h₁⟩, ⟨w₂, h₂⟩⟩ := h
  exact ⟨w₁, w₂, fun he => h₂ (he ▸ h₁)⟩

theorem width_gives_freedom {w₁ w₂ : W} (hne : w₁ ≠ w₂) :
    ∃ P : W → Prop, Free P :=
  ⟨fun w => w = w₁, ⟨w₁, rfl⟩, ⟨w₂, fun h => hne h.symm⟩⟩

theorem richness_iff_records :
    (∃ w₁ w₂ : W, w₁ ≠ w₂) ↔ (∃ P : W → Prop, Free P) := by
  constructor
  · intro ⟨_, _, hne⟩
    exact width_gives_freedom hne
  · intro ⟨P, hP⟩
    exact freedom_gives_width P hP

theorem point_has_no_flesh (point : ∀ w w' : W, w = w')
    (P : W → Prop) : ¬ Free P := by
  intro h
  obtain ⟨w₁, w₂, hne⟩ := freedom_gives_width P h
  exact hne (point w₁ w₂)

/-- Global relabeling of the doubled carrier. -/
def flip (p : Bool × Bool) : Bool × Bool := (!p.1, !p.2)

/-- Coupled pair: each cell is the other's outside. -/
def dstep (p : Bool × Bool) : Bool × Bool := (p.2, !p.1)

/-- Uncoupled pair: two independent clocks. -/
def solo (p : Bool × Bool) : Bool × Bool := (!p.1, !p.2)

def orbit {S : Type} (f : S → S) (seed : S) : Nat → S
  | 0 => seed
  | n + 1 => f (orbit f seed n)

theorem dyad_equivariant : ∀ p, dstep (flip p) = flip (dstep p) := by
  intro p
  obtain ⟨a, b⟩ := p
  rfl

theorem dyad_no_fixpoint : ∀ p, dstep p ≠ p := by
  intro p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> decide

theorem dyad_moves (p : Bool × Bool) :
    ∀ n, orbit dstep p (n + 1) ≠ orbit dstep p n :=
  fun n => dyad_no_fixpoint (orbit dstep p n)

theorem dyad_square_is_flip : ∀ p, dstep (dstep p) = flip p := by
  intro p
  obtain ⟨a, b⟩ := p
  rfl

theorem dyad_period_four (p : Bool × Bool) :
    ∀ n, orbit dstep p (n + 4) = orbit dstep p n := by
  intro n
  show dstep (dstep (dstep (dstep (orbit dstep p n))))
      = orbit dstep p n
  generalize orbit dstep p n = q
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> rfl

theorem dyad_outruns_the_clock (p : Bool × Bool) :
    ∀ n, orbit dstep p (n + 2) ≠ orbit dstep p n := by
  intro n
  show dstep (dstep (orbit dstep p n)) ≠ orbit dstep p n
  generalize orbit dstep p n = q
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> decide

theorem dyad_visits_every_state (p q : Bool × Bool) :
    q = orbit dstep p 0 ∨ q = orbit dstep p 1
    ∨ q = orbit dstep p 2 ∨ q = orbit dstep p 3 := by
  show q = p ∨ q = dstep p ∨ q = dstep (dstep p)
      ∨ q = dstep (dstep (dstep p))
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem solo_equivariant : ∀ p, solo (flip p) = flip (solo p) := by
  intro p
  obtain ⟨a, b⟩ := p
  rfl

theorem solo_no_fixpoint : ∀ p, solo p ≠ p := by
  intro p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> decide

theorem solo_period_two (p : Bool × Bool) :
    ∀ n, orbit solo p (n + 2) = orbit solo p n := by
  intro n
  show solo (solo (orbit solo p n)) = orbit solo p n
  generalize orbit solo p n = q
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> rfl

theorem the_coupling_is_a_record :
    (∀ p, dstep (flip p) = flip (dstep p)) ∧ (∀ p, dstep p ≠ p)
    ∧ (∀ p, solo (flip p) = flip (solo p)) ∧ (∀ p, solo p ≠ p)
    ∧ (∃ p, dstep p ≠ solo p) :=
  ⟨dyad_equivariant, dyad_no_fixpoint, solo_equivariant,
   solo_no_fixpoint, ⟨(false, false), by decide⟩⟩

/-- Three loci, one twist. -/
def ring3 (p : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (p.2.1, p.2.2, !p.1)

theorem ring_three_no_fixpoint : ∀ p, ring3 p ≠ p := by
  intro p
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> decide

theorem ring_three_period_six :
    orbit ring3 (false, false, false) 6 = (false, false, false)
    ∧ orbit ring3 (false, false, false) 1 ≠ (false, false, false)
    ∧ orbit ring3 (false, false, false) 2 ≠ (false, false, false)
    ∧ orbit ring3 (false, false, false) 3 ≠ (false, false, false) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

end Flesh

#print axioms Flesh.freedom_gives_width
#print axioms Flesh.width_gives_freedom
#print axioms Flesh.richness_iff_records
#print axioms Flesh.point_has_no_flesh
#print axioms Flesh.dyad_equivariant
#print axioms Flesh.dyad_no_fixpoint
#print axioms Flesh.dyad_moves
#print axioms Flesh.dyad_square_is_flip
#print axioms Flesh.dyad_period_four
#print axioms Flesh.dyad_outruns_the_clock
#print axioms Flesh.dyad_visits_every_state
#print axioms Flesh.solo_period_two
#print axioms Flesh.the_coupling_is_a_record
#print axioms Flesh.ring_three_no_fixpoint
#print axioms Flesh.ring_three_period_six
