/-!
# Eternal

Drops `Regress.lean`'s well-foundedness hypothesis `wf`. Without it,
`answered` alone still yields a dichotomy: unseeded ground, or an
unending demand chain. On `Bool` with law = negation, the chain is
the clock (`Loeb.godel_is_clock`).

Axiom footprint: `regress_dichotomy` within `[propext, Classical.choice,
Quot.sound]`; everything else, including `eternal_shape`, none.
-/

namespace Eternal

variable {S : Type}

inductive Desc (dem : S → S → Prop) : S → S → Prop
  | refl (s : S) : Desc dem s s
  | head {s g a : S} : dem g s → Desc dem a g → Desc dem a s

/-- Extend a descent at the bottom. -/
theorem Desc.snoc {dem : S → S → Prop} {a s : S} :
    Desc dem a s → ∀ {b}, dem b a → Desc dem b s := by
  intro h
  induction h with
  | refl s => intro b hb; exact Desc.head hb (Desc.refl b)
  | head h1 _ ih => intro b hb; exact Desc.head h1 (ih hb)

def iter {A : Type} (f : A → A) : Nat → A → A
  | 0,     a => a
  | n + 1, a => f (iter f n a)

/-- Every specification either descends to an unseeded ground, or
    generates an unending demand chain. -/
theorem regress_dichotomy (Seeded : S → Prop) (dem : S → S → Prop)
    (answered : ∀ s, Seeded s → ∃ g, dem g s) (s : S) :
    (∃ g, Desc dem g s ∧ ¬ Seeded g)
    ∨ (∃ chain : Nat → S, chain 0 = s ∧ ∀ n, dem (chain (n + 1)) (chain n)) := by
  refine Classical.byCases (fun h : ∃ g, Desc dem g s ∧ ¬ Seeded g => Or.inl h)
    (fun h => Or.inr ?_)
  have hall : ∀ g, Desc dem g s → Seeded g := by
    intro g hg
    refine Classical.byCases (fun hs : Seeded g => hs)
      (fun hns => absurd ⟨g, hg, hns⟩ h)
  have hstep : ∀ x : {g : S // Desc dem g s},
      ∃ y : {g : S // Desc dem g s}, dem y.1 x.1 := by
    intro x
    match answered x.1 (hall x.1 x.2) with
    | ⟨g, hg⟩ => exact ⟨⟨g, Desc.snoc x.2 hg⟩, hg⟩
  let f : {g : S // Desc dem g s} → {g : S // Desc dem g s} :=
    fun x => Classical.choose (hstep x)
  have hf : ∀ x, dem (f x).1 x.1 := fun x => Classical.choose_spec (hstep x)
  exact ⟨fun n => (iter f n ⟨s, Desc.refl s⟩).1, rfl,
         fun n => hf (iter f n ⟨s, Desc.refl s⟩)⟩

/-- The alternating clock. -/
def alt : Nat → Bool
  | 0     => true
  | n + 1 => !(alt n)

/-- Self-loop: every specification demands itself. -/
def loop (g s : Bool) : Prop := g = s
/-- Two-cycle: every specification demands its negation. -/
def cyc (g s : Bool) : Prop := g = !s

/-- No infinite descending chain. -/
def WellFounded' {S : Type} (dem : S → S → Prop) : Prop :=
  ∀ f : Nat → S, ¬ ∀ n, dem (f (n + 1)) (f n)

theorem both_answered :
    (∀ s, ∃ g, loop g s) ∧ (∀ s, ∃ g, cyc g s) :=
  ⟨fun s => ⟨s, rfl⟩, fun s => ⟨!s, rfl⟩⟩

theorem cyc_not_wf : ¬ WellFounded' cyc :=
  fun wf => wf alt (fun _ => rfl)

theorem loop_not_wf : ¬ WellFounded' loop :=
  fun wf => wf (fun _ => true) (fun _ => rfl)

theorem wf_excludes_both : ¬ WellFounded' loop ∧ ¬ WellFounded' cyc :=
  ⟨loop_not_wf, cyc_not_wf⟩

theorem cyc_chain_is_clock : ∀ n, cyc (alt (n + 1)) (alt n) :=
  fun _ => rfl

theorem loop_chain_constant :
    ∀ n, loop ((fun _ => true) (n + 1)) ((fun _ => true) n) :=
  fun _ => rfl

/-- Each specification demands exactly one ground, named by a law. -/
def Functional (dem : Bool → Bool → Prop) (law : Bool → Bool) : Prop :=
  ∀ g s, dem g s ↔ g = law s

def Equivariant (h : Bool → Bool) : Prop := ∀ b, h (!b) = !(h b)

theorem equivariant_id_or_not (h : Bool → Bool) (he : Equivariant h) :
    (∀ b, h b = b) ∨ (∀ b, h b = !b) := by
  cases htrue : h true with
  | true =>
    left; intro b; cases b with
    | true  => exact htrue
    | false => have hf := he true; rw [htrue] at hf; exact hf
  | false =>
    right; intro b; cases b with
    | true  => exact htrue
    | false => have hf := he true; rw [htrue] at hf; exact hf

/-- Without `wf`: `structureless` and `generative` on the demand
    relation itself force the law to be negation, its chain to be the
    clock, and rule out any static resting point. -/
theorem eternal_shape (dem : Bool → Bool → Prop) (law : Bool → Bool)
    (func : Functional dem law)
    (structureless : Equivariant law)
    (generative : ∃ b, law b ≠ b) :
    (∀ b, law b = !b)
    ∧ (∀ n, dem (alt (n + 1)) (alt n))
    ∧ (¬ ∃ b, law b = b) := by
  have hneg : ∀ b, law b = !b := by
    match equivariant_id_or_not law structureless with
    | Or.inl hid =>
      match generative with
      | ⟨b, hb⟩ => exact absurd (hid b) hb
    | Or.inr hn => exact hn
  refine ⟨hneg, ?_, ?_⟩
  · intro n
    exact (func (alt (n + 1)) (alt n)).mpr (by rw [hneg]; rfl)
  · intro ⟨b, hb⟩
    rw [hneg b] at hb
    cases b <;> exact Bool.noConfusion hb

theorem eternal_fork :
    (∀ n, loop ((fun _ => true) (n + 1)) ((fun _ => true) n))
    ∧ (∀ n, cyc (alt (n + 1)) (alt n))
    ∧ (¬ WellFounded' loop ∧ ¬ WellFounded' cyc) :=
  ⟨loop_chain_constant, cyc_chain_is_clock, wf_excludes_both⟩

end Eternal

#print axioms Eternal.regress_dichotomy
#print axioms Eternal.cyc_not_wf
#print axioms Eternal.wf_excludes_both
#print axioms Eternal.cyc_chain_is_clock
#print axioms Eternal.eternal_shape
#print axioms Eternal.eternal_fork
