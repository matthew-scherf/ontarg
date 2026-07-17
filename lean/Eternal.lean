/-!
# Eternal

The regress without well-foundedness: it does not bottom out, it closes
into the clock.

`Regress.lean` reaches its ground from four hypotheses: `answered`, `wf`,
`structureless`, `generative`. The last two are about the law and are
discharged in `Articulation.lean` (`non_equivariant_names`,
`generativity_is_saying_something`). This file takes the other two.

What `wf` says is that the demand relation has no infinite descending
chain. What that excludes, exactly, is a demand chain that runs forever.
The corpus's conclusion is that the ground runs forever. The hypothesis
and the conclusion are in tension, and this file measures it and then
removes the hypothesis.

Main results:
* `regress_dichotomy` — without `wf`, `answered` alone still decides:
  every specification either descends to an unseeded ground, or generates
  an unending chain. The second branch is a run, not a failure.
  `Regress.regress_terminates` is this theorem with the second branch
  assumed away.
* `cyc_not_wf` / `loop_not_wf` / `wf_excludes_both` — the two eternal
  structures on the bare distinction are the self-loop and the two-cycle,
  and `wf` excludes both. Read `cyc_not_wf`'s proof: the chain that
  refutes well-foundedness is `alt`, the alternation. `wf` does not
  exclude a pathology near the clock. It excludes the clock, by name, as
  its own counterexample — and it takes out the contentless loop and
  the generative cycle with equal force, so it cannot tell them apart. It
  is not a filter on content; it is a filter on running at all.
* `cyc_chain_is_clock` — the two-cycle's descending chain is the
  alternation, tick for tick.
* `eternal_shape` — the main result. Drop `wf`. Apply `structureless` and
  `generative` to the demand relation itself rather than to a terminus
  that `wf` was needed to reach. The law is still negation, its chain is
  still the clock, and there is no static resting point anywhere on it.
  Axiom-free, where `Regress.regress_terminates` needs
  `Classical.choice`.

So `wf` is not load-bearing for the conclusion. It is load-bearing only
for the *terminus reading* of it — the route that posits an unseeded
terminus and reaches it by a step that cannot be run. Drop it and
`x = ¬x` arrives anyway, constructively, as the shape of a grounding
chain that closes into a cycle instead of bottoming out on an
unexplained unseeded floor.

The defence against the viciousness charge is `wf_excludes_both`: a
hypothesis that cannot distinguish the contentless loop from the
generative cycle was never tracking explanatory adequacy. It was
tracking termination. Grounding here is coherentist, not
foundationalist.

The cost is generality: `eternal_shape` lives on `Bool`. By
`Arena.speaks_needs_exactly_two` that is not a restriction — `Bool` is
the only carrier on which a structureless law moves anything.

Lean 4, prelude only; no imports. Axiom footprint: `regress_dichotomy`
within `[propext, Classical.choice, Quot.sound]` (the same footprint as
`Regress.regress_terminates`, which it generalizes); everything else,
including `eternal_shape`, uses none.
-/

namespace Eternal

variable {S : Type}

/- ---------- descent, as in Regress ---------- -/

inductive Desc (dem : S → S → Prop) : S → S → Prop
  | refl (s : S) : Desc dem s s
  | head {s g a : S} : dem g s → Desc dem a g → Desc dem a s

/-- Extend a descent at the bottom. `Regress` only ever extends at the
    head; following a chain downward forever needs this direction. -/
theorem Desc.snoc {dem : S → S → Prop} {a s : S} :
    Desc dem a s → ∀ {b}, dem b a → Desc dem b s := by
  intro h
  induction h with
  | refl s => intro b hb; exact Desc.head hb (Desc.refl b)
  | head h1 _ ih => intro b hb; exact Desc.head h1 (ih hb)

def iter {A : Type} (f : A → A) : Nat → A → A
  | 0,     a => a
  | n + 1, a => f (iter f n a)

/- ---------- the dichotomy ---------- -/

/-- Without `wf`, `answered` alone still decides the question — into two
    branches rather than one. Every specification either descends to an
    unseeded ground, or generates an unending demand chain.

    `Regress.regress_terminates` is this theorem with the second branch
    assumed away. The second branch is not the absence of a ground; it is
    a run. -/
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

/- ---------- what wf actually excludes ---------- -/

/-- The alternating clock: `Loeb.godel_is_clock`'s unique solution. -/
def alt : Nat → Bool
  | 0     => true
  | n + 1 => !(alt n)

/-- The self-loop: every specification demands itself. -/
def loop (g s : Bool) : Prop := g = s
/-- The two-cycle: every specification demands its negation. -/
def cyc (g s : Bool) : Prop := g = !s

/-- No infinite descending chain — `Regress`'s `wf`, in order form. -/
def WellFounded' {S : Type} (dem : S → S → Prop) : Prop :=
  ∀ f : Nat → S, ¬ ∀ n, dem (f (n + 1)) (f n)

/-- Both eternal structures are answered everywhere, so both run forever,
    and neither has an unseeded ground. -/
theorem both_answered :
    (∀ s, ∃ g, loop g s) ∧ (∀ s, ∃ g, cyc g s) :=
  ⟨fun s => ⟨s, rfl⟩, fun s => ⟨!s, rfl⟩⟩

/-- The two-cycle is not well-founded, and the chain that refutes
    well-foundedness is the clock itself. `wf` does not merely exclude
    some pathology — it excludes this object by name. -/
theorem cyc_not_wf : ¬ WellFounded' cyc :=
  fun wf => wf alt (fun _ => rfl)

/-- The self-loop is not well-founded either; its chain is constant. -/
theorem loop_not_wf : ¬ WellFounded' loop :=
  fun wf => wf (fun _ => true) (fun _ => rfl)

/-- `wf` excludes both eternal structures at once — the contentless loop
    and the generative cycle alike. It cannot tell them apart. It is not a
    filter on content; it is a filter on running at all. -/
theorem wf_excludes_both : ¬ WellFounded' loop ∧ ¬ WellFounded' cyc :=
  ⟨loop_not_wf, cyc_not_wf⟩

/-- The two-cycle's descending chain is the alternation, tick for tick. -/
theorem cyc_chain_is_clock : ∀ n, cyc (alt (n + 1)) (alt n) :=
  fun _ => rfl

/-- The self-loop's chain is constant: it runs forever and nothing
    happens. `OnlyShape.id_generates_nothing`, wearing a chain. -/
theorem loop_chain_constant :
    ∀ n, loop ((fun _ => true) (n + 1)) ((fun _ => true) n) :=
  fun _ => rfl

/- ---------- the shape, without wf ---------- -/

/-- A functional demand: each specification demands exactly one ground,
    named by a law. -/
def Functional (dem : Bool → Bool → Prop) (law : Bool → Bool) : Prop :=
  ∀ g s, dem g s ↔ g = law s

/-- Structurelessness on the bare distinction (`Regress.Equivariant`). -/
def Equivariant (h : Bool → Bool) : Prop := ∀ b, h (!b) = !(h b)

/-- `Regress.equivariant_id_or_not`, re-proved locally. -/
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

/-- The shape survives the loss of `wf`.

    Drop well-foundedness entirely. Keep `structureless` and `generative`,
    now applied to the demand relation itself rather than to a terminus
    that well-foundedness was needed to reach. The law is still negation;
    the chain it generates is still the clock; and there is no static
    resting point anywhere on it.

    The regress does not bottom out. It closes into `x = ¬x`.

    Note the axiom footprint: none. `Regress.regress_terminates` needs
    `Classical.choice` to reach its ground. This route needs nothing. -/
theorem eternal_shape (dem : Bool → Bool → Prop) (law : Bool → Bool)
    (func : Functional dem law)
    (structureless : Equivariant law)
    (generative : ∃ b, law b ≠ b) :
    (∀ b, law b = !b)                        -- the law is negation
    ∧ (∀ n, dem (alt (n + 1)) (alt n))       -- its chain is the clock
    ∧ (¬ ∃ b, law b = b) := by               -- with no static resting point
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

/-- The fork, restated on the eternal branch. `Regress` excludes the
    contentless law by `generative` and reaches negation at a terminus.
    Here the same exclusion runs on the same classification, and reaches
    negation as a cycle: the self-loop runs forever and generates nothing;
    the two-cycle runs forever and is the clock. Same classification, same
    exclusion, no well-foundedness, no terminus, no axioms. -/
theorem eternal_fork :
    (∀ n, loop ((fun _ => true) (n + 1)) ((fun _ => true) n))
    ∧ (∀ n, cyc (alt (n + 1)) (alt n))
    ∧ (¬ WellFounded' loop ∧ ¬ WellFounded' cyc) :=
  ⟨loop_chain_constant, cyc_chain_is_clock, wf_excludes_both⟩

end Eternal

/- audit -/
#print axioms Eternal.regress_dichotomy
#print axioms Eternal.cyc_not_wf
#print axioms Eternal.wf_excludes_both
#print axioms Eternal.cyc_chain_is_clock
#print axioms Eternal.eternal_shape
#print axioms Eternal.eternal_fork
