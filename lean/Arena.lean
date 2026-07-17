/-!
# Arena

Why two — the premise nobody listed.

Every classification in the corpus, and everything in `Articulation.lean`,
runs on a two-valued arena. Why? If the answer is "because we chose the
bare distinction", then the choice is a premise, and an unlisted one:
the count of values would be an assumption doing load-bearing work.

The threat is concrete. `OnlyShape.lean` also classifies on the
three-element alphabet `V3`, where `neg` fixes a vacuum `b`. There
`x = neg x` *has* a static solution. On that arena becoming is not
forced — it is optional. So the whole result appears to hang on an arena
size that was picked rather than derived.

The answer is that the arena is not picked, and it is settled twice
over: once for laws, once for specifications.

Look again at `OnlyShape.equivariant_endomaps_V3`. Its hypotheses
include `hb : g b = b` — the vacuum is *named*, and the classification
holds only for maps that fix it. Naming an element is importing
structure; it is the one thing a structureless specification may not do
(`Structureless.constants_not_defble`). Drop the name and ask what
survives full symmetry — invariance under *every* relabeling, which is
what "bare" means — and the three-element arena collapses:

* On a bare set with three or more values, the only equivariant
  endomap is the identity (`bare_three_is_mute`). There is no `neg`
  there to solve. `V3`'s negation exists only because `b` was named.
* On a bare set with one value, the only endomap is the identity
  (`bare_one_is_mute`), and no distinction is drawn at all.
* On a bare set with exactly two values, `not` is equivariant and is not
  the identity (`two_speaks`).

So at the level of laws the arena is forced by the same principle as
everything else: import nothing. Two is the unique size at which a
structureless law is not the identity. Three is mute, one is mute; two
speaks.

`Articulation.lean` reads specifications as graphs rather than endomaps,
and at that level the count is settled by determination rather than by
muteness. The inequation is definable from equality alone on any
carrier, and on `V3` it says something and has runs. But two of its
runs share a seed and diverge at the next tick, and no equivariant
endomap realizes it — the only equivariant endomap is the identity,
which satisfies the inequation nowhere. So on three values the
specification underdetermines every tick: each step of any run imports
a choice no structureless law supplies. Only on two values does the
structureless specification determine its own run
(`Articulation.run_unique`). Two is forced from both sides: the only
arena where a structureless law moves anything, and the only arena
where the structureless specification runs of itself.

The proof is one line of group theory made explicit. If `f` moves `x` to
`y ≠ x`, and a third value `z` exists, then the transposition of `y` and
`z` fixes `x` — so equivariance sends `f x` to both `y` and `z`, and
they differ. The third value is exactly what gives the symmetry group
enough room to pin `f x` down to `x`. Two values leave no room, and that
freedom is the whole of the founding law.

Main results:
* `transp_fixes` — a transposition of two values fixes anything unequal
  to both.
* `bare_three_is_mute` — on three or more bare values, every equivariant
  endomap is the identity: nothing structureless can be said.
* `bare_one_is_mute` — on one value, likewise, and no distinction is
  drawn.
* `two_speaks` — on two, `not` is equivariant and moves everything.
* `arena_is_forced` — the conjunction: two is the unique arena of the
  absolute.
* `speaks_needs_exactly_two` — the converse, and the strongest form: if
  *any* structureless law on a bare carrier moves *anything*, the carrier
  has exactly two values. The count is not a premise but a consequence of
  there being an articulation at all.
* `arena_iff_two` — the arena settled from both sides.
* `v3_negation_names_the_vacuum` — and the escape hatch, priced: `V3`'s
  `neg` is not invariant under the transposition that would move `b`.
  The vacuum is a name, and the static solution was bought with it.
* `three_does_not_determine` — the relational side: on `V3` the
  inequation is definable from equality alone and has runs, but two of
  its runs share a seed and diverge, and no equivariant endomap
  realizes it. A structureless specification can speak on three values;
  it cannot run of itself there.

Lean 4, prelude only; no imports. Axiom footprint: axiom-free except
`speaks_needs_exactly_two` and `arena_iff_two`, which are within
`[propext, Classical.choice, Quot.sound]` — the classical step is
pushing a negation through "three or more values" to reach "exactly
two", and nothing else — and `v3_runs_diverge` and
`three_does_not_determine`, within `[propext]`.
-/

namespace Arena

/- ---------- transpositions ---------- -/

/-- The transposition of `a` and `b`: the simplest relabeling there is. -/
def transp {V : Type u} [DecidableEq V] (a b : V) : V → V :=
  fun x => if x = a then b else if x = b then a else x

theorem transp_left {V : Type u} [DecidableEq V] (a b : V) :
    transp a b a = b := by
  show (if a = a then b else if a = b then a else a) = b
  rw [if_pos rfl]

/-- A transposition fixes every value distinct from both of its
    arguments. -/
theorem transp_fixes {V : Type u} [DecidableEq V] {a b x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) : transp a b x = x := by
  show (if x = a then b else if x = b then a else x) = x
  rw [if_neg hxa, if_neg hxb]

/-- Equivariance: the law commutes with every transposition. This is
    structurelessness on a bare carrier — no value is named, so every
    relabeling is a symmetry, and the transpositions generate them. -/
def Equivariant {V : Type u} [DecidableEq V] (f : V → V) : Prop :=
  ∀ a b x : V, f (transp a b x) = transp a b (f x)

/- ---------- three or more values: mute ---------- -/

/-- On a bare arena of three or more values, only the identity is
    structureless.

    Suppose `f` moves `x` to some `y ≠ x`. Because a third value `z`
    exists, the transposition of `y` and `z` fixes `x`. Equivariance then
    forces `f x = z` as well as `f x = y` — and `y ≠ z`. So `f` moves
    nothing.

    There is no negation on a bare three-element arena. Nothing
    structureless can be said there: every equivariant law holds of
    everything, which is to say nothing (`Articulation.identity_is_mute`).
    A three-valued absolute is silence. -/
theorem bare_three_is_mute {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f)
    (h3 : ∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) :
    ∀ x, f x = x := by
  intro x
  by_cases hfx : f x = x
  · exact hfx
  · -- f moves x to y ≠ x; a third value z gives the contradiction
    obtain ⟨z, hzx, hzf⟩ := h3 x (f x)
    have hxfix : transp (f x) z x = x :=
      transp_fixes (fun h => hfx h.symm) (fun h => hzx h.symm)
    have h := hequiv (f x) z x
    rw [hxfix, transp_left] at h
    exact absurd h.symm hzf

/- ---------- one value: mute ---------- -/

/-- On a bare arena of one value, every endomap is the identity — and no
    distinction is drawn, so there is nothing to say and nothing to say
    it with. -/
theorem bare_one_is_mute {V : Type u} (f : V → V)
    (h1 : ∀ x y : V, x = y) : ∀ x, f x = x :=
  fun x => h1 (f x) x

/- ---------- two values: speech ---------- -/

/-- On the two-valued arena, `not` commutes with every transposition. -/
theorem not_equivariant : Equivariant (fun x : Bool => !x) := by
  intro a b x
  cases a <;> cases b <;> cases x <;> rfl

/-- And it is not the identity: it moves everything. -/
theorem not_moves : ∀ x : Bool, (fun x : Bool => !x) x ≠ x := by
  intro x; cases x <;> decide

/-- Two speaks. On exactly two bare values there is a structureless
    law that is not the identity — and by `Articulation.absolute_law` it
    is the only one, and it can only run. -/
theorem two_speaks :
    Equivariant (fun x : Bool => !x) ∧ (∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨not_equivariant, not_moves⟩

/- ---------- the arena is forced ---------- -/

/-- The arena is forced. One value: mute. Three or more: mute. Two:
    the founding law.

    The count of values is not a premise of the position. It is the
    unique count at which a structureless law moves anything. The bare
    distinction is not an arena the position chose to work on; it is
    the only arena on which a structureless law speaks — and, by
    `three_does_not_determine` below, the only one on which the
    structureless specification determines its own run. -/
theorem arena_is_forced :
    (∀ (V : Type) (f : V → V), (∀ x y : V, x = y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨fun _ f h1 => bare_one_is_mute f h1,
   fun _ _ f he h3 => bare_three_is_mute f he h3,
   two_speaks⟩

/- ---------- the converse: speech needs exactly two ---------- -/

/-- Speech needs exactly two. The strongest form, and the converse of
    `bare_three_is_mute`: if *any* structureless law on a bare carrier
    moves *anything*, the carrier has exactly two values.

    Not "we work on two values". Not "two values suffice". The existence
    of a single structureless law that is not the identity *entails* that
    there are exactly two values to be had. Three would give the symmetry
    group room to freeze every map (`bare_three_is_mute`); one would leave
    nothing to move (`bare_one_is_mute`). The bare distinction is not the
    arena the position chose. It is the arena that anything saying
    anything is already in.

    So the count of values is not a premise, and never could have been: it
    is a *consequence* of there being an articulation at all. -/
theorem speaks_needs_exactly_two {V : Type u} [DecidableEq V] (f : V → V)
    (hequiv : Equivariant f) (hne : ∃ x, f x ≠ x) :
    ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b := by
  obtain ⟨x₀, hx₀⟩ := hne
  -- the carrier cannot have three or more values, or `f` would be frozen
  have h3 : ¬ (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) := by
    intro h
    exact hx₀ (bare_three_is_mute f hequiv h x₀)
  -- so two values exhaust it
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
  -- and the two are distinct, or `f` would have nothing to move
  intro he
  apply hx₀
  apply bare_one_is_mute f
  intro u v
  rcases hab u with hu | hu <;> rcases hab v with hv | hv
  · rw [hu, hv]
  · rw [hu, hv, he]
  · rw [hu, hv, he]
  · rw [hu, hv]

/-- The arena, settled from both sides: three or more values is mute, one
    is mute, two speaks — and anything that speaks is on exactly two.
    Nothing about the count was assumed at any point. -/
theorem arena_iff_two :
    (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∀ x y : V, ∃ z : V, z ≠ x ∧ z ≠ y) → ∀ x, f x = x)
    ∧ (∀ (V : Type) [DecidableEq V] (f : V → V), Equivariant f →
        (∃ x, f x ≠ x) → ∃ a b : V, a ≠ b ∧ ∀ z : V, z = a ∨ z = b)
    ∧ (Equivariant (fun x : Bool => !x) ∧ ∀ x : Bool, (fun x : Bool => !x) x ≠ x) :=
  ⟨fun _ _ f he h3 => bare_three_is_mute f he h3,
   fun _ _ f he hne => speaks_needs_exactly_two f he hne,
   two_speaks⟩

/- ---------- the escape hatch, priced ---------- -/

inductive V3 where
  | t | b | f
  deriving DecidableEq

open V3

/-- `OnlyShape`'s three-valued negation: swaps `t` and `f`, fixes the
    vacuum `b`. -/
def neg3 : V3 → V3
  | t => f
  | b => b
  | f => t

/-- The vacuum really is a static solution: `x = neg x` does not force a
    process on `V3`. This is the escape hatch, and it is real. -/
theorem v3_vacuum_is_static : neg3 b = b := rfl

/-- But the hatch is bought with a name. `neg3` is not equivariant:
    it fails to commute with the transposition that would move the
    vacuum. The `b` in its definition is a named element — precisely
    what `Structureless.constants_not_defble` forbids a structureless law
    to contain.

    So the three-valued arena offers no escape from becoming. It offers
    an escape only to a law that has already imported the structure the
    absolute was supposed to do without. Fix the import and, by
    `bare_three_is_mute`, nothing is left but the identity: not a static
    absolute, but no absolute at all.

    The vacuum is not a way for the ground to hold still. It is a way of
    smuggling one in. -/
theorem v3_negation_names_the_vacuum : ¬ Equivariant neg3 := by
  intro h
  -- transpose the vacuum b with t, and watch neg3 fail to follow
  have hb := h b t b
  rw [transp_left] at hb
  -- LHS: neg3 t = f. RHS: transp b t (neg3 b) = transp b t b = t.
  exact absurd hb (by decide)

/-- The finding, assembled: the static solution on `V3` exists, and it
    exists only for a law that names an element. Structurelessness and
    the escape hatch cannot be had together. -/
theorem escape_costs_a_name :
    neg3 b = b ∧ ¬ Equivariant neg3 :=
  ⟨v3_vacuum_is_static, v3_negation_names_the_vacuum⟩

/- ---------- the relational reading: three speaks but does not run ---------- -/

/- The results above classify laws — endomaps of the carrier.
   `Articulation.lean` reads specifications as graphs, and at that level
   three values are not mute: the inequation is definable from equality
   alone on any carrier, it excludes every diagonal state, and it has
   runs on `V3`. What three values lack is determination. Two runs of
   the inequation share a seed and diverge at the next tick, and no
   equivariant endomap realizes the specification, so nothing
   structureless selects between them: each step of any run imports a
   choice. On two values the run from a seed is unique
   (`Articulation.run_unique`). Determination, not speech, is what
   forces two at the relational level. -/

/-- Relations on `V3` definable from equality alone
    (as `Structureless.Defble`, at three values). -/
inductive Defble3 : (V3 → V3 → Prop) → Prop where
  | eq : Defble3 (fun x y => x = y)
  | neg {R} : Defble3 R → Defble3 (fun x y => ¬ R x y)
  | conj {R S} : Defble3 R → Defble3 S → Defble3 (fun x y => R x y ∧ S x y)
  | disj {R S} : Defble3 R → Defble3 S → Defble3 (fun x y => R x y ∨ S x y)

/-- The inequation is structureless on three values too. -/
theorem ne_defble3 : Defble3 (fun x y : V3 => ¬ (x = y)) :=
  Defble3.neg Defble3.eq

/-- A run of the inequation on `V3` through `t` and `b`. -/
def flipTB : V3 → V3
  | t => b
  | _ => t

def runTB : Nat → V3
  | 0 => t
  | n + 1 => flipTB (runTB n)

/-- A run of the inequation on `V3` through `t` and `f`. -/
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

/-- Both are genuine runs: consecutive values differ at every tick. -/
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

/-- The two runs share a seed and diverge at the next tick: on three
    values the inequation does not determine its run. -/
theorem v3_runs_diverge : runTB 0 = runTF 0 ∧ runTB 1 ≠ runTF 1 :=
  ⟨rfl, fun h => nomatch h⟩

/-- And nothing structureless closes the gap: an equivariant endomap on
    `V3` that satisfied the inequation everywhere would move something,
    and the only equivariant endomap is the identity. -/
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

/-- Three speaks but does not run. On `V3` the inequation is definable
    from equality alone and has runs, but two of its runs share a seed
    and diverge, and no equivariant endomap realizes it. Each step of
    any run on three values imports a choice no structureless law
    supplies; on two values the run from a seed is unique. -/
theorem three_does_not_determine :
    Defble3 (fun x y : V3 => ¬ (x = y))
    ∧ (∀ n, runTB n ≠ runTB (n + 1))
    ∧ (∀ n, runTF n ≠ runTF (n + 1))
    ∧ (runTB 0 = runTF 0 ∧ runTB 1 ≠ runTF 1)
    ∧ (∀ g : V3 → V3, Equivariant g → ¬ ∀ x, g x ≠ x) :=
  ⟨ne_defble3, runTB_runs, runTF_runs, v3_runs_diverge,
   fun g hg => v3_no_structureless_realizer g hg⟩

end Arena

/- audit -/
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
