/-!
# Obstruction

Premise `P`, independence, obstruction, orientation, and rigidity (Th. 5–7).
Standalone Lean 4; prelude only; no imports; no axioms.
-/

namespace Obstruction

/- Worlds -/

structure World : Type 1 where
  T : Type
  h : T → Bool
  tok : Prop → T

/-- Property of worlds. -/
def Claim : Type 1 := World → Prop

def DiscriminatesDenial (w : World) (A : Claim) : Prop :=
  w.h (w.tok (¬ A w)) ≠ w.h (w.tok (A w))

def Undeniable (A : Claim) : Prop :=
  ∀ w : World, DiscriminatesDenial w A → A w

theorem occurs_undeniable :
    Undeniable (fun w => ∃ t₁ t₂ : w.T, w.h t₁ ≠ w.h t₂) := by
  intro w hd
  exact ⟨w.tok (¬ (∃ t₁ t₂ : w.T, w.h t₁ ≠ w.h t₂)),
         w.tok (∃ t₁ t₂ : w.T, w.h t₁ ≠ w.h t₂), hd⟩

/-- The constant-true claim is undeniable. -/
theorem undeniable_trivial : Undeniable (fun _ => True) :=
  fun _ _ => trivial

/- Tensed worlds -/

structure TensedWorld : Type 1 where
  w : World
  succ : w.T → w.T → Prop

/-- No succession holds. -/
def Still (s : TensedWorld) : Prop := ∀ t t' : s.w.T, ¬ s.succ t t'

def Runs (s : TensedWorld) : Prop :=
  ∃ seq : Nat → s.w.T,
    (∀ m n : Nat, m ≠ n → seq m ≠ seq n) ∧
    (∀ n, s.succ (seq n) (seq (n + 1))) ∧
    (∀ n, s.w.h (seq (n + 1)) = !(s.w.h (seq n)))

/- Freeze -/


theorem freeze (A : Claim) (w : World) (r₁ r₂ : w.T → w.T → Prop) :
    A (TensedWorld.mk w r₁).w ↔ A (TensedWorld.mk w r₂).w :=
  Iff.rfl

theorem two_models (w : World) (t : w.T) :
    (∀ A : Claim,
        A (TensedWorld.mk w (fun _ _ => False)).w
          ↔ A (TensedWorld.mk w (fun _ _ => True)).w)
    ∧ Still (TensedWorld.mk w (fun _ _ => False))
    ∧ ¬ Still (TensedWorld.mk w (fun _ _ => True)) :=
  ⟨fun _ => Iff.rfl, fun _ _ h => h, fun h => h t t trivial⟩

/- Obstruction -/


theorem still_never_runs (s : TensedWorld) (hs : Still s) : ¬ Runs s :=
  fun ⟨seq, _, hsucc, _⟩ => hs (seq 0) (seq 1) (hsucc 0)


theorem obstruction {A : Claim} (hU : Undeniable A)
    (hB : ∀ s : TensedWorld, A s.w → Runs s) :
    ∀ s : TensedWorld, Still s → ¬ DiscriminatesDenial s.w A :=
  fun s hs hd => still_never_runs s hs (hB s (hU s.w hd))

theorem no_undeniable_bridge {A : Claim} (hU : Undeniable A)
    (s : TensedWorld) (hs : Still s) (hd : DiscriminatesDenial s.w A) :
    ¬ ∀ v : TensedWorld, A v.w → Runs v :=
  fun hB => obstruction hU hB s hs hd

theorem obstruction_tensed {A' : TensedWorld → Prop} {D : World → Prop}
    (hU : ∀ s : TensedWorld, D s.w → A' s)
    (hB : ∀ s : TensedWorld, A' s → Runs s) :
    ∀ s : TensedWorld, Still s → ¬ D s.w :=
  fun s hs hd => still_never_runs s hs (hB s (hU s hd))

/- Premise -/


theorem ne_eq_not : ∀ a b : Bool, a ≠ b → b = !a := by
  intro a b h
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

def Successive (s : TensedWorld) (tok : Prop → s.w.T) (X : Prop) : Prop :=
  s.succ (tok (¬ X)) (tok X)

theorem actuality_tick (s : TensedWorld) (tok : Prop → s.w.T) (X : Prop)
    (hd : s.w.h (tok (¬ X)) ≠ s.w.h (tok X))
    (hax : Successive s tok X) :
    s.succ (tok (¬ X)) (tok X)
      ∧ s.w.h (tok X) = !(s.w.h (tok (¬ X))) :=
  ⟨hax, ne_eq_not _ _ hd⟩

theorem chain_runs (s : TensedWorld) (seq : Nat → s.w.T)
    (hinj : ∀ m n : Nat, m ≠ n → seq m ≠ seq n)
    (hsucc : ∀ n, s.succ (seq n) (seq (n + 1)))
    (hd : ∀ n, s.w.h (seq n) ≠ s.w.h (seq (n + 1))) : Runs s :=
  ⟨seq, hinj, hsucc, fun n => ne_eq_not _ _ (hd n)⟩

/- Independence -/

def stillWitness : TensedWorld :=
  ⟨⟨Bool, id, fun _ => true⟩, fun _ _ => False⟩


def runningWitness : TensedWorld :=
  ⟨⟨Bool, id, fun _ => true⟩, fun _ _ => True⟩


/-- Still witness: discrimination holds; `Successive` fails for every tokening. -/
theorem premise_fails_still :
    (∃ t₁ t₂ : stillWitness.w.T, stillWitness.w.h t₁ ≠ stillWitness.w.h t₂)
    ∧ Still stillWitness
    ∧ ∀ (tok : Prop → stillWitness.w.T) (X : Prop),
        stillWitness.w.h (tok (¬ X)) ≠ stillWitness.w.h (tok X) →
          tok (¬ X) ≠ tok X
          ∧ stillWitness.w.h (tok X) = !(stillWitness.w.h (tok (¬ X)))
          ∧ ¬ Successive stillWitness tok X := by
  refine ⟨⟨true, false, by decide⟩, fun _ _ h => h, ?_⟩
  intro tok X hd
  exact ⟨fun he => hd (congrArg stillWitness.w.h he),
         ne_eq_not _ _ hd,
         fun h => h⟩

/-- Running witness: `Successive` holds for every tokening. -/
theorem premise_holds_running :
    ∀ (tok : Prop → runningWitness.w.T) (X : Prop),
      Successive runningWitness tok X :=
  fun _ _ => trivial

/-- `stillWitness` and `runningWitness` agree on all claims and disagree on `Successive`. -/
theorem premise_independent :
    (∀ A : Claim, A stillWitness.w ↔ A runningWitness.w)
    ∧ (∀ (tok : Prop → stillWitness.w.T) (X : Prop),
        ¬ Successive stillWitness tok X)
    ∧ (∀ (tok : Prop → runningWitness.w.T) (X : Prop),
        Successive runningWitness tok X) :=
  ⟨fun _ => Iff.rfl, fun _ _ h => h, fun _ _ => trivial⟩

theorem chain_premise_independent :
    (∀ A : Claim, A stillWitness.w ↔ A runningWitness.w)
    ∧ (∀ seq : Nat → stillWitness.w.T,
        ¬ ∀ n, stillWitness.succ (seq n) (seq (n + 1)))
    ∧ (∀ seq : Nat → runningWitness.w.T,
        ∀ n, runningWitness.succ (seq n) (seq (n + 1))) :=
  ⟨fun _ => Iff.rfl, fun _ h => h 0, fun _ _ => trivial⟩

/-- No claim true at the shared world entails or refutes `Successive` for all tensed worlds. -/
theorem no_claim_settles_premise (A : Claim) (hA : A stillWitness.w) :
    (¬ ∀ s : TensedWorld, A s.w →
        ∀ (tok : Prop → s.w.T) (X : Prop), Successive s tok X)
    ∧ (¬ ∀ s : TensedWorld, A s.w →
        ∀ (tok : Prop → s.w.T) (X : Prop), ¬ Successive s tok X) :=
  ⟨fun hE => hE stillWitness hA (fun _ => true) True,
   fun hR => hR runningWitness hA (fun _ => true) True trivial⟩

theorem self_ne_not : ∀ b : Bool, b ≠ !b := by
  intro b; cases b <;> decide

def alt : Nat → Bool
  | 0 => true
  | n + 1 => !(alt n)

def chainWitness : TensedWorld :=
  ⟨⟨Nat, alt, fun _ => 0⟩, fun _ _ => True⟩

theorem chain_hypothesis_realizable :
    ∃ seq : Nat → chainWitness.w.T,
      (∀ m n : Nat, m ≠ n → seq m ≠ seq n)
      ∧ (∀ n, chainWitness.succ (seq n) (seq (n + 1)))
      ∧ (∀ n, chainWitness.w.h (seq n) ≠ chainWitness.w.h (seq (n + 1))) :=
  ⟨fun n => n, fun _ _ h => h, fun _ => trivial,
   fun n => self_ne_not (alt n)⟩

/- Loci -/

/-- A two-element carrier admits no run. -/
theorem two_loci_never_run (s : TensedWorld) {a b : s.w.T}
    (h2 : ∀ z : s.w.T, z = a ∨ z = b) : ¬ Runs s := by
  intro ⟨seq, hinj, _, _⟩
  have h01 : seq 0 ≠ seq 1 := hinj 0 1 (by decide)
  have h02 : seq 0 ≠ seq 2 := hinj 0 2 (by decide)
  have h12 : seq 1 ≠ seq 2 := hinj 1 2 (by decide)
  cases h2 (seq 0) with
  | inl e0 =>
    cases h2 (seq 1) with
    | inl e1 => exact h01 (e0.trans e1.symm)
    | inr e1 =>
      cases h2 (seq 2) with
      | inl e2 => exact h02 (e0.trans e2.symm)
      | inr e2 => exact h12 (e1.trans e2.symm)
  | inr e0 =>
    cases h2 (seq 1) with
    | inl e1 =>
      cases h2 (seq 2) with
      | inl e2 => exact h12 (e1.trans e2.symm)
      | inr e2 => exact h02 (e0.trans e2.symm)
    | inr e1 => exact h01 (e0.trans e1.symm)

theorem one_locus_never_run (s : TensedWorld)
    (h1 : ∀ x y : s.w.T, x = y) : ¬ Runs s :=
  fun ⟨seq, hinj, _, _⟩ => hinj 0 1 (by decide) (h1 (seq 0) (seq 1))

/-- `runningWitness` has a two-element carrier, hence does not run. -/
theorem running_witness_never_runs : ¬ Runs runningWitness := by
  refine two_loci_never_run runningWitness (a := true) (b := false) ?_
  intro z
  cases z with
  | false => exact Or.inr rfl
  | true  => exact Or.inl rfl

/-- If succession implies equality, there is no run. -/
theorem reflexive_never_runs (s : TensedWorld)
    (h : ∀ u v : s.w.T, s.succ u v → u = v) : ¬ Runs s :=
  fun ⟨seq, hinj, hsucc, _⟩ =>
    hinj 0 1 (by decide) (h (seq 0) (seq 1) (hsucc 0))

/- Invariant succession -/

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

/-- Succession invariant under transposition. -/
def InvariantSucc {T : Type} [DecidableEq T] (R : T → T → Prop) : Prop :=
  ∀ a b x y, R (transp a b x) (transp a b y) ↔ R x y

theorem diag_uniform {T : Type} [DecidableEq T] {R : T → T → Prop}
    (hR : InvariantSucc R) (x x' : T) : R x x ↔ R x' x' := by
  have h := hR x x' x x
  rw [transp_left] at h
  exact h.symm

theorem offdiag_uniform {T : Type} [DecidableEq T] {R : T → T → Prop}
    (hR : InvariantSucc R) {x y x' y' : T} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    R x y ↔ R x' y' := by
  have hy1 : transp x x' y ≠ x' := by
    by_cases hyx' : y = x'
    · have hxx' : x ≠ x' := fun h => hxy (h.trans hyx'.symm)
      have hval : transp x x' y = x := by
        rw [hyx']
        show (if x' = x then x' else if x' = x' then x else x') = x
        rw [if_neg (fun h => hxx' h.symm), if_pos rfl]
      rw [hval]
      exact hxx'
    · rw [transp_fixes (fun h => hxy h.symm) hyx']
      exact hyx'
  have step1 : R x' (transp x x' y) ↔ R x y := by
    have h := hR x x' x y
    rw [transp_left] at h
    exact h
  have step2 : R x' y' ↔ R x' (transp x x' y) := by
    have h := hR (transp x x' y) y' x' (transp x x' y)
    rw [transp_left, transp_fixes (fun k => hy1 k.symm) hxy'] at h
    exact h
  exact (step2.trans step1).symm

/-- An invariant succession is determined by its diagonal and off-diagonal values. -/
theorem invariant_succ_classified {T : Type} [DecidableEq T]
    {R : T → T → Prop} (hR : InvariantSucc R) (x y : T) (hxy : x ≠ y) :
    (∀ u : T, R u u ↔ R x x)
    ∧ (∀ u v : T, u ≠ v → (R u v ↔ R x y)) :=
  ⟨fun u => diag_uniform hR u x, fun _ _ huv => offdiag_uniform hR huv hxy⟩

/-- An invariant succession that fails somewhere on the diagonal and holds off-diagonal is inequality. -/
theorem invariant_says_is_ne {T : Type} [DecidableEq T] {R : T → T → Prop}
    (hR : InvariantSucc R) (hsays : ∃ u, ¬ R u u)
    (hsat : ∃ u v, u ≠ v ∧ R u v) : ∀ u v, R u v ↔ u ≠ v := by
  obtain ⟨p, hp⟩ := hsays
  obtain ⟨q, r, hqr, hR'⟩ := hsat
  have hdiag : ∀ u : T, ¬ R u u := fun u hu => hp ((diag_uniform hR u p).mp hu)
  intro u v
  constructor
  · intro huv he; exact hdiag u (he ▸ huv)
  · intro huv; exact (offdiag_uniform hR hqr huv).mp hR'

/-- Every invariant succession is symmetric. -/
theorem invariant_succ_symm {T : Type} [DecidableEq T] {R : T → T → Prop}
    (hR : InvariantSucc R) : ∀ u v, R u v ↔ R v u := by
  intro u v
  by_cases huv : u = v
  · subst huv; exact Iff.rfl
  · exact offdiag_uniform hR huv (fun h => huv h.symm)

/-- No invariant succession is asymmetric on any pair. -/
theorem no_invariant_orientation {T : Type} [DecidableEq T]
    {R : T → T → Prop} (hR : InvariantSucc R) :
    ¬ ∃ u v, R u v ∧ ¬ R v u :=
  fun ⟨u, v, hf, hb⟩ => hb ((invariant_succ_symm hR u v).mp hf)

/- Orientation -/

/-- Oriented succession: `tok (¬X)` succeeds to `tok X`, and not conversely. -/
def OrientedSuccessive (s : TensedWorld) (tok : Prop → s.w.T)
    (X : Prop) : Prop :=
  s.succ (tok (¬ X)) (tok X) ∧ ¬ s.succ (tok X) (tok (¬ X))

theorem oriented_is_successive (s : TensedWorld) (tok : Prop → s.w.T)
    (X : Prop) (h : OrientedSuccessive s tok X) : Successive s tok X :=
  h.1

/-- Oriented succession requires distinct tokens. -/
theorem oriented_needs_distinct_tokens (s : TensedWorld)
    (tok : Prop → s.w.T) (X : Prop) (h : OrientedSuccessive s tok X) :
    tok (¬ X) ≠ tok X :=
  fun he => h.2 (he ▸ h.1)

/-- Run with irreversible succession at each step. -/
def OrientedRuns (s : TensedWorld) : Prop :=
  ∃ seq : Nat → s.w.T,
    (∀ m n : Nat, m ≠ n → seq m ≠ seq n) ∧
    (∀ n, s.succ (seq n) (seq (n + 1)) ∧ ¬ s.succ (seq (n + 1)) (seq n)) ∧
    (∀ n, s.w.h (seq (n + 1)) = !(s.w.h (seq n)))

theorem oriented_runs_run (s : TensedWorld) (h : OrientedRuns s) : Runs s :=
  let ⟨seq, hinj, hsucc, halt⟩ := h
  ⟨seq, hinj, fun n => (hsucc n).1, halt⟩

/-- Symmetric succession admits no oriented run. -/
theorem symmetric_never_oriented (s : TensedWorld)
    (hsym : ∀ u v : s.w.T, s.succ u v → s.succ v u) : ¬ OrientedRuns s :=
  fun ⟨_, _, hsucc, _⟩ => (hsucc 0).2 (hsym _ _ (hsucc 0).1)

/-- Invariant succession admits no oriented run. -/
theorem invariant_never_oriented (s : TensedWorld) [DecidableEq s.w.T]
    (hR : InvariantSucc s.succ) : ¬ OrientedRuns s :=
  symmetric_never_oriented s
    (fun u v h => (invariant_succ_symm hR u v).mp h)

/-- Oriented succession at a discriminated pair yields distinct tokens, complementary values, and non-stillness. -/
theorem oriented_tick (s : TensedWorld) (tok : Prop → s.w.T) (X : Prop)
    (hd : s.w.h (tok (¬ X)) ≠ s.w.h (tok X))
    (hax : OrientedSuccessive s tok X) :
    tok (¬ X) ≠ tok X
      ∧ s.w.h (tok X) = !(s.w.h (tok (¬ X)))
      ∧ ¬ Still s :=
  ⟨fun he => hd (congrArg s.w.h he),
   ne_eq_not _ _ hd,
   fun hstill => hstill _ _ hax.1⟩

/-- A chain of oriented, discriminated steps yields an oriented run. -/
theorem oriented_chain_runs (s : TensedWorld) (seq : Nat → s.w.T)
    (hinj : ∀ m n : Nat, m ≠ n → seq m ≠ seq n)
    (hsucc : ∀ n, s.succ (seq n) (seq (n + 1))
      ∧ ¬ s.succ (seq (n + 1)) (seq n))
    (hd : ∀ n, s.w.h (seq n) ≠ s.w.h (seq (n + 1))) :
    OrientedRuns s ∧ Runs s ∧ ¬ Still s :=
  have ho : OrientedRuns s :=
    ⟨seq, hinj, hsucc, fun n => ne_eq_not _ _ (hd n)⟩
  ⟨ho, oriented_runs_run s ho, fun hstill => hstill _ _ (hsucc 0).1⟩

/-- On `runningWitness`, `OrientedSuccessive` fails for every tokening. -/
theorem running_witness_not_oriented :
    ∀ (tok : Prop → runningWitness.w.T) (X : Prop),
      ¬ OrientedSuccessive runningWitness tok X :=
  fun _ _ ⟨_, hb⟩ => hb trivial

/-- Symmetric adjacency on `Nat`. -/
def adjacencyWitness : TensedWorld :=
  ⟨⟨Nat, alt, fun _ => 0⟩, fun m n => n = m + 1 ∨ m = n + 1⟩

theorem adjacency_runs : Runs adjacencyWitness :=
  ⟨fun n => n, fun _ _ h => h, fun _ => Or.inl rfl, fun _ => rfl⟩

theorem adjacency_not_still : ¬ Still adjacencyWitness :=
  fun h => h (0 : Nat) (1 : Nat) (Or.inl rfl)

theorem adjacency_symmetric :
    ∀ u v, adjacencyWitness.succ u v → adjacencyWitness.succ v u :=
  fun _ _ h => h.elim Or.inr Or.inl

/-- `adjacencyWitness` admits no oriented run. -/
theorem adjacency_not_oriented : ¬ OrientedRuns adjacencyWitness :=
  symmetric_never_oriented adjacencyWitness adjacency_symmetric

/-- Successor relation on `Nat`. -/
def orientedWitness : TensedWorld :=
  ⟨⟨Nat, alt, fun _ => 0⟩, fun m n => n = m + 1⟩

theorem succ_ne_plus_two : ∀ n : Nat, n ≠ n + 2 := by
  intro n
  induction n with
  | zero => intro h; exact Nat.noConfusion h
  | succ k ih => intro h; exact ih (Nat.succ.inj h)

/-- `orientedWitness` admits an oriented run. -/
theorem oriented_witness_runs : OrientedRuns orientedWitness :=
  ⟨fun n => n, fun _ _ h => h,
   fun n => ⟨rfl, fun h => succ_ne_plus_two n h⟩,
   fun _ => rfl⟩

/-- An oriented discriminated pair exists in `orientedWitness`. -/
theorem oriented_pair_realizable :
    ∃ t t' : orientedWitness.w.T,
      orientedWitness.succ t t'
      ∧ ¬ orientedWitness.succ t' t
      ∧ orientedWitness.w.h t ≠ orientedWitness.w.h t' :=
  ⟨(0 : Nat), (1 : Nat), rfl, fun h => Nat.noConfusion h, by decide⟩

/-- Still structure over `Bool` with given tokening. -/
def orientedStill (tok : Prop → Bool) : TensedWorld :=
  ⟨⟨Bool, id, tok⟩, fun _ _ => False⟩

/-- Oriented succession `false → true` over the same world. -/
def orientedRunning (tok : Prop → Bool) : TensedWorld :=
  ⟨⟨Bool, id, tok⟩, fun u v => u = false ∧ v = true⟩

/-- `orientedStill` and `orientedRunning` agree on claims and disagree on oriented succession at a discriminated pair. -/
theorem oriented_premise_independent (tok : Prop → Bool) (X : Prop)
    (h0 : tok (¬ X) = false) (h1 : tok X = true) :
    (∀ A : Claim, A (orientedStill tok).w ↔ A (orientedRunning tok).w)
    ∧ (∀ (tk : Prop → (orientedStill tok).w.T) (Y : Prop),
        ¬ OrientedSuccessive (orientedStill tok) tk Y)
    ∧ OrientedSuccessive (orientedRunning tok) tok X := by
  refine ⟨fun _ => Iff.rfl, fun _ _ h => h.1, ⟨⟨h0, h1⟩, ?_⟩⟩
  intro ⟨hf, _⟩
  rw [h1] at hf
  exact Bool.noConfusion hf

/- Succession-using discrimination -/

/-- Succession between the tokens of `¬A s` and `A s`. -/
def SuccDiscriminates (s : TensedWorld) (A : TensedWorld → Prop) : Prop :=
  s.succ (s.w.tok (¬ A s)) (s.w.tok (A s))

/-- `SuccDiscriminates` is an instance of `Successive`. -/
theorem horn_two_is_premise (s : TensedWorld) (A : TensedWorld → Prop) :
    SuccDiscriminates s A ↔ Successive s s.w.tok (A s) :=
  Iff.rfl

/-- Any predicate entailing a succession fact refutes stillness. -/
theorem horn_two (D : TensedWorld → Prop)
    (hD : ∀ s : TensedWorld, D s → ∃ t t', s.succ t t') :
    ∀ s : TensedWorld, D s → ¬ Still s :=
  fun s hd hstill =>
    let ⟨t, t', h⟩ := hD s hd
    hstill t t' h

/- Rigidity -/

theorem no_half_tick : ∀ a u b : Bool, b = !a → u = !a → b = !u → False := by
  decide

theorem no_interpolation (s : TensedWorld) (seq : Nat → s.w.T)
    (hrun : ∀ n, s.w.h (seq (n + 1)) = !(s.w.h (seq n))) (n : Nat) (u : s.w.T)
    (before : s.w.h u = !(s.w.h (seq n)))
    (after : s.w.h (seq (n + 1)) = !(s.w.h u)) : False :=
  no_half_tick (s.w.h (seq n)) (s.w.h u) (s.w.h (seq (n + 1)))
    (hrun n) before after

theorem prior_value_exists : ∀ x : Bool, ∃ p : Bool, x = !p := by
  decide

theorem prior_token_determined (s : TensedWorld) (t₀ p q : s.w.T)
    (hp : s.w.h t₀ = !(s.w.h p)) (hq : s.w.h t₀ = !(s.w.h q)) :
    s.w.h p = s.w.h q := by
  revert hp hq
  cases s.w.h t₀ <;> cases s.w.h p <;> cases s.w.h q <;> decide

end Obstruction

/- Axiom audit -/
#print axioms Obstruction.occurs_undeniable
#print axioms Obstruction.undeniable_trivial
#print axioms Obstruction.freeze
#print axioms Obstruction.two_models
#print axioms Obstruction.still_never_runs
#print axioms Obstruction.obstruction
#print axioms Obstruction.no_undeniable_bridge
#print axioms Obstruction.obstruction_tensed
#print axioms Obstruction.actuality_tick
#print axioms Obstruction.chain_runs
#print axioms Obstruction.premise_fails_still
#print axioms Obstruction.premise_holds_running
#print axioms Obstruction.premise_independent
#print axioms Obstruction.chain_premise_independent
#print axioms Obstruction.no_claim_settles_premise
#print axioms Obstruction.oriented_premise_independent
#print axioms Obstruction.chain_hypothesis_realizable
#print axioms Obstruction.two_loci_never_run
#print axioms Obstruction.one_locus_never_run
#print axioms Obstruction.running_witness_never_runs
#print axioms Obstruction.reflexive_never_runs
#print axioms Obstruction.diag_uniform
#print axioms Obstruction.offdiag_uniform
#print axioms Obstruction.invariant_succ_classified
#print axioms Obstruction.invariant_says_is_ne
#print axioms Obstruction.invariant_succ_symm
#print axioms Obstruction.no_invariant_orientation
#print axioms Obstruction.oriented_is_successive
#print axioms Obstruction.oriented_needs_distinct_tokens
#print axioms Obstruction.oriented_runs_run
#print axioms Obstruction.symmetric_never_oriented
#print axioms Obstruction.invariant_never_oriented
#print axioms Obstruction.oriented_tick
#print axioms Obstruction.oriented_chain_runs
#print axioms Obstruction.running_witness_not_oriented
#print axioms Obstruction.adjacency_runs
#print axioms Obstruction.adjacency_not_still
#print axioms Obstruction.adjacency_symmetric
#print axioms Obstruction.adjacency_not_oriented
#print axioms Obstruction.succ_ne_plus_two
#print axioms Obstruction.oriented_witness_runs
#print axioms Obstruction.oriented_pair_realizable
#print axioms Obstruction.horn_two_is_premise
#print axioms Obstruction.horn_two
#print axioms Obstruction.no_interpolation
#print axioms Obstruction.prior_value_exists
#print axioms Obstruction.prior_token_determined
