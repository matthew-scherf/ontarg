/-!
# Event

`Hist T M := T → M` is a history: a medium's configuration at each time.
`Occurs h` holds when two times give different configurations. A
realized contrast lives at two loci (a margin) or two times; on a
total, marginless configuration only the temporal fork remains
(`no_margin_forces_time`). On a two-valued medium the resulting
contrast is a single tick of `¬` (`contrast_is_a_tick`,
`the_law_of_the_event`), assembled in `denial_ticks_the_clock`.
-/

namespace Event

/-- A history: the medium's configuration at each time. -/
def Hist (T M : Type) : Type := T → M

/-- Two times at which `h`'s configuration differs. -/
def Occurs {T M : Type} (h : Hist T M) : Prop := ∃ t₁ t₂ : T, h t₁ ≠ h t₂

/-- A configuration over loci. -/
def Config (L V : Type) : Type := L → V

theorem still_tokens_nothing {T M : Type} (h : Hist T M)
    (hstill : ∀ t₁ t₂ : T, h t₁ = h t₂) : ¬ Occurs h :=
  fun ⟨t₁, t₂, hne⟩ => hne (hstill t₁ t₂)

theorem no_distinction_no_event {T M : Type} (hM : ∀ a b : M, a = b)
    (h : Hist T M) : ¬ Occurs h :=
  fun ⟨_, _, hne⟩ => hne (hM _ _)

/-- A single configuration of a one-locus medium contains no contrast. -/
theorem a_moment_is_mute {L V : Type} (c : Config L V)
    (hone : ∀ l₁ l₂ : L, l₁ = l₂) : ¬ ∃ l₁ l₂ : L, c l₁ ≠ c l₂ :=
  fun ⟨l₁, l₂, hne⟩ => hne (congrArg c (hone l₁ l₂))

/-- A two-locus medium can bear a mark and margin differing at one moment. -/
theorem the_margin_carries_static_tokens :
    ∃ (c : Config Bool Bool) (l₁ l₂ : Bool), l₁ ≠ l₂ ∧ c l₁ ≠ c l₂ :=
  ⟨fun l => l, true, false, by decide, by decide⟩

theorem same_time_needs_two_loci {L V : Type} (c : Config L V)
    {l₁ l₂ : L} (hc : c l₁ ≠ c l₂) : l₁ ≠ l₂ :=
  fun he => hc (congrArg c he)

theorem same_locus_needs_two_times {T M : Type} (h : Hist T M)
    {t₁ t₂ : T} (hc : h t₁ ≠ h t₂) : t₁ ≠ t₂ :=
  fun he => hc (congrArg h he)

/-- Two distinct total configurations of one history occur at two distinct times. -/
theorem no_margin_forces_time {T M : Type} (h : Hist T M)
    {m₁ m₂ : M} (hd : m₁ ≠ m₂)
    (h₁ : ∃ t, h t = m₁) (h₂ : ∃ t, h t = m₂) :
    ∃ t₁ t₂ : T, t₁ ≠ t₂ := by
  obtain ⟨t₁, e₁⟩ := h₁
  obtain ⟨t₂, e₂⟩ := h₂
  exact ⟨t₁, t₂, fun he =>
    hd (e₁.symm.trans ((congrArg h he).trans e₂))⟩

/-- A tokening in time: each claim assigned the time its mark stands. -/
def TimeTok (T : Type) : Type := Prop → T

theorem event_retorsion {T M : Type} (h : Hist T M) (tok : TimeTok T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) : Occurs h :=
  ⟨tok (¬ Occurs h), tok (Occurs h), hd⟩

theorem no_still_denial {T M : Type} (h : Hist T M) (tok : TimeTok T) :
    ¬ (h (tok (¬ Occurs h)) ≠ h (tok (Occurs h)) ∧ ¬ Occurs h) :=
  fun ⟨hd, hn⟩ => hn (event_retorsion h tok hd)

theorem ne_eq_not : ∀ a b : Bool, a ≠ b → b = !a := by
  intro a b h
  cases a <;> cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

/-- On `Bool`, a realized contrast is an alternation. -/
theorem contrast_is_a_tick {T : Type} (h : Hist T Bool) {t₁ t₂ : T}
    (hc : h t₁ ≠ h t₂) : h t₂ = !(h t₁) :=
  ne_eq_not (h t₁) (h t₂) hc

/-- Commutes with negation, naming no side. -/
def Structureless (g : Bool → Bool) : Prop := ∀ b, g (!b) = !(g b)

/-- A structureless law on `Bool` that moves anything is `¬` everywhere. -/
theorem the_law_of_the_event (g : Bool → Bool) (hg : Structureless g)
    {a : Bool} (hmove : g a ≠ a) : ∀ b, g b = !b := by
  have hfalse : g false = !(g true) := hg true
  cases htrue : g true with
  | true =>
    exfalso
    rw [htrue] at hfalse
    cases a with
    | true  => exact hmove htrue
    | false => exact hmove hfalse
  | false =>
    intro b
    cases b with
    | true  => exact htrue
    | false => rw [htrue] at hfalse; exact hfalse

/-- The trajectory of `f` from `seed`. -/
def orbit (f : Bool → Bool) (seed : Bool) : Nat → Bool
  | 0     => seed
  | n + 1 => f (orbit f seed n)

/-- Assembled: on a two-valued, marginless medium, tokening "nothing occurs" against its
    denial forces occurrence, forces two distinct times, makes the contrast an alternation,
    makes that alternation's law unique, and identifies it with one step of `orbit not`. -/
theorem denial_ticks_the_clock {T : Type} (h : Hist T Bool)
    (tok : TimeTok T)
    (hd : h (tok (¬ Occurs h)) ≠ h (tok (Occurs h))) :
    Occurs h
    ∧ tok (¬ Occurs h) ≠ tok (Occurs h)
    ∧ h (tok (Occurs h)) = !(h (tok (¬ Occurs h)))
    ∧ (∀ g : Bool → Bool, Structureless g →
        g (h (tok (¬ Occurs h))) = h (tok (Occurs h)) →
        ∀ b, g b = !b)
    ∧ h (tok (Occurs h)) = orbit not (h (tok (¬ Occurs h))) 1 :=
  have htick : h (tok (Occurs h)) = !(h (tok (¬ Occurs h))) :=
    contrast_is_a_tick h hd
  ⟨event_retorsion h tok hd,
   same_locus_needs_two_times h hd,
   htick,
   fun g hg hgc =>
     the_law_of_the_event g hg (fun he => hd (he.symm.trans hgc)),
   htick⟩

end Event

#print axioms Event.still_tokens_nothing
#print axioms Event.no_distinction_no_event
#print axioms Event.a_moment_is_mute
#print axioms Event.the_margin_carries_static_tokens
#print axioms Event.same_time_needs_two_loci
#print axioms Event.same_locus_needs_two_times
#print axioms Event.no_margin_forces_time
#print axioms Event.event_retorsion
#print axioms Event.no_still_denial
#print axioms Event.contrast_is_a_tick
#print axioms Event.the_law_of_the_event
#print axioms Event.denial_ticks_the_clock
