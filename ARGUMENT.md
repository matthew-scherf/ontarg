# The Ontological Argument of Becoming

An ontological argument derives an existence verdict from a concept
alone, a priori, without reliance on observation or any premise about
the world. Classical instances begin with the most comprehensive
concept — a maximally perfect being — and aim at a necessary substance.
The present argument begins with the minimal concept:
presuppositionlessness, a specification that imports no structure,
names no constant, distinguishes no element. What follows from that
concept is not a necessary being but the impossibility of one, and the
necessity — constructed, unique — of a becoming. And this time the
derivation carries no premise anywhere: each assumption earlier
versions of this argument named is now a theorem, a proved openness, or
a condition whose denial cannot be tokened.

The whole core is assembled in [`lean/Becoming.lean`](lean/Becoming.lean)
as the single theorem `Becoming.ontological_argument` — axiom-free.
Everything below cites that file and the twenty others it draws on.

## Tags

Each claim carries one of three explicit verdicts, so its status is
never implicit:

* **forced** — carried by a machine-verified theorem, cited by file and
  name.
* **free** — proved undecidable in the relevant vocabulary; what is
  asserted is the undecidability, not either answer.
* **interpretation** — a suggested reading of a theorem, marked as
  such. The mathematics stands without it.

Earlier versions of this argument carried a fourth tag, **premise**,
and named four (R1–R4), plus a residue on the reading of the
classification. There is no such tag now. Why there is not is a section
of its own, below, and it is the one place a reader should press
hardest.

A specification is a rule a state must satisfy, and it can be read two
ways. Written `x = f(x)` it is an equation, demanding a fixed point — a
state identical to its image (the object frame). Written
`x(n+1) = f(x(n))` it is a recursion, specifying a trajectory over
discrete steps (the process frame). The distinction between these
readings is the engine of the argument.

## The argument in eight steps

### Step 1 — The distinction is drawn *(forced; its denial unsayable)*

A medium with one state gives every claim the same mark, which is to
token none of them: nothing is said rather than anything else. So any
medium that marks two claims differently has two distinct states — a
distinction is drawn. Now let the claim be *that no distinction is
drawn*. To token it as opposed to its denial is to draw one. The denial
is not refuted; it is unsayable.

This is the only entry point the argument has, and it is not an
assumption but the shape of any act that could contain one. It binds
only because the claim in question has claimed everything: one can
truly write "this page is blank" — on another page. A retorsion never
binds a claim with somewhere else to stand
(`the_outside_is_the_premise`); it binds a claim with no outside, which
is what *absolute* means.

*Lean:* `Becoming.retorsion`, `Becoming.no_undrawn_denial`;
[`Tokening.lean`](lean/Tokening.lean) `subsingleton_tokens_nothing`,
`denial_draws_the_distinction`, `discrimination_says_and_sat`,
`the_outside_is_the_premise`. Axiom-free.

### Step 2 — The arena is two *(forced)*

On a bare carrier of one value, every law is the identity. On a bare
carrier of three or more, every law invariant under all relabelings is
*also* the identity — the third value gives the symmetry group room
enough to pin every map down. Only on exactly two values is there a
structureless law that is not the identity. And the converse: if any
structureless law on a bare carrier moves anything, the carrier has
exactly two values. One is mute, three is mute; two speaks. The count
of values is not a choice the argument makes; it is a consequence of
there being an articulation at all.

This also prices an apparent escape. On the three-element alphabet,
`x = neg x` has a static solution — the vacuum — so becoming looks
optional there. But that alphabet's negation fixes the vacuum *by
naming it*: the classification for it carries the name as a hypothesis
(`OnlyShape.equivariant_endomaps_V3`, hypothesis `g b = b`), and naming
an element is importing structure. Drop the name and nothing is left
but the identity: not a static absolute, but no absolute at all. The
vacuum is not a way for the ground to hold still; it is a way of
smuggling one in. Nor does the relational reading reopen the case: on
three values the inequation speaks but does not determine — two of its
runs share a seed and diverge, and nothing structureless selects
between them (`three_does_not_determine`).

*Lean:* `Becoming.bare_one_is_mute`, `Becoming.bare_three_is_mute`,
`Becoming.two_speaks`; [`Arena.lean`](lean/Arena.lean)
`arena_is_forced`, `speaks_needs_exactly_two`, `arena_iff_two`,
`v3_negation_names_the_vacuum`, `three_does_not_determine`. The
becoming-side results axiom-free; the converse within
`[propext, Classical.choice, Quot.sound]`.

### Step 3 — The unique forced candidate *(forced)*

To import no structure on the bare distinction is to commute with the
relabeling that exchanges its sides (equivariance): the law cannot tell
the sides apart, so it acts the same after they are swapped. That
identification is not a reading left to charity — it is grounded from
both directions. A law is definable from the distinction alone (from
pure equality, naming nothing) iff it is equivariant, and no constant
law is so definable (`structureless_iff_equivariant`,
`constants_not_defble`). And there is no third thing for
"structureless" to mean: a law on the bare distinction that fails to
commute with the relabeling is a *constant* — it ignores its input and
names a value, which is the maximally structured case, not the
structureless one equivariance missed (`non_equivariant_names`). What
earlier versions carried as premise R3 is a theorem.

The classification then follows: the structureless laws on the bare
distinction are exactly the identity and the negation, constants are
excluded, and the identity is satisfied by everything and so says
nothing. Exactly one structureless specification has content: `x = ¬x`.

Read specifications as graphs rather than endomaps and the
classification strengthens rather than weakens. An endomap is already a
commitment — it says every state has a successor. Over relations a
fourth candidate stands beside `=`, `≠` and `⊤`: the empty relation.
That is *nothing*, and here it is ruled out for a stateable reason: it
says something — it excludes every state — but nothing satisfies it in
any frame. It is not a rival absolute; it is silence
(`nothing_is_silent`). The one specification that is both contentful
and satisfiable is `≠`.

*Lean:* `Becoming.one_candidate`, `Becoming.constants_not_structureless`,
`Becoming.id_says_nothing`; fuller generality
[`OnlyShape.lean`](lean/OnlyShape.lean) `spec_forced`; the equivariance
identification [`Structureless.lean`](lean/Structureless.lean)
`structureless_iff_equivariant`, `constants_not_defble`; the closure of
the rival reading and the relational classification
[`Articulation.lean`](lean/Articulation.lean) `non_equivariant_names`,
`nothing_is_silent`, `identity_is_mute`, `absolute_is_inhabited`.
Axiom-free.

### Step 4 — No being *(forced)*

The candidate reads, as an equation, as the demand for a state
identical to its own negation — a side of a distinction that is
simultaneously the other side. No such state exists; neither side
satisfies `x = ¬x`. And the impasse is not a peculiarity of the
negation: no structureless specification could have singled out a state
at all. Read of itself, a structureless specification holds of every
state or of none — the diagonal is uniform — so one that excludes
anything excludes everything, and its object frame is empty
(`diagonal_uniform`, `says_kills_the_object`). The absolute cannot be a
thing, not because its law happens to lack a solution, but because
nothing structureless could have had one. At the level of propositions
the impasse persists: a proposition equal to its own negation is
absurd, as the liar and Russell's paradox exemplify. The
presuppositionless candidate necessarily lacks any static instance.

*Lean:* `Becoming.no_static_instance`, `Becoming.no_being`,
`Becoming.diagonal_uniform`, `Becoming.says_kills_the_object`;
[`TwoReadings.lean`](lean/TwoReadings.lean) `object_reading_empty`;
[`Aseity.lean`](lean/Aseity.lean) `founding_diagonal`. Axiom-free.

### Step 5 — Unique becoming *(forced)*

Take the same candidate as a recursion, `x(n+1) = ¬x(n)`. Now it is
satisfiable in the strongest sense: from any initial value there is a
trajectory, exactly one, alternating forever, each step determined by
the last — a two-state periodic sequence, the two-tick clock. The
existence is not argued for but constructed: the trajectory is written
down and its uniqueness is a short induction. Assembled relationally: a
specification that imports nothing and articulates — excludes
something, and is satisfied in some frame — *is* the negation graph;
its object frame is empty, its process frame is inhabited, and its run
is the clock, unique given a seed (`absolute_articulation`). The same
shape returns at the foundations: the Gödel-style guarded fixed point
of the founding specification *is* this clock (`godel_is_clock`). The
construction that yields a self-referential sentence in incompleteness
yields, here, a time series.

"Exists" here means only that the recursion has a constructed, unique
solution — the way the natural numbers exist once the successor is
given. It does not mean a process is occurring; that question is
Step 8's.

*Lean:* `Becoming.becoming_exists`, `Becoming.becoming_unique`,
`Becoming.two_tick_clock`, `Becoming.absolute_law`,
`Becoming.absolute_articulation`;
[`TwoReadings.lean`](lean/TwoReadings.lean) `founding_two_readings`;
[`Loeb.lean`](lean/Loeb.lean) `deJonghSambin`, `godel_is_clock`.
Axiom-free (`Loeb` within `[propext, Quot.sound]`).

### Step 6 — The refusal is the running *(forced)*

Steps 4 and 5 are not two facts but one. **A specification has no
fixed point if and only if every orbit moves at every tick.** A fixed
point would be a one-state orbit that never moves; a stalled orbit
would sit at a fixed point. So "refuses to be" and "cannot stop
running" are the same hypothesis on the law, stated in the two frames
— a biconditional, not a resemblance.

*Lean:* `Becoming.refusal_is_running`;
[`TwoReadings.lean`](lean/TwoReadings.lean) `frames_one_fact`.
Axiom-free.

This is the beam against equivocation. The non-existence of the being
and the existence of the becoming are not two verdicts the prose
reconciles; they are one theorem about the law, proved without passing
through natural language.

### Step 7 — The seed is a record, not a premise *(forced)*

The run is unique *given a seed*. Two seeds, two runs — and a choice
the mathematics leaves open and the world closes is exactly what a
premise is. If the seed were one, the count would be one, not zero. It
is not. The two runs are one run relabelled (`seed_is_relabel`), and
the relabeling is the whole symmetry of the bare distinction, so no
structureless proposition separates them: to the only vocabulary the
absolute allows itself, the two runs are one world
(`seed_is_invisible`). A proposition that *did* separate them — "the
run starts `true`" — would name a value, and naming is importing
structure (`naming_the_seed_imports`). So the seed is neither assumed
nor derived: it is *read*. The last choice the mathematics leaves open
arrives not as the final premise but as the first record — a
value-class fact of the kind `SelfDerivation.lean` proves must be
underivable.

*Lean:* `Becoming.seed_is_relabel`, `Becoming.seed_is_invisible`;
[`Seed.lean`](lean/Seed.lean) `structureless_blind_to_seed`,
`absolute_class_is_a_point`, `naming_the_seed_imports`,
`starts_true_is_not_structureless`. `seed_is_relabel` axiom-free; the
invisibility corollaries within `[Quot.sound]` (function
extensionality).

### Step 8 — Actuality, graded

Steps 1–7 give necessity de dicto: it is a *theorem* that nothing
static answers to the concept and a *theorem* that exactly one process
does. Whether anything *actual* answers to it is a further question.
The classical arguments cross this gap in one silent stride, inside a
value-word ("greater," "perfection," "great"). Here it is crossed in
public and graded, each grade priced:

| Grade | Asserts | Price | Lean |
|---|---|---|---|
| **0** | Steps 1–7: the chain — entry, arena, uniqueness, refutation, unique construction, equivalence, seed | Nothing | `Becoming.ontological_argument` — axiom-free |
| **1** | Any absolute articulation is already the founding shape, and the grounding chain closes into the clock with or without a floor | Nothing | [`Articulation.lean`](lean/Articulation.lean) `absolute_articulation`; [`Eternal.lean`](lean/Eternal.lean) `eternal_shape` |
| **2** | Denial of one's own occurrence self-refutes in the tokening | A tokening (the denier supplies it) | [`Cogito.lean`](lean/Cogito.lean) `no_self_denial` |
| **3** | The clock has actually run | Reading the kernel's check as an instance *(interpretation)* | [`Instantiation.lean`](lean/Instantiation.lean) `run_class_generated` |

- **Grade 1** *(forced)* — earlier versions reached this grade through
  four named premises: that every demand for a ground is answered (R1),
  that the demand relation is well-founded (R2), that an unseeded
  ground imports no structure (R3), and that it is generative (R4).
  None remains. R3 and R4 are theorems (Steps 3 and 4:
  `non_equivariant_names`, `generativity_is_saying_something`). R2 is
  dropped, and the result is stronger without it: well-foundedness
  excludes the clock *by name* — the chain refuting it is the
  alternation itself — and it takes out the contentless self-loop and
  the generative two-cycle with equal force, so it was never a filter
  on content, only on running at all (`wf_excludes_both`). Drop it and
  the shape arrives anyway, axiom-free, as a chain that closes into the
  cycle instead of resting on an unexplained unseeded floor
  (`eternal_shape`), where the old route needed `Classical.choice` to
  reach its terminus. R1's denial is a brute contingency — a fact whose
  demand for a ground goes unanswered — and this argument already has a
  name for facts not derivable from the law: records, whose
  underivability is a theorem (`SelfDerivation.lean`). The denial of R1
  does not embarrass the position; it populates it. What is lost is the
  old proposition's reach — it spoke of the demand chains of arbitrary
  existing things, and the replacements do not. That loss is real and
  is priced in *Why there are no premises*. The superseded conditional
  route survives in [`Regress.lean`](lean/Regress.lean) and still
  checks.
- **Grade 2** *(forced)* — needs no premise, only a tokening, which any
  objector supplies. It is the cogito, split: what is necessary is the
  *validity* of the seat's self-affirmation; that any particular
  carrier is inhabited stays contingent
  (`Cogito.existence_is_contingent`). Occurrence is affirmed, a bearer
  is not.
- **Grade 3** *(forced mathematics; interpretation on the reading)* —
  the kernel does not merely inspect the recursions it verifies, it
  *runs* them. Every check of `Becoming.lean` computes the two-tick
  clock. On the reading that a computation instances its process, the
  clock has run — as a side effect of checking this argument. The claim
  is not that the kernel's micro-physics is a two-tick clock, but that
  the process it realizes is, for all descriptive purposes, that clock:
  the run class has width one (`run_class_generated`), so every
  expressible distinction between the map and the run is settled and no
  vocabulary separates the territory from its law (`map_is_territory`).

The grades do not collapse and are never collapsed in summary. What the
argument does **not** have, at any grade, is a premise-free proof that
becoming is actual without remainder. It has a labelled ladder where
the classical arguments have a single unlabelled step — and now nothing
on the ladder is an assumption.

## The running diagonal

The engine of Steps 4–6 is one theorem: **Lawvere's fixed-point
diagonal at the fixed-point-free instance `f = not`** — the common core
of Cantor, Russell, Tarski, Gödel, and Turing
([`OneDiagonal.lean`](lean/OneDiagonal.lean) `lawvere`,
`diagonal_no_go`). The tradition reads these results as *limitative* —
walls around what systems can do. Read in the process frame the same
theorem is *generative*: the fixed point the diagonal refuses to a
state, the recursion grants — uniquely — to a process. `frames_one_fact`
makes wall and motor one hypothesis; `godel_is_clock` exhibits the
Gödel-style fixed point as the clock. One diagonal, run at five seats:

| Seat | Refused as a state (the wall) | Delivered as a process (the running) | Lean |
|---|---|---|---|
| The ground | a solution of `x = ¬x` | time: the unique two-tick clock | `TwoReadings.founding_two_readings`; `Loeb.godel_is_clock` |
| The ground's certificate | a faithful self-model | the aseity question, open in principle | `Aseity.no_self_model`, `aseity` |
| The describer | derivation of its own anti-diagonal record | novelty: value-class records, underivable in principle | `SelfDerivation.no_self_derivation`, `two_obstructions` |
| The chooser | a correct self-prediction | interior openness inside strict determinism | `FreeWill.never_foreknown`, `free_will_is_the_diagonal` |
| The doubter | a consistent total self-doubt | the undeniability of occurrence | `Cogito.the_gap`, `no_self_denial` |

*Priority.* Spencer-Brown's re-entrant mark oscillates, and
Kauffman–Varela read it as generating time; Yanofsky unified the
diagonal arguments; process primacy is ancient. To our knowledge no
prior argument derives an *existence verdict* from the diagonal's
refusal itself. The new parts are the uniqueness clause (Step 3), the
frame-correspondence biconditional (Step 6), the `godel_is_clock`
identification — and the discharge of every premise the derivation
once carried.

## Why there are no premises

Everything turns on what a premise is, so it is stated rather than left
to work in the dark.

> A premise is a proposition that the argument's claims depend on and
> whose negation is coherently assertable.

Under that criterion the count is zero. It is not reached by moving
assumptions into antecedents — relocating a hypothesis is not
discharging one — but by showing that each thing earlier versions
assumed is one of three things, none of them an assumption:

| Was | Verdict | Why | Carried by |
|---|---|---|---|
| R3 (the ground imports no structure = equivariance) | forced | A law on the bare distinction that fails to commute with the relabeling is a *constant*: it names a value. "Structureless but not equivariant" is not the case equivariance missed; it is the maximally structured one. | `Structureless.structureless_iff_equivariant`; `Articulation.non_equivariant_names` |
| R4 (the ground is generative) | forced | A structureless specification that excludes any state excludes them all. Generativity is what saying anything already amounts to; the static rival is the case where nothing was said. | `Articulation.generativity_is_saying_something`, `identity_is_mute` |
| R2 (the demand relation is well-founded) | dropped — the theorem is stronger without it | Well-foundedness excludes the clock *by name* and cannot tell the contentless loop from the generative cycle apart. Drop it and the shape arrives anyway, axiom-free. | `Eternal.eternal_shape`, `wf_excludes_both` |
| R1 (every demand for a ground is answered) | void | Its denial is a brute contingency: a fact whose demand goes unanswered. This argument calls such facts records and proves their underivability. The denial populates the position rather than embarrassing it. | `SelfDerivation.no_self_derivation` |
| The arena (unlisted: why two values?) | forced | One value is mute, three or more are mute, two speaks — and anything that speaks is on exactly two. | `Arena.arena_iff_two` |
| The seed (unlisted: which start?) | forced (a record) | The two runs are one run relabelled; naming the seed imports structure. Read, not assumed. | `Seed.absolute_class_is_a_point`, `naming_the_seed_imports` |

What remains at the bottom is Step 1, and it is not a premise under the
criterion, because its denial is not coherently assertable: to token
"no distinction is drawn" as opposed to its denial is to draw one. The
denial is unsayable rather than false.

Two objections deserve their answers in advance.

*Is zero even possible in principle?* One might suspect a theorem
forbids it — that any position joining mathematics to an interpretation
must keep at least one bridge row. No such theorem exists, and the
candidate for one is a disjunction whose left horn is live: each
proposition either factors through the vocabulary or is undecided by
it, and nothing forces the second horn. A proposition *constant on the
admissible class* factors through every vocabulary, including the one
that sees nothing — and by Step 7 every structureless proposition about
the founding runs is constant on its class. The horn where premises
live is empty ([`NoFloor.lean`](lean/NoFloor.lean)
`fork_is_not_a_floor`, `constant_is_expressible_everywhere`,
`structureless_needs_no_bridge`).

*Reject the criterion.* A reader may hold that "at least one
distinction is drawn" is an assumption like any other. Then the count
is one — but it is then one for *every* position whatever, including
"there is nothing", which must be tokened to be held; and on that
reading zero premises is not an unmet target but an incoherent one. The
criterion used here is the only one under which the question has an
answer, and it is not new: it is Aristotle's, against the denier of
non-contradiction, who must say something in order to deny anything
(*Metaphysics* Γ.4). The honest boundary is also proved rather than
waved at: a retorsion never binds a claim with an outside to stand on,
and every premise this argument used to carry was such an outside
(`Tokening.the_outside_is_the_premise`).

**What it cost.** The old Grade 1 said: given R1–R4, anything that
occurs grounds in the shape `x = ¬x` — a claim about the demand chains
of arbitrary existing things. Its replacements say: any absolute
articulation is already that shape, and the chain closes into the clock
whether or not it terminates. Neither reaches the grounding chains of
arbitrary things. That reach is lost — and what it cost to have was R1
and R2, hypotheses that claim a survey of the chain from outside, which
the wider corpus's own theorems say nobody is in a position to conduct.
Trading a claim about all chains for one that needs no survey is the
right trade. It remains a trade, and it is stated rather than hidden.

## Refutation vs. rejection

To **refute** the core is to find a kernel error: a second structureless
law with content, a static solution of `x = ¬x`, a second orbit from a
seed, a failure of the biconditional, a bare three-valued carrier on
which something structureless moves, or a structureless proposition
that separates the two seeds. Each is a definite mathematical event,
and each is where the argument *cannot* be attacked — the kernel has
checked its absence.

To **reject** the argument, now that no premise is on offer, is one of
two moves, and each has a stated price. Reject the criterion of what a
premise is — then every position, "there is nothing" included, carries
at least one, and the comparison of counts still favors this argument.
Or reject a marked reading — Grade 3's reading of a computation as
instancing its process, the naming of the process frame's parameter as
time — and each is tagged *interpretation*, with the mathematics
standing without it. There is no move that is both cheap and total.
That is the sense of the Gödel-tightness aimed at: not immunity from
disagreement, but disagreement forced to name its price.

## Checking it

Every file is standalone — Lean 4, prelude only, no imports — and checks
with plain `lean` under the pinned toolchain (`leanprover/lean4:v4.31.0`,
in `lean-toolchain`). Each ends by printing the axioms its results use.

```sh
lean lean/Becoming.lean                       # the assembled argument; prints "no axioms"
for f in lean/*.lean; do lean "$f" || break; done   # all twenty-one files
```

The full paper is in [`paper/becoming.tex`](paper/becoming.tex). The
wider process-metaphysics corpus these files are drawn from — with the
space, causation, mind, modality, and ethics results — lives in the
sibling `metaphys` repository.
