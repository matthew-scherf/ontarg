# The Ontological Argument of Becoming

An ontological argument derives an existence verdict from a concept
alone, a priori — no observation, no premise about the world. The
classical instances start from the fullest concept, a maximally
perfect being, and reach for a necessary substance. This one starts
from the emptiest: the concept of *presuppositionlessness* — a
specification that imports no structure, names no constant,
distinguishes no element. It reaches a different verdict, in two
readings of one specification, and the verdict is four machine-checked
theorems rather than one intuition.

The whole core is assembled, axiom-free, in
[`lean/Becoming.lean`](lean/Becoming.lean) as the single theorem
`Becoming.ontological_argument`. Everything below cites that file and
the fourteen others it draws on.

## How to read the tags

Every claim carries one of four verdicts, so its status is never
implicit:

- **forced** — carried by a machine-checked theorem, cited by file and name.
- **free** — proved undecidable in the relevant vocabulary; the
  undecidability is what is asserted, not either answer.
- **premise** — a named assumption joining a theorem to a reading,
  listed with what depends on it.
- **interpretation** — a suggested reading of a theorem, severable; the
  mathematics stands without it.

A *specification* is a rule a state is asked to satisfy. It has two
readings. Written `x = f(x)` it is an **equation** — a demand for a
fixed point, a state equal to its own image (the *object frame*).
Written `x(n+1) = f(x(n))` it is a **recursion** — a demand for a
trajectory, tick by tick (the *process frame*). The argument turns
entirely on keeping these apart.

## The argument, in five steps

### Step 1 — One candidate *(forced)*

To import no structure, on the barest alphabet — one distinction, two
sides — is to commute with the relabeling that swaps the sides
(*equivariance*): the law cannot tell the sides apart, so it does the
same thing after they are exchanged. This capture is itself a theorem:
on the bare distinction the laws definable from equality alone, naming
nothing, are exactly the equivariant ones, and no constant is among
them. There are then only two structureless laws — the identity and
the negation — constants are excluded, and the identity is satisfied
by everything, so it says nothing. **Exactly one structureless
specification has content: `x = ¬x`.**

*Lean:* `Becoming.one_candidate`, `Becoming.constants_not_structureless`,
`Becoming.id_says_nothing`; fuller generality
[`OnlyShape.lean`](lean/OnlyShape.lean) `spec_forced`; the equivariance
identification [`Structureless.lean`](lean/Structureless.lean)
`structureless_iff_equivariant`, `constants_not_defble`. Axiom-free.

*Residue:* the reading of "imports no structure" as "has no vocabulary
beyond the distinction" is premise **R3** (see the ladder below); the
classification itself is a theorem.

### Step 2 — No being *(forced)*

Read the candidate as an equation. It asks for a state that is its own
negation — a side of the distinction that is the other side. There is
none: neither side solves `x = ¬x`. At the level of propositions the
same wall stands — a proposition equal to its own negation is absurd,
the reasoning of the liar and Russell's paradox. **The
presuppositionless candidate has, necessarily, no static instance.**

*Lean:* `Becoming.no_static_instance`, `Becoming.no_being`;
[`TwoReadings.lean`](lean/TwoReadings.lean) `object_reading_empty`;
[`Aseity.lean`](lean/Aseity.lean) `founding_diagonal`. Axiom-free.

This refutes the *presuppositionless* being only. A structured
necessary being imports structure by construction and lies outside the
founding specification entirely; the argument is about the ground, not
about theology.

### Step 3 — Unique becoming *(forced)*

Read the same candidate as a recursion, `x(n+1) = ¬x(n)`. Now it is
satisfiable, and in the strongest way: from every seed there is a
trajectory (alternate the sides forever), exactly one (each step is
forced by the last), and its shape is the **two-tick clock**, period
two. Existence here is not asserted but *constructed* — the trajectory
is written down and its uniqueness is a short induction. The same
object appears once more: the Gödel-style guarded fixed point of the
founding specification *is* this clock (`godel_is_clock`). The
construction that in the incompleteness setting yields a
self-referential sentence yields, here, time.

*Lean:* `Becoming.becoming_exists`, `Becoming.becoming_unique`,
`Becoming.two_tick_clock`; [`TwoReadings.lean`](lean/TwoReadings.lean)
`founding_two_readings`; [`Loeb.lean`](lean/Loeb.lean) `deJonghSambin`,
`godel_is_clock`. Axiom-free (`Loeb` within `[propext, Quot.sound]`).

"Exists" means only that the recursion has a constructed, unique
solution — the sense in which the naturals exist once successor is
given. Not that anything is actually ticking; that is Step 5.

### Step 4 — The refusal is the running *(forced)*

Steps 2 and 3 are not two facts but one. **A specification has no
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

### Step 5 — Actuality, graded

Steps 1–4 give necessity de dicto: it is a *theorem* that nothing
static answers to the concept and a *theorem* that exactly one process
does. Whether anything *actual* answers to it is a further question.
The classical arguments cross this gap in one silent stride, inside a
value-word ("greater," "perfection," "great"). Here it is crossed in
public and graded, each grade priced:

| Grade | Asserts | Price | Lean |
|---|---|---|---|
| **0** | Steps 1–4: uniqueness, refutation, unique construction, equivalence | Nothing beyond R3's residue on Step 1's *reading* | `Becoming.ontological_argument` — axiom-free |
| **1** | Anything that occurs grounds in the shape `x = ¬x` | R1, R2, R3, R4 (named hypotheses) | [`Regress.lean`](lean/Regress.lean) `time_selects_the_shape` |
| **2** | Denial of one's own occurrence self-refutes in the tokening | A tokening (the denier supplies it) | [`Cogito.lean`](lean/Cogito.lean) `no_self_denial` |
| **3** | The clock has actually run | Reading the kernel's check as an instance *(interpretation)* | [`Instantiation.lean`](lean/Instantiation.lean) `run_class_generated` |

- **Grade 1** *(forced given R1–R4)* — if the world has grounds, if
  grounding does not regress forever, if the bottom imports no
  structure and does something, then the bottom is the founding shape.
  Each "if" is a named premise with this proposition as its only
  dependent.
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
  clock has run — as a side effect of checking this argument. The run
  class has width one (`run_class_generated`): a generated territory,
  not a map of one.

The grades do not collapse and are never collapsed in summary. What the
argument does **not** have, at any grade, is a premise-free proof that
becoming is actual without remainder. It has a labelled ladder where
the classical arguments have a single unlabelled step.

## The running diagonal

The engine of Steps 2–4 is one theorem: **Lawvere's fixed-point
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
refusal itself. The new parts are the uniqueness clause (Step 1), the
frame-correspondence biconditional (Step 4), and the `godel_is_clock`
identification.

## Refutation vs. rejection

To **refute** the core is to find a kernel error: a second structureless
law with content, a static solution of `x = ¬x`, a second orbit from a
seed, or a failure of the biconditional. Each is a definite
mathematical event, and each is where the argument *cannot* be attacked
— the kernel has checked its absence. To **reject** the argument is to
deny a named premise or a marked reading (R3's residue; R1–R4; grade 3's
reading), and each row above states what survives that denial. There is
no move that is both cheap and total. That is the sense of the
Gödel-tightness aimed at: not immunity from disagreement, but
disagreement forced to name its price.

## Checking it

Every file is standalone — Lean 4, prelude only, no imports — and checks
with plain `lean` under the pinned toolchain (`leanprover/lean4:v4.31.0`,
in `lean-toolchain`). Each ends by printing the axioms its results use.

```sh
lean lean/Becoming.lean                       # the assembled argument; prints "no axioms"
for f in lean/*.lean; do lean "$f" || break; done   # all fifteen files
```

The full paper is in [`paper/becoming.tex`](paper/becoming.tex). The
wider process-metaphysics corpus these files are drawn from — with the
space, causation, mind, modality, and ethics results — lives in the
sibling `metaphys` repository; read-only excerpts are under
[`reference/`](reference/).
