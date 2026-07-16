# Spec: The Ontological Argument of Becoming — paper and documentation

**Audience:** the model executing this spec (you). You are writing the
paper and top-level documentation for this repository. This spec is
binding. Where it prescribes wording, structure, claims, or
prohibitions, follow it exactly. Where it is silent, follow the
conventions of `reference/TREATISE.md` and `reference/paper.tex`. If
you find a factual error in this spec (a theorem name that does not
exist, a wrong axiom footprint), correct to what the repository
actually contains and record the correction in your final report —
never invent a theorem, never paper over a mismatch.

**This repository.** `becoming` is a standalone repository carved out
of a larger machine-checked process-metaphysics corpus (the `metaphys`
repository, a sibling directory; its treatise and systematic paper are
vendored read-only under `reference/`). Everything the argument needs
is already here: fifteen self-contained Lean 4 proof files in `lean/`
(prelude only, no imports, each checkable with plain `lean` under the
pinned toolchain in `lean-toolchain`), including `lean/Becoming.lean`,
which assembles the whole argument into one kernel-checked, axiom-free
theorem. You write prose; you do not write or modify Lean.

**Read before writing, in this order:**
1. This spec, fully.
2. `SKILL.md` (binding style rules).
3. `lean/Becoming.lean` (the argument's assembled proof — already
   kernel-checked, zero axioms; do not modify it).
4. The rest of `lean/`: `TwoReadings.lean`, `OneDiagonal.lean`,
   `Loeb.lean` (`godel_is_clock`), `OnlyShape.lean`,
   `Structureless.lean`, `Aseity.lean`, `Regress.lean`, `Cogito.lean`,
   `FreeWill.lean`, `SelfDerivation.lean`, `Instantiation.lean`,
   `RichAlphabet.lean`, `Modality.lean`, `Ledger.lean`.
5. `reference/TREATISE.md` (the parent position and its conventions —
   especially the tag discipline and the VI.7 scholium) and
   `reference/paper.tex` (the systematic paper; source of the LaTeX
   preamble conventions, reusable bibliography entries, and the vetted
   related-work claims).

---

## 1. Mission

The parent corpus contains, distributed across its files, a single
argument that has not yet been stated as one thing: **the Ontological
Argument of Becoming**. This repository exists to state it — in a
standalone paper and in repository documentation — with the precision
of the corpus and the lucidity of a paper written to be read.
Precision means: every mathematical claim cites a kernel-checked
theorem by file and name, and the status of every non-mathematical
claim is tagged. Lucidity means: a philosopher who has never seen Lean
can follow every step, because each formal move is expounded in plain
prose before it is cited.

The standard aimed at is the standard of Gödel's incompleteness
theorems — and the paper must say, once and exactly, what that
standard is: the mathematics is not up for debate (it is held by the
kernel, axiom-free at the core); the philosophical import is debatable
exactly at the named seams, and the seams are enumerated, priced, and
themselves covered by theorems (`Ledger.lean`:
`settling_needs_new_primitive`). Gödel-tightness is not "no one can
disagree"; it is "everyone can see precisely where disagreement is
possible, and it is nowhere in the derivation."

## 2. The argument (canonical statement — the paper's spine)

The paper presents exactly this argument, in exactly these five steps,
in this order. The step names below are the paper's internal names for
them. Wording of the surrounding prose is yours (within SKILL.md);
the content of each step is not.

**Definition (ontological argument).** An ontological argument derives
an existence verdict a priori, from a concept alone. The classical
instances start from the concept of a maximally perfect being. This
argument starts from the opposite pole: the concept of
*presuppositionlessness* — a specification that imports no structure,
names no constant, distinguishes no element.

**Step 1 — One candidate.** On the bare distinction, "imports no
structure" is captured by equivariance: the law commutes with the
relabeling (and this capture is itself grounded by a theorem — a law
is definable from the distinction alone, naming nothing, iff it is
equivariant: `Structureless.lean` `structureless_iff_equivariant`,
`constants_not_defble`, axiom-free). The structureless laws are exactly
the identity and the negation; constants are excluded; the identity is
satisfied by everything and so says nothing. Exactly one structureless
specification has content: `x = ¬x`.
*Lean:* `Becoming.one_candidate`, `Becoming.constants_not_structureless`,
`Becoming.id_says_nothing`; fuller generality `OnlyShape.spec_forced`.
*Tag:* forced, with the residual identification of "no structure" =
"no vocabulary beyond the distinction" named (this is premise R3's
residue; see §6).

**Step 2 — No being.** The candidate has, necessarily, no static
instance. As an equation over states, `x = ¬x` has no solution; at the
level of propositions, a proposition equal to its own negation is
absurd. The unique presuppositionless candidate provably fails to
exist as an object.
*Lean:* `Becoming.no_static_instance`, `Becoming.no_being`;
`TwoReadings.object_reading_empty`; `Aseity.founding_diagonal`.
Axiom-free. *Tag:* forced.

**Step 3 — Unique becoming.** Read the same specification as a
recursion over ticks, `x(n+1) = ¬x(n)`, and it has a solution from
every seed — by construction, not by postulate — exactly one solution
per seed, and that solution is the two-tick clock, period exactly two.
The guarded (Gödel-style) fixed point of the founding specification
exists, is unique, and *is* this clock.
*Lean:* `Becoming.becoming_exists`, `Becoming.becoming_unique`,
`Becoming.two_tick_clock`; `TwoReadings.founding_two_readings`;
`Loeb.deJonghSambin`, `Loeb.godel_is_clock`. Axiom-free (the `Loeb`
results within `[propext, Quot.sound]`). *Tag:* forced.

**Step 4 — The refusal is the running.** Steps 2 and 3 are not two
facts but one. A specification has no static solution if and only if
every orbit moves at every tick: the object frame's emptiness and the
process frame's perpetual motion are the same hypothesis, as a
biconditional. What refuses to *be* thereby *runs* — this is an
equivalence, not a metaphor.
*Lean:* `Becoming.refusal_is_running`; `TwoReadings.frames_one_fact`.
Axiom-free. *Tag:* forced.

**Step 5 — Actuality, graded.** What the first four steps establish is
necessity de dicto: it is a theorem that nothing static answers to the
presuppositionless concept and a theorem that exactly one process does.
Whether anything *actual* answers to it is a further question, and the
argument's honesty consists in grading it instead of leaping it. Three
grades, in ascending strength of assumption:

- **Conditional (premised).** If anything occurs, and grounding
  demands are answered (R1), well-founded (R2), with unseeded grounds
  structureless (R3) and generative (R4), then every demand chain
  terminates in a ground whose law is `x = ¬x`.
  *Lean:* `Regress.time_selects_the_shape`; premises as named
  hypotheses in the signature. *Tag:* forced given R1–R4.
- **Tokened (self-refuting to deny).** The denial of any token's
  occurrence refutes itself in the tokening; occurrence needs no
  bearer and cannot be coherently denied from where it occurs.
  *Lean:* `Becoming.denial_self_refutes`; `Cogito.no_self_denial`,
  `Cogito.cogito_valid_necessarily`. Axiom-free. *Tag:* forced; note
  the cap — validity is necessary, existence of any given carrier is
  contingent (`Cogito.existence_is_contingent`).
- **Enacted (the check runs the clock).** The kernel normalizes the
  recursions it verifies: every check of `TwoReadings.lean` and
  `Becoming.lean` actually runs the two-tick clock. The corpus is a
  generated territory — the class of runs of a known law from a known
  seed has width one, and over it the map–territory seam closes.
  *Lean:* `Instantiation.run_class_generated`,
  `Instantiation.map_is_territory`. *Tag:* forced mathematics; the
  reflexive reading is interpretation, exactly as in the treatise's
  VI.7 scholium (`reference/TREATISE.md`).

**Conclusion (the argument's verdict, to be stated in this form).**
From the concept of presuppositionlessness alone, it is a theorem that
nothing static answers to it and a theorem that exactly one process
does — and a theorem that these are the same fact. If an ontological
argument is an a priori derivation of an existence verdict from a
concept, this is one, with two inversions: it starts from the emptiest
concept rather than the fullest, and it ends in a becoming rather than
a being — the being-version is not merely unproven but refuted. Its
existential import is not smuggled in a definition of "perfection";
it is graded, and each grade is priced.

## 3. The novelty claim — the running diagonal

This is the paper's central contribution and gets its own section.
State it exactly at this strength, no higher, no lower:

The engine of Steps 2–4 is one theorem: Lawvere's fixed-point diagonal
(`OneDiagonal.lawvere`) at the fixed-point-free instance `f = not`
(`OneDiagonal.diagonal_no_go`) — the common core of Cantor's, Russell's,
Tarski's, Gödel's, and Turing's arguments. The tradition reads these
results as *limitative*: walls around what systems, sets, and theories
can do. The corpus's finding is that the same theorem, read in the
process frame, is *generative*: the fixed point the diagonal refuses to
a state, it grants — uniquely — to a process. `frames_one_fact` makes
wall and motor one hypothesis; `godel_is_clock` exhibits the Gödel-style
guarded fixed point as the two-tick clock. The diagonal does not only
bound being; run, it generates.

The section must include this table (prose around it is yours): one
diagonal, run at five seats —

| Seat | Refused as a state (the wall) | Delivered as a process (the running) | Lean |
|---|---|---|---|
| The ground | a solution of `x = ¬x` | time: the unique two-tick clock | `TwoReadings.founding_two_readings`; `Loeb.godel_is_clock` |
| The ground's certificate | a faithful self-model | the aseity question held open in principle | `Aseity.no_self_model`, `Aseity.aseity` |
| The describer | derivation of its own anti-diagonal record | novelty: value-class records, underivable in principle | `SelfDerivation.no_self_derivation`, `two_obstructions` |
| The chooser | a correct self-prediction | interior openness inside strict determinism | `FreeWill.never_foreknown`, `free_will_is_the_diagonal` |
| The doubter | a consistent total self-doubt | the undeniability of occurrence | `Cogito.the_gap`, `Cogito.no_self_denial` |

Priority hygiene: Spencer-Brown's re-entrant form oscillates and
Kauffman–Varela read it as generating time — cite both; what has no
precedent (this is already vetted wording from `reference/paper.tex`
§"What is new in content", item 1, and you may not strengthen it) is
the uniqueness clause (Step 1), the frame-correspondence biconditional
(Step 4), and the identification `godel_is_clock`. The paper may say:
to our knowledge, no prior argument derives an existence verdict from
the diagonal's refusal itself. It may not claim novelty for
process-primacy (Heraclitus, Whitehead), nor for oscillating re-entry
(Spencer-Brown), nor for machine-checking an ontological argument
(Benzmüller & Woltzenlogel Paleo).

## 4. Deliverables

**D1. `paper/becoming.tex`** — the paper. Take the LaTeX preamble,
theorem environments, `\dem{}` demonstration lines, and tag macros
from `reference/paper.tex` (copy and trim; do not redesign). Title,
exactly:

> **The Ontological Argument of Becoming**
> *A machine-checked existence argument from the concept of presuppositionlessness*

Length: 6,000–9,000 words. Section plan, binding:

1. **Introduction.** The classical arc in one page: Anselm's derivation
   of existence from the concept of that-than-which-nothing-greater;
   Gaunilo's parody; Aquinas's rejection; Descartes' restatement;
   Kant's diagnosis (existence is not a real predicate); Gödel's
   modal axiomatization; and the modern coda — mechanization by
   Benzmüller and Woltzenlogel Paleo confirming modal collapse and
   finding the inconsistency of Gödel's axioms. Then the turn: this
   paper runs the same ambition through the same modern instrument at
   the opposite pole, and the instrument's verdict inverts — the
   necessary *being* dies at the diagonal, and a necessary *becoming*
   survives it. One paragraph forecasting the five steps.
2. **Ground rules.** Compressed from `reference/paper.tex` §2: the
   kernel, the four tags (forced / free / premise / interpretation),
   standalone prelude-only files, axiom audits, what the certainty
   covers and what it does not. State the Gödel-tightness claim as
   worded in §1 of this spec. Note that this repository vendors
   exactly the fifteen proof files the argument uses, and that the
   full systematic position lives in the parent corpus.
3. **The argument.** Steps 1–4 as §2 above prescribes. Each step:
   plain-prose exposition first (a reader with no Lean must be able to
   reconstruct the mathematics from the prose), then the proposition
   in a numbered environment with its tag, then the `\dem{}` line, then
   one paragraph of "what this step does not say." For Step 1 that
   paragraph handles the R3 residue; for Step 2, that refutation here
   is of the *presuppositionless* being (a structured necessary being
   is untouched — the argument is about the ground, not about
   theology); for Step 3, that "exists" means the recursion has a
   constructed unique solution, nothing more; for Step 4, that the
   biconditional is doing the anti-equivocation work.
4. **The running diagonal.** §3 of this spec, with the table.
5. **Actuality, graded.** Step 5. The contrast to make explicit: every
   classical ontological argument takes the step from concept to
   actuality inside an unexamined premise (Anselm: existence-in-re is
   greater; Descartes: existence is a perfection; Plantinga: possibly,
   a maximally great being exists). This argument takes it three times
   in public, each grade with its exact price tag: four named premises,
   or a tokening, or the check itself.
6. **Necessity without a possibility premise.** The modal face. In the
   corpus's modality (S5 over the admissible class,
   `Modality.modality_is_S5`), Steps 1–4 are necessary in the only
   sense on offer: theorems, true over every admissible class. Contrast
   with the modal ontological arguments (Hartshorne, Malcolm,
   Plantinga), which require the premise "possibly, necessarily, p" and
   S5 to detach `p` — here S5 is proved, not assumed, and no
   possibility premise appears anywhere. Contrast with Gödel's modal
   collapse: in this system contingency is not collapsed but preserved
   as a proved third verdict (*free*, `Modality.verdict_trichotomy`).
7. **Objections and replies.** Exactly these seven, in this order,
   each with the reply this spec sketches (expand, don't weaken):
   1. *Equivocation* — "the argument trades on two senses of 'is'."
      Reply: the two readings are two formal frames of one
      specification, and their correspondence is itself a theorem
      (`frames_one_fact`); no step passes through natural language.
   2. *Triviality* — "it's a flip-flop." Reply: the mathematics is
      deliberately small and fully visible; the force is the
      conjunction — uniqueness of the candidate, the refutation, the
      unique construction, the biconditional — each axiom-free. Small
      and checked beats deep and disputed; the diagonal core of the
      incompleteness theorems is also small. Alphabet-enrichment
      escapes are closed (`RichAlphabet.no_rich_separation`,
      `escape_closed`).
   3. *The load is in R3* — "structureless = equivariant smuggles the
      conclusion." Reply: grounded by `structureless_iff_equivariant`
      (definability from pure equality; axiom-free); the residue is
      named and the argument survives as a conditional under any
      reading of it.
   4. *Kant* — "existence is not a predicate." Reply: obeyed, not
      evaded. Existence never occurs as a predicate in the argument:
      the object-frame verdict is a refutation, and the process-frame
      verdict is a construction (`orbit`, `gfix`) — existence enters
      exactly the way Kant permits, by exhibition.
   5. *Gaunilo* — "run the parody: a perfect island." Reply: the
      parody is blocked by a theorem. Step 1 is a uniqueness clause;
      any rival candidate imports structure, and importing structure
      is checkable (`constants_not_structureless`; `Structureless`).
      The classical argument fell to parody because nothing
      individuated its concept; this one's concept is individuated by
      classification.
   6. *No actuality* — "nothing shows anything actually runs." Reply:
      correct as far as grade 0 goes, and the grading is the answer —
      state which grade buys what at which price; note the classical
      arguments took the same step tacitly.
   7. *Why "ontological"* — "this is not what the word means." Reply:
      the definitional criterion (a priori, from a concept, to an
      existence verdict) is met; the differences — emptiest concept
      rather than fullest, becoming rather than being, graded rather
      than smuggled actuality — are the finding, not a
      disqualification.
8. **Relation to the literature.** Two lineages. (a) The ontological
   lineage: Anselm, Gaunilo, Aquinas, Descartes, Kant, Hegel,
   Hartshorne, Malcolm, Plantinga, Gödel, Sobel, Oppenheimer & Zalta,
   Benzmüller & Woltzenlogel Paleo, with Oppy's survey for taxonomy.
   Hegel gets a full paragraph, as the nearest precedent in content:
   the opening of the *Logic* — pure being, wholly indeterminate,
   passes into nothing, and their truth is becoming. This argument is
   that move with the assertion replaced by two theorems and a
   biconditional: indeterminacy (structurelessness) provably yields no
   being-instance and provably yields a unique becoming-instance, and
   the passage between the verdicts is `frames_one_fact`. What Hegel
   narrated, the kernel checks — and what the kernel cannot check
   (that our world is an instance) is named rather than narrated.
   (b) The process/formal lineage: compress from `reference/paper.tex`
   §Related (Heraclitus, Spencer-Brown, Kauffman–Varela, Whitehead,
   Lawvere, Yanofsky's unification of the diagonal arguments). Reuse
   `reference/paper.tex` bibliography entries verbatim where they
   exist; add: Anselm (*Proslogion*, c. 1077), Gaunilo (*Pro
   Insipiente*), Aquinas (*Summa Theologiae* Ia q.2 a.1), Hegel
   (*Wissenschaft der Logik*, 1812), Malcolm ("Anselm's Ontological
   Arguments," Phil. Review 69, 1960), Hartshorne (*The Logic of
   Perfection*, 1962), Plantinga (*The Nature of Necessity*, 1974),
   Sobel ("Gödel's ontological proof," in *On Being and Saying*,
   1987), Oppy (*Ontological Arguments and Belief in God*, 1995),
   Yanofsky ("A universal approach to self-referential paradoxes,
   incompleteness and fixed points," Bull. Symbolic Logic 9(3), 2003).
9. **What is claimed and what is not.** A short section with two lists.
   Claimed: the five steps at their tagged strengths; the novelty as
   worded in §3. Not claimed: see §5 prohibitions — render them as
   first-person disclaimers ("this argument does not show...").
   Include the argument's premise table from §6 of this spec, plus the
   note that grade-0 steps depend on no premise at all. Close with the
   refutation discipline: what would count as refuting this argument
   (a second structureless contentful law; a static solution; a second
   solution from a seed; a failure of the biconditional — each of
   which would be a kernel error, i.e., the mathematics is where it
   *cannot* be refuted) versus what would count as rejecting it
   (denying a named premise or reading — each row listing what
   survives).
10. **Conclusion.** One page. The inversion stated once more, plainly;
    the grade ladder; the last sentence should land on the running
    diagonal, not on a flourish.

**D2. `ARGUMENT.md`** — new top-level document, the argument in
repository form. 1,500–2,500 words. Structure: the definition; the five
steps, each with its plain statement, tag, and Lean citations (file +
theorem names, as links into `lean/`); the running-diagonal table; the
grade ladder; the premise subset; a "checking it" section (the two
commands: `lean lean/Becoming.lean`, and the loop over `lean/*.lean`).
Same tag discipline as `reference/TREATISE.md`. This document must
stand alone: a reader who reads only `ARGUMENT.md` and
`lean/Becoming.lean` gets the whole argument.

**D3. `README.md`** — write fresh (this repository has none). Model it
on the parent corpus's README register. Contents: one paragraph saying
what this repository is (one argument, machine-checked, assembled in
`lean/Becoming.lean`, presented in `ARGUMENT.md` and
`paper/becoming.tex`); a contents table (`ARGUMENT.md`, `lean/` —
fifteen standalone Lean 4 proof files, prelude only, no imports;
`paper/`, `reference/` — read-only excerpts from the parent corpus;
`SKILL.md`, `lean-toolchain`); a "Checking the proofs" section (plain
`lean` per file, pinned toolchain `leanprover/lean4:v4.31.0`, axiom
audits printed at end of each file, `Becoming.lean` axiom-free); the
tag conventions in brief; and a pointer to the parent corpus
(`metaphys`, sibling repository) for the full position and its ethics.

## 5. Claim discipline (binding prohibitions)

Never, in any deliverable:

1. **No theology.** Do not identify the ground with God, do not use
   the word "God" outside the discussion of the classical arguments,
   and state explicitly (Objection/§9) that the argument neither
   supports nor opposes any theological conclusion — Step 2 refutes
   only the *presuppositionless* being.
2. **No unconditional actuality.** Never write "becoming necessarily
   exists" or "the universe is the clock" without the grade
   qualification. The grade ladder may never be collapsed, summarized
   away, or demoted to a footnote.
3. **No unchecked mathematics.** Every mathematical assertion cites an
   existing theorem by file and name. If you want a claim with no
   theorem, it is a premise or an interpretation and must be tagged.
   You may not add new Lean files or modify existing ones.
4. **No tag inflation.** *Forced* only with a citation and only for the
   theorem's exact content; readings are *interpretation*; named
   assumptions are *premise* with their dependents stated.
5. **No priority inflation.** Novelty claims only as worded in §3.
   "To our knowledge" on every priority claim. Nothing "solves" the
   ontological argument debate; the paper relocates it and says where
   it moved.
6. **No hedging theater either.** The inverse failure is also barred:
   where a step is axiom-free and kernel-checked, say so flatly and
   move on. "It seems," "arguably," "one might say" are banned within
   the five steps.

## 6. The argument's premise accounting (for §9 of the paper and ARGUMENT.md)

| Grade | What it asserts | Price | Lean |
|---|---|---|---|
| 0 | Steps 1–4: uniqueness, refutation, unique construction, equivalence | Nothing beyond the R3 residue on Step 1's *reading* (the mathematics of all four steps is premise-free) | `Becoming.ontological_argument` (axiom-free) |
| 1 | Anything that occurs grounds in the shape | R1, R2, R3, R4 (named hypotheses in the signature) | `Regress.time_selects_the_shape` |
| 2 | Denial of occurrence self-refutes in the tokening | A tokening (supplied by the denier) | `Cogito.no_self_denial` |
| 3 | The clock has actually run | Reading the kernel's check as an instance (interpretation, as in the treatise's VI.7 scholium) | `Instantiation.run_class_generated` |

## 7. Style (binding)

1. **Apply `SKILL.md` in full**, including the self-edit pass, to every
   deliverable. The paper is formal register — human voice there means
   varied rhythm, committed claims, and concrete nouns, not
   colloquialism.
2. **Expound, then cite.** Every proposition is preceded by prose that
   would let a careful reader reconstruct the formal statement. Never
   let notation carry meaning prose hasn't already carried.
3. **Define before use.** Specification, frame, orbit, seed,
   structureless, equivariant, forced/free/premise/interpretation,
   diagonal — each defined at first occurrence. The Lawvere theorem is
   stated with its two-line proof idea (the diagonal `g a := f (e a a)`)
   in the running-diagonal section.
4. **One idea per paragraph; short sections.** The reader must always
   know which step they are inside.
5. **Every claim checkable in under a minute:** file + theorem name at
   the point of use, not gathered in an appendix.
6. **No em-dash pivots into grandeur, no "profound," no "remarkable."**
   The material carries itself; adjectives subtract.

## 8. Verification protocol (run all; the job is not done until all pass)

1. `lean lean/Becoming.lean` — every `#print axioms` line reports
   "does not depend on any axioms."
2. `for f in lean/*.lean; do lean "$f" || break; done` — all fifteen
   files check (you changed no Lean, so this is a smoke test).
3. Citation audit: every theorem name cited in `paper/becoming.tex`,
   `ARGUMENT.md`, and `README.md` exists in `lean/` — extract the
   `\lf{...}` names and backtick-names and check each against the
   corpus with grep.
4. `pdflatex` twice on `paper/becoming.tex` from `paper/`; no errors;
   resolve all undefined references; commit the built
   `paper/becoming.pdf`.
5. Claim audit: reread §5; search your own text for "God," "proves
   that," "necessarily exists," "first ever," and confirm each
   occurrence complies.
6. SKILL.md self-edit pass on all three deliverables.
7. Report: list deliverables, verification results, and any spec
   corrections made under the rule in the preamble.

## 9. Out of scope (do not touch)

Every existing file in `lean/` including `Becoming.lean`; everything
under `reference/`; `SKILL.md`; `lean-toolchain`; this spec. The
sibling `metaphys` repository is read-only context and must not be
modified in any way. No new Lean files. Commit the three deliverables
and the built PDF to this repository when done; nothing else.
