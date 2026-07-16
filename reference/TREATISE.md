# Metaphysica, ordine mechanico demonstrata

*A machine-checked process metaphysics.*

A process metaphysics whose central claims are Lean theorems. This
document states the position and points each claim at its proof. The
proofs live in [`lean/`](lean/). A companion ethics is in
[`ETHICA.md`](ETHICA.md), and a paper version in [`paper/`](paper/).

---

## Overview

The position is a process metaphysics. What exists is a running, not a
collection of things. Everything else here grows from a single formal
observation about the specification `x = ¬x`. Read as an equation over
states, it has no solution. Read as a recursion over time steps, it has
exactly one: an alternating two-tick clock (Proposition I.2). And among
specifications that assume no structure at all, it is the only one that
says anything (I.1). So if there is a structureless place to begin,
this is it — and it can only run.

The rest of the document works out what follows, keeping proved
claims, assumptions, and suggested readings clearly separated:

- The order of time is the only strict order compatible with a short
  list of ordering properties (II.1). Presenting the founding
  distinction at a tick takes at least two loci — a structureless
  reading over one locus is constant, on any alphabet its relabelings
  sweep — and even the stored record by which the clock shows its mark
  at a tick is a two-locus configuration. That is space, on this
  account: the other realization of the one shape, forced to exist and
  free in its arrangement, where time is forced in both (II.2–II.4).
  Records, in a simple register model, are write-once and not
  derivable from the law; that is the sense in which novelty is
  structural rather than apparent (II.5–II.8). And determination runs
  forward and not back, under every law — the causal arrow is the
  direction of functional dependence, not an asymmetry premise (II.9).
- Causation is the reads relation, and it needs no glue: correlation
  and causation come apart at a constructed confounder, with
  intervention — not observation — as what separates them (IV.5).
  Composition is the same mechanism run the other way: the joint of
  two readings always exists, is canonical, and expresses binding
  facts neither part can state, while no composite is an entity
  (IV.6).
- The modality of the position is S5 over the admissible class, with
  contingency the verdict *free*; counterfactuals evaluate at unique
  runs, so no similarity order is needed — though which law is
  running, and hence which counterfactuals hold, is underdetermined by
  the complete actual history (VI.4–VI.5).
- Several traditional questions — whether the whole is experiencing,
  whether the ground is fundamental, whether the world is discrete at
  the bottom, whether some other system is conscious — turn out to be
  undecidable in any structural vocabulary, provably. The position
  leaves them open rather than picking a side, and treats the
  undecidability itself as the finding (Parts III–V).
- Boundaries between streams are properties of the law, and they do
  not survive composition, so nothing in the formalism plays the role
  of a persistent self. What does survive is occurrence: that
  something is happening at a seat is valid wherever it occurs, and
  needs no bearer (Part IV).
- Determinism and openness-from-inside are two readings of one
  operator, which removes most of what the free-will debate was about
  (VI.3).

The theorems are about formal structures. Where a proposition needs
more than the mathematics — an identification, a reading, a named
hypothesis — that surplus is a listed assumption, collected in
*Premises* together with what depends on each.

---

## How to read this document

**Proofs.** Every proposition cites the Lean theorems that carry it.
Each file in `lean/` is self-contained — Lean 4, prelude only, no
imports — and checks with plain `lean` under the pinned toolchain
(`leanprover/lean4:v4.31.0`). Each file ends by printing the axioms
its main results use (`#print axioms`); the footprint is stated in the
file header and tabulated in Appendix A. Many results use no axioms at
all, and none goes beyond `[propext, Classical.choice, Quot.sound]`.

**Tags.** Every claim carries one of four tags, so its status is never
implicit:

- **forced** — carried by a machine-checked theorem.
- **free** — proved undecidable in the relevant vocabulary. What is
  asserted is the undecidability, not either answer.
- **premise** — a named assumption joining a theorem to an informal
  reading. Each is listed in the premise table with what depends
  on it.
- **interpretation** — a suggested reading of a theorem, marked as
  such. The mathematics stands without it.

**Scope.** Every proposition in Parts I–VI is an unconditional theorem
— about any process, any vocabulary, any observer — except where a
named premise appears in its statement. The position makes no claim
that our world in particular is an instance of the substrate; the
premises are the complete list of what it assumes beyond the
mathematics.

**Definitions** (used throughout; formal versions in the cited files):

1. A *history* is an unending assignment `Nat → A` of alphabet values
   to ticks.
2. An *observable of depth k* is a map on histories invariant under
   agreement on the first `k` ticks.
3. A *seat* is an index from which a quantity is read; a quantity is
   *form-class* when all seats read it identically, *value-class* when
   two seats disagree.
4. A *vocabulary* is a map `v : W → Obs` from worlds to what a theory
   sees of them; a proposition is *expressible* in `v` when its truth
   factors through `v`.
5. A proposition over a world class is *forced* when true in every
   admissible world, *refuted* when false in every one, *free* when
   both values occur.
6. Stream `j` is *blind* to stream `i` under a law when no change at
   `i` moves `j`'s next value; `j` *reads* `i` otherwise.
7. A *configuration* is an assignment `ι → A` of alphabet values to
   loci; a configuration *presents the mark* when two of its loci read
   different values.

---

## Part I — The Ground

**Proposition I.1 (One shape).** Call a specification structureless if
it imports nothing — names no constant, singles out no element.
Formally, that means its law commutes with every relabeling of the
alphabet. On the bare distinction only two maps do that: the identity
and the negation. The identity holds of everything, so it says nothing.
That leaves exactly one structureless specification with any content:
`x = ¬x`. *(forced)*

*Proofs.* `lean/OnlyShape.lean`: `equivariant_endomaps`,
`constants_not_equivariant`, `equivariant_endomaps_V3`,
`id_generates_nothing`, `spec_forced`. Axioms: within `[propext]`.
The identification of "structureless" with "equivariant" (premise R3)
is itself grounded by a definability theorem:
`lean/Structureless.lean`: `structureless_iff_equivariant` — on the
bare distinction, a law is definable from the distinction alone (from
pure equality, naming nothing) iff it is equivariant, and no constant
law is so definable (`constants_not_defble`). Axiom-free.

**Proposition I.2 (Becoming is primary).** The founding specification
has no static solution at all. Give it a seed, though, and it has
exactly one running solution. As an equation over states, `x = ¬x`
cannot be satisfied. As a recursion over ticks it is satisfied
uniquely, and its orbit is the two-tick clock. *(forced)*

*Proofs.* `lean/TwoReadings.lean`: `object_reading_empty`,
`process_reading_inhabited`, `process_reading_unique`,
`founding_two_readings`; `lean/OneDiagonal.lean`. Axiom-free.

**Proposition I.3 (The frame correspondence).** A specification is
restless — its object frame is empty — exactly when every orbit moves
at every tick. So the absence of solutions and the perpetuity of motion
are the same hypothesis seen in two frames. That they coincide is a
theorem, not an analogy. *(forced)*

*Remark.* Diagonal "limitation" results limit the object reading, not
the process: what fails as a completed totality is, in the process
frame, the guarantee that the process never halts. *(interpretation)*

*Proofs.* `lean/TwoReadings.lean`: `frames_one_fact`,
`object_solution_iff_fixed_orbit`. Axiom-free.

**Proposition I.4 (The regress terminates in the one shape).** Grant
four named premises: every seeded specification's demand for a ground
is answered (R1); that demand relation is well-founded (R2); an
unseeded ground imports no structure, i.e. is equivariant (R3); and an
unseeded ground is generative — its law moves something (R4). Then
every specification's demand chain terminates in a ground whose law is
`x = ¬x`. So if anything occurs at all, its chain grounds in that
shape. *(forced given R1–R4)*

*Proofs.* `lean/Regress.lean`: `regress_terminates`,
`ground_has_one_shape`, `time_selects_the_shape`; the premises are
hypotheses in the signatures. Axioms: within
`[propext, Classical.choice, Quot.sound]`.

**Proposition I.5 (No self-certificate of the ground).** No description
type can name and decide every predicate about itself. So no consistent
system settles, from inside, whether it is the fundamental ground or the
image of some deeper level. The ground's aseity is open in principle,
not merely in practice. *(forced; the answer is free)*

*Proofs.* `lean/Aseity.lean`: `founding_diagonal`, `no_self_model`,
`aseity`. Axiom-free.

---

## Part II — Time, Space, Records, Novelty

**Proposition II.1 (The order of time is unique).** Fix the strict
orders on tick counts that are irreflexive, transitive, total on
distinct elements, and translation-invariant. Exactly one of them is
well-founded: the standard order. And well-foundedness is not a further
thing to assume — it is interderivable with Löb's rule, and so with
induction. *(forced)*

*Proofs.* `lean/OrderForced.lean`: `order_is_forced`,
`reverse_is_not_wellfounded`; `lean/Loeb.lean`: `loeb_iff_induction`,
`deJonghSambin`, `godel_is_clock`. Axioms: within
`[propext, Quot.sound]`.

**Proposition II.2 (Multiplicity is forced).** A structureless reading
over a single locus is constant. On one bit, invariance under the
relabeling runs the two sides together; in configuration form, any
relabel-invariant predicate over one locus takes the same truth value
everywhere. Over two loci the situation reverses: the edge mark — "the
loci differ" — is itself structureless, and it realizes the
distinction, holding of a complementary configuration and failing of a
uniform one. Nor does a richer alphabet buy the second locus back. On
any alphabet whose structureless relabeling reaches every value — the
two-element and the four-element alphabets are instances — a
single-locus reading invariant under it separates nothing; an alphabet
that blocked the sweep would name an element, which is importing
structure. So wherever the founding distinction is presented at a tick
(premise R5), there are at least two loci, and the second locus is
irreducible. *(forced given R5)*

*Proofs.* `lean/Multiplicity.lean`: `one_locus_blind`,
`one_locus_constant`, `edge_structureless`, `edge_realizes`,
`multiplicity_forced`; `lean/RichAlphabet.lean`:
`invariant_transitive_constant`, `no_rich_separation`,
`escape_closed`. `Multiplicity` within `[propext, Quot.sound]`;
`RichAlphabet` axiom-free.

**Proposition II.3 (One shape, two readings).** The complementary pair
— the shape the founding law runs — is realized two ways: across loci,
as an edge at a tick, and across ticks, as the clock. And the fork is
ordered. The bare clock's state at a tick is a single locus and
presents nothing; to present its mark at a tick it must store the
predecessor, and the stored state is already a two-locus
configuration. A static pair of loci, by contrast, presents the mark
with no dynamical law at all. Record-at-a-tick embeds a spatial pair;
spatial-at-a-tick embeds no history. *(forced)*

*Remark.* Read the loci as space and the ticks as time. The two are
then not two substrates but two realizations of the one shape, and the
embedding runs one way. Becoming stays primary in the generative order
— the ground can only run (I.2). Presentation is spatial before it is
historical: even the record by which the running shows itself at a
tick is a pair of places. *(interpretation)*

*Proofs.* `lean/Multiplicity.lean`: `spatial_pair`, `temporal_pair`,
`one_shape_two_readings`; `lean/Priority.lean`: `unit_never_presents`,
`clock_bare_tick_blind`, `stored_presents`, `stored_is_two_locus`,
`space_static_presents`, `space_prior`. `Priority` axiom-free; the
fork within `[propext]`.

**Proposition II.4 (Time is forced, space is free).** The four order
axioms — irreflexivity, transitivity, totality on distinct elements,
translation-invariance — are satisfied by the forward order and by its
reverse alike, and the two disagree, so without well-foundedness the
axioms pin nothing. Well-foundedness holds forward, fails in reverse,
and by II.1 is interderivable with induction: it is the whole
difference. A cycle, finally, can be no strict order at all, so the
ring is an arrangement open to what lacks the induction mandate and
closed to what carries it. The reading that reasons by induction has a
forced arrow; the reading that does not is free in its arrangement.
*(forced; the naming of the free reading as space, interpretation)*

*Proofs.* `lean/SpaceOrder.lean`: `fwd_axioms`, `rev_axioms`,
`space_order_free`, `fwd_wf`, `rev_not_wf`, `cycle_not_strict`,
`time_forced_space_free`. Axioms: within `[propext, Quot.sound]`.

**Proposition II.5 (Records are write-once).** Take a register that
writes slot `t` at tick `t` and touches nothing else. It is a
write-once, prefix-determined, monotone log. Its content at each slot
depends only on the trajectory prefix up to the write tick; it is never
overwritten; the written region only grows. And none of this requires
an irreversible dynamics — a reversible global law coexists with the
monotone structure. The asymmetry lives in the records, not the law.
*(forced)*

*Proofs.* `lean/RecordMonotone.lean`: `write_untouched`,
`record_content`, `record_permanent`, `written_monotone`, `write_once`.
Axioms: within `[propext]`.

**Proposition II.6 (Persistence requires interaction).** On a
non-interacting sector, no finitely-supported state survives the
dynamics — not exactly, not up to a phase, not even after arbitrarily
many ticks. Concretely, a drift eigenvector with bounded support is
zero. So an entity here is a persistence that interaction keeps
renewing. Substance is not a primitive. *(forced)*

*Proofs.* `lean/NoFreeRecords.lean`: `no_drift_eigenvector`,
`no_free_pair_record`. Axioms: within `[propext]`.

**Proposition II.7 (The form/value split).** Quantities come in two
kinds. Form-class ones read identically from every seat; these are
exactly the law-derivable quantities. Value-class ones are
seat-relative and, in principle, not derivable from the law. There is a
further twist. Whether a given reading is pinned by the law or merely
recorded cannot be settled at any finite depth, because the same
seat-history occurs under a law that pins it and under a law that only
records it. The split even survives self-inclusion: a describer whose
own procedures are quantities over seats still cannot derive its
anti-diagonal record at any seat, by any procedure. *(forced)*

*Proofs.* `lean/ValueForm.lean`: `form_iff_derivable`,
`value_not_derivable`, `status_underdetermined`, `no_status_decider`;
`lean/SelfDerivation.lean`: `repertoire_incomplete`,
`no_self_derivation`, `repertoire_escape`, `two_obstructions`.
Axiom-free.

*Scholium.* The split lands on a constant of nature. Take one law and
the family of its runs, indexed by seed. A quantity that varies across
runs — a constant the law does not fix — is value-class: seat-relative,
a record read from whichever run one is in, with no law-side
derivation. The law itself, and the seed-to-run map, are form-class,
the same from every run. So what a law leaves unfixed is not missing
from the world; it is written into it, exactly as `value_not_derivable`
requires. *(forced)*

*Proofs.* `lean/Constant.lean`: `constant_is_value`, `law_is_form`,
`map_is_form`, `constant_not_derivable`, `priced_collapse`,
`constant_is_record`. Axiom-free.

**Proposition II.8 (Novelty is structural).** Every record is at once
new (value-class, so not law-derivable), permanent (write-once), and
interaction-born (absent from the free sector). Novelty, then, is not
an appearance thrown up by ignorance of the law. It is what value-class
facts are. *(forced)*

*Proofs.* Conjunction of II.5, II.6, II.7.

**Proposition II.9 (The causal arrow).** Fix any law on states and
run it. Two runs that agree at a tick agree at every later tick: the
present screens off the past, under every law. The converse fails:
some law sends two states to one, so the future does not pin the
past. Determination is temporally asymmetric — not by an asymmetry
premise, but because a law is a function, and a function has a
direction. *(forced; the causal naming, interpretation)*

*Proofs.* `lean/Causation.lean`: `forward_determined`,
`past_not_determined`, `causal_arrow`. Axiom-free.

---

## Part III — The Limits of Observation

**Proposition III.1 (Completed totalities carry no observational
weight).** Every finite-depth observable is a function of a finite
prefix. Past any given depth, all continuations read equal, and
completions of the alphabet are invisible. Even the universally
quantified predicate "this value at every tick" is an observable at no
depth. So anything measured is a fact about a finite prefix, and no
measurement bears on the completed whole. *(forced; the measurement
reading on O)*

*Proofs.* `lean/Totalization.lean`: `depth_factors`,
`continuations_indistinguishable`, `completion_invisible`,
`no_finite_depth_detects_forever`; `lean/CompletionFree.lean`:
`depth_k_finite`, `completion_invisible`. Axioms: within `[propext]`;
the schema file's core results are axiom-free. The finite-depth
notion itself is robust: `lean/Continuity.lean` proves finite depth,
uniform continuity on histories, and finite-prefix factorization one
class (`uniform_iff_depth`, `factors_iff_depth`), and locates the
boundary — pointwise continuity is strictly weaker over an infinite
alphabet (`continuity_strictly_weaker`). Axioms: within
`[Quot.sound]`; core results axiom-free.

**Proposition III.2 (Horizon quantities).** Nonconstant tail
functionals exist — quantities that stay invariant whenever two
histories agree from some point on. Anything both finite-depth and tail
is constant, so a nonconstant horizon quantity is an interior
observable at no depth. It is well-defined on histories yet never the
content of a finite-depth measurement. *(forced)*

*Proofs.* `lean/Horizon.lean`: `constant_iff_both`, `eventually_tail`,
`eventually_nonconstant`, `horizon_not_interior`. Axioms: within
`[propext]`.

**Proposition III.3 (The cutoff is interior-undecidable).** Any two
resolution cutoffs at or above an observer's own resolution give
identical measurements. The no-cutoff substrate, likewise, matches
every discrete one resolved finely enough. So the discreteness scale
can be bounded from above but never measured from inside, and finite
data never excludes the continuum. *(forced; the answer is free)*

*Proofs.* `lean/PlanckFree.lean`: `cutoff_invisible`,
`continuum_consistent`, `no_finite_cutoff_forced`. Axiom-free.

**Proposition III.4 (The geometry beyond the window is free).** A
geometry is an adjacency relation on loci, and an observer reads it
through a window. Two geometries that agree on the window are
identical to every window-supported reading, whatever it computes —
and they can differ beyond it by a topology. The line, and the line
closed into a ring four loci past the window, are one geometry to
every interior reading and two geometries in fact. So the global
arrangement, the topology, and any dimension-like invariant computed
from adjacency beyond the window can be bounded from inside but never
measured — the spatial face of III.3. *(forced; the window reading is
the spatial face of premise O)*

*Proofs.* `lean/DimensionFree.lean`: `window_agree`,
`beyond_window_invisible`, `geometries_differ`, `ringed_cycle`,
`dimension_beyond_window`. Axioms: within `[propext, Quot.sound]`;
the instance facts axiom-free.

---

## Part IV — Seats and Streams

**Proposition IV.1 (The self is a process-knot).** The guarded
self-model of any loop has exactly one fixed point — existence by
guarded recursion, uniqueness by Löb's rule. A self held statically
equal to its own model is only the vacuum. No loop completes its own
self-map. And systems observationally identical at every depth are
equal. Identity, on this account, is specification plus records.
Require it to hold still and it collapses to nothing. *(forced)*

*Proofs.* `lean/InteriorExperience.lean`: `unity`,
`duplicate_is_identity`, `no_static_self`, `gap_forced`,
`zombie_incoherent`, `other_minds_free`, `mind_count_free`. Axioms:
within `[propext, Quot.sound]`.

**Proposition IV.2 (Boundaries without bearers).** A stream is blind to
another when the law factors through a vocabulary that forgets that
other. So a boundary is a property of the law, borne by no entity. And
it does not compose: a stream blind to a source at each of two ticks
can still read it, through a mediator, in the composite. Boundaries are
tick-local, streams interpenetrate, and at the top there is no
self-model (I.5). No persistent self appears at any scale. The streams
within the process do the work. *(forced)*

*Proofs.* `lean/Streams.lean`: `blind_iff_factors`,
`reads_not_expressible`, `boundaries_leak`; `lean/Aseity.lean`:
`no_self_model`; instance at every width: `lean/Family.lean`:
`family_control_fails_noci_blindness`. Envelope
`[propext, Quot.sound]`; `boundaries_leak` axiom-free.

**Proposition IV.3 (Seated occurrence).** For any token of any type,
its occurrence is certain and its denial self-refutes — and this is
provable with no instance in hand. That any token exists, by contrast,
is contingent and cannot be proved. So the validity is necessary while
the existence is not, and nothing in the validity calls for a bearer.
The *who* dissolves (IV.2); the *where* does not. Occurrence is valid
wherever it occurs, with no tenant. *(forced)*

*Proofs.* `lean/Cogito.lean`: `cogito`, `no_self_denial`,
`existence_is_contingent`, `cogito_valid_necessarily`,
`cogito_ergo_sum`. Axiom-free.

**Proposition IV.4 (The indexical is a value).** No reading that
identifies two distinct worlds is total. Interior readings do identify
worlds (III.1), so no interior reading is total. Assume the law reads
every seat alike — the homogeneity premise. Then the indexical
"here = this seat" comes out free, inexpressible in the law-vocabulary,
and value-class. The you-are-here fact is a record: real, seat-relative,
underivable. It is not missing from the law, but neither is it the kind
of thing the law could contain. *(forced given the homogeneity
premise)*

*Proofs.* `lean/Occurrence.lean`: `no_total_reading`,
`indexical_is_value`. Axiom-free.

**Proposition IV.5 (Causation without glue).** Causation, in this
vocabulary, is the reads relation: an intervention at one stream that
moves another's next value. And reading is exactly the failure of the
law to factor through the vocabulary that forgets the source (IV.2),
so the causal structure of a process and its boundary structure are
one mechanism. Causation comes apart from correlation provably: two
streams that copy a common source agree at every tick past the seed
while neither reads the other, and what separates the pairs is
intervention, not any observation of the run. Mediation is already
priced — per-tick blindness does not compose (IV.2) — so causal
boundaries are tick-local like all boundaries. No glue, power, or
necessitation appears anywhere in the definitions; the law's
factorization structure does all the work. *(forced; the causal
naming, interpretation)*

*Proofs.* `lean/Causation.lean`: `left_reads_src`,
`left_blind_right`, `right_blind_left`, `correlated_forever`,
`correlation_not_causation`, `intervention_discriminates`;
`lean/Streams.lean`: `blind_iff_factors`, `boundaries_leak`.
`Causation` axiom-free.

**Proposition IV.6 (Composition is vocabulary-relative).** Parthood,
in this vocabulary, is factorization: one reading is part of another
when everything it sees is a function of what the other sees — the
same mechanism again. On this reading composition always succeeds and
never produces an entity. The joint of two readings contains both and
is least among vocabularies that do, so every two readings have a
canonical whole. The whole exceeds its parts: the joint expresses
binding facts — the agreement of its coordinates — that neither part
expresses in any way. And mutual parthood does not force identity, so
the order is of expressive power, not of things. Whether "the
composite exists" is thereby a (proposition, vocabulary) fact:
expressible in one vocabulary over the class, inexpressible in
another. *(forced; the mereological naming, interpretation)*

*Proofs.* `lean/Composition.lean`: `part_refl`, `part_trans`,
`part_left`, `part_right`, `joint_lub`, `antisym_fails`,
`whole_exceeds_parts`, `composition_relative`. Axiom-free.

---

## Part V — Mind

**Proposition V.1 (One process, two vocabularies).** Fix one class of
worlds and two readings of it. Whatever either reading expresses, their
joint expresses too. A proposition can be expressible in one reading
and not the other — which makes classification by reading a fact about
the (proposition, vocabulary) pair, not about the worlds themselves.
And the correlation between the two readings is expressible in the
joint, and in neither component on its own. *(forced)*

*Remark.* Read the two vocabularies as physics-talk and mind-talk. Then
mind and matter are two coarsenings of one process, not two substances,
and the mind–body "relation" becomes a truth statable in neither
vocabulary alone — which is exactly where the problem always lived.
This is offered as a reading; the mathematics stands without it.
*(interpretation)*

*Proofs.* `lean/OneProcess.lean`: `component_in_joint_left`,
`component_in_joint_right`, `vocabulary_relative`,
`correlation_needs_both`. Axiom-free.

**Proposition V.2 (Attribution is doubly undecidable).** The question
"is X experiencing?" fails twice over. First the predicate. Relative to
any chosen boundary, an inert interior flag is expressible in no
structural vocabulary — in full generality, and in particular in the
published vocabularies of the Conscious Turing Machine and of
Integrated Information Theory, whose own predicates provably neither
assert nor deny it. Then the subject. The term "X" denotes a tick-local
factorization that leaks under composition (IV.2), so there is no
dynamics-invariant bearer to attribute anything to. Occurrence (IV.3)
never needed a subject. Only attribution did. *(forced, both failures;
fidelity to the named theories on F1/F2)*

*Proofs.* `lean/Schema.lean`: `structural_iff_invariant`,
`theory_cannot_decide`, `deciding_theory_not_structural`,
`instance_schema`; `lean/CTMConservativity.lean`:
`ctm_conscious_awareness_cannot_decide_interior`, `ctm_flag_free`;
`lean/IIT.lean`: `iit_cannot_decide`; `lean/Streams.lean`:
`boundaries_leak`; `lean/Family.lean`: `family_interior_is_free`.
Schema and IIT axiom-free; the rest within `[propext, Quot.sound]`
(`Family.width4_matches_certificate` additionally trusts the compiler,
stated in the file).

**Proposition V.3 (Silent witnessing is conservative).** Any process
extends by a witness coordinate — written every tick, read by nothing.
On the base the extension changes no trajectory; to every
witness-blind instrument it changes no observation; and it forgets its
own seed after a single tick. So the reading "the process registers
itself" costs nothing and could never be detected. The independence of
the interior flag is built here, not merely asserted. *(forced)*

*Proofs.* `lean/Witness.lean`: `base_unchanged`,
`observables_unchanged`, `witness_forgets_seed`, `silent_witness`.
Axiom-free.

**Proposition V.4 (The registration hierarchy closes at height one).**
Stack witnesses to any finite height and the ground is unchanged. One
tick of the whole tower is a function of the ground alone, and from the
first tick on, any two towers with the same ground coincide completely
at every height. Higher-order registration adds nothing — even its
bookkeeping is overwritten each tick. *(forced)*

*Proofs.* `lean/WitnessTower.lean`: `tower_ground_unchanged`,
`towerStep_ground`, `tower_amnesia`, `tower_free`. Axiom-free.

**Proposition V.5 (Binding rigidity).** Fix any abelian value alphabet
and any abelian summary group. One axiom — translation-difference
integration, that the summary's increment under translating a single
locus is state-independent — then forces the entire binding law. Each
per-locus response must be a homomorphism, and the summary must be
their sum, up to one vacuum constant. The Boolean parity instance holds
at every width. Integration leaves no freedom beyond that one constant.
*(forced)*

*Proofs.* `lean/Rigidity.lean`: `phi_hom`, `decomposition`,
`rigidity`; Boolean instance `lean/Family.lean`: `family_rigidity`,
`family_membership`, `interior_location`. `Rigidity` within
`[Quot.sound]`; `Family` within `[propext, Quot.sound]`.

---

## Part VI — Freedom, Modality, and the Calculus of Verdicts

**Proposition VI.1 (The verdict calculus).** Forced, refuted, and free
are pairwise exclusive. Inexpressibility is monotone under vocabulary
restriction. If a vocabulary identifies the witnesses of a free
proposition, no such vocabulary can express it — and any vocabulary
that does express it has to separate every witness pair. Settling a
free question therefore takes a new primitive: one that tells apart
worlds the given vocabulary runs together. *(forced)*

*Proofs.* `lean/Ledger.lean`: `ledger_consistent`,
`expressible_monotone`, `inexpressible_of_free_unseparated`,
`settling_needs_new_primitive`. Axiom-free.

**Proposition VI.2 (Interminability).** Under freedom with identified
witnesses, no expressible proposition decides the question either way.
A debate conducted wholly inside the vocabulary cannot end in a
verdict. *(forced)*

*Proofs.* `lean/Ledger.lean`: `debate_interminable`. Axiom-free.

**Proposition VI.3 (Free will, dissolved twice).** The next choice of a
self-referential system is a total function of its state — nothing is
random. Yet the system's own prediction of that choice is falsified by
the very tick that receives it, precisely at the self-referential
coordinate. Determinism and interior openness turn out to be two faces
of one operator, not rivals. And the question "free *for whom*?" has no
referent, since there is no bearer at any scale (IV.2). What survives is
a closed orbit, open seats, and records that are genuine novelty (II.8).
*(forced; the naming is interpretation)*

*Proofs.* `lean/FreeWill.lean`: `determined`, `interior_openness`,
`never_foreknown`, `free_will_is_the_diagonal`;
`lean/TwoReadings.lean`: `process_reading_unique`;
`lean/SelfDerivation.lean`. Axiom-free.

**Proposition VI.4 (The modality is S5).** Read necessity as truth at
every admissible world and possibility as truth at some. Then K and T
hold, iterated modality is flat — the necessary is necessarily
necessary, the possible necessarily possible — and necessity and
possibility are classical duals. The logic is S5, and not by
stipulation: there is no accessibility structure in the vocabulary
for a weaker logic to live on. Every proposition is necessary,
impossible, or contingent over the class, and contingency is exactly
the verdict *free* (VI.1). Necessity survives restriction of the
class, so modal status is class-relative; no world-intrinsic
necessity remains for it to answer to. *(forced)*

*Proofs.* `lean/Modality.lean`: `axiom_K`, `axiom_T`, `axiom_four`,
`axiom_five`, `modality_is_S5`, `nec_dual`, `verdict_trichotomy`,
`nec_of_subclass`. The S5 conjunction axiom-free; the dual and the
trichotomy within `[propext, Classical.choice, Quot.sound]`.

**Proposition VI.5 (Counterfactuals without similarity).** Read "had
the seed been s, it would be that Q" as Q evaluated at the run from
s. Under seeded determinism the antecedent picks exactly one run —
anything satisfying the recursion is the run — so the closest world
is the run, and similarity orderings have nothing left to do. What
the actual history settles is less. Two laws can agree at every
actual tick and disagree at the counterfactual seed, and in the
vocabulary that sees only the actual run the counterfactual is
expressible in no way at all. Counterfactual truth is a fact about
the (law, seed) pair; the law is underdetermined at every finite
depth (II.7); so counterfactuals are real, evaluable, and
interior-unsettleable — one more value-class fact about which run one
is in and what is running it. *(forced; the counterfactual naming,
interpretation)*

*Proofs.* `lean/Counterfactual.lean`: `run_unique`, `agree_actual`,
`disagree_counterfactual`, `counterfactual_underdetermined`,
`counterfactual_not_expressible`. Within `[Quot.sound]`; all but the
last axiom-free.

**Proposition VI.6 (Refutation lands on the table).** Let a checked
core, a table of readings, and a prediction stand in the entailment:
core plus table implies prediction. If the prediction fails while the
core is held — and this corpus's core is held by the kernel, not by
argument — then the table is refuted, and classically some specific
row fails: the search space of any empirical miss is the table's
finite enumeration. Confirmation carries no converse force — a true
prediction is consistent with the falsity of every row. So
machine-checking does not close the seam between theorem and world;
it localizes Duhem's problem to ten rows, and it makes evidence cut
asymmetrically: readings can be closed off by experiment, never
closed in. *(forced; "the core is held" names the kernel check)*

*Proofs.* `lean/Duhem.lean`: `refutation_lands_on_the_table`,
`some_row_fails`, `confirmation_forces_nothing`. The first and third
axiom-free; `some_row_fails` within
`[propext, Classical.choice, Quot.sound]`.

**Proposition VI.7 (Freedom is width; instantiation collapses it).**
A free proposition yields two distinct worlds: freedom is inhabited
width in the admissible class, and nothing else. Over a *generated*
class — one world, given by evaluating a known law from a known seed
— nothing is free, every proposition is forced or refuted, and every
proposition is expressible in every vocabulary, including the
vocabulary that sees nothing: expressibility stops discriminating,
and settling never needs a new primitive because nothing is left to
settle. The class of runs of a known law from a known seed is such a
class. So the bridge results are width phenomena — bridges price
reference, and reference is what generation replaces. A map that
pictures a territory needs a correspondence; a map that runs its
territory needs nothing. The god's-eye view of an instantiated world
is not a better seat; it is a narrower class. Every undecidability in
this corpus is thereby located: each one measures the width of a
class some seat cannot collapse. *(forced; the map–territory naming,
interpretation)*

*Scholium.* This corpus is itself a generated territory: its law is
the source files, its seed the toolchain pin, its run the kernel's
check — and the check actually runs the small laws, since the kernel
normalizes the recursions it verifies. The two-tick clock has ticked
in every check of `TwoReadings.lean`. To its authors, then, the
corpus is a width-one class, and reading it as being about itself
needs no bridge row: generation replaces reference. What remains
width-many is the world the authors occupy — and that residual width
is not a defect in the map but the very quantity every freedom
theorem above measures. The position also has one instance whose
existence is tokened rather than premised: denying that any process
occurs refutes itself in the tokening (IV.3), and the tokening, here,
is the check. *(interpretation)*

*Proofs.* `lean/Instantiation.lean`: `freedom_needs_width`,
`generated_no_freedom`, `generated_dichotomy`,
`no_seam_when_generated`, `run_class_generated`, `map_is_territory`.
`freedom_needs_width`, `generated_no_freedom`, and
`no_seam_when_generated` axiom-free; `run_class_generated` within
`[Quot.sound]`; the dichotomy and the conjunction within
`[propext, Classical.choice, Quot.sound]`.

---

## Questions left unanswered

Each row below is a question this document does not answer, paired
with the theorem showing that, in the vocabulary the position allows
itself, it cannot be answered. The open status is the result, not an
omission.

| Question | Why it stays open |
|---|---|
| Whether the whole (or anything) is experiencing | `Family.lean` `family_interior_is_free` (every width); `Witness.lean` (the reading constructed as conservative, axiom-free); `Schema.lean` (settling it requires a non-structural primitive) |
| Whether the ground is fundamental or derived | `Aseity.lean` (no consistent system settles its own ground from inside, axiom-free) |
| The completed totality (the finished whole, the continuum, the "forever" fact) | `Totalization.lean` (no finite-depth observable reads it); `CompletionFree.lean` |
| Other minds | `InteriorExperience.lean` `other_minds_free` (attribution undecidable from observation) |
| Which branch; any value-class fact from the law | `ValueForm.lean`, `SelfDerivation.lean` (values are seat-relative records, underivable in principle) |
| The cutoff scale / absolute units | `PlanckFree.lean` (interior-undecidable, axiom-free) |
| The arrangement of space (line, reversed line, ring; any orientation) | `SpaceOrder.lean` `space_order_free` (the order axioms without the induction mandate admit distinct orders), `cycle_not_strict` (the ring stays available to what time excludes) |
| The geometry beyond the window (global topology, dimension) | `DimensionFree.lean` `dimension_beyond_window` (two geometries, one ringed, identical to every window-supported reading) |
| Which law is running — hence which counterfactuals hold — from the complete actual history | `Counterfactual.lean` `counterfactual_underdetermined`, `counterfactual_not_expressible` |
| Anything beyond occurrence from the first-person datum | `Cogito.lean` (the cap is part of the theorem) |

What *can* be challenged is collected in the premise table below;
that is where the assumptions live.

---

## Premises

A premise is a named assumption joining a theorem to an informal
reading. Each row states how it could be challenged and which
propositions would lose their application — never their validity — if
it failed. An unconditional proposition depends on no premise; only the
propositions that name one in their statement appear below.

That this table cannot be emptied is itself covered by a theorem. A
reading joins the mathematical vocabulary to a metaphysical one, and
any vocabulary that expresses the joined claim separates worlds the
mathematical vocabulary identifies (`lean/Ledger.lean`
`settling_needs_new_primitive`; `lean/Bridge.lean` `the_fork`) — the
seam between *forced* and *interpretation* is the semantic twin of the
is/ought bridge (ETHICA.md I.2). A row can be narrowed by a grounding
theorem, as R3 was by `Structureless.lean` and O by
`Continuity.lean`, and each narrowing leaves a smaller residual
identification; none reaches zero. Applying the fork to this
paragraph is itself a reading, which is where the regress stops being
vicious and starts being the table. And empirical contact is priced
by the same discipline (VI.6): because the core is kernel-checked, a
failed prediction refutes rows and never theorems, while a confirmed
one forces nothing — the table is also where every experiment lands.
Finally, the seam has a measure (VI.7): bridges price the width of
the admissible class, and over a generated class — where the map runs
the territory rather than picturing it — no bridge is ever needed.
The rows below price the width of the one class this position's seat
cannot collapse: the world it occupies. The table is not the
position's apology; it is its closure.

| # | Premise | Status | How to challenge it | What depends on it |
|---|---|---|---|---|
| B3 | Seat-indexed quantities read as observers/perspectives | Definitional identification | Exhibit a seat-indexed quantity that is not perspectival | The philosophical reading of II.7; its mathematics untouched |
| R1 | Every seeded specification's demand for a ground is answered | Hypothesis, named in `Regress.lean` | An unanswered demand — a brute contingency | I.4 only |
| R2 | No infinite regress of grounds (well-foundedness of demand) | Hypothesis, named | Infinite-descent metaphysics | I.4 only |
| R3 | An unseeded ground imports no structure (structureless = equivariant) | Grounded by theorem: equivariant = definable from the distinction alone (`Structureless.lean` `structureless_iff_equivariant`, axiom-free); residual identification: "no structure" = "no vocabulary beyond the distinction" | A reading of "importing no structure" outside pure-equality definability | I.4 only |
| R4 | An unseeded ground is generative: its law moves something | Hypothesis, named in `Regress.lean` | A static "from nothing" | I.4 only |
| R5 | The founding distinction is presented at some tick: some configuration exhibits both sides at once | Hypothesis, named in `Priority.lean`; its failure has an exhibited witness — the bare clock realizes the pair across two ticks, one locus per tick (`clock_two_tick_pair`) | A running whose mark is never present in any state: exhibited only across ticks, stored nowhere, read by nothing | The existential reading of II.2 — that the second locus is anywhere actual; the classification itself, and II.3–II.4, untouched |
| H | The law reads every seat alike (homogeneity) | Hypothesis, named in `Occurrence.lean` | An inhomogeneous law | IV.4 only |
| O | Whatever an instrument or evaluator reads is a finite-depth observable | Definitional identification, robust under reformulation: finite depth = uniform continuity = finite-prefix factorization, with pointwise continuity strictly weaker (`Continuity.lean`) | Exhibit a measurement that is not uniformly finitary — one whose modulus grows with the history | The measurement readings of III.1–III.4 (in III.4 the spatial face: instrument access is window-supported); their mathematics untouched. Inherited by the ethics (ETHICA.md V.1–V.2) |
| F1 | The transcription of the Conscious Turing Machine in `CTMConservativity.lean` is faithful to the published theory | Theory fidelity; source cited in the file | Exhibit a published CTM predicate the transcription omits | The CTM clause of V.2; the general schema result untouched. Inherited by the ethics (ETHICA.md II.1) |
| F2 | The transcription of Integrated Information Theory in `IIT.lean` is faithful to the published theory | Theory fidelity; source cited in the file | Exhibit a published IIT predicate the transcription omits | The IIT clause of V.2; the general schema result untouched. Inherited by the ethics (ETHICA.md II.1) |

Rule: no proposition may rely on a premise absent from this table.

---

## Dissolved questions

Each debate below has the same anatomy. Its target is a totalization —
a substance, a flag, a whole, a bottom, an owner. A theorem then shows
that totalization to be undecidable, unmeasurable, or resting on a
presupposition that fails. And a successor question keeps whatever was
tractable.

**1. Substance dualism** (mind vs. matter: which is fundamental?).
Dissolved by V.1. Mind-talk and matter-talk are two vocabularies over
one world class, classification is vocabulary-relative, and the
correlation between the readings — the mind–body relation itself — is
expressible in neither alone. The debate assumed two candidate
substances. The theorems describe one process and two readings, neither
able to state its relation to the other. *Successor:* which
architectures bind which streams, and at what cost — an empirical
program.

**2. Consciousness attribution** (is it conscious?). Dissolved by VI.2
together with V.2. The interior flag is free, and every structural
vocabulary — CTM's and IIT's included — identifies its witnesses, so no
debate inside those vocabularies can terminate. The subject term,
meanwhile, denotes a leaking factorization, so there is no invariant
bearer to attribute anything to. *Successor:* what does this
architecture integrate, and what is it blind to? Both decidable
(V.5, IV.2) and measurable.

**3. The completed totality** (what is the universe, as a whole?).
Dissolved by III.1. Every observable is a prefix fact, completions are
invisible, and "forever" is not a measurement. The whole-as-object is
not wrong, just outside the reach of any observation. *Successor:* the
finite-depth structure of the ongoing process.

**4. The ground** (why is there something? what is at the bottom?).
Split in two by I.5 and I.4. The certificate question — "am I
fundamental?" — is interior-undecidable. The shape question is
answered: given R1–R4, well-founded answered-demand chains terminate in
a ground whose law is `x = ¬x`. The tradition asked for a certificate
of the terminus. What it can have instead is a theorem about the chain.
*Successor:* what the one ground forces.

**5. Free will** (could I have done otherwise?). Dissolved by VI.3.
Determinism and interior openness are one operator's two faces, and the
owner the question presupposes does not exist. All three classic camps
— libertarian author, hard-determinist puppet, compatibilist desirer —
share that failed presupposition. *Successor:* which seats are
self-referential, where the diagonal binds, and what their records
create.

**6. Special composition** (when do parts make a whole?). Dissolved
by IV.6. At the level of readings, composition is total and canonical
— the joint always exists and is least among vocabularies containing
the parts — while at the level of entities there is nothing to
compose: mutual parts need not be identical, and every boundary leaks
(IV.2). Universalism and nihilism were reports from different
vocabularies, quarreling over a question the worlds never carried.
*Successor:* which joints express which binding facts, at what cost —
the same successor as mind (V.1), because it is the same question.

**7. Possible worlds** (what are they, and how close is closest?).
Dissolved by VI.4 and VI.5. Modality is S5 quantification over an
admissible class, with no accessibility structure in the vocabulary
for rival metaphysics of modality to disagree about; and the
counterfactual's "closest world" is the unique run from the
counterfactual seed, so the similarity apparatus idles. Realism and
ersatzism about worlds priced furniture the calculus never uses.
*Successor:* which class is admissible, and which law is running —
where the second inherits a proved limit (VI.5).

---

## Related positions

Most of the individual theses here have ancient or modern precedents.
The table lists the closest ones and what this treatment adds — in
most cases a proof where there was an assertion, or an explicit
assumption where there was an implicit one.

| Prior | Asserted | Maps to | What this treatment adds |
|---|---|---|---|
| Heraclitus | Flux; no static being | I.2 | The equivalence (I.3): stasis-denial *equals* perpetual motion, proved |
| Nāgārjuna / Madhyamaka | No svabhāva; dependent origination | II.6, III.1 | Persistence-requires-interaction as a theorem; totalization unmeasurable, axiom-free |
| Leibniz, correspondence with Clarke | Space the order of coexistence, time the order of succession | II.2–II.4 | The asymmetry proved: succession carries the induction mandate and is forced; coexistence is forced to exist, free in arrangement |
| Hume, *Treatise* I.iii | Causation as constant conjunction; no necessary connexion | II.9, IV.5 | The confounder constructed: constant conjunction and reading come apart, and intervention — not further observation — separates them |
| Lewis, *Counterfactuals*; plurality of worlds | Counterfactuals via similarity over concrete worlds | VI.4–VI.5 | The closest world proved unique — it is the run; similarity orders idle; S5 with no accessibility structure to argue over |
| Pearl, *Causality* | Intervention calculus; do-operator vs conditioning | IV.5 | The core distinction — intervening is not observing — at the law level, kernel-checked on the minimal confounder |
| van Inwagen, *Material Beings* | The special composition question | IV.6 | The question relocated: composition total and canonical among readings, empty among entities |
| Duhem; Quine, "Two Dogmas" | Confirmation holism: blame spreads over the whole web | VI.6 | The web given a rigid part: with the core kernel-checked, every miss lands on ten enumerated rows |
| Popper | Falsifiability; the asymmetry of refutation | VI.6 | The asymmetry as two theorems: refutation forces a row's failure, confirmation forces nothing |
| Korzybski | "The map is not the territory" | VI.7 | The exception characterized exactly: a generated map is its territory — the class of runs of a known law and seed has width one — and the slogan's truth is measured by class width, which every freedom theorem prices |
| Spencer-Brown, *Laws of Form* | One mark; re-entry generates form | I.1 | Uniqueness proved: the mark is the *only* structureless generative form |
| Whitehead, *Process and Reality* | Process primary; creativity ultimate | I.2, II.8 | Novelty as theorem: value-class facts underivable in principle |
| Rescher, *Process Metaphysics* | Processes over substances, systematically | whole treatise | Every clause tagged, checked, or proven free |
| Wheeler, "it from bit" | Physics from binary distinctions | I.1 | The distinction's dynamics forced, not chosen |
| Rovelli, relational QM | Facts are relative to systems | II.7 | The form/value split with the self-derivation no-go attached |
| Ladyman & Ross, *Every Thing Must Go* | Ontic structural realism | II.6 | The structural core as prelude-only Lean rather than argument |
| Blum & Blum (CTM); IIT | Structural theories of consciousness | V.2 | Conservativity proved inside their own vocabularies |

A few features of the format we have not found in earlier work:
questions left open by theorem rather than by modesty (*Questions left
unanswered*), and premises with stated dependency scopes (*Premises*).

---

## Appendix A — Index of proofs

Every file: Lean 4, prelude only, standalone; checked with
`lean lean/<File>.lean` under `leanprover/lean4:v4.31.0`; axiom
footprint printed at end of file.

| File | Main results | Axioms |
|---|---|---|
| `OneDiagonal.lean` | `lawvere`, `diagonal_no_go` | ≤ `propext` |
| `OnlyShape.lean` | `spec_forced` | ≤ `propext` |
| `Structureless.lean` | `structureless_iff_equivariant`, `constants_not_defble` | none |
| `TwoReadings.lean` | `frames_one_fact`, `object_reading_empty`, `process_reading_unique` | none |
| `Regress.lean` | `ground_has_one_shape`, `time_selects_the_shape` | `propext, Classical.choice, Quot.sound` |
| `Aseity.lean` | `no_self_model`, `aseity` | none |
| `Loeb.lean` | `loeb_iff_induction`, `deJonghSambin`, `godel_is_clock` | ≤ `propext, Quot.sound` |
| `OrderForced.lean` | `order_is_forced` | ≤ `propext, Quot.sound` |
| `Multiplicity.lean` | `multiplicity_forced`, `one_shape_two_readings` | ≤ `propext, Quot.sound` |
| `RichAlphabet.lean` | `no_rich_separation`, `escape_closed` | none |
| `Priority.lean` | `space_prior` | none |
| `SpaceOrder.lean` | `time_forced_space_free`, `space_order_free` | ≤ `propext, Quot.sound` |
| `RecordMonotone.lean` | `write_once` | ≤ `propext` |
| `Causation.lean` | `causal_arrow`, `correlation_not_causation`, `intervention_discriminates` | none |
| `NoFreeRecords.lean` | `no_drift_eigenvector` | ≤ `propext` |
| `ValueForm.lean` | `status_underdetermined`, `no_status_decider` | none |
| `Constant.lean` | `constant_is_record`, `constant_not_derivable` | none |
| `SelfDerivation.lean` | `two_obstructions` | none |
| `Totalization.lean` | `continuations_indistinguishable`, `no_finite_depth_detects_forever` | ≤ `propext` |
| `CompletionFree.lean` | `completion_invisible` | none |
| `Continuity.lean` | `factors_iff_depth`, `continuity_strictly_weaker` | ≤ `Quot.sound` |
| `Horizon.lean` | `horizon_not_interior` | ≤ `propext` |
| `PlanckFree.lean` | `no_finite_cutoff_forced` | none |
| `DimensionFree.lean` | `dimension_beyond_window` | ≤ `propext, Quot.sound` |
| `InteriorExperience.lean` | `unity`, `gap_forced`, `other_minds_free` | ≤ `propext, Quot.sound` |
| `Streams.lean` | `blind_iff_factors`, `boundaries_leak` | ≤ `propext, Quot.sound` |
| `Cogito.lean` | `cogito_valid_necessarily`, `cogito_ergo_sum` | none |
| `Occurrence.lean` | `no_total_reading`, `indexical_is_value` | none |
| `OneProcess.lean` | `vocabulary_relative`, `correlation_needs_both` | none |
| `Composition.lean` | `joint_lub`, `antisym_fails`, `whole_exceeds_parts`, `composition_relative` | none |
| `Schema.lean` | `structural_iff_invariant`, `theory_cannot_decide` | none |
| `CTMConservativity.lean` | `ctm_conscious_awareness_cannot_decide_interior` | ≤ `propext, Quot.sound` |
| `IIT.lean` | `iit_cannot_decide` | none |
| `Family.lean` | `family_membership`, `family_rigidity`, `family_interior_is_free` | ≤ `propext, Quot.sound` (+ compiler for `width4_matches_certificate`) |
| `Witness.lean` | `silent_witness` | none |
| `WitnessTower.lean` | `tower_free` | none |
| `Rigidity.lean` | `phi_hom`, `decomposition`, `rigidity` | ≤ `Quot.sound` |
| `Ledger.lean` | `settling_needs_new_primitive`, `debate_interminable` | none |
| `Modality.lean` | `modality_is_S5`, `verdict_trichotomy`, `nec_of_subclass` | ≤ `propext, Classical.choice, Quot.sound` |
| `Counterfactual.lean` | `counterfactual_underdetermined`, `counterfactual_not_expressible` | ≤ `Quot.sound` |
| `Duhem.lean` | `refutation_lands_on_the_table`, `some_row_fails`, `confirmation_forces_nothing` | ≤ `propext, Classical.choice, Quot.sound` |
| `Instantiation.lean` | `freedom_needs_width`, `no_seam_when_generated`, `run_class_generated`, `map_is_territory` | ≤ `propext, Classical.choice, Quot.sound` |
| `FreeWill.lean` | `free_will_is_the_diagonal` | none |
