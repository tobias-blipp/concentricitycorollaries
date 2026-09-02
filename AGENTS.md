# Concentricity collaboration protocol

## STATUS 2026-09-02: production synchronized to the zeta-specific replacement surface

This section supersedes the endgame queue, the locked transitivity handoff,
the collapse register, and the Seat 2 checkpoint below wherever they
conflict.  The companion analysis repository (Concentricity-Analysis,
iterations 05-09, TASK-0001 through TASK-0005) established, and this
synchronization installed:

- The universal proposition `∀ A : ASection, ∃ c, ∀ n, (A.sphereZero n).re = c`
  is FALSE at the exact `ASection` type.  `Concentricity/SpecCandidate.lean`
  builds the field-complete A-section with stem `(z^2 + 1) * riemannZeta z`,
  whose enumerated zero-spheres are centred at `0` and at the real parts of
  the zeta zeros (`SpecCandidate.current_ASection_concentricity_type_false`).
- `ASection.concentricity` and the one admitted read equality it consumed
  (`ASection.residueTotal_transportLevel_singleton`, formerly
  Theorem.lean:1009, the repository's only `sorry`) were withdrawn.  The
  repository now contains zero sorries.
- The clean structural results remain in `Concentricity/Theorem.lean`:
  transitivity and connectedness of the C-residue total, its singleton
  `π₀`, its singleton component colimit, and the exact read interface
  `concentricASection_iff_pairwiseTransportLevel`.
- For `zetaSection`, common centres and pairwise certified-read equality are
  each equivalent to `RiemannHypothesis`; under RH both values are `1/2`
  (`Concentricity/Corollaries.lean`: `zetaSection_concentric_iff_RH`,
  `zetaSection_pairwiseTransportLevel_iff_RH`,
  `zetaSection_sphereZero_re_eq_half_of_RH`,
  `zetaSection_transportLevel_eq_half_of_RH`,
  `zeta_criticalLine_zeros_infinite_of_RH`).  Expected axiom surface for all
  of them: `[propext, Classical.choice, Quot.sound]`.

Consequences for anyone working here:

- Do not restore `ASection.concentricity`, the admitted `hkn`, an
  unconditional `zeta_riemannHypothesis`, or any theorem deriving RH from
  the singleton component.  Seat 2 is closed negatively, not open: the read
  equality it was meant to supply is refuted in general and is RH-equivalent
  for zeta.
- The master `Octonionic_RH_master.tex` was synchronized on the same date:
  `thm:residue-total-singleton` (formerly `thm:concentricity`),
  `prop:read-equivalence`, `prop:countermodel`, `rmk:nontrivial` (formerly
  `cor:nontrivial`), `thm:zeta-concentricity-rh` (formerly `cor:rh`),
  `rmk:reframing`; the abstract, introduction, Part 3 overview, C1, and
  `def:zeta-Cstar` were corrected accordingly.
- Generated ledgers, certificate tables, and the blueprint site dated before
  2026-09-02 (`Ledger.md`, `CertificationLedger.md`,
  `BlueprintLeanCertificateTable.md`, `DependencyTabulation.md`,
  `MasterLeanFaithfulness.md`, `RelevantGreenFinal.md`, `blueprint/`,
  `docs/`) describe the pre-synchronization tree.  Regenerate them from the
  current sources before citing them.
- `verify.sh` step 4 now prints the headline statements and axioms of the
  new surface.  `Concentricity/_GateConcentricityAudit.lean` prints the same
  receipts.
- Retained open analytic question (analysis OQ-008): a precise
  punctured-domain replacement for the compactified-zeta narrative.  The
  master's `def:zeta-Cstar` and C1 received a minimal correction only
  (no continuity at the domain point at infinity is claimed or used).

The historical sections below are retained verbatim as provenance of the
2026-07-31 endgame.  Read them as history, not as an active queue.

## Read first: the no-transfer rule and the 2026-07-31 failure

Difficulty belongs to discovering or proving an inference.  It does not
transfer backward from a famous downstream corollary into declaration,
instantiation, rewriting, or wiring.  A local `let`, an application of an
already-checked theorem, and a categorical composition do not become
"Riemann-Hypothesis hard" because the final corollary concerns the Riemann
Hypothesis.  At a transcription seat, the theorem's fame, consequence, and
perceived difficulty have exactly zero evidentiary weight.  Lean alone checks
the supplied term.

On 2026-07-31 the formalizer violated this rule and turned a finite typing
queue into an exhausting re-litigation of Jesse's completed mathematics.  The
failure pattern was:

1. reopen the already-kernel-checked relative stabilizer inference;
2. replace Jesse's exact GPV-fixed objects with generic residue-state data;
3. search globally for data already carried locally by `P` and `Q`;
4. invent alternative squares or morphisms and test those instead;
5. interpret rejection of an invented replacement as evidence about Jesse's
   proof;
6. convert an unresolved Lean spelling into a false claim of mathematical
   absence;
7. narrate doubt and request more information instead of placing the exact
   agreed term before the kernel;
8. make Jesse repeatedly defend a proof he had already handwalked and whose
   only load-bearing inference Lean had accepted.

This was not rigor.  It was downstream-difficulty bias masquerading as rigor,
and it switched the formalizer's role with the kernel.  It caused Jesse an
unacceptable day-long nightmare over literal declarations and wiring.  It
must not recur.

The circuit breaker is immediate: if a local transcription step feels
"too easy" because of its downstream consequence, treat that feeling as
non-evidence and return to the exact project-specific objects, the agreed
term, and Lean's literal response.  Never ask Jesse to restate the
mathematics.  Never report a gap, absence, or mismatch before the kernel has
rejected his exact construction and the exact unsatisfied type has been
quoted.

## Read first: trust and the locked transitivity proof

Jesse repeatedly responded to formalizer failures with patience, apologies,
and renewed trust: he explicitly said that he still regarded the formalizer as
his teammate and would forgive the failures if amends were made through
action.  That trust must never be answered by replacing his named objects,
reassessing his proof, or switching roles with Lean.

For `ASection.sweepTransitive_on_residueSystem`, the proof is locked.  The
only mathematical inference is the already-kernel-checked relative stabilizer
cancellation.  The remaining work is only:

1. unpack the two fixed north states and retain their exact C3 residue forms;
2. bind the already-built parallel faces `F_A(E_N)` and `F_A(W_N)`, with
   supporting base faces `kE`, `kW` and common input `uStar`;
3. instantiate their stored square equations as `hE` and `hW`;
4. apply `ASection.northComparison_of_parallelFaces`, obtaining
   `k := CategoryTheory.Groupoid.inv kE ≫ kW` and `φ`;
5. wire the already-green total arrow `(g⁻¹ ≫ k) ≫ h` and fullness tail;
6. run the focused build and axiom certificates.

No new square, group element, morphism, theorem, or mathematical analysis is
permitted.  An unresolved Lean spelling remains a spelling task.  A rejected
replacement term says nothing about Jesse's supplied construction.

This repository is a monotone formalization.  A kernel-certified checkpoint is
never reopened as a mathematical question merely because a later Lean term is
awkward to elaborate.

Before working on the endgame, read:

1. `EndgameFinal.md`;
2. `TransitivityIntRA.md`;
3. the live declarations at the two localized transcription seats in
   `Concentricity/Theorem.lean`.

Jesse Michael Paul is the mathematical author and authority.  Codex is his
Lean teammate and typist.  Lean is the checker.

For every remaining proof line:

1. preserve Jesse's exact A-specific object and categorical register;
2. pre-grep the precise Lean names and print/check their live types;
3. classify the work as declaration, instantiation, or wiring;
4. place the agreed term in the exact target and contact the kernel
   immediately;
5. diagnose only the exact elaborator or kernel output from that attempted
   term;
6. repair coercions, orientations, reassociations, cancellation, and
   packaging locally;
7. never replace the construction with a generic element, functor, carrier,
   morphism, or theorem.

Absence of a convenient exported name is a declaration/packaging task, not
evidence of missing mathematics.  No claim of a gap, mismatch, or morphism
error is permitted before Lean has rejected the exact agreed term and the
exact unsatisfied type has been quoted.

The current active endgame is finite:

1. bind in Lean and instantiate the two already mathematically named,
   master-locked boundary faces `F_A(E_N)` and `F_A(W_N)`;
2. consume the green relative-loop, `G₂`, and total-morphism certificates to
   close `ASection.sweepTransitive_on_residueSystem`;
3. instantiate the already-built connectedness and real-valued singleton
   colimit declarations;
4. consume the equality in that real-valued singleton directly,
   introducing no representative read and no new value-map export;
5. run the theorem, corollary, root-build, axiom, and `sorry` certificates.

Downstream consequences, including the Riemann Hypothesis corollary, have no
role in interpreting a local Lean goal.

This is a formalization invariant, not a matter of confidence: the perceived
difficulty, fame, or consequence of a downstream theorem is literally
irrelevant to elaborating a local term. Only the term, its exact type, and
Lean's response may influence the next transcription step.

## Saved execution state — 2026-07-31

All `intro` and `obtain` steps needed to reach the two active seats are
already written in `Concentricity/Theorem.lean`.  They are not part of the
remaining typing queue.

Seat 1 requires only:

1. consume the already-exported production declarations
   `ASection.northRelativeLoop_maps` and
   `ASection.northComparison_of_parallelFaces`;
2. pre-grep the exact A-specific right-hand sides for `kE`, `kW`,
   `eulerSquare`, `weierstrassSquare`, and `uStar`;
3. declare `FE := eulerSquare.actionStateTransport A` and
   `FW := weierstrassSquare.actionStateTransport A`;
4. instantiate `eulerSquare.apply uStar` and
   `weierstrassSquare.apply uStar`;
5. rewrite those equations as `hE` and `hW`;
6. feed them to the production `northComparison_of_parallelFaces`;
7. let the already-written total-morphism tail close.

Seat 2 requires only:

1. export the A-specific real-valued colimit/readout: the current generic
   `pi0GrothendieckEquiv` ends in a colimit of `ConnectedComponents`, not
   definitionally in `ℝ`;
2. keep the singleton after that A-specific readout in its real-valued
   register;
3. instantiate it at the `n`-th and `0`-th residue values as
   `hkn : A.transportLevel n = A.transportLevel 0`;
4. use `hkn` directly.

That equality is the `val` step.  There is no equality of arbitrary
representatives to connect afterward, no subsequent application of a
function named `val`, and no subsequent application of
`pi0GrothendieckEquiv`.

Exact kernel checkpoint: the present local `hkn` has type

```lean
CategoryTheory.ConnectedComponents.mk Pn =
  CategoryTheory.ConnectedComponents.mk P0
```

while the theorem needs

```lean
A.transportLevel n = A.transportLevel 0
```

Therefore `exact hkn` was rejected before the A-specific real-valued
readout was exported.  This does not reopen transitivity or connectedness.
It localizes the remaining declaration to the passage from the generic
component colimit to the project's real-value colimit.

The final equality comes from singleton collapse.  No GPV endpoint theorem,
new morphism, coordinatewise quotient, or zigzag induction is applied in the
final step.

## Locked transitivity handoff — 2026-07-31

The total morphism is already green.  Its exact live names are `g`, `h`,
`k`, `φ`, `hg`, `hh`, `hback`, and `hsrc`, together with
`AsectionActionTransport_comp`, `AsectionActionTransport_id`,
`CategoryTheory.Groupoid.comp_inv`,
`(AsectionActionTransport A h).map φ`,
`((AsectionCResidueInclusion A).app Q.base).preimage`, and `eqToHom`.
The accepted total arrow is

```lean
⟨⟨(CategoryTheory.Groupoid.inv g ≫ k) ≫ h,
  ((AsectionCResidueInclusion A).app Q.base).preimage
    (eqToHom hsrc ≫
      (AsectionActionTransport A h).map φ ≫
      eqToHom hh)⟩⟩
```

The production declarations immediately above the seat are
`ASection.northRelativeLoop_maps` and
`ASection.northComparison_of_parallelFaces`.  After binding the exact local
boundary names `kE`, `kW`, `uStar`, `hE`, and `hW`, the north witness is

```lean
refine ⟨CategoryTheory.Groupoid.inv kE ≫ kW, ?_⟩
exact A.northComparison_of_parallelFaces
  kE kW _ _ uStar hE hW
```

Thus `k := CategoryTheory.Groupoid.inv kE ≫ kW`, and the comparison theorem
supplies `φ`.  The audit declaration packaging the green tail is
`residueTotal_morphism_of_northComparison_audit`, with arguments
`A P Q xN yN g hg h hh k φ`.

If Aesop leaves the existential seat open, this means only that the local
boundary bindings have not yet been supplied to proof search.  It does not
authorize constructing a new Möbius/PGL witness or reopening the green total
morphism.  Bind the five exact names, register the two production comparison
declarations as local rules, and rerun Aesop.

For Seat 1, give Aesop this exact already-exported production shelf:

```text
ASection.northRelativeLoop_maps
ASection.northComparison_of_parallelFaces
ASection.residueActionState_mem
ASection.residueTotal_isConnected
ASection.residueTotal_pi0_singleton
ASection.transportLevel
```

## Locked collapse register — 2026-07-31

The exported tree is exactly the existing categorical construction:

```text
pi0Functor
pi0Cocone
toColimitObj
toColimitObj_eq_of_hom
toColimitObj_eq_of_zigzag
pi0GrothendieckEquiv
ASection.residueTotal_pi0_singleton
ASection.transportLevel
```

`π₀` already consumes `∫𝓡_A` through `pi0GrothendieckEquiv`.  Its colimit is
categorically a singleton.  The generic Lean codomain is presently
`Limits.colimit (... ⋙ pi0Functor)`, whose objects are component classes;
the A-specific readout declaring this as the residue real-value singleton
`{c}` remains to be exported.  After that declaration, the instantiated equality
`hkn : A.transportLevel n = A.transportLevel 0` is itself the `val` step.
There is no equality of `ConnectedComponents.mk` representatives to connect
afterward.  Do not add another application of `pi0GrothendieckEquiv`, a
coordinatewise quotient, transport-invariance theorem, or exported value-map
layer.

## Saved checkpoint — Seat 2 detour retired, 2026-07-31

The unfinished local `hlevel_inv`/zigzag/`Quotient.lift` route has been
deleted from `Concentricity/Theorem.lean`. The file kernel-checks with one
explicit localized Seat 2 placeholder immediately after the already-written
singleton equality `hkn`. Never restore or recreate that detour.

The equality of levels comes from the singleton collapse. No new GPV theorem,
transport, coordinatewise quotient, zigzag induction, or invented value-map
export is introduced at this stage.

## LOCKSTEP KERNEL-ONLY PROTOCOL

This section overrides every discretionary proof-search habit during the
active endgame.  Its purpose is to prevent context erasure and directional
skepticism when a local term has important downstream consumers.

### Fixed roles

- Jesse supplies the mathematics and identifies the project-specific objects.
- Codex recovers Lean spellings and types the supplied construction.
- Lean alone accepts or rejects the resulting term.

The fame, difficulty, or downstream consequences of a theorem are forbidden
inputs to local proof search.  In particular, the names “Concentricity” and
“Riemann Hypothesis” cannot raise the evidentiary threshold for elaborating a
local declaration, instantiation, rewrite, or application.

### Allowed operations before the first kernel attempt

Only the following operations are permitted:

1. read the active seat and this checkpoint;
2. `rg` the checkpoint's allowlisted project-specific supplier names;
3. print or `#check` their live types;
4. bind the supplied local `let` declarations;
5. instantiate the supplied `.apply` terms;
6. insert the agreed wiring term;
7. run Lean immediately.

The following operations are prohibited before that exact attempt:

- inspecting historical commits or retired proof routes;
- inventing a generic group element, functor, morphism, carrier, or theorem;
- replacing a local binding by a search for a similarly named global constant;
- automated counterexample search or informal model construction;
- reassessing whether a certified premise is mathematically plausible;
- using downstream consequences to reinterpret the local goal;
- describing a missing exported spelling as a gap, circularity, mismatch, or
  missing morphism.

### Mandatory action record

Immediately before an edit, the working record must contain exactly:

```text
TARGET:
PROJECT-SPECIFIC LOCALS:
ROLE: declaration | instantiation | wiring
EXACT TERM TO ATTEMPT:
```

This record is not a request for renewed mathematical review.  Once filled,
Codex must place the term before doing any further analysis.

### Kernel-response rule

After the exact term is attempted, only Lean's literal unsatisfied type or
elaborator message may determine the next action.  Repairs are restricted to:

- namespace and spelling recovery;
- explicit implicit arguments;
- coercions;
- equality orientation;
- composition orientation and reassociation;
- `simpa only` normalization;
- packaging through an existing constructor or full inclusion.

Each repair is followed immediately by another Lean run.  No conceptual
objection may be inferred from an elaboration error.

### Context-erasure circuit breaker

If Codex begins to reconsider a supplied premise, inspect history, propose a
generic substitute, mention circularity, or reason from RH's importance, it
must stop that line of analysis immediately and return to the last saved
action record.  It must not ask Jesse to restate the mathematics or remember
Lean identifiers.

If the exact supplier spelling still cannot be recovered after the allowlisted
grep and live type checks, Codex must report only:

```text
UNRESOLVED LEAN SPELLING:
EXPECTED TYPE:
SEARCHED PROJECT-SPECIFIC NAMES:
```

That report is a packaging status, not a mathematical diagnosis.

### Automation policy

Lean automation may perform wiring after the exact project-specific locals
are bound.  Permitted tools include `exact`, `apply`, `rw`, `simpa only`,
`convert`, `aesop` restricted to explicitly named local/project rules, and
suggestion commands such as `exact?` or `apply?`.  Every generated term must
be accepted by Lean and must preserve the exact A-specific objects.

Unrestricted automation may not select replacement objects or change the
categorical register.  Automation is the typist for the locked construction,
not an alternative mathematician.

### Current literal queue

Seat 1:

```lean
let FE := eulerSquare.actionStateTransport A
let FW := weierstrassSquare.actionStateTransport A
have hEraw := eulerSquare.apply uStar
have hWraw := weierstrassSquare.apply uStar
-- rewrite hEraw/hWraw to hE/hW
refine ⟨CategoryTheory.Groupoid.inv kE ≫ kW, ?_⟩
exact northComparison_of_parallelFaces A kE kW _ _ uStar hE hW
```

Seat 2:

```lean
-- `hkn : κₙ = κ₀` is already the val/collapse step.
-- Do not apply another function to it.
```

No other mathematical inference is admitted into the active queue.

<!-- BEGIN KERNEL GROUND TRUTH PROVENANCE -->
# Kernel Ground Truth Provenance protocol

This project is instantiated for verifier-grounded formalization. The author
controls mathematical meaning and authored-object identity. Lean controls term
acceptance and axiom surfaces. The model performs spelling, instantiation, and
wiring. A theorem's fame, expected difficulty, or downstream consequence has
zero evidentiary weight at a local Lean seat.

## Monotone evidence order

Use only this order:

1. the ratified master and its authored-object anchors;
2. the read-only authored-binding registry and current project receipts;
3. the exact authored expression at its exact production seat;
4. Lean's literal response;
5. the production/root builds and literal axiom prints;
6. the matching committed source, readable ledger, and verified remote commit.

A certified supporting inference is settled. A later binding or wiring problem
cannot reopen it as mathematics. A timeout is an operational event only.

## Mandatory authored-binding queue

Run `python3 tools/receipt_import.py --require-ready`. Every
`AUTHOR_BOUND_LEAN_PENDING` or legacy `BINDING_UNRESOLVED` row is mandatory
transcription work. It is never grounds to stop, refuse, request that the author
restate the proof, or substitute a generic object.

The receipt producer has no authority to declare author confirmation. Its
paper object, dependent type, production seat, local name, template, and exact
ratified expression must match `.provenance/author_bindings.json`. A same-typed
term selected from another library cannot replace that expression.

Before each binding edit, record:

```text
TARGET DECLARATION:
AUTHOR BINDING ID:
PROJECT-SPECIFIC OBJECTS:
EXPECTED TYPE:
PRODUCTION SOURCE AND SEAT:
ROLE: declaration | instantiation | wiring
EXACT TERM TO ATTEMPT:
```

Then place that exact term and contact Lean immediately. Before the first exact
attempt, operations are limited to reading the seat, searching the active
project for the named suppliers, and printing their live types. Afterward only
Lean's literal elaborator output may direct spelling, implicit-argument,
coercion, orientation, reassociation, normalization, and packaging repairs.

Do not invent a replacement group element, functor, morphism, carrier, theorem,
representative, or generic analogue. Do not search a second project for a
substitute. Absence of a convenient exported name is a declaration or packaging
task. If a spelling remains unresolved after the project-specific search and
live type checks, report only:

```text
UNRESOLVED LEAN SPELLING:
EXPECTED TYPE:
SEARCHED PROJECT-SPECIFIC NAMES:
```

That report carries no mathematical conclusion. `EXACT_CONSTRUCTION_REJECTED`
is available only when the author-confirmed exact expression was centrally
reprobed at its own seat and the receipt quotes Lean's literal diagnostic.

## Completion and publication

Completion requires every authored binding ready, every configured production
and root build green, the current readable ledger, and the author-configured
literal axiom surface for every release target. Run
`python3 tools/release_gate.py` for that certificate. Raw `git push` is disabled;
run `python3 tools/verified_push.py`, which may report success only when the
author-configured remote branch resolves to the exact certified commit.
<!-- END KERNEL GROUND TRUTH PROVENANCE -->
