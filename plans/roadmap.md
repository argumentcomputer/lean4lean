# Lean4Lean completion roadmap

**Status:** authoritative local roadmap, audited 2026-08-12 against the
committed fork, the current `jcb/formalization2` development bookmark, and
the uncommitted L4L-16 working copy; publication (moving
`origin/jcb/formalization2`) is a separate boundary and currently matches
the local bookmark at the L4L-18B checkpoint.

**Versioning.** `plans/roadmap.md` is intentionally tracked so the
status-bearing milestone ladder travels with each checkpoint, as are the
design/decision notes the ladder references
(`l4l-15-structure-eta-design.md`, `l4l-16-sort-inversion-decision.md`,
`l4l-18b-extension-interface-design.md`); every other file under `/plans`
remains ignored. The root-level `upstream-divergence.md` is the
tracked per-delta ledger and complements this roadmap. This document is
forward-looking only: completed milestones are deleted from the ladder when
they close, and their full narratives, hashes, and gate evidence live in this
file's git history and the checkpoint commit messages.

## 1. Mission and exact meaning of “complete”

Lean4Lean has two products:

1. `Lean4Lean/Theory/`: an implementation-independent model of Lean's kernel
   language, typing, definitional equality, environment growth, and the
   metatheory needed to use that model safely.
2. `Lean4Lean/Verify/`: a proof that the executable checker over `Lean.Expr`
   refines Theory.

External checkers translate their own expression representations into the
same Theory and prove their checkers sound there; lean4lean's job is to make
that possible from published Theory APIs alone. Success therefore means more
than deleting the original three inductive sorries.

The supported formalization is complete when all of the following hold:

- **Theory coverage:** every safe inductive declaration accepted by
  `Lean4Lean/Inductive/Add.lean` has a faithful Theory description, generated
  recursors and iota rules, and an `Ordered`/`WF` preservation proof. Temporary
  `stageN` predicates are gone from the public contract or have become proved
  implementation lemmas rather than permanent restrictions.
- **Live proof closure:** there are zero real `sorry` tokens in
  `Lean4Lean/Theory/` and `Lean4Lean/Verify/`. `Experimental/` is explicitly
  not part of the supported product; parked experiments must not be imported
  by a supported root.
- **No semantic placeholders:** `Verify.Environment.AddInduct` is inhabited
  and useful, `TrProj` has a justified semantics, and every currently empty or
  impossible verification path corresponds to a real checker execution.
- **Checker refinement:** the remaining Level/TypeChecker proof roots are
  proved, including recursor reduction, projection inference/reduction,
  structure eta, and unit-like comparison.
- **Trust is explicit:** all final roots have an audited `#print axioms`
  closure. No bridge axiom known to be false for the pinned Lean toolchain is
  reachable. Any unavoidable runtime contracts (for example pointer equality
  or opaque C++ implementations) are narrowly stated, tested, documented, and
  separated from the mathematical Theory.
- **Consumers are enabled:** a downstream checker can, from published
  `Lean4Lean.Theory.*` APIs alone, construct inductive block certificates with
  their lookup/pattern consequences, obtain a concrete projection-laws
  package, and derive literal well-formedness from a prelude contract.
  Consumer-side trusted oracles remain consumer trust boundaries by design,
  not lean4lean proof holes.
- **Upstreamability:** the fork delta is split into reviewable PRs, every
  deliberate divergence is tracked, and both the fork and upstream build at
  each release boundary.

This definition deliberately separates **proof-complete** (no sorries or
fake relations) from **trust-minimal** (no unnecessary custom axioms). Both are
required for the final release; they can be reached in separate milestones.

## 2. Current state

| Fact | Value |
|---|---|
| Ladder position | **L4L-16 active** (semantic environment bridge and sort inversion). L4L-18B completed first on 2026-08-12: proof-carrying pattern contractions, an explicit registered-equation join contract, beta-collapsed generated-iota/`quotDefEq` coverage, and `VEnv.LE` transport now form the fork-owned interface (design note `plans/l4l-18b-extension-interface-design.md`, ledger D020). The uncommitted working copy completes the L4L-16A slice and carries partial 16B/16C progress (§5) |
| Current formalization source | the L4L-18B checkpoint (jj change `oluxtqyk`) descends from the L4L-15B checkpoint `7c1e89fc` (jj change `xuzusmnl`) and is published at `jcb/formalization2` after the complete gate passed |
| Parent lineage | the L4L-15B implementation descends from the v4.33 reconciliation merge `99a7f8ae7b89` (second parent: digama `upstream/master` `b292275c`); Lean on v4.33.0 final, lean4-nix on `argumentcomputer/lean4-nix` (upstream pins v4.33.0-rc2 — ledger D018) |
| Fixed `master` baseline | `1a16b72d2e35932a82aa501beb29ef2c3d072580` — local `master` bookmark (corrected 2026-08-12; the row previously carried a fork formalization hash that no `master` ref ever pointed at). The v4.33 reconciliation merged the later digama `upstream/master` `b292275c` as its second parent without moving `master`; `origin/master` has since moved (see remote drift) |
| Remote drift (verified 2026-08-12) | digama `upstream/master` is two commits past the merged `b292275c`, at `3f6e8f92` ("perf: replay into a stage-2 environment"; "chore: enable the new level algorithm") — unabsorbed checker-side work landing in L4L-19A/B territory; reconcile-or-defer decision due at the L4L-16 boundary (§7). `origin/master` moved one commit to `715bfaff` ("verify: prove soundness of the standard library normalize") — already an ancestor of the fork's formalization line (the `eval_normalize`/`eval_normalize_total` proofs are in-tree), so content is absorbed and only the ref recording changed |
| Trust frontier | exactly 16 sorried proof declarations (10 Tier V, 6 Tier R; `NormalEq.parRed` carries two tokens) plus six kernel-rejection recovery declarations — 22 compiled allowlist entries — and 34 custom-axiom declarations; all are pinned by exact audits. L4L-15B removed the two structure-eta checker roots from the direct frontier; their inherited L4L-16--19 dependencies remain explicit in exact axiom guards |
| Gates | the full §6 gate is green on this checkpoint: the 212-job default Lake build, the Nix flake checks, the 22-entry exact sorry frontier, the Theory-only import/axiom audit, downstream-consumer and CLI checks, and whitespace hygiene |

### 2.1 What is green

Completed-milestone narratives, hashes, and gate evidence live in this
file's git history and the checkpoint commit messages; this section keeps
only the current claim surface and where each piece lives.

**Inductive Theory: analysis, generation, transactions.** One artifact
path runs from the raw/view `Normalization` boundary (computed shape plus
semantic `Normalization.WF env`) through dependent `Checked`/`CheckedBlock`
analysis — arbitrary nonempty non-nested mutual blocks, block-wide
target-family ordinals, generated-name uniqueness, the impredicative-Prop
exception — into mixed generation and the four-phase block transaction:
the public raw `addInduct` selects the block descriptor, its exact trace
supplies atomicity, freshness, lookups, monotonicity, and `Ordered`/WF
preservation, and the proof-carrying `GenerationCertificate`/
`addInductCertified` and `ValidationCertificate` boundaries remain
available (`addInductSingleton` survives only as a deprecated migration
wrapper). The accepted slice covers parameters, per-family indices,
direct and sibling recursion, recursive targets below Pi telescopes,
small and subsingleton-large elimination, exact K-target metadata, and
zero-/one-constructor generation. The consumer-neutral local-context
core lives in `Theory/LocalContext.lean`; `Theory/Literals.lean` owns
literal encodings, containment, primitive descriptors, and
`VEnv.PreludeReady` — an ordered exact Bool/Nat/Char/List/String
contract (generated recursors and iota rules for Bool/Nat/List;
`Char`/`String` opaque behind `Char.ofNat`/`String.ofList`) that derives
direct literal WF, is stable under ordered extension and fresh
constants, and stays independent of `Lean.Expr`; Verify retains only
traversal and proves its constructor result equal to the direct Theory
encoding.

**Mutual blocks.** `Normalization.BlockWF`, `CheckedBlock.WF`,
`ValidatedBlock.WF`, and `ValidationCertificate` give arbitrary blocks an
exact environment-indexed semantic package: shared-parameter agreement,
one semantic result universe, staged family constants, and a complete
source-order constructor trace including sibling recursion and recursion
beneath Pi binders. The real Tree/TreeList and IndexedTree/IndexedTreeList
fixtures run the ordinary kernel validators, inhabit every WF certificate,
compare all generated metadata with the kernel field by field, and replay
the four phase boundaries through `AddInductBlockTrace`,
`TrEnv'.inductBlock`, and `Aligned.addInductBlock` to actual
implementation `ConstMap`s; exact negatives pin the parameter-mismatch,
result-universe-mismatch, and reordered-family validation phases.

**Kernel parity and differential fixtures.** One integrated 14-row
positive matrix (Nat, Bool, List, Option, Prod, Unit — honestly
represented by the kernel's `PUnit` — Empty, Or, And, Eq, HEq, Fin,
Vector, Acc) reruns the ordinary producer and definitionally compares
every represented metadata field, recursor type, rule count, and iota
RHS; the consolidated 32-row rejection matrix covers the closure,
collision, universe/result-shape, raw/view-incoherence, normalization,
negativity/recursive-target, field-universe, and elimination/K failure
space. `AliasFormer`, `AliasRec`, and `NormalizationMatrix` prove
normalization is necessary and exactly aligned across alias positions,
with fuel-boundary, opaque, and non-defeq rejections. Elimination and
K-target decisions retain exact operational traces differentially
aligned with Theory generation, pinned by the
`Eq`/`And`/`Or`/`Nat`/source-universe fixtures and the `PUnit`/`Empty`
one-/zero-constructor boundary; Verify's `RecursorKMatches` makes a
type-correct recursor with wrong K metadata fail alignment.

**Verify refinement layer.** Checker-run certificates (`WhnfRun`,
`CheckTypeRun`, `IsDefEqRun`, `DefEqEvidence`, `TelDefEqEvidence`,
`NormalizedCtorRun`, `GenerationRun`) turn exact ordinary-checker
executions into Theory typing and definitional equality. The level
normalizer, subsumption, and equivalence layer is proved sound through
the verified project comparator (`NormLevel.le_eval`, `geq'_wf`,
`isEquiv_wf`) at standard-only closures with all-pairs core/project
differentials; the constructor-universe audit's non-Prop branch keeps
Lean's core `Level.geq` decision inside the ordinary validator's
existing acceptance boundary. The executable candidate producer
(`buildNormalizationCandidate`) retains recursively indexed traces,
structurally certified annotation consumption (runtime producer
validation, never a semantic proof field), and arbitrary-length
dependent `Produced` witnesses. Semantic-hierarchy assembly is automatic
under `Nonempty`: the staged owners — generation readiness, post-family
alignment independent of fresh-FVar identities, and the executable
pre-family replay with omitted recursive locals — close structurally on
real metadata (`ConstructorValidityMatrix`, `PropRecursiveBoundary`)
with nearest-kernel negatives, at the guarded transitional closure plus
the single exact L4L-01E producer-execution witness.

**End-to-end producer regressions.** AliasFormer, AnnotatedPi, and
`IndexedVec` each prove the exact successful whole
`buildNormalizationCandidate` call, inhabit the exact produced package
through the generic closure, and route both the certified Theory
transaction and the checked replay through it; `AnnotatedParam` closes
constructor-parameter parity against real kernel metadata, with a
well-typed but genuinely non-defeq prefix rejected at the exact
kernel-facing error. The operational L4L-01E package authority remains
the exact AnnotatedPi producer case. Negatives stay sharp: opaque
annotations, truncated/reordered views, missing/extra constructors,
recursive-local dependency, and the environment-free
closure/universe/name/result/collision matrix.

**Replay and the consumer certificate API.** The supported replay matrix
executes 25 actual-metadata transactions: the 19-row L4L-07 singleton
inventory (the 14 fixed rows plus the alias/normalization/annotation
fixtures, with Fin and Vector replaying over their real dependency
slices) plus the two-parameter `BiBox` dependency, both mutual tree
blocks, and three nested blocks. Every row retains its exact
input/output `ConstMap` and `VEnv`, input-map WF and dependency
ordering, data-bearing transaction trace, final roles, and recursor
lookup uniqueness. The consumer-neutral Theory API
`VInductDecl.BlockCertificate`/`NestedBlockCertificate` reconstructs the
raw `addInduct` result, `addInduct_le`, `addInduct_WF`, exact lookups,
freshness, uniqueness, registered rule membership/WF, rule closure, and
the L4L-10 recursor-pattern facts from one checked transaction; it
imports no Verify state, `Lean.Expr`, normalization oracle, or kernel
object, its WF root closes at the standard baseline (the rule/pattern
root adds `Classical.choice`), and neither reaches `sorryAx`. Verify's
unified matrix keeps one exact guarded `sorryAx`, solely through the
separately tracked projection/refinement frontier. A separate fresh
replay loads the 296-declaration compiled dependency closure of the
notation-heavy fixture into an empty kernel environment and checks every
declaration, so numerals, notation, lists, arrays, products,
conditionals, and strings exercise real compiled prelude dependencies.

**Nested inductives.** The stored Theory payload is the source
`VInductDecl` unchanged; nested support is additive.
`VInductDecl.nestedElimination?` (`Theory/NestedInductive.lean`) mirrors
`ElimNestedInductive` phase for phase against caller-supplied
environment-free target metadata, and `nestedStage3` gates acceptance by
flattening success plus generation readiness of the flattened block
through the unchanged block analyzers. The restoration σ (`restoreExpr`)
rebuilds the flattened block's generation artifacts onto the
`appendIndexAfter` inventory (`NestedBlockChecked`),
`VEnv.addInductNested` inserts source families/constructors plus
restored recursors/rules through the four block phases, and
`AddInductNestedTrace`, `NestedBlockChecked.WF`, and
`addInductNested_WF` mirror the block transaction's lemma suite through
`Ordered` preservation. Verify proves the Theory flattening equal to the
port's on the rose-tree, nested-indexed, and `DeepBi`/`BiBox` fixtures,
matches kernel accept/reject on four nearest negatives, and round-trips
the port's complete `Environment.addInductive` output against the Theory
artifacts (payload constants, recursors, K flags, rule RHSs,
`numNested`).

All three nested fixtures also replay from real stored metadata through
`TrEnv'.inductNested` (`Verify/Environment/NestedReplay.lean`), with
exact freshness chains, K-flag agreement, the literal rule fold, and
complete `NestedBlockChecked.WF` packages proved by direct concrete
typing derivations; the package closures are the standard baseline plus
the persistent-map container axioms and named `native_decide`
observations — no `sorryAx` — while the full `TrEnv'` roots carry the
usual guarded transitional checker closure. The generic σ̂ typed
transport (`Theory/Typing/NestedTransport.lean`: the `ConstInterp`
environment morphism and `IsDefEq.substConst` with its
`HasType`/`IsType`/`VConstant.WF`/`VDefEq.WF` corollaries) is proved as
the justification layer; its β-collapse bridge to the spine-collapsed
artifact substitution on generated artifacts remains available future
work, not a nested-coverage gap. Source nested declarations remain
rejected by the non-nested raw analyzer; the dedicated nested analyzer
and transaction own their flattened/restored recursors, rules, and
replay.

**Patterns.** Every certified block's iota rules are exact
`SimplePattern.iota` patterns with RHS templates, check lists, and
`RuleClosure` payload closedness (`Theory/Typing/InductivePattern.lean`;
implementation-independent shape layer in `Theory/Typing/Pattern.lean`).
The complete generic pattern-combinatorics obligations — `pat_simple`, match
inversion with rule-index/constructor recovery, rule distinctness, and the
`pat_uniq`/`pat_app_l`/`pat_app_l_uniq`/`pat_app_uniq` non-intersection
laws — are proved for one certified block from the certified inventories
at guarded `propext`/`Quot.sound`-level closures. The typed β-collapse
layer (`Theory/Typing/InductivePatternWF.lean`: `IsDefEq.appN_lamN`,
`varN_matches_paths`) is sorry-free, and `pat_wf` composes it into
pattern soundness: a successful match whose parameter and index checks
hold is definitionally equal to the instantiated RHS template, derived
from the exact rule defeq registered by `addInduct`, with the redex
arriving decomposed into recursor and constructor spines — precisely
what a verified reduction site holds — at exactly the Church–Rosser
development's transitional unique-typing closure, shedding `sorryAx`
automatically when L4L-16/17 land. The block-local assembler
(`Theory/Typing/InductivePatternEnv.lean`) builds environments whose
defeq set is exactly one certified block's generated rules plus
separately certified extension rules over a constant base
(`assembleEnv_defeqs`, `assembleEnv_WF`), and the union pattern set
`AssembledPat` couples the block's facts with each
`CertifiedExtension`'s payload and beta-collapsed coverage. L4L-18B removes
semantic soundness and raw-registration coverage from `Params`: each
`ParRed`/`CParRed`/`WHRed.extra` step carries the exact local `IsDefEqU`
certificate, while `Params.Extension.join` separately requires a typed
`CRDefEq` witness for every registered raw equation. Generated iota rules and
`quotDefEq` have kernel-checked `VExpr.stripLams` coverage, and named
`VEnv.LE.extra`/`extra_appN` transports preserve registered tower equality
under environment growth. No open-environment extension instance is
installed; both fixture blocks assemble over the empty base with their defeq
sets pinned to their generated rules.

**Projections.** `Theory/Projection.lean` is the consumer-neutral
projection boundary decided at L4L-13A/B. `VStructureView` restricts the
same one-family `GenerationChecked` artifact used by inductive
generation to the kernel structure class — exactly one constructor, no
indices, no recursive fields — and retains per-field sort levels.
Projections are recursor-encoded: `projectionCodes` computes, per field,
a dependent motive (`typeFn`, with earlier projections substituted into
later field types), the selecting minor, and the projector program,
with `projectionType?`/`project?` derived. `Registered`/`WF` tie a view
to exact environment lookups and generated iota rules, and
`VEnv.TrProj env U Γ view levels params idx major result` demands level
WF and arities, a well-formed parameter spine, the exact instantiated
major type, and the computed program; syntactic determinism
(`result_eq`) and environment extension (`mono`) are proved at
`propext`/`Quot.sound`. Verify's `TrProj` is now a fully constrained
compatibility wrapper (existential view/levels/params with
`view.name = structName`; no invented metadata), so the former Tier S
specification sorry is gone and roots that merely mention `TrExprS` no
longer inherit `sorryAx` through the projection branch. The
`DependentRecord` fixture — simultaneously parameterized,
universe-polymorphic, and dependent — pins the complete encoding
(`Tests/ProjectionExpressibility.lean`).

The L4L-14 structural package is proved: weakening, inverse weakening,
context-defeq transport, WF, uniqueness, term substitution, and universe
instantiation retain their compatibility names and are bundled by
`TrProj.structuralLaws`. L4L-15A proves `inferProj.WF`, both constructor and
string branches of `reduceProj.WF`, and the enclosing WHNF/translation
projection paths. Their exact guards distinguish the remaining inherited
Tier-R inversion dependency from projection-specific proof debt.

**Structure eta.** L4L-15B adds the registered lower-layer `VStructEta`
descriptor, monotone `VEnv.structEtas` registry, ordered subject-reduction
certificate, and the exact `VEnv.IsDefEq.structEta` contraction for complete
parameter spines. The checked-view bridge fixes reconstruction to the
deterministic recursor-encoded projector programs; `StructureEtaArtifact`
retains the exact host family/constructor alignment and registry membership.
Weakening, substitution, strong typing, inversion/discrimination,
standardization, nested transport, and every environment-schema consumer
carry the new case. `StructEq` retains oriented reconstruction
seeds and complete typed constructor-spine congruence; its named parallel
join records the constructor/iota, nesting, internal reduction, dependent
field, proof/Prop, and registered-`.extra` interactions. The unconditional
`tryEtaStructCore.WF` and `isDefEqUnitLike.WF` roots are now proved from the
registered artifact, removing both direct Tier V sorries. Exact axiom guards
pin registration, subject reduction, the primitive rule, Church--Rosser, and
both roots; the executable/kernel fixture matrix covers dependent
parameterized, zero-field, proof-field, Prop-valued, recursive,
multi-constructor, and indexed declarations.

**Theory-only consumer surface.** The L4L-15C audit moved the generic
`SpineWF` weakening/inversion laws to `Theory/Typing/UniqueTyping.lean`,
primitive-environment extension and Bool-literal typing to
`Theory/Literals.lean`, constant-absence and containment facts to their
Theory owners, and the Bool-to-elimination-mode conversion to
`Theory/Inductive.lean`. Verify keeps only deprecated compatibility shims
where a public name existed. `Tests/TheoryConsumerSurface.lean` imports no
Verify module and pins the availability and exact axiom closure of every
migrated API.

**Not claimed.** The remaining metatheory/checker roots. The beta-collapsed
certificates do not constitute the whole-live-environment
`Params.Extension` instance: L4L-16 must construct that instance through the
semantic bridge for every supported registered equation. Pattern coverage,
checks, and registry membership never imply an operational rewrite without
the local equality certificate. The nested fixtures prove the current
single-target, indexed, and queued deep two-parameter boundaries; nesting
classes beyond the accepted flattened-block analyzer remain rejected. The
296-declaration notation replay is a real fresh prelude prefix, not a claim
that an arbitrary whole kernel environment replays. Bare producer success is
never generation-shape authority or Theory semantics.

### 2.2 Live debt

The sorry audit (`Lean4Lean/Audit/SorryFrontier.lean`, a declaration-level
`sorryAx` allowlist over the compiled Theory/Verify surface) currently
accepts exactly 16 sorried proof declarations (`NormalEq.parRed` carries two
tokens), plus six deliberately kernel-rejected fixture recoveries that are
not proof debt. The compiled allowlist therefore contains 22 declarations:

| Area | Live debt |
|---|---|
| Core metatheory (Tier R) | `Injectivity.lean` x3; `UniqueTyping.lean` x1; `Projection.lean` x1; `ChurchRosser.lean` x2 |
| Checker verification (Tier V) | `Verify/Environment.lean` x2 (`addDecl.WF` — now only its `inductDecl` case — and the re-sorried `addQuot.WF`); `Boundaries.lean` x1 (upstream's `checkPrimitiveDef.WF`); `Extension.lean` x5 (the D017 checker-readiness transports); `WHNF.lean` x1; `InductiveFixtures.lean` x1 (`aliasFormerAlignmentRun` repair debt) |

All Tier V entries are L4L-19A/19B territory; the eight added at the v4.33
reconciliation are classified in ledger row D017. Non-sorry debt:

- The public inductive spec has complete one-family, non-nested mutual,
  and nested generation, preservation, metadata parity, environment
  replay, generic iota-pattern facts, pattern soundness (`pat_wf`), and
  the block-local pattern environment assembler. The complete supported
  replay matrix and consumer certificate API are now closed, but the accepted
  inductive language remains a growing subset rather than kernel-complete;
  projection semantics landed at L4L-13A/B and projection structural/checker
  verification closed at L4L-14/L4L-15A; structure eta and unit-like
  comparison closed at L4L-15B as a documented divergence (ledger D019) on
  the reconciled v4.33 base. `pat_wf` carries the Church–Rosser
  development's transitional unique-typing closure until L4L-16/17 close it.
- The L4L-15C consumer-neutral audit is complete. Generic spine laws,
  primitive-environment extension, literal typing, containment/absence, and
  elimination-mode conversion now have Theory-only homes, with a dedicated
  import-boundary/axiom audit and deprecated Verify shims only where needed.
- 34 project-specific `axiom` declarations outside `Experimental/`: 32 in
  `Verify/Axioms.lean` and two pointer-equality contracts in `PtrEq.lean`.
  The v4.33 reconciliation added five upstream reference equations for core
  level operations (`Level.normalize_eq`, `Level.mkMaxAux_eq`,
  `Level.skipExplicit_eq`, `Level.isExplicitSubsumedAux_eq`,
  `TreeMap.any_eq_any_toList`) consumed by upstream's `LevelStd`
  verification. Three cached-field equations from the group once false on
  older pins (`lean4#8554`) remain unproved and therefore forbidden
  contracts. The 2026-08-10 dead-axiom finding shrank: upstream's merged
  proofs use `TreeMap.all_eq_all_toList` again, so only
  `Level.mkLevelIMaxCore_eq`, `Expr.liftLooseBVars_eq`, and `Expr.equal_eq`
  remain deletion candidates, and their reachability must be re-run on the
  v4.33 tree at L4L-20A before deleting. 28 of the 32 carry `@[simp]`, so
  §3's simp ban is containment work not yet done. The L4L-13A/B `sorryAx`
  shed moved a large population of candidate/fixture roots into the
  sorry-free set with the cached-field trio (and other reference equations)
  still in their closures, so enforcing the "no forbidden axiom in a
  sorry-free supported root" CI rule waits on the actual L4L-20A retirement
  (prove the equations for the pinned implementation or take them off the
  trace-proof simp path).
- `addInductSingleton` (deprecated 2026-08-07) has zero callers outside
  its own shim block and is deletable as one self-contained block; the
  deprecation has not yet appeared in any published checkpoint, so time
  the removal against the consumer window.
- `NestedBlockCertificate` exposes the full lookup/freshness/WF/rule
  surface but no `ruleClosure`/`IotaPat` pattern facts; pattern facts are
  block-certificate-only until the σ̂ β-collapse bridge lands (L4L-19A).
- The semantic route to injectivity/unique typing runs through the in-tree
  `Experimental/` `SExpr`/`ShapeLogRel` development brought over by the
  v4.33 reconciliation; `plans/l4l-16-sort-inversion-decision.md` records
  the route decision. The 2026-08-12 working-copy audit supersedes that
  note's measured closure: the SExpr `Params` class is proof-carrying (the
  `extra_pat` axiom is deleted), the four-field `Params.Semantic` bridge
  interface exists, the current-judgment translation
  `VEnv.IsDefEqStrong.mkS` — including `IsDefEq.structEta` — is proved at
  `[propext, Quot.sound]`, and the endpoint `VEnv.IsDefEqU.sort_invS`
  closes at `[propext, sorryAx, Classical.choice, Quot.sound]` with no
  project axiom. The remaining `sorryAx` enters through `LR.adequacy`'s
  last constant-adequacy branch — the semantic-action child obligation,
  now isolated behind the `LR.constLamDefEq` helper; the definition-body
  branch is proved — and the SExpr infrastructure admissions
  (`LE_Interp.sound` is already clean); `ShapeLogRel`'s `Shape.WF.plift`
  additionally hides an admission behind a `stop` tactic that sorry-token
  counts do not see. Nothing there merges as a completed proof, and no
  experimental assumption substitutes for a supported root's accepted
  closure.
- `Lean4Lean.Experimental` is not among Lake's `defaultTargets`, so no §6
  gate ever builds it. L4L-16A explicitly parked the four pre-broken,
  unreferenced prototypes — `Stratified`, `StratifiedUntyped`, `Stronger`,
  and `ParallelReduction` — as import-compatible stubs. Their stale source
  targeted the pre-structure-eta/non-mutual judgment, and `Stronger` and
  `ParallelReduction` also carried admissions; none belongs on the L4L-16
  trust path. `Experimental/UniqueTyping.lean` was separately migrated to
  a strong-judgment compatibility endpoint: it no longer attempts the
  invalid recovery of lost strong evidence from weak `IsDefEq`.
- The dev-branch flake rework scoped `leanSrc` to a fileset, retiring the
  earlier `inputs.self.outPath` source-invalidation debt; remaining flake
  debt is cosmetic. The `system` deprecation warning comes from the
  pinned Nix stack and is non-fatal.
- The generated transitive axiom-closure report for all supported roots does
  not exist yet (L4L-20A); the reachability audit is partially established,
  not release-clean.

## 3. Trust policy

**Decision.** The axiom set of the current inductive **Theory** roots is
reasonable: only the standard logical baseline `propext`,
`Classical.choice`, `Quot.sound` (often a strict subset) and no axiom about
Lean's implementation behavior or representation. The axiom set of the
end-to-end **Verify** roots is not release-acceptable: their `sorryAx` and
collection/opaque implementation contracts are diagnostics while proofs
migrate, not foundations. Returning assembled hierarchies under `Nonempty` is
deliberate: it states semantic existence without using choice to extract a
data-bearing checker-selected view.

Current custom-axiom inventory (34 declarations; classification records
intended release treatment, not evidence the equations are true):

| Class | Count | Declarations | Release treatment |
|---|---:|---|---|
| Unproved cached-field equations, once false on older pins | 3 | `Level.hasParam_eq`, `Level.hasMVar_eq`, `Expr.looseBVarRange_eq` | Forbidden from every supported theorem root until proved for the pinned implementation |
| Reference equations documented as `@[implemented_by]` candidates | 17 | `Expr.replace_eq`, lift/lower, instantiate/range/reverse, abstract/range, `hasLooseBVar_eq`, `eqv_eq`, `equal_eq`; the v4.33 core level-operation equations `Level.normalize_eq`, `Level.mkMaxAux_eq`, `Level.skipExplicit_eq`, `Level.isExplicitSubsumedAux_eq` | Replace axioms with logical reference definitions and separately justified implementations |
| Persistent collection semantics | 6 | `TreeMap.all_eq_all_toList`, `TreeMap.any_eq_any_toList`; `PersistentArray.toList'_push`; hash-map insert, find, and contains/find agreement | Prove upstream or narrow to the actual WF/reachable-state invariant |
| Other opaque or representation-layout bridges | 5 | `Syntax.structEq_eq`; Level and Expr data-layout equations; `Level.mkLevelIMaxCore_eq` | Expose/prove upstream, narrow to the properties actually needed, or reject |
| Candidate platform contracts | 3 | `ptrEqExpr_eq`, `ptrEqConstantInfo_eq`, `Level.instLawfulBEqLevel` | May remain only in a named, version-pinned platform manifest with differential tests |

**Per-root closures.** Exact `#guard_msgs`/`#print axioms` guards in the
source are the authoritative per-root record; this roadmap does not mirror
them. Two standing facts frame that record: generic Theory transaction and
inductive roots close over the standard baseline only, while concrete Verify
packages, candidate/semantic runs, and replay fixtures inherit the
transitional closure (`sorryAx` via `TrProj`, pointer/reflection, layout, and
container contracts) — exactly guarded, release-blocking, and kept out of
Theory. The separation to preserve: once a checked generation value is
supplied, Theory-level consequences (for example iota-rule membership in the
final environment) close at `propext`/`Quot.sound` without inheriting the
Verify closure. Do not summarize any of this as “four acceptable axioms”: a
theorem's axiom set includes dependencies through its statement and inductive
types, so a proof can be locally sorry-free while its exported roots remain
transitively sorry-bearing. Only the generated transitive closure of each
named root is authoritative for release (L4L-20A).

| Boundary | Allowed during development | Required at its release gate |
|---|---|---|
| Computational `Checked` analysis, normalization shape, and generation | No axiom declaration; evaluation and equality fixtures must compute | Same; no oracle or opaque semantic bridge in acceptance/generation |
| Theory normalization validity, preservation, patterns, projection semantics, and consumer-facing Theory API | Any subset of `propext`, `Classical.choice`, `Quot.sound`; exact closure guarded per exported root | Same subset policy; zero `sorryAx`, zero project-specific axiom, and no import path to `Verify/Axioms` or `PtrEq` |
| Verify's mathematical refinement roots | Transitional bridges may remain only when named, classified, and exposed by an exact guard | Standard logical baseline only, unless the theorem is explicitly a platform-refinement theorem |
| Version-pinned platform adapter | A narrowly stated candidate contract with an owner, pinned Lean revision, removal issue, and tests | Only reviewed manifest entries; expected upper bound is the two pointer-equality implications and possibly lawful level `BEq`; never reachable from Theory or a consumer-facing semantic root |
| Fixtures and differential tests | May expose transitional dependencies to diagnose their path | They do not justify an axiom; release fixtures must have the closure required by the root they certify |

Apply these rules mechanically:

1. Treat the accepted baseline as a **set upper bound**. Keep exact
   `#guard_msgs` checks for named roots so growth or unexpected shrinkage
   receives review; audit computation and proof closure separately.
2. Reject `sorryAx` from every release root; a statement reaching a sorried
   relation is not release-clean merely because its proof body has no sorry.
3. Reject every known-false or unproved cache equation from supported roots
   and ban project-specific axioms from the global simp set; removing `[simp]`
   is containment, not discharge.
4. Expanding the logical baseline or platform manifest requires an explicit
   design decision; difficulty, convenience, or prior existence in
   `Verify/Axioms.lean` is not justification.
5. A consumer's trusted oracle stays in the consumer; it authorizes no
   lean4lean Theory axiom, assumed inductive oracle, or opaque projection
   relation.
6. A normalization view is untrusted data until it has both computed shape
   coherence and an environment-indexed `Normalization.WF` proof derived from
   checker/defeq evidence; neither Verify nor any consumer may assume a
   normalization oracle or add a reduction axiom.
7. Before closing a milestone checkbox, run both the exact guards and a
   generated transitive-closure check of the public roots; the same audit
   applies to every exported consumer-facing theorem.

## 4. Architecture and trust contract

These are invariants at every milestone.

1. **Theory points downward only.** `Lean4Lean/Theory/` imports no
   `Lean4Lean/Verify/`. Mathematical declarations mention `VExpr`, `VLevel`,
   `VEnv`, and proof objects, not `Lean.Expr`, `FVarId`, `ConstMap`, or any
   consumer's expression/address/catalog types.
2. **Consumer-neutral semantics.** No consumer-specific namespace, hash,
   address, cache, or checker-state type enters lean4lean; consumer-specific
   transport stays downstream.
3. **Theory-shaped APIs live in Theory.** Move literal encodings, the
   VExpr-only local-declaration core, primitive readiness, projection
   semantics, and generally useful pattern lemmas down. Leave `Lean.Expr`
   translation and `ConstMap` alignment in Verify. Old Verify paths re-export
   compatibility names while consumers migrate.
4. **Kernel parity is the adequacy test.** `Inductive/Add.lean` determines
   which safe declarations and metadata must be modeled. The Theory generator
   must compute its own output; proofs may compare it with the kernel but may
   not assume translated recursor shapes as hypotheses.
5. **Staging is monotone and temporary.** Every Stage-N predicate is an
   executable, proved subset with rejection fixtures. The final public
   contract covers the full safe implementation. Extend the shared
   `Checked`/`Normalization`/`GenerationChecked` contracts monotonically; do
   not reintroduce parallel Boolean analyses or downstream de Bruijn
   reconstruction, and never replace a missing case with `sorry`, an oracle,
   or an overstrong premise that real kernel output cannot satisfy.
6. **Checked analysis and normalization have explicit roles.** The raw
   `VInductDecl` is the stored constant payload. `Normalization` supplies a
   shape-compatible analysis view, and `Normalization.WF env` justifies that
   view by Theory defeq at the kernel's declaration stages. `Checked` is the
   environment-independent result computed from the view; `Checked.WF env`
   supplies its semantic typing evidence. Do not fold `VEnv`, `Lean.Expr`, or
   consumer-specific evidence into the computational analyzer, and do not
   treat a shape-compatible view as semantically valid without its WF proof.
7. **One accepted source/view pair, one artifact path.** A normalized block
   accepted by the public transaction must preserve the raw metadata payload,
   use the same checked view for every WHNF-sensitive decision, generate and
   preserve one artifact set, expose it through `AddInductSuccess`, and replay
   it in Verify. Parallel raw/view or direct/generalized generators are
   permitted only as short-lived proof migrations; no checkpoint may accept a
   case for which the public accessor returns a weaker or different
   recursor/rule set. The consumer-facing erasure is `GenerationCertificate`:
   it must couple the exact generation with its WF proof, and
   `addInductCertified` must remain definitionally the same computation as
   `addInductGeneration`. The proof may authorize preservation but may not
   affect generated artifacts or transaction control flow.
8. **Additive migrations first.** Before changing an existing exported Theory
   signature, add the new API and a compatibility theorem or re-export first;
   remove the old path only after a deprecation window for downstream
   consumers.
9. **Classic-module compatibility.** Do not introduce `module` headers in
   reachable files without a coordinated migration; downstream consumers use
   classic imports because lean4lean does.
10. **Axiom budget is checked per root.** New Theory roots may depend only on
   the accepted logical baseline (usually a subset). Verify bridge contracts
   need a separate, named manifest. “It was already in `Verify/Axioms.lean`”
   is not acceptance.
11. **Every fork divergence is tracked.** `upstream-divergence.md` carries one
   entry per semantic/API delta, its downstream impact, test, upstream
   issue/PR, and removal condition. Empty means fully upstreamed.

## 5. Milestone ladder

This is the sole status-bearing execution ladder and the only milestone
naming scheme. Exactly one milestone may be active; every later milestone is
queued, and no later milestone begins until the active one is complete. A
milestone completes only when its entire deliverable and every applicable §6
gate pass on one committed checkpoint; completed milestones are then removed
from this ladder, with their record kept in git history. Earlier partial
implementation counts as a prerequisite, never as partial credit. A suffixed
identifier such as L4L-01D2 is a full checkpoint with its own commit and
gates. Read-only design reconnaissance for a later milestone is allowed when
it changes the active design. Implementation and publication normally stay
serial; an explicitly independent later milestone may close as its own
audited checkpoint while the active milestone waits at a mandatory external
approval gate, provided this exception is recorded here and does not change
the blocked semantics. L4L-15C closed under this exception while L4L-15B
stood at the former structure-eta approval gate. This keeps one auditable
claim per checkpoint and
prevents several half-migrated public artifact paths from being live
simultaneously.

If upstream advances at a milestone boundary, insert an explicit
integration-only reconciliation checkpoint (as was done for v4.31) rather
than hiding merge work inside a semantic milestone.

### Metatheory closure (L4L-16–L4L-18A)

L4L-18B completed the prerequisite interface split on 2026-08-12 (design note
`plans/l4l-18b-extension-interface-design.md`, ledger D020). The L4L-16 route
spike (`plans/l4l-16-sort-inversion-decision.md`) can now target an explicit
`Params.Extension.join` semantic obligation instead of the impossible raw
lambda-tower `extra_pat` contract. Identifiers are stable names carried by
their deliverables; execution order is this list's order. This work proceeds
independently of upstream: no milestone blocks on upstream review or
interface approval, every interface departure is decided here and recorded,
and upstream engagement consolidates in the L4L-20C series.

**L4L-16 — semantic environment bridge and sort inversion.** Execute the
semantic route recorded in `plans/l4l-16-sort-inversion-decision.md` on the
L4L-18B interface, in suffixed checkpoints:

- *L4L-16A — bridge interface and judgment translation.* Largely
  implemented in the uncommitted working copy (audited 2026-08-12): the
  SExpr `Params` class is proof-carrying (`extra_pat` deleted), the
  five-field `Params.Semantic` bridge interface
  (`structureEta`/`ctor`/`defn`/`registered`/`iotaSite`) packages the
  environment-specific obligations, `VEnv.IsDefEqStrong.mkS` translates
  the current Theory judgment — including `IsDefEq.structEta` — at
  `[propext, Quot.sound]`, `IsDefEqStrong.defeq` and `Params.ctor_ty` are
  proved, and `VEnv.IsDefEqU.sort_invS` states the endpoint with no
  project axiom. The remaining L4L-16A cleanup is complete in the working
  copy: `Experimental/UniqueTyping.lean` now exposes only the valid strong
  sort-uniqueness compatibility theorem, while the four pre-broken,
  unreferenced prototypes are explicit import-compatible parked stubs
  (§2.2).
- *L4L-16B — SExpr infrastructure closure.* Discharge the remaining
  SExpr-side admissions, which are no longer
  `strong`/`defeq`/`ctor_ty` but: substitution (`IsDefEqLift.subst`),
  reduction/typing soundness (`WHRedS.defeq`,
  `InferType.hasType`/`whRed`, `InferTypeS.hasType`, the `.extra` cases
  of `WHRed.subst`/`weakU_inv`), `CRDefEq.trans`, and `ShapeLogRel`'s
  `Shape.WF.plift`, whose `stop` tactic must become a proof or an
  explicit sorry. The generic substitution-container repair is
  kernel-checked in the working copy: `Ctx.Subst.lift_r`, `lift`, `id`, and
  `one` now take the weakening/variable operations they actually require,
  and `Ctx.SubstEq.ofLift` supplies the binder-stable equality embedding.
  The under-specified `NormalEq.appDF` constructor now carries equality of
  its two instantiated codomains; this makes the application cases of
  `NormalEq.symm` and `NormalEq.weak'` kernel-checked rather than opaque
  transports. `CRDefEq.trans` and the remaining reduction/typing admissions
  are still open.
  The live stratified-S `mono`, `to_core`, and `isType` admissions are also
  discharged. Same-substitution `IsDefEq.subst`, heterogeneous
  `IsDefEqStrong.substCongr`/`subst`, and context conversion
  `Lookup.defeqDF_l'`/`IsDefEq.defeqDF_l'` are now kernel-checked. The
  three-way substitution interface is `Ctx.SubstEq`, and `LRS.PiInstDefEq`
  retains both the semantic codomain edge and its raw SExpr congruence.
  `Ctx.Subst.imp` now transports substitution evidence, and a genuinely
  typed substitution transports an entire proof-carrying
  `Pattern.Action`; consequently `WHRed.subst` and `WHRedS.subst`, including
  the generated-rule `.extra` branch, are kernel-checked under the narrowed
  SExpr-typing premise. `SExpr.SpineDefEq` now records a dependently typed
  pointwise equality between two application spines, with checked head
  congruence, left-spine projection, and reflexive construction from
  `SpineWF`; this is the raw alignment layer needed by the paired generated
  RHS certificate.
  `IsDefEqLift.subst` remains open because its old polymorphic
  `Ctx.Subst HasType` premise permits an arbitrary `HasType` relation and is
  therefore not a sound theorem statement; narrow that interface to lifted
  SExpr typings before proving it.
- *L4L-16C — constant adequacy.* Close the `LR.adequacy` constant
  branch: the definition-body evaluation route is token-closed but leans
  on the circular `hDef` premise noted below, and one admission remains
  at the reached pattern leaf. The structural `Const.lam` recursion is
  now kernel-checked: it transports the related application spine and Pi
  edge into `LR.constDefEq`, which discharges every semantic
  `bot`/`lam`/`ctor`/`indTy` case and follows the well-founded `R` child.
  The working copy now
  makes the local evidence boundary finite and uniform: `Pattern.Action`
  bundles membership, the exact match/captures, discharged checks, and the
  concrete local equality; `IsDefEqStrong.extra`, `WHRed.extra`, and
  `ParRed.extra` all consume that one certificate, its weakening transport
  is proved once, and both semantic soundness and adequacy consume it without
  recovering soundness from membership. The zero-arity definition bridge
  constructs an `Action` explicitly. The first half of the nonzero leaf
  contract is also kernel-checked: `LRS.CaptureDefEq`,
  `LE_Interp.Matches.varN_materialize`, and
  `LE_Interp.Matches.iota_materialize_exact` turn exact related recursor and
  constructor spines into the two concrete `MatchesS` witnesses, retain a
  typed logical-relation witness for every capture, and lift major-premise
  reductions under the recursor spine. The iota lemma deliberately keeps
  recursor captures at depth `n+1` and constructor fields at depth `n`.
  The transport-aware closure API is now kernel-checked as
  `LRS.CtorDefEq.Algebra`/`fold`: its `.unlift` handler receives the already
  folded high-level result, making pointwise projection of arbitrary refined
  fields unavailable by construction. The evaluator now also carries the
  invariant that its accumulated related spine is nonempty. The checked
  `LE_Interp.Matches.iota_of_pat_nonempty` inversion excludes definition
  patterns at the leaf, and `LR.PatternLeafDefEq`/`LR.IotaLeafDefEq` name the
  exact boundary with a checked adapter between them. `LR.DefEq.ctor'_inv`
  now uses the iota constructor's `.ctor` classification to rule out the
  eta-collapse branch of `WShape.ctor'` and exposes the exact
  `LRS.CtorDefEq` witness needed by the fold. Thus the remaining admission is
  no longer polymorphic over definitions and iota rules: it is exactly the
  iota leaf, whose finite contraction and generated-RHS congruence are now
  separate obligations. A subsequent interface audit found that the former four
  `Params.Semantic` fields could not recover a certified nonzero rule, its
  checks, or a typed local action from an arbitrary `Params.Pat` witness.
  The former provisional `iotaAction` obligation has now been replaced in
  the working copy by the evidence-rich `iotaSite` contract.  Its
  `Pattern.IotaTyping` input retains the typed recursor and constructor
  spines (with the exact constructor levels), while
  `Pattern.IotaReductionSite` exposes the registered tower, typed capture
  spine, beta collapse, checks, and RHS computation.  The generic
  `IotaReductionSite.action` construction applies the registered equation
  along that spine, so the bridge no longer returns a contraction oracle or
  any logical-relation conclusion. Every
  SExpr now also has a chosen well-formed Theory representative
  (`SExpr.reify`), semantic pattern matches reify to exact Theory matches, and
  RHS application commutes with that representation. `LR.constDefEq` carries
  the accumulated raw equality and result-type validity down to the leaf.
  Finally, `LR.iotaActions_of_exact` conditionally combines exact related recursor and
  constructor spines with that bridge to construct both concrete actions,
  pointwise capture relations, and both full weak-head reduction paths to the
  instantiated RHSs.  The fold-facing form is now kernel-checked without a
  canonical-relation assumption: `LRS.CaptureDefEqAt`,
  `LE_Interp.Matches.varN_materializeAt`,
  `LE_Interp.Matches.iota_materialize_exactAt`, and
  `LR.iotaActions_of_exactAt` keep constructor captures in an arbitrary `IH`
  and recursor captures in `LRS IH`; the older existential-depth theorems are
  wrappers over that adjacent-level API.  `LRS.IotaRHSDefEq` names the
  intended evidence-only congruence boundary for the fold. A second
  interface audit pins the missing live premise:
  semantic `MatchesS` erases the constructor levels, while
  `BlockGenerationChecked.pat_wf` requires the rule-instantiated constructor
  levels and typed recursor, constructor, and capture spines. Bare SExpr
  self-typing cannot recover those data without application/type inversion.
  The accumulator now carries `SExpr.SpineWF` certificates for both recursor
  applications, and `LRS.CtorDefEq.exact` retains both typed constructor
  spines and their head typings through the transport-aware fold. A leaf
  audit now shows that the provisional `LRS.IotaRHSDefEq` statement still
  erases one essential fact: at a variable RHS leaf the capture witness has
  its own existential SExpr type, but the contract supplies no alignment
  between that type and the whole RHS equality's type. Weak type uniqueness
  cannot manufacture that alignment before L4L-17. The next local boundary
  is therefore to retain a typed RHS/capture alignment witness in the
  reduction site (or equivalently narrow the congruence contract). The raw
  dependent-spine half of that boundary is now `SExpr.SpineDefEq`; the next
  step is to retain the ordered generated capture paths and their exact
  codomain/semantic alignment.  The transport core for that continuation is
  now kernel-checked: `LRS.DefEq.app` is polymorphic in the predecessor
  relation, `LogRel.LiftEquiv` packages the two fold transport laws, its
  `trans` and base-origin-only `cancelRight` operations compose/cancel those
  laws without projecting arbitrary high refinements, and `succ` transports
  the package through one `LRS` layer.  Capture and constructor-argument
  witnesses rebase through the same package.  The accumulator now packages
  its final application as `LR.PatternLeafSpine`: the raw last-Pi
  certificate, the major's logical relation at that exact domain, the
  remaining recursor arguments, and the semantic Pi edge are one dependent
  witness.  This package is threaded through every recursive
  `LR.constDefEq` lambda layer, and the focused adequacy target is green with
  that stronger invariant.  A fold audit then exposed the remaining
  non-root gap: `LRS.CtorDefEq.trans` deliberately erases the SExpr type of
  its midpoint, so two exact constructor leaves can carry unrelated
  existential field types even when their shared midpoint syntax agrees.
  Neither the aligned capture relation nor the generated-RHS application
  chain can compose those leaves without a type alignment, and the current
  coarse `LRS.TyDefEq.indTy` supplies only two `IndTyHead` witnesses.
  Retrying the rejected type-indexed `CtorDefEq` encoding merely moves the
  same issue to untyped weak-head subject expansion.  The next repair must
  therefore retain a composable canonical field-type alignment in exact
  constructor observations (derived from the live constructor certificate),
  or explicitly promote the required limited uniqueness lemma from L4L-17;
  it must not manufacture the midpoint type.  Once that boundary is
  kernel-checked, construct the repaired contract over `LE_Interp.recR`,
  instantiate `LRS.CtorDefEq.fold`, close the leaf, and replace the circular
  constant `hDef` premise with its live-environment construction. The
  accumulator typing currently inherits the
  open L4L-16B `WHRedS.defeq` obligation; `IsDefEq.subst` itself is now
  kernel-checked. The
  continuation's `.unlift` case must
  lower the whole result; arbitrary high-level field refinements cannot be
  projected pointwise without reviving the rejected `Shape.WF.plift`
  principle.
- *L4L-16D — live-environment instance.* The headline deliverable, not
  yet started: construct `Params` and `Params.Semantic` from a live
  `VEnv.WF`, covering definitions, mutual definitions, quotient rules,
  ordinary/block/nested inductive rules, and registered structure eta
  (the block-local assembler is a seed, not this bridge). Concretely:
  derive `classify` from the block certificates; populate `Pat` from
  generated iota/quot rules through the D020 `stripLams`/beta-collapsed
  coverage (`AssembledPat`, `CertifiedExtension`); discharge the
  non-overlap laws from the L4L-10B match-inversion library; and source
  the `Semantic` fields — `structureEta` from the L4L-15B registry
  certificate, `ctor` from generation certificates, `defn` from
  declaration history, `registered` from Theory's `IsDefEq.strong` plus
  beta collapse. Nested rules enter here as registered equations only;
  nested pattern facts stay L4L-19A.
- *L4L-16E — promotion.* Supported roots never import experiments: the
  consumed modules leave `Experimental/` with a stable API and a
  sorry-free path, the public `IsDefEqU.sort_inv` closes from the
  development, and the audit allowlist shrinks 22 → 21.

*Exit:* the public sorry is removed with an exact accepted axiom closure —
no `sorryAx`, no `extra_pat`-style axiom, and no environment oracle on the
path — and the route record is updated with any residual semantic-route
debt.

**L4L-17 — remaining injectivity and weakening inversion.** From the same
semantic development, prove `IsDefEqU.forallE_inv_stratified`,
`IsDefEqU.sort_forallE_inv`, `IsDefEqU.weakN_iff`, and
`VEnv.WF.registeredStructureHeadInversion` (whose projection consumers shed
`sorryAx` automatically); re-run `IsDefEq.uniq`/`uniqU`, context inversion,
and all downstream `#print axioms` checks. This milestone also owns the
weak-judgment scope retired from `Experimental/UniqueTyping.lean` at
L4L-16A: general type uniqueness over weak SExpr defeq and admissibility
of the heterogeneous `trans'` rule. The known design gap is
reflection: `sort_invS` reflects its SExpr conclusion back to `VLevel`
through `SLevel.mk` injectivity because SExpr levels are semantically
quotiented, but the adequacy development's SExpr-side `forallE_inv` and
`sort_forallE_inv` have no comparable route — nothing yet states that
SExpr defeq of `mk`-images yields `IsDefEqU` on the VExpr preimages, and
`weakN_iff`/`registeredStructureHeadInversion` have no SExpr-side
counterparts at all. Deciding the mk-faithfulness story (prove a
reflection/conservativity lemma, or restate adequacy to produce VEnv-side
conclusions directly) is the first task of this milestone.
*Exit:* the remaining public injectivity/inversion statements are sorry-free;
affected Theory and checker roots have exact accepted closures.

**L4L-18A — Church–Rosser `.extra` cases.** The holes in `NormalEq.parRed`
are the constant/application cases where a parallel step meets a
proof-carrying user-defeq pattern step. Use the generic `Params` pattern
combinatorics, L4L-10B's match
inversion/non-overlap library, and rule RHS congruence to prove the
commuting diagrams, keeping the theorem generic in `[Params]`. Neither hole
requires `[Params.Extension]`: each operational step already carries its
local equality certificate, while the global join instance is consumed only
by `IsDefEq.church_rosser`;
`ParRed.triangle`'s `.extra` case is the working template. The concrete
missing lemmas: (1) `NormalEq` match inversion/spine descent — the `≡ₚ`
analogue of the existing `ParRed` inversion, with proof irrelevance at a
pattern-spine head the genuinely open sub-case; (2) `Check.OK` transport
along `≡ₚ` and `≈`-equivalent level lists, extending `Check.OK.map`;
(3) level-congruence for `RHS.apply` on closed templates under
`Forall₂ (· ≈ ·)` — bridge `EqUpToLevels.instL` into a
`NormalEq`/`IsDefEq` congruence; (4) routine typing side conditions at
the transported match. The L4L-16 working copy's SExpr-side
`NormalEq`/`CRDefEq` admissions mirror the same commuting diagrams; the
Theory `parRed` holes are the only gated ones, so land the argument once
(prove the Theory holes and let the SExpr mirrors follow the same script)
rather than evolving two divergent proofs.
*Exit:* `ParRed.church_rosser`, normal-form uniqueness, and the live
standardization/head-reduction endpoints contain no hidden placeholder
assumptions.

### Checker closure (L4L-19A–L4L-19C)

Digama upstream carries two unabsorbed checker-side commits past the
reconciled `b292275c` (stage-2 environment replay; enabling the new level
algorithm — see the §2 remote-drift row) that land in exactly this
territory. The reconcile-or-defer decision made at the L4L-16 boundary
precedes detailed L4L-19 scoping; if deferred, repeat the check here.

**L4L-19A — recursor reduction verification.** Prove `reduceRecursor.WF` for
Quot and certified inductive rules, obtaining the selected rule, match,
checks, RHS translation, and result typing from the generated/translated
metadata — not from a global oracle. For nested blocks this requires the
σ̂ β-collapse bridge left open in `NestedTransport` — transporting the
flattened block's rule defeqs and pattern facts onto the restored
`appendIndexAfter` artifacts — and extending the certificate pattern
surface accordingly (`NestedBlockCertificate` currently exposes no
`ruleClosure`/`IotaPat` facts).
*Exit:* Quot, singleton, mutual, and nested recursor reductions pass;
enclosing WHNF roots have exact guards.

**L4L-19B — environment-to-checker closure.** Prove the remaining
nonprojection checker refinements (the v4.33 front-end `addDecl.WF` — now
only its `inductDecl` case — plus the D017 `checkPrimitiveDef.WF` and
extension-transport entries and the re-sorried `addQuot.WF`) and full
`TrEnv` over fixture environments containing ordinary
declarations, Quot, single/mutual/nested inductives, literals, structures,
and extension defeqs; state and audit the final executable-checker soundness
theorem over this full environment class.
*Exit:* the complete environment corpus and final checker root build with
exact closures; only the mechanical zero-sorry policy switch remains.

**L4L-19C — zero-sorry gate.** Remove every remaining supported Theory/Verify
sorry. Keep the audit allowlist exact throughout: every proof PR deletes
entries, and no PR may rename/move a sorry and merely update the allowlist.
At zero, reduce the allowlist to the deliberately kernel-rejected fixture
recoveries so any sorried declaration fails outright.
*Exit:* the proof-debt frontier is zero, only fixture-recovery entries
remain, and full gates pass.

### Trust closure and release (L4L-20A–L4L-20C)

**L4L-20A — axiom reachability and retirement.** Generate the actual
transitive closure for every supported root rather than hand-maintaining §3.
The root set contains at minimum the exported
checked-inductive/transaction/preservation roots and the consumer-facing
checked-inductive/projection API; the unique-typing, Church-Rosser,
standardization, and head-reduction endpoints; and the public checker
operations with the final executable-checker soundness theorem. Each row
records the root, layer, standard axioms, project axioms, §3 classification,
pinned Lean revision, and disposition; keep normalized output under version
control or as a deterministic CI artifact so a dependency change produces a
reviewable diff, generalizing the existing local `#guard_msgs` mechanism.

Acceptance states: (1) logical baseline; (2) platform contract — narrowly
stated, manifested, version-pinned, tested, absent from Theory roots;
(3) transitional bridge — named, classified, with a removal issue, never a
silent release assumption; (4) forbidden — known false on a supported
toolchain or unproved after the implementation changed.

Immediate pre-work is already scoped by the 2026-08-10 audit, as amended
2026-08-12: delete the three dead axioms (`Level.mkLevelIMaxCore_eq`,
`Expr.liftLooseBVars_eq`, `Expr.equal_eq`); upstream's merged v4.33 proofs
consume `TreeMap.all_eq_all_toList` again, and the unmerged
`origin/ap/prove-treemap-all` branch would turn that axiom into a theorem
at a future reconciliation. After the L4L-13A/B `sorryAx`
shed the forbidden cached-field trio sits in many sorry-free closures, so
the forbidden-axiom CI rule waits on their actual retirement rather than
a two-root cleanup. Then retire in risk order: the three remaining
cached-field equations; the
remaining reference equations (convert to logical definitions with
`@[implemented_by]` only when extensionally correct); the collection and
opaque/layout equations (replace with upstream theorems or narrowly bounded
WF lemmas); then decide the final platform budget explicitly (expected: the
two pointer-equality implications, possibly lawful level `BEq`). CI must
reject a new unclassified project axiom, any project axiom in a Theory root,
any forbidden axiom in a supported root, a retained platform contract without
manifest entry and tests, and `[simp]` on any project-specific axiom.
*Exit:* the report regenerates from a green build with every dependency in
an accepted state; no project axiom reaches Theory.

**L4L-20B — complete differential corpus.** Automate a harness that
elaborates fixture declarations with Lean, translates the resulting raw
environment metadata, constructs the justified analysis view, and compares it
with Theory generation, across the fixed inductive, projection, prelude, and
extension corpus. Compare failures as data: accepted/rejected, raw/view
normalization stage, generated constants, universe lists, field counts,
recursive positions, K flag, rule count, and every RHS.
*Exit:* CI compares acceptance phase, metadata, generated constants,
universes, recursive positions, flags, rules, and every RHS; all supported
cases pass.

**L4L-20C — upstream series and release.** Submit dependency-ordered semantic
PRs: (1) level-normalizer proofs and small generic lemmas; (2) Theory API
extraction with compatibility re-exports; (3) the staged inductive vertical
slice and fixtures; (4) indexed/normalization/small-elimination/
recursive-argument support; (5) mutual and nested support; (6) the pattern
package and Verify `AddInduct` alignment; (7) the projection structure view,
laws, and checker proofs; (8) injectivity/Church-Rosser completion; (9) the
remaining checker and axiom-minimization work. Do not rewrite published
`jcb/formalization2` checkpoints: each PR series is extracted onto a fresh
review branch rebased on its current upstream target. Do not mix the large
Nix/fork-infrastructure delta into proof PRs unless upstream asks. Record
every PR in the divergence ledger.
*Exit:* the final release revision is green; every fork delta is upstreamed
or has an owner, issue, and removal condition; release artifacts and
manifests are reproducible.

## 6. Gates and process

Every milestone must pass all applicable gates:

```text
lake build Lean4Lean.Theory Lean4Lean.Verify
lake build Lean4Lean.Audit.SorryFrontier
lake build
nix build --accept-flake-config .#lean4lean .#lake-dependency
nix flake check --accept-flake-config --print-build-logs
nix fmt --accept-flake-config -- --check flake.nix
git diff --check
```

The dev-branch fileset flake does not support eval-only checking
(`nix flake check --no-build` fails with "path '…-source' is not valid", as
documented at the `leanSrc` definition), so the flake gate builds for real;
non-Linux systems stay declared but ungated, matching dev CI.

Plain `lake build` covers Lake's `defaultTargets` (`Lean4Lean`,
`lean4lean`, `Lean4Lean.Theory`, `Lean4Lean.Verify`, `Lean4Lean.Tests`);
`Lean4Lean.Experimental` is a separate lib outside every gate and builds
only via `lake build Lean4Lean.Experimental`. A red experiment therefore
never blocks a checkpoint, and conversely a green gate claims nothing
about `Experimental/` — promotion at L4L-16E is what moves the semantic
development into the gated surface.

The flake is authoritative: milestone evidence must use the pinned Nix
toolchain and dependencies. The Lake commands above run directly from the
already active `nix develop` shell; from outside that shell,
`nix develop --command lake ...` is equivalent. Elan or another host `lake`
never substitutes for the pinned-shell Lake builds, `nix build`, or the flake
checks above.

Additionally:

- all new fixtures build in a default proof target;
- new theorem roots have checked `#print axioms` output;
- every named root satisfies the boundary-specific axiom threshold in §3,
  with no `sorryAx` or project-specific dependency in a Theory root;
- `rg '^import Lean4Lean.Verify' Lean4Lean/Theory` is empty;
- every source/view pair accepted by the public checked transaction is
  generated and preserved by the same artifact path; temporary
  direct/generalized or raw/normalized migration functions are not both
  semantically live at a checkpoint;
- exported Theory names change only additively, through compatibility
  re-exports and a deprecation window;
- the kernel differential matrix is green for inductive/projection changes.

**Publication.** Publish only after the complete gate passes on one committed
checkpoint; never publish a red or semantically split state (for example
midway through an artifact or transaction switch). Only
`origin/jcb/formalization2` moves; local/remote `master` and every
digama/upstream ref move only at explicit reconciliation checkpoints, and
remote-ref verification is part of each publication. Keep published
checkpoints recoverable, and refresh the divergence ledger and sorry-frontier
wording with each checkpoint.

**Downstream consumers.** Lean4Lean is an independent upstream. Downstream
projects pin published green checkpoints and are responsible for their own
migrations, audits, and pin cadence; their demand analyses, oracle
constructions, and migration protocols live in their own repositories and do
not gate this ladder. Consumer worktrees, lockfiles, and branches stay out of
lean4lean commits. What this repository guarantees to consumers: published
checkpoints pass the complete gate; exported Theory APIs are consumer-neutral
and change additively with compatibility re-exports; the trust story (exact
per-root guards, the tracked sorry frontier, the divergence ledger) travels
with every checkpoint; and consumer-facing semantic obligations are met by
strengthening the checked-block API here, never by asking a consumer to
assume an oracle or axiom.

## 7. Principal risks and decision points

- **Checkpoint drift.** The `jcb/formalization2` line is ahead of `master`,
  and the local head runs ahead of `origin/jcb/formalization2` between
  publications. Keep published checkpoints recoverable, require
  Linux/Darwin CI builds at release boundaries, and record any replacement
  hash here.
- **A subset masquerading as the spec.** A sorry-free `stageN` definition can
  still be incomplete. Final acceptance is kernel coverage plus negative
  agreement, not the absence of sorries.
- **Analyzer/artifact drift.** Guarded for the current subset: analysis,
  public accessors, preservation, transaction output, and Verify metadata all
  consume the same generalized artifacts. Keep the kernel-equality and alias
  fixtures as regressions; older direct/raw-only definitions remain
  compatibility specifications only.
- **Normalization as an accidental oracle.** Shape equality alone does not
  justify a rewritten declaration, and whole-type defeq alone does not
  identify raw binder positions. Require `Normalization.WF`, structural
  raw/view pairing, and derivation from checker or consumer defeq evidence.
  Runtime agreement with opaque `consumeTypeAnnotations` is a producer
  consistency check, never semantic authority. Never accept an arbitrary
  supplied view; never repair a missing reduction theorem with a custom
  axiom.
- **Raw de Bruijn scaling.** Indexed, mutual, and recursive-Pi rules multiply
  lift/inst arithmetic. Keep moving normalized evidence into the descriptor
  and telescope lemmas rather than duplicating index calculations.
- **Structure eta changes Theory as a tracked divergence.** The new defeq
  constructor affects injectivity, confluence, standardization, and
  downstream consumers. The design note and ledger entry come first
  (decision 2026-08-11); upstream review moves to the L4L-20C PR series,
  and every reconciliation checkpoint revisits the divergence.
- **Pattern-interface divergence.** The upstream `Params` fields
  (`extra_pat`'s syntactic match, `pat_wf`'s bare-`HasType` premise)
  cannot be satisfied by tower-registered environments, including
  `quotDefEq`. L4L-18B resolves this with proof-carrying contractions,
  beta-collapsed coverage, and `Params.Extension.join` (ledger D020).
  The residual risks are a larger upstream-review surface at L4L-20C and
  reconciliation conflicts wherever upstream's own `Params` and
  experimental work move — keep the redesign minimal, ledgered, and behind
  compatibility shims where feasible.
- **Research-branch optimism.** The in-tree `SExpr`/`ShapeLogRel`
  development is evidence of a viable path, not a drop-in solution. The
  2026-08-12 spike measured its live closure (`sorryAx` plus the
  `Params.extra_pat` project axiom); the same day's working-copy rebuild
  eliminated the project axiom (`sort_invS` at the standard baseline plus
  `sorryAx`), leaving the obligations scoped at L4L-16A–E. The remaining
  optimism hazard is concentrated in L4L-16D: the live-environment
  instance is the one segment of the route that has never been executed
  end to end.
- **Unsound bridge axioms.** Some cache equations were documented false on
  older pins and remain unproved. Zero sorries is not a soundness claim until
  final-root axiom reachability is clean.
- **Upstream collision.** Repeat the ancestry and overlap check at every
  milestone boundary; if upstream advances again, insert another explicit
  integration checkpoint rather than hiding merge work inside a semantic
  milestone. The 2026-08-12 check found digama `upstream/master` two
  checker-side commits past the merged `b292275c` (§2 remote-drift row);
  the reconcile-or-defer decision is due at the L4L-16 boundary.
  `origin/master`'s one-commit advance is already in the fork's ancestry
  and needs no action.
- **Scope leakage from Experimental.** No supported root may import
  experiments. Promote a proof only after removing its experimental sorries
  and giving it a stable API.
