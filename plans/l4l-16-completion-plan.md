# L4L-16 completion plan

Date: 2026-08-13 (audit window 04:50–05:10 EDT)
Author: fresh audit session (Claude), commissioned because L4L-16 "looks
stuck or spinning."
Status: proposal for review. No Experimental/ or roadmap edits were made by
this session. All measurements below were taken against the live working
copy and its freshly rebuilt oleans; the working copy is a **moving
target** (see §1.0), so line numbers are approximate by ±20.

## 0. TL;DR

L4L-16 is much closer to done than the roadmap's tone suggests, and the
spinning has an identifiable root cause. The measured critical path to the
gate theorem is **one file-local sorry** (the adequacy iota leaf, which
decomposes into three named obligations O1–O3, §3) **plus one `SExpr.lean`
lemma** (`WHRedS.defeq`, consumed by the leaf machinery via dot-notation —
the only one of the nine SExpr sorries on the gate path). Of the other
eight, two are false as stated, and one (`CRDefEq.trans`) is a disguised
port of all of L4L-18A. The fix is a milestone re-cut: narrow L4L-16B to
what the gate consumes, resolve the leaf by an explicit interface decision
instead of a sixth transport-infrastructure repair, move the
Church–Rosser-shaped debt into L4L-18A where it belongs, and stage
L4L-16D (the only never-executed segment). Two of L4L-17's four targets
land free when the leaf closes; L4L-17 re-scopes to reflection +
`weakN_iff` + structure-head inversion. The live worker has already begun
the recommended leaf repair (the `PatternLeafSpine.aligned` refactor) —
this plan endorses completing it, with the endpoint pinned in advance.

## 1. Measured state (evidence, not narrative)

### 1.0 Operational context

- Two other AI sessions have this checkout as cwd: a codex session on
  pts/3 (running since Aug 10, ~50 h CPU) and a Claude session on pts/11
  (since Aug 12). One of them was still editing
  `ShapeLogRel.lean`/`ShapeLogRelAdequacy.lean` at 05:02 and rebuilding at
  05:03 during this audit. The Claude peer `navigatrix-1b` explicitly does
  **not** work in this repo (confirmed by direct message).
- The uncommitted working copy is one 18h+ mega-change on top of the
  L4L-18B checkpoint (`oluxtqyk`/`96aeab5c`), mixing: completed L4L-16A,
  partial 16B, near-complete 16C, four file parkings, and ~300 lines of
  roadmap narrative. During the audit window `SExpr.lean` was briefly
  red (a `WithLift.defeq` projection error) and was fixed at 04:56 —
  i.e. the working copy has been oscillating red/green.

### 1.1 The gate path is one sorry wide

Measured with `#print axioms` against the 05:03 oleans:

| Declaration | Closure |
|---|---|
| `VEnv.IsDefEqU.sort_invS` (the L4L-16 endpoint) | `[propext, sorryAx, Classical.choice, Quot.sound]` — **no project axiom** |
| `SExpr.LR.adequacy` | same |
| `SExpr.LE_Interp.sound` | `[propext, Classical.choice, Quot.sound]` — clean |
| `VEnv.IsDefEqStrong.mkS` (judgment translation incl. structEta) | `[propext, Quot.sound]` — clean |
| `SExpr.LRS.CtorDefEq.fold`, `SExpr.LR.DefEq.ctor'_inv` | clean |
| `SExpr.forallE_inv`, `SExpr.sort_forallE_inv` | sorryAx **only via the leaf** |

The `sorryAx` sources on the route are exactly two:

1. the adequacy leaf (`ShapeLogRelAdequacy.lean:~1228`, the body of
   `LR.PatternLeafDefEq.of_iota`'s `by` block inside `LR.adequacy`'s
   const case, downstream of the proved `ctor'_inv`), and
2. `SExpr.WHRedS.defeq` (SExpr.lean:~2920), consumed **via dot-notation**
   (`hredX.defeq`, `hMajorX.defeq`) at ≥6 sites in the adequacy file
   (495/496/507/518 inside the proved `LR.iotaActions_of_exactAt`, plus
   839, 1125). A literal-name grep misses these — which is how one audit
   pass wrongly concluded no SExpr sorry is on the path.

The other eight `SExpr.lean` sorries are not referenced by
`ShapeLogRel.lean` or `ShapeLogRelAdequacy.lean`.

Bonus: `SExpr.forallE_inv` and `SExpr.sort_forallE_inv` already exist and
are sorry-free **except through the leaf** — closing the leaf delivers the
SExpr side of two L4L-17 targets simultaneously.

### 1.2 The L4L-16B list is mis-scoped

Current live `SExpr.lean` sorries (9), triaged:

| # | Decl (≈line) | Verdict |
|---|---|---|
| S1 | `IsDefEqLift.subst` (2655) | **False as stated** — `HasType` is a free section variable, so the premise admits the trivial relation. The sound weak form `substDefEq` (2648) is already proved. Restate with a `:↑`-valued `Ctx.Subst` or **delete** if no consumer needs the lifted conclusion. |
| S2 | `WHRed.weakU_inv` `.extra` (2796) | Real but bounded: needs lowering of `Pattern.Action`'s two `IsDefEq` fields; match-lowering (`matchesS_lift'`) already proved. Route: restate `Action`'s `checked`/`sound` at `:↑`, which also subsumes S1's consumer. |
| S3 | `WHRedS.defeq` (2919) | **On the gate path now** (measured: 6 dot-notation call sites in the adequacy file, §1.1). As stated it needs a weak-`IsDefEq` typing-inversion layer (`isType`, `app_inv`, `lam_inv`…) that does not exist SExpr-side and is uniqueness-strength — see §2.3 circularity. Do not prove as stated; close via the narrowed form in §3 (16C′ step 2). |
| S4/S5 | `InferType.hasType`/`InferTypeS.hasType` (3017/3097) | Routine ports **once S3-shaped facts exist**; S5 is a 3-line corollary. |
| S6 | `CRDefEq.trans` (3239) | **A whole-module port in disguise**: needs `CParRed`, `ParRed.triangle`, `ParRed.church_rosser`, `NormalEq.trans`, `NormalEq.parRed` — the last is itself the open L4L-18A Theory debt. Move out of L4L-16 entirely. |
| S7–S9 | `InferType.whRed` cases (3263–3269) | **Statement wrong** (`▷` is syntactic; no conversion rule; all three cases unprovable as written). Restate (`▷*`/up-to-defeq) or delete; no Theory analogue exists. |

Also stale in the roadmap: `Shape.WF.plift`'s "hidden `stop` admission"
does not exist — lines ~1687–1754 of `ShapeLogRel.lean` are a block
comment with zero consumers, and the file is **live-sorry-free**. The
architectural replacement (`CtorDefEq.lift/unlift` + `LogRel.LiftEquiv`)
is already in place and proved. Delete the commented block and strike the
ledger item. (Also: `Params.Semantic` now has six fields, not five —
`iotaRule` is undocumented.)

### 1.3 L4L-16D is genuinely at zero, with enumerated gaps

No `Params` or `Params.Semantic` instance exists anywhere. Known gaps for
a live instance:

- SExpr `Params`: `classify`, `Pat`, `pat_wf`, and the six combinatorial
  laws must be sourced from block certificates; `AssembledPat` currently
  supplies only `pat_simple` and `ext_covers` — the four uniqueness/
  non-overlap laws exist only block-locally (`IotaPat.*`) and there is no
  cross-term (block-rule vs extension-rule) non-overlap lemma.
- SExpr `Params.Semantic`: six fields (`structureEta`, `ctor`, `defn`,
  `iotaRule`, `iotaSite`, `registered`) to be populated from the L4L-15B
  eta registry, generation certificates, declaration history, and
  D020 beta-collapsed coverage respectively.
- Theory-side `Params`/`Params.Extension.join` (consumed only by
  `IsDefEq.church_rosser`) additionally needs four structEta/forallE
  inversion fields with **no current supplier** — weakN-inversion-strength
  facts, i.e. L4L-17 territory. It is NOT needed for `sort_inv`.

### 1.4 Theory frontier interaction

`IsDefEq.uniq` consumes exactly `sort_inv` (×9) and
`forallE_inv_stratified` (×1); nothing else on the Tier-R list. So the
semantic route, once reflected, unlocks the entire transitional
unique-typing closure — which is what `pat_wf` and the projection
consumers shed `sorryAx` on.

## 2. Root-cause of the spinning

1. **The leaf is a design decision being treated as a lemma.** The
   working-copy roadmap records five successive infrastructure repairs at
   the leaf (`iotaSite` contract, `SpineDefEq`, `LiftEquiv`,
   `PatternLeafSpine`, `CtorDefEq` fold audit), each ending in the same
   discovery: exact constructor observations erase the SExpr type of
   their midpoint/captures, and no amount of transport machinery can
   re-manufacture it. The roadmap itself names the two exits (carry the
   canonical type as data, or promote a limited uniqueness lemma) — and
   the sessions kept building a third thing instead.
2. **A mis-drawn milestone boundary legitimized off-path work.**
   "L4L-16B = close all SExpr admissions" put two false statements, one
   L4L-18A-sized port, and several gate-irrelevant lemmas on the active
   list. Effort flowed to what was listed, not to what the exit consumes.
3. **A latent circularity in the repair machinery.** The already-proved
   leaf machinery (`iotaActions_of_exactAt` and friends) routes typing
   through the sorried `WHRedS.defeq`, whose honest generic proof needs
   weak-judgment typing inversion — the very uniqueness-strength
   frontier this development exists to prove. Theory "solves" this only
   inside its transitional (sorry-bearing) closure. Any repair that
   keeps the generic dependency re-imports the problem. The way out is
   that every call site has stronger evidence in scope than the generic
   lemma assumes (carried `Action.sound` equalities, full `SpineWF`
   certificates), so a certificate-carrying variant suffices — see
   §3 16C′ "S3-narrow".
4. **Process:** 18+ hours of uncommitted mega-change, red↔green
   oscillation, roadmap-as-lab-notebook, and (this morning) two sessions
   plus an auditor in the same working copy. The ladder's own
   one-auditable-claim-per-checkpoint rule has been suspended in practice.

## 3. The re-cut

Principle: **L4L-16's exit is the promotion of `sort_inv` at the accepted
closure. Everything not consumed by that path moves to the milestone that
consumes it.**

### L4L-16B′ — SExpr infrastructure, narrowed

Keep only:
- S2 via the `Pattern.Action`-at-`:↑` restatement (also settles S1's
  consumer question).
- S1: restate-or-delete (decide by grepping consumers; expected: delete).
- S7–S9: restate `InferType.whRed` with a `▷*`/up-to-defeq conclusion or
  delete (no consumer found).
- Delete the commented `Shape.WF.plift` block; correct the roadmap claims
  (§1.2).

Explicitly move out:
- S6 `CRDefEq.trans` → L4L-18A′ (it IS Church–Rosser).
- S3/S4/S5 → deferred until §3's leaf decision determines whether any
  accumulator-typing fact is needed at all, and in what judgment (see
  next).

### L4L-16C′ — close the leaf by decision, not accretion

The leaf (`~1228`) decomposes into three named obligations (per the
2026-08-13 audit; details in the audit agent's map):

- **O1 — a composable fold motive over `LRS.CtorDefEq`.** The blocker.
  `CtorDefEq.exact` hides its head/result types (`CHead, CHead', A, A'`)
  existentially, so the `.trans` handler of any `CtorDefEq.fold` has a
  shared midpoint `N` with **no exportable typing**. Fix (Option A,
  recommended, **already begun by the live worker** — the
  `PatternLeafSpine.recArgs → aligned : LRS.CtorSpineDefEq` refactor):
  restate `.exact` to carry `LRS.CtorSpineDefEq` — which already shares
  **one** result type `A` and one domain `D` per field — and give
  `CtorSpineDefEq` a `trans`. That `trans` does NOT need general
  uniqueness: `SpineWF`/`SpineDefEq` conversion steps each **carry**
  their defeq certificate, and the constructor's head type is pinned
  **syntactically** as a Pi telescope by the live certificate
  (`CtorBundle.rhs` is literally `Ts.foldr .forallE …`, supplied by
  `Params.Semantic.ctor` into `IsDefEqStrong.const`'s `F`/`hF` fields).
  So the midpoint alignment composes from carried conversions plus the
  certificate telescope — nothing is manufactured. Update the two
  construction sites (`constDefEq` ctor case ~961; nullary case ~1264)
  and the `Algebra`/`fold` handlers.
  **Option B (fallback only):** the scoped alignment lemma
  "`SpineWF Γ CHead args.reverse A → SpineWF Γ CHead args.reverse A' →
  ∃ u, Γ ⊢ A ≡ A' : .sort u` for a certificate-pinned head" — L4L-17
  content promoted into 16C. Try it only if A's encoding change
  explodes.
- **O2 — mechanical glue.** With O1's `.exact` handler,
  `LRS.iotaDefEq_of_exactAt` (proved, currently unconsumed) is a direct
  fit; all its remaining inputs are already in scope at the sorry.
- **O3 — `LRS.IotaRHSDefEq`, the one genuinely new proof.** Reduce via
  `of_nonbot` (proved); variable-RHS leaves are discharged by the
  supplied `CaptureDefEqAligned` family (already type-aligned — no
  uniqueness needed). The remaining fixed-tower head case is to be
  proved by **well-founded recursion on the semantic `R`-edges via
  `LE_Interp.recR`** (the design comment at the `IotaRHSDefEq` def says
  exactly this), then the application chain closes by `LRS.DefEq.app`.
  No environment or reduction oracle.

Plus **S3 (revised 2026-08-13 after reading the site contracts —
supersedes "S3-narrow")**: the four live `.defeq` call sites reduce to
two facts about the ROOT pair only — the spine-redex self-typing at the
package `A` (from `htermX` plus major-position congruence) and
`IotaTyping.majorEq` (the typed collapse `majorX ≡ ctorSpine :
majorType`). Neither can be discharged by a certificate-carrying
variant alone: the major's stored reduction is an arbitrary weak-head
sequence, and per-step subject reduction hits beta/extra cases needing
typing inversion. The honest route is the one the `▷` layer was built
for — the **InferType principal-types bootstrap**: syntactic
`InferType.determ` (already proved) substitutes for type uniqueness;
prove inference completeness over `IsDefEq` (each case computes the
principal type and connects it to the derivation's type by the IH, no
uniqueness needed), restate `InferType.whRed` up-to-defeq (the false
exact-form was deleted at 16B′), restore `InferType.subst`/`inst` with
a `:↑`-valued substitution premise, and derive the needed `⤳* → ≡`
conversions from principal-type subject reduction. S4/S5 close en route.
This is a real sub-development (days), and it is confined to the ROOT
pair: intermediate chain links never need it (see the chain addendum).

Note on `hDef`: the "circular constant premise" is a field of
`IsDefEqStrong.const` discharged by `mkS` out of
`Params.Semantic.defn` — it needs **no separate 16C work**; its
live-environment construction is exactly 16D's `defn` field.

Rule: if the chosen option hits a second wall, STOP and re-derive the
mathematical obligation in this file before writing more Lean. No sixth
transport layer.

**O1 design addendum (2026-08-13, recorded before implementation).**
Deriving the fold motive abstractly hit the two-strikes rule: every
variant that runs the typed iota-site construction at *intermediate*
fold nodes (trans midpoints, or exact nodes reached inside the free
closure) terminates at the same irreducible brick — reconciling two weak
typings of one term (midpoint, or reduct spine) without inversion, which
is the uniqueness-strength frontier itself. `Pattern.Action` sites for
intermediate pairs are therefore impossible by design, not by missing
lemmas: the free closure's midpoints are genuinely untyped up to
weak-head expansion (`LogRel.whr` is deliberately an untyped iff).
Decided architecture — **root-anchored capture-chain fold**:

- The fold motive carries NO typing and NO sites: only (i) each
  endpoint's weak-head reduction to its constructor spine, and (ii)
  composable per-field semantic relations (`IH`-level) between the two
  spines' fields, plus the head/level agreement.
- `trans` composes via weak-head determinism (`WHRedS.inferType`
  uniqueness: the shared midpoint's two constructor-spine reducts are
  syntactically equal, so field columns literally coincide) and the
  relation's PER laws; `whr`/`unwhr` via `WHRedS.determ_l`; `mono` via
  `mono_l`; `lift`/`unlift` via the carried `LiftEquiv` fields; `left`/
  `symm` via the PER laws.
- The typed layer (both `Pattern.IotaTyping` sites, the `Action`s, the
  `PathSpineWF` capture spines) is built ONCE, at the root pair, where
  the `PatternLeafSpine` package supplies every typing; the fold's
  output supplies the root-to-root capture relations that
  `IotaRHSDefEq` consumes.

Implementation status (2026-08-13, checkpoint `wolxmups`): the
syntactic midpoint-agreement layer is kernel-checked in `SExpr.lean` —
`Pattern.WF.arity_head`, `spine_inj`, `Params.matchesS_symb_head`,
`WHNF.ctorSpine`, `WHRedS.ctorSpine_eq`, and `WHRedS.ctorSpine_determ`
(two weak-head reductions of one term onto classified constructor
spines land on the same syntactic spine). Remaining chain work, in
order: (1) define `LRS.CtorLink`/`LRS.CtorChain` (links = `.exact`
field bundles between adjacent spines; concatenation via
`ctorSpine_determ`); (2) `CtorDefEq.toChain` by induction on the free
closure — `left`/`symm` need the link mirror (either add the
right-anchored aligned spine to `.exact`, free at both construction
sites since they pass the same head twice, or re-anchor
semantically); `whr`/`unwhr` via `WHRedS.determ_l`; the open
sub-design is `mono`/`lift`/`unlift` bookkeeping — per-field
`HasType` side conditions for `mono_l` must travel in the links
(`CtorSpineDefEq.cons` already stores `hp`), and cross-level moves
compose stored `LiftEquiv`s; if a zigzag resists `trans`/`cancelRight`
reduction, keep links at their native levels and let the consumer
rebase, since links carry their own `HasType`s; (3) per-link
consumption: each link certifies its own iota contraction pair with
conclusions glued by `(LRS IH).trans` at the package-fixed result type,
with the root endpoints attached by `whr`-expansion.

Verification condition checked before implementation: the per-field
composition step needs `IH.DefEq x y D p a` and `IH.DefEq y z D' p a`
(same syntactic `y`, same shapes, two validity types) to compose.
**Resolved (2026-08-13, by reading `LRS.DefEq`'s definition):** the
concrete relation is type-independent modulo validity — at `.sort`
type-shapes `DefEq` ignores its type argument entirely, at `.indTy` the
only type-dependence is the `IndTyHead` conjunct (supplied by the target
type's own validity), and at `.forallE` every consumed component
(domain reduction, domain validity, `PiDefEq`, `LamDefEq`) is carried
inside the definition. Therefore a `Retype` law — `R.TyDefEq A' A' a →
R.DefEq M N A m a → R.DefEq M N A' m a` — is provable with no new
assumptions: trivially at `LR0` (its `DefEq` never inspects the type),
by shape-case analysis with recursion into the lower level at `LRS`,
hence at `LR` for every level. With `Retype`, cross-observation field
composition is `retype` + `IH.trans`; no canonical-telescope data, no
promoted uniqueness, and no residual sorry is needed for O1. This is
the precise sense in which the roadmap's "canonical field-type
alignment" exists: the semantic relation never needed the types
aligned, only valid.

Exit measurement: `sort_invS` reaches
`[propext, Classical.choice, Quot.sound]`. Record that
`SExpr.forallE_inv` and `SExpr.sort_forallE_inv` went clean at the same
moment (they become L4L-16 deliverables; their VExpr reflection stays
L4L-17).

### L4L-16D — live-environment instance, staged (the real risk)

The only segment never executed end-to-end. De-risk with a thin vertical
slice before full coverage:

- **D0 (slice):** a two-declaration environment (one definition + one
  generated iota rule from an existing fixture block) through
  `Params` + `Params.Semantic`, endpoint `sort_invS` instantiated. This
  smokes out interface mismatches while they are cheap.
- **D1:** definitions/mutual definitions + quotient (`CertifiedExtension.quot`).
- **D2:** ordinary/block inductive rules via `AssembledPat` — requires
  lifting the four `IotaPat` non-overlap laws to the union and the
  cross-term non-overlap lemma (new, bounded, combinatorial).
- **D3:** nested rules as registered equations only (per roadmap).
- **D4:** registered structure eta from the L4L-15B registry.

Explicitly OUT of L4L-16: constructing Theory's `Params`/
`Params.Extension.join` live instance (consumed only by
`IsDefEq.church_rosser`; needs L4L-17-strength inversion fields). It
moves to L4L-18A′. The roadmap's §2.1 "Not claimed" paragraph should be
amended accordingly.

### L4L-16E — promotion (unchanged, plus corrections)

Move the consumed modules out of `Experimental/`, close public
`IsDefEqU.sort_inv` from the instances, shrink the allowlist 22 → 21,
add the missing `#guard_msgs`/`#print axioms` pins for the promoted
roots (none exist today because Experimental is ungated), and take the
digama reconcile-or-defer decision recorded as due at this boundary.

### L4L-17′ — re-scoped

1. **Reflection first** (already the roadmap's position, now sharper):
   decide conservativity-lemma vs adequacy-restated-on-VEnv. Note `mk`
   is a proved retraction (surjective), so naive injectivity is
   unavailable; any faithfulness statement is modulo `≈`.
2. Reflect `forallE_inv_stratified` and `sort_forallE_inv` (SExpr halves
   already delivered by 16C′).
3. `weakN_iff` (forward direction) and
   `registeredStructureHeadInversion` — no SExpr counterparts yet; and
   whatever Option B promoted, generalize here.
4. Re-run `uniq`/`uniqU` and downstream guards (unlocks the transitional
   closure: `pat_wf`, projection consumers).

### L4L-18A′ — grows, honestly

Theory `NormalEq.parRed` holes (as before) **plus** the work moved here:
Theory-side live `Params`/`Params.Extension.join` instance (its four
structEta/forallE fields now supplied by L4L-17 outputs), and only then —
if any promoted statement still needs it — the SExpr Church–Rosser mirror
(S6). Expected outcome: S6 is simply deleted along with `CRDefEq` if no
promoted API consumes it.

## 4. Execution order and checkpoints

Each numbered item is one committed checkpoint (jj makes this cheap);
Experimental stays buildable at every pause point.

1. **Stabilize & checkpoint L4L-16A(+)**: single writer designated
   (§5.1); commit the current working copy as the L4L-16A checkpoint with
   the roadmap corrections from §1.2 (plift, six fields, S1/S7–9
   verdicts, S6 move). Gated surface is untouched by the diff, so §6
   gates pass as-is; run them anyway.
2. **16B′ cleanup** (delete/restate items — small, mechanical).
3. **16C′ O1** (finish the `aligned`/`CtorSpineDefEq.trans` encoding the
   worker already started; decision + endpoint recorded in
   `plans/l4l-16-sort-inversion-decision.md` as a dated section).
4. **16C′ S3-narrow + O3 + O2 leaf closure** → measured clean
   `sort_invS`; SExpr `forallE_inv`/`sort_forallE_inv` recorded clean.
5. **16D0 slice**, then **16D1–D4** as separate checkpoints.
6. **16E promotion** + allowlist 21 + digama decision.
7. Hand the ladder to L4L-17′ (reflection decision first).

Rough effort guess (calibrate against how fast 16A went): 1–2 days for
1–2; the 16C′ spike+closure is the genuine unknown — timebox the spike,
expect days not hours for closure; 16D is 1–2 weeks of mostly
certificate plumbing; 16E days.

## 5. Anti-spin guardrails (process)

1. **One writer.** Exactly one session edits `Experimental/` at a time.
   Right now at least two AI sessions plus an auditor share this working
   copy; pick one (the pts/3 codex session and pts/11 Claude session
   cannot both continue).
2. **Checkpoint every kernel-checked sub-result.** No more 18-hour
   uncommitted mega-changes; the ladder's one-claim-per-checkpoint rule
   applies to Experimental work too.
3. **Two-strikes rule.** Two failed repair attempts on the same
   obligation → stop, write the obligation as a Lean statement in the
   plan file, and make an interface decision before more proof text.
4. **Roadmap is status, not lab notebook.** Move the L4L-16C attempt
   narrative (~100 lines) into `plans/l4l-16c-adequacy-log.md`; the
   roadmap keeps a 5-line status per slice. (The narrative was valuable —
   it is how this audit found the root cause — it just belongs in a log.)
5. **Measure, don't assert, closures.** The roadmap carried three stale
   claims about this work (plift `stop`, five fields, `WHRed.subst`
   `.extra` open). Add a tiny uncommitted probe file with
   `#print axioms` for the route waypoints and re-run it at every
   checkpoint until 16E's real guards exist.
