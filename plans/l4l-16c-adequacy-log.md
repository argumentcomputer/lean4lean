# L4L-16C adequacy attempt log

This file preserves the working-notes narrative that accumulated in
`plans/roadmap.md`'s L4L-16 ladder entry between 2026-08-12 and
2026-08-13, moved here when the 2026-08-13 audit re-cut the milestone
(`plans/l4l-16-completion-plan.md`). It is a historical record of the
repair sequence at the adequacy iota leaf — valuable precisely because it
documents the repeated erased-type-alignment discoveries that motivated
the O1/O2/O3 decomposition — and is not status-bearing.

## Original L4L-16A bullet (roadmap, as of 2026-08-13 04:32)

*L4L-16A — bridge interface and judgment translation.* Largely
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
unreferenced prototypes are explicit import-compatible parked stubs.

(Correction recorded at the 16B′ checkpoint: `Params.Semantic` has six
fields — the bullet above omitted `iotaRule`.)

## Original L4L-16B bullet

*L4L-16B — SExpr infrastructure closure.* Discharge the remaining
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

(Corrections recorded at the 16B′ checkpoint: the `Shape.WF.plift`
"`stop` tactic" claim was stale — the whole prototype was inside a block
comment, never elaborated, with zero consumers; and `WHRed.subst`'s
`.extra` case was already kernel-checked, only `weakU_inv`'s remained.)

## Original L4L-16C bullet — the attempt history

*L4L-16C — constant adequacy.* Close the `LR.adequacy` constant
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

(Correction recorded at the 16B′ checkpoint: the `hDef` premise is a
field of `IsDefEqStrong.const` discharged by `mkS` from
`Params.Semantic.defn`; its live construction is the 16D `defn` field,
not separate 16C work.)
