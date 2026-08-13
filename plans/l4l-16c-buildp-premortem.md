# L4L-16C buildP pre-mortem: gap map for the final adequacy-leaf step

## Worker resolution (2026-08-14, after review integration)

The signature audit was correct to stop the leaf-local draft.  The moving
working tree now resolves the mapped gaps as follows:

- **G1 is closed.** `FixedHeadResult` and
  `iotaDefEq_of_ctorExactAt_fixedHead` no longer require `Ctx.WF`; the
  target-context well-formedness dependency belongs only at the joint
  uniqueness/root-reduction boundary.
- **The old G2 obligation is obsolete.** The retained consumer uses
  `RDeepChildren (fun _ => True)`, whose laws are already complete; it does
  not require a `Laws FixedHeadResult` instance.
- **G3 exposed an additional depth mismatch, now repaired.**
  `FixedHeadResultAt hX depth` is retained at the same Nat index as
  `SelfAdequateAt`; `FixedHeadStep` receives that freshly constructed
  same-depth self-adequacy result.  Only after the Nat-first recursion has
  produced every depth does `FixedHeadResult.of_forall_at` recover the old
  depth-polymorphic contract.  The adequacy module builds after this change.
- **G4 chooses route 2.** Route 1 cannot instantiate the existing
  `CtorChain.NativeAlgebra` safely: a native exact link is stated in an
  arbitrary relation `J`, while
  `iotaDefEq_of_ctorExactAt_fixedHead` is stated in canonical `LR` at both
  the recursor prefix and generated RHS.  An `unlift` frame does not permit
  projecting arbitrary high-level fields or the canonical prefix into `J`.
  Thus a uniqueness-free leaf-local fold would recreate the already rejected
  native/root projection.  The main adequacy construction must expose the
  predecessor limited-uniqueness/lower-adequacy package through the existing
  level-indexed joint boundary; it must not manufacture a completed
  `JointBuilder` inside the current direct induction.
- **G5 remains live** and is part of the fixed-head application-chain proof,
  not an admissible raw-to-semantic conversion shortcut.

This resolution supersedes the alternatives in G4 below; the rest of the
document remains as the snapshot evidence that motivated it.

Purpose: before the worker writes the "consumer-specific fixed-head `buildP`
application-chain algebra" (the last named obligation per
`plans/l4l-16c-adequacy-log.md` final entry and
`plans/l4l-16-completion-plan.md` §3 line 649), map exactly what that step
must consume, whether each input is actually available at the sorry site,
and where erasure-failure-mode #7 could hide. All claims carry file:line
references to the snapshot below. Uncertainty is flagged inline; nothing
below was elaborated through Lean (read-only analysis).

## Snapshot (MOVING TARGET — verify before relying on line numbers)

Read window: 2026-08-14 ~03:35–03:55 EDT. A worker session is actively
editing these files; mtimes were checked at the start and end of the read
session and did not change in between, so all line numbers are consistent
with this exact state:

| file | mtime | size |
|---|---|---|
| `Lean4Lean/Experimental/ShapeLogRel.lean` | 2026-08-14 01:21:27 | 583544 B |
| `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean` | 2026-08-14 03:31:07 | 181248 B |
| `Lean4Lean/Experimental/SExpr.lean` | 2026-08-13 13:07:35 | 182986 B |

Sole adequacy-file sorry: `ShapeLogRelAdequacy.lean:3058`. (SExpr.lean has
four separate sorries at 3516/3739/3842/3908 — L4L-16B′ scope, not this
leaf.) Re-locate after any edit with
`grep -n "sorry" Lean4Lean/Experimental/ShapeLogRelAdequacy.lean`.

Abbreviations: SLR = ShapeLogRel.lean, ADQ = ShapeLogRelAdequacy.lean,
SE = SExpr.lean. All Lean names live under `Lean4Lean.SExpr` unless noted.

## The sorry site

### Enclosing structure (outermost → innermost)

1. `LR.adequacy` (ADQ:2856-2858): `(H : IsDefEqStrong Γ M N A) (hM :
   LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
   Adequate Γ₀ Γ ρ M N A m a`, by `induction H generalizing ρ n m a`.
   **No `Ctx.WF` premise anywhere in the statement.** `Adequate`
   (ADQ:9-13) quantifies over `LR.SubstWF Γ₀ σ σ' Γ ρ`.
2. `| @const c ci Γ ls u h1 h2 hTy F hF hDef ihTy ihF ihDef` (ADQ:2886).
3. `cases hM.witness`, const branch (ADQ:2891):
   `| @const _ _ ci' _ m' _ a' _ R hreg _ hle hm'ty hA' hConst hR`.
   This binds the proof-relevant callback
   **`hR : ∀ m e, R m e → LE_Interp.Witness ρ m e`** and
   `hA' : LE_Interp.Witness ρ a' (mkInst ls ci.type)` (the registered
   type's witness tree).
4. `suffices`-block per substitution; `intro σ σ' W` with
   `W : LR.SubstWF Γ₀ σ σ' Γ ρ` (ADQ:2893-2896).
5. `hC : LE_Interp.Const c ls (LE_Interp.Lower R) [] m.T` (ADQ:2898-2899);
   `cases hC with | lam hrec hlam` + `rename_i nsem hlen_sem fsem`
   (ADQ:2902-2903). Per `LE_Interp.Const.lam` (SLR:3542-3543):
   `hrec : ∀ x y : WShape nsem, (x, y) ∈ fsem →
   LE_Interp.Const c ls (LE_Interp.Lower R) [x] y.T`.
6. `hmem.unfold` lam branch `| @lam k f a₁ a₂ htm` (ADQ:2908); soundness
   unpack of the constant's type (ADQ:2909-2915, the `toValTy` pattern);
   `split <;> rename_i hf`, Pi-observation unpack
   `⟨A₁, A₂, _, _, u₁, u₂, hred, _, hA₁, hA₂, hvalA₁, hpi⟩` (ADQ:2919).
7. `have eval : ∀ {k'} (hn : k ≤ k') (hnsem hnArgs : nsem ≤ k') {x y p x₀
   y₀}, p.HasType (a₁.lift k') → Γ₀ ⊢ x ≡ y : A₁ → (LR Γ₀).DefEq x y A₁ p
   (a₁.lift k') → (x₀,y₀) ∈ fsem → x₀.lift k' ≤ p → (f.lift k').app p ≤
   y₀.lift k' → (LR Γ₀).DefEq ((const c ls).app x) ((const c ls).app y)
   (A₂.inst x) ((f.lift k').app p) ((a₂.lift k').app p)` (ADQ:2928-2937).
   Inside: `hPiK hAK hout hchildLe hType₀ hTypePi hConstPi hAppTerm
   hAppType hAppSpineX hAppCodomain hAppSpineY hA₁K hAppPair hAppAligned
   hAppLeaf` (ADQ:2939-3020); `hAppLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
   (mkInst ls ci.type) [x] [y] [p] (A₂.inst x) ((f.lift k').app p)
   ((a₂.lift k').app p)` (ADQ:2997-3020).
8. `evalPat : LR.PatternLeafDefEq Γ₀ c ls (LE_Interp.Lower R) :=
   LR.PatternLeafDefEq.of_iota (by …)` (ADQ:3021-3059) — the sorry is the
   tail of this by-block. After it, `eval` is consumed by `LR.constDefEq`
   (ADQ:3060-3065) and wrapped into `LogRel.DefEqRect.diagonal` for
   `LR.constLamDefEq` (ADQ:3066-3069) — diagonal suffices here because
   both heads are the same `const c ls`.

### Hypotheses introduced inside the `of_iota` block (ADQ:3027-3057)

`of_iota` (ADQ:2178-2185) reduces `PatternLeafDefEq` to `IotaLeafDefEq`
(ADQ:1302-1326) instantiated at `R := LE_Interp.Lower R`. The intro at
ADQ:3027-3029 binds (types per ADQ:1304-1323):

- `nI : Nat`, `rargsI : List (WShape nI)`, `rec major ctor arity`,
  `rI : (RecursorIotaPattern rec major ctor arity).RHS × ….Check`,
  `mcapI : ….Path → TShape`, `xsI ysI CHeadI AI : SExpr`,
  `outI outTyI : WShape nI`
- `hpatI : Params.Pat (RecursorIotaPattern rec major ctor arity) rI`
- `hmatchI : LE_Interp.Matches (RecursorIotaPattern …) c rargsI mcapI`
- `hrhsI : LE_Interp.RHS ls mcapI (LE_Interp.Lower R) outI.T rI.1`
- `hleafI : LR.PatternLeafSpine Γ₀ (LR Γ₀) CHeadI xsI ysI rargsI AI outI
  outTyI`
- `htermI : Γ₀ ⊢ xsI.foldr app-fold (const c ls) ≡ ysI.foldr … : AI`
- `hAIType : ∃ u, Γ₀ ⊢ AI : .sort u`;
  `hheadI : Γ₀ ⊢ const c ls : CHeadI`
- `hspineXI hspineYI : SExpr.SpineWF Γ₀ CHeadI xsI.reverse AI` (resp. ysI)
- `houtI : outI.HasType outTyI`; `hAI : (LR Γ₀).TyDefEq AI AI outTyI`

Then `cases hmatchI | @app fPat nCtor head recShapes mrec aPat ctorHead
ctorShapes mctor hmfI hmaI` (ADQ:3030-3032) yields
- `hmfI : LE_Interp.Matches (Pattern.varN (.const rec) major) rec
  recShapes mrec` (recursor prefix, successor depth) and
- `hmaI : LE_Interp.Matches (Pattern.varN (.const ctor) arity) ctor
  ctorShapes mctor` (constructor, one depth lower);

`rcases hleafI` (ADQ:3033-3037) destructures the `PatternLeafSpine`
fields (ADQ:1144-1168): `majorX recXs majorY recYs majorShape recShapesI
majorTypeShape resultShape resultTypeShape hxs hys hrargs houtEq houtTyEq
hlastPair hpMajor hresultType htyMajor hvMajor halignedI hPiI`; substs
collapse `xsI = majorX :: recXs`, `ysI = majorY :: recYs`, `rargsI =
majorShape :: recShapes`, `outI = resultShape.app majorShape`, `outTyI =
resultTypeShape.app majorShape`, and identify `ctorHead = ctor`
(ADQ:3038-3048). Then:
- `hctorClass : Params.classify ctor = some (.ctor
  ctorShapes.reverse.length)` (ADQ:3049-3052)
- `hmajorCtor := LR.DefEq.ctor'_inv hctorClass hpMajor hvMajor`
  (ADQ:3053-3054): by SLR:11040-11047 this is
  `LRS.IndTyHead Γ₀ D ∧ LRS.CtorDefEq Γ₀ (LR Γ₀) majorX majorY
  (WShape.ctor ctor ctorShapes.reverse hwf)` where `D` is the last-Pi
  domain (`hvMajor : (LR Γ₀).DefEq majorX majorY hlastPair.domain
  majorShape majorTypeShape`, per field `majorRel` ADQ:1165). Note: the
  free-closure `CtorDefEq`, **not** a native `CtorExact` leaf.
- `hrecargsI : LRS.CtorArgsDefEq (LR Γ₀) recXs recYs recShapes :=
  halignedI.args.tail` (ADQ:3055-3057).

### Target of the sorry

The `IotaLeafDefEq` conclusion (ADQ:1324-1326) after the substs. Modulo
exact post-`subst` normal form (inferred, not elaborated — verify in
goal view):

```
(LR Γ₀).DefEq
  ((majorX :: recXs).foldr (fun a f => f.app a) (.const c ls))
  ((majorY :: recYs).foldr (fun a f => f.app a) (.const c ls))
  AI (resultShape.app majorShape) (resultTypeShape.app majorShape)
```

with `c = rec` derivable from `hmfI` (the analogous
`iotaDefEq_of_ctorExactAt` consumers all state the head as
`.const rec recLs`, e.g. ADQ:1983-1986). This matches the conclusion
shape of `LRS.iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2072-2077) at
`recLs := ls`.

## buildP status

**`buildP` exists as a named hypothesis slot, not a definition.** It is
the main callback of `LE_Interp.Witness.recNatRDeepSound`
(SLR:8521-8548, binder at SLR:8523-8532):

```
buildP : ∀ (d : Nat) {ρ m M} (hM : LE_Interp.Witness ρ m M),
  hM.RDeepChildren (fun hM' => P hM' ∧ hM'.RDeepChildren P ∧
    LE_Interp.Witness.SoundRDeepAt P Γ₀ hM' d) →
  (∀ d' < d, ∀ {ρ m M} (hM' : Witness ρ m M),
    P hM' ∧ hM'.RDeepChildren P ∧ SoundRDeepAt P Γ₀ hM' d') →
  P hM
```

Sibling slots: `buildC` in `recNatRDeepConsumer` (SLR:8553) and
`recNatRDeepConsumerAt` (SLR:8592). The plans' phrase "the buildP
algebra" (log line 295, completion plan line 649, roadmap line 776) means:
*write the concrete instantiation of this slot* — i.e. choose the
predicate `P` and prove the per-constructor cases.

The evident candidate for `P` is **`LR.FixedHeadResult`** (ADQ:1331-1367):
a Prop on one witness `hX : Witness ρ root X`, universally quantified
inside over level `n`, context `Γ` (with a `Ctx.WF Γ` input, ADQ:1346),
iota rule, and spine data; conclusion
`(LR (n+1) Γ).DefEq (r.1.applyS recLs mx) (r.1.applyS recLs my) A out
outTy` (ADQ:1366-1367). Already proved cases/transports:
`mono` (ADQ:1369), `mono_l` (ADQ:1380), `bot` (ADQ:1391), `bvar`
(ADQ:1408), `sort` (ADQ:1424). Its consumer chain is fully in place:
`LRS.iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2040-2088) takes
`hP : ∀ (hr : R m M), LR.FixedHeadResult (hR hr)` and feeds
`LRS.IotaRHSDefEq.of_nonbotWitnessResult` (ADQ:1635-1699, applied at
ADQ:2081-2088), which selects the fixed-head witness *together with* its
retained `P` via `LE_Interp.RHS.fixedLowerWitnessResult` (SLR:4507-4517),
so lowering cannot reselect a different evaluator (the instance-#6
repair).

So the missing work is exactly: (i) `RDeepChildren.Laws FixedHeadResult`
(two of five fields unproved — see gap G2), (ii) the `buildP` cases for
witness constructors `app`, `lam`, `forallE`, `const` (the
application-chain algebra proper, plus the "conversion/type-relation
handoff and constant case" named at completion plan lines 653-656), and
(iii) the assembly at the sorry (gaps G1, G4).

## Machinery signatures (statement-level)

Witness layer (SLR):
- `LE_Interp.Witness` (3584-3605), **Type**-valued mirror of `LE_Interp`
  (3550-3567). `const` case (3599-3605) stores `Params.env.constants c =
  some ci`, `ls.length = ci.uvars`, root bound `m ≤ m'`, `m'.HasType a`,
  the registered type's witness `Witness ρ a (mkInst ls ci.type)`, the
  Prop evaluator `LE_Interp.Const c ls R [] m'`, and the proof-relevant
  callback `∀ m e, R m e → Witness ρ m e`.
- `Witness.mono` (3657) / `mono_l` (3672): lower root / grow valuation,
  preserving the tree. `Witness.closed` (4957): change valuation entries
  irrelevant to a `ClosedN M k` term. `Witness.recR` (3693): follow
  exactly the stored R-edges.
- `Witness.recDeep` (3748) / `recDeep₂` (3769): full structural recursion
  (deep children); recDeep₂ keeps the first tree's IH polymorphic in the
  second (term/type role swap).
- `Witness.RDeepChildren P` (3799-3816): retained tree granting `P` (and
  recursively `RDeepChildren P`) **only at abstract constant R-edges**
  (const case, 3813-3816); ordinary children get only the recursive
  structure. Closure lemmas: `map` 3838, `mono` 3858, `mono_l` 3898,
  `closed` 5003, `lift'` 5114, `weak` 5172, `subst` 5215, `inst` 5277,
  `forallE_inv'`/`lam_inv'` 6448/6490, `forallE_inst`/`lam_inst`
  6552/6572.
- `RDeepChildren.JoinLaws P` (3822-3834): `bot`, `mono`, `mono_l`,
  `join` (join of two witnesses at `m₁.join m₂`). `RDeepChildren.Laws P`
  (6814-6820) **extends JoinLaws with `closed`** — five fields total.
- `RDeepChildren.compat_join` (5686+): from `JoinLaws P`, `ρ'.LE ρ`, and
  two retained trees on the same `M`, produces `m₁.Compat m₂` and a
  joined witness with a retained tree.
- `recRDeep` (3942) / `recNatRDeep` (4020) / `recRDeep₂` (4044) /
  `recNatRDeep₂` (4129): R-edge recursions; the `Nat` variants make
  stratification depth the primary decrease, so conversion restarts on an
  arbitrary witness only after `d' < d`.
- `TypedRDeep P ρ m M A` (6614-6621): ∃ enlarged root `m'`, type shape
  `a`, witnesses for `M` and `A`, `m ≤ m'`, `m'.HasType a`, both retained
  trees. `TypeRDeep` (6624), `toType` (6632), `bot` (6640).
- `TypedRDeep.app` (6654-6670): from `mono_l`+`closed` laws and two
  callbacks (function typed at `.forallE A B`; instantiated result
  `B.inst X` as a type), applies — "application itself introduces no new
  semantic R edge".
- `TypedRDeep.lam` (6895): laws + body callback (under `ρ.push x`) →
  typed at `A.forallE B`. `TypedRDeep.forallE` (7169): laws + domain +
  codomain callbacks → typed at `.sort (.imax u v)`.
- `FitsRDeep P base Γ ρ` (8359-8366): valuation whose entries carry
  witnesses + retained trees; `lookup` 8368, `push` 8386,
  `Valuation.Fits.toFitsRDeepTrue` 8396.
- `SoundRDeepAt P Γ₀ hM d` (8408-8415): ∀ `{Γ A core}`,
  `HasTypeStratifiedS Γ M A core d → FitsRDeep P Γ₀ Γ ρ →
  Valuation.Fits Γ₀ Γ ρ → TypedRDeep P ρ m M A`. (`Γ₀` here is an
  auto-bound variable of each statement, chosen by the consumer.)
- `soundRDeepRestart` (8421-8433): proves `SoundRDeepAt` below a depth
  bound from `Laws P` + strictly-smaller restarts; syntax-directed cases
  compiled through `TypedRDeep.app/lam/forallE`; the `defeq` case
  (8503-8515) converts via `LE_Interp.sound` on the stratified equation.
- `recNatRDeepSound` (8521-8548): `Laws P` + `buildP` ⊢ ∀ hM d,
  `P hM ∧ hM.RDeepChildren P ∧ SoundRDeepAt P Γ₀ hM d`.
- Fixed-head selection: `Lower R` (4447), `Lower.realizeWitness` (4466),
  `RHS.fixedWitness` (4432), `RHS.fixedLowerWitness` (4476),
  `RHS.fixedLowerWitnessResult(P, hR, hP, hmono)` (4490-4517) — selects
  witness **and** its `P` from the same R-edge.
- `LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a` (8666-8670): `left`, `right`,
  `cross` edges at one relation/type/shapes. Ops: `diagonal` 8674,
  `trans` 8680, `conv` 8689 (needs semantic `TyDefEq`), `mono_l` 8696,
  `mono_r_1/2` 8705/8715, `whr` 8724 (all four endpoints in lockstep),
  `LRS.DefEqRect.app` 10988 / `LR.DefEqRect.app` 11020.
- `LRS.DefEq.app` (10962-10972): function edge at `LRS IH` level n+1 with
  shape `.lam mf hmf : WShape (n+1)`, argument `IH.DefEq x y A₁ p b` at
  level n, `p.HasType b`, raw `Γ ⊢ x ≡ y : A₁` ⊢ result `IH.DefEq (M.app
  x) (N.app y) (A₂.inst x) (mf.app p) (tf.app p)` at level n. **Each app
  step descends one level.**
- `LR.DefEq.ctor'_inv` (11040-11047): classification + `HasType` +
  `(LR Γ).DefEq M N A (.ctor' c fields) a` ⊢ `IndTyHead Γ A ∧
  LRS.CtorDefEq Γ (LR Γ) M N (.ctor c fields hwf)` (free closure).
- `LRS.CtorExact` (9561-9579): the native leaf — classification, level
  lists equal (`ls = ls'`), head typings, two `SpineWF`s, `CtorArgsDefEq`
  and both `CtorSpineDefEq`s.
- `LRS.CaptureDefEqAligned IH m x y typeExpr` (11481-11487): ∃ shapes,
  `m ≤ elemShape.T`, `elemShape.HasType typeShape`, `IH.TyDefEq typeExpr
  typeExpr typeShape`, raw `Γ ⊢ x ≡ y : typeExpr`, `IH.DefEq x y typeExpr
  elemShape typeShape`. `mono` 11504, `lift` 11511, `rebase` 11527.
- `LE_Interp.RHS.ShapeSpine m2 head paths out` (3375-3383): per-path cons
  `{n} {f : WShape (n+1)} {a : WShape n}`: `a.T ≤ m2 path → m ≤ (f.app
  a).T → ShapeSpine m2 m paths out → ShapeSpine m2 f.T (path::paths) out`.
  **The level `n` is existential and independent per step.**
  `typedLowerHead` (3417): from per-path typed lower bounds + typed out,
  a typed lower approximation of the head.
- `LE_Interp.sound` (8353-8355): `IsDefEqStrong Γ M N A → Fits Γ₀ Γ ρ →
  (LE_Interp ρ m M ↔ … N) ∧ (… → InterpTyped ρ m M A)`.

SExpr layer:
- `PathSpineWF Γ value type A paths B` (SE:1537-1550): dependent spine
  over paths; `cons` consumes `.forallE (type path) A₂` and instantiates
  at `value path`; **`conv` and `ret` embed raw `IsDefEq … (.sort u)`
  edges** with no semantic counterpart.

Adequacy layer (ADQ):
- `LR.PatternLeafDefEq` (1276) / `LR.IotaLeafDefEq` (1302) — the leaf
  contracts; `of_iota` (2178) bridges them.
- `LR.FixedHeadResult` (1331-1367) — see above. Inputs at use-site: `Ctx.WF
  Γ`, `X = mkInst recLs rule.df.rhs`, `head ≤ root`, strong self-typing
  `IsDefEqStrong Γ X X (mkInst recLs rule.df.type)` (supplied by
  `rule.rhsStrong`, used at ADQ:1575), `ShapeSpine`, typed lower head,
  two `PathSpineWF`s at one shared `captureType`, per-path
  `CaptureDefEqAligned` (rec at `LR (n+1) Γ`, ctor at `LR n Γ`,
  ADQ:1358-1363), `out.HasType outTy`, `(LR (n+1) Γ).TyDefEq A A outTy`.
- `LRS.IotaRHSDefEq` (1480-1508); `of_nonbot` (1519, discharges the bot
  RHS and extracts head + `ShapeSpine` via `rule.rhsShapeSpine`,
  supplies `rule.rhsStrong recLs`); `of_nonbotWitness` (1582);
  `of_nonbotWitnessResult` (1635) — the P-preserving form; its capture
  input shape (1669-1674) **matches FixedHeadResult's exactly** (levels
  `LRS IH`/`IH` vs `LR (n+1)`/`LR n`).
- `LRS.iotaDefEq_of_ctorExactAt` (1951-2031): pattern + matches + RHS +
  **`CtorExact Γ₀ IH …`** + `PatternLeafSpine` + rec-head typing + out/A +
  `rhsDefEq : ∀ rule, IotaRHSDefEq …` ⊢ the goal-shaped `DefEq`.
- `LRS.iotaDefEq_of_ctorExactAt_fixedHead` (2040-2088): same but
  discharges `rhsDefEq` from `hR` + `hP : ∀ hr, FixedHeadResult (hR hr)`;
  demands **`hΓ : Ctx.WF Γ₀`** (2054) and `leaf : CtorExact Γ₀ (LR Γ₀) …`
  (2064) — everything at the canonical relation.
- `LR.iotaActions_of_exactEqAt` (used 1929, 2153) / `iotaDefEq_of_exactEqAt`
  wrapper ending 1926-1939: the root-pair form taking `CtorArgsDefEq` for
  both spines + weak-head reductions of both majors to their ctor spines.
- `LR.constDefEq` (2193-2217): the structural constant evaluator; caller
  supplies only `evalPat : PatternLeafDefEq`.
- `LR.adequateApp` (2452-2471): the Adequate-level dependent-application
  core (three lower callbacks: function, argument, instantiated result);
  the template the buildP `app` case is meant to mirror
  (completion plan 650-653).
- `LR.Adequate.rect` (~935-945): packages adequacy output as a
  `DefEqRect`; `LR.constLamDefEq` (1076-1137) consumes a rect-valued
  `eval`.
- `LR.JointBuilder` (717+), `foldRaw_of_jointBuilder` (751-756): the
  typed chain-fold consumer — needs `B : JointBuilder` and `Ctx.WF Γ`,
  where `B.rawTypeUniq`/`B.stratifiedInversion` (729-739) are derived
  from **`LR.ContextualAdequacyAt 1`** (`B.first B.zero`) — i.e. from the
  full adequacy theorem at levels 0/1.

## Gap map

Notation: (a) = directly in scope at the sorry, (b) = constructible via a
named kernel-checked lemma, (c) = gap.

Assembly route assumed (the only one whose consumers exist today): apply
`LRS.iotaDefEq_of_ctorExactAt_fixedHead` (or its `exactEqAt` sibling)
after decomposing `hmajorCtor.2`.

| input | status |
|---|---|
| `hpat` | (a) `hpatI` ADQ:3028 |
| `hmf`/`hma` | (a) `hmfI`/`hmaI` ADQ:3031-3032 |
| `hrhs` at `Lower R` | (a) `hrhsI` ADQ:3028 — relation matches: the leaf is stated at `LE_Interp.Lower R` (ADQ:3021) and `of_nonbotWitnessResult` concludes at `Lower R` (ADQ:1679-1680) |
| `hR : R → Witness` | (a) from the witness destructuring, ADQ:2891 (explicit-binder form; the consumer wants implicit — trivial eta wrapper) |
| `hmono` for P | (b) `FixedHeadResult.mono` ADQ:1369; wired at ADQ:2083-2084 |
| `hP : ∀ hr, FixedHeadResult (hR hr)` | (c) **G3** — this is buildP itself: `(recNatRDeepSound laws buildP (hR _ _ hr) 0).1` once laws+buildP exist |
| `laws : RDeepChildren.Laws FixedHeadResult` | (c) **G2** — `join` and `closed` unproved (only `bot`/`mono`/`mono_l` exist, ADQ:1391/1369/1380; Laws needs five fields, SLR:6814+3822) |
| `hΓ : Ctx.WF Γ₀` | (c) **G1** — see below |
| `leaf : CtorExact Γ₀ (LR Γ₀) …` (or `exactEqAt`'s reductions + `CtorArgsDefEq` for the ctor spines) | (c) **G4** — `hmajorCtor.2` is the free-closure `CtorDefEq`; decomposition machinery is conditional on `JointBuilder` |
| `hleaf : PatternLeafSpine` | (a) re-assemble the rcased fields of `hleafI` (all bound at ADQ:3033-3037) |
| `hrecHead` | (a) `hheadI` after `c = rec` identification (via `hmfI`, cf. `varN_const_head` used at ADQ:3046-3048) |
| `hout`, `hA` | (a) `houtI`, `hAI` |
| capture relations for `IotaRHSDefEq` | produced internally by `iotaActions_of_exactEqAt` (ADQ:1927-1935) — needs G4's inputs first |

### G1 — `Ctx.WF Γ₀` is not in scope (availability gap, low design risk)

Required by `iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2054) and by
`FixedHeadResult` itself (ADQ:1346). Not available: `LR.adequacy`
(ADQ:2856-2858) has no WF premise; `LR.SubstWF` (SLR:11797-11805) does
not record target-context well-formedness; nothing in the const case
introduces it. Downstream churn if threaded: `LR.adequacyAt` (ADQ:3547),
`forallE_whRed_l` (ADQ:3573-3577), `sort_forallE_inv` (ADQ:3631), and
`sort_inv` (ADQ:3696) all instantiate adequacy at an **arbitrary** Γ with
no WF; `sort_invS` (ADQ:3698-3708) does have `hΓ : OnCtx …` to feed a WF
premise, but the `forallE_inv` co-deliverables (ADQ:3605, 3631) would
need new hypotheses or a move to their `_of_adequacy_collapsed` variants
(ADQ:3583). Alternative: audit whether `FixedHeadResult` actually needs
`Ctx.WF Γ` (it plausibly does, for stratified-typing restarts /
weakening the closed head's typing into Γ) — if not, drop the field
instead of threading it. Decide explicitly; do not discover this at
`exact`-time.

### G2 — `Laws FixedHeadResult`: `join` and `closed` unproved

`recNatRDeepSound` needs all five fields (SLR:8521-8522, 6814-6820,
3822-3834). `closed` should follow the `mono_l` pattern (FixedHeadResult
never inspects ρ except through the witness; cf. ADQ:1380-1389 where the
proof is transparent pass-through). `join` is the suspicious one: given
`P H₁`, `P H₂` at `m₁.join m₂` on the same `M`, the ShapeSpine input
arrives at `head ≤ m₁.join m₂` — the proof must route `head` through one
of the joined bounds. Check whether `TShape.join`'s LE lemmas suffice
(`head ≤ m₁.join m₂` does NOT give `head ≤ m₁` or `head ≤ m₂` in a join
semilattice — it gives the reverse). If not directly provable, the
`compat_join` machinery (SLR:5686) exists precisely because joins were
needed at application nodes; `FixedHeadResult.join` may need the same
`Compat`-based split of the ShapeSpine head. Budget real time here.

### G3 — the buildP cases themselves (the planned work)

Missing witness cases: `app`, `lam`, `forallE`, `const` (plus using
`bot`/`bvar`/`sort` already proved). Per completion plan 649-656 the
remaining content is "the conversion/type-relation handoff and constant
case, then consuming the rectangle along the generated `ShapeSpine`".
Available cores: `TypedRDeep.app/lam/forallE` (SLR:6654/6895/7169),
`soundRDeepRestart` (8421), `LRS.DefEq.app` (10962), `DefEqRect` ops
(8666-8737), `LR.adequateApp` as the shape template (ADQ:2452).
Known sub-gap inside: converting TShape-level witness facts into
level-indexed `(LR n Γ)` facts at the *consumer-demanded* `n` — the
`toValTy` pattern (ADQ:2909-2915) handles existential levels via
`le_n`/`le_a` + lift; the algebra must do this at every chain node whose
`ShapeSpine` cons level is existential (SLR:3378-3380).

### G4 — the major-side decomposition (highest #7 risk)

`hmajorCtor.2` is a **free-closure** `LRS.CtorDefEq` at the canonical
relation. Both existing leaf consumers need more: `…_of_ctorExactAt*`
need a native `CtorExact` (ADQ:1972/2064); `…of_exactEqAt` needs
weak-head reductions of both majors onto ctor spines plus root-to-root
`CtorArgsDefEq` for the ctor fields (ADQ:2109-2114 in the `of_exact`
wrapper). The chain-normalization layer (`CtorExact/CtorFrame/CtorLink/
CtorChain/NativeAlgebra`, `CtorDefEq.toChain`, per completion plan
430-446) exists, but the only typed fold consumer visible is
`foldRaw_of_jointBuilder` (ADQ:751), which requires `B : LR.JointBuilder`
— and `JointBuilder` is powered by `ContextualAdequacyAt 0/1`
(ADQ:729-739), i.e. by the very theorem whose proof contains this sorry.
**Inside `LR.adequacy`'s single derivation-induction there is no
level-indexed fixpoint from which lower-level full adequacy (hence
uniqueness, hence the typed chain fold) can be consumed.** The decided
joint route (completion plan 403-412, 414-428) prescribes exactly that
offset bootstrap ("uniqueness at n consumed by adequacy at n+2"), but
`LR.adequacy` as written (2856) has not been restructured into it. So one
of the following must be true before the leaf closes, and the worker
should decide which *in the plan file first*:
  1. The buildP/fixedHead route makes the typed chain fold unnecessary at
     this site: a uniqueness-free *semantic* fold (per-link iota results
     glued by `(LRS IH).trans` at the package-fixed type, midpoints via
     `WHRedS.ctorSpine_determ`, frames folding completed results — plan
     259-276, 440-446, 488-491) is written as a new `CtorChain` algebra
     instance whose leaf handler is `iotaDefEq_of_ctorExactAt_fixedHead`.
     Watch item: that handler is stated at `(LR Γ₀)` throughout; a link's
     native relation must reach it only through the frame-transport of
     the *completed* result, never by projecting the root prefix into the
     native relation (the instance-#5 trap, plan 532-544).
  2. Or `LR.adequacy` is restructured into the level fixpoint so a
     `JointBuilder` (or `LimitedUniq` at the ctor-field level) is in
     scope. That is a statement-level change to the main induction, not
     leaf-local work — if the worker finds themselves needing
     `ContextualAdequacyAt` inside the sorry, STOP (this is the two-strikes
     rule's tripwire).
  Note the composition-impossibility map (plan 342-356): lam-shaped
  constructor fields cannot compose without uniqueness; `ctorShapes` here
  come from a live `Matches` and are arbitrary. Route 1 works only if
  the per-link/fold design genuinely avoids root-to-root *field*
  composition (it composes link *conclusions*, not fields — that is the
  design's whole point; verify this property survives contact with the
  actual `CtorChain.Algebra` interface before writing Lean).

### G5 — PathSpineWF's raw-only conv edges (latent)

`PathSpineWF.conv`/`ret` (SE:1543-1550) inject raw `IsDefEq … (.sort u)`
steps into the capture telescope with no semantic counterpart, while the
chain algebra's `LRS.DefEq.app` needs semantic Pi data per step and
`DefEqRect.conv` (SLR:8689) needs semantic `TyDefEq`. The intended
source of the semantic telescope is the head's own type witness
(`Witness.const` stores `hA : Witness ρ a (mkInst ls ci.type)`,
SLR:3602) — i.e. the algebra derives its own telescope semantically and
uses the supplied final `(LRS IH).TyDefEq A A outTy` (ADQ:1506) to land,
never converting *along* a raw edge mid-chain. If a draft finds itself
needing "raw defeq ⇒ semantic TyDefEq" mid-spine, that is adequacy-shaped
and circular — same tripwire as G4.2.

## Pre-mortem checklist (the six historical erasures, re-asked for buildP)

1. **Erased midpoint/capture types (iotaSite/SpineDefEq era).** Q: does
   any buildP-facing interface erase the types of intermediate chain
   nodes? A: mostly repaired — both `PathSpineWF`s share **one**
   `captureType` map (ADQ:1492-1498) and `CaptureDefEqAligned`
   (SLR:11481) is stated *at* that map, so variable leaves are related at
   the exact telescope domain ("the very domain used by both dependent
   application spines", ADQ:1476-1477). Residual: the raw-only
   `conv`/`ret` edges inside `PathSpineWF` (G5) are the one place a
   midpoint typing is only raw. File:SE:1543-1550.

2. **False assumption-free Retype (lambda observations).** Q: does the
   buildP conversion handoff anywhere retype a lam-shaped observation
   without the term-indexed callback? A: the new layer does not assume
   `Retype`: `DefEqRect.conv` (SLR:8689) demands semantic `TyDefEq`;
   `soundRDeepRestart`'s defeq case (SLR:8503-8515) converts via
   `LE_Interp.sound` on the stratified equation itself; the lambda
   boundary remains `LimitedUniq.LamRetype` (plan 509-519) and is NOT
   consumed by the Witness layer. Risk shifts to G4's fold, not buildP.

3. **Shallow children lost under symm/trans (RChildren era).** Q: does
   `RDeepChildren` survive every transport buildP will perform? A: YES —
   the closure family is comprehensive: `mono` SLR:3858, `mono_l` 3898,
   `closed` 5003, `lift'` 5114, `weak` 5172, `subst` 5215, `inst` 5277,
   binder inversions 6448/6490, instantiations 6552/6572, join via
   `compat_join` 5686, plus `TypedRDeep.{mono,weak,out}` 6855/6862/6873.
   This instance looks genuinely repaired.

4. **Unary recursion couldn't cover two semantic inputs (recRDeep →
   recRDeep₂ era).** Q: does the unary `recNatRDeepSound` reach the
   type-side tree, and "does the hypothesis at an abstract constant edge
   arrive at the level the root chain consumer folds at"? A: the
   type-side tree is a *structural child* of `Witness.const` (SLR:3602)
   retained by `RDeepChildren.const` (3813), and `TypedRDeep` carries
   both trees (6617-6621) — so unary suffices structurally;
   `recDeep₂`/`recNatRDeep₂` (3769/4129) remain available for role
   swaps. Levels: the Witness layer is TShape-valued (level-free), and
   `FixedHeadResult` is level-polymorphic *inside* the predicate
   (ADQ:1333), so there is no fixed-level mismatch at R-edges **by
   construction**; the level obligation moves entirely into the
   TShape→`WShape n` conversion inside each buildP case (G3 sub-gap).
   One verify-item: `FixedHeadResult` receives `IsDefEqStrong` self-typing
   (ADQ:1349) but `SoundRDeepAt` consumes `HasTypeStratifiedS`
   (SLR:8412); confirm the strong→stratified adapter exists at the depth
   accounting `recNatRDeepSound` provides (`∀ d` is unbounded, so any
   finite stratification depth is reachable — the question is only which
   lemma produces the stratified derivation for `mkInst recLs
   rule.df.rhs` in context Γ).

5. **Native vs root relation (lift/unlift zigzag era).** Q: "does
   DefEqRect's cross edge survive recursion into spine tails, or is it
   rebuilt per node?" A: it survives compositionally —
   `LRS.DefEqRect.app` (SLR:10988-11003) produces all three result edges
   from the same argument observation and left-oriented codomain, and
   `trans`/`whr`/`mono_*` (8680-8737) never mix endpoint witnesses; no
   per-node rebuild. The eval site currently needs only `diagonal`
   (ADQ:3067-3069) because both heads are the same constant. The
   instance-#5 trap re-enters ONLY through G4's chain fold (a native
   link's relation vs the canonical `(LR Γ₀)` of
   `iotaDefEq_of_ctorExactAt_fixedHead`'s statement, ADQ:2064-2071) —
   this is the single most likely home of failure mode #7.

6. **Prop-valued provenance (LE_Interp proof irrelevance era).** Q: "is
   anything in the chain Prop-valued where the consumer needs to case on
   which branch produced it?" A: the fixed-head selection is clean —
   `hR` is data in the witness (SLR:3604) and
   `fixedLowerWitnessResult` (SLR:4490-4517) selects witness + retained
   `P` from the *same* R-edge, with `hmono` covering the `Lower` root
   drop (the instance-#6 repair, correctly threaded at ADQ:2081-2088).
   Residual Prop-boundaries checked: `LE_Interp.Const`/`RHS`/`Matches`
   are Props, but their consumers only *universally quantify* over rules
   (`rhsDefEq : ∀ rule, …`, ADQ:1921-1922, 1980-1981) or destruct them
   inside Prop goals — no consumer needs to remember *which* rule/pattern
   fired across a proof-irrelevant boundary. One watch item: inside
   buildP's `const` case, the witness's `hC : LE_Interp.Const c ls R []
   m'` (SLR:3603) is Prop; if the app-chain algebra ever needs to case on
   `hC`'s `.pat` vs `.lam` branch AND retain the choice into a
   Type-valued construction, that is #6 all over again — the design says
   it should not (the chain consumes only `hR`-selected witnesses and the
   Prop-level `RHS`), but check the first draft for exactly this.

## Probe file

Ready-to-run axiom-closure probe. Place at repo root (e.g.
`AxiomProbe.lean`) and run `lake env lean AxiomProbe.lean` (the flake dev
shell provides lake; the Experimental import convention is confirmed by
ADQ:1 and `Lean4Lean/Experimental/UniqueTyping.lean:1`).

```lean
import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Axiom-closure waypoints for the L4L-16 gate path.
Expected clean baseline: [propext, Classical.choice, Quot.sound].
`LR.adequacy` and everything through it (incl. `sort_invS`,
`forallE_inv`, `sort_forallE_inv`) will show `sorryAx` until the
iota leaf closes; the Witness-layer roots must NOT. -/

#print axioms Lean4Lean.VEnv.IsDefEqU.sort_invS
#print axioms Lean4Lean.SExpr.LR.adequacy
#print axioms Lean4Lean.SExpr.LE_Interp.sound
#print axioms Lean4Lean.SExpr.forallE_inv
#print axioms Lean4Lean.SExpr.sort_forallE_inv
-- Witness-layer roots the buildP step will lean on:
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.recNatRDeepSound
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.RDeepChildren.compat_join
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.TypedRDeep.lam
#print axioms Lean4Lean.SExpr.LRS.IotaRHSDefEq.of_nonbotWitnessResult
#print axioms Lean4Lean.SExpr.LRS.iotaDefEq_of_ctorExactAt_fixedHead
```

Caveat: `LE_Interp.sound` / `TypedRDeep.lam` etc. are `Lean4Lean.SExpr.*`
because SLR/ADQ open `namespace Lean4Lean … namespace SExpr` (ADQ:4-6);
`sort_invS` is declared `_root_.Lean4Lean.VEnv.IsDefEqU.sort_invS`
(ADQ:3698). If a name fails to resolve after worker edits, re-grep — the
declarations may have been renamed since this snapshot.

### Measured (2026-08-14 ~07:15 EDT, all four Experimental files green)

First live run (extended with `IsDefEqStrong.mkS` and three D0 fixture
waypoints; run against the freshly built oleans):

- `sort_invS`, `LR.adequacy`, `forallE_inv`, `sort_forallE_inv`:
  `[propext, sorryAx, Classical.choice, Quot.sound]` — expected while the
  leaf is open.
- CLEAN at `[propext, Classical.choice, Quot.sound]`: `LE_Interp.sound`,
  `IsDefEqStrong.mkS`, all five Witness-layer roots listed above, and the
  D0 waypoints `ParamsD0.natParams` / `natTypeStrong` / `natIotaRule` —
  the fixture inherits no admission so far.
- `LR.iotaActions_of_exactEqAt` is CLEAN. The sorry-bearing
  `LR.iotaActions_of_exact` (ADQ:2212 at probe time) has **zero
  consumers**, and literal `WHRedS.defeq` no longer occurs in the
  adequacy file. Modulo transitive consumption of the other three SExpr
  admissions (all measured off-path at the 16B′ audit), the gate's sole
  `sorryAx` source is now the leaf's own `sorry`: closing it cleans
  `sort_invS` and both inversion co-deliverables simultaneously. The
  orphaned `of_exact` wrapper is deletable at the next touch.

## Review response: the shape-order mismatch (2026-08-14, sibling session)

Re the reported gap — recursive fixed-head adequacy needs a typed lower
observation (`headElem ≤ head`, supplied by `ShapeSpine.typedLowerHead`)
*together with* a semantic interpretation of its type, while soundness
types only an upper extension, and the two directions do not compose.

1. **The rejection of the downward pullback is consistent with two
   recorded corrections**, not just prudence: the `Shape.WF.plift`
   refutation (no lift-shaped Pi below an arbitrary function shape) and
   the `Retype` correction (lambda observations pin codomain validity to
   the original Pi typing). Contravariant domains are the same wall in
   both. Do not revisit it under stronger-sounding hypotheses; the
   established principle is CARRY the evidence, never project it down.
2. **The type's semantic witness may already exist in the retained tree
   — check before constructing anything new.** `Witness.const` stores
   `hA : Witness ρ a (mkInst ls ci.type)` (SLR:3602 at snapshot time):
   the fixed head's *type* witness is a field of the very node the
   fixed-head selection destructs. The synchronized package then needs
   only to THREAD `hA` through the retained invariant and peel it per
   application via the already-kernel-checked exact Pi inversion of the
   retained-tree transport layer, feeding `TypedRDeep`'s dependent
   application. If that holds, the repair is plumbing an existing field
   through `FitsRDeep`'s motive, not new mathematics.
3. **Two pre-flight checks on the widened invariant, per the
   signature-first rule** (write the package as a Lean statement and
   check every recursion case has its transport before proving):
   (a) *binder cases* — the type-witness component must weaken through
   `TypedRDeep.lam`/`forallE`; the transport layer's lift/weakening
   coverage should supply this, verify it applies at the package's
   indexing; (b) *depth/restart indexing* — the type's interpretation
   recurses independently of the term's (this is WHY `Witness.recDeep₂`
   is binary); the package must put the type witness in the second,
   polymorphic slot of the binary principle rather than forcing it
   through the unary `recNatRDeepSound` axis, and its restarts must obey
   the same strict stratification-depth decrease.
4. **Anchor at the lower observation from construction**, per the
   NativeAlgebra order: build the package where `typedLowerHead` is
   produced and transport completed results root-ward; never build at
   `head` and project down.
5. This is invariant-widening #8, but the first caught pre-proof; each
   revision since the re-cut has strictly narrowed. If the widened
   package hits a second wall (the likely spot: the compat-join case
   failing to synchronize the type witness), the two-strikes rule
   applies — state the obligation here before more Lean.

### Frontier re-map after the pause (2026-08-14 ~16:30)

Codex session PAUSED; tree stable. Snapshot for this section (verified
unchanged across the analysis window): SLR mtime 2026-08-14 13:58:42,
597560 B; ADQ mtime 2026-08-14 14:43:33, 214542 B. Sole sorry:
**ADQ:4285**. Everything in the original body above refers to the old
(2026-08-14 03:31) state; line numbers in THIS section are current.

#### 1. The sorry site now

The leaf was **extracted into a standalone theorem**:
`LR.iotaWitnessStep : LR.IotaWitnessStep Γ₀` (ADQ:4255-4285), where
`LR.IotaWitnessStep Γ₀` (ADQ:1505-1510) is
`Ctx.WF Γ₀ → ∀ {ρ c ls R}, (∀ {m M}, R m M → Witness ρ m M) →
LR.IotaLeafDefEq Γ₀ c ls (LE_Interp.Lower R)`. The proof intros
`hΓ₀ ρ c ls R hR` (4256) and then replays the exact prelude of the old
in-line block (intro 4257-4259 = old 3027-3029; `cases hmatchI` app case
4260-4262; `rcases hleafI` 4263-4267; substs 4268-4277; `hctorClass`
4278-4280; `hmajorCtor := LR.DefEq.ctor'_inv …` 4281; `hrecargsI` 4282-
4284; sorry 4285). Target: unchanged from the original "Target of the
sorry" section above (the `IotaLeafDefEq` conclusion, ADQ:1422-1424).

Scope changes vs the old site: **`hΓ₀ : Ctx.WF Γ₀` is now bound**
(4256) — old gap G1 is resolved at the leaf, and globally: `LR.adequacy`
(4288-4293) and `LR.adequacyAt` (4298-4300) now take `hΓ₀`. But the
scope is also LEANER: the old outer const-case data (`W : SubstWF`, the
constant's type witness `hA'`, `hConst`, `hrec`, the `eval` app package)
is gone — the step receives ONLY `hΓ₀` and the bare callback `hR`.

**Is a lower-level adequacy hypothesis / JointBuilder bound at the
sorry? NO.** The intended discipline is stated in the docstring
(ADQ:4251-4254): the body "may consume only the well-founded fixed-head
and predecessor-uniqueness packages, never the final polymorphic
adequacy theorem" — but no such package appears in the theorem's
hypotheses. The fixpoint restructure reached the *boundary*, not the
sorry: `LR.adequacy_of_iotaWitnessStep` (ADQ:3572, ~680 lines) is the
old induction parameterized by `iotaStep`, and it consumes the leaf
**level-pinned** — `evalPat : LR.PatternLeafDefEqAt Γ₀ k c ls (Lower R)
:= LR.PatternLeafDefEqAt.of_iota (iotaStep hΓ₀ hRI)` (ADQ:3743-3745),
with `LR.constDefEq` restated to take the At-form (ADQ:2521). The
level-indexed step interfaces exist but are **parked with zero
consumers**: `IotaWitnessStepAt` (ADQ:1493), `IotaLeafDefEqAt`
(ADQ:1427), `PatternLeafDefEqAt` (ADQ:1456). No level-indexed
`adequacy_of_iotaWitnessStepAt` exists yet.

#### 2. What codex built (the synchronized-package layer)

The proposed "synchronized package" repair **largely exists**:

- `LR.SelfAdequateAt Γ₀ hX depth` (ADQ:3145-3154): for all `n`, `mx bx :
  WShape n`, `Δ`, `mx.T ≤ root` (**typed lower observation**),
  `HasTypeStratifiedS Δ X B core depth`, `mx.HasType bx`, and
  **`Witness ρ bx.T B` (semantic type witness) as an input** —
  concludes `LR.Adequate Γ₀ Δ ρ X X B mx bx`. Private exact-root worker
  `SelfAdequateExactAt` (3157); public downward closure is by
  `hX.mono hroot` on the witness (ADQ:3467-3469), never by pulling
  `HasType` back — consistent with the review response's point 1.
- `LR.RetainedResultAt Γ₀ hX depth` (ADQ:3169-3175) =
  `(SelfAdequateAt ∧ FixedHeadResultAt) ∧ RDeepChildren (True) ∧
  SoundRDeepAt (True)` — the full retained invariant.
- **Proved**: `selfAdequateExactAtStep` (ADQ:3200-3455) — every
  `HasTypeStratifiedS` case of self-adequacy EXCEPT const (delegated to
  a contract), given `inv : JointStratifiedInversion` + `hΓ₀`; its app
  case (3247+) uses `lower`-restarts as the three adequateApp callbacks.
  `selfAdequateAtStep` (3456-3469). `retainedResultAt_of_steps`
  (ADQ:3488-3523): the complete well-founded plumbing via
  `recNatRDeepConsumerAt` (SLR:8811) with retained-tree predicate
  `T := fun _ => True` and `Laws.true` (ADQ:3519-3521) — **this
  resolves old gap G2**: no `join`/`closed` laws for `FixedHeadResult`
  are needed; the consumer/tree separation eliminates them.
  `fixedHeadResult_of_steps` (ADQ:3527-3536). The conversion algebra
  `LR.adequateDefeqSelf_of_stratifiedInversion` (ADQ:3071+, given inv)
  and `LR.TyDefEq.of_defeq_of_stratifiedInversion` (ADQ:813) — the
  "conversion/type-relation handoff" named in the old plan is proved,
  conditional on `inv`.
- `LR.FixedHeadResult` **restated** (ADQ:1515-1560): now `Γ₀`-explicit
  and quantified over `LR.SubstWF Γ₀ σ σ' Δ ρ` (1517-1518) instead of
  taking `Ctx.WF Γ`; `PathSpineWF`s at Γ₀ (1539-1542). Depth-indexed
  `LR.FixedHeadResultAt` (ADQ:1562-1600) adds the input
  **`HasTypeStratifiedS Δ X (mkInst recLs rule.df.type) true depth`**
  (1582) — the stratified certificate the chain algebra needs to invoke
  `SelfAdequateAt`; adapters `FixedHeadResult.at` (1604),
  `of_forall_at` (1615, uses `IsDefEqStrong.stratify` 1621),
  `FixedHeadResultAt.mono` (1625). Surviving case lemmas: `mono` 1636,
  `bot` 1647, `bvar` 1664, `sort` 1680 (old `mono_l` dropped — no
  longer needed by the new plumbing).
- Leaf consumers restated: `iotaDefEq_of_ctorExactAt` (ADQ:2211, now
  takes `hΓ`), `iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2358-2408, now
  takes `W : SubstWF Γ₀ σ σ' Δ ρ` (2373) + `hΓ : Ctx.WF Γ₀` (2374) +
  `hP` at the new `FixedHeadResult Γ₀` (2383); still `leaf : CtorExact
  Γ₀ (LR Γ₀) …` (2384)); `of_nonbotWitnessResult` at ADQ:1891.
- New SLR plumbing (+~14KB): `WShapeFun.AppLEData`/`appLEData`
  (SLR:6516/6526) and `WShape.HasDomData`/`HasDom.data`
  (SLR:6559/6565) — noncomputable Type-valued extractors of lower-shape
  application/domain data (the peeling plumbing for the chain);
  `LE_Interp.RHS.realizeWitness*` (SLR:4384-4408).
- **Unchanged**: `LE_Interp.Witness` (SLR:3584) — the `const`
  constructor (3599-3605) still has exactly seven fields (hreg, hlen,
  hle, hty, hA, hC, hR); the `ihA/ihR` seen at SLR:3640 are induction-
  hypothesis names inside `witnessNonempty`'s proof, not constructor
  fields. `FitsRDeep` (now SLR:8578) is the same inductive; its `cons`
  carries a per-BINDING type witness (8583-8584) as before. The
  head-type witness of the synchronized package lives in
  `SelfAdequateAt`'s `hB` input, not in `FitsRDeep`.

#### 3. Gap map at ADQ:4285 (current)

(a) in scope: `hΓ₀` (new), `hR`, `hpatI hmatchI hrhsI`, all
`PatternLeafSpine` fields, `hctorClass`, `hmajorCtor` (IndTyHead ∧
free-closure `CtorDefEq`), `hrecargsI` — as before.

(b) constructible via named lemmas GIVEN the three missing inputs
below: `hP hr := (fixedHeadResult_of_steps inv hΓ₀ constStep fixedStep
(hR hr))` (ADQ:3527); the RHS discharge is fully wired inside
`iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2398-2408).

(c) gaps, ordered by depth:

- **C1 — `inv : JointStratifiedInversion`, non-circularly.** Gates
  everything: `retainedResultAt_of_steps`, `fixedHeadResult_of_steps`,
  `adequateDefeqSelf…`, and any `foldRaw_of_jointBuilder` use. The only
  constructors are `JointStratifiedInversion.of_adequacy`
  (ADQ:435, needs `ContextualAdequacyAt 1`) and
  `of_adequacy_and_typeUniq` (ADQ:4417) — both need the theorem being
  proved. No prover of `JointBuilder.zero`/`first` (ADQ:718-719)
  exists. The designed escape (JointBuilder docstring ADQ:700-716:
  "level-zero adequacy is built first; a specialized base argument
  builds level-one adequacy without predecessor uniqueness") requires
  the level ladder: a level-indexed `adequacy_of_iotaWitnessStepAt`
  consuming `IotaWitnessStepAt` (the consumption at ADQ:3743-3745 is
  already level-pinned, so this refactor is prepared), plus direct
  proofs of the level-0/1 leaf instances. None of this is wired yet.
  **If the worker tries to prove `LR.iotaWitnessStep` as stated
  (polymorphic, no package hypotheses), C1 is unreachable — the
  statement must gain hypotheses or the ladder must land first.**
- **C2 — `constStep : LR.SelfAdequateConstStep Γ₀`** (ADQ:3178-3195),
  unproven, no prover theorem exists. Content: constant self-adequacy
  from the evaluator semantics + `RetainedResultAt` restarts; the
  template is the main induction's const case (ADQ:~3600-3757).
- **C3 — `fixedStep : LR.FixedHeadStep Γ₀`** (ADQ:3474-3483), unproven
  — the application-chain algebra proper, and the home of the
  **residual shape-order blocker**. Status of the blocker: NARROWED but
  live. To invoke `SelfAdequateAt` at the fixed head, the algebra must
  supply (i) `mx.T ≤ root` — available via `typedLowerHead` (SLR:3417)
  ✓; (ii) the stratified typing — now an input of `FixedHeadResultAt`
  (ADQ:1582) ✓ (added in the final pre-pause hours); (iii)
  `mx.HasType bx` — from `typedLowerHead`'s TShape pair, plumbing ✓;
  (iv) **`Witness ρ bx.T B` — the registered type interpreted at the
  LOWER type observation — still has no visible producer.** Soundness
  (`LE_Interp.sound`, `TypedRDeep`) types only upper extensions;
  downward pullback stays invalid at function shapes. The intended
  construction (per review-response point 4 and the new
  `AppLEData`/`HasDomData` extractors) is to BUILD the lower Pi-shaped
  type witness along the registered telescope from capture-type
  witnesses + the out-type witness — that constructor does not exist
  yet. This is the one place the blocker's mathematics remains.
- **C4 — major decomposition** (old G4, unchanged): `hmajorCtor.2` is
  the free-closure `CtorDefEq`; consumers need `CtorExact` (ADQ:2384)
  or exactEq reductions + ctor-field `CtorArgsDefEq`. The typed fold
  `foldRaw_of_jointBuilder` (ADQ:751) needs a full `JointBuilder` —
  same circularity family as C1. A uniqueness-free semantic fold
  instance for THIS consumer is still unwritten.
- **C5 — SubstWF availability at the leaf (wiring check, flagged
  uncertain).** The restated consumers demand `W : SubstWF Γ₀ σ σ' Δ ρ`
  at the leaf's *arbitrary* ρ, but `SubstWF` (SLR:12143-12151) only
  constructs `.id` at `ρ = .nil` plus pushes — no instance for
  arbitrary ρ. Plausible intended resolution: the fixed head is CLOSED
  (`rule.rhsClosed`), so `Witness.closedAt` (SLR:5168) transports its
  witness to `.nil` and `W := SubstWF.id` suffices; but then the
  capture relations (at the ambient ρ) and the head relations (at
  `.nil`) must be recombined. Verify this valuation split *on paper*
  before writing the fixedStep — it smells like erasure-instance
  material if done implicitly.

#### 4. Bottom line

The pause state is a genuine narrowing: G1 resolved (hΓ₀ threaded), G2
dissolved (consumer/tree separation — no Laws needed), the synchronized
package designed, stated, and proved for every non-const structural
case, and the well-founded plumbing finished. What remains is exactly
three unproven inputs (C1 ladder/base-levels, C2 const producer, C3
chain algebra with the narrowed type-witness-at-lower-shape
construction) plus the unchanged major-decomposition assembly (C4) and
one valuation-wiring check (C5). The sorry itself is now a pure
assembly point: nothing in its local scope blocks it except the absence
of those inputs.

## Decision synthesis — the resumption work order (2026-08-14 ~16:45)

Product of three parallel design investigations against the paused
tree (frontier re-map above; a construction-probe pass; a ladder/
alternative adversarial pass). All referenced probe files elaborate
green under `lake env lean` and are preserved in `plans/probes/`
(gitignored). Statements marked PROVED are fully term-proved there and
can be lifted into the codebase directly.

**Architectural decision (supersedes the level-ladder reading of route
2): index the joint fixpoint by stratified typing DEPTH, not shape
level.** The shape-level `JointBuilder` tower (`zero`/`first`/succ) is
structurally unrealizable: `LE_Interp.app` stores function shapes at a
free constructor level and `adequateApp` runs at interpretation-derived
max-levels, so full adequacy at any fixed level requires leaf instances
at unboundedly many levels — every rung is same-index circular
(unbounded-ascent argument; cruxes in `probeC-ladder-crux.lean`, all
seven elaborate). `LiftEquiv` cannot rescue it (iff only at
literally-lifted observations). The predecessor-package alternative is
also dead: the lower head's type lives at a level ≥ the leaf's own, and
adequacy consumes interpretations rather than manufacturing `Witness`es.
Depth, by contrast, genuinely decreases (`HasTypeStratifiedS.forallE_inv`)
and is already the machinery's measure (Nat-first restarts,
`lower : ∀ d' < depth+1`). The level tower may survive only as a final
public assembly facade.

**Work order, in dependency order:**

1. **Depth-indexed bootstrap** (unblocks everything inv-shaped: C1, the
   conversion cases, C4's callbacks). Retire the level-polymorphic
   `iotaWitnessStep` obligation in favor of the depth-indexed form
   (`IotaWitnessStepAt`, parked at ADQ:1493); restate the ~400-line
   bootstrap (ADQ:59-440) depth-bounded (`AdequacyAtDepth` +
   `JointStratifiedInversionAt D` from depth-≤D adequacy — statements
   elaborate in probeC). Mechanical but the largest single chunk.
   STANDING TRIPWIRE: audit every leaf-internal inversion consumption
   for strictly-smaller depth; one same-depth consumption re-imports
   the G4 circularity.
2. **N1 — `typedLowerHeadLE`** (the C3(iv) shape half). Strengthen
   `typedLowerHead` so `elemTy ≤ a` by the spine recursion over the
   single-layer peel, which is PROVED (`peelLayerProved`,
   probeB-2). The witness half is `Witness.mono` (root-lowering is
   legitimate — no pullback). Remaining content: the induction's
   level-lifting bookkeeping and re-anchoring the tail at
   `tyFun.app argCap`. C5's type-witness half is dissolved: registered
   types are closed (`closedAt` + `henv.closedC`), so the witness
   component is valuation-free.
3. **N2 — the capture-domain link. The ONE surviving design decision;
   state it in this file before writing Lean (two-strikes rule).** Each
   capture shape needs a typed upper bound in the *peeled registered
   domain*; element-side singletons need fire points ≥ the spine arg
   while `HasDom.data` supplies typed args ≤ it, so the bound must come
   from peeling the OUTER recursor-constant's `hA` along the pattern
   `Matches` — i.e. an invariant-widening of `FixedHeadResultAt`'s
   `hcap` input (or a joint two-telescope recursion). The context-free
   form (probeB-1 S6) is stated but likely unprovable as written; do
   not attempt it.
4. **C2 `SelfAdequateConstStep`** — assembles from 1-3's outputs
   (probeB-1 S2 confirms the exact `SelfAdequateAt` invocation fits).
5. **C4** — one `RawAlgebra` consumer instance; its `RawTypeUniq` and
   two root callbacks all derive from step 1's inversion package
   (`foldRaw_of_jointBuilder` body pattern, ADQ:756-762). Needs no
   `JointBuilder`.
6. `FixedHeadStep`, the leaf fold, then the endpoint measurement
   (probe: `plans/probes/AxiomProbe.lean`; expect `sort_invS` clean and
   record `forallE_inv`/`sort_forallE_inv` clean simultaneously).

**Verified non-risks** (do not re-litigate): unary recursion axis
suffices (widened component threads through `recNatRDeepConsumerAt` —
`widenedThreading` PROVED; `recDeep₂` has zero adequacy-file
consumers); compat-join demands nothing of the widened consumer
(`Laws.true` separation, and `compat_join` would synchronize anyway);
restarts cover fresh-depth type witnesses (`soundRDeepRestart`).

**Risk ranking:** (1) N2's design — the shape-order wall's surviving
kernel, now one input of one structure; (2) step 1's rung audit; (3)
N1's literal-Pi requirement across `PathSpineWF`'s raw conv/ret edges
(G5) — the peel needs `mkInst recLs rule.df.type` to stay a literal Pi
telescope along capture paths.

## N2 decision — retain one ordered term/type telescope (2026-08-14)

**Decision: take the joint two-telescope route, not a pointwise widening of
`CaptureDefEqAligned`.**  A standalone field for each path cannot certify
that its alleged domain is the domain selected by the *same* registered-type
observation after all earlier dependent applications.  It would also leave
`PathSpineWF.conv`/`.ret` free to switch the syntax telescope without moving
the semantic type witness.  Both are erasure #7 in a new wrapper.

The producer will therefore recurse in `rule.capturePaths` order while the
outer recursor evaluator and its registered-type evidence are still in
scope.  One layer retains, at a common shape level:

- the RHS-spine argument `aSp` and a capture cap `argCap` with
  `aSp ≤ argCap`;
- `argCap.HasType tyDom`, where `tyDom` is the domain of the current peeled
  registered-type observation;
- the recursive result below `g.app aSp`, re-anchored at
  `tyFun.app argCap` on the type side.

The consumer for exactly this layer is now kernel-checked as
`LE_Interp.RHS.ShapeSpine.peelTypedLayer` in `ShapeLogRel.lean`.  Its proof
needs no ambient upper function or downward typing transport: the three
fields above plus the recursive term/type bounds construct the singleton
lambda/Pi layer and prove both lower inequalities.

The completed ordered certificate must expose the fixed-head consumer's
actual endpoint, not merely another synthetic typing pair:

```text
∃ headElem headTy,
  headElem ≤ head ∧ headElem.HasType headTy ∧
  Nonempty (LE_Interp.Witness ρ headTy
    (SExpr.mkInst recLs rule.df.type))
```

`FixedHeadResultAt` will consume that synchronized endpoint.  The current
context-free `typedLowerHead` input remains useful only as the shape fallback
and must not be used to manufacture the final witness.  The ordered producer
belongs at the outer `constDefEq`/`Matches` materialization boundary, where
the recursor's type evidence and the accumulated semantic-to-logical
argument caps coexist; the leaf-local `hcap` map is already too late.

Two invariants are part of this decision:

1. A raw `PathSpineWF.conv`/`.ret` edge may be crossed only by the strictly
   smaller typing-depth inversion package.  A same-depth conversion call is
   the standing circularity tripwire.
2. Valuation changes are explicit.  Closed registered roots may use
   `Witness.closedAt`, but an ambient-`ρ` capture certificate is never
   silently combined with a `.nil` head witness; the joint producer performs
   and records the transport before the leaf boundary.

## Post-resumption rung audit (2026-08-14)

The first implementation pass validated the shape half of the review and
found two additional interface mismatches in the proposed depth bootstrap.
They must be resolved before C2/C4 are implemented against that bootstrap.

1. **The bounded semantic result is path-valued, not ordinary inversion.**
   `AdequacyAtDepth` directly proves bounded sort observation and Pi
   observation with `TypeDefEqPath` domain/codomain outputs.  It does *not*
   directly prove `JointStratifiedInversionAt`: a `TypeDefEqPath` erases the
   stratification depths of its intermediate endpoints, so the existing
   global path-collapse proof cannot be reused inside one bounded rung.
   Probe C only established that the stronger statement elaborated; its body
   was `sorry`.  The kernel-checked result is now named
   `JointStratifiedPathInversionAt.of_adequacyAtDepth`.  Ordinary inversion is
   recovered only after the final, depth-polymorphic adequacy theorem exists.

2. **`IotaWitnessStepAt` is shape-level indexed.**  Its parameter pins the
   `WShape` level of `IotaLeafDefEqAt`; it carries no typing-depth certificate.
   It therefore cannot be the depth rung named in work-order item 1 without a
   new contract.

There is also a statement-level tripwire on the current
`AdequacyAtDepth`: a stratification of only the left endpoint does not bound
the strong equality derivation paired with it.  In `symm` the recursive
derivation needs the opposite endpoint; in `trans` it needs the intermediate
endpoint; and in `const` the registered RHS premise can have a deeper typing
derivation than the constant's declared type.  Consequently the current
definition is a valid observation interface but is too broad, by itself, to
be the induction unit for the main adequacy proof.  The repaired rung must
retain a coherent depth certificate for the strong derivation (or an
equivalent proof-relevant transport invariant), not merely an arbitrary
`HasTypeStratifiedS` proof for its left term.

One dependency previously routed through ordinary bounded inversion has
already been removed safely.  The `HasTypeStratifiedS.defeq` branch of
retained self-adequacy now consumes a `SelfAdequateDefeqStepAt` callback.
Its well-founded implementation calls `LR.adequateDefeq` with heterogeneous
adequacy at the strictly smaller certificate depth; the compatibility
implementation still accepts completed global stratified inversion.  Both
paths are kernel-checked.  This isolates the remaining rung decision to the
constant/fixed-head producers instead of letting it leak through the whole
syntax-directed algebra.

The next bootstrap edit must therefore choose and state the coherent
derivation-depth certificate first.  Until then, do not implement C2/C4 by
assuming either `JointStratifiedInversionAt.of_adequacyAtDepth` or a
depth-indexed meaning for the existing `IotaWitnessStepAt`; neither theorem
exists.

## Ordered-telescope implementation status (2026-08-14)

The consumer half of the N2 decision is now complete and kernel-checked in
`ShapeLogRel.lean`:

- `ShapeSpine.TypedTelescope` retains the exact capture order and threads the
  same `argCap` through both the term spine and the dependent codomain
  `tyFun.app argCap`;
- `TypedTelescope.lowerHead` folds that certificate through
  `peelTypedLayer` into `TypedLowerHead`; and
- `TypedLowerHead.withWitness` exposes the fixed-head endpoint selected
  above:

  ```text
  ∃ headElem headTy,
    headElem ≤ head ∧ headElem.HasType headTy ∧
    Nonempty (LE_Interp.Witness ρ headTy A)
  ```

This closes the ordered *consumer/certificate* problem, not its producer.
The remaining architecture gate is the recursion contract.  The current
Nat-first `R`-deep recursor supplies semantic-child consumer results only at
the parent term's exact typing depth.  That contract is not evaluator
coherent: a shallow constant typing derivation can unfold to a registered RHS
whose syntax-directed typing proof is deeper.  Conversely, restarting only
from the semantic witness loses the retained provenance needed after
conversion.  C2/C4 must therefore wait for a recursion certificate that
supports evaluator unfolding and retained conversion together; the new
ordered telescope must not be wired to the known-invalid same-depth callback.

### Recursion-contract probe

A focused elaboration probe of `selfAdequateExactAtStep` confirms exactly
where the information is lost.  The `HasTypeStratifiedS` induction
hypotheses are generalized over the semantic witnesses, but invoking one at
a selected function/argument/result witness requires
`RDeepChildren (RetainedResultAt ... d)` for that witness.  The parent
package retains consumer results only at abstract `R` edges, and semantic
typing was intentionally separated with tree predicate `T := fun _ => True`.
Consequently the `TypedRDeep` enlargement/join can retain an exact evaluator
tree, but not the consumer result needed when the enlarged witness becomes a
syntax-induction subject.

The two tempting interface changes are both invalid in isolation:

1. Keeping Nat first and asking an `R` child only at the parent's depth fails
   when the reached registered RHS has a deeper syntax-directed typing.
2. Keeping semantic descent first and asking every `R` child at all depths
   still cannot restart on an unrelated converted/enlarged witness: supplying
   both freedoms abstractly admits the cycle “raise depth along `R`, then
   lower depth and restart at the parent witness.”

The repaired certificate must therefore be *provenance-sensitive*.  It must
show that each witness selected by application/conversion is obtained from
the retained subject/type trees by the existing root, valuation, closed,
instantiation, or compatible-join transports, and it must carry the consumer
result across exactly those transports.  Equivalently, a replacement may
use a genuinely derived environment/evaluator bound, but a bare global Nat
assumption would be a new oracle and is not admissible.  This is now the sole
architecture decision before C2/C4; more wrappers around
`recNatRDeepConsumerAt` do not address it.

### Provenance-closure checkpoint

The first half of that replacement is now kernel-checked.  The semantic
module has a free `Witness.TransportClosure P` containing only the transports
that preserve an already-selected evaluator tree (`bot`, root lowering,
valuation growth, compatible join, and closed-term valuation change), with
an automatic `RDeepChildren.Laws` instance.  `Witness.recRDeepTransport`
therefore follows genuine `R` edges before inserting `.base`; it does not
grant a consumer result to a witness merely because that witness has the
same public indices.

On the adequacy side, `LR.CoherentRetainedResult` packages self-adequacy and
the fixed-head result at every stratification depth, and
`coherentRetainedResult_of_step` closes that package from one semantic-first
algebra.  A direct induction,
`Witness.typedRDeep_of_stratified`, also kernel-checks all syntax-directed
typing constructors without a Nat restart.  Binder enlargement is discharged
by semantic typing of the domain; the only abstract input left by this
theorem is proof-relevant transport across the displayed-type equality in a
`HasTypeStratifiedS.defeq` node (`DefeqRDeepTransport`).

The mixed eliminator is now explicit as
`Witness.recRDeepNatTransport`.  It performs structural `R` descent before
the Nat induction, gives genuine `R` children every Nat index, and permits a
strictly-smaller Nat restart only after the caller supplies the restarted
witness's complete `RDeepChildren (TransportClosure ...)` certificate.  The
adequacy specialization is `LR.CoherentRetainedNatStep`, closed by
`coherentRetainedResult_of_natStep`; its two consumer obligations are split
as `CoherentSelfStep` and `CoherentFixedHeadStep` and reassembled by
`CoherentRetainedNatStep.of_steps`.  All of these declarations and the full
adequacy module build with the sole pre-existing iota admission unchanged.

That callback is an *isolation boundary*, not yet an admissible assumption.
In particular, its fully generic statement for an arbitrary tree predicate
`P` is stronger than the final construction may use.  The reverse direction
of a registered definition/action can build a constant witness whose selected
`R` edge is the current RHS witness.  To prove `RDeepChildren P` for that new
constant, a generic transport would need `P` of the current witness, exactly
the result under construction.  Adding such a case to `TransportClosure`
would reintroduce the cycle in proof-relevant form.

Consequently the next interface must retain the *actual strong equality (or
endpoint stratification) derivation* at conversion.  Congruence, beta/eta,
root/valuation transport, instantiation, and compatible join can preserve the
tree structurally; a reverse registered step must instead consume its genuine
smaller RHS-typing/equality hypothesis.  Do not implement
`DefeqRDeepTransport (TransportClosure CoherentRetainedResult)` as a global
oracle, and do not add an unconstrained “conversion” constructor to
`TransportClosure`.

### Depth-local endpoint-rebuild refinement

The next implementation probe found a smaller sufficient interface than a
constructor-by-constructor interpreter for `IsDefEqStrong`, while preserving
the checkpoint's prohibition on a global conversion oracle.

The recursive-edge evidence is now split into two layers:

```text
NatSeed Q d h       := (∀ k, Q h k) ∨ Q h d
NatProvenance Q d h := TransportClosure (NatSeed Q d) h
```

`Witness.recRDeepNatProvenance` exposes `RDeepChildren (NatSeed Q d)` to the
consumer algebra and injects genuine outer-recursion children on the left.
A tree rebuilt after a strict Nat decrease may inject an edge only on the
right, at that exact smaller depth.  `NatProvenance` is introduced later,
inside retained semantic typing, where root/valuation/closed/join transports
must be recorded.  The adequacy specializations are respectively
`LR.CoherentSeedAt` and `LR.CoherentProvenanceAt`; the outer self/fixed-head
consumers see only the inspectable seed, never the free transport closure.

The key new operation is `Witness.RDeepChildren.of_step`.  Given an exact
converted endpoint witness, it rebuilds that witness's evaluator tree
structurally.  Only after a real `R` child's own tree has been rebuilt may a
caller attach a result for that child.  Therefore, inside an outer rung at
depth `D`, the already-complete callback for `d < D` can safely attach
`CoherentRetainedAt ... d` local seeds throughout a freshly selected endpoint
tree.  Reverse definition folding is then harmless: if the new constant's
`R` edge points back to the old RHS witness, that edge receives only the
already-complete result at `d`, never the all-depth result at `D` currently
under construction.

The following bridge is kernel-checked:

- `LR.CoherentSeedAt.rebuild` constructs the inspectable exact evaluator
  tree used at the consumer boundary;
- `LR.CoherentProvenanceAt.rebuild` performs the guarded tree rebuild;
- `LR.CoherentRetainedAt.restart` packages the strictly-smaller-depth
  restart;
- `LR.coherentDefeqRDeepTransportAt` selects the converted endpoint by
  semantic soundness and rebuilds its tree from the local seed constructor;
  and
- `Witness.typedRDeep_of_stratifiedLocal` instantiates the retained semantic
  typing proof with that conversion bridge.

This supersedes only the claim that the equality derivation itself must be
interpreted constructor by constructor.  The safety conclusion above is
unchanged: generic `DefeqRDeepTransport P` remains only an isolation boundary,
and no unconstrained conversion constructor belongs in `TransportClosure`.

### Exact iota-consumer revalidation

The first direct consumer of the refined seed interface is now
kernel-checked as `LRS.iotaDefEq_of_ctorExactAt_coherent`.  It preserves the
`NatSeed` injection through root lowering and splits at the selected fixed
RHS head:

- an `.inl` genuine evaluator child chooses the native depth returned by
  `rule.rhsStrong recLs |>.stratify` and consumes its all-depth fixed-head
  result there;
- an `.inr` rebuilt child consumes only its exact local result and therefore
  requires the registered RHS typing raised to that same local depth.

This confirms that the provenance repair is sufficient on the consumer side
and makes the remaining producer obligation exact.  The direct coherent
constant/fixed-head algebra must justify the local RHS depth budget at the
actual rebuilt endpoint.

The follow-up implementation now packages that obligation as
`LR.CoherentRhsSeedAt Γ₀ Δ depth hRhs rhsType`.  Its two constructors are
deliberately asymmetric:

- a genuine evaluator child carries `CoherentRetainedResult` and therefore
  needs no selected depth certificate; and
- a rebuilt child carries both `CoherentRetainedAt ... depth` and the exact
  `HasTypeStratifiedS Δ rhs rhsType true depth` certificate.

`LRS.iotaDefEq_of_ctorExactAt_coherent` consumes this coupled package at the
*same proof-relevant `R` edge*.  The generic lower-witness eliminator hides
the endpoint index, so the implementation guards its predicate by the
explicit equality to `mkInst recLs rule.df.rhs` and discharges that equality
before opening the package.  This prevents a proof-irrelevant re-selection
from pairing one edge's retained result with another edge's typing budget.
The focused adequacy target builds with this interface.

The stale proof-independent route has also been removed: `RetainedResultAt`,
`FixedHeadStep`, `CoherentFixedHeadStep.of_step`,
`retainedResultAt_of_steps`, and `fixedHeadResult_of_steps` no longer exist.
The syntax-directed self algebra now receives `CoherentSeedAt` trees and
returns coherent retained results directly.

What remains is therefore a producer theorem, not another consumer adapter:
at the actual constant evaluator edge it must construct
`CoherentRhsSeedAt`.  A bare local `CoherentSeedAt` is insufficient in the
constant case, because a shallow constant typing may expose a registered RHS
whose native stratification is deeper.  No all-depth result, generic
conversion transport, proof-independent pairing, or same-depth assumption
may be manufactured to discharge that local branch.  The next producer
contract must retain the derivation that justifies the local RHS certificate
(or retain an equivalent exact ordered type-telescope witness) at the point
where that edge is created.

### Focused-edge correction and producer boundary

Rechecking the exact iota consumer against the live conversion code found one
stale conclusion in the depth-local endpoint-rebuild checkpoint above.
`LR.coherentDefeqRDeepTransportAt` does rebuild a selected endpoint tree, but
it ignores the endpoint stratifications supplied by the equality derivation
and reselects the public endpoint witness through semantic soundness.  It
therefore does **not** preserve the proof-relevant evaluator edge required by
`CoherentRhsSeedAt`, and it must not be used as the final conversion producer.
The checkpoint remains useful for the guarded rebuild operation itself; its
claim that the conversion bridge is complete is superseded here.

The proof-relevant RHS half of the replacement is now kernel-checked:

- `LE_Interp.Witness.appNVarsFocused` peels the exact application witness,
  joins repeated capture occurrences, and retains the literal fixed-head
  sub-witness;
- `Pattern.IotaRule.focusedShapeSpine` specializes that extraction to the
  registered iota tower; and
- `Pattern.IotaRule.focusedRHS` reconstructs the registered RHS using only
  root lowerings of that retained head witness.

Thus the next producer contract is deliberately narrower than another
conversion oracle.  While the reverse registered action still has both the
exact endpoint derivation and the exact RHS witness in scope, it must produce
one package containing:

1. the retained fixed-head sub-witness and its ordered semantic capture
   spine;
2. the ordered registered-type telescope for the same capture caps; and
3. either the genuine evaluator-child result or the exact local
   `HasTypeStratifiedS` derivation for the focused RHS edge.

Only after constructing that package may the reverse action rebuild the
constant with `appsRealizeFocused`.  Extending `LR.constDefEq` alone cannot
repair the loss: the current reverse action uses proof-independent
`RHS.of_applyS` followed by ordinary `apps_realize`, so it can discard the
selected edge before `constDefEq` is entered.  The implementation order is
therefore fixed: retain the ordered type derivation at action materialization,
rebuild the focused constant witness, then thread the resulting
`CoherentRhsSeedAt` through the constant/fixed-head algebra.

### Packed-telescope consumer checkpoint (2026-08-15)

The consumer side of that order is now stronger than the earlier
`TypedTelescope`/`Captures` sketch.  The active tree contains
`ShapeSpine.TypedTelescope.WithCaptures`, a single inductive certificate that
owns the semantic spine, the registered-type telescope, and the exact aligned
capture payload at every layer.  Its fold
`TypedTelescope.fixedHeadShapeChain` returns the lower term, its lower
registered-type observation, the type bound, and the logical application
chain from the same constructor choices.

On the adequacy side, `LR.FixedHeadTelescope.withWitnessAndChain` lowers the
registered-type witness and returns it together with that same chain.
`LR.FixedHeadTelescope.toApplicationWith` then zips the chain with the
concrete `PathSpineWF`, invoking semantic conversion only for actual
`conv`/`ret`/domain edges and invoking head self-validity only for the literal
lower endpoint just selected.  Both experimental semantic modules build with
these declarations, and no new admission was introduced.

This closes the downstream erasure risk: once a producer supplies
`WithCaptures`, no later theorem can independently reselect the lower head,
its registered type, or its capture chain.  It does **not** yet construct that
certificate.  The live `StrongSoundEq.ofAction` reverse direction still calls
proof-independent `RHS.of_applyS`, `build_spine`, and `apps_realize`; by then
the exact RHS witness used by the endpoint derivation may already have been
replaced.  The next producer edit must therefore live at (or immediately
inside) that reverse-action/conversion boundary and return the packed
telescope before rebuilding through `appsRealizeFocused`.

### Producer-placement correction and first depth peel (2026-08-15)

The last sentence above is too literal about what can be returned at the
reverse-action boundary.  `LR.FixedHeadTelescope` is instantiated with
`CaptureDefEqAligned.AtShapes`; it depends on the later adequacy-side
`mx`/`my` endpoints, shared `captureType`, substitution, and logical relation.
None of those values exists inside `StrongSoundEq.ofAction`.  Constructing
that exact package there is therefore not merely inconvenient but
ill-typed.  The semantic conversion boundary must instead retain the exact
focused RHS witness and its derivation-aware registered-head typing.  The
final `WithCaptures` fusion belongs at the fixed-head adequacy boundary,
where that semantic certificate and the logical capture payload first
coexist.

The first producer-side depth fact is now kernel-checked in `SExpr.lean`:

- `HasTypeStratifiedS.app_inv` removes outer displayed-type conversions and
  exposes all five premises of the literal application derivation at
  `depth - 1`;
- `foldl_app_head` iterates that inversion through a concrete left-associated
  application tower;
- `foldl_app_head_of_ne_nil` proves that a nonempty tower's literal head is
  typed at a strictly smaller depth; and
- `Pattern.IotaRule.rhsHeadStratified{,_of_nonempty}` specializes the result
  to the exact fixed RHS selected by `rule.rhsApply`.

This removes the former uncertainty about whether focused application
inversion supplies a genuine well-founded decrease.  The remaining type
alignment is now explicit: the native head derivation returned by the peel
has an existential `HeadType`, while `CoherentRhsSeedAt` requires the
registered `mkInst recLs rule.df.type`.  The next producer theorem must align
those two at the same smaller derivation depth using the concrete registered
capture spine (and only its actual conversion edges).  Once that alignment
is retained, `appsRealizeFocused` can rebuild the outer constant with edges
generated from the exact head witness; the adequacy-side fold can then fuse
the aligned captures into `FixedHeadTelescope` without reselecting the head
or its type.

### Exact head handoff correction (2026-08-15)

The final paragraph above overstates the need to identify the peeled native
`HeadType` with the registered rule type.  The head-term half is
heterogeneous: `AdequacyAtDepth` is indexed by the exact registered
`HasTypeStratifiedS` derivation but accepts the semantic witness for the
displayed registered type independently.  Consequently the proof does not
need raw type uniqueness, an equality cast, or a general conversion oracle
to obtain the head term relation.

The consumer now makes the two genuinely distinct obligations explicit.
`LR.AdequacyAtDepth.closedHeadSelf` returns both the head term relation and
semantic validity of the exact registered head type at the same lower type
observation.  The former comes from heterogeneous term adequacy.  The latter
uses `hstrat.isType` and adequacy at the preceding type rung.  Moreover,
`LR.FixedHeadApplication` retains the exact head term relation instead of
discarding it and asking a later consumer to run self-adequacy again.  The
focused adequacy module kernel-checks with this term-and-type handoff and no
new admission.

The remaining producer obligation is therefore narrower and more concrete:
construct `ShapeSpine.TypedTelescope.WithCaptures` (or an equivalent single
proof-relevant package) whose lower head type, ordered capture layers, and
output observation are all selected from one recursion.  An independently
chosen lower type witness is insufficient, even when it is propositionally
compatible, because downward projection through a function observation is
not generally available.  This ordered packed producer--not equality of the
native and registered syntax types--is now the live architecture gate.

### Focused reverse-action certificate (2026-08-15)

The first producer-side handoff at the corrected boundary is now
kernel-checked.  `Pattern.IotaRule.FocusedActionPreimage` is a data-bearing
certificate selected from the exact interpreted RHS witness.  It retains:

- the literal fixed-head sub-witness and ordered semantic capture spine;
- the matched constant/argument prefix reconstructed by `build_spine`; and
- the exact `Const` derivation whose abstract evaluator relation is
  `headWitness.LowerEdge`.

`Pattern.IotaRule.focusedActionPreimage` constructs the certificate without
calling `RHS.of_applyS`, and `FocusedActionPreimage.witness` realizes the
matched redex with `Witness.appsRealizeFocused` at a caller-supplied typed
observation.  Thus reverse action no longer needs to erase and then reselect
the fixed RHS edge.

This checkpoint intentionally stops before claiming the complete producer.
The caller must still obtain that typed RHS observation from the retained
endpoint stratification without losing its evaluator tree, and the
adequacy-side boundary must still fuse the retained semantic spine with the
ordered logical captures into `WithCaptures`.  Those are now separate,
explicit obligations; neither can be replaced by public semantic soundness
or an independently selected type witness.

### Derivation-aware reverse-action transport (2026-08-15)

The focused certificate is now wired into retained semantic conversion.
`LR.focusedExtraReverseRDeepAt` dispatches the pattern carried by an
`IsDefEqStrong.extra` node: zero-arity definition patterns keep the guarded
local endpoint rebuild, while generated iota patterns use the exact
`FocusedActionPreimage` path.  The internal focused evaluator is generalized
over the action's declared type; the public displayed-type conversion remains
the `Sort u` specialization.

`LR.coherentDefeqRDeepPairAt` interprets the strong equality
bidirectionally.  It swaps continuations under `symm`, composes them under
`trans`, and focuses precisely the reverse branch of `extra`.  Consequently
an iota action nested under equality symmetry or composition can no longer be
hidden by one proof-independent soundness call.  The live
`coherentDefeqRDeepTransportAt` now consumes this derivation-aware path, and
the focused adequacy module kernel-checks with the sole pre-existing iota
admission unchanged.

This closes evaluator-edge preservation through conversion, but not the
coupled producer required by the coherent iota consumer.  The rebuilt
constant's `LowerEdge` still receives `CoherentProvenanceAt`; it does not yet
receive the exact registered-head `HasTypeStratifiedS` certificate needed to
form `CoherentRhsSeedAt` in the local branch.  That certificate must be
constructed where the retained semantic spine and the concrete ordered
`PathSpineWF`/capture relations coexist, then packed with `WithCaptures`.

### Producer split after live-signature audit (2026-08-15)

The last sentence above places one half of the remaining producer too late.
The logical `WithCaptures` package still belongs at the fixed-head adequacy
boundary: its `mx`/`my`, substitution, logical relation, and aligned capture
payload do not exist during semantic conversion.  The exact local registered
RHS typing certificate cannot wait for that boundary, however.

The live signatures make the loss explicit:

- `StratifiedDefeqRDeepTransport` supplies both endpoint
  `HasTypeStratifiedS` derivations at the conversion node;
- `coherentDefeqRDeepTransportAt` currently binds them as `_hA`/`_hB` and
  returns only `RDeepChildren (CoherentProvenanceAt ...)`;
- the focused `extra` branch preserves `headWitness.LowerEdge`, but
  `CoherentProvenanceAt.local` stores only `CoherentRetainedAt`; and
- `CoherentFixedHeadStep` later receives neither the discarded endpoint
  derivation nor an action-indexed replacement for it.

Consequently generic provenance plus the later ordered capture telescope is
not by itself an implementable producer for `CoherentRhsSeedAt`.  Public
semantic soundness would merely reselect the endpoint, and
`rule.rhsStrong.stratify` chooses an unrelated native depth that need not fit
the local guarded-restart depth.

The producer must be split across the two boundaries:

1. **At focused reverse conversion**, retain a semantic-only certificate
   tied to the literal `LowerEdge`: the exact fixed-head witness and semantic
   spine already carried by `FocusedActionPreimage`, plus the derivation/depth
   evidence needed to justify the local registered RHS typing.  This package
   must survive the result type of derivation-aware conversion; constructing
   it transiently and returning plain `CoherentProvenanceAt` still erases it.
2. **At the fixed-head adequacy boundary**, combine that retained semantic
   and typing certificate with the concrete `PathSpineWF` and aligned logical
   captures to construct `TypedTelescope.WithCaptures`, then consume it via
   `FixedHeadTelescope.toApplicationWithAdequacyAtDepth`.

This correction does not reopen the rejected raw type-equality route and does
not move logical captures into conversion.  It only identifies the minimum
action-indexed fact that must cross conversion before the later synchronized
fusion can be sound.

### Post-implementation preservation audit (2026-08-15)

The first enriched-provenance implementation kernel-checks, but auditing its
actual flow through `coherentDefeqRDeepPairAt` found a second erasure point.
The recursive interpreter does visit an `extra` nested below `symm` or
`trans`, and `rebuildFocused` tags the literal lower edges of the reconstructed
constant.  That is not yet sufficient to say the certificate survives the
whole equality:

- each non-`extra` leg is implemented by
  `coherentDefeqRDeepFallbackPairAt`;
- that fallback deliberately ignores the incoming `RDeepChildren` tree,
  selects a fresh endpoint through public semantic soundness, and rebuilds a
  new local tree; and
- consequently, in a composite equality, any fallback leg *after* the
  focused leg erases the focused seed before the final endpoint is returned.

Thus the earlier statement that a nested action “can no longer be hidden” is
only a traversal claim.  It is not yet an end-to-end preservation theorem.
The next contract must make the suffix explicit: either interpret the
remaining equality constructors proof-relevantly while retaining the same
focused evaluator relation, or return a conversion-path certificate whose
consumer can replay those exact endpoint choices.  Adding more data solely
to `FocusedRhsOriginAt`, while leaving the suffix fallback proof-independent,
cannot close the producer.

This also sharpens the role of the retained typing fields already added to
`FocusedActionPreimage`.  They are necessary at the action boundary, but they
must travel with the proof-relevant evaluator edge through the *entire*
conversion path.  A transient focused node followed by a plain local rebuild
is observationally indistinguishable from the erasing implementation that
the producer split was meant to replace.

### Closed-valuation leaf consumer and consumption-tower survey (2026-08-15, session-C subagent)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf (statement now ADQ:6406, sorry
ADQ:6436 after this session's insertions).  Source and olean were
consistent at 06:24; a fresh full elaboration reconfirmed the state before
any edit.

**The preservation question of the previous section is already answered in
the tree.**  Between writing "Post-implementation preservation audit" and
pausing, the previous writer landed the replayable conversion-path
certificate (candidate 2): `LR.FocusedRhsTraceAt` (ADQ:3882),
`LR.FocusedRhsTraceBundleAt` (ADQ:3896), the `carried`/`replayed`
constructors of `LR.CoherentSemanticSeedAt` (ADQ:3907), and
`LR.CoherentProvenanceAt.rebuildTracingFocused` (ADQ:4220), which is now
wired into both legs of `LR.coherentDefeqRDeepFallbackPairAt` (ADQ:4845).
The fallback no longer discards the incoming tree's focused history: every
rebuilt recursive edge carries the complete source trace bundle, replayable
at matching registered-head syntax.  I did not re-litigate that design;
this session's work is downstream of it.

**Two consumption walls found between the conversion layer and the sorry,
one repaired, one mapped:**

1. *SubstWF/valuation coupling (repaired this session).*
   `LR.FixedHeadResult`/`FixedHeadResultAt` are consumed through
   `LR.SubstWF Γ₀ σ σ' Δ ρ` at the witness's own valuation, and the only
   closed `SubstWF` constructor is `.id` at `Valuation.nil`
   (SLR:14222).  The `IotaWitnessStep` leaf receives an arbitrary caller
   valuation with no fits certificate, so the existing consumers
   `iotaDefEq_of_ctorExactAt_fixedHead` and `_coherent` are unusable at
   that leaf as stated — their `W` pins ρ.  Repair, kernel-checked and
   landed: the registered RHS is closed, so the selected head witness is
   transported to `Valuation.nil` at the same root shape by
   `Witness.closedAt` (whole-tree transport, not endpoint reselection)
   and consumed at `SubstWF.id` with `Γ := Γ₀` instances of
   `rule.rhsStrong`.  This is the C5-dissolution argument
   ("registered types are closed") applied to the witness side, and it
   retains everything: spine, typed lower head, raw telescopes, and
   aligned captures were already valuation-free.

2. *The chain wall (mapped; NOT repaired; do not attempt leaf-locally).*
   At the sorry, the major arrives as `hmajorCtor.2 :
   LRS.CtorDefEq Γ₀ (LR Γ₀) majorX majorY (ctor' ...)` via
   `LR.DefEq.ctor'_inv` — the free closure, not a single `CtorExact`.
   Consuming it requires the normalized chain fold
   (`CtorDefEq.toChain` + rectangles; the exact-link rectangle
   `LRS.iotaDefEqRect_of_ctorExactAt` ADQ:2748 was prepared for exactly
   this and `LogRel.DefEqRect.trans` composes shared-middle rectangles).
   The blocker: interior chain vertices must be retyped at the recursor
   domain, and every chain consumer that does this
   (`CtorChain.rawDefEqAt`, `foldRaw`, `foldRaw_of_stratifiedInversion`)
   takes raw type uniqueness / `JointStratifiedInversion` — which is only
   constructible FROM adequacy (`of_adequacy` needs
   `ContextualAdequacyAt 1`, ADQ:582), i.e., not at the bare leaf (G4).
   A uniq-free fold was examined and fails structurally: `NativeAlgebra.trans`
   threads no typing for the shared middle vertex, and deriving it from
   link raw equalities reintroduces pairwise type uniqueness.  Conclusion:
   the leaf sorry is discharge-LAST.  It needs inversion at strictly
   smaller stratified depth, i.e., the depth-indexed adequacy rungs
   (`LR.AdequacyAtDepth` producers) of work-order step 1, which remain
   unlanded — nothing in the file yet produces `AdequacyAtDepth`, it is
   only consumed (ADQ:31/1834/1946/5355).

**Landed this session (kernel-checked, elaboration green, zero errors, the
sole sorry unchanged at ADQ:6436):**

- `LRS.iotaDefEq_of_ctorExactAt_closedFixedHead` (ADQ:2871).  The
  ρ-decoupled exact-link consumer: same interface as `_fixedHead` but the
  fixed-head oracle is `∀ hX : Witness Valuation.nil root X,
  FixedHeadResult Γ₀ hX`, consumed after `closedAt` transport at
  `SubstWF.id`.  Proof goes through `IotaRHSDefEq.of_nonbotWitness` (no
  P-threading needed — the oracle is global, so no `mono`-commutation
  obligation arises).
- `LRS.iotaDefEq_of_ctorExactAt_natStep` (ADQ:4561).  The formal residual-
  gap statement: the exact iota link follows from
  `LR.CoherentRetainedNatStep Γ₀` alone, via
  `coherentRetainedResult_of_natStep` + `CoherentRetainedResult.fixedHead`
  + the closed consumer above.

**The remaining tower, in dependency order (all names live in the file):**

1. Depth bootstrap (work-order step 1, still the critical path): produce
   `LR.AdequacyAtDepth Γ₀ d` / `ContextualAdequacyAtDepth d` by strong Nat
   induction.  Both walls above point here: it feeds
   `SelfAdequateDefeqStepAt.of_lowerAdequacy` (ADQ:5355) and depth-bounded
   inversion (`JointStratifiedPathInversionAt.of_adequacyAtDepth`,
   ADQ:563) for the chain fold's vertex retyping.
2. `LR.SelfAdequateConstStep Γ₀` (ADQ:5298, unproved): the constant case
   remake consuming `children`/`lower` instead of derivation induction; its
   internal iota leaf should use the coherent consumer with seeds drawn
   from the const witness's own `RDeepChildren` tree — NOT the global
   `iotaWitnessStep`.
3. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4503, unproved): the
   `WithCaptures` fusion.  Its missing ingredient is the ordered
   spine→`FixedHeadTelescope` producer (N1/N2 peel); only the `nil`/`cons`
   constructors exist today (ADQ:1700/1715).  `SelfAdequateAt` (not global
   `AdequacyAtDepth`) supplies the head validity inside the algebra via
   `of_fixedHeadTelescope`/`toApplicationWith`.
4. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4516) then the chain
   fold at the leaf feeding `iotaDefEq_of_ctorExactAt_natStep` per exact
   link, with vertex retyping through the depth-bounded inversion of 1.

**Design note recorded for the depth-local variant:** a depth-local closed
consumer (analogue of `_coherent` at `Valuation.nil`) would need either a
witness-term commutation lemma `closedAt`-vs-`mono` (to thread a
per-witness seed through `of_nonbotWitnessResult`'s `hmono`), or seeds
stated directly at `Valuation.nil` witnesses.  Deliberately not attempted
this session (two-strikes discipline; the global-oracle form needed no such
commutation).  Whoever writes `SelfAdequateConstStep` should prefer stating
its rule-indexed seeds at nil witnesses from the start.

### Depth bootstrap landed conditionally; N1 peel core ported (2026-08-15, session-C subagent 2)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf.  Reconfirmed by full elaboration
before edits; the identical inventory holds after every edit below (final
log `elab2`: sole sorry warning at ADQ:6540:8, the same leaf statement,
moved only by insertions).

**Landed (all kernel-checked; no new sorries):**

- `LR.IotaWitnessStepAtDepth Γ₀ depth` (ADQ:1701) and
  `LR.ContextualIotaWitnessStepAtDepth depth` (ADQ:1709): the
  depth-indexed joint-leaf obligation.  At rung `depth` the leaf
  producer receives `∀ d' < depth, LR.ContextualAdequacyAtDepth d'` —
  the raw strict-predecessor family, deliberately unprocessed — and
  returns the ordinary level-polymorphic `IotaWitnessStep Γ₀`.
- `JointStratifiedPathInversionAt.of_predecessorAdequacy` (ADQ:584):
  the `<`-shaped bridge — a successor rung's strict family below
  `depth + 1` is exactly the `≤ depth` family `of_adequacyAtDepth`
  (ADQ:563) consumes, so a leaf producer at rung `d + 1` can assemble
  bounded path inversion at depth `d` with no same-depth adequacy
  consumption.
- `LR.contextualAdequacyAtDepth_of_iotaSteps` (ADQ:6503): THE
  BOOTSTRAP.  `(∀ d, ContextualIotaWitnessStepAtDepth d) → ∀ d,
  ContextualAdequacyAtDepth d` by `Nat.strongRecOn`.  The step case
  hands the untouched strong-induction hypothesis to `steps d` and runs
  `adequacy_of_iotaWitnessStep` (ADQ:5808) with the resulting leaf.  No
  separate base case: at `d = 0` the family quantifier is vacuous and
  the step receives an empty package (honesty note below).
- `LR.contextualAdequacyAt_of_adequacyAtDepth` (ADQ:6519) and the
  composition `LR.contextualAdequacyAt_of_iotaSteps` (ADQ:6530): the
  full depth tower subsumes every level-indexed contextual package via
  `IsDefEqStrong.stratify`.  The level tower is now formally a facade
  over the depth fixpoint, closing that architectural decision of the
  2026-08-14 synthesis.
- `WShape.HasTypeLam.peelLayer` (ADQ:1743): verbatim port of the PROVED
  probe `probeB.peelLayerProved` (plans/probes/probeB-2.lean), placed
  with the `FixedHeadTelescope` producers it will feed.  `hgle`/`hty`
  stay in the signature (unused by the layer algebra, two lint warnings
  accepted) to pin the spine recursion's interface.  `widenedThreading`
  was NOT ported: it commits the `LowerSyncAt` widened-component
  interface, which belongs to the N2 capture-domain decision this file
  requires stating in prose before Lean.

**Why the design respects the standing constraints.**  Depth-indexed,
never level-indexed: the fixpoint index is stratified typing depth; the
leaf stays level-polymorphic exactly as `IotaWitnessStep` is today.
G4: the bootstrap constructs no predecessor package — no inversion, no
uniqueness, nothing derived from the IH inside the induction — it
forwards the raw rung family through the step interface, whose
docstring names the two sanctioned consumers
(`of_predecessorAdequacy`, `SelfAdequateDefeqStepAt.of_lowerAdequacy`,
ADQ:5440).  The global sorried `iotaWitnessStep` is never referenced.
Erasure: the step receives the full contextual family, not a
projection.

**Honesty note — where the remaining depth content lives.**  Producing
`AdequacyAtDepth Γ₀ d` cannot use the rung's own certificate: the
derivation induction is depth-blind (the ADQ:25 docstring caveat is
real — `trans`/`symm`/evaluator descent reach subderivations the
left-endpoint certificate does not bound, and depth-0 certificates
exist via `sort'`, so even the base rung covers arbitrary derivations
with sort-left endpoints).  The bootstrap therefore ignores `hstrat`
(it is a hypothesis of the PRODUCED statement, for consumers), and
`IotaWitnessStepAtDepth 0` degenerates to the bare global leaf.  The
depth restriction that will make the step family dischargeable must
come from the leaf's OWN certificates — the registered-rule stratified
typings (`rhsStratified`/`headStratified`, SLR:9280-9283) that bound
the chain fold's vertex retyping — not from the adequacy root.  That is
the rung audit of the 2026-08-14 synthesis (risk #2), now localized to
one named obligation instead of an amorphous circularity.

**Remaining tower (updated difficulty against the previous survey):**

1. `LR.SelfAdequateConstStep Γ₀` (ADQ:5383, unproved; hard, design
   partly pre-committed): state its rule-indexed seeds at
   `Valuation.nil` witnesses from the start (previous section's design
   note).  Its conversion callback is now one hypothesis away:
   `of_lowerAdequacy` consumes exactly the bootstrap's rungs.
2. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4588, unproved; medium once N2 is
   stated): ordered spine→`FixedHeadTelescope` producer.  Per-layer
   core is now in-file (`peelLayer`); N2 (capture-domain link) remains
   the one open design decision and must be stated in this document
   before Lean.
3. Assembly `CoherentRetainedNatStep.of_steps` (ADQ:4601), then the
   chain fold at the leaf feeding `iotaDefEq_of_ctorExactAt_natStep`
   (ADQ:4646) per exact link, vertex retyping through
   `of_predecessorAdequacy` at the rule certificates' depths.  If those
   depths stay strictly below the rung index, the step family
   discharges per-rung and the bootstrap closes unconditionally; if a
   same-rung consumption appears, that is the G4 tripwire firing — stop
   and escalate to a design session, do not patch.

Consumers already prepared (`closedHeadSelf` ADQ:1919,
`toApplicationWithAdequacyAtDepth` ADQ:2009, `of_lowerAdequacy`
ADQ:5440, bounded inversion ADQ:563/584) are all reachable from the
single hypothesis family `∀ d, LR.ContextualIotaWitnessStepAtDepth d`.

— session-C subagent 2

### SelfAdequateConstStep interface decision — seeds pinned by the ambient SubstWF, not restated at nil (2026-08-15, session-C subagent 3)

Written before the Lean, per the two-strikes prose-first rule, because it
deviates in letter (not in force) from the standing note "state the
rule-indexed seeds at `Valuation.nil` witnesses from the start."

**Where the seeds live.**  Inside `SelfAdequateConstStep`'s proof the
constant witness is destructured together with its
`RDeepChildren (CoherentSeedAt Γ₀ (depth+1))` tree.  The `const` branch
of that tree (SLR:4170-4173) yields, per abstract `R` edge, the exact
seed `pR : ∀ m e hr, CoherentSeedAt Γ₀ (depth+1) (hR m e hr)` and the
child's own tree `cR`.  These seeds are attached to witnesses at the
constant's ambient valuation ρ — and, crucially, the const case proves an
`LR.Adequate` conclusion, so it works under an introduced
`W : LR.SubstWF Γ₀ σ σ' Γ ρ` that pins that same ρ end to end.

**Why the nil restatement is not available here.**  Transporting a seed's
result to the `closedAt`-transported witness needs
`CoherentRetainedAt Γ₀ hV d → CoherentRetainedAt Γ₀ (hV.closedAt cl) d`.
Its `SelfAdequateAt` half quantifies over demands
`LE_Interp.Witness Valuation.nil bx.T B → Adequate Γ₀ Δ Valuation.nil …`
whose `Adequate` components quantify over `SubstWF … Δ Valuation.nil`;
the only closed constructor is `.id` at `Δ = Γ₀`, `σ = σ' = .id`, and the
ρ-stated result can never be instantiated there (no
`SubstWF Γ₀ .id .id Γ₀ ρ` exists for a non-nil ρ).  The same wall blocks
`RDeepChildren.closed` (SLR:5598): its `hP` premise is exactly this
underivable stability.  So per-rule seeds *stated at nil witnesses* are
not producible from the tree; a `SelfAdequateConstStep` conditional on
them would be a hypothesis no producer can ever discharge.

**What the standing note was actually protecting.**  The predecessor's
rationale was "no `closedAt`-vs-`mono` commutation."  The commutation
only arises when a per-witness seed must be threaded through
`of_nonbotWitnessResult`'s `hmono` *and then* moved across a valuation
change.  The kernel-checked `_coherent` consumer (ADQ:4697) already
threads per-witness seeds through `hmono` via `CoherentRhsSeedAt.mono`
with zero valuation transport, consuming the seed's `FixedHeadResultAt`
at the caller's own `W`.  The const case has that `W`.  Decision:

- The internal-leaf obligation is factored as
  `LR.CoherentIotaLeafStep Γ₀`, stated at the ambient valuation with an
  explicit `SubstWF Γ₀ σ σ' Δ ρ` input plus the per-edge seed family,
  the per-edge child trees, and the strict-predecessor restart family —
  the exact inventory `_coherent` + the chain fold will want.  No
  `closedAt` appears anywhere in the const step, which satisfies the
  note's operative content (no commutation obligation is ever created).
- The nil-witness form remains the right interface where no caller
  SubstWF exists — the bare global leaf — and is already served there by
  the global-oracle consumer `_closedFixedHead` (ADQ:2956).  Nothing in
  this decision forecloses it.

**Second interface introduced.**  The stratified `const` rule carries
only the constant's *type* certificate (SExpr:2383-2387); unlike the
strong constructor it carries no definitional-unfold premise.  The
unfold must therefore come from the witness's own `R` edge seed.  A
genuine child's all-depth result covers the value's native stratified
depth; a *local* (guarded-restart) seed is pinned to `depth+1` while the
registered value's certificate depth is unrelated — the exact
"registered premise deeper than the declared type" tripwire from the
2026-08-14 rung audit, now localized.  That branch is factored as
`LR.ConstDefnLocalStep Γ₀` (local seed on a registered definitional
value extends to every certificate depth), keeping the provable branch
proved and naming the budget question instead of patching it.

— session-C subagent 3

### SelfAdequateConstStep landed conditionally on two named leaf obligations (2026-08-15, session-C subagent 3)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf (6540:8 before this session's
insertions).  Reconfirmed by full elaboration before any edit; the same
sole-sorry inventory holds after the landing (final log `main1`, exit 0:
the one warning at the leaf statement, moved only by insertions to
ADQ:6866, sorry token ADQ:6896; warning profile otherwise byte-identical
to the baseline modulo line shifts).

**Landed (kernel-checked; no new sorries; probe-verified first in
`plans/probes/probeC2-conststep.lean` against the fresh olean, then ported
verbatim):**

- `LR.CoherentIotaLeafStep Γ₀` (ADQ:5820): the internal iota-leaf
  obligation of the constant producer.  Inputs: the depth index, the
  per-`R`-edge seed family `∀ m M hr, CoherentSeedAt Γ₀ depth (hR m M hr)`
  and exact child trees (both drawn from the const witness's own
  `RDeepChildren` const branch), `Ctx.WF Γ₀`, the ambient
  `SubstWF Γ₀ σ σ' Δ ρ`, and the strict-predecessor coherent restart
  family.  Output: level-polymorphic `IotaLeafDefEqAt Γ₀ level c ls
  (Lower R)`.
- `LR.ConstDefnLocalStep Γ₀` (ADQ:5848): the definitional-unfold budget
  obligation — a local (guarded-restart) coherent seed on a registered
  definitional value extends to the value's own certificate depths.
- `LR.SelfAdequateConstStep.of_steps` (ADQ:5871, ~250 lines):
  `Ctx.WF Γ₀ → CoherentIotaLeafStep Γ₀ → ConstDefnLocalStep Γ₀ →
  SelfAdequateConstStep Γ₀`.  Everything else in the constant case is
  proved outright — see the case inventory below.
- `LR.CoherentSelfStep.of_leafSteps` (ADQ:6122): composition through
  `coherentSelfStep_of_steps`, so the full self-adequacy half of the
  coherent Nat algebra is now conditional on exactly
  `defeqStep`-family + the two new Props (and `defeqStep` is itself one
  hypothesis away via `SelfAdequateDefeqStepAt.of_lowerAdequacy` from the
  bootstrap rungs).

**Case inventory of the remake** (mirrors the old derivation-induction
const case at `adequacy_of_iotaWitnessStep`, with every induction
hypothesis replaced by witness-tree data):

- Witness `bot` / `Const.bot`: unchanged bottom collapses.
- `Const.lam` (the recursion): the constant-type observation that the old
  proof took from `ihTy` is now
  `(CoherentRetainedAt.restart lower (Nat.lt_succ_self depth)).1` at the
  sound-transported witness of the type — legitimate because the
  stratified `const` rule carries the type certificate at the strictly
  smaller `depth`.  The reached leaf callback `evalPat` is
  `PatternLeafDefEqAt.of_iota (leafStep (depth+1) hR hΓ₀ W pR cR lower k)`
  — the witness's own seeds, never the global sorried `iotaWitnessStep`.
- `Const.ctor` / `Const.indTy`: the `IndTyHead` fact the old proof took
  from `ihF` is recovered with no `F`-bundle at all: the same `lower`
  restart at the type witness, `toValTy` landing at the unfold-forced
  `.indTy` type shape, and the definitional `TyDefEq`-at-`.indTy`
  conjunction (the `indTy_m` simp lemma is `rfl`; the projection form
  needs the definitional bridge, not the simp set).
- `Const.pat` (nullary = definitional unfold): the old `ihDef` is
  replaced by the seed on the witness's own `R` edge (`Lower R` at the
  registered value).  Genuine child (`inl`): the all-depth result is
  consumed at the value's native stratified depth from
  `defn_whRed (Γ := Γ)` + `stratify`, then the goal closes by
  `(LR Γ₀).whr` along `defn_whRed (Γ := Γ₀)`'s one-step reduction.
  Local child (`inr`): `ConstDefnLocalStep` — the one branch with a real
  depth-budget gap (below).

**The seed-interface decision** is recorded in full in the preceding
section ("SelfAdequateConstStep interface decision", same date): seeds
stay at the ambient valuation pinned by the caller's `SubstWF`; the
`Valuation.nil` restatement demanded by the earlier design note is not
producible from the tree (per-edge retained results quantify over
`SubstWF` at their own valuation and do not transport across `closedAt`;
`RDeepChildren.closed`'s `hP` premise is that same underivable
stability), while the ambient-`W` interface is exactly what the
kernel-checked `_coherent` consumer threads with zero valuation
transport, so the note's operative content — never create a
`closedAt`-vs-`mono` commutation obligation — is satisfied by
construction.

**What discharging each hypothesis takes:**

1. `CoherentIotaLeafStep` is the chain wall, scoped: split the joint
   `RecursorIotaPattern` match (the `Matches.app` inversion already used
   by the bare leaf at ADQ:6866), normalize the major's free-closure
   `CtorDefEq` through `CtorDefEq.toChain` + rectangles, retype interior
   vertices with strictly-smaller bounded inversion
   (`JointStratifiedPathInversionAt.of_predecessorAdequacy`, ADQ:584),
   and per exact link run `iotaDefEq_of_ctorExactAt_coherent` (ADQ:4697)
   with `hP := CoherentRhsSeedAt.of_seed` applied to the received seeds —
   the right-injection branch needs the RHS typing raised to the seed's
   index, which is the same rung-audit question as item 2's.  Note the
   Prop hands over the raw `NatSeed` family untruncated plus the child
   trees, so the discharger keeps every option (including per-edge
   sub-restarts).  If the discharge turns out to need the constant's own
   type certificate as well, extend the Prop — it has exactly one call
   site (ADQ:6017, the `evalPat` construction).
2. `ConstDefnLocalStep` is the localized "registered premise deeper than
   the declared type" tripwire from the 2026-08-14 rung audit.  Two known
   discharge routes, to be decided at assembly time: (a) prove that the
   coherent tower only ever attaches local seeds to definitional-value
   edges together with a budget covering the value's certificate (then
   this Prop follows from the producer invariant — likely requires
   enriching `CoherentSeedAt`'s right injection with the coupled typing,
   the same enrichment `CoherentRhsSeedAt` models one level up); or
   (b) show closed registered values admit depth-extension of local
   coherent results directly.  Route (a) is an ADQ-file interface change
   with wide transport-lemma ripple; deliberately not attempted this
   session (two-strikes discipline).

**Opportunistic extension not attempted.**  The gate condition (short
hypothesis list) was met, but `CoherentFixedHeadStep`'s missing N2 piece
is the one OPEN interface decision the predecessor explicitly declined to
commit (`LowerSyncAt` / widened `hcap`), and it must be a prose decision
first.  With the session budget spent on the const landing and the
elaboration cycle, writing that decision well was not affordable; wiring
a skeleton conditional on an uncommitted N2 shape would be exactly the
premature commitment the pause was protecting against.

**Remaining tower (updated):**

1. `LR.CoherentIotaLeafStep Γ₀` (new, hard): the chain fold against the
   received seeds — this is where the G4 rung audit resolves (interior
   retyping depths vs the rung index).
2. `LR.ConstDefnLocalStep Γ₀` (new, medium): the local-seed budget for
   definitional values, routes (a)/(b) above.
3. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4588, unchanged; medium once N2 is
   stated in prose): ordered spine→`FixedHeadTelescope` producer over the
   in-file `peelLayer`.
4. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4601) from
   `CoherentSelfStep.of_leafSteps` (ADQ:6122) + item 3, then the bare
   leaf per rung via `iotaDefEq_of_ctorExactAt_natStep` (ADQ:4646) and
   the bootstrap (`contextualAdequacyAtDepth_of_iotaSteps`, ADQ:6829).

— session-C subagent 3

### The chain wall resolves as a G4 tripwire; the residual is named and wired (2026-08-15, session-C subagent 4)

Baseline at resumption: green, exit 0, zero errors, exactly one
`declaration uses sorry` at `LR.iotaWitnessStep` (6866:8 before this
session's insertions).  Reconfirmed by a full elaboration before any edit
(log `baseline`).  Final state after the landings below (log `edit1`, exit
0): zero errors, the same sole sorry warning at the same leaf statement,
moved only by insertions to ADQ:6985 (sorry token ADQ:7015).  The warning
profile is otherwise identical modulo line shifts, plus two new instances
of the file's already-accepted `unusedSectionVars` lint (56 → 58) for the
two new theorems that do not use `[Params.Semantic]`.

**Primary target `LR.CoherentIotaLeafStep Γ₀` (ADQ:5884): obstruction, not
a landing.  The rung audit fires the G4 tripwire.**  Per the standing
instruction the discharge line was stopped rather than patched, and the
residual was factored, named, and given both a producer and a consumer so
that it is a checkable object rather than a narrative.

#### The rung audit — the depth arithmetic, spelled out

The journaled recipe survives its first three steps and dies at the fourth.
Splitting the joint `RecursorIotaPattern` match and normalizing the major's
free closure through `LRS.CtorDefEq.toChain` (SLR:11390) are available.
More importantly, **every per-link consumer is inversion-free**: neither
`LRS.iotaDefEq_of_ctorExactAt_coherent` (ADQ:4751) nor the synchronized
rectangle `LRS.iotaDefEqRect_of_ctorExactAt` (ADQ:2887) takes a uniqueness,
inversion, or subject-reduction premise, and `LogRel.DefEqRect.trans`
(SLR:9960) composes shared-middle rectangles with pure logical-relation
transitivity.  So the *entire* residual is the fold that carries the
rectangle along the normalized chain.

That fold spends exactly two facts, and both are unbounded:

1. **Interior-vertex retyping.**  `LRS.CtorPath.foldRaw` (SLR:11072) calls
   `uniq hXY.hasType.1 hX` once per link, where `hXY : IsDefEq Γ₀ X Y
   A_link` is the link's own result type from `CtorExact.rawDefEq`
   (SLR:10937) and `hX : IsDefEq Γ₀ X X D` anchors the vertex at the
   recursor's major domain `D = pair.domain`.  `uniq : LogRel.RawTypeUniq
   Γ₀` (SLR:10446) has exactly one producer in the tree,
   `IsDefEq.uniq_of_stratified_inversion` (ADQ:646), whose induction is on
   `max n₁ n₂` for the two *existentially obtained* stratification depths
   of the vertex (`(h.strong hΓ).stratify`, ADQ:276-277, inside `uniqPath_of_stratified_inversion`) and which consumes
   the **unbounded** `JointStratifiedInversion`.  That package's only
   producer is `JointStratifiedInversion.of_adequacy` (ADQ:594) from
   `LR.ContextualAdequacyAt 1` — full level-one adequacy at *every* depth.
   At rung `d` the leaf holds only `∀ d' < d, ContextualAdequacyAtDepth d'`.
2. **Root subject reduction.**  `LRS.CtorChain.foldRaw`'s two root
   callbacks (SLR:11185) must move each major to its classified constructor
   spine at `D`; the only producer is
   `WHRedS.defeq_of_stratified_inversion` (ADQ:841), which internally
   spends `uniq_of_stratified_inversion` again at the reducing term's own
   depth.  Same unbounded package.

**Why no certificate reachable at the leaf bounds the depth in (1).**  Three
candidate bounds were checked and all fail, for three different reasons:

- *The rung index `d`.*  The bootstrap deliberately does not hand the
  produced rung's own certificate to the leaf (`_hstrat` at ADQ:6955; the
  docstring at ADQ:6943-6947 states why: the derivation induction is
  depth-blind, so a left-endpoint certificate cannot bound the leaf
  instances reached through `trans` or evaluator descent).  This is
  subagent 2's honesty note and it is load-bearing here.
- *The registered-rule certificates `rhsStratified` / `headStratified`
  (SLR:9280-9285).*  These are the ones the 2026-08-14 audit nominated, and
  they are the wrong side of the redex.  They bound the *contractum* — the
  applied RHS and its peeled fixed head, the latter exactly
  `capturePaths.length` shallower.  The chain lives on the **major**, i.e.
  the redex's inspected argument.  No arithmetic connects them.
- *The redex's own stratification, hypothetically granted.*  This is the
  decisive one.  Even if the leaf were handed
  `HasTypeStratifiedS Δ (rec … major) B core D`, `HasTypeStratifiedS.app`
  (SExpr:2388) would bound only the two **endpoint** majors at `D - 1`.  The
  chain's *interior* vertices are the middle terms of `LRS.CtorDefEq.trans`
  (SLR:10712), which relates `M ≡ N` and `N ≡ P` while retaining nothing
  whatsoever about `N` — no typing, no shape, no certificate.  An interior
  vertex is an arbitrary term of the ambient theory whose stratified depth
  is not a function of the endpoints' depths at all.  **This is the exact
  failing vertex.**

So the demand is not "inversion at some depth `< d`" that we failed to
arrange; it is "inversion at a depth that no premise in scope names".  There
is no depth arithmetic that makes it strictly-predecessor, and manufacturing
the package inside the proof would be precisely the same-rung
self-consumption G4 forbids.  Extending `CoherentIotaLeafStep`'s inputs with
the strict-predecessor contextual family therefore does **not** help, which
is why the sanctioned "extend the Prop, there is one call site" escape hatch
was not taken.

**The repair that would close it is not local, and it is not in this
session's territory.**  The erasure-north-star fix is to stop erasing the
middle vertex: index `LRS.CtorDefEq`/`CtorLink`/`CtorPath`/`CtorChain` by
the raw domain and have `trans` retain `IsDefEq Γ N N D`, after which
`CtorPath.foldRaw` needs no `uniq` at all.  That is a ShapeLogRel.lean
change and it was **not** attempted; more importantly it does not stay
local: `LRS.CtorDefEq` is consumed through `LRS.IndDefEq` (SLR:11544), whose
`trans` (SLR:11560) is the `trans` field of the `LogRel` record (SLR:9927),
and `LogRel` carries **no** raw-typing projection at all — `DefEq M N A m a`
does not imply `IsDefEq Γ M N A`.  So a strengthened `CtorDefEq.trans` would
make `IndDefEq.trans` underivable unless the logical relation itself is
given a soundness field, and that field's own `whr`/`unwhr` closure
conditions (SLR:9937) are subject reduction, i.e. the inversion package
again.  **Exact needed change, for the record:** either (i) `LRS.CtorDefEq`
gains a raw domain index with `trans` retaining the middle vertex's
self-typing *and* `LogRel` gains a raw-soundness field discharging
`IndDefEq.trans`'s new premise, or (ii) an environment-level discipline on
constructor result types (each constructor's instantiated result type is
determined by the constructor and its arguments) replaces general raw
uniqueness at exactly these vertices.  Route (ii) is the cheaper-looking one
and is untouched research.

**A second, independent blocker in the same fold, for whoever resumes.**  It
is mechanical, not circular, and it was not visible in the journaled recipe.
`CtorChain.RawAlgebra.exact` hands over a *framed* native leaf: `CtorFrame
Γ₀ (LR Γ₀) m J p` plus `CtorExact Γ₀ J X Y p` at the leaf's own level `k`
and shape `p`.  `iotaDefEqRect_of_ctorExactAt` pins the leaf's level to the
ambient recursor level (`out`/`outTy : WShape (nI+1)` are fixed by the
goal), and `CtorExact` has **no** level transport by design — its only
lemmas are `toCtorDefEq`, `symm`, `rawDefEq` (SLR:10912-10945), because
frames exist precisely to keep transports outside the native leaf
(SLR:10858-10861).  So the fold must run the iota *natively* at level `k`
and transport the finished rectangle back through the frame.  The parts for
that exist: `LE_Interp.Matches.lift`/`.unlift` (SLR:5287/5416) move the
match, `LE_Interp.RHS` is level-erased (`TShape`-valued) and needs no
transport at all, and `LogRel.LiftEquiv.rect` (SLR:10783) is exactly the
rectangle's transport iff.  Budget this as a real second layer.

#### Landed (kernel-checked; no new sorries)

- `LR.MajorChainFoldStep Γ₀` (ADQ:960): the named residual of the
  normalized-chain fold, as a two-field structure — `uniq :
  LogRel.RawTypeUniq Γ₀` and `subjectRed : WHRedS Γ₀ e₁ e₂ → IsDefEq Γ₀ e₁
  e₁ A → IsDefEq Γ₀ e₁ e₂ A`.  Stated as two separate fields rather than
  bundled as `JointStratifiedInversion` on purpose: a future producer may
  reach either half by other means (route (ii) above reaches the first
  without the second), and the fold consumes nothing else.
- `LR.MajorChainFoldStep.of_stratifiedInversion` (ADQ:972): the completed
  inversion package supplies both fields.  This certifies that the two
  named facts are *precisely* what the existing
  `foldRaw_of_stratifiedInversion` consumer spends — nothing else is hidden
  in the package, so the factorization is faithful rather than convenient.
- `LRS.CtorDefEq.foldRaw_of_majorChainFoldStep` (ADQ:981): the consumer.
  The free constructor-observation closure folds from the named residual
  alone, with no well-formedness hypothesis and no inversion package in
  sight.  The Prop is therefore both produced and consumed in-file, not a
  dangling definition.
- `LR.ConstDefnDeepStep Γ₀` (ADQ:5941) and
  `LR.ConstDefnLocalStep.of_deepStep` (ADQ:5957): the secondary target's
  reduction (below).
- `LR.CoherentSelfStep.of_leafStepsDeep` (ADQ:6241): the same assembly as
  `of_leafSteps` (ADQ:6229) against the strictly smaller definitional
  obligation, so the new Prop reaches the top-level composition.
- Docstring on `LR.CoherentIotaLeafStep` (ADQ:5884) now records the audit
  status inline, so the next reader of the Prop does not re-derive it.

#### Secondary target `LR.ConstDefnLocalStep` (ADQ:5912): route (b) refuted, obligation strictly reduced

Route (b) — "closed registered values admit depth-extension of local
coherent results directly" — is **not** provable from closedness, and the
reason is structural rather than a missing lemma.  `LR.SelfAdequateAt`
(ADQ:3796) mentions its depth index in exactly one place, the stratified
certificate it *consumes*; its conclusion `LR.Adequate …` is depth-free.
Since `HasTypeStratifiedS.mono` (SExpr:2414) raises a certificate to any
larger index, `SelfAdequateAt` is *stronger* at larger depth, and a local
seed at index `depth` already discharges every `depth' ≤ depth` with no
hypothesis at all.  All residual content is the strictly deeper case — and
closedness of the value says nothing about it: `value.Closed` constrains
substitution (`closed.mkInstS.subst_eq`), not stratification depth.

The real content of that residual is worth stating plainly, because it is
the same family of finding as the chain wall: **the stratified-depth measure
does not decrease along δ-unfolding.**  The stratified `const` rule
(SExpr:2383-2387) certifies only `SExpr.mkInst ls ci.type`; a definitional
value is routinely far deeper than its declared type (`def foo : Nat := ⟨big
term⟩`), so no environment-independent inequality can bound the value's
depth by the constant's.  The old derivation induction handled this because
`Params.Semantic.defn`'s equality is a *subderivation*; the witness-tree
remake replaced derivation induction with a Nat recursion whose index simply
does not travel across δ.  Note the call site is not rescued by the easy
half either: it obtains `nV` from `hdefΓ.stratify` (ADQ:6212), and
`.mono` lets that be taken arbitrarily large, so the `≤` half never applies
there.  Route (a) — couple the budget to the seed at its creation point, as
`CoherentRhsSeedAt` (ADQ:3976) already models one level up, with the budget
derived from the *value's* certificate rather than the constant's — remains
the only route, and it must be a producer-side change.  Deliberately not
implemented (two-strikes; wide transport ripple), exactly as the predecessor
scoped it.

What landed is the honest reduction: `ConstDefnLocalStep.of_deepStep`
(ADQ:5957) proves the whole `depth' ≤ depth` half unconditionally by
`HasTypeStratifiedS.mono`, spending **no** adequacy content — it is pure
depth arithmetic — leaving `ConstDefnDeepStep` (ADQ:5941) as a strictly
smaller obligation stated only for `depth < depth'`.

#### N2 capture-domain interface decision (prose, per the two-strikes rule)

The one open design decision, stated before any Lean, as required.  The
2026-08-14 N2 entry already ruled out pointwise widening of
`CaptureDefEqAligned` and adopted the joint two-telescope route, which is
landed as `LR.FixedHeadTelescope` (ADQ:1775) with `nil`/`cons`
(ADQ:1839/1854) and the N1 layer core `WShape.HasTypeLam.peelLayer`
(ADQ:1797).  What was left open is narrower and is the actual N2 question:
the telescope *synthesizes* its head-type observation from the captures
(`cons` builds `forallE tyDom tyFun` with `tyDom := capture`'s own
`typeShape`), while `LR.FixedHeadResultAt` (ADQ:2148) must consume a head
that observes the **registered** type `SExpr.mkInst recLs rule.df.type`.
Something must link the two.  The alternatives:

- **(i) Widened threading.**  Add the probe's `probeB.LowerSyncAt`
  (plans/probes/probeB-2.lean:63) to the tower's per-witness invariant: on
  demand from `head ≤ root`, a stratified certificate and `Fits`, it yields
  `∃ headElem headTy, headElem ≤ head ∧ headElem.HasType headTy ∧ Nonempty
  (Witness ρ headTy B)`, instantiated at `B :=` the registered type.  Its
  threading through the unary recursor is PROVED
  (`probeB.widenedThreading`).
- **(ii) State the link on the consumer's premise.**  Replace
  `FixedHeadResultAt`'s third premise — today the context-free fallback
  `(∃ headElem headTy, headElem ≤ head ∧ headElem.HasType headTy)`,
  ADQ:2171-2172 — by the ordered telescope itself together with
  `Nonempty (Witness ρ headTy (SExpr.mkInst recLs rule.df.type))` stated at
  the **telescope's own** `headTy` index.

**Decision: (ii).**  The argument is the eight-failure erasure pattern, and
it is decisive.  Option (i)'s conclusion is a *fresh* existential: the
invariant chooses some `headElem`/`headTy` pair, while the telescope has
already chosen the pair that every layer's `AtShapes` is indexed by.  Two
independently chosen shape pairs for the same head, with a reconciliation
obligation between them, is erasure #7 recurring one level up — the very
shape the 2026-08-14 entry rejected when it refused a standalone per-path
field ("a standalone field for each path cannot certify that its alleged
domain is the domain selected by the *same* registered-type observation").
Wrapping the semantic component in `Nonempty` makes it worse, not better:
the consumer receives a witness it provably cannot align with its own
telescope indices.  Option (ii) creates no reconciliation obligation at all,
because there is only ever one pair per layer, chosen once, and the
registered-type witness is attached to that same index.  This is also
verbatim what the 2026-08-14 decision already prescribed for the completed
certificate ("`FixedHeadResultAt` will consume that synchronized endpoint …
the current context-free `typedLowerHead` input remains useful only as the
shape fallback and must not be used to manufacture the final witness"), so
(ii) is continuation rather than a new commitment.

Note also that `widenedThreading` being PROVED argues only that the widening
is *possible*; it was recorded in the 2026-08-14 synthesis under "verified
non-risks", i.e. as evidence that adopting it would not break the recursion —
not as evidence that it should be adopted.

**Consequence, and why `CoherentFixedHeadStep` (ADQ:4642) was not attempted
after the decision.**  Decision (ii) is an interface change to
`FixedHeadResultAt`/`FixedHeadResult` (ADQ:2101/2148) with an enumerable but
real ripple — `iotaDefEq_of_ctorExactAt_fixedHead`, `_closedFixedHead`,
`_coherent`, `FixedHeadResult.mono`, `FixedHeadResult.of_forall_at`, and the
`CoherentRetainedResult.fixedHead` projection.  Landing the premise change
and the ordered producer in one session, after the audit and its elaboration
cycles, would have put the green state at risk for a partial result; wiring
a skeleton against an unchanged premise would bake in the fallback the
decision just rejected.  The next session should land the premise change
first, as its own green step, and only then build the producer at the
`constDefEq`/`Matches` materialization boundary where the registered-type
evidence is still in scope.

#### Remaining tower (updated)

1. `LR.MajorChainFoldStep Γ₀` (ADQ:960, NEW, blocked): the chain wall,
   reduced to two named raw facts.  Not reachable from any adequacy rung;
   see the audit above.  Next moves are the two repairs named there, both
   outside `ShapeLogRelAdequacy.lean` — (i) retain the middle vertex in
   `LRS.CtorDefEq` plus a `LogRel` soundness field, or (ii) an
   environment-level constructor-result-type discipline.  Recommend
   scoping (ii) first: it is local to the vertices that actually occur.
2. `LR.CoherentIotaLeafStep Γ₀` (ADQ:5884, still unproved): now known to
   reduce to item 1 plus the mechanical multi-level frame layer.  Do not
   re-attempt before item 1 has an answer.
3. `LR.ConstDefnDeepStep Γ₀` (ADQ:5941, NEW, strictly smaller than the
   retired-in-half `ConstDefnLocalStep`): the δ-unfold depth budget.  Route
   (a), producer-side, with the budget taken from the value's own
   certificate.
4. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4642, unchanged): N2 is now decided
   (option (ii) above).  Land the `FixedHeadResultAt` premise change first,
   then the ordered producer over `peelLayer` (ADQ:1797).
5. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4655) from
   `CoherentSelfStep.of_leafStepsDeep` (ADQ:6241) + item 4, then the bare
   leaf per rung via `iotaDefEq_of_ctorExactAt_natStep` and the bootstrap
   `contextualAdequacyAtDepth_of_iotaSteps` (ADQ:6948).

One structural observation worth carrying forward, since items 1 and 3 are
the same finding twice: the stratified-depth measure decreases along
syntax-directed typing but **not** along the two moves the joint leaf
actually needs — δ-unfolding (item 3) and free-closure transitivity on
constructor observations (item 1).  A depth-indexed fixpoint cannot by
itself reach either.  Both residuals are now named, so the next design pass
can be about those two moves specifically rather than about the fixpoint.

— session-C subagent 4

### Chain-wall repair: the reconciliation moves to the constructor observation (2026-08-15, session-C subagent 5)

Written before any Lean, as the prose-first rule requires.  The task was to
discharge `LR.MajorChainFoldStep` (ADQ:960) by a structural change.  Below is
the route comparison, the choice, and — because it is the part that decides —
what the choice does *not* buy.

#### What the fold actually spends, restated exactly

`LRS.CtorPath.foldRaw` (SLR:11072) does not use `uniq` to type the middle
term of a `trans`.  It uses it, once per link, to reconcile **two independent
type observations of the link's left vertex**: the link's own natural result
type `A` (from `CtorExact`'s retained `hspine : SpineWF Γ CHead args.reverse
A`, surfaced by `CtorExact.rawDefEq`, SLR:10937) against the running anchor
`D` threaded from the root.  For the first link the anchor is the recursor's
major domain; for every later link it is `hXYD.hasType.2`, i.e. the anchor
*transported by the previous link*.  So the residual is not "type the middle
vertex" — the middle vertex is already typed at `D` by construction once the
previous link has been retyped.  The residual is: **the link's own result
type and the inherited anchor are two derivations that must be identified.**

This restatement is what separates the two candidate routes, and it kills one
of them outright.

#### (R1) Retain the middle vertex — refuted, twice, and for a new reason

The predecessor's R1 was "index `CtorDefEq` by the raw domain and have `trans`
retain `IsDefEq Γ N N D`".  Two findings:

- *The blocker the predecessor named is not fatal.*  The audit said a raw
  component on `CtorDefEq`/`IndDefEq` cannot survive `whr`/`unwhr`, because
  those closure conditions would become subject reduction.  That is true for a
  component stated about `M` and `N` — but **not** for one stated about their
  classified spines.  `LRS.CtorView.whr`/`.unwhr` (SLR:10955/10963) move a
  view across a weak-head reduction in *both* directions using only
  `WHRedS.determ_l … .ctorSpine`, i.e. weak-head determinism at classified
  constructor spines.  A component of the form `∀ X, CtorView Γ M X → P X` is
  therefore exactly whr-invariant with no subject reduction at all.  Recorded
  because it is a reusable fact: the whr regress the audit feared is avoidable,
  and any future raw component on the ctor branch of the relation should be
  stated on views rather than on roots.
- *R1 nevertheless fails, one level down.*  Even with whr survived, a
  D-indexed `CtorDefEq` must produce `IsDefEq Γ X Y D` at its `exact`
  constructor for the externally chosen `D`, and there the leaf has only its
  own `A`.  The reconciliation is not removed; it is relocated to the leaf
  **and simultaneously made harder**, because `LogRel.conv` (SLR:9930) changes
  the raw type index `A` of `IndDefEq` using only `LRS.TyDefEq`, which at
  `.indTy` is `IndTyHead Γ A ∧ IndTyHead Γ B` (SLR:11629) and carries *no* raw
  type equality.  A raw component pinned to `IndDefEq`'s own `A` is destroyed
  by `conv`.  So R1 must in any case be stated anchor-*polymorphically*, at
  which point it is R2 with extra indices.  Two strikes; R1 abandoned.

#### (R2) Constructor-result-type discipline — chosen, in the form below

The chosen shape, and the reason it is the right one, is that it makes the
reconciliation *anchor-polymorphic and leaf-local*:

- `LRS.CtorRetype Γ X Y`: a two-field **transport**, `∀ D, IsDefEq Γ X X D →
  IsDefEq Γ X Y D` and its right-hand mirror.  Not an existential, not a sort
  equality: it is the retyping *action* the fold performs, retained as data.
- `LRS.CtorAnchorDisciplineAt Γ IH m`: that transport is available for every
  framed native leaf of the root observation, with the frame and the leaf both
  in hand — exactly the signature `CtorPath.RawAlgebra.exact` (SLR:11064)
  already receives, so the discipline is scoped to the leaves that actually
  occur under the root shape rather than to the whole environment.
- `LRS.CtorSpineTypeUniqPath Γ`: the environment-level statement the
  discipline reduces to — *the declared result type of a registered
  constructor determines the type of its applications*, path-valued.

Every closure operation of the chain machinery is then free of new premises:
`foldRaw`'s per-link `uniq` call is replaced by the leaf's own transport, and
`trans` needs nothing, because after the first link the anchor travels with the
term.

**Why this survives the eight-failure erasure pattern.**  The north star is
retain more; proof-relevant, positional, replayable; never truncate to
Prop/existence what a consumer needs.  Judged against it:

1. *Proof-relevant rather than existential.*  `RawTypeUniq`'s conclusion is
   `∃ u, IsDefEq Γ A B (.sort u)` — the consumer must then pick `u` and
   `defeqDF` by hand, and every call site re-chooses.  `CtorRetype` hands over
   the transport itself, already applied to the right endpoint.  Nothing is
   existentially quantified that a consumer must re-align.
2. *Positional.*  The discipline is indexed by the *frame and leaf* of the
   observation it serves, so a consumer cannot accidentally satisfy it with a
   retyping of some other constructor spine.  This is the same discipline the
   2026-08-14 N2 entry enforced when it refused a standalone per-path field:
   one pair per position, chosen once.
3. *Path-valued, so no premature collapse.*  `CtorSpineTypeUniqPath` returns
   `TypeDefEqPath` (SLR:10121), not a single conversion.  `TypeDefEqPath`
   exists precisely because adjacent type equalities may assign different
   universes, and `TypeDefEqPath.collapse` (SLR:10460) charges *the whole of
   raw type uniqueness* for the collapse.  Since the fold only ever transports
   term equalities (`TypeDefEqPath.defeqDF`, SLR:10157), collapsing first
   would be erasure #2 — throwing away the sequence a consumer never needed
   flattened.  The reduction therefore never asks for it.
4. *Additive.*  `CtorDefEq`, `CtorExact`, `IndDefEq` and `LogRel` are not
   touched; the anchored fold lands beside the existing one.  No consumer of
   the free relation loses anything it has today, and the old
   `foldRaw_of_majorChainFoldStep` stays green as the reference consumer.

**What the choice does not buy, stated plainly so the next session does not
rediscover it.**  It does **not** make the residual reachable from a strict
predecessor adequacy rung.  Interior vertices are still classified constructor
spines of unbounded stratified depth, and *any* identification of two type
observations of the same term must invert at least one of the two derivations:
`HasTypeStratifiedS.app_inv` (SExpr:2613) walks a spine, but reconciling the
two codomains at each application step is Pi inversion at that vertex's own
depth.  There is no reformulation of the fold that escapes this — the two
types genuinely originate in two independent derivations, so the repair must
remove the *independence*, and the only place independence can be removed is
the producer of constructor observations, where the constructor's declared
type is available and there is exactly one of it.

That is the whole content of the choice: the obligation is moved **out of the
depth-indexed fixpoint** and onto the environment, where it has no depth index
to be blocked on.  `MajorChainFoldStep` demanded `LogRel.RawTypeUniq Γ₀` for
arbitrary terms plus subject reduction for arbitrary reductions; what replaces
it demands a retyping only for terms carrying a native `CtorExact` certificate,
plus subject reduction only for reductions **to a classified constructor
spine** — and the latter, per the 2026-08-15 audit's own third bullet, is the
one half a redex certificate does bound (`HasTypeStratifiedS.app`, SExpr:2388,
bounds the two endpoint majors at `D - 1`).  Removing the interior demand is
therefore what makes the endpoint bound worth having.

— session-C subagent 5 (design decision; landing recorded below)

#### Landed (kernel-checked; no new sorries; additive, zero ripple)

Baseline at resumption, reconfirmed by a full elaboration before any edit (log
`baseline-adq`, exit 0): zero errors, exactly one `declaration uses sorry` at
the `LR.iotaWitnessStep` leaf, ADQ:6985:8.  Final state after everything below:
zero errors in both edited files, `ShapeLogRel.lean` with zero sorries, the
same sole sorry warning in `ShapeLogRelAdequacy.lean` at the same leaf
statement, moved only by insertion to ADQ:7062:8.  Warning profile otherwise
identical modulo line shifts, plus two further instances of the file's already
accepted `unusedSectionVars` lint (81 → 83 file-anchored warnings) for the two
new theorems that do not use `[Params.Semantic]`.  `ShapeLogRel.lean` gained
no warnings beyond its existing profile.

In `Lean4Lean/Experimental/ShapeLogRel.lean`:

- `LRS.CtorRetype` (SLR:11112) and `.symm` (SLR:11119): the two-field retyping
  transport of one native link.
- `LRS.CtorSpineTypeUniqPath` (SLR:11135): the environment-level constructor
  result-type discipline, path-valued.
- `LRS.CtorSpineTypeUniqPath.of_rawTypeUniq` (SLR:11147): raw type uniqueness
  supplies it by a single-edge path — the faithfulness certificate that the
  new obligation is *implied by* the one it replaces.
- `LRS.CtorExact.retype_of_ctorSpineTypeUniqPath` (SLR:11161): the discipline
  retypes any native exact link.  The right-endpoint field is the interesting
  one: it applies the discipline twice at that endpoint's own spine
  certificate — once against the link's type, once against the requested
  domain — and composes the two paths.  No sort index is ever identified, so
  `TypeDefEqPath.collapse` (and with it the whole of raw type uniqueness) is
  never charged.
- `LRS.CtorAnchorDisciplineAt` (SLR:11188) with `.of_ctorSpineTypeUniqPath`
  (SLR:11194) and `.of_rawTypeUniq` (SLR:11200): the frame-scoped form the
  folds consume.
- `LRS.CtorPath.foldRaw_of_anchorDiscipline` (SLR:11210),
  `LRS.CtorPath.rawDefEqAt_of_anchorDiscipline` (SLR:11229),
  `LRS.CtorChain.foldRaw_of_anchorDiscipline` (SLR:11356),
  `LRS.CtorChain.rawDefEqAt_of_anchorDiscipline` (SLR:11374),
  `LRS.CtorDefEq.foldRaw_of_anchorDiscipline` (SLR:11625),
  `LRS.CtorDefEq.rawDefEqAt_of_anchorDiscipline` (SLR:11636): the complete
  raw-consumer surface of the chain machinery, re-landed without
  `LogRel.RawTypeUniq`.  All six have the same statements as their `uniq`-taking
  originals (SLR:11041/11072/11155/11185/11416/11428), which are untouched.

In `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean`:

- `LR.MajorChainAnchorStep Γ₀` (ADQ:1015): the repaired residual, two fields —
  `ctorRetype` (per-framed-leaf transport) and `rootRed` (subject reduction *to
  a classified constructor spine*, i.e. the two root views only).
- `LR.MajorChainAnchorStep.of_ctorSpineTypeUniqPath` (ADQ:1030): the intended
  producer, taking the environment-level discipline directly.
- `LR.MajorChainAnchorStep.of_majorChainFoldStep` (ADQ:1040): the old residual
  implies the new one, so this is a weakening and not a restatement.
- `LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep` (ADQ:1053): the consumer.
  Identical statement to `foldRaw_of_majorChainFoldStep` (ADQ:981), which stays
  green beside it as the reference consumer.
- The status paragraph of `LR.CoherentIotaLeafStep` (ADQ:5961) now records the
  repair and the surviving mechanical multi-level frame layer inline.

**Ripple: none, by construction.**  `LRS.CtorDefEq`, `LRS.CtorExact`,
`LRS.CtorLink`, `LRS.CtorPath`, `LRS.CtorChain`, `LRS.IndDefEq` and `LogRel`
are untouched — no constructor gained a premise, no structure gained a field,
so not one existing consumer changed.  Enumerated before editing: the free
relation is reached through `IndDefEq` (SLR:11544 pre-edit) which is the ctor
branch of `LR`, hence through `LogRel`'s `trans`/`whr`/`conv`; every one of
those would have been a breaking site under R1.  Landing beside the existing
fold instead of inside it avoids all of them, as the additive-first rule
prefers.  `LogRel.RawTypeUniq` still has its original consumers; nothing was
removed.

#### What `MajorChainFoldStep` now reduces to

Precisely, and with the honest limits stated:

1. **Interior of the chain: discharged outright.**  `CtorPath.foldRaw` used to
   call `uniq` once per link.  `CtorPath.foldRaw_of_anchorDiscipline` calls
   nothing: the link retypes itself and its retyped right endpoint anchors the
   tail.  The unbounded family of interior obligations is gone from the
   consumer, not renamed.
2. **Per native leaf: `LRS.CtorSpineTypeUniqPath Γ₀`.**  This is where the
   payment now sits, and it has *no depth index at all* — it has left the
   depth-indexed fixpoint.  Its subject is a registered constructor
   application with its head typing and spine certificate retained; its
   content is that a registered constructor's declared result type is the type
   of its applications.
3. **At the two roots: `rootRed`.**  Weak-head subject reduction restricted to
   reductions that land on a classified constructor spine.

**A correction to the 2026-08-15 audit's endpoint claim, since it matters for
whoever discharges item 3.**  The audit observed that a redex certificate
bounds the two endpoint majors at `D - 1` (`HasTypeStratifiedS.app`,
SExpr:2388), and that reads as though `rootRed` is therefore reachable.  It is
not, quite: `WHRedS` is the reflexive-transitive closure, and
`WHRedS.defeq_of_stratified_inversion` (ADQ:841) inducts along the sequence
taking each next step's typing from `ih.hasType.2` — an `IsDefEq` whose own
stratified depth is existential.  The redex certificate bounds the *first*
step only.  So item 3 is a well-posed *local* target — one reduction sequence
from one bounded term — but it needs a subject-reduction lemma that
re-certifies each reduct, which does not exist yet.  Worth noting that the
single-step producer's one uniqueness use in the registered-action case
(`uniq hcore.hasType action.sound.hasType.1`, ADQ:836) is on the *contractum*,
which is exactly the side `rhsStratified`/`headStratified` (SLR:9280-9285) do
bound — so for the root callbacks, unlike for the interior, the registered-rule
certificates are on the right side of the redex after all.

#### Secondary: `LR.ConstDefnDeepStep` (ADQ:6018) — not landed, and deliberately not faked

The instruction was to look for whether the primary repair also serves the
δ-unfold budget.  It does, as a *principle*, and not as a lemma; both halves
are worth recording.

The principle transfers exactly.  The call site (ADQ:6284) obtains the value's
stratification depth by `obtain ⟨nV, -, hstratV⟩ := hdefΓ.stratify` — an
existential index re-chosen at consumption time — and then needs
`SelfAdequateAt Γ₀ hV nV` while the local seed offers only `depth + 1`.  That
is the same erasure as the chain wall: an index the producer already knew is
discarded and re-chosen downstream.  The repair is the same shape too — retain
it at creation, i.e. give the local (`NatSeed` right-injection) branch on a
registered definitional edge the value's own certificate at the seed's index,
exactly as `CoherentRhsSeedAt` (ADQ:4048) already does one level up — after
which the call site consumes the retained certificate and the deep case
disappears entirely rather than being discharged.

The lemma does not transfer.  For the chain, the obligation's *subject* could
be narrowed (from arbitrary terms to certified constructor spines) and that
was enough.  Here the obligation is a universally quantified *index*
(`∀ depth', depth < depth' → SelfAdequateAt Γ₀ hV depth'`), and no leaf-local
retention weakens a quantified index — only bounding the demand does, which is
a producer-side change to the seed interface with the transport ripple the
predecessor already scoped.  Two strikes on route (b) (refuted), route (a) not
attempted.

One thing was deliberately *not* done, and the next session should not do it
either: factoring `ConstDefnDeepStep` through a "certificate lowering" Prop of
the form `HasTypeStratifiedS Δ X B core depth' → HasTypeStratifiedS Δ X B core
depth`.  That reads like the analogous narrowing but is underivable, and worse,
false in spirit: `HasTypeStratifiedS.defeq` (SExpr:2405) lets a certificate
reach an arbitrary type `B` at an arbitrary larger index, so no lowering to a
seed index chosen by an unrelated guarded restart can hold.  It would be a
hypothesis no producer could ever discharge — the exact failure mode the
2026-08-15 interface-decision section rejected for nil-restated seeds.

#### Tertiary: not attempted

Gated on the secondary being resolved, which it is not.  The N2 decision
(option (ii)) and its ~five-consumer ripple stand exactly as the previous
session left them.

#### Remaining tower (updated)

1. `LRS.CtorSpineTypeUniqPath Γ₀` (SLR:11135, NEW): the environment-level
   constructor result-type discipline.  This is the interior half of the chain
   wall, now outside the depth fixpoint.  It is the first residual in this
   development that a *generation-side* argument can attack, because its
   subject is a registered declaration rather than an arbitrary derivation.
2. `LR.MajorChainAnchorStep.rootRed` (ADQ:1015): root subject reduction to a
   classified spine.  Needs a re-certifying multi-step subject-reduction
   lemma; see the correction above for why the redex certificate alone is not
   enough and where the rule certificates *do* apply.
3. `LR.CoherentIotaLeafStep Γ₀` (ADQ:5961, unproved): items 1 + 2 plus the
   mechanical multi-level frame layer (run the rectangle natively at the
   leaf's level `k`, transport back through `LogRel.LiftEquiv.rect`,
   SLR:10783).
4. `LR.ConstDefnDeepStep Γ₀` (ADQ:6018, unproved): route (a) only, as a
   producer-side retention of the value's certificate at seed creation.
5. `LR.CoherentFixedHeadStep Γ₀` (unchanged): N2 decided; land the
   `FixedHeadResultAt` premise change first, then the ordered producer over
   `peelLayer`.
6. Assembly: `CoherentRetainedNatStep.of_steps` from
   `CoherentSelfStep.of_leafStepsDeep` + item 5, then the bare leaf per rung
   and the depth bootstrap.

`LR.MajorChainFoldStep` (ADQ:960) and its two lemmas are kept, unused by the
new path, as the reference statement of what the repair removed.

**Build note for the fixture slice:** this session changed `ShapeLogRel.lean`
and rebuilt only `Lean4Lean.Experimental.ShapeLogRel` and
`Lean4Lean.Experimental.ShapeLogRelAdequacy`.  The D0/D1/D2 fixture oleans
(`SExprParamsD0/D1/D2`) are stale by design and need a rebuild before they are
trusted again.  The change is purely additive, so no fixture source edit is
expected.

— session-C subagent 5
