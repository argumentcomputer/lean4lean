import Lean4Lean.Theory.Typing.InductivePatternWF

/-! # The block-local pattern environment assembler

`assembleEnv` builds an environment whose defeq set consists of exactly one
certified block's generated iota rules plus separately certified extension
rules over a defeq-free constant base. The exposed helpers are the ones
Church–Rosser instantiation and downstream consumers need:

* `assembleEnv_defeqs` inverts the assembled defeq set exactly: a registered
  defeq is a generated rule, an extension, or a base defeq — nothing else.
* `assembleEnv_WF` preserves ordering through the block phases and the
  extension fold, given the block's semantic package and each extension's
  well-formedness.
* `AssembledPat` is the union pattern set. The block half carries the full
  L4L-10A obligations and `pat_wf`; the extension half carries each
  certificate's own pattern payload. `CertifiedExtension.covers` records
  the match at the beta-collapsed body of a registered lambda tower, never
  at the closed tower itself. No open-environment `Params` instance is
  installed. -/

namespace Lean4Lean

namespace VExpr

/-- Remove the leading lambda tower from an expression.  This is the
syntactic point at which first-order reduction patterns are matched; a
closed lambda tower itself is deliberately not a `Pattern`. -/
def stripLams : VExpr → VExpr
  | .lam _ body => stripLams body
  | e => e

@[simp] theorem stripLams_lamN (binders : List VExpr) (body : VExpr) :
    stripLams (lamN binders body) = stripLams body := by
  induction binders with
  | nil => rfl
  | cons _ binders ih => exact ih

/-- Universe instantiation commutes with exposing the body of a lambda
tower. -/
theorem stripLams_instL (e : VExpr) (ls : List VLevel) :
    stripLams (e.instL ls) = (stripLams e).instL ls := by
  induction e with
  | lam _ _ _ ih => exact ih
  | _ => rfl

end VExpr

namespace VInductDecl

/-- One separately certified extension rule for an assembled environment:
its registered defeq, a simple pattern, and the pattern payload. Coverage is
stated at `VExpr.stripLams (df.lhs.instL ls)`, the beta-collapsed pattern
site, rather than at `df.lhs.instL ls`, which is generally a closed lambda
tower. Check obligations and the typed equality from the matched redex to
the RHS are discharged by the consumer at the reduction site and are
carried by `ParRed.extra`; this certificate does not make either fact true
by registration alone. -/
structure CertifiedExtension where
  df : VDefEq
  pat : SimplePattern
  rhs : (pat.toPattern).RHS
  check : (pat.toPattern).Check
  covers : ∀ (ls : List VLevel), ls.length = df.uvars →
    ∃ m1 m2, (pat.toPattern).Matches
      (VExpr.stripLams (df.lhs.instL ls)) m1 m2

namespace CertifiedExtension

/-- The first-order pattern exposed by the body of `quotDefEq`: five
arguments to `Quot.lift`, followed by a three-argument `Quot.mk` major. -/
def quotPattern : SimplePattern :=
  .iota ``Quot.lift 5 ``Quot.mk 3

private def quotRecPaths :=
  Pattern.varNPaths (.const ``Quot.lift) 5

private def quotCtorPaths :=
  Pattern.varNPaths (.const ``Quot.mk) 3

/-- The six arguments of the registered quotient tower: all five lift
arguments followed by the quotient representative. -/
def quotCaptureArgs : List (quotPattern.toPattern.RHS) :=
  quotRecPaths.map (fun path => .var (.inl path)) ++
    (quotCtorPaths.drop 2).map (fun path => .var (.inr path))

/-- The registered right tower applied to the captures selected by the
collapsed quotient pattern. -/
def quotRHS : quotPattern.toPattern.RHS :=
  Pattern.RHS.appN (.fixed quotDefEq.rhs (by decide)) quotCaptureArgs

/-- The constructor-side `α` and relation arguments must agree with the
corresponding `Quot.lift` arguments. -/
def quotCheck : quotPattern.toPattern.Check :=
  ((quotCtorPaths.take 2).zip (quotRecPaths.take 2)).foldr
    (fun paths rest => .defeq (.var (.inr paths.1))
      (.var (.inl paths.2)) rest) .true

/-- Exact non-lambda body of the registered quotient equation. -/
def quotLhsBody : VExpr :=
  .app
    (VExpr.appN (.const ``Quot.lift [.param 0, .param 1])
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1])
    (VExpr.appN (.const ``Quot.mk [.param 0])
      [.bvar 5, .bvar 4, .bvar 0])

theorem quotDefEq_lhsBody :
    VExpr.stripLams quotDefEq.lhs = quotLhsBody := rfl

/-- `quotDefEq` satisfies the same beta-collapsed registration contract as
generated iota rules.  This is a kernel proof of pattern coverage, not a
project axiom and not an operational equality oracle. -/
def quot : CertifiedExtension where
  df := quotDefEq
  pat := quotPattern
  rhs := quotRHS
  check := quotCheck
  covers := by
    intro ls hlen
    have hlen' : ls.length = 2 := by simpa [quotDefEq] using hlen
    have hlevels : [.param 0, .param 1].map (VLevel.inst ls) = ls :=
      VLevel.inst_map_id hlen'
    let mkLevels := [.param 0].map (VLevel.inst ls)
    have hleft : HeadConstN ``Quot.lift ls 5
        (VExpr.appN (.const ``Quot.lift ls)
          [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]) := by
      have h0 : HeadConstN ``Quot.lift ls 0 (.const ``Quot.lift ls) := .const
      simpa using h0.appN
        [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]
    have hright : HeadConstN ``Quot.mk mkLevels 3
        (VExpr.appN (.const ``Quot.mk mkLevels)
          [.bvar 5, .bvar 4, .bvar 0]) := by
      have h0 : HeadConstN ``Quot.mk mkLevels 0 (.const ``Quot.mk mkLevels) := .const
      simpa using h0.appN [.bvar 5, .bvar 4, .bvar 0]
    obtain ⟨m2, hm⟩ := RecursorIotaPattern.matches_of hleft hright
    refine ⟨ls, m2, ?_⟩
    rw [VExpr.stripLams_instL, quotDefEq_lhsBody]
    have hbody : quotLhsBody.instL ls =
        .app
          (VExpr.appN (.const ``Quot.lift ls)
            [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1])
          (VExpr.appN (.const ``Quot.mk mkLevels)
            [.bvar 5, .bvar 4, .bvar 0]) := by
      simp [quotLhsBody, VExpr.instL, VExpr.instL_appN, hlevels, mkLevels]
    rw [hbody]
    exact hm

end CertifiedExtension

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-- Every generated iota rule satisfies the beta-collapsed extension shape.
The witness is derived from the generated rule body and is independent of
the rule's semantic soundness proof (`pat_wf`). -/
def iotaExtension (hcl : gen.RuleClosure) {i : Nat}
    {constructor : NormalizedBlockCtor} (h : gen.ruleEntry i constructor) :
    CertifiedExtension where
  df := gen.rule i constructor
  pat := gen.rulePattern constructor
  rhs := gen.ruleRHS hcl h
  check := gen.ruleCheck hcl (List.mem_of_getElem? h)
  covers := by
    intro ls hlen
    obtain ⟨m2, hm⟩ := gen.ruleLhsBody_matches constructor
    have hm := hm.instL ls
    have hlevels : gen.recLevels.map (VLevel.inst ls) = ls :=
      VLevel.inst_map_id (hlen.trans (gen.rule_uvars i constructor))
    rw [hlevels] at hm
    refine ⟨ls, (fun x => (m2 x).instL ls), ?_⟩
    rw [gen.rule_lhs, VExpr.instL_lamN, VExpr.stripLams_lamN]
    have hbody : gen.ruleLhsBody constructor =
        .app (VExpr.appN
          (gen.recBase (gen.ruleFieldCount constructor) constructor.owner)
          (gen.ruleIdx constructor)) (gen.ruleCtorApp constructor) := by
      rw [ruleLhsBody, VExpr.appN_append]
      rfl
    have hstrip : VExpr.stripLams ((gen.ruleLhsBody constructor).instL ls) =
        (gen.ruleLhsBody constructor).instL ls := by
      rw [hbody]
      rfl
    rw [hstrip]
    exact hm

/-- The assembled block-local environment: dependency constants from the
base, the block's four insertion phases, and the certified extension
defeqs. -/
def assembleEnv (base : VEnv) (exts : List CertifiedExtension) :
    Option VEnv := do
  let env ← base.addInductBlockGeneration gen
  return exts.foldl (fun env ext => env.addDefEq ext.df) env

/-! ## Defeq-set inversion -/

private theorem addConst_defeqs {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') {df : VDefEq} :
    env'.defeqs df ↔ env.defeqs df := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · cases h
    exact Iff.rfl

private theorem foldlM_addConst_defeqs {α : Type _} (name : α → Name)
    (ci : α → VConstant) :
    ∀ (xs : List α) {env env' : VEnv},
      xs.foldlM (fun env x => env.addConst (name x) (ci x)) env = some env' →
      ∀ {df : VDefEq}, (env'.defeqs df ↔ env.defeqs df)
  | [], env, env', h, df => by cases h; exact Iff.rfl
  | x :: xs, env, env', h, df => by
    rw [List.foldlM_cons] at h
    rcases Option.bind_eq_some_iff.1 h with ⟨envx, hx, hrest⟩
    exact (foldlM_addConst_defeqs name ci xs hrest).trans (addConst_defeqs hx)

private theorem foldl_addDefEq_defeqs :
    ∀ (dfs : List VDefEq) (env : VEnv) (df : VDefEq),
      ((dfs.foldl VEnv.addDefEq env).defeqs df ↔ df ∈ dfs ∨ env.defeqs df)
  | [], env, df => by simp
  | d :: dfs, env, df => by
    rw [List.foldl_cons, foldl_addDefEq_defeqs dfs (env.addDefEq d) df]
    show _ ∨ (df = d ∨ _) ↔ _
    rw [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- Registered defeqs of a completed block transaction are exactly the
generated rules over the base's. -/
theorem addInductBlockGeneration_defeqs {base env₁ : VEnv}
    (hadd : base.addInductBlockGeneration gen = some env₁) (df : VDefEq) :
    env₁.defeqs df ↔ df ∈ gen.generatedRules ∨ base.defeqs df := by
  rcases VEnv.addInductBlockGeneration_trace hadd with ⟨H⟩
  rw [← H.addRules, foldl_addDefEq_defeqs]
  refine or_congr Iff.rfl ?_
  exact ((foldlM_addConst_defeqs _ _ _ H.addRecs).trans
    ((foldlM_addConst_defeqs _ _ _ H.addCtors).trans
      (foldlM_addConst_defeqs _ _ _ H.addTypes)))

/-- The assembled defeq set, inverted exactly. -/
theorem assembleEnv_defeqs {base env' : VEnv}
    {exts : List CertifiedExtension}
    (hadd : gen.assembleEnv base exts = some env') (df : VDefEq) :
    env'.defeqs df ↔
      df ∈ gen.generatedRules ∨ (∃ ext ∈ exts, df = ext.df) ∨
        base.defeqs df := by
  unfold assembleEnv at hadd
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₁, h₁, h₂⟩
  cases Option.some.inj h₂
  have hfold : ∀ (es : List CertifiedExtension) (env : VEnv),
      ((es.foldl (fun env ext => env.addDefEq ext.df) env).defeqs df ↔
        (∃ ext ∈ es, df = ext.df) ∨ env.defeqs df) := by
    intro es
    induction es with
    | nil => intro env; simp
    | cons e es ih =>
      intro env
      rw [List.foldl_cons, ih (env.addDefEq e.df)]
      show _ ∨ (df = e.df ∨ _) ↔ _
      constructor
      · rintro (⟨ext, hm, rfl⟩ | rfl | hbase)
        · exact .inl ⟨ext, .tail _ hm, rfl⟩
        · exact .inl ⟨e, .head _, rfl⟩
        · exact .inr hbase
      · rintro (⟨ext, hm, rfl⟩ | hbase)
        · rcases List.mem_cons.1 hm with rfl | hm
          · exact .inr (.inl rfl)
          · exact .inl ⟨ext, hm, rfl⟩
        · exact .inr (.inr hbase)
  rw [hfold, gen.addInductBlockGeneration_defeqs h₁]
  constructor
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)

/-- A defeq-free base makes the assembled defeq set exactly the generated
rules plus the certified extensions. -/
theorem assembleEnv_defeq_cases {base env' : VEnv}
    {exts : List CertifiedExtension}
    (hadd : gen.assembleEnv base exts = some env')
    (hbase : ∀ df, ¬base.defeqs df) {df : VDefEq}
    (hdf : env'.defeqs df) :
    df ∈ gen.generatedRules ∨ ∃ ext ∈ exts, df = ext.df := by
  rcases (gen.assembleEnv_defeqs hadd df).1 hdf with h | h | h
  · exact .inl h
  · exact .inr h
  · exact absurd h (hbase df)

/-! ## Ordering -/

/-- The assembled environment is ordered: the block transaction preserves
ordering through its four phases, and each certified extension is well
formed over the post-block environment. -/
theorem assembleEnv_WF {base : VEnv} (henv : base.Ordered)
    {blockEnv : VEnv} (hgen : gen.WF base blockEnv)
    {exts : List CertifiedExtension} {env₁ : VEnv}
    (hadd₁ : base.addInductBlockGeneration gen = some env₁)
    (hexts : ∀ ext ∈ exts, ext.df.WF env₁) :
    ∃ env', gen.assembleEnv base exts = some env' ∧ env'.Ordered := by
  refine ⟨exts.foldl (fun env ext => env.addDefEq ext.df) env₁, ?_, ?_⟩
  · unfold assembleEnv
    rw [hadd₁]
    rfl
  · have hord₁ : env₁.Ordered :=
      VEnv.addInductBlockGeneration_WF henv hgen hadd₁
    have hmap : exts.foldl (fun env ext => env.addDefEq ext.df) env₁ =
        (exts.map (·.df)).foldl VEnv.addDefEq env₁ := by
      rw [List.foldl_map]
    rw [hmap]
    exact VInductDecl.rulesFold_WF _ hord₁
      (fun df hdf => by
        rcases List.mem_map.1 hdf with ⟨ext, hm, rfl⟩
        exact hexts ext hm)

/-! ## The union pattern set -/

/-- The assembled pattern set: the block's iota patterns with their L4L-10A
payloads, plus each certified extension's pattern payload. -/
inductive AssembledPat (hcl : gen.RuleClosure)
    (exts : List CertifiedExtension) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | rule {p : Pattern} {r : p.RHS × p.Check} :
      gen.IotaPat hcl p r → AssembledPat hcl exts p r
  | ext (ext : CertifiedExtension) (hmem : ext ∈ exts) :
      AssembledPat hcl exts (ext.pat.toPattern) (ext.rhs, ext.check)

/-- `Params.pat_simple` for the assembled set. -/
theorem AssembledPat.pat_simple {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} {p : Pattern} {r : p.RHS × p.Check}
    (H : gen.AssembledPat hcl exts p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | rule h => exact h.pat_simple
  | ext ext hmem => exact ⟨ext.pat, rfl⟩

/-- Extension defeqs of the assembled set expose their pattern at the
beta-collapsed body of the registered lambda tower. -/
theorem AssembledPat.ext_covers {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} {ext : CertifiedExtension}
    (hmem : ext ∈ exts) {ls : List VLevel} (hls : ls.length = ext.df.uvars) :
    ∃ p r m1 m2, gen.AssembledPat hcl exts p r ∧
      p.Matches (VExpr.stripLams (ext.df.lhs.instL ls)) m1 m2 := by
  obtain ⟨m1, m2, hmatch⟩ := ext.covers ls hls
  exact ⟨ext.pat.toPattern, (ext.rhs, ext.check), m1, m2,
    .ext ext hmem, hmatch⟩

end BlockGenerationChecked

end VInductDecl

end Lean4Lean

/-! ## Axiom closures -/

/-- info: 'Lean4Lean.Pattern.Matches.instL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.Pattern.Matches.instL

/-- info: 'Lean4Lean.VInductDecl.CertifiedExtension.quot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.CertifiedExtension.quot

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.iotaExtension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.iotaExtension

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_defeqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_defeqs

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_WF

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.ext_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.ext_covers
