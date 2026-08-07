import Lean4Lean.Verify.Environment.ConstructorValidityMatrix
import Lean4Lean.Verify.Environment.CandidateIdentityReplay

/-!
# L4L-05 accepted constructor-validity replay

The two accepted differential fixtures retain the exact executable
normalization candidate, close it through the staged D1--D4 owner, and route
the resulting generation certificate through both the Theory transaction and
the actual-kernel-metadata environment replay.
-/

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

local instance : Inhabited VEnv := ⟨.empty⟩

private theorem exceptUnit_eq_ok_of_isOk {error : Type}
    (result : Except error Unit) (h : result.isOk = true) :
    result = .ok () := by
  cases result with
  | error error =>
      change false = true at h
      contradiction
  | ok result =>
      cases result
      rfl

private theorem normalization_eq_of_view_eq
    {source : VInductDecl} {left right : VInductDecl.Normalization source}
    (view_eq : left.view = right.view) : left = right := by
  cases left with
  | mk leftView leftShape =>
      cases right with
      | mk rightView rightShape =>
          simp only [VInductDecl.Normalization.mk.injEq] at *
          exact view_eq

private theorem stagedPreFamily_transport_raw
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {left right : AddInductive.NormalizationCandidate [kernelSource]}
    (candidate_eq : left = right)
    (input : VInductDecl.StagedNormalizationCandidatePreFamilyInput
      familyContext constructorContext env Us left source) :
    ((candidate_eq ▸ input :
      VInductDecl.StagedNormalizationCandidatePreFamilyInput
        familyContext constructorContext env Us right source)
      |>.postFamilyInput.universeInput.staged.raw) =
      input.postFamilyInput.universeInput.staged.raw := by
  cases candidate_eq
  rfl

def l4l05EmptyVEnvs : VEnvs where
  venv _ := VEnv.empty

theorem l4l05EmptyHasPrimitives : VEnv.HasPrimitives VEnv.empty := by
  apply TypeChecker.VEnv.HasPrimitives.of_avoids
  intro name membership
  rfl

theorem cvmEmptySafePrimitives :
    constructorValidityMatrixContext.env.find? name = some info →
      Kernel.Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro hfind hprimitive
  change ({} : ConstMap).find?' name = some info at hfind
  rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind

theorem cvmEmptyVEnvsWF :
    l4l05EmptyVEnvs.WF constructorValidityMatrixContext.env where
  tr := by
    intro safety
    change TrEnv' safety ({} : ConstMap) false VEnv.empty
    exact .empty
  hasPrimitives := l4l05EmptyHasPrimitives
  safePrimitives := cvmEmptySafePrimitives
  mono := fun _ => .rfl

theorem prbEmptySafePrimitives :
    propRecursiveBoundaryContext.env.find? name = some info →
      Kernel.Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro hfind hprimitive
  change ({} : ConstMap).find?' name = some info at hfind
  rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind

theorem prbEmptyVEnvsWF :
    l4l05EmptyVEnvs.WF propRecursiveBoundaryContext.env where
  tr := by
    intro safety
    change TrEnv' safety ({} : ConstMap) false VEnv.empty
    exact .empty
  hasPrimitives := l4l05EmptyHasPrimitives
  safePrimitives := prbEmptySafePrimitives
  mono := fun _ => .rfl

def cvmExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 2
    [constructorValidityMatrixKernelType] 0 false
    constructorValidityMatrixContext

theorem cvmExecutionResult_isOk : cvmExecutionResult.isOk = true := by
  native_decide

def cvmProducedExecution :
    { execution // cvmExecutionResult = .ok execution } :=
  match h : cvmExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := cvmExecutionResult_isOk
      rw [h] at hOk
      contradiction

def cvmExecution := cvmProducedExecution.val

def cvmCandidate := cvmExecution.candidate

open TypeChecker in
def cvmFamilyIdentityShape :
    CandidateExprIdentityReplay.Shaped constructorValidityMatrixContext
      constructorValidityMatrixKernelType.type 2
      (.sort (.succ (.param `u))) := by
  let aName := constructorValidityMatrixKernelType.type.bindingBody!
    |>.bindingDomain!.bindingName!
  change CandidateExprIdentityReplay.Shaped constructorValidityMatrixContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE `P
        (.forallE aName (.bvar 0) (.sort .zero) .default)
        (.sort (.succ (.param `u))) .default) .default)
    2 (.sort (.succ (.param `u)))
  let alphaContext := constructorValidityMatrixContext.pushLocalDecl
    `α .default (.sort (.succ (.param `u)))
  let alphaAnnotations := AddInductive.builtCandidateTypeAnnotations
    (Expr.sort (.succ (.param `u)))
  refine .forallE (expectedSpineLength := 1)
    constructorValidityMatrixContext `α
    (.sort (.succ (.param `u)))
    (.forallE `P
      (.forallE aName (.bvar 0) (.sort .zero) .default)
      (.sort (.succ (.param `u))) .default) .default
    (by rfl) alphaAnnotations
    (AddInductive.buildCandidateTypeAnnotations_built _) (by
      simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          (.sort (.succ (.param `u)))).symm)
    (.terminal _ _ (by rfl) rfl) ?_
  let pDomain := Expr.forallE aName
    constructorValidityMatrixContext.freshExpr
    (.sort .zero) .default
  have alphaFVarWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨alphaContext, constructorValidityMatrixContext.freshExpr,
        constructorValidityMatrixContext.freshExpr⟩ := by
    simpa [alphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        constructorValidityMatrixContext `α
        (.sort (.succ (.param `u))) .default 9999 (by rfl)
        (by
          change LocalContext.WF ⟨.empty, .empty, .empty⟩
          exact LocalContext.WF.nil)
        (by
          change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
            constructorValidityMatrixContext.freshFVarId = none
          exact TypeChecker.emptyLocalContextFindNone _)
  have pDomainShape : CandidateExprIdentityReplay.Shaped alphaContext
      pDomain 1 (.sort .zero) := by
    let aAnnotations := AddInductive.builtCandidateTypeAnnotations
      constructorValidityMatrixContext.freshExpr
    refine .forallE (expectedSpineLength := 0) alphaContext aName
      constructorValidityMatrixContext.freshExpr (.sort .zero) .default
      (by rfl) aAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            constructorValidityMatrixContext.freshExpr).symm)
      (.terminal _ _ alphaFVarWhnf rfl) ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl aName .default
          constructorValidityMatrixContext.freshExpr)
        (.sort .zero) 0 (.sort .zero) :=
      .terminal _ _ (by rfl) rfl
    simpa [aAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      AddInductive.Context.freshExpr,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  have alphaBody : CandidateExprIdentityReplay.Shaped alphaContext
      (.forallE `P pDomain (.sort (.succ (.param `u))) .default)
      1 (.sort (.succ (.param `u))) := by
    let pAnnotations := AddInductive.builtCandidateTypeAnnotations pDomain
    refine .forallE (expectedSpineLength := 0) alphaContext `P pDomain
      (.sort (.succ (.param `u))) .default (by rfl) pAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [pDomain, AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            pDomain).symm)
      pDomainShape.replay ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl `P .default pDomain)
        (.sort (.succ (.param `u))) 0
        (.sort (.succ (.param `u))) :=
      .terminal _ _ (by rfl) rfl
    simpa [pAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  simpa [alphaContext, alphaAnnotations, pDomain,
    AddInductive.builtCandidateTypeAnnotations,
    AddInductive.CandidateTypeAnnotationTrace.build,
    Expr.instantiate1_eq, Expr.instantiate1'] using alphaBody

def cvmFamilyIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay
      constructorValidityMatrixContext
      constructorValidityMatrixKernelType.type :=
  cvmFamilyIdentityShape.replay

theorem cvmFamilyCandidateBuild :
    AddInductive.buildCandidateExpr constructorValidityMatrixKernelType.type
        constructorValidityMatrixContext =
      .ok cvmCandidate.families.singleton.familyType.type := by
  have produced := cvmExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.familyTypes.candidates] at produced
  rw [← cvmExecution.families.produced.singleton_familyType] at produced
  have exactProduced : AddInductive.CandidateFamilyTypeListProduced
      constructorValidityMatrixContext
      (.cons cvmCandidate.families.singleton.familyType .nil) := by
    simpa [cvmCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      constructorValidityMatrixContext] using produced
  exact exactProduced.singleton_build

def cvmFamilyIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      cvmFamilyIdentityReplay
      cvmCandidate.families.singleton.familyType.type.trace :=
  cvmFamilyIdentityReplay.evidence_of_build cvmFamilyCandidateBuild

theorem cvmFamilyIdentityReplay_shape :
    cvmFamilyIdentityReplay.spineLength = 2 ∧
      cvmFamilyIdentityReplay.terminalSource =
        .sort (.succ (.param `u)) :=
  ⟨cvmFamilyIdentityShape.spineLength_eq,
    cvmFamilyIdentityShape.terminalSource_eq⟩

theorem cvmFamilyValidationAnnotations :
    cvmCandidate.families.singleton.familyType.type.trace
      |>.validationAnnotations := by
  have h := cvmExecution.familyTypes.produced
    |>.singleton_validationAnnotations
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate] using h

private theorem cvmFamilyData_hasExprMVar_false :
    constructorValidityMatrixInfo.type.data.hasExprMVar = false := by
  change constructorValidityMatrixInfo.type.hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem cvmFamilyData_hasLevelMVar_false :
    constructorValidityMatrixInfo.type.data.hasLevelMVar = false := by
  change constructorValidityMatrixInfo.type.hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [constructorValidityMatrixInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.hasLevelMVar',
    Level.hasMVar_eq, Level.hasMVar']

private theorem cvmFamilyData_hasFVar_false :
    constructorValidityMatrixInfo.type.data.hasFVar = false := by
  change constructorValidityMatrixInfo.type.hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem cvmFamily_hasMVar_false :
    constructorValidityMatrixInfo.type.hasMVar = false := by
  change (constructorValidityMatrixInfo.type.data.hasExprMVar ||
    constructorValidityMatrixInfo.type.data.hasLevelMVar) = false
  rw [cvmFamilyData_hasExprMVar_false,
    cvmFamilyData_hasLevelMVar_false]
  rfl

private theorem cvmFamily_hasFVar_false :
    constructorValidityMatrixInfo.type.hasFVar = false :=
  cvmFamilyData_hasFVar_false

theorem cvmFamilyClosed :
    cvmCandidate.families.singleton.familyType.type.context.env.checkNoMVarNoFVar
        constructorValidityMatrixKernelType.name
        constructorValidityMatrixKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show constructorValidityMatrixKernelType.type.hasMVar = false by
    simpa [constructorValidityMatrixKernelType] using
      cvmFamily_hasMVar_false]
  rw [show constructorValidityMatrixKernelType.type.hasFVar = false by
    simpa [constructorValidityMatrixKernelType] using
      cvmFamily_hasFVar_false]
  rfl

theorem cvmFamilyEnsureSort :
    TypeChecker.M.run
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.safety
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.fuel
        (TypeChecker.ensureSort (.sort (.succ (.param `u)))) =
      .ok (.sort (.succ (.param `u))) := by
  rfl

theorem cvmFamilySpineCount :
    2 ≤ cvmCandidate.families.singleton.familyType.type.trace.spineLength := by
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]
  decide

theorem cvmFamilySpineFuel :
    cvmCandidate.families.singleton.familyType.type.trace.spineLength <
      cvmCandidate.families.singleton.familyType.type.context.fuel.inductiveFuel := by
  have contextFuel := congrArg (fun context : AddInductive.Context =>
      context.fuel.inductiveFuel)
    (AddInductive.CandidateExpr.context_eq_of_build cvmFamilyCandidateBuild)
  rw [contextFuel]
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]
  decide

def cvmFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      constructorValidityMatrixKernelType
      cvmCandidate.families.singleton.familyType.type.trace where
  nparams := 2
  resultLevel := .succ (.param `u)
  stats :=
    cvmCandidate.families.singleton.familyType.type.trace
      |>.singletonCandidateInductiveStats
        constructorValidityMatrixKernelType 2 (.succ (.param `u))
  stats_eq := rfl
  terminal_eq := cvmFamilyIdentityEvidence.terminalResult_eq.trans
    cvmFamilyIdentityReplay_shape.2
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      constructorValidityMatrixKernelType
      cvmCandidate.families.singleton.familyType.type.trace
      2 (.succ (.param `u)) k
      cvmFamilyClosed cvmFamilySpineCount cvmFamilySpineFuel
      cvmFamilyValidationAnnotations
      (cvmFamilyIdentityEvidence.terminalResult_eq.trans
        cvmFamilyIdentityReplay_shape.2)
      cvmFamilyEnsureSort

theorem cvmFamilyContext_eq :
    cvmCandidate.families.singleton.familyType.type.context =
      constructorValidityMatrixContext := by
  have h := cvmExecution.familyTypes.produced.singleton_context_eq
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    constructorValidityMatrixContext] using h

theorem cvmFamilyNparams_eq : cvmFamilyValidationRun.nparams = 2 := by
  rfl

theorem cvmFamilyValidationRun_exact : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 2 #[constructorValidityMatrixKernelType]
        k constructorValidityMatrixContext =
      k cvmFamilyValidationRun.stats
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext := by
  intro alpha k
  simpa only [cvmFamilyNparams_eq, cvmFamilyContext_eq] using
    cvmFamilyValidationRun.run k

theorem cvmAfterValidationRun :
    AddInductive.buildNormalizationCandidateExecutionAfterValidation 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext cvmFamilyValidationRun.stats
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok cvmExecution := by
  have h := cvmProducedExecution.property
  change AddInductive.buildNormalizationCandidateExecution 2
      [constructorValidityMatrixKernelType] 0 false
      constructorValidityMatrixContext = .ok cvmExecution at h
  unfold AddInductive.buildNormalizationCandidateExecution at h
  rw [cvmFamilyValidationRun_exact] at h
  exact h

theorem cvmExecutionStats_eq :
    cvmExecution.stats = cvmFamilyValidationRun.stats :=
  (cvmExecution.fields_of_afterValidation cvmFamilyValidationRun.stats
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext
    cvmAfterValidationRun).1

theorem cvmExecutionValidationContext_eq :
    cvmExecution.validationContext =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext :=
  (cvmExecution.fields_of_afterValidation cvmFamilyValidationRun.stats
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext
    cvmAfterValidationRun).2

theorem cvmExecutionValidationRun : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 2 #[constructorValidityMatrixKernelType]
        k constructorValidityMatrixContext =
      k cvmExecution.stats cvmExecution.validationContext := by
  intro alpha k
  rw [cvmFamilyValidationRun_exact, cvmExecutionStats_eq,
    cvmExecutionValidationContext_eq]

theorem cvmCandidate_produced :
    AddInductive.buildNormalizationCandidate 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext = .ok cvmCandidate :=
  cvmExecution.produces cvmExecutionValidationRun

def cvmFamilyContext : AddInductive.Context :=
  { constructorValidityMatrixContext with lctx := {} }

def cvmConstructorContext : AddInductive.Context :=
  { constructorValidityMatrixContext with
    env := cvmExecution.familyEnv, lctx := {} }

theorem cvmFamilyCandidateContext_eq :
    cvmCandidate.families.singleton.familyType.type.context =
      cvmFamilyContext := by
  simpa [cvmFamilyContext, constructorValidityMatrixContext] using
    cvmFamilyContext_eq

theorem cvmConstructorCandidateContext_eq :
    cvmCandidate.families.singleton.constructors.singleton.type.context =
      cvmConstructorContext := by
  have h := cvmExecution.families.produced.singleton_constructors
    |>.singleton_context_eq
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    cvmConstructorContext] using h

theorem cvmFamilyPrefix_ne :
    cvmFamilyContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def cvmFamilyContextRun :
    TypeChecker.CandidateContextRun cvmFamilyContext :=
  TypeChecker.CandidateContextRun.root cvmEmptyVEnvsWF rfl
    cvmFamilyPrefix_ne

def cvmPreFamilyStage :
    TypeChecker.CandidateSemanticStage cvmFamilyContext VEnv.empty [`u] where
  contextRun := cvmFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem cvmRawFamily_isType :
    VEnv.empty.IsType 1 [] constructorValidityMatrixType.type := by
  change VEnv.empty.IsType 1 []
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.forallE (.bvar 0) (.sort .zero))
        (.sort (.succ (.param 0)))))
  apply VEnv.IsType.forallE
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · apply VEnv.IsType.forallE
    · apply VEnv.IsType.forallE
      · exact ⟨_, by type_tac⟩
      · exact ⟨_, VEnv.HasType.sort (by decide)⟩
    · exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem cvmFamilySource_tr :
    TrExprS VEnv.empty [`u] [] constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type := by
  have shape : TrTypeExpr VEnv.empty [`u] []
      constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := cvmRawFamily_isType
  exact shape.to_trExprS .empty trivial ⟨.sort level, type⟩

theorem cvmStatsNindices_eq :
    cvmFamilyValidationRun.stats.nindices = #[0] := by
  rw [cvmFamilyValidationRun.stats_eq]
  change #[cvmCandidate.families.singleton.familyType.type.trace.spineLength -
    2] = #[0]
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]

theorem cvmTerminalEnv_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env =
      constructorValidityMatrixContext.env := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.env :=
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext_env
    _ = cvmFamilyContext.env :=
      congrArg AddInductive.Context.env cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.env := rfl

theorem cvmTerminalLparams_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
      constructorValidityMatrixContext.lparams := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.lparams :=
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext_lparams
    _ = cvmFamilyContext.lparams :=
      congrArg AddInductive.Context.lparams cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.lparams := rfl

theorem cvmTerminalAllowPrimitive_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.allowPrimitive =
      constructorValidityMatrixContext.allowPrimitive := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.allowPrimitive :=
      cvmCandidate.families.singleton.familyType.type.trace
        |>.terminalContext_allowPrimitive
    _ = cvmFamilyContext.allowPrimitive :=
      congrArg AddInductive.Context.allowPrimitive cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.allowPrimitive := rfl

theorem cvmFamilyNameAbsent :
    constructorValidityMatrixContext.env.contains
      constructorValidityMatrixKernelType.name = false := by
  change ({} : ConstMap).contains
    constructorValidityMatrixKernelType.name = false
  rw [SMap.find?_isSome,
    SMap.WF.find?_eq SMap.WF.empty]
  simp [SMap.toList']

theorem cvmFamilyNameNotPrimitive :
    Kernel.Environment.primitives.contains
      constructorValidityMatrixKernelType.name = false := by
  simp [constructorValidityMatrixKernelType,
    constructorValidityMatrixInfo, Kernel.Environment.primitives,
    NameSet.ofList]
  simp +decide [NameSet.contains]

def cvmDeclaredInfo : ConstantInfo :=
  .inductInfo <| AddInductive.singletonDeclaredInfo
    cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
    0 false
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext

theorem cvmFamilyNames_eq :
    constructorValidityMatrixKernelType.name =
      constructorValidityMatrixType.name := by
  decide

theorem cvmFamilyMap_add :
    cvmExecution.familyEnv.constants =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        constructorValidityMatrixType.name cvmDeclaredInfo := by
  have h := cvmExecution.declareRun
  rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
  rw [← cvmFamilyNames_eq]
  simpa [cvmDeclaredInfo] using
    AddInductive.declareInductiveTypes_singleton_constants
      cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
      0 false
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext
      cvmExecution.familyEnv cvmStatsNindices_eq h

def cvmTypeEnv : VEnv :=
  (VEnv.empty.addConst constructorValidityMatrixType.name
    constructorValidityMatrixType.toVConstant).get!

theorem cvmTypeEnv_add :
    VEnv.empty.addConst constructorValidityMatrixType.name
        constructorValidityMatrixType.toVConstant = some cvmTypeEnv := by
  rfl

theorem cvmDeclaredInfo_tr :
    TrConstVal .safe VEnv.empty cvmDeclaredInfo
      constructorValidityMatrixType.toVConstVal := by
  refine ⟨⟨by decide, ?_, ?_⟩, rfl⟩
  · change
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams.length =
        constructorValidityMatrixType.uvars
    rw [cvmTerminalLparams_eq]
    rfl
  · change TrExprS VEnv.empty
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
      [] constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type
    rw [cvmTerminalLparams_eq]
    exact cvmFamilySource_tr

def cvmAddType :
    AddInductConstant .induct cvmFamilyContext.env.constants VEnv.empty
      constructorValidityMatrixType.toVConstVal
      cvmConstructorContext.env.constants cvmTypeEnv where
  info := cvmDeclaredInfo
  kind_eq := by simp [cvmDeclaredInfo, InductConstantKind.Matches]
  tr := cvmDeclaredInfo_tr
  map_fresh := by
    change ({} : ConstMap).find?
      constructorValidityMatrixType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  env_add := cvmTypeEnv_add
  map_add := by
    simpa [cvmFamilyContext, cvmConstructorContext,
      cvmTerminalEnv_eq] using cvmFamilyMap_add

theorem cvmFamilyWhnfDepth :
    cvmCandidate.families.singleton.familyType.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [cvmFamilyCandidateContext_eq]
  rfl

def cvmFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate.families.singleton.familyType
      constructorValidityMatrixType cvmPreFamilyStage where
  name_eq := cvmFamilyNames_eq
  uvars_eq := rfl
  type := {
    context_eq := cvmFamilyCandidateContext_eq.symm
    source_tr := cvmFamilySource_tr
    whnfFuel := 9999
    whnfDepth := cvmFamilyWhnfDepth }
  validation := cvmFamilyValidationRun
  typeEnv := cvmTypeEnv
  addInduct := cvmAddType
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := by
    have h := cvmExecution.declareRun
    rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
    simpa [cvmConstructorContext, cvmFamilyContext,
      cvmTerminalEnv_eq] using
      AddInductive.declareInductiveTypes_singleton_quotInit
        cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
        0 false
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext
        cvmExecution.familyEnv cvmStatsNindices_eq h
  name_not_reflected := by decide
  name_not_primitive := by
    rw [← cvmFamilyNames_eq]
    exact cvmFamilyNameNotPrimitive

def cvmCtorAlphaDomain : Expr :=
  constructorValidityMatrixKernelCtor.type.bindingDomain!

def cvmCtorAlphaContext : AddInductive.Context :=
  cvmConstructorContext.pushLocalDecl `α .implicit cvmCtorAlphaDomain

def cvmCtorAfterAlpha : Expr :=
  constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
    cvmConstructorContext.freshExpr

def cvmCtorPDomain : Expr := cvmCtorAfterAlpha.bindingDomain!

def cvmCtorPContext : AddInductive.Context :=
  cvmCtorAlphaContext.pushLocalDecl `P .implicit cvmCtorPDomain

def cvmCtorAfterP : Expr :=
  cvmCtorAfterAlpha.bindingBody!.instantiate1
    cvmCtorAlphaContext.freshExpr

def cvmCtorXDomain : Expr := cvmCtorAfterP.bindingDomain!

def cvmCtorXContext : AddInductive.Context :=
  cvmCtorPContext.pushLocalDecl `x .default cvmCtorXDomain

def cvmCtorAfterX : Expr :=
  cvmCtorAfterP.bindingBody!.instantiate1 cvmCtorPContext.freshExpr

def cvmCtorProofDomain : Expr := cvmCtorAfterX.bindingDomain!

def cvmCtorProofContext : AddInductive.Context :=
  cvmCtorXContext.pushLocalDecl `proof .default cvmCtorProofDomain

def cvmCtorAfterProof : Expr :=
  cvmCtorAfterX.bindingBody!.instantiate1 cvmCtorXContext.freshExpr

def cvmCtorDirectDomain : Expr := cvmCtorAfterProof.bindingDomain!

def cvmCtorDirectContext : AddInductive.Context :=
  cvmCtorProofContext.pushLocalDecl `direct .default cvmCtorDirectDomain

def cvmCtorAfterDirect : Expr :=
  cvmCtorAfterProof.bindingBody!.instantiate1 cvmCtorProofContext.freshExpr

def cvmCtorFunctionDomain : Expr := cvmCtorAfterDirect.bindingDomain!

def cvmCtorFunctionContext : AddInductive.Context :=
  cvmCtorDirectContext.pushLocalDecl `function .default cvmCtorFunctionDomain

def cvmCtorAfterFunction : Expr :=
  cvmCtorAfterDirect.bindingBody!.instantiate1
    cvmCtorDirectContext.freshExpr

def cvmCtorLaterDomain : Expr := cvmCtorAfterFunction.bindingDomain!

def cvmCtorLaterContext : AddInductive.Context :=
  cvmCtorFunctionContext.pushLocalDecl `later .default cvmCtorLaterDomain

def cvmCtorAfterLater : Expr :=
  cvmCtorAfterFunction.bindingBody!.instantiate1
    cvmCtorFunctionContext.freshExpr

def cvmCtorLaterProofDomain : Expr := cvmCtorAfterLater.bindingDomain!

def cvmCtorLaterProofContext : AddInductive.Context :=
  cvmCtorLaterContext.pushLocalDecl `laterProof .default
    cvmCtorLaterProofDomain

def cvmCtorTerminal : Expr :=
  cvmCtorAfterLater.bindingBody!.instantiate1
    cvmCtorLaterContext.freshExpr

def cvmCtorPArgContext : AddInductive.Context :=
  cvmCtorAlphaContext.pushLocalDecl cvmCtorPDomain.bindingName!
    .default cvmCtorPDomain.bindingDomain!

def cvmCtorFunctionArgContext : AddInductive.Context :=
  cvmCtorDirectContext.pushLocalDecl `y .default
    cvmCtorFunctionDomain.bindingDomain!

def cvmCtorRootLocalRun :
    TypeChecker.CandidateLocalContextRun cvmConstructorContext :=
  .empty _ rfl

def cvmCtorAlphaLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorAlphaContext :=
  cvmCtorRootLocalRun.push `α .implicit cvmCtorAlphaDomain

def cvmCtorPLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorPContext :=
  cvmCtorAlphaLocalRun.push `P .implicit cvmCtorPDomain

def cvmCtorXLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorXContext :=
  cvmCtorPLocalRun.push `x .default cvmCtorXDomain

def cvmCtorProofLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorProofContext :=
  cvmCtorXLocalRun.push `proof .default cvmCtorProofDomain

def cvmCtorDirectLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorDirectContext :=
  cvmCtorProofLocalRun.push `direct .default cvmCtorDirectDomain

def cvmCtorFunctionLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorFunctionContext :=
  cvmCtorDirectLocalRun.push `function .default cvmCtorFunctionDomain

def cvmCtorLaterLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorLaterContext :=
  cvmCtorFunctionLocalRun.push `later .default cvmCtorLaterDomain

def cvmCtorLaterProofLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorLaterProofContext :=
  cvmCtorLaterLocalRun.push `laterProof .default cvmCtorLaterProofDomain

theorem cvmCtorAlphaFindInAlpha :
    cvmCtorAlphaContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorRootLocalRun.push_findNew `α .implicit cvmCtorAlphaDomain

theorem cvmCtorAlphaFindInP :
    cvmCtorPContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorAlphaLocalRun.push_findOld `P .implicit cvmCtorPDomain
    cvmCtorAlphaFindInAlpha

theorem cvmCtorAlphaFindInX :
    cvmCtorXContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorPLocalRun.push_findOld `x .default cvmCtorXDomain
    cvmCtorAlphaFindInP

theorem cvmCtorAlphaFindInProof :
    cvmCtorProofContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorXLocalRun.push_findOld `proof .default cvmCtorProofDomain
    cvmCtorAlphaFindInX

theorem cvmCtorAlphaFindInDirect :
    cvmCtorDirectContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorProofLocalRun.push_findOld `direct .default cvmCtorDirectDomain
    cvmCtorAlphaFindInProof

theorem cvmCtorAlphaFindInFunction :
    cvmCtorFunctionContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorDirectLocalRun.push_findOld `function .default
    cvmCtorFunctionDomain cvmCtorAlphaFindInDirect

theorem cvmCtorPFindInP :
    cvmCtorPContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorAlphaLocalRun.push_findNew `P .implicit cvmCtorPDomain

theorem cvmCtorPFindInX :
    cvmCtorXContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorPLocalRun.push_findOld `x .default cvmCtorXDomain
    cvmCtorPFindInP

theorem cvmCtorPFindInProof :
    cvmCtorProofContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorXLocalRun.push_findOld `proof .default cvmCtorProofDomain
    cvmCtorPFindInX

theorem cvmCtorPFindInDirect :
    cvmCtorDirectContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorProofLocalRun.push_findOld `direct .default cvmCtorDirectDomain
    cvmCtorPFindInProof

theorem cvmCtorPFindInFunction :
    cvmCtorFunctionContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorDirectLocalRun.push_findOld `function .default
    cvmCtorFunctionDomain cvmCtorPFindInDirect

theorem cvmCtorPFindInLater :
    cvmCtorLaterContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorFunctionLocalRun.push_findOld `later .default cvmCtorLaterDomain
    cvmCtorPFindInFunction

theorem cvmCtorFamilyLookup :
    cvmConstructorContext.env.find?
        constructorValidityMatrixKernelType.name =
      some cvmDeclaredInfo := by
  change cvmExecution.familyEnv.constants.find?'
      constructorValidityMatrixKernelType.name = some cvmDeclaredInfo
  rw [show cvmExecution.familyEnv.constants =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        constructorValidityMatrixType.name cvmDeclaredInfo from cvmFamilyMap_add]
  have hbase :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.WF := by
    rw [cvmTerminalEnv_eq]
    exact SMap.WF.empty
  have hfresh :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.find?
        constructorValidityMatrixType.name = none := by
    rw [cvmTerminalEnv_eq]
    change ({} : ConstMap).find? constructorValidityMatrixType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  have hinsert := hbase.insert constructorValidityMatrixType.name
    cvmDeclaredInfo hfresh
  rw [SMap.WF.find?'_eq_find? hinsert]
  rw [hbase.find?_insert]
  simp [cvmFamilyNames_eq]

theorem cvmCtorFamilyWhnf
    (context : AddInductive.Context)
    (arg1 arg2 : FVarId)
    (henv : context.env = cvmConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .app
          (.app (.const ``ConstructorValidityMatrix [.param `u])
            (.fvar arg1))
          (.fvar arg2),
        .app
          (.app (.const ``ConstructorValidityMatrix [.param `u])
            (.fvar arg1))
          (.fvar arg2)⟩ := by
  apply TypeChecker.candidateWhnfConstFVarFVar_refl context
    ``ConstructorValidityMatrix [.param `u] arg1 arg2
    (AddInductive.singletonDeclaredInfo
      cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
      0 false
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext)
  · exact hdepth
  · exact hwhnf
  · exact hquot
  · rw [henv]
    simpa [cvmDeclaredInfo, constructorValidityMatrixKernelType,
      constructorValidityMatrixInfo, ConstantInfo.name,
      ConstantInfo.toConstantVal] using cvmCtorFamilyLookup
  · rfl

def cvmCtorFamilyApp : Expr :=
  .app
    (.app (.const ``ConstructorValidityMatrix [.param `u])
      cvmConstructorContext.freshExpr)
    cvmCtorAlphaContext.freshExpr

macro "simp_cvm_ctor_expr" : tactic =>
  `(tactic| simp [cvmCtorTerminal, cvmCtorLaterProofContext,
    cvmCtorPArgContext, cvmCtorFunctionArgContext,
    cvmCtorLaterProofDomain, cvmCtorAfterLater, cvmCtorLaterContext,
    cvmCtorLaterDomain, cvmCtorAfterFunction, cvmCtorFunctionContext,
    cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorDirectContext,
    cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorProofContext,
    cvmCtorProofDomain, cvmCtorAfterX, cvmCtorXContext,
    cvmCtorXDomain, cvmCtorAfterP, cvmCtorPContext, cvmCtorPDomain,
    cvmCtorAfterAlpha, cvmCtorAlphaContext, cvmCtorAlphaDomain,
    cvmCtorFamilyApp, cvmConstructorContext,
    constructorValidityMatrixKernelCtor,
    constructorValidityMatrixKernelType,
    constructorValidityMatrixMkInfo, constructorValidityMatrixInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    Expr.bindingDomain!, Expr.bindingBody!, Expr.bindingName!,
    Expr.bindingInfo!, Expr.isForall,
    Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero,
    AddInductive.CandidateTypeAnnotationTrace.build])

macro "simpa_cvm_ctor_expr" " using " t:term : tactic =>
  `(tactic| simpa [cvmCtorTerminal, cvmCtorLaterProofContext,
      cvmCtorPArgContext, cvmCtorFunctionArgContext,
      cvmCtorLaterProofDomain, cvmCtorAfterLater, cvmCtorLaterContext,
      cvmCtorLaterDomain, cvmCtorAfterFunction, cvmCtorFunctionContext,
      cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorDirectContext,
      cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorProofContext,
      cvmCtorProofDomain, cvmCtorAfterX, cvmCtorXContext,
      cvmCtorXDomain, cvmCtorAfterP, cvmCtorPContext, cvmCtorPDomain,
      cvmCtorAfterAlpha, cvmCtorAlphaContext, cvmCtorAlphaDomain,
      cvmCtorFamilyApp, cvmConstructorContext,
      constructorValidityMatrixKernelCtor,
      constructorValidityMatrixKernelType,
      constructorValidityMatrixMkInfo, constructorValidityMatrixInfo,
      ConstantInfo.type, ConstantInfo.toConstantVal,
      AddInductive.Context.pushLocalDecl,
      AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
      Expr.bindingDomain!, Expr.bindingBody!, Expr.bindingName!,
      Expr.bindingInfo!, Expr.isForall,
      Expr.instantiate1_eq, Expr.instantiate1',
      Expr.liftLooseBVars_zero,
      AddInductive.CandidateTypeAnnotationTrace.build] using $t)


theorem cvmCtorQuotInit :
    cvmConstructorContext.env.quotInit = false := by
  rw [cvmFamilyStage.quotInit_eq]
  rfl

theorem cvmCtorFamilyAppWhnf
    (context : AddInductive.Context)
    (henv : context.env = cvmConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context, cvmCtorFamilyApp, cvmCtorFamilyApp⟩ := by
  have hquot : context.env.quotInit = false := by
    rw [henv]
    exact cvmCtorQuotInit
  simpa [cvmCtorFamilyApp, AddInductive.Context.freshExpr,
      constructorValidityMatrixKernelType,
      constructorValidityMatrixInfo, ConstantInfo.name] using
    cvmCtorFamilyWhnf context cvmConstructorContext.freshFVarId
      cvmCtorAlphaContext.freshFVarId henv hdepth hwhnf hquot

open TypeChecker in
def cvmCtorIdentityShape :
    CandidateExprIdentityReplay.Shaped cvmConstructorContext
      constructorValidityMatrixKernelCtor.type 8 cvmCtorFamilyApp := by
  have alphaInAlpha : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorAlphaContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    simpa [cvmCtorAlphaContext, cvmCtorAlphaDomain] using
      TypeChecker.candidateWhnfPushedFVar_refl
        cvmConstructorContext `α cvmCtorAlphaDomain .implicit 9999
        (by rfl) cvmCtorRootLocalRun.wf cvmCtorRootLocalRun.fresh
  have alphaInP : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorPContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInP]
  have alphaInDirect : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorDirectContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInDirect]
  have alphaInFunction : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorFunctionContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInFunction]
  have proofDomainWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorXContext, cvmCtorProofDomain,
        cvmCtorProofDomain⟩ := by
    have run := TypeChecker.candidateWhnfFVarAppFVar_refl
      cvmCtorXContext cvmCtorAlphaContext.freshFVarId
      cvmCtorPContext.freshFVarId (by rfl) (by rfl)
      (by
        change cvmConstructorContext.env.quotInit = false
        exact cvmCtorQuotInit) (by
        unfold TypeChecker.Inner.isLetFVar
        rw [cvmCtorPFindInX])
    rw [show cvmCtorProofDomain =
      .app cvmCtorAlphaContext.freshExpr cvmCtorPContext.freshExpr by
        simp_cvm_ctor_expr]
    exact run
  have laterProofDomainWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorLaterContext, cvmCtorLaterProofDomain,
        cvmCtorLaterProofDomain⟩ := by
    have run := TypeChecker.candidateWhnfFVarAppFVar_refl
      cvmCtorLaterContext cvmCtorAlphaContext.freshFVarId
      cvmCtorFunctionContext.freshFVarId (by rfl) (by rfl)
      (by
        change cvmConstructorContext.env.quotInit = false
        exact cvmCtorQuotInit) (by
        unfold TypeChecker.Inner.isLetFVar
        rw [cvmCtorPFindInLater])
    rw [show cvmCtorLaterProofDomain =
      .app cvmCtorAlphaContext.freshExpr
        cvmCtorFunctionContext.freshExpr by simp_cvm_ctor_expr]
    exact run
  have terminalShape : CandidateExprIdentityReplay.Shaped
      cvmCtorLaterProofContext cvmCtorTerminal 0
      cvmCtorFamilyApp := by
    rw [show cvmCtorTerminal = cvmCtorFamilyApp by simp_cvm_ctor_expr]
    exact .terminal _ _
      (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have laterProofShape : CandidateExprIdentityReplay.Shaped
      cvmCtorLaterContext cvmCtorAfterLater 1
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorLaterContext cvmCtorAfterLater
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          laterProofDomainWhnf (by simp_cvm_ctor_expr)).replay)
    · simpa_cvm_ctor_expr using terminalShape
  have laterShape : CandidateExprIdentityReplay.Shaped
      cvmCtorFunctionContext cvmCtorAfterFunction 2
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorFunctionContext cvmCtorAfterFunction
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInFunction rfl).replay)
    · simpa_cvm_ctor_expr using laterProofShape
  have functionArgTerminal : CandidateExprIdentityReplay.Shaped
      cvmCtorFunctionArgContext cvmCtorFamilyApp 0
      cvmCtorFamilyApp :=
    .terminal _ _ (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have functionDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorDirectContext cvmCtorFunctionDomain 1
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorDirectContext cvmCtorFunctionDomain
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInDirect rfl).replay)
    · simpa_cvm_ctor_expr using functionArgTerminal
  have functionShape : CandidateExprIdentityReplay.Shaped
      cvmCtorDirectContext cvmCtorAfterDirect 3
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorDirectContext cvmCtorAfterDirect
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using functionDomainShape.replay
    · simpa_cvm_ctor_expr using laterShape
  have directDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorProofContext cvmCtorDirectDomain 0
      cvmCtorFamilyApp := by
    rw [show cvmCtorDirectDomain = cvmCtorFamilyApp by simp_cvm_ctor_expr]
    exact .terminal _ _ (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have directShape : CandidateExprIdentityReplay.Shaped
      cvmCtorProofContext cvmCtorAfterProof 4
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorProofContext cvmCtorAfterProof
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · have consumeDirect : AddInductive.consumeTypeAnnotations
          cvmCtorDirectDomain = cvmCtorDirectDomain := by
        rw [show cvmCtorDirectDomain = cvmCtorFamilyApp by simp_cvm_ctor_expr]
        simpa [cvmCtorFamilyApp,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            cvmCtorFamilyApp).symm
      simpa only [cvmCtorDirectDomain] using consumeDirect
    · simpa_cvm_ctor_expr using directDomainShape.replay
    · simpa_cvm_ctor_expr using functionShape
  have proofShape : CandidateExprIdentityReplay.Shaped
      cvmCtorXContext cvmCtorAfterX 5 cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorXContext cvmCtorAfterX
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          proofDomainWhnf (by simp_cvm_ctor_expr)).replay)
    · simpa_cvm_ctor_expr using directShape
  have xShape : CandidateExprIdentityReplay.Shaped
      cvmCtorPContext cvmCtorAfterP 6 cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorPContext cvmCtorAfterP
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _ alphaInP rfl).replay)
    · simpa_cvm_ctor_expr using proofShape
  have pArgTerminal : CandidateExprIdentityReplay.Shaped
      cvmCtorPArgContext (.sort .zero) 0 (.sort .zero) :=
    .terminal _ _ (by rfl) rfl
  have pDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorAlphaContext cvmCtorPDomain 1 (.sort .zero) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorAlphaContext cvmCtorPDomain
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInAlpha rfl).replay)
    · simpa_cvm_ctor_expr using pArgTerminal
  have pShape : CandidateExprIdentityReplay.Shaped
      cvmCtorAlphaContext cvmCtorAfterAlpha 7
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorAlphaContext cvmCtorAfterAlpha
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using pDomainShape.replay
    · simpa_cvm_ctor_expr using xShape
  apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
    cvmConstructorContext constructorValidityMatrixKernelCtor.type
  · simp_cvm_ctor_expr
  · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
      _ _ 9999 (by rfl)
    simp_cvm_ctor_expr
  · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
    simp_cvm_ctor_expr
  · have alphaDomainWhnf : AddInductive.CandidateWhnfStep.Valid
        ⟨cvmConstructorContext, cvmCtorAlphaDomain,
          cvmCtorAlphaDomain⟩ := by
      change AddInductive.CandidateWhnfStep.Valid
        ⟨cvmConstructorContext, .sort (.succ (.param `u)),
          .sort (.succ (.param `u))⟩
      rfl
    exact (CandidateExprIdentityReplay.Shaped.terminal _ _
      alphaDomainWhnf rfl).replay
  · simpa_cvm_ctor_expr using pShape

theorem cvmCtorCandidateBuild :
    AddInductive.buildCandidateExpr constructorValidityMatrixKernelCtor.type
        cvmConstructorContext =
      .ok cvmCandidate.families.singleton.constructors.singleton.type := by
  have produced := cvmExecution.families.produced.singleton_constructors
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.families.candidates.singleton.constructors] at produced
  have exactProduced : AddInductive.CandidateConstructorListProduced
      cvmConstructorContext
      (.cons cvmCandidate.families.singleton.constructors.singleton .nil) := by
    simpa [cvmCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      cvmConstructorContext, constructorValidityMatrixKernelType] using produced
  exact exactProduced.singleton_build

def cvmCtorIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay cvmConstructorContext
      constructorValidityMatrixKernelCtor.type :=
  cvmCtorIdentityShape.replay

def cvmCtorIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      cvmCtorIdentityReplay
      cvmCandidate.families.singleton.constructors.singleton.type.trace :=
  cvmCtorIdentityReplay.evidence_of_build cvmCtorCandidateBuild

theorem cvmCtorIdentityReplay_shape :
    cvmCtorIdentityReplay.spineLength = 8 ∧
      cvmCtorIdentityReplay.terminalSource = cvmCtorFamilyApp :=
  ⟨cvmCtorIdentityShape.spineLength_eq,
    cvmCtorIdentityShape.terminalSource_eq⟩

theorem cvmTypeEnv_ordered : cvmTypeEnv.Ordered :=
  .const (n := constructorValidityMatrixType.name)
    (ci := constructorValidityMatrixType.toVConstant)
    .empty cvmRawFamily_isType cvmTypeEnv_add

theorem cvmRawCtor_isType :
    cvmTypeEnv.IsType 1 [] constructorValidityMatrixType.ctors[0].type := by
  have hFamily : cvmTypeEnv.constants constructorValidityMatrixType.name =
      some constructorValidityMatrixType.toVConstant :=
    VEnv.addConst_self cvmTypeEnv_add
  exact ⟨_, by type_tac⟩

theorem cvmCtorSource_tr :
    TrExprS cvmTypeEnv [`u] [] constructorValidityMatrixKernelCtor.type
      constructorValidityMatrixType.ctors[0].type := by
  have shape : TrTypeExpr cvmTypeEnv [`u] []
      constructorValidityMatrixKernelCtor.type
      constructorValidityMatrixType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := cvmRawCtor_isType
  exact shape.to_trExprS cvmTypeEnv_ordered trivial ⟨.sort level, type⟩

theorem cvmCtorNames_eq :
    constructorValidityMatrixKernelCtor.name =
      constructorValidityMatrixType.ctors[0].name := by
  decide

theorem cvmCtorWhnfDepth :
    cvmCandidate.families.singleton.constructors.singleton.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [cvmConstructorCandidateContext_eq]
  rfl

theorem cvmRawCtors_eq :
    constructorValidityMatrixType.ctors =
      [constructorValidityMatrixType.ctors[0]] := by
  rfl

def cvmCtorStagedInput :
    VInductDecl.CandidateConstructorStagedInput
      cvmFamilyStage.postFamily
      cvmCandidate.families.singleton.constructors.singleton
      constructorValidityMatrixType.ctors[0] where
  name_eq := cvmCtorNames_eq
  uvars_eq := rfl
  type := {
    context_eq := cvmConstructorCandidateContext_eq.symm
    source_tr := cvmCtorSource_tr
    whnfFuel := 9999
    whnfDepth := cvmCtorWhnfDepth }

def cvmConstructorsStage :
    VInductDecl.CandidateConstructorStagedListInput
      cvmFamilyStage.postFamily
      cvmCandidate.families.singleton.constructors
      constructorValidityMatrixType.ctors := by
  rw [AddInductive.CandidateList.singleton_eta
    cvmCandidate.families.singleton.constructors, cvmRawCtors_eq]
  exact .cons cvmCtorStagedInput .nil

theorem cvmFamilyTypesProduced :
    AddInductive.CandidateFamilyTypeListProduced cvmFamilyContext
      (.cons cvmCandidate.families.singleton.familyType .nil) := by
  have h := cvmExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.familyTypes.candidates] at h
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate, cvmFamilyContext,
    AddInductive.NormalizationCandidateExecution.candidate] using h

theorem cvmFamiliesProduced :
    AddInductive.CandidateFamilyListProduced cvmConstructorContext
      (.cons cvmCandidate.families.singleton.familyType .nil)
      cvmCandidate.families := by
  simpa [cvmCandidate, cvmConstructorContext,
    AddInductive.NormalizationCandidateExecution.candidate] using
    cvmExecution.families.produced.singleton_reindex

theorem cvmCheckConstructorsRun :
    AddInductive.checkConstructors #[constructorValidityMatrixKernelType]
        cvmFamilyValidationRun.stats false
        { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := cvmConstructorContext.env } = .ok () := by
  have h := cvmExecution.constructorRun
  rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
  simpa [cvmConstructorContext] using h

theorem cvmUniverseRun :
    AddInductive.checkConstructorUniverseListSemantics
        cvmFamilyValidationRun.stats constructorValidityMatrixKernelType.ctors
        { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := cvmConstructorContext.env } = .ok () := by
  apply exceptUnit_eq_ok_of_isOk
  native_decide

def cvmConstructorValidationResult :=
  AddInductive.ConstructorValidationRun.buildExecution
    constructorValidityMatrixKernelType cvmFamilyValidationRun.stats false
    { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := cvmConstructorContext.env }

theorem cvmConstructorValidationResult_isOk :
    cvmConstructorValidationResult.isOk = true := by
  native_decide

def cvmProducedConstructorValidation :
    { validation // cvmConstructorValidationResult = .ok validation } :=
  match h : cvmConstructorValidationResult with
  | .ok validation => ⟨validation, rfl⟩
  | .error _ => by
      have hOk := cvmConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

def cvmConstructorValidation := cvmProducedConstructorValidation.val

def cvmStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl where
  staged := {
    raw := constructorValidityMatrixType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := cvmPreFamilyStage
    family := cvmFamilyStage
    validation_nparams_eq := rfl
    constructorValidation := cvmConstructorValidation
    constructors := cvmConstructorsStage
    familyTypesProduced := cvmFamilyTypesProduced
    familiesProduced := cvmFamiliesProduced }
  universeRun := cvmUniverseRun

theorem cvmAlignmentRun :
    cvmStagedUniverseInput.staged.constructorValidation.trace.checkCandidateAlignment
        cvmCandidate.families.singleton.constructors
        { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := cvmConstructorContext.env } = .ok () := by
  apply exceptUnit_eq_ok_of_isOk
  native_decide

noncomputable def cvmStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl :=
  VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun
    cvmStagedUniverseInput cvmAlignmentRun

theorem cvmSafetyRunDirect :
    AddInductive.checkConstructorPreFamilySafety
        cvmStagedUniverseInput.staged.family.validation.stats
        cvmCandidate.families.singleton.familyType.type.view
        cvmCandidate.families.singleton.constructors
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  apply exceptUnit_eq_ok_of_isOk
  native_decide

theorem cvmSafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        cvmStagedPostFamilyInput.universeInput.staged.family.validation.stats
        cvmCandidate.families.singleton.familyType.type.view
        cvmCandidate.families.singleton.constructors
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  simpa [cvmStagedPostFamilyInput,
    VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun] using
    cvmSafetyRunDirect

noncomputable def cvmStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    cvmStagedPostFamilyInput cvmSafetyRun

def prbExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 1
    [propRecursiveBoundaryKernelType] 0 false
    propRecursiveBoundaryContext

theorem prbExecutionResult_isOk : prbExecutionResult.isOk = true := by
  native_decide

def prbProducedExecution :
    { execution // prbExecutionResult = .ok execution } :=
  match h : prbExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := prbExecutionResult_isOk
      rw [h] at hOk
      contradiction

def prbExecution := prbProducedExecution.val

def prbCandidate := prbExecution.candidate

open TypeChecker in
def prbFamilyIdentityShape :
    CandidateExprIdentityReplay.Shaped propRecursiveBoundaryContext
      propRecursiveBoundaryKernelType.type 2 (.sort .zero) := by
  let aName := propRecursiveBoundaryKernelType.type.bindingBody!.bindingName!
  change CandidateExprIdentityReplay.Shaped propRecursiveBoundaryContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE aName (.bvar 0) (.sort .zero) .default) .default)
    2 (.sort .zero)
  let alphaContext := propRecursiveBoundaryContext.pushLocalDecl
    `α .default (.sort (.succ (.param `u)))
  let alphaAnnotations := AddInductive.builtCandidateTypeAnnotations
    (Expr.sort (.succ (.param `u)))
  refine .forallE (expectedSpineLength := 1)
    propRecursiveBoundaryContext `α
    (.sort (.succ (.param `u)))
    (.forallE aName (.bvar 0) (.sort .zero) .default) .default
    (by rfl) alphaAnnotations
    (AddInductive.buildCandidateTypeAnnotations_built _) (by
      simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          (.sort (.succ (.param `u)))).symm)
    (.terminal _ _ (by rfl) rfl) ?_
  have alphaFVarWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨alphaContext, propRecursiveBoundaryContext.freshExpr,
        propRecursiveBoundaryContext.freshExpr⟩ := by
    simpa [alphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        propRecursiveBoundaryContext `α
        (.sort (.succ (.param `u))) .default 9999 (by rfl)
        (by
          change LocalContext.WF ⟨.empty, .empty, .empty⟩
          exact LocalContext.WF.nil)
        (by
          change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
            propRecursiveBoundaryContext.freshFVarId = none
          exact TypeChecker.emptyLocalContextFindNone _)
  have alphaBody : CandidateExprIdentityReplay.Shaped alphaContext
      (.forallE aName propRecursiveBoundaryContext.freshExpr
        (.sort .zero) .default) 1 (.sort .zero) := by
    let aAnnotations := AddInductive.builtCandidateTypeAnnotations
      propRecursiveBoundaryContext.freshExpr
    refine .forallE (expectedSpineLength := 0) alphaContext aName
      propRecursiveBoundaryContext.freshExpr (.sort .zero) .default
      (by rfl) aAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            propRecursiveBoundaryContext.freshExpr).symm)
      (.terminal _ _ alphaFVarWhnf rfl) ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl aName .default
          propRecursiveBoundaryContext.freshExpr)
        (.sort .zero) 0 (.sort .zero) :=
      .terminal _ _ (by rfl) rfl
    simpa [aAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      AddInductive.Context.freshExpr,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  simpa [alphaContext, alphaAnnotations,
    AddInductive.builtCandidateTypeAnnotations,
    AddInductive.CandidateTypeAnnotationTrace.build,
    Expr.instantiate1_eq, Expr.instantiate1'] using alphaBody

def prbFamilyIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay propRecursiveBoundaryContext
      propRecursiveBoundaryKernelType.type :=
  prbFamilyIdentityShape.replay

theorem prbFamilyCandidateBuild :
    AddInductive.buildCandidateExpr propRecursiveBoundaryKernelType.type
        propRecursiveBoundaryContext =
      .ok prbCandidate.families.singleton.familyType.type := by
  have produced := prbExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.familyTypes.candidates] at produced
  rw [← prbExecution.families.produced.singleton_familyType] at produced
  have exactProduced : AddInductive.CandidateFamilyTypeListProduced
      propRecursiveBoundaryContext
      (.cons prbCandidate.families.singleton.familyType .nil) := by
    simpa [prbCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      propRecursiveBoundaryContext] using produced
  exact exactProduced.singleton_build

def prbFamilyIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      prbFamilyIdentityReplay
      prbCandidate.families.singleton.familyType.type.trace :=
  prbFamilyIdentityReplay.evidence_of_build prbFamilyCandidateBuild

theorem prbFamilyIdentityReplay_shape :
    prbFamilyIdentityReplay.spineLength = 2 ∧
      prbFamilyIdentityReplay.terminalSource = .sort .zero :=
  ⟨prbFamilyIdentityShape.spineLength_eq,
    prbFamilyIdentityShape.terminalSource_eq⟩

theorem prbFamilyValidationAnnotations :
    prbCandidate.families.singleton.familyType.type.trace
      |>.validationAnnotations := by
  have h := prbExecution.familyTypes.produced
    |>.singleton_validationAnnotations
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate] using h

private theorem prbFamilyData_hasExprMVar_false :
    propRecursiveBoundaryInfo.type.data.hasExprMVar = false := by
  change propRecursiveBoundaryInfo.type.hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem prbFamilyData_hasLevelMVar_false :
    propRecursiveBoundaryInfo.type.data.hasLevelMVar = false := by
  change propRecursiveBoundaryInfo.type.hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [propRecursiveBoundaryInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.hasLevelMVar',
    Level.hasMVar_eq, Level.hasMVar']

private theorem prbFamilyData_hasFVar_false :
    propRecursiveBoundaryInfo.type.data.hasFVar = false := by
  change propRecursiveBoundaryInfo.type.hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem prbFamily_hasMVar_false :
    propRecursiveBoundaryInfo.type.hasMVar = false := by
  change (propRecursiveBoundaryInfo.type.data.hasExprMVar ||
    propRecursiveBoundaryInfo.type.data.hasLevelMVar) = false
  rw [prbFamilyData_hasExprMVar_false,
    prbFamilyData_hasLevelMVar_false]
  rfl

private theorem prbFamily_hasFVar_false :
    propRecursiveBoundaryInfo.type.hasFVar = false :=
  prbFamilyData_hasFVar_false

theorem prbFamilyClosed :
    prbCandidate.families.singleton.familyType.type.context.env.checkNoMVarNoFVar
        propRecursiveBoundaryKernelType.name
        propRecursiveBoundaryKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show propRecursiveBoundaryKernelType.type.hasMVar = false by
    simpa [propRecursiveBoundaryKernelType] using
      prbFamily_hasMVar_false]
  rw [show propRecursiveBoundaryKernelType.type.hasFVar = false by
    simpa [propRecursiveBoundaryKernelType] using
      prbFamily_hasFVar_false]
  rfl

theorem prbFamilyEnsureSort :
    TypeChecker.M.run
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.env
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.safety
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.fuel
        (TypeChecker.ensureSort (.sort .zero)) =
      .ok (.sort .zero) := by
  rfl

theorem prbFamilySpineCount :
    1 ≤ prbCandidate.families.singleton.familyType.type.trace.spineLength := by
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]
  decide

theorem prbFamilySpineFuel :
    prbCandidate.families.singleton.familyType.type.trace.spineLength <
      prbCandidate.families.singleton.familyType.type.context.fuel.inductiveFuel := by
  have contextFuel := congrArg (fun context : AddInductive.Context =>
      context.fuel.inductiveFuel)
    (AddInductive.CandidateExpr.context_eq_of_build prbFamilyCandidateBuild)
  rw [contextFuel]
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]
  decide

def prbFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      propRecursiveBoundaryKernelType
      prbCandidate.families.singleton.familyType.type.trace where
  nparams := 1
  resultLevel := .zero
  stats :=
    prbCandidate.families.singleton.familyType.type.trace
      |>.singletonCandidateInductiveStats
        propRecursiveBoundaryKernelType 1 .zero
  stats_eq := rfl
  terminal_eq := prbFamilyIdentityEvidence.terminalResult_eq.trans
    prbFamilyIdentityReplay_shape.2
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      propRecursiveBoundaryKernelType
      prbCandidate.families.singleton.familyType.type.trace
      1 .zero k
      prbFamilyClosed prbFamilySpineCount prbFamilySpineFuel
      prbFamilyValidationAnnotations
      (prbFamilyIdentityEvidence.terminalResult_eq.trans
        prbFamilyIdentityReplay_shape.2)
      prbFamilyEnsureSort

theorem prbFamilyContext_eq :
    prbCandidate.families.singleton.familyType.type.context =
      propRecursiveBoundaryContext := by
  have h := prbExecution.familyTypes.produced.singleton_context_eq
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    propRecursiveBoundaryContext] using h

theorem prbFamilyNparams_eq : prbFamilyValidationRun.nparams = 1 := by
  rfl

theorem prbFamilyValidationRun_exact : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 1 #[propRecursiveBoundaryKernelType]
        k propRecursiveBoundaryContext =
      k prbFamilyValidationRun.stats
        prbCandidate.families.singleton.familyType.type.trace.terminalContext := by
  intro alpha k
  simpa only [prbFamilyNparams_eq, prbFamilyContext_eq] using
    prbFamilyValidationRun.run k

theorem prbAfterValidationRun :
    AddInductive.buildNormalizationCandidateExecutionAfterValidation 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext prbFamilyValidationRun.stats
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok prbExecution := by
  have h := prbProducedExecution.property
  change AddInductive.buildNormalizationCandidateExecution 1
      [propRecursiveBoundaryKernelType] 0 false
      propRecursiveBoundaryContext = .ok prbExecution at h
  unfold AddInductive.buildNormalizationCandidateExecution at h
  rw [prbFamilyValidationRun_exact] at h
  exact h

theorem prbExecutionStats_eq :
    prbExecution.stats = prbFamilyValidationRun.stats :=
  (prbExecution.fields_of_afterValidation prbFamilyValidationRun.stats
    prbCandidate.families.singleton.familyType.type.trace.terminalContext
    prbAfterValidationRun).1

theorem prbExecutionValidationContext_eq :
    prbExecution.validationContext =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext :=
  (prbExecution.fields_of_afterValidation prbFamilyValidationRun.stats
    prbCandidate.families.singleton.familyType.type.trace.terminalContext
    prbAfterValidationRun).2

theorem prbExecutionValidationRun : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 1 #[propRecursiveBoundaryKernelType]
        k propRecursiveBoundaryContext =
      k prbExecution.stats prbExecution.validationContext := by
  intro alpha k
  rw [prbFamilyValidationRun_exact, prbExecutionStats_eq,
    prbExecutionValidationContext_eq]

theorem prbCandidate_produced :
    AddInductive.buildNormalizationCandidate 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext = .ok prbCandidate :=
  prbExecution.produces prbExecutionValidationRun

def prbFamilyContext : AddInductive.Context :=
  { propRecursiveBoundaryContext with lctx := {} }

def prbConstructorContext : AddInductive.Context :=
  { propRecursiveBoundaryContext with
    env := prbExecution.familyEnv, lctx := {} }

theorem prbFamilyCandidateContext_eq :
    prbCandidate.families.singleton.familyType.type.context =
      prbFamilyContext := by
  simpa [prbFamilyContext, propRecursiveBoundaryContext] using
    prbFamilyContext_eq

theorem prbConstructorCandidateContext_eq :
    prbCandidate.families.singleton.constructors.singleton.type.context =
      prbConstructorContext := by
  have h := prbExecution.families.produced.singleton_constructors
    |>.singleton_context_eq
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    prbConstructorContext] using h

/-- The retained singleton family spine selects exactly its first generated
local as the sole kernel parameter.  This is derived from the structural
identity witness, not by evaluating the opaque outer producer again. -/
theorem prbStatsParams_eq :
    prbFamilyValidationRun.stats.params =
      #[prbFamilyContext.freshExpr] := by
  rw [prbFamilyValidationRun.stats_eq]
  change
    (prbCandidate.families.singleton.familyType.type.trace.parameterList 1).toArray =
      #[prbFamilyContext.freshExpr]
  have identity := prbFamilyIdentityEvidence.identity
  have spineLength := prbFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    prbCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [prbFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      simp only [AddInductive.CandidateExprTrace.parameterList]
      rw [prbFamilyCandidateContext_eq]

theorem prbFamilyPrefix_ne :
    prbFamilyContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def prbFamilyContextRun :
    TypeChecker.CandidateContextRun prbFamilyContext :=
  TypeChecker.CandidateContextRun.root prbEmptyVEnvsWF rfl
    prbFamilyPrefix_ne

def prbPreFamilyStage :
    TypeChecker.CandidateSemanticStage prbFamilyContext VEnv.empty [`u] where
  contextRun := prbFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem prbRawFamily_isType :
    VEnv.empty.IsType 1 [] propRecursiveBoundaryType.type := by
  change VEnv.empty.IsType 1 []
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0) (.sort .zero)))
  apply VEnv.IsType.forallE
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · apply VEnv.IsType.forallE
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem prbFamilySource_tr :
    TrExprS VEnv.empty [`u] [] propRecursiveBoundaryKernelType.type
      propRecursiveBoundaryType.type := by
  have shape : TrTypeExpr VEnv.empty [`u] []
      propRecursiveBoundaryKernelType.type
      propRecursiveBoundaryType.type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := prbRawFamily_isType
  exact shape.to_trExprS .empty trivial ⟨.sort level, type⟩

theorem prbStatsNindices_eq :
    prbFamilyValidationRun.stats.nindices = #[1] := by
  rw [prbFamilyValidationRun.stats_eq]
  change #[prbCandidate.families.singleton.familyType.type.trace.spineLength -
    1] = #[1]
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]

theorem prbFamilyNames_eq :
    propRecursiveBoundaryKernelType.name =
      propRecursiveBoundaryType.name := by
  decide

theorem prbFamilyNameAbsent :
    propRecursiveBoundaryContext.env.contains
      propRecursiveBoundaryKernelType.name = false := by
  change ({} : ConstMap).contains
    propRecursiveBoundaryKernelType.name = false
  rw [SMap.find?_isSome,
    SMap.WF.find?_eq SMap.WF.empty]
  simp [SMap.toList']

theorem prbFamilyNameNotPrimitive :
    Kernel.Environment.primitives.contains
      propRecursiveBoundaryKernelType.name = false := by
  simp [propRecursiveBoundaryKernelType,
    propRecursiveBoundaryInfo, Kernel.Environment.primitives,
    NameSet.ofList]
  simp +decide [NameSet.contains]

def prbDeclaredInfo : ConstantInfo :=
  .inductInfo <| AddInductive.singletonDeclaredInfo
    prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
    0 false
    prbCandidate.families.singleton.familyType.type.trace.terminalContext

theorem prbFamilyMap_add :
    prbExecution.familyEnv.constants =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        propRecursiveBoundaryType.name prbDeclaredInfo := by
  have h := prbExecution.declareRun
  rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
  rw [← prbFamilyNames_eq]
  simpa [prbDeclaredInfo] using
    AddInductive.declareInductiveTypes_singleton_constants
      prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
      0 false
      prbCandidate.families.singleton.familyType.type.trace.terminalContext
      prbExecution.familyEnv prbStatsNindices_eq h

def prbTypeEnv : VEnv :=
  (VEnv.empty.addConst propRecursiveBoundaryType.name
    propRecursiveBoundaryType.toVConstant).get!

theorem prbTypeEnv_add :
    VEnv.empty.addConst propRecursiveBoundaryType.name
        propRecursiveBoundaryType.toVConstant = some prbTypeEnv := by
  rfl

theorem prbTerminalLparams_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
      propRecursiveBoundaryContext.lparams := by
  calc
    _ = prbCandidate.families.singleton.familyType.type.context.lparams :=
      prbCandidate.families.singleton.familyType.type.trace.terminalContext_lparams
    _ = prbFamilyContext.lparams :=
      congrArg AddInductive.Context.lparams prbFamilyCandidateContext_eq
    _ = propRecursiveBoundaryContext.lparams := rfl

theorem prbTerminalEnv_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext.env =
      propRecursiveBoundaryContext.env := by
  calc
    _ = prbCandidate.families.singleton.familyType.type.context.env :=
      prbCandidate.families.singleton.familyType.type.trace.terminalContext_env
    _ = prbFamilyContext.env :=
      congrArg AddInductive.Context.env prbFamilyCandidateContext_eq
    _ = propRecursiveBoundaryContext.env := rfl

theorem prbDeclaredInfo_tr :
    TrConstVal .safe VEnv.empty prbDeclaredInfo
      propRecursiveBoundaryType.toVConstVal := by
  refine ⟨⟨by decide, ?_, ?_⟩, rfl⟩
  · change
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams.length =
        propRecursiveBoundaryType.uvars
    rw [prbTerminalLparams_eq]
    rfl
  · change TrExprS VEnv.empty
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
      [] propRecursiveBoundaryKernelType.type propRecursiveBoundaryType.type
    rw [prbTerminalLparams_eq]
    exact prbFamilySource_tr

def prbAddType :
    AddInductConstant .induct prbFamilyContext.env.constants VEnv.empty
      propRecursiveBoundaryType.toVConstVal
      prbConstructorContext.env.constants prbTypeEnv where
  info := prbDeclaredInfo
  kind_eq := by simp [prbDeclaredInfo, InductConstantKind.Matches]
  tr := prbDeclaredInfo_tr
  map_fresh := by
    change ({} : ConstMap).find?
      propRecursiveBoundaryType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  env_add := prbTypeEnv_add
  map_add := by
    simpa [prbFamilyContext, prbConstructorContext,
      prbTerminalEnv_eq] using prbFamilyMap_add

theorem prbFamilyWhnfDepth :
    prbCandidate.families.singleton.familyType.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [prbFamilyCandidateContext_eq]
  rfl

def prbFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate.families.singleton.familyType
      propRecursiveBoundaryType prbPreFamilyStage where
  name_eq := prbFamilyNames_eq
  uvars_eq := rfl
  type := {
    context_eq := prbFamilyCandidateContext_eq.symm
    source_tr := prbFamilySource_tr
    whnfFuel := 9999
    whnfDepth := prbFamilyWhnfDepth }
  validation := prbFamilyValidationRun
  typeEnv := prbTypeEnv
  addInduct := prbAddType
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := by
    have h := prbExecution.declareRun
    rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
    simpa [prbConstructorContext, prbFamilyContext,
      prbTerminalEnv_eq] using
      AddInductive.declareInductiveTypes_singleton_quotInit
        prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
        0 false
        prbCandidate.families.singleton.familyType.type.trace.terminalContext
        prbExecution.familyEnv prbStatsNindices_eq h
  name_not_reflected := by decide
  name_not_primitive := by
    rw [← prbFamilyNames_eq]
    exact prbFamilyNameNotPrimitive

def prbCtorAlphaContext := prbConstructorContext.pushLocalDecl `α .implicit
  (.sort (.succ (.param `u)))

def prbCtorAContext := prbCtorAlphaContext.pushLocalDecl `a .default
  prbConstructorContext.freshExpr

def prbCtorNextDomain : Expr :=
  .forallE `b prbConstructorContext.freshExpr
    (.app
      (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
        (.fvar prbConstructorContext.freshFVarId))
      (.bvar 0)) .default

def prbCtorNextContext := prbCtorAContext.pushLocalDecl `next .default
  prbCtorNextDomain

def prbCtorBContext := prbCtorAContext.pushLocalDecl `b .default
  prbConstructorContext.freshExpr

theorem prbCtorFamilyLookup :
    prbConstructorContext.env.find?
        propRecursiveBoundaryKernelType.name =
      some prbDeclaredInfo := by
  change prbExecution.familyEnv.constants.find?'
      propRecursiveBoundaryKernelType.name = some prbDeclaredInfo
  rw [show prbExecution.familyEnv.constants =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        propRecursiveBoundaryType.name prbDeclaredInfo from prbFamilyMap_add]
  have hbase :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.WF := by
    rw [prbTerminalEnv_eq]
    exact SMap.WF.empty
  have hfresh :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.find?
        propRecursiveBoundaryType.name = none := by
    rw [prbTerminalEnv_eq]
    change ({} : ConstMap).find? propRecursiveBoundaryType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  have hinsert := hbase.insert propRecursiveBoundaryType.name
    prbDeclaredInfo hfresh
  rw [SMap.WF.find?'_eq_find? hinsert]
  rw [hbase.find?_insert]
  simp [prbFamilyNames_eq]

theorem prbCtorFamilyWhnf
    (context : AddInductive.Context)
    (arg1 arg2 : FVarId)
    (henv : context.env = prbConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar arg1))
          (.fvar arg2),
        .app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar arg1))
          (.fvar arg2)⟩ := by
  apply TypeChecker.candidateWhnfConstFVarFVar_refl context
    propRecursiveBoundaryKernelType.name [.param `u] arg1 arg2
    (AddInductive.singletonDeclaredInfo
      prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
      0 false
      prbCandidate.families.singleton.familyType.type.trace.terminalContext)
  · exact hdepth
  · exact hwhnf
  · exact hquot
  · rw [henv]
    simpa [prbDeclaredInfo] using prbCtorFamilyLookup
  · rfl

theorem prbCtorRootWF : prbConstructorContext.lctx.WF := by
  change LocalContext.WF ⟨.empty, .empty, .empty⟩
  exact LocalContext.WF.nil

theorem prbCtorRootFresh :
    prbConstructorContext.lctx.find?
      prbConstructorContext.freshFVarId = none := by
  change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
    prbConstructorContext.freshFVarId = none
  exact TypeChecker.emptyLocalContextFindNone _

theorem prbCtorAlphaContextWF : prbCtorAlphaContext.lctx.WF := by
  simpa [prbCtorAlphaContext, AddInductive.Context.pushLocalDecl] using
    (LocalContext.WF.mkLocalDecl prbCtorRootWF prbCtorRootFresh)

theorem prbCtorAlphaContextFresh :
    prbCtorAlphaContext.lctx.find?
      prbCtorAlphaContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := prbCtorAlphaContext.freshFVarId) prbCtorAlphaContextWF
  rw [h]
  simp only [prbCtorAlphaContext, prbConstructorContext,
    propRecursiveBoundaryContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]

theorem prbCtorAlphaFindInA :
    prbCtorAContext.lctx.find? prbConstructorContext.freshFVarId =
      some (.cdecl 0 prbConstructorContext.freshFVarId `α
        (.sort (.succ (.param `u))) .implicit .default) := by
  have hnew := TypeChecker.localContextFindNew
    prbConstructorContext.lctx prbConstructorContext.freshFVarId
    `α (.sort (.succ (.param `u))) .implicit .default
    prbCtorRootWF prbCtorRootFresh
  have hold := TypeChecker.localContextFindOld
      prbCtorAlphaContext.lctx prbConstructorContext.freshFVarId
      prbCtorAlphaContext.freshFVarId `a
      prbConstructorContext.freshExpr .default .default
      (.cdecl prbConstructorContext.lctx.decls.size
        prbConstructorContext.freshFVarId `α
        (.sort (.succ (.param `u))) .implicit .default)
      prbCtorAlphaContextWF prbCtorAlphaContextFresh (by
        simpa [prbCtorAlphaContext, AddInductive.Context.pushLocalDecl]
          using hnew)
  simpa [prbCtorAContext, prbCtorAlphaContext,
    prbConstructorContext, propRecursiveBoundaryContext,
    AddInductive.Context.pushLocalDecl] using hold

open TypeChecker in
def prbCtorIdentityShape :
    CandidateExprIdentityReplay.Shaped prbConstructorContext
      propRecursiveBoundaryKernelCtor.type 3
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
  change CandidateExprIdentityReplay.Shaped prbConstructorContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE `a (.bvar 0)
        (.forallE `next
          (.forallE `b (.bvar 1)
            (.app
              (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
                (.bvar 2))
              (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.bvar 2))
            (.bvar 1)) .default) .default) .implicit)
    3
    (.app
      (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
        (.fvar prbConstructorContext.freshFVarId))
      (.fvar prbCtorAlphaContext.freshFVarId))
  have alphaInAlpha : AddInductive.CandidateWhnfStep.Valid
      ⟨prbCtorAlphaContext, prbConstructorContext.freshExpr,
        prbConstructorContext.freshExpr⟩ := by
    simpa [prbCtorAlphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        prbConstructorContext `α (.sort (.succ (.param `u)))
        .implicit 9999 (by rfl) prbCtorRootWF prbCtorRootFresh
  have alphaInA : AddInductive.CandidateWhnfStep.Valid
      ⟨prbCtorAContext, prbConstructorContext.freshExpr,
        prbConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [prbCtorAlphaFindInA]
  have bBody : CandidateExprIdentityReplay.Shaped prbCtorBContext
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId))
      0
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId)) :=
    .terminal _ _ (prbCtorFamilyWhnf _ _ _ rfl rfl rfl (by
      rw [show prbCtorBContext.env = prbConstructorContext.env by rfl]
      rw [prbFamilyStage.quotInit_eq]
      rfl)) rfl
  have nextDomainShape : CandidateExprIdentityReplay.Shaped prbCtorAContext
      prbCtorNextDomain 1
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt prbCtorAContext `b
      prbConstructorContext.freshExpr
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.bvar 0)) .default (by rfl)
    · simpa [AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbConstructorContext.freshExpr).symm
    · exact (CandidateExprIdentityReplay.Shaped.terminal
        _ _ alphaInA rfl).replay
    · simpa [prbCtorBContext, prbCtorNextDomain,
        AddInductive.Context.freshExpr,
        Expr.instantiate1_eq, Expr.instantiate1'] using bBody
  have resultShape : CandidateExprIdentityReplay.Shaped prbCtorNextContext
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId))
      0
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) :=
    .terminal _ _ (prbCtorFamilyWhnf _ _ _ rfl rfl rfl (by
      rw [show prbCtorNextContext.env = prbConstructorContext.env by rfl]
      rw [prbFamilyStage.quotInit_eq]
      rfl)) rfl
  have nextShape : CandidateExprIdentityReplay.Shaped prbCtorAContext
      (.forallE `next prbCtorNextDomain
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar prbConstructorContext.freshFVarId))
          (.fvar prbCtorAlphaContext.freshFVarId)) .default)
      1
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt
      prbCtorAContext `next prbCtorNextDomain
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) .default (by rfl)
    · simpa [prbCtorNextDomain,
          AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbCtorNextDomain).symm
    · exact nextDomainShape.replay
    · simpa [prbCtorNextContext, Expr.instantiate1_eq,
        Expr.instantiate1'] using resultShape
  have aShape : CandidateExprIdentityReplay.Shaped prbCtorAlphaContext
      (.forallE `a prbConstructorContext.freshExpr
        (.forallE `next
          (.forallE `b prbConstructorContext.freshExpr
            (.app
              (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
                (.fvar prbConstructorContext.freshFVarId))
              (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 1)) .default) .default)
      2
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt
      prbCtorAlphaContext `a
      prbConstructorContext.freshExpr
      (.forallE `next
        (.forallE `b prbConstructorContext.freshExpr
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 1)) .default) .default (by rfl)
    · simpa [AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbConstructorContext.freshExpr).symm
    · exact (CandidateExprIdentityReplay.Shaped.terminal
        _ _ alphaInAlpha rfl).replay
    · simpa [prbCtorAContext, prbCtorNextDomain,
        AddInductive.Context.freshExpr,
        Expr.instantiate1_eq, Expr.instantiate1',
        Expr.liftLooseBVars_zero] using nextShape
  apply CandidateExprIdentityReplay.Shaped.forallEBuilt
    prbConstructorContext `α
    (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `next
        (.forallE `b (.bvar 1)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.bvar 2))
            (.bvar 0)) .default)
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.bvar 2))
          (.bvar 1)) .default) .default) .implicit (by rfl)
  · simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
      (AddInductive.CandidateTypeAnnotationTrace.build_consumed
        (.sort (.succ (.param `u)))).symm
  · exact (CandidateExprIdentityReplay.Shaped.terminal
      _ _ (by rfl) rfl).replay
  · simpa [prbCtorAlphaContext, Expr.instantiate1_eq,
      Expr.instantiate1', Expr.liftLooseBVars_zero,
      AddInductive.Context.freshExpr] using aShape

theorem prbCtorCandidateBuild :
    AddInductive.buildCandidateExpr propRecursiveBoundaryKernelCtor.type
        prbConstructorContext =
      .ok prbCandidate.families.singleton.constructors.singleton.type := by
  have produced := prbExecution.families.produced.singleton_constructors
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.families.candidates.singleton.constructors] at produced
  have exactProduced : AddInductive.CandidateConstructorListProduced
      prbConstructorContext
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) := by
    simpa [prbCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      prbConstructorContext, propRecursiveBoundaryKernelType] using produced
  exact exactProduced.singleton_build

def prbCtorIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay prbConstructorContext
      propRecursiveBoundaryKernelCtor.type :=
  prbCtorIdentityShape.replay

def prbCtorIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      prbCtorIdentityReplay
      prbCandidate.families.singleton.constructors.singleton.type.trace :=
  prbCtorIdentityReplay.evidence_of_build prbCtorCandidateBuild

/-- The structurally identity-normalizing constructor candidate reconstructs
the exact closed kernel constructor type.  In particular, later alignment can
inspect the retained view without a separate computation oracle. -/
theorem prbCtorView_eq :
    prbCandidate.families.singleton.constructors.singleton.type.view =
      propRecursiveBoundaryKernelCtor.type := by
  apply prbCtorIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [prbConstructorCandidateContext_eq]
    rfl
  · rw [prbConstructorCandidateContext_eq]
    simp [propRecursiveBoundaryKernelCtor,
      propRecursiveBoundaryMkInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar']

theorem prbCtorIdentityReplay_shape :
    prbCtorIdentityReplay.spineLength = 3 ∧
      prbCtorIdentityReplay.terminalSource =
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar prbConstructorContext.freshFVarId))
          (.fvar prbCtorAlphaContext.freshFVarId)) :=
  ⟨prbCtorIdentityShape.spineLength_eq,
    prbCtorIdentityShape.terminalSource_eq⟩

theorem prbTypeEnv_ordered : prbTypeEnv.Ordered :=
  .const (n := propRecursiveBoundaryType.name)
    (ci := propRecursiveBoundaryType.toVConstant)
    .empty prbRawFamily_isType prbTypeEnv_add

theorem prbRawCtor_isType :
    prbTypeEnv.IsType 1 [] propRecursiveBoundaryType.ctors[0].type := by
  have hFamily : prbTypeEnv.constants propRecursiveBoundaryType.name =
      some propRecursiveBoundaryType.toVConstant :=
    VEnv.addConst_self prbTypeEnv_add
  exact ⟨_, by type_tac⟩

theorem prbCtorSource_tr :
    TrExprS prbTypeEnv [`u] [] propRecursiveBoundaryKernelCtor.type
      propRecursiveBoundaryType.ctors[0].type := by
  have shape : TrTypeExpr prbTypeEnv [`u] []
      propRecursiveBoundaryKernelCtor.type
      propRecursiveBoundaryType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := prbRawCtor_isType
  exact shape.to_trExprS prbTypeEnv_ordered trivial ⟨.sort level, type⟩

theorem prbCtorNames_eq :
    propRecursiveBoundaryKernelCtor.name =
      propRecursiveBoundaryType.ctors[0].name := by
  decide

theorem prbCtorWhnfDepth :
    prbCandidate.families.singleton.constructors.singleton.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [prbConstructorCandidateContext_eq]
  rfl

theorem prbRawCtors_eq :
    propRecursiveBoundaryType.ctors =
      [propRecursiveBoundaryType.ctors[0]] := by
  rfl

def prbCtorStagedInput :
    VInductDecl.CandidateConstructorStagedInput
      prbFamilyStage.postFamily
      prbCandidate.families.singleton.constructors.singleton
      propRecursiveBoundaryType.ctors[0] where
  name_eq := prbCtorNames_eq
  uvars_eq := rfl
  type := {
    context_eq := prbConstructorCandidateContext_eq.symm
    source_tr := prbCtorSource_tr
    whnfFuel := 9999
    whnfDepth := prbCtorWhnfDepth }

def prbConstructorsStage :
    VInductDecl.CandidateConstructorStagedListInput
      prbFamilyStage.postFamily
      prbCandidate.families.singleton.constructors
      propRecursiveBoundaryType.ctors := by
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors, prbRawCtors_eq]
  exact .cons prbCtorStagedInput .nil

theorem prbFamilyTypesProduced :
    AddInductive.CandidateFamilyTypeListProduced prbFamilyContext
      (.cons prbCandidate.families.singleton.familyType .nil) := by
  have h := prbExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.familyTypes.candidates] at h
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate, prbFamilyContext,
    AddInductive.NormalizationCandidateExecution.candidate] using h

theorem prbFamiliesProduced :
    AddInductive.CandidateFamilyListProduced prbConstructorContext
      (.cons prbCandidate.families.singleton.familyType .nil)
      prbCandidate.families := by
  simpa [prbCandidate, prbConstructorContext,
    AddInductive.NormalizationCandidateExecution.candidate] using
    prbExecution.families.produced.singleton_reindex

theorem prbCheckConstructorsRun :
    AddInductive.checkConstructors #[propRecursiveBoundaryKernelType]
        prbFamilyValidationRun.stats false
        { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := prbConstructorContext.env } = .ok () := by
  have h := prbExecution.constructorRun
  rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
  simpa [prbConstructorContext] using h

theorem prbUniverseRun :
    AddInductive.checkConstructorUniverseListSemantics
        prbFamilyValidationRun.stats propRecursiveBoundaryKernelType.ctors
        { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := prbConstructorContext.env } = .ok () := by
  let validation : AddInductive.ConstructorValidationRun
      propRecursiveBoundaryKernelType prbFamilyValidationRun.stats false
      { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := prbConstructorContext.env } :=
    AddInductive.ConstructorValidationRun.of_run prbCheckConstructorsRun
  apply validation.trace.universeRun_of_semantics
  apply validation.trace.universeSemantics_of_resultLevel_isZero
  rfl

def prbValidationAlphaContext : AddInductive.Context :=
  prbFamilyContext.pushLocalDecl `α .default (.sort (.succ (.param `u)))

def prbValidationAName : Name :=
  propRecursiveBoundaryKernelType.type.bindingBody!.bindingName!

def prbValidationFamilyContext : AddInductive.Context :=
  prbValidationAlphaContext.pushLocalDecl prbValidationAName .default
    prbFamilyContext.freshExpr

theorem prbFamilyTerminalContext_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      prbValidationFamilyContext := by
  have identity := prbFamilyIdentityEvidence.identity
  have spineLength := prbFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    prbCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [prbFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      simp only [AddInductive.CandidateExprTrace.spineLength,
        AddInductive.CandidateExprTrace.terminalContext]
      cases bodyIdentity with
      | terminal result_eq =>
          simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
          rw [prbFamilyIdentityReplay_shape.1] at spineLength
          omega
      | forallE domainCandidate' bodyCandidate' source_eq' consumed_eq'
          domainIdentity' bodyIdentity' =>
          cases bodyIdentity' with
          | terminal result_eq =>
              simp only [AddInductive.CandidateExprTrace.terminalContext]
              simp [propRecursiveBoundaryKernelType,
                propRecursiveBoundaryInfo, ConstantInfo.type,
                ConstantInfo.toConstantVal] at source_eq
              rcases source_eq with ⟨rfl, rfl, rfl, rfl⟩
              simp [Expr.instantiate1_eq, Expr.instantiate1'] at source_eq'
              rcases source_eq' with ⟨rfl, rfl, rfl, rfl⟩
              rw [consumed_eq, consumed_eq', prbFamilyCandidateContext_eq]
              rfl
          | forallE domainCandidate'' bodyCandidate'' source_eq'' consumed_eq''
              domainIdentity'' bodyIdentity'' =>
              simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
              rw [prbFamilyIdentityReplay_shape.1] at spineLength
              omega

def prbConstructorValidationContext : AddInductive.Context :=
  { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
    env := prbConstructorContext.env }

theorem prbConstructorValidationContext_eq :
    prbConstructorValidationContext =
      { prbValidationFamilyContext with env := prbConstructorContext.env } := by
  rw [prbConstructorValidationContext, prbFamilyTerminalContext_eq]

def prbValidationAlphaLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationAlphaContext :=
  (TypeChecker.CandidateLocalContextRun.empty prbFamilyContext rfl).push
    `α .default (.sort (.succ (.param `u)))

def prbValidationFamilyLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationFamilyContext :=
  prbValidationAlphaLocalRun.push prbValidationAName .default
    prbFamilyContext.freshExpr

def prbValidationRootContext : AddInductive.Context :=
  { prbValidationFamilyContext with env := prbConstructorContext.env }

def prbValidationRootLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationRootContext where
  wf := prbValidationFamilyLocalRun.wf
  reserves := prbValidationFamilyLocalRun.reserves

def prbValidationAlphaId : FVarId := prbFamilyContext.freshFVarId
def prbValidationAlpha : Expr := prbFamilyContext.freshExpr
def prbValidationIndexId : FVarId := prbValidationAlphaContext.freshFVarId

theorem prbValidationAlphaFind :
    prbValidationRootContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  have first :=
    (TypeChecker.CandidateLocalContextRun.empty prbFamilyContext rfl).push_findNew
      `α .default (.sort (.succ (.param `u)))
  have old := prbValidationAlphaLocalRun.push_findOld
    prbValidationAName .default prbFamilyContext.freshExpr first
  simpa [prbValidationRootContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbValidationAlphaId, prbFamilyContext,
    propRecursiveBoundaryContext, AddInductive.Context.pushLocalDecl] using old

theorem prbValidationIndexFind :
    prbValidationRootContext.lctx.find? prbValidationIndexId =
      some (.cdecl prbValidationAlphaContext.lctx.decls.size
        prbValidationIndexId prbValidationAName
        prbValidationAlpha .default .default) := by
  have found := prbValidationAlphaLocalRun.push_findNew
    prbValidationAName .default prbFamilyContext.freshExpr
  simpa [prbValidationRootContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbValidationIndexId, prbValidationAlpha,
    prbValidationAlphaId, prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr] using found

theorem prbCandidateCheckTypeFVar
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (hdepth : context.fuel.recDepth = 10000)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .fvar id, type⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.checkType (.fvar id)) =
      .ok type
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State)) = .ok type
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker, hfind,
    LocalDecl.type, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

@[simp] theorem prbValidationAlpha_shape :
    prbValidationAlpha = .fvar prbValidationAlphaId := by
  rfl

theorem prbValidationGetTypeAlpha :
    AddInductive.getType prbValidationAlpha prbValidationRootContext =
      .ok (.sort (.succ (.param `u))) := by
  unfold AddInductive.getType
  simp only [getLCtx, ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((prbValidationRootContext.lctx.get!
    prbValidationAlpha.fvarId!).type) = _
  rw [show prbValidationAlpha.fvarId! = prbValidationAlphaId by
    rw [prbValidationAlpha_shape]
    rfl]
  simp [LocalContext.get!, prbValidationAlphaFind, LocalDecl.type]

@[simp] theorem prbValidationCheckLevelSuccParam :
    TypeChecker.Inner.checkLevel prbValidationRootContext.toTypeChecker
      (.succ (.param `u)) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, prbValidationRootContext,
    prbValidationFamilyContext, prbValidationAlphaContext,
    prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.toTypeChecker, Level.getUndefParam,
    Level.forEach, Level.hasParam_eq, Level.hasParam']
  rfl

theorem prbValidationSortCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationRootContext, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run prbValidationRootContext.env
    prbValidationRootContext.safety prbValidationRootContext.lctx
    prbValidationRootContext.lparams prbValidationRootContext.fuel
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationRootContext.toTypeChecker
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    prbValidationCheckLevelSuccParam, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

def prbValidationSortChecked : AddInductive.ConstructorCheckedExpr
    prbValidationRootContext (.sort (.succ (.param `u))) :=
  .ofRun (by simp [FVarsIn, Level.hasMVar']) prbValidationSortCheckValid

def prbValidationFamilyApp (arg : Expr) : Expr :=
  .app
    (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
      prbValidationAlpha)
    arg

def prbValidationNextDomain : Expr :=
  .forallE `b prbValidationAlpha
    (prbValidationFamilyApp (.bvar 0)) .default

def prbValidationAfterParam : Expr :=
  .forallE `a prbValidationAlpha
    (.forallE `next prbValidationNextDomain
      (prbValidationFamilyApp (.bvar 1)) .default) .default

def prbValidationAId : FVarId := prbValidationRootContext.freshFVarId
def prbValidationAExpr : Expr := prbValidationRootContext.freshExpr
def prbValidationAContext : AddInductive.Context :=
  prbValidationRootContext.pushLocalDecl `a .default prbValidationAlpha

def prbValidationAfterA : Expr :=
  .forallE `next prbValidationNextDomain
    (prbValidationFamilyApp prbValidationAExpr) .default

def prbValidationNextContext : AddInductive.Context :=
  prbValidationAContext.pushLocalDecl `next .default prbValidationNextDomain

def prbValidationBId : FVarId := prbValidationAContext.freshFVarId
def prbValidationBExpr : Expr := prbValidationAContext.freshExpr
def prbValidationBContext : AddInductive.Context :=
  prbValidationAContext.pushLocalDecl `b .default prbValidationAlpha

@[simp] theorem prbValidationAExpr_shape :
    prbValidationAExpr = .fvar prbValidationAId := by
  rfl

@[simp] theorem prbValidationBExpr_shape :
    prbValidationBExpr = .fvar prbValidationBId := by
  rfl

def prbValidationTerminal : Expr :=
  prbValidationFamilyApp prbValidationAExpr

def prbValidationTarget : Expr :=
  prbValidationFamilyApp prbValidationBExpr

theorem prbValidationAfterParam_shape :
    (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
      prbValidationAlpha) = prbValidationAfterParam := by
  simp [propRecursiveBoundaryKernelCtor, propRecursiveBoundaryMkInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    prbValidationAfterParam, prbValidationNextDomain,
    prbValidationFamilyApp, prbValidationAlpha,
    prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.freshExpr,
    propRecursiveBoundaryKernelType, propRecursiveBoundaryInfo,
    ConstantInfo.name,
    TypeChecker.candidateLiftLooseBVarsFVar,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero]

theorem prbValidationAfterA_shape :
    prbValidationAfterParam.bindingBody!.instantiate1
      prbValidationAExpr = prbValidationAfterA := by
  simp [prbValidationAfterParam, prbValidationAfterA,
    prbValidationNextDomain, prbValidationTerminal,
    prbValidationFamilyApp, prbValidationAExpr,
    prbValidationRootContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbFamilyContext,
    propRecursiveBoundaryContext, AddInductive.Context.freshExpr,
    TypeChecker.candidateLiftLooseBVarsFVar,
    Expr.bindingBody!,
    Expr.instantiate1_eq, Expr.instantiate1']

theorem prbValidationTerminal_shape :
    prbValidationAfterA.bindingBody!.instantiate1
      prbValidationAContext.freshExpr = prbValidationTerminal := by
  simp [prbValidationAfterA, prbValidationTerminal,
    prbValidationFamilyApp, prbValidationAExpr,
    prbValidationRootContext, prbValidationAContext,
    prbValidationFamilyContext, prbValidationAlphaContext,
    prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.freshExpr,
    TypeChecker.candidateInstantiateFVar,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem prbValidationTarget_shape :
    prbValidationNextDomain.bindingBody!.instantiate1
      prbValidationBExpr = prbValidationTarget := by
  simp [prbValidationNextDomain, prbValidationTarget,
    prbValidationFamilyApp, Expr.bindingBody!,
    Expr.instantiate1_eq, Expr.instantiate1']

def prbValidationALocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationAContext :=
  prbValidationRootLocalRun.push `a .default prbValidationAlpha

def prbValidationNextLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationNextContext :=
  prbValidationALocalRun.push `next .default prbValidationNextDomain

def prbValidationBLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationBContext :=
  prbValidationALocalRun.push `b .default prbValidationAlpha

theorem prbValidationAlphaFindInA :
    prbValidationAContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationRootLocalRun.push_findOld `a .default prbValidationAlpha
    prbValidationAlphaFind

theorem prbValidationAlphaFindInNext :
    prbValidationNextContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationALocalRun.push_findOld `next .default
    prbValidationNextDomain prbValidationAlphaFindInA

theorem prbValidationAlphaFindInB :
    prbValidationBContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationALocalRun.push_findOld `b .default prbValidationAlpha
    prbValidationAlphaFindInA

theorem prbValidationAFind :
    prbValidationAContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
  simpa [prbValidationAContext, prbValidationAId, prbValidationAExpr] using
    prbValidationRootLocalRun.push_findNew `a .default prbValidationAlpha

theorem prbValidationAFindInNext :
    prbValidationNextContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) :=
  prbValidationALocalRun.push_findOld `next .default
    prbValidationNextDomain prbValidationAFind

theorem prbValidationAFindInB :
    prbValidationBContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) :=
  prbValidationALocalRun.push_findOld `b .default prbValidationAlpha
    prbValidationAFind

theorem prbValidationBFind :
    prbValidationBContext.lctx.find? prbValidationBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationBId `b prbValidationAlpha .default .default) := by
  simpa [prbValidationBContext, prbValidationBId, prbValidationBExpr] using
    prbValidationALocalRun.push_findNew `b .default prbValidationAlpha

theorem prbValidationRootFresh :
    prbValidationRootContext.lctx.find?
      prbValidationRootContext.freshFVarId = none :=
  prbValidationRootLocalRun.fresh

theorem prbValidationAFresh :
    prbValidationAContext.lctx.find?
      prbValidationAContext.freshFVarId = none :=
  prbValidationALocalRun.fresh

theorem prbValidationNextFresh :
    prbValidationNextContext.lctx.find?
      prbValidationNextContext.freshFVarId = none :=
  prbValidationNextLocalRun.fresh

theorem prbValidationBFresh :
    prbValidationBContext.lctx.find?
      prbValidationBContext.freshFVarId = none :=
  prbValidationBLocalRun.fresh

theorem prbValidationFamilyGet :
    prbConstructorContext.env.get propRecursiveBoundaryKernelType.name =
      .ok prbDeclaredInfo := by
  unfold Kernel.Environment.get
  rw [prbCtorFamilyLookup]
  rfl

@[simp] theorem prbValidationCheckLevelParam
    (context : AddInductive.Context)
    (hlparams : context.lparams = [`u]) :
    TypeChecker.Inner.checkLevel context.toTypeChecker (.param `u) =
      .ok () := by
  simp [TypeChecker.Inner.checkLevel, AddInductive.Context.toTypeChecker,
    hlparams, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem prbValidationInferConstantFamily
    (context : AddInductive.Context)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferConstant context.toTypeChecker
        propRecursiveBoundaryKernelType.name [.param `u] false =
      .ok propRecursiveBoundaryKernelType.type := by
  unfold TypeChecker.Inner.inferConstant
  simp only [AddInductive.Context.toTypeChecker]
  rw [henv, prbValidationFamilyGet]
  have terminalLparams :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
        [`u] := by
    rw [prbTerminalLparams_eq]
    rfl
  unfold prbDeclaredInfo AddInductive.singletonDeclaredInfo
  rw [terminalLparams]
  have hlevel : TypeChecker.Inner.checkLevel
      ({ env := prbConstructorContext.env
         lctx := context.lctx
         safety := .safe
         lparams := [`u]
         fuel := context.fuel } : TypeChecker.Context)
      (.param `u) = .ok () := by
    simp [TypeChecker.Inner.checkLevel,
      Level.getUndefParam, Level.forEach,
      Level.hasParam_eq, Level.hasParam']
    rfl
  simp [
    propRecursiveBoundaryKernelType, propRecursiveBoundaryInfo,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Syntax.structEq_eq,
    Level.substParams', hsafety, hlparams,
    hlevel, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [Expr.instantiateLevelParamsCore', Level.substParams',
    propRecursiveBoundaryKernelType, propRecursiveBoundaryInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal]

def prbValidationFamilyTail (alpha : Expr) : Expr :=
  .forallE prbValidationAName alpha (.sort .zero) .default

def prbValidationFirstApp (alpha : Expr) : Expr :=
  .app (.const propRecursiveBoundaryKernelType.name [.param `u]) alpha

def prbReplayInsert (state : TypeChecker.State) (source type : Expr) :
    TypeChecker.State :=
  { state with inferTypeC := state.inferTypeC.insert source type }

@[simp] theorem prbEnsureForallExact
    (name : Name) (domain body : Expr) (bi : BinderInfo)
    (source : Expr) (fuel : Nat) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    TypeChecker.Inner.ensureForallCore (.forallE name domain body bi)
      source (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, state) := by
  rfl

theorem prbSelfDefEq (source : Expr) fuel context state :
    TypeChecker.Inner.isDefEq source source
      (TypeChecker.Methods.withFuel fuel) context state = .ok (true, state) := by
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

@[simp] theorem prbConstBeqFVar (name : Name) (levels : List Level)
    (id : FVarId) :
    ((.const name levels : Expr) == .fvar id) = false := by
  change Expr.eqv (.const name levels) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbAppBeqFVar (fn arg : Expr) (id : FVarId) :
    ((.app fn arg : Expr) == .fvar id) = false := by
  change Expr.eqv (.app fn arg) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbFVarBeqConst (id : FVarId) (name : Name)
    (levels : List Level) :
    ((.fvar id : Expr) == .const name levels) = false := by
  change Expr.eqv (.fvar id) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbFVarBeqApp (id : FVarId) (fn arg : Expr) :
    ((.fvar id : Expr) == .app fn arg) = false := by
  change Expr.eqv (.fvar id) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbConstBeqApp (name : Name) (levels : List Level)
    (fn arg : Expr) :
    ((.const name levels : Expr) == .app fn arg) = false := by
  change Expr.eqv (.const name levels) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbAppBeqConst (fn arg : Expr) (name : Name)
    (levels : List Level) :
    ((.app fn arg : Expr) == .const name levels) = false := by
  change Expr.eqv (.app fn arg) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

theorem prbInferAppCoreOf
    (fuel : Nat) (context : TypeChecker.Context)
    (state stateFn stateArg : TypeChecker.State)
    (fn arg domain body : Expr) (name : Name) (bi : BinderInfo)
    (hclosed : (.app fn arg : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[(.app fn arg : Expr)]? = none)
    (hfn : TypeChecker.Inner.inferType' fn false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, stateFn))
    (harg : TypeChecker.Inner.inferType' arg false
      (TypeChecker.Methods.withFuel fuel) context stateFn =
        .ok (domain, stateArg))
    (heager : arg.isAppOfArity ``eagerReduce 2 = false) :
    TypeChecker.Inner.inferType' (.app fn arg) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (body.instantiate1 arg,
          { stateArg with inferTypeC :=
              (stateArg.inferTypeC.insert
                (.app fn arg) (body.instantiate1 arg)) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hfn, harg, heager,
    prbEnsureForallExact, prbSelfDefEq,
    Expr.instantiate1_eq, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem prbInferTypeForallCore
    (fuel : Nat) (context : TypeChecker.Context)
    (state finalState : TypeChecker.State)
    (name : Name) (domain body result : Expr) (bi : BinderInfo)
    (hclosed : (.forallE name domain body bi : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[
      (.forallE name domain body bi : Expr)]? = none)
    (hforall : TypeChecker.Inner.inferForall
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, finalState)) :
    TypeChecker.Inner.inferType'
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, { finalState with inferTypeC :=
          (finalState.inferTypeC.insert
            (.forallE name domain body bi) result) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hforall, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

open private mkLevelIMaxCore mkLevelMaxCore from Lean.Level in
@[simp] theorem prbMkLevelIMaxSuccParamZero :
    mkLevelIMax' (.succ (.param `u)) .zero = .zero := by
  simp [mkLevelIMax', mkLevelIMaxCore, mkLevelMax', mkLevelMaxCore,
    Level.isNeverZero, Level.isZero]

def prbValidationConstState (state : TypeChecker.State) : TypeChecker.State :=
  prbReplayInsert state
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    propRecursiveBoundaryKernelType.type

def prbValidationAlphaState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationConstState state)
    (.fvar alphaId) (.sort (.succ (.param `u)))

def prbValidationFirstAppState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationAlphaState state alphaId)
    (prbValidationFirstApp (.fvar alphaId))
    (prbValidationFamilyTail (.fvar alphaId))

def prbValidationArgumentState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationFirstAppState state alphaId)
    (.fvar argId) (.fvar alphaId)

def prbValidationFamilyAppState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationArgumentState state alphaId argId)
    (prbValidationFamilyApp (.fvar argId)) (.sort .zero)

def prbValidationCachedFirstAppState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationConstState state)
    (prbValidationFirstApp (.fvar alphaId))
    (prbValidationFamilyTail (.fvar alphaId))

def prbValidationCachedArgumentState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationCachedFirstAppState state alphaId)
    (.fvar argId) (.fvar alphaId)

def prbValidationCachedFamilyAppState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationCachedArgumentState state alphaId argId)
    (prbValidationFamilyApp (.fvar argId)) (.sort .zero)

theorem prbWithLocalDeclEq
    {α} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Expr → TypeChecker.RecM α)
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (withLocalDecl (m := TypeChecker.RecM) name bi type k)
        methods context state =
      k (.fvar ⟨state.ngen.curr⟩) methods
        { context with lctx :=
            context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name type bi }
        { state with ngen := state.ngen.next } := by
  rfl

@[simp] theorem prbEnsureSortExact
    (level : Level) (source : Expr) (fuel : Nat)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    TypeChecker.Inner.ensureSortCore (.sort level) source
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.sort level, state) := by
  rfl

def prbValidationNextAlphaState : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State) prbValidationAlpha
    (.sort (.succ (.param `u)))

def prbValidationNextInternalBId : FVarId :=
  ⟨prbValidationNextAlphaState.ngen.curr⟩

def prbValidationNextInternalLctx : LocalContext :=
  prbValidationAContext.lctx.mkLocalDecl prbValidationNextInternalBId `b
    prbValidationAlpha .default

def prbValidationNextInternalContext : AddInductive.Context :=
  { prbValidationAContext with lctx := prbValidationNextInternalLctx }

def prbValidationNextBodyState : TypeChecker.State :=
  { prbValidationNextAlphaState with
    ngen := prbValidationNextAlphaState.ngen.next }

theorem prbValidationNextInternalFresh :
    prbValidationAContext.lctx.find? prbValidationNextInternalBId = none := by
  rw [prbValidationALocalRun.wf.find?_eq_find?_toList,
    List.find?_eq_none]
  intro decl membership equal
  simp only [prbValidationAContext, prbValidationRootContext,
    prbValidationFamilyContext, prbValidationAlphaContext,
    AddInductive.Context.pushLocalDecl,
    LocalContext.mkLocalDecl_toList, List.mem_cons] at membership
  rw [show prbFamilyContext.lctx.toList = [] by rfl] at membership
  simp only [List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl
  all_goals
    simp [LocalDecl.fvarId, prbValidationNextInternalBId,
      prbValidationNextAlphaState, prbReplayInsert,
      prbValidationAlpha, prbValidationAId, prbValidationIndexId,
      prbValidationAlphaId, prbValidationRootContext,
      prbValidationFamilyContext, prbValidationAlphaContext,
      prbFamilyContext, propRecursiveBoundaryContext,
      AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId] at equal
  all_goals injection equal
  all_goals simp [NameGenerator.next] at *

theorem prbValidationAlphaFindInternal :
    prbValidationNextInternalContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  exact TypeChecker.localContextFindOld prbValidationAContext.lctx
    prbValidationAlphaId prbValidationNextInternalBId `b
    prbValidationAlpha .default .default _ prbValidationALocalRun.wf
    prbValidationNextInternalFresh prbValidationAlphaFindInA

theorem prbValidationNextInternalBFind :
    prbValidationNextInternalContext.lctx.find?
        prbValidationNextInternalBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationNextInternalBId `b prbValidationAlpha
        .default .default) := by
  exact TypeChecker.localContextFindNew prbValidationAContext.lctx
    prbValidationNextInternalBId `b prbValidationAlpha .default .default
    prbValidationALocalRun.wf prbValidationNextInternalFresh

theorem prbValidationAlphaNeNextInternalB :
    prbValidationAlphaId ≠ prbValidationNextInternalBId := by
  intro equal
  have fresh := prbValidationNextInternalFresh
  rw [← equal, prbValidationAlphaFindInA] at fresh
  contradiction

theorem prbValidationAlphaNeA :
    prbValidationAlphaId ≠ prbValidationAId := by
  intro equal
  have fresh : prbValidationRootContext.lctx.find?
      prbValidationAId = none := by
    simpa [prbValidationAId] using prbValidationRootFresh
  rw [← equal, prbValidationAlphaFind] at fresh
  contradiction

theorem prbValidationAlphaNeB :
    prbValidationAlphaId ≠ prbValidationBId := by
  intro equal
  have fresh : prbValidationAContext.lctx.find?
      prbValidationBId = none := by
    simpa [prbValidationBId] using prbValidationAFresh
  rw [← equal, prbValidationAlphaFindInA] at fresh
  contradiction

@[simp] theorem prbValidationConsumeAlpha :
    AddInductive.consumeTypeAnnotations prbValidationAlpha =
      prbValidationAlpha := by
  rw [prbValidationAlpha_shape]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem prbValidationConsumeNextDomain :
    AddInductive.consumeTypeAnnotations prbValidationNextDomain =
      prbValidationNextDomain := by
  simp [prbValidationNextDomain,
    AddInductive.consumeTypeAnnotations]

theorem prbValidationInferTypeFamilyCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State)
    (hcache : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (.const propRecursiveBoundaryKernelType.name [.param `u]) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (propRecursiveBoundaryKernelType.type,
        prbValidationConstState state) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    prbValidationConstState, prbReplayInsert,
    prbValidationInferConstantFamily context henv hlparams hsafety,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem prbValidationInferTypeFVarCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (id : FVarId) (type : Expr)
    (hcache : state.inferTypeC[(.fvar id : Expr)]? = none)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (type, prbReplayInsert state (.fvar id) type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker,
    hfind, LocalDecl.type, prbReplayInsert,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem prbValidationInferTypeCachedCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (source type : Expr)
    (hclosed : source.hasLooseBVars = false)
    (hcache : state.inferTypeC[source]? = some type) :
    TypeChecker.Inner.inferType' source false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (type, state) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache]

theorem prbValidationInferFirstAppAlphaCachedCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId : FVarId)
    (halpha : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (hconst : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (happ : state.inferTypeC[
      prbValidationFirstApp (.fvar alphaId)]? = none)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (prbValidationFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationCachedFirstAppState state alphaId) := by
  have constRun := prbValidationInferTypeFamilyCore fuel context state hconst
    henv hlparams hsafety
  have alphaCache : (prbValidationConstState state).inferTypeC[
      (.fvar alphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
    simp only [prbValidationConstState, prbReplayInsert,
      Std.HashMap.getElem?_insert]
    rw [prbConstBeqFVar]
    exact halpha
  have alphaRun := prbValidationInferTypeCachedCore fuel context
    (prbValidationConstState state) (.fvar alphaId)
    (.sort (.succ (.param `u)))
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange']) alphaCache
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (prbValidationConstState state) (prbValidationConstState state)
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE prbValidationAName (.bvar 0) (.sort .zero) .default)
    `α .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange']) happ
    (by simpa [prbValidationAName, propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.bindingBody!,
      Expr.bindingName!] using constRun)
    alphaRun (by rfl)
  simpa [prbValidationCachedFirstAppState,
    prbValidationFirstApp, prbValidationFamilyTail, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationNextBodyInferExists :
    ∃ finalState : TypeChecker.State,
      TypeChecker.Inner.inferType'
          (prbValidationFamilyApp
            (.fvar prbValidationNextInternalBId)) false
          (TypeChecker.Methods.withFuel 9998)
          prbValidationNextInternalContext.toTypeChecker
          prbValidationNextBodyState =
        .ok (.sort .zero, finalState) := by
  have alphaCache : prbValidationNextBodyState.inferTypeC[
      (.fvar prbValidationAlphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
    simp [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert]
  have constMiss : prbValidationNextBodyState.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbFVarBeqConst]
    exact Std.HashMap.getElem?_empty
  have firstMiss : prbValidationNextBodyState.inferTypeC[
      prbValidationFirstApp (.fvar prbValidationAlphaId)]? = none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbValidationFirstApp,
      prbFVarBeqApp]
    exact Std.HashMap.getElem?_empty
  have firstRun : TypeChecker.Inner.inferType'
      (prbValidationFirstApp (.fvar prbValidationAlphaId)) false
      (TypeChecker.Methods.withFuel 9998)
      prbValidationNextInternalContext.toTypeChecker
      prbValidationNextBodyState =
        .ok (prbValidationFamilyTail (.fvar prbValidationAlphaId),
          prbValidationCachedFirstAppState
            prbValidationNextBodyState prbValidationAlphaId) := by
    apply prbValidationInferFirstAppAlphaCachedCore
    · exact alphaCache
    · exact constMiss
    · exact firstMiss
    · rfl
    · rfl
    · rfl
  have idBeq : ((.fvar prbValidationAlphaId : Expr) ==
      .fvar prbValidationNextInternalBId) = false := by
    change Expr.eqv (.fvar prbValidationAlphaId)
      (.fvar prbValidationNextInternalBId) = false
    rw [Expr.eqv_eq]
    simp [Expr.eqv', prbValidationAlphaNeNextInternalB]
  have argMiss : (prbValidationCachedFirstAppState
      prbValidationNextBodyState prbValidationAlphaId).inferTypeC[
        (.fvar prbValidationNextInternalBId : Expr)]? = none := by
    simp only [prbValidationCachedFirstAppState,
      prbValidationConstState, prbValidationNextBodyState,
      prbValidationNextAlphaState, prbReplayInsert,
      Std.HashMap.getElem?_insert]
    rw [prbValidationFirstApp, prbAppBeqFVar, prbConstBeqFVar,
      prbValidationAlpha_shape, idBeq]
    exact Std.HashMap.getElem?_empty
  have argRun : TypeChecker.Inner.inferType'
      (.fvar prbValidationNextInternalBId) false
      (TypeChecker.Methods.withFuel 9998)
      prbValidationNextInternalContext.toTypeChecker
      (prbValidationCachedFirstAppState
        prbValidationNextBodyState prbValidationAlphaId) =
        .ok (.fvar prbValidationAlphaId,
          prbValidationCachedArgumentState prbValidationNextBodyState
            prbValidationAlphaId prbValidationNextInternalBId) := by
    simpa [prbValidationCachedArgumentState,
      prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998
        prbValidationNextInternalContext
        (prbValidationCachedFirstAppState
          prbValidationNextBodyState prbValidationAlphaId)
        prbValidationNextInternalBId (.fvar prbValidationAlphaId)
        argMiss prbValidationNextInternalBFind
  have appMiss : prbValidationNextBodyState.inferTypeC[
      prbValidationFamilyApp
        (.fvar prbValidationNextInternalBId)]? = none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbValidationFamilyApp,
      prbFVarBeqApp]
    exact Std.HashMap.getElem?_empty
  have appRun := prbInferAppCoreOf 9998
    prbValidationNextInternalContext.toTypeChecker
    prbValidationNextBodyState
    (prbValidationCachedFirstAppState
      prbValidationNextBodyState prbValidationAlphaId)
    (prbValidationCachedArgumentState prbValidationNextBodyState
      prbValidationAlphaId prbValidationNextInternalBId)
    (prbValidationFirstApp (.fvar prbValidationAlphaId))
    (.fvar prbValidationNextInternalBId)
    (.fvar prbValidationAlphaId) (.sort .zero)
    prbValidationAName .default
    (by simp [prbValidationFamilyApp, prbValidationFirstApp,
      Expr.hasLooseBVars, Expr.looseBVarRange'])
    appMiss firstRun argRun (by rfl)
  refine ⟨prbValidationCachedFamilyAppState prbValidationNextBodyState
    prbValidationAlphaId prbValidationNextInternalBId, ?_⟩
  simpa [prbValidationFamilyApp, prbValidationFirstApp,
    prbValidationFamilyTail, prbValidationCachedFamilyAppState,
    prbReplayInsert, Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationNextDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationAContext, prbValidationNextDomain,
        .sort .zero⟩ := by
  obtain ⟨bodyFinalState, bodyRun⟩ :=
    prbValidationNextBodyInferExists
  have domainRun : TypeChecker.Inner.inferType'
      prbValidationAlpha false (TypeChecker.Methods.withFuel 9998)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          prbValidationNextAlphaState) := by
    simpa [prbValidationNextAlphaState, prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998 prbValidationAContext
        ({} : TypeChecker.State) prbValidationAlphaId
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty
        prbValidationAlphaFindInA
  have forallRun : TypeChecker.Inner.inferForall
      prbValidationNextDomain false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort .zero, bodyFinalState) := by
    unfold prbValidationNextDomain TypeChecker.Inner.inferForall
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show prbValidationAlpha.instantiateRev #[] =
        prbValidationAlpha by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType prbValidationAlpha false
        (TypeChecker.Methods.withFuel 9999)
        prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType' prbValidationAlpha false
            (TypeChecker.Methods.withFuel 9998)
            prbValidationAContext.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop
      false
      #[Expr.fvar prbValidationNextInternalBId]
      #[Level.succ (.param `u)]
      (prbValidationFamilyApp (.bvar 0))
      (TypeChecker.Methods.withFuel 9999)
      prbValidationNextInternalContext.toTypeChecker
      prbValidationNextBodyState =
        .ok (Expr.sort .zero, bodyFinalState)
    simp only [prbValidationFamilyApp,
      TypeChecker.Inner.inferForall.loop]
    rw [show (((.const propRecursiveBoundaryKernelType.name
          [.param `u] : Expr).app prbValidationAlpha).app (.bvar 0)
          ).instantiateRev #[Expr.fvar prbValidationNextInternalBId] =
          prbValidationFamilyApp
            (.fvar prbValidationNextInternalBId) by
      simp [prbValidationFamilyApp, Expr.instantiateRev_eq,
        Expr.instantiate_eq, Expr.instantiate1_eq, Expr.instantiate1']]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType
        (prbValidationFamilyApp
          (.fvar prbValidationNextInternalBId)) false
        (TypeChecker.Methods.withFuel 9999)
        prbValidationNextInternalContext.toTypeChecker
        prbValidationNextBodyState =
          TypeChecker.Inner.inferType'
            (prbValidationFamilyApp
              (.fvar prbValidationNextInternalBId)) false
            (TypeChecker.Methods.withFuel 9998)
            prbValidationNextInternalContext.toTypeChecker
            prbValidationNextBodyState by rfl]
    rw [bodyRun]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999
    prbValidationAContext.toTypeChecker ({} : TypeChecker.State)
    bodyFinalState `b prbValidationAlpha
    (prbValidationFamilyApp (.bvar 0)) (.sort .zero) .default
    (by simp [prbValidationNextDomain, prbValidationFamilyApp,
      Expr.hasLooseBVars, Expr.looseBVarRange'])
    Std.HashMap.getElem?_empty
    (by simpa [prbValidationNextDomain] using forallRun)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run prbValidationAContext.env
    prbValidationAContext.safety prbValidationAContext.lctx
    prbValidationAContext.lparams prbValidationAContext.fuel
      (TypeChecker.checkType prbValidationNextDomain) = .ok (.sort .zero)
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' prbValidationNextDomain false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State)) =
        .ok (.sort .zero)
  simpa [prbValidationNextDomain, Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1)) outerRun

theorem prbValidationInferFirstAppCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId : FVarId)
    (hconst : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (halpha : (prbValidationConstState state).inferTypeC[
      (.fvar alphaId : Expr)]? = none)
    (happ : state.inferTypeC[
      prbValidationFirstApp (.fvar alphaId)]? = none)
    (hfind : context.lctx.find? alphaId =
      some (.cdecl index alphaId name
        (.sort (.succ (.param `u))) bi kind))
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (prbValidationFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationFirstAppState state alphaId) := by
  have constRun := prbValidationInferTypeFamilyCore fuel context state hconst
    henv hlparams hsafety
  have alphaRun := prbValidationInferTypeFVarCore fuel context
    (prbValidationConstState state) alphaId
    (.sort (.succ (.param `u))) halpha hfind
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (prbValidationConstState state) (prbValidationAlphaState state alphaId)
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE prbValidationAName (.bvar 0) (.sort .zero) .default)
    `α .default
    (by simp [prbValidationFirstApp, Expr.hasLooseBVars,
      Expr.looseBVarRange']) happ
    (by simpa [prbValidationAName, propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.bindingBody!,
      Expr.bindingName!] using constRun)
    (by simpa [prbValidationAlphaState] using alphaRun) (by rfl)
  simpa [prbValidationFirstAppState, prbValidationFirstApp,
    prbValidationFamilyTail, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationFamilyAppCheckValid
    (context : AddInductive.Context) (alphaId argId : FVarId)
    (hne : alphaId ≠ argId)
    (halphaExpr : (.fvar alphaId : Expr) = prbValidationAlpha)
    (halpha : context.lctx.find? alphaId =
      some (.cdecl alphaIndex alphaId alphaName
        (.sort (.succ (.param `u))) alphaBi alphaKind))
    (harg : context.lctx.find? argId =
      some (.cdecl argIndex argId argName (.fvar alphaId) argBi argKind))
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe)
    (hdepth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, prbValidationFamilyApp (.fvar argId), .sort .zero⟩ := by
  let initial := ({} : TypeChecker.State)
  have firstRun : TypeChecker.Inner.inferType'
      (prbValidationFirstApp (.fvar alphaId)) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationFirstAppState initial alphaId) := by
    apply prbValidationInferFirstAppCore
    · simp [initial]
    · simp [initial, prbValidationConstState,
        prbReplayInsert]
    · simp [initial, prbValidationFirstApp]
    · exact halpha
    · exact henv
    · exact hlparams
    · exact hsafety
  have argMiss : (prbValidationFirstAppState initial alphaId).inferTypeC[
      (.fvar argId : Expr)]? = none := by
    have initialMiss : initial.inferTypeC[(.fvar argId : Expr)]? = none := by
      simpa [initial] using
        (Std.HashMap.getElem?_empty (k := (.fvar argId : Expr))
          (v := Expr))
    have idBeq : ((.fvar alphaId : Expr) == .fvar argId) = false := by
      change Expr.eqv (.fvar alphaId) (.fvar argId) = false
      rw [Expr.eqv_eq]
      simp [Expr.eqv', hne]
    simp [prbValidationFirstAppState, prbValidationAlphaState,
      prbValidationConstState, prbReplayInsert,
      prbValidationFirstApp, idBeq, initialMiss]
    intro hmem
    have hsome := Std.HashMap.mem_iff_isSome_getElem?.mp hmem
    simp [initialMiss] at hsome
  have argRun : TypeChecker.Inner.inferType' (.fvar argId) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      (prbValidationFirstAppState initial alphaId) =
      .ok (.fvar alphaId,
        prbValidationArgumentState initial alphaId argId) := by
    simpa [prbValidationArgumentState] using
      prbValidationInferTypeFVarCore 9999 context
        (prbValidationFirstAppState initial alphaId) argId
        (.fvar alphaId) argMiss harg
  have appRun := prbInferAppCoreOf 9999 context.toTypeChecker initial
    (prbValidationFirstAppState initial alphaId)
    (prbValidationArgumentState initial alphaId argId)
    (prbValidationFirstApp (.fvar alphaId)) (.fvar argId)
    (.fvar alphaId) (.sort .zero) prbValidationAName .default
    (by simp [prbValidationFamilyApp, prbValidationFirstApp,
      Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by simp [initial, prbValidationFamilyApp]) firstRun argRun (by rfl)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType (prbValidationFamilyApp (.fvar argId))) =
        .ok (.sort .zero)
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (prbValidationFamilyApp (.fvar argId))
      false (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = .ok (.sort .zero)
  simpa [prbValidationFamilyApp, prbValidationFirstApp, halphaExpr, initial,
    Expr.instantiate1_eq, Expr.instantiate1', Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1)) appRun

theorem prbValidationAlphaRootCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationRootContext, prbValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  simpa [prbValidationAlpha_shape] using
    prbCandidateCheckTypeFVar prbValidationRootContext
      prbValidationAlphaId (.sort (.succ (.param `u)))
      (by rfl) prbValidationAlphaFind

theorem prbValidationAlphaACheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationAContext, prbValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  simpa [prbValidationAlpha_shape] using
    prbCandidateCheckTypeFVar prbValidationAContext
      prbValidationAlphaId (.sort (.succ (.param `u)))
      (by rfl) prbValidationAlphaFindInA

theorem prbValidationTerminalCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationNextContext, prbValidationTerminal,
        .sort .zero⟩ := by
  simpa [prbValidationTerminal,
    prbValidationAExpr_shape, prbValidationAlpha_shape] using
    prbValidationFamilyAppCheckValid prbValidationNextContext
      prbValidationAlphaId prbValidationAId
      prbValidationAlphaNeA rfl prbValidationAlphaFindInNext
      prbValidationAFindInNext rfl rfl rfl rfl

theorem prbValidationTargetCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationBContext, prbValidationTarget,
        .sort .zero⟩ := by
  simpa [prbValidationTarget,
    prbValidationBExpr_shape, prbValidationAlpha_shape] using
    prbValidationFamilyAppCheckValid prbValidationBContext
      prbValidationAlphaId prbValidationBId
      prbValidationAlphaNeB rfl prbValidationAlphaFindInB
      prbValidationBFind rfl rfl rfl rfl

private def prbCheckedOfValid
    (context : AddInductive.Context) (source inferred : Expr)
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (valid : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    AddInductive.ConstructorCheckedExpr context source :=
  .ofRun fvars valid

private def prbValidationAlphaRootChecked :
    AddInductive.ConstructorCheckedExpr prbValidationRootContext
      prbValidationAlpha :=
  prbCheckedOfValid _ _ _ (by
    rw [prbValidationAlpha_shape]
    change (prbValidationRootContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFind]
    rfl)
    prbValidationAlphaRootCheckValid

private def prbValidationAlphaAChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      prbValidationAlpha :=
  prbCheckedOfValid _ _ _ (by
    rw [prbValidationAlpha_shape]
    change (prbValidationAContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFindInA]
    rfl)
    prbValidationAlphaACheckValid

private def prbValidationAlphaAConsumedChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      (AddInductive.consumeTypeAnnotations prbValidationAlpha) :=
  prbCheckedOfValid _ _ (.sort (.succ (.param `u))) (by
    rw [prbValidationConsumeAlpha]
    exact prbValidationAlphaAChecked.fvars)
    (by simpa only [prbValidationConsumeAlpha] using
      prbValidationAlphaACheckValid)

private def prbValidationNextDomainChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      prbValidationNextDomain :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationNextDomain, prbValidationFamilyApp,
      prbValidationAlpha, FVarsIn, Level.hasMVar']
    change (prbValidationAContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFindInA]
    rfl)
    prbValidationNextDomainCheckValid

private def prbValidationTerminalChecked :
    AddInductive.ConstructorCheckedExpr prbValidationNextContext
      prbValidationTerminal :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationTerminal, prbValidationFamilyApp,
      prbValidationAlpha, prbValidationAExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (prbValidationNextContext.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbValidationAlphaFindInNext]
      rfl
    · change (prbValidationNextContext.lctx.find?
        prbValidationAId).isSome = true
      rw [prbValidationAFindInNext]
      rfl)
    prbValidationTerminalCheckValid

private def prbValidationTargetChecked :
    AddInductive.ConstructorCheckedExpr prbValidationBContext
      prbValidationTarget :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationTarget, prbValidationFamilyApp,
      prbValidationAlpha, prbValidationBExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (prbValidationBContext.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbValidationAlphaFindInB]
      rfl
    · change (prbValidationBContext.lctx.find?
        prbValidationBId).isSome = true
      rw [prbValidationBFind]
      rfl)
    prbValidationTargetCheckValid

private theorem prbValidationAlphaRootWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationRootContext, prbValidationAlpha,
        prbValidationAlpha⟩ := by
  rw [prbValidationAlpha_shape]
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [prbValidationAlphaFind]

private theorem prbValidationAlphaAWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationAContext, prbValidationAlpha,
        prbValidationAlpha⟩ := by
  rw [prbValidationAlpha_shape]
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [prbValidationAlphaFindInA]

private theorem prbValidationNextDomainWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationAContext, prbValidationNextDomain,
        prbValidationNextDomain⟩ := by
  apply TypeChecker.CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
    _ _ 9999
  · rfl
  · rfl

private theorem prbValidationTargetWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationBContext, prbValidationTarget,
        prbValidationTarget⟩ := by
  rw [prbValidationTarget, prbValidationFamilyApp,
    prbValidationAlpha_shape, prbValidationBExpr_shape]
  apply prbCtorFamilyWhnf prbValidationBContext prbValidationAlphaId
    prbValidationBId rfl rfl rfl
  rw [show prbValidationBContext.env = prbConstructorContext.env by rfl]
  rw [prbFamilyStage.quotInit_eq]
  rfl

private theorem prbValidationTerminalWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationNextContext, prbValidationTerminal,
        prbValidationTerminal⟩ := by
  rw [prbValidationTerminal, prbValidationFamilyApp,
    prbValidationAlpha_shape, prbValidationAExpr_shape]
  apply prbCtorFamilyWhnf prbValidationNextContext prbValidationAlphaId
    prbValidationAId rfl rfl rfl
  rw [show prbValidationNextContext.env = prbConstructorContext.env by rfl]
  rw [prbFamilyStage.quotInit_eq]
  rfl

private theorem prbCandidateWhnfResult_eq
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (other : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, result⟩) :
    result = source := by
  unfold AddInductive.CandidateWhnfStep.Valid at self other
  rw [self] at other
  exact (Except.ok.inj other).symm

noncomputable def prbConstructorValidation :
    AddInductive.ConstructorValidationRun propRecursiveBoundaryKernelType
      prbFamilyValidationRun.stats false
      prbConstructorValidationContext :=
  AddInductive.ConstructorValidationRun.of_run (by
    simpa [prbConstructorValidationContext] using prbCheckConstructorsRun)

noncomputable def prbStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl where
  staged := {
    raw := propRecursiveBoundaryType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := prbPreFamilyStage
    family := prbFamilyStage
    validation_nparams_eq := rfl
    constructorValidation := prbConstructorValidation
    constructors := prbConstructorsStage
    familyTypesProduced := prbFamilyTypesProduced
    familiesProduced := prbFamiliesProduced }
  universeRun := by
    simpa [prbFamilyStage, prbConstructorValidationContext] using
      prbUniverseRun

theorem prbStagedStats_eq :
    prbStagedUniverseInput.staged.family.validation.stats =
      prbFamilyValidationRun.stats := by
  rfl

private theorem prbStagedIndConsts_eq :
    prbStagedUniverseInput.staged.family.validation.stats.indConsts =
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] := by
  rw [prbStagedStats_eq, prbFamilyValidationRun.stats_eq]
  simp only [prbFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats]
  rw [show
    prbCandidate.families.singleton.familyType.type.context.lparams = [`u] by
      rw [prbFamilyCandidateContext_eq]
      rfl]
  rfl

private theorem prbValidationAlphaHasNoIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationAlpha = false := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationAlpha_shape]

private theorem prbValidationNextDomainHasIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationNextDomain = true := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationNextDomain,
    prbValidationFamilyApp, Expr.constName!]

private theorem prbValidationTargetHasIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationTarget = true := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationTarget,
    prbValidationFamilyApp, Expr.constName!]

private def prbValidationAlphaRootAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationRootContext
      prbValidationAlpha prbValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationRootContext
    prbValidationAlpha⟩

private def prbValidationAlphaAAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationAContext
      prbValidationAlpha prbValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationAContext
    prbValidationAlpha⟩

private def prbValidationNextDomainAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationAContext
      prbValidationNextDomain prbValidationNextDomain :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationAContext
    prbValidationNextDomain⟩

private noncomputable def prbValidationAlphaPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      prbStagedUniverseInput.staged.family.validation.stats false
      propRecursiveBoundaryKernelCtor.name 1 prbValidationRootContext
      prbValidationAlpha) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          subst result
          exact .absent prbValidationAlphaRootChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [prbValidationAlpha_shape, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          subst result
          rw [prbValidationAlphaHasNoIndOcc] at occurs
          contradiction

private def prbTransportPositivityTrace
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel) :
    AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context' source' fuel := by
  subst context'
  subst source'
  exact trace

private def prbTransportPositivityAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel)
    (alignment : AddInductive.ConstructorPositivityAlignmentTrace
      (prbTransportPositivityTrace context_eq source_eq trace)) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  subst context'
  subst source'
  exact alignment

private noncomputable def prbValidationNextPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      prbStagedUniverseInput.staged.family.validation.stats false
      propRecursiveBoundaryKernelCtor.name 2 prbValidationAContext
      prbValidationNextDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          subst result
          rw [prbValidationNextDomainHasIndOcc] at occurs
          contradiction
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          change (Expr.forallE name domain body binderInfo) =
            (Expr.forallE `b prbValidationAlpha
              (prbValidationFamilyApp (.bvar 0)) .default) at result_eq
          injection result_eq with name_eq domain_eq body_eq binderInfo_eq
          subst name
          subst domain
          subst body
          subst binderInfo
          have tailContext_eq :
              prbValidationAContext.pushLocalDecl `b .default
                  (AddInductive.consumeTypeAnnotations prbValidationAlpha) =
                prbValidationBContext := by
            rw [prbValidationConsumeAlpha]
            rfl
          have tailSource_eq :
              (prbValidationFamilyApp (.bvar 0)).instantiate1
                  prbValidationAContext.freshExpr =
                prbValidationTarget := by
            simpa [prbValidationNextDomain, Expr.bindingBody!,
              prbValidationBExpr] using prbValidationTarget_shape
          let tailNormalized := prbTransportPositivityTrace
            tailContext_eq tailSource_eq tail
          have tailNormalizedAlignment :
              AddInductive.ConstructorPositivityAlignmentTrace
                tailNormalized := by
            cases htail : tailNormalized with
            | absent context source result fuel whnf occurs =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                subst result
                rw [prbValidationTargetHasIndOcc] at occurs
                contradiction
            | forallE context source fuel name domain body binderInfo whnf
                occurs domainFree tail =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                have impossible := congrArg Expr.isForall result_eq
                simp [prbValidationTarget, prbValidationFamilyApp,
                  Expr.isForall] at impossible
            | target context source result fuel targetIdx whnf occurs
                terminal valid =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                subst result
                exact .target prbValidationTargetChecked
          have tailAlignment := prbTransportPositivityAlignment
            tailContext_eq tailSource_eq tail tailNormalizedAlignment
          exact .forallE prbValidationNextDomainChecked
            prbValidationAlphaAChecked
            prbValidationAlphaAConsumedChecked
            (.succ (.param `u)) rfl prbValidationAFresh
            (by simpa only [prbValidationConsumeAlpha] using
              prbValidationAlphaAAnnotations)
            tail tailAlignment
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          subst result
          simp [prbValidationNextDomain, Expr.isForall] at terminal

private def prbTransportValidationTrace
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx fuel := by
  subst context'
  subst source'
  exact trace

private def prbTransportViewAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (prbTransportValidationTrace context_eq source_eq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  exact alignment

@[simp] private theorem prbTransportValidationTrace_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (prbTransportValidationTrace context_eq source_eq trace).spineLength =
      trace.spineLength := by
  subst context'
  subst source'
  rfl

private def prbTransportValidationTraceIndexed
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx' fuel' := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  exact trace

private def prbTransportViewAlignmentIndexed
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (prbTransportValidationTraceIndexed context_eq source_eq argIdx_eq
        fuel_eq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  subst argIdx'
  subst fuel'
  exact alignment

@[simp] private theorem prbTransportValidationTraceIndexed_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (prbTransportValidationTraceIndexed context_eq source_eq argIdx_eq
      fuel_eq trace).spineLength = trace.spineLength := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  rfl

set_option pp.universes false in
set_option pp.all false in
noncomputable def prbStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl where
  universeInput := prbStagedUniverseInput
  alignment := by
    rw [AddInductive.CandidateList.singleton_eta
      prbCandidate.families.singleton.constructors]
    change AddInductive.ConstructorCandidateAlignmentTrace
      prbStagedUniverseInput.staged.family.validation.stats false 0
      { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := prbConstructorContext.env }
      prbStagedUniverseInput.staged.constructorValidation.trace
      (.cons prbCandidate.families.singleton.constructors.singleton .nil)
    generalize htrace :
      prbStagedUniverseInput.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors fresh closed rootCheck typeTrace tailTrace =>
      clear htrace
      have rootContext_eq :
          { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := prbConstructorContext.env } =
            prbValidationRootContext := by
        rw [prbFamilyTerminalContext_eq]
        rfl
      have rootFuel_eq :
          { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := prbConstructorContext.env }.fuel.inductiveFuel = 1000 := by
        rw [prbFamilyTerminalContext_eq]
        rfl
      let rootNormalized :
          AddInductive.ConstructorTypeValidationTrace
            prbStagedUniverseInput.staged.family.validation.stats false 0
            propRecursiveBoundaryKernelCtor.name prbValidationRootContext
            propRecursiveBoundaryKernelCtor.type 0 1000 :=
        prbTransportValidationTraceIndexed rootContext_eq (by rfl)
          (by rfl) rootFuel_eq typeTrace
      let rootNormalizedTrace := rootNormalized
      have rootSpine : typeTrace.spineLength =
          rootNormalizedTrace.spineLength := by
        exact (prbTransportValidationTraceIndexed_spineLength rootContext_eq
          (by rfl) (by rfl) rootFuel_eq typeTrace).symm
      cases hroot : rootNormalizedTrace with
      | parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeRun defeq tail =>
        simp [hroot,
          AddInductive.ConstructorTypeValidationTrace.spineLength] at rootSpine
        rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
        simp at parameterAt
        subst param
        change AddInductive.getType prbValidationAlpha
          prbValidationRootContext = .ok parameterType at parameterTypeRun
        rw [prbValidationGetTypeAlpha] at parameterTypeRun
        injection parameterTypeRun with parameterType_eq
        subst parameterType
        let afterParamNormalized := prbTransportValidationTrace (by rfl)
          prbValidationAfterParam_shape tail
        let afterParamNormalizedTrace := afterParamNormalized
        have afterParamSpine : tail.spineLength =
            afterParamNormalizedTrace.spineLength := by
          exact (prbTransportValidationTrace_spineLength (by rfl)
            prbValidationAfterParam_shape tail).symm
        cases hafterParam : afterParamNormalizedTrace with
        | parameter context fuel argIdx name domain body binderInfo param
            parameterType parameterAt parameterTypeRun defeq tail =>
            rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
            simp at parameterAt
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity afterATrace =>
            simp [hafterParam,
              AddInductive.ConstructorTypeValidationTrace.spineLength]
              at afterParamSpine
            have aContext_eq :
                prbValidationRootContext.pushLocalDecl `a .default
                    (AddInductive.consumeTypeAnnotations
                      prbValidationAlpha) =
                  prbValidationAContext := by
              rw [prbValidationConsumeAlpha]
              rfl
            let afterANormalized :
                AddInductive.ConstructorTypeValidationTrace
                  prbStagedUniverseInput.staged.family.validation.stats
                  false 0 propRecursiveBoundaryKernelCtor.name
                  prbValidationAContext prbValidationAfterA 2 998 :=
              prbTransportValidationTrace aContext_eq
                prbValidationAfterA_shape afterATrace
            let afterANormalizedTrace := afterANormalized
            have afterASpine : afterATrace.spineLength =
                afterANormalizedTrace.spineLength := by
              exact (prbTransportValidationTrace_spineLength aContext_eq
                prbValidationAfterA_shape afterATrace).symm
            cases hafterA : afterANormalizedTrace with
            | parameter context fuel argIdx name domain body binderInfo param
                parameterType parameterAt parameterTypeRun defeq tail =>
                rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
                simp at parameterAt
            | ordinary context fuel argIdx name domain body binderInfo
                sortResult noParameter ensureType universeTrace
                nextPositivity terminalTrace =>
                simp [hafterA,
                  AddInductive.ConstructorTypeValidationTrace.spineLength]
                  at afterASpine
                have nextPositivityAlignment :=
                  prbValidationNextPositivityAlignment nextPositivity
                have terminalContext_eq :
                    prbValidationAContext.pushLocalDecl `next .default
                        (AddInductive.consumeTypeAnnotations
                          prbValidationNextDomain) =
                      prbValidationNextContext := by
                  rw [prbValidationConsumeNextDomain]
                  rfl
                let terminalNormalized :
                    AddInductive.ConstructorTypeValidationTrace
                      prbStagedUniverseInput.staged.family.validation.stats
                      false 0 propRecursiveBoundaryKernelCtor.name
                      prbValidationNextContext prbValidationTerminal 3 997 :=
                  prbTransportValidationTrace terminalContext_eq
                    prbValidationTerminal_shape terminalTrace
                let terminalNormalizedTrace := terminalNormalized
                have terminalSpine : terminalTrace.spineLength =
                    terminalNormalizedTrace.spineLength := by
                  exact (prbTransportValidationTrace_spineLength
                    terminalContext_eq prbValidationTerminal_shape
                    terminalTrace).symm
                cases hterminal : terminalNormalizedTrace with
                | terminal context source fuel argIdx terminal valid =>
                    simp [hterminal,
                      AddInductive.ConstructorTypeValidationTrace.spineLength]
                      at terminalSpine
                    have terminalNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          terminalNormalizedTrace prbValidationTerminal := by
                      rw [hterminal]
                      exact .terminal prbValidationTerminalChecked
                        prbValidationTerminalChecked terminal valid
                    have terminalAlignment := prbTransportViewAlignment
                      terminalContext_eq prbValidationTerminal_shape
                      prbValidationTerminal_shape terminalTrace
                      terminalNormalizedAlignment
                    have afterANormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          afterANormalizedTrace prbValidationAfterA := by
                      rw [hafterA]
                      exact .ordinary prbValidationNextDomainChecked
                        prbValidationNextDomainChecked
                        prbValidationNextDomainAnnotations
                        (by simpa only [prbValidationConsumeNextDomain] using
                          prbValidationNextDomainChecked)
                        nextPositivity nextPositivityAlignment
                        prbValidationAFresh
                        (by simpa only [prbValidationConsumeNextDomain] using
                          prbValidationNextDomainAnnotations)
                        terminalTrace terminalAlignment
                    have afterAAlignment := prbTransportViewAlignment
                      aContext_eq prbValidationAfterA_shape
                      prbValidationAfterA_shape afterATrace
                      afterANormalizedAlignment
                    have afterParamNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          afterParamNormalizedTrace
                          prbValidationAfterParam := by
                      rw [hafterParam]
                      exact .ordinary prbValidationAlphaRootChecked
                        prbValidationAlphaRootChecked
                        prbValidationAlphaRootAnnotations
                        (by simpa only [prbValidationConsumeAlpha] using
                          prbValidationAlphaRootChecked)
                        positivity
                        (prbValidationAlphaPositivityAlignment positivity)
                        prbValidationRootFresh
                        (by simpa only [prbValidationConsumeAlpha] using
                          prbValidationAlphaRootAnnotations)
                        afterATrace afterAAlignment
                    have afterParamAlignment := prbTransportViewAlignment
                      (by rfl) prbValidationAfterParam_shape
                      prbValidationAfterParam_shape tail
                      afterParamNormalizedAlignment
                    have rootNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          rootNormalizedTrace
                          propRecursiveBoundaryKernelCtor.type := by
                      rw [hroot]
                      exact .parameter prbValidationSortChecked
                        prbValidationSortChecked prbValidationSortChecked
                        prbValidationAlpha_shape
                        (by rw [prbValidationAlphaFind]; rfl)
                        tail afterParamAlignment
                    have headAlignment := prbTransportViewAlignmentIndexed
                      rootContext_eq (by rfl) prbCtorView_eq (by rfl)
                      rootFuel_eq typeTrace rootNormalizedAlignment
                    let rootScope :
                        AddInductive.ConstructorCheckedExpr
                          ({ prbCandidate.families.singleton.familyType.type.trace.terminalContext with
                            env := prbConstructorContext.env }).withEmptyLocalContext
                          propRecursiveBoundaryKernelCtor.type :=
                      AddInductive.ConstructorCheckedExpr.ofClosedRoot
                        closed rootCheck
                    cases tailTrace with
                    | nil finalSeen =>
                        exact
                          AddInductive.ConstructorCandidateAlignmentTrace.cons
                            rootScope
                            (by
                              change
                                prbCandidate.families.singleton.constructors.singleton.type.trace.storedSpine =
                                  true
                              exact prbCtorIdentityEvidence.identity.storedSpine)
                            (by
                              change
                                prbCandidate.families.singleton.constructors.singleton.type.trace.spineLength =
                                  typeTrace.spineLength
                              have candidateSpine :=
                                prbCtorIdentityEvidence.spineLength_eq.trans
                                  prbCtorIdentityReplay_shape.1
                              omega)
                            (by
                              rw [prbCtorWhnfDepth, rootContext_eq]
                              rfl)
                            headAlignment
                            (AddInductive.ConstructorCandidateAlignmentTrace.nil
                              ((∅ : NameSet).insert
                                propRecursiveBoundaryKernelCtor.name))
            | terminal context source fuel argIdx terminal valid =>
                simp [prbValidationAfterA, Expr.isForall] at terminal
        | terminal context source fuel argIdx terminal valid =>
            simp [prbValidationAfterParam, Expr.isForall] at terminal
      | ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureType universeTrace positivity tail =>
        rw [prbStagedStats_eq, prbStatsParams_eq] at noParameter
        simp at noParameter
      | terminal context source fuel argIdx terminal valid =>
        simp [propRecursiveBoundaryKernelType, propRecursiveBoundaryKernelCtor,
          propRecursiveBoundaryMkInfo, ConstantInfo.type,
          ConstantInfo.toConstantVal, Expr.isForall] at terminal

def prbPreFamilyContextReplay : AddInductive.Context :=
  prbValidationFamilyContext

def prbPreFamilyAContextReplay : AddInductive.Context :=
  prbPreFamilyContextReplay.pushLocalDecl `a .default prbValidationAlpha

def prbPreFamilyBContextReplay : AddInductive.Context :=
  prbPreFamilyAContextReplay.pushLocalDecl `b .default prbValidationAlpha

def prbPreFamilyResultContextReplay : AddInductive.Context :=
  prbPreFamilyAContextReplay.advanceFresh

def prbPreFamilyIndexTelescopeReplay : Expr :=
  .forallE prbValidationAName prbValidationAlpha (.sort .zero) .default

theorem prbPreFamilyContextReplay_eq :
    prbPreFamilyContextReplay = prbValidationFamilyContext := by
  rfl

theorem prbPreFamilyAContextReplay_eq :
    prbPreFamilyAContextReplay =
      { prbValidationAContext with env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyAContextReplay, prbValidationAContext,
    prbValidationRootContext, prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyBContextReplay_eq :
    prbPreFamilyBContextReplay =
      { prbValidationBContext with env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyBContextReplay, prbPreFamilyAContextReplay_eq,
    prbValidationBContext]
  rfl

theorem prbPreFamilyResultContextReplay_eq :
    prbPreFamilyResultContextReplay =
      { prbValidationAContext.advanceFresh with
        env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyResultContextReplay, prbPreFamilyAContextReplay_eq]
  rfl

theorem prbFamilyViewReplay_eq :
    prbCandidate.families.singleton.familyType.type.view =
      propRecursiveBoundaryKernelType.type := by
  apply prbFamilyIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [prbFamilyCandidateContext_eq]
    rfl
  · rw [prbFamilyCandidateContext_eq]
    simp [propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar']

theorem prbStagedParamsReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.params =
      #[prbValidationAlpha] := by
  rw [prbStagedStats_eq, prbStatsParams_eq]
  rfl

theorem prbStagedNindicesReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.nindices = #[1] := by
  rw [prbStagedStats_eq, prbStatsNindices_eq]

theorem prbStagedIndConstsReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.indConsts =
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] := by
  rw [prbStagedStats_eq, prbFamilyValidationRun.stats_eq]
  simp only [prbFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats]
  rw [show
    prbCandidate.families.singleton.familyType.type.context.lparams = [`u] by
      rw [prbFamilyCandidateContext_eq]
      rfl]
  rfl

def prbPreFamilyFVarInferOnlyStateReplay
    (id : FVarId) (type : Expr) : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeI := ({} : TypeChecker.State).inferTypeI.insert
      (.fvar id) type }

theorem prbPreFamilyFVarInferOnlyReplay
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (find : context.lctx.find? id =
      some (.cdecl index id name type bi kind))
    (depth : context.fuel.recDepth = 10000) :
    TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (type, prbPreFamilyFVarInferOnlyStateReplay id type) := by
  rw [depth]
  change TypeChecker.Inner.inferType' (.fvar id) true
    (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
    ({} : TypeChecker.State) = _
  unfold TypeChecker.Inner.inferType'
  simp [prbPreFamilyFVarInferOnlyStateReplay,
    Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker,
    find, LocalDecl.type, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem prbPreFamilyFVarEnsureValidReplay
    (context : AddInductive.Context) (id : FVarId) (level : Level)
    (find : context.lctx.find? id =
      some (.cdecl index id name (.sort level) bi kind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, .fvar id, .sort level⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
    TypeChecker.ensureType TypeChecker.inferType TypeChecker.ensureSort
    TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      { env := context.env, lctx := context.lctx,
        safety := context.safety, lparams := context.lparams,
        fuel := context.fuel }
      ({} : TypeChecker.State) =
        .ok (.sort level,
          prbPreFamilyFVarInferOnlyStateReplay id (.sort level)) by
    simpa [AddInductive.Context.toTypeChecker] using
      prbPreFamilyFVarInferOnlyReplay context id (.sort level) find depth]
  rfl

theorem prbPreFamilyCheckLevelSuccParamReplay
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u]) :
    TypeChecker.Inner.checkLevel context.toTypeChecker
      (.succ (.param `u)) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, AddInductive.Context.toTypeChecker,
    lparams, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

theorem prbPreFamilySortCheckValidReplay
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    prbPreFamilyCheckLevelSuccParamReplay context lparams,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

theorem prbPreFamilySortZeroCheckValidReplay
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort .zero, .sort (.succ .zero)⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.checkType (.sort .zero)) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.sort .zero) false
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.checkLevel, Level.getUndefParam,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

@[simp] theorem prbPreFamilyCheckLevelZeroReplay
    (context : TypeChecker.Context) :
    TypeChecker.Inner.checkLevel context .zero = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam,
    Level.forEach, Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem prbFVarBeqSortReplay (id : FVarId) (level : Level) :
    ((.fvar id : Expr) == .sort level) = false := by
  change Expr.eqv (.fvar id) (.sort level) = false
  rw [Expr.eqv_eq]
  rfl

def prbPreFamilyTelescopeAlphaStateReplay : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State) prbValidationAlpha
    (.sort (.succ (.param `u)))

def prbPreFamilyTelescopeInternalIdReplay : FVarId :=
  ⟨prbPreFamilyTelescopeAlphaStateReplay.ngen.curr⟩

def prbPreFamilyTelescopeInternalStateReplay : TypeChecker.State :=
  { prbPreFamilyTelescopeAlphaStateReplay with
    ngen := prbPreFamilyTelescopeAlphaStateReplay.ngen.next }

def prbPreFamilyTelescopeFinalStateReplay : TypeChecker.State :=
  prbReplayInsert prbPreFamilyTelescopeInternalStateReplay
    (.sort .zero) (.sort (.succ .zero))

theorem prbPreFamilyInferSortZeroCoreReplay
    (fuel : Nat) (context : TypeChecker.Context)
    (state : TypeChecker.State)
    (miss : state.inferTypeC[(.sort .zero : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.sort .zero) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.sort (.succ .zero),
          prbReplayInsert state (.sort .zero) (.sort (.succ .zero))) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', miss,
    prbPreFamilyCheckLevelZeroReplay,
    prbReplayInsert, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem prbPreFamilyIndexTelescopeCheckValidReplay
    (context : AddInductive.Context)
    (alphaFind : context.lctx.find? prbValidationAlphaId =
      some (.cdecl alphaIndex prbValidationAlphaId alphaName
        (.sort (.succ (.param `u))) alphaBi alphaKind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, prbPreFamilyIndexTelescopeReplay,
        .sort (mkLevelIMax' (.succ (.param `u)) (.succ .zero))⟩ := by
  have domainRun : TypeChecker.Inner.inferType'
      prbValidationAlpha false (TypeChecker.Methods.withFuel 9998)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          prbPreFamilyTelescopeAlphaStateReplay) := by
    simpa [prbPreFamilyTelescopeAlphaStateReplay,
      prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998 context
        ({} : TypeChecker.State) prbValidationAlphaId
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty alphaFind
  have bodyMiss : prbPreFamilyTelescopeInternalStateReplay.inferTypeC[
      (.sort .zero : Expr)]? = none := by
    simp [prbPreFamilyTelescopeInternalStateReplay,
      prbPreFamilyTelescopeAlphaStateReplay, prbReplayInsert,
      prbValidationAlpha_shape]
  have bodyRun : TypeChecker.Inner.inferType'
      (.sort .zero) false (TypeChecker.Methods.withFuel 9998)
      { context.toTypeChecker with
        lctx := context.lctx.mkLocalDecl
          prbPreFamilyTelescopeInternalIdReplay prbValidationAName
          prbValidationAlpha .default }
      prbPreFamilyTelescopeInternalStateReplay =
        .ok (.sort (.succ .zero),
          prbPreFamilyTelescopeFinalStateReplay) := by
    simpa [prbPreFamilyTelescopeFinalStateReplay] using
      prbPreFamilyInferSortZeroCoreReplay 9998 _
        prbPreFamilyTelescopeInternalStateReplay bodyMiss
  have forallRun : TypeChecker.Inner.inferForall
      prbPreFamilyIndexTelescopeReplay false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort
          (mkLevelIMax' (.succ (.param `u)) (.succ .zero)),
          prbPreFamilyTelescopeFinalStateReplay) := by
    unfold prbPreFamilyIndexTelescopeReplay TypeChecker.Inner.inferForall
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show prbValidationAlpha.instantiateRev #[] =
        prbValidationAlpha by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType prbValidationAlpha false
        (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
        ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType' prbValidationAlpha false
            (TypeChecker.Methods.withFuel 9998) context.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop false
      #[Expr.fvar prbPreFamilyTelescopeInternalIdReplay]
      #[Level.succ (.param `u)] (.sort .zero)
      (TypeChecker.Methods.withFuel 9999)
      { context.toTypeChecker with
        lctx := context.lctx.mkLocalDecl
          prbPreFamilyTelescopeInternalIdReplay prbValidationAName
          prbValidationAlpha .default }
      prbPreFamilyTelescopeInternalStateReplay = _
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show (.sort .zero : Expr).instantiateRev
        #[Expr.fvar prbPreFamilyTelescopeInternalIdReplay] =
          .sort .zero by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType (.sort .zero) false
        (TypeChecker.Methods.withFuel 9999) _
        prbPreFamilyTelescopeInternalStateReplay =
          TypeChecker.Inner.inferType' (.sort .zero) false
            (TypeChecker.Methods.withFuel 9998) _
            prbPreFamilyTelescopeInternalStateReplay by rfl]
    rw [bodyRun]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999 context.toTypeChecker
    ({} : TypeChecker.State) prbPreFamilyTelescopeFinalStateReplay
    prbValidationAName prbValidationAlpha (.sort .zero)
    (.sort (mkLevelIMax' (.succ (.param `u)) (.succ .zero)))
    .default
    (by simp [prbPreFamilyIndexTelescopeReplay,
      prbValidationAlpha_shape, Expr.hasLooseBVars,
      Expr.looseBVarRange']) Std.HashMap.getElem?_empty forallRun
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType prbPreFamilyIndexTelescopeReplay) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' prbPreFamilyIndexTelescopeReplay false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State)) = _
  simpa [prbPreFamilyIndexTelescopeReplay,
    Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      outerRun

theorem prbPreFamilyAlphaFindReplay :
    prbPreFamilyContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyContextReplay_eq]
  simpa [prbValidationRootContext] using prbValidationAlphaFind

theorem prbPreFamilyAlphaFindInAReplay :
    prbPreFamilyAContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyAContextReplay_eq]
  exact prbValidationAlphaFindInA

theorem prbPreFamilyAlphaFindInBReplay :
    prbPreFamilyBContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationAlphaFindInB

theorem prbPreFamilyAlphaFindInResultReplay :
    prbPreFamilyResultContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyResultContextReplay_eq]
  simpa [AddInductive.Context.advanceFresh] using
    prbValidationAlphaFindInA

theorem prbPreFamilyAFindInResultReplay :
    prbPreFamilyResultContextReplay.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
  rw [prbPreFamilyResultContextReplay_eq]
  simpa [AddInductive.Context.advanceFresh] using prbValidationAFind

theorem prbPreFamilyBFindReplay :
    prbPreFamilyBContextReplay.lctx.find? prbValidationBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationBId `b prbValidationAlpha .default .default) := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationBFind

theorem prbPreFamilyRootFreshReplay :
    prbPreFamilyContextReplay.lctx.find?
      prbPreFamilyContextReplay.freshFVarId = none := by
  rw [prbPreFamilyContextReplay_eq]
  simpa [prbValidationRootContext,
    AddInductive.Context.freshFVarId] using prbValidationRootFresh

theorem prbPreFamilyAFreshReplay :
    prbPreFamilyAContextReplay.lctx.find?
      prbPreFamilyAContextReplay.freshFVarId = none := by
  rw [prbPreFamilyAContextReplay_eq]
  exact prbValidationAFresh

theorem prbPreFamilyBFreshReplay :
    prbPreFamilyBContextReplay.lctx.find?
      prbPreFamilyBContextReplay.freshFVarId = none := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationBFresh

theorem prbPreFamilyRootDepthReplay :
    prbPreFamilyContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyADepthReplay :
    prbPreFamilyAContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyBDepthReplay :
    prbPreFamilyBContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyBContextReplay_eq]
  rfl

theorem prbPreFamilyResultDepthReplay :
    prbPreFamilyResultContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyResultContextReplay_eq]
  rfl

theorem prbPreFamilyRootInductiveFuelReplay :
    prbPreFamilyContextReplay.fuel.inductiveFuel = 1000 := by
  rw [prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyAInductiveFuelReplay :
    prbPreFamilyAContextReplay.fuel.inductiveFuel = 1000 := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyAFreshExprReplay :
    prbPreFamilyAContextReplay.freshExpr = prbValidationBExpr := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyRootFreshExprReplay :
    prbPreFamilyContextReplay.freshExpr = prbValidationAExpr := by
  rfl

theorem prbPreFamilyAlphaHasNoIndOccReplay :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationAlpha = false := by
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationAlpha_shape]

theorem prbPreFamilyNextDomainHasIndOccReplay :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationNextDomain = true := by
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationNextDomain,
    prbValidationFamilyApp, Expr.constName!]

@[simp] theorem prbValidationFamilyAppGetAppFnReplay (arg : Expr) :
    (prbValidationFamilyApp arg).getAppFn =
      .const propRecursiveBoundaryKernelType.name [.param `u] := by
  rfl

@[simp] theorem prbValidationFamilyAppGetAppArgsReplay (arg : Expr) :
    (prbValidationFamilyApp arg).getAppArgs =
      #[prbValidationAlpha, arg] := by
  rfl

@[simp] theorem prbExprBneSelfReplay (source : Expr) :
    (source != source) = false := by
  change (!Expr.eqv source source) = false
  rw [show Expr.eqv source source = true by exact Expr.eqv_refl source]
  rfl

theorem prbPreFamilyFamilyAppValidReplay (arg : Expr)
    (argFree : AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      arg = false) :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      (prbValidationFamilyApp arg) 0 = true := by
  have parameterSelf : (prbValidationAlpha != prbValidationAlpha) = false := by
    change (!Expr.eqv prbValidationAlpha prbValidationAlpha) = false
    rw [show Expr.eqv prbValidationAlpha prbValidationAlpha = true by
      exact Expr.eqv_refl prbValidationAlpha]
    rfl
  have argFree' : AddInductive.hasIndOcc
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] arg =
        false := by
    simpa [prbStagedIndConstsReplay_eq] using argFree
  simp +decide [AddInductive.isValidIndAppIdx,
    prbStagedParamsReplay_eq, prbStagedNindicesReplay_eq,
    prbStagedIndConstsReplay_eq,
    prbValidationFamilyAppGetAppFnReplay,
    prbValidationFamilyAppGetAppArgsReplay,
    prbExprBneSelfReplay, parameterSelf, argFree', Expr.constName!]

theorem prbPreFamilyTargetValidReplay :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      prbValidationTarget 0 = true := by
  apply prbPreFamilyFamilyAppValidReplay
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationTarget,
    prbValidationFamilyApp, prbValidationBExpr_shape]

theorem prbPreFamilyTerminalValidReplay :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      prbValidationTerminal 0 = true := by
  apply prbPreFamilyFamilyAppValidReplay
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationTerminal,
    prbValidationFamilyApp, prbValidationAExpr_shape]

theorem prbPreFamilyAIdNeRemovedReplay :
    prbValidationAId ≠ prbPreFamilyAContextReplay.freshFVarId := by
  intro equality
  have fresh := prbPreFamilyAFreshReplay
  rw [← equality] at fresh
  have found : prbPreFamilyAContextReplay.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
    rw [prbPreFamilyAContextReplay_eq]
    exact prbValidationAFind
  rw [found] at fresh
  contradiction

theorem prbPreFamilyAlphaIdNeRemovedReplay :
    prbValidationAlphaId ≠ prbPreFamilyAContextReplay.freshFVarId := by
  intro equality
  have fresh := prbPreFamilyAFreshReplay
  rw [← equality, prbPreFamilyAlphaFindInAReplay] at fresh
  contradiction

theorem prbSafetyRunDirect :
    AddInductive.checkConstructorPreFamilySafety
        prbStagedUniverseInput.staged.family.validation.stats
        prbCandidate.families.singleton.familyType.type.view
        prbCandidate.families.singleton.constructors
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  rw [prbFamilyViewReplay_eq]
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors]
  rw [prbFamilyTerminalContext_eq]
  change AddInductive.checkConstructorPreFamilySafety
    prbStagedUniverseInput.staged.family.validation.stats
    propRecursiveBoundaryKernelType.type
    (.cons prbCandidate.families.singleton.constructors.singleton .nil)
    prbPreFamilyContextReplay = .ok ()
  let rootAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindReplay]
      rfl)
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyRootDepthReplay prbPreFamilyAlphaFindReplay)
  let rootAlphaEnsure : AddInductive.ConstructorEnsureTypeObservation
      prbPreFamilyContextReplay prbValidationAlpha :=
    ⟨.sort (.succ (.param `u)), by
      simpa [prbValidationAlpha_shape] using
        prbPreFamilyFVarEnsureValidReplay prbPreFamilyContextReplay
          prbValidationAlphaId (.succ (.param `u))
          prbPreFamilyAlphaFindReplay prbPreFamilyRootDepthReplay⟩
  let rootAlphaConsumed : AddInductive.ConstructorCheckedExpr
      prbPreFamilyContextReplay
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact rootAlpha
  let rootAlphaAnnotations : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyContextReplay prbValidationAlpha
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyContextReplay prbValidationAlpha⟩
  let aAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyAContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyAContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInAReplay]
      rfl)
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyAContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyADepthReplay prbPreFamilyAlphaFindInAReplay)
  let aAlphaEnsure : AddInductive.ConstructorEnsureTypeObservation
      prbPreFamilyAContextReplay prbValidationAlpha :=
    ⟨.sort (.succ (.param `u)), by
      simpa [prbValidationAlpha_shape] using
        prbPreFamilyFVarEnsureValidReplay prbPreFamilyAContextReplay
          prbValidationAlphaId (.succ (.param `u))
          prbPreFamilyAlphaFindInAReplay prbPreFamilyADepthReplay⟩
  let aAlphaConsumed : AddInductive.ConstructorCheckedExpr
      prbPreFamilyAContextReplay
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact aAlpha
  let aAlphaAnnotations : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyAContextReplay prbValidationAlpha
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyAContextReplay prbValidationAlpha⟩
  let bTelescope : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay :=
    .ofRun (by
      simp [prbPreFamilyIndexTelescopeReplay,
        prbValidationAlpha_shape, FVarsIn, Level.hasMVar']
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInBReplay]
      rfl)
      (prbPreFamilyIndexTelescopeCheckValidReplay
        prbPreFamilyBContextReplay prbPreFamilyAlphaFindInBReplay
          prbPreFamilyBDepthReplay)
  let bArgument : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbValidationBExpr :=
    .ofRun (by
      rw [prbValidationBExpr_shape]
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationBId).isSome = true
      rw [prbPreFamilyBFindReplay]
      rfl)
      (by
        simpa [prbValidationBExpr_shape, prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyBContextReplay
            prbValidationBId prbValidationAlpha prbPreFamilyBDepthReplay
            prbPreFamilyBFindReplay)
  let bAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInBReplay]
      rfl)
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyBContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyBDepthReplay prbPreFamilyAlphaFindInBReplay)
  let bSortZero : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay (.sort .zero) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (prbPreFamilySortZeroCheckValidReplay
        prbPreFamilyBContextReplay prbPreFamilyBDepthReplay)
  let bComparison : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyBContextReplay prbValidationAlpha prbValidationAlpha :=
    ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyBContextReplay prbValidationAlpha⟩
  let targetSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
        [prbValidationBExpr] := by
    unfold prbPreFamilyIndexTelescopeReplay
    exact .cons prbPreFamilyBContextReplay prbValidationAName
      prbValidationAlpha (.sort .zero) .default
      prbValidationBExpr [] bTelescope
      ⟨bArgument, bAlpha, bComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            prbPreFamilyBContextReplay (.sort .zero) bSortZero rfl))
  have targetArgs : prbValidationTarget.getAppArgs.toList.drop
      prbStagedUniverseInput.staged.family.validation.stats.params.size =
        [prbValidationBExpr] := by
    rw [prbStagedParamsReplay_eq]
    simp [prbValidationTarget,
      prbValidationFamilyAppGetAppArgsReplay]
  obtain ⟨targetSpineExact, targetSpineRun⟩ :
      ∃ targetSpineExact :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTarget.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTarget.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size) =
          .ok targetSpineExact := by
    rw [targetArgs]
    exact ⟨targetSpine, targetSpine.build_eq⟩
  let targetTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
      prbValidationTarget 999 :=
    .target prbPreFamilyBContextReplay prbValidationTarget
      prbPreFamilyTargetValidReplay targetSpineExact
  have targetRun : AddInductive.ConstructorPreFamilyRecursiveTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
      prbValidationTarget 999 = .ok targetTrace := by
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
      (fuel := 998) rfl prbPreFamilyTargetValidReplay targetSpineExact
  obtain ⟨recursiveTargetTrace, recursiveTargetRun⟩ :
      ∃ recursiveTargetTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
          (prbValidationNextDomain.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 999,
        AddInductive.ConstructorPreFamilyRecursiveTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
            (prbValidationNextDomain.bindingBody!.instantiate1
              prbPreFamilyAContextReplay.freshExpr) 999 =
          .ok recursiveTargetTrace := by
    rw [show prbValidationNextDomain.bindingBody!.instantiate1
        prbPreFamilyAContextReplay.freshExpr = prbValidationTarget by
      rw [prbPreFamilyAFreshExprReplay]
      exact prbValidationTarget_shape]
    exact ⟨targetTrace, targetRun⟩
  have recursiveTailContext_eq :
      prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha) =
        prbPreFamilyBContextReplay := by
    rw [prbValidationConsumeAlpha]
    rfl
  have recursiveTailSource_eq :
      (prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr =
        prbValidationTarget := by
    rw [prbPreFamilyAFreshExprReplay]
    simpa [prbValidationNextDomain, Expr.bindingBody!] using
      prbValidationTarget_shape
  let recursiveTailSpineExact :
      AddInductive.ConstructorPreFamilyIndexSpineTrace
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        prbPreFamilyIndexTelescopeReplay
        (((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr).getAppArgs.toList.drop
            prbStagedUniverseInput.staged.family.validation.stats.params.size) := by
    rw [recursiveTailContext_eq, recursiveTailSource_eq]
    exact targetSpineExact
  have recursiveTailValid : AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      ((prbValidationFamilyApp (.bvar 0)).instantiate1
        prbPreFamilyAContextReplay.freshExpr) 0 = true := by
    rw [recursiveTailSource_eq]
    exact prbPreFamilyTargetValidReplay
  let recursiveTargetTraceExact :
      AddInductive.ConstructorPreFamilyRecursiveTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        ((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr) 999 :=
    .target _ _ recursiveTailValid recursiveTailSpineExact
  have recursiveTargetRunExact :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        ((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr) 999 =
        .ok recursiveTargetTraceExact := by
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
      (fuel := 998) (by rw [recursiveTailSource_eq]; rfl)
      recursiveTailValid recursiveTailSpineExact
  let recursiveFieldTrace :
      AddInductive.ConstructorPreFamilyRecursiveTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        prbValidationNextDomain 1000 :=
    .forallE prbPreFamilyAContextReplay `b prbValidationAlpha
      (prbValidationFamilyApp (.bvar 0)) .default aAlpha aAlphaEnsure
      aAlphaConsumed aAlphaAnnotations prbPreFamilyAFreshReplay
      recursiveTargetTraceExact
  have recursiveFieldRun :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        prbValidationNextDomain 1000 = .ok recursiveFieldTrace := by
    unfold prbValidationNextDomain
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.forallE_build_eq
      aAlpha aAlphaEnsure aAlphaConsumed aAlphaAnnotations
      prbPreFamilyAFreshReplay recursiveTargetTraceExact
      recursiveTargetRunExact
  obtain ⟨recursiveFieldTraceAtContext, recursiveFieldRunAtContext⟩ :
      ∃ recursiveFieldTraceAtContext :
          AddInductive.ConstructorPreFamilyRecursiveTrace
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationNextDomain
            prbPreFamilyAContextReplay.fuel.inductiveFuel,
        AddInductive.ConstructorPreFamilyRecursiveTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationNextDomain
            prbPreFamilyAContextReplay.fuel.inductiveFuel =
          .ok recursiveFieldTraceAtContext := by
    rw [prbPreFamilyAInductiveFuelReplay]
    exact ⟨recursiveFieldTrace, recursiveFieldRun⟩
  let resultTelescope : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay :=
    .ofRun (by
      simp [prbPreFamilyIndexTelescopeReplay,
        prbValidationAlpha_shape, FVarsIn, Level.hasMVar']
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInResultReplay]
      rfl)
      (prbPreFamilyIndexTelescopeCheckValidReplay
        prbPreFamilyResultContextReplay prbPreFamilyAlphaFindInResultReplay
          prbPreFamilyResultDepthReplay)
  let resultArgument : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbValidationAExpr :=
    .ofRun (by
      rw [prbValidationAExpr_shape]
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAId).isSome = true
      rw [prbPreFamilyAFindInResultReplay]
      rfl)
      (by
        simpa [prbValidationAExpr_shape, prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyResultContextReplay
            prbValidationAId prbValidationAlpha
            prbPreFamilyResultDepthReplay prbPreFamilyAFindInResultReplay)
  let resultAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInResultReplay]
      rfl)
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyResultContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyResultDepthReplay
            prbPreFamilyAlphaFindInResultReplay)
  let resultSortZero : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay (.sort .zero) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (prbPreFamilySortZeroCheckValidReplay
        prbPreFamilyResultContextReplay prbPreFamilyResultDepthReplay)
  let resultComparison : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyResultContextReplay prbValidationAlpha
        prbValidationAlpha :=
    ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyResultContextReplay prbValidationAlpha⟩
  let resultSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
        [prbValidationAExpr] := by
    unfold prbPreFamilyIndexTelescopeReplay
    exact .cons prbPreFamilyResultContextReplay prbValidationAName
      prbValidationAlpha (.sort .zero) .default
      prbValidationAExpr [] resultTelescope
      ⟨resultArgument, resultAlpha, resultComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            prbPreFamilyResultContextReplay (.sort .zero)
            resultSortZero rfl))
  have resultArgs : prbValidationTerminal.getAppArgs.toList.drop
      prbStagedUniverseInput.staged.family.validation.stats.params.size =
        [prbValidationAExpr] := by
    rw [prbStagedParamsReplay_eq]
    simp [prbValidationTerminal,
      prbValidationFamilyAppGetAppArgsReplay]
  obtain ⟨resultSpineExact, resultSpineRun⟩ :
      ∃ resultSpineExact :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTerminal.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTerminal.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size) =
          .ok resultSpineExact := by
    rw [resultArgs]
    exact ⟨resultSpine, resultSpine.build_eq⟩
  have resultIndependent : AddInductive.constructorIndependentOf
      prbValidationTerminal
      [prbPreFamilyAContextReplay.freshFVarId] = true := by
    simp [AddInductive.constructorIndependentOf,
      prbValidationTerminal, prbValidationFamilyApp,
      Expr.fvarsList, prbValidationAlpha_shape,
      prbValidationAExpr_shape,
      prbPreFamilyAlphaIdNeRemovedReplay,
      prbPreFamilyAIdNeRemovedReplay]
  let resultTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyResultContextReplay
      prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true :=
    .terminal prbPreFamilyResultContextReplay prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true
      prbPreFamilyTerminalValidReplay resultIndependent resultSpineExact
  have resultRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyResultContextReplay
      prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true 997 =
        .ok resultTrace := by
    exact AddInductive.ConstructorPreFamilyViewTrace.terminal_build_eq
      (fuel := 996) rfl prbPreFamilyTerminalValidReplay resultIndependent
      resultSpineExact
  obtain ⟨recursiveViewTailTrace, recursiveViewTailRun⟩ :
      ∃ recursiveViewTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            (prbValidationAfterA.bindingBody!.instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true 997 =
          .ok recursiveViewTailTrace := by
    rw [show prbPreFamilyAContextReplay.advanceFresh =
        prbPreFamilyResultContextReplay by rfl]
    rw [show prbValidationAfterA.bindingBody!.instantiate1
        prbPreFamilyAContextReplay.freshExpr = prbValidationTerminal by
      simp [prbValidationAfterA, prbValidationTerminal,
        prbValidationFamilyApp, Expr.bindingBody!,
        Expr.instantiate1_eq, Expr.instantiate1']]
    exact ⟨resultTrace, resultRun⟩
  obtain ⟨recursiveViewTailTraceExact, recursiveViewTailRunExact⟩ :
      ∃ recursiveViewTailTraceExact :
          AddInductive.ConstructorPreFamilyViewTrace
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            ((prbValidationFamilyApp prbValidationAExpr).instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            ((prbValidationFamilyApp prbValidationAExpr).instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true 997 =
          .ok recursiveViewTailTraceExact := by
    change ∃ recursiveViewTailTraceExact :
        AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true 997 =
        .ok recursiveViewTailTraceExact
    exact ⟨recursiveViewTailTrace, recursiveViewTailRun⟩
  have noParameterTwo :
      prbStagedUniverseInput.staged.family.validation.stats.params[2]? =
        none := by
    rw [prbStagedParamsReplay_eq]
    rfl
  have recursiveIndependent : AddInductive.constructorIndependentOf
      prbValidationNextDomain [] = true := by
    simp [AddInductive.constructorIndependentOf]
  let recursiveViewTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp prbValidationAExpr) .default)
      2 [] false :=
    .recursive prbPreFamilyAContextReplay 2 [] false `next
      prbValidationNextDomain (prbValidationFamilyApp prbValidationAExpr)
      .default noParameterTwo prbPreFamilyNextDomainHasIndOccReplay
      recursiveIndependent recursiveFieldTraceAtContext
      prbPreFamilyAFreshReplay recursiveViewTailTraceExact
  have recursiveViewRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp prbValidationAExpr) .default)
      2 [] false 998 =
        .ok recursiveViewTrace := by
    simp only [prbValidationAfterA,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterTwo] at parameterAt
      contradiction
    · split
      · rename_i nonrecursive
        rw [prbPreFamilyNextDomainHasIndOccReplay] at nonrecursive
        contradiction
      · rw [dif_pos recursiveIndependent]
        rw [recursiveFieldRunAtContext]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos prbPreFamilyAFreshReplay]
        rw [recursiveViewTailRunExact]
        rfl
  obtain ⟨afterATrace, afterARun⟩ :
      ∃ afterATrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
          prbValidationAfterA 2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationAfterA 2 [] false 998 = .ok afterATrace := by
    change ∃ afterATrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp prbValidationAExpr) .default)
        2 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
          (.forallE `next prbValidationNextDomain
            (prbValidationFamilyApp prbValidationAExpr) .default)
          2 [] false 998 = .ok afterATrace
    exact ⟨recursiveViewTrace, recursiveViewRun⟩
  obtain ⟨ordinaryTailTrace, ordinaryTailRun⟩ :
      ∃ ordinaryTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          (prbPreFamilyContextReplay.pushLocalDecl `a .default
            (AddInductive.consumeTypeAnnotations prbValidationAlpha))
          (prbValidationAfterParam.bindingBody!.instantiate1
            prbPreFamilyContextReplay.freshExpr) 2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            (prbPreFamilyContextReplay.pushLocalDecl `a .default
              (AddInductive.consumeTypeAnnotations prbValidationAlpha))
            (prbValidationAfterParam.bindingBody!.instantiate1
              prbPreFamilyContextReplay.freshExpr) 2 [] false 998 =
          .ok ordinaryTailTrace := by
    rw [prbValidationConsumeAlpha]
    rw [show prbPreFamilyContextReplay.pushLocalDecl `a .default
        prbValidationAlpha = prbPreFamilyAContextReplay by rfl]
    rw [show prbValidationAfterParam.bindingBody!.instantiate1
        prbPreFamilyContextReplay.freshExpr = prbValidationAfterA by
      rw [prbPreFamilyRootFreshExprReplay]
      exact prbValidationAfterA_shape]
    exact ⟨afterATrace, afterARun⟩
  have noParameterOne :
      prbStagedUniverseInput.staged.family.validation.stats.params[1]? =
        none := by
    rw [prbStagedParamsReplay_eq]
    rfl
  have rootIndependent : AddInductive.constructorIndependentOf
      prbValidationAlpha [] = true := by
    simp [AddInductive.constructorIndependentOf]
  let ordinaryViewTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.forallE `a prbValidationAlpha
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp (.bvar 1)) .default) .default)
      1 [] false :=
    .ordinary prbPreFamilyContextReplay 1 [] false `a
      prbValidationAlpha
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp (.bvar 1)) .default)
      .default noParameterOne prbPreFamilyAlphaHasNoIndOccReplay
      rootIndependent rootAlpha rootAlphaEnsure rootAlphaConsumed
      rootAlphaAnnotations prbPreFamilyRootFreshReplay ordinaryTailTrace
  have ordinaryViewRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.forallE `a prbValidationAlpha
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp (.bvar 1)) .default) .default)
      1 [] false 999 = .ok ordinaryViewTrace := by
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterOne] at parameterAt
      contradiction
    · split
      · rw [dif_pos rootIndependent]
        rw [rootAlpha.check_eq, rootAlphaEnsure.observe_eq,
          rootAlphaConsumed.check_eq]
        simp only [Bind.bind, Except.bind]
        rw [rootAlphaAnnotations.observe_eq]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos prbPreFamilyRootFreshReplay]
        have ordinaryTailRun' :
            AddInductive.ConstructorPreFamilyViewTrace.build
                prbStagedUniverseInput.staged.family.validation.stats 0
                prbPreFamilyIndexTelescopeReplay
                (prbPreFamilyContextReplay.pushLocalDecl `a .default
                  (AddInductive.consumeTypeAnnotations prbValidationAlpha))
                ((Expr.forallE `next prbValidationNextDomain
                  (prbValidationFamilyApp (.bvar 1)) .default).instantiate1
                    prbPreFamilyContextReplay.freshExpr)
                2 [] false 998 = .ok ordinaryTailTrace := by
          simpa only [prbValidationAfterParam, Expr.bindingBody!] using
            ordinaryTailRun
        rw [ordinaryTailRun']
        rfl
      · rename_i recursive
        rw [prbPreFamilyAlphaHasNoIndOccReplay] at recursive
        contradiction
  obtain ⟨afterParamTrace, afterParamRun⟩ :
      ∃ afterParamTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          prbValidationAfterParam 1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            prbValidationAfterParam 1 [] false 999 =
          .ok afterParamTrace := by
    change ∃ afterParamTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `a prbValidationAlpha
          (.forallE `next prbValidationNextDomain
            (prbValidationFamilyApp (.bvar 1)) .default) .default)
        1 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (.forallE `a prbValidationAlpha
            (.forallE `next prbValidationNextDomain
              (prbValidationFamilyApp (.bvar 1)) .default) .default)
          1 [] false 999 = .ok afterParamTrace
    exact ⟨ordinaryViewTrace, ordinaryViewRun⟩
  obtain ⟨parameterTailTrace, parameterTailRun⟩ :
      ∃ parameterTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
            prbValidationAlpha) 1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
              prbValidationAlpha) 1 [] false 999 =
          .ok parameterTailTrace := by
    rw [prbValidationAfterParam_shape]
    exact ⟨afterParamTrace, afterParamRun⟩
  have parameterAtZero :
      prbStagedUniverseInput.staged.family.validation.stats.params[0]? =
        some prbValidationAlpha := by
    rw [prbStagedParamsReplay_eq]
    rfl
  obtain ⟨rawViewTrace, rawViewRun⟩ :
      ∃ rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          propRecursiveBoundaryKernelCtor.type 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            propRecursiveBoundaryKernelCtor.type 0 [] false 1000 =
          .ok rawViewTrace := by
    change ∃ rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `α (.sort (.succ (.param `u)))
          propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
        0 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (.forallE `α (.sort (.succ (.param `u)))
            propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
          0 [] false 1000 = .ok rawViewTrace
    let rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `α (.sort (.succ (.param `u)))
          propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
        0 [] false :=
      .parameter prbPreFamilyContextReplay 0 [] false `α
        (.sort (.succ (.param `u)))
        propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit
        prbValidationAlpha parameterAtZero parameterTailTrace
    refine ⟨rawViewTrace, ?_⟩
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [parameterAtZero] at parameterAt
      cases parameterAt
      rw [parameterTailRun]
      rfl
    · rename_i noParameter
      rw [parameterAtZero] at noParameter
      contradiction
  obtain ⟨headTrace, headRun⟩ :
      ∃ headTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          prbCandidate.families.singleton.constructors.singleton.type.view
          0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            prbCandidate.families.singleton.constructors.singleton.type.view
            0 [] false 1000 = .ok headTrace := by
    rw [prbCtorView_eq]
    exact ⟨rawViewTrace, rawViewRun⟩
  let listTrace : AddInductive.ConstructorPreFamilyListTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) :=
    .cons headTrace .nil
  have listRun : AddInductive.ConstructorPreFamilyListTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) =
        .ok listTrace := by
    exact AddInductive.ConstructorPreFamilyListTrace.cons_build_eq
      headTrace (by
        rw [prbPreFamilyRootInductiveFuelReplay]
        exact headRun)
      .nil rfl
  have parametersRun : AddInductive.instantiateFamilyParameters
      propRecursiveBoundaryKernelType.type
      prbStagedUniverseInput.staged.family.validation.stats.params.toList =
        .ok prbPreFamilyIndexTelescopeReplay := by
    rw [prbStagedParamsReplay_eq]
    simp [propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal,
      AddInductive.instantiateFamilyParameters,
      prbPreFamilyIndexTelescopeReplay, prbValidationAlpha,
      prbValidationAName, Expr.bindingName!,
      Expr.instantiate1_eq, Expr.instantiate1',
      Pure.pure, Except.pure]
  unfold AddInductive.checkConstructorPreFamilySafety
  have translationUnique :
      (AddInductive.theoryTranslationUnique
          propRecursiveBoundaryKernelType.type &&
        (AddInductive.CandidateList.cons
          prbCandidate.families.singleton.constructors.singleton
          (AddInductive.CandidateList.nil : AddInductive.CandidateList
            AddInductive.CandidateConstructor [])).viewTranslationUnique) =
        true := by
    change (AddInductive.theoryTranslationUnique
      propRecursiveBoundaryKernelType.type &&
      (prbCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique &&
        true)) = true
    rw [prbCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique_eq]
    change (AddInductive.theoryTranslationUnique
      propRecursiveBoundaryKernelType.type &&
      (AddInductive.theoryTranslationUnique
        prbCandidate.families.singleton.constructors.singleton.type.view &&
        true)) = true
    rw [prbCtorView_eq]
    simp [AddInductive.theoryTranslationUnique,
      propRecursiveBoundaryKernelType, propRecursiveBoundaryKernelCtor,
      propRecursiveBoundaryInfo, propRecursiveBoundaryMkInfo,
      ConstantInfo.type, ConstantInfo.toConstantVal]
  rw [if_pos translationUnique]
  rw [parametersRun]
  simp only [Bind.bind, Except.bind]
  rw [listRun]
  rfl

theorem prbSafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        prbStagedPostFamilyInput.universeInput.staged.family.validation.stats
        prbCandidate.families.singleton.familyType.type.view
        prbCandidate.families.singleton.constructors
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  simpa [prbStagedPostFamilyInput,
    VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun] using
    prbSafetyRunDirect

noncomputable def prbStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    prbStagedPostFamilyInput prbSafetyRun

/-! ## Exact produced generation packages -/

def cvmCanonicalFamily :
    AddInductive.CandidateFamily constructorValidityMatrixKernelType where
  familyType := cvmCandidate.families.singleton.familyType
  constructors := .cons
    cvmCandidate.families.singleton.constructors.singleton .nil

def cvmCanonicalCandidate :
    AddInductive.NormalizationCandidate [constructorValidityMatrixKernelType] where
  families := .cons cvmCanonicalFamily .nil

theorem cvmOneCtorCandidate_eta
    (candidate : AddInductive.NormalizationCandidate
      [constructorValidityMatrixKernelType]) :
    candidate = {
      families := .cons {
        familyType := candidate.families.singleton.familyType
        constructors := .cons
          candidate.families.singleton.constructors.singleton .nil }
        .nil } := by
  cases candidate with
  | mk families =>
      cases families with
      | cons family tail =>
          cases tail
          cases family with
          | mk familyType constructors =>
              cases constructors with
              | cons constructor tail =>
                  cases tail
                  rfl

theorem cvmCandidate_eq_canonical : cvmCandidate = cvmCanonicalCandidate := by
  simpa [cvmCanonicalCandidate, cvmCanonicalFamily] using
    cvmOneCtorCandidate_eta cvmCandidate

theorem cvmCanonicalCandidate_produced :
    AddInductive.buildNormalizationCandidate 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext = .ok cvmCanonicalCandidate := by
  rw [← cvmCandidate_eq_canonical]
  exact cvmCandidate_produced

noncomputable abbrev cvmCanonicalStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCanonicalCandidate constructorValidityMatrixDecl :=
  cvmCandidate_eq_canonical ▸ cvmStagedPreFamilyInput

def cvmFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun VEnv.empty [`u]
      cvmCanonicalCandidate.families.singleton.familyType.type
      constructorValidityMatrixType.type :=
  cvmFamilyStage.type.rootInput.semanticOfIdentity
    cvmFamilyIdentityEvidence.identity

def cvmCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors.singleton.type
      constructorValidityMatrixType.ctors[0].type :=
  cvmCtorStagedInput.type.rootInput.semanticOfIdentity
    cvmCtorIdentityEvidence.identity

def cvmCtorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors.singleton
      constructorValidityMatrixType.ctors[0] where
  name_eq := cvmCtorNames_eq
  uvars_eq := rfl
  type := cvmCtorSemanticRootRun

def cvmConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors
      constructorValidityMatrixType.ctors :=
  .cons cvmCtorSemanticRun .nil

def cvmFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun VEnv.empty [`u]
      cvmCanonicalCandidate.families.singleton constructorValidityMatrixType where
  name_eq := cvmFamilyNames_eq
  uvars_eq := rfl
  type := cvmFamilySemanticRootRun
  typeEnv := cvmTypeEnv
  addType := cvmTypeEnv_add
  constructors := cvmConstructorSemanticListRun

def cvmReferenceNormalization :
    VInductDecl.NormalizationCandidateSemanticRun VEnv.empty [`u]
      cvmCanonicalCandidate constructorValidityMatrixDecl where
  raw := constructorValidityMatrixType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := cvmFamilySemanticRun

theorem cvmCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape
      constructorValidityMatrixDecl constructorValidityMatrixType
      cvmCanonicalCandidate = true := by
  rw [← cvmCandidate_eq_canonical]
  unfold VInductDecl.normalizationCandidateGenerationShape
  rw [AddInductive.CandidateList.singleton_eta
    cvmCandidate.families.singleton.constructors]
  have familyStored := cvmFamilyIdentityEvidence.identity.storedSpine
  have familyLength := cvmFamilyIdentityEvidence.spineLength_eq.trans
    cvmFamilyIdentityReplay_shape.1
  have ctorStored := cvmCtorIdentityEvidence.identity.storedSpine
  have ctorLength := cvmCtorIdentityEvidence.spineLength_eq.trans
    cvmCtorIdentityReplay_shape.1
  simp [VInductDecl.candidateConstructorSemanticGenerationShape,
    constructorValidityMatrixDecl, constructorValidityMatrixType,
    VExpr.telN, VExpr.dropN, VInductDecl.ctorFields,
    familyStored, familyLength, ctorStored, ctorLength]

abbrev cvmProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate constructorValidityMatrixDecl
      constructorValidityMatrixType constructorValidityMatrixKernelType 0
      false constructorValidityMatrixContext where
  candidate := cvmCanonicalCandidate
  produced := cvmCanonicalCandidate_produced
  shape := cvmCandidate_generationShape

private theorem cvmCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun VEnv.empty
      [`u] cvmCanonicalCandidate constructorValidityMatrixDecl) :
    normalization.root.normalization.generation? =
      some constructorValidityMatrixGenerationChecked := by
  rw [cvmCanonicalStagedPreFamilyInput.normalization_eq normalization
    cvmReferenceNormalization]
  have hnorm : cvmReferenceNormalization.root.normalization =
      VInductDecl.Normalization.identity constructorValidityMatrixDecl := by
    apply normalization_eq_of_view_eq
    rfl
  rw [hnorm]
  rfl

theorem cvmExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      VEnv.empty [`u] cvmProducedGenerationShapeCandidate
      constructorValidityMatrixGenerationChecked) :=
  cvmProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    cvmCanonicalStagedPreFamilyInput
      (stagedPreFamily_transport_raw cvmCandidate_eq_canonical
        cvmStagedPreFamilyInput).symm
      constructorValidityMatrixGenerationChecked
    cvmCandidate_analysis

private noncomputable def cvmExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage VEnv.empty [`u]
      cvmProducedGenerationShapeCandidate
      constructorValidityMatrixGenerationChecked :=
  Classical.choice cvmExactProducedGenerationCandidatePackage_exists

noncomputable def cvmGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      cvmExactProducedGenerationCandidatePackage.normalization
      constructorValidityMatrixGenerationChecked :=
  cvmExactProducedGenerationCandidatePackage.semantic

noncomputable def cvmProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage VEnv.empty [`u] :=
  cvmExactProducedGenerationCandidatePackage.package

def cvmGenerationCertificate :
    constructorValidityMatrixDecl.GenerationCertificate VEnv.empty where
  generation := constructorValidityMatrixGenerationChecked
  wf := cvmExactProducedGenerationCandidatePackage.semantic.run.wf

def cvmCertifiedFinalEnv : VEnv :=
  (VEnv.empty.addInductGeneration
    constructorValidityMatrixGenerationChecked).get!

theorem cvm_addInductGeneration :
    VEnv.empty.addInductGeneration
        constructorValidityMatrixGenerationChecked =
      some cvmCertifiedFinalEnv := by
  rfl

theorem cvm_addInductCertified :
    VEnv.empty.addInductCertified cvmGenerationCertificate =
      some cvmCertifiedFinalEnv :=
  cvm_addInductGeneration

theorem cvmGeneration_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty cvmCertifiedFinalEnv
      constructorValidityMatrixGenerationChecked) :=
  VEnv.addInductGeneration_trace cvm_addInductGeneration

theorem cvmCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty cvmCertifiedFinalEnv
      constructorValidityMatrixGenerationChecked) :=
  cvmGeneration_trace

theorem cvmCertified_ordered : cvmCertifiedFinalEnv.Ordered :=
  VEnv.addInductCertified_WF .empty cvm_addInductCertified

def prbCanonicalFamily :
    AddInductive.CandidateFamily propRecursiveBoundaryKernelType where
  familyType := prbCandidate.families.singleton.familyType
  constructors := .cons
    prbCandidate.families.singleton.constructors.singleton .nil

def prbCanonicalCandidate :
    AddInductive.NormalizationCandidate [propRecursiveBoundaryKernelType] where
  families := .cons prbCanonicalFamily .nil

theorem prbOneCtorCandidate_eta
    (candidate : AddInductive.NormalizationCandidate
      [propRecursiveBoundaryKernelType]) :
    candidate = {
      families := .cons {
        familyType := candidate.families.singleton.familyType
        constructors := .cons
          candidate.families.singleton.constructors.singleton .nil }
        .nil } := by
  cases candidate with
  | mk families =>
      cases families with
      | cons family tail =>
          cases tail
          cases family with
          | mk familyType constructors =>
              cases constructors with
              | cons constructor tail =>
                  cases tail
                  rfl

theorem prbCandidate_eq_canonical : prbCandidate = prbCanonicalCandidate := by
  simpa [prbCanonicalCandidate, prbCanonicalFamily] using
    prbOneCtorCandidate_eta prbCandidate

theorem prbCanonicalCandidate_produced :
    AddInductive.buildNormalizationCandidate 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext = .ok prbCanonicalCandidate := by
  rw [← prbCandidate_eq_canonical]
  exact prbCandidate_produced

noncomputable abbrev prbCanonicalStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCanonicalCandidate propRecursiveBoundaryDecl :=
  prbCandidate_eq_canonical ▸ prbStagedPreFamilyInput

def prbFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun VEnv.empty [`u]
      prbCanonicalCandidate.families.singleton.familyType.type
      propRecursiveBoundaryType.type :=
  prbFamilyStage.type.rootInput.semanticOfIdentity
    prbFamilyIdentityEvidence.identity

def prbCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors.singleton.type
      propRecursiveBoundaryType.ctors[0].type :=
  prbCtorStagedInput.type.rootInput.semanticOfIdentity
    prbCtorIdentityEvidence.identity

def prbCtorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors.singleton
      propRecursiveBoundaryType.ctors[0] where
  name_eq := prbCtorNames_eq
  uvars_eq := rfl
  type := prbCtorSemanticRootRun

def prbConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors
      propRecursiveBoundaryType.ctors :=
  .cons prbCtorSemanticRun .nil

def prbFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun VEnv.empty [`u]
      prbCanonicalCandidate.families.singleton propRecursiveBoundaryType where
  name_eq := prbFamilyNames_eq
  uvars_eq := rfl
  type := prbFamilySemanticRootRun
  typeEnv := prbTypeEnv
  addType := prbTypeEnv_add
  constructors := prbConstructorSemanticListRun

def prbReferenceNormalization :
    VInductDecl.NormalizationCandidateSemanticRun VEnv.empty [`u]
      prbCanonicalCandidate propRecursiveBoundaryDecl where
  raw := propRecursiveBoundaryType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := prbFamilySemanticRun

theorem prbCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape
      propRecursiveBoundaryDecl propRecursiveBoundaryType
        prbCanonicalCandidate =
        true := by
  rw [← prbCandidate_eq_canonical]
  unfold VInductDecl.normalizationCandidateGenerationShape
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors]
  have familyStored := prbFamilyIdentityEvidence.identity.storedSpine
  have familyLength := prbFamilyIdentityEvidence.spineLength_eq.trans
    prbFamilyIdentityReplay_shape.1
  have ctorStored := prbCtorIdentityEvidence.identity.storedSpine
  have ctorLength := prbCtorIdentityEvidence.spineLength_eq.trans
    prbCtorIdentityReplay_shape.1
  simp [VInductDecl.candidateConstructorSemanticGenerationShape,
    propRecursiveBoundaryDecl, propRecursiveBoundaryType,
    VExpr.telN, VExpr.dropN, VInductDecl.ctorFields,
    familyStored, familyLength, ctorStored, ctorLength]

abbrev prbProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate propRecursiveBoundaryDecl
      propRecursiveBoundaryType propRecursiveBoundaryKernelType 0 false
      propRecursiveBoundaryContext where
  candidate := prbCanonicalCandidate
  produced := prbCanonicalCandidate_produced
  shape := prbCandidate_generationShape

private theorem prbCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun VEnv.empty
      [`u] prbCanonicalCandidate propRecursiveBoundaryDecl) :
    normalization.root.normalization.generation? =
      some propRecursiveBoundaryGenerationChecked := by
  rw [prbCanonicalStagedPreFamilyInput.normalization_eq normalization
    prbReferenceNormalization]
  have hnorm : prbReferenceNormalization.root.normalization =
      VInductDecl.Normalization.identity propRecursiveBoundaryDecl := by
    apply normalization_eq_of_view_eq
    rfl
  rw [hnorm]
  rfl

theorem prbExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      VEnv.empty [`u] prbProducedGenerationShapeCandidate
      propRecursiveBoundaryGenerationChecked) :=
  prbProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    prbCanonicalStagedPreFamilyInput
    (stagedPreFamily_transport_raw prbCandidate_eq_canonical
      prbStagedPreFamilyInput).symm propRecursiveBoundaryGenerationChecked
    prbCandidate_analysis

private noncomputable def prbExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage VEnv.empty [`u]
      prbProducedGenerationShapeCandidate
      propRecursiveBoundaryGenerationChecked :=
  Classical.choice prbExactProducedGenerationCandidatePackage_exists

noncomputable def prbGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      prbExactProducedGenerationCandidatePackage.normalization
      propRecursiveBoundaryGenerationChecked :=
  prbExactProducedGenerationCandidatePackage.semantic

noncomputable def prbProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage VEnv.empty [`u] :=
  prbExactProducedGenerationCandidatePackage.package

def prbGenerationCertificate :
    propRecursiveBoundaryDecl.GenerationCertificate VEnv.empty where
  generation := propRecursiveBoundaryGenerationChecked
  wf := prbExactProducedGenerationCandidatePackage.semantic.run.wf

def prbCertifiedFinalEnv : VEnv :=
  (VEnv.empty.addInductGeneration propRecursiveBoundaryGenerationChecked).get!

theorem prb_addInductGeneration :
    VEnv.empty.addInductGeneration propRecursiveBoundaryGenerationChecked =
      some prbCertifiedFinalEnv := by
  rfl

theorem prb_addInductCertified :
    VEnv.empty.addInductCertified prbGenerationCertificate =
      some prbCertifiedFinalEnv :=
  prb_addInductGeneration

theorem prbGeneration_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty prbCertifiedFinalEnv
      propRecursiveBoundaryGenerationChecked) :=
  VEnv.addInductGeneration_trace prb_addInductGeneration

theorem prbCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty prbCertifiedFinalEnv
      propRecursiveBoundaryGenerationChecked) :=
  prbGeneration_trace

theorem prbCertified_ordered : prbCertifiedFinalEnv.Ordered :=
  VEnv.addInductCertified_WF .empty prb_addInductCertified

/-! ## Actual kernel-metadata replay -/

def cvmReplayCtorEnv : VEnv :=
  (cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
    constructorValidityMatrixType.ctors[0].toVConstant).get!

def cvmReplayRecEnv : VEnv :=
  (cvmReplayCtorEnv.addConst ``ConstructorValidityMatrix.rec
    constructorValidityMatrixGenerationChecked.recursor).get!

theorem cvmRawCtor_wf :
    constructorValidityMatrixType.ctors[0].toVConstant.WF cvmTypeEnv :=
  cvmRawCtor_isType

theorem cvmReplayCtorEnv_ordered : cvmReplayCtorEnv.Ordered :=
  .const (n := constructorValidityMatrixType.ctors[0].name)
    (ci := constructorValidityMatrixType.ctors[0].toVConstant)
    cvmTypeEnv_ordered cvmRawCtor_wf rfl

theorem cvmGenerationEnv :
    VInductDecl.GenerationEnv constructorValidityMatrixGenerationChecked
      cvmReplayCtorEnv := by
  apply cvmGenerationCertificate.wf.toGenerationEnv (envT := cvmTypeEnv)
  · rfl
  · exact (VEnv.addConst_le cvmTypeEnv_add).trans
      (VEnv.addConst_le (show
        cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
          constructorValidityMatrixType.ctors[0].toVConstant =
            some cvmReplayCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
        constructorValidityMatrixType.ctors[0].toVConstant =
          some cvmReplayCtorEnv from rfl)
  · exact cvmReplayCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨constructorValidityMatrixType.ctors[0],
        constructorValidityMatrixChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem cvmInfo_tr :
    TrConstVal .safe VEnv.empty constructorValidityMatrixInfo
      constructorValidityMatrixType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty
      constructorValidityMatrixInfo.levelParams []
      constructorValidityMatrixInfo.type
      constructorValidityMatrixType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := cvmRawFamily_isType
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem cvmMkInfo_tr :
    TrConstVal .safe cvmTypeEnv constructorValidityMatrixMkInfo
      constructorValidityMatrixType.ctors[0] := by
  exact ⟨⟨by decide, rfl, cvmCtorSource_tr⟩, rfl⟩

theorem cvmRecInfo_tr :
    TrConstVal .safe cvmReplayCtorEnv constructorValidityMatrixRecInfo
      (inductGenerationRecVal constructorValidityMatrixGenerationChecked) := by
  have hfamily : cvmReplayCtorEnv.constants
      ``ConstructorValidityMatrix =
        some constructorValidityMatrixType.toVConstant := rfl
  have hmk : cvmReplayCtorEnv.constants
      ``ConstructorValidityMatrix.mk =
        some constructorValidityMatrixType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr cvmReplayCtorEnv
      constructorValidityMatrixRecInfo.levelParams []
      constructorValidityMatrixRecInfo.type
      (inductGenerationRecVal
        constructorValidityMatrixGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := cvmGenerationEnv.recursor_wf
  exact hshape.to_trExprS cvmReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def cvmReplayTypeMap : ConstMap :=
  ({} : ConstMap).insert constructorValidityMatrixType.name
    constructorValidityMatrixInfo

def cvmReplayCtorMap : ConstMap :=
  cvmReplayTypeMap.insert constructorValidityMatrixType.ctors[0].name
    constructorValidityMatrixMkInfo

def cvmReplayMap : ConstMap :=
  cvmReplayCtorMap.insert ``ConstructorValidityMatrix.rec
    constructorValidityMatrixRecInfo

theorem cvmReplayType_fresh :
    ({} : ConstMap).find? constructorValidityMatrixType.name = none := by
  simp [SMap.find?]

theorem cvmReplayTypeMap_wf : cvmReplayTypeMap.WF :=
  SMap.WF.empty.insert _ _ cvmReplayType_fresh

theorem cvmReplayMk_fresh :
    cvmReplayTypeMap.find? constructorValidityMatrixType.ctors[0].name =
      none := by
  rw [cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType, SMap.find?]

theorem cvmReplayCtorMap_wf : cvmReplayCtorMap.WF :=
  cvmReplayTypeMap_wf.insert _ _ cvmReplayMk_fresh

theorem cvmReplayRec_fresh :
    cvmReplayCtorMap.find? ``ConstructorValidityMatrix.rec = none := by
  rw [cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert,
    cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType, SMap.find?]

noncomputable def cvmAddInductTraceChecked :
    AddInductTrace ({} : ConstMap) VEnv.empty constructorValidityMatrixDecl
      cvmReplayMap cvmCertifiedFinalEnv := by
  refine cvmProducedGenerationCandidatePackage.package.addInductTrace
    cvmReplayTypeMap cvmTypeEnv cvmReplayCtorMap cvmReplayCtorEnv
    cvmReplayRecEnv ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := constructorValidityMatrixInfo
      kind_eq := by
        simp [constructorValidityMatrixInfo, InductConstantKind.Matches]
      tr := cvmInfo_tr
      map_fresh := cvmReplayType_fresh
      env_add := cvmTypeEnv_add
      map_add := rfl }
  · exact .cons {
      info := constructorValidityMatrixMkInfo
      kind_eq := by
        simp [constructorValidityMatrixMkInfo, InductConstantKind.Matches]
      tr := cvmMkInfo_tr
      map_fresh := by
        simpa [constructorValidityMatrixType] using cvmReplayMk_fresh
      env_add := rfl
      map_add := rfl } .nil
  · exact {
      info := constructorValidityMatrixRecInfo
      kind_eq := by
        simp [constructorValidityMatrixRecInfo, InductConstantKind.Matches]
      tr := cvmRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            cvmProducedGenerationCandidatePackage.package.generation).name =
              ``ConstructorValidityMatrix.rec by rfl]
        exact cvmReplayRec_fresh
      env_add := rfl
      map_add := rfl }

theorem cvm_addInduct_checked :
    AddInduct ({} : ConstMap) VEnv.empty constructorValidityMatrixDecl
      cvmReplayMap cvmCertifiedFinalEnv :=
  ⟨cvmAddInductTraceChecked⟩

theorem cvm_trEnv'_checked :
    TrEnv' .safe cvmReplayMap false cvmCertifiedFinalEnv :=
  .induct cvm_addInduct_checked .empty

theorem cvm_env_wf_checked : cvmCertifiedFinalEnv.WF :=
  cvm_trEnv'_checked.wf

theorem cvm_aligned_checked :
    Aligned .safe cvmReplayMap cvmCertifiedFinalEnv :=
  cvm_trEnv'_checked.aligned

theorem cvmReplay_type_map_lookup :
    cvmReplayMap.find? constructorValidityMatrixType.name =
      some constructorValidityMatrixInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert,
    cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert,
    cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType]

theorem cvmReplay_ctor_map_lookup :
    cvmReplayMap.find? constructorValidityMatrixType.ctors[0].name =
      some constructorValidityMatrixMkInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert,
    cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert]
  simp [constructorValidityMatrixType]

theorem cvmReplay_rec_map_lookup :
    cvmReplayMap.find? ``ConstructorValidityMatrix.rec =
      some constructorValidityMatrixRecInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert]
  simp

theorem cvmFinalEnv_type_lookup :
    cvmCertifiedFinalEnv.constants constructorValidityMatrixType.name =
      some constructorValidityMatrixType.toVConstant := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.family_lookup

theorem cvmFinalEnv_ctor_lookup :
    cvmCertifiedFinalEnv.constants
        constructorValidityMatrixType.ctors[0].name =
      some constructorValidityMatrixType.ctors[0].toVConstant := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem cvmFinalEnv_rec_lookup :
    cvmCertifiedFinalEnv.constants ``ConstructorValidityMatrix.rec =
      some constructorValidityMatrixGenerationChecked.recursor := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem cvmReplay_type_lookup_unique :
    constructorValidityMatrixInfo.name =
        constructorValidityMatrixType.name ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixInfo
        constructorValidityMatrixType.toVConstant :=
  cvm_aligned_checked.find?_uniq cvmReplay_type_map_lookup
    cvmFinalEnv_type_lookup

theorem cvmReplay_ctor_lookup_unique :
    constructorValidityMatrixMkInfo.name =
        constructorValidityMatrixType.ctors[0].name ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixMkInfo
        constructorValidityMatrixType.ctors[0].toVConstant :=
  cvm_aligned_checked.find?_uniq cvmReplay_ctor_map_lookup
    cvmFinalEnv_ctor_lookup

theorem cvmReplay_rec_lookup_unique :
    constructorValidityMatrixRecInfo.name =
        ``ConstructorValidityMatrix.rec ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixRecInfo
        constructorValidityMatrixGenerationChecked.recursor :=
  cvm_aligned_checked.find?_uniq cvmReplay_rec_map_lookup
    cvmFinalEnv_rec_lookup

theorem cvmFinalEnv_rule_mem :
    ∀ df ∈ constructorValidityMatrixGenerationChecked.generatedRules,
      cvmCertifiedFinalEnv.defeqs df := by
  intro df hdf
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.rule_mem hdf

theorem cvmFinalEnv_iota_mem :
    cvmCertifiedFinalEnv.defeqs
      constructorValidityMatrixGenerationChecked.generatedRules[0] := by
  apply cvmFinalEnv_rule_mem
  exact .head _

def prbReplayCtorEnv : VEnv :=
  (prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
    propRecursiveBoundaryType.ctors[0].toVConstant).get!

def prbReplayRecEnv : VEnv :=
  (prbReplayCtorEnv.addConst ``PropRecursiveBoundary.rec
    propRecursiveBoundaryGenerationChecked.recursor).get!

theorem prbRawCtor_wf :
    propRecursiveBoundaryType.ctors[0].toVConstant.WF prbTypeEnv :=
  prbRawCtor_isType

theorem prbReplayCtorEnv_ordered : prbReplayCtorEnv.Ordered :=
  .const (n := propRecursiveBoundaryType.ctors[0].name)
    (ci := propRecursiveBoundaryType.ctors[0].toVConstant)
    prbTypeEnv_ordered prbRawCtor_wf rfl

theorem prbGenerationEnv :
    VInductDecl.GenerationEnv propRecursiveBoundaryGenerationChecked
      prbReplayCtorEnv := by
  apply prbGenerationCertificate.wf.toGenerationEnv (envT := prbTypeEnv)
  · rfl
  · exact (VEnv.addConst_le prbTypeEnv_add).trans
      (VEnv.addConst_le (show
        prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
          propRecursiveBoundaryType.ctors[0].toVConstant =
            some prbReplayCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
        propRecursiveBoundaryType.ctors[0].toVConstant =
          some prbReplayCtorEnv from rfl)
  · exact prbReplayCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨propRecursiveBoundaryType.ctors[0],
        propRecursiveBoundaryChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem prbInfo_tr :
    TrConstVal .safe VEnv.empty propRecursiveBoundaryInfo
      propRecursiveBoundaryType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty
      propRecursiveBoundaryInfo.levelParams []
      propRecursiveBoundaryInfo.type propRecursiveBoundaryType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := prbRawFamily_isType
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem prbMkInfo_tr :
    TrConstVal .safe prbTypeEnv propRecursiveBoundaryMkInfo
      propRecursiveBoundaryType.ctors[0] := by
  exact ⟨⟨by decide, rfl, prbCtorSource_tr⟩, rfl⟩

theorem prbRecInfo_tr :
    TrConstVal .safe prbReplayCtorEnv propRecursiveBoundaryRecInfo
      (inductGenerationRecVal propRecursiveBoundaryGenerationChecked) := by
  have hfamily : prbReplayCtorEnv.constants ``PropRecursiveBoundary =
      some propRecursiveBoundaryType.toVConstant := rfl
  have hmk : prbReplayCtorEnv.constants ``PropRecursiveBoundary.mk =
      some propRecursiveBoundaryType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr prbReplayCtorEnv
      propRecursiveBoundaryRecInfo.levelParams []
      propRecursiveBoundaryRecInfo.type
      (inductGenerationRecVal propRecursiveBoundaryGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := prbGenerationEnv.recursor_wf
  exact hshape.to_trExprS prbReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def prbReplayTypeMap : ConstMap :=
  ({} : ConstMap).insert propRecursiveBoundaryType.name
    propRecursiveBoundaryInfo

def prbReplayCtorMap : ConstMap :=
  prbReplayTypeMap.insert propRecursiveBoundaryType.ctors[0].name
    propRecursiveBoundaryMkInfo

def prbReplayMap : ConstMap :=
  prbReplayCtorMap.insert ``PropRecursiveBoundary.rec
    propRecursiveBoundaryRecInfo

theorem prbReplayType_fresh :
    ({} : ConstMap).find? propRecursiveBoundaryType.name = none := by
  simp [SMap.find?]

theorem prbReplayTypeMap_wf : prbReplayTypeMap.WF :=
  SMap.WF.empty.insert _ _ prbReplayType_fresh

theorem prbReplayMk_fresh :
    prbReplayTypeMap.find? propRecursiveBoundaryType.ctors[0].name =
      none := by
  rw [prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType, SMap.find?]

theorem prbReplayCtorMap_wf : prbReplayCtorMap.WF :=
  prbReplayTypeMap_wf.insert _ _ prbReplayMk_fresh

theorem prbReplayRec_fresh :
    prbReplayCtorMap.find? ``PropRecursiveBoundary.rec = none := by
  rw [prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert,
    prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType, SMap.find?]

noncomputable def prbAddInductTraceChecked :
    AddInductTrace ({} : ConstMap) VEnv.empty propRecursiveBoundaryDecl
      prbReplayMap prbCertifiedFinalEnv := by
  refine prbProducedGenerationCandidatePackage.package.addInductTrace
    prbReplayTypeMap prbTypeEnv prbReplayCtorMap prbReplayCtorEnv
    prbReplayRecEnv ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := propRecursiveBoundaryInfo
      kind_eq := by
        simp [propRecursiveBoundaryInfo, InductConstantKind.Matches]
      tr := prbInfo_tr
      map_fresh := prbReplayType_fresh
      env_add := prbTypeEnv_add
      map_add := rfl }
  · exact .cons {
      info := propRecursiveBoundaryMkInfo
      kind_eq := by
        simp [propRecursiveBoundaryMkInfo, InductConstantKind.Matches]
      tr := prbMkInfo_tr
      map_fresh := by
        simpa [propRecursiveBoundaryType] using prbReplayMk_fresh
      env_add := rfl
      map_add := rfl } .nil
  · exact {
      info := propRecursiveBoundaryRecInfo
      kind_eq := by
        simp [propRecursiveBoundaryRecInfo, InductConstantKind.Matches]
      tr := prbRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            prbProducedGenerationCandidatePackage.package.generation).name =
              ``PropRecursiveBoundary.rec by rfl]
        exact prbReplayRec_fresh
      env_add := rfl
      map_add := rfl }

theorem prb_addInduct_checked :
    AddInduct ({} : ConstMap) VEnv.empty propRecursiveBoundaryDecl
      prbReplayMap prbCertifiedFinalEnv :=
  ⟨prbAddInductTraceChecked⟩

theorem prb_trEnv'_checked :
    TrEnv' .safe prbReplayMap false prbCertifiedFinalEnv :=
  .induct prb_addInduct_checked .empty

theorem prb_env_wf_checked : prbCertifiedFinalEnv.WF :=
  prb_trEnv'_checked.wf

theorem prb_aligned_checked :
    Aligned .safe prbReplayMap prbCertifiedFinalEnv :=
  prb_trEnv'_checked.aligned

theorem prbReplay_type_map_lookup :
    prbReplayMap.find? propRecursiveBoundaryType.name =
      some propRecursiveBoundaryInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert,
    prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert,
    prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType]

theorem prbReplay_ctor_map_lookup :
    prbReplayMap.find? propRecursiveBoundaryType.ctors[0].name =
      some propRecursiveBoundaryMkInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert,
    prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert]
  simp [propRecursiveBoundaryType]

theorem prbReplay_rec_map_lookup :
    prbReplayMap.find? ``PropRecursiveBoundary.rec =
      some propRecursiveBoundaryRecInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert]
  simp

theorem prbFinalEnv_type_lookup :
    prbCertifiedFinalEnv.constants propRecursiveBoundaryType.name =
      some propRecursiveBoundaryType.toVConstant := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.family_lookup

theorem prbFinalEnv_ctor_lookup :
    prbCertifiedFinalEnv.constants propRecursiveBoundaryType.ctors[0].name =
      some propRecursiveBoundaryType.ctors[0].toVConstant := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem prbFinalEnv_rec_lookup :
    prbCertifiedFinalEnv.constants ``PropRecursiveBoundary.rec =
      some propRecursiveBoundaryGenerationChecked.recursor := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem prbReplay_type_lookup_unique :
    propRecursiveBoundaryInfo.name = propRecursiveBoundaryType.name ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryInfo
        propRecursiveBoundaryType.toVConstant :=
  prb_aligned_checked.find?_uniq prbReplay_type_map_lookup
    prbFinalEnv_type_lookup

theorem prbReplay_ctor_lookup_unique :
    propRecursiveBoundaryMkInfo.name =
        propRecursiveBoundaryType.ctors[0].name ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryMkInfo
        propRecursiveBoundaryType.ctors[0].toVConstant :=
  prb_aligned_checked.find?_uniq prbReplay_ctor_map_lookup
    prbFinalEnv_ctor_lookup

theorem prbReplay_rec_lookup_unique :
    propRecursiveBoundaryRecInfo.name = ``PropRecursiveBoundary.rec ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryRecInfo
        propRecursiveBoundaryGenerationChecked.recursor :=
  prb_aligned_checked.find?_uniq prbReplay_rec_map_lookup
    prbFinalEnv_rec_lookup

theorem prbFinalEnv_rule_mem :
    ∀ df ∈ propRecursiveBoundaryGenerationChecked.generatedRules,
      prbCertifiedFinalEnv.defeqs df := by
  intro df hdf
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.rule_mem hdf

theorem prbFinalEnv_iota_mem :
    prbCertifiedFinalEnv.defeqs
      propRecursiveBoundaryGenerationChecked.generatedRules[0] := by
  apply prbFinalEnv_rule_mem
  exact .head _

end Lean4Lean.InductiveReplayFixtures
