import Lean4Lean.Verify.Environment.ConstructorValidityMatrix

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

theorem cvmFamilyIdentityCheck :
    TypeChecker.CandidateExprIdentity.check
      cvmCandidate.families.singleton.familyType.type.trace = true := by
  native_decide

theorem cvmCtorIdentityCheck :
    TypeChecker.CandidateExprIdentity.check
      cvmCandidate.families.singleton.constructors.singleton.type.trace =
        true := by
  native_decide

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
  terminal_eq :=
    TypeChecker.CandidateExprIdentity.terminalResult_eq_of_check
      (by native_decide)
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      constructorValidityMatrixKernelType
      cvmCandidate.families.singleton.familyType.type.trace
      2 (.succ (.param `u)) k
      cvmFamilyClosed (by native_decide) (by native_decide)
      cvmFamilyValidationAnnotations
      (TypeChecker.CandidateExprIdentity.terminalResult_eq_of_check
      (by native_decide))
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
  native_decide

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

theorem prbFamilyIdentityCheck :
    TypeChecker.CandidateExprIdentity.check
      prbCandidate.families.singleton.familyType.type.trace = true := by
  native_decide

theorem prbCtorIdentityCheck :
    TypeChecker.CandidateExprIdentity.check
      prbCandidate.families.singleton.constructors.singleton.type.trace =
        true := by
  native_decide

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
  terminal_eq :=
    TypeChecker.CandidateExprIdentity.terminalResult_eq_of_check
      (by native_decide)
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      propRecursiveBoundaryKernelType
      prbCandidate.families.singleton.familyType.type.trace
      1 .zero k
      prbFamilyClosed (by native_decide) (by native_decide)
      prbFamilyValidationAnnotations
      (TypeChecker.CandidateExprIdentity.terminalResult_eq_of_check
      (by native_decide))
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
  native_decide

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
  apply exceptUnit_eq_ok_of_isOk
  native_decide

def prbConstructorValidationResult :=
  AddInductive.ConstructorValidationRun.buildExecution
    propRecursiveBoundaryKernelType prbFamilyValidationRun.stats false
    { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := prbConstructorContext.env }

theorem prbConstructorValidationResult_isOk :
    prbConstructorValidationResult.isOk = true := by
  native_decide

def prbProducedConstructorValidation :
    { validation // prbConstructorValidationResult = .ok validation } :=
  match h : prbConstructorValidationResult with
  | .ok validation => ⟨validation, rfl⟩
  | .error _ => by
      have hOk := prbConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

def prbConstructorValidation := prbProducedConstructorValidation.val

def prbStagedUniverseInput :
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
  universeRun := prbUniverseRun

theorem prbAlignmentRun :
    prbStagedUniverseInput.staged.constructorValidation.trace.checkCandidateAlignment
        prbCandidate.families.singleton.constructors
        { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := prbConstructorContext.env } = .ok () := by
  apply exceptUnit_eq_ok_of_isOk
  native_decide

noncomputable def prbStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl :=
  VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun
    prbStagedUniverseInput prbAlignmentRun

theorem prbSafetyRunDirect :
    AddInductive.checkConstructorPreFamilySafety
        prbStagedUniverseInput.staged.family.validation.stats
        prbCandidate.families.singleton.familyType.type.view
        prbCandidate.families.singleton.constructors
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  apply exceptUnit_eq_ok_of_isOk
  native_decide

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
    (TypeChecker.CandidateExprIdentity.of_check cvmFamilyIdentityCheck)

def cvmCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors.singleton.type
      constructorValidityMatrixType.ctors[0].type :=
  cvmCtorStagedInput.type.rootInput.semanticOfIdentity
    (TypeChecker.CandidateExprIdentity.of_check cvmCtorIdentityCheck)

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
  native_decide

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
    (TypeChecker.CandidateExprIdentity.of_check prbFamilyIdentityCheck)

def prbCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors.singleton.type
      propRecursiveBoundaryType.ctors[0].type :=
  prbCtorStagedInput.type.rootInput.semanticOfIdentity
    (TypeChecker.CandidateExprIdentity.of_check prbCtorIdentityCheck)

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
  native_decide

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
