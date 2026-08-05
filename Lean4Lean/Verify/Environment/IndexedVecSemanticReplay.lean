import Lean4Lean.Verify.Environment.IndexedVecOuterReplay

/-!
# Complete semantic replay of the IndexedVec normalization candidate

This module connects the exact executable family/`nil`/`cons` candidate
produced by `buildNormalizationCandidate` to its Theory generation
certificate and the E1 kernel-environment replay. Every retained candidate
node is interpreted in its exact pre-family or post-family verifier context;
the final transaction therefore consumes the certificate projected from the
same producer-selected package rather than an independently supplied
well-formedness proof.
-/

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta
open Lean4Lean.InductiveFixtures
open IndexedVecConsReplay

theorem indexedVecSemanticNatHasPrimitives : VEnv.HasPrimitives natFinalEnv := by
  have absent (n : Name) (hlookup : natFinalEnv.constants n = none) :
      ¬ natFinalEnv.contains n := by
    rintro ⟨ci, hci⟩
    rw [hlookup] at hci
    contradiction
  refine {
    bool := fun h => (absent ``Bool rfl h).elim
    boolFalse := fun h => by
      change none = some _ at h
      contradiction
    boolTrue := fun h => by
      change none = some _ at h
      contradiction
    nat := fun _ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    natZero := fun h => by
      change some natType.ctors[0].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natSucc := fun h => by
      change some natType.ctors[1].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natAdd := fun h => (absent ``Nat.add rfl h).elim
    natSub := fun h => (absent ``Nat.sub rfl h).elim
    natMul := fun h => (absent ``Nat.mul rfl h).elim
    natPow := fun h => (absent ``Nat.pow rfl h).elim
    natGcd := fun h => (absent ``Nat.gcd rfl h).elim
    natMod := fun h => (absent ``Nat.mod rfl h).elim
    natDiv := fun h => (absent ``Nat.div rfl h).elim
    natBEq := fun h => (absent ``Nat.beq rfl h).elim
    natBLE := fun h => (absent ``Nat.ble rfl h).elim
    natLAnd := fun h => (absent ``Nat.land rfl h).elim
    natLOr := fun h => (absent ``Nat.lor rfl h).elim
    natXor := fun h => (absent ``Nat.xor rfl h).elim
    natShiftLeft := fun h => (absent ``Nat.shiftLeft rfl h).elim
    natShiftRight := fun h => (absent ``Nat.shiftRight rfl h).elim
    charOfNat := fun h => by
      change none = some _ at h
      contradiction
    stringOfList := fun h => by
      change none = some _ at h
      contradiction }

theorem indexedVecSemanticNatSafePrimitives :
    indexedVecKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change natMap.find?' n = some ci at hfind
  rw [natMap_wf.find?'_eq_find?, natMap,
    natCtorMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp at hfind
    subst ci
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [natCtorMap, natZeroMap_wf.find?_insert] at hfind
    split at hfind
    · rename_i heq
      simp at heq
      subst n
      simp at hfind
      subst ci
      exact ⟨rfl, rfl⟩
    · rw [natZeroMap, natTypeMap_wf.find?_insert] at hfind
      split at hfind
      · rename_i heq
        simp at heq
        subst n
        simp at hfind
        subst ci
        exact ⟨rfl, rfl⟩
      · rw [natTypeMap,
          SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
          at hfind
        split at hfind
        · rename_i heq
          simp at heq
          subst n
          simp at hfind
          subst ci
          exact ⟨rfl, rfl⟩
        · simp [SMap.find?] at hfind

def indexedVecSemanticNatVEnvs : VEnvs where
  venv _ := natFinalEnv

theorem indexedVecSemanticNatVEnvsWF : indexedVecSemanticNatVEnvs.WF indexedVecKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ natMap false natFinalEnv
    exact nat_trEnv'.sf_mono DefinitionSafety.le_safe
  hasPrimitives := indexedVecSemanticNatHasPrimitives
  safePrimitives := indexedVecSemanticNatSafePrimitives
  mono := fun _ => .rfl

def indexedVecSemanticAddType :
    AddInductConstant .induct natMap natFinalEnv
      indexedVecType.toVConstVal indexedVecTypeMap indexedVecTypeEnv where
  info := indexedVecInfo
  kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
  tr := indexedVecInfo_tr
  map_fresh := by simpa [indexedVecType] using indexedVecType_fresh
  env_add := rfl
  map_add := rfl

theorem indexedVecSemanticFamilyPrefixNe :
    indexedVecFamilyCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedVecSemanticFamilyContextRun :
    TypeChecker.CandidateContextRun indexedVecFamilyCandidateContext :=
  TypeChecker.CandidateContextRun.root indexedVecSemanticNatVEnvsWF rfl
    indexedVecSemanticFamilyPrefixNe

theorem indexedVecSemanticFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedVecInfo.type indexedVecType.type :=
  indexedVecInfo_tr.1.2.2

def indexedVecPreFamilyStage :
    TypeChecker.CandidateSemanticStage indexedVecFamilyCandidateContext
      natFinalEnv [`u] where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

def indexedVecFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      indexedVecKernelType indexedVecFamilyCandidate.trace where
  nparams := 1
  resultLevel := .succ (.param `u)
  stats := indexedVecCandidateInductiveStats
  stats_eq := rfl
  terminal_eq := indexedVecFamilyCandidate_terminalResult
  run := indexedVec_checkInductiveTypes

def indexedVecFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecFamilyListCandidate.familyType indexedVecType
      indexedVecPreFamilyStage where
  name_eq := rfl
  uvars_eq := rfl
  type := {
    context_eq := rfl
    source_tr := indexedVecSemanticFamilySourceTr
    whnfFuel := 9999
    whnfDepth := rfl }
  validation := indexedVecFamilyValidationRun
  typeEnv := indexedVecTypeEnv
  addInduct := indexedVecSemanticAddType
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := rfl
  name_not_reflected := by decide
  name_not_primitive := by
    simp [indexedVecType, Kernel.Environment.primitives,
      NameSet.ofList]
    simp +decide [NameSet.contains]

def indexedVecSemanticCtorContextRun :
    TypeChecker.CandidateContextRun ctorContext :=
  indexedVecFamilyStage.postContextRun

theorem indexedVecSemanticNilSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecNilInfo.type
      indexedVecType.ctors[0].type :=
  indexedVecNilInfo_tr.1.2.2

theorem indexedVecSemanticConsIsType :
    indexedVecTypeEnv.IsType 1 [] indexedVecType.ctors[1].type := by
  have hwf :=
    (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
      nat_env_wf.ordered
  have hctor := hwf.rawCtor_isType (envT := indexedVecTypeEnv) rfl
    (ctor := indexedVecChecked.identityGeneration.block.ctorPairs[1])
    (by simp)
  simpa only [
    show indexedVecDecl.uvars = 1 by rfl,
    show indexedVecChecked.identityGeneration.block.ctorPairs[1].raw.type =
      indexedVecType.ctors[1].type by rfl] using hctor

theorem indexedVecSemanticConsSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecConsInfo.type
      indexedVecType.ctors[1].type := by
  have hshape : TrTypeExpr indexedVecTypeEnv [`u] []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

noncomputable def indexedVecStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  staged := {
    raw := indexedVecType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := indexedVecPreFamilyStage
    family := indexedVecFamilyStage
    constructorValidation :=
      AddInductive.ConstructorValidationRun.of_run
        indexedVecValidationCheckConstructors
    constructors := .cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := indexedVecSemanticNilSourceTr
        whnfFuel := 9999
        whnfDepth := rfl } } (.cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := indexedVecSemanticConsSourceTr
        whnfFuel := 9999
        whnfDepth := rfl } } .nil)
    familyTypesProduced := indexedVecFamilyTypeListProduced
    familiesProduced := indexedVecFamilyListProduced }
  universeRun := indexedVecValidationCheckConstructorUniverseSemantics

/-- Generic automatic assembly joins the arbitrary-length operational list
witnesses to the complete retained semantic hierarchy for the two-constructor
fixture.  No expected normalized view is an input to this theorem. -/
theorem indexedVecProducedSemanticHierarchy_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidateSemanticRun
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl) :=
  indexedVecStagedUniverseInput.exists

/-- The automatically assembled hierarchy retains both constructor headers in
the producer's `nil`/`cons` source order.  This inspects the semantic result,
not the separately constructed concrete replay below. -/
theorem indexedVecProducedSemanticHierarchy_constructorHeaders :
    ∃ run : VInductDecl.ProducedNormalizationCandidateSemanticRun
        indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
        indexedVecNormalizationCandidate indexedVecDecl,
      VInductDecl.sameCtorHeaders indexedVecType.ctors
        run.semantic.family.root.constructors.views = true := by
  obtain ⟨run⟩ := indexedVecProducedSemanticHierarchy_exists
  have hraw : run.semantic.raw = indexedVecType := by
    have htypes : [indexedVecType] = [run.semantic.raw] := by
      simpa [indexedVecDecl] using run.semantic.raw_types_eq
    injection htypes with h
    exact h.symm
  exact ⟨run, by
    simpa only [hraw] using
      run.semantic.family.root.constructors.sameHeaders⟩

/-! ## Post-family constructor alignment -/

private theorem indexedVecValidationSortCheckTypeM (lctx : LocalContext) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    checkLevelSuccParam, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

private def indexedVecValidationZeroState (alphaId : FVarId) :
    TypeChecker.State :=
  replayInsert (validationFirstAppState alphaId)
    (.const ``Nat.zero []) (.const ``Nat [])

private def indexedVecValidationZeroFinalState (alphaId : FVarId) :
    TypeChecker.State :=
  replayInsert (indexedVecValidationZeroState alphaId)
    (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero []))
    (.sort (.succ (.param `u)))

private theorem indexedVecValidationZeroCheckTypeM
    (lctx : LocalContext) (alphaId : FVarId)
    (halpha : lctx.find? alphaId = some (.cdecl alphaIndex alphaId
      alphaName (.sort (.succ (.param `u))) alphaBi alphaKind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType
        (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero []))) =
      .ok (.sort (.succ (.param `u))) := by
  have hfirst :
      TypeChecker.Inner.inferType' (replayFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (vecFamilyTail, validationFirstAppState alphaId) := by
    simpa [validationFirstAppState] using
      (replayInferFirstAppFVarCore 9999 lctx
        ({} : TypeChecker.State) alphaId
        (by simp)
        (by simp [replayInsert])
        (by simp [replayFirstApp]) halpha)
  have hzero :
      TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        (validationFirstAppState alphaId) =
      .ok (.const ``Nat [], indexedVecValidationZeroState alphaId) := by
    simpa [indexedVecValidationZeroState, replayInsert] using
      (inferTypeZeroCore 9999 lctx (validationFirstAppState alphaId)
        (by simp [validationFirstAppState, replayInsert,
          replayFirstApp]))
  have hresult :
      TypeChecker.Inner.inferType'
        (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero [])) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.param `u)),
        indexedVecValidationZeroFinalState alphaId) := by
    simpa [indexedVecValidationZeroFinalState] using
      (replayInferIndexedVecAppCore 9999 lctx
        ({} : TypeChecker.State) (validationFirstAppState alphaId)
        (indexedVecValidationZeroState alphaId) (.fvar alphaId)
        (.const ``Nat.zero [])
        (by simp [ctorIndexedVecApp, Expr.hasLooseBVars,
          Expr.looseBVarRange'])
        (by simp [ctorIndexedVecApp])
        hfirst hzero (by rfl))
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero [])) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [hresult]
  rfl

private def indexedVecValidationSuccState
    (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert (validationFirstAppState alphaId)
        (.const ``Nat.succ [])
        (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
      (.fvar nId) (.const ``Nat []))
    (replaySuccApp (.fvar nId)) (.const ``Nat [])

private def indexedVecValidationSuccFinalState
    (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert (indexedVecValidationSuccState alphaId nId)
    (ctorIndexedVecApp (.fvar alphaId) (replaySuccApp (.fvar nId)))
    (.sort (.succ (.param `u)))

private theorem indexedVecValidationSuccCheckTypeM
    (lctx : LocalContext) (alphaId nId : FVarId)
    (hne : alphaId ≠ nId)
    (halpha : lctx.find? alphaId = some (.cdecl alphaIndex alphaId
      alphaName (.sort (.succ (.param `u))) alphaBi alphaKind))
    (hn : lctx.find? nId = some (.cdecl nIndex nId nName
      (.const ``Nat []) nBi nKind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType
        (ctorIndexedVecApp (.fvar alphaId)
          (replaySuccApp (.fvar nId)))) =
      .ok (.sort (.succ (.param `u))) := by
  have hfirst :
      TypeChecker.Inner.inferType' (replayFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (vecFamilyTail, validationFirstAppState alphaId) := by
    simpa [validationFirstAppState] using
      (replayInferFirstAppFVarCore 9999 lctx
        ({} : TypeChecker.State) alphaId
        (by simp)
        (by simp [replayInsert])
        (by simp [replayFirstApp]) halpha)
  have hsucc :
      TypeChecker.Inner.inferType' (replaySuccApp (.fvar nId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        (validationFirstAppState alphaId) =
      .ok (.const ``Nat [], indexedVecValidationSuccState alphaId nId) := by
    simpa [indexedVecValidationSuccState] using
      (replayInferSuccFVarCore 9999 lctx
        (validationFirstAppState alphaId) nId
        (by simp [validationFirstAppState, replayInsert,
          replayFirstApp])
        (by
          simp only [validationFirstAppState, replayInsert,
            Std.HashMap.getElem?_insert]
          rw [constBeqFVar]
          rw [show (replayFirstApp (.fvar alphaId) ==
              (.fvar nId : Expr)) = false by
            simp [replayFirstApp]]
          rw [show ((.fvar alphaId : Expr) == .fvar nId) = false by
            change Expr.eqv (.fvar alphaId) (.fvar nId) = false
            rw [Expr.eqv_eq]
            simp [Expr.eqv', hne]]
          rw [constBeqFVar]
          simp)
        (by simp [validationFirstAppState, replayInsert,
          replaySuccApp])
        hn)
  have hresult :
      TypeChecker.Inner.inferType'
        (ctorIndexedVecApp (.fvar alphaId)
          (replaySuccApp (.fvar nId))) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.param `u)),
        indexedVecValidationSuccFinalState alphaId nId) := by
    simpa [indexedVecValidationSuccFinalState] using
      (replayInferIndexedVecAppCore 9999 lctx
        ({} : TypeChecker.State) (validationFirstAppState alphaId)
        (indexedVecValidationSuccState alphaId nId) (.fvar alphaId)
        (replaySuccApp (.fvar nId))
        (by simp [ctorIndexedVecApp, replaySuccApp,
          Expr.hasLooseBVars, Expr.looseBVarRange'])
        (by simp [ctorIndexedVecApp, replaySuccApp])
        hfirst hsucc (by rfl))
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId)
        (replaySuccApp (.fvar nId))) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [hresult]
  rfl

private theorem indexedVecValidationHeadContextFresh :
    indexedVecValidationHeadContext.lctx.find?
      indexedVecValidationHeadContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecValidationHeadContext.freshFVarId)
    indexedVecValidationHeadContextWF
  rw [h]
  simp only [indexedVecValidationHeadContext,
    indexedVecValidationNContext, indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp +decide

private theorem indexedVecValidationAlphaFindInTail :
    indexedVecValidationTailContext.lctx.find?
        indexedVecValidationAlphaId =
      some (.cdecl 0 indexedVecValidationAlphaId
        indexedVecValidationParamName
        (.sort (.succ (.param `u))) .default .default) := by
  have hfresh := indexedVecValidationHeadContextFresh
  have hne : indexedVecValidationAlphaId ≠
      indexedVecValidationTailId := by
    change indexedVecValidationAlphaId ≠
      indexedVecValidationHeadContext.freshFVarId
    intro heq
    rw [← heq] at hfresh
    rw [indexedVecValidationAlphaFindInHead] at hfresh
    contradiction
  have h := localContextFindOld
    (lctx := indexedVecValidationHeadContext.lctx)
    (oldId := indexedVecValidationAlphaId)
    (newId := indexedVecValidationTailId)
    (newName := consTailName)
    (newType := ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 0 indexedVecValidationAlphaId
      indexedVecValidationParamName (.sort (.succ (.param `u)))
      .default .default)
    indexedVecValidationHeadContextWF
    hfresh hne
    indexedVecValidationAlphaFindInHead
  simpa [indexedVecValidationTailContext,
    indexedVecValidationTailId,
    AddInductive.Context.pushLocalDecl] using h

private theorem indexedVecValidationNFindInTail :
    indexedVecValidationTailContext.lctx.find?
        indexedVecValidationNId =
      some (.cdecl 2 indexedVecValidationNId consNName
        (.const ``Nat []) .implicit .default) := by
  have hfresh := indexedVecValidationHeadContextFresh
  have hne : indexedVecValidationNId ≠
      indexedVecValidationTailId := by
    change indexedVecValidationNId ≠
      indexedVecValidationHeadContext.freshFVarId
    intro heq
    rw [← heq] at hfresh
    rw [indexedVecValidationNFindInHead] at hfresh
    contradiction
  have h := localContextFindOld
    (lctx := indexedVecValidationHeadContext.lctx)
    (oldId := indexedVecValidationNId)
    (newId := indexedVecValidationTailId)
    (newName := consTailName)
    (newType := ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 2 indexedVecValidationNId consNName
      (.const ``Nat []) .implicit .default)
    indexedVecValidationHeadContextWF
    hfresh hne
    indexedVecValidationNFindInHead
  simpa [indexedVecValidationTailContext,
    indexedVecValidationTailId,
    AddInductive.Context.pushLocalDecl] using h

private theorem indexedVecValidationSortCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext,
        .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  exact indexedVecValidationSortCheckTypeM
    indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationNatCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext, .const ``Nat [],
        .sort (.succ .zero)⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.const ``Nat [])) = _
  exact ctorNatCheckTypeM indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationAlphaCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationNContext, indexedVecValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationNContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.fvar indexedVecValidationAlphaId)) = _
  exact ctorFVarCheckTypeM indexedVecValidationNContext.lctx
    indexedVecValidationAlphaId (.sort (.succ (.param `u)))
    indexedVecValidationAlphaFindInN

private theorem indexedVecValidationTailCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationHeadContext,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationHeadContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (.fvar indexedVecValidationNId))) = _
  exact ctorIndexedVecFVarCheckTypeM
    indexedVecValidationHeadContext.lctx
    indexedVecValidationAlphaId indexedVecValidationNId
    indexedVecValidationAlphaNeN indexedVecValidationAlphaFindInHead
    indexedVecValidationNFindInHead

private theorem indexedVecValidationNilResultCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext, indexedVecValidationNilResult,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (.const ``Nat.zero []))) = _
  exact indexedVecValidationZeroCheckTypeM
    indexedVecCtorValidationContext.lctx indexedVecValidationAlphaId
    indexedVecValidationAlphaFind

private theorem indexedVecValidationConsResultCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationTailContext, indexedVecValidationConsResult,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationTailContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (replaySuccApp (.fvar indexedVecValidationNId)))) = _
  exact indexedVecValidationSuccCheckTypeM
    indexedVecValidationTailContext.lctx
    indexedVecValidationAlphaId indexedVecValidationNId
    indexedVecValidationAlphaNeN
    indexedVecValidationAlphaFindInTail
    indexedVecValidationNFindInTail

private def indexedVecCheckedOfValid
    (context : AddInductive.Context) (source inferred : Expr)
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (valid : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    AddInductive.ConstructorCheckedExpr context source :=
  .ofRun fvars valid

private def indexedVecValidationSortChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      (.sort (.succ (.param `u))) :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [FVarsIn, Level.hasMVar'])
    indexedVecValidationSortCheckValid

private def indexedVecValidationNatChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      (.const ``Nat []) :=
  indexedVecCheckedOfValid _ _ _ (by simp [FVarsIn])
    indexedVecValidationNatCheckValid

private def indexedVecValidationAlphaChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationNContext
      indexedVecValidationAlpha :=
  indexedVecCheckedOfValid _ _ _ (by
    change (indexedVecValidationNContext.lctx.find?
      indexedVecValidationAlphaId).isSome = true
    rw [indexedVecValidationAlphaFindInN]
    rfl)
    indexedVecValidationAlphaCheckValid

private def indexedVecValidationTailChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [ctorIndexedVecApp, indexedVecValidationAlpha,
      indexedVecValidationNExpr, AddInductive.Context.freshExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationAlphaId).isSome = true
      rw [indexedVecValidationAlphaFindInHead]
      rfl
    · change (indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [indexedVecValidationNFindInHead]
      rfl)
    indexedVecValidationTailCheckValid

private def indexedVecValidationNilResultChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      indexedVecValidationNilResult :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [indexedVecValidationNilResult, ctorIndexedVecApp,
      indexedVecValidationAlpha,
      AddInductive.Context.freshExpr, FVarsIn, Level.hasMVar']
    change (indexedVecCtorValidationContext.lctx.find?
      indexedVecValidationAlphaId).isSome = true
    rw [indexedVecValidationAlphaFind]
    rfl)
    indexedVecValidationNilResultCheckValid

private def indexedVecValidationConsResultChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationTailContext
      indexedVecValidationConsResult :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [indexedVecValidationConsResult, ctorIndexedVecApp,
      replaySuccApp, indexedVecValidationAlpha,
      indexedVecValidationNExpr, AddInductive.Context.freshExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (indexedVecValidationTailContext.lctx.find?
        indexedVecValidationAlphaId).isSome = true
      rw [indexedVecValidationAlphaFindInTail]
      rfl
    · change (indexedVecValidationTailContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [indexedVecValidationNFindInTail]
      rfl)
    indexedVecValidationConsResultCheckValid

private theorem indexedVecStagedStats_eq :
    indexedVecStagedUniverseInput.staged.family.validation.stats =
      indexedVecCandidateInductiveStats := rfl

private theorem indexedVecValidationPostContext_eq :
    { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := ctorContext.env } = indexedVecCtorValidationContext := rfl

private def indexedVecTransportValidationTrace
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

private def indexedVecTransportViewAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (indexedVecTransportValidationTrace context_eq source_eq trace)
      view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  exact alignment

@[simp] private theorem indexedVecTransportValidationTrace_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (indexedVecTransportValidationTrace context_eq source_eq trace).spineLength =
      trace.spineLength := by
  subst context'
  subst source'
  rfl

private theorem indexedVecValidationNatWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecCtorValidationContext, .const ``Nat [],
        .const ``Nat []⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf (.const ``Nat [])) = .ok (.const ``Nat [])
  exact ctorNatWhnfM indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationAlphaWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecValidationNContext, indexedVecValidationAlpha,
        indexedVecValidationAlpha⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationNContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf (.fvar indexedVecValidationAlphaId)) =
      .ok (.fvar indexedVecValidationAlphaId)
  exact ctorFVarWhnfM indexedVecValidationNContext.lctx
    indexedVecValidationAlphaId indexedVecValidationAlphaFindInN

private theorem indexedVecValidationTailWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecValidationHeadContext,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationHeadContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)) =
      .ok (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
  exact ctorIndexedVecWhnfM indexedVecValidationHeadContext.lctx
    indexedVecValidationAlpha indexedVecValidationNExpr

private theorem indexedVecCandidateWhnfResult_eq
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (other : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, result⟩) :
    result = source := by
  unfold AddInductive.CandidateWhnfStep.Valid at self other
  rw [self] at other
  exact (Except.ok.inj other).symm

private noncomputable def indexedVecValidationNatPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 1 indexedVecCtorValidationContext
      (.const ``Nat [])) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          subst result
          exact .absent indexedVecValidationNatChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq,
            indexedVecValidationNatHasNoIndOcc] at occurs
          contradiction

private noncomputable def indexedVecValidationAlphaPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 2 indexedVecValidationNContext
      indexedVecValidationAlpha) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          subst result
          exact .absent indexedVecValidationAlphaChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [indexedVecValidationAlphaShape, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq] at occurs
          change AddInductive.hasIndOcc
            indexedVecCandidateInductiveStats.indConsts
              indexedVecValidationAlpha = true at occurs
          rw [indexedVecValidationAlphaHasNoIndOcc] at occurs
          contradiction

private noncomputable def indexedVecValidationTailPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 3 indexedVecValidationHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq] at occurs
          change AddInductive.hasIndOcc
            indexedVecCandidateInductiveStats.indConsts
              (ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr) = false at occurs
          rw [indexedVecValidationTailHasIndOcc] at occurs
          contradiction
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [ctorIndexedVecApp, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          subst result
          exact .target indexedVecValidationTailChecked

private def indexedVecValidationNatAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecCtorValidationContext (.const ``Nat [])
        (.const ``Nat []) :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecCtorValidationContext
    (.const ``Nat [])⟩

private def indexedVecValidationAlphaAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecValidationNContext indexedVecValidationAlpha
        indexedVecValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecValidationNContext
    indexedVecValidationAlpha⟩

private def indexedVecValidationTailAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecValidationHeadContext
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr) :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecValidationHeadContext
    (ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)⟩

/-- The validator and analyzer intentionally allocate the retained `n` field
under different fresh-FVar histories.  D2 alignment must therefore be
positional rather than identifier-based. -/
theorem indexedVecValidationCandidateFieldFVars_ne :
    indexedVecValidationNId ≠ consNId := by
  simp [indexedVecValidationNId, indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext, indexedVecFamilyCandidateContext,
    consNId, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId,
    NameGenerator.next, NameGenerator.curr]

/-- Exact D2 owner for `IndexedVec`.  Its validator telescope is transported
only across proved context/source equalities, while every candidate view is
instantiated with the validator-owned locals at the same de Bruijn position. -/
noncomputable def indexedVecStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  universeInput := indexedVecStagedUniverseInput
  alignment := by
    change AddInductive.ConstructorCandidateAlignmentTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false 0
      indexedVecCtorValidationContext
      indexedVecStagedUniverseInput.staged.constructorValidation.trace
      (.cons indexedVecNilConstructorCandidate
        (.cons indexedVecConsConstructorCandidate .nil))
    generalize htrace :
      indexedVecStagedUniverseInput.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors fresh closed rootCheck typeTrace tailTrace =>
        clear htrace
        cases hnilRoot : typeTrace with
        | parameter context fuel argIdx name domain body binderInfo param
            parameterType parameterAt parameterTypeRun parameterDefEq
            nilTypeTail =>
            rw [indexedVecStagedStats_eq,
              indexedVecValidationStatsParams] at parameterAt
            simp at parameterAt
            subst param
            change AddInductive.getType indexedVecValidationAlpha
              indexedVecCtorValidationContext = .ok parameterType at parameterTypeRun
            rw [indexedVecValidationGetTypeAlpha] at parameterTypeRun
            injection parameterTypeRun with parameterType_eq
            subst parameterType
            let nilNormalized := indexedVecTransportValidationTrace
              indexedVecValidationPostContext_eq
              indexedVecValidationNilResultShape nilTypeTail
            let nilNormalizedTrace := nilNormalized
            have nilSpine : nilTypeTail.spineLength =
                nilNormalizedTrace.spineLength := by
              exact (indexedVecTransportValidationTrace_spineLength
                indexedVecValidationPostContext_eq
                indexedVecValidationNilResultShape nilTypeTail).symm
            cases hnilNormalized : nilNormalizedTrace with
            | terminal context source fuel argIdx nilTerminal nilValid =>
                simp [hnilNormalized,
                  AddInductive.ConstructorTypeValidationTrace.spineLength] at nilSpine
                have nilNormalizedAlignment :
                    AddInductive.ConstructorViewAlignmentTrace
                      nilNormalizedTrace indexedVecValidationNilResult := by
                  rw [hnilNormalized]
                  exact .terminal indexedVecValidationNilResultChecked
                    indexedVecValidationNilResultChecked nilTerminal nilValid
                have nilTailAlignment := indexedVecTransportViewAlignment
                  indexedVecValidationPostContext_eq
                  indexedVecValidationNilResultShape
                  indexedVecValidationNilResultShape nilTypeTail
                  nilNormalizedAlignment
                have nilHeadAlignment :
                    AddInductive.ConstructorViewAlignmentTrace
                      (.parameter
                        { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                          env := ctorContext.env }
                        999 0 `α (.sort (.succ (.param `u)))
                        nilCtorBodyRaw .implicit indexedVecValidationAlpha
                        (.sort (.succ (.param `u))) parameterAt
                        parameterTypeRun parameterDefEq nilTypeTail)
                      indexedVecNilConstructorCandidate.type.view := by
                  change AddInductive.ConstructorViewAlignmentTrace
                    _ nilCandidate.view
                  rw [nilCandidate_view_eq]
                  exact .parameter indexedVecValidationSortChecked
                    indexedVecValidationSortChecked
                    indexedVecValidationSortChecked rfl
                    (by simp [indexedVecValidationAlphaFind])
                    nilTypeTail nilTailAlignment
                cases tailTrace with
                | cons seen head constructors consFresh consClosed
                    consRootCheck consTypeTrace finalTrace =>
                    cases hconsRoot : consTypeTrace with
                    | parameter context fuel argIdx name domain body binderInfo
                        param parameterType parameterAt parameterTypeRun
                        parameterDefEq consAfterParamTrace =>
                        rw [indexedVecStagedStats_eq,
                          indexedVecValidationStatsParams] at parameterAt
                        simp at parameterAt
                        subst param
                        change AddInductive.getType indexedVecValidationAlpha
                          indexedVecCtorValidationContext = .ok parameterType at parameterTypeRun
                        rw [indexedVecValidationGetTypeAlpha] at parameterTypeRun
                        injection parameterTypeRun with parameterType_eq
                        subst parameterType
                        let buildConsHeadAlignment
                            (tailAlignment :
                              AddInductive.ConstructorViewAlignmentTrace
                                consAfterParamTrace
                                (consNTypeRaw.instantiate1
                                  indexedVecValidationAlpha)) :
                            AddInductive.ConstructorViewAlignmentTrace
                              (.parameter
                                { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                                  env := ctorContext.env }
                                999 0 consAlphaName
                                (.sort (.succ (.param `u))) consNTypeRaw
                                .implicit indexedVecValidationAlpha
                                (.sort (.succ (.param `u))) parameterAt
                                parameterTypeRun parameterDefEq
                                consAfterParamTrace)
                              indexedVecConsConstructorCandidate.type.view := by
                          change AddInductive.ConstructorViewAlignmentTrace
                            _ consCandidate.view
                          rw [consCandidate_view_eq]
                          exact .parameter indexedVecValidationSortChecked
                            indexedVecValidationSortChecked
                            indexedVecValidationSortChecked rfl
                            (by simp [indexedVecValidationAlphaFind])
                            consAfterParamTrace tailAlignment
                        have consAfterParamSource_eq :
                            indexedVecConsInfo.type.bindingBody!.instantiate1
                                indexedVecValidationAlpha =
                              indexedVecValidationConsAfterParam :=
                          indexedVecValidationConsAfterParamShape
                        have consAfterParamExplicit_eq :
                            indexedVecConsInfo.type.bindingBody!.instantiate1
                                indexedVecValidationAlpha =
                              .forallE consNName (.const ``Nat [])
                                (.forallE consHeadName
                                  indexedVecValidationAlpha
                                  (.forallE consTailName
                                    (ctorIndexedVecApp
                                      indexedVecValidationAlpha (.bvar 1))
                                    (ctorIndexedVecApp
                                      indexedVecValidationAlpha
                                      (replaySuccApp (.bvar 2))) .default)
                                  .default)
                                .implicit :=
                          consAfterParamSource_eq.trans
                            indexedVecValidationConsAfterParamExplicitShape
                        let consAfterParamNormalized :=
                          indexedVecTransportValidationTrace
                            indexedVecValidationPostContext_eq
                            consAfterParamExplicit_eq consAfterParamTrace
                        let consAfterParamNormalizedTrace :=
                          consAfterParamNormalized
                        have consAfterParamSpine :
                            consAfterParamTrace.spineLength =
                              consAfterParamNormalizedTrace.spineLength := by
                          exact (indexedVecTransportValidationTrace_spineLength
                            indexedVecValidationPostContext_eq
                            consAfterParamExplicit_eq
                            consAfterParamTrace).symm
                        cases hconsAfterParamNormalized :
                            consAfterParamNormalizedTrace with
                        | parameter context fuel argIdx name domain body
                            binderInfo param parameterType parameterAt
                            parameterTypeRun parameterDefEq tail =>
                            rw [indexedVecStagedStats_eq,
                              indexedVecValidationStatsParams] at parameterAt
                            simp at parameterAt
                        | ordinary context fuel argIdx name domain body
                            binderInfo sortResult noParameter ensureType
                            universeTrace natPositivity consAfterNTrace =>
                            simp [hconsAfterParamNormalized,
                              AddInductive.ConstructorTypeValidationTrace.spineLength]
                              at consAfterParamSpine
                            have natPositivityAlignment :=
                              indexedVecValidationNatPositivityAlignment
                                natPositivity
                            have afterParamBody_eq :
                                indexedVecValidationConsAfterParam.bindingBody! =
                                  .forallE consHeadName
                                    indexedVecValidationAlpha
                                    (.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default := by
                              exact congrArg Expr.bindingBody!
                                indexedVecValidationConsAfterParamExplicitShape
                            have afterNSource_eq :
                                ((Expr.forallE consHeadName
                                    indexedVecValidationAlpha
                                    (Expr.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default).instantiate1
                                  indexedVecCtorValidationContext.freshExpr) =
                                    indexedVecValidationConsAfterN := by
                              change
                                ((Expr.forallE consHeadName
                                    indexedVecValidationAlpha
                                    (Expr.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default).instantiate1
                                  indexedVecValidationNExpr) =
                                    indexedVecValidationConsAfterN
                              rw [← afterParamBody_eq]
                              exact indexedVecValidationConsAfterNShape
                            have nContext_eq :
                                indexedVecCtorValidationContext.pushLocalDecl
                                    consNName .implicit
                                      (AddInductive.consumeTypeAnnotations
                                        (.const ``Nat [])) =
                                  indexedVecValidationNContext := by
                              simp [indexedVecValidationNContext]
                            let consAfterNNormalized :=
                              indexedVecTransportValidationTrace nContext_eq
                                afterNSource_eq consAfterNTrace
                            let consAfterNNormalizedTrace := consAfterNNormalized
                            have consAfterNSpine :
                                consAfterNTrace.spineLength =
                                  consAfterNNormalizedTrace.spineLength := by
                              exact
                                (indexedVecTransportValidationTrace_spineLength
                                  nContext_eq afterNSource_eq
                                  consAfterNTrace).symm
                            cases hconsAfterNNormalized :
                                consAfterNNormalizedTrace with
                            | parameter context fuel argIdx name domain body
                                binderInfo param parameterType parameterAt
                                parameterTypeRun parameterDefEq tail =>
                                rw [indexedVecStagedStats_eq,
                                  indexedVecValidationStatsParams] at parameterAt
                                simp at parameterAt
                            | ordinary context fuel argIdx name domain body
                                binderInfo sortResult noParameter ensureType
                                universeTrace alphaPositivity
                                consAfterHeadTrace =>
                                simp [hconsAfterNNormalized,
                                  AddInductive.ConstructorTypeValidationTrace.spineLength]
                                  at consAfterNSpine
                                have alphaPositivityAlignment :=
                                  indexedVecValidationAlphaPositivityAlignment
                                    alphaPositivity
                                have headContext_eq :
                                    indexedVecValidationNContext.pushLocalDecl
                                        consHeadName .default
                                          (AddInductive.consumeTypeAnnotations
                                            indexedVecValidationAlpha) =
                                      indexedVecValidationHeadContext := by
                                  rw [indexedVecValidationConsumeAlpha]
                                  rfl
                                let consAfterHeadNormalized :=
                                  indexedVecTransportValidationTrace
                                    headContext_eq
                                    indexedVecValidationConsAfterHeadShape
                                    consAfterHeadTrace
                                let consAfterHeadNormalizedTrace :=
                                  consAfterHeadNormalized
                                have consAfterHeadSpine :
                                    consAfterHeadTrace.spineLength =
                                      consAfterHeadNormalizedTrace.spineLength := by
                                  exact
                                    (indexedVecTransportValidationTrace_spineLength
                                      headContext_eq
                                      indexedVecValidationConsAfterHeadShape
                                      consAfterHeadTrace).symm
                                cases hconsAfterHeadNormalized :
                                    consAfterHeadNormalizedTrace with
                                | parameter context fuel argIdx name domain body
                                    binderInfo param parameterType parameterAt
                                    parameterTypeRun parameterDefEq tail =>
                                    rw [indexedVecStagedStats_eq,
                                      indexedVecValidationStatsParams] at parameterAt
                                    simp at parameterAt
                                | ordinary context fuel argIdx name domain body
                                    binderInfo sortResult noParameter ensureType
                                    universeTrace tailPositivity
                                    consResultTrace =>
                                    simp [hconsAfterHeadNormalized,
                                      AddInductive.ConstructorTypeValidationTrace.spineLength]
                                      at consAfterHeadSpine
                                    have tailPositivityAlignment :=
                                      indexedVecValidationTailPositivityAlignment
                                        tailPositivity
                                    have tailContext_eq :
                                        indexedVecValidationHeadContext.pushLocalDecl
                                            consTailName .default
                                              (AddInductive.consumeTypeAnnotations
                                                (ctorIndexedVecApp
                                                  indexedVecValidationAlpha
                                                  indexedVecValidationNExpr)) =
                                          indexedVecValidationTailContext := by
                                      rw [indexedVecValidationConsumeTail]
                                      rfl
                                    let consResultNormalized :=
                                      indexedVecTransportValidationTrace
                                        tailContext_eq
                                        indexedVecValidationConsResultShape
                                        consResultTrace
                                    let consResultNormalizedTrace :=
                                      consResultNormalized
                                    have consResultSpine :
                                        consResultTrace.spineLength =
                                          consResultNormalizedTrace.spineLength := by
                                      exact
                                        (indexedVecTransportValidationTrace_spineLength
                                          tailContext_eq
                                          indexedVecValidationConsResultShape
                                          consResultTrace).symm
                                    cases hconsResultNormalized :
                                        consResultNormalizedTrace with
                                    | terminal context source fuel argIdx
                                        resultTerminal resultValid =>
                                        simp [hconsResultNormalized,
                                          AddInductive.ConstructorTypeValidationTrace.spineLength]
                                          at consResultSpine
                                        have consResultNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consResultNormalizedTrace
                                              indexedVecValidationConsResult := by
                                          rw [hconsResultNormalized]
                                          exact .terminal
                                            indexedVecValidationConsResultChecked
                                            indexedVecValidationConsResultChecked
                                            resultTerminal resultValid
                                        have consResultAlignment :=
                                          indexedVecTransportViewAlignment
                                            tailContext_eq
                                            indexedVecValidationConsResultShape
                                            indexedVecValidationConsResultShape
                                            consResultTrace
                                            consResultNormalizedAlignment
                                        have consAfterHeadNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterHeadNormalizedTrace
                                              indexedVecValidationConsAfterHead := by
                                          rw [hconsAfterHeadNormalized]
                                          exact .ordinary
                                            indexedVecValidationTailChecked
                                            indexedVecValidationTailChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeTail]
                                              using indexedVecValidationTailChecked)
                                            tailPositivity
                                            tailPositivityAlignment
                                            indexedVecValidationHeadContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeTail]
                                              using
                                                indexedVecValidationTailAnnotations)
                                            consResultTrace consResultAlignment
                                        have consAfterHeadAlignment :=
                                          indexedVecTransportViewAlignment
                                            headContext_eq
                                            indexedVecValidationConsAfterHeadShape
                                            indexedVecValidationConsAfterHeadShape
                                            consAfterHeadTrace
                                            consAfterHeadNormalizedAlignment
                                        have consAfterNNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterNNormalizedTrace
                                              indexedVecValidationConsAfterN := by
                                          rw [hconsAfterNNormalized]
                                          exact .ordinary
                                            indexedVecValidationAlphaChecked
                                            indexedVecValidationAlphaChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeAlpha]
                                              using indexedVecValidationAlphaChecked)
                                            alphaPositivity
                                            alphaPositivityAlignment
                                            indexedVecValidationNContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeAlpha]
                                              using
                                                indexedVecValidationAlphaAnnotations)
                                            consAfterHeadTrace
                                            consAfterHeadAlignment
                                        have consAfterNAlignment :=
                                          indexedVecTransportViewAlignment
                                            nContext_eq afterNSource_eq
                                            afterNSource_eq consAfterNTrace
                                            consAfterNNormalizedAlignment
                                        have consAfterParamNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterParamNormalizedTrace
                                              (.forallE consNName
                                                (.const ``Nat [])
                                                (.forallE consHeadName
                                                  indexedVecValidationAlpha
                                                  (.forallE consTailName
                                                    (ctorIndexedVecApp
                                                      indexedVecValidationAlpha
                                                      (.bvar 1))
                                                    (ctorIndexedVecApp
                                                      indexedVecValidationAlpha
                                                      (replaySuccApp (.bvar 2)))
                                                    .default)
                                                  .default)
                                                .implicit) := by
                                          rw [hconsAfterParamNormalized]
                                          exact .ordinary
                                            indexedVecValidationNatChecked
                                            indexedVecValidationNatChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeNat]
                                              using indexedVecValidationNatChecked)
                                            natPositivity natPositivityAlignment
                                            indexedVecCtorValidationContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeNat]
                                              using
                                                indexedVecValidationNatAnnotations)
                                            consAfterNTrace consAfterNAlignment
                                        have consAfterParamAlignment :=
                                          indexedVecTransportViewAlignment
                                            indexedVecValidationPostContext_eq
                                            consAfterParamExplicit_eq
                                            consAfterParamExplicit_eq
                                            consAfterParamTrace
                                            consAfterParamNormalizedAlignment
                                        have consHeadAlignment :=
                                          buildConsHeadAlignment
                                            consAfterParamAlignment
                                        change
                                          AddInductive.CandidateCheckTypeObservation
                                            indexedVecCtorValidationContext.withEmptyLocalContext
                                            indexedVecKernelNil.type at rootCheck
                                        change
                                          AddInductive.CandidateCheckTypeObservation
                                            indexedVecCtorValidationContext.withEmptyLocalContext
                                            indexedVecKernelCons.type at consRootCheck
                                        let nilRootScope :
                                            AddInductive.ConstructorCheckedExpr
                                              indexedVecCtorValidationContext.withEmptyLocalContext
                                              indexedVecKernelNil.type :=
                                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                                            closed rootCheck
                                        let consRootScope :
                                            AddInductive.ConstructorCheckedExpr
                                              indexedVecCtorValidationContext.withEmptyLocalContext
                                              indexedVecKernelCons.type :=
                                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                                            consClosed consRootCheck
                                        cases finalTrace with
                                        | nil finalSeen =>
                                            exact
                                              AddInductive.ConstructorCandidateAlignmentTrace.cons
                                                nilRootScope
                                                (by
                                                  change nilCandidate.trace.storedSpine = true
                                                  exact nilCandidate_identity.storedSpine)
                                                (by
                                                  change 1 =
                                                    nilTypeTail.spineLength + 1
                                                  omega)
                                                (by rfl) nilHeadAlignment <|
                                              AddInductive.ConstructorCandidateAlignmentTrace.cons
                                                consRootScope
                                                (by
                                                  change consCandidate.trace.storedSpine = true
                                                  exact consCandidate_identity.storedSpine)
                                                (by
                                                  change 4 =
                                                    consAfterParamTrace.spineLength + 1
                                                  omega)
                                                (by rfl) consHeadAlignment <|
                                              AddInductive.ConstructorCandidateAlignmentTrace.nil
                                                ((∅ : NameSet).insert
                                                  indexedVecKernelNil.name |>.insert
                                                    indexedVecKernelCons.name)
                                | terminal context source fuel argIdx terminal
                                    valid =>
                                    simp [indexedVecValidationConsAfterHead,
                                      Expr.isForall] at terminal
                            | terminal context source fuel argIdx terminal valid =>
                                simp [indexedVecValidationConsAfterN,
                                  Expr.isForall] at terminal
                        | terminal context source fuel argIdx terminal valid =>
                            simp [Expr.isForall] at terminal
                    | ordinary context fuel argIdx name domain body binderInfo
                        sortResult noParameter ensureType universeTrace positivity
                        tail =>
                        rw [indexedVecStagedStats_eq,
                          indexedVecValidationStatsParams] at noParameter
                        simp at noParameter
                    | terminal context source fuel argIdx terminal valid =>
                        have consType_eq : indexedVecKernelCons.type =
                            consCtorTypeRaw := by
                          simpa [indexedVecKernelCons] using consInfoTypeShape
                        rw [consType_eq] at terminal
                        simp [consCtorTypeRaw, Expr.isForall] at terminal
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity nilTypeTail =>
            rw [indexedVecStagedStats_eq,
              indexedVecValidationStatsParams] at noParameter
            simp at noParameter
        | terminal context source fuel argIdx terminal valid =>
            simp [indexedVecKernelNil, indexedVecNilInfo,
              ConstantInfo.type, ConstantInfo.toConstantVal,
              Expr.isForall] at terminal

/-- The retained `nil`/`cons` validator telescopes, exact analyzer views, field
checks, positivity target, and terminal family applications all admit the D2
post-family Theory interpretation despite their distinct fresh identifiers. -/
theorem indexedVecProducedPostFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePostFamilySemanticRun
      indexedVecStagedPostFamilyInput) :=
  indexedVecStagedPostFamilyInput.exists

private def indexedVecReorderedViewType : VInductiveType :=
  { indexedVecType with
    ctors := [indexedVecType.ctors[1], indexedVecType.ctors[0]] }

private def indexedVecReorderedViewDecl : VInductDecl :=
  { indexedVecDecl with types := [indexedVecReorderedViewType] }

/-- Swapping the two otherwise unchanged constructor payloads fails the
computational normalization-shape gate before semantic or generation evidence
can be attached. -/
theorem indexedVecReorderedView_rejected :
    VInductDecl.normalization? indexedVecDecl
      indexedVecReorderedViewDecl = none := rfl

theorem indexedVecSemanticFamilyViewTr :
    TrExpr natFinalEnv [`u] [] indexedVecFamilyCandidate.view
      indexedVecType.type := by
  rw [indexedVecFamilyCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecType_wf
  exact ⟨_, indexedVecSemanticFamilySourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticNilViewTr :
    TrExpr indexedVecTypeEnv [`u] [] nilCandidate.view
      indexedVecType.ctors[0].type := by
  rw [nilCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecNil_wf
  exact ⟨_, indexedVecSemanticNilSourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticConsViewTr :
    TrExpr indexedVecTypeEnv [`u] [] consCandidate.view
      indexedVecType.ctors[1].type := by
  rw [consCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact ⟨_, indexedVecSemanticConsSourceTr, ⟨_, htype⟩⟩

def indexedVecSemanticFamilyRootRun :
    TypeChecker.CandidateExprRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type indexedVecType.type where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticFamilySourceTr
  view_tr := indexedVecSemanticFamilyViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticNilRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type where
  contextRun := by
    simpa [nilCandidate, nilCandidateContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticNilSourceTr
  view_tr := indexedVecSemanticNilViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticConsRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type where
  contextRun := by
    simpa [consCandidate, consRootContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticConsSourceTr
  view_tr := indexedVecSemanticConsViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type :=
  indexedVecSemanticFamilyRootRun.semanticOfIdentity
    indexedVecFamilyCandidate_identity

def indexedVecSemanticNilSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type :=
  indexedVecSemanticNilRootRun.semanticOfIdentity nilCandidate_identity

def indexedVecSemanticConsSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type :=
  indexedVecSemanticConsRootRun.semanticOfIdentity consCandidate_identity

def indexedVecSemanticNilConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticNilSemanticRootRun

def indexedVecSemanticConsConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticConsSemanticRootRun

def indexedVecSemanticNilConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] :=
  indexedVecSemanticNilConstructorSemanticRun.root

def indexedVecSemanticConsConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] :=
  indexedVecSemanticConsConstructorSemanticRun.root

def indexedVecSemanticConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors := by
  exact .cons indexedVecSemanticNilConstructorSemanticRun
    (.cons indexedVecSemanticConsConstructorSemanticRun .nil)

def indexedVecSemanticConstructorListRun :
    VInductDecl.CandidateConstructorListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors :=
  indexedVecSemanticConstructorSemanticListRun.roots

def indexedVecSemanticFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticFamilySemanticRootRun
  typeEnv := indexedVecTypeEnv
  addType := rfl
  constructors := indexedVecSemanticConstructorSemanticListRun

def indexedVecSemanticFamilyRun :
    VInductDecl.CandidateFamilyRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType :=
  indexedVecSemanticFamilySemanticRun.root

/-- Temporary L4L-01A compatibility witness. The two-stage owner proves a
semantic run exists without choosing this concrete identity value; L4L-01E
removes the explicit downstream witness. -/
def indexedVecSemanticNormalizationCandidateSemanticRun :
    VInductDecl.NormalizationCandidateSemanticRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  raw := indexedVecType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := indexedVecSemanticFamilySemanticRun

def indexedVecSemanticNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl :=
  indexedVecSemanticNormalizationCandidateSemanticRun.root

/-- Reconstructing every family and constructor payload leaves the identity
IndexedVec declaration unchanged. -/
theorem indexedVecSemantic_viewDecl_eq :
    indexedVecSemanticNormalizationCandidateRun.viewDecl =
      indexedVecDecl := rfl

/-- The candidate-derived normalization is exactly the analyzer's canonical
identity normalization, not merely propositionally interchangeable with it. -/
theorem indexedVecSemantic_normalization_eq :
    indexedVecSemanticNormalizationCandidateRun.normalization =
      indexedVecChecked.identityGeneration.block.normalization := rfl

def indexedVecSemanticFamilySpineRun :
    TypeChecker.CandidateExprSpineRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type
      indexedVecType.type :=
  indexedVecSemanticFamilySemanticRootRun.spine
    indexedVecFamilyCandidate_identity.storedSpine

def indexedVecSemanticNilSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type :=
  indexedVecSemanticNilSemanticRootRun.spine
    nilCandidate_identity.storedSpine

def indexedVecSemanticConsSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type :=
  indexedVecSemanticConsSemanticRootRun.spine
    consCandidate_identity.storedSpine

theorem indexedVecSemanticCandidate_generationShape :
    indexedVecSemanticNormalizationCandidateSemanticRun.generationShape =
      true := by
  change ((indexedVecFamilyCandidate.trace.storedSpine && true) &&
    ((nilCandidate.trace.storedSpine && true) &&
      ((consCandidate.trace.storedSpine && true) && true))) = true
  rw [indexedVecFamilyCandidate_identity.storedSpine,
    nilCandidate_identity.storedSpine,
    consCandidate_identity.storedSpine]
  rfl

/-- The consolidated constructor gate rejects truncation in either direction
before dependent semantic generation is assembled. -/
theorem indexedVecSemanticCandidate_missingRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      (.cons indexedVecNilConstructorCandidate .nil) [] = false :=
  rfl

theorem indexedVecSemanticCandidate_extraRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      .nil [indexedVecType.ctors[0]] = false :=
  rfl

/-- Temporary L4L-01A view-WF compatibility premise. L4L-01D derives this
from retained validation and L4L-01E removes it from package construction. -/
theorem indexedVecSemanticCandidate_viewDecl_wf :
    indexedVecSemanticNormalizationCandidateRun.viewDecl.WF natFinalEnv := by
  change indexedVecDecl.WF natFinalEnv
  exact indexedVecDecl_wf

def indexedVecSemanticProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext where
  candidate := indexedVecNormalizationCandidate
  produced := indexedVecNormalizationCandidateProduced
  shape := indexedVecSemanticCandidate_generationShape

/-- The strengthened outer gate retains the complete parameter/index and
ordered `nil`/`cons` generation layout in the same produced result. -/
theorem indexedVecSemanticGenerationShapeCandidate_produced :
    VInductDecl.produceGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecSemanticProducedGenerationShapeCandidate := by
  have produced :
      AddInductive.buildNormalizationCandidate indexedVecDecl.nparams
          [indexedVecKernelType] 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecNormalizationCandidate :=
    indexedVecNormalizationCandidateProduced
  simpa only [indexedVecSemanticProducedGenerationShapeCandidate] using
    VInductDecl.produceGenerationShapeCandidate_eq_ok
      (source := indexedVecDecl) (raw := indexedVecType)
      produced indexedVecSemanticCandidate_generationShape

def indexedVecSemanticGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      indexedVecSemanticNormalizationCandidateSemanticRun
      indexedVecChecked.identityGeneration :=
  VInductDecl.GenerationCandidateSemanticRun.ofGenerationShape
    indexedVecSemanticNormalizationCandidateSemanticRun
    indexedVecChecked.identityGeneration rfl
    indexedVecSemanticCandidate_viewDecl_wf
    indexedVecSemanticCandidate_generationShape

def indexedVecSemanticGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      indexedVecSemanticNormalizationCandidateRun
      indexedVecChecked.identityGeneration :=
  indexedVecSemanticGenerationCandidateSemanticRun.run

def indexedVecSemanticGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticGenerationCandidateSemanticRun.package

def indexedVecSemanticProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticProducedGenerationShapeCandidate.producedPackage
    indexedVecSemanticNormalizationCandidateSemanticRun rfl
    indexedVecChecked.identityGeneration rfl
    indexedVecSemanticCandidate_viewDecl_wf

def indexedVecSemanticGenerationCertificate :
    indexedVecDecl.GenerationCertificate natFinalEnv :=
  indexedVecSemanticProducedGenerationCandidatePackage.package.certificate

theorem indexedVecSemantic_addInductCertified :
    natFinalEnv.addInductCertified indexedVecSemanticGenerationCertificate =
      some indexedVecFinalEnv := by
  rfl

theorem indexedVecSemanticCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace natFinalEnv
      indexedVecFinalEnv indexedVecChecked.identityGeneration) :=
  VEnv.addInductCertified_trace indexedVecSemantic_addInductCertified

theorem indexedVecSemanticCertified_ordered :
    indexedVecFinalEnv.Ordered :=
  VEnv.addInductCertified_WF nat_env_wf.ordered
    indexedVecSemantic_addInductCertified

def indexedVecSemanticAddInductTraceChecked :
    AddInductTrace natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv := by
  refine indexedVecSemanticProducedGenerationCandidatePackage.package.addInductTrace
    indexedVecTypeMap indexedVecTypeEnv indexedVecCtorMap
    indexedVecCtorEnv indexedVecRecEnv ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := indexedVecInfo
      kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
      tr := indexedVecInfo_tr
      map_fresh := by
        rw [show
          indexedVecSemanticProducedGenerationCandidatePackage.package.generation.block.sourceType.name =
            ``IndexedVec by rfl]
        exact indexedVecType_fresh
      env_add := rfl
      map_add := rfl }
  · refine .cons (m₂ := indexedVecNilMap)
      (env₂ := indexedVecNilEnv) ?_ ?_
    · exact {
        info := indexedVecNilInfo
        kind_eq := by simp [indexedVecNilInfo, InductConstantKind.Matches]
        tr := indexedVecNilInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecNil_fresh
        env_add := rfl
        map_add := rfl }
    · refine .cons ?_ .nil
      exact {
        info := indexedVecConsInfo
        kind_eq := by simp [indexedVecConsInfo, InductConstantKind.Matches]
        tr := indexedVecConsInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecCons_fresh
        env_add := rfl
        map_add := rfl }
  · exact {
      info := indexedVecRecInfo
      kind_eq := by simp [indexedVecRecInfo, InductConstantKind.Matches]
      tr := indexedVecRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            indexedVecSemanticProducedGenerationCandidatePackage.package.generation).name =
              ``IndexedVec.rec by rfl]
        exact indexedVecRec_fresh
      env_add := rfl
      map_add := rfl }

theorem indexedVecSemantic_addInduct_checked :
    AddInduct natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv :=
  ⟨indexedVecSemanticAddInductTraceChecked⟩

theorem indexedVecSemantic_trEnv'_checked :
    TrEnv' .safe indexedVecMap false indexedVecFinalEnv :=
  .induct indexedVecSemantic_addInduct_checked nat_trEnv'

theorem indexedVecSemantic_env_wf_checked : indexedVecFinalEnv.WF :=
  indexedVecSemantic_trEnv'_checked.wf

theorem indexedVecSemantic_aligned_checked :
    Aligned .safe indexedVecMap indexedVecFinalEnv :=
  indexedVecSemantic_trEnv'_checked.aligned

/-
The semantic assembly, executable producer, and final E1 replay intentionally
inherit the existing transitional verifier closure. These guards make
additions to that closure visible at the public roots of this module.
-/
/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecProducedSemanticHierarchy_exists

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecProducedPostFamilySemantic_exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecProducedPostFamilySemantic_exists

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_constructorHeaders' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecProducedSemanticHierarchy_constructorHeaders

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecReorderedView_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms indexedVecReorderedView_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticCandidate_missingRawShape_rejected' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticCandidate_missingRawShape_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticCandidate_extraRawShape_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedVecSemanticCandidate_extraRawShape_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticGenerationShapeCandidate_produced' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticGenerationShapeCandidate_produced

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticGenerationCandidateSemanticRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticGenerationCandidateSemanticRun

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticProducedGenerationCandidatePackage' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticProducedGenerationCandidatePackage

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemantic_trEnv'_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemantic_trEnv'_checked

end Lean4Lean.InductiveReplayFixtures
