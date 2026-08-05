import Lean4Lean.Verify.Environment.Normalization

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-!
# Semantic interpretation of constructor validation

This module interprets the operational trace retained by
`Inductive.ValidationTrace`.  It deliberately sits above both the verified
checker and candidate normalization: validation supplies the accepted kernel
path, while normalization supplies the exact analyzer-owned Theory view.
-/

/-- Structural equality of kernel levels is sound after strict translation. -/
theorem levelStructEq_ofLevel
    (equal : levelStructEq lhs rhs = true)
    (lhs_tr : VLevel.ofLevel Us lhs = some lhs')
    (rhs_tr : VLevel.ofLevel Us rhs = some rhs') :
    lhs' = rhs' := by
  induction lhs generalizing rhs lhs' rhs' with
  | zero =>
      cases rhs <;> simp_all [levelStructEq, VLevel.ofLevel]
  | succ lhs ih =>
      cases rhs with
      | succ rhs =>
          simp only [levelStructEq] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs'', lhs_inner_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨rhs'', rhs_inner_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          change some lhs''.succ = some lhs' at lhs'_eq
          change some rhs''.succ = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih equal lhs_inner_tr rhs_inner_tr]
      | zero | max _ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | max lhs₁ lhs₂ ih₁ ih₂ =>
      cases rhs with
      | max rhs₁ rhs₂ =>
          simp only [levelStructEq, Bool.and_eq_true] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs₁', lhs₁_tr, lhsTail⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨lhs₂', lhs₂_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhsTail
          obtain ⟨rhs₁', rhs₁_tr, rhsTail⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          obtain ⟨rhs₂', rhs₂_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhsTail
          change some (.max lhs₁' lhs₂') = some lhs' at lhs'_eq
          change some (.max rhs₁' rhs₂') = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih₁ equal.1 lhs₁_tr rhs₁_tr,
            ih₂ equal.2 lhs₂_tr rhs₂_tr]
      | zero | succ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | imax lhs₁ lhs₂ ih₁ ih₂ =>
      cases rhs with
      | imax rhs₁ rhs₂ =>
          simp only [levelStructEq, Bool.and_eq_true] at equal
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at lhs_tr rhs_tr
          obtain ⟨lhs₁', lhs₁_tr, lhsTail⟩ :=
            Option.bind_eq_some_iff.mp lhs_tr
          obtain ⟨lhs₂', lhs₂_tr, lhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp lhsTail
          obtain ⟨rhs₁', rhs₁_tr, rhsTail⟩ :=
            Option.bind_eq_some_iff.mp rhs_tr
          obtain ⟨rhs₂', rhs₂_tr, rhs'_eq⟩ :=
            Option.bind_eq_some_iff.mp rhsTail
          change some (.imax lhs₁' lhs₂') = some lhs' at lhs'_eq
          change some (.imax rhs₁' rhs₂') = some rhs' at rhs'_eq
          injection lhs'_eq with lhs'_eq
          injection rhs'_eq with rhs'_eq
          subst lhs'
          subst rhs'
          rw [ih₁ equal.1 lhs₁_tr rhs₁_tr,
            ih₂ equal.2 lhs₂_tr rhs₂_tr]
      | zero | succ _ | max _ _ | param _ | mvar _ =>
          simp_all [levelStructEq]
  | param lhsName =>
      cases rhs <;> simp_all [levelStructEq, VLevel.ofLevel]
  | mvar lhsId =>
      simp [VLevel.ofLevel] at lhs_tr

/-- The transparent fast path used by constructor validation implies the
Theory universe inequality required by `fieldsWF`. -/
theorem levelStructGe_ofLevel
    (greater : levelStructGe result field = true)
    (result_tr : VLevel.ofLevel Us result = some result')
    (field_tr : VLevel.ofLevel Us field = some field') :
    field' ≤ result' := by
  induction result generalizing field result' field' with
  | zero =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some result' at result_tr
          change some (.zero : VLevel) = some field' at field_tr
          injection result_tr with result_tr
          injection field_tr with field_tr
          subst result'
          subst field'
          exact VLevel.le_refl _
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          simp_all [levelStructGe, levelStructEq]
  | succ result ih =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ field =>
          simp only [levelStructGe] at greater
          simp only [VLevel.ofLevel, Option.bind_eq_bind] at result_tr field_tr
          obtain ⟨result'', result_inner_tr, result'_eq⟩ :=
            Option.bind_eq_some_iff.mp result_tr
          obtain ⟨field'', field_inner_tr, field'_eq⟩ :=
            Option.bind_eq_some_iff.mp field_tr
          change some result''.succ = some result' at result'_eq
          change some field''.succ = some field' at field'_eq
          injection result'_eq with result'_eq
          injection field'_eq with field'_eq
          subst result'
          subst field'
          exact VLevel.succ_le_succ
            (ih greater result_inner_tr field_inner_tr)
      | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | max result₁ result₂ ih₁ ih₂ =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | imax result₁ result₂ ih₁ ih₂ =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | param resultName =>
      cases field with
      | zero =>
          change some (.zero : VLevel) = some field' at field_tr
          injection field_tr with field_tr
          subst field'
          exact VLevel.zero_le
      | succ _ | max _ _ | imax _ _ | param _ | mvar _ =>
          have equal := levelStructEq_ofLevel (Us := Us)
            (by simpa [levelStructGe] using greater) result_tr field_tr
          cases equal
          exact VLevel.le_refl _
  | mvar resultId =>
      simp [VLevel.ofLevel] at result_tr

/-- The impredicative fallback is exact: a kernel level recognized as zero
translates to Theory's zero level. -/
theorem ofLevel_eq_zero_of_isZero
    (zero : level.isZero = true)
    (level_tr : VLevel.ofLevel Us level = some level') :
    level' = .zero := by
  cases level <;> simp_all [Level.isZero, VLevel.ofLevel]

/-- Executable universe comparison supported by the current semantic proof.

This is deliberately an under-approximation of Lean's constructor validator:
it accepts the transparent structural comparison and the impredicative Prop
exception, but not the normalized `Level.geq` fallback.  Soundness of that
fallback requires a correctness theorem for Lean's core `Level.normalize`,
which Lean 4.31 does not currently expose. -/
def constructorUniverseSemanticGe (resultLevel fieldLevel : Level) : Bool :=
  levelStructGe resultLevel fieldLevel || resultLevel.isZero

/-- Replay just the universe-bearing part of one constructor telescope.

The traversal deliberately follows the validator's parameter substitution,
ordinary-field local contexts, annotation consumption, and recursion fuel.
Unlike `checkConstructorType`, it accepts an ordinary field only through the
proved structural/`Prop` comparison above.  Running this audit in addition to
the ordinary validator is therefore an executable under-approximation, not a
replacement validator and not a proof-only semantic premise. -/
def checkConstructorUniverseSemantics (stats : InductiveStats) (t : Expr) :
    M Unit := do
  loop t 0 (← readThe Context).fuel.inductiveFuel
where
  loop (t : Expr) (i : Nat) : Nat → M Unit
    | 0 => throw .deepRecursion
    | fuel + 1 => do
      if let .forallE name domain body binderInfo := t then
        if let some parameter := stats.params[i]? then
          loop (body.instantiate1 parameter) (i + 1) fuel
        else
          let sortResult ← ensureType domain
          unless constructorUniverseSemanticGe stats.resultLevel
              sortResult.sortLevel! do
            throw <| .other
              "constructor universe lies outside the verified semantic subset"
          withLocalDecl name binderInfo (consumeTypeAnnotations domain) fun arg =>
            loop (body.instantiate1 arg) (i + 1) fuel

/-- Source-ordered universe audit for every constructor in one singleton
family.  Constructor names and types come from the same indexed source list
as `ConstructorListValidationTrace`; all non-universe validation remains in
that retained ordinary trace. -/
def checkConstructorUniverseListSemantics (stats : InductiveStats) :
    List Constructor → M Unit
  | [] => pure ()
  | constructor :: constructors => do
      checkConstructorUniverseSemantics stats constructor.type
      checkConstructorUniverseListSemantics stats constructors

/-- The executable semantic decision at the exact universe node retained by
ordinary constructor validation. -/
def ConstructorUniverseTrace.semantic
    (_trace : ConstructorUniverseTrace resultLevel fieldLevel) : Bool :=
  constructorUniverseSemanticGe resultLevel fieldLevel

/-- Conjunction of the semantic universe decisions in one exact constructor
telescope. Parameter and terminal nodes contribute no universe obligation. -/
def ConstructorTypeValidationTrace.universeSemantics
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) : Bool :=
  match trace with
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail =>
      tail.universeSemantics
  | .ordinary _ _ _ _ _ _ _ _ _ _ universeTrace _ tail =>
      universeTrace.semantic && tail.universeSemantics
  | .terminal _ _ _ _ _ _ => true

/-- Source-ordered conjunction of every constructor telescope's semantic
universe decisions. -/
def ConstructorListValidationTrace.universeSemantics
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) : Bool :=
  match trace with
  | .nil _ => true
  | .cons _ _ _ _ _ _ typeTrace tailTrace =>
      typeTrace.universeSemantics && tailTrace.universeSemantics

/-- The complete semantic-universe gate attached to one retained ordinary
constructor-validation run. -/
def ConstructorValidationRun.universeSemantics
    (validation : ConstructorValidationRun indType stats isUnsafe context) :
    Bool :=
  validation.trace.universeSemantics

/-- Recover the state-bearing verified-checker execution erased by the
ordinary constructor validator's `ensureType` observation. -/
theorem ConstructorEnsureTypeStep.innerRun
    (step : ConstructorEnsureTypeStep) (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.ensureType step.source step.context.toTypeChecker
          ({} : TypeChecker.State) = .ok (step.result, state) := by
  unfold ConstructorEnsureTypeStep.Valid TypeChecker.M.run at hvalid
  cases hrun : TypeChecker.ensureType step.source
      { env := step.context.env
        lctx := step.context.lctx
        safety := step.context.safety
        lparams := step.context.lparams
        fuel := step.context.fuel }
      ({} : TypeChecker.State) with
  | error err =>
      simp [StateT.run', Functor.map, Except.map, hrun] at hvalid
  | ok pair =>
      rcases pair with ⟨result, state⟩
      have result_eq : result = step.result := by
        simpa [StateT.run', Functor.map, Except.map, hrun] using hvalid
      subst result
      exact ⟨state, by simpa [Context.toTypeChecker] using hrun⟩

/-- Theory interpretation of the exact `ensureType` execution retained for
an ordinary constructor field. -/
structure TypeChecker.EnsureTypeRun (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (source result : Expr) (source' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  source_tr : TrExprS env Us Δ source source'
  resultLevel : Level
  resultLevel' : VLevel
  result_eq : result = .sort resultLevel
  resultLevel_tr : VLevel.ofLevel Us resultLevel = some resultLevel'
  source_type : env.HasType Us.length Δ.toCtx source' (.sort resultLevel')
  run_eq : ∃ state : State,
    ensureType source context.toContext ({} : State) = .ok (result, state)

/-- Attach verified Theory meaning to one retained ordinary-field
`ensureType` step in its exact post-family context. -/
theorem TypeChecker.EnsureTypeRun.exists_ofConstructorStep
    (step : ConstructorEnsureTypeStep) (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source') :
    Nonempty (EnsureTypeRun contextRun.context.venv
      contextRun.context.lparams contextRun.context.vlctx
      step.source step.result source') := by
  obtain ⟨state, run⟩ := step.innerRun hvalid
  rw [← contextRun.context_eq] at run
  obtain ⟨_, _, _, _, translated, translated_tr, u, u', result_eq,
      level_tr, source_type⟩ :=
    (ensureType.WF source_tr) contextRun.state_wf step.result state run
  have translated_def := translated_tr.uniq contextRun.context.Ewf
    (.refl contextRun.context.Ewf contextRun.context.Δwf) source_tr
  have source_type' := source_type.defeqU_l contextRun.context.Ewf
    contextRun.context.Δwf translated_def
  exact ⟨{
    context := contextRun.context
    venv_eq := rfl
    lparams_eq := rfl
    vlctx_eq := rfl
    state_wf := contextRun.state_wf
    source_tr := source_tr
    resultLevel := u
    resultLevel' := u'
    result_eq := result_eq
    resultLevel_tr := level_tr
    source_type := source_type'
    run_eq := ⟨state, run⟩ }⟩

/-!
## Exact post-family view alignment

Constructor validation and constructor-candidate construction deliberately
allocate their ordinary-field free variables from different reader states.
The following audit therefore never compares those identifiers.  It follows
the already-retained validation trace and instantiates the exact candidate
view with the *validation* parameter/field expression at each position.
Every comparison consequently happens in the real post-family local context,
while the candidate itself still owns the view being inspected.
-/

/-- Number of parameter/ordinary binders consumed by one exact constructor
validation trace. -/
def ConstructorTypeValidationTrace.spineLength
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) : Nat :=
  match trace with
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.spineLength + 1
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.spineLength + 1
  | .terminal .. => 0

/-- Every local declaration entered by a retained positivity traversal uses
an identifier absent from the exact incoming local context.  This is an
executable structural condition, not a semantic premise. -/
def ConstructorPositivityTrace.freshNames
    (trace : ConstructorPositivityTrace stats ctor argIdx context source fuel) :
    Bool :=
  match trace with
  | .absent .. => true
  | .forallE context _ _ _ _ _ _ _ _ _ tail =>
      (context.lctx.find? context.freshFVarId).isNone && tail.freshNames
  | .target .. => true

def ConstructorPositivityModeTrace.freshNames
    (trace : ConstructorPositivityModeTrace stats isUnsafe ctor argIdx
      context source) : Bool :=
  match trace with
  | .skipped .. => true
  | .safe _ trace => trace.freshNames

/-- One exact full-check observation together with the syntactic premise used
by the verified checker refinement.  Keeping the premise at the operational
boundary avoids reconstructing free-variable membership later from binder
names or from a parallel telescope. -/
structure ConstructorCheckedExpr (context : Context) (source : Expr) where
  fvars : source.FVarsIn
    (fun fv => (context.lctx.find? fv).isSome = true)
  observation : CandidateCheckTypeObservation context source

/-- Retain an already verified full-check execution together with a structural
scope proof for its exact source expression. -/
def ConstructorCheckedExpr.ofRun
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (run : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    ConstructorCheckedExpr context source :=
  ⟨fvars, ⟨inferred, run⟩⟩

private theorem constructorClosed_hasMVar_false
    {env : Kernel.Environment} {name : Name} {source : Expr}
    (closed : env.checkNoMVarNoFVar name source = .ok ()) :
    source.hasMVar = false := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar at closed
  cases hmvars : source.hasMVar
  · rfl
  · simp [hmvars, Bind.bind, Except.bind] at closed

private theorem constructorClosed_hasFVar_false
    {env : Kernel.Environment} {name : Name} {source : Expr}
    (closed : env.checkNoMVarNoFVar name source = .ok ()) :
    source.hasFVar = false := by
  have hmvars := constructorClosed_hasMVar_false closed
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar at closed
  cases hfvars : source.hasFVar
  · rfl
  · simp [hmvars, hfvars, Bind.bind, Except.bind, Pure.pure,
      Except.pure] at closed

/-- Constructor metadata accepted by the validator is closed, so its retained
empty-context full-check observation directly supplies the D2 root scope. -/
def ConstructorCheckedExpr.ofClosedRoot
    {context : Context} {name : Name} {source : Expr}
    (closed : context.env.checkNoMVarNoFVar name source = .ok ())
    (observation : CandidateCheckTypeObservation
      context.withEmptyLocalContext source) :
    ConstructorCheckedExpr context.withEmptyLocalContext source where
  fvars := fvarsIn_iff.2 ⟨by
    intro fv present
    have empty := fvarsList_eq_nil.mpr
      (constructorClosed_hasFVar_false closed)
    rw [empty] at present
    contradiction,
    fvarsIn_iff_hasMVar.2 (constructorClosed_hasMVar_false closed)⟩
  observation := observation

/-- Execute a full check only after confirming that every free variable of
the exact source belongs to the retained implementation context. -/
def checkConstructorAlignedExpr (context : Context) (source : Expr) :
    Except Exception (ConstructorCheckedExpr context source) := do
  if hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true then
    if hmvars : source.hasMVar = false then
      have fvars : source.FVarsIn
          (fun fv => (context.lctx.find? fv).isSome = true) :=
        fvarsIn_iff.2 ⟨by
          intro fv hfv
          have h := List.all_eq_true.mp hfvars fv hfv
          exact h,
        fvarsIn_iff_hasMVar.2 hmvars⟩
      let observation ← observeCandidateCheckType context source
      pure ⟨fvars, observation⟩
    else
      throw <| .other "constructor alignment source contains a metavariable"
  else
    throw <| .other "constructor alignment source escaped its local context"

/-- Reuse an exact full-check execution to expose the successful result of
the supplemental scope-aware checker boundary. -/
theorem checkConstructorAlignedExpr.exists_of_run
    (hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true)
    (hmvars : source.hasMVar = false)
    (hrun : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    ∃ checked : ConstructorCheckedExpr context source,
      checkConstructorAlignedExpr context source = .ok checked := by
  unfold checkConstructorAlignedExpr
  rw [dif_pos hfvars, dif_pos hmvars]
  rw [observeCandidateCheckType_of_run context source inferred hrun]
  exact ⟨_, rfl⟩

/-- Re-executing the supplemental scope/full-check boundary reproduces any
retained successful observation.  The only reconstructed fields are proofs,
so proof irrelevance identifies the executable result with the retained
value itself. -/
theorem ConstructorCheckedExpr.check_eq
    (checked : ConstructorCheckedExpr context source) :
    checkConstructorAlignedExpr context source = .ok checked := by
  have hfvars : source.fvarsList.all
      (fun fv => (context.lctx.find? fv).isSome) = true := by
    apply List.all_eq_true.mpr
    intro fv present
    exact (fvarsIn_iff.mp checked.fvars).1 fv present
  have hmvars : source.hasMVar = false :=
    fvarsIn_iff_hasMVar.mp (fvarsIn_iff.mp checked.fvars).2
  unfold checkConstructorAlignedExpr
  rw [dif_pos hfvars, dif_pos hmvars]
  rw [observeCandidateCheckType_of_run context source
    checked.observation.inferred checked.observation.valid]
  cases checked
  rfl

/-- Determinism of the erased implementation run pins a retained full-check
observation to any independently proved result of that same exact check. -/
theorem ConstructorCheckedExpr.inferred_eq_of_run
    (checked : ConstructorCheckedExpr context source)
    (hrun : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩) :
    checked.observation.inferred = inferred := by
  have retained := checked.observation.valid
  unfold CandidateCheckTypeStep.Valid at retained hrun
  rw [hrun] at retained
  exact (Except.ok.inj retained).symm

/-- Re-executing a retained equality observation returns that same
observation; its sole field is proof-valued. -/
theorem CandidateIsDefEqObservation.observe_eq
    (observation : CandidateIsDefEqObservation context lhs rhs) :
    observeCandidateIsDefEq context lhs rhs = .ok observation := by
  rw [observeCandidateIsDefEq_of_run context lhs rhs observation.valid]

/-- The verified implementation equality checker accepts a syntactically
identical pair without inspecting or mutating its equivalence manager. -/
theorem candidateIsDefEqRefl
    (context : Context) (source : Expr) :
    CandidateIsDefEqStep.Valid ⟨context, source, source⟩ := by
  unfold CandidateIsDefEqStep.Valid TypeChecker.M.run TypeChecker.isDefEq
    TypeChecker.RecM.run TypeChecker.Inner.isDefEq
  simp [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
    StateT.bind, Except.bind, StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rfl

/-- Convert the executable implementation-context scope check to the exact
Theory free-variable premise used by verified `checkType` refinement. -/
theorem ConstructorCheckedExpr.fvarsIn
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) :
    source.FVarsIn (· ∈ contextRun.context.vlctx.fvars) := by
  apply checked.fvars.mono
  intro fv present
  have implementationPresent :
      ∃ declaration, context.lctx.find? fv = some declaration := by
    simpa only [Option.isSome_iff_exists] using present
  have verifiedPresent :
      ∃ declaration, contextRun.context.lctx.find? fv = some declaration := by
    simpa only [contextRun.context_lctx] using implementationPresent
  apply contextRun.context.trlctx.find?_eq_some.mp
  change ∃ declaration,
    contextRun.context.mlctx.lctx.find? fv = some declaration
  rw [contextRun.context.lctx_eq]
  exact verifiedPresent

/-- Verified meaning of one full check retained by the alignment audit.  Both
Theory endpoints are selected by the checker refinement; callers cannot
substitute an unrelated translation for the exact source position. -/
structure ConstructorCheckedExpr.Run
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) where
  source' : VExpr
  inferred' : VExpr
  check : TypeChecker.CheckTypeRun contextRun.context.venv
    contextRun.context.lparams contextRun.context.vlctx source
    checked.observation.inferred source' inferred'

/-- Interpret an aligned full-check observation in its exact verified
post-family context. -/
theorem ConstructorCheckedExpr.Run.exists
    (checked : ConstructorCheckedExpr context source)
    (contextRun : TypeChecker.CandidateContextRun context) :
    Nonempty (ConstructorCheckedExpr.Run checked contextRun) := by
  obtain ⟨source', inferred', ⟨check⟩⟩ :=
    TypeChecker.CheckTypeRun.exists_ofCandidateStepFVars
      ⟨context, source, checked.observation.inferred⟩
      checked.observation.valid contextRun (checked.fvarsIn contextRun)
  exact ⟨⟨source', inferred', check⟩⟩

/-- A retained full check whose implementation result is syntactically a
sort supplies the exact Theory `IsType` premise needed to extend the local
context. -/
theorem ConstructorCheckedExpr.Run.isType_of_inferredSort
    (run : ConstructorCheckedExpr.Run checked contextRun)
    (inferred_eq : checked.observation.inferred = .sort u) :
    contextRun.context.IsType run.source' := by
  rcases run with ⟨source', inferred', check⟩
  have inferred_tr := check.inferred_tr
  rw [inferred_eq] at inferred_tr
  cases inferred_tr
  exact check.isType

/-- Reuse a proved scope boundary with the exact full-check observation owned
by another retained execution of the same source expression. -/
def ConstructorCheckedExpr.withObservation
    (scope : ConstructorCheckedExpr context source)
    (observation : CandidateCheckTypeObservation context source) :
    ConstructorCheckedExpr context source :=
  ⟨scope.fvars, observation⟩

/-- Interpret one retained equality observation at the exact Theory
translations selected by the two aligned full checks. -/
def ConstructorCheckedExpr.Run.isDefEq
    {context : Context} {lhs rhs : Expr}
    {lhsCheck : ConstructorCheckedExpr context lhs}
    {rhsCheck : ConstructorCheckedExpr context rhs}
    {contextRun : TypeChecker.CandidateContextRun context}
    (lhsRun : ConstructorCheckedExpr.Run lhsCheck contextRun)
    (rhsRun : ConstructorCheckedExpr.Run rhsCheck contextRun)
    (observation : CandidateIsDefEqObservation context lhs rhs) :
    TypeChecker.IsDefEqRun contextRun.context.venv
      contextRun.context.lparams contextRun.context.vlctx lhs rhs
      lhsRun.source' rhsRun.source' :=
  TypeChecker.IsDefEqRun.ofCandidateStep
    ⟨context, lhs, rhs⟩ observation.valid contextRun.context
    contextRun.context_eq rfl rfl rfl contextRun.state_wf
    lhsRun.check.expr_tr rhsRun.check.expr_tr context.fuel.recDepth rfl

/-- A validation-local verified context pinned to the one post-family Theory
environment and universe-parameter list used by the whole constructor list. -/
structure ConstructorContextRun (env : VEnv) (Us : List Name)
    (context : Context) where
  candidate : TypeChecker.CandidateContextRun context
  venv_eq : candidate.context.venv = env
  lparams_eq : candidate.context.lparams = Us

def ConstructorContextRun.withEmptyLocalContext
    (run : ConstructorContextRun env Us context) :
    ConstructorContextRun env Us context.withEmptyLocalContext where
  candidate := run.candidate.withEmptyLocalContext
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq

/-- Extend the actual post-family verified context by exactly one retained
validation local declaration. -/
def ConstructorContextRun.pushLocalDecl
    (run : ConstructorContextRun env Us context)
    (name : Name) (binderInfo : BinderInfo) (domain : Expr)
    (fresh : context.lctx.find? context.freshFVarId = none)
    (domain' : VExpr)
    (domain_tr : run.candidate.context.TrExprS domain domain')
    (domain_type : run.candidate.context.IsType domain') :
    ConstructorContextRun env Us
      (context.pushLocalDecl name binderInfo domain) := by
  let candidate := run.candidate.pushLocalDecl name binderInfo domain fresh
    domain' domain_tr domain_type
  refine ⟨candidate, ?_, ?_⟩
  · calc
      candidate.context.venv = run.candidate.context.venv := by
        simp [candidate]
      _ = env := run.venv_eq
  · calc
      candidate.context.lparams = run.candidate.context.lparams := by
        simp [candidate, AddInductive.Context.pushLocalDecl]
      _ = Us := run.lparams_eq

/-- Verified interpretation of one exact retained WHNF operation, sharing the
source translation already selected by its aligned full check. -/
structure ConstructorWhnfRun
    {context : Context} {source : Expr}
    {sourceCheck : ConstructorCheckedExpr context source}
    (contextRun : TypeChecker.CandidateContextRun context)
    (sourceRun : ConstructorCheckedExpr.Run sourceCheck contextRun)
    (result : Expr) where
  result' : VExpr
  result_tr : contextRun.context.TrExprS result result'
  whnf : TypeChecker.WhnfRun contextRun.context.venv
    contextRun.context.lparams contextRun.context.vlctx source result
    sourceRun.source' result'

theorem ConstructorWhnfRun.exists
    {context : Context} {source result : Expr}
    {sourceCheck : ConstructorCheckedExpr context source}
    (contextRun : TypeChecker.CandidateContextRun context)
    (sourceRun : ConstructorCheckedExpr.Run sourceCheck contextRun)
    (valid : CandidateWhnfStep.Valid ⟨context, source, result⟩)
    (recursionFuel : Nat)
    (depth : context.fuel.recDepth = recursionFuel + 1) :
    Nonempty (ConstructorWhnfRun contextRun sourceRun result) := by
  obtain ⟨result', result_tr, ⟨whnf⟩⟩ :=
    TypeChecker.WhnfRun.exists_ofCandidateStep
      ⟨context, source, result⟩ valid contextRun sourceRun.source'
      sourceRun.check.expr_tr recursionFuel depth
  exact ⟨⟨result', result_tr, whnf⟩⟩

/-- Retained operational evidence for the supplemental nested-positivity
alignment.  The ordinary positivity trace continues to own every WHNF,
occurrence decision, and accepted recursive target.  This trace adds the full
checks and annotation equality needed to interpret those exact operations in
the verified checker. -/
inductive ConstructorPositivityAlignmentTrace :
    {stats : InductiveStats} → {ctor : Name} → {argIdx : Nat} →
    {context : Context} → {source : Expr} → {fuel : Nat} →
    ConstructorPositivityTrace stats ctor argIdx context source fuel → Type where
  | absent
      (sourceCheck : ConstructorCheckedExpr context source) :
      ConstructorPositivityAlignmentTrace
        (.absent context source result fuel whnfStep occurs)
  | forallE
      (sourceCheck : ConstructorCheckedExpr context source)
      (domainCheck : ConstructorCheckedExpr context domain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (consumedLevel : Level)
      (consumedInferred : consumedCheck.observation.inferred =
        .sort consumedLevel)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (tailTrace : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel)
      (tail : ConstructorPositivityAlignmentTrace tailTrace) :
      ConstructorPositivityAlignmentTrace
        (.forallE context source fuel name domain body binderInfo whnfStep occurs
          domainFree tailTrace)
  | target
      (sourceCheck : ConstructorCheckedExpr context source) :
      ConstructorPositivityAlignmentTrace
        (.target context source result fuel targetIdx whnfStep occurs terminal
          valid)

namespace ConstructorPositivityAlignmentTrace

def build :
    (positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
      source fuel) →
      Except Exception (ConstructorPositivityAlignmentTrace positivityTrace)
  | .absent context source result fuel whnfStep occurs => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      pure <| .absent sourceCheck
  | .forallE context source fuel name domain body binderInfo whnfStep occurs
      domainFree tailTrace => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      let domainCheck ← checkConstructorAlignedExpr context domain
      let consumedCheck ← checkConstructorAlignedExpr context
        (consumeTypeAnnotations domain)
      match consumedInferred : consumedCheck.observation.inferred with
      | .sort consumedLevel =>
        if fresh : context.lctx.find? context.freshFVarId = none then
          let annotations ← observeCandidateIsDefEq context domain
            (consumeTypeAnnotations domain)
          let tail ← build tailTrace
          pure <| .forallE sourceCheck domainCheck consumedCheck consumedLevel
            consumedInferred fresh annotations tailTrace tail
        else
          throw <| .other "positivity traversal reused a local identifier"
      | _ =>
        throw <| .other
          "consumed positivity domain did not check as a type"
  | .target context source result fuel targetIdx whnfStep occurs terminal
      valid => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      pure <| .target sourceCheck

/-- Executable erasure of the retained positivity alignment. -/
def check (positivityTrace : ConstructorPositivityTrace stats ctor argIdx
    context source fuel) : M Unit := fun _ =>
  (ConstructorPositivityAlignmentTrace.build positivityTrace).map fun _ => ()

theorem nonempty_of_check
    {positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
      source fuel}
    (success : ConstructorPositivityAlignmentTrace.check positivityTrace
      context = .ok ()) :
    Nonempty (ConstructorPositivityAlignmentTrace positivityTrace) := by
  unfold check at success
  cases h : ConstructorPositivityAlignmentTrace.build positivityTrace with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorPositivityAlignmentTrace

inductive ConstructorPositivityModeAlignmentTrace :
    {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
    {argIdx : Nat} → {context : Context} → {source : Expr} →
    ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source →
      Type where
  | skipped : ConstructorPositivityModeAlignmentTrace (.skipped unsafeEq)
  | safe (alignment : ConstructorPositivityAlignmentTrace positivityTrace) :
      ConstructorPositivityModeAlignmentTrace (.safe unsafeEq positivityTrace)

namespace ConstructorPositivityModeAlignmentTrace

def build :
    (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
      argIdx context source) →
      Except Exception
        (ConstructorPositivityModeAlignmentTrace positivityTrace)
  | .skipped unsafeEq => pure <| .skipped
  | .safe unsafeEq positivityTrace => do
      let alignment ← ConstructorPositivityAlignmentTrace.build
        positivityTrace
      pure <| .safe alignment

def check (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe
    ctor argIdx context source) : M Unit := fun _ =>
  (ConstructorPositivityModeAlignmentTrace.build positivityTrace).map fun _ => ()

theorem nonempty_of_check
    {positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
      argIdx context source}
    (success : ConstructorPositivityModeAlignmentTrace.check positivityTrace
      context = .ok ()) :
    Nonempty (ConstructorPositivityModeAlignmentTrace positivityTrace) := by
  unfold check at success
  cases h : ConstructorPositivityModeAlignmentTrace.build positivityTrace with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorPositivityModeAlignmentTrace

/-- Exact operational alignment between one retained validation telescope and
the analyzer-owned kernel view.  The recursive indices instantiate the view
with validation-owned parameters and fields, so no equality between the
producer's and validator's fresh free-variable identifiers is assumed. -/
inductive ConstructorViewAlignmentTrace :
    {stats : InductiveStats} → {isUnsafe : Bool} → {familyIdx : Nat} →
    {ctor : Name} → {context : Context} → {source : Expr} →
    {argIdx fuel : Nat} →
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor context
      source argIdx fuel →
    (view : Expr) → Type where
  | parameter
      (domainCheck : ConstructorCheckedExpr context domain)
      (viewDomainCheck : ConstructorCheckedExpr context viewDomain)
      (parameterTypeCheck : ConstructorCheckedExpr context parameterType)
      (parameterShape : param = .fvar fv)
      (parameterPresent : (context.lctx.find? fv).isSome = true)
      (tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel)
      (tail : ConstructorViewAlignmentTrace tailTrace
        (viewBody.instantiate1 param)) :
      ConstructorViewAlignmentTrace
        (.parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeRun validationDefEq tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | ordinary
      (domainCheck : ConstructorCheckedExpr context domain)
      (viewDomainCheck : ConstructorCheckedExpr context viewDomain)
      (consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain))
      (positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
        argIdx context domain)
      (positivityAlignment :
        ConstructorPositivityModeAlignmentTrace positivityTrace)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateIsDefEqObservation context domain
        (consumeTypeAnnotations domain))
      (tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel)
      (tail : ConstructorViewAlignmentTrace tailTrace
        (viewBody.instantiate1 context.freshExpr)) :
      ConstructorViewAlignmentTrace
        (.ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureTypeStep universeTrace positivityTrace tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | terminal
      (sourceCheck : ConstructorCheckedExpr context source)
      (viewCheck : ConstructorCheckedExpr context view)
      (viewTerminal : view.isForall = false)
      (viewValid : isValidIndAppIdx stats view familyIdx = true) :
      ConstructorViewAlignmentTrace
        (.terminal context source fuel argIdx sourceTerminal sourceValid) view

namespace ConstructorViewAlignmentTrace

/-- Execute the exact component audit and retain every successful checker
observation.  This is intentionally not a second `checkConstructors` run: the
raw branch shape, parameter selection, universe decision, positivity target,
and raw terminal acceptance remain owned by the ordinary validation trace. -/
def build :
    (validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel) →
    (view : Expr) →
      Except Exception (ConstructorViewAlignmentTrace validationTrace view)
  | .parameter context parameterFuel parameterArgIdx parameterName domain
      parameterBody parameterBinderInfo param parameterType parameterAt
      parameterTypeRun validationDefEq tailTrace,
      .forallE viewName viewDomain viewBody viewBinderInfo => do
      let domainCheck ← checkConstructorAlignedExpr context domain
      let viewDomainCheck ← checkConstructorAlignedExpr context viewDomain
      let parameterTypeCheck ← checkConstructorAlignedExpr context
        parameterType
      match param with
      | .fvar fv =>
        if parameterPresent : (context.lctx.find? fv).isSome = true then
          let tail ← build tailTrace
            (viewBody.instantiate1 (.fvar fv))
          pure <| .parameter domainCheck viewDomainCheck parameterTypeCheck
            rfl parameterPresent tailTrace tail
        else
          throw <| .other
            "constructor parameter is absent from validation context"
      | _ =>
        throw <| .other "constructor parameter is not a local variable"
  | .parameter .., _ =>
      throw <| .other "candidate and validation constructor telescopes differ"
  | .ordinary context ordinaryFuel ordinaryArgIdx name domain body binderInfo
      sortResult noParameter ensureType universeTrace positivityTrace tailTrace,
      .forallE viewName viewDomain viewBody viewBinderInfo => do
      let domainCheck ← checkConstructorAlignedExpr context domain
      let viewDomainCheck ← checkConstructorAlignedExpr context viewDomain
      let consumedCheck ← checkConstructorAlignedExpr context
        (consumeTypeAnnotations domain)
      let positivityAlignment ←
        ConstructorPositivityModeAlignmentTrace.build positivityTrace
      if fresh : context.lctx.find? context.freshFVarId = none then
        let annotations ← observeCandidateIsDefEq context domain
          (consumeTypeAnnotations domain)
        let tail ← build tailTrace
          (viewBody.instantiate1 context.freshExpr)
        pure <| .ordinary domainCheck viewDomainCheck consumedCheck
          positivityTrace positivityAlignment fresh annotations tailTrace tail
      else
        throw <| .other "constructor validation reused a local identifier"
  | .ordinary .., _ =>
      throw <| .other "candidate and validation constructor telescopes differ"
  | .terminal context source fuel argIdx sourceTerminal sourceValid, view => do
      let sourceCheck ← checkConstructorAlignedExpr context source
      let viewCheck ← checkConstructorAlignedExpr context view
      if viewTerminal : view.isForall = false then
        if viewValid : isValidIndAppIdx stats view familyIdx = true then
          pure <| .terminal sourceCheck viewCheck viewTerminal viewValid
        else
          throw <| .other
            "candidate view changed the terminal family application"
      else
        throw <| .other "candidate view has an extra constructor field"

def check (validationTrace : ConstructorTypeValidationTrace stats isUnsafe
    familyIdx ctor context source argIdx fuel) (view : Expr) : M Unit :=
  fun _ => (build validationTrace view).map fun _ => ()

theorem nonempty_of_check
    {validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel}
    (success : check validationTrace view context = .ok ()) :
    Nonempty (ConstructorViewAlignmentTrace validationTrace view) := by
  unfold check at success
  cases h : build validationTrace view with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorViewAlignmentTrace

/-- Supplemental checker audit for the exact analyzer-owned view of one
constructor.  It follows the validation telescope and instantiates the view
with validation-owned locals; successful execution retains no rewritten
declaration and claims no independent view acceptance. -/
def ConstructorTypeValidationTrace.checkViewAlignment
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) (view : Expr) : M Unit :=
  ConstructorViewAlignmentTrace.check trace view

/-- Source-ordered retained alignment for the complete constructor list.
The source indices make omission, duplication, and reordering unrepresentable.
Each node also retains the closed-root scope check needed to interpret the
validator's original empty-local-context `checkType` observation. -/
inductive ConstructorCandidateAlignmentTrace
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) :
    {seen : NameSet} → {constructors : List Constructor} →
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    AddInductive.CandidateList AddInductive.CandidateConstructor constructors →
      Type where
  | nil (seen : NameSet) :
      ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
        (.nil seen) .nil
  | cons
      {seen : NameSet} {head : Constructor} {tail : List Constructor}
      {fresh : seen.contains head.name = false}
      {closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ()}
      {rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type}
      {typeTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel}
      {tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail}
      {candidate : AddInductive.CandidateConstructor head}
      {candidates : AddInductive.CandidateList
        AddInductive.CandidateConstructor tail}
      (rootScope : ConstructorCheckedExpr context.withEmptyLocalContext
        head.type)
      (storedSpine : candidate.type.trace.storedSpine = true)
      (spineLength : candidate.type.trace.spineLength =
        typeTrace.spineLength)
      (candidateDepth : candidate.type.context.fuel.recDepth =
        context.fuel.recDepth)
      (headAlignment : ConstructorViewAlignmentTrace typeTrace
        candidate.type.view)
      (tailAlignment : ConstructorCandidateAlignmentTrace stats isUnsafe
        familyIdx context tailTrace candidates) :
      ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
        (.cons seen head tail fresh closed rootCheck typeTrace tailTrace)
        (.cons candidate candidates)

namespace ConstructorCandidateAlignmentTrace

/-- Execute the source-ordered constructor alignment and retain all successful
component checks.  The candidate list's dependent source index selects the
same constructor at every recursive position as the validation trace. -/
def build :
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) →
      Except Exception
        (ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
          validationTrace candidates)
  | .nil seen, .nil => pure <| .nil seen
  | .cons seen head tail fresh closed rootCheck typeTrace tailTrace,
      .cons candidate candidates => do
      let rootScope ← checkConstructorAlignedExpr
        context.withEmptyLocalContext head.type
      if storedSpine : candidate.type.trace.storedSpine = true then
        if spineLength : candidate.type.trace.spineLength =
            typeTrace.spineLength then
          if candidateDepth : candidate.type.context.fuel.recDepth =
              context.fuel.recDepth then
            let headAlignment ← ConstructorViewAlignmentTrace.build typeTrace
              candidate.type.view
            let tailAlignment ← build tailTrace candidates
            pure <| .cons rootScope storedSpine spineLength candidateDepth
              headAlignment tailAlignment
          else
            throw <| .other
              "candidate and validation checker depths differ"
        else
          throw <| .other
            "candidate and validation constructor lengths differ"
      else
        throw <| .other
          "candidate constructor did not preserve its stored spine"

def check
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) : M Unit :=
  fun _ => (build validationTrace candidates).map fun _ => ()

theorem nonempty_of_check
    {validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    (success : check validationTrace candidates context = .ok ()) :
    Nonempty (ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx
      context validationTrace candidates) := by
  unfold check at success
  cases h : build validationTrace candidates with
  | error error =>
      rw [h] at success
      change Except.error error = Except.ok () at success
      contradiction
  | ok alignment => exact ⟨alignment⟩

end ConstructorCandidateAlignmentTrace

/-- Source-ordered supplemental alignment audit for every exact constructor
candidate selected by the producer.  The dependent list indices rule out
truncation, reordering, duplication, or a view from another source position.
The Boolean gates additionally pin the candidate main-spine length to the
retained validation telescope. -/
def ConstructorListValidationTrace.checkCandidateAlignment
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) : M Unit :=
  ConstructorCandidateAlignmentTrace.check trace candidates

/-!
## Verified interpretation of the aligned validation telescope

The following semantic traces contain only executions refined by the verified
checker.  Their indices still carry the ordinary validator's branch choices
and exact candidate view, while `ConstructorContextRun` fixes every recursive
local context to the actual post-family Theory environment.
-/

/-- Verified interpretation of every exact WHNF and nested binder visited by
one retained positivity traversal. -/
inductive ConstructorPositivitySemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {ctor : Name} → {argIdx : Nat} →
    {context : Context} → {source : Expr} → {fuel : Nat} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPositivityTrace stats ctor argIdx context source fuel → Type where
  | absent
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source result : Expr} {fuel : Nat}
      {whnfStep : CandidateWhnfStep.Valid ⟨context, source, result⟩}
      {occurs : hasIndOcc stats.indConsts result = false}
      {sourceCheck : ConstructorCheckedExpr context source}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun result) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.absent context source result fuel whnfStep occurs)
  | forallE
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source : Expr} {fuel : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {whnfStep : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩}
      {occurs : hasIndOcc stats.indConsts
        (.forallE name domain body binderInfo) = true}
      {domainFree : hasIndOcc stats.indConsts domain = false}
      {tailTrace : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel}
      {sourceCheck : ConstructorCheckedExpr context source}
      {domainCheck : ConstructorCheckedExpr context domain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {consumedLevel : Level}
      {consumedInferred : consumedCheck.observation.inferred =
        .sort consumedLevel}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun
        (.forallE name domain body binderInfo))
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorPositivitySemanticRun env Us whnfFuel
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.forallE context source fuel name domain body binderInfo whnfStep
          occurs domainFree tailTrace)
  | target
      {stats : InductiveStats} {ctor : Name} {argIdx : Nat}
      {context : Context} {source result : Expr} {fuel targetIdx : Nat}
      {whnfStep : CandidateWhnfStep.Valid ⟨context, source, result⟩}
      {occurs : hasIndOcc stats.indConsts result = true}
      {terminal : result.isForall = false}
      {valid : isValidIndApp? stats result = some targetIdx}
      {sourceCheck : ConstructorCheckedExpr context source}
      {contextRun : ConstructorContextRun env Us context}
      (depth : context.fuel.recDepth = whnfFuel + 1)
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (whnfRun : ConstructorWhnfRun contextRun.candidate sourceRun result) :
      ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        (.target context source result fuel targetIdx whnfStep occurs terminal
          valid)

namespace ConstructorPositivitySemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {trace : ConstructorPositivityTrace stats ctor argIdx context source fuel}
    (alignment : ConstructorPositivityAlignmentTrace trace) :
    Nonempty (ConstructorPositivitySemanticRun env Us whnfFuel contextRun
      trace) := by
  induction trace with
  | absent context source result fuel whnfStep occurs =>
      cases alignment with
      | absent sourceCheck =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          exact ⟨ConstructorPositivitySemanticRun.absent
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            depth sourceRun whnfRun⟩
  | forallE context source fuel name domain body binderInfo whnfStep occurs
      domainFree tailTrace ih =>
      cases alignment with
      | forallE sourceCheck domainCheck consumedCheck consumedLevel
          consumedInferred fresh annotations _ tailAlignment =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨consumedRun⟩ :=
            ConstructorCheckedExpr.Run.exists consumedCheck
              contextRun.candidate
          let annotationsRun := domainRun.isDefEq consumedRun annotations
          have consumedType : contextRun.candidate.context.IsType
              consumedRun.source' :=
            consumedRun.isType_of_inferredSort consumedInferred
          let tailContext := contextRun.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain) fresh consumedRun.source'
            consumedRun.check.expr_tr consumedType
          have tailDepth :
              (context.pushLocalDecl name binderInfo
                (consumeTypeAnnotations domain)).fuel.recDepth =
                  whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using depth
          obtain ⟨tail⟩ := ih tailContext tailDepth tailAlignment
          exact ⟨ConstructorPositivitySemanticRun.forallE
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            (consumedLevel := consumedLevel)
            (consumedInferred := consumedInferred)
            depth sourceRun whnfRun domainRun consumedRun annotationsRun
            consumedType tail⟩
  | target context source result fuel targetIdx whnfStep occurs terminal valid =>
      cases alignment with
      | target sourceCheck =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨whnfRun⟩ := ConstructorWhnfRun.exists
            contextRun.candidate sourceRun whnfStep whnfFuel depth
          exact ⟨ConstructorPositivitySemanticRun.target
            (stats := stats) (ctor := ctor) (argIdx := argIdx)
            depth sourceRun whnfRun⟩

end ConstructorPositivitySemanticRun

/-- Verified meaning of the exact safe/unsafe positivity branch retained by
ordinary constructor validation. -/
inductive ConstructorPositivityModeSemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
    {argIdx : Nat} → {context : Context} → {source : Expr} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source →
      Type where
  | skipped :
      {stats : InductiveStats} → {isUnsafe : Bool} → {ctor : Name} →
      {argIdx : Nat} → {context : Context} → {source : Expr} →
      {unsafeEq : isUnsafe = true} →
      {contextRun : ConstructorContextRun env Us context} →
      ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
        (@ConstructorPositivityModeTrace.skipped stats isUnsafe ctor argIdx
          context source unsafeEq)
  | safe
      {stats : InductiveStats} {isUnsafe : Bool} {ctor : Name}
      {argIdx : Nat} {context : Context} {source : Expr}
      {unsafeEq : isUnsafe = false}
      {positivityTrace : ConstructorPositivityTrace stats ctor argIdx context
        source context.fuel.inductiveFuel}
      {contextRun : ConstructorContextRun env Us context}
      (semantic : ConstructorPositivitySemanticRun env Us whnfFuel contextRun
        positivityTrace) :
      ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
        (@ConstructorPositivityModeTrace.safe stats isUnsafe ctor argIdx
          context source unsafeEq positivityTrace)

namespace ConstructorPositivityModeSemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {trace : ConstructorPositivityModeTrace stats isUnsafe ctor argIdx
      context source}
    (alignment : ConstructorPositivityModeAlignmentTrace trace) :
    Nonempty (ConstructorPositivityModeSemanticRun env Us whnfFuel contextRun
      trace) := by
  cases alignment with
  | @skipped unsafeEq =>
      exact ⟨ConstructorPositivityModeSemanticRun.skipped
        (env := env) (Us := Us) (whnfFuel := whnfFuel)
        (stats := stats) (isUnsafe := isUnsafe) (ctor := ctor)
        (argIdx := argIdx) (context := context) (source := source)
        (unsafeEq := unsafeEq) (contextRun := contextRun)⟩
  | safe positivityAlignment =>
      obtain ⟨semantic⟩ :=
        ConstructorPositivitySemanticRun.nonempty_of_alignment contextRun depth
          positivityAlignment
      exact ⟨.safe semantic⟩

end ConstructorPositivityModeSemanticRun

/-- Verified, componentwise interpretation of one aligned constructor
telescope.  The view is followed at validation-owned parameter and field
locals; no equality between candidate and validator fresh identifiers is
required or asserted. -/
inductive ConstructorViewSemanticRun
    (env : VEnv) (Us : List Name) (whnfFuel : Nat) :
    {stats : InductiveStats} → {isUnsafe : Bool} → {familyIdx : Nat} →
    {ctor : Name} → {context : Context} → {source : Expr} →
    {argIdx fuel : Nat} →
    (contextRun : ConstructorContextRun env Us context) →
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor context
      source argIdx fuel →
    (view : Expr) → Type where
  | parameter
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {fuel argIdx : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {param parameterType : Expr}
      {parameterAt : stats.params[argIdx]? = some param}
      {parameterTypeGet : getType param context = .ok parameterType}
      {validationDefEq : CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩}
      {tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel}
      {viewName : Name} {viewDomain viewBody : Expr}
      {viewBinderInfo : BinderInfo}
      {domainCheck : ConstructorCheckedExpr context domain}
      {viewDomainCheck : ConstructorCheckedExpr context viewDomain}
      {parameterTypeCheck : ConstructorCheckedExpr context parameterType}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (viewDomainRun : ConstructorCheckedExpr.Run viewDomainCheck
        contextRun.candidate)
      (parameterTypeSemantic : ConstructorCheckedExpr.Run parameterTypeCheck
        contextRun.candidate)
      (validationRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain parameterType
        domainRun.source' parameterTypeSemantic.source')
      (tail : ConstructorViewSemanticRun env Us whnfFuel contextRun tailTrace
        (viewBody.instantiate1 param)) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeGet validationDefEq tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | ordinary
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {fuel argIdx : Nat}
      {name : Name} {domain body : Expr} {binderInfo : BinderInfo}
      {sortResult : Expr} {noParameter : stats.params[argIdx]? = none}
      {ensureTypeStep : ConstructorEnsureTypeStep.Valid
        ⟨context, domain, sortResult⟩}
      {universeTrace : ConstructorUniverseTrace stats.resultLevel
        sortResult.sortLevel!}
      {positivityTrace : ConstructorPositivityModeTrace stats isUnsafe ctor
        argIdx context domain}
      {tailTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel}
      {viewName : Name} {viewDomain viewBody : Expr}
      {viewBinderInfo : BinderInfo}
      {domainCheck : ConstructorCheckedExpr context domain}
      {viewDomainCheck : ConstructorCheckedExpr context viewDomain}
      {consumedCheck : ConstructorCheckedExpr context
        (consumeTypeAnnotations domain)}
      {fresh : context.lctx.find? context.freshFVarId = none}
      {contextRun : ConstructorContextRun env Us context}
      (domainRun : ConstructorCheckedExpr.Run domainCheck
        contextRun.candidate)
      (viewDomainRun : ConstructorCheckedExpr.Run viewDomainCheck
        contextRun.candidate)
      (consumedRun : ConstructorCheckedExpr.Run consumedCheck
        contextRun.candidate)
      (ensureTypeRun : TypeChecker.EnsureTypeRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain sortResult
        domainRun.source')
      (positivity : ConstructorPositivityModeSemanticRun env Us whnfFuel
        contextRun positivityTrace)
      (annotationsRun : TypeChecker.IsDefEqRun
        contextRun.candidate.context.venv
        contextRun.candidate.context.lparams
        contextRun.candidate.context.vlctx domain
        (consumeTypeAnnotations domain) domainRun.source'
        consumedRun.source')
      (consumedType : contextRun.candidate.context.IsType
        consumedRun.source')
      (tail : ConstructorViewSemanticRun env Us whnfFuel
        (contextRun.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain) fresh consumedRun.source'
          consumedRun.check.expr_tr consumedType)
        tailTrace (viewBody.instantiate1 context.freshExpr)) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureTypeStep universeTrace positivityTrace tailTrace)
        (.forallE viewName viewDomain viewBody viewBinderInfo)
  | terminal
      {stats : InductiveStats} {isUnsafe : Bool} {familyIdx : Nat}
      {ctor : Name} {context : Context} {source view : Expr}
      {fuel argIdx : Nat} {sourceTerminal : source.isForall = false}
      {sourceValid : isValidIndAppIdx stats source familyIdx = true}
      {sourceCheck : ConstructorCheckedExpr context source}
      {viewCheck : ConstructorCheckedExpr context view}
      {contextRun : ConstructorContextRun env Us context}
      (sourceRun : ConstructorCheckedExpr.Run sourceCheck
        contextRun.candidate)
      (viewRun : ConstructorCheckedExpr.Run viewCheck contextRun.candidate) :
      ConstructorViewSemanticRun env Us whnfFuel contextRun
        (.terminal context source fuel argIdx sourceTerminal sourceValid) view

namespace ConstructorViewSemanticRun

theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    (depth : context.fuel.recDepth = whnfFuel + 1)
    {validationTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
      ctor context source argIdx fuel}
    {view : Expr}
    (alignment : ConstructorViewAlignmentTrace validationTrace view) :
    Nonempty (ConstructorViewSemanticRun env Us whnfFuel contextRun
      validationTrace view) := by
  induction validationTrace generalizing view with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeGet validationDefEq tailTrace ih =>
      cases alignment with
      | parameter domainCheck viewDomainCheck parameterTypeCheck
          parameterShape parameterPresent _ tailAlignment =>
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨viewDomainRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewDomainCheck
              contextRun.candidate
          obtain ⟨parameterTypeSemantic⟩ :=
            ConstructorCheckedExpr.Run.exists parameterTypeCheck
              contextRun.candidate
          let validationRun := TypeChecker.IsDefEqRun.ofCandidateStep
            ⟨context, domain, parameterType⟩ validationDefEq
            contextRun.candidate.context contextRun.candidate.context_eq
            rfl rfl rfl contextRun.candidate.state_wf
            domainRun.check.expr_tr parameterTypeSemantic.check.expr_tr
            context.fuel.recDepth rfl
          obtain ⟨tail⟩ := ih contextRun depth tailAlignment
          exact ⟨ConstructorViewSemanticRun.parameter
            domainRun viewDomainRun parameterTypeSemantic validationRun tail⟩
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureTypeStep universeTrace positivityTrace tailTrace ih =>
      cases alignment with
      | ordinary domainCheck viewDomainCheck consumedCheck _
          positivityAlignment fresh annotations _ tailAlignment =>
          obtain ⟨domainRun⟩ :=
            ConstructorCheckedExpr.Run.exists domainCheck contextRun.candidate
          obtain ⟨viewDomainRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewDomainCheck
              contextRun.candidate
          obtain ⟨consumedRun⟩ :=
            ConstructorCheckedExpr.Run.exists consumedCheck
              contextRun.candidate
          obtain ⟨ensureTypeRun⟩ :=
            TypeChecker.EnsureTypeRun.exists_ofConstructorStep
              ⟨context, domain, sortResult⟩ ensureTypeStep
              contextRun.candidate domainRun.source' domainRun.check.expr_tr
          obtain ⟨positivity⟩ :=
            ConstructorPositivityModeSemanticRun.nonempty_of_alignment
              contextRun depth positivityAlignment
          let annotationsRun := domainRun.isDefEq consumedRun annotations
          have consumedType : contextRun.candidate.context.IsType
              consumedRun.source' := by
            have annotationDef := annotationsRun.isDefEqU.of_l
              contextRun.candidate.context.Ewf
              contextRun.candidate.context.Δwf.toCtx
              ensureTypeRun.source_type
            exact ⟨ensureTypeRun.resultLevel', annotationDef.hasType.2⟩
          let tailContext := contextRun.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain) fresh consumedRun.source'
            consumedRun.check.expr_tr consumedType
          have tailDepth :
              (context.pushLocalDecl name binderInfo
                (consumeTypeAnnotations domain)).fuel.recDepth =
                  whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using depth
          obtain ⟨tail⟩ := ih tailContext tailDepth tailAlignment
          exact ⟨ConstructorViewSemanticRun.ordinary
            domainRun viewDomainRun consumedRun ensureTypeRun positivity
            annotationsRun consumedType tail⟩
  | terminal context source fuel argIdx sourceTerminal sourceValid =>
      cases alignment with
      | terminal sourceCheck viewCheck viewTerminal viewValid =>
          obtain ⟨sourceRun⟩ :=
            ConstructorCheckedExpr.Run.exists sourceCheck contextRun.candidate
          obtain ⟨viewRun⟩ :=
            ConstructorCheckedExpr.Run.exists viewCheck contextRun.candidate
          exact ⟨ConstructorViewSemanticRun.terminal
            (stats := stats) (isUnsafe := isUnsafe)
            (familyIdx := familyIdx) (ctor := ctor)
            sourceRun viewRun⟩

end ConstructorViewSemanticRun

/-!
## Source-ordered post-family constructor semantics

The alignment trace connects the validator's exact source telescope to the
analyzer-owned candidate view.  The semantic list below interprets that trace
alongside the already-produced constructor semantic hierarchy.  Its indices
keep source order, raw constructor order, and the exact candidate view fixed;
its payload retains both validation-local checks and Theory telescope/result
evidence selected by the candidate's recursive checker run.
-/

/-- Complete post-family meaning for every constructor position selected by
one exact validation/candidate alignment.

`root` interprets the validator-owned root `checkType` observation (the
supplemental audit contributes only its scope proof). `telescope` interprets
parameter equality, ordinary-field typing, positivity, and the terminal
family application while following the exact candidate view at
validation-owned locals. `spine` exposes the exact Theory view binders and
terminal result selected by the candidate semantic root. -/
inductive ConstructorPostFamilySemanticListRun
    (env : VEnv) (Us : List Name)
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) (contextRun : ConstructorContextRun env Us context) :
    {seen : NameSet} → {constructors : List Constructor} →
    (validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors) →
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors) →
    {raws : List VConstVal} →
    ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx context
      validationTrace candidates →
    VInductDecl.CandidateConstructorSemanticListRun env Us candidates raws →
      Type where
  | nil (seen : NameSet) :
      ConstructorPostFamilySemanticListRun env Us stats isUnsafe familyIdx
        context contextRun (.nil seen) .nil (.nil seen) .nil
  | cons
      {seen : NameSet} {head : Constructor} {tail : List Constructor}
      {freshName : seen.contains head.name = false}
      {closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ()}
      {rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type}
      {typeTrace : ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel}
      {tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail}
      {candidate : AddInductive.CandidateConstructor head}
      {candidates : AddInductive.CandidateList
        AddInductive.CandidateConstructor tail}
      {raw : VConstVal} {raws : List VConstVal}
      {rootScope : ConstructorCheckedExpr context.withEmptyLocalContext
        head.type}
      {storedSpine : candidate.type.trace.storedSpine = true}
      {spineLength : candidate.type.trace.spineLength =
        typeTrace.spineLength}
      {candidateDepth : candidate.type.context.fuel.recDepth =
        context.fuel.recDepth}
      {headAlignment : ConstructorViewAlignmentTrace typeTrace
        candidate.type.view}
      {tailAlignment : ConstructorCandidateAlignmentTrace stats isUnsafe
        familyIdx context tailTrace candidates}
      {headSemantic : VInductDecl.CandidateConstructorSemanticRun env Us
        candidate raw}
      {tailSemantic : VInductDecl.CandidateConstructorSemanticListRun env Us
        candidates raws}
      (root : ConstructorCheckedExpr.Run
        (rootScope.withObservation rootCheck)
        contextRun.withEmptyLocalContext.candidate)
      (telescope : ConstructorViewSemanticRun env Us
        headSemantic.type.whnfFuel contextRun typeTrace candidate.type.view)
      (spine : ∃ resultType,
        TypeChecker.TelResultDefEqEvidence env Us.length []
          (VExpr.telN candidate.type.trace.spineLength raw.type)
          (VExpr.telN candidate.type.trace.spineLength
            headSemantic.type.view)
          (VExpr.dropN candidate.type.trace.spineLength raw.type)
          (VExpr.dropN candidate.type.trace.spineLength
            headSemantic.type.view)
          resultType)
      (tailRun : ConstructorPostFamilySemanticListRun env Us stats isUnsafe
        familyIdx context contextRun tailTrace candidates
        tailAlignment tailSemantic) :
      ConstructorPostFamilySemanticListRun env Us stats isUnsafe familyIdx
        context contextRun
        (.cons seen head tail freshName closed rootCheck typeTrace tailTrace)
        (.cons candidate candidates)
        (.cons rootScope storedSpine spineLength candidateDepth headAlignment
          tailAlignment)
        (.cons headSemantic tailSemantic)

namespace ConstructorPostFamilySemanticListRun

/-- Interpret an exact source-ordered alignment together with the exact
candidate semantic list produced for the same raw constructor positions. -/
theorem nonempty_of_alignment
    (contextRun : ConstructorContextRun env Us context)
    {validationTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor constructors}
    {raws : List VConstVal}
    (alignment : ConstructorCandidateAlignmentTrace stats isUnsafe familyIdx
      context validationTrace candidates)
    (semantics : VInductDecl.CandidateConstructorSemanticListRun env Us
      candidates raws) :
    Nonempty (ConstructorPostFamilySemanticListRun env Us stats isUnsafe
      familyIdx context contextRun validationTrace candidates alignment
      semantics) := by
  induction alignment generalizing raws with
  | nil seen =>
      cases semantics
      exact ⟨.nil seen⟩
  | @cons seen head tail freshName closed rootCheck typeTrace tailTrace
      candidate candidates rootScope storedSpine spineLength candidateDepth
      headAlignment tailAlignment ih =>
      cases semantics with
      | cons headSemantic tailSemantic =>
          obtain ⟨root⟩ := ConstructorCheckedExpr.Run.exists
            (rootScope.withObservation rootCheck)
            contextRun.withEmptyLocalContext.candidate
          have depth : context.fuel.recDepth =
              headSemantic.type.whnfFuel + 1 := by
            calc
              context.fuel.recDepth =
                  candidate.type.context.fuel.recDepth := candidateDepth.symm
              _ = headSemantic.type.whnfFuel + 1 :=
                headSemantic.type.whnfDepth
          obtain ⟨telescope⟩ :=
            ConstructorViewSemanticRun.nonempty_of_alignment contextRun depth
              headAlignment
          have spine := TypeChecker.CandidateExprSpineRun.evidence
            (headSemantic.type.spine storedSpine)
          obtain ⟨tailRun⟩ := ih tailSemantic
          exact ⟨.cons root telescope spine tailRun⟩

end ConstructorPostFamilySemanticListRun

/-- A successful executable universe audit marks every universe node in an
arbitrary retained constructor telescope.  The proof uses determinism of the
same `ensureType` execution retained by the ordinary trace; it cannot change a
field level or skip a source position. -/
theorem ConstructorTypeValidationTrace.universeSemantics_of_loop
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel)
    (success : checkConstructorUniverseSemantics.loop stats source argIdx fuel
      context = .ok ()) :
    trace.universeSemantics = true := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo parameter
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      simp only [universeSemantics]
      rw [show fuel + 1 = Nat.succ fuel by rfl] at success
      rw [checkConstructorUniverseSemantics.loop.eq_2] at success
      rw [parameterAt] at success
      exact ih success
  | ordinary context fuel argIdx name domain body binderInfo sortResult
      noParameter ensureType universeTrace positivity tail ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      rw [show fuel + 1 = Nat.succ fuel by rfl] at success
      rw [checkConstructorUniverseSemantics.loop.eq_2] at success
      rw [noParameter] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      rw [ensureType] at success
      simp only [Except.bind] at success
      cases valid : constructorUniverseSemanticGe stats.resultLevel
          sortResult.sortLevel! with
      | false =>
          rw [valid] at success
          change Except.error _ = Except.ok () at success
          cases success
      | true =>
          rw [valid] at success
          simp only [Pure.pure] at success
          exact ⟨valid, ih success⟩
  | terminal => rfl

/-- Root form of `universeSemantics_of_loop`, with the audit initialized from
the exact context fuel just like ordinary constructor validation. -/
theorem ConstructorTypeValidationTrace.universeSemantics_of_run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source 0 context.fuel.inductiveFuel)
    (success : checkConstructorUniverseSemantics stats source context =
      .ok ()) :
    trace.universeSemantics = true := by
  apply trace.universeSemantics_of_loop
  simpa only [checkConstructorUniverseSemantics, readThe,
    MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
    ReaderT.pure, Pure.pure, Except.bind, Except.pure] using success

/-- A successful source-list audit marks every retained constructor position;
the dependent list indices prevent omission, duplication, or reordering. -/
theorem ConstructorListValidationTrace.universeSemantics_of_run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors)
    (success : checkConstructorUniverseListSemantics stats constructors
      context = .ok ()) :
    trace.universeSemantics = true := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      simp only [universeSemantics, Bool.and_eq_true]
      simp only [checkConstructorUniverseListSemantics,
        ReaderT.bind, Bind.bind] at success
      cases headRun : checkConstructorUniverseSemantics stats head.type
          context with
      | error error =>
          rw [headRun] at success
          cases success
      | ok result =>
          cases result
          rw [headRun] at success
          simp only [Except.bind] at success
          exact ⟨typeTrace.universeSemantics_of_run headRun, ih success⟩

/-- Ordinary constructor validation paired with the executable semantic
universe audit over the identical singleton source list. This record narrows
the accepted package boundary while preserving the ordinary validator result
and every retained non-universe check unchanged. -/
structure ConstructorSemanticValidationRun
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  validation : ConstructorValidationRun indType stats isUnsafe context
  universeRun : checkConstructorUniverseListSemantics stats indType.ctors
    context = .ok ()

namespace ConstructorSemanticValidationRun

/-- Forgetting the semantic audit replays the exact ordinary validator, so
the strengthened run cannot widen kernel acceptance. -/
theorem run
    (semantic : ConstructorSemanticValidationRun indType stats isUnsafe
      context) :
    checkConstructors #[indType] stats isUnsafe context = .ok () :=
  semantic.validation.run

/-- Every universe-bearing node of the retained ordinary trace passed the
executable structural/`Prop` gate. -/
theorem universeSemantics
    (semantic : ConstructorSemanticValidationRun indType stats isUnsafe
      context) :
    semantic.validation.universeSemantics = true :=
  semantic.validation.trace.universeSemantics_of_run semantic.universeRun

end ConstructorSemanticValidationRun

/-- The semantic universe gate only accepts branches already accepted by the
ordinary constructor validator.  It therefore narrows package construction
without widening kernel validation behavior. -/
theorem ConstructorUniverseTrace.nonempty_of_semanticGe
    (valid : constructorUniverseSemanticGe resultLevel fieldLevel = true) :
    Nonempty (ConstructorUniverseTrace resultLevel fieldLevel) := by
  unfold constructorUniverseSemanticGe at valid
  simp only [Bool.or_eq_true] at valid
  rcases valid with structural | prop
  · exact ⟨.structural structural⟩
  · cases structural : levelStructGe resultLevel fieldLevel with
    | true => exact ⟨.structural structural⟩
    | false =>
        exact ⟨.fallback structural (by simp [prop])⟩

/-- The executable semantic subset implies exactly the disjunct required for
a non-recursive field in `VInductDecl.fieldsWF`: either the family is Prop or
the field universe is bounded by the family universe. -/
theorem constructorUniverseSemanticGe_ofLevel
    (valid : constructorUniverseSemanticGe resultLevel fieldLevel = true)
    (result_tr : VLevel.ofLevel Us resultLevel = some result')
    (field_tr : VLevel.ofLevel Us fieldLevel = some field') :
    result' = .zero ∨ field' ≤ result' := by
  unfold constructorUniverseSemanticGe at valid
  simp only [Bool.or_eq_true] at valid
  rcases valid with structural | prop
  · exact .inr (levelStructGe_ofLevel structural result_tr field_tr)
  · exact .inl (ofLevel_eq_zero_of_isZero prop result_tr)

/-- A fallback accepted solely by normalized `Level.geq` lies outside the
current sound semantic subset.  L4L-02C may widen this gate only after the
core level comparison has its own soundness proof. -/
theorem constructorUniverseSemanticGe_eq_false_of_geq_only
    (structural : levelStructGe resultLevel fieldLevel = false)
    (notProp : resultLevel.isZero = false) :
    constructorUniverseSemanticGe resultLevel fieldLevel = false := by
  simp [constructorUniverseSemanticGe, structural, notProp]

/- Regression for the v4.31 comparison gap: core normalization recognizes a
parameter below a `max`, while the sound structural/`Prop` subset deliberately
rejects that non-`Prop` comparison.  `Level.geq` is opaque, so its executable
outcome is pinned with `#guard` rather than promoted to an unproved theorem. -/
#guard (Level.max (.param `u) (.param `v)).geq (.param `u)
#guard !constructorUniverseSemanticGe
  (Level.max (.param `u) (.param `v)) (.param `u)

/- The universe bridge stays within Theory's accepted quotient/propositional
baseline.  In particular it does not inherit the project's pending
level-normalizer sorries, a custom axiom, or Lean's opaque `Level.geq`
implementation. -/
/--
info: 'Lean4Lean.AddInductive.levelStructEq_ofLevel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms levelStructEq_ofLevel

/--
info: 'Lean4Lean.AddInductive.levelStructGe_ofLevel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms levelStructGe_ofLevel

/--
info: 'Lean4Lean.AddInductive.constructorUniverseSemanticGe_ofLevel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms constructorUniverseSemanticGe_ofLevel

/--
info: 'Lean4Lean.AddInductive.ConstructorUniverseTrace.nonempty_of_semanticGe' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorUniverseTrace.nonempty_of_semanticGe

/--
info: 'Lean4Lean.AddInductive.ConstructorSemanticValidationRun.universeSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorSemanticValidationRun.universeSemantics

end AddInductive

namespace VInductDecl

/-!
## Staged ownership

The ordinary outer producer deliberately remains unchanged: its successful
equation records kernel validation, while this additive wrapper retains the
strictly smaller universe-semantic audit required by L4L-01D1.  Later
constructor-semantic checkpoints can extend this owner without making bare
`buildNormalizationCandidate` success carry Theory meaning.
-/

/-- A staged singleton semantic input together with the exact executable
constructor-universe audit for the same source list, family-validation stats,
and post-family checker context.

Keeping the ordinary staged input as data preserves the established candidate
and semantic hierarchy.  The dependent `universeRun` field prevents an audit
for another family, constructor ordering, parameter split, or environment from
being reused here. -/
structure StagedNormalizationCandidateUniverseInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  staged : StagedNormalizationCandidateSemanticInput familyContext
    constructorContext env Us candidate rawDecl
  universeRun :
    AddInductive.checkConstructorUniverseListSemantics
        staged.family.validation.stats source.ctors
        { candidate.families.singleton.familyType.type.trace.terminalContext with
          env := constructorContext.env } = .ok ()

/-- Pair the retained ordinary validation trace with its source-indexed
universe audit.  This is the strengthened D1 validation object; forgetting it
recovers exactly the pre-existing staged owner. -/
def StagedNormalizationCandidateUniverseInput.semanticValidation
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    AddInductive.ConstructorSemanticValidationRun source
      input.staged.family.validation.stats false
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env } where
  validation := input.staged.constructorValidation
  universeRun := input.universeRun

/-- Every universe-bearing node in the staged source-ordered validation trace
passes the structural/`Prop` semantic subset. -/
theorem StagedNormalizationCandidateUniverseInput.universeSemantics
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    input.staged.constructorValidation.universeSemantics = true :=
  input.semanticValidation.universeSemantics

/-- Preserve the existing automatic semantic-hierarchy construction while
retaining the strengthened universe gate in its staged owner. -/
theorem StagedNormalizationCandidateUniverseInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidateSemanticRun familyContext
    constructorContext env Us candidate rawDecl) :=
  input.staged.exists

/-!
## Post-family constructor ownership

This additive D2 owner keeps D1's universe gate and adds the exact executable
alignment between the retained validation telescope and every analyzer-owned
constructor candidate.  It does not replay `checkConstructors` on the view or
claim any pre-family field judgment.
-/

/-- The staged semantic/universe owner together with the source-ordered
post-family constructor alignment audit. -/
structure StagedNormalizationCandidatePostFamilyInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  universeInput : StagedNormalizationCandidateUniverseInput familyContext
    constructorContext env Us candidate rawDecl
  alignment : AddInductive.ConstructorCandidateAlignmentTrace
    universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors

/-- Package a successful executable alignment audit into the staged D2 owner.
The direct `alignment` field also permits proof-oriented clients to assemble
the same indexed trace from already-retained checker observations. -/
noncomputable def StagedNormalizationCandidatePostFamilyInput.ofRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (universeInput : StagedNormalizationCandidateUniverseInput familyContext
      constructorContext env Us candidate rawDecl)
    (alignmentRun :
      universeInput.staged.constructorValidation.trace.checkCandidateAlignment
          candidate.families.singleton.constructors
          { candidate.families.singleton.familyType.type.trace.terminalContext with
            env := constructorContext.env } = .ok ()) :
    StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl where
  universeInput := universeInput
  alignment := Classical.choice <|
    AddInductive.ConstructorCandidateAlignmentTrace.nonempty_of_check
      alignmentRun

/-- The exact output of D2: the established produced semantic hierarchy plus
the actual post-family validation context, retained source/candidate
alignment, and a positional semantic interpretation of every exact candidate
view binder and terminal result. -/
structure ProducedNormalizationCandidatePostFamilySemanticRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl) where
  produced : ProducedNormalizationCandidateSemanticRun familyContext
    constructorContext env Us candidate rawDecl
  contextRun : AddInductive.ConstructorContextRun
    produced.semantic.family.typeEnv Us
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
  alignment : AddInductive.ConstructorCandidateAlignmentTrace
    input.universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    input.universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors
  constructors : AddInductive.ConstructorPostFamilySemanticListRun
    produced.semantic.family.typeEnv Us
    input.universeInput.staged.family.validation.stats false 0
    { candidate.families.singleton.familyType.type.trace.terminalContext with
      env := constructorContext.env }
    contextRun input.universeInput.staged.constructorValidation.trace
    candidate.families.singleton.constructors alignment
    produced.semantic.family.constructors

/-- Interpret D2's executable alignment in the exact post-family Theory
environment obtained by the retained raw-family insertion.  The only
existential selections are checker-produced Theory translations already
encapsulated by `Nonempty`; no caller supplies a view. -/
theorem StagedNormalizationCandidatePostFamilyInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidatePostFamilyInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidatePostFamilySemanticRun input) := by
  obtain ⟨familySemantic⟩ :=
    input.universeInput.staged.semanticInput.family.exists
  let semantic : NormalizationCandidateSemanticRun env Us candidate rawDecl :=
    { raw := input.universeInput.staged.raw
      raw_types_eq := input.universeInput.staged.raw_types_eq
      uvars_eq := input.universeInput.staged.declaration_uvars_eq
      family := familySemantic }
  let produced : ProducedNormalizationCandidateSemanticRun familyContext
      constructorContext env Us candidate rawDecl :=
    { semantic := semantic
      familyTypesProduced :=
        input.universeInput.staged.familyTypesProduced
      familiesProduced := input.universeInput.staged.familiesProduced }
  have typeEnv_eq : familySemantic.typeEnv =
      input.universeInput.staged.family.typeEnv := by
    exact Option.some.inj <|
      familySemantic.addType.symm.trans
        input.universeInput.staged.family.addInduct.env_add
  obtain ⟨candidateContext, venv_eq, lparams_eq⟩ :=
    input.universeInput.staged.family.validationContextRun
      familySemantic.type
  let contextRun : AddInductive.ConstructorContextRun
      produced.semantic.family.typeEnv Us
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env } :=
    ⟨candidateContext, venv_eq.trans typeEnv_eq.symm, lparams_eq⟩
  let alignment := input.alignment
  obtain ⟨constructors⟩ :=
    AddInductive.ConstructorPostFamilySemanticListRun.nonempty_of_alignment
      contextRun alignment produced.semantic.family.constructors
  exact ⟨⟨produced, contextRun, alignment, constructors⟩⟩

/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidatePostFamilyInput.exists' depends on axioms: [propext,
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
#print axioms StagedNormalizationCandidatePostFamilyInput.exists

/- The wrapper projections expose their exact existing Verify closure.  The
new universe bridge itself remains separately guarded above; staging does not
hide the transitional dependencies already present in the semantic owner. -/
/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidateUniverseInput.semanticValidation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StagedNormalizationCandidateUniverseInput.semanticValidation

/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidateUniverseInput.universeSemantics' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StagedNormalizationCandidateUniverseInput.universeSemantics

/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidateUniverseInput.exists' depends on axioms: [propext,
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
#print axioms StagedNormalizationCandidateUniverseInput.exists

end VInductDecl
end Lean4Lean
