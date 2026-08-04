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
