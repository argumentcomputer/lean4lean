import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.Projection
import Lean4Lean.Theory.Typing.InductiveLemmas

/-!
# Projection expressibility fixtures

The main fixture is simultaneously parameterized, universe-polymorphic, and
dependent: the final field type mentions the preceding projection.  It is
small enough that the complete recursor encoding remains definitionally
inspectable.
-/

namespace Lean4Lean.Tests.ProjectionExpressibility

open Lean4Lean VInductDecl

universe u v

structure DependentRecord (α : Type u) (family : α → Type v) where
  key : α
  value : family key

def dependentRecordType : VInductiveType where
  name := ``DependentRecord
  uvars := 2
  type := vconst(type_of% @DependentRecord).type
  ctors := [⟨vconst(type_of% @DependentRecord.mk), ``DependentRecord.mk⟩]

def dependentRecordDecl : VInductDecl :=
  ⟨2, 2, [dependentRecordType]⟩

example : dependentRecordDecl.checked?.isSome = true := rfl

def dependentRecordChecked : dependentRecordDecl.Checked :=
  dependentRecordDecl.checked?.get (by decide)

def dependentRecordGeneration : dependentRecordDecl.GenerationChecked :=
  dependentRecordChecked.identityGeneration

def dependentRecordView : VStructureView where
  source := dependentRecordDecl
  generation := dependentRecordGeneration
  constructor := dependentRecordGeneration.block.ctorPairs[0]
  constructor_eq := rfl
  raw_indices_eq := rfl
  checked_indices_eq := rfl
  recursive_eq := rfl
  fieldSorts := [.succ (.param 0), .succ (.param 1)]
  fieldSorts_length := rfl

def dependentRecordEnv : VEnv :=
  (VEnv.empty.addInductGeneration dependentRecordGeneration).get (by decide)

theorem dependentRecord_add :
    VEnv.empty.addInductGeneration dependentRecordGeneration =
      some dependentRecordEnv := rfl

theorem dependentRecord_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty
      dependentRecordEnv dependentRecordGeneration) :=
  VEnv.addInductGeneration_trace dependentRecord_add

theorem dependentRecord_registered :
    dependentRecordView.Registered dependentRecordEnv := by
  rcases dependentRecord_trace with ⟨trace⟩
  refine {
    family := trace.family_lookup
    constructor := ?_
    recursor := trace.rec_lookup
    rules := fun _ h => trace.rule_mem h }
  apply trace.ctor_lookup
  rw [← dependentRecordGeneration.rawCtors_eq]
  exact List.mem_map.2 ⟨dependentRecordView.constructor,
    by
      change dependentRecordView.constructor ∈
        dependentRecordView.generation.block.ctorPairs
      rw [dependentRecordView.constructor_eq]
      simp,
    rfl⟩

theorem dependentRecord_view_wf :
    dependentRecordView.WF dependentRecordEnv := by
  refine {
    toRegistered := dependentRecord_registered
    parameters := ?_
    fieldTelescope := ?_
    smallFields := ?_ }
  · exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩
  · exact .cons (by type_tac) (.cons (by type_tac) .nil)
  · intro h
    change VInductDecl.ElimMode.large = .small at h
    contradiction

/-- The checked artifact retains both parameters and exactly the two
dependent fields from the real kernel declaration. -/
example : dependentRecordGeneration.block.rawParams =
    [.sort (.succ (.param 0)),
      .forallE (.bvar 0) (.sort (.succ (.param 1)))] := rfl

example : dependentRecordView.fields =
    [.bvar 1, .app (.bvar 1) (.bvar 0)] := rfl

example : dependentRecordGeneration.elimination = .large := rfl

private def permC (ci : VConstant) (levels : List VLevel) : VConstant :=
  ⟨ci.uvars, ci.type.instL levels⟩

example : dependentRecordGeneration.recursor =
    permC (vconst(type_of% @DependentRecord.rec))
      [.param 1, .param 2, .param 0] := rfl

def symbolicLevels : List VLevel := [.param 0, .param 1]

/-- Parameters in the context `[family, α]`, outermost first. -/
def symbolicParams : List VExpr := [.bvar 1, .bvar 0]

def symbolicStructureType : VExpr :=
  dependentRecordView.structureType symbolicLevels symbolicParams

example : dependentRecordView.specializedFields symbolicLevels symbolicParams =
    [.bvar 1, .app (.bvar 1) (.bvar 0)] := rfl

def keyCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicParams)[0]

def valueCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicParams)[1]

/-- Constructor reduction selects the first field for `key`. -/
example : keyCode.minor =
    .lam (.bvar 1)
      (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 1)) := rfl

/-- Constructor reduction selects the second field for `value`. -/
example : valueCode.minor =
    .lam (.bvar 1)
      (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 0)) := rfl

/-- The first field type is `α`. -/
example : keyCode.typeFn =
    .lam symbolicStructureType (.bvar 2) := rfl

/-- The dependent second field type is `family (key major)`: the earlier
projection program occurs in the later motive, rather than being supplied by
an unconstrained witness. -/
example : valueCode.typeFn =
    .lam symbolicStructureType
      (.app (.bvar 1) (.app keyCode.projector.lift (.bvar 0))) := rfl

example : dependentRecordView.projectionLevels keyCode.fieldSort symbolicLevels =
    [.succ (.param 0), .param 0, .param 1] := rfl

example : dependentRecordView.projectionLevels valueCode.fieldSort symbolicLevels =
    [.succ (.param 1), .param 0, .param 1] := rfl

example : dependentRecordView.project? symbolicLevels symbolicParams 2 (.bvar 0) =
    none := rfl

/-! A fully constrained `VEnv.TrProj` witness in a universe-polymorphic
local context. -/

def symbolicAlphaType : VExpr := .sort (.succ (.param 0))

def symbolicFamilyType : VExpr :=
  .forallE (.bvar 0) (.sort (.succ (.param 1)))

/-- The major binder type is written over `[family, α]`. -/
def symbolicMajorBinderType : VExpr :=
  dependentRecordView.structureType symbolicLevels [.bvar 1, .bvar 0]

def symbolicContext : List VExpr :=
  [symbolicMajorBinderType, symbolicFamilyType, symbolicAlphaType]

/-- The same parameters as seen under the major binder. -/
def symbolicMajorParams : List VExpr := [.bvar 2, .bvar 1]

def symbolicMajor : VExpr := .bvar 0

theorem symbolicLevels_wf :
    ∀ level ∈ symbolicLevels, level.WF 2 := by
  simp [symbolicLevels, VLevel.WF]

theorem symbolicParams_spine :
    ∃ resultLevel, dependentRecordEnv.SpineWF 2 symbolicContext
      (dependentRecordView.familyType.instL symbolicLevels)
      symbolicMajorParams (.sort resultLevel) := by
  refine ⟨.max (.succ (.param 0)) (.succ (.param 1)),
    ⟨_, _, rfl, by type_tac, ?_⟩⟩
  exact ⟨_, _, rfl, by type_tac, rfl⟩

theorem symbolicMajor_hasType :
    dependentRecordEnv.HasType 2 symbolicContext symbolicMajor
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams) := by
  exact .bvar .zero

def symbolicKeyCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicMajorParams)[0]

def symbolicValueCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicMajorParams)[1]

def symbolicKeyResult : VExpr :=
  .app symbolicKeyCode.projector symbolicMajor

def symbolicValueResult : VExpr :=
  .app symbolicValueCode.projector symbolicMajor

theorem key_representable :
    dependentRecordEnv.TrProj 2 symbolicContext dependentRecordView
      symbolicLevels symbolicMajorParams 0 symbolicMajor symbolicKeyResult := by
  refine {
    viewWF := dependentRecord_view_wf
    levelsWF := symbolicLevels_wf
    levels_length := rfl
    params_length := rfl
    paramsSpine := symbolicParams_spine
    majorType := symbolicMajor_hasType
    program := ⟨symbolicKeyCode, rfl, rfl⟩ }

theorem value_representable :
    dependentRecordEnv.TrProj 2 symbolicContext dependentRecordView
      symbolicLevels symbolicMajorParams 1 symbolicMajor symbolicValueResult := by
  refine {
    viewWF := dependentRecord_view_wf
    levelsWF := symbolicLevels_wf
    levels_length := rfl
    params_length := rfl
    paramsSpine := symbolicParams_spine
    majorType := symbolicMajor_hasType
    program := ⟨symbolicValueCode, rfl, rfl⟩ }

/-- The one generated iota equation used by both projection programs is
actually registered in the final Theory environment. -/
example : dependentRecordGeneration.generatedRules.length = 1 := rfl

theorem dependentRecord_rules_registered :
    ∀ rule ∈ dependentRecordGeneration.generatedRules,
      dependentRecordEnv.defeqs rule :=
  dependentRecord_view_wf.rules

/-! ## Frozen legacy surface

The seven fields below preserve the exact pre-L4L-13 theorem shapes.  They
are intentionally only statement data: constructing this bundle would
reintroduce the old proof obligations.  In particular, `wf` permits
unrelated contexts, `uniq` permits unrelated structure names, and every
field omits the environment, universe instantiation, and parameter spine. -/

abbrev LegacyTrProj :=
  List VExpr → Name → Nat → VExpr → VExpr → Prop

structure LegacyProjectionLaws (R : LegacyTrProj) : Prop where
  weak : ∀ {n Γ Γ' s i e e'},
    Ctx.Lift' n Γ Γ' → R Γ s i e e' →
      R Γ' s i (e.lift' n) (e'.lift' n)
  inverseWeakening : ∀ {env U l Γ Γ' s i e e'},
    VEnv.WF env → OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      R Γ' s i (e.lift' l) e' → ∃ result, R Γ s i e result
  contextDefEq : ∀ {env U Γ₁ Γ₂ s i e₁ e₂ result},
    VEnv.WF env → env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.IsDefEqU U Γ₁ e₁ e₂ → R Γ₁ s i e₁ result →
        ∃ result', R Γ₂ s i e₂ result'
  wellFormed : ∀ {env U Δ Γ s i e result},
    R Δ s i e result → VExpr.WF env U Γ e →
      VExpr.WF env U Γ result
  unique : ∀ {env U Γ₁ Γ₂ s₁ s₂ i e₁ e₂ result₁ result₂},
    VEnv.WF env → env.IsDefEqCtx U [] Γ₁ Γ₂ →
      R Γ₁ s₁ i e₁ result₁ → R Γ₂ s₂ i e₂ result₂ →
        env.IsDefEqU U Γ₁ e₁ e₂ →
          env.IsDefEqU U Γ₁ result₁ result₂
  termSubstitution : ∀ {Γ₀ Γ₁ Γ s i e e' e₀ A₀ k},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → R Γ₁ s i e e' →
      R Γ s i (e.inst e₀ k) (e'.inst e₀ k)
  universeInstantiation : ∀ {U' Γ s i e e'} {ls : List VLevel},
    (∀ level ∈ ls, level.WF U') → R Γ s i e e' →
      R (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls)

/-! ## Zero-field behavior -/

universe w

structure EmptyRecord (α : Type w) where

def emptyRecordType : VInductiveType where
  name := ``EmptyRecord
  uvars := 1
  type := vconst(type_of% @EmptyRecord).type
  ctors := [⟨vconst(type_of% @EmptyRecord.mk), ``EmptyRecord.mk⟩]

def emptyRecordDecl : VInductDecl :=
  ⟨1, 1, [emptyRecordType]⟩

example : emptyRecordDecl.checked?.isSome = true := rfl

def emptyRecordChecked : emptyRecordDecl.Checked :=
  emptyRecordDecl.checked?.get (by decide)

def emptyRecordGeneration : emptyRecordDecl.GenerationChecked :=
  emptyRecordChecked.identityGeneration

def emptyRecordView : VStructureView where
  source := emptyRecordDecl
  generation := emptyRecordGeneration
  constructor := emptyRecordGeneration.block.ctorPairs[0]
  constructor_eq := rfl
  raw_indices_eq := rfl
  checked_indices_eq := rfl
  recursive_eq := rfl
  fieldSorts := []
  fieldSorts_length := rfl

def emptyRecordEnv : VEnv :=
  (VEnv.empty.addInductGeneration emptyRecordGeneration).get (by decide)

theorem emptyRecord_add :
    VEnv.empty.addInductGeneration emptyRecordGeneration =
      some emptyRecordEnv := rfl

theorem emptyRecord_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty
      emptyRecordEnv emptyRecordGeneration) :=
  VEnv.addInductGeneration_trace emptyRecord_add

theorem emptyRecord_registered : emptyRecordView.Registered emptyRecordEnv := by
  rcases emptyRecord_trace with ⟨trace⟩
  refine {
    family := trace.family_lookup
    constructor := ?_
    recursor := trace.rec_lookup
    rules := fun _ h => trace.rule_mem h }
  apply trace.ctor_lookup
  rw [← emptyRecordGeneration.rawCtors_eq]
  exact List.mem_map.2 ⟨emptyRecordView.constructor,
    by
      change emptyRecordView.constructor ∈
        emptyRecordView.generation.block.ctorPairs
      rw [emptyRecordView.constructor_eq]
      simp,
    rfl⟩

theorem emptyRecord_view_wf : emptyRecordView.WF emptyRecordEnv := by
  refine {
    toRegistered := emptyRecord_registered
    parameters := ⟨⟨_, by type_tac⟩, trivial⟩
    fieldTelescope := .nil
    smallFields := ?_ }
  intro _ level hlevel
  change level ∈ ([] : List VLevel) at hlevel
  contradiction

example : emptyRecordView.fields = [] := rfl

example : emptyRecordView.projectionCodes [.param 0] [.bvar 0] = [] := rfl

theorem emptyRecord_project_none (idx : Nat) (major : VExpr) :
    emptyRecordView.project? [.param 0] [.bvar 0] idx major = none := by
  simp [VStructureView.project?, show
    emptyRecordView.projectionCodes [.param 0] [.bvar 0] = [] from rfl]

/--
info: 'Lean4Lean.Tests.ProjectionExpressibility.dependentRecord_view_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dependentRecord_view_wf

/--
info: 'Lean4Lean.Tests.ProjectionExpressibility.key_representable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms key_representable

/--
info: 'Lean4Lean.Tests.ProjectionExpressibility.value_representable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms value_representable

/--
info: 'Lean4Lean.Tests.ProjectionExpressibility.emptyRecord_project_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms emptyRecord_project_none

end Lean4Lean.Tests.ProjectionExpressibility
