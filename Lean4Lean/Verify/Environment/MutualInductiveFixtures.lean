import Lean4Lean.Verify.Environment.InductiveFixtures
import Lean4Lean.Theory.MutualInductiveFixtures

/-!
# Mutual validation and normalization replay

L4L-08B instantiates the arbitrary-block validator traces and Theory semantic
boundary for the real `Tree`/`TreeList` and indexed mutual fixtures.  Family
types are interpreted in one input environment, every family is then staged
before any constructor is interpreted, and constructors may target either
source-ordered family (including beneath a positive Pi telescope).

This checkpoint remains validation-only: it introduces no mutual recursor,
rule generation, or permanent environment transaction.
-/

namespace Lean4Lean.MutualInductiveReplayFixtures

open Lean Meta Elab Term
open Kernel
open AddInductive
open VInductDecl
open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.InductiveReplayFixtures

local instance : Inhabited VEnv := ⟨.empty⟩

/-- Quote a kernel recursor type using the recursor metadata's own universe
parameter order. -/
syntax "kernelRecConstant08C%" ident : term
syntax "kernelConstVType08C%" ident : term

elab_rules : term
  | `(kernelRecConstant08C% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    let type ← Lean4Lean.Meta.expandExpr info.type
    let type ← Lean4Lean.Meta.ofExpr info.levelParams {} type
    return toExpr ({ uvars := info.levelParams.length, type } : VConstant)

/-- Quote a stored kernel metadata type in that record's own universe order.
Together with the explicit record-field checks below, this observes universe
permutations as well as the translated type expression. -/
elab_rules : term
  | `(kernelConstVType08C% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let info ← getConstInfo name
    let type ← Lean4Lean.Meta.expandExpr info.type
    let type ← Lean4Lean.Meta.ofExpr info.levelParams {} type
    return toExpr type

/-! ## Complete block metadata parity -/

/-- One block-wide comparison between the retained Theory generation and all
kernel inductive metadata.  The nested lists preserve family/constructor
ownership and split each recursor's local rules out of the globally flattened
Theory rule list. -/
structure MutualKernelBlockRow where
  source : VInductDecl
  generation : BlockGenerationChecked source
  inductInfos : List ConstantInfo
  ctorInfos : List (List ConstantInfo)
  recInfos : List ConstantInfo
  familyTypes : List VExpr
  ctorTypes : List (List VExpr)
  recTypes : List VExpr
  ruleRhs : List (List VExpr)

namespace MutualKernelBlockRow

def ctorMatches (row : MutualKernelBlockRow)
    (family : NormalizedFamily) (info : ConstantInfo)
    (constructor : NormalizedCtor) (storedType : VExpr) : Bool :=
  match info with
  | .ctorInfo ctor =>
      ctor.name == constructor.raw.name &&
        ctor.levelParams.length == row.source.uvars &&
        ctor.induct == family.raw.name &&
        ctor.numParams == row.source.nparams &&
        ctor.numFields == constructor.view.fields.length &&
        !ctor.isUnsafe && storedType == constructor.raw.type
  | _ => false

def ctorsMatch (row : MutualKernelBlockRow)
    (family : NormalizedFamily) :
    List ConstantInfo → List NormalizedCtor → List VExpr → Bool
  | [], [], [] => true
  | info :: infos, constructor :: constructors, storedType :: storedTypes =>
      row.ctorMatches family info constructor storedType &&
        row.ctorsMatch family infos constructors storedTypes
  | _, _, _ => false

def recursorMatches (row : MutualKernelBlockRow)
    (family : NormalizedFamily) (offset : Nat)
    (info : ConstantInfo) (storedType : VExpr)
    (rhs : List VExpr) : Bool :=
  match info with
  | .recInfo rec =>
      rec.name == .str family.raw.name "rec" &&
        rec.levelParams.length == row.generation.recUvars &&
        rec.all == row.source.types.map (·.name) &&
        rec.numParams == row.source.nparams &&
        rec.numIndices == family.view.indices.length &&
        rec.numMotives == row.generation.familyCount &&
        rec.numMinors == row.generation.minorCount &&
        rec.k == row.generation.kTarget &&
        !rec.isUnsafe &&
        rec.rules.map (fun rule => (rule.ctor, rule.nfields)) ==
          family.ctorPairs.map (fun constructor =>
            (constructor.raw.name, constructor.view.fields.length)) &&
        storedType == (row.generation.recursor family).type &&
        rhs == ((row.generation.generatedRules.drop offset).take
          family.ctorPairs.length |>.map (·.rhs))
  | _ => false

def familiesMatch (row : MutualKernelBlockRow) :
    List NormalizedFamily → List ConstantInfo → List (List ConstantInfo) →
      List ConstantInfo → List VExpr → List (List VExpr) → List VExpr →
      List (List VExpr) → Nat → Bool
  | [], [], [], [], [], [], [], [], _ => true
  | family :: families, inductInfo :: inductInfos,
      ctorInfos :: ctorInfosTail, recInfo :: recInfos,
      familyType :: familyTypes, ctorTypes :: ctorTypesTail,
      recType :: recTypes, ruleRhs :: ruleRhsTail, offset =>
      (match inductInfo with
        | .inductInfo induct =>
            induct.name == family.raw.name &&
              induct.levelParams.length == row.source.uvars &&
              induct.numParams == row.source.nparams &&
              induct.numIndices == family.view.indices.length &&
              induct.all == row.source.types.map (·.name) &&
              induct.ctors == family.raw.ctors.map (·.name) &&
              induct.numNested == 0 && !induct.isUnsafe &&
              familyType == family.raw.type
        | _ => false) &&
      row.ctorsMatch family ctorInfos family.ctorPairs ctorTypes &&
      row.recursorMatches family offset recInfo recType ruleRhs &&
      row.familiesMatch families inductInfos ctorInfosTail recInfos
        familyTypes ctorTypesTail recTypes ruleRhsTail
        (offset + family.ctorPairs.length)
  | _, _, _, _, _, _, _, _, _ => false

/-- Every list must agree position-for-position; no truncated family,
constructor, recursor, or rule inventory can satisfy the comparison. -/
def agrees (row : MutualKernelBlockRow) : Bool :=
  row.familiesMatch row.generation.families row.inductInfos row.ctorInfos
    row.recInfos row.familyTypes row.ctorTypes row.recTypes row.ruleRhs 0

end MutualKernelBlockRow

/-! ## Executable kernel validation -/

def treeKernelInfo : ConstantInfo := kernelInductInfo% Tree
def treeListKernelInfo : ConstantInfo := kernelInductInfo% TreeList
def treeLeafKernelInfo : ConstantInfo := kernelCtorInfo% Tree.leaf
def treeNodeKernelInfo : ConstantInfo := kernelCtorInfo% Tree.node
def treeBranchKernelInfo : ConstantInfo := kernelCtorInfo% Tree.branch
def treeListNilKernelInfo : ConstantInfo := kernelCtorInfo% TreeList.nil
def treeListConsKernelInfo : ConstantInfo := kernelCtorInfo% TreeList.cons
def treeRecKernelInfo : ConstantInfo := kernelRecInfo% Tree.rec
def treeListRecKernelInfo : ConstantInfo := kernelRecInfo% TreeList.rec
def treeRecKernelConstant : VConstant := kernelRecConstant08C% Tree.rec
def treeListRecKernelConstant : VConstant :=
  kernelRecConstant08C% TreeList.rec
def treeLeafKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 0
def treeNodeKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 1
def treeBranchKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 2
def treeListNilKernelRuleRhs : VExpr := kernelRecRuleRhs% TreeList.rec 0
def treeListConsKernelRuleRhs : VExpr := kernelRecRuleRhs% TreeList.rec 1

example : treeRecKernelConstant =
    treeGeneration.recursors[0].toVConstant := rfl
example : treeListRecKernelConstant =
    treeGeneration.recursors[1].toVConstant := rfl
example : treeLeafKernelRuleRhs = treeGeneration.generatedRules[0].rhs := rfl
example : treeNodeKernelRuleRhs = treeGeneration.generatedRules[1].rhs := rfl
example : treeBranchKernelRuleRhs = treeGeneration.generatedRules[2].rhs := rfl
example : treeListNilKernelRuleRhs = treeGeneration.generatedRules[3].rhs := rfl
example : treeListConsKernelRuleRhs = treeGeneration.generatedRules[4].rhs := rfl

def treeKernelType : InductiveType where
  name := treeKernelInfo.name
  type := treeKernelInfo.type
  ctors := [
    ⟨treeLeafKernelInfo.name, treeLeafKernelInfo.type⟩,
    ⟨treeNodeKernelInfo.name, treeNodeKernelInfo.type⟩,
    ⟨treeBranchKernelInfo.name, treeBranchKernelInfo.type⟩]

def treeListKernelType : InductiveType where
  name := treeListKernelInfo.name
  type := treeListKernelInfo.type
  ctors := [
    ⟨treeListNilKernelInfo.name, treeListNilKernelInfo.type⟩,
    ⟨treeListConsKernelInfo.name, treeListConsKernelInfo.type⟩]

def treeKernelTypes : List InductiveType :=
  [treeKernelType, treeListKernelType]

def treeKernelContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_mutualTree ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def treeExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 1 treeKernelTypes 0 false
    treeKernelContext

theorem treeExecutionResult_isOk : treeExecutionResult.isOk = true := by
  native_decide

def treeProducedExecution :
    { execution // treeExecutionResult = .ok execution } :=
  match h : treeExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := treeExecutionResult_isOk
      rw [h] at hOk
      contradiction

def treeExecution := treeProducedExecution.val

def treeFamilyValidationResult :=
  FamilyValidationBlockRun.buildExecution 1 treeKernelTypes treeKernelContext

theorem treeFamilyValidationResult_isOk :
    treeFamilyValidationResult.isOk = true := by
  native_decide

def treeProducedFamilyValidation :
    { run // treeFamilyValidationResult = .ok run } :=
  match h : treeFamilyValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := treeFamilyValidationResult_isOk
      rw [h] at hOk
      contradiction

def treeFamilyValidation := treeProducedFamilyValidation.val

def treeConstructorContext : AddInductive.Context :=
  { treeExecution.validationContext with env := treeExecution.familyEnv }

def treeConstructorValidationResult :=
  ConstructorBlockValidationRun.buildExecution treeKernelTypes
    treeExecution.stats false treeConstructorContext

theorem treeConstructorValidationResult_isOk :
    treeConstructorValidationResult.isOk = true := by
  native_decide

def treeProducedConstructorValidation :
    { run // treeConstructorValidationResult = .ok run } :=
  match h : treeConstructorValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := treeConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

def treeConstructorValidation := treeProducedConstructorValidation.val

/-- The real positivity traversal selects both sibling targets and records the
one Pi binder above `Tree.branch`'s recursive occurrence. -/
theorem treeConstructorTargets_exact :
    treeConstructorValidation.traces.targets =
      [
        [[none],
          [some { familyIdx := 1, binderDepth := 0 }],
          [some { familyIdx := 1, binderDepth := 1 }]],
        [[],
          [some { familyIdx := 0, binderDepth := 0 },
            some { familyIdx := 1, binderDepth := 0 }]]
      ] := by
  native_decide

example : treeFamilyValidation.parameters.size = 1 :=
  treeFamilyValidation.params_size

example : treeFamilyValidation.result.stats.nindices = #[0, 0] := by
  native_decide

#guard AddInductive.levelStructEq treeFamilyValidation.resultLevel
  (.succ (.param `u))

#guard AddInductive.levelStructEq treeExecution.stats.resultLevel
  (.succ (.param `u))

def indexedTreeKernelInfo : ConstantInfo := kernelInductInfo% IndexedTree
def indexedTreeListKernelInfo : ConstantInfo :=
  kernelInductInfo% IndexedTreeList
def indexedTreeLeafKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTree.leaf
def indexedTreeNodeKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTree.node
def indexedTreeListNilKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTreeList.nil
def indexedTreeListConsKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTreeList.cons
def indexedTreeRecKernelInfo : ConstantInfo :=
  kernelRecInfo% IndexedTree.rec
def indexedTreeListRecKernelInfo : ConstantInfo :=
  kernelRecInfo% IndexedTreeList.rec
def indexedTreeRecKernelConstant : VConstant :=
  kernelRecConstant08C% IndexedTree.rec
def indexedTreeListRecKernelConstant : VConstant :=
  kernelRecConstant08C% IndexedTreeList.rec
def indexedTreeLeafKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTree.rec 0
def indexedTreeNodeKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTree.rec 1
def indexedTreeListNilKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTreeList.rec 0
def indexedTreeListConsKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTreeList.rec 1

example : indexedTreeRecKernelConstant =
    indexedTreeGeneration.recursors[0].toVConstant := rfl
example : indexedTreeListRecKernelConstant =
    indexedTreeGeneration.recursors[1].toVConstant := rfl
example : indexedTreeLeafKernelRuleRhs =
    indexedTreeGeneration.generatedRules[0].rhs := rfl
example : indexedTreeNodeKernelRuleRhs =
    indexedTreeGeneration.generatedRules[1].rhs := rfl
example : indexedTreeListNilKernelRuleRhs =
    indexedTreeGeneration.generatedRules[2].rhs := rfl
example : indexedTreeListConsKernelRuleRhs =
    indexedTreeGeneration.generatedRules[3].rhs := rfl

/-- Complete kernel/Theory metadata row for the unindexed mutual block. -/
def treeKernelBlockRow : MutualKernelBlockRow where
  source := treeDecl
  generation := treeGeneration
  inductInfos := [treeKernelInfo, treeListKernelInfo]
  ctorInfos := [
    [treeLeafKernelInfo, treeNodeKernelInfo, treeBranchKernelInfo],
    [treeListNilKernelInfo, treeListConsKernelInfo]]
  recInfos := [treeRecKernelInfo, treeListRecKernelInfo]
  familyTypes := [kernelConstVType08C% Tree,
    kernelConstVType08C% TreeList]
  ctorTypes := [
    [kernelConstVType08C% Tree.leaf, kernelConstVType08C% Tree.node,
      kernelConstVType08C% Tree.branch],
    [kernelConstVType08C% TreeList.nil,
      kernelConstVType08C% TreeList.cons]]
  recTypes := [kernelConstVType08C% Tree.rec,
    kernelConstVType08C% TreeList.rec]
  ruleRhs := [
    [treeLeafKernelRuleRhs, treeNodeKernelRuleRhs,
      treeBranchKernelRuleRhs],
    [treeListNilKernelRuleRhs, treeListConsKernelRuleRhs]]

#guard treeKernelBlockRow.agrees

/-- Complete kernel/Theory metadata row for the indexed mutual block. -/
def indexedTreeKernelBlockRow : MutualKernelBlockRow where
  source := indexedTreeDecl
  generation := indexedTreeGeneration
  inductInfos := [indexedTreeKernelInfo, indexedTreeListKernelInfo]
  ctorInfos := [
    [indexedTreeLeafKernelInfo, indexedTreeNodeKernelInfo],
    [indexedTreeListNilKernelInfo, indexedTreeListConsKernelInfo]]
  recInfos := [indexedTreeRecKernelInfo, indexedTreeListRecKernelInfo]
  familyTypes := [kernelConstVType08C% IndexedTree,
    kernelConstVType08C% IndexedTreeList]
  ctorTypes := [
    [kernelConstVType08C% IndexedTree.leaf,
      kernelConstVType08C% IndexedTree.node],
    [kernelConstVType08C% IndexedTreeList.nil,
      kernelConstVType08C% IndexedTreeList.cons]]
  recTypes := [kernelConstVType08C% IndexedTree.rec,
    kernelConstVType08C% IndexedTreeList.rec]
  ruleRhs := [
    [indexedTreeLeafKernelRuleRhs, indexedTreeNodeKernelRuleRhs],
    [indexedTreeListNilKernelRuleRhs, indexedTreeListConsKernelRuleRhs]]

#guard indexedTreeKernelBlockRow.agrees

def indexedTreeKernelType : InductiveType where
  name := indexedTreeKernelInfo.name
  type := indexedTreeKernelInfo.type
  ctors := [
    ⟨indexedTreeLeafKernelInfo.name, indexedTreeLeafKernelInfo.type⟩,
    ⟨indexedTreeNodeKernelInfo.name, indexedTreeNodeKernelInfo.type⟩]

def indexedTreeListKernelType : InductiveType where
  name := indexedTreeListKernelInfo.name
  type := indexedTreeListKernelInfo.type
  ctors := [
    ⟨indexedTreeListNilKernelInfo.name, indexedTreeListNilKernelInfo.type⟩,
    ⟨indexedTreeListConsKernelInfo.name, indexedTreeListConsKernelInfo.type⟩]

def indexedTreeKernelTypes : List InductiveType :=
  [indexedTreeKernelType, indexedTreeListKernelType]

def indexedTreeKernelContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_mutualIndexedTree natMap
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def indexedTreeExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 1 indexedTreeKernelTypes
    0 false indexedTreeKernelContext

theorem indexedTreeExecutionResult_isOk :
    indexedTreeExecutionResult.isOk = true := by
  native_decide

def indexedTreeProducedExecution :
    { execution // indexedTreeExecutionResult = .ok execution } :=
  match h : indexedTreeExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := indexedTreeExecutionResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeExecution := indexedTreeProducedExecution.val

def indexedTreeFamilyValidationResult :=
  FamilyValidationBlockRun.buildExecution 1 indexedTreeKernelTypes
    indexedTreeKernelContext

theorem indexedTreeFamilyValidationResult_isOk :
    indexedTreeFamilyValidationResult.isOk = true := by
  native_decide

def indexedTreeProducedFamilyValidation :
    { run // indexedTreeFamilyValidationResult = .ok run } :=
  match h : indexedTreeFamilyValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := indexedTreeFamilyValidationResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeFamilyValidation := indexedTreeProducedFamilyValidation.val

def indexedTreeConstructorContext : AddInductive.Context :=
  { indexedTreeExecution.validationContext with
    env := indexedTreeExecution.familyEnv }

def indexedTreeConstructorValidationResult :=
  ConstructorBlockValidationRun.buildExecution indexedTreeKernelTypes
    indexedTreeExecution.stats false indexedTreeConstructorContext

theorem indexedTreeConstructorValidationResult_isOk :
    indexedTreeConstructorValidationResult.isOk = true := by
  native_decide

def indexedTreeProducedConstructorValidation :
    { run // indexedTreeConstructorValidationResult = .ok run } :=
  match h : indexedTreeConstructorValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := indexedTreeConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeConstructorValidation :=
  indexedTreeProducedConstructorValidation.val

/-- Indexed recursive fields retain sibling ordinals after the ordinary Nat
binder, while nonrecursive fields occupy explicit `none` slots. -/
theorem indexedTreeConstructorTargets_exact :
    indexedTreeConstructorValidation.traces.targets =
      [
        [[none],
          [none, some { familyIdx := 1, binderDepth := 0 }]],
        [[],
          [none,
            some { familyIdx := 0, binderDepth := 0 },
            some { familyIdx := 1, binderDepth := 0 }]]
      ] := by
  native_decide

example : indexedTreeFamilyValidation.parameters.size = 1 :=
  indexedTreeFamilyValidation.params_size

example : indexedTreeFamilyValidation.result.stats.nindices = #[1, 1] := by
  native_decide

#guard AddInductive.levelStructEq indexedTreeFamilyValidation.resultLevel
  (.succ (.param `u))

/-! ## Phase-specific failures -/

def treeParameterMismatchType : InductiveType :=
  { treeListKernelType with
    type := .forallE `α (.sort .zero) (.sort (.succ (.param `u))) .default }

#guard match observeFamilyValidationBlock 1
    [treeKernelType, treeParameterMismatchType] treeKernelContext with
  | .error (.other message) =>
      message == "parameters of all inductive datatypes must match"
  | _ => false

def treeResultUniverseMismatchType : InductiveType :=
  { treeListKernelType with
    type := .forallE `α (.sort (.succ (.param `u))) (.sort .zero) .default }

#guard match observeFamilyValidationBlock 1
    [treeKernelType, treeResultUniverseMismatchType] treeKernelContext with
  | .error (.other message) =>
      message == "mutually inductive types must live in the same universe"
  | _ => false

/-- Reusing the original family statistics after swapping source owners
reaches constructor validation and fails at the first now-misowned return. -/
def treeReorderedConstructorResult :=
  checkConstructors #[treeListKernelType, treeKernelType]
    treeExecution.stats false treeConstructorContext

#guard match treeReorderedConstructorResult with
  | .error (.other message) =>
      message ==
        "invalid return type for 'Lean4Lean.MutualInductiveFixtures.TreeList.nil'"
  | _ => false

def treeReorderedView : VInductDecl :=
  { treeDecl with types := [treeListType, treeType] }

/- Raw/view normalization rejects family reordering before semantic evidence
can be attached to the dependent candidate list. -/
#guard (normalization? treeDecl treeReorderedView).isNone

/-! The host elaborator diagnostics independently pin the corresponding
family-validation phases in Lean itself. -/

namespace KernelPhases

universe v

/--
error: Invalid mutually inductive types: Parameter `α` has type
  Prop
of sort `Type` but is expected to have type
  Type v
of sort `Type (v + 1)`
-/
#guard_msgs in
mutual
inductive ParamA (α : Type v) : Type v
inductive ParamB (α : Prop) : Type v
end

/--
error: Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type v

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
-/
#guard_msgs in
mutual
inductive UniverseA (α : Type v) : Type v
inductive UniverseB (α : Type v) : Prop
end

end KernelPhases

/-! ## Tree/TreeList Theory semantics -/

def treeBlockEnv : VEnv :=
  (VEnv.empty.stageInductiveTypes treeDecl.types).get!

theorem treeStage :
    VEnv.empty.stageInductiveTypes treeDecl.types = some treeBlockEnv := by
  rfl

theorem treeFamilyTypeWF (type : VInductiveType)
    (h : type = treeType ∨ type = treeListType) :
    type.type.WF VEnv.empty type.uvars [] := by
  rcases h with rfl | rfl <;>
    refine ⟨.sort (.imax (.succ (.succ (.param 0)))
      (.succ (.succ (.param 0)))), VEnv.HasType.forallE ?_ ?_⟩ <;>
    exact VEnv.HasType.sort (by decide)

theorem treeCtorWF (ctor : VConstVal)
    (h : ctor ∈ treeType.ctors ∨ ctor ∈ treeListType.ctors) :
    ctor.type.WF treeBlockEnv 1 [] := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := by rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := by rfl
  rcases h with h | h
  · simp [treeType] at h
    rcases h with (rfl | rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
  · simp [treeListType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩

theorem treeNormalizationBlockWF :
    (Normalization.identity treeDecl).BlockWF VEnv.empty treeBlockEnv := by
  refine ⟨treeStage, ?_⟩
  change List.Forall₂ _ [treeType, treeListType] [treeType, treeListType]
  apply List.Forall₂.cons
  · refine ⟨?_, ?_⟩
    · exact VEnv.IsDefEqU.refl (treeFamilyTypeWF treeType (.inl rfl))
    · apply List.Forall₂.rfl
      intro ctor h
      exact VEnv.IsDefEqU.refl (treeCtorWF ctor (.inl h))
  · apply List.Forall₂.cons
    · refine ⟨?_, ?_⟩
      · exact VEnv.IsDefEqU.refl (treeFamilyTypeWF treeListType (.inr rfl))
      · apply List.Forall₂.rfl
        intro ctor h
        exact VEnv.IsDefEqU.refl (treeCtorWF ctor (.inr h))
    · exact .nil

theorem treeLeafSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[0]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).fields =
      [.bvar 0] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).recursiveAt =
      [none] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).resultIndices =
      [] by rfl]
  exact ⟨⟨⟨.succ (.param 0), .bvar .zero,
    .inr (VLevel.le_refl _)⟩, trivial⟩, rfl⟩

theorem treeNodeSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[1]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).fields =
      [.app (.const ``TreeList [.param 0]) (.bvar 0)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).recursiveAt =
      [some ({
        fieldIndex := 0
        binders := []
        targetType := 1
        indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).resultIndices =
      [] by rfl]
  exact ⟨⟨⟨rfl, trivial, rfl⟩, trivial⟩, rfl⟩

theorem treeBranchSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[2]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).fields =
      [.forallE (.bvar 0)
        (.app (.const ``TreeList [.param 0]) (.bvar 1))] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).recursiveAt =
      [some ({
        fieldIndex := 0
        binders := [.bvar 0]
        targetType := 1
        indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨rfl, ⟨⟨⟨.succ (.param 0), .bvar .zero⟩, trivial⟩, rfl⟩⟩,
      trivial⟩,
    rfl⟩

theorem treeListNilSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeListType.ctors[0]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).fields =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).recursiveAt =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).resultIndices =
      [] by rfl]
  exact ⟨trivial, rfl⟩

theorem treeListConsSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeListType.ctors[1]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).fields =
      [.app (.const ``Tree [.param 0]) (.bvar 0),
        .app (.const ``TreeList [.param 0]) (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).recursiveAt =
      [some ({
          fieldIndex := 0
          binders := []
          targetType := 0
          indices := [] } : RecArg),
        some ({
          fieldIndex := 1
          binders := []
          targetType := 1
          indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨rfl, trivial, rfl⟩,
      ⟨⟨rfl, trivial, rfl⟩, trivial⟩⟩,
    rfl⟩

theorem treeCheckedBlockWF :
    treeChecked.WF VEnv.empty (.succ (.param 0)) := by
  have hparams : treeChecked.params =
      [.sort (.succ (.param 0))] := rfl
  have hindices : treeChecked.families.indices = [[], []] := rfl
  have hlevels : treeChecked.families.resultLevels =
      [.succ (.param 0), .succ (.param 0)] := rfl
  have hconstructors : treeChecked.families.constructors =
      [treeType.ctors.map (CheckedCtor.ofBlock treeDecl),
        treeListType.ctors.map (CheckedCtor.ofBlock treeDecl)] := rfl
  rw [CheckedBlock.WF, hindices, hlevels, hconstructors]
  rw [hparams]
  simp only [checkedFamilyListsWF]
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · intro ctor h
    simp [treeType] at h
    rcases h with rfl | rfl | rfl
    · exact treeLeafSemantic
    · exact treeNodeSemantic
    · exact treeBranchSemantic
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · refine ⟨?_, trivial⟩
    intro ctor h
    simp [treeListType] at h
    rcases h with rfl | rfl
    · exact treeListNilSemantic
    · exact treeListConsSemantic

def treeNormalizedBlock : NormalizedCheckedBlock treeDecl where
  normalization := Normalization.identity treeDecl
  checked := treeChecked
  checked_eq := (Option.some_get (x := treeDecl.checkedBlock?)
    (by decide)).symm

def treeValidatedBlock : ValidatedBlock treeDecl where
  block := treeNormalizedBlock
  resultLevel := .succ (.param 0)

/-- Exact validation-only semantic package for the unindexed mutual block. -/
def treeValidationCertificate : ValidationCertificate treeDecl VEnv.empty where
  validated := treeValidatedBlock
  blockEnv := treeBlockEnv
  wf := ⟨treeNormalizationBlockWF, treeCheckedBlockWF⟩

/-! ## IndexedTree/IndexedTreeList Theory semantics -/

def indexedTreeBlockEnv : VEnv :=
  (natFinalEnv.stageInductiveTypes indexedTreeDecl.types).get!

theorem indexedTreeStage :
    natFinalEnv.stageInductiveTypes indexedTreeDecl.types =
      some indexedTreeBlockEnv := by
  rfl

theorem indexedTreeFamilyTypeWF (type : VInductiveType)
    (h : type = indexedTreeType ∨ type = indexedTreeListType) :
    type.type.WF natFinalEnv type.uvars [] := by
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  rcases h with rfl | rfl <;>
    exact ⟨_, by type_tac⟩

theorem indexedTreeCtorWF (ctor : VConstVal)
    (h : ctor ∈ indexedTreeType.ctors ∨
      ctor ∈ indexedTreeListType.ctors) :
    ctor.type.WF indexedTreeBlockEnv 1 [] := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := by rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := by rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := by rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := by rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := by rfl
  rcases h with h | h
  · simp [indexedTreeType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
  · simp [indexedTreeListType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩

theorem indexedTreeNormalizationBlockWF :
    (Normalization.identity indexedTreeDecl).BlockWF
      natFinalEnv indexedTreeBlockEnv := by
  refine ⟨indexedTreeStage, ?_⟩
  change List.Forall₂ _ [indexedTreeType, indexedTreeListType]
    [indexedTreeType, indexedTreeListType]
  apply List.Forall₂.cons
  · refine ⟨?_, ?_⟩
    · exact VEnv.IsDefEqU.refl
        (indexedTreeFamilyTypeWF indexedTreeType (.inl rfl))
    · apply List.Forall₂.rfl
      intro ctor h
      exact VEnv.IsDefEqU.refl (indexedTreeCtorWF ctor (.inl h))
  · apply List.Forall₂.cons
    · refine ⟨?_, ?_⟩
      · exact VEnv.IsDefEqU.refl
          (indexedTreeFamilyTypeWF indexedTreeListType (.inr rfl))
      · apply List.Forall₂.rfl
        intro ctor h
        exact VEnv.IsDefEqU.refl (indexedTreeCtorWF ctor (.inr h))
    · exact .nil

theorem indexedTreeLeafSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).fields = [.bvar 0] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).recursiveAt = [none] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).resultIndices = [.const ``Nat.zero []] by rfl]
  constructor
  · exact ⟨⟨.succ (.param 0), .bvar .zero,
      .inr (VLevel.le_refl _)⟩, trivial⟩
  · have hNat : natFinalEnv.constants ``Nat =
        some InductiveFixtures.natType.toVConstant := rfl
    have hZero : natFinalEnv.constants ``Nat.zero =
        some InductiveFixtures.natType.ctors[0].toVConstant := rfl
    exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
      (by type_tac), rfl⟩

theorem indexedTreeNodeSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).fields =
        [.const ``Nat [],
          (VExpr.const ``IndexedTreeList [.param 0]).app (.bvar 1)
            |>.app (.bvar 0)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).recursiveAt =
        [none, some ({
          fieldIndex := 1
          binders := []
          targetType := 1
          indices := [.bvar 0] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).resultIndices =
        [(VExpr.const ``Nat.succ []).app (.bvar 1)] by rfl]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : natFinalEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨⟨.succ .zero, (by type_tac),
        .inr (VLevel.succ_le_succ VLevel.zero_le)⟩, ?_⟩
    exact ⟨⟨rfl, trivial, ⟨.const ``Nat [],
      .sort (.succ (.param 0)), rfl, (by type_tac), rfl⟩⟩, trivial⟩
  · exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
      (by type_tac), rfl⟩

theorem indexedTreeListNilSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).fields = [] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).recursiveAt = [] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).resultIndices =
        [.const ``Nat.zero []] by rfl]
  refine ⟨trivial, ?_⟩
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : natFinalEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
    (by type_tac), rfl⟩

theorem indexedTreeListConsSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).fields =
        [.const ``Nat [],
          (VExpr.const ``IndexedTree [.param 0]).app (.bvar 1)
            |>.app (.bvar 0),
          (VExpr.const ``IndexedTreeList [.param 0]).app (.bvar 2)
            |>.app (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).recursiveAt =
        [none,
          some ({
            fieldIndex := 1
            binders := []
            targetType := 0
            indices := [.bvar 0] } : RecArg),
          some ({
            fieldIndex := 2
            binders := []
            targetType := 1
            indices := [.bvar 1] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).resultIndices =
        [(VExpr.const ``Nat.succ []).app (.bvar 2)] by rfl]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : natFinalEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨⟨.succ .zero, (by type_tac),
        .inr (VLevel.succ_le_succ VLevel.zero_le)⟩, ?_⟩
    refine ⟨⟨rfl, trivial, ⟨.const ``Nat [],
      .sort (.succ (.param 0)), rfl, (by type_tac), rfl⟩⟩, ?_⟩
    exact ⟨⟨rfl, trivial, ⟨.const ``Nat [],
      .sort (.succ (.param 0)), rfl, (by type_tac), rfl⟩⟩, trivial⟩
  · exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
      (by type_tac), rfl⟩

theorem indexedTreeCheckedBlockWF :
    indexedTreeChecked.WF natFinalEnv (.succ (.param 0)) := by
  have hparams : indexedTreeChecked.params =
      [.sort (.succ (.param 0))] := rfl
  have hindices : indexedTreeChecked.families.indices =
      [[.const ``Nat []], [.const ``Nat []]] := rfl
  have hlevels : indexedTreeChecked.families.resultLevels =
      [.succ (.param 0), .succ (.param 0)] := rfl
  have hconstructors : indexedTreeChecked.families.constructors =
      [indexedTreeType.ctors.map (CheckedCtor.ofBlock indexedTreeDecl),
        indexedTreeListType.ctors.map
          (CheckedCtor.ofBlock indexedTreeDecl)] := rfl
  rw [CheckedBlock.WF, hindices, hlevels, hconstructors]
  rw [hparams]
  simp only [checkedFamilyListsWF]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩,
      ⟨⟨_, (by type_tac)⟩, trivial⟩⟩
  · intro ctor h
    simp [indexedTreeType] at h
    rcases h with rfl | rfl
    · exact indexedTreeLeafSemantic
    · exact indexedTreeNodeSemantic
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩,
      ⟨⟨_, (by type_tac)⟩, trivial⟩⟩
  · refine ⟨?_, trivial⟩
    intro ctor h
    simp [indexedTreeListType] at h
    rcases h with rfl | rfl
    · exact indexedTreeListNilSemantic
    · exact indexedTreeListConsSemantic

def indexedTreeNormalizedBlock : NormalizedCheckedBlock indexedTreeDecl where
  normalization := Normalization.identity indexedTreeDecl
  checked := indexedTreeChecked
  checked_eq := (Option.some_get (x := indexedTreeDecl.checkedBlock?)
    (by decide)).symm

def indexedTreeValidatedBlock : ValidatedBlock indexedTreeDecl where
  block := indexedTreeNormalizedBlock
  resultLevel := .succ (.param 0)

/-- Exact validation-only semantic package for the indexed mutual block. -/
def indexedTreeValidationCertificate :
    ValidationCertificate indexedTreeDecl natFinalEnv where
  validated := indexedTreeValidatedBlock
  blockEnv := indexedTreeBlockEnv
  wf := ⟨indexedTreeNormalizationBlockWF, indexedTreeCheckedBlockWF⟩

/-! ## Trust-boundary manifests -/

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeCheckedBlockWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms treeCheckedBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCheckedBlockWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeCheckedBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeNormalizationBlockWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeNormalizationBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeNormalizationBlockWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeNormalizationBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeValidationCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeValidationCertificate

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeValidationCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeValidationCertificate

end Lean4Lean.MutualInductiveReplayFixtures
