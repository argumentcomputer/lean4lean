import Lean4Lean.Theory.SingletonParity
import Lean4Lean.Verify.Environment.ConstructorValidityMatrix
import Lean4Lean.Verify.Environment.EliminationFixturesEqNat
import Lean4Lean.Verify.Environment.EliminationFixturesOrAnd
import Lean4Lean.Verify.Environment.EliminationFixturesEdges
import Lean4Lean.Verify.Environment.NormalizationMatrix

/-!
# L4L-07 complete singleton kernel matrix

The rows below join the single Theory artifact inventory to Lean's actual
`inductInfo`/`ctorInfo`/`recInfo` records.  The executable predicate compares
the retained raw types, names, parameter/index and field counts, universe
order, elimination/K metadata, recursor type, rule count, and every iota RHS.
It also reruns the ordinary normalization producer on the exact kernel source.
-/

namespace Lean4Lean.InductiveReplayFixtures

open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

/-! ## Exact conversion of stored kernel types -/

syntax "kernelConstVType%" ident : term

/-- Quote the stored `ConstantInfo.type` using that record's own universe
parameter order.  Unlike `vconst(type_of% ...)`, this observes the raw kernel
record directly. -/
elab_rules : term
  | `(kernelConstVType% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let info ← getConstInfo name
    let type ← Lean4Lean.Meta.expandExpr info.type
    let type ← Lean4Lean.Meta.ofExpr info.levelParams {} type
    return toExpr type

/-! ## Missing standard-library metadata rows -/

def boolInfo07 : ConstantInfo := kernelInductInfo% Bool
def boolFalseInfo07 : ConstantInfo := kernelCtorInfo% Bool.false
def boolTrueInfo07 : ConstantInfo := kernelCtorInfo% Bool.true
def boolRecInfo07 : ConstantInfo := kernelRecInfo% Bool.rec
def boolFalseRuleRhs07 : VExpr := kernelRecRuleRhs% Bool.rec 0
def boolTrueRuleRhs07 : VExpr := kernelRecRuleRhs% Bool.rec 1

def listInfo07 : ConstantInfo := kernelInductInfo% List
def listNilInfo07 : ConstantInfo := kernelCtorInfo% List.nil
def listConsInfo07 : ConstantInfo := kernelCtorInfo% List.cons
def listRecInfo07 : ConstantInfo := kernelRecInfo% List.rec
def listNilRuleRhs07 : VExpr := kernelRecRuleRhs% List.rec 0
def listConsRuleRhs07 : VExpr := kernelRecRuleRhs% List.rec 1

def optionInfo07 : ConstantInfo := kernelInductInfo% Option
def optionNoneInfo07 : ConstantInfo := kernelCtorInfo% Option.none
def optionSomeInfo07 : ConstantInfo := kernelCtorInfo% Option.some
def optionRecInfo07 : ConstantInfo := kernelRecInfo% Option.rec
def optionNoneRuleRhs07 : VExpr := kernelRecRuleRhs% Option.rec 0
def optionSomeRuleRhs07 : VExpr := kernelRecRuleRhs% Option.rec 1

def prodInfo07 : ConstantInfo := kernelInductInfo% Prod
def prodMkInfo07 : ConstantInfo := kernelCtorInfo% Prod.mk
def prodRecInfo07 : ConstantInfo := kernelRecInfo% Prod.rec
def prodRuleRhs07 : VExpr := kernelRecRuleRhs% Prod.rec 0

def heqInfo07 : ConstantInfo := kernelInductInfo% HEq
def heqReflInfo07 : ConstantInfo := kernelCtorInfo% HEq.refl
def heqRecInfo07 : ConstantInfo := kernelRecInfo% HEq.rec
def heqRuleRhs07 : VExpr := kernelRecRuleRhs% HEq.rec 0

def finInfo07 : ConstantInfo := kernelInductInfo% Fin
def finMkInfo07 : ConstantInfo := kernelCtorInfo% Fin.mk
def finRecInfo07 : ConstantInfo := kernelRecInfo% Fin.rec
def finRuleRhs07 : VExpr := kernelRecRuleRhs% Fin.rec 0

def vectorInfo07 : ConstantInfo := kernelInductInfo% Vector
def vectorMkInfo07 : ConstantInfo := kernelCtorInfo% Vector.mk
def vectorRecInfo07 : ConstantInfo := kernelRecInfo% Vector.rec
def vectorRuleRhs07 : VExpr := kernelRecRuleRhs% Vector.rec 0

/-! ## Producer dependency contexts -/

def finDependencyMap07 : ConstMap :=
  ((((({} : ConstMap).insert ``Nat natInfo).insert ``LT
    (kernelInductInfo% LT)).insert ``LT.mk
      (kernelCtorInfo% LT.mk)).insert ``LT.lt
        (.defnInfo (kernelDefVal% LT.lt))).insert ``instLTNat
          (.defnInfo (kernelDefVal% instLTNat))

def vectorDependencyMap07 : ConstMap :=
  (((({} : ConstMap).insert ``Nat natInfo).insert ``Eq eqInfo).insert ``Array
    (kernelInductInfo% Array)).insert ``Array.size
      (.defnInfo (kernelDefVal% Array.size))

/-! ## Integrated row type -/

structure SingletonKernelRow where
  artifact : SingletonParityArtifact
  inductInfo : ConstantInfo
  ctorInfos : List ConstantInfo
  recInfo : ConstantInfo
  familyType : VExpr
  ctorTypes : List VExpr
  recType : VExpr
  ruleRhs : List VExpr
  dependencies : ConstMap := {}

namespace SingletonKernelRow

def constructor? : ConstantInfo → Option Constructor
  | .ctorInfo ctor => some { name := ctor.name, type := ctor.type }
  | _ => none

def kernelType? (row : SingletonKernelRow) : Option InductiveType := do
  let .inductInfo induct := row.inductInfo | none
  let ctors ← row.ctorInfos.mapM constructor?
  some { name := induct.name, type := induct.type, ctors := ctors }

def context (row : SingletonKernelRow) : AddInductive.Context where
  env := Kernel.Environment.ofConstants
    (.str `_singletonParity row.artifact.label.toString) row.dependencies
  lparams := row.inductInfo.levelParams
  safety := .safe
  allowPrimitive := row.artifact.typeName == ``Nat ||
    row.artifact.typeName == ``Bool

def producerAccepted (row : SingletonKernelRow) : Bool :=
  match row.kernelType? with
  | none => false
  | some kernelType =>
      match AddInductive.buildNormalizationCandidate
          row.artifact.source.nparams [kernelType] 0 false row.context with
      | .ok _ => true
      | .error _ => false

def ctorMatches (row : SingletonKernelRow) (info : ConstantInfo)
    (raw : VConstVal) (rawType : VExpr) : Bool :=
  match info with
  | .ctorInfo ctor =>
      ctor.name == raw.name &&
        ctor.levelParams.length == row.artifact.source.uvars &&
        ctor.induct == row.artifact.typeName &&
        ctor.numParams == row.artifact.source.nparams &&
        ctor.numFields == (VInductDecl.ctorFields
          (VExpr.dropN row.artifact.source.nparams raw.type)).length &&
        !ctor.isUnsafe && rawType == raw.type
  | _ => false

def constructorsMatch (row : SingletonKernelRow) :
    List ConstantInfo → List VConstVal → List VExpr → Bool
  | [], [], [] => true
  | info :: infos, raw :: raws, rawType :: rawTypes =>
      row.ctorMatches info raw rawType &&
        row.constructorsMatch infos raws rawTypes
  | _, _, _ => false

def recursorMatches (row : SingletonKernelRow) : Bool :=
  match row.recInfo with
  | .recInfo rec =>
      rec.name == .str row.artifact.typeName "rec" &&
        rec.levelParams.length == row.artifact.generation.recUvars &&
        rec.all == [row.artifact.typeName] &&
        rec.numParams == row.artifact.source.nparams &&
        rec.numIndices ==
          row.artifact.generation.block.checked.indices.length &&
        rec.numMotives == 1 &&
        rec.numMinors ==
          row.artifact.generation.block.sourceType.ctors.length &&
        rec.k == row.artifact.generation.kTarget &&
        !rec.isUnsafe &&
        rec.rules.map (fun rule => (rule.ctor, rule.nfields)) ==
          row.artifact.generation.block.sourceType.ctors.map (fun ctor =>
            (ctor.name, (VInductDecl.ctorFields
              (VExpr.dropN row.artifact.source.nparams ctor.type)).length)) &&
        row.recType == row.artifact.generation.recursor.type &&
        row.ruleRhs ==
          row.artifact.generation.generatedRules.map (·.rhs)
  | _ => false

/-- Exact fixed-row agreement after binder-name erasure.  Universe order is
still observed: `familyType`/`ctorTypes`/`recType` were converted with the
stored metadata parameter lists, not with elaborator-inferred ordering. -/
def agrees (row : SingletonKernelRow) : Bool :=
  match row.inductInfo with
  | .inductInfo induct =>
      induct.name == row.artifact.typeName &&
        induct.levelParams.length == row.artifact.source.uvars &&
        induct.numParams == row.artifact.source.nparams &&
        induct.numIndices ==
          row.artifact.generation.block.checked.indices.length &&
        induct.all == [row.artifact.typeName] &&
        induct.ctors == row.artifact.constructorNames &&
        induct.numNested == 0 && !induct.isUnsafe &&
        row.familyType == row.artifact.generation.block.sourceType.type &&
        row.constructorsMatch row.ctorInfos
          row.artifact.generation.block.sourceType.ctors row.ctorTypes &&
        row.recursorMatches
  | _ => false

end SingletonKernelRow

/-! ## The fixed rows -/

def singletonKernelRows : List SingletonKernelRow :=
  [ { artifact := singletonPositiveArtifacts[0]
      inductInfo := natInfo
      ctorInfos := [natZeroInfo, natSuccInfo]
      recInfo := natRecInfo
      familyType := kernelConstVType% Nat
      ctorTypes := [kernelConstVType% Nat.zero, kernelConstVType% Nat.succ]
      recType := kernelConstVType% Nat.rec
      ruleRhs := [natZeroKernelRuleRhs, natSuccKernelRuleRhs] },
    { artifact := singletonPositiveArtifacts[1]
      inductInfo := boolInfo07
      ctorInfos := [boolFalseInfo07, boolTrueInfo07]
      recInfo := boolRecInfo07
      familyType := kernelConstVType% Bool
      ctorTypes := [kernelConstVType% Bool.false, kernelConstVType% Bool.true]
      recType := kernelConstVType% Bool.rec
      ruleRhs := [boolFalseRuleRhs07, boolTrueRuleRhs07] },
    { artifact := singletonPositiveArtifacts[2]
      inductInfo := listInfo07
      ctorInfos := [listNilInfo07, listConsInfo07]
      recInfo := listRecInfo07
      familyType := kernelConstVType% List
      ctorTypes := [kernelConstVType% List.nil, kernelConstVType% List.cons]
      recType := kernelConstVType% List.rec
      ruleRhs := [listNilRuleRhs07, listConsRuleRhs07] },
    { artifact := singletonPositiveArtifacts[3]
      inductInfo := optionInfo07
      ctorInfos := [optionNoneInfo07, optionSomeInfo07]
      recInfo := optionRecInfo07
      familyType := kernelConstVType% Option
      ctorTypes := [kernelConstVType% Option.none,
        kernelConstVType% Option.some]
      recType := kernelConstVType% Option.rec
      ruleRhs := [optionNoneRuleRhs07, optionSomeRuleRhs07] },
    { artifact := singletonPositiveArtifacts[4]
      inductInfo := prodInfo07
      ctorInfos := [prodMkInfo07]
      recInfo := prodRecInfo07
      familyType := kernelConstVType% Prod
      ctorTypes := [kernelConstVType% Prod.mk]
      recType := kernelConstVType% Prod.rec
      ruleRhs := [prodRuleRhs07] },
    { artifact := singletonPositiveArtifacts[5]
      inductInfo := punitInfo06C
      ctorInfos := [punitCtorInfo06C]
      recInfo := punitRecInfo06C
      familyType := kernelConstVType% PUnit
      ctorTypes := [kernelConstVType% PUnit.unit]
      recType := kernelConstVType% PUnit.rec
      ruleRhs := [punitRuleRhs06C] },
    { artifact := singletonPositiveArtifacts[6]
      inductInfo := emptyInfo06C
      ctorInfos := []
      recInfo := emptyRecInfo06C
      familyType := kernelConstVType% Empty
      ctorTypes := []
      recType := kernelConstVType% Empty.rec
      ruleRhs := [] },
    { artifact := singletonPositiveArtifacts[7]
      inductInfo := orInfo06
      ctorInfos := [orInlInfo06, orInrInfo06]
      recInfo := orRecInfo06
      familyType := kernelConstVType% Or
      ctorTypes := [kernelConstVType% Or.inl, kernelConstVType% Or.inr]
      recType := kernelConstVType% Or.rec
      ruleRhs := [orInlKernelRuleRhs06, orInrKernelRuleRhs06] },
    { artifact := singletonPositiveArtifacts[8]
      inductInfo := andInfo06
      ctorInfos := [andIntroInfo06]
      recInfo := andRecInfo06
      familyType := kernelConstVType% And
      ctorTypes := [kernelConstVType% And.intro]
      recType := kernelConstVType% And.rec
      ruleRhs := [andKernelRuleRhs06] },
    { artifact := singletonPositiveArtifacts[9]
      inductInfo := eqInfo
      ctorInfos := [eqReflInfo]
      recInfo := eqRecInfo
      familyType := kernelConstVType% Eq
      ctorTypes := [kernelConstVType% Eq.refl]
      recType := kernelConstVType% Eq.rec
      ruleRhs := [eqReflKernelRuleRhs] },
    { artifact := singletonPositiveArtifacts[10]
      inductInfo := heqInfo07
      ctorInfos := [heqReflInfo07]
      recInfo := heqRecInfo07
      familyType := kernelConstVType% HEq
      ctorTypes := [kernelConstVType% HEq.refl]
      recType := kernelConstVType% HEq.rec
      ruleRhs := [heqRuleRhs07] },
    { artifact := singletonPositiveArtifacts[11]
      inductInfo := finInfo07
      ctorInfos := [finMkInfo07]
      recInfo := finRecInfo07
      familyType := kernelConstVType% Fin
      ctorTypes := [kernelConstVType% Fin.mk]
      recType := kernelConstVType% Fin.rec
      ruleRhs := [finRuleRhs07]
      dependencies := finDependencyMap07 },
    { artifact := singletonPositiveArtifacts[12]
      inductInfo := vectorInfo07
      ctorInfos := [vectorMkInfo07]
      recInfo := vectorRecInfo07
      familyType := kernelConstVType% Vector
      ctorTypes := [kernelConstVType% Vector.mk]
      recType := kernelConstVType% Vector.rec
      ruleRhs := [vectorRuleRhs07]
      dependencies := vectorDependencyMap07 },
    { artifact := singletonPositiveArtifacts[13]
      inductInfo := accInfo
      ctorInfos := [accIntroInfo]
      recInfo := accRecInfo
      familyType := kernelConstVType% Acc
      ctorTypes := [kernelConstVType% Acc.intro]
      recType := kernelConstVType% Acc.rec
      ruleRhs := [accKernelRuleRhs] } ]

example : singletonKernelRows.map (·.artifact.label) =
    singletonPositiveArtifacts.map (·.label) := rfl

#guard singletonKernelRows.all (·.agrees)
#guard singletonKernelRows.all (·.producerAccepted)

end Lean4Lean.InductiveReplayFixtures
