import Lean4Lean.Verify.Environment.SingletonParityMatrix

/-!
# L4L-07 environment replay inventory

This module is the sole public environment-facing inventory for singleton
parity.  A row packages the actual implementation map, the Theory input and
output environments, input alignment/order, and the proof-carrying inductive
transaction.  Consequently every row exposes final alignment and orderedness;
mere Theory generation is not enough to inhabit this structure.
-/

namespace Lean4Lean.InductiveReplayFixtures

open Lean
open Lean4Lean.InductiveFixtures

structure SingletonReplayArtifact where
  label : Name
  source : VInductDecl
  inputMap : ConstMap
  inputEnv : VEnv
  outputMap : ConstMap
  outputEnv : VEnv
  inputOrdered : inputEnv.Ordered
  transaction : AddInduct inputMap inputEnv source outputMap outputEnv
  aligned : Aligned .safe outputMap outputEnv

namespace SingletonReplayArtifact

theorem outputAligned (artifact : SingletonReplayArtifact) :
    Aligned .safe artifact.outputMap artifact.outputEnv := artifact.aligned

theorem outputOrdered (artifact : SingletonReplayArtifact) :
    artifact.outputEnv.Ordered := by
  obtain ⟨generation, generation_wf, transaction⟩ :=
    artifact.transaction.to_addInduct
  exact VEnv.addInductGeneration_WF artifact.inputOrdered generation_wf
    transaction

end SingletonReplayArtifact

/-! ## Replays already established by the completed singleton pipeline -/

def natReplay07 : SingletonReplayArtifact where
  label := ``Nat
  source := natDecl
  inputMap := {}
  inputEnv := .empty
  outputMap := natMap
  outputEnv := natFinalEnv
  inputOrdered := .empty
  transaction := nat_addInduct
  aligned := nat_aligned

def eqReplay07 : SingletonReplayArtifact where
  label := ``Eq
  source := eqDecl
  inputMap := {}
  inputEnv := .empty
  outputMap := eqMap
  outputEnv := eqFinalEnv
  inputOrdered := .empty
  transaction := eq_addInduct
  aligned := eq_aligned

def accReplay07 : SingletonReplayArtifact where
  label := ``Acc
  source := accDecl
  inputMap := {}
  inputEnv := .empty
  outputMap := accMap
  outputEnv := accFinalEnv
  inputOrdered := .empty
  transaction := acc_addInduct
  aligned := acc_aligned

def aliasFormerReplay07 : SingletonReplayArtifact where
  label := ``AliasFormer
  source := aliasFormerRawDecl
  inputMap := typeFamilyAliasMap
  inputEnv := typeFamilyAliasEnv
  outputMap := aliasFormerMap
  outputEnv := aliasFormerFinalEnv
  inputOrdered := typeFamilyAliasEnv_ordered
  transaction := aliasFormer_addInduct_checked
  aligned := aliasFormer_aligned_checked

def aliasRecReplay07 : SingletonReplayArtifact where
  label := ``AliasRec
  source := aliasRecRawDecl
  inputMap := recAliasMap
  inputEnv := recAliasEnv
  outputMap := aliasRecMap
  outputEnv := aliasRecFinalEnv
  inputOrdered := recAliasEnv_ordered
  transaction := aliasRec_addInduct_checked
  aligned := aliasRec_aligned_checked

def normalizationMatrixReplay07 : SingletonReplayArtifact where
  label := ``NormalizationMatrix
  source := normalizationMatrixRawDecl
  inputMap := matrixAliasMap
  inputEnv := normalizationMatrixAliasEnv
  outputMap := normalizationMatrixMap
  outputEnv := normalizationMatrixFinalEnv
  inputOrdered := normalizationMatrixAliasEnv_ordered
  transaction := normalizationMatrix_addInduct
  aligned := normalizationMatrix_aligned

noncomputable def annotatedPiReplay07 : SingletonReplayArtifact where
  label := ``AnnotatedPi
  source := annotatedPiRawDecl
  inputMap := _
  inputEnv := outParamEnv
  outputMap := _
  outputEnv := annotatedPiFinalEnv
  inputOrdered := outParamEnv_ordered
  transaction := annotatedPi_addInduct_checked
  aligned := annotatedPi_aligned_checked

def annotatedParamReplay07 : SingletonReplayArtifact where
  label := ``AnnotatedParam
  source := annotatedParamRawDecl
  inputMap := _
  inputEnv := outParamEnv
  outputMap := _
  outputEnv := annotatedParamFinalEnv
  inputOrdered := outParamEnv_ordered
  transaction := annotatedParam_addInduct_checked
  aligned := annotatedParam_aligned_checked

/-- The pre-L4L-07 replay subset, now represented uniformly.  The fixed
standard-family rows added below extend this same inventory instead of
creating a second public replay path. -/
noncomputable def singletonReplaySubset : List SingletonReplayArtifact :=
  [natReplay07, eqReplay07, accReplay07, aliasFormerReplay07, aliasRecReplay07,
    normalizationMatrixReplay07, annotatedPiReplay07,
    annotatedParamReplay07]

example : singletonReplaySubset.map (·.label) =
    [``Nat, ``Eq, ``Acc, ``AliasFormer, ``AliasRec, ``NormalizationMatrix,
      ``AnnotatedPi, ``AnnotatedParam] := rfl

example : singletonReplaySubset.length = 8 := rfl

end Lean4Lean.InductiveReplayFixtures
