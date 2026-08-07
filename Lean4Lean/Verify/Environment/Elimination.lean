import Lean4Lean.Inductive.EliminationTrace
import Lean4Lean.Theory.Inductive

namespace Lean4Lean
open Lean hiding Environment Exception

namespace AddInductive

/-- Theory's presentation of the Boolean returned by the ordinary
large-eliminator checker. -/
def checkerElimMode : Bool → VInductDecl.ElimMode
  | false => .small
  | true => .large

/-- Lightweight alignment for an exact `getElimLevel` execution when the
normalization statistics are already pinned independently. This is useful for
the never-zero branch, which returns before inspecting any constructor. -/
structure CheckerElimLevelRun
    {source : VInductDecl} (generation : VInductDecl.GenerationChecked source)
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {context : Context}
    (execution : ElimLevelExecution stats indTypes context) : Type where
  sourceUvars_eq : source.uvars = context.lparams.length
  mode_eq : generation.elimination =
    checkerElimMode execution.large.result
  recUvars_eq : generation.recUvars =
    (getRecLevelParams execution.level context.lparams).length
  recLevels_eq :
    (getRecLevels execution.level stats.levels).mapM
      (VLevel.ofLevel (getRecLevelParams execution.level context.lparams)) =
        some generation.recLevels

namespace CheckerElimLevelRun

/-- Decide the complete mode and level-layout alignment from the retained
ordinary execution. -/
def build?
    {source : VInductDecl} (generation : VInductDecl.GenerationChecked source)
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {context : Context}
    (execution : ElimLevelExecution stats indTypes context) :
    Option (CheckerElimLevelRun generation execution) := do
  if huvars : source.uvars = context.lparams.length then
    if hmode : generation.elimination =
        checkerElimMode execution.large.result then
      if hrecUvars : generation.recUvars =
          (getRecLevelParams execution.level context.lparams).length then
        if hlevels :
            (getRecLevels execution.level stats.levels).mapM
              (VLevel.ofLevel
                (getRecLevelParams execution.level context.lparams)) =
              some generation.recLevels then
          some {
            sourceUvars_eq := huvars
            mode_eq := hmode
            recUvars_eq := hrecUvars
            recLevels_eq := hlevels }
        else none
      else none
    else none
  else none

theorem large_result_iff
    (run : CheckerElimLevelRun generation execution) :
    execution.large.result = true ↔
      generation.elimination = VInductDecl.ElimMode.large := by
  cases hresult : execution.large.result with
  | false =>
      have hmode : generation.elimination = VInductDecl.ElimMode.small := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]
  | true =>
      have hmode : generation.elimination = VInductDecl.ElimMode.large := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]

theorem small_result_iff
    (run : CheckerElimLevelRun generation execution) :
    execution.large.result = false ↔
      generation.elimination = VInductDecl.ElimMode.small := by
  cases hresult : execution.large.result with
  | false =>
      have hmode : generation.elimination = VInductDecl.ElimMode.small := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]
  | true =>
      have hmode : generation.elimination = VInductDecl.ElimMode.large := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]

end CheckerElimLevelRun

/-- Executable alignment between an exact ordinary elimination run and the
mode/universe layout consumed by one Theory generation artifact.

The operational side owns the real `ensureType` observations, selected fresh
level name, recursive-call levels, and stored metadata parameter order.  The
equations below are checked data, so a Theory generation whose mode or
numeric universe layout disagrees with that run cannot inhabit this record. -/
structure CheckerEliminationRun
    {source : VInductDecl} (generation : VInductDecl.GenerationChecked source)
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool} {candidateContext : Context}
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : Type where
  nparams_eq : nparams = source.nparams
  sourceUvars_eq : source.uvars =
    execution.normalization.validationContext.lparams.length
  mode_eq : generation.elimination =
    checkerElimMode execution.elimination.large.result
  recUvars_eq : generation.recUvars = execution.recLevelParams.length
  recLevels_eq : execution.recLevels.mapM
    (VLevel.ofLevel execution.recLevelParams) = some generation.recLevels

namespace CheckerEliminationRun

/-- Build the alignment by deciding every equality rather than asking a
fixture or caller to supply a mode or level permutation. -/
def build?
    {source : VInductDecl} (generation : VInductDecl.GenerationChecked source)
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool} {candidateContext : Context}
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) :
    Option (CheckerEliminationRun generation execution) := do
  if hparams : nparams = source.nparams then
    if huvars : source.uvars =
        execution.normalization.validationContext.lparams.length then
      if hmode : generation.elimination =
          checkerElimMode execution.elimination.large.result then
        if hrecUvars : generation.recUvars =
            execution.recLevelParams.length then
          if hlevels : execution.recLevels.mapM
              (VLevel.ofLevel execution.recLevelParams) =
                some generation.recLevels then
            some {
              nparams_eq := hparams
              sourceUvars_eq := huvars
              mode_eq := hmode
              recUvars_eq := hrecUvars
              recLevels_eq := hlevels }
          else none
        else none
      else none
    else none
  else none

theorem large_result_iff
    (run : CheckerEliminationRun generation execution) :
    execution.elimination.large.result = true ↔
      generation.elimination = VInductDecl.ElimMode.large := by
  cases hresult : execution.elimination.large.result with
  | false =>
      have hmode : generation.elimination = VInductDecl.ElimMode.small := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]
  | true =>
      have hmode : generation.elimination = VInductDecl.ElimMode.large := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]

theorem small_result_iff
    (run : CheckerEliminationRun generation execution) :
    execution.elimination.large.result = false ↔
      generation.elimination = VInductDecl.ElimMode.small := by
  cases hresult : execution.elimination.large.result with
  | false =>
      have hmode : generation.elimination = VInductDecl.ElimMode.small := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]
  | true =>
      have hmode : generation.elimination = VInductDecl.ElimMode.large := by
        simpa [checkerElimMode, hresult] using run.mode_eq
      simp [hmode]

end CheckerEliminationRun

/--
info: 'Lean4Lean.AddInductive.CheckerEliminationRun.large_result_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CheckerEliminationRun.large_result_iff

/--
info: 'Lean4Lean.AddInductive.CheckerElimLevelRun.large_result_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CheckerElimLevelRun.large_result_iff

end AddInductive
end Lean4Lean
