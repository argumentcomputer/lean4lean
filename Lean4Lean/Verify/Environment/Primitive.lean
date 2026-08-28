import Lean4Lean.Verify.Environment.Primitive.Recursion

/-!
This module contains the front-end-specific trust boundary for declaration verification.
The checker, extension, and declaration modules introduce no additional `sorry`-backed
assumptions. The imported type-checker and theory layers retain their own explicit
verification gaps.
-/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

variable {v : DefinitionVal} {ci' : VDefVal}

/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer.

The recognizer's `isDefEq` calls are about `v.value` and `v.type`, so lifting them into the
model requires their translations. `addDefinition` establishes those before calling the
recognizer -- that is what the reordering there is for -- and they arrive here as `hvalue` and
`htype`, describing the very `ci'` that the caller goes on to add. -/
theorem checkDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal)
    (hu : v.levelParams.length = ci'.uvars)
    (htype : TrExprS (ves.venv .safe) v.levelParams [] v.type ci'.type)
    (hvalue : TrExprS (ves.venv .safe) v.levelParams [] v.value ci'.value)
    (hci : ci'.WF (ves.venv .safe))
    (state : VState := {}) :
    (checkDef v).WF (.mk' wf .safe v.levelParams) state fun allow _ =>
      allow → PrimitiveResult (ves.venv .safe) v ci' := sorry
