import Lean4Lean.Theory.Typing.InductivePatternEnv

/-! # Pattern facts for concrete certified blocks

Two self-contained certified blocks pin the L4L-10A pattern layer by
evaluation: a mutual tree/forest pair (two families, three flattened
constructors, recursion in both directions) and an indexed vector (one
family, a `Nat` index, indices spelled with `Nat.zero`/`Nat.succ`). Both
use literal names throughout, keeping every closedness and inventory bit
kernel-decidable. The expected `SimplePattern` inventories are written by
hand: the major arity counts shared parameters, all motives, all minors, and
the constructor's result indices; the argument arity counts the
constructor's parameters and fields. -/

namespace Lean4Lean.InductivePatternFixtures

open Lean4Lean.VInductDecl
open Lean4Lean.VInductDecl.BlockGenerationChecked

deriving instance DecidableEq for SimplePattern

/-- `mutual inductive PatTree (α : Type u) | node : α → PatForest α → PatTree α
inductive PatForest (α : Type u) | nil | cons : PatTree α → PatForest α →
PatForest α end` -/
def patBlock : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `PatTree
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `PatForest [.param 0]) (.bvar 1))
                 (.app (.const `PatTree [.param 0]) (.bvar 2))))⟩,
           `PatTree.node⟩] },
     { name := `PatForest
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const `PatForest [.param 0]) (.bvar 0))⟩,
           `PatForest.nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.app (.const `PatTree [.param 0]) (.bvar 0))
               (.forallE (.app (.const `PatForest [.param 0]) (.bvar 1))
                 (.app (.const `PatForest [.param 0]) (.bvar 2))))⟩,
           `PatForest.cons⟩] }]

/-- `inductive PatVec (α : Type) : Nat → Type | nil : PatVec α Nat.zero
| cons : α → (n : Nat) → PatVec α n → PatVec α (Nat.succ n)` -/
def patVec : VInductDecl where
  uvars := 0
  nparams := 1
  types :=
    [{ name := `PatVec
       uvars := 0
       type := .forallE (.sort (.succ .zero))
         (.forallE (.const `Nat []) (.sort (.succ .zero)))
       ctors :=
         [⟨⟨0, .forallE (.sort (.succ .zero))
             (.app (.app (.const `PatVec []) (.bvar 0))
               (.const `Nat.zero []))⟩,
           `PatVec.nil⟩,
          ⟨⟨0, .forallE (.sort (.succ .zero))
             (.forallE (.bvar 0)
               (.forallE (.const `Nat [])
                 (.forallE (.app (.app (.const `PatVec []) (.bvar 2)) (.bvar 0))
                   (.app (.app (.const `PatVec []) (.bvar 3))
                     (.app (.const `Nat.succ []) (.bvar 1))))))⟩,
           `PatVec.cons⟩] }]

#guard patBlock.stage3
#guard patVec.stage3

/-- The certified mutual block. -/
def patTreeGen : patBlock.BlockGenerationChecked :=
  (identityBlockGeneration? patBlock).get (by decide)

/-- The certified indexed block. -/
def patVecGen : patVec.BlockGenerationChecked :=
  (identityBlockGeneration? patVec).get (by decide)

/-! ## Pattern inventories

Majors: `PatTree`/`PatForest` share one parameter, two motives, and three
minors with no indices (major arity 6); `PatVec` has one parameter, one
motive, two minors, and one index (major arity 5). -/

#guard patTreeGen.flatCtors.map (fun c => patTreeGen.rulePattern c) ==
  [.iota (.str `PatTree "rec") 6 `PatTree.node 3,
   .iota (.str `PatForest "rec") 6 `PatForest.nil 1,
   .iota (.str `PatForest "rec") 6 `PatForest.cons 3]

#guard patVecGen.flatCtors.map (fun c => patVecGen.rulePattern c) ==
  [.iota (.str `PatVec "rec") 5 `PatVec.nil 1,
   .iota (.str `PatVec "rec") 5 `PatVec.cons 4]

/-! ## Payload closedness by evaluation -/

theorem patTreeClosure : patTreeGen.RuleClosure :=
  RuleClosure.of_all _ (by decide) (by decide)

theorem patVecClosure : patVecGen.RuleClosure :=
  RuleClosure.of_all _ (by decide) (by decide)

/-! ## The instantiated pattern sets

Both blocks now carry complete pattern payloads: `patTreeGen.IotaPat
patTreeClosure` and `patVecGen.IotaPat patVecClosure` satisfy every generic
obligation proved in `Theory/Typing/InductivePattern.lean`, at the standard
axiom closure recorded below. -/

/-- info: 'Lean4Lean.InductivePatternFixtures.patTreeClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patTreeClosure

/-- info: 'Lean4Lean.InductivePatternFixtures.patVecClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patVecClosure

/-! ## The assembled block-local environments

Both blocks assemble over the empty base with no extensions; their defeq
sets are exactly their generated rules. -/

#guard (patTreeGen.assembleEnv .empty []).isSome
#guard (patVecGen.assembleEnv .empty []).isSome

/-- Every defeq of the assembled tree/forest environment is a generated
rule: the base is defeq-free and no extensions are registered. -/
example {env' : VEnv} (h : patTreeGen.assembleEnv .empty [] = some env')
    {df : VDefEq} (hdf : env'.defeqs df) :
    df ∈ patTreeGen.generatedRules := by
  rcases patTreeGen.assembleEnv_defeq_cases h (fun _ hd => hd) hdf with
    hrule | ⟨ext, hm, -⟩
  · exact hrule
  · cases hm

end Lean4Lean.InductivePatternFixtures
