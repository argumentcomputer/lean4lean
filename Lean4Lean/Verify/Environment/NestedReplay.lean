import Lean4Lean.Verify.Environment.SingletonParityReplay
import Lean4Lean.Verify.Environment.NestedTransformation

/-!
# Nested environment replay (L4L-09C)

The rose-tree nested declaration replayed over the completed `List`
environment: the real stored metadata is inserted through
`AddInductNestedTrace`, with the `NestedBlockChecked.WF` package proved by
direct concrete typing derivations, and the final environments driven
through `TrEnv'.inductNested`.
-/

namespace Lean4Lean.NestedReplayFixtures

open Lean
open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.NestedRepresentation
open Lean4Lean.NestedInductiveFixtures
open VInductDecl

local instance : Inhabited VEnv := ⟨.empty⟩
local instance : Inhabited VConstVal := ⟨⟨⟨0, .sort .zero⟩, .anonymous⟩⟩

/-! ## The completed List replay as the input boundary -/

theorem listTrEnv07 : TrEnv' .safe listMap07 false listFinalEnv07 :=
  .induct listAddInduct07 .empty

theorem listFinalOrdered07 : listFinalEnv07.Ordered :=
  listTrEnv07.wf.ordered

/-! ## The translated rose source and its nested artifact -/

def roseSourceV : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := ``RoseTree
       uvars := 1
       type := nestedConstVType09A% RoseTree
       ctors :=
         [⟨⟨1, nestedConstVType09A% RoseTree.node⟩, ``RoseTree.node⟩] }]

def roseNestedC? : Option (NestedBlockChecked roseSourceV) :=
  nestedBlockChecked? [listTarget] roseSourceV

#guard roseNestedC?.isSome

def roseNestedC : NestedBlockChecked roseSourceV :=
  roseNestedC?.get (by native_decide)

/-! ## Stored metadata and phase maps/environments -/

def roseInfo09 : ConstantInfo := kernelInductInfo% RoseTree
def roseNodeInfo09 : ConstantInfo := kernelCtorInfo% RoseTree.node
def roseRecInfo09 : ConstantInfo := kernelRecInfo% RoseTree.rec
def roseRec1Info09 : ConstantInfo := kernelRecInfo% RoseTree.rec_1

def roseFamilyV : VConstVal := roseSourceV.types[0].toVConstVal
def roseNodeV : VConstVal := roseSourceV.types[0].ctors[0]
def roseRecV : VConstVal := roseNestedC.recursors[0]!
def roseRec1V : VConstVal := roseNestedC.recursors[1]!

#guard roseRecV.name == ``RoseTree.rec
#guard roseRec1V.name == `Lean4Lean.NestedRepresentation.RoseTree.rec_1

def roseTypeMap09 : ConstMap := listMap07.insert ``RoseTree roseInfo09
def roseCtorMap09 : ConstMap := roseTypeMap09.insert ``RoseTree.node roseNodeInfo09
def roseRecMap09 : ConstMap := roseCtorMap09.insert ``RoseTree.rec roseRecInfo09
def roseMap09 : ConstMap :=
  roseRecMap09.insert `Lean4Lean.NestedRepresentation.RoseTree.rec_1 roseRec1Info09

def roseTypeEnv09 : VEnv :=
  (listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant).get!
def roseCtorEnv09 : VEnv :=
  (roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant).get!
-- the recursor and rule phase environments are defined below, over the
-- printed literal inventories


/-! ## Printed artifact literals

The restored recursor types and rule components, printed from the
computed artifact and tied back to it below; the concrete typing
derivations are stated over these literals. -/

/-- Printed image of `roseNestedC.recursors[0]!.type`. -/
def roseRecTypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.app (.bvar 5) (.bvar 0))))))))

def roseRec1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const `List [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))
                (.app (.bvar 4) (.bvar 0))))))))

def roseRule0LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree.rec
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const
                            `Lean4Lean.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule0RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app (.bvar 4) (.bvar 1))
                      (.bvar 0))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule0TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.bvar 5)
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 6)
                    (.app
                      (.app
                        (.app
                          (.const
                            `Lean4Lean.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule1LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                              [.param 0, .param 1])
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.bvar 1))
                  (.bvar 0))
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule1RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.bvar 1))))))

def roseRule1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.bvar 3)
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule2LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule2RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app (.bvar 2) (.bvar 1))
                        (.bvar 0))
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.app
                                    (.const
                                      `Lean4Lean.NestedRepresentation.RoseTree.rec
                                      [.param 0, .param 1])
                                    (.bvar 7))
                                  (.bvar 6))
                                (.bvar 5))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule2TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 5)
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

#guard roseRecV.type == roseRecTypeL
#guard roseRec1V.type == roseRec1TypeL
#guard roseNestedC.generatedRules.map (fun df => (df.uvars, df.lhs, df.rhs, df.type)) ==
  [(2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL),
   (2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL),
   (2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL)]
#guard roseRecV.uvars == 2 && roseRec1V.uvars == 2


/-! ## Literal inventories -/

def roseRecVL : VConstVal := ⟨⟨2, roseRecTypeL⟩, ``RoseTree.rec⟩
def roseRec1VL : VConstVal :=
  ⟨⟨2, roseRec1TypeL⟩, `Lean4Lean.NestedRepresentation.RoseTree.rec_1⟩

def roseRulesL : List VDefEq :=
  [⟨2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL⟩,
   ⟨2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL⟩,
   ⟨2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL⟩]

theorem roseRecursors_eq : roseNestedC.recursors = [roseRecVL, roseRec1VL] := by
  native_decide

theorem roseRules_eq : roseNestedC.generatedRules = roseRulesL := by
  native_decide

def roseRecEnv09 : VEnv :=
  (roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant).get!
def roseRec1Env09 : VEnv :=
  (roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant).get!
def roseFinalEnv09 : VEnv :=
  roseRulesL.foldl VEnv.addDefEq roseRec1Env09

/-! ## Concrete constant well-formedness -/

theorem roseFamilyWF09 : roseFamilyV.toVConstant.WF listFinalEnv07 :=
  ⟨_, by type_tac⟩

theorem roseTypeEnv09_eq :
    listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant =
      some roseTypeEnv09 := rfl

theorem roseTypeOrdered09 : roseTypeEnv09.Ordered :=
  .const listFinalOrdered07 roseFamilyWF09 roseTypeEnv09_eq

theorem roseNodeWF09 : roseNodeV.toVConstant.WF roseTypeEnv09 := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseCtorEnv09_eq :
    roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant =
      some roseCtorEnv09 := rfl

theorem roseCtorOrdered09 : roseCtorEnv09.Ordered :=
  .const roseTypeOrdered09 roseNodeWF09 roseCtorEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRecWF09 : (⟨2, roseRecTypeL⟩ : VConstant).WF roseCtorEnv09 := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseRecEnv09_eq :
    roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant =
      some roseRecEnv09 := rfl

theorem roseRecOrdered09 : roseRecEnv09.Ordered :=
  .const roseCtorOrdered09 roseRecWF09 roseRecEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRec1WF09 : (⟨2, roseRec1TypeL⟩ : VConstant).WF roseRecEnv09 := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem roseRec1Env09_eq :
    roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant =
      some roseRec1Env09 := rfl

theorem roseRec1Ordered09 : roseRec1Env09.Ordered :=
  .const roseRecOrdered09 roseRec1WF09 roseRec1Env09_eq


/-! ## Rule well-formedness at the rule-phase environment -/

section RuleWF

set_option maxRecDepth 8000

/-- The lookup hypotheses shared by every rule component derivation; the
environment argument is any `addDefEq` extension of `roseRec1Env09`, whose
constants agree definitionally. -/
macro "rose_rule_hyps" e:term : tactic => `(tactic| (
  have hList : VEnv.constants $e ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : VEnv.constants $e ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : VEnv.constants $e ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : VEnv.constants $e ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : VEnv.constants $e ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  have hRec : VEnv.constants $e ``RoseTree.rec =
      some ⟨2, roseRecTypeL⟩ := rfl
  have hRec1 : VEnv.constants $e
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
      some ⟨2, roseRec1TypeL⟩ := rfl))

def roseRuleEnv1 : VEnv := roseRec1Env09.addDefEq roseRulesL[0]
def roseRuleEnv2 : VEnv := roseRuleEnv1.addDefEq roseRulesL[1]

theorem roseRule0WF09 : roseRulesL[0].WF roseRec1Env09 := by
  constructor
  · rose_rule_hyps roseRec1Env09; type_tac
  · rose_rule_hyps roseRec1Env09; type_tac

theorem roseRule1WF09 : roseRulesL[1].WF roseRuleEnv1 := by
  constructor
  · rose_rule_hyps roseRuleEnv1; type_tac
  · rose_rule_hyps roseRuleEnv1; type_tac

theorem roseRule2WF09 : roseRulesL[2].WF roseRuleEnv2 := by
  constructor
  · rose_rule_hyps roseRuleEnv2; type_tac
  · rose_rule_hyps roseRuleEnv2; type_tac

end RuleWF


/-! ## The semantic package -/

theorem roseTypesFold_eq :
    roseSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) listFinalEnv07 =
      some roseTypeEnv09 := rfl

theorem roseCtorsFold_eq :
    roseSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseTypeEnv09 =
      some roseCtorEnv09 := rfl

theorem roseRecsFold_eq :
    roseNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseCtorEnv09 =
      some roseRec1Env09 := by
  rw [roseRecursors_eq]; rfl

theorem roseNestedWF09 : roseNestedC.WF listFinalEnv07 := by
  refine ⟨⟨roseFamilyWF09, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_, fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (roseTypeEnv09_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (roseTypesFold_eq.symm.trans h)
    exact ⟨roseNodeWF09, fun env' h' => by
      cases Option.some.inj (roseCtorEnv09_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    rw [roseRecursors_eq]
    exact ⟨roseRecWF09, fun env' h' => by
      cases Option.some.inj (roseRecEnv09_eq.symm.trans h')
      exact ⟨roseRec1WF09, fun env'' h'' => by
        cases Option.some.inj (roseRec1Env09_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (roseRecsFold_eq.symm.trans hR)
    rw [roseRules_eq]
    exact ⟨roseRule0WF09, roseRule1WF09, roseRule2WF09, trivial⟩


/-! ## Freshness of the stored insertions -/

theorem listMapWF07 : listMap07.WF :=
  listCtorMapWF07.insert _ _ listRecFresh07

theorem roseTypeFresh09 : listMap07.find? ``RoseTree = none := by
  rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseTypeMapWF09 : roseTypeMap09.WF :=
  listMapWF07.insert _ _ roseTypeFresh09

theorem roseNodeFresh09 : roseTypeMap09.find? ``RoseTree.node = none := by
  rw [roseTypeMap09, listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseCtorMapWF09 : roseCtorMap09.WF :=
  roseTypeMapWF09.insert _ _ roseNodeFresh09

theorem roseRecFresh09 : roseCtorMap09.find? ``RoseTree.rec = none := by
  rw [roseCtorMap09, roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseRecMapWF09 : roseRecMap09.WF :=
  roseCtorMapWF09.insert _ _ roseRecFresh09

theorem roseRec1Fresh09 :
    roseRecMap09.find? `Lean4Lean.NestedRepresentation.RoseTree.rec_1 = none := by
  rw [roseRecMap09, roseCtorMapWF09.find?_insert, roseCtorMap09,
    roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-! ## Stored-metadata translations -/

theorem roseInfoTr09 :
    TrConstVal .safe listFinalEnv07 roseInfo09 roseFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listFinalEnv07 roseInfo09.levelParams []
      roseInfo09.type roseFamilyV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS listFinalOrdered07 trivial ⟨_, by type_tac⟩

theorem roseNodeTr09 :
    TrConstVal .safe roseTypeEnv09 roseNodeInfo09 roseNodeV := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseTypeEnv09 roseNodeInfo09.levelParams []
      roseNodeInfo09.type roseNodeV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS roseTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem roseRecTr09 :
    TrConstVal .safe roseCtorEnv09 roseRecInfo09 roseRecVL := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseCtorEnv09 roseRecInfo09.levelParams []
      roseRecInfo09.type roseRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRecWF09
  exact shape.to_trExprS roseCtorOrdered09 trivial ⟨_, hty⟩

theorem roseRec1Tr09 :
    TrConstVal .safe roseRecEnv09 roseRec1Info09 roseRec1VL := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseRecEnv09 roseRec1Info09.levelParams []
      roseRec1Info09.type roseRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRec1WF09
  exact shape.to_trExprS roseRecOrdered09 trivial ⟨_, hty⟩


/-! ## Recursor K metadata and stored lookups -/

theorem roseKTarget09 : roseNestedC.generation.kTarget = false := by
  native_decide

theorem roseRecLookup09 :
    roseMap09.find? ``RoseTree.rec = some roseRecInfo09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp [roseRecMap09, roseCtorMapWF09.find?_insert]

theorem roseRec1Lookup09 :
    roseMap09.find? `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
      some roseRec1Info09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp

theorem roseRecK09 :
    RecursorMapKMatches roseMap09 roseNestedC.recursors
      roseNestedC.generation.kTarget := by
  rw [roseRecursors_eq, roseKTarget09]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRecInfo09, roseRecLookup09, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRec1Info09, roseRec1Lookup09, by decide⟩
  · cases hmem

/-! ## The nested alignment trace and its `TrEnv'` drive -/

def roseTrace09 :
    AddInductNestedTrace listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 where
  nested := roseNestedC
  nested_wf := roseNestedWF09
  typeMap := roseTypeMap09
  typeEnv := roseTypeEnv09
  ctorMap := roseCtorMap09
  ctorEnv := roseCtorEnv09
  recEnv := roseRec1Env09
  addTypes := .cons
    { info := roseInfo09
      kind_eq := trivial
      tr := roseInfoTr09
      map_fresh := roseTypeFresh09
      env_add := roseTypeEnv09_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := roseNodeInfo09
      kind_eq := trivial
      tr := roseNodeTr09
      map_fresh := roseNodeFresh09
      env_add := roseCtorEnv09_eq
      map_add := rfl } .nil
  addRecs := roseRecursors_eq ▸ .cons
    { info := roseRecInfo09
      kind_eq := trivial
      tr := roseRecTr09
      map_fresh := roseRecFresh09
      env_add := roseRecEnv09_eq
      map_add := rfl } (.cons
    { info := roseRec1Info09
      kind_eq := trivial
      tr := roseRec1Tr09
      map_fresh := roseRec1Fresh09
      env_add := roseRec1Env09_eq
      map_add := rfl } .nil)
  recK := roseRecK09
  addRules := ⟨by rw [roseRules_eq]; rfl⟩

theorem roseAddInductNested09 :
    AddInductNested listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 :=
  ⟨roseTrace09⟩

/-- The rose-tree nested declaration, replayed from real stored metadata
over the completed `List` environment through the nested alignment
constructor. -/
theorem roseTrEnv09 : TrEnv' .safe roseMap09 false roseFinalEnv09 :=
  .inductNested roseAddInductNested09 listTrEnv07

theorem roseFinalOrdered09 : roseFinalEnv09.Ordered :=
  roseTrEnv09.wf.ordered


/-! ## Round-trip guards

The stored-metadata surface inserted by the trace is tied to the Theory
artifact inventory, and the final map/environment pair carries the
documented transitional closure (the checker-refinement frontier plus the
compiler-trust axiom introduced by the `native_decide` observations). -/

#guard roseNestedC.elim.numNested == 1
#guard roseRecV == roseRecVL && roseRec1V == roseRec1VL

/--
info: 'Lean4Lean.NestedReplayFixtures.roseTrEnv09' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseKTarget09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseTrEnv09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseNestedWF09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseNestedWF09

end Lean4Lean.NestedReplayFixtures
