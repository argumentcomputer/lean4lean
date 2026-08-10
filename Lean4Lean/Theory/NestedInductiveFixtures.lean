import Lean4Lean.Theory.NestedInductive

/-!
# Nested flattening fixtures (L4L-09B)

Executable pins for `nestedElimination?` on the two ladder fixtures — a
universe-polymorphic rose tree through `List` and a nested indexed family
through a `PVec`-style vector — plus the nearest structural rejections.
Every family, constructor, auxiliary specification, and acceptance bit is
compared against a hand-written expected descriptor.  The kernel
differential for the same shapes lives in
`Lean4Lean/Verify/Environment/NestedTransformation.lean`.
-/

namespace Lean4Lean.NestedInductiveFixtures

open VInductDecl

/-! ## Target blocks

Hand-written copies of the nested-into metadata, in each block's own
universe parameters; the Verify differential checks the same shapes
against Lean's stored metadata. -/

/-- `List` as a nested target: one family, one parameter. -/
def listTarget : NestedTargetBlock where
  nparams := 1
  families :=
    [{ name := `List
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const `List [.param 0]) (.bvar 0))⟩, `List.nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0]) (.bvar 1))
                 (.app (.const `List [.param 0]) (.bvar 2))))⟩, `List.cons⟩] }]

/-- A `PVec`-style indexed vector as a nested target: one parameter, one
`Nat` index, indices spelled with `Nat.zero`/`Nat.succ`. -/
def pvecTarget : NestedTargetBlock where
  nparams := 1
  families :=
    [{ name := `PVec
       uvars := 0
       type := .forallE (.sort (.succ .zero))
         (.forallE (.const `Nat []) (.sort (.succ .zero)))
       ctors :=
         [⟨⟨0, .forallE (.sort (.succ .zero))
             (.app (.app (.const `PVec []) (.bvar 0)) (.const `Nat.zero []))⟩,
           `PVec.nil⟩,
          ⟨⟨0, .forallE (.sort (.succ .zero))
             (.forallE (.bvar 0)
               (.forallE (.const `Nat [])
                 (.forallE (.app (.app (.const `PVec []) (.bvar 2)) (.bvar 0))
                   (.app (.app (.const `PVec []) (.bvar 3))
                     (.app (.const `Nat.succ []) (.bvar 1))))))⟩,
           `PVec.cons⟩] }]

/-! ## Rose tree through `List` -/

def roseAux : Lean.Name := (`_nested ++ `List).appendIndexAfter 1

/-- `inductive Rose (α : Type u) | node : α → List (Rose α) → Rose α` -/
def roseSource : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0])
                   (.app (.const `Rose [.param 0]) (.bvar 1)))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] }]

/-- The expected flattened rose block: the rewritten source family plus one
auxiliary family, exactly the shapes pinned against the kernel by the
L4L-09A probes. -/
def roseFlat : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] },
     { name := roseAux
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const roseAux [.param 0]) (.bvar 0))⟩, roseAux ++ `nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.app (.const `Rose [.param 0]) (.bvar 0))
               (.forallE (.app (.const roseAux [.param 0]) (.bvar 1))
                 (.app (.const roseAux [.param 0]) (.bvar 2))))⟩,
           roseAux ++ `cons⟩] }]

/-- The expected auxiliary specification: `List (Rose α)`, open over the
block parameter. -/
def roseSpec : NestedAuxSpec where
  aux := roseAux
  target := `List
  levels := [.param 0]
  values := [.app (.const `Rose [.param 0]) (.bvar 0)]

def roseElim? : Option (NestedElimination roseSource) :=
  nestedElimination? [listTarget] roseSource

#guard roseElim?.isSome
#guard (roseElim?.map fun elim => elim.flat == roseFlat).getD false
#guard (roseElim?.map fun elim => elim.specs == [roseSpec]).getD false
#guard (roseElim?.map (·.numNested)).getD 0 == 1
#guard roseFlat.stage3
#guard nestedStage3 [listTarget] roseSource
-- acceptance behavior of the raw analyzers on the source is unchanged
#guard !roseSource.stage3

/-! ## Nested indexed family through `PVec` -/

def nvAux : Lean.Name := (`_nested ++ `PVec).appendIndexAfter 1

/-- `inductive NV | node : (n : Nat) → PVec NV n → NV` -/
def nvSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `NV
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.app (.const `PVec []) (.const `NV []))
                 (.bvar 0))
               (.const `NV []))⟩, `NV.node⟩] }]

/-- The expected flattened indexed block: the auxiliary family keeps the
`Nat` index, its `nil` instantiates the index at `Nat.zero`, and its
`cons` retains sibling recursion through `NV` plus the successor index. -/
def nvFlat : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `NV
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.const nvAux []) (.bvar 0))
               (.const `NV []))⟩, `NV.node⟩] },
     { name := nvAux
       uvars := 0
       type := .forallE (.const `Nat []) (.sort (.succ .zero))
       ctors :=
         [⟨⟨0, .app (.const nvAux []) (.const `Nat.zero [])⟩, nvAux ++ `nil⟩,
          ⟨⟨0, .forallE (.const `NV [])
             (.forallE (.const `Nat [])
               (.forallE (.app (.const nvAux []) (.bvar 0))
                 (.app (.const nvAux [])
                   (.app (.const `Nat.succ []) (.bvar 1)))))⟩,
           nvAux ++ `cons⟩] }]

/-- The expected specification: the closed partial application `PVec NV`;
the index argument stays behind on each occurrence. -/
def nvSpec : NestedAuxSpec where
  aux := nvAux
  target := `PVec
  levels := []
  values := [.const `NV []]

def nvElim? : Option (NestedElimination nvSource) :=
  nestedElimination? [pvecTarget] nvSource

#guard nvElim?.isSome
#guard (nvElim?.map fun elim => elim.flat == nvFlat).getD false
#guard (nvElim?.map fun elim => elim.specs == [nvSpec]).getD false
#guard nvFlat.stage3
#guard nestedStage3 [pvecTarget] nvSource
#guard !nvSource.stage3

/-! ## Nearest structural rejections -/

/-- A parametric argument mentioning a constructor-local binder:
`node : (n : Nat) → List (Loose n) → Loose` — the kernel's "parameters
cannot contain local variables" class.  Flattening itself rejects. -/
def looseSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Loose
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Nat [])
             (.forallE (.app (.const `List [.zero])
                 (.app (.const `Loose []) (.bvar 0)))
               (.const `Loose []))⟩, `Loose.node⟩] }]

#guard (nestedElimination? [listTarget] looseSource).isNone
#guard !nestedStage3 [listTarget] looseSource

/-- A well-scoped but ill-shaped parametric argument:
`node : Bad → List (Bad Nat.zero) → Bad` flattens, but the auxiliary
constructor then mentions `Bad` applied off the parameter spine, which the
unchanged block analyzer rejects. -/
def badAppSource : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := `Bad
       uvars := 0
       type := .sort (.succ .zero)
       ctors :=
         [⟨⟨0, .forallE (.const `Bad [])
             (.forallE (.app (.const `List [.zero])
                 (.app (.const `Bad []) (.const `Nat.zero [])))
               (.const `Bad []))⟩, `Bad.node⟩] }]

#guard (nestedElimination? [listTarget] badAppSource).isSome
#guard !nestedStage3 [listTarget] badAppSource

-- Without the `List` target metadata the occurrence is not recognized,
-- the flattened block is the source itself, and the unchanged analyzer
-- rejects the under-a-foreign-head family mention.
#guard (nestedElimination? [] roseSource).isSome
#guard ((nestedElimination? [] roseSource).map
  fun elim => elim.flat == roseSource && elim.specs == []).getD false
#guard !nestedStage3 [] roseSource

/-- A source family occupying the first canonical auxiliary name collides
with the created auxiliary family; `blockNamesOK` rejects the flattened
block exactly where the kernel's `checkName` rejects its own duplicate
insertion. -/
def collisionSource : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `Rose
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `List [.param 0])
                   (.app (.const `Rose [.param 0]) (.bvar 1)))
                 (.app (.const `Rose [.param 0]) (.bvar 2))))⟩, `Rose.node⟩] },
     { name := (`_nested ++ `List).appendIndexAfter 1
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors := [] }]

#guard (nestedElimination? [listTarget] collisionSource).isSome
#guard !nestedStage3 [listTarget] collisionSource

end Lean4Lean.NestedInductiveFixtures
