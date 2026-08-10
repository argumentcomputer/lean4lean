import Lean4Lean.Theory.Inductive

/-!
# Nested-inductive flattening (L4L-09B)

The Theory mirror of the kernel's `ElimNestedInductive` transformation,
following the committed L4L-09A design
(`Lean4Lean/Verify/Environment/NestedRepresentation.lean`): the stored
payload of a nested declaration is the source `VInductDecl`, and nested
support flows through an additive artifact coupling

1. the flattened mutual block, an ordinary `VInductDecl` handled by the
   existing arbitrary-block analyzer, and
2. one auxiliary specification per auxiliary family — the Theory analog of
   the kernel's `aux2nested` map.

`nestedElimination?` computes both from the source declaration plus the
caller-supplied metadata of the previously declared inductives that are
nested into (`NestedTargetBlock`).  Keeping the target metadata an explicit
input keeps this analyzer environment-free, exactly like `checked?`;
`NestedTargetBlock.WF` separately ties the supplied copy to a Theory
environment.

The transformation mirrors the kernel phase for phase:

- An application `I Ds is` is a nested occurrence when `I` is a family of a
  supplied target block, the spine covers at least `I`'s parameters, and
  the parametric arguments `Ds` mention a family of the growing flattened
  block.  Parametric arguments that also mention a constructor-local binder
  reject the declaration (the kernel's "parameters cannot contain local
  variables"), and matched occurrences are rewritten without descending
  into the emitted replacement, exactly like `Expr.replace`.
- One auxiliary family is created per family of `I`'s block, in `all`
  order, with `I`'s family and constructor types level-instantiated at the
  occurrence's levels and parameter-instantiated at `Ds`; auxiliary
  constructor bodies are queued and flattened by the same loop until the
  block is stable.
- Auxiliary names are canonical: `(`_nested` ++ familyName).appendIndexAfter i`
  with a global counter, matching the kernel's choice whenever the ambient
  environment contains no colliding `_nested.*` constant.  The L4L-09A
  collision probe shows the choice is erased from all final artifacts, and
  in-block collisions are rejected downstream by `blockNamesOK` exactly
  where the kernel's `checkName` rejects its own collisions.

Acceptance (`nestedStage3`) is flattening success plus generation
readiness of the flattened block through the unchanged L4L-08 machinery.
No generated recursor, rule, or environment replay is claimed at this
checkpoint; the restoration substitution over generation artifacts is
L4L-09C's obligation.
-/

namespace Lean4Lean

deriving instance DecidableEq for VConstant
deriving instance DecidableEq for VConstVal
deriving instance DecidableEq for VInductiveType
deriving instance DecidableEq for VInductDecl

/-- Does `e` mention, through a loose bvar, one of the `k` binders directly
below its root?  `d` counts binders passed inside `e` itself. -/
def VExpr.hasLooseBelow (k : Nat) : VExpr → (d : Nat := 0) → Bool
  | .bvar i, d => d ≤ i && i - d < k
  | .sort _, _ | .const .., _ => false
  | .app e1 e2, d => e1.hasLooseBelow k d || e2.hasLooseBelow k d
  | .lam e1 e2, d | .forallE e1 e2, d =>
      e1.hasLooseBelow k d || e2.hasLooseBelow k (d+1)

/-- Lower every loose bvar of `e` by `n`.  Total; meaningful only when no
loose bvar lies below `n`, which callers establish with `hasLooseBelow`. -/
def VExpr.lowerN (n : Nat) : VExpr → (d : Nat := 0) → VExpr
  | .bvar i, d => if i < d then .bvar i else .bvar (i - n)
  | .sort l, _ => .sort l
  | .const c ls, _ => .const c ls
  | .app e1 e2, d => .app (e1.lowerN n d) (e2.lowerN n d)
  | .lam e1 e2, d => .lam (e1.lowerN n d) (e2.lowerN n (d+1))
  | .forallE e1 e2, d => .forallE (e1.lowerN n d) (e2.lowerN n (d+1))

namespace VInductDecl

/-- Simultaneous outermost-first parameter substitution: the first list
element replaces the outermost of the `args.length` innermost loose bvars.
The same shape as `instantiateRev` on the implementation side. -/
def instRevParams : VExpr → List VExpr → VExpr
  | C, [] => C
  | C, e :: es => instRevParams (C.inst e es.length) es

/-- Substitute the leading `np`-binder telescope of `ty` simultaneously at
`args` (outermost parameter first), mirroring the kernel's
`instantiateForallParams`.  Fails when `ty` exposes fewer than `np`
binders. -/
def instTelescope (np : Nat) (ty : VExpr) (args : List VExpr) :
    Option VExpr := do
  guard (args.length == np)
  guard ((VExpr.telN np ty).length == np)
  return instRevParams (VExpr.dropN np ty) args

/-- One previously declared mutual block that nested occurrences may point
into.  `families` is the complete block in `all` order, in that block's own
universe parameters; a copy is supplied so the analyzer stays
environment-free, and `NestedTargetBlock.WF` ties the copy to an
environment. -/
structure NestedTargetBlock where
  nparams : Nat
  families : List VInductiveType

/-- The supplied target copy agrees with the environment's stored
constants. -/
structure NestedTargetBlock.WF (env : VEnv) (block : NestedTargetBlock) :
    Prop where
  families : ∀ f ∈ block.families,
    env.constants f.name = some f.toVConstVal.toVConstant
  ctors : ∀ f ∈ block.families, ∀ c ∈ f.ctors,
    env.constants c.name = some c.toVConstant

def NestedTargetsWF (env : VEnv) (targets : List NestedTargetBlock) : Prop :=
  ∀ t ∈ targets, t.WF env

/-- One auxiliary family created by nested elimination: the Theory analog
of one `aux2nested` binding.  `values` are the parametric arguments `Ds`,
open over the block parameters (innermost bvar = last parameter), in
declaration level-world. -/
structure NestedAuxSpec where
  aux : Name
  target : Name
  levels : List VLevel
  values : List VExpr
  deriving DecidableEq

/-- The nested occurrence this auxiliary family abbreviates: `I Ds`. -/
def NestedAuxSpec.value (spec : NestedAuxSpec) : VExpr :=
  (VExpr.const spec.target spec.levels).appN spec.values

/-- The flattening result: the flattened mutual block plus one auxiliary
specification per auxiliary family, in flattened family order.  When the
source contains no nested occurrence, `flat` is the source itself and
`specs` is empty. -/
structure NestedElimination (source : VInductDecl) where
  flat : VInductDecl
  specs : List NestedAuxSpec

namespace ElimNested

/-- Growing flattening state.  `types` extends the source families with the
auxiliary families; `specs` aligns with `types.drop ntypes`. -/
structure State where
  types : Array VInductiveType
  specs : Array NestedAuxSpec
  nextIdx : Nat := 1

variable (targets : List NestedTargetBlock) (uvars np : Nat)

/-- The target block owning family `c`, ignoring names that are currently
part of the flattened block itself (the kernel only recognizes previously
*declared* inductives). -/
def findTarget? (st : State) (c : Name) : Option NestedTargetBlock :=
  if st.types.any (·.name == c) then none
  else targets.find? fun t => t.families.any (·.name == c)

/-- Register the auxiliary families for one first-seen nested occurrence
`I Ds` and return the auxiliary family name standing for `I` itself.
`doms` is the discovering constructor's parameter telescope, and `values`
are the parametric arguments in parameter-world. -/
def registerAux (st : State) (block : NestedTargetBlock) (I : Name)
    (ls : List VLevel) (doms values : List VExpr) :
    Option (Name × State) := do
  let mut st := st
  let mut result := none
  for J in block.families do
    if J.uvars != ls.length then failure
    let auxName := (`_nested ++ J.name).appendIndexAfter st.nextIdx
    let auxType ← instTelescope block.nparams (J.type.instL ls) values
    let mut auxCtors : List VConstVal := []
    for c in J.ctors do
      let ctype ← instTelescope block.nparams (c.type.instL ls) values
      auxCtors := auxCtors ++
        [⟨⟨uvars, VExpr.forallN doms ctype⟩, c.name.replacePrefix J.name auxName⟩]
    let auxFamily : VInductiveType :=
      { name := auxName, uvars, type := VExpr.forallN doms auxType
        ctors := auxCtors }
    st :=
      { types := st.types.push auxFamily
        specs := st.specs.push ⟨auxName, J.name, ls, values⟩
        nextIdx := st.nextIdx + 1 }
    if J.name == I then result := some auxName
  match result with
  | some auxName => return (auxName, st)
  | none => none

/-- Rewrite one constructor-body subterm at binder depth `k`, mirroring
`replaceAllNested`: matched occurrences are replaced without descending
into the replacement; unmatched nodes recurse into their children. -/
def replace (doms : List VExpr) :
    VExpr → (k : Nat) → State → Option (VExpr × State)
  | e@(.app f a), k, st => do
      match rewrite? e k st with
      | some result => result
      | none =>
          let (f', st) ← replace doms f k st
          let (a', st) ← replace doms a k st
          return (.app f' a', st)
  | e@(.const ..), k, st => (rewrite? e k st).getD (some (e, st))
  | .lam ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.lam ty' body', st)
  | .forallE ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.forallE ty' body', st)
  | e, _, st => some (e, st)
  where
  /-- `some (some ..)` rewrites the node, `some none` is a hard rejection,
  `none` leaves the node to the structural recursion. -/
  rewrite? (e : VExpr) (k : Nat) (st : State) :
      Option (Option (VExpr × State)) := do
    let .const c ls := VExpr.appHead e | none
    let args := e.appArgs []
    let block ← findTarget? targets st c
    guard (block.nparams ≤ args.length)
    guard (0 < block.nparams)
    let ds := args.take block.nparams
    let names := st.types.toList.map (·.name)
    guard (ds.any (·.hasAnyConst names))
    -- the kernel's "nested inductive datatypes parameters cannot contain
    -- local variables" rejection
    if ds.any (·.hasLooseBelow k) then return none
    let values := ds.map (·.lowerN k)
    let key := (VExpr.const c ls).appN values
    let rest := args.drop block.nparams
    let recover (auxName : Name) (st : State) : VExpr × State :=
      ((VExpr.const auxName (VLevel.params uvars)).appN
        (VExpr.bvarRevRange k np ++ rest), st)
    match st.specs.find? (·.value == key) with
    | some spec => return some (recover spec.aux st)
    | none =>
        match registerAux uvars st block c ls doms values with
        | some (auxName, st) => return some (recover auxName st)
        | none => return none

/-- Flatten every constructor of every block family, including the queued
auxiliary families, until the block is stable.  `fuel` mirrors the
kernel's `inductiveFuel` bound on the same loop. -/
def run (fuel : Nat) (i : Nat) (st : State) : Option State :=
  match fuel with
  | 0 => none
  | fuel+1 =>
    if h : i < st.types.size then
      let ty := st.types[i]
      let step := ty.ctors.foldlM (init := ([], st)) fun (acc, st) c => do
        let doms := VExpr.telN np c.type
        guard (doms.length == np)
        let (body, st) ← replace targets uvars np doms (VExpr.dropN np c.type) 0 st
        return (acc ++ [{ c with type := VExpr.forallN doms body }], st)
      match step with
      | some (ctors, st) =>
          run fuel (i+1) { st with types := st.types.set! i { ty with ctors } }
      | none => none
    else some st

end ElimNested

/-- Flatten one source declaration against the supplied target blocks.
Returns the flattened block plus the auxiliary specifications; the
identity result (`flat = source`, no specs) is returned when nothing is
nested. -/
def nestedElimination? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedElimination source) := do
  let st ← ElimNested.run targets source.uvars source.nparams fuel 0
    { types := source.types.toArray, specs := #[] }
  return { flat := { source with types := st.types.toList }
           specs := st.specs.toList }

/-- The number of auxiliary families, matching the stored
`InductiveVal.numNested` of an accepted nested declaration. -/
def NestedElimination.numNested {source : VInductDecl}
    (elim : NestedElimination source) : Nat :=
  elim.specs.length

/-- A flattened declaration accepted by the unchanged arbitrary-block
machinery: the complete L4L-09B validation gate.  Positivity, name, level,
anatomy, and generation-shape checking of the flattened block reuse the
L4L-08 analyzers verbatim. -/
structure NestedBlockChecked (source : VInductDecl) where
  elim : NestedElimination source
  generation : BlockGenerationChecked elim.flat

def nestedBlockChecked? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedBlockChecked source) := do
  let elim ← nestedElimination? targets source fuel
  let generation ← elim.flat.identityBlockGeneration?
  return ⟨elim, generation⟩

/-- Structural acceptance for a nested declaration. -/
def nestedStage3 (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) : Bool :=
  (nestedBlockChecked? targets source fuel).isSome

end VInductDecl

end Lean4Lean
