import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Structure projections

This module is the consumer-neutral projection boundary.  A projection is
not determined by a structure name and field number alone: universe
instantiations, parameters, the constructor telescope, and the generated
recursor/iota package all affect its meaning.  `VStructureView` retains that
data from the same checked artifact used by inductive generation.

Projection terms are encoded with the generated recursor.  Earlier
projections occur in the motive of a dependent later projection, so one view
determines both the projected term and its dependent result type.  No
projection-function name map or unconstrained metadata witness is involved.
-/

namespace Lean4Lean

open VInductDecl

/-- Instantiate an outermost-first argument list at a fixed offset.

The `k` variables below the substituted telescope remain bound.  Each
argument is lifted past them before it replaces the then-outermost variable.
This is the operation needed to specialize constructor parameters while
retaining the preceding dependent fields. -/
def VExpr.instRevAt : VExpr → List VExpr → Nat → VExpr
  | e, [], _ => e
  | e, a :: as, k => instRevAt (e.inst a (k + as.length)) as k

/-- A telescope whose entries have the exact retained sort levels. -/
inductive VEnv.OnSortTel (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VLevel → Prop where
  | nil : OnSortTel env U Γ [] []
  | cons :
      env.HasType U Γ A (.sort u) →
      OnSortTel env U (A :: Γ) As us →
      OnSortTel env U Γ (A :: As) (u :: us)

private theorem VEnv.OnTel.monoProjection {env env' : VEnv}
    (henv : env ≤ env') (H : env.OnTel U Γ As) : env'.OnTel U Γ As := by
  induction As generalizing Γ with
  | nil => trivial
  | cons _ _ ih =>
      exact ⟨H.1.mono henv, ih H.2⟩

theorem VEnv.OnSortTel.mono {env env' : VEnv} (henv : env ≤ env')
    (H : env.OnSortTel U Γ As us) : env'.OnSortTel U Γ As us := by
  induction H with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (hA.mono henv) ih

/-- The checked, generated description of a nonrecursive structure.

`generation` supplies the exact family, constructor, recursor, and iota rule
artifacts.  The shape fields restrict that general one-family artifact to the
kernel class on which `.proj` is meaningful: no indices, exactly one
constructor, and no recursive constructor arguments.  `fieldSorts` records
the motive universe required by each projection; `WF` below ties every entry
to the corresponding dependent constructor field type. -/
structure VStructureView where
  source : VInductDecl
  generation : source.GenerationChecked
  constructor : NormalizedCtor
  constructor_eq : generation.block.ctorPairs = [constructor]
  raw_indices_eq : generation.block.rawIndices = []
  checked_indices_eq : generation.block.checked.indices = []
  recursive_eq : constructor.view.recursive = []
  fieldSorts : List VLevel
  fieldSorts_length :
    fieldSorts.length = (constructor.rawFields source.nparams).length

namespace VStructureView

abbrev name (view : VStructureView) : Name :=
  view.generation.block.sourceType.name

abbrev constructorName (view : VStructureView) : Name :=
  view.constructor.raw.name

def recursorName (view : VStructureView) : Name :=
  .str view.name "rec"

abbrev uvars (view : VStructureView) : Nat := view.source.uvars

abbrev nparams (view : VStructureView) : Nat := view.source.nparams

abbrev familyType (view : VStructureView) : VExpr :=
  view.generation.block.sourceType.type

def constructorParams (view : VStructureView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VStructureView) : List VExpr :=
  view.constructor.rawFields view.nparams

/-- The instantiated structure type `S.{levels} params`. -/
def structureType (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

/-- Specialize declaration universes and constructor parameters, retaining
the preceding field binders of each dependent field. -/
def specializedFields (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  view.fields.zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

/-- Universe arguments supplied to the generated recursor for a projection
whose result type inhabits `Sort fieldSort`. -/
def projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : List VLevel :=
  match view.generation.elimination with
  | .large => fieldSort :: levels
  | .small => levels

/-- The two expressions generated for one field.  `typeFn` is the dependent
field type as a function of the structure value; `projector` is a recursor
program implementing the projection. -/
structure ProjectionCode where
  fieldSort : VLevel
  typeFn : VExpr
  minor : VExpr
  projector : VExpr

private def projectionCodes.go (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (allFields : List VExpr) (structType : VExpr) :
    List VExpr → List VLevel → Nat → List ProjectionCode →
      List ProjectionCode
  | field :: fields, fieldSort :: fieldSorts, i, previous =>
      let previousAtMajor := previous.map fun code =>
        .app code.projector.lift (.bvar 0)
      let motiveBody := VExpr.instRevAt
        (field.liftN 1 i) previousAtMajor 0
      let typeFn := .lam structType motiveBody
      let minor := VExpr.lamN allFields
        (.bvar (allFields.length - 1 - i))
      let recursor := .const view.recursorName
        (view.projectionLevels fieldSort levels)
      let projector := .lam structType <| VExpr.appN recursor <|
        params.map (VExpr.liftN 1) ++
          [typeFn.lift, minor.lift, .bvar 0]
      let code := { fieldSort, typeFn, minor, projector }
      code :: projectionCodes.go view levels params allFields structType
        fields fieldSorts (i + 1) (previous ++ [code])
  | _, _, _, _ => []

/-- All field projections, in constructor-field order. -/
def projectionCodes (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List ProjectionCode :=
  let fields := view.specializedFields levels params
  projectionCodes.go view levels params fields
    (view.structureType levels params) fields view.fieldSorts 0 []

/-- The dependent result type of projection `idx`, applied to `major`. -/
def projectionType? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.typeFn major

/-- The recursor encoding of projection `idx`, applied to `major`. -/
def project? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.projector major

/-- Exact registration of the checked structure artifact in a Theory
environment.  These are concrete lookups and generated iota rules, not an
oracle supplied by a projection consumer. -/
structure Registered (view : VStructureView) (env : VEnv) : Prop where
  family : env.constants view.name =
    some view.generation.block.sourceType.toVConstant
  constructor : env.constants view.constructorName =
    some view.constructor.raw.toVConstant
  recursor : env.constants view.recursorName =
    some view.generation.recursor
  rules : ∀ rule ∈ view.generation.generatedRules, env.defeqs rule

/-- Semantic well-formedness of one structure view in its registered
environment.  The retained sort list is checked against the exact raw
dependent field telescope. -/
structure WF (view : VStructureView) (env : VEnv) : Prop
    extends VStructureView.Registered view env where
  parameters : env.OnTel view.uvars [] view.constructorParams
  fieldTelescope : env.OnSortTel view.uvars
    view.constructorParams.reverse view.fields view.fieldSorts
  smallFields : view.generation.elimination = .small →
    ∀ level ∈ view.fieldSorts, level = .zero

theorem WF.rule_mem (self : VStructureView.WF view env) {df : VDefEq}
    (h : df ∈ VInductDecl.GenerationChecked.generatedRules view.generation) :
    VEnv.defeqs env df :=
  self.rules df h

theorem Registered.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.Registered view env) :
    VStructureView.Registered view env' where
  family := henv.1 self.family
  constructor := henv.1 self.constructor
  recursor := henv.1 self.recursor
  rules := fun rule hrule => henv.2 (self.rules rule hrule)

theorem WF.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.WF view env) : VStructureView.WF view env' where
  toRegistered := self.toRegistered.mono henv
  parameters := self.parameters.monoProjection henv
  fieldTelescope := self.fieldTelescope.mono henv
  smallFields := self.smallFields

end VStructureView

namespace VEnv

private theorem SpineWF.monoProjection {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {A es B}, env.SpineWF U Γ A es B → env'.SpineWF U Γ A es B
  | _, [], _, h => h
  | _, _ :: _, _, ⟨A₁, A₂, rfl, he, hrest⟩ =>
      ⟨A₁, A₂, rfl, he.mono henv, SpineWF.monoProjection henv hrest⟩

/-- Environment-indexed projection semantics.

The universe and parameter spines are explicit.  The major premise must have
the exact instantiated structure type, and the result is the unique program
computed by the registered view. -/
structure TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VStructureView) (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major result : VExpr) : Prop where
  viewWF : VStructureView.WF view env
  levelsWF : ∀ level ∈ levels, level.WF U
  levels_length : levels.length = view.uvars
  params_length : params.length = view.nparams
  paramsSpine : ∃ resultLevel,
    env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)
  majorType : env.HasType U Γ major (view.structureType levels params)
  program : ∃ code : VStructureView.ProjectionCode,
    (view.projectionCodes levels params)[idx]? = some code ∧
      result = .app code.projector major

theorem TrProj.project_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VStructureView.project? view levels params idx major = some result := by
  obtain ⟨code, hcode, rfl⟩ := self.program
  simp [VStructureView.project?, hcode]

theorem TrProj.type_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    ∃ code : VStructureView.ProjectionCode,
      VStructureView.projectionType? view levels params idx major =
        some (VExpr.app code.typeFn major) := by
  obtain ⟨code, hcode, _⟩ := self.program
  exact ⟨code, by simp [VStructureView.projectionType?, hcode]⟩

/-- A fixed checked view, universe/parameter instantiation, field index, and
major determine the projection result syntactically. -/
theorem TrProj.result_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result)
    (other : VEnv.TrProj env U Γ view levels params idx major result') :
    result = result' :=
  Option.some.inj (self.project_eq.symm.trans other.project_eq)

/-- Projection evidence is stable when the registered environment is
extended without changing any existing constants or reduction rules. -/
theorem TrProj.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env' U Γ view levels params idx major result where
  viewWF := self.viewWF.mono henv
  levelsWF := self.levelsWF
  levels_length := self.levels_length
  params_length := self.params_length
  paramsSpine := self.paramsSpine.imp fun _ h => h.monoProjection henv
  majorType := self.majorType.mono henv
  program := self.program

/--
info: 'Lean4Lean.VEnv.TrProj.result_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms TrProj.result_eq

/--
info: 'Lean4Lean.VEnv.TrProj.mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms TrProj.mono

end VEnv

end Lean4Lean
