import Lean4Lean.Experimental.SExprParamsD1
import Lean4Lean.Verify.Environment.MutualInductiveFixtures
import Lean4Lean.Theory.Typing.InductivePatternFixtures

/-!
# L4L-16D2: a live block-inductive environment over the D1 fixture

This module extends the kernel-checked D1 instance
(`Lean4Lean/Experimental/SExprParamsD1.lean`) with the next staged slice of
live-environment coverage: a genuine *mutual inductive block* declaration
step.  The block is the real `Tree`/`TreeList` pair of
`Lean4Lean/Theory/MutualInductiveFixtures.lean` — two families, five
flattened constructors, two recursors, five generated iota rules — added to
`d1Env` by a checked `VDecl.WF.inductBlock` history step.

The pattern layer is the first live consumer of the union-level non-overlap
laws landed in `Theory/Typing/InductivePatternEnv.lean`: the block's five
generated rules and the three D1 *definition* rules are packaged as one
`AssembledPat` whose `ExtSeparation` certificate is discharged by kernel
`decide` through the block's rule-pattern inventory.

Scope note.  The `Params.Semantic` bridge is *not* completed here.  Four of
its six fields are delivered (see `d2StructureEtaSound`, `d2IotaRule`, and
the transport-free observations below); `iotaSite` and `registered` for the
five *new* block rules require the full evidence-rich reduction-site replay
that D0/D1 performed per Nat rule, which is a bounded but large piece of
work.  The obstruction is recorded precisely at the end of this file, in the
same style as D1's quotient record.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD2

open InductiveFixtures InductiveReplayFixtures VInductDecl
open MutualInductiveFixtures MutualInductiveReplayFixtures
open ParamsD0 ParamsD1

/-! ## D2 block data

`treeGeneration` is the certified block-wide generation descriptor of the
real `Tree`/`TreeList` declaration, together with the semantic package
`treeBlockGenerationWF` proved over the empty environment in
`Verify/Environment/MutualInductiveFixtures.lean`.  Nothing about the block
is re-derived here; the D2 work is re-basing that package onto `d1Env` and
consuming it. -/

/-- The certified mutual block used by D2. -/
abbrev TreeGen := MutualInductiveFixtures.treeGeneration

/-- The five generated iota RHS towers and index towers are closed. -/
theorem treeRuleClosure : TreeGen.RuleClosure :=
  VInductDecl.BlockGenerationChecked.RuleClosure.of_all _
    (by decide) (by decide)

/-- The block's rule-pattern inventory, kernel-checked.  Majors count the
shared parameter, both motives, all five minors, and the (empty) result
indices; argument arities count parameters plus constructor fields. -/
theorem treeRulePattern_inventory :
    TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) =
      [.iota (.str ``Tree "rec") 8 ``Tree.leaf 2,
       .iota (.str ``Tree "rec") 8 ``Tree.node 2,
       .iota (.str ``Tree "rec") 8 ``Tree.branch 2,
       .iota (.str ``TreeList "rec") 8 ``TreeList.nil 1,
       .iota (.str ``TreeList "rec") 8 ``TreeList.cons 3] := by decide

/-! ## D2 environment layer

The block is added to `d1Env` by the four-phase block transaction.  Its
semantic package is the empty-environment package re-based by monotonicity:
`BlockGenerationChecked.WF` is monotone in every field except the staging
equation, which is re-established over `d1Env` directly. -/

local instance : Inhabited VEnv := ⟨VEnv.empty⟩

theorem tree_fresh : d1Env.constants ``Tree = none := by native_decide

theorem treeList_fresh : d1Env.constants ``TreeList = none := by native_decide

theorem tree_name_ne_treeList : (``Tree : Name) ≠ ``TreeList := by decide

/-- The environment after the block's family constants, before any
constructor. -/
def d2StageT := (d1Env.addConst ``Tree treeType.toVConstant).get!

def d2BlockEnv := (d2StageT.addConst ``TreeList treeListType.toVConstant).get!

theorem d1Env_add_tree :
    d1Env.addConst ``Tree treeType.toVConstant = some d2StageT := by
  simp [VEnv.addConst, tree_fresh, d2StageT]

theorem treeList_fresh_T : d2StageT.constants ``TreeList = none := by
  have hne := tree_name_ne_treeList
  simp [d2StageT, VEnv.addConst, tree_fresh, hne, treeList_fresh]

theorem d2StageT_add_treeList :
    d2StageT.addConst ``TreeList treeListType.toVConstant =
      some d2BlockEnv := by
  simp [VEnv.addConst, treeList_fresh_T, d2BlockEnv]

theorem d1Env_stage :
    d1Env.stageInductiveTypes treeDecl.types = some d2BlockEnv := by
  simp [VEnv.stageInductiveTypes, treeDecl, List.foldlM]
  exact ⟨_, d1Env_add_tree, d2StageT_add_treeList⟩

theorem d1Env_le_d2BlockEnv : d1Env ≤ d2BlockEnv :=
  (VEnv.addConst_le d1Env_add_tree).trans
    (VEnv.addConst_le d2StageT_add_treeList)

/-! ### Re-basing the block's semantic package

`treeBlockGenerationWF` lives over `VEnv.empty`/`treeBlockEnv`.  Every field
except the staging equation is monotone, so the D2 package follows from two
environment inclusions. -/

theorem empty_le_d1Env : VEnv.empty ≤ d1Env where
  constants h := by simp [VEnv.empty] at h
  defeqs h := h.elim
  structEtas h := h.elim

/-- Adding the same constant to a larger environment stays larger. -/
theorem addConst_le_of_le {e₁ e₂ s₁ s₂ : VEnv} {n : Name} {ci : VConstant}
    (h₁ : e₁.addConst n ci = some s₁) (h₂ : e₂.addConst n ci = some s₂)
    (hle : e₁ ≤ e₂) : s₁ ≤ s₂ := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁
  · cases h₁
  split at h₂
  · cases h₂
  cases h₁
  cases h₂
  constructor
  · intro n' a h
    have h' : (if n = n' then some ci else e₁.constants n') = some a := h
    show (if n = n' then some ci else e₂.constants n') = some a
    by_cases hn : n = n'
    · rw [if_pos hn] at h' ⊢
      exact h'
    · rw [if_neg hn] at h' ⊢
      exact hle.constants h'
  · exact fun h => hle.defeqs h
  · exact fun h => hle.structEtas h

/-- Staging the same family list over a larger environment stays larger. -/
theorem stageInductiveTypes_le_of_le :
    ∀ (types : List VInductiveType) {e₁ e₂ s₁ s₂ : VEnv},
      e₁.stageInductiveTypes types = some s₁ →
      e₂.stageInductiveTypes types = some s₂ →
      e₁ ≤ e₂ → s₁ ≤ s₂
  | [], _, _, _, _, h₁, h₂, hle => by
    cases h₁; cases h₂; exact hle
  | ty :: types, e₁, e₂, s₁, s₂, h₁, h₂, hle => by
    rw [VEnv.stageInductiveTypes, List.foldlM_cons] at h₁ h₂
    rcases Option.bind_eq_some_iff.1 h₁ with ⟨t₁, ht₁, hrest₁⟩
    rcases Option.bind_eq_some_iff.1 h₂ with ⟨t₂, ht₂, hrest₂⟩
    exact stageInductiveTypes_le_of_le types hrest₁ hrest₂
      (addConst_le_of_le ht₁ ht₂ hle)

/-- Pointwise strengthening of a `Forall₂` witness. -/
theorem forall₂_imp {α β : Type _} {R S : α → β → Prop}
    (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (forall₂_imp H t)

theorem treeBlockEnv_le_d2BlockEnv : treeBlockEnv ≤ d2BlockEnv :=
  stageInductiveTypes_le_of_le treeDecl.types treeStage d1Env_stage
    empty_le_d1Env

/-- The block's semantic package, re-based from the empty environment onto
`d1Env`.  Only the staging equation is genuinely new; every other field is
the empty-environment field transported by monotonicity. -/
theorem d2BlockGenerationWF : TreeGen.WF d1Env d2BlockEnv where
  blockWF :=
    ⟨⟨d1Env_stage,
      forall₂_imp
        (fun _ _ h =>
          ⟨VEnv.IsDefEqU.mono empty_le_d1Env h.1,
            forall₂_imp
              (fun _ _ hc => VEnv.IsDefEqU.mono treeBlockEnv_le_d2BlockEnv hc)
              h.2⟩)
        treeNormalizationBlockWF.2⟩,
      VInductDecl.CheckedBlock.WF.mono empty_le_d1Env
        treeBlockGenerationWF.blockWF.2⟩
  resultLevelWF := treeBlockGenerationWF.resultLevelWF
  paramsTel := VEnv.TelDefEq.mono empty_le_d1Env treeBlockGenerationWF.paramsTel
  families := fun family hfamily =>
    VInductDecl.NormalizedFamily.WF.mono empty_le_d1Env
      (treeBlockGenerationWF.families family hfamily)
  constructors := fun constructor hconstructor =>
    VInductDecl.NormalizedBlockCtor.WF.mono treeBlockEnv_le_d2BlockEnv
      (treeBlockGenerationWF.constructors constructor hconstructor)

/-! ### The completed block transaction -/

theorem d2Env_isSome : (d1Env.addInductBlockGeneration TreeGen).isSome := by
  native_decide

/-- The complete D2 environment: the D1 environment followed by one checked
mutual inductive block declaration. -/
def d2Env : VEnv := (d1Env.addInductBlockGeneration TreeGen).get d2Env_isSome

theorem d1Env_addBlock :
    d1Env.addInductBlockGeneration TreeGen = some d2Env :=
  (Option.some_get d2Env_isSome).symm

theorem d2Env_ordered : d2Env.Ordered :=
  VEnv.addInductBlockGeneration_WF d1Env_ordered d2BlockGenerationWF
    d1Env_addBlock

/-- The block is a genuine declaration history step. -/
theorem d2Env_step : VDecl.WF d1Env (.induct treeDecl) d2Env :=
  .inductBlock d2BlockGenerationWF d1Env_addBlock

theorem d2Env_wf : d2Env.WF := by
  obtain ⟨ds, hds⟩ := d1Env_wf
  exact ⟨.induct treeDecl :: ds, .decl d2Env_step hds⟩

theorem d2Trace :
    Nonempty (VEnv.AddInductBlockGenerationTrace d1Env d2Env TreeGen) :=
  VEnv.addInductBlockGeneration_trace d1Env_addBlock

theorem d1Env_le_d2Env : d1Env ≤ d2Env := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.le

theorem d2Env_family_lookup {type : VInductiveType}
    (htype : type ∈ treeDecl.types) :
    d2Env.constants type.name = some type.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.family_lookup htype

theorem d2Env_ctor_lookup {constructor : VConstVal}
    (hconstructor : constructor ∈ treeDecl.blockConstructorConstants) :
    d2Env.constants constructor.name = some constructor.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.ctor_lookup hconstructor

theorem d2Env_rec_lookup {recursor : VConstVal}
    (hrecursor : recursor ∈ TreeGen.recursors) :
    d2Env.constants recursor.name = some recursor.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.rec_lookup hrecursor

theorem d2Env_rule_mem {rule : VDefEq}
    (hrule : rule ∈ TreeGen.generatedRules) : d2Env.defeqs rule := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.rule_mem hrule

/-- The registered defeqs of the block-extended environment, inverted
exactly: a generated block rule or an inherited D1 rule.  This is the landed
`addInductBlockGeneration_defeqs` instantiated at the live fixture. -/
theorem d2Env_defeqs_iff (df : VDefEq) :
    d2Env.defeqs df ↔ df ∈ TreeGen.generatedRules ∨ d1Env.defeqs df :=
  TreeGen.addInductBlockGeneration_defeqs d1Env_addBlock df

/-! ### Structure-eta transparency of the transaction

Neither phase of the block transaction touches the structure-eta registry. -/

theorem addConst_structEtas {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') {rule : VStructEta} :
    env'.structEtas rule ↔ env.structEtas rule := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · cases h
    exact Iff.rfl

theorem foldlM_addConst_structEtas {α : Type _} (name : α → Name)
    (ci : α → VConstant) :
    ∀ (xs : List α) {env env' : VEnv},
      xs.foldlM (fun env x => env.addConst (name x) (ci x)) env = some env' →
      ∀ {rule : VStructEta}, (env'.structEtas rule ↔ env.structEtas rule)
  | [], _, _, h, _ => by cases h; exact Iff.rfl
  | x :: xs, _, _, h, _ => by
    rw [List.foldlM_cons] at h
    rcases Option.bind_eq_some_iff.1 h with ⟨envx, hx, hrest⟩
    exact (foldlM_addConst_structEtas name ci xs hrest).trans
      (addConst_structEtas hx)

theorem foldl_addDefEq_structEtas :
    ∀ (dfs : List VDefEq) (env : VEnv) (rule : VStructEta),
      ((dfs.foldl VEnv.addDefEq env).structEtas rule ↔ env.structEtas rule)
  | [], _, _ => Iff.rfl
  | d :: dfs, env, rule =>
    (foldl_addDefEq_structEtas dfs (env.addDefEq d) rule).trans Iff.rfl

theorem d2Env_no_structEta (rule : VStructEta) : ¬d2Env.structEtas rule := by
  obtain ⟨trace⟩ := d2Trace
  intro h
  rw [← trace.addRules, foldl_addDefEq_structEtas] at h
  rw [foldlM_addConst_structEtas _ _ _ trace.addRecs,
    foldlM_addConst_structEtas _ _ _ trace.addCtors,
    foldlM_addConst_structEtas _ _ _ trace.addTypes] at h
  exact d1Env_no_structEta rule h

/-! ## D2 pattern layer

The block's own five iota rules are the `.rule` half of `AssembledPat`; they
must *not* appear in the `exts` list, whose members are required to be head
separated from every block rule.  The genuinely external extensions are the
three zero-universe definition rules inherited from D1. -/

/-- The `d0def` unfolding rule as a certified extension.  Its registered
tower is a bare constant, so the beta-collapsed match is the constant
pattern itself. -/
def d0DefExt : CertifiedExtension where
  df := d0DefVal.toDefEq
  pat := .defn d0DefVal.name
  rhs := .fixed d0DefVal.value d0DefClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

def d1MutAExt : CertifiedExtension where
  df := d1MutAVal.toDefEq
  pat := .defn d1MutAVal.name
  rhs := .fixed d1MutAVal.value d1MutAClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

def d1MutBExt : CertifiedExtension where
  df := d1MutBVal.toDefEq
  pat := .defn d1MutBVal.name
  rhs := .fixed d1MutBVal.value d1MutBClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

/-- The external extension list of the D2 assembly: exactly the D1
definition rules. -/
def d2Exts : List CertifiedExtension := [d0DefExt, d1MutAExt, d1MutBExt]

/-- Head separation of a definition extension from a generated iota rule.
The constructor-side obligation is vacuous: a `defn` pattern has no
constructor head. -/
theorem headSep_defn_iota {n R C : Name} {m k : Nat}
    (h1 : n ≠ R) (h2 : n ≠ C) :
    (SimplePattern.defn n).HeadSep (.iota R m C k) where
  symb_ne_symb := h1
  symb_ne_ctor := fun c hc => by cases hc; exact h2
  ctor_ne_symb := fun c hc => by simp at hc

/-- Head separation of two distinct definition extensions. -/
theorem headSep_defn_defn {n n' : Name} (h : n ≠ n') :
    (SimplePattern.defn n).HeadSep (.defn n') where
  symb_ne_symb := h
  symb_ne_ctor := fun c hc => by simp at hc
  ctor_ne_symb := fun c hc => by simp at hc

/-- Every D1 definition head is head separated from every rule of the
block. -/
theorem d2Ext_headSep_tree {n : Name}
    (h1 : n ≠ .str ``Tree "rec") (h2 : n ≠ .str ``TreeList "rec")
    (h3 : n ≠ ``Tree.leaf) (h4 : n ≠ ``Tree.node) (h5 : n ≠ ``Tree.branch)
    (h6 : n ≠ ``TreeList.nil) (h7 : n ≠ ``TreeList.cons)
    {constructor : NormalizedBlockCtor} (hc : constructor ∈ TreeGen.flatCtors) :
    (SimplePattern.defn n).HeadSep (TreeGen.rulePattern constructor) := by
  have hp : TreeGen.rulePattern constructor ∈
      TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
    List.mem_map_of_mem hc
  rw [treeRulePattern_inventory] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp <;> rw [hp]
  · exact headSep_defn_iota h1 h3
  · exact headSep_defn_iota h1 h4
  · exact headSep_defn_iota h1 h5
  · exact headSep_defn_iota h2 h6
  · exact headSep_defn_iota h2 h7

/-- The complete separation certificate for the D2 assembly: the block's
five generated rules unioned with the three inherited definition rules.
Every obligation is a literal name comparison, discharged by kernel
`decide`. -/
theorem d2ExtSeparation : TreeGen.ExtSeparation d2Exts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ext hm
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact trivial
  · rintro ext hm c hc
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      exact d2Ext_headSep_tree (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc
  · rintro e1 h1 e2 h2 hpat
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first
        | rfl
        | exact absurd hpat (by decide)
  · rintro e1 h1 e2 h2 hne
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact headSep_defn_defn (by decide)

/-- The complete D2 pattern inventory: the generated `Nat` rules inherited
from D0, and the assembled union of the new block's five generated rules
with the three inherited definition rules. -/
inductive D2Pat : (p : Pattern) → p.RHS × p.Check → Prop where
  | nat {p : Pattern} {r : p.RHS × p.Check} : NatPat p r → D2Pat p r
  | assembled {p : Pattern} {r : p.RHS × p.Check} :
      TreeGen.AssembledPat treeRuleClosure d2Exts p r → D2Pat p r

/-- Transport the complete D1 inventory into D2: the `Nat` rules stay
`IotaPat` members, and the three definition rules become extension members
of the assembly.  The payloads are literally the same terms. -/
theorem d1Pat_to_d2 {p : Pattern} {r : p.RHS × p.Check}
    (H : D1Pat p r) : D2Pat p r := by
  cases H with
  | old H =>
    cases H with
    | iota H => exact .nat H
    | defn =>
      exact .assembled (.ext d0DefExt (by simp [d2Exts]))
  | defnA => exact .assembled (.ext d1MutAExt (by simp [d2Exts]))
  | defnB => exact .assembled (.ext d1MutBExt (by simp [d2Exts]))

/-! ### Simple-pattern inventories and cross-block separation -/

def d2NatPatterns : List SimplePattern :=
  [.iota ``Nat.rec 3 ``Nat.zero 0, .iota ``Nat.rec 3 ``Nat.succ 1]

def d2AssembledPatterns : List SimplePattern :=
  [.iota (.str ``Tree "rec") 8 ``Tree.leaf 2,
   .iota (.str ``Tree "rec") 8 ``Tree.node 2,
   .iota (.str ``Tree "rec") 8 ``Tree.branch 2,
   .iota (.str ``TreeList "rec") 8 ``TreeList.nil 1,
   .iota (.str ``TreeList "rec") 8 ``TreeList.cons 3,
   .defn d0DefVal.name, .defn d1MutAVal.name, .defn d1MutBVal.name]

theorem natPat_inventory {p : Pattern} {r : p.RHS × p.Check} (H : NatPat p r) :
    ∃ sp ∈ d2NatPatterns, p = sp.toPattern := by
  rcases natPat_pattern H with hp | hp
  · exact ⟨_, by simp [d2NatPatterns], hp⟩
  · exact ⟨_, by simp [d2NatPatterns], hp⟩

theorem assembledPat_inventory {p : Pattern} {r : p.RHS × p.Check}
    (H : TreeGen.AssembledPat treeRuleClosure d2Exts p r) :
    ∃ sp ∈ d2AssembledPatterns, p = sp.toPattern := by
  cases H with
  | rule h =>
    cases h with
    | @mk i c hentry =>
      have hp : TreeGen.rulePattern c ∈
          TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
        List.mem_map_of_mem (List.mem_of_getElem? hentry)
      rw [treeRulePattern_inventory] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      refine ⟨TreeGen.rulePattern c, ?_, rfl⟩
      rcases hp with hp | hp | hp | hp | hp <;> rw [hp] <;>
        simp [d2AssembledPatterns]
  | ext ext hmem =>
    refine ⟨ext.pat, ?_, rfl⟩
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp [d2AssembledPatterns,
      d0DefExt, d1MutAExt, d1MutBExt]

/-- Cross-block head separation: every `Nat` rule pattern is head separated
from every member of the assembly. -/
theorem d2Nat_headSep_assembled {spn spa : SimplePattern}
    (hn : spn ∈ d2NatPatterns) (ha : spa ∈ d2AssembledPatterns) :
    spn.HeadSep spa := by
  simp only [d2NatPatterns, d2AssembledPatterns, List.mem_cons,
    List.not_mem_nil, or_false] at hn ha
  rcases hn with rfl | rfl <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact SimplePattern.HeadSep.iota_iota (by decide) (by decide)
          (by decide)
      | exact (headSep_defn_iota (by decide) (by decide)).symm

/-! ### The four `Params` non-overlap obligations

The same-block cases delegate to the landed laws: `IotaPat.pat_uniq` for the
`Nat` block and `AssembledPat.pat_uniq` (etc.) for the assembly.  Only the
*cross-block* cases are proved here, from the landed cross-term engine
`SimplePattern.HeadSep.inter_subpattern_none` and the two shape lemmas
below, which mirror the corresponding inlined cases of the landed union
proofs. -/

/-- Cross-block `pat_app_l_uniq`, for two head-separated simple patterns.
This is the inlined `(rule, ext)` case of `AssembledPat.pat_app_l_uniq`,
restated for two arbitrary head-separated simple patterns. -/
theorem simple_app_l_uniq {sp sp' : SimplePattern} {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases sp with
  | defn n => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R m C k =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := Subpattern.var_varN_const_le h₃
    cases sp' with
    | defn n' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' m' C' k' =>
      obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h'
      exact Pattern.varN_const_inter_of_ne_name
        hsep.symb_ne_symb.symm _ _

/-- Cross-block `pat_app_uniq`, for two head-separated simple patterns. -/
theorem simple_app_uniq {sp sp' : SimplePattern}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases sp with
  | defn n => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R m C k =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := h₃.varN_const_le
    cases sp' with
    | defn n' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' m' C' k' =>
      obtain ⟨-, rfl⟩ := RecursorIotaPattern.app_subpattern h'
      obtain ⟨j', -, rfl⟩ := h₃'.varN_const_le
      exact Pattern.varN_const_inter_of_ne_name
        (hsep.symb_ne_ctor C' rfl) _ _

theorem d2Pat_simple {p : Pattern} {r : p.RHS × p.Check}
    (H : D2Pat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | nat H =>
    exact VInductDecl.BlockGenerationChecked.IotaPat.pat_simple NatGeneration H
  | assembled H =>
    exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple TreeGen H

theorem d2Pat_uniq {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : D2Pat p₁ r) (H2 : D2Pat p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with
  | nat H1 =>
    cases H2 with
    | nat H2 =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
        H1 H2 H3 H4
    | assembled H2 =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H1
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H2
      rw [(d2Nat_headSep_assembled hn ha).inter_subpattern_none H3] at H4
      cases H4
  | assembled H1 =>
    cases H2 with
    | nat H2 =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H1
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H2
      rw [((d2Nat_headSep_assembled hn ha).symm).inter_subpattern_none H3]
        at H4
      cases H4
    | assembled H2 =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_uniq TreeGen
        d2ExtSeparation H1 H2 H3 H4

theorem d2Pat_app_l {p : Pattern} {r : p.RHS × p.Check}
    {p₁ p₂ p₃ p₄ : Pattern}
    (H : D2Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨sp, rfl⟩ := d2Pat_simple H
  exact SimplePattern.toPattern_app_l h

theorem d2Pat_app_l_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : D2Pat p r) (H' : D2Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with
  | nat H =>
    cases H' with
    | nat H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l_uniq
        NatGeneration H H' h h' h₃
    | assembled H' =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H'
      exact simple_app_l_uniq (d2Nat_headSep_assembled hn ha) h h' h₃
  | assembled H =>
    cases H' with
    | nat H' =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H'
      exact simple_app_l_uniq ((d2Nat_headSep_assembled hn ha).symm) h h' h₃
    | assembled H' =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l_uniq
        TreeGen d2ExtSeparation H H' h h' h₃

theorem d2Pat_app_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : D2Pat p r) (H' : D2Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases H with
  | nat H =>
    cases H' with
    | nat H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_uniq
        NatGeneration H H' h h' h₃ h₃'
    | assembled H' =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H'
      exact simple_app_uniq (d2Nat_headSep_assembled hn ha) h h' h₃ h₃'
  | assembled H =>
    cases H' with
    | nat H' =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H'
      exact simple_app_uniq ((d2Nat_headSep_assembled hn ha).symm) h h' h₃ h₃'
    | assembled H' =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_uniq
        TreeGen d2ExtSeparation H H' h h' h₃ h₃'

/-! ### The classification table

The block contributes two family heads, five constructor heads, and two
recursor heads.  Major arity 8 (one parameter, two motives, five minors, no
indices) gives each recursor the symbol arity 9 demanded by `Pattern.WF` at
the top of an iota pattern. -/

def d2Classify (n : Name) : Option Classification :=
  if n = ``Tree then some (.indTy 1)
  else if n = ``TreeList then some (.indTy 1)
  else if n = ``Tree.leaf then some (.ctor 2)
  else if n = ``Tree.node then some (.ctor 2)
  else if n = ``Tree.branch then some (.ctor 2)
  else if n = ``TreeList.nil then some (.ctor 1)
  else if n = ``TreeList.cons then some (.ctor 3)
  else if n = .str ``Tree "rec" then some (.symb 9)
  else if n = .str ``TreeList "rec" then some (.symb 9)
  else d1Classify n

/-- The D1 table is the restriction of the D2 table: every name it
classifies is distinct from all nine block heads. -/
theorem d1Classify_agrees {c : Name} {cl : Classification}
    (H : d1Classify c = some cl) : d2Classify c = some cl := by
  have hcases : c = d1MutAVal.name ∨ c = d1MutBVal.name ∨
      c = d0DefVal.name ∨ c = ``Nat ∨ c = ``Nat.zero ∨ c = ``Nat.succ ∨
      c = ``Nat.rec := by
    by_cases h1 : c = d1MutAVal.name
    · exact .inl h1
    by_cases h2 : c = d1MutBVal.name
    · exact .inr (.inl h2)
    by_cases h3 : c = d0DefVal.name
    · exact .inr (.inr (.inl h3))
    by_cases h4 : c = ``Nat
    · exact .inr (.inr (.inr (.inl h4)))
    by_cases h5 : c = ``Nat.zero
    · exact .inr (.inr (.inr (.inr (.inl h5))))
    by_cases h6 : c = ``Nat.succ
    · exact .inr (.inr (.inr (.inr (.inr (.inl h6)))))
    by_cases h7 : c = ``Nat.rec
    · exact .inr (.inr (.inr (.inr (.inr (.inr h7)))))
    simp [d1Classify, d0Classify, natClassify, h1, h2, h3, h4, h5, h6,
      h7] at H
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [d2Classify, d0DefVal, d1MutAVal, d1MutBVal] using H

theorem d1PatWF_lift {p : Pattern} {top : Bool} {extra : Nat}
    (H : p.WF d1Classify top extra) : p.WF d2Classify top extra := by
  induction p generalizing top extra with
  | const c => exact d1Classify_agrees H
  | var f ih => exact ih H
  | app f a ihf iha => exact ⟨ihf H.1, iha H.2⟩

theorem d2Pat_wf {p : Pattern} {r : p.RHS × p.Check}
    (H : D2Pat p r) : p.WF d2Classify := by
  cases H with
  | nat H => exact d1PatWF_lift (d1Pat_wf (.old (.iota H)))
  | assembled H =>
    cases H with
    | rule h =>
      cases h with
      | @mk i c hentry =>
        have hp : TreeGen.rulePattern c ∈
            TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
          List.mem_map_of_mem (List.mem_of_getElem? hentry)
        rw [treeRulePattern_inventory] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        show ((TreeGen.rulePattern c).toPattern).WF d2Classify
        rcases hp with hp | hp | hp | hp | hp <;> rw [hp] <;>
          simp [SimplePattern.toPattern, Pattern.varN, Pattern.WF, d2Classify]
    | ext ext hmem =>
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact d1PatWF_lift (d1Pat_wf (.old .defn))
      · exact d1PatWF_lift (d1Pat_wf .defnA)
      · exact d1PatWF_lift (d1Pat_wf .defnB)

/-- The complete D2 structural instance: the D1 inventory extended by a live
mutual inductive block, over the block-extended environment. -/
def d2Params (univs : Nat) : Params where
  env := d2Env
  henv := d2Env_ordered
  univs := univs
  Pat := D2Pat
  classify := d2Classify
  pat_simple := d2Pat_simple
  pat_wf := d2Pat_wf
  pat_uniq := d2Pat_uniq
  pat_app_l := d2Pat_app_l
  pat_app_l_uniq := d2Pat_app_l_uniq
  pat_app_uniq := d2Pat_app_uniq

/-! ## Semantic-layer fragments

`Params.StructureEtaSound` and `Params.Semantic.iotaRule` are the two
semantic obligations that are purely registry-level: neither needs a typed
reduction site.  They are delivered here for the complete inventory. -/

theorem d2StructureEtaSound (univs : Nat) :
    @Params.StructureEtaSound (d2Params univs) := by
  letI : Params := d2Params univs
  intro rule levels Gamma params major hreg
  exact (d2Env_no_structEta rule hreg).elim

/-- Every generated rule of the block is registered in `d2Env`. -/
theorem treeRule_registered {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    d2Env.defeqs (TreeGen.rule i constructor) := by
  refine d2Env_rule_mem ?_
  have : (constructor, i) ∈ TreeGen.flatCtors.zipIdx := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  simpa only [VInductDecl.BlockGenerationChecked.generatedRules,
    List.mem_map] using ⟨_, this, rfl⟩

/-- The RHS template of a block rule is the registered right tower applied
to the ordered capture list. -/
theorem treeRuleRHS_tower {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    TreeGen.ruleRHS treeRuleClosure hentry =
      Pattern.RHS.appN
        (.fixed (TreeGen.rule i constructor).rhs
          (treeRuleClosure.rhs_closed hentry))
        (TreeGen.captureArgs constructor) := rfl

/-- The ordered capture inventory of one block rule: the recursor side's
parameter, motives, and minors, then the constructor's fields. -/
def treeCapturePaths (constructor : NormalizedBlockCtor) :
    List (((TreeGen.rulePattern constructor).toPattern).Path) :=
  ((Pattern.varNPaths (.const (TreeGen.ruleRecName constructor))
      (TreeGen.ruleMajorArity constructor)).take
    (treeDecl.nparams + TreeGen.familyCount + TreeGen.minorCount)).map Sum.inl ++
  ((Pattern.varNPaths (.const constructor.ctor.raw.name)
      (TreeGen.ruleArgArity constructor)).drop treeDecl.nparams).map Sum.inr

theorem treeCapturePaths_map_var (constructor : NormalizedBlockCtor) :
    (treeCapturePaths constructor).map (fun path => .var path) =
      TreeGen.captureArgs constructor := by
  simp [treeCapturePaths, VInductDecl.BlockGenerationChecked.captureArgs,
    List.map_map, Function.comp_def]

/-- The `Pattern.IotaRule.rhsTower` shape for a block rule: the registered
right tower applied to the ordered capture path list. -/
theorem treeRuleRHS_capture_tower {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    TreeGen.ruleRHS treeRuleClosure hentry =
      Pattern.RHS.appN
        (.fixed (TreeGen.rule i constructor).rhs
          (treeRuleClosure.rhs_closed hentry))
        ((treeCapturePaths constructor).map fun path => .var path) :=
  (treeRuleRHS_tower hentry).trans (by rw [treeCapturePaths_map_var])

/-- Inversion for the assembly at a *variable* pattern.  `cases` cannot be
used at a concrete iota pattern — the block half's index
`(rulePattern c).toPattern` is a stuck `varN` tower — so this is the
`AssembledPat` counterpart of `IotaPat.recover`. -/
theorem assembledPat_cases {p : Pattern} {r : p.RHS × p.Check}
    (H : TreeGen.AssembledPat treeRuleClosure d2Exts p r) :
    (∃ (i : Nat) (c : NormalizedBlockCtor)
        (h : TreeGen.flatCtors[i]? = some c),
        p = (TreeGen.rulePattern c).toPattern ∧
          r ≍ (TreeGen.ruleRHS treeRuleClosure h,
            TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? h))) ∨
      (∃ ext ∈ d2Exts, p = ext.pat.toPattern) := by
  cases H with
  | rule h =>
    cases h with
    | @mk i c hentry => exact .inl ⟨i, c, hentry, rfl, HEq.rfl⟩
  | ext ext hmem => exact .inr ⟨ext, hmem, rfl⟩

/-- `Params.Semantic.iotaRule` for the complete D2 inventory: every iota
pattern in `Pat` recovers its unique registered tower and ordered capture
inventory.  This field is purely registry-level — it needs no typed
reduction site — and is therefore delivered for both blocks. -/
theorem d2IotaRule_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d2Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    Nonempty (@Pattern.IotaRule (d2Params univs) rec major ctor arity r) := by
  letI : Params := d2Params univs
  change D2Pat _ _ at H
  cases H with
  | nat H =>
    let oldRule := d1IotaRule univs (D1Pat.old (D0Pat.iota H))
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    exact ⟨{
      pat := D2Pat.nat H
      df := df
      registered := d1Env_le_d2Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }⟩
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      exact ⟨{
        pat := D2Pat.assembled (.rule (.mk hentry))
        df := TreeGen.rule i c
        registered := treeRule_registered hentry
        rhsClosed := treeRuleClosure.rhs_closed hentry
        capturePaths := treeCapturePaths c
        rhsTower := treeRuleRHS_capture_tower hentry }⟩
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

noncomputable def d2IotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d2Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (d2Params univs) rec major ctor arity r :=
  Classical.choice (d2IotaRule_nonempty univs H)

/-! ## Endpoints and pins -/

/-- The block-extended environment is well formed, ordered, and registers
exactly the block's generated rules over D1's. -/
theorem d2Env_live :
    d2Env.WF ∧ d2Env.Ordered ∧
      ∀ df, d2Env.defeqs df ↔
        df ∈ TreeGen.generatedRules ∨ d1Env.defeqs df :=
  ⟨d2Env_wf, d2Env_ordered, d2Env_defeqs_iff⟩

/-! ## What remains for the D2 `Params.Semantic` bridge

The two forcing observations below make the residual obligation exact.
Every generated rule of the live block is simultaneously a `Pat` member and
a registered defeq of `d2Env`, so a `Params.Semantic (d2Params univs)` value
must supply, for each of the five block rules,

* `Params.Semantic.iotaSite` — an evidence-rich reduction-site certificate,
  and
* `Params.Semantic.registered` — the strong equality between the two
  registered towers.

Neither is derivable from pattern membership; both are the per-rule replay
that D0 performed for the two `Nat` rules (`SExprParamsD0.lean:1954-6829`,
about 640 lines per rule) and D1 re-performed against the extended
environment (`SExprParamsD1.lean:1930-2611`).  Unlike D1's quotient
obstruction this is *not* an interface defect: the block is non-`Prop`, its
constructors are ordinary, and nothing in `CtorBundle` disqualifies it.  The
gap is the volume of a five-rule replay over an 8-argument major with two
universe parameters, plus the D1→D2 transport functor
(`SExprParamsD1.lean:484-1107`) that `Params.Semantic.ctor`/`.defn` need in
order to move the inherited derivations into the new instance.  See the D3
notes in the session report. -/

/-- Forcing observation 1: every generated rule of the live block is a
pattern member of the D2 registry. -/
theorem d2Pat_block_rule {i : Nat} {c : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some c) :
    D2Pat ((TreeGen.rulePattern c).toPattern)
      (TreeGen.ruleRHS treeRuleClosure hentry,
        TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry)) :=
  .assembled (.rule (.mk hentry))

/-- Forcing observation 2: the same rule is a registered defeq of the live
environment, so `Params.Semantic.registered` is obliged at it. -/
theorem d2Registered_obligation {i : Nat} {c : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some c) :
    d2Env.defeqs (TreeGen.rule i c) ∧
      D2Pat ((TreeGen.rulePattern c).toPattern)
        (TreeGen.ruleRHS treeRuleClosure hentry,
          TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry)) :=
  ⟨treeRule_registered hentry, d2Pat_block_rule hentry⟩

/-! ## Axiom closures

The pattern layer — including all four union-level non-overlap laws, this
file's first live consumption of `Theory/Typing/InductivePatternEnv.lean` —
stays on the standard logical baseline with kernel `decide` only.  The
environment layer inherits D1's named concrete `native_decide` freshness
observations and adds three of its own; it carries no `sorryAx`, so the live
block-inductive environment is admission-free. -/

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2ExtSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2ExtSeparation

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_uniq

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_app_l_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_app_l_uniq

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_app_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_app_uniq

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Env_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Env_wf

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Params' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Params

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2StructureEtaSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2StructureEtaSound

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2IotaRule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaRule

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Registered_obligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 d2Env_isSome._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Registered_obligation

end ParamsD2
end SExpr
end Lean4Lean
