import Lean4Lean.Theory.Typing.Strong

/-! # Theory encodings of Lean literals and primitive reflection

This file contains only `VExpr`/`VEnv` semantics.  Traversal of `Lean.Expr`
and `Literal.toConstructor` belongs to the Verify translation layer.
-/

namespace Lean4Lean
open Lean

def VEnv.ContainsLits (env : VEnv) : Literal → Prop
  | .natVal _ => env.contains ``Nat
  | .strVal _ => env.contains ``Char.ofNat ∧ env.contains ``String.ofList

def VExpr.bool : VExpr := .const ``Bool []
def VExpr.boolTrue : VExpr := .const ``Bool.true []
def VExpr.boolFalse : VExpr := .const ``Bool.false []
def VExpr.boolLit : Bool → VExpr
  | .false => .boolFalse
  | .true => .boolTrue

def VExpr.nat : VExpr := .const ``Nat []
def VExpr.natZero : VExpr := .const ``Nat.zero []
def VExpr.natSucc : VExpr := .const ``Nat.succ []
def VExpr.natLit : Nat → VExpr
  | 0 => .natZero
  | n+1 => .app .natSucc (.natLit n)

def VExpr.char : VExpr := .const ``Char []
def VExpr.string : VExpr := .const ``String []
def VExpr.stringOfList : VExpr := .const ``String.ofList []
def VExpr.listChar : VExpr := .app (.const ``List [.zero]) .char
def VExpr.listCharNil : VExpr := .app (.const ``List.nil [.zero]) .char
def VExpr.listCharCons : VExpr := .app (.const ``List.cons [.zero]) .char
def VExpr.charOfNat : VExpr := .const ``Char.ofNat []
def VExpr.listCharLit : List Char → VExpr
  | [] => .listCharNil
  | a :: as =>
    .app (.app .listCharCons (.app .charOfNat (.natLit a.toNat))) (.listCharLit as)

def VExpr.trLiteral : Literal → VExpr
  | .natVal n => .natLit n
  | .strVal s => .app .stringOfList (.listCharLit s.toList)

def VEnv.ReflectsNatNatNat (env : VEnv) (fc : Name) (f : Nat → Nat → Nat) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 []
    (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.natLit (f a b))

def VEnv.ReflectsNatNatBool (env : VEnv) (fc : Name) (f : Nat → Nat → Bool) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 []
    (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.boolLit (f a b))

structure VEnv.HasPrimitives (env : VEnv) : Prop where
  bool : env.contains ``Bool → env.contains ``Bool.false ∧ env.contains ``Bool.true
  boolFalse : env.constants ``Bool.false = some ci → ci = { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true = some ci → ci = { uvars := 0, type := .bool }
  nat : env.contains ``Nat → env.contains ``Nat.zero ∧ env.contains ``Nat.succ
  natZero : env.constants ``Nat.zero = some ci → ci = { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ = some ci →
    ci = { uvars := 0, type := .forallE .nat .nat }
  natAdd : env.ReflectsNatNatNat ``Nat.add Nat.add
  natSub : env.ReflectsNatNatNat ``Nat.sub Nat.sub
  natMul : env.ReflectsNatNatNat ``Nat.mul Nat.mul
  natPow : env.ReflectsNatNatNat ``Nat.pow Nat.pow
  natGcd : env.ReflectsNatNatNat ``Nat.gcd Nat.gcd
  natMod : env.ReflectsNatNatNat ``Nat.mod Nat.mod
  natDiv : env.ReflectsNatNatNat ``Nat.div Nat.div
  natBEq : env.ReflectsNatNatBool ``Nat.beq Nat.beq
  natBLE : env.ReflectsNatNatBool ``Nat.ble Nat.ble
  natLAnd : env.ReflectsNatNatNat ``Nat.land Nat.land
  natLOr : env.ReflectsNatNatNat ``Nat.lor Nat.lor
  natXor : env.ReflectsNatNatNat ``Nat.xor Nat.xor
  natShiftLeft : env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft
  natShiftRight : env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight
  charOfNat : env.constants ``Char.ofNat = some ci →
    ci = { uvars := 0, type := .forallE .nat .char }
  stringOfList : env.constants ``String.ofList = some ci →
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem VEnv.ContainsLits.mono : ∀ {l}, env.ContainsLits l → env'.ContainsLits l
  | .natVal _, ⟨_, H⟩ => ⟨_, henv.constants H⟩
  | .strVal _, ⟨⟨_, H1⟩, ⟨_, H2⟩⟩ =>
    ⟨⟨_, henv.constants H1⟩, ⟨_, henv.constants H2⟩⟩

@[simp] theorem VExpr.instL_boolFalse : VExpr.boolFalse.instL ls = VExpr.boolFalse := by
  simp [boolFalse, instL]

@[simp] theorem VExpr.instL_boolTrue : VExpr.boolTrue.instL ls = VExpr.boolTrue := by
  simp [boolTrue, instL]

@[simp] theorem VExpr.instL_boolLit : (VExpr.boolLit b).instL ls = VExpr.boolLit b := by
  cases b <;> simp [boolLit]

@[simp] theorem VExpr.liftN_boolLit : (VExpr.boolLit b).liftN n k = VExpr.boolLit b := by
  cases b <;> rfl

@[simp] theorem VExpr.lift'_boolLit : (VExpr.boolLit b).lift' ρ = VExpr.boolLit b := by
  cases b <;> rfl

@[simp] theorem VExpr.inst_boolLit : (VExpr.boolLit b).inst e k = VExpr.boolLit b := by
  cases b <;> rfl

@[simp] theorem VExpr.instL_natZero : VExpr.natZero.instL ls = .natZero := by
  simp [natZero, instL]

@[simp] theorem VExpr.instL_natSucc : VExpr.natSucc.instL ls = .natSucc := by
  simp [natSucc, instL]

@[simp] theorem VExpr.instL_natLit : (VExpr.natLit n).instL ls = VExpr.natLit n := by
  induction n <;> simp [*, natLit, instL]

@[simp] theorem VExpr.liftN_natLit : (VExpr.natLit a).liftN n k = VExpr.natLit a := by
  induction a <;> simp [natLit, natZero, natSucc, VExpr.liftN, *]

@[simp] theorem VExpr.lift'_natLit : (VExpr.natLit a).lift' ρ = VExpr.natLit a := by
  induction a <;> simp [natLit, natZero, natSucc, VExpr.lift', *]

@[simp] theorem VExpr.inst_natLit : (VExpr.natLit a).inst e k = VExpr.natLit a := by
  induction a <;> simp [natLit, natZero, natSucc, VExpr.inst, *]

@[simp] theorem VExpr.liftN_listCharLit :
    (VExpr.listCharLit cs).liftN n k = VExpr.listCharLit cs := by
  induction cs <;>
    simp [listCharLit, listCharNil, listCharCons, char, charOfNat, VExpr.liftN, *]

@[simp] theorem VExpr.lift'_listCharLit :
    (VExpr.listCharLit cs).lift' ρ = VExpr.listCharLit cs := by
  induction cs <;>
    simp [listCharLit, listCharNil, listCharCons, char, charOfNat, VExpr.lift', *]

@[simp] theorem VExpr.inst_listCharLit :
    (VExpr.listCharLit cs).inst e k = VExpr.listCharLit cs := by
  induction cs <;>
    simp [listCharLit, listCharNil, listCharCons, char, charOfNat, VExpr.inst, *]

@[simp] theorem VExpr.instL_listCharLit :
    (VExpr.listCharLit cs).instL ls = VExpr.listCharLit cs := by
  induction cs <;>
    simp [listCharLit, listCharNil, listCharCons, char, charOfNat,
      VExpr.instL, VLevel.inst, *]

@[simp] theorem VExpr.liftN_trLiteral :
    (VExpr.trLiteral l).liftN n k = VExpr.trLiteral l := by
  cases l <;> simp [trLiteral, stringOfList, VExpr.liftN]

@[simp] theorem VExpr.lift'_trLiteral :
    (VExpr.trLiteral l).lift' ρ = VExpr.trLiteral l := by
  cases l <;> simp [trLiteral, stringOfList, VExpr.lift']

@[simp] theorem VExpr.inst_trLiteral :
    (VExpr.trLiteral l).inst e k = VExpr.trLiteral l := by
  cases l <;> simp [trLiteral, stringOfList, VExpr.inst]

@[simp] theorem VExpr.instL_trLiteral :
    (VExpr.trLiteral l).instL ls = VExpr.trLiteral l := by
  cases l <;> simp [trLiteral, stringOfList, VExpr.instL]

theorem VEnv.HasPrimitives.nat_of_charOfNat (wf : Ordered env)
    (henv : env.HasPrimitives) (H : env.contains ``Char.ofNat) : env.contains ``Nat := by
  let ⟨_, H⟩ := H
  have ⟨_, H⟩ := wf.constWF (henv.charOfNat H ▸ H)
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv wf
  let ⟨_, H, _⟩ := H.const_inv (Γ := []) wf (by trivial)
  exact ⟨_, H⟩

end Lean4Lean
