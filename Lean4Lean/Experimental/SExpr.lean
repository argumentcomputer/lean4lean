import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean
open Lean4Lean

inductive Classification where
  | ctor (arity : Nat)
  | etaCtor (params args : Nat)
  | symb (arity : Nat)
  | indTy (arity : Nat)

def Classification.arity : Classification → Nat
  | .ctor k | .symb k | .indTy k => k
  | .etaCtor p a => p + a

def Pattern.WF (cl : Name → Option Classification) :
    Pattern → (top : Bool := true) → (extra : Nat := 0) → Prop
  | .const c, top, n => cl c = some (if top then .symb n else .ctor n)
  | .var p, top, n => WF cl p top (n + 1)
  | .app p p', top, n => WF cl p top (n + 1) ∧ WF cl p' false

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  -- pat_wf : Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
  --   r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  -- pat_app_r_arity : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Arity (.const c) n p₂ → Arity (.const c) n' p₂' → n = n'
  -- extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
  --   ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2 ∧
  --   df.rhs.instL ls = r.1.apply m1 m2
open Params
variable [Params]

/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.WF univs ∧ l.eval = f }

namespace SLevel

def zero : SLevel := ⟨_, .zero, ⟨⟩, rfl⟩

def mk (l : VLevel) : SLevel := if h : l.WF univs then ⟨_, l, h, rfl⟩ else .zero

/-- Choose a well-formed syntactic representative of a semantic level. -/
noncomputable def reify (l : SLevel) : VLevel := Classical.choose l.2

theorem reify_wf (l : SLevel) : (reify l).WF univs :=
  (Classical.choose_spec l.2).1

theorem reify_eval (l : SLevel) : (reify l).eval = l.1 :=
  (Classical.choose_spec l.2).2

theorem mk_of_wf (h : l.WF univs) :
    mk l = (⟨_, l, h, rfl⟩ : SLevel) := by
  have hm : mk l = if h' : l.WF univs then
      (⟨_, l, h', rfl⟩ : SLevel) else SLevel.zero := rfl
  rw [hm]
  exact dif_pos h

@[simp] theorem mk_reify (l : SLevel) : mk (reify l) = l := by
  rw [mk_of_wf (reify_wf l)]
  apply Subtype.ext
  exact reify_eval l

theorem mk_eq (hl : l.WF univs) (hl' : l'.WF univs) (h : l ≈ l') : mk l = mk l' := by
  rw [mk_of_wf hl, mk_of_wf hl']
  apply Subtype.ext
  exact VLevel.equiv_def'.1 h

@[simp] theorem mk_zero : mk .zero = zero := by
  apply Subtype.ext
  rfl

theorem mk_val (h : l.WF univs) : (mk l).1 = l.eval := by rw [mk_of_wf h]

def succ (l : SLevel) : SLevel :=
  ⟨fun v => l.1 v + 1, let ⟨u, h1, h2⟩ := l.2; ⟨u.succ, h1, h2 ▸ rfl⟩⟩

def max (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => (l₁.1 v).max (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.max v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

def imax (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => Lean.Nat.imax (l₁.1 v) (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.imax v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

@[simp] theorem mk_succ (h : l.WF univs) : mk l.succ = succ (mk l) := by
  have hs : l.succ.WF univs := h
  rw [mk_of_wf hs, mk_of_wf h]; apply Subtype.ext; rfl

@[simp] theorem mk_max (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.max l₁ l₂) = max (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.max l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

@[simp] theorem mk_imax (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.imax l₁ l₂) = imax (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.imax l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

def inst (ls : List SLevel) (l : SLevel) : SLevel := by
  refine ⟨fun v => l.1 (ls.map (·.1 v)), ?_⟩
  simp [funext_iff]
  have ⟨ls', h3⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a l ih =>
      let ⟨l', h1, h2⟩ := a.2; let ⟨ls', h3⟩ := ih
      exact ⟨l'::ls', .cons ⟨h1, h2⟩ h3⟩
  have ⟨l', h1, h2⟩ := l.2
  refine ⟨l'.inst ls', VLevel.WF.inst fun _ h => ?_, fun v => ?_⟩
  · let ⟨_, h⟩ := h3.forall_exists_l _ h; exact h.2.1
  · simp [VLevel.eval_inst, ← h2]; congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h3.imp fun _ _ h => congrFun h.2 _

/-- Instantiate a syntactic level directly into semantic levels. Unlike `inst ls (mk l)`,
this does not require `l` to be well-formed in the ambient universe context. -/
def instV (ls : List SLevel) (l : VLevel) : SLevel := by
  refine ⟨fun v => l.eval (ls.map (·.1 v)), ?_⟩
  have ⟨ls', h⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a ls ih =>
      let ⟨l', h1, h2⟩ := a.2
      let ⟨ls', ih⟩ := ih
      exact ⟨l' :: ls', .cons ⟨h1, h2⟩ ih⟩
  refine ⟨l.inst ls', VLevel.WF.inst fun _ hl => ?_, ?_⟩
  · let ⟨_, hl⟩ := h.forall_exists_l _ hl; exact hl.2.1
  · funext v
    simp only [VLevel.eval_inst]
    congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun _ _ hl => congrFun hl.2 _

theorem instV_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    instV (ls.map mk) l = mk (l.inst ls) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval ((ls.map mk).map fun u => u.1 ns) = l.eval (ls.map (VLevel.eval ns))
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact congrFun (mk_val (hls u hu)) ns

theorem mk_inst (hl : l.WF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (l.inst ls) = inst (ls.map mk) (mk l) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval (ls.map (VLevel.eval ns)) = (mk l).1 ((ls.map mk).map fun u => u.1 ns)
  rw [congrFun (mk_val hl) _]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact (congrFun (mk_val (hls u hu)) ns).symm

theorem map_mk_eq (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (h : List.Forall₂ (fun l l' => l ≈ l') ls ls') :
    ls.map mk = ls'.map mk := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [List.map_cons]
    rw [mk_eq (hls _ (by simp)) (hls' _ (by simp)) h,
      ih (fun _ hu => hls _ (by simp [hu])) (fun _ hu => hls' _ (by simp [hu]))]

end SLevel

inductive SExpr where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | app (f a : SExpr)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : SExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : SExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : SExpr} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : SExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

/-- Choose a well-formed syntactic representative of a semantic expression. -/
noncomputable def reify : SExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u.reify
  | .const c us => .const c (us.map SLevel.reify)
  | .app fn arg => .app fn.reify arg.reify
  | .lam ty body => .lam ty.reify body.reify
  | .forallE ty body => .forallE ty.reify body.reify

@[simp] theorem mk_reify : ∀ e : SExpr, mk e.reify = e
  | .bvar _ => rfl
  | .sort _ => by simp [reify, mk]
  | .const c us => by
    simp only [reify, mk, List.map_map]
    congr 1
    exact List.map_id''' us fun u _ => SLevel.mk_reify u
  | .app f a => by simp [reify, mk, mk_reify f, mk_reify a]
  | .lam A e => by simp [reify, mk, mk_reify A, mk_reify e]
  | .forallE A B => by simp [reify, mk, mk_reify A, mk_reify B]

theorem reify_levelWF : ∀ e : SExpr, e.reify.LevelWF univs
  | .bvar _ => trivial
  | .sort u => u.reify_wf
  | .const _ us => by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨u, _, rfl⟩ := hl
    exact u.reify_wf
  | .app f a => ⟨reify_levelWF f, reify_levelWF a⟩
  | .lam A e => ⟨reify_levelWF A, reify_levelWF e⟩
  | .forallE A B => ⟨reify_levelWF A, reify_levelWF B⟩

/-- Translate an expression while instantiating its universe parameters. -/
def mkInst (ls : List SLevel) : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.instV ls u)
  | .const c us => .const c (us.map (.instV ls))
  | .app fn arg => .app (mkInst ls fn) (mkInst ls arg)
  | .lam ty body => .lam (mkInst ls ty) (mkInst ls body)
  | .forallE ty body => .forallE (mkInst ls ty) (mkInst ls body)

@[simp] theorem mkInst_lift' : mkInst ls (e.lift' ρ) = (mkInst ls e).lift' ρ := by
  induction e generalizing ρ <;> simp [VExpr.lift', mkInst, *]

theorem _root_.Lean4Lean.VExpr.ClosedN.mkInstS : ∀ {e : VExpr},
    e.ClosedN k → (mkInst ls e).ClosedN k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkInstS, h.2.mkInstS⟩

theorem mkInst_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    mkInst (ls.map SLevel.mk) e = mk (e.instL ls) := by
  induction e with
  | bvar => rfl
  | sort u => exact congrArg SExpr.sort (SLevel.instV_map_mk hls)
  | const c us =>
    simp only [mkInst, VExpr.instL, mk, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.instV_map_mk hls
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [mkInst, VExpr.instL, mk]
    rw [ihf, iha]

@[simp] theorem mk_lift' : ∀ {e : VExpr}, mk (e.lift' ρ) = (mk e).lift' ρ
  | .bvar .. | .sort .. | .const .. => rfl
  | .app .. | .lam .. | .forallE .. => by simp [VExpr.lift', mk, mk_lift']

@[simp] theorem mk_lift {e : VExpr} : mk e.lift = (mk e).lift := by
  rw [VExpr.lift_eq_lift']
  exact mk_lift'

theorem mk_instL {e : VExpr} {ls : List VLevel}
    (he : e.LevelWF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (e.instL ls) = (mk e).instL (ls.map SLevel.mk) := by
  induction e with
  | bvar => rfl
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    rw [ihf he.1, iha he.2]
  | sort u =>
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    exact congrArg SExpr.sort (SLevel.mk_inst he hls)
  | const c us =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, mk, instL, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.mk_inst (he u hu) hls

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩

@[reducible] def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : SExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : SExpr) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : SExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.Lean4Lean.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

def mkSubst (σ : VExpr.Subst) : Subst := fun i => mk (σ i)

@[simp] theorem mkSubst_lift : mkSubst σ.lift = (mkSubst σ).lift := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mk_lift

@[simp] theorem mk_subst : mk (e.subst σ) = (mk e).subst (mkSubst σ) := by
  induction e generalizing σ with
  | bvar => rfl
  | sort | const => rfl
  | app f a ihf iha => simp only [VExpr.subst, mk, subst, ihf, iha]
  | lam A e ihA ihe | forallE A e ihA ihe =>
    simp only [VExpr.subst, mk, subst, ihA, ihe, mkSubst_lift]

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : SExpr} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : SExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : SExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : SExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, SExpr.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : SExpr} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : SExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, SExpr.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : SExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, SExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def inst (e a : SExpr) : SExpr := e.subst (.one a)

@[simp] theorem mkSubst_one : mkSubst (VExpr.Subst.one a) = Subst.one (mk a) := by
  funext i
  cases i <;> rfl

@[simp] theorem mk_instExpr : mk (e.inst a) = (mk e).inst (mk a) := by
  rw [VExpr.inst_eq, inst, mk_subst, mkSubst_one]

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv _ ρ) j

theorem skips_inter {e : SExpr} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : SExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : SExpr) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : SExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : SExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [SExpr.inst, SExpr.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, SExpr.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← SExpr.inst, lift_inst]; rfl

theorem inst_lift_cons {e : SExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [SExpr.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, SExpr.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List SExpr → List SExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact SExpr.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List SExpr → List SExpr → Lift → List SExpr → Lift → List SExpr → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : SExpr} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, SExpr.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

inductive _root_.Lean4Lean.Pattern.MatchesS :
    (p : Pattern) → SExpr → List SLevel → (p.Path → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) ls nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

/-- A constant application spine is matched by the corresponding `varN`
pattern.  This is the SExpr-side constructor used when a logical-relation
head witness exposes a recursor or constructor spine. -/
theorem _root_.Lean4Lean.Pattern.varN_const_matchesS
    (c : Name) (ls : List SLevel) (args : List SExpr) :
    ∃ m2, (Pattern.varN (.const c) args.length).MatchesS
      (args.foldr (fun a f => f.app a) (.const c ls)) ls m2 := by
  induction args with
  | nil =>
    refine ⟨nofun, ?_⟩
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [List.length_nil, Pattern.varN, List.foldr_nil]
    congr 1
    funext path
    exact Empty.elim path
  | cons a args ih =>
    obtain ⟨m2, hm⟩ := ih
    refine ⟨fun path => Option.elim path a m2, ?_⟩
    simpa only [List.length_cons, Pattern.varN, List.foldr_cons] using hm.var

/-- Exact syntactic match for the simple recursor/iota pattern once both
constant-headed spines and their arities are known. -/
theorem _root_.Lean4Lean.RecursorIotaPattern.matchesS_spines
    {r c : Name} {rls cls : List SLevel} {rargs cargs : List SExpr}
    {major ctorArity : Nat}
    (hr : rargs.length = major) (hc : cargs.length = ctorArity) :
    ∃ m2, (RecursorIotaPattern r major c ctorArity).MatchesS
      (.app (rargs.foldr (fun a f => f.app a) (.const r rls))
        (cargs.foldr (fun a f => f.app a) (.const c cls))) rls m2 := by
  obtain ⟨mr, hmr⟩ := Pattern.varN_const_matchesS r rls rargs
  obtain ⟨mc, hmc⟩ := Pattern.varN_const_matchesS c cls cargs
  subst major
  subst ctorArity
  exact ⟨Sum.elim mr mc, hmr.app hmc⟩

/-- Invert a `varN` match headed by a constant into the exact application
spine it inspected.  Besides the arity equation, retain the capture map and
its original match proof so dependent consumers do not have to reconstruct
either one from list indexing. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.varN_const_inv
    (H : (Pattern.varN (.const c) arity).MatchesS e ls mcap) :
    ∃ (args : List SExpr),
      args.length = arity ∧
      e = args.foldr (fun a f => f.app a) (.const c ls) ∧
      (Pattern.varN (.const c) arity).MatchesS
        (args.foldr (fun a f => f.app a) (.const c ls)) ls mcap := by
  induction arity generalizing e with
  | zero =>
    simp only [Pattern.varN] at H ⊢
    cases H
    exact ⟨[], rfl, rfl, .const⟩
  | succ arity ih =>
    simp only [Pattern.varN] at H ⊢
    cases H with
    | @var f f' f1 g1 a' h =>
      obtain ⟨args, hlen, rfl, hmatch⟩ := ih h
      exact ⟨a' :: args, congrArg Nat.succ hlen, rfl, hmatch.var⟩

/-- Exact decomposition of a semantic iota match.  In particular this
recovers the constructor universe levels, which are not stored in the
match's `m1` index, and separates the recursor and constructor capture maps.
Generated-rule soundness must validate those recovered levels against its
rule certificate before constructing a contraction. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.iota_inv
    {rec ctor : Name} {major arity : Nat} {e : SExpr}
    {recLs : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (H : (RecursorIotaPattern rec major ctor arity).MatchesS e recLs mcap) :
    ∃ (recArgs ctorArgs : List SExpr) (ctorLs : List SLevel)
        (mrec : (Pattern.varN (.const rec) major).Path → SExpr)
        (mctor : (Pattern.varN (.const ctor) arity).Path → SExpr),
      recArgs.length = major ∧ ctorArgs.length = arity ∧
      e = (recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) ∧
      mcap = Sum.elim mrec mctor ∧
      (Pattern.varN (.const rec) major).MatchesS
        (recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)) recLs mrec ∧
      (Pattern.varN (.const ctor) arity).MatchesS
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) ctorLs mctor := by
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨recArgs, hrecLen, rfl, hrec'⟩ := hrec.varN_const_inv
    obtain ⟨ctorArgs, hctorLen, rfl, hctor'⟩ := hctor.varN_const_inv
    exact ⟨recArgs, ctorArgs, ctorLevels, recCap, ctorCap,
      hrecLen, hctorLen, rfl, rfl, hrec', hctor'⟩

/-- A successful syntactic match remembers the constant-headed application
spine that it inspected. Arguments are stored in reverse application order,
matching the representation used by the shape interpretation. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.head_spine (H : p.MatchesS e ls m) :
    ∃ (c : Name) (ls' : List SLevel) (args : List SExpr),
      e = args.foldr (fun a f => f.app a) (.const c ls') ∧
      Arity (.const c) args.length p := by
  induction H with
  | const => exact ⟨_, _, [], rfl, .refl⟩
  | @var f f' f1 g1 a' h ih =>
    obtain ⟨c, ls, args, heq, har⟩ := ih
    refine ⟨c, ls, a' :: args, ?_, .var har⟩
    simp only [List.foldr_cons]
    rw [← heq]
  | @app f f' f1 g1 a a' f2 g2 hf ha ihf iha =>
    obtain ⟨c, ls, args, heq, har⟩ := ihf
    refine ⟨c, ls, a' :: args, ?_, .app har⟩
    simp only [List.foldr_cons]
    rw [← heq]

theorem _root_.Lean4Lean.Pattern.matchesS_inter {p q : Pattern} {e : SExpr} :
    (∃ m1 m2, p.MatchesS e m1 m2) ∧ (∃ m1 m2, q.MatchesS e m1 m2) ↔
    (∃ r m1 m2, p.inter q = some r ∧ r.MatchesS e m1 m2) := by
  constructor
  · rintro ⟨⟨m1, m2, hp⟩, ⟨m3, m4, hq⟩⟩
    induction hp generalizing q m3 <;> cases hq <;> simp [Pattern.inter]
    · case const.const => exact ⟨_, _, .const⟩
    · case var.var ih _ _ ih' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih _ _ ih'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
    · case var.app ihf _ _ _ _ _ ha2 ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.var ha2 ihf _ _ _ ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.app ihf iha _ _ _ _ _ iha' ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha _ _ iha'
      exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r m1 <;> cases q <;> simp [Pattern.inter] at h1 <;> [
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨_, wf, _, wa, rfl⟩ := h1;
        obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1
      ] <;> cases h2
    · exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    · next ihf iha _ _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      have ⟨⟨ma1, ma2, ha⟩, ⟨ma1', ma2', ha'⟩⟩ := iha _ _ _ wa ha
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .var hf'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha' hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .var hf'⟩⟩

theorem _root_.Lean4Lean.Pattern.MatchesS.determ
    (h1 : Pattern.MatchesS p e m1 m2) (h2 : Pattern.MatchesS p e m1' m2') :
    m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

/-- Reify a semantic match into an exact syntactic match. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.reify
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.Matches p e.reify (m1.map SLevel.reify)
      fun path => (m2 path).reify := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.Matches.const
      (c := c) (ls := ls.map SLevel.reify))
    simp only [SExpr.reify]
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.Matches (.var f) (.app f'.reify a'.reify)
      (f1.map SLevel.reify) fun path => (Option.elim path a' g1).reify
    have heq : (fun path => (Option.elim path a' g1).reify) =
        (fun path => Option.elim path a'.reify fun path => (g1 path).reify) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ihf iha =>
    change Pattern.Matches (.app f a) (.app f'.reify a'.reify)
      (f1.map SLevel.reify) fun path => (Sum.elim g1 g2 path).reify
    have heq : (fun path => (Sum.elim g1 g2 path).reify) =
        Sum.elim (fun path => (g1 path).reify)
          (fun path => (g2 path).reify) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ihf.app iha

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.RHS → SExpr
  | .fixed c _ => .mkInst m1 c
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

/-- Applying a left-associated RHS application tower is the corresponding
left fold of the instantiated template arguments. -/
theorem _root_.Lean4Lean.Pattern.RHS.appN_applyS {p : Pattern}
    (f : p.RHS) (as : List p.RHS) (m1 : List SLevel)
    (m2 : p.Path → SExpr) :
    (Pattern.RHS.appN f as).applyS m1 m2 =
      as.foldl (fun acc a => acc.app (a.applyS m1 m2))
        (f.applyS m1 m2) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
    simpa only [Pattern.RHS.appN, Pattern.RHS.applyS,
      List.foldl_cons] using ih (.app f a)

/-- Expose the last application in an RHS application tower. -/
theorem _root_.Lean4Lean.Pattern.RHS.appN_append_singleton {p : Pattern}
    (f a : p.RHS) (as : List p.RHS) :
    Pattern.RHS.appN f (as ++ [a]) = .app (Pattern.RHS.appN f as) a := by
  induction as generalizing f with
  | nil => rfl
  | cons b as ih =>
    simpa only [List.cons_append, Pattern.RHS.appN] using ih (.app f b)

/-- Reification commutes with applying a pattern RHS, up to the semantic
quotient map. -/
theorem _root_.Lean4Lean.Pattern.RHS.mk_apply_reify {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    SExpr.mk (r.apply (m1.map SLevel.reify) fun path => (m2 path).reify) =
      r.applyS m1 m2 := by
  induction r with
  | fixed e closed =>
    simp only [Pattern.RHS.apply, Pattern.RHS.applyS]
    rw [← SExpr.mkInst_map_mk
      (ls := m1.map SLevel.reify) (e := e)
      (by
        intro l hl
        simp only [List.mem_map] at hl
        obtain ⟨u, _, rfl⟩ := hl
        exact u.reify_wf)]
    congr 1
    rw [List.map_map]
    apply List.map_id'''
    intro u _
    exact SLevel.mk_reify u
  | var path => exact SExpr.mk_reify (m2 path)
  | app f a ihf iha =>
    simp only [Pattern.RHS.apply, Pattern.RHS.applyS, SExpr.mk]
    rw [ihf, iha]

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed c _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

def _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkInstS.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2

theorem _root_.Lean4Lean.Pattern.MatchesS.lift'
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.MatchesS p (e.lift' ρ) m1 fun path => (m2 path).lift' ρ := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [SExpr.lift']
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.MatchesS (.var f) (.app (f'.lift' ρ) (a'.lift' ρ)) f1
      (fun path => (Option.elim path a' g1).lift' ρ)
    have heq : (fun path => (Option.elim path a' g1).lift' ρ) =
        (fun path => Option.elim path (a'.lift' ρ) fun path => (g1 path).lift' ρ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ih1 ih2 =>
    change Pattern.MatchesS (.app f a) (.app (f'.lift' ρ) (a'.lift' ρ)) f1
      (fun path => (Sum.elim g1 g2 path).lift' ρ)
    have heq : (fun path => (Sum.elim g1 g2 path).lift' ρ) =
        Sum.elim (fun path => (g1 path).lift' ρ) (fun path => (g2 path).lift' ρ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih1.app ih2

theorem _root_.Lean4Lean.Pattern.RHS.lift'_applyS {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (r.applyS m1 m2).lift' ρ = r.applyS m1 fun path => (m2 path).lift' ρ := by
  induction r with
  | fixed e cl => exact (cl.mkInstS.lift'_eq .zero)
  | var => rfl
  | app _ _ ih1 ih2 =>
    simp only [Pattern.RHS.applyS, SExpr.lift']
    rw [ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_lift' {p : Pattern}
    (ck : p.Check) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (ck.defeqsS m1 m2).map (fun ab => (ab.1.lift' ρ, ab.2.lift' ρ)) =
      ck.defeqsS m1 fun path => (m2 path).lift' ρ := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih]
    rw [a.lift'_applyS, b.lift'_applyS]

theorem _root_.Lean4Lean.Pattern.matchesS_lift' {p : Pattern} {e : SExpr} {m1 m2'} :
    p.MatchesS (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.MatchesS e m1 m2 ∧ ∀ path, m2' path = (m2 path).lift' ρ := by
  constructor
  · intro h
    generalize eq : e.lift' ρ = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, hmatch, hpath⟩ := ih rfl
      refine ⟨_, .var hmatch, ?_⟩
      intro path
      cases path <;> simp_all
    | app _ _ ihf iha =>
      cases e <;> cases eq
      have ⟨_, hf, hfp⟩ := ihf rfl
      have ⟨_, ha, hap⟩ := iha rfl
      refine ⟨_, .app hf ha, ?_⟩
      intro path
      cases path <;> simp_all
  · rintro ⟨m2, hmatch, hpath⟩
    induction hmatch with
    | const => exact (show m2' = _ by ext path; exact Empty.elim path) ▸ .const
    | @var f f' f1 g1 a' _ ih =>
      have h := ih (hpath <| some ·)
      have heq : m2' = fun path => Option.elim path (a'.lift' ρ) fun path => m2' (some path) := by
        funext path
        cases path <;> simp [hpath]
      rw [heq]
      exact h.var
    | app _ _ ihf iha =>
      have h := (ihf (hpath <| .inl ·)).app (iha (hpath <| .inr ·))
      refine cast ?_ h
      congr 1
      funext path
      cases path <;> rfl

theorem _root_.Lean4Lean.Pattern.MatchesS.subst
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.MatchesS p (e.subst σ) m1 fun path => (m2 path).subst σ := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [SExpr.subst]
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.MatchesS (.var f) (.app (f'.subst σ) (a'.subst σ)) f1
      (fun path => (Option.elim path a' g1).subst σ)
    have heq : (fun path => (Option.elim path a' g1).subst σ) =
        (fun path => Option.elim path (a'.subst σ) fun path => (g1 path).subst σ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ih1 ih2 =>
    change Pattern.MatchesS (.app f a) (.app (f'.subst σ) (a'.subst σ)) f1
      (fun path => (Sum.elim g1 g2 path).subst σ)
    have heq : (fun path => (Sum.elim g1 g2 path).subst σ) =
        Sum.elim (fun path => (g1 path).subst σ) (fun path => (g2 path).subst σ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih1.app ih2

theorem _root_.Lean4Lean.Pattern.RHS.subst_applyS {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (r.applyS m1 m2).subst σ = r.applyS m1 fun path => (m2 path).subst σ := by
  induction r with
  | fixed e cl => exact cl.mkInstS.subst_eq .zero
  | var => rfl
  | app _ _ ih1 ih2 =>
    simp only [Pattern.RHS.applyS, SExpr.subst]
    rw [ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_subst {p : Pattern}
    (ck : p.Check) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (ck.defeqsS m1 m2).map (fun ab => (ab.1.subst σ, ab.2.subst σ)) =
      ck.defeqsS m1 fun path => (m2 path).subst σ := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih]
    rw [a.subst_applyS, b.subst_applyS]

section
set_option hygiene false

inductive Lookup : List SExpr → Nat → SExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.mkS (H : Lean4Lean.Lookup Γ i A) : Lookup (Γ.map mk) i (mk A) := by
  induction H with
  | zero => rw [mk_lift]; exact .zero
  | succ _ ih => rw [mk_lift]; exact .succ ih

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [SExpr.lift, ← SExpr.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [SExpr.lift, ← SExpr.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [SExpr.lift, ← SExpr.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

scoped notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  -- | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
  --   (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ≡ r.1.applyS m1 m2' : A
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type

/-- SExpr-side typing of an exact application spine.  Unlike a bare typing
of the final application, this retains the type of every argument at the
point where its surrounding pi is peeled.  Generated iota soundness needs
this evidence for the recursor, constructor, and captured-rule spines. -/
inductive SpineWF (Γ : List SExpr) : SExpr → List SExpr → SExpr → Prop where
  | nil : SpineWF Γ A [] A
  | cons :
    IsDefEq Γ e e A₁ →
    SpineWF Γ (A₂.inst e) es B →
    SpineWF Γ (.forallE A₁ A₂) (e :: es) B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    SpineWF Γ A' es B →
    SpineWF Γ A es B
  | ret :
    SpineWF Γ A es B →
    IsDefEq Γ B B' (.sort u) →
    SpineWF Γ A es B'

/-- Extend a conversion-aware spine by its final argument. -/
theorem SpineWF.snoc
    (H : SpineWF Γ A es B)
    (hB : IsDefEq Γ B (.forallE D C) (.sort u))
    (he : IsDefEq Γ e e D) :
    SpineWF Γ A (es ++ [e]) (C.inst e) := by
  induction H generalizing D C u with
  | nil => exact .conv hB (.cons he .nil)
  | cons harg _ ih => exact .cons harg (ih hB he)
  | conv hty _ ih => exact .conv hty (ih hB he)
  | ret _ hret ih => exact ih (hret.trans' hB) he

/-- Two application spines with a common final Pi layer.  The explicit
codomain conversions are deliberately retained for both majors: they let a
consumer combine either recursor prefix with either endpoint of a related
major without appealing to global type uniqueness. -/
structure SpineWF.LastPair (Γ : List SExpr) (Head : SExpr)
    (xs ys : List SExpr) (x y A : SExpr) where
  prefixType : SExpr
  domain : SExpr
  codomain : SExpr
  piSort : SLevel
  resultSortX : SLevel
  resultSortY : SLevel
  prefixX : SpineWF Γ Head xs.reverse prefixType
  prefixY : SpineWF Γ Head ys.reverse prefixType
  pi : IsDefEq Γ prefixType (.forallE domain codomain) (.sort piSort)
  major : IsDefEq Γ x y domain
  resultX : IsDefEq Γ (codomain.inst x) A (.sort resultSortX)
  resultY : IsDefEq Γ (codomain.inst y) A (.sort resultSortY)

/-- Recover the complete left application spine. -/
theorem SpineWF.LastPair.fullX
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF Γ Head (x :: xs).reverse A := by
  rw [List.reverse_cons]
  exact .ret (H.prefixX.snoc H.pi (H.major.trans H.major.symm)) H.resultX

/-- Recover the complete right application spine. -/
theorem SpineWF.LastPair.fullY
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF Γ Head (y :: ys).reverse A := by
  rw [List.reverse_cons]
  exact .ret (H.prefixY.snoc H.pi (H.major.symm.trans H.major)) H.resultY

/-- Keep the major pair and use the left prefix at both endpoints. -/
def SpineWF.LastPair.leftPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs xs x y A :=
  { H with prefixY := H.prefixX }

/-- Keep the major pair and use the right prefix at both endpoints. -/
def SpineWF.LastPair.rightPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys ys x y A :=
  { H with prefixX := H.prefixY }

/-- Swap only the two recursor prefixes. -/
def SpineWF.LastPair.symmPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys xs x y A :=
  { H with prefixX := H.prefixY, prefixY := H.prefixX }

/-- Keep the prefixes and use the left major at both endpoints. -/
def SpineWF.LastPair.leftMajors
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs ys x x A :=
  { H with
    major := H.major.trans H.major.symm
    resultSortY := H.resultSortX
    resultY := H.resultX }

/-- Keep the prefixes and use the right major at both endpoints. -/
def SpineWF.LastPair.rightMajors
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs ys y y A :=
  { H with
    major := H.major.symm.trans H.major
    resultSortX := H.resultSortY
    resultX := H.resultY }

/-- Swap both prefixes and majors. -/
def SpineWF.LastPair.symm
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys xs y x A :=
  { H with
    prefixX := H.prefixY
    prefixY := H.prefixX
    major := H.major.symm
    resultSortX := H.resultSortY
    resultSortY := H.resultSortX
    resultX := H.resultY
    resultY := H.resultX }

/-- Packaging of the final-application certificate for callers that keep
their accumulated spines as whole lists. -/
structure SpineWF.NonemptyLastPair (Γ : List SExpr) (Head : SExpr)
    (args args' : List SExpr) (A : SExpr) where
  x : SExpr
  xs : List SExpr
  y : SExpr
  ys : List SExpr
  args_eq : args = x :: xs
  args'_eq : args' = y :: ys
  pair : SpineWF.LastPair Γ Head xs ys x y A

/-- Apply a certified spine to a term typed at its head type. -/
theorem SpineWF.hasType
    (H : SpineWF Γ A es B) (hf : IsDefEq Γ f f A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es.foldl (fun f a => f.app a) f) B := by
  induction H generalizing f with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- Self-typing of the complete left application. -/
theorem SpineWF.LastPair.hasTypeX
    (H : SpineWF.LastPair Γ Head xs ys x y A)
    (hhead : IsDefEq Γ f f Head) :
    IsDefEq Γ ((x :: xs).foldr (fun a f => f.app a) f)
      ((x :: xs).foldr (fun a f => f.app a) f) A := by
  simpa only [List.foldl_reverse, List.foldr_cons] using H.fullX.hasType hhead

/-- Self-typing of the complete right application. -/
theorem SpineWF.LastPair.hasTypeY
    (H : SpineWF.LastPair Γ Head xs ys x y A)
    (hhead : IsDefEq Γ f f Head) :
    IsDefEq Γ ((y :: ys).foldr (fun a f => f.app a) f)
      ((y :: ys).foldr (fun a f => f.app a) f) A := by
  simpa only [List.foldl_reverse, List.foldr_cons] using H.fullY.hasType hhead

/-- Apply a certified spine congruently to both endpoints of a typed
equality.  This is the SExpr counterpart of Theory's `appN_congr`; retaining
the spine certificate avoids reconstructing the intermediate pi types. -/
theorem SpineWF.congr
    (H : SpineWF Γ A es B) (hf : IsDefEq Γ f f' A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es.foldl (fun f a => f.app a) f') B := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- A dependently typed pointwise equality between two application spines.
The recursive head is instantiated with the left argument, matching the
result type chosen by `IsDefEq.appDF`; the right endpoint is transported to
that same type by the equality stored at the current argument. -/
inductive SpineDefEq (Γ : List SExpr) :
    SExpr → List SExpr → List SExpr → SExpr → Prop where
  | nil : SpineDefEq Γ A [] [] A
  | cons :
    IsDefEq Γ e e' A₁ →
    SpineDefEq Γ (A₂.inst e) es es' B →
    SpineDefEq Γ (.forallE A₁ A₂) (e :: es) (e' :: es') B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    SpineDefEq Γ A' es es' B →
    SpineDefEq Γ A es es' B
  | ret :
    SpineDefEq Γ A es es' B →
    IsDefEq Γ B B' (.sort u) →
    SpineDefEq Γ A es es' B'

/-- Extend a dependently typed pointwise spine by its final related
argument.  The conversion at the old result exposes the next Pi; the new
result is oriented at the left argument, exactly like `SpineDefEq.cons`. -/
theorem SpineDefEq.snoc
    (H : SpineDefEq Γ A es es' B)
    (hB : IsDefEq Γ B (.forallE D C) (.sort u))
    (he : IsDefEq Γ e e' D) :
    SpineDefEq Γ A (es ++ [e]) (es' ++ [e']) (C.inst e) := by
  induction H generalizing D C u with
  | nil => exact .conv hB (.cons he .nil)
  | cons harg _ ih => exact .cons harg (ih hB he)
  | conv hty _ ih => exact .conv hty (ih hB he)
  | ret _ hret ih => exact ih (hret.trans' hB) he

/-- A typed pointwise spine applies congruently to related heads. -/
theorem SpineDefEq.congr
    (H : SpineDefEq Γ A es es' B) (hf : IsDefEq Γ f f' A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es'.foldl (fun f a => f.app a) f') B := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- Forget the right endpoint of a pointwise spine equality. -/
theorem SpineDefEq.left
    (H : SpineDefEq Γ A es es' B) : SpineWF Γ A es B := by
  induction H with
  | nil => exact .nil
  | cons he _ ih => exact .cons (he.trans he.symm) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Reflexive pointwise equality underlying a well-typed spine. -/
theorem SpineWF.toSpineDefEq
    (H : SpineWF Γ A es B) : SpineDefEq Γ A es es B := by
  induction H with
  | nil => exact .nil
  | cons he _ ih => exact .cons he ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- A spine indexed by the keys that selected its arguments.  Besides
remembering order, the index fixes the exact domain type used at each
dependent application.  This is the alignment that a plain `List SExpr`
necessarily erases. -/
inductive PathSpineWF (Γ : List SExpr) {α : Type}
    (value type : α → SExpr) : SExpr → List α → SExpr → Prop where
  | nil : PathSpineWF Γ value type A [] A
  | cons :
    PathSpineWF Γ value type (A₂.inst (value path)) paths B →
    PathSpineWF Γ value type (.forallE (type path) A₂) (path :: paths) B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    PathSpineWF Γ value type A' paths B →
    PathSpineWF Γ value type A paths B
  | ret :
    PathSpineWF Γ value type A paths B →
    IsDefEq Γ B B' (.sort u) →
    PathSpineWF Γ value type A paths B'

/-- Erase path indices after supplying the exact self-typing attached to
each selected argument. -/
theorem PathSpineWF.toSpineWF
    (H : PathSpineWF Γ value type A paths B)
    (htyped : ∀ path, IsDefEq Γ (value path) (value path) (type path)) :
    SpineWF Γ A (paths.map value) B := by
  induction H with
  | nil => exact .nil
  | cons _ ih =>
    simp only [List.map_cons]
    exact .cons (htyped _) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Retain the path-indexed dependent spine while replacing each selected
capture by a related endpoint.  The recursive codomain is instantiated with
the left capture, exactly as in `SpineDefEq.cons`; consequently no type
uniqueness or reconstruction from the right spine is needed. -/
theorem PathSpineWF.toSpineDefEq
    (H : PathSpineWF Γ value type A paths B)
    (hvalue : ∀ path, IsDefEq Γ (value path) (value' path) (type path)) :
    SpineDefEq Γ A (paths.map value) (paths.map value') B := by
  induction H with
  | nil => exact .nil
  | cons _ ih =>
    simp only [List.map_cons]
    exact .cons (hvalue _) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Concrete capture typings supplied to a generated reduction site.  Two
sites can share the same `type` map while carrying endpoint-specific
self-typings, which is precisely what dependent RHS congruence needs. -/
structure _root_.Lean4Lean.Pattern.CaptureTyping
    (Γ : List SExpr) {p : Pattern} (capture : p.Path → SExpr)
    (type : p.Path → SExpr) : Prop where
  typed : ∀ path, IsDefEq Γ (capture path) (capture path) (type path)

/-- Typed syntax retained at one concrete iota site before its generated
tower is selected.  Recursor arguments are in newest-first semantic order,
so the typing spine reverses them and appends the major premise. -/
structure _root_.Lean4Lean.Pattern.IotaTyping
    (Γ : List SExpr) (rec ctor : Name)
    (recLs ctorLs : List SLevel) (recArgs ctorArgs : List SExpr)
    (majorTerm A : SExpr) where
  recHeadType : SExpr
  ctorHeadType : SExpr
  ctorResultType : SExpr
  majorType : SExpr
  recHead : IsDefEq Γ (.const rec recLs) (.const rec recLs) recHeadType
  recSpine : SpineWF Γ recHeadType
    (recArgs.reverse ++ [majorTerm]) A
  ctorHead : IsDefEq Γ (.const ctor ctorLs) (.const ctor ctorLs) ctorHeadType
  ctorSpine : SpineWF Γ ctorHeadType ctorArgs.reverse ctorResultType
  majorEq : IsDefEq Γ majorTerm
    (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) majorType

/-- The concrete registered tower selected by one iota-pattern payload.
This rule descriptor is independent of a particular match, so the two
endpoints of a logical-relation comparison share the same tower and the same
ordered capture paths by construction. -/
structure _root_.Lean4Lean.Pattern.IotaRule
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check) where
  pat : Params.Pat (RecursorIotaPattern rec major ctor arity) r
  df : VDefEq
  registered : Params.env.defeqs df
  rhsClosed : df.rhs.Closed
  capturePaths : List (RecursorIotaPattern rec major ctor arity).Path
  rhsTower : r.1 = Pattern.RHS.appN (.fixed df.rhs rhsClosed)
    (capturePaths.map fun path => .var path)

/-- The syntax computed by a rule descriptor is its registered right tower
applied to the descriptor's ordered concrete captures. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsApply
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) (recLs : List SLevel)
    (mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr) :
    (rule.capturePaths.map mcap).foldl
        (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.rhs) =
      r.1.applyS recLs mcap := by
  rw [rule.rhsTower, Pattern.RHS.appN_applyS]
  simp only [Pattern.RHS.applyS, List.foldl_map]

/-- Evidence-rich generated reduction site.  Unlike the former direct
`iotaAction` hook, this records the registered lambda tower, the exact typed
capture application used to instantiate it, and the local beta collapse to
the matched redex.  The final `Pattern.Action` is derived below. -/
structure _root_.Lean4Lean.Pattern.IotaReductionSite
    (Γ : List SExpr) {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (rule : Pattern.IotaRule r)
    (recLs ctorLs : List SLevel) (recArgs ctorArgs : List SExpr)
    (majorTerm A : SExpr)
    (mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
    (captureTyping : Pattern.CaptureTyping Γ mcap captureType) where
  typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs recArgs ctorArgs majorTerm A
  matched : (RecursorIotaPattern rec major ctor arity).MatchesS
    ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
      (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs))) recLs mcap
  levelsLength : recLs.length = rule.df.uvars
  captureSpine : PathSpineWF Γ mcap captureType
    (SExpr.mkInst recLs rule.df.type) rule.capturePaths A
  lhsCollapse : IsDefEq Γ
    ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
      (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
    ((rule.capturePaths.map mcap).foldl
      (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.lhs)) A
  dfs : List (SExpr × SExpr × SExpr)
  defeqs : dfs.map (·.2) = r.2.defeqsS recLs mcap
  checked : ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Γ a b B

/-- The finite evidence attached to one concrete pattern contraction.

Pattern membership is only combinatorial. An `Action` additionally records
the exact matched redex and captures, the finite list of checked equalities,
and the local equality to the instantiated RHS. It deliberately does not
contain endpoint typings: consumers of the action must retain those at the
typing/reduction layer where they are known. -/
structure _root_.Lean4Lean.Pattern.Action (Gamma : List SExpr) {p : Pattern}
    (r : p.RHS × p.Check) (e : SExpr) (m1 : List SLevel)
    (m2 : p.Path → SExpr) (A : SExpr) where
  pat : Pat p r
  matched : p.MatchesS e m1 m2
  dfs : List (SExpr × SExpr × SExpr)
  defeqs : dfs.map (·.2) = r.2.defeqsS m1 m2
  checked : ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Gamma a b B
  sound : IsDefEq Gamma e (r.1.applyS m1 m2) A

/-- Semantic closure required to translate the live registered structure-eta
rule.  This is a bridge obligation, not an axiom: L4L-16 constructs it from
the checked `VEnv.WF` history before exposing sort inversion. -/
def Params.StructureEtaSound : Prop :=
  ∀ {rule : VStructEta} {levels : List VLevel} {Γ params : List VExpr}
    {major : VExpr},
    env.structEtas rule →
    IsDefEq (Γ.map mk)
      (mk (rule.rebuild levels params major))
      (mk (rule.rebuild levels params major))
      (mk (rule.structureType levels params)) →
    IsDefEq (Γ.map mk) (mk major) (mk major)
      (mk (rule.structureType levels params)) →
    IsDefEq (Γ.map mk) (mk (rule.rebuild levels params major)) (mk major)
      (mk (rule.structureType levels params))

/-- Translate the main typing judgment into the semantically quotiented syntax. -/
theorem IsDefEq.mkS (hstruct : Params.StructureEtaSound)
    (H : Params.env.IsDefEq Params.univs Γ e₁ e₂ A) :
    OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    IsDefEq (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  intro hΓ
  induction H using VEnv.IsDefEq.rec
      (motive_2 := fun _ _ _ _ _ => True) with
  | bvar h => exact .bvar (SExpr.Lookup.mkS h)
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hΓ) (ih₂ hΓ)
  | @sortDF l l' Γ hl hl' h =>
    change IsDefEq _ (.sort (SLevel.mk _)) (.sort (SLevel.mk _)) (.sort (SLevel.mk _))
    have hu := SLevel.mk_eq hl hl' h
    have hus : SLevel.mk l.succ = (SLevel.mk l').succ := by rw [SLevel.mk_succ hl, hu]
    rw [hu, hus]
    exact .sort
  | @constDF c ci ls ls' Γ h₁ h₂ h₃ h₄ h₅ =>
    change IsDefEq _ (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    rw [← SLevel.map_mk_eq h₂ h₃ h₅, ← mkInst_map_mk h₂]
    exact IsDefEq.const (ls := ls.map SLevel.mk) h₁ (by simpa using h₄)
  | appDF _ _ ihf iha => simpa only [mk, mk_instExpr] using IsDefEq.appDF (ihf hΓ) (iha hΓ)
  | lamDF hA _ ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    exact .lamDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | forallEDF hA hb ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    have hu := (hA.levelWF hΓ).2.2
    have hv := (hb.levelWF ⟨hΓ, hAwf⟩).2.2
    simpa only [mk, SLevel.mk_imax hu hv] using IsDefEq.forallEDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hΓ) (ihe hΓ)
  | beta _ he' ihe ihe' =>
    have hAwf := (he'.levelWF hΓ).2.2
    simpa only [mk, mk_instExpr] using IsDefEq.beta (ihe ⟨hΓ, hAwf⟩) (ihe' hΓ)
  | eta _ ih => simpa only [mk, mk_lift] using IsDefEq.eta (ih hΓ)
  | structEta hreg _ _ _ _ _ _ _ ihMajor ihRebuild =>
    exact hstruct hreg (ihRebuild hΓ) (ihMajor hΓ)
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel (ihp hΓ) (ihh hΓ) (ihh' hΓ)
  | @extra df ls Γ h₁ h₂ h₃ =>
    simpa only [mkInst_map_mk h₂] using
      (IsDefEq.extra (Γ := Γ.map mk) (ls := ls.map SLevel.mk) h₁ (by simpa using h₃))
  | nil => trivial
  | cons => trivial

/-- Translate a Theory application-spine certificate without erasing its
per-argument typings.  This is the bridge needed by a live generated-iota
reduction site; the endpoint-only translation is intentionally insufficient.
-/
theorem _root_.Lean4Lean.VEnv.SpineWF.mkS
    (hstruct : Params.StructureEtaSound)
    (H : Params.env.SpineWF Params.univs Γ A es B)
    (hΓ : OnCtx Γ (fun _ A => A.LevelWF Params.univs)) :
    SExpr.SpineWF (Γ.map SExpr.mk) (SExpr.mk A)
      (es.map SExpr.mk) (SExpr.mk B) := by
  exact VEnv.SpineWF.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ A es B _ =>
      OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
      SExpr.SpineWF (Γ.map SExpr.mk) (SExpr.mk A)
        (es.map SExpr.mk) (SExpr.mk B))
    (bvar := by simp) (symm := by simp) (trans := by simp)
    (sortDF := by simp) (constDF := by simp) (appDF := by simp)
    (lamDF := by simp) (forallEDF := by simp) (defeqDF := by simp)
    (beta := by simp) (eta := by simp) (structEta := by simp)
    (proofIrrel := by simp) (extra := by simp)
    (nil := fun {_Γ _A} _hΓ => .nil)
    (cons := fun {_Γ _e _A₁ _es _B _A₂} he _ _ ih hΓ => by
      exact .cons (SExpr.IsDefEq.mkS hstruct he hΓ) (by
        simpa only [SExpr.mk_instExpr] using ih hΓ))
    H hΓ

def CtorBundle.IsCtor (c : Name) : Prop :=
  ∃ cl, Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..

def CtorBundle.IsCtor.cl (H : CtorBundle.IsCtor c) :
    {cl // Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..} := by
  dsimp [CtorBundle.IsCtor] at H
  match Params.classify c, H with
  | some cl, H => refine ⟨cl, ?_⟩; obtain ⟨_, ⟨⟩, H⟩ := H; exact ⟨rfl, H⟩

structure CtorBundle (c : Name) (cl : CtorBundle.IsCtor c) : Type where
  I : Name
  Ts : List SExpr
  args : List SExpr
  u : SLevel
  hlen : Ts.length = cl.cl.1.arity
  hclI : Params.classify I = some (.indTy args.length)
  hu0 : u ≠ .zero

def CtorBundle.rhs (H : CtorBundle c cl) (ls : List SLevel) : SExpr :=
  H.Ts.foldr .forallE (H.args.foldr (fun A acc => acc.app A) (.const H.I ls))

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
inductive IsDefEqStrong : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    -- Definition bodies are stored in the direction used by semantic
    -- recursion: the body is the left endpoint, so its adequacy hypothesis can
    -- consume the strictly smaller `R`-child exposed by `LE_Interp.Const.pat`.
    -- The ordinary constant equality remains available by symmetry.
    (∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check}, Pat (.const c) r →
      Γ ⊢ r.1.applyS ls Empty.elim ≡ .const c ls : SExpr.mkInst ls ci.type) →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ A : .sort u →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  /-- A local, proof-carrying extension contraction.  Unlike a registered
  raw equation, this constructor can be interpreted operationally: it names
  the concrete matched redex, carries its successful checks and exact local
  equality, and retains strong typings for both endpoints. -/
  | extra : (action : Pattern.Action Γ r e m1 m2 A) →
    Γ ⊢ e : A → Γ ⊢ r.1.applyS m1 m2 : A →
    Γ ⊢ e ≡ r.1.applyS m1 m2 : A
end

/-! The semantic bridge packages only environment-specific facts.  Its fields
are propositions carried by a concrete value; the public L4L-16 theorem
constructs that value from `VEnv.WF`, so none of these are trusted axioms. -/
class Params.Semantic [Params] where
  structureEta :
    ∀ {rule : VStructEta} {levels : List VLevel} {Γ params : List VExpr}
      {major : VExpr},
      env.structEtas rule →
      IsDefEqStrong (Γ.map mk)
        (mk (rule.rebuild levels params major))
        (mk (rule.rebuild levels params major))
        (mk (rule.structureType levels params)) →
      IsDefEqStrong (Γ.map mk) (mk major) (mk major)
        (mk (rule.structureType levels params)) →
      IsDefEqStrong (Γ.map mk) (mk (rule.rebuild levels params major))
        (mk major) (mk (rule.structureType levels params))
  ctor :
    ∀ {c : Name} {ci : VConstant} {ls : List SLevel} {Γ : List SExpr},
      env.constants c = some ci → ls.length = ci.uvars →
      ∀ cl : CtorBundle.IsCtor c,
        {F : CtorBundle c cl //
          IsDefEqStrong Γ (SExpr.mkInst ls ci.type) (F.rhs ls) (.sort F.u)}
  /-- Zero-arity patterns are definition rules.  The payload is a closed
  fixed expression and the bridge supplies its evidence-rich unfolding in
  every context.  This is proved from the declaration history; pattern
  membership by itself provides none of these facts. -/
  defn :
    ∀ {c : Name} {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      Pat (.const c) r →
      ∃ (value : VExpr) (closed : value.Closed),
        r = (.fixed value closed, .true) ∧
        ∀ {ci : VConstant} {ls : List SLevel} {Γ : List SExpr},
          env.constants c = some ci → ls.length = ci.uvars →
          IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
            (SExpr.mkInst ls ci.type)
  /-- Recover the one registered tower and ordered capture inventory selected
  by an iota payload.  This descriptor is match-independent and is therefore
  shared by both endpoints of a semantic comparison. -/
  iotaRule :
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      Pat (RecursorIotaPattern rec major ctor arity) r →
      Pattern.IotaRule r
  /-- Construct the evidence-rich site for a generated iota contraction.
  This field cannot return the contraction itself: it must expose the
  registered tower, typed capture application, and beta collapse, while the
  caller supplies the exact typed recursor and constructor spines (including
  the constructor levels recovered from the match).  `IotaReductionSite.action`
  derives the finite local contraction generically from this certificate. -/
  iotaSite :
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {Γ : List SExpr} {A majorTerm : SExpr} {recLs ctorLs : List SLevel}
      {recArgs ctorArgs : List SExpr}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr},
      (rule : Pattern.IotaRule r) →
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr) →
      (captureTyping : Pattern.CaptureTyping Γ mcap captureType) →
      (typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs
        recArgs ctorArgs majorTerm A) →
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
        recLs mcap →
      IsDefEq Γ
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs))) A →
      (∃ u, IsDefEq Γ A A (.sort u)) →
      Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
        majorTerm A mcap captureType captureTyping
  /-- Expand a registered raw equation into structural strong equality whose
  only extension leaves are the proof-carrying local contractions above.
  Generated iota and quotient towers are therefore exposed under their
  lambdas instead of being falsely matched at the closed tower. -/
  registered :
    ∀ {df : VDefEq} {ls : List SLevel} {Γ : List SExpr},
      env.defeqs df → ls.length = df.uvars →
      IsDefEqStrong Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type) →
      IsDefEqStrong Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type) →
      IsDefEqStrong Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type)

/-- A generated reduction-site certificate determines its finite local
contraction.  Soundness is assembled from the local beta collapse and the
registered tower equation applied along the retained capture spine; it is
not supplied by pattern membership. -/
def _root_.Lean4Lean.Pattern.IotaReductionSite.action
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {Γ : List SExpr} {recLs ctorLs : List SLevel}
    {recArgs ctorArgs : List SExpr} {majorTerm A : SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureTyping : Pattern.CaptureTyping Γ mcap captureType}
    (site : Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
      majorTerm A mcap captureType captureTyping) :
    Pattern.Action Γ r
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
      recLs mcap A := by
  have hregistered : IsDefEq Γ
      (SExpr.mkInst recLs rule.df.lhs) (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.type) :=
    .extra rule.registered site.levelsLength
  have hspine := site.captureSpine.toSpineWF captureTyping.typed
  have happlied := hspine.congr hregistered
  have hsound := site.lhsCollapse.trans happlied
  rw [rule.rhsApply recLs mcap] at hsound
  exact {
    pat := rule.pat
    matched := site.matched
    dfs := site.dfs
    defeqs := site.defeqs
    checked := site.checked
    sound := hsound }

/-- Translate Theory's evidence-rich judgment directly.  Unlike the former
admitted `SExpr.IsDefEq.strong`, this theorem never tries to recover missing
typing premises from a raw SExpr derivation. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqStrong.mkS [Params.Semantic]
    (H : Params.env.IsDefEqStrong Params.univs Γ e₁ e₂ A) :
    IsDefEqStrong (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  induction H with
  | bvar h _ _ ihA => exact .bvar (SExpr.Lookup.mkS h) ihA
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sortDF l l' Γ hl hl' heq =>
    have hll := SLevel.mk_eq hl hl' heq
    have hsucc : SLevel.mk l.succ = (SLevel.mk l').succ := by
      rw [SLevel.mk_succ hl, hll]
    simpa only [mk, hll, hsucc] using (IsDefEqStrong.sort (Γ := Γ.map mk)
      (l := SLevel.mk l'))
  | @constDF c ci ls ls' u Γ hci hls hls' hlen hlevels _ _ _ ihGlobal ihLocal =>
    have hmap := SLevel.map_mk_eq hls hls' hlevels
    change IsDefEqStrong (Γ.map mk)
      (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    rw [← hmap]
    have ihLocal' := ihLocal
    rw [← mkInst_map_mk hls, ← mkInst_map_mk hls', ← hmap] at ihLocal'
    have htype : IsDefEqStrong (Γ.map mk)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type)
        (.sort (SLevel.mk u)) := by
      simpa only [mk] using ihLocal'
    let F : ∀ cl, CtorBundle c cl := fun cl =>
      (Params.Semantic.ctor (ls := ls.map SLevel.mk) (Γ := Γ.map mk)
        hci (by simpa using hlen) cl).1
    have hF : ∀ cl, IsDefEqStrong (Γ.map mk)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type) ((F cl).rhs (ls.map SLevel.mk))
        (.sort (F cl).u) := by
      intro cl
      exact (Params.Semantic.ctor (ls := ls.map SLevel.mk) (Γ := Γ.map mk)
        hci (by simpa using hlen) cl).2
    have hDef : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong (Γ.map mk) (r.1.applyS (ls.map SLevel.mk) Empty.elim)
          (.const c (ls.map SLevel.mk))
          (SExpr.mkInst (ls.map SLevel.mk) ci.type) := by
      intro r hpat
      obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
      subst r
      simpa only [Pattern.RHS.applyS] using
        (hdef hci (by simpa using hlen) : IsDefEqStrong (Γ.map mk)
          (.const c (ls.map SLevel.mk)) (SExpr.mkInst (ls.map SLevel.mk) value)
          (SExpr.mkInst (ls.map SLevel.mk) ci.type)).symm
    simpa only [mkInst_map_mk hls] using
      (IsDefEqStrong.const hci (by simpa using hlen) htype F hF hDef)
  | appDF _ _ _ _ _ _ _ ihA _ ihf iha ihB =>
    have ihB' := ihB
    simp only [mk, mk_instExpr] at ihB'
    simpa only [mk, mk_instExpr] using IsDefEqStrong.appDF ihA ihf iha ihB'
  | lamDF _ _ _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    exact .lamDF ihA ihB ihBody ihBody'
  | forallEDF hu hv _ _ _ ihA ihBody ihBody' =>
    simpa only [mk, SLevel.mk_imax hu hv] using
      IsDefEqStrong.forallEDF ihA ihBody ihBody'
  | defeqDF _ _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ _ _ _ _ ihA ihB ihBody ihArg ihResult ihInst =>
    have ihResult' := ihResult
    have ihInst' := ihInst
    simp only [mk, mk_instExpr] at ihResult' ihInst'
    have hlam := IsDefEqStrong.lamDF ihA ihB ihBody ihBody
    have happ := IsDefEqStrong.appDF ihA hlam ihArg ihResult'
    simpa only [mk, mk_instExpr] using
      IsDefEqStrong.beta ihBody ihArg happ ihInst'
  | @eta Γ A u B v e _ _ _ _ _ _ _ _
      ihA ihB _ ihe iheWeak ihAWeak =>
    have ihAWeak' : IsDefEqStrong (mk A :: Γ.map mk)
        (mk A).lift (mk A).lift (.sort (SLevel.mk u)) := by
      simpa only [List.map_cons, mk, mk_lift] using ihAWeak
    have iheWeak' : IsDefEqStrong (mk A :: Γ.map mk)
        (mk e).lift (mk e).lift
        (.forallE (mk A).lift (mk (B.liftN 1 1))) := by
      simpa only [List.map_cons, mk, mk_lift] using iheWeak
    have hbvar : IsDefEqStrong (mk A :: Γ.map mk)
        (.bvar 0) (.bvar 0) (mk A).lift :=
      .bvar .zero ihAWeak'
    have hresult : (mk (B.liftN 1 1)).inst (.bvar 0) = mk B := by
      change (mk (B.liftN 1 1)).inst (mk (.bvar 0)) = mk B
      rw [← mk_instExpr]
      exact congrArg mk (VExpr.instN_bvar0 B 0)
    have happ : IsDefEqStrong (mk A :: Γ.map mk)
        (.app (mk e).lift (.bvar 0)) (.app (mk e).lift (.bvar 0)) (mk B) := by
      rw [← hresult]
      exact IsDefEqStrong.appDF ihAWeak' iheWeak' hbvar (hresult ▸ ihB)
    have hlam := IsDefEqStrong.lamDF ihA ihB happ happ
    simpa only [mk, mk_lift] using IsDefEqStrong.eta ihe hlam
  | structEta hreg _ _ _ _ _ _ _ _ ihType ihMajor ihRebuild =>
    exact Params.Semantic.structureEta hreg ihRebuild ihMajor
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @extra df ls u Γ hreg hlevels hlen _ _ _ _ _ _ _ _ _ ihLhs ihRhs =>
    have ihLhs' := ihLhs
    have ihRhs' := ihRhs
    rw [← mkInst_map_mk hlevels, ← mkInst_map_mk hlevels] at ihLhs' ihRhs'
    simpa only [mkInst_map_mk hlevels] using
      (Params.Semantic.registered (Γ := Γ.map mk) (ls := ls.map SLevel.mk)
        hreg (by simpa using hlen) ihLhs' ihRhs')

theorem IsDefEqStrong.defeq : IsDefEqStrong Γ e1 e2 A → Γ ⊢ e1 ≡ e2 : A := by
  intro H
  induction H with
  | bvar h _ _ => exact .bvar h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | trans' _ _ ih₁ ih₂ => exact ih₁.trans' ih₂
  | sort => exact .sort
  | const hreg hlen _ _ _ => exact .const hreg hlen
  | appDF _ _ _ _ _ ihf iha _ => exact .appDF ihf iha
  | lamDF _ _ _ _ ihA _ ihBody _ => exact .lamDF ihA ihBody
  | forallEDF _ _ _ ihA ihBody _ => exact .forallEDF ihA ihBody
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ ihBody ihArg _ _ => exact .beta ihBody ihArg
  | eta _ _ ihe _ => exact .eta ihe
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | extra action _ _ _ _ => exact action.sound

theorem _root_.Lean4Lean.Params.ctor_ty [Params.Semantic]
    (hcl1 : Params.classify c = some cl) (hcl2 : cl matches .ctor .. | .etaCtor ..)
    (hci : env.constants c = some ci) (h_len : ls.length = ci.uvars) :
    ∃ (I : Name) (Ts args : List SExpr) (u : SLevel),
      Ts.length = cl.arity ∧ Params.classify I = some (.indTy args.length) ∧ u ≠ .zero ∧
      Γ ⊢ SExpr.mkInst ls ci.type ≡
        Ts.foldr .forallE (args.foldr (fun A acc => acc.app A) (.const I ls)) : .sort u := by
  let hctor : CtorBundle.IsCtor c := by
    refine ⟨cl, hcl1, ?_⟩
    cases cl <;> simp_all
  have hcl : hctor.cl.1 = cl := by
    have hc := hctor.cl.2.1
    exact (Option.some.inj (hcl1.symm.trans hc)).symm
  let ⟨F, hF⟩ := Params.Semantic.ctor (ls := ls) (Γ := Γ) hci h_len hctor
  refine ⟨F.I, F.Ts, F.args, F.u, ?_, F.hclI, F.hu0, hF.defeq⟩
  simpa only [hcl] using F.hlen

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- SExpr-side analog of `HasTypeStratified`: a typing derivation indexed by
its tree depth `n`, used for well-founded induction on stratification. -/
inductive HasTypeStratifiedS : List SExpr → SExpr → SExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : Γ ⊢ .sort l :! .sort (.succ l) !! n
  | const :
    env.constants c = some ci →
    ls.length = ci.uvars →
    Γ ⊢ (mk ci.type).instL ls : .sort u !! n →
    Γ ⊢ .const c ls :! (mk ci.type).instL ls !! n+1
  | app :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
    Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

scoped notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
scoped notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

theorem HasTypeStratifiedS.mono (le : m ≤ n)
    (H : HasTypeStratifiedS Γ e A b m) : HasTypeStratifiedS Γ e A b n := by
  induction H generalizing n with
  | bvar h _ ih =>
    let n + 1 := n
    exact .bvar h (ih (Nat.le_of_succ_le_succ le))
  | sort' => exact .sort'
  | const hreg hlen _ ih =>
    let n + 1 := n
    exact .const hreg hlen (ih (Nat.le_of_succ_le_succ le))
  | app _ _ _ _ _ ihA ihB ihf iha ihR =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .app (ihA le) (ihB le) (ihf le) (iha le) (ihR le)
  | lam _ _ _ _ ihA ihB ihBody ihPi =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .lam (ihA le) (ihB le) (ihBody le) (ihPi le)
  | forallE _ _ ihA ihBody =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .forallE (ihA le) (ihBody le)
  | base _ ih => exact .base (ih le)
  | defeq h _ _ _ ihA ihB ihe =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .defeq h (ihA le) (ihB le) (ihe le)

theorem HasTypeStratifiedS.to_core (H : Γ ⊢ e : A !! n) :
    ∃ A', Γ ⊢ e :! A' !! n := by
  generalize hb : true = b at H
  induction H with cases hb
  | base h _ => exact ⟨_, h⟩
  | defeq _ _ _ _ _ _ ih =>
    obtain ⟨A', hA'⟩ := ih rfl
    exact ⟨A', hA'.mono (Nat.le_succ _)⟩

theorem HasTypeStratifiedS.isType (H : HasTypeStratifiedS Γ e A b n) :
    ∃ u, Γ ⊢ A : .sort u !! n - 1 := by
  induction H with
  | base _ ih => exact ih
  | bvar _ h => exact ⟨_, h⟩
  | const _ _ h => exact ⟨_, h⟩
  | app _ _ _ _ h => exact ⟨_, h⟩
  | lam _ _ _ h => exact ⟨_, h⟩
  | defeq _ _ h => exact ⟨_, h⟩
  | @sort' _ l _ => exact ⟨_, .base (.sort' (l := l.succ))⟩
  | @forallE _ A u _ body v _ _ => exact ⟨_, .base (.sort' (l := .imax u v))⟩

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst (Γ : List SExpr) : SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.lookup (H : Ctx.Subst HasType Γ σ Δ) :
    Lookup Δ i A → HasType Γ (σ i) (A.subst σ) := by
  intro h
  induction H generalizing i A with
  | nil => cases h
  | @cons Δ σ A₀ H hhead ih =>
    cases h with
    | zero =>
      simpa only [show σ 0 = σ.head from rfl, SExpr.lift_subst] using hhead
    | succ h =>
      change HasType Γ (σ.tail _) (_)
      simpa only [SExpr.lift_subst] using ih h

/-- Change only the evidence relation carried by a substitution. -/
theorem Ctx.Subst.imp
    (f : ∀ {Γ e A}, HasType Γ e A → HasType' Γ e A)
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType' Γ σ Δ := by
  induction H with
  | nil => exact .nil
  | cons _ h ih => exact .cons ih (f h)

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lift_r
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (H1 : Ctx.Subst HasType Θ σ Γ) (H2 : Ctx.Lift' ρ Θ Δ) :
    Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := by
  induction H1 with
  | nil => exact .nil
  | @cons Δ' σ' A H h ih =>
    refine .cons ih ?_
    change HasType Δ (σ'.head.lift' ρ) (A.subst (σ'.tail.lift_r ρ))
    rw [← SExpr.lift'_subst]
    exact weak H2 h

theorem Ctx.Subst.lift
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  refine .cons (this ▸ .lift_r weak H .one) (this ▸ bvar ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .zero

theorem Ctx.Subst.id
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A) :
    ∀ {Γ}, Ctx.Subst HasType Γ .id Γ
  | [] => .nil
  | A :: Γ => by
    have htail : SExpr.Subst.id.tail = SExpr.Subst.id.lift_r (.skip .refl) := by
      funext i
      rfl
    refine .cons (htail ▸ (Ctx.Subst.id weak bvar).lift_r weak (.skip .refl)) ?_
    change HasType (A :: Γ) (.bvar 0) (A.subst SExpr.Subst.id.tail)
    rw [htail, ← SExpr.lift'_subst, SExpr.subst_id]
    exact bvar .zero

theorem Ctx.Subst.one
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons (.id weak bvar) (by simpa)

inductive Ctx.SubstEq (Γ₀ : List SExpr) : SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.SubstEq Γ₀ .id .id Γ₀
  /-- A pure context embedding is an equality substitution.  This base case
  is what makes equality substitutions stable under entering a binder; the
  old identity-only relation could not represent the weakened tail of a
  lifted substitution. -/
  | ofLift : Ctx.Lift' ρ Γ Γ₀ → Ctx.SubstEq Γ₀ ρ.toSubst ρ.toSubst Γ
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ A : .sort u →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)

theorem Ctx.Subst.ofLookup
    (H : ∀ {i A}, Lookup Δ i A → HasType Γ (σ i) (A.subst σ)) :
    Ctx.Subst HasType Γ σ Δ := by
  induction Δ generalizing σ with
  | nil => exact .nil
  | cons A Δ ih =>
    refine .cons (ih (σ := σ.tail) fun {i B} h => ?_) ?_
    · change HasType Γ (σ (i + 1)) (B.subst σ.tail)
      simpa only [SExpr.lift_subst] using H (.succ h)
    · change HasType Γ (σ 0) (A.subst σ.tail)
      simpa only [SExpr.lift_subst] using H (.zero (ty := A) (Γ := Δ))

theorem Ctx.Lift'.toSubst (W : Ctx.Lift' ρ Γ Γ') :
    Ctx.Subst (· ⊢ · : ·) Γ' ρ.toSubst Γ := by
  apply Ctx.Subst.ofLookup
  intro i A h
  simpa only [Lift.toSubst_apply, SExpr.subst_toSubst] using
    (IsDefEq.bvar (h.weak' W))

theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ := by
  induction W with
  | nil =>
    apply Ctx.Subst.ofLookup
    intro i A h
    change Γ₀ ⊢ SExpr.Subst.id i : A.subst SExpr.Subst.id
    rw [SExpr.subst_id]
    exact IsDefEq.bvar h
  | ofLift W => exact W.toSubst
  | cons _ _ h ih => exact .cons ih h.hasType.1

/-- Forget the right side of an equality substitution while retaining the
same evidence format.  This is the diagonal used by simultaneous
heterogeneous substitution proofs. -/
theorem Ctx.SubstEq.leftEq (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₀ σ σ Γ := by
  induction W with
  | nil => exact .nil
  | ofLift W => exact .ofLift W
  | cons _ hA hhead ih => exact .cons ih hA hhead.hasType.1

theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  intro h
  induction W generalizing i A with
  | nil =>
    change Γ₀ ⊢ .bvar i ≡ .bvar i : A.subst .id
    rw [subst_id]
    exact .bvar h
  | ofLift W =>
    simpa only [Lift.toSubst_apply, SExpr.subst_toSubst] using
      (IsDefEq.bvar (h.weak' W))
  | cons W' hA' hhead ih =>
    cases h with
    | zero =>
      simp only [show ∀ (s : SExpr.Subst), s 0 = s.head from fun _ => rfl, lift_subst]
      exact hhead
    | succ h' =>
      simp only [show ∀ (s : SExpr.Subst) n, s (n+1) = s.tail n from fun _ _ => rfl,
        lift_subst]
      exact ih h'

/-- The core weakening proof is placed before equality-substitution lifting:
the latter must weaken every equality stored in the substitution. -/
theorem IsDefEq.weakCore (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [((henv.closedC h1).mkInstS).lift'_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => refine cast ?_ (IsDefEq.eta (ih W)); congr 1; simp [← SExpr.lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkInstS.lift'_eq .zero, hA2.mkInstS.lift'_eq .zero,
      hA3.mkInstS.lift'_eq .zero]
    exact .extra h1 h2

theorem Ctx.SubstEq.weak' (W₀ : Ctx.Lift' ρ Γ₀ Γ₁)
    (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₁ (σ.lift_r ρ) (σ'.lift_r ρ) Γ := by
  induction W with
  | nil =>
    have hσ : SExpr.Subst.id.lift_r ρ = ρ.toSubst := by
      funext i
      rfl
    simpa only [hσ] using Ctx.SubstEq.ofLift W₀
  | @ofLift ρ' Γ' W' =>
    have h := Ctx.SubstEq.ofLift (W'.comp W₀)
    have heq : ρ'.toSubst.lift_r ρ = (ρ'.comp ρ).toSubst := by
      funext i
      simp only [SExpr.Subst.lift_r, Lift.toSubst_apply, SExpr.lift',
        Lift.liftVar_comp]
    simpa only [heq] using h
  | @cons Γ' A u τ τ' W hA hhead ih =>
    have ht : (τ.lift_r ρ).tail = τ.tail.lift_r ρ := by
      funext i
      rfl
    have ht' : (τ'.lift_r ρ).tail = τ'.tail.lift_r ρ := by
      funext i
      rfl
    refine .cons ?_ hA ?_
    · simpa only [ht, ht'] using ih
    · rw [ht, ← SExpr.lift'_subst]
      exact hhead.weakCore W₀

theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (hA : Γ ⊢ A : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  have W' := W.weak' (Ctx.Lift'.one (Γ := Γ₀) (A := A.subst σ))
  have hσ : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i
    rfl
  have hσ' : σ'.lift.tail = σ'.lift_r (.skip .refl) := by
    funext i
    rfl
  refine .cons (σ := σ.lift) (σ' := σ'.lift) ?_ hA ?_
  · simpa only [hσ, hσ'] using W'
  · rw [hσ, ← SExpr.lift'_subst]
    exact IsDefEq.bvar (Lookup.zero (ty := A.subst σ) (Γ := Γ₀))

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := H.weakCore W

/-- Weak definitional equality is stable under one typed substitution.

The two endpoints deliberately use the same substitution.  Heterogeneous
substitution needs the domain/codomain evidence retained by
`IsDefEqStrong`; erasing that evidence first makes the corresponding claim
false for dependent application and beta. -/
theorem IsDefEq.subst (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Γ₀ σ Γ)
    (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ := by
  induction H generalizing Γ₀ σ with
  | bvar h => exact W.lookup h
  | symm _ ih => exact (ih W).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ W).trans (ih₂ W)
  | trans' _ _ ih₁ ih₂ => exact (ih₁ W).trans' (ih₂ W)
  | sort => exact .sort
  | const hreg hlen =>
    rw [((henv.closedC hreg).mkInstS).subst_eq .zero]
    exact .const hreg hlen
  | appDF _ _ ihf iha =>
    rw [SExpr.subst_inst]
    exact .appDF (ihf W) (iha W)
  | lamDF _ _ ihA ihBody =>
    exact .lamDF (ihA W)
      (by simpa only [SExpr.subst] using
        ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
  | forallEDF _ _ ihA ihBody =>
    exact .forallEDF (ihA W)
      (by simpa only [SExpr.subst] using
        ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA W) (ihe W)
  | beta _ _ ihBody ihArg =>
    simpa only [SExpr.subst, SExpr.subst_inst] using
      (IsDefEq.beta
        (by simpa only [SExpr.subst] using
          ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
        (ihArg W))
  | @eta Γ e A B _ ihe =>
    have hout := IsDefEq.eta (ihe W)
    have htail : σ.lift.tail = σ.lift_r (.skip .refl) := by
      funext i
      rfl
    have heq : e.lift.subst σ.lift = (e.subst σ).lift := by
      rw [SExpr.lift_subst, htail, ← SExpr.lift'_subst]
    simpa only [SExpr.subst, SExpr.Subst.lift, heq] using hout
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp W) (ihh W) (ihh' W)
  | extra hreg hlen =>
    have ⟨⟨hlhs, _⟩, hrhs, htype⟩ := henv.closed.2 hreg
    rw [hlhs.mkInstS.subst_eq .zero, hrhs.mkInstS.subst_eq .zero,
      htype.mkInstS.subst_eq .zero]
    exact .extra hreg hlen

/-- A strong derivation retains enough local validity evidence to show that
each endpoint respects an equality substitution.  Both conclusions are
typed at the left-substituted source type; keeping them together makes
symmetry and transitivity structural instead of requiring an invalid
symmetry operation on weak equality substitutions. -/
theorem IsDefEqStrong.substCongr (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : IsDefEqStrong Γ e1 e2 A) :
    (Γ₀ ⊢ e1.subst σ ≡ e1.subst σ' : A.subst σ) ∧
    (Γ₀ ⊢ e2.subst σ ≡ e2.subst σ' : A.subst σ) := by
  induction H generalizing Γ₀ σ σ' with
  | bvar h _ _ =>
    exact ⟨W.lookup h, W.lookup h⟩
  | symm _ ih =>
    exact ⟨(ih W).2, (ih W).1⟩
  | trans _ _ ih₁ ih₂ =>
    exact ⟨(ih₁ W).1, (ih₂ W).2⟩
  | trans' h₁ h₂ ih₁ ih₂ =>
    have hsame₁ := h₁.defeq.subst W.left
    have hsame₂ := h₂.defeq.subst W.left
    have hcross₂ := hsame₂.trans (ih₂ W).2
    have hsame := hsame₁.trans' hsame₂
    have hcross := hsame₁.trans' hcross₂
    exact ⟨(ih₁ W).1, hsame.symm.trans hcross⟩
  | sort =>
    exact ⟨.sort, .sort⟩
  | const hreg hlen _ _ _ =>
    constructor <;>
      rw [((henv.closedC hreg).mkInstS).subst_eq .zero] <;>
      exact .const hreg hlen
  | @appDF Γ A u f f' B a a' v hA hf ha hB ihA ihf iha ihB =>
    have hf' := ihf W
    have ha' := iha W
    have hcod : Γ₀ ⊢
        (B.subst σ.lift).inst (a.subst σ) ≡
        (B.subst σ.lift).inst (a'.subst σ) : .sort v := by
      simpa only [SExpr.subst, SExpr.subst_inst] using hB.defeq.subst W.left
    constructor
    · simpa only [SExpr.subst, SExpr.subst_inst] using
        (IsDefEq.appDF hf'.1 ha'.1)
    · have happ := IsDefEq.appDF hf'.2 ha'.2
      have happ' := hcod.symm.defeqDF happ
      simpa only [SExpr.subst, SExpr.subst_inst] using happ'
  | @lamDF Γ A A' u B v body body' hA hB hBody hBody'
      ihA ihB ihBody ihBody' =>
    have WA := W.lift hA.defeq.hasType.1
    have WA' := W.lift hA.defeq.hasType.2
    have hdom := ihA W
    have hbody := ihBody WA
    have hbody' := ihBody' WA'
    constructor
    · simpa only [SExpr.subst] using
        (IsDefEq.lamDF hdom.1 hbody.1)
    · have hlam := IsDefEq.lamDF hdom.2 hbody'.2
      have hPi : Γ₀ ⊢
          .forallE (A.subst σ) (B.subst σ.lift) ≡
          .forallE (A'.subst σ) (B.subst σ.lift) : .sort (.imax u v) :=
        .forallEDF (hA.defeq.subst W.left)
          (hB.defeq.subst (W.left.lift IsDefEq.weakCore IsDefEq.bvar))
      simpa only [SExpr.subst] using hPi.symm.defeqDF hlam
  | @forallEDF Γ A A' u body body' v hA hBody hBody'
      ihA ihBody ihBody' =>
    have hdom := ihA W
    constructor
    · simpa only [SExpr.subst] using
        (IsDefEq.forallEDF hdom.1
          (ihBody (W.lift hA.defeq.hasType.1)).1)
    · simpa only [SExpr.subst] using
        (IsDefEq.forallEDF hdom.2
          (ihBody' (W.lift hA.defeq.hasType.2)).2)
  | defeqDF hA _ ihA ihe =>
    have htype := hA.defeq.subst W.left
    exact ⟨htype.defeqDF (ihe W).1, htype.defeqDF (ihe W).2⟩
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    exact ⟨(ihApp W).1, (ihInst W).1⟩
  | eta _ _ ihe ihLam =>
    exact ⟨(ihLam W).1, (ihe W).1⟩
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact ⟨(ihh W).1, (ihh' W).1⟩
  | extra _ _ _ ihLeft ihRight =>
    exact ⟨(ihLeft W).1, (ihRight W).1⟩

/-- Heterogeneous substitution for the evidence-rich judgment, returned in
the weak judgment consumed by the logical relation. -/
theorem IsDefEqStrong.subst (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : IsDefEqStrong Γ e1 e2 A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.defeq.subst W.left).trans (H.substCongr W).2

/-- A certified local contraction remains certified after weakening.  The
finite check list is transported pointwise, so downstream reduction rules do
not need to unpack and rebuild the certificate themselves. -/
def _root_.Lean4Lean.Pattern.Action.weak' (action : Pattern.Action Γ r e m1 m2 A)
    (W : Ctx.Lift' ρ Γ Γ') :
    Pattern.Action Γ' r (e.lift' ρ) m1
      (fun path => (m2 path).lift' ρ) (A.lift' ρ) := by
  let dfs' := action.dfs.map fun d =>
    (d.1.lift' ρ, d.2.1.lift' ρ, d.2.2.lift' ρ)
  refine {
    pat := action.pat
    matched := action.matched.lift'
    dfs := dfs'
    defeqs := ?_
    checked := ?_
    sound := ?_ }
  · rw [← Pattern.Check.defeqsS_lift', ← action.defeqs]
    simp [dfs', Function.comp_def]
  · intro a b B hab
    simp only [dfs', List.mem_map] at hab
    obtain ⟨⟨B₀, a₀, b₀⟩, hab, heq⟩ := hab
    have hB : B₀.lift' ρ = B := congrArg Prod.fst heq
    have hab' : (a₀.lift' ρ, b₀.lift' ρ) = (a, b) := congrArg Prod.snd heq
    have ha : a₀.lift' ρ = a := congrArg Prod.fst hab'
    have hb : b₀.lift' ρ = b := congrArg Prod.snd hab'
    subst B
    subst a
    subst b
    exact (action.checked a₀ b₀ B₀ hab).weak' W
  · simpa only [Pattern.RHS.lift'_applyS] using action.sound.weak' W

/-- A certified local contraction remains certified after a genuinely typed
substitution.  In particular, generated-rule checks and the final local
equality are transported by the same weak-defeq substitution theorem. -/
def _root_.Lean4Lean.Pattern.Action.subst
    (action : Pattern.Action Γ r e m1 m2 A)
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ) :
    Pattern.Action Δ r (e.subst σ) m1
      (fun path => (m2 path).subst σ) (A.subst σ) := by
  let dfs' := action.dfs.map fun d =>
    (d.1.subst σ, d.2.1.subst σ, d.2.2.subst σ)
  refine {
    pat := action.pat
    matched := action.matched.subst
    dfs := dfs'
    defeqs := ?_
    checked := ?_
    sound := ?_ }
  · rw [← Pattern.Check.defeqsS_subst, ← action.defeqs]
    simp [dfs', Function.comp_def]
  · intro a b B hab
    simp only [dfs', List.mem_map] at hab
    obtain ⟨⟨B₀, a₀, b₀⟩, hab, heq⟩ := hab
    have hB : B₀.subst σ = B := congrArg Prod.fst heq
    have hab' : (a₀.subst σ, b₀.subst σ) = (a, b) := congrArg Prod.snd heq
    have ha : a₀.subst σ = a := congrArg Prod.fst hab'
    have hb : b₀.subst σ = b := congrArg Prod.snd hab'
    subst B
    subst a
    subst b
    exact (action.checked a₀ b₀ B₀ hab).subst W
  · simpa only [Pattern.RHS.subst_applyS] using action.sound.subst W

/-- A lookup remains typable when one older context entry is replaced by a
definitionally equal type.  The distinguished lookup is the only case that
needs conversion; entries above it are weakened and entries below it are
unchanged. -/
theorem Lookup.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h : Lookup (Δ ++ A :: Γ) i B) : Δ ++ A' :: Γ ⊢ .bvar i : B := by
  induction Δ generalizing i B with
  | nil =>
    cases h with
    | zero =>
      exact (h1.weak' (.skip .refl)).symm.defeqDF (.bvar .zero)
    | succ h => exact .bvar (.succ h)
  | cons D Δ ih =>
    cases h with
    | zero => exact .bvar .zero
    | succ h =>
      simpa only [List.cons_append, SExpr.lift, SExpr.lift', Lift.liftVar] using
        (ih h).weak' (.skip .refl)

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) : Δ++A'::Γ ⊢ e1 ≡ e2 : B := by
  generalize hctx : Δ ++ A :: Γ = Γ₁ at h2
  induction h2 generalizing Δ with
  | bvar h =>
    rw [← hctx] at h
    exact h.defeqDF_l' h1
  | symm _ ih => exact (ih hctx).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hctx).trans (ih₂ hctx)
  | trans' _ _ ih₁ ih₂ => exact (ih₁ hctx).trans' (ih₂ hctx)
  | sort => exact .sort
  | const hreg hlen => exact .const hreg hlen
  | appDF _ _ ihf iha => exact .appDF (ihf hctx) (iha hctx)
  | lamDF _ _ ihA ihBody =>
    exact .lamDF (ihA hctx)
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx))
  | forallEDF _ _ ihA ihBody =>
    exact .forallEDF (ihA hctx)
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx))
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hctx) (ihe hctx)
  | beta _ _ ihBody ihArg =>
    exact .beta
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx)) (ihArg hctx)
  | eta _ ih => exact .eta (ih hctx)
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp hctx) (ihh hctx) (ihh' hctx)
  | extra hreg hlen => exact .extra hreg hlen

theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
scoped notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

theorem WithLift.imp
    (imp : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq' Γ e1 e2 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq' Γ e1 e2 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := imp (H.defeq' W' h1 h2 h3)
  left' _ _ _ _ W' h1 hA := imp (H.left' W' h1 hA)
  right' _ _ _ _ W' h1 hA := imp (H.right' W' h1 hA)

theorem WithLift.refl
    (refl : ∀ {ρ Δ e' A'}, Ctx.Lift' ρ Δ Γ →
      e = .lift' e' ρ → A = .lift' A' ρ → DefEq Δ e' e' A')
    : WithLift DefEq Γ e e A where
  defeq' _ _ _ _ _ W := by rintro rfl he rfl; cases SExpr.lift'_inj.1 he; exact refl W rfl rfl
  left' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl
  right' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl

theorem WithLift.weak'
    (weak : ∀ {ρ Γ Δ e1 e2 A}, Ctx.Lift' ρ Γ Δ → DefEq Γ e1 e2 A →
      DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ))
    (W : Ctx.Lift' ρ Γ Δ) (H : WithLift DefEq Γ e1 e2 A) :
    WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) where
  defeq' Δ' ρ' e1' e2' A' W' h1 h2 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨e2, rfl, rfl⟩ := lift_eq_lift h2
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.defeq' I.symm.diff rfl rfl rfl)
  left' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.left' I.symm.diff rfl rfl)
  right' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.right' I.symm.diff rfl rfl)

theorem IsDefEqLift.weak' : Ctx.Lift' ρ Γ Δ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ := WithLift.weak' IsDefEq.weak'

/-- A lowering-stable equality may always be instantiated as an ordinary
typed equality.  This is the sound substitution fact that does not claim the
result still has universal inverse-weakening closure. -/
theorem IsDefEqLift.substDefEq
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ)
    (H : Γ ⊢ e1 ≡ e2 :↑ A) :
    Δ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ :=
  (H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm
    SExpr.lift'_refl.symm).subst W

theorem IsDefEqLift.subst : Ctx.Subst HasType Δ σ Γ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.subst σ ≡ e2.subst σ :↑ A.subst σ := sorry

theorem WithLift.weak'_inv (W : Ctx.Lift' ρ Γ Δ)
    (H : WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ)) : WithLift DefEq Γ e1 e2 A where
  defeq' Δ' ρ' _ _ _ W' := by
    rintro rfl rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.defeq' (W'.comp W) rfl rfl rfl
  left' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.left' (W'.comp W) rfl rfl
  right' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.right' (W'.comp W) rfl rfl

nonrec theorem IsDefEqLift.weak'_inv : Ctx.Lift' ρ Γ Δ →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ → Γ ⊢ e1 ≡ e2 :↑ A := .weak'_inv

theorem WithLift.symm
    (symm : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq Γ e2 e1 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e1 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := symm (H.defeq' W' h2 h1 h3)
  left' _ _ _ _ W' h1 hA := H.right' W' h1 hA
  right' _ _ _ _ W' h1 hA := H.left' W' h1 hA

nonrec theorem IsDefEqLift.symm : Γ ⊢ e1 ≡ e2 :↑ A → Γ ⊢ e2 ≡ e1 :↑ A := .symm .symm

theorem WithLift.left (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e1 e1 A :=
  .refl (H.left' ·)

theorem WithLift.right (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e2 A :=
  .refl (H.right' ·)

theorem IsDefEqLift.left (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 :↑ A where
  defeq' _ _ _ _ _ W' := by rintro rfl he hA; exact SExpr.lift'_inj.1 he ▸ H.left' W' rfl hA
  left' := H.left'
  right' := H.left'

theorem WithLift.defeq (H : WithLift DefEq Γ e1 e2 A) : DefEq Γ e1 e2 A :=
  H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm SExpr.lift'_refl.symm

nonrec theorem IsDefEqLift.defeq (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 ≡ e2 : A := H.defeq

variable (Γ₀ : List SExpr) in
inductive IsDefEqCtx : List SExpr → List SExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEq.defeqDFC' (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' h2)

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A := .defeqDFC' (Δ := []) h1 h2

omit [Params] in theorem Subpattern.varN_constS (H : Subpattern p (.varN (.const c) n)) :
    ∃ n, p = .varN (.const c) n := by
  generalize eq : Pattern.varN (.const c) n = p' at H
  induction H generalizing n with
  | refl => exact ⟨_, eq.symm⟩
  | appL | appR => cases n <;> cases eq
  | varL _ ih => cases n <;> cases eq; exact ih rfl

theorem Params.simple_appS (H : Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    .app p₁ p₂ = p := by
  obtain ⟨_|_, rfl⟩ := Params.pat_simple H <;> cases h
  · rfl
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_constS ‹_›
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_constS ‹_›

/-- A function spine whose next argument is inspected by a registered
pattern.  This is the SExpr counterpart of Theory's `VEnv.IsMajorPremise`;
it is what permits weak-head reduction inside an iota major premise before
the proof-carrying pattern contraction fires. -/
def IsMajorPremise (e : SExpr) :=
  ∃ p, (∃ r, Pat p r) ∧ ∃ p₁ p₂, Subpattern (.app p₁ p₂) p ∧
    ∃ m1 m2, p₁.MatchesS e m1 m2

theorem IsMajorPremise.lift' {e : SExpr} {ρ : Lift} :
    IsMajorPremise (e.lift' ρ) ↔ IsMajorPremise e := by
  constructor <;> intro ⟨_, h1, _, _, h2, _, _, h3⟩
  · obtain ⟨_, h4, _⟩ := Pattern.matchesS_lift'.1 h3
    exact ⟨_, h1, _, _, h2, _, _, h4⟩
  · exact ⟨_, h1, _, _, h2, _, _, h3.lift'⟩

theorem IsMajorPremise.subst {e : SExpr} {σ : Subst} :
    IsMajorPremise e → IsMajorPremise (e.subst σ)
  | ⟨_, h1, _, _, h2, _, _, h3⟩ =>
    ⟨_, h1, _, _, h2, _, _, h3.subst⟩

theorem IsMajorPremise.lam : ¬IsMajorPremise (.lam A e) := nofun

theorem Params.pat_not_varS : ¬Pat (.var p) r := (nomatch Params.pat_simple ·)

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  /-- A local extension contraction consumes the same finite certificate as
  strong equality; pattern membership alone is not operational evidence. -/
  | extra : Pattern.Action Γ r e m1 m2 A →
    Γ ⊢ e ⤳ r.1.applyS m1 m2

theorem WHRed.subst
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ) :
    Γ ⊢ e1 ⤳ e2 → Δ ⊢ e1.subst σ ⤳ e2.subst σ
  | .app h1 => .app (h1.subst W)
  | .major h1 h2 => .major h1.subst (h2.subst W)
  | .beta => subst_inst ▸ .beta
  | @extra _ Γ p r e m1 m2 A action => by
    rw [Pattern.RHS.subst_applyS]
    exact .extra (action.subst W)

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .major h1 h2 => .major (IsMajorPremise.lift'.2 h1) (h2.weak' W)
  | .beta => by rw [SExpr.lift'_inst_hi]; exact .beta
  | @extra _ Γ p r e m1 m2 A action => by
    rw [Pattern.RHS.lift'_applyS]
    exact .extra (action.weak' W)

theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | major h1 h2 ih =>
    let .app .. := e1
    cases he
    obtain ⟨_, rfl, a1⟩ := ih rfl
    exact ⟨_, rfl, .major (IsMajorPremise.lift'.1 h1) a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra => sorry

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.sort : WHNF Γ (.sort A) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.forallE : WHNF Γ (.forallE A B) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.subpattern
    (h1 : Params.Pat p r) (h2 : Subpattern p₁ p) (h3 : p₁ ≠ p)
    (h4 : p₁.MatchesS e m1 m2) : WHNF Γ e := by
  intro _ H2
  obtain ⟨c, n, rfl⟩ : ∃ c n, p₁ = .varN (.const c) n := by
    obtain ⟨_|_, rfl⟩ := Params.pat_simple h1 <;> cases h2 <;>
      first | cases h3 rfl | exact ⟨_, Subpattern.varN_constS ‹_›⟩
  have hn : ∀ r, ¬Params.Pat (.const c) r := fun _ h => by
    cases (Params.pat_uniq h1 h (.trans (.varN .refl) h2) (Pattern.inter_self _)).1
    exact h3.symm (h2.antisymm (.varN .refl))
  clear h3
  induction H2 generalizing n with
  | app r1 ih =>
    let n+1 := n
    let .var h4 := h4
    exact ih _ (.trans (.varL .refl) h2) h4
  | major r1 r2 ih =>
    let n+1 := n
    let .var h4 := h4
    let ⟨p', ⟨_, h1'⟩, p₁', p₂', h2', _, _, h3'⟩ := r1
    cases Params.simple_appS h1' h2'
    obtain ⟨⟨_, n, _⟩ | _, rfl⟩ := Params.pat_simple h1 <;>
      [skip; cases n <;> cases h2]
    have ⟨_, _, _, a1, _a2⟩ := Pattern.matchesS_inter.1
      ⟨⟨_, _, h3'⟩, ⟨_, _, h4⟩⟩
    cases h2 with
    | appL h2 =>
      cases (Params.pat_app_l_uniq h1 h1' .refl .refl h2).symm.trans a1
    | appR h2 =>
      cases (Params.pat_app_uniq h1' h1 .refl .refl .refl
        (.trans (.varL .refl) h2)).symm.trans a1
  | beta => generalize Pattern.varN .. = p' at m1 m2 h4; nomatch h4
  | extra action =>
    have ⟨_, _, _, a1, a2⟩ := Pattern.matchesS_inter.1
      ⟨⟨_, _, action.matched⟩, ⟨_, _, h4⟩⟩
    obtain ⟨⟨_, major, _, _⟩ | _, rfl⟩ := Params.pat_simple h1 <;>
      [skip; cases n <;> cases h2]
    obtain ⟨rfl, eq, _⟩ := Params.pat_uniq h1 action.pat h2 a1
    cases n <;> cases eq
    exact hn _ h1

theorem IsMajorPremise.whnf : IsMajorPremise e → WHNF Γ e := by
  rintro ⟨p, ⟨_, h1⟩, p₁, p₂, h2, _, _, h3⟩
  refine .subpattern h1 (.trans (.appL .refl) h2) ?_ h3
  rintro rfl
  cases h2.antisymm (.appL .refl)

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | major r1 r2 => cases r1.whnf _ l1
    | beta => cases WHNF.lam _ l1
    | extra action =>
      cases action.matched with
      | app r3 =>
        cases IsMajorPremise.whnf ⟨_, ⟨_, action.pat⟩, _, _, .refl, _, _, r3⟩ _ l1
      | var => cases Params.pat_not_varS action.pat
  | major l1 l2 ih =>
    cases H2 with
    | app r1 => cases l1.whnf _ r1
    | major _ r2 => cases ih r2; rfl
    | beta => cases l1.lam
    | extra action =>
      cases action.matched with
      | var => cases Params.pat_not_varS action.pat
      | app _ r4 => cases WHNF.subpattern action.pat (.appR .refl) nofun r4 _ l2
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | major r1 => cases r1.lam
    | beta => rfl
    | extra action => nomatch action.matched
  | extra actionL =>
    cases H2 with
    | beta => nomatch actionL.matched
    | major r1 r2 =>
      cases actionL.matched with
      | var => cases Params.pat_not_varS actionL.pat
      | app _ l4 => cases WHNF.subpattern actionL.pat (.appR .refl) nofun l4 _ r2
    | app r1 =>
      cases actionL.matched with
      | app l3 =>
        cases IsMajorPremise.whnf ⟨_, ⟨_, actionL.pat⟩, _, _, .refl, _, _, l3⟩ _ r1
      | var => cases Params.pat_not_varS actionL.pat
    | extra actionR =>
      have ⟨_, _, _, a1, a2⟩ := Pattern.matchesS_inter.1
        ⟨⟨_, _, actionR.matched⟩, ⟨_, _, actionL.matched⟩⟩
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq actionL.pat actionR.pat .refl a1
      obtain ⟨rfl, rfl⟩ := actionL.matched.determ actionR.matched
      rfl

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.subst
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ)
    (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.subst σ ⤳* e2.subst σ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.subst W)

theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.major (H1 : IsMajorPremise f) (H : Γ ⊢ a ⤳* a') :
    Γ ⊢ f.app a ⤳* f.app a' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.major H1)

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)

scoped notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
inductive ParRed : List SExpr → SExpr → SExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pattern.Action Γ r e m1 m2 A →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.applyS m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫ e2 → Γ' ⊢ e1.lift' ρ ≫ e2.lift' ρ
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .app h1 h2 => .app (h1.weak' W) (h2.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 => .forallE (h1.weak' W) (h2.weak' W.cons)
  | .beta h1 h2 => by rw [SExpr.lift'_inst_hi]; exact (h1.weak' W.cons).beta (h2.weak' W)
  | extra action hred => by
    rw [Pattern.RHS.lift'_applyS]
    exact .extra (action.weak' W) fun a => (hred a).weak' W

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ SExpr.mkInst ls ci.type
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := sorry

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.determ h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort => .sort
  | .const h1 h2 => by rw [(henv.closedC h1).mkInstS.lift'_eq .zero]; exact .const h1 h2
  | .app h1 h2 h3 => SExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort => let .sort _ := e; cases he; exact ⟨_, rfl, .sort⟩
  | const h1 h2 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.closedC h1).mkInstS.lift'_eq .zero).symm, .const h1 h2⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv W; cases F <;> cases a2
    refine ⟨_, by rw [SExpr.lift'_inst_hi], .app a1 a3 (h3.weak'_inv W)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih W.cons rfl
    exact ⟨_, rfl, .lam (h1.weak'_inv W) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv W; cases U <;> cases a2
    obtain ⟨_, rfl, b1⟩ := ih2 W.cons rfl
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv W.cons; cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem InferType.subst (W : Ctx.Subst InferType Δ σ Γ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.subst σ ▷ A.subst σ := by
  induction H generalizing Δ σ with
  | @bvar Γ i A h =>
    simp [SExpr.subst]
    induction W generalizing i A with | nil | @cons Γ σ B W h' ih <;> cases h
    case zero => rw [SExpr.lift, SExpr.subst_lift']; exact h'
    case succ i C h => rw [SExpr.lift, SExpr.subst_lift']; exact ih h
  | sort => exact .sort
  | const h1 h2 =>
    rw [(henv.closedC h1).mkInstS.subst_eq .zero]
    exact .const h1 h2
  | app h1 h2 h3 ih =>
    exact subst_inst ▸ .app (ih W)
      (h2.subst (W.imp InferType.hasType)) (h3.subst W)
  | lam h1 h2 ih => exact .lam (h1.subst W) (ih (W.lift InferType.weak' .bvar))
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallE (ih1 W) (h2.subst (W.imp InferType.hasType))
      (ih2 (W.lift InferType.weak' .bvar))
      (h4.subst ((W.lift InferType.weak' .bvar).imp InferType.hasType))

theorem InferType.inst (H₀ : Γ ⊢ a ▷ A₀) (H : A₀::Γ ⊢ e ▷ A) :
    Γ ⊢ e.inst a ▷ A.inst a := .subst (.one InferType.weak' .bvar H₀) H

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A := sorry

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHRed.parRed (H : Γ ⊢ e ⤳ e') : Γ ⊢ e ≫ e' := by
  induction H with
  | app _ ih => exact .app ih .rfl
  | major _ _ ih => exact .app .rfl ih
  | beta => exact .beta .rfl .rfl
  | extra action => exact .extra action fun _ => .rfl

theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.parRed

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

theorem InferTypeS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A := by
  let ⟨_, h1, h2⟩ := H
  obtain ⟨_, rfl, a1⟩ := h1.weakU_inv W
  obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
  exact ⟨_, rfl, _, a1, a2⟩

scoped notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ B.inst a₁ ≡ B.inst a₂ : .sort v →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂ : B.inst a₁
  | lamDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body₁ ≡ₚ body₂ : B → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂ : .forallE A B
  | forallEDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≡ₚ A₂ : .sort u → A::Γ ⊢ B₁ ≡ₚ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) : B → Γ ⊢ .lam A e ≡ₚ e' : .forallE A B
  | etaR : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e : B → Γ ⊢ e' ≡ₚ .lam A e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h' : p
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ₚ e2 : A → Γ ⊢ e1 ≡ₚ e2 : B

theorem NormalEq.defeqDFC (W : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2 : A) : Γ₂ ⊢ e1 ≡ₚ e2 : A := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (h.defeqDFC W)
  | appDF h1 h2 h3 ih1 ih2 => exact .appDF (ih1 W) (ih2 W) (h3.defeqDFC W)
  | lamDF h1 h2 h3 _ ih2 =>
    exact .lamDF (h1.defeqDFC W) (h2.defeqDFC W)
      (h3.defeqDFC (W.succ h1.hasType.2)) (ih2 (W.succ h1.hasType.2))
  | forallEDF h1 h2 _ _ ih1 ih2 =>
    exact .forallEDF (h1.defeqDFC W) (h2.defeqDFC W) (ih1 W) (ih2 (W.succ h1.hasType.2))
  | etaL h1 h2 h3 _ ih =>
    exact .etaL (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | etaR h1 h2 h3 _ ih =>
    exact .etaR (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.defeqDFC W) (h2.defeqDFC W) (h3.defeqDFC W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.defeqDFC W) (ih W)

theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | refl h => exact h
  | appDF h1 h2 _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF hA₁ hA₂ hB _ ihB =>
    exact have W := .succ .zero hA₁.symm
      .defeqDF (.forallEDF hA₁ (hB.defeqDFC W)) (.lamDF (hA₁.trans hA₂.symm) (ihB.defeqDFC W))
  | forallEDF hA₁ hA₂ _ _ ihA ihB =>
    exact .forallEDF (hA₁.trans hA₂.symm) (ihB.defeqDFC (.succ .zero hA₁.symm))
  | etaL hA _ h1 _ ih => exact .trans (.lamDF hA ih) (.eta h1)
  | etaR hA _ h1 _ ih => exact .trans (.symm (.eta h1)) (.lamDF hA ih)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e2 ≡ₚ e1 : A := by
  induction H with
  | refl h => exact .refl h
  | appDF h1 h2 h3 ih1 ih2 => exact .defeqDF h3.symm <| .appDF ih1 ih2 h3.symm
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF h2 h1 h3 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 h2 h3 _ ih => exact .etaR h1 h2 h3 ih
  | etaR h1 h2 h3 _ ih => exact .etaL h1 h2 h3 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ₚ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing Γ' ρ with
  | refl h => exact .refl (h.weak' W)
  | appDF h1 h2 h3 ih1 ih2 =>
    simpa only [SExpr.lift', SExpr.lift'_inst_hi] using
      (NormalEq.appDF (ih1 W) (ih2 W) (by
        simpa only [SExpr.lift'_inst_hi, SExpr.lift'] using h3.weak' W))
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (ih2 W.cons)
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF (h1.weak' W) (h2.weak' W) (ih1 W) (ih2 W.cons)
  | etaL h1 h2 h3 _ ih =>
    refine .etaL (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | etaR h1 h2 h3 _ ih =>
    refine .etaR (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.weak' W) (ih W)

def CRDefEq (Γ : List SExpr) (e₁ e₂ A : SExpr) : Prop :=
  Γ ⊢ e₁ ≡ e₂ : A ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' : A
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₃ : A → Γ ⊢ e₁ ≫≪ e₃ : A
  | ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry

theorem CRDefEq.defeqDF : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≫≪ e₂ : B
  | ⟨l1, _, _, l3, l4, l5⟩, H => ⟨H.defeqDF l1, _, _, l3, l4, l5.defeqDF H⟩

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

theorem WHRedS.crDefEq (H1 : Γ ⊢ e1 : A) (H2 : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫≪ e2 : A :=
  ⟨H2.defeq H1, _, _, H2.parRedS, .rfl, .refl (H2.defeq H1).hasType.2⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

theorem InferType.whRed (H1 : Γ ⊢ e ⤳ e') (H2 : Γ ⊢ e ▷ A) : Γ ⊢ e' ▷ A := by
  induction H1 generalizing A with
  | app h1 ih => let .app r1 r2 r3 := H2; exact .app (ih r1) r2 r3
  | major => sorry
  | beta =>
    let .app a1 a2 a3 := H2
    let .lam b1 b2 := a1
    cases WHNF.forallE.whRedS a2
    exact .inst sorry b2
  | extra => sorry
