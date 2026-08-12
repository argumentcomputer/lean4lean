import Lean4Lean.Experimental.ShapeLogRel
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean

namespace SExpr
variable [Params] [Params.Semantic]

def LR.Adequate (Γ₀ Γ : List SExpr) (ρ : Valuation) (M N A : SExpr) (m a : WShape n) :=
  (∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
    (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR Γ₀).DefEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.SubstWF Γ₀ σ σ Γ ρ → (LR Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a

theorem LR.Adequate.bot (ha : a.HasType .type) : Adequate Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ _ => ⟨(LR _).bot ha, (LR _).bot ha⟩, fun _ _ => (LR _).bot ha⟩

theorem LR.Adequate.fits
    (H : ρ.Fits Γ₀ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem LR.Adequate.refl
    (H : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
      (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem LR.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem LR.Adequate.symm : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ => ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR _).symm (h2 W)⟩

theorem LR.Adequate.trans :
    Adequate Γ₀ Γ ρ M₁ M₂ A m a → Adequate Γ₀ Γ ρ M₂ M₃ A m a → Adequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR _).trans (a2 W) (b2 W)⟩

theorem LR.Adequate.trans' : Adequate Γ₀ Γ ρ A₁ A₂ (.sort u) a s →
    Adequate Γ₀ Γ ρ A₂ A₃ (.sort v) a (.sort r) → Adequate Γ₀ Γ ρ A₁ A₃ (.sort u) a s
  | ⟨a1, a2⟩, ⟨b1, b2⟩ => by
    refine ⟨fun σ σ' W => ⟨(a1 W).1, ?_⟩, fun _ W => (LR _).trans' (a2 W) (b2 W)⟩
    have h1 := (LR _).trans' (a1 W.left).2 (b2 W.left)
    have h2 := (LR _).trans' (a1 W.symm.left).2 (b2 W.symm.left)
    exact (LR _).trans ((LR _).symm h1) <| (LR _).trans (a1 W).2 h2

/-- Lower adequacy from a saturated semantic witness to a compatible smaller
witness.  Constant evaluation recursively builds finite approximants; this
lemma reconciles the resulting type witnesses through their join. -/
theorem LR.Adequate.mono_r {Γ₀ Γ : List SExpr} {ρ : Valuation} {M N A : SExpr}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a)
    (hAty' : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a')
    (H : Adequate Γ₀ Γ ρ M N A m' a') : Adequate Γ₀ Γ ρ M N A m a := by
  have hJ := TShape.Join.mk hc
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
  have hkn : n ≤ max n n' := Nat.le_max_left ..
  have hkn' : n' ≤ max n n' := Nat.le_max_right ..
  have hjk : (a.T.join a'.T).1 ≤ max n n' := Nat.max_le.2 ⟨hkn, hkn'⟩
  have hJ1' := (TShape.LE.def hkn hjk).1 hJ1
  have hJ2' := (TShape.LE.def hkn' hjk).1 hJ2
  have hJ_t := (TShape.HasType.sort_r.2 hmem.isType).join' hJ
    (TShape.HasType.sort_r.2 hmem'.isType)
  have hmem_k := (WShape.HasType.lift hkn).2 hmem
  have hmem'_k := (WShape.HasType.lift hkn').2 hmem'
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  have lower : ∀ {M₀ N₀ : SExpr} {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).DefEq M₀ N₀ (A.subst σ) m' a' →
      (LR Γ₀).DefEq M₀ N₀ (A.subst σ) m a := by
    intro M₀ N₀ σ σ' W hv
    have ha_kty : (WShape.lift (max n n') a).HasType .type := by
      simpa using (WShape.HasType.lift hkn).2 hmem.isType
    have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
      simpa using (WShape.HasType.lift hkn').2 hmem'.isType
    have tyJ := (LR Γ₀).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
      ((TyDefEq.lift hkn hmem.isType).2 (hAty W))
      ((TyDefEq.lift hkn' hmem'.isType).2 (hAty' W))
    have tyJ' : (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ)
        ((a.T.join a'.T).snd.lift (max n n')) := WShape.lift_self ▸ tyJ
    refine (DefEq.lift hkn hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' <|
      (LR Γ₀).mono_l ((TShape.LE.def hkn hkn').1 le)
        (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hmem'_k) <|
      (LR Γ₀).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
        (DefEq.lift hkn' hmem').2 hv
  exact ⟨fun σ σ' W => ⟨lower W (H.1 W).1, lower W (H.1 W).2⟩,
    fun σ W => lower W (H.2 W)⟩

theorem LR.Adequate.cons
    (ihA : ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (sort u) m a)
    (HA : IsDefEqStrong Γ A A' (.sort u))
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR Γ₀).DefEq x x' (A.subst σ) p a₁)
    (W : SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.defeq.hasType.1 ⟨hx, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 hA
    exact ⟨_, le_a, hA', (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType⟩
  have ha' := LE_Interp.weak_iff.1 ha'
  refine ⟨fun ht => ⟨⟨_, (HA.substCongr W.toSubstEq).1⟩, ?_⟩, fun m' hm' ht => ?_⟩
  · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 ha' |>.out
    refine (TyDefEq.lift le_n ht).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
      (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
      (.mono_r hSort.le_sort' .sort hmem') .sort ((ihA hA' hSort hmem').1 W).1
  · have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1 (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (DefEq.lift le_n ht).1 <|
      (LR Γ₀).mono_r_2 hj2 ht' hJ <|
      (LR Γ₀).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      (LR Γ₀).mono_r_1 hj1 hp' hJ' ?_ <| (DefEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd} (hA : LE_Interp ρ a.T A) (ha : a.HasType .type) :
        (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.left.fits).2 hA |>.out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := (LR Γ₀).left_ty <| (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort v2
      (TyDefEq.lift le_n ha).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    refine (LR Γ₀).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
    · exact (TyDefEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (TyDefEq.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `TyDefEq` from a `DefEq` at sort type. -/
theorem LR.toValTy {m : WShape n'} {b : WShape n} (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type) (hSort : LE_Interp ρ a.T (.sort u)) (hmem' : m.HasType a)
    (H : (LR Γ₀).DefEq M N (.sort u) m a) : (LR Γ₀).TyDefEq M N b := by
  have hle := hSort.le_sort'
  refine (LR.TyDefEq.lift le_n ht).1 ?_
  refine (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hle hmem'
    (.mono_r hle .sort hmem') .sort H

/-- One function layer of constant evaluation.  The continuation receives
the original strictly smaller semantic branch together with the input and
output bounds that select it.  Keeping that provenance explicit lets the
caller recurse on the actual `Const.lam` child rather than on a reconstructed
`lift`/`mono` proof of equal depth. -/
theorem LR.constLamDefEq
    {n n' nArgs : Nat} {f : WShapeFun n} {f' : WShapeFun n'} {hf : f.NonZero}
    {M N : SExpr}
    {a₁ : WShape n} {a₂ : WShapeFun n}
    {A₁ A₂ : SExpr}
    (htm : WShape.HasTypeLam f a₁ a₂)
    (hlam : (WShape.lam' f).T ≤ (WShape.lam' f').T)
    (evalLeft : ∀ {k : Nat} (hn : n ≤ k) (hn' : n' ≤ k) (hnArgs : nArgs ≤ k)
      {x y : SExpr} {p : WShape k} {x₀ y₀ : WShape n'},
      p.HasType (a₁.lift k) →
      Γ₀ ⊢ x ≡ y : A₁ →
      (LR Γ₀).DefEq x y A₁ p (a₁.lift k) →
      (x₀, y₀) ∈ f' → x₀.lift k ≤ p →
      (f.lift k).app p ≤ y₀.lift k →
      (LR Γ₀).DefEq (M.app x) (M.app y)
        (A₂.inst x) ((f.lift k).app p) ((a₂.lift k).app p))
    (evalRight : ∀ {k : Nat} (hn : n ≤ k) (hn' : n' ≤ k) (hnArgs : nArgs ≤ k)
      {x y : SExpr} {p : WShape k} {x₀ y₀ : WShape n'},
      p.HasType (a₁.lift k) →
      Γ₀ ⊢ x ≡ y : A₁ →
      (LR Γ₀).DefEq x y A₁ p (a₁.lift k) →
      (x₀, y₀) ∈ f' → x₀.lift k ≤ p →
      (f.lift k).app p ≤ y₀.lift k →
      (LR Γ₀).DefEq (N.app x) (N.app y)
        (A₂.inst x) ((f.lift k).app p) ((a₂.lift k).app p))
    (evalEq : ∀ {k : Nat} (hn : n ≤ k) (hn' : n' ≤ k) (hnArgs : nArgs ≤ k)
      {x y : SExpr} {p : WShape k} {x₀ y₀ : WShape n'},
      p.HasType (a₁.lift k) →
      Γ₀ ⊢ x ≡ y : A₁ →
      (LR Γ₀).DefEq x y A₁ p (a₁.lift k) →
      (x₀, y₀) ∈ f' → x₀.lift k ≤ p →
      (f.lift k).app p ≤ y₀.lift k →
      (LR Γ₀).DefEq (M.app x) (N.app y)
        (A₂.inst x) ((f.lift k).app p) ((a₂.lift k).app p)) :
    LRS.LamDefEq (LR Γ₀) M N A₁ A₂ f a₁ a₂ := by
  let k := max (max n n') nArgs
  have hn : n ≤ k := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have hn' : n' ≤ k := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)
  have hnArgs : nArgs ≤ k := Nat.le_max_right ..
  have hff' : f.lift k ≤ f'.lift k := by
    have hk : max n n' ≤ k := Nat.le_max_left ..
    have h := WShapeFun.lift_mono hk (TShape.LE.lam'_decomp hlam)
    rw [WShapeFun.lift_lift (.inl (Nat.le_max_left n n')),
      WShapeFun.lift_lift (.inl (Nat.le_max_right n n'))] at h
    exact h
  have childBounds (p : WShape n) :
      ∃ x₀ y₀ : WShape n', (x₀, y₀) ∈ f' ∧
        x₀.lift k ≤ p.lift k ∧
        (f.lift k).app (p.lift k) ≤ y₀.lift k := by
    obtain ⟨x, hx, hmem⟩ := (f.lift k).app_eq (p.lift k)
    obtain ⟨x', y', hmem', hx', hy'⟩ := WShapeFun.LE.def'.1 hff' _ _ hmem
    obtain ⟨x₀, y₀, hmem₀, rfl, rfl⟩ := (WShapeFun.mem_lift hn').1 hmem'
    exact ⟨x₀, y₀, hmem₀, hx'.trans hx, hy'⟩
  have lower {P Q : SExpr}
      (evalChild : ∀ {k : Nat} (hn : n ≤ k) (hn' : n' ≤ k) (hnArgs : nArgs ≤ k)
        {x y : SExpr} {p : WShape k} {x₀ y₀ : WShape n'},
        p.HasType (a₁.lift k) →
        Γ₀ ⊢ x ≡ y : A₁ →
        (LR Γ₀).DefEq x y A₁ p (a₁.lift k) →
        (x₀, y₀) ∈ f' → x₀.lift k ≤ p →
        (f.lift k).app p ≤ y₀.lift k →
        (LR Γ₀).DefEq (P.app x) (Q.app y)
          (A₂.inst x) ((f.lift k).app p) ((a₂.lift k).app p))
      {x y : SExpr} {p : WShape n}
      (hp : p.HasType a₁) (hxy : Γ₀ ⊢ x ≡ y : A₁)
      (hv : (LR Γ₀).DefEq x y A₁ p a₁) :
      (LR Γ₀).DefEq (P.app x) (Q.app y)
        (A₂.inst x) (f.app p) (a₂.app p) := by
    have hpₖ : (p.lift k).HasType (a₁.lift k) :=
      (WShape.HasType.lift hn).2 hp
    have hvₖ : (LR Γ₀).DefEq x y A₁ (p.lift k) (a₁.lift k) :=
      (LR.DefEq.lift hn hp).2 hv
    obtain ⟨x₀, y₀, hmem₀, hx₀, hy₀⟩ := childBounds p
    have hout := evalChild hn hn' hnArgs hpₖ hxy hvₖ hmem₀ hx₀ hy₀
    have hout' : (LR Γ₀).DefEq
        (P.app x) (Q.app y)
        (A₂.inst x) ((f.app p).lift k) ((a₂.app p).lift k) := by
      simpa only [WShapeFun.lift_app hn] using hout
    exact (LR.DefEq.lift hn ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)).1 hout'
  exact ⟨fun _ _ _ hp hxy hv =>
      ⟨lower evalLeft hp hxy hv, lower evalRight hp hxy hv⟩,
    fun _ _ hp hx hv => lower evalEq hp hx hv⟩

/-- The final semantic application carried by the constant evaluator.  This
packages the raw final-Pi spine together with the *same* logical-relation
argument witness and Pi edge.  Keeping these fields in one dependent record
prevents the reached iota leaf from forgetting that the constructor major is
related at the domain used by the recursor application. -/
structure LR.PatternLeafSpine (Γ : List SExpr) (IH : LogRel Γ n)
    (Head : SExpr) (args args' : List SExpr) (rargs : List (WShape n))
    (A : SExpr) (out outTy : WShape n) where
  majorX : SExpr
  recXs : List SExpr
  majorY : SExpr
  recYs : List SExpr
  majorShape : WShape n
  recShapes : List (WShape n)
  majorTypeShape : WShape n
  resultShape : WShapeFun n
  resultTypeShape : WShapeFun n
  args_eq : args = majorX :: recXs
  args'_eq : args' = majorY :: recYs
  rargs_eq : rargs = majorShape :: recShapes
  out_eq : out = resultShape.app majorShape
  outTy_eq : outTy = resultTypeShape.app majorShape
  pair : SExpr.SpineWF.LastPair Γ Head recXs recYs majorX majorY A
  majorHasType : majorShape.HasType majorTypeShape
  majorType : IH.TyDefEq pair.domain pair.domain majorTypeShape
  majorRel : IH.DefEq majorX majorY pair.domain majorShape majorTypeShape
  aligned : LRS.CtorSpineDefEq IH Head args args' rargs A
  pi : LRS.PiDefEq IH pair.domain pair.codomain pair.codomain
    majorTypeShape resultTypeShape

/-- Forget the final-Pi alignment back to the ordinary related argument
spine consumed by the structural constant cases. -/
theorem LR.PatternLeafSpine.args
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LRS.CtorArgsDefEq IH xs ys rargs := H.aligned.args

/-- A packaged final application is definitionally nonempty. -/
theorem LR.PatternLeafSpine.nonempty
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    rargs ≠ [] := by
  rw [H.rargs_eq]
  simp

/-- The remaining consumer obligation at a reached nonempty pattern leaf. -/
def LR.PatternLeafDefEq (Γ₀ : List SExpr) (c : Name) (ls : List SLevel)
    (rho : Valuation) : Prop :=
  ∀ {n : Nat} {rargs : List (WShape n)}
      {p : Pattern} {r : p.RHS × p.Check} {mcap : p.Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n},
      Params.Pat p r →
      LE_Interp.Matches (n := n) p c rargs mcap →
      LE_Interp.RHS ls mcap (LE_Interp rho) out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- The nonempty leaf contract after eliminating the impossible definition
case.  Its pattern is definitionally an iota pattern, so consumers can invert
the semantic match into recursor and constructor spines without another
shape oracle. -/
def LR.IotaLeafDefEq (Γ₀ : List SExpr) (c : Name) (ls : List SLevel)
    (rho : Valuation) : Prop :=
  ∀ {n : Nat} {rargs : List (WShape n)}
      {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      LE_Interp.Matches (n := n) (RecursorIotaPattern rec major ctor arity)
        c rargs mcap →
      LE_Interp.RHS ls mcap (LE_Interp rho) out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- Logical-relation congruence for one generated iota RHS at adjacent
stratification levels.  The two endpoints share the rule's ordered paths and
one exact capture-type map; each variable leaf is therefore related at the
very domain used by both dependent application spines.  The eventual
constructor proves the fixed-tower case by `LE_Interp.recR`; no environment
or reduction oracle appears in this contract. -/
def LRS.IotaRHSDefEq
    (IH : LogRel Γ n) (rho : Valuation)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (rule : Pattern.IotaRule r)
    (out : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) (LE_Interp rho) out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
          (mx path) (my path) (captureType path)) →
    out.HasType outTy →
    (LRS IH).TyDefEq A A outTy →
    (LRS IH).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Build the full generated-RHS contract from its only nontrivial case.
`RHS.bot` is discharged uniformly; the continuation receives the semantic
fixed head and the exact ordered application chain extracted from the rule. -/
theorem LRS.IotaRHSDefEq.of_nonbot
    {IH : LogRel Γ n} {rho : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)},
      LE_Interp.RHS (p := RecursorIotaPattern rec major ctor arity)
        recLs (Sum.elim mrec mctor) (LE_Interp rho) head
        (.fixed rule.df.rhs rule.rhsClosed) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRS IH).TyDefEq A A outTy →
      (LRS IH).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRS.IotaRHSDefEq IH rho recLs mrec mctor r rule out := by
  intro hrhs mx my captureType A outTy hspineX hspineY hcap hout hA
  obtain hbot | ⟨head, hhead, hshapeSpine⟩ := rule.rhsShapeSpine hrhs
  · have houtBot : out = .bot := TShape.le_bot.1 hbot
    subst out
    exact (LRS IH).bot hout.isType
  · exact H hhead hshapeSpine hspineX hspineY hcap hout hA

/-- The exact constructor case of iota materialization.  It recovers both
concrete matches, constructs only the two finite local actions through the
live semantic bridge, and composes major reduction with those actions. -/
theorem LR.iotaActions_of_exactAt
    {n : Nat} {IH : LogRel Γ₀ n} {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LRS.CtorArgsDefEq (LRS IH) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq IH ctorXs ctorYs ctorShapes)
    (hMajorX : Γ₀ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs))
    (hMajorY : Γ₀ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs'))
    (htermX : Γ₀ ⊢
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ≡
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX : A)
    (htermY : Γ₀ ⊢
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ≡
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorTypeX : Γ₀ ⊢ majorX : majorType)
    (hMajorTypeY : Γ₀ ⊢ majorY : majorType) :
    ∃ (mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType)
      (captureTypingY : Pattern.CaptureTyping Γ₀ my captureType)
      (rule : Pattern.IotaRule r)
      (siteX : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs
        recXs ctorXs majorX A mx captureType captureTypingX)
      (siteY : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs'
        recYs ctorYs majorY A my captureType captureTypingY),
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
        recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
        recLs my A,
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) ∧
      Γ₀ ⊢
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ⤳*
          r.1.applyS recLs mx ∧
      Γ₀ ⊢
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ⤳*
          r.1.applyS recLs my := by
  obtain ⟨mx, my, hmatchX, hmatchY, hcap, hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materialize_exactAt hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY
  have hredXEq := hredX.defeq htermX
  have hredYEq := hredY.defeq htermY
  let typingX : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs
      recXs ctorXs majorX A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeX
    ctorResultType := ctorResultX
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineX
    ctorHead := hctorHeadX
    ctorSpine := hctorSpineX
    majorEq := hMajorX.defeq hMajorTypeX }
  let typingY : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs'
      recYs ctorYs majorY A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeY
    ctorResultType := ctorResultY
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineY
    ctorHead := hctorHeadY
    ctorSpine := hctorSpineY
    majorEq := hMajorY.defeq hMajorTypeY }
  classical
  let captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr :=
    fun path => match path with
      | Sum.inl p => (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).typeExpr
      | Sum.inr p => (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).typeExpr
  let captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).defeq.hasType.1
      | inr p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).defeq.hasType.1 }
  let captureTypingY : Pattern.CaptureTyping Γ₀ my captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).defeq.hasType.2
      | inr p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).defeq.hasType.2 }
  let rule := Params.Semantic.iotaRule hpat
  let siteX := Params.Semantic.iotaSite rule captureType captureTypingX typingX hmatchX
    hredXEq.hasType.2 hAType
  let siteY := Params.Semantic.iotaSite rule captureType captureTypingY typingY hmatchY
    hredYEq.hasType.2 hAType
  let actionX := siteX.action
  let actionY := siteY.action
  have hcapAligned : ∀ path :
      (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
          (mx path) (my path) (captureType path) := by
    intro path
    cases path with
    | inl p =>
      exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).aligned
    | inr p =>
      exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).aligned
  exact ⟨mx, my, captureType, captureTypingX, captureTypingY,
    rule, siteX, siteY, actionX, actionY, hcapAligned,
    .tail hredX (.extra actionX), .tail hredY (.extra actionY)⟩

/-- Consume one exact constructor observation once the registered RHS has a
logical-relation congruence proof.  This is the exact leaf used by the
transport-aware `CtorDefEq` fold: materialization and the two local iota
contractions are entirely internal, while semantic recursion supplies only
the evidence-only RHS continuation. -/
theorem LRS.iotaDefEq_of_exactAt
    {n : Nat} {IH : LogRel Γ₀ n} {rec ctor : Name} {major arity : Nat}
    {rho : Valuation}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      (LE_Interp rho) out.T r.1)
    (hrecargs : LRS.CtorArgsDefEq (LRS IH) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq IH ctorXs ctorYs ctorShapes)
    (hMajorX : Γ₀ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs))
    (hMajorY : Γ₀ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs'))
    (htermX : Γ₀ ⊢
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ≡
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX : A)
    (htermY : Γ₀ ⊢
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ≡
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorTypeX : Γ₀ ⊢ majorX : majorType)
    (hMajorTypeY : Γ₀ ⊢ majorY : majorType)
    (hout : out.HasType outTy)
    (hA : (LRS IH).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRS.IotaRHSDefEq IH rho recLs mrec mctor r rule out) :
    (LRS IH).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY)
      A out outTy := by
  obtain ⟨mx, my, captureType, captureTypingX, captureTypingY,
      rule, siteX, siteY, actionX, actionY, hcap, hredX, hredY⟩ :=
    LR.iotaActions_of_exactAt (IH := IH) hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY htermX htermY hAType hrecHead
      hrecSpineX hrecSpineY hctorHeadX hctorHeadY hctorSpineX hctorSpineY
      hMajorTypeX hMajorTypeY
  have hrhsDefEq : (LRS IH).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
    rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine hcap hout hA
  exact ((LRS IH).whr hredX hredY).2 hrhsDefEq

/-- Canonical wrapper for `iotaActions_of_exactAt`.  It forgets whether a
capture came from the predecessor or successor relation by existentially
packaging its shape depth. -/
theorem LR.iotaActions_of_exact
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LRS.CtorArgsDefEq (LR Γ₀) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ₀) ctorXs ctorYs ctorShapes)
    (hMajorX : Γ₀ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs))
    (hMajorY : Γ₀ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs'))
    (hterm : Γ₀ ⊢
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ≡
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorTypeX : Γ₀ ⊢ majorX : majorType)
    (hMajorTypeY : Γ₀ ⊢ majorY : majorType) :
    ∃ mx my,
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
        recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
        recLs my A,
      (∀ path, LRS.CaptureDefEq Γ₀ (Sum.elim mrec mctor path)
        (mx path) (my path)) ∧
      Γ₀ ⊢
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ⤳*
          r.1.applyS recLs mx ∧
      Γ₀ ⊢
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ⤳*
          r.1.applyS recLs my := by
  obtain ⟨mx, my, _, _, _, _, _, _, actionX, actionY,
      hcap, hredX, hredY⟩ :=
    LR.iotaActions_of_exactAt (IH := LR Γ₀) hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY hterm.hasType.1 hterm.hasType.2
      hAType hrecHead
      hrecSpineX hrecSpineY hctorHeadX hctorHeadY hctorSpineX hctorSpineY
      hMajorTypeX hMajorTypeY
  refine ⟨mx, my, actionX, actionY, ?_, hredX, hredY⟩
  intro path
  cases path with
  | inl path =>
    obtain ⟨elemShape, typeShape,
      hshape, htype, hty, hxy, hrel⟩ :=
      hcap (Sum.inl path)
    exact ⟨n + 1, elemShape, typeShape, _,
      hshape, htype, hty, hxy, hrel⟩
  | inr path =>
    obtain ⟨elemShape, typeShape,
      hshape, htype, hty, hxy, hrel⟩ :=
      hcap (Sum.inr path)
    exact ⟨n, elemShape, typeShape, _,
      hshape, htype, hty, hxy, hrel⟩

/-- A proof of the iota-only leaf contract discharges every nonempty simple
pattern leaf. -/
theorem LR.PatternLeafDefEq.of_iota
    (H : LR.IotaLeafDefEq Γ₀ c ls rho) :
    LR.PatternLeafDefEq Γ₀ c ls rho := by
  intro n rargs p r mcap xs ys CHead A out outTy
    hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout hA
  obtain ⟨rec, major, ctor, arity, rfl⟩ :=
    hmatch.iota_of_pat_nonempty hpat hleaf.nonempty
  exact H hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout hA

/-- Evaluate a semantic constant using exact related syntax for its accumulated
application spine.  All structural cases are discharged here; a caller only
supplies the finite, proof-carrying action at a reached pattern leaf.  The
extra `rargs'` layer is essential: recursive semantic function layers may
change shape depth, while the already accumulated spine must only be lifted
or enlarged, never projected. -/
theorem LR.constDefEq
    {c : Name} {ls : List SLevel} {rho : Valuation}
    (evalPat : LR.PatternLeafDefEq Γ₀ c ls rho)
    {n : Nat} {rargs : List (WShape n)} {mout : TShape}
    (hC : LE_Interp.Const c ls (LE_Interp rho) rargs mout)
    {n' : Nat} {rargs' : List (WShape n')}
    {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n'}
    (hn : n ≤ n')
    (hargle : List.Forall₂ (· ≤ ·) (rargs.map (.lift n')) rargs')
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
      CHead xs ys rargs' A out outTy)
    (hterm : Γ₀ ⊢
      (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
      (ys.foldr (fun a f => f.app a) (.const c ls)) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    (hhead : Γ₀ ⊢ .const c ls : CHead)
    (hspineX : SExpr.SpineWF Γ₀ CHead xs.reverse A)
    (hspineY : SExpr.SpineWF Γ₀ CHead ys.reverse A)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy)
    (houtle : out.T ≤ mout) :
    (LR Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy := by
  induction hC generalizing n' rargs' xs ys A out outTy with
  | bot =>
    have hb : out.T ≤ TShape.bot := houtle.trans TShape.bot_eqv.1
    have heq : out = .bot := TShape.le_bot.1 hb
    subst out
    exact (LR Γ₀).bot hout.isType
  | pat hpat hmatch hrhs =>
    obtain ⟨mcap₁, hmatch₁, hcap₁⟩ := hmatch.lift hn
    obtain ⟨mcap₂, hmatch₂, hcap₂⟩ :=
      hmatch₁.mono_l (Params.pat_wf hpat) hargle
    have hrhs₁ := hrhs.mono_l (fun path => (hcap₁ path).1)
    have hrhs₂ := hrhs₁.mono_l hcap₂
    have hrhs' := hrhs₂.mono houtle (fun le hr => hr.mono le)
    exact evalPat hpat hmatch₂ hrhs' hleaf hterm hAType
      hhead hspineX hspineY hout hA
  | @lam f rargs mout hrec hlam ih =>
    have hlam₀ := houtle.trans hlam
    have hlam' := hlam₀
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_lam' hlam').elim
    | forallE => exact (TShape.forallE_not_le_lam' hlam').elim
    | @lam q g a₁ a₂ htm =>
      rw [LR_succ] at hA ⊢
      unfold WShape.lam' at hlam' ⊢
      split at hlam' <;> rename_i hg
      · obtain ⟨B₁, F₁, B₂, F₂, u, v, rA, _, hB, hF, hValB, hPi₀⟩ := hA
        have hPi := LRS.PiDefEq.left hPi₀
        have evalChild : ∀ {K : Nat}
            (hq : q ≤ K) (hn₀ : n ≤ K) (hnArgs : q + 1 ≤ K)
            {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape n}
            {zs zs' : List SExpr},
            LRS.CtorSpineDefEq (LR Γ₀) CHead zs zs' rargs' A →
            Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) : A →
            SExpr.SpineWF Γ₀ CHead zs.reverse A →
            SExpr.SpineWF Γ₀ CHead zs'.reverse A →
            p.HasType (a₁.lift K) →
            Γ₀ ⊢ x ≡ y : B₁ →
            (LR Γ₀).DefEq x y B₁ p (a₁.lift K) →
            (x₀, y₀) ∈ f → x₀.lift K ≤ p →
            (g.lift K).app p ≤ y₀.lift K →
            (LR Γ₀).DefEq
              ((zs.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p) ((a₂.lift K).app p) := by
          intro K hq hn₀ hnArgs x y p x₀ y₀ zs zs' htailAligned htailTerm
            htailSpineX htailSpineY hp hxy hv hmem hx hy
          have htailAlignedK : LRS.CtorSpineDefEq (LR Γ₀) CHead zs zs'
              (rargs'.map (fun z => z.lift K)) A :=
            htailAligned.lift hnArgs (fun hmt => LR.TyDefEq.lift hnArgs hmt)
              (fun hma => LR.DefEq.lift hnArgs hma)
          have hleTail : List.Forall₂ (· ≤ ·)
              (rargs.map (fun z => z.lift K))
              (rargs'.map (fun z => z.lift K)) :=
            WShape.forall₂_lift hn hnArgs hargle
          have hchildLe : List.Forall₂ (· ≤ ·)
              ((x₀ :: rargs).map (fun z => z.lift K))
              (p :: rargs'.map (fun z => z.lift K)) := by
            simp only [List.map_cons]
            exact .cons hx hleTail
          have hBK : (LR Γ₀).TyDefEq B₁ B₁ (a₁.lift K) :=
            (LR.TyDefEq.lift hq
              (WShape.HasTypePi.iff.1 htm.1).1.isType).2
              ((LR Γ₀).left_ty hValB)
          have htmK : WShape.HasTypeLam (g.lift K) (a₁.lift K) (a₂.lift K) :=
            (WShape.HasTypeLam.lift hq).2 htm
          have houtK : ((g.lift K).app p).HasType ((a₂.lift K).app p) :=
            (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
          have hPiK : LRS.PiDefEq (LR Γ₀) B₁ F₁ F₁
              (a₁.lift K) (a₂.lift K) :=
            (LRS.PiDefEq.lift hq htm.1).2 hPi
          have hAK : (LR Γ₀).TyDefEq (F₁.inst x) (F₁.inst x)
              ((a₂.lift K).app p) :=
            hPiK.2 hp hxy.hasType.1 ((LR Γ₀).left hv)
          obtain ⟨uA, hAType⟩ := hAType
          have hAeqPi : Γ₀ ⊢ A ≡ .forallE B₁ F₁ : .sort uA :=
            rA.defeq hAType
          have htailPi : Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) :
                .forallE B₁ F₁ :=
            hAeqPi.defeqDF htailTerm
          have hchildTerm : Γ₀ ⊢
              (zs.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app x ≡
              (zs'.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app y :
                F₁.inst x :=
            .appDF htailPi hxy
          have hchildType : Γ₀ ⊢ F₁.inst x : .sort v :=
            (IsDefEq.beta hF.hasType.1 hxy.hasType.1).hasType.2
          have hchildSpineX : SExpr.SpineWF Γ₀ CHead
              (x :: zs).reverse (F₁.inst x) := by
            simpa only [List.reverse_cons] using
              htailSpineX.snoc hAeqPi hxy.hasType.1
          obtain ⟨_, hCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
          have hchildAligned : LRS.CtorSpineDefEq (LR Γ₀) CHead
              (x :: zs) (y :: zs')
              (p :: rargs'.map (fun z => z.lift K)) (F₁.inst x) :=
            .cons htailAlignedK hAeqPi hp hBK hxy hv hCodomain.symm
          have hchildSpineY : SExpr.SpineWF Γ₀ CHead
              (y :: zs').reverse (F₁.inst x) := by
            have hspine := htailSpineY.snoc hAeqPi hxy.hasType.2
            simpa only [List.reverse_cons] using
              SExpr.SpineWF.ret hspine hCodomain.symm
          let hchildPair : SExpr.SpineWF.LastPair Γ₀ CHead
              zs zs' x y (F₁.inst x) := {
              prefixType := A
              domain := B₁
              codomain := F₁
              piSort := uA
              resultSortX := v
              resultSortY := _
              prefixX := htailSpineX
              prefixY := htailSpineY
              pi := hAeqPi
              major := hxy
              resultX := hchildType
              resultY := hCodomain.symm }
          have hchildLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead
              (x :: zs) (y :: zs') (p :: rargs'.map (fun z => z.lift K))
              (F₁.inst x) ((g.lift K).app p) ((a₂.lift K).app p) := {
            majorX := x
            recXs := zs
            majorY := y
            recYs := zs'
            majorShape := p
            recShapes := rargs'.map (fun z => z.lift K)
            majorTypeShape := a₁.lift K
            resultShape := g.lift K
            resultTypeShape := a₂.lift K
            args_eq := rfl
            args'_eq := rfl
            rargs_eq := rfl
            out_eq := rfl
            outTy_eq := rfl
            pair := hchildPair
            majorHasType := hp
            majorType := hBK
            majorRel := hv
            aligned := hchildAligned
            pi := hPiK }
          have houtleK : ((g.lift K).app p).T ≤ y₀.T :=
            hy.T.trans (TShape.lift_eqv hn₀).1
          simpa only [List.foldr_cons] using
            ih x₀ y₀ hmem hn₀ hchildLe hchildLeaf
              hchildTerm ⟨v, hchildType⟩ hchildSpineX hchildSpineY
              houtK hAK houtleK
        rw [dif_pos hg]
        refine (LRS.DefEq.lam_forallE
          (M := xs.foldr (fun a f => f.app a) (.const c ls))
          (N := ys.foldr (fun a f => f.app a) (.const c ls))
          (A := A) (f := g) (hf := hg) (a₁ := a₁) (a₂ := a₂)
          (LR Γ₀)).2 ?_
        refine ⟨B₁, F₁, u, v, rA, hB.hasType.1,
          (LR Γ₀).left_ty hValB, hF.hasType.1, hPi, ?_⟩
        exact LR.constLamDefEq (hf := hg) (nArgs := q + 1) htm hlam₀
          (fun hq hn₀ hnArgs =>
            evalChild hq hn₀ hnArgs hleaf.aligned.left hterm.hasType.1
              hspineX hspineX)
          (fun hq hn₀ hnArgs =>
            evalChild hq hn₀ hnArgs hleaf.aligned.right hterm.hasType.2
              hspineY hspineY)
          (fun hq hn₀ hnArgs => evalChild hq hn₀ hnArgs hleaf.aligned hterm
            hspineX hspineY)
      · rw [dif_neg hg]
        exact (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_lam' hlam').elim
    | indTy => exact (TShape.indTy_not_le_lam' hlam').elim
  | @ctor semOut semArgs hcl hctor =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.ctor rargs'.length) := hlen ▸ hcl
    have hLift : (WShape.ctor' c semArgs.reverse).T ≤
        (WShape.ctor' c (semArgs.map (.lift n')).reverse).T := by
      have h := (TShape.lift_eqv
        (a := (WShape.ctor' c semArgs.reverse).T) (Nat.succ_le_succ hn)).2
      rw [WShape.lift_ctor' hn, List.map_reverse] at h
      exact h
    have hSame : (WShape.ctor' c (semArgs.map (.lift n')).reverse).T ≤
        (WShape.ctor' c rargs'.reverse).T :=
      (WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 hargle)).T
    have hctor' := houtle.trans (hctor.trans (hLift.trans hSame))
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_ctor' hctor').elim
    | forallE => exact (TShape.forallE_not_le_ctor' hctor').elim
    | lam htm =>
      unfold WShape.lam' at hctor' ⊢
      split at hctor' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_ctor' hctor').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | @ctor q c' fields hwf =>
      have hIndHead : LRS.IndTyHead Γ₀ A := by
        simpa only [LR_succ, LRS.TyDefEq.indTy_m] using hA.1
      rw [LR_succ]
      change LRS.IndDefEq Γ₀ (LR Γ₀)
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A
        (WShape.ctor c' fields hwf)
      exact ⟨hIndHead, LRS.CtorDefEq.of_exact_ctor_spines
        hleaf.args hleaf.aligned hcl' hhead hhead hspineX hspineY hctor'⟩
    | indTy => exact (TShape.indTy_not_le_ctor' hctor').elim
  | @indTy semOut semArgs hcl hind =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.indTy rargs'.length) := hlen ▸ hcl
    have hind' := houtle.trans hind
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_indTy hind').elim
    | forallE => exact (TShape.forallE_not_le_indTy hind').elim
    | lam htm =>
      unfold WShape.lam' at hind' ⊢
      split at hind' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_indTy hind').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_indTy hind').elim
    | indTy =>
      rw [LR_succ]
      change LRS.IndTyHead Γ₀
          (xs.foldr (fun a f => f.app a) (.const c ls)) ∧
        LRS.IndTyHead Γ₀
          (ys.foldr (fun a f => f.app a) (.const c ls))
      exact ⟨⟨c, ls, xs, hleaf.args.lengths.1.symm ▸ hcl', .rfl⟩,
        ⟨c, ls, ys, hleaf.args.lengths.2.symm ▸ hcl', .rfl⟩⟩

/-- A zero-arity semantic definition rule is also a concrete one-step head
reduction.  Keeping this consequence next to adequacy makes the recursive
constant case consume the local, proof-carrying contraction rather than
reconstructing a registered equation from global membership. -/
theorem Params.Semantic.defn_whRed
    {c : Name} {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (hpat : Params.Pat (.const c) r)
    {ci : VConstant} {ls : List SLevel} {Γ : List SExpr}
    (hci : Params.env.constants c = some ci) (hlen : ls.length = ci.uvars) :
    ∃ (value : VExpr) (closed : value.Closed),
      r = (.fixed value closed, .true) ∧
      IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
        (SExpr.mkInst ls ci.type) ∧
      WHRed Γ (.const c ls) (SExpr.mkInst ls value) := by
  obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
  subst r
  have hstrong : IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
      (SExpr.mkInst ls ci.type) := hdef (Γ := Γ) hci hlen
  obtain ⟨m2, hmatch⟩ : ∃ m2,
      (Pattern.const c).MatchesS (.const c ls) ls m2 :=
    ⟨_, .const (c := c) (ls := ls)⟩
  let action : Pattern.Action Γ (.fixed value closed, .true)
      (.const c ls) ls m2 (SExpr.mkInst ls ci.type) := {
    pat := hpat
    matched := hmatch
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := hstrong.defeq }
  exact ⟨value, closed, rfl, hstrong, .extra action⟩

/-- Main adequacy theorem for the logical relation. -/
theorem LR.adequacy (H : IsDefEqStrong Γ M N A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a := by
  induction H generalizing ρ n m a with
  | @bvar Γ i A _ h h2 ih =>
    refine .refl fun _ _ W => ?_; clear h2 ih
    have hle := LE_Interp.bvar_iff.1 hM; clear hM
    induction W generalizing i A with
    | id =>
      cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
      exact (LR _).bot hmem.isType
    | cons W' _ _ _ _ h0 ih =>
      cases h with
      | zero => exact lift_subst ▸ (h0.2 a hA).2 (.bvar hle) hmem
      | succ h' => exact lift_subst ▸ ih h' (LE_Interp.weak_iff.1 hA) hle
  | symm H ih => exact .fits fun W => (ih ((LE_Interp.sound H W).1.2 hM) hA hmem).symm
  | trans H1 H2 ih1 ih2 =>
    exact .fits fun W => (ih1 hM hA hmem).trans (ih2 ((LE_Interp.sound H1 W).1.1 hM) hA hmem)
  | trans' H1 H2 ih1 ih2 =>
    by_cases hm : m ≤ .bot; · exact WShape.le_bot.1 hm ▸ .bot hmem.isType
    rename_i A B u C v
    refine .fits fun W => ?_
    refine (ih1 hM hA hmem).trans' (v := v) (r := v ≠ .zero) ?_
    refine have ihs1 := LE_Interp.sound H1 W; have hM₂ := ihs1.1.1 hM; ?_
    have ihs2 := LE_Interp.sound H2 W (m := m.T)
    have ⟨a₂, s₂, b1, b2, b3, b4⟩ := ihs2.2 hM₂
    replace b4 := TShape.HasType.sort.mono_r b3.le_sort b4
    have := TShape.HasType.mono_r hA.le_sort .sort hmem.T
    refine ih2 (ihs1.1.1 hM) (.sort TShape.sort_eqv.1) ?_
    exact WShape.HasType.T_iff.1 <| .mono_r TShape.sort_eqv.2 .sort_T <| this.retype b4 b1
  | @sort _ l =>
    suffices (LR Γ₀).DefEq (.sort l) (.sort l) (.sort l.succ) m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => exact (LR _).sort_iff.2 ⟨_, .rfl, .rfl⟩
    | _ =>
      obtain h | h := WShape.le_sort.1 hM.le_sort'
      · dsimp only at h; rw [h]; exact (LR _).bot hmem.isType
      · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
          WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
          Shape.bot] at h <;> first | split at h <;> simp_all only [reduceCtorEq] | simp_all
  | @const c ci Γ ls u h1 h2 hTy F hF hDef ihTy ihF ihDef =>
    cases hM with
    | bot => exact .bot hmem.isType
    | @const _ _ ci' _ m' _ a' _ R hreg _ hle hm'ty hA' hConst hR =>
      cases h1.symm.trans hreg
      suffices ∀ {σ σ'}, LR.SubstWF Γ₀ σ σ' Γ ρ →
          (LR Γ₀).DefEq (const c ls) (const c ls) ((mkInst ls ci.type).subst σ) m a
        from ⟨fun _ _ W => ⟨this W, this W⟩, fun _ W => this W⟩
      intro σ σ' W
      rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero]
      have hC : LE_Interp.Const c ls (LE_Interp ρ) [] m.T :=
        hConst.mono hle (fun le hr => (hR _ _ hr).mono le)
      cases hC with
      | bot => exact (LR Γ₀).bot hmem.isType
      | lam hrec hlam =>
        rename_i nsem hlen_sem fsem
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_lam' hlam).elim
        | forallE => exact (TShape.forallE_not_le_lam' hlam).elim
        | @lam k f a₁ a₂ htm =>
          obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
            (LE_Interp.sound hTy W.left.fits).2 hA |>.out
          have hty' := (ihTy hTy' hSort hmTy).2 W.left
          rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero] at hty'
          have hty : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type)
              (.forallE a₁ a₂) :=
            toValTy le_n le_a hmem.isType hSort hmTy hty'
          rw [LR_succ] at hty ⊢
          unfold WShape.lam'
          split <;> rename_i hf
          · obtain ⟨A₁, A₂, _, _, u₁, u₂, hred, _, hA₁, hA₂, hvalA₁, hpi⟩ := hty
            refine (LRS.DefEq.lam_forallE (M := .const c ls) (N := .const c ls)
              (A := mkInst ls ci.type) (f := f) (hf := hf) (a₁ := a₁) (a₂ := a₂)
              (LR Γ₀)).2
              ⟨A₁, A₂, u₁, u₂, hred, hA₁.hasType.1,
                (LR Γ₀).left_ty hvalA₁, hA₂.hasType.1, LRS.PiDefEq.left hpi, ?_⟩
            -- `hrec` is the semantic action of this constant.  Its child at
            -- each related argument is the well-founded predecessor needed
            -- to establish this `LamDefEq`; no type-shape work remains here.
            have eval : ∀ {k' : Nat} (hn : k ≤ k') (hnsem : nsem ≤ k')
                (_hnArgs : nsem ≤ k')
                {x y : SExpr} {p : WShape k'} {x₀ y₀ : WShape nsem},
                p.HasType (a₁.lift k') →
                Γ₀ ⊢ x ≡ y : A₁ →
                (LR Γ₀).DefEq x y A₁ p (a₁.lift k') →
                (x₀, y₀) ∈ fsem → x₀.lift k' ≤ p →
                (f.lift k').app p ≤ y₀.lift k' →
                (LR Γ₀).DefEq ((const c ls).app x) ((const c ls).app y)
                  (A₂.inst x) ((f.lift k').app p) ((a₂.lift k').app p) := by
              intro k' hn hnsem _hnArgs x y p x₀ y₀ hp hxy hv hmem₀ hx₀ hy₀
              have hPiK : LRS.PiDefEq (LR Γ₀) A₁ A₂ A₂
                  (a₁.lift k') (a₂.lift k') :=
                (LRS.PiDefEq.lift hn htm.1).2 (LRS.PiDefEq.left hpi)
              have hAK : (LR Γ₀).TyDefEq (A₂.inst x) (A₂.inst x)
                  ((a₂.lift k').app p) :=
                hPiK.2 hp hxy.hasType.1 ((LR Γ₀).left hv)
              have hout : ((f.lift k').app p).HasType ((a₂.lift k').app p) :=
                (WShape.HasTypeLam.iff.1 ((WShape.HasTypeLam.lift hn).2 htm)).2.2 p hp
              have hchildLe : ((f.lift k').app p).T ≤ y₀.T :=
                hy₀.T.trans (TShape.lift_eqv hnsem).1
              have hType₀ : Γ₀ ⊢ mkInst ls ci.type : .sort u := by
                simpa only [(Params.henv.closedC h1).mkInstS.subst_eq .zero,
                  SExpr.subst] using
                  (hTy.subst W.left.toSubstEq).hasType.1
              have hTypePi : Γ₀ ⊢
                  mkInst ls ci.type ≡ .forallE A₁ A₂ : .sort u :=
                hred.defeq hType₀
              have hConstPi : Γ₀ ⊢ .const c ls : .forallE A₁ A₂ :=
                hTypePi.defeqDF (.const h1 h2)
              have hAppTerm : Γ₀ ⊢
                  SExpr.app (SExpr.const c ls) x ≡
                    SExpr.app (SExpr.const c ls) y : A₂.inst x :=
                .appDF hConstPi hxy
              have hAppType : Γ₀ ⊢ A₂.inst x : .sort u₂ :=
                (IsDefEq.beta hA₂.hasType.1 hxy.hasType.1).hasType.2
              have hAppSpineX : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                  [x] (A₂.inst x) := by
                simpa only [List.nil_append] using
                  (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                    hTypePi hxy.hasType.1
              obtain ⟨_, hAppCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
              have hAppSpineY : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                  [y] (A₂.inst x) := by
                have hspine :=
                  (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                    hTypePi hxy.hasType.2
                exact SExpr.SpineWF.ret hspine hAppCodomain.symm
              have hA₁K : (LR Γ₀).TyDefEq A₁ A₁ (a₁.lift k') :=
                (LR.TyDefEq.lift hn
                  (WShape.HasTypePi.iff.1 htm.1).1.isType).2
                  ((LR Γ₀).left_ty hvalA₁)
              let hAppPair : SExpr.SpineWF.LastPair Γ₀
                  (mkInst ls ci.type) [] [] x y (A₂.inst x) := {
                  prefixType := mkInst ls ci.type
                  domain := A₁
                  codomain := A₂
                  piSort := u
                  resultSortX := u₂
                  resultSortY := _
                  prefixX := .nil
                  prefixY := .nil
                  pi := hTypePi
                  major := hxy
                  resultX := hAppType
                  resultY := hAppCodomain.symm }
              have hAppAligned : LRS.CtorSpineDefEq (LR Γ₀)
                  (mkInst ls ci.type) [x] [y] [p] (A₂.inst x) :=
                .cons .nil hTypePi hp hA₁K hxy hv hAppCodomain.symm
              have hAppLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
                  (mkInst ls ci.type) [x] [y] [p] (A₂.inst x)
                  ((f.lift k').app p) ((a₂.lift k').app p) := {
                majorX := x
                recXs := []
                majorY := y
                recYs := []
                majorShape := p
                recShapes := []
                majorTypeShape := a₁.lift k'
                resultShape := f.lift k'
                resultTypeShape := a₂.lift k'
                args_eq := rfl
                args'_eq := rfl
                rargs_eq := rfl
                out_eq := rfl
                outTy_eq := rfl
                pair := hAppPair
                majorHasType := hp
                majorType := hA₁K
                majorRel := hv
                aligned := hAppAligned
                pi := hPiK }
              have evalPat : LR.PatternLeafDefEq Γ₀ c ls ρ :=
                LR.PatternLeafDefEq.of_iota (by
                  -- Definitions have already been excluded by the nonempty
                  -- accumulated spine.  This exact iota branch turns the
                  -- constructor observation into the finite local
                  -- `Pattern.Action` certified by the live environment.
                  intro nI rargsI rec major ctor arity rI mcapI
                    xsI ysI CHeadI AI outI outTyI hpatI hmatchI hrhsI hleafI
                    htermI hAIType hheadI hspineXI hspineYI houtI hAI
                  cases hmatchI with
                  | @app fPat nCtor head recShapes mrec aPat ctorHead
                      ctorShapes mctor hmfI hmaI =>
                    rcases hleafI with
                      ⟨majorX, recXs, majorY, recYs, majorShape, recShapesI,
                        majorTypeShape, resultShape, resultTypeShape,
                        hxs, hys, hrargs, houtEq, houtTyEq, hlastPair,
                        hpMajor, htyMajor, hvMajor, halignedI, hPiI⟩
                    subst xsI
                    subst ysI
                    simp only [List.cons.injEq] at hrargs
                    rcases hrargs with ⟨hmajorShape, hrecShapes⟩
                    subst majorShape
                    subst recShapesI
                    subst outI
                    subst outTyI
                    have hctorHead : ctor = ctorHead :=
                      hmaI.varN_const_head
                    subst ctorHead
                    have hctorClass : Params.classify ctor =
                        some (.ctor ctorShapes.reverse.length) := by
                      simpa using
                        hmaI.head_wf_eq (Params.pat_wf hpatI).2
                    have hmajorCtor :=
                      LR.DefEq.ctor'_inv hctorClass hpMajor hvMajor
                    have hrecargsI : LRS.CtorArgsDefEq (LR Γ₀)
                        recXs recYs recShapes :=
                      halignedI.args.tail
                    sorry
                  )
              simpa only [List.foldr_cons, List.foldr_nil] using
                LR.constDefEq evalPat (hrec x₀ y₀ hmem₀) hnsem
                  (.cons hx₀ .nil) hAppLeaf
                  hAppTerm ⟨u₂, hAppType⟩ (.const h1 h2) hAppSpineX hAppSpineY
                  hout hAK hchildLe
            exact LR.constLamDefEq (hf := hf) (nArgs := nsem) htm hlam eval eval eval
          · exact (LR Γ₀).bot hmem.isType
        | ctor => exact (TShape.ctor_not_le_lam' hlam).elim
        | indTy => exact (TShape.indTy_not_le_lam' hlam).elim
      | ctor hcl hctor =>
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_ctor' hctor).elim
        | forallE => exact (TShape.forallE_not_le_ctor' hctor).elim
        | lam htm =>
          unfold WShape.lam' at hctor ⊢
          split at hctor <;> rename_i hn
          · exact (TShape.lam_not_le_ctor' hctor).elim
          · simpa [hn] using (LR Γ₀).bot hmem.isType
        | @ctor n c' l' h' =>
          obtain ⟨hc, hl⟩ := TShape.ctor_le_ctor'_nil (by simpa using hcl) hctor
          subst c'
          subst l'
          let cl : CtorBundle.IsCtor c := ⟨.ctor 0, by simpa using hcl, rfl⟩
          let Fc := F cl
          have hsort : LE_Interp ρ (WShape.type : WShape (n+1)).T (.sort Fc.u) := by
            exact .sort (decide_eq_true Fc.hu0 ▸ TShape.sort_eqv.1)
          have hty := (ihF cl hA hsort WShape.HasType.indTy).2 W.left
          have hhead : LRS.IndTyHead Γ₀ (mkInst ls ci.type) := by
            rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero] at hty
            simpa only [LR_succ, LRS.DefEq.sort_a, LRS.TyDefEq.indTy_m] using hty.1
          rw [LR_succ]
          change LRS.IndDefEq Γ₀ (LR Γ₀) (const c ls) (const c ls) (mkInst ls ci.type)
            (WShape.ctor c [] h')
          exact ⟨hhead, LRS.CtorDefEq.exact
            (IH := LR Γ₀) (c := c) (rargs := [])
            (M := const c ls) (N := const c ls)
            (ls := ls) (ls' := ls) (args := []) (args' := [])
            (by simpa using hcl) rfl rfl .rfl .rfl
            (.const h1 h2) (.const h1 h2)
            (.nil (Γ := Γ₀) (A := mkInst ls ci.type))
            (.nil (Γ := Γ₀) (A := mkInst ls ci.type)) .nil
            (LRS.CtorSpineDefEq.nil
              (IH := LR Γ₀) (Head := mkInst ls ci.type))⟩
        | indTy => exact (TShape.indTy_not_le_ctor' hctor).elim
      | indTy hcl hind =>
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_indTy hind).elim
        | forallE => exact (TShape.forallE_not_le_indTy hind).elim
        | lam htm =>
          unfold WShape.lam' at hind ⊢
          split at hind <;> rename_i hn
          · exact (TShape.lam_not_le_indTy hind).elim
          · simpa [hn] using (LR Γ₀).bot hmem.isType
        | ctor => exact (TShape.ctor_not_le_indTy hind).elim
        | indTy =>
          rw [LR_succ]
          change LRS.IndTyHead Γ₀ (const c ls) ∧ LRS.IndTyHead Γ₀ (const c ls)
          have hhead : LRS.IndTyHead Γ₀ (const c ls) :=
            ⟨c, ls, [], by simpa using hcl, .rfl⟩
          exact ⟨hhead, hhead⟩
      | @pat p r _ _ _ hpat hmatch hrhs =>
        have hp : p = .const c := hmatch.nil_inv
        subst p
        obtain ⟨value, closed, hr, hdef, hred⟩ :=
          Params.Semantic.defn_whRed (Γ := Γ₀) hpat h1 h2
        subst r
        cases hrhs with
        | bot => exact (LR Γ₀).bot hmem.isType
        | const hvalue =>
          simpa only [SExpr.subst, (Params.henv.closedC h1).mkInstS.subst_eq .zero] using
            ((ihDef hpat hvalue hA hmem).1 W).2
  | @appDF Γ A u F F' B X X' v _ Hf Ha HBa _ ihf iha ihBa =>
    cases hM with | bot => exact .bot hmem.isType | @app _ nf_app f _ _ _ x hif hia le_m
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        IsDefEqStrong Γ F F' (A.forallE B) →
        IsDefEqStrong Γ X X' A →
        IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v) →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X → LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
          mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X → LE_Interp ρ aa.T A →
          ma.HasType aa → Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
          mb.HasType av → Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR Γ₀).DefEq (.subst (.app F X) σ) (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this W Hf Ha HBa hif hia hA ihf iha ihBa⟩
      · refine this W (Hf.trans Hf.symm) (Ha.trans Ha.symm) (HBa.trans HBa.symm)
          hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W
          (Hf.symm.trans Hf) (Ha.symm.trans Ha) (HBa.symm.trans HBa)
          ((LE_Interp.sound Hf W.fits).1.1 hif) ((LE_Interp.sound Ha W.fits).1.1 hia)
          ((LE_Interp.sound HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBa W.fits).2 hA |>.out
          exact toValTy le le' hmem.isType iv hmb ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.sound Hf W.left.fits).1.2 hf) hPi hmf).symm.left
        · exact (iha ((LE_Interp.sound Ha W.left.fits).1.2 ha) hA hma).symm.left
        · exact (ihBa ((LE_Interp.sound HBa W.left.fits).1.2 hB) hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ := (LE_Interp.sound hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ (LR _).bot hmem.isType
      cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
      exact TShape.le_bot.1 ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
    cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
    cases hmf.unfold with | bot => cases hm0 rfl | lam hg => ?_ | _ =>
      refine have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
        have := (TShape.LE.def (Nat.le_succ_of_le (Nat.le_max_left ..)) le₂).1 le; ?_
      simp only [WShape.lift_sort, WShape.LE.def, WShape.lift_val le₂] at this; cases this
    rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
    simp at le_nf
    let k := max n (max n₁ n₂); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
    have hA' := hA.lift hk.1
    have ⟨_, le_x', hx'_a₁, hgx2⟩ := WShape.HasDom.iff.1 hg.2.1 (x.lift _)
    have hia' := (hia.lift le_nf).mono le_x'.T
    have hax' := LE_Interp.forallE' haA hbA hd hiB |>.mono le |>.forallE_inv.2 hia'
    have hJ := TShape.Join.mk (hA.compat hax')
    have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
    have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
    have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
    have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
    have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
    have hJ_t := TShape.HasType.sort_r.2 hmem.isType
      |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    rw [subst_inst]
    have hJ_t' := TShape.HasType.sort_r.1 <|
      hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
    refine (LR.DefEq.lift hk.1 hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' ?_
    have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
    refine (LR Γ₀).mono_l ?_ (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hgx'') ?_
    · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
        (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans (WShape.lam'_app ▸ hgx2.T)
    refine (LR Γ₀).mono_r_1 hJ2' hgx'' (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
    · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
        (LE_Interp.sound hBa W.left.fits).2 (hA.join hJ hax') |>.out
      exact (LR Γ₀).left_ty <| (TyDefEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
        subst_inst ▸ toValTy le_j le_j' (TShape.HasType.sort_r.1 hJ_t) hSj hmj
          ((ihBa hBj hSj hmj).2 W.left)
    · have hAf := (LR _).trans (Af.2 W.left) (Af.1 W).2
      dsimp only [LR, LRS] at hAf
      unfold WShape.lam' at hAf; split at hAf
      · rw [LRS.DefEq.lam_forallE] at hAf
        obtain ⟨_, _, _, _, red, _, _, _, _, valPi⟩ := hAf
        cases WHNF.forallE.whRedS red
        have le' := (TShape.LE.def (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
        simp only [WShape.T, WShape.lift_forallE hk.2.2, WShape.lift_forallE hk.2.1,
          WShape.forallE_le_forallE] at le'
        have Aa := iha hia' (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
        have := (LR _).trans (Aa.2 W.left) (Aa.1 W).2
        exact (DefEq.lift hk.2.2 hgx').2 <| (LR _).trans
          (valPi.2 hx'_a₁ (hX.subst W.toSubstEq).hasType.1 <| (LR _).left this)
          (valPi.1 hx'_a₁ (hX.subst W.toSubstEq) this).2
      · refine (hm0 ?_).elim; unfold WShape.lam'; simp_all
  | @lamDF Γ A A' u B v body body' HA HB HBody HBody' ihA ihB ihBody =>
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ m.T (.lam X Y) → SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : WShape np} {mb ab : WShape k},
          (ρ.push p.T).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p.T) mb.T Y → LE_Interp (ρ.push p.T) ab.T B → mb.HasType ab →
          Adequate Γ₀ (A :: Γ) (ρ.push p.T) Y Y' B mb ab) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this hM W fun _ => ihBody⟩
      · exact this hM W fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left
      · refine this ?_ W fun W hMb' hBb hmb => ?_
        · exact (LE_Interp.sound (.lamDF HA HB HBody HBody') W.fits).1.1 hM
        · exact (ihBody ((LE_Interp.sound HBody W).1.2 hMb') hBb hmb).symm.left
    intro X Y X' Y' σ σ' hTerm W IH
    suffices ∀ n' b (f : WShapeFun _), n = n' + 1 → a ≍ (.forallE b f : WShape (n'+1)) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | bot | sort => cases n <;> trivial | indTy => trivial
        | forallE => exact this _ _ _ rfl .rfl
      | sort => cases n <;> let .lam _ _ _ h := hTerm <;> cases TShape.sort_not_le_lam' h
      | forallE => let .lam _ _ _ h := hTerm <;> cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | ctor => let .lam _ _ _ h := hTerm; cases TShape.ctor_not_le_lam' h
      | indTy => let .lam _ _ _ h := hTerm; cases TShape.indTy_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      (HA.subst W.left.toSubstEq).hasType.1
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      HB.subst (W.left.toSubstEq.lift HA.defeq.hasType.1)
    have hA1 := hA.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
    have cons := Adequate.cons ihA HA
    obtain ⟨g, hg, htm⟩ := WShape.HasType.forallE_inv hmem
    unfold WShape.lam' at hg; split at hg <;> [skip; (subst hg; exact (LR _).bot hmem.isType)]
    rename_i hlam; subst hg
    simp only [LR, LRS, LRS.DefEq.lam_forallE]
    have aty := WShape.HasTypePi.iff.1 aty
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, ?_, hTypB, ?_, ?_⟩
    · exact (LR Γ₀).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').2 W.left)
    · simp only [LRS.PiDefEq]
      have edge : ∀ {{x x' p}}, p.HasType a₁ →
          Γ₀ ⊢ x ≡ x' : A.subst σ →
          (LR Γ₀).DefEq x x' (A.subst σ) p a₁ →
          LRS.PiInstDefEq (LR Γ₀) (B.subst σ.lift)
            (B.subst σ.lift) x x' (a₂.app p) := by
        intro x x' p hp ha hv
        have W' := cons hp hA1 ha hv W.left
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2 (hA.forallE_inv'.2 p) |>.out
        have hsem : (LR Γ₀).TyDefEq
            ((B.subst σ.lift).inst x) ((B.subst σ.lift).inst x') (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
        have hraw : Γ₀ ⊢
            (B.subst σ.lift).inst x ≡ (B.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using
            (HB.substCongr W'.toSubstEq).1
        exact ⟨hsem, hsem, ⟨v, hraw⟩, ⟨v, hraw⟩⟩
      exact ⟨edge, fun _ _ hp ha hv => (edge hp ha hv).leftTy⟩
    have beta {X Y t : SExpr} {σ} : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv'.2 p
      replace IH W := IH W (hTerm.lam_inv' p) hBb_sd ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · exact ((LR Γ₀).whr beta beta).2 <| ((IH W'.fits).1 W').1
      · have vtAA' := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' :=
          ((HA.substCongr W.toSubstEq).1).defeqDF ha
        have hv' := (LR Γ₀).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB W'.fits).2 hBb_sd |>.out
        have W2 := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
        have vtBB := toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W2).1
        refine ((LR Γ₀).whr beta beta).2 <| (LR Γ₀).conv ((LR Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      exact ((LR Γ₀).whr beta beta).2 <|
        (LR _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | @forallEDF Γ A A' u body body' v HA HBody _ ihA ihBody =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | forallE => let .sort h := hA; cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
      | _ => exact .bot hmem.isType
    | sort => cases n <;> have .forallE _ _ _ _ h := hM <;> cases TShape.sort_not_le_forallE h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'; split <;> [skip; exact fun _ => .bot hmem.isType]
      intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
    | ctor => have .forallE _ _ _ _ h := hM; cases TShape.ctor_not_le_forallE h
    | indTy => have .forallE _ _ _ _ h := hM; cases TShape.indTy_not_le_forallE h
    | @forallE k a₂ a₁ r aty
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst W.left.toSubstEq
      have S' := W.toSubstEq.lift HA.defeq.hasType.1)
    · have HAσ := (HA.substCongr W.toSubstEq).1
      have HA'σ := (HA.substCongr W.toSubstEq).2
      constructor
      · refine ⟨A.subst σ, body.subst σ.lift, A.subst σ', body.subst σ'.lift, u, v,
          .rfl, .rfl, HAσ, (HBody.substCongr S').1, ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp only [LRS.PiDefEq]
        constructor
        · intro x x' p hp ha hv
          have hB := hM.forallE_inv'.2 p
          have WL := cons hp hA1 ha hv W.left
          have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
            (LE_Interp.sound HBody WL.fits).2 hB |>.out
          have semL : (LR Γ₀).TyDefEq
              ((body.subst σ.lift).inst x) ((body.subst σ.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leL leL' (aty.2 _ hp).toType ivL hmbL
                ((ihBody iBL ivL hmbL).1 WL).1
          have valA := toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
          have WR := cons hp hA1 (HAσ.defeqDF ha) ((LR Γ₀).conv valA hv)
            W.symm.left
          have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
            (LE_Interp.sound HBody WR.fits).2 hB |>.out
          have semR : (LR Γ₀).TyDefEq
              ((body.subst σ'.lift).inst x) ((body.subst σ'.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leR leR' (aty.2 _ hp).toType ivR hmbR
                ((ihBody iBR ivR hmbR).1 WR).1
          have rawL : Γ₀ ⊢
              (body.subst σ.lift).inst x ≡ (body.subst σ.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WL.toSubstEq).1
          have rawR : Γ₀ ⊢
              (body.subst σ'.lift).inst x ≡ (body.subst σ'.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WR.toSubstEq).1
          exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
        · intro x p hp ha hv
          have hB := hM.forallE_inv'.2 p
          have WX := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
          have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBody WX.fits).2 hB |>.out
          have hout : (LR Γ₀).TyDefEq
              ((body.subst σ.lift).inst x) ((body.subst σ'.lift).inst x)
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 WX).1
          exact cast (by congr 1) hout
      · refine ⟨A'.subst σ, body'.subst σ.lift, A'.subst σ', body'.subst σ'.lift, u, v,
          .rfl, .rfl, HA'σ, HAAσ.defeqDF_l (HBody.substCongr S').2, ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp only [LRS.PiDefEq]
        have valA' := toValTy le_n le_a aty.1.isType hSort hmem'
          ((ihA hA' hSort hmem').2 W.left)
        constructor
        · intro x x' p hp ha hv
          have ha₀ := HAAσ.symm.defeqDF ha
          have hv₀ := (LR Γ₀).conv ((LR Γ₀).symm_ty valA') hv
          have hB := hM.forallE_inv'.2 p
          have WL := cons hp hA1 ha₀ hv₀ W.left
          have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
            (LE_Interp.sound HBody WL.fits).2 hB |>.out
          have semL : (LR Γ₀).TyDefEq
              ((body'.subst σ.lift).inst x) ((body'.subst σ.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leL leL' (aty.2 _ hp).toType ivL hmbL
                ((ihBody iBL ivL hmbL).1 WL).2
          have valA := toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
          have WR := cons hp hA1 (HAσ.defeqDF ha₀) ((LR Γ₀).conv valA hv₀)
            W.symm.left
          have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
            (LE_Interp.sound HBody WR.fits).2 hB |>.out
          have semR : (LR Γ₀).TyDefEq
              ((body'.subst σ'.lift).inst x) ((body'.subst σ'.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leR leR' (aty.2 _ hp).toType ivR hmbR
                ((ihBody iBR ivR hmbR).1 WR).2
          have rawL : Γ₀ ⊢
              (body'.subst σ.lift).inst x ≡ (body'.subst σ.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WL.toSubstEq).2
          have rawR : Γ₀ ⊢
              (body'.subst σ'.lift).inst x ≡ (body'.subst σ'.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WR.toSubstEq).2
          exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
        · intro x p hp ha hv
          have ha₀ := HAAσ.symm.defeqDF ha
          have hv₀ := (LR Γ₀).conv ((LR Γ₀).symm_ty valA') hv
          have hB := hM.forallE_inv'.2 p
          have WX := cons hp hA1 ha₀ ((LR Γ₀).left hv₀) W
          have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBody WX.fits).2 hB |>.out
          have hout : (LR Γ₀).TyDefEq
              ((body'.subst σ.lift).inst x) ((body'.subst σ'.lift).inst x)
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 WX).2
          exact cast (by congr 1) hout
    · refine ⟨A.subst σ, body.subst σ.lift, A'.subst σ, body'.subst σ.lift, u, v,
        .rfl, .rfl, HAAσ, HBody.subst S', ?_, ?_⟩
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp only [LRS.PiDefEq]
      constructor
      · intro x x' p hp ha hv
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HBody W'.fits).2 hB |>.out
        have sem := (ihBody iB iv hmb).1 W'
        have semL : (LR Γ₀).TyDefEq
            ((body.subst σ.lift).inst x) ((body.subst σ.lift).inst x')
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb sem.1
        have semR : (LR Γ₀).TyDefEq
            ((body'.subst σ.lift).inst x) ((body'.subst σ.lift).inst x')
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb sem.2
        have hraw := HBody.substCongr W'.toSubstEq
        have rawL : Γ₀ ⊢
            (body.subst σ.lift).inst x ≡ (body.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using hraw.1
        have rawR : Γ₀ ⊢
            (body'.subst σ.lift).inst x ≡ (body'.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using hraw.2
        exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
      · intro x p hp ha hv
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HBody W'.fits).2 hB |>.out
        have hout : (LR Γ₀).TyDefEq
            ((body.subst σ.lift).inst x) ((body'.subst σ.lift).inst x)
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).2 W')
        exact cast (by congr 1) hout
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
      have hA' := (LE_Interp.sound Hty W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ :=
        (LE_Interp.sound Hty W.fits).2 hA' |>.out
      toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := (LE_Interp.sound Hty W.left.fits).1.2 hA
    · exact ⟨(LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).1,
             (LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).2⟩
    · exact (LR Γ₀).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta He Ha Happ Hinst _ihe _iha ihapp ihinst =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihapp hM hA hmem).1 W).1
    · exact ((ihinst ((LE_Interp.sound (.beta He Ha Happ Hinst) W.fits).1.1 hM)
        hA hmem).1 W).2
    · exact ((LR _).whr .rfl (subst_inst ▸ .tail .rfl .beta)).1 ((ihapp hM hA hmem).2 W)
  | @eta _ e0 A0 B0 He Hlam ihe ihlam =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihlam hM hA hmem).1 W).1
    · exact ((ihe ((LE_Interp.sound (.eta He Hlam) W.fits).1.1 hM) hA hmem).1 W).2
    have hM' := (LE_Interp.sound (.eta He Hlam) W.fits).1.1 hM
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => cases n <;> let .lam _ _ _ h := hM <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM; cases TShape.forallE_not_le_lam' h
    | ctor => let .lam _ _ _ h := hM; cases TShape.ctor_not_le_lam' h
    | indTy => let .lam _ _ _ h := hM; cases TShape.indTy_not_le_lam' h
    | lam htm
    revert hM hM' hmem; unfold WShape.lam'
    split <;> intro hM hM' hmem <;> [skip; exact (LR _).bot hmem.isType]
    have ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, vpi_M⟩ := (ihlam hM hA hmem).2 W
    have ⟨_, _, _, _, whr_N, _, _, _, _, vpi_N⟩ := (ihe hM' hA hmem).2 W
    cases whr_t.determ .forallE whr_N .forallE
    refine ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, ?_, fun a p hp ha hv => ?_⟩
    · exact fun a b p hp ha hv => ⟨(vpi_M.1 hp ha hv).1, (vpi_N.1 hp ha hv).2⟩
    refine ((LR _).whr ?_ .rfl).2 (vpi_N.2 hp ha hv)
    rw [(?_ : (e0.subst σ).app a = _)]; · exact .tail .rfl .beta
    rw [inst_lift_cons, subst, lift_subst_cons]; rfl
  | proofIrrel Hp =>
    refine .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.sound Hp W).2 hA |>.out
    have hS := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; simp at hS
    have ha' := hS.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot hmem.isType
  | extra action Hl Hr ihl ihr =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihl hM hA hmem).1 W).1
    · exact ((ihr ((LE_Interp.sound
        (.extra action Hl Hr) W.fits).1.1 hM)
        hA hmem).1 W).2
    · have hself := (ihl hM hA hmem).2 W
      have hlocal := SExpr.WHRed.extra action
      have hred := hlocal.subst W.toSubstEq.left
      exact ((LR _).whr .rfl (.tail .rfl hred)).1 hself

theorem forallE_whRed_l
    (d : IsDefEqStrong Γ A₀ (SExpr.forallE B₁ F₁) (.sort s)) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v := by
  have hPi : LE_Interp .nil (WShape.T (n := 1) (.forallE .bot WShapeFun.bot)) (.forallE B₁ F₁) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : WShape.HasType (n := 1) (.forallE .bot WShapeFun.bot) (.sort (s ≠ .zero)) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx; exact WShapeFun.bot_app.symm ▸ .bot .sort
  have := (LR.adequacy d ((LE_Interp.sound d .nil).1.2 hPi) (.sort TShape.sort_eqv.1) hmem).2 .id
  have ⟨_, _, _, _, _, _, redA₀, redPi, convB, convF, _⟩ := subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.forallE.whRedS redPi; exact ⟨_, _, redA₀, _, _, convB, convF⟩

/-- Pi–Pi injectivity: if two Pi types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem forallE_inv
    (H : IsDefEqStrong Γ (SExpr.forallE A₀ B₀) (SExpr.forallE A₁ B₁) (.sort s)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨_, _, red, H⟩ := forallE_whRed_l H
  cases WHNF.forallE.whRedS red; exact H

theorem sort_forallE_inv :
    ¬IsDefEqStrong Γ (.sort u) (SExpr.forallE A₁ B₁) (.sort s) :=
  fun H => have ⟨_, _, H⟩ := forallE_whRed_l H; nomatch WHNF.sort.whRedS H.1

/-- Sort injectivity: if two sorts are definitionally equal, their levels are equal. -/
theorem sort_inv (d : IsDefEqStrong Γ (SExpr.sort u) (SExpr.sort v) V) : u = v := by
  have hM : LE_Interp .nil (WShape.T (n := 1) (.sort (decide (u ≠ .zero)))) (.sort u) :=
    .sort TShape.sort_eqv.1
  have ⟨n, mU, mV, h1, h2, h3, hA, h5⟩ := (LE_Interp.sound d .nil).2 hM |>.out
  have h2' := WShape.lift_sort ▸ (TShape.LE.lift_l h1).1 h2; dsimp only at h2'
  cases WShape.sort_le.1 h2'
  cases show mV = (.sort true : WShape 1).lift n by
    let _+1 := n
    simp only [WShape.HasType, WShape.sort] at h5
    ext1; generalize mV.val = mv at h5
    let .sort := Shape.HasType.unfold_iff.1 h5; rfl
  have h1' : (1 : Nat) ≤ n := h1
  have := (LR.adequacy d hM (hA.unlift h1') .sort).2 .id
  have ⟨w, h1, h2⟩ := (LR _).sort_iff.1 (subst_id ▸ subst_id ▸ subst_id ▸ this)
  cases WHNF.sort.whRedS h1; cases WHNF.sort.whRedS h2; rfl

/-- Experimental end-to-end sort injectivity for `VExpr`, assuming the rewrite-rule
infrastructure packaged by `SExpr.Params`. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqU.sort_invS
    [Params.Semantic]
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (h : Params.env.IsDefEqU Params.univs Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨A, h⟩ := h
  have hΓwf := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hu : u.WF Params.univs := (h.levelWF hΓwf).1
  have hv : v.WF Params.univs := (h.levelWF hΓwf).2.1
  have huv := SExpr.sort_inv ((h.strong Params.henv hΓ).mkS)
  apply VLevel.equiv_def'.2
  rw [← SLevel.mk_val hu, ← SLevel.mk_val hv, huv]
