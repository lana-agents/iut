/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Full
import Iut.HodgeTheater.FRlfIso

/-!
# `F^⊩`-prime-strips (MR20 T6; IUT I, Example 3.5 (i), Definition 5.2 (iv))

IUT I, Example 3.5 (i) (l.5485–5543) and Definition 5.2 (iv) (l.9183–9220) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`: an `F^⊩`-prime-strip is a
collection `(‡C^⊩, Prime(‡C^⊩) ≅ V, ‡F^⊢, {‡ρ_v}_{v ∈ V})` with (e)
`‡ρ_v : Φ_{‡C^⊩,v} ≅ Φ^rlf_{‡C^⊢_v}` isomorphisms of topological monoids (both `≅ ℝ_{≥0}`) and (f)
the collection isomorphic to `F^⊩_mod`; "the realification `Φ^rlf_{C^⊢_v}` of the divisor monoid
`Φ_{C^⊢_v}` of `C^⊢_v` […] may be regarded as a single abstract monoid isomorphic to `ℝ_{≥0}`"
(the divisor monoid of `C^⊢_v` does not vary over the base category), and for
`F^⊩_mod`, `ρ_v` is "given by the assignment `log⊢_mod(p_v) ↦ (1/[K_v : (F_mod)_v]) logΦ(p_v)`".

## Formalisation

* **`Φ^rlf`** of a Frobenioid at an object `A` of its base: `PhiRlf X A = Φ(A) ⊗_ℕ ℝ_{≥0}` (the
  realification of the monoid `Φ(A)`, here of rank one, `≅ ℕ`); isomorphisms of Frobenioids act
  through their `Φ`-isomorphisms (`rlfMap`). At `v ∈ V^arc` the divisor monoid of `C^⊢_v` is
  already `ℝ_{≥0}` ([FrdII], Example 3.3), and `Φ^rlf_{C^⊢_v} = Φ_{C^⊢_v}`.
* `Φ_{‡C^⊩,v}`: as in `HodgeTheater.FRlfGlobal` (MR19), the global data `‡C^⊩ ≌ C^⊩_mod` carry
  `Prime(‡C^⊩) ≅ V` and `Φ_{‡C^⊩,v} = Φ_{C^⊩_mod,v} = phiAt v` transported from `F^⊩_mod`.
* `FRlfData`: global data, an `F^⊢`-prime-strip and the isomorphisms `ρ_v` (at every object of
  the base of `‡C^⊢_v`, compatible with the pull-backs); `FRlfData.Iso`: isomorphisms of the
  global data and of the `F^⊢`-prime-strips compatible with the `ρ_v` (both directions);
  `FRlfStrip`: the data isomorphic to `F^⊩_mod` (condition (f)).
* **The model `F^⊩_mod`** (`FRlfData.ofThetaData`): `ρ_v` at `v ∈ V^non` is
  `Φ_v ≅ ℝ_{≥0}` (`phiAtEquiv`, the coordinate `ord_v`), scaled so that
  `log⊢_mod(p_v) ↦ 1/[K_v : (F_mod)_v]`, followed by `ℝ_{≥0} ≅ Φ^rlf_{C^⊢_v}` in the coordinate
  `ord` of `C^⊢_v` (`ord(p) = 1`, so `logΦ(p_v) = 1`; `rlfCoord`, through
  `Φ_{C^⊢_v} = ℕ · ord(τ) ≅ ℕ`, `coneEquivNat`): **`rlfCoord_rhoModelNon_logMod`**
  `ρ_v(log⊢_mod(p_v)) = (1/[K_v : (F_mod)_v])·logΦ(p_v)`. At `v ∈ V^arc` it is MR19's
  `rhoEquivInf` (`log e = 1 ↦ [(F_mod)_v : ℝ]/[K_v : ℝ]`, `rhoModelArc_logMod`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid Iut.Frobenioid.GlobalRealified TensorProduct

/-! ### Realification -/

section Rlf

variable {M N L : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid L]

/-- `φ ⊗ id : M ⊗_ℕ ℝ_{≥0} → N ⊗_ℕ ℝ_{≥0}`. -/
def rlfMap (φ : M →+ N) : M ⊗[ℕ] NNReal →+ N ⊗[ℕ] NNReal :=
  (TensorProduct.map φ.toNatLinearMap LinearMap.id).toAddMonoidHom

lemma rlfMap_tmul (φ : M →+ N) (x : M) (r : NNReal) : rlfMap φ (x ⊗ₜ r) = φ x ⊗ₜ r := rfl

lemma rlfMap_id_of (φ : M →+ M) (h : ∀ x, φ x = x) (y : M ⊗[ℕ] NNReal) : rlfMap φ y = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x r => rw [rlfMap_tmul, h]
  | add a b ha hb => rw [map_add, ha, hb]

lemma rlfMap_comp_of (φ : M →+ N) (ψ : N →+ L) (χ : M →+ L) (h : ∀ x, χ x = ψ (φ x))
    (y : M ⊗[ℕ] NNReal) : rlfMap χ y = rlfMap ψ (rlfMap φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x r => rw [rlfMap_tmul, rlfMap_tmul, rlfMap_tmul, h]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Rlf

namespace FrobCat

/-- **`Φ^rlf(A) = Φ(A) ⊗_ℕ ℝ_{≥0}`**. -/
abbrev PhiRlf (X : FrobCat) (A : X.D) : Type := X.Φ.pos A ⊗[ℕ] NNReal

/-- The pull-back `Φ(B) → Φ(A)` along `f : A ⟶ B`. -/
def posPb (X : FrobCat) {A B : X.D} (f : A ⟶ B) : X.Φ.pos B →+ X.Φ.pos A where
  toFun x := ⟨X.Φ.pb f x, X.Φ.pb_mem f x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

namespace Iso

variable {X Y Z : FrobCat}

/-- `Φ(A) → Φ'(D(A))`. -/
def posMap (f : X.Iso Y) (A : X.D) : X.Φ.pos A →+ Y.Φ.pos (f.D.functor.obj A) where
  toFun x := ⟨f.phi A x, (f.phi_pos A x).mp x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- `Φ'(B) → Φ(D⁻¹(B))`. -/
def posInvMap (f : X.Iso Y) (B : Y.D) : Y.Φ.pos B →+ X.Φ.pos (f.D.inverse.obj B) where
  toFun y := ⟨f.phiInv B y, (f.phiInv_pos B y).mp y.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

lemma posMap_refl (A : X.D) (x : X.Φ.pos A) : (Iso.refl X).posMap A x = x := rfl

lemma posInvMap_refl (A : X.D) (x : X.Φ.pos A) : (Iso.refl X).posInvMap A x = x := rfl

lemma posMap_trans (f : X.Iso Y) (g : Y.Iso Z) (A : X.D) (x : X.Φ.pos A) :
    (f.trans g).posMap A x = g.posMap _ (f.posMap A x) := rfl

lemma posInvMap_trans (f : X.Iso Y) (g : Y.Iso Z) (B : Z.D) (x : Z.Φ.pos B) :
    (f.trans g).posInvMap B x = f.posInvMap _ (g.posInvMap B x) := rfl

end Iso

end FrobCat

/-! ### Isomorphisms of the global data -/

namespace FRlfGlobalIso

variable {D : InitialThetaData.{0}}

open HodgeTheater

/-- The identity of global data of `F^⊩`. -/
def refl (A : FRlfGlobal D) : A.Iso A := ⟨CategoryTheory.Equivalence.refl, Functor.leftUnitor _⟩

/-- The inverse. -/
def symm {A B : FRlfGlobal D} (f : A.Iso B) : B.Iso A where
  equiv := f.equiv.symm
  comm := (Functor.isoWhiskerLeft f.equiv.inverse f.comm).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight f.equiv.counitIso _ ≪≫ Functor.leftUnitor _

/-- The composite. -/
def trans {A B C : FRlfGlobal D} (f : A.Iso B) (g : B.Iso C) : A.Iso C where
  equiv := f.equiv.trans g.equiv
  comm := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft f.equiv.functor g.comm ≪≫ f.comm

end FRlfGlobalIso

/-! ### `F^⊩`-prime-strips -/

section Strips

variable (D : InitialThetaData.{0})

/-- `F_mod`. -/
abbrev Kmod : Type := ↥(fieldOfModuli D.F D.E)

/-- **The data of an `F^⊩`-prime-strip** (IUT I, Definition 5.2 (iv) (a)–(e)): the global data
`‡C^⊩ ≌ C^⊩_mod` (with `Prime(‡C^⊩) ≅ V` and `Φ_{‡C^⊩,v} = phiAt v`), an `F^⊢`-prime-strip and
the isomorphisms `ρ_v : Φ_{‡C^⊩,v} ≅ Φ^rlf_{‡C^⊢_v}` (at every object of the base of `‡C^⊢_v`,
compatible with the pull-backs at `V^non`). -/
structure FRlfData : Type 1 where
  /-- The global data. -/
  glob : HodgeTheater.FRlfGlobal D
  /-- The `F^⊢`-prime-strip. -/
  strip : FVdashStrip D
  /-- `ρ_v`, `v ∈ V^non`. -/
  rhoNon : ∀ (w : Vnon D) (A : (strip.non.comp w).F.F.D),
    phiAt (Sum.inl w : GlobalRealified.Place (Kmod D)) ≃+ (strip.non.comp w).F.F.PhiRlf A
  /-- `ρ_v` is compatible with the pull-backs (`Φ^rlf` does not vary over the base). -/
  rhoNon_pb : ∀ (w : Vnon D) {A B : (strip.non.comp w).F.F.D} (f : A ⟶ B) x,
    rlfMap ((strip.non.comp w).F.F.posPb f) (rhoNon w B x) = rhoNon w A x
  /-- `ρ_v`, `v ∈ V^arc` (`Φ_{C^⊢_v}` is already real). -/
  rhoArc : ∀ (w : Varc D) (A : (strip.arc w).X.F.F.D),
    phiAt (Sum.inr w : GlobalRealified.Place (Kmod D)) ≃+ (strip.arc w).X.F.F.Φ.pos A

variable {D}

/-- **An isomorphism of `F^⊩`-data** (IUT I, Definition 5.2 (iv): an isomorphism of collections
of data): isomorphisms of the global data and of the `F^⊢`-prime-strips, compatible with the
`ρ_v` (both directions). -/
structure FRlfData.Iso (P Q : FRlfData D) where
  /-- The isomorphism of global data. -/
  glob : P.glob.Iso Q.glob
  /-- The isomorphism of `F^⊢`-prime-strips. -/
  strip : P.strip.Iso Q.strip
  rhoNon : ∀ w A x, rlfMap ((strip.1 w).iso.posMap A) (P.rhoNon w A x) = Q.rhoNon w _ x
  rhoNonInv : ∀ w B x, rlfMap ((strip.1 w).iso.posInvMap B) (Q.rhoNon w B x) = P.rhoNon w _ x
  rhoArc : ∀ w A x, (strip.2 w).F.iso.posMap A (P.rhoArc w A x) = Q.rhoArc w _ x
  rhoArcInv : ∀ w B x, (strip.2 w).F.iso.posInvMap B (Q.rhoArc w B x) = P.rhoArc w _ x

namespace FRlfData.Iso

/-- The identity. -/
def refl (P : FRlfData D) : P.Iso P where
  glob := FRlfGlobalIso.refl _
  strip := FVdashStrip.Iso.refl _
  rhoNon _ _ _ := rlfMap_id_of _ (fun _ => rfl) _
  rhoNonInv _ _ _ := rlfMap_id_of _ (fun _ => rfl) _
  rhoArc _ _ _ := rfl
  rhoArcInv _ _ _ := rfl

/-- The inverse. -/
def symm {P Q : FRlfData D} (f : P.Iso Q) : Q.Iso P where
  glob := FRlfGlobalIso.symm f.glob
  strip := FVdashStrip.Iso.symm f.strip
  rhoNon := f.rhoNonInv
  rhoNonInv := f.rhoNon
  rhoArc := f.rhoArcInv
  rhoArcInv := f.rhoArc

/-- The composite. -/
def trans {P Q R : FRlfData D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R where
  glob := FRlfGlobalIso.trans f.glob g.glob
  strip := FVdashStrip.Iso.trans f.strip g.strip
  rhoNon w A x :=
    (rlfMap_comp_of ((f.strip.1 w).iso.posMap A) ((g.strip.1 w).iso.posMap _) _ (fun _ => rfl)
      _).trans ((congrArg _ (f.rhoNon w A x)).trans (g.rhoNon w _ x))
  rhoNonInv w B x :=
    (rlfMap_comp_of ((g.strip.1 w).iso.posInvMap B) ((f.strip.1 w).iso.posInvMap _) _
      (fun _ => rfl) _).trans ((congrArg _ (g.rhoNonInv w B x)).trans (f.rhoNonInv w _ x))
  rhoArc w A x := (congrArg _ (f.rhoArc w A x)).trans (g.rhoArc w _ x)
  rhoArcInv w B x := (congrArg _ (g.rhoArcInv w B x)).trans (f.rhoArcInv w _ x)

end FRlfData.Iso

end Strips

/-! ### The model `F^⊩_mod` -/

section Model

/-- `n ↦ n·t`. -/
def coneHom (t : ℝ) (ht : 0 < t) : ℕ →+ gammaCone (AddSubgroup.zmultiples t) where
  toFun n := ⟨⟨n • t, AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples t) n⟩,
    show (0 : ℝ) ≤ n • t from nsmul_nonneg ht.le n⟩
  map_zero' := Subtype.ext (Subtype.ext (zero_nsmul t))
  map_add' a b := Subtype.ext (Subtype.ext (add_nsmul t a b))

/-- `ℕ ≅ Φ = ℕ · t` for `t > 0`. -/
def coneEquivNat (t : ℝ) (ht : 0 < t) : ℕ ≃+ gammaCone (AddSubgroup.zmultiples t) :=
  AddEquiv.ofBijective (coneHom t ht)
    ⟨fun a b h => by
      have h' : (a : ℝ) * t = b * t := by
        have := congrArg (fun x : gammaCone (AddSubgroup.zmultiples t) => ((x.1 : ℝ))) h
        change a • t = b • t at this
        simpa only [nsmul_eq_mul] using this
      exact_mod_cast mul_right_cancel₀ ht.ne' h',
    fun x => by
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.1.2
      have hx : (0 : ℝ) ≤ x.1 := x.2
      have hk0 : 0 ≤ k := by
        by_contra hneg
        have : (k : ℝ) * t < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast not_le.mp hneg) ht
        rw [← zsmul_eq_mul, hk] at this
        linarith
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      change n • t = (x.1 : ℝ)
      rw [← hk, natCast_zsmul]⟩

/-- **The coordinate `Φ^rlf ≅ ℝ_{≥0}`**, `x ⊗ r ↦ x·r`, of `Φ = ℕ · t ⊆ ℝ`. -/
def rlfCoord (t : ℝ) (ht : 0 < t) : gammaCone (AddSubgroup.zmultiples t) ⊗[ℕ] NNReal ≃+ NNReal :=
  ((TensorProduct.congr (coneEquivNat t ht).symm.toNatLinearEquiv (LinearEquiv.refl ℕ NNReal)).trans
    (TensorProduct.lid ℕ NNReal)).toAddEquiv.trans (nnScale t ht)

variable (D : InitialThetaData.{0})

/-- `ord(τ) > 0`. -/
lemma ordTau_pos (w : Vnon D) : 0 < ordTau D w := by
  unfold ordTau
  split_ifs with hv
  · have hℓ : (0 : ℝ) < 2 * D.ℓ := by
      have : (0 : ℝ) < D.ℓ := by exact_mod_cast D.prime.ℓ_prime.pos
      linarith
    exact div_pos (ord_toMul_pos D w _ (D.localData.tateX w hv).t.norm_lt_one) hℓ
  · exact one_pos

/-- `p_v ≠ 0` and `|p_v|_v < 1`. -/
lemma pv_ne_zero_lt_one (w : FinitePlace (Kmod D)) :
    GlobalRealified.pv w ≠ 0 ∧ w (GlobalRealified.pv w) < 1 := by
  set I := w.maximalIdeal.asIdeal.under ℤ with hI
  have hmem : ((Ideal.absNorm I : ℕ) : ℤ) ∈ I := Ideal.absNorm_mem I
  have hP : algebraMap ℤ (𝓞 (Kmod D)) (Ideal.absNorm I : ℕ) ∈ w.maximalIdeal.asIdeal := hmem
  have hlt := (FinitePlace.norm_lt_one_iff_mem (Kmod D) w.maximalIdeal _).mpr hP
  rw [FinitePlace.norm_embedding_eq] at hlt
  have hne : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ideal.under_ne_bot ℤ w.maximalIdeal.ne_bot
  refine ⟨by unfold GlobalRealified.pv; exact_mod_cast hne, ?_⟩
  unfold GlobalRealified.pv
  simpa using hlt

/-- **`ord_v(p_v) > 0`**: the coordinate of `log⊢_mod(p_v)`. -/
lemma coord_logMod_pos (w : FinitePlace (Kmod D)) :
    0 < coord (logMod (Sum.inl w : GlobalRealified.Place (Kmod D))) (Sum.inl w) := by
  obtain ⟨h0, hlt⟩ := pv_ne_zero_lt_one D w
  rw [coord_logMod_inl w h0]
  have h := (Arakelov.ArithLineBundle.principal (GlobalRealified.pv w) h0).norm_fin_eq w
  have hn : ‖(Arakelov.ArithLineBundle.principal (GlobalRealified.pv w) h0).fin w‖ < 1 := by
    change ‖FinitePlace.embedding w.maximalIdeal (GlobalRealified.pv w)‖ < 1
    rw [FinitePlace.norm_embedding_eq]; exact hlt
  rw [h] at hn
  have hp := Arakelov.one_lt_primeNorm w
  by_contra hle
  push Not at hle
  have : (1 : ℝ) ≤ Arakelov.primeNorm w ^ (-(Arakelov.ArithLineBundle.principal
      (GlobalRealified.pv w) h0).ord w) :=
    one_le_zpow₀ hp.le (by exact_mod_cast neg_nonneg.mpr (by exact_mod_cast hle))
  linarith

/-- `log⊢_mod(p_v) ∈ Φ_v`. -/
lemma logMod_mem (w : FinitePlace (Kmod D)) :
    logMod (Sum.inl w : GlobalRealified.Place (Kmod D)) ∈ phiAt (Sum.inl w) := by
  have h : logMod (Sum.inl w : GlobalRealified.Place (Kmod D)) = single (Sum.inl w)
      (coord (logMod (Sum.inl w : GlobalRealified.Place (Kmod D))) (Sum.inl w)) := by
    simp [logMod, single]
  rw [h]
  exact single_mem_phiAt _ (coord_logMod_pos D w).le

/-- **The local degree `[K_v : (F_mod)_v] > 0`**. -/
lemma localDeg_pos (w : Vnon D) :
    0 < GlobalRealified.localDeg (Sum.inl (D.V.sectFin w) : GlobalRealified.Place D.Kt)
      (Sum.inl w : GlobalRealified.Place (Kmod D)) := by
  have hwv := D.V.sectFin_liesOver w
  simp only [GlobalRealified.localDeg]
  exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero (ramificationIdx'_ne_zero hwv)
    (inertiaDeg'_ne_zero hwv))

/-- **`ρ_v` of `F^⊩_mod`**, `v ∈ V^non`: `Φ_v ≅ ℝ_{≥0} ≅ Φ^rlf_{C^⊢_v}`,
`log⊢_mod(p_v) ↦ (1/[K_v : (F_mod)_v]) logΦ(p_v)`. -/
def rhoModelNon (w : Vnon D) :
    phiAt (Sum.inl w : GlobalRealified.Place (Kmod D)) ≃+
      gammaCone (AddSubgroup.zmultiples (ordTau D w)) ⊗[ℕ] NNReal :=
  (phiAtEquiv (Sum.inl w)).trans ((nnScale _ (one_div_pos.mpr (mul_pos (coord_logMod_pos D w)
    (localDeg_pos D w)))).trans (rlfCoord _ (ordTau_pos D w)).symm)

/-- **`ρ_v(log⊢_mod(p_v)) = (1/[K_v : (F_mod)_v])·logΦ(p_v)`** (IUT I, Example 3.5 (i)), in the
coordinate `ord` of `Φ^rlf_{C^⊢_v}` (`logΦ(p_v) = ord(p) = 1`). -/
theorem rlfCoord_rhoModelNon_logMod (w : Vnon D) :
    ((rlfCoord _ (ordTau_pos D w) (rhoModelNon D w ⟨_, logMod_mem D w⟩) : NNReal) : ℝ) =
      1 / GlobalRealified.localDeg (Sum.inl (D.V.sectFin w) : GlobalRealified.Place D.Kt)
        (Sum.inl w : GlobalRealified.Place (Kmod D)) := by
  rw [rhoModelNon, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  change 1 / (coord (logMod (Sum.inl w : GlobalRealified.Place (Kmod D))) (Sum.inl w) *
    GlobalRealified.localDeg (Sum.inl (D.V.sectFin w) : GlobalRealified.Place D.Kt)
      (Sum.inl w : GlobalRealified.Place (Kmod D))) *
    coord (logMod (Sum.inl w : GlobalRealified.Place (Kmod D))) (Sum.inl w) = _
  have h1 := coord_logMod_pos D w
  have h2 := localDeg_pos D w
  field_simp

/-- `ℝ_{≥0} ≅ realCone`. -/
def nnRealCone : NNReal ≃+ realCone.{0} where
  toFun t := ⟨⟨t⟩, show (0 : ℝ) ≤ t from t.2⟩
  invFun x := ⟨x.1.down, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **`ρ_v` of `F^⊩_mod`**, `v ∈ V^arc` (MR19's `rhoEquivInf`). -/
def rhoModelArc (w : Varc D) :
    phiAt (Sum.inr w : GlobalRealified.Place (Kmod D)) ≃+ realCone.{0} :=
  (rhoEquivInf (D.V.sectInf w) w).trans nnRealCone

/-- **`ρ_v(log⊢_mod(e)) = (1/[K_v : (F_mod)_v])·logΦ(e)`** at `v ∈ V^arc` (`logΦ(e) = 1`). -/
theorem rhoModelArc_logMod (w : Varc D)
    (h : logMod (Sum.inr w : GlobalRealified.Place (Kmod D)) ∈ phiAt (Sum.inr w)) :
    (rhoModelArc D w ⟨_, h⟩ : realCone.{0}).1.down =
      GlobalRealified.logPhi (K := D.Kt) (Sum.inr w) (Sum.inr (D.V.sectInf w)) /
        GlobalRealified.localDeg (Sum.inr (D.V.sectInf w) : GlobalRealified.Place D.Kt)
          (Sum.inr w : GlobalRealified.Place (Kmod D)) := by
  change ((rhoEquivInf (D.V.sectInf w) w ⟨_, h⟩ : NNReal) : ℝ) = _
  rw [coe_rhoEquivInf]
  exact rho_logMod_inf

/-- **`F^⊩_mod`** (IUT I, Example 3.5 (ii)): the global data of `F_mod`, the tautological
`F^⊢`-prime-strip and the `ρ_v` above. -/
def FRlfData.ofThetaData : FRlfData D where
  glob := HodgeTheater.FRlfGlobal.ofThetaData D
  strip := FVdashStrip.ofThetaData D
  rhoNon w _ := rhoModelNon D w
  rhoNon_pb _ _ _ _ _ := rlfMap_id_of _ (fun _ => rfl) _
  rhoArc w _ := rhoModelArc D w

/-- **An `F^⊩`-prime-strip** (IUT I, Definition 5.2 (iv)): data isomorphic to `F^⊩_mod`
(condition (f)). -/
structure FRlfStrip : Type 1 where
  /-- The data. -/
  X : FRlfData D
  /-- They are isomorphic to `F^⊩_mod`. -/
  equiv_model : Nonempty (X.Iso (FRlfData.ofThetaData D))

variable {D}

/-- **Isomorphisms of `F^⊩`-prime-strips**. -/
def FRlfStrip.Iso (P Q : FRlfStrip D) : Type := P.X.Iso Q.X

/-- **Any two `F^⊩`-prime-strips are isomorphic.** -/
theorem FRlfStrip.nonempty_iso (P Q : FRlfStrip D) : Nonempty (P.Iso Q) :=
  ⟨P.equiv_model.some.trans Q.equiv_model.some.symm⟩

variable (D)

/-- **The tautological `F^⊩`-prime-strip `F^⊩_mod`**. -/
def FRlfStrip.ofThetaData : FRlfStrip D := ⟨FRlfData.ofThetaData D, ⟨FRlfData.Iso.refl _⟩⟩

end Model

end PrimeStrip

end Multiradial

end Iut
