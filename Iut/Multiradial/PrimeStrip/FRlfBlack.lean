/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.FRlf
import Iut.Multiradial.PrimeStrip.Black

/-!
# `F^{⊩▶×μ}`-prime-strips (MR20; IUT II, Definition 4.9 (viii))

IUT II, Definition 4.9 (viii) (l.11910–11925 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory II.txt`): an `F^{⊩▶×μ}`-prime-strip
is a collection `(∗C^⊩, Prime(∗C^⊩) ≅ V, ∗F^{⊢▶×μ}, {∗ρ_v}_{v ∈ V})` "satisfying the conditions
(a)–(f) of [IUTchI], Definition 5.2, (iv), for an `F^⊩`-prime-strip, where the portion of the
collection of data constituted by an `F^⊢`-prime-strip is replaced by an `F^{⊢▶×μ}`-prime-strip";
"the generators of the monoids `O^▶(−)` [each of which is abstractly isomorphic to `ℕ`] … together
with the `{∗ρ_w}` determine … the pilot object". A morphism is an isomorphism of collections of
data.

## Formalisation

* The constituent of an `F^{⊢▶×μ}`-prime-strip at `v` is `G ↷ M` with `M ≅ O^▶ × O^{×μ}`
  (`Black.lean`); its **`O^▶`-portion is recovered canonically as `M/M^×`** (`Associates M`: the
  units of `O^▶ ≅ ℕ` are trivial and `O^{×μ}` is a group, `assocProdEquiv`). Isomorphisms act
  through `assocMap`.
* `ρ_v` (condition (e)) at `v ∈ V^non`: `Φ_{C^⊩,v} ≅ (M/M^×) ⊗_ℕ ℝ_{≥0}` (the realification of
  `O^▶`, `BlackRlf`); at `v ∈ V^arc`: `Φ_{C^⊩,v} ≅ M/M^×` (`O^▶ = (0, 1]` is already real).
* `FRlfBlackData`, `FRlfBlackData.Iso` (global data, `F^{⊢▶×μ}`-strips, compatibility with the
  `ρ_v`), `FRlfBlackStrip` (isomorphic to the model, condition (f)), `nonempty_iso`.
* **The model** (`FRlfBlackData.ofThetaData`): `O^▶ = τ^ℕ ≅ ℕ` (`oBlackNat`, using `|τ| < 1`),
  identified with `Φ_{C^⊢_v} = ℕ · ord(τ)` by `τ ↦ ord(τ)` (`blackCoord`), and `ρ_v` the `ρ_v` of
  `F^⊩_mod` through this identification (`blackToVdash_rhoBlackNon`), so that
  `ρ_v(log⊢_mod(p_v)) = (1/[K_v : (F_mod)_v])·logΦ(p_v)` (`rlfCoord_blackToVdash_logMod`); at
  `V^arc`, `ρ_v` of `F^⊩_mod` followed by `t ↦ e^{-t} ∈ (0, 1]`.

Not formalised: the pilot object itself (an object of `∗C^⊩` of negative degree, [FrdI],
Theorem 6.4), and the passage `F^⊩ ↦ F^{⊩▶×μ}`; the wall's value-group BPSs
(`ThetaLink/PrimeStrip.lean` `RlfMuStrip`) are not yet replaced by these strips (MR25).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid Iut.Frobenioid.GlobalRealified Iut.Frobenioid.Angular TensorProduct

/-! ### `M/M^×` -/

section Assoc

variable {M N P : Type*} [CommMonoid M] [CommMonoid N] [CommMonoid P]

/-- The map `M/M^× → N/N^×` induced by a homomorphism. -/
def assocMap (e : M →* N) : Associates M →* Associates N where
  toFun := Quotient.map' e fun _ _ h => h.map e
  map_one' := by
    change Associates.mk (e 1) = 1
    rw [map_one, Associates.mk_one]
  map_mul' a b := by
    obtain ⟨a, rfl⟩ := Associates.mk_surjective a
    obtain ⟨b, rfl⟩ := Associates.mk_surjective b
    change Associates.mk (e (a * b)) = Associates.mk (e a) * Associates.mk (e b)
    rw [map_mul, Associates.mk_mul_mk]

lemma assocMap_mk (e : M →* N) (a : M) : assocMap e (Associates.mk a) = Associates.mk (e a) :=
  rfl

lemma assocMap_comp (e : M →* N) (f : N →* P) (x : Associates M) :
    assocMap (f.comp e) x = assocMap f (assocMap e x) := by
  obtain ⟨a, rfl⟩ := Associates.mk_surjective x
  rfl

lemma assocMap_id_of (e : M →* M) (h : ∀ a, e a = a) (x : Associates M) : assocMap e x = x := by
  obtain ⟨a, rfl⟩ := Associates.mk_surjective x
  rw [assocMap_mk, h]

/-- `M/M^× → N/N^×`, additively. -/
def assocAdd (e : M →* N) : Additive (Associates M) →+ Additive (Associates N) :=
  MonoidHom.toAdditive (assocMap e)

/-- **`(A × G)/(A × G)^× ≅ A`** for a group `G` and a monoid `A` without nontrivial units. -/
def assocProdEquiv (A G : Type*) [CommMonoid A] [CommGroup G] [Subsingleton Aˣ] :
    Associates (A × G) ≃* A where
  toFun := Quotient.lift (fun x : A × G => x.1) fun x y h => by
    obtain ⟨u, hu⟩ := h
    have h1 : x.1 * ((MulEquiv.prodUnits u).1 : A) = y.1 := congrArg Prod.fst hu
    rwa [Subsingleton.elim (MulEquiv.prodUnits u).1 1, Units.val_one, mul_one] at h1
  invFun a := Associates.mk (a, 1)
  left_inv x := by
    obtain ⟨x, rfl⟩ := Associates.mk_surjective x
    change Associates.mk (x.1, (1 : G)) = Associates.mk x
    rw [Associates.mk_eq_mk_iff_associated]
    refine ⟨⟨(1, x.2), (1, x.2⁻¹), by simp, by simp⟩, ?_⟩
    ext
    · exact mul_one _
    · exact one_mul _
  right_inv _ := rfl
  map_mul' x y := by
    obtain ⟨x, rfl⟩ := Associates.mk_surjective x
    obtain ⟨y, rfl⟩ := Associates.mk_surjective y
    rfl

/-- A monoid isomorphic to `ℕ` has no nontrivial units. -/
lemma subsingleton_units_of_equiv_nat {A : Type*} [CommMonoid A] (e : A ≃* Multiplicative ℕ) :
    Subsingleton Aˣ := by
  refine ⟨fun u v => ?_⟩
  have key : ∀ w : Aˣ, w = 1 := fun w => by
    have h := congrArg (fun x => Multiplicative.toAdd (e x)) w.mul_inv
    simp only [map_mul, toAdd_mul, map_one, toAdd_one] at h
    have h0 : Multiplicative.toAdd (e w) = 0 := Nat.eq_zero_of_add_eq_zero_right h
    apply Units.ext
    apply e.injective
    rw [Units.val_one, map_one]
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  rw [key u, key v]

end Assoc

/-! ### Realification of `O^▶` -/

/-- **`(O^▶)^rlf = (M/M^×) ⊗_ℕ ℝ_{≥0}`** of a `G ↷ M` constituent. -/
abbrev BlackRlf (X : GMObj) : Type := Additive (Associates X.M) ⊗[ℕ] NNReal

/-- The map of realifications induced by an isomorphism. -/
def blackMap {X Y : GMObj} (e : X.Iso Y) : BlackRlf X →+ BlackRlf Y :=
  rlfMap (assocAdd e.M.toMonoidHom)

/-- The map of `M/M^×` induced by an isomorphism. -/
def blackArcMap {X Y : GMObj} (e : X.Iso Y) : Additive (Associates X.M) →+
    Additive (Associates Y.M) :=
  assocAdd e.M.toMonoidHom

lemma blackMap_refl (X : GMObj) (x : BlackRlf X) : blackMap (GMObj.Iso.refl X) x = x :=
  rlfMap_id_of _ (fun a => assocMap_id_of _ (fun _ => rfl) (Additive.toMul a)) x

lemma blackMap_trans {X Y Z : GMObj} (e : X.Iso Y) (f : Y.Iso Z) (x : BlackRlf X) :
    blackMap (e.trans f) x = blackMap f (blackMap e x) :=
  rlfMap_comp_of _ _ _ (fun a => assocMap_comp e.M.toMonoidHom f.M.toMonoidHom
    (Additive.toMul a)) x

lemma blackMap_symm_apply {X Y : GMObj} (e : X.Iso Y) (x : BlackRlf X) :
    blackMap e.symm (blackMap e x) = x := by
  rw [← blackMap_trans]
  exact rlfMap_id_of _ (fun a => assocMap_id_of _ (fun m => e.M.symm_apply_apply m)
    (Additive.toMul a)) x

lemma blackArcMap_symm_apply {X Y : GMObj} (e : X.Iso Y) (x : Additive (Associates X.M)) :
    blackArcMap e.symm (blackArcMap e x) = x := by
  change Additive.ofMul (assocMap _ (assocMap _ (Additive.toMul x))) = x
  rw [← assocMap_comp, assocMap_id_of _ (fun m => e.M.symm_apply_apply m)]
  rfl

/-! ### `F^{⊩▶×μ}`-prime-strips -/

section Strips

variable (D : InitialThetaData.{0})

/-- **The data of an `F^{⊩▶×μ}`-prime-strip** (IUT II, Definition 4.9 (viii)): the global data
`‡C^⊩ ≌ C^⊩_mod`, an `F^{⊢▶×μ}`-prime-strip and the isomorphisms `ρ_v` from `Φ_{‡C^⊩,v}` to the
realified `O^▶`-portions (`M/M^×`) of its constituents. -/
structure FRlfBlackData : Type 1 where
  /-- The global data. -/
  glob : HodgeTheater.FRlfGlobal D
  /-- The `F^{⊢▶×μ}`-prime-strip. -/
  strip : FBlackStrip D
  /-- `ρ_v`, `v ∈ V^non`. -/
  rhoNon : ∀ w : Vnon D,
    phiAt (Sum.inl w : GlobalRealified.Place (Kmod D)) ≃+ BlackRlf (strip.non w).X
  /-- `ρ_v`, `v ∈ V^arc` (`O^▶ = (0, 1]` is already real). -/
  rhoArc : ∀ w : Varc D,
    phiAt (Sum.inr w : GlobalRealified.Place (Kmod D)) ≃+ Additive (Associates (strip.arc w).X.M)

variable {D}

/-- **An isomorphism of `F^{⊩▶×μ}`-data**: isomorphisms of the global data and of the
`F^{⊢▶×μ}`-prime-strips compatible with the `ρ_v`. -/
structure FRlfBlackData.Iso (P Q : FRlfBlackData D) where
  /-- The isomorphism of global data. -/
  glob : P.glob.Iso Q.glob
  /-- The isomorphism of `F^{⊢▶×μ}`-prime-strips. -/
  strip : P.strip.Iso Q.strip
  rhoNon : ∀ w x, blackMap (strip.1 w) (P.rhoNon w x) = Q.rhoNon w x
  rhoArc : ∀ w x, blackArcMap (strip.2 w) (P.rhoArc w x) = Q.rhoArc w x

namespace FRlfBlackData.Iso

/-- The identity. -/
def refl (P : FRlfBlackData D) : P.Iso P where
  glob := FRlfGlobalIso.refl _
  strip := FBlackStrip.Iso.refl _
  rhoNon _ _ := blackMap_refl _ _
  rhoArc _ x := assocMap_id_of _ (fun _ => rfl) (Additive.toMul (P.rhoArc _ x))

/-- The inverse. -/
def symm {P Q : FRlfBlackData D} (f : P.Iso Q) : Q.Iso P where
  glob := FRlfGlobalIso.symm f.glob
  strip := FBlackStrip.Iso.symm f.strip
  rhoNon w x := by
    rw [← f.rhoNon w x]
    exact blackMap_symm_apply _ _
  rhoArc w x := by
    rw [← f.rhoArc w x]
    exact blackArcMap_symm_apply _ _

/-- The composite. -/
def trans {P Q R : FRlfBlackData D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R where
  glob := FRlfGlobalIso.trans f.glob g.glob
  strip := FBlackStrip.Iso.trans f.strip g.strip
  rhoNon w x := (blackMap_trans _ _ _).trans ((congrArg _ (f.rhoNon w x)).trans (g.rhoNon w x))
  rhoArc w x := (show blackArcMap ((f.strip.2 w).trans (g.strip.2 w)) (P.rhoArc w x) =
      blackArcMap (g.strip.2 w) (blackArcMap (f.strip.2 w) (P.rhoArc w x)) from
      congrArg Additive.ofMul (assocMap_comp (f.strip.2 w).M.toMonoidHom
        (g.strip.2 w).M.toMonoidHom (Additive.toMul (P.rhoArc w x)))).trans
    ((congrArg (blackArcMap (g.strip.2 w)) (f.rhoArc w x)).trans (g.rhoArc w x))

end FRlfBlackData.Iso

end Strips

/-! ### The model -/

section Model

variable (D : InitialThetaData.{0})

/-- `|·| : \bar{ℚ}_p^×/μ_N → ℝ` (roots of unity have absolute value `1`). -/
def normMod (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) : UnitsModMu p N →* ℝ :=
  QuotientGroup.lift _ ((normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (Units.coeHom _))
    fun ζ hζ => by
      rw [mem_rootsOfUnity] at hζ
      change ‖((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1
      have h : ‖((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ ^ N = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').mp h

/-- **`ord(τ) > 0`**, i.e. `|τ| < 1`. -/
lemma ord_tauElt_pos (v : Vnon D) : 0 < PAdicGalois.ord (pv D v) (tauElt D v) := by
  by_cases hv : v ∈ D.VBad
  · have hq := qRootExists D v hv
    have hτ : tauElt D v = toMul D v hq.choose := by simp only [tauElt, dif_pos hv]
    have hqlt : ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ < 1 := (D.localData.tateX v hv).t.norm_lt_one
    have hxlt : ‖((hq.choose : (Kv D v)ˣ) : Kv D v)‖ < 1 := by
      have h := hq.choose_spec
      have h' : ‖((hq.choose : (Kv D v)ˣ) : Kv D v)‖ ^ (2 * D.ℓ) < 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h]; exact hqlt
      by_contra hge
      push Not at hge
      exact absurd (one_le_pow₀ hge) (not_le.mpr h')
    rw [hτ]
    exact ord_toMul_pos D v _ hxlt
  · have hτ : tauElt D v = pMul D v := by simp only [tauElt, dif_neg hv]
    rw [hτ, ord_pMul]
    exact one_pos

lemma norm_tauUnit_lt_one (v : Vnon D) :
    ‖((tauUnit D v : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v))‖ < 1 := by
  have h := ord_tauElt_pos D v
  have hp : (1 : ℝ) < pv D v := by exact_mod_cast (Fact.out : (pv D v).Prime).one_lt
  have hpos : 0 < ‖((tauUnit D v : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v))‖ :=
    norm_pos_iff.mpr (Units.ne_zero _)
  change 0 < -Real.logb (pv D v) ‖((tauUnit D v : (PadicAlgCl (pv D v))ˣ) :
    PadicAlgCl (pv D v))‖ at h
  rw [neg_pos, Real.logb_neg_iff hp hpos] at h
  exact h

lemma two_ell_pos : 0 < 2 * D.ℓ := Nat.mul_pos two_pos D.prime.ℓ_prime.pos

/-- `n ↦ τ^n ∈ O^▶`. -/
def oBlackPow (v : Vnon D) : Multiplicative ℕ →* OBlackV D v where
  toFun n := ⟨(QuotientGroup.mk (tauUnit D v) : UnitsModMu (pv D v) (2 * D.ℓ)) ^
      Multiplicative.toAdd n, by
    rw [oBlack_eq_powers]; exact ⟨_, rfl⟩⟩
  map_one' := Subtype.ext (pow_zero _)
  map_mul' a b := Subtype.ext (pow_add _ _ _)

/-- **`O^▶ = τ^ℕ ≅ ℕ`** (`|τ| < 1`). -/
def oBlackNat (v : Vnon D) : Multiplicative ℕ ≃* OBlackV D v :=
  MulEquiv.ofBijective (oBlackPow D v)
    ⟨fun a b h => by
      have h' := congrArg (fun x : OBlackV D v =>
        normMod (pv D v) (2 * D.ℓ) (two_ell_pos D) (x : UnitsModMu (pv D v) (2 * D.ℓ))) h
      simp only [oBlackPow, MonoidHom.coe_mk, OneHom.coe_mk, map_pow] at h'
      have hpos : 0 < ‖((tauUnit D v : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v))‖ :=
        norm_pos_iff.mpr (Units.ne_zero _)
      exact Multiplicative.toAdd.injective
        (pow_right_injective₀ hpos (norm_tauUnit_lt_one D v).ne h'),
    fun x => by
      obtain ⟨y, hy⟩ := x
      have hy' := hy
      rw [oBlack_eq_powers] at hy'
      obtain ⟨n, rfl⟩ := hy'
      exact ⟨Multiplicative.ofAdd n, rfl⟩⟩

instance (v : Vnon D) : Subsingleton (OBlackV D v)ˣ :=
  subsingleton_units_of_equiv_nat (oBlackNat D v).symm

/-- **`(O^▶ × O^{×μ})/(units) ≅ ℕ · ord(τ) = Φ_{C^⊢_v}`**: the generator `τ` of `O^▶` goes to
its divisor `ord(τ)`. -/
def blackCoord (v : Vnon D) :
    Additive (Associates (fBlackModel D v).M) ≃+ gammaCone (AddSubgroup.zmultiples (ordTau D v)) :=
  (MulEquiv.toAdditive ((assocProdEquiv (OBlackV D v) (OxMuBar (pv D v))).trans
    (oBlackNat D v).symm)).trans (coneEquivNat _ (ordTau_pos D v))

/-- **`(O^▶)^rlf ≅ Φ^rlf_{C^⊢_v}`** in the model. -/
def blackToVdash (v : Vnon D) :
    BlackRlf (fBlackModel D v) ≃+ gammaCone (AddSubgroup.zmultiples (ordTau D v)) ⊗[ℕ] NNReal :=
  (TensorProduct.congr (blackCoord D v).toNatLinearEquiv (LinearEquiv.refl ℕ NNReal)).toAddEquiv

/-- **`ρ_v` of `F^{⊩▶×μ}_mod`**, `v ∈ V^non`: `ρ_v` of `F^⊩_mod` through
`(O^▶)^rlf ≅ Φ^rlf_{C^⊢_v}`. -/
def rhoBlackNon (v : Vnon D) :
    phiAt (Sum.inl v : GlobalRealified.Place (Kmod D)) ≃+ BlackRlf (fBlackModel D v) :=
  (rhoModelNon D v).trans (blackToVdash D v).symm

theorem blackToVdash_rhoBlackNon (v : Vnon D) (x) :
    blackToVdash D v (rhoBlackNon D v x) = rhoModelNon D v x := by
  rw [rhoBlackNon, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]

/-- **`ρ_v(log⊢_mod(p_v)) = (1/[K_v : (F_mod)_v])·logΦ(p_v)`** (IUT I, Example 3.5 (i)) for the
model `F^{⊩▶×μ}`-prime-strip, in the coordinate `ord` (`O^▶ ≅ Φ_{C^⊢_v}`). -/
theorem rlfCoord_blackToVdash_logMod (v : Vnon D) :
    ((rlfCoord _ (ordTau_pos D v) (blackToVdash D v (rhoBlackNon D v ⟨_, logMod_mem D v⟩)) :
      NNReal) : ℝ) =
      1 / GlobalRealified.localDeg (Sum.inl (D.V.sectFin v) : GlobalRealified.Place D.Kt)
        (Sum.inl v : GlobalRealified.Place (Kmod D)) := by
  rw [blackToVdash_rhoBlackNon]
  exact rlfCoord_rhoModelNon_logMod D v

/-! #### `V^arc` -/

/-- `e^{-t} ∈ (0, 1]`. -/
def expRay (t : NNReal) : rayC :=
  ⟨⟨(Real.exp (-(t : ℝ)) : ℂ), mem_orhdC.mpr ⟨by exact_mod_cast (Real.exp_pos _).ne', by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.2)⟩⟩,
    ⟨by
      change 0 < ((Real.exp (-(t : ℝ)) : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; exact Real.exp_pos _, Complex.ofReal_im _⟩⟩

lemma norm_ray_pos (r : rayC) : 0 < ‖((r : orhdC) : ℂ)‖ :=
  norm_pos_iff.mpr (mem_orhdC.mp (r : orhdC).2).1

lemma norm_ray_le_one (r : rayC) : ‖((r : orhdC) : ℂ)‖ ≤ 1 :=
  (mem_orhdC.mp (r : orhdC).2).2

/-- **`ℝ_{≥0} ≅ (0, 1]`**, `t ↦ e^{-t}`. -/
def nnRay : NNReal ≃+ Additive rayC where
  toFun t := Additive.ofMul (expRay t)
  invFun r := ⟨-Real.log ‖(((Additive.toMul r : rayC) : orhdC) : ℂ)‖,
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (norm_ray_le_one _))⟩
  left_inv t := NNReal.eq (by
    change -Real.log ‖((Real.exp (-(t : ℝ)) : ℝ) : ℂ)‖ = t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg])
  right_inv r := by
    apply Additive.toMul.injective
    apply Subtype.ext; apply Subtype.ext
    change ((Real.exp (-(-Real.log ‖(((Additive.toMul r : rayC) : orhdC) : ℂ)‖)) : ℝ) : ℂ) = _
    rw [neg_neg, Real.exp_log (norm_ray_pos _)]
    exact (ray_eq_norm (Additive.toMul r).2).symm
  map_add' a b := by
    apply Additive.toMul.injective
    apply Subtype.ext; apply Subtype.ext
    change ((Real.exp (-((a + b : NNReal) : ℝ)) : ℝ) : ℂ) =
      (Real.exp (-(a : ℝ)) : ℂ) * (Real.exp (-(b : ℝ)) : ℂ)
    rw [NNReal.coe_add, neg_add, Real.exp_add, Complex.ofReal_mul]

instance : Subsingleton (rayC)ˣ := by
  refine ⟨fun u v => ?_⟩
  have key : ∀ w : (rayC)ˣ, w = 1 := fun w => by
    have h := congrArg (fun x : rayC => ‖((x : orhdC) : ℂ)‖) w.mul_inv
    simp only [Submonoid.coe_mul, Submonoid.coe_one, norm_mul, norm_one] at h
    have h1 := norm_ray_le_one (w : rayC)
    have h2 := norm_ray_le_one ((w⁻¹ : (rayC)ˣ) : rayC)
    have hw : ‖(((w : rayC) : orhdC) : ℂ)‖ = 1 := by
      nlinarith [norm_ray_pos (w : rayC), norm_ray_pos ((w⁻¹ : (rayC)ˣ) : rayC)]
    apply Units.ext; apply Subtype.ext; apply Subtype.ext
    rw [ray_eq_norm (w : rayC).2, hw]
    simp
  rw [key u, key v]

/-- **`ρ_v` of `F^{⊩▶×μ}_mod`**, `v ∈ V^arc`: `ρ_v` of `F^⊩_mod`, then `t ↦ e^{-t} ∈ (0, 1]`. -/
def rhoBlackArc (w : Varc D) :
    phiAt (Sum.inr w : GlobalRealified.Place (Kmod D)) ≃+ Additive (Associates fBlackArcModel.M) :=
  (((rhoModelArc D w).trans nnRealCone.symm).trans nnRay).trans
    (MulEquiv.toAdditive (assocProdEquiv rayC OxMuArc)).symm

/-- **`F^{⊩▶×μ}_mod`** (IUT II, Definition 4.9 (viii)): the global data of `F_mod`, the
tautological `F^{⊢▶×μ}`-prime-strip and the `ρ_v` above. -/
def FRlfBlackData.ofThetaData : FRlfBlackData D where
  glob := HodgeTheater.FRlfGlobal.ofThetaData D
  strip := FBlackStrip.ofThetaData D
  rhoNon v := rhoBlackNon D v
  rhoArc w := rhoBlackArc D w

/-- **An `F^{⊩▶×μ}`-prime-strip** (IUT II, Definition 4.9 (viii)): data isomorphic to
`F^{⊩▶×μ}_mod` (condition (f) of IUT I, Definition 5.2 (iv)). -/
structure FRlfBlackStrip : Type 1 where
  /-- The data. -/
  X : FRlfBlackData D
  /-- They are isomorphic to `F^{⊩▶×μ}_mod`. -/
  equiv_model : Nonempty (X.Iso (FRlfBlackData.ofThetaData D))

variable {D}

/-- **Isomorphisms of `F^{⊩▶×μ}`-prime-strips**. -/
def FRlfBlackStrip.Iso (P Q : FRlfBlackStrip D) : Type := P.X.Iso Q.X

/-- **Any two `F^{⊩▶×μ}`-prime-strips are isomorphic.** -/
theorem FRlfBlackStrip.nonempty_iso (P Q : FRlfBlackStrip D) : Nonempty (P.Iso Q) :=
  ⟨P.equiv_model.some.trans Q.equiv_model.some.symm⟩

variable (D)

/-- **The tautological `F^{⊩▶×μ}`-prime-strip `F^{⊩▶×μ}_mod`**. -/
def FRlfBlackStrip.ofThetaData : FRlfBlackStrip D :=
  ⟨FRlfBlackData.ofThetaData D, ⟨FRlfBlackData.Iso.refl _⟩⟩

end Model

end PrimeStrip

end Multiradial

end Iut
