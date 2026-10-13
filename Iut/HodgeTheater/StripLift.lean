/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.PrimeStrip
import Iut.Reconstruction.Local.Valuation
import Iut.Reconstruction.Local.LogVolumeCompletion

/-!
# Lifting isomorphisms of `D^⊢`-prime-strips to `F^⊢`-prime-strips (IUT I, Corollary 5.3(ii))

IUT I, Corollary 5.3 states that the passage from an `F`- (resp. `F^⊢`-) prime-strip to its
`D`- (resp. `D^⊢`-) prime-strip induces a **surjection** on isomorphism sets: the Frobenioids
are reconstructed functorially from their base categories, so isomorphisms of the bases lift.
In the P18 model (`PrimeStrip.lean`) the Frobenioid components are categories recorded up to
equivalence, over the trivial Galois extension and not tied to a base; the passage `F ↦ D` is
not defined there. Here we

1. construct the **Galois-induced autoequivalence of the `p`-adic Frobenioid**: an automorphism
   `φ` of `G_v = Gal(K̄_v/K_v)` gives, through P17's reconstruction `Kˣ ≃* Kˣ`
   (`Reconstruction.galEquiv_multEquiv`), an `ord`-preserving automorphism `β = galMult φ` of the
   rational functions `K_vˣ`, hence an autoequivalence `galFrob φ` of `PAdic v` acting by
   `(deg, base, Z, u) ↦ (deg, base, Z, β u)`; this is functorial in `φ`;
2. define **non-archimedean `D^⊢`- and `F^⊢`-prime-strips with the local Galois groups**
   `Gal(K̄_v/K_v)` (`DGalStrip`, `FGalStrip`, with the passage `FGalStrip.toD`), and prove the
   lifting statements: for arbitrary `F^⊢`-prime-strips every isomorphism of the `D^⊢`-strips
   lifts, the lifts being parametrised by equivalences of the Frobenioid components
   (`FGalStrip.liftsEquiv`: no uniqueness in the model); for **rigidified** `D^⊢`-prime-strips
   (`RigidDGalStrip`: identifications `κ_v` of the constituents with `Gal(K̄_v/K_v)`), the
   reconstruction `RigidDGalStrip.toF` and the **Galois-induced lift** `RigidDGalStrip.liftIso`,
   whose Frobenioid portion is `galFrob` of the Galois automorphism `gal f v` read off from `f`.

## Main results

* `Reconstruction.galEquiv_multEquiv_trans`, `galEquiv_multEquiv_refl`: functoriality of P17's
  reconstruction `Aut(G_k) → Aut(kˣ)`;
* `Frobenioid.PAdic.OrdPres`, **`ordPres_of_norm_le_one`** (an automorphism of `K_vˣ` preserving
  the unit ball preserves `ord_v`), `unitsFunctor`, `unitsEquiv` (`PAdic v ≌ PAdic v`),
  `unitsFunctor_trans`, `unitsFunctor_refl`;
* `LocGal`, `galMult`, `norm_galMult_le_one_iff`, `ordPres_galMult`, **`galFrob`**,
  `galFrob_map_u`, `galFrob_trans_functor`, `galFrob_refl_functor`;
* `HodgeTheater.locGalModel`, `DGalStrip`, `FGalStrip`, `FGalStrip.toD`, `FGalStrip.forget`,
  **`FGalStrip.liftsEquiv`**, `FGalStrip.exists_lift`;
* `RigidDGalStrip`, `RigidDGalStrip.gal` (`gal_refl`, `gal_trans`), `galFrobAt`,
  `RigidDGalStrip.toF`, `toF_toD`, **`RigidDGalStrip.liftIso`**, `forget_liftIso`,
  **`RigidDGalStrip.exists_lift`** (Corollary 5.3(ii) in the model), `liftIso_refl_functor`,
  `liftIso_trans_functor` (the lift is functorial).

## Deviations

* Only `v ∈ V^non`. The model of `G_v` is `Gal(K̄_v/K_v)` (the group on which P17 operates), not
  the decomposition group `galModel` of `PrimeStrip.lean` (a closed subgroup of `Gal(F̄/K)`; the
  isomorphism of the two is not formalised).
* The rigidifications `κ_v` are data; they stand for the Kummer structures of IUT. Without them
  the arithmetic of the model does not see the abstract strip, and the lift of
  `FGalStrip.exists_lift` is the weak (non-unique) one.
* That the `galFrob φ` are the **only** lifts compatible with the Frobenioid structure (the
  uniqueness part of Corollary 5.3) is not claimed.
-/

namespace Iut

namespace Reconstruction

section Functorial

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- **The reconstruction `Aut(G_k) → Aut(kˣ)` is functorial**: composition. -/
theorem galEquiv_multEquiv_trans (φ ψ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) (x : kˣ) :
    galEquiv_multEquiv p p (φ.trans ψ) x =
      galEquiv_multEquiv p p ψ (galEquiv_multEquiv p p φ x) := by
  apply (multAbEquiv p k Ω).injective
  apply Subtype.ext
  rw [multAbEquiv_galEquiv_multEquiv, multAbEquiv_galEquiv_multEquiv,
    multAbEquiv_galEquiv_multEquiv]
  generalize (multAbEquiv p k Ω x : TopologicalAbelianization (Ω ≃ₐ[k] Ω)) = y
  induction y using QuotientGroup.induction_on with
  | H g => rfl

/-- Identity. -/
theorem galEquiv_multEquiv_refl (x : kˣ) :
    galEquiv_multEquiv p p (ContinuousMulEquiv.refl (Ω ≃ₐ[k] Ω)) x = x := by
  apply (multAbEquiv p k Ω).injective
  apply Subtype.ext
  rw [multAbEquiv_galEquiv_multEquiv]
  generalize (multAbEquiv p k Ω x : TopologicalAbelianization (Ω ≃ₐ[k] Ω)) = y
  induction y using QuotientGroup.induction_on with
  | H g => rfl

end Functorial

end Reconstruction

namespace Frobenioid

open CategoryTheory NumberField LocalConstruct

universe u

namespace PAdic

variable {K : Type u} [Field K] [NumberField K] {w : FinitePlace K}

/-- An automorphism `β` of `K_wˣ` **preserves `ord_w`**. -/
def OrdPres (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ) : Prop :=
  ∀ x, ordHom w (Additive.ofMul (β x)) = ordHom w (Additive.ofMul x)

theorem OrdPres.symm {β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ} (h : OrdPres β) :
    OrdPres β.symm := fun x => by
  rw [← h, MulEquiv.apply_symm_apply]

theorem OrdPres.trans {β γ : (completionAt K w)ˣ ≃* (completionAt K w)ˣ} (hβ : OrdPres β)
    (hγ : OrdPres γ) : OrdPres (β.trans γ) := fun x => by
  rw [MulEquiv.trans_apply, hγ, hβ]

theorem ordPres_refl : OrdPres (MulEquiv.refl (completionAt K w)ˣ) := fun _ => rfl

variable (w) in
/-- A uniformizer: `ord_w(π) = 1`. -/
theorem exists_ordHom_eq_one : ∃ π : (completionAt K w)ˣ, ordHom w (Additive.ofMul π) = ⟨1⟩ := by
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer K
  have hv : Valued.v (π : w.maximalIdeal.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hne : (π : w.maximalIdeal.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  simp [ordHom, hπ]

/-- `ord_w` as an integer-valued function on `K_wˣ`. -/
noncomputable def ordZ (x : (completionAt K w)ˣ) : ℤ := (ordHom w (Additive.ofMul x)).down

theorem ordZ_mul (x y : (completionAt K w)ˣ) : ordZ (x * y) = ordZ x + ordZ y := by
  simp only [ordZ, ofMul_mul, map_add, ULift.add_down]

theorem ordZ_inv (x : (completionAt K w)ˣ) : ordZ x⁻¹ = -ordZ x := by
  simp only [ordZ, ofMul_inv, map_neg, ULift.neg_down]

theorem ordZ_zpow (x : (completionAt K w)ˣ) (n : ℤ) : ordZ (x ^ n) = n * ordZ x := by
  simp only [ordZ, ofMul_zpow, map_zsmul]
  rw [ULift.smul_down, smul_eq_mul]

/-- **An automorphism of `K_wˣ` preserving the unit ball `{‖x‖ ≤ 1}` preserves `ord_w`**: the
homomorphisms `ord ∘ β` and `ord` to `ℤ` have the same nonnegative cone, hence agree up to a
positive factor, which is `1` as `β` is surjective. -/
theorem ordPres_of_norm_le_one (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (h : ∀ x, ‖((β x : (completionAt K w)ˣ) : completionAt K w)‖ ≤ 1 ↔
      ‖(x : completionAt K w)‖ ≤ 1) : OrdPres β := by
  have hfg : ∀ x, 0 ≤ ordZ (β x) ↔ 0 ≤ ordZ x := fun x => by
    rw [ordZ, ordZ, ordHom_nonneg_iff, ordHom_nonneg_iff, h]
  have hzero : ∀ x, ordZ x = 0 → ordZ (β x) = 0 := fun x hx => by
    have h1 := (hfg x).2 hx.ge
    have h2 := (hfg x⁻¹).2 (by rw [ordZ_inv, hx, neg_zero])
    rw [map_inv, ordZ_inv] at h2
    omega
  obtain ⟨π, hπ⟩ := exists_ordHom_eq_one w
  have hgπ : ordZ π = 1 := by rw [ordZ, hπ]
  have hlin : ∀ x, ordZ (β x) = ordZ x * ordZ (β π) := fun x => by
    have := hzero (x * π ^ (-ordZ x)) (by
      rw [ordZ_mul, ordZ_zpow, hgπ]
      ring)
    rw [map_mul, map_zpow, ordZ_mul, ordZ_zpow] at this
    linarith
  have hc : ordZ (β π) = 1 := by
    have h1 := hlin (β.symm π)
    rw [MulEquiv.apply_symm_apply, hgπ] at h1
    have h0 : 0 ≤ ordZ (β π) := (hfg π).2 (by rw [hgπ]; exact zero_le_one)
    exact Int.eq_one_of_mul_eq_one_right h0 (by rw [mul_comm]; exact h1.symm)
  intro x
  ext
  have := hlin x
  rw [hc, mul_one] at this
  exact this

/-! ### The autoequivalence of the `p`-adic Frobenioid induced by `β ∈ Aut(K_wˣ)` -/

/-- **The functor `PAdic w ⥤ PAdic w` induced by an `ord`-preserving automorphism `β` of the
rational functions `K_wˣ`**: the identity on objects, `(deg, base, Z, u) ↦ (deg, base, Z, β u)`
on morphisms. -/
noncomputable def unitsFunctor (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ) (hβ : OrdPres β) :
    PAdic w ⥤ PAdic w where
  obj X := X
  map {X Y} φ := Model.mk' φ.deg φ.base φ.div φ.div_mem (MulEquiv.toAdditive β φ.u) (by
    change _ = _ + ordHom w (Additive.ofMul (β (Additive.toMul φ.u)))
    rw [hβ]
    exact φ.rel)
  map_id X := Model.hom_ext rfl rfl rfl (by
    change MulEquiv.toAdditive β 0 = 0
    exact map_zero _)
  map_comp {X Y Z} φ ψ := Model.hom_ext rfl rfl rfl (by
    change MulEquiv.toAdditive β (ψ.u + (ψ.deg : ℕ) • φ.u) =
      MulEquiv.toAdditive β ψ.u + (ψ.deg : ℕ) • MulEquiv.toAdditive β φ.u
    rw [map_add, map_nsmul])

@[simp] lemma unitsFunctor_obj (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ) (hβ : OrdPres β)
    (X : PAdic w) : (unitsFunctor β hβ).obj X = X := rfl

@[simp] lemma unitsFunctor_map_deg (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) : ((unitsFunctor β hβ).map φ).deg = φ.deg :=
  rfl

@[simp] lemma unitsFunctor_map_base (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) : ((unitsFunctor β hβ).map φ).base = φ.base :=
  rfl

@[simp] lemma unitsFunctor_map_div (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) : ((unitsFunctor β hβ).map φ).div = φ.div :=
  rfl

/-- **The rational function of the image of `φ` is `β (u_φ)`.** -/
@[simp] lemma unitsFunctor_map_u (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) :
    ((unitsFunctor β hβ).map φ).u = Additive.ofMul (β (Additive.toMul φ.u)) :=
  rfl

theorem unitsFunctor_congr {β β' : (completionAt K w)ˣ ≃* (completionAt K w)ˣ} (h : β = β')
    (hβ : OrdPres β) (hβ' : OrdPres β') : unitsFunctor β hβ = unitsFunctor β' hβ' := by
  subst h
  rfl

theorem unitsFunctor_trans (β γ : (completionAt K w)ˣ ≃* (completionAt K w)ˣ) (hβ : OrdPres β)
    (hγ : OrdPres γ) :
    unitsFunctor (β.trans γ) (hβ.trans hγ) = unitsFunctor β hβ ⋙ unitsFunctor γ hγ :=
  rfl

theorem unitsFunctor_refl : unitsFunctor (MulEquiv.refl _) ordPres_refl = 𝟭 (PAdic w) :=
  rfl

theorem unitsFunctor_symm_map (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) :
    (unitsFunctor β.symm hβ.symm).map ((unitsFunctor β hβ).map φ) = φ :=
  Model.hom_ext rfl rfl rfl (by simp)

theorem unitsFunctor_map_symm (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) {X Y : PAdic w} (φ : X ⟶ Y) :
    (unitsFunctor β hβ).map ((unitsFunctor β.symm hβ.symm).map φ) = φ :=
  Model.hom_ext rfl rfl rfl (by simp)

/-- **The autoequivalence of the `p`-adic Frobenioid induced by `β`.** -/
noncomputable def unitsEquiv (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ) (hβ : OrdPres β) :
    PAdic w ≌ PAdic w where
  functor := unitsFunctor β hβ
  inverse := unitsFunctor β.symm hβ.symm
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun φ => by
    simp only [Functor.id_map, Iso.refl_hom, Functor.comp_map, unitsFunctor_symm_map]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun φ => by
    simp only [Functor.id_map, Iso.refl_hom, Functor.comp_map, unitsFunctor_map_symm]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp X := by
    simp only [NatIso.ofComponents_hom_app, Iso.refl_hom]
    exact (Category.comp_id _).trans ((unitsFunctor β hβ).map_id X)

@[simp] lemma unitsEquiv_functor (β : (completionAt K w)ˣ ≃* (completionAt K w)ˣ)
    (hβ : OrdPres β) : (unitsEquiv β hβ).functor = unitsFunctor β hβ := rfl

/-! ### The autoequivalence induced by a Galois automorphism -/

section Galois

variable {p : ℕ} [Fact p.Prime] (hw : residueChar w = p)

variable (w) in
/-- **The local Galois group** `G_w = Gal(K̄_w/K_w)` (the same type as `LogLink.CompGal w`). -/
abbrev LocGal : Type u :=
  AlgebraicClosure (completionAt K w) ≃ₐ[completionAt K w] AlgebraicClosure (completionAt K w)

/-- **The automorphism of `K_wˣ` reconstructed from a topological automorphism `φ` of `G_w`**
(P17, `Reconstruction.galEquiv_multEquiv`, [AbsTopIII], Proposition 5.8(i)), for the
`ℚ_p`-structure `padicAlgebra hw`. -/
noncomputable def galMult (φ : LocGal w ≃ₜ* LocGal w) :
    (completionAt K w)ˣ ≃* (completionAt K w)ˣ :=
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  Reconstruction.galEquiv_multEquiv p p φ

/-- **The reconstructed automorphism preserves the unit ball** (the valuation is
group-theoretic, `Reconstruction.v_galEquiv_multEquiv`). -/
theorem norm_galMult_le_one_iff (φ : LocGal w ≃ₜ* LocGal w) (x : (completionAt K w)ˣ) :
    ‖((galMult hw φ x : (completionAt K w)ˣ) : completionAt K w)‖ ≤ 1 ↔
      ‖(x : completionAt K w)‖ ≤ 1 := by
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  have hb := Reconstruction.hball_completionAt hw
  rw [hb, hb, PadicField.nrm_le_one_iff_v_nonneg (Units.ne_zero _),
    PadicField.nrm_le_one_iff_v_nonneg (Units.ne_zero _)]
  change 0 ≤ PadicField.v p ((Reconstruction.galEquiv_multEquiv p p φ x :
    (completionAt K w)ˣ) : completionAt K w) ↔ _
  rw [Reconstruction.v_galEquiv_multEquiv]

theorem ordPres_galMult (φ : LocGal w ≃ₜ* LocGal w) : OrdPres (galMult hw φ) :=
  ordPres_of_norm_le_one _ (norm_galMult_le_one_iff hw φ)

/-- **The autoequivalence of the `p`-adic Frobenioid of `K_w` induced by a topological
automorphism `φ` of `G_w`** (the Frobenioid portion reconstructed functorially from `G_w`). -/
noncomputable def galFrob (φ : LocGal w ≃ₜ* LocGal w) : PAdic w ≌ PAdic w :=
  unitsEquiv (galMult hw φ) (ordPres_galMult hw φ)

/-- **It acts on rational functions by the P17 reconstruction** `galEquiv_multEquiv`. -/
@[simp] theorem galFrob_map_u (φ : LocGal w ≃ₜ* LocGal w) {X Y : PAdic w} (f : X ⟶ Y) :
    ((galFrob hw φ).functor.map f).u = Additive.ofMul (galMult hw φ (Additive.toMul f.u)) :=
  rfl

theorem galMult_trans (φ ψ : LocGal w ≃ₜ* LocGal w) :
    galMult hw (φ.trans ψ) = (galMult hw φ).trans (galMult hw ψ) := by
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  ext1 x
  exact Reconstruction.galEquiv_multEquiv_trans φ ψ x

theorem galMult_refl : galMult hw (ContinuousMulEquiv.refl (LocGal w)) = MulEquiv.refl _ := by
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  haveI : Algebra.IsAlgebraic ℚ_[p] (AlgebraicClosure (completionAt K w)) :=
    Algebra.IsAlgebraic.trans ℚ_[p] (completionAt K w) _
  ext1 x
  exact Reconstruction.galEquiv_multEquiv_refl x

/-- **Functoriality of the lift**: `galFrob (φ ψ) = galFrob φ ⋙ galFrob ψ`. -/
theorem galFrob_trans_functor (φ ψ : LocGal w ≃ₜ* LocGal w) :
    (galFrob hw (φ.trans ψ)).functor = (galFrob hw φ).functor ⋙ (galFrob hw ψ).functor := by
  exact unitsFunctor_congr (galMult_trans hw φ ψ) (ordPres_galMult hw _)
    ((ordPres_galMult hw φ).trans (ordPres_galMult hw ψ))

theorem galFrob_refl_functor :
    (galFrob hw (ContinuousMulEquiv.refl (LocGal w))).functor = 𝟭 (PAdic w) := by
  exact unitsFunctor_congr (galMult_refl hw) (ordPres_galMult hw _) ordPres_refl

end Galois

end PAdic

end Frobenioid

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid Frobenioid.PAdic

universe u

noncomputable section

section Strips

variable (D : InitialThetaData.{u})

/-- **`V^non ≅ V_mod^non`**: the finite places of `F_mod`, indexing the non-archimedean portion
of the prime-strips. -/
abbrev Vnon : Type u := FinitePlace ↥(fieldOfModuli D.F D.E)

/-- **The local Galois group `G_v = Gal(K̄_v/K_v)`** at `v ∈ V^non`, as a topological group. -/
noncomputable def locGalModel (w : Vnon D) : Kind.TGrp.{u} := ⟨LocGal (D.V.sectFin w)⟩

/-- The kinds of the constituents of a `D^⊢`-prime-strip (non-archimedean portion). -/
def dGalKind : Vnon D → Kind.{u} := fun _ => Kind.tgrp

/-- **`D^⊢`-prime-strips (non-archimedean portion), with the local Galois groups**
`G_v = Gal(K̄_v/K_v)` as models (IUT I, Definition 4.1(iii); the decomposition group of
`galModel` is replaced by the Galois group of the completion, on which P17 operates). -/
abbrev DGalStrip : Type (u + 1) := PrimeStrip (dGalKind D) (locGalModel D)

/-- The kinds of the constituents of an `F^⊢`-prime-strip (non-archimedean portion): a category
(the Frobenioid, up to equivalence) and a topological group (its base `G_v`). -/
def fGalKind : Vnon D → Kind.{u} := fun _ => Kind.prod Kind.cat Kind.tgrp

/-- **The tautological `F^⊢`-prime-strip** (non-archimedean portion): the `p`-adic Frobenioid of
`K_v` with the base `G_v` (IUT I, Definition 5.2(ii)). -/
noncomputable def fGalModel : ∀ w : Vnon D, (fGalKind D w).Obj :=
  fun w => (padicModel D w, locGalModel D w)

/-- **`F^⊢`-prime-strips (non-archimedean portion), with the local Galois groups as bases.** -/
abbrev FGalStrip : Type (u + 1) := PrimeStrip (fGalKind D) (fGalModel D)

/-- The passage `F^⊢ ↦ D^⊢` (the base), componentwise. -/
def forgetKind (w : Vnon D) : PrimeStrip.KindMap (fGalKind D w) (dGalKind D w) :=
  ⟨fun X => X.2, fun f => f.2⟩

variable {D}

/-- **The `D^⊢`-prime-strip of an `F^⊢`-prime-strip** (IUT I, Corollary 5.3(i)-(iii): the
functor `†F^⊢ ↦ †D^⊢`). -/
def FGalStrip.toD (P : FGalStrip D) : DGalStrip D :=
  PrimeStrip.map (forgetKind D) (fun w => ⟨(dGalKind D w).refl _⟩) P

/-- The induced map `Isom(†F^⊢, ‡F^⊢) → Isom(†D^⊢, ‡D^⊢)`. -/
def FGalStrip.forget {P Q : FGalStrip D} (g : P.Iso Q) : P.toD.Iso Q.toD :=
  PrimeStrip.mapIso (forgetKind D) (fun w => ⟨(dGalKind D w).refl _⟩) g

/-- **The set of lifts of an isomorphism of `D^⊢`-prime-strips** to arbitrary `F^⊢`-prime-strips
is the set of families of equivalences of the Frobenioid components: in the model the
Frobenioids are recorded up to equivalence and are not tied to their bases, so the lifts exist
but are not unique (in IUT I, Corollary 5.3, the Frobenioid is reconstructed from the base). -/
def FGalStrip.liftsEquiv {P Q : FGalStrip D} (f : P.toD.Iso Q.toD) :
    {g : P.Iso Q // FGalStrip.forget g = f} ≃
      ∀ w, Kind.cat.Iso (P.obj w).1 (Q.obj w).1 where
  toFun g w := (g.1 w).1
  invFun e := ⟨fun w => (e w, f w), rfl⟩
  left_inv g := by
    obtain ⟨g, rfl⟩ := g
    rfl
  right_inv e := rfl

/-- **Every isomorphism of `D^⊢`-prime-strips lifts** (to any `F^⊢`-prime-strips with these
`D^⊢`-prime-strips; the weak form, see `RigidDGalStrip.liftIso` for the Galois-induced lift). -/
theorem FGalStrip.exists_lift {P Q : FGalStrip D} (f : P.toD.Iso Q.toD) :
    ∃ g : P.Iso Q, FGalStrip.forget g = f :=
  ⟨fun w => (((P.iso_model w).some.1.trans (Q.iso_model w).some.1.symm), f w), rfl⟩

variable (D) in
/-- **A `D^⊢`-prime-strip with a rigidification** (non-archimedean portion): at every
`v ∈ V^non` an identification `κ_v` of the constituent topological group with the model
`G_v = Gal(K̄_v/K_v)`. This is the datum which makes the arithmetic of the model (P17's
reconstruction on `Gal(K̄_v/K_v)`) applicable to the abstract strip; in IUT it corresponds to
the Kummer structure relating the abstract `†D^⊢_v` to the field `K_v` of a Hodge theater. -/
structure RigidDGalStrip where
  /-- The `D^⊢`-prime-strip. -/
  strip : DGalStrip D
  /-- The rigidification `κ_v : †G_v ≅ Gal(K̄_v/K_v)`. -/
  kappa : ∀ w, (strip.obj w : Kind.TGrp.{u}).carrier ≃ₜ* LocGal (D.V.sectFin w)

namespace RigidDGalStrip

variable (D) in
/-- The tautological rigidified `D^⊢`-prime-strip. -/
noncomputable def taut : RigidDGalStrip D :=
  ⟨PrimeStrip.tautological _ _, fun _ => ContinuousMulEquiv.refl _⟩

/-- **The Galois automorphisms read off from an isomorphism of `D^⊢`-prime-strips**:
`φ_v = κ^Q_v ∘ f_v ∘ (κ^P_v)⁻¹ ∈ Aut(G_v)`. -/
def gal {P Q : RigidDGalStrip D} (f : P.strip.Iso Q.strip) (w : Vnon D) :
    LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w) :=
  ((P.kappa w).symm.trans (f w)).trans (Q.kappa w)

theorem gal_refl (P : RigidDGalStrip D) (w : Vnon D) :
    gal (PrimeStrip.Iso.refl P.strip) w = ContinuousMulEquiv.refl _ := by
  apply ContinuousMulEquiv.ext
  intro x
  exact (P.kappa w).apply_symm_apply x

theorem gal_trans {P Q R : RigidDGalStrip D} (f : P.strip.Iso Q.strip) (g : Q.strip.Iso R.strip)
    (w : Vnon D) : gal (PrimeStrip.Iso.trans f g) w = (gal f w).trans (gal g w) := by
  apply ContinuousMulEquiv.ext
  intro x
  simp only [gal, PrimeStrip.Iso.trans, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.symm_apply_apply]
  rfl

end RigidDGalStrip

variable (D) in
/-- **The Frobenioid autoequivalence at `v ∈ V^non` induced by `φ ∈ Aut(G_v)`**
(`Frobenioid.PAdic.galFrob` for the residue characteristic of `v`). -/
noncomputable def galFrobAt (w : Vnon D) (φ : LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w)) :
    PAdic (D.V.sectFin w) ≌ PAdic (D.V.sectFin w) :=
  haveI : Fact (residueChar (D.V.sectFin w)).Prime := ⟨residueChar_prime _⟩
  galFrob rfl φ

theorem galFrobAt_map_u (w : Vnon D) (φ : LocGal (D.V.sectFin w) ≃ₜ* LocGal (D.V.sectFin w))
    {X Y : PAdic (D.V.sectFin w)} (f : X ⟶ Y) :
    haveI : Fact (residueChar (D.V.sectFin w)).Prime := ⟨residueChar_prime _⟩
    ((galFrobAt D w φ).functor.map f).u = Additive.ofMul (galMult rfl φ (Additive.toMul f.u)) :=
  rfl

namespace RigidDGalStrip

/-- **The reconstruction `†D^⊢ ↦ †F^⊢`** (IUT I, Corollary 5.3, in the model): the `p`-adic
Frobenioid of `K_v` over the rigidified `†G_v`. -/
noncomputable def toF (P : RigidDGalStrip D) : FGalStrip D :=
  ⟨fun w => (padicModel D w, P.strip.obj w), fun w => ⟨(CategoryTheory.Equivalence.refl,
    P.kappa w)⟩⟩

/-- The `D^⊢`-prime-strip of the reconstructed `F^⊢`-prime-strip is the given one. -/
theorem toF_toD (P : RigidDGalStrip D) : P.toF.toD = P.strip := rfl

/-- **The lift of an isomorphism of `D^⊢`-prime-strips** (IUT I, Corollary 5.3(ii) in the
model): at every `v ∈ V^non` the Frobenioid autoequivalence induced (via P17) by the Galois
automorphism `φ_v = gal f v` read off from `f`, together with `f_v`. -/
noncomputable def liftIso {P Q : RigidDGalStrip D} (f : P.strip.Iso Q.strip) :
    P.toF.Iso Q.toF :=
  fun w => (galFrobAt D w (gal f w), f w)

/-- **`liftIso f` lifts `f`.** -/
theorem forget_liftIso {P Q : RigidDGalStrip D} (f : P.strip.Iso Q.strip) :
    FGalStrip.forget (liftIso f) = f := rfl

/-- **IUT I, Corollary 5.3(ii) in the model**: every isomorphism of rigidified
`D^⊢`-prime-strips lifts to an isomorphism of the reconstructed `F^⊢`-prime-strips whose
Frobenioid portion is induced by the Galois automorphisms read off from the strips. -/
theorem exists_lift {P Q : RigidDGalStrip D} (f : P.strip.Iso Q.strip) :
    ∃ g : P.toF.Iso Q.toF, FGalStrip.forget g = f ∧
      ∀ w, (g w).1.functor = (galFrobAt D w (gal f w)).functor :=
  ⟨liftIso f, rfl, fun _ => rfl⟩

/-- **The lift is functorial** (identities). -/
theorem liftIso_refl_functor (P : RigidDGalStrip D) (w : Vnon D) :
    (liftIso (PrimeStrip.Iso.refl P.strip) w).1.functor = 𝟭 _ := by
  change (galFrobAt D w _).functor = _
  rw [gal_refl]
  haveI : Fact (residueChar (D.V.sectFin w)).Prime := ⟨residueChar_prime _⟩
  exact galFrob_refl_functor rfl

/-- **The lift is functorial** (composites). -/
theorem liftIso_trans_functor {P Q R : RigidDGalStrip D} (f : P.strip.Iso Q.strip)
    (g : Q.strip.Iso R.strip) (w : Vnon D) :
    (liftIso (PrimeStrip.Iso.trans f g) w).1.functor =
      (liftIso f w).1.functor ⋙ (liftIso g w).1.functor := by
  change (galFrobAt D w _).functor = (galFrobAt D w _).functor ⋙ (galFrobAt D w _).functor
  rw [gal_trans]
  haveI : Fact (residueChar (D.V.sectFin w)).Prime := ⟨residueChar_prime _⟩
  exact galFrob_trans_functor rfl _ _

end RigidDGalStrip

end Strips

end

end HodgeTheater

end Iut
