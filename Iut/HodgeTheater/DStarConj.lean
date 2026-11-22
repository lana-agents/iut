/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStarDescent
import Iut.HodgeTheater.DStarElastic
import Iut.Reconstruction.Cusp.HemiPiXChar
import Iut.Reconstruction.Thm19.AutConj
import Iut.Reconstruction.Thm19.RatSection

/-!
# `CKSemiAbsConj` from [AbsTopIII] Thm 1.9 (MR9)

`HodgeTheater/DStarDescent.lean` reduces the descent `π₁(C_{F_mod}) ≅ Aut(π₁(C_K))` to two named
statements, `CKStrictSemiAbs` ([AbsTopI] Cor. 2.8 (ii)) and `CKSemiAbsConj`: a continuous
automorphism `α` of `π₁(C_K)` preserving `Δ_{C_K}` acts on the image of `π₁(C_K)` in
`Gal(F̄/F_mod)` by conjugation by an element of `Gal(F̄/F_mod)`. This file proves
`CKSemiAbsConj` (`ckSemiAbsConj`) from the functoriality of [AbsTopIII] Thm 1.9 for
`X_K = E_K ∖ {O}` (`Thm19/AutConj.lean`), with the inputs of that theorem as explicit
arguments: `BelyiCuspSpec` (MR8) and `RelIsomDGC.Exists` (MR7).

* `restrictAutOfRange` (generic): an automorphism preserving the image of an embedding restricts;
* `piConstC_orbiIncl`, **`mem_range_orbiIncl_iff_of_aut`** (`α(Π_X) = Π_X`, from
  `Reconstruction/Cusp/HemiPiXChar.lean`: `Π_X` is group-theoretic in `Π_C` by the `ℓ`-torsion
  condition of IUT I, Def. 3.1 (c), (d)), **`exists_conj_hemi`** (an automorphism of `Π_C`
  preserving `Δ_C` acts on `Gal(k̄ / K)` as conjugation by `σ` with `σ(j) = j`);
* `resK` (`π₁(C_K) → Gal(k̄ / K)`), `iotaK` (`k̄ ≃ F̄`, an `F_mod`-embedding), **`iotaK_resK`**:
  `π₁(C_K) ↪ π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)` is `resK` conjugated by `iotaK`;
* **`ckSemiAbsConj`**; **`hAbs_of_strict`**, **`piCmodAutEquivOfStrict`**: the input `hAbs` of
  `DStarDescent` discharged; `CKStrictSemiAbs` is proved in `DStarElastic.lean` (`ckStrictSemiAbs`)
  from the very elasticity of `Gal(F̄/F_mod)` ([AbsTopI] Thm. 1.7 (iii)), the remaining standard
  input `hEl`.
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Iut.Reconstruction Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiPiXChar
  Iut.Reconstruction.Thm19
  Iut.Anabelian AlgebraicGeometry Belyi Belyi.Anabelian Topology KummerTheory KummerTheory.Curve
  Pi1 Pi1.Orbifold WeilCurves.FunctionField CurvesJacobian.Kummer
  CurvesJacobian.LocAn

universe u

/-! ### Restricting an automorphism to the image of an embedding -/

section Generic

variable {P Q : Type*} [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
  [IsTopologicalGroup P] [IsTopologicalGroup Q]

/-- An automorphism `β` of `Q` mapping the image of an injective homomorphism `ι : P → Q` onto
itself, as a group automorphism of `P`. -/
def restrictAutMul (ι : P →* Q) (hι : Function.Injective ι) (β : Q ≃* Q)
    (hβ : ∀ y, β y ∈ ι.range ↔ y ∈ ι.range) : P ≃* P :=
  (MonoidHom.ofInjective hι).trans
    ((β.subgroupMap ι.range).trans (MulEquiv.subgroupCongr (by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hβ z).2 hz
      · intro hy
        exact ⟨β.symm y, (hβ _).1 (by rw [MulEquiv.apply_symm_apply]; exact hy),
          β.apply_symm_apply y⟩)) |>.trans (MonoidHom.ofInjective hι).symm)

omit [TopologicalSpace P] [TopologicalSpace Q] [IsTopologicalGroup P] [IsTopologicalGroup Q] in
lemma restrictAutMul_spec (ι : P →* Q) (hι : Function.Injective ι) (β : Q ≃* Q)
    (hβ : ∀ y, β y ∈ ι.range ↔ y ∈ ι.range) (p : P) :
    ι (restrictAutMul ι hι β hβ p) = β (ι p) := by
  have h := (MonoidHom.ofInjective hι).apply_symm_apply
    ⟨β (ι p), (hβ (ι p)).2 ⟨p, rfl⟩⟩
  exact congrArg Subtype.val h

/-- **An automorphism `β` of `Q` preserving the image of an embedding `ι : P → Q` restricts to an
automorphism of `P`** (`ι ∘ restrictAutOfRange = β ∘ ι`). -/
def restrictAutOfRange (ι : P →ₜ* Q) (hι : IsEmbedding ι) (β : Q ≃ₜ* Q)
    (hβ : ∀ y, β y ∈ ι.toMonoidHom.range ↔ y ∈ ι.toMonoidHom.range) : P ≃ₜ* P where
  toMulEquiv := restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ
  continuous_toFun := by
    refine hι.isInducing.continuous_iff.2 ?_
    have e : ι ∘ restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ = β ∘ ι :=
      funext (restrictAutMul_spec ι.toMonoidHom hι.injective β.toMulEquiv hβ)
    change Continuous (ι ∘ restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ)
    rw [e]
    exact β.continuous.comp ι.continuous
  continuous_invFun := by
    refine hι.isInducing.continuous_iff.2 ?_
    have e : ι ∘ (restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ).symm =
        β.symm ∘ ι := funext fun q => by
      obtain ⟨p, rfl⟩ := (restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ).surjective q
      rw [Function.comp_apply, MulEquiv.symm_apply_apply, Function.comp_apply]
      change ι p = β.symm (ι.toMonoidHom (restrictAutMul ι.toMonoidHom hι.injective
        β.toMulEquiv hβ p))
      rw [restrictAutMul_spec]
      exact (β.symm_apply_apply _).symm
    change Continuous (ι ∘ (restrictAutMul ι.toMonoidHom hι.injective β.toMulEquiv hβ).symm)
    rw [e]
    exact β.symm.continuous.comp ι.continuous

omit [IsTopologicalGroup P] [IsTopologicalGroup Q] in
lemma restrictAutOfRange_spec (ι : P →ₜ* Q) (hι : IsEmbedding ι) (β : Q ≃ₜ* Q)
    (hβ : ∀ y, β y ∈ ι.toMonoidHom.range ↔ y ∈ ι.toMonoidHom.range) (p : P) :
    ι (restrictAutOfRange ι hι β hβ p) = β (ι p) :=
  restrictAutMul_spec ι.toMonoidHom hι.injective β.toMulEquiv hβ p

end Generic

/-! ### Automorphisms of `Π_C` of the hemi-elliptic orbicurve -/

section Hemi

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic
  Thm19.isAlgClosed_algebraicClosure Thm19.isFunctionField_fnf

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]

/-- `Π_C = H ⧸ ⟨⟨S⟩⟩` of `C = [(E ∖ {O}) / ±1]` (Galois model). -/
abbrev PiCG : Type u := GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H

/-- **`Π_X ↪ Π_C ↠ Gal(k̄ / K)` is `Π_X ↠ Gal(k̄ / K)`.** -/
lemma piConstC_orbiIncl (p : Pi (curveGaloisData K (transcendental_xN E))) :
    piConstC (hemiData E) (orbiIncl (hemiData E) p) =
      piToGk (curveGaloisData K (transcendental_xN E)) p := by
  induction p using QuotientGroup.induction_on with
  | H h =>
    refine AlgEquiv.ext fun z => Subtype.ext ?_
    exact (algebraMap_hToGk_apply (curveGaloisData K (transcendental_xN E)) h z).symm

/-- **`α(Π_X) = Π_X`** for an automorphism of `Π_C` preserving `Δ_C`, when `E[N] ⊆ E(K)` for an odd
`N > 1` (IUT I, Def. 3.1 (c), (d); `mem_hemiPiX_iff_aut`). -/
theorem mem_range_orbiIncl_iff_of_aut {N : ℕ} [NeZero N] (hcard : TorsionCardN E N)
    (hN : N ≠ 1) (hodd : Odd N) (β : PiCG E ≃ₜ* PiCG E)
    (hβ : ∀ y, piConstC (hemiData E) (β y) = 1 ↔ piConstC (hemiData E) y = 1) (y : PiCG E) :
    β y ∈ (orbiIncl (hemiData E)).toMonoidHom.range ↔
      y ∈ (orbiIncl (hemiData E)).toMonoidHom.range := by
  let Ω' := AlgebraicClosure K
  let e := (hemiData E).equivPi1
  let α' : HemiPiC E ≃ₜ* HemiPiC E := e.trans (β.trans e.symm)
  have he : ∀ τ, e (α' τ) = β (e τ) := fun τ => e.apply_symm_apply _
  have hα' : ∀ τ, α' τ ∈ hemiDeltaC E Ω' ↔ τ ∈ hemiDeltaC E Ω' := fun τ => by
    rw [hemiDeltaC, mem_ker_hemiPrC_iff₂, mem_ker_hemiPrC_iff₂, MonoidHom.mem_ker,
      MonoidHom.mem_ker, he]
    exact hβ _
  have key := mem_hemiPiX_iff_aut Ω' hcard hN hodd α' hα' (e.symm y)
  rw [hemiPiX, mem_range_hemiPiXEmb_iff₂, mem_range_hemiPiXEmb_iff₂, he,
    e.apply_symm_apply] at key
  exact key

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
  [CharZero Ω] [hc : Fact ((hypCurveE E).U : Set (hypCurveE E).Xbar)ᶜ.Nonempty]

set_option maxHeartbeats 3000000 in
-- `Π_X ↪ Π_C` and the Galois model of `Π_X` are compared at heavy instance terms
/-- **An automorphism of `Π_C` preserving `Δ_C` and `Π_X` acts on `Gal(k̄ / K)` by conjugation by
`σ` with `σ(j(E)) = j(E)`** ([AbsTopIII] Thm 1.9 for `X = E ∖ {O}`, `exists_conj_of_aut`). -/
theorem exists_conj_hemi (hS : BelyiCuspSpec Ω (hypCurveE E) hc.out)
    (σ₀ : Spec (CommRingCat.of K) ⟶ (hypCurveE E).Xbar)
    (hσ₀ : σ₀ ≫ ((hypCurveE E).Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hDGC : RelIsomDGC.Exists K) (β : PiCG E ≃ₜ* PiCG E)
    (hβ : ∀ y, piConstC (hemiData E) (β y) = 1 ↔ piConstC (hemiData E) y = 1)
    (hβX : ∀ y, β y ∈ (orbiIncl (hemiData E)).toMonoidHom.range ↔
      y ∈ (orbiIncl (hemiData E)).toMonoidHom.range) :
    ∃ σ : kbar K (FFClosure (curveE E)) ≃+* kbar K (FFClosure (curveE E)),
      σ (algebraMap K (kbar K (FFClosure (curveE E))) E.j) =
        algebraMap K (kbar K (FFClosure (curveE E))) E.j ∧
      ∀ (y : PiCG E) (z : kbar K (FFClosure (curveE E))),
        piConstC (hemiData E) (β y) z = σ (piConstC (hemiData E) y (σ.symm z)) := by
  let αX := restrictAutOfRange (orbiIncl (hemiData E))
    (isOpenEmbedding_orbiIncl (hemiData E)).isEmbedding β hβX
  have hαX : ∀ p, orbiIncl (hemiData E) (αX p) = β (orbiIncl (hemiData E) p) :=
    restrictAutOfRange_spec _ _ β hβX
  have hαX1 : ∀ p : Pi (curveGaloisData K (transcendental_xN E)),
      piToGk (curveGaloisData K (transcendental_xN E)) (αX p) = 1 ↔
        piToGk (curveGaloisData K (transcendental_xN E)) p = 1 := fun p => by
    rw [← piConstC_orbiIncl, ← piConstC_orbiIncl, hαX]
    exact hβ _
  obtain ⟨σ, hσj, hσ⟩ := exists_conj_of_aut E hS σ₀ hσ₀ hDGC αX hαX1
  refine ⟨σ, hσj, fun y z => ?_⟩
  obtain ⟨p, hp⟩ := piToGk_surjective_curve (C := hypCurveE E) (transcendental_xN E)
    (piConstC (hemiData E) y)
  have hk : piConstC (hemiData E) ((orbiIncl (hemiData E) p)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, piConstC_orbiIncl, hp, inv_mul_cancel]
  have hβk := (hβ _).2 hk
  have hy : y = orbiIncl (hemiData E) p * ((orbiIncl (hemiData E) p)⁻¹ * y) := by group
  have hβy : piConstC (hemiData E) (β y) =
      piToGk (curveGaloisData K (transcendental_xN E)) (αX p) := by
    rw [hy, map_mul, map_mul, hβk, mul_one, ← hαX, piConstC_orbiIncl]
  rw [hβy]
  refine (hσ p z).trans ?_
  rw [hp]

end Hemi

/-! ### `π₁(C_K)` -/

variable (D : InitialThetaData.{0})

/-- `E_K = E_F ×_F K`. -/
abbrev EK : WeierstrassCurve D.Kt := D.E.map (algebraMap D.F D.Kt)

/-- `π₁(C_K) ≃ₜ* Π_C` (Galois model of `C_K = (E_K ∖ {O}) / ±1`). -/
def bCK : piCK D ≃ₜ* PiCG (EK D) :=
  (genuinePi1EqEquiv (CK_eq D)).trans (genuinePi1HemiEquiv (EK D))

/-- **`π₁(C_K) ↠ Gal(k̄ / K)`**, the restriction to the field of constants. -/
def resK : piCK D →* Gk D.Kt (FFClosure (curveE (EK D))) :=
  (piConstC (hemiData (EK D))).comp (bCK D).toMulEquiv.toMonoidHom

lemma resK_apply (x : piCK D) : resK D x = piConstC (hemiData (EK D)) (bCK D x) := rfl

/-- The ring isomorphism `ψ : K(E_K)^alg ≃ F_mod(Ē_mod)^alg` inducing `π₁(C_K) ↪ π₁(C_{F_mod})`
on the field of constants (`exists_piCK_emb`). -/
def psiK : Genuine.Ω (EK D) ≃+* FFClosure (curveE (curveMod D.E)) :=
  Exists.choose (piCKToCmod_constCompat D)

lemma psiK_algebraMap (c : D.Kt) :
    psiK D (algebraMap D.Kt (Genuine.Ω (EK D)) c) =
      ((embConst (curveMod D.E) c : constFmod D) : FFClosure (curveE (curveMod D.E))) :=
  (Exists.choose_spec (piCKToCmod_constCompat D)).1 c

lemma psiK_spec (σ : Genuine.Gal (EK D)) (z : constFmod D) :
    ((piConstC (hemiData (curveMod D.E)) (genuinePi1HemiEquiv (curveMod D.E)
      (piCKToCmod D ((genuinePi1EqEquiv (CK_eq D)).symm (mkC _ σ)))) z : constFmod D) :
        FFClosure (curveE (curveMod D.E))) = psiK D (σ ((psiK D).symm z)) :=
  (Exists.choose_spec (piCKToCmod_constCompat D)).2 σ z

/-- A ring isomorphism restricts to the algebraic numbers. -/
def qbarRestrict {Ω₁ Ω₂ : Type*} [Field Ω₁] [Field Ω₂] [CharZero Ω₁] [CharZero Ω₂]
    (φ : Ω₁ ≃+* Ω₂) : algebraicClosure ℚ Ω₁ ≃+* algebraicClosure ℚ Ω₂ where
  toFun z := ⟨φ z.1, mem_algebraicClosure_iff.2
    ((mem_algebraicClosure_iff.1 z.2).algHom (φ : Ω₁ →+* Ω₂).toRatAlgHom)⟩
  invFun z := ⟨φ.symm z.1, mem_algebraicClosure_iff.2
    ((mem_algebraicClosure_iff.1 z.2).algHom (φ.symm : Ω₂ →+* Ω₁).toRatAlgHom)⟩
  left_inv z := Subtype.ext (φ.symm_apply_apply z.1)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.1)
  map_mul' a b := Subtype.ext (map_mul φ a.1 b.1)
  map_add' a b := Subtype.ext (map_add φ a.1 b.1)

/-- `ψ ∘ (hemiOmegaEquiv)⁻¹ : K(Ē_K)^alg ≃ F_mod(Ē_mod)^alg`. -/
def psiK' : FFClosure (curveE (EK D)) ≃+* FFClosure (curveE (curveMod D.E)) :=
  (hemiOmegaEquiv (EK D)).symm.trans (psiK D)

/-- The algebraic numbers of `F_mod(Ē_mod)^alg` are its algebraic closure of `F_mod`. -/
def qbarConstFmod : algebraicClosure ℚ (FFClosure (curveE (curveMod D.E))) ≃+* constFmod D where
  toFun c := ⟨c.1, mem_kbar_of_isAlgebraic (mem_algebraicClosure_iff.1 c.2)⟩
  invFun c := ⟨c.1, mem_algebraicClosure_iff.2 (isAlgebraic_of_mem_kbar c.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`ι : k̄ ≃ F̄`** (`k̄ ⊆ K(Ē_K)^alg`), through `ψ` and `F̄ = constFmod D`. -/
def iotaK : kbar D.Kt (FFClosure (curveE (EK D))) ≃+* D.Fbar :=
  (kbarQbar D.Kt (FFClosure (curveE (EK D)))).trans ((qbarRestrict (psiK' D)).trans
    ((qbarConstFmod D).trans (constFmodEquiv D).toRingEquiv))

lemma iotaK_apply (w : kbar D.Kt (FFClosure (curveE (EK D)))) :
    iotaK D w = constFmodEquiv D (qbarConstFmod D (qbarRestrict (psiK' D)
      (kbarQbar D.Kt (FFClosure (curveE (EK D))) w))) :=
  rfl

lemma coe_symm_iotaK (w : kbar D.Kt (FFClosure (curveE (EK D)))) :
    (((constFmodEquiv D).symm (iotaK D w) : constFmod D) : FFClosure (curveE (curveMod D.E))) =
      psiK' D w := by
  rw [iotaK_apply, AlgEquiv.symm_apply_apply]
  rfl

lemma iotaK_eq (w : kbar D.Kt (FFClosure (curveE (EK D)))) (v : constFmod D)
    (h : (v : FFClosure (curveE (curveMod D.E))) = psiK' D w) :
    iotaK D w = constFmodEquiv D v := by
  rw [iotaK_apply]
  congr 1
  exact Subtype.ext h.symm

/-- `galConstEquiv` unfolded. -/
lemma galConstEquiv_apply (g : constFmod D ≃ₐ[Fmod D] constFmod D) (y : D.Fbar) :
    galConstEquiv D g y = constFmodEquiv D (g ((constFmodEquiv D).symm y)) :=
  rfl

lemma resK_mkC (σ : Genuine.Gal (EK D)) (w : kbar D.Kt (FFClosure (curveE (EK D)))) :
    ((resK D ((genuinePi1EqEquiv (CK_eq D)).symm (mkC _ σ)) w :
      kbar D.Kt (FFClosure (curveE (EK D)))) : FFClosure (curveE (EK D))) =
      hemiOmegaEquiv (EK D) (σ ((hemiOmegaEquiv (EK D)).symm w)) := by
  rw [resK_apply, bCK, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 1000000 in
-- `piCmodPr` and `piCKToCmod` live over `Fmod D` with large instance terms
/-- **`π₁(C_K) ↪ π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)` is `resK` conjugated by `ι`**:
`ρ(x) ∘ ι = ι ∘ resK(x)`. -/
theorem iotaK_resK (x : piCK D) (w : kbar D.Kt (FFClosure (curveE (EK D)))) :
    iotaK D (resK D x w) = piCmodPr D (piCKToCmod D x) (iotaK D w) := by
  obtain ⟨x', rfl⟩ := (genuinePi1EqEquiv (CK_eq D)).symm.surjective x
  obtain ⟨σ, rfl⟩ := mkC_surjective (EK D) x'
  rw [piCmodPr_apply, galConstEquiv_apply]
  refine iotaK_eq D _ _ ?_
  rw [psiK_spec, coe_symm_iotaK, psiK', RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    resK_mkC]
  simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

/-- `ρ(x) = 1 ↔ resK(x) = 1`. -/
lemma piCmodPr_eq_one_iff (x : piCK D) :
    piCmodPr D (piCKToCmod D x) = 1 ↔ resK D x = 1 := by
  constructor
  · intro h
    refine AlgEquiv.ext fun w => (iotaK D).injective ?_
    rw [iotaK_resK, h]
    rfl
  · intro h
    refine AlgEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := (iotaK D).surjective w
    rw [← iotaK_resK, h]
    rfl

/-- `ι` on `K ⊆ k̄` is the `F_mod`-embedding `embConst`. -/
lemma iotaK_algebraMap (c : D.Kt) :
    iotaK D (algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) c) =
      constFmodEquiv D (embConst (curveMod D.E) c) := by
  refine iotaK_eq D _ _ ?_
  rw [psiK', RingEquiv.trans_apply]
  change _ = psiK D ((hemiOmegaEquiv (EK D)).symm
    (algebraMap D.Kt (FFClosure (curveE (EK D))) c))
  rw [← hemiOmegaEquiv_algebraMap_K, RingEquiv.symm_apply_apply, psiK_algebraMap]

/-- `ι` is `F_mod`-linear. -/
lemma iotaK_algebraMap_Fmod (a : Fmod D) :
    iotaK D (algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D))))
      (algebraMap (Fmod D) D.Kt a)) = algebraMap (Fmod D) D.Fbar a := by
  rw [iotaK_algebraMap, AlgHom.commutes, AlgEquiv.commutes]

/-- A field automorphism of `k̄` fixing `j(E_K)` fixes `F_mod = ℚ(j)`. -/
lemma fix_Fmod_of_fix_j (σ : kbar D.Kt (FFClosure (curveE (EK D))) ≃+*
      kbar D.Kt (FFClosure (curveE (EK D))))
    (hσ : σ (algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) (EK D).j) =
      algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) (EK D).j) (a : Fmod D) :
    σ (algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) (algebraMap (Fmod D) D.Kt a)) =
      algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) (algebraMap (Fmod D) D.Kt a) := by
  let φ : D.F →+* kbar D.Kt (FFClosure (curveE (EK D))) :=
    (algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D))))).comp (algebraMap D.F D.Kt)
  let T : IntermediateField ℚ D.F :=
    ((RingHom.eqLocusField (σ.toRingHom.comp φ) φ)).toIntermediateField fun q => by
      change σ (φ (algebraMap ℚ D.F q)) = φ (algebraMap ℚ D.F q)
      rw [eq_ratCast (algebraMap ℚ D.F), map_ratCast, map_ratCast]
  have hj : D.E.j ∈ T := by
    change σ (φ D.E.j) = φ D.E.j
    have e : φ D.E.j = algebraMap D.Kt (kbar D.Kt (FFClosure (curveE (EK D)))) (EK D).j := by
      rw [WeierstrassCurve.map_j]
      rfl
    rw [e]
    exact hσ
  have hle : fieldOfModuli D.F D.E ≤ T := IntermediateField.adjoin_simple_le_iff.2 hj
  exact hle a.2

/-- `E_K[ℓ]` is `K`-rational (IUT I, Def. 3.1 (c); `AdmissiblePrimeData.card_TK`). -/
lemma torsionCardN_EK : TorsionCardN (EK D) D.prime.ℓ := by
  classical
  unfold TorsionCardN
  convert D.prime.card_TK using 3

instance : NeZero D.prime.ℓ := ⟨D.prime.ℓ_prime.ne_zero⟩

lemma odd_ell : Odd D.prime.ℓ :=
  D.prime.ℓ_prime.odd_of_ne_two (by have := D.prime.five_le; omega)

lemma ell_ne_one : D.prime.ℓ ≠ 1 := D.prime.ℓ_prime.ne_one

/-- A `K`-rational point of `Ē_K` (a nonzero `ℓ`-torsion point, `ℓ` odd). -/
lemma exists_section_EK :
    ∃ σ₀ : Spec (CommRingCat.of D.Kt) ⟶ (hypCurveE (EK D)).Xbar,
      σ₀ ≫ ((hypCurveE (EK D)).Xbar ↘ Spec (CommRingCat.of D.Kt)) =
        𝟙 (Spec (CommRingCat.of D.Kt)) := by
  -- the decidable equality used by `TorsionCardN`
  letI : DecidableEq D.Kt := fun a b => Classical.propDecidable (a = b)
  have hcard := torsionCardN_EK D
  unfold TorsionCardN at hcard
  have h : 1 < D.prime.ℓ ^ 2 := by
    have := D.prime.five_le
    nlinarith
  have h1 := lt_of_lt_of_eq h hcard.symm
  haveI := Nat.finite_of_card_ne_zero (ne_of_gt (lt_trans zero_lt_one h1))
  obtain ⟨⟨P, hP⟩, hP0⟩ := @exists_ne _ (Finite.one_lt_card_iff_nontrivial.1 h1) 0
  have hP0' : P ≠ 0 := fun h => hP0 (Subtype.ext h)
  have hℓ : D.prime.ℓ • P = 0 := WeierstrassCurve.Affine.mem_torsion_iff.1 hP
  refine exists_ratSection (EK D) hP0' fun h2 => hP0' ?_
  obtain ⟨m, hm⟩ := odd_ell D
  have h3 : (2 * m + 1) • P = 0 := by
    rw [← hm]
    exact hℓ
  rwa [add_smul, one_smul, mul_comm, mul_smul, h2, smul_zero, zero_add] at h3

instance factEK : Fact ((hypCurveE (EK D)).U : Set (hypCurveE (EK D)).Xbar)ᶜ.Nonempty :=
  ⟨compl_XE_nonempty (EK D)⟩

set_option maxHeartbeats 3000000 in
-- `π₁(C_K)`, its Galois model and `Gal(F̄/F_mod)` are compared at heavy instance terms
/-- **`CKSemiAbsConj`** ([AbsTopIII] Thm 1.9, functoriality, for `X_K = E_K ∖ {O}`): a continuous
automorphism `α` of `π₁(C_K)` preserving `Δ_{C_K}` preserves `π₁(X_K)` (the `ℓ`-torsion condition,
`mem_range_orbiIncl_iff_of_aut`), acts on `Gal(k̄ / K)` as conjugation by `σ` with `σ(j) = j`
(`exists_conj_hemi`), and `ι σ ι⁻¹ ∈ Gal(F̄/F_mod)` conjugates its image in `Gal(F̄/F_mod)`
(`iotaK_resK`). Inputs: `BelyiCuspSpec` (MR8) and `RelIsomDGC.Exists` (MR7) for `E_K`. -/
theorem ckSemiAbsConj
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : RelIsomDGC.Exists D.Kt) : CKSemiAbsConj D := by
  intro α hα
  let β : PiCG (EK D) ≃ₜ* PiCG (EK D) := (bCK D).symm.trans (α.trans (bCK D))
  have hβb : ∀ x, β (bCK D x) = bCK D (α x) := fun x => by
    change bCK D (α ((bCK D).symm (bCK D x))) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
  have hβ : ∀ y, piConstC (hemiData (EK D)) (β y) = 1 ↔ piConstC (hemiData (EK D)) y = 1 :=
    fun y => by
      obtain ⟨x, rfl⟩ := (bCK D).surjective y
      rw [hβb, ← resK_apply, ← resK_apply, ← piCmodPr_eq_one_iff, ← piCmodPr_eq_one_iff]
      exact hα x
  have hβX := mem_range_orbiIncl_iff_of_aut (EK D) (torsionCardN_EK D) (ell_ne_one D)
    (odd_ell D) β hβ
  obtain ⟨σ₀, hσ₀⟩ := exists_section_EK D
  obtain ⟨σ, hσj, hσ⟩ := exists_conj_hemi (EK D) (Ω := AlgebraicClosure D.Kt) hS σ₀ hσ₀ hDGC β
    hβ hβX
  let gR : D.Fbar ≃+* D.Fbar := ((iotaK D).symm.trans σ).trans (iotaK D)
  have hgR : ∀ v, gR (iotaK D v) = iotaK D (σ v) := fun v => by
    change iotaK D (σ ((iotaK D).symm (iotaK D v))) = _
    rw [RingEquiv.symm_apply_apply]
  let g : GalG (Fmod D) D.Fbar := AlgEquiv.ofRingEquiv (f := gR) fun a => by
    rw [← iotaK_algebraMap_Fmod, hgR, fix_Fmod_of_fix_j D σ hσj]
  refine ⟨g, fun x => AlgEquiv.ext fun w => ?_⟩
  obtain ⟨v, rfl⟩ := (iotaK D).surjective w
  have hginv : g⁻¹ (iotaK D v) = iotaK D (σ.symm v) := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    change iotaK D v = gR (iotaK D (σ.symm v))
    rw [hgR, RingEquiv.apply_symm_apply]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hginv, ← iotaK_resK, ← iotaK_resK]
  change iotaK D (resK D (α x) v) = gR (iotaK D (resK D x (σ.symm v)))
  rw [hgR, resK_apply, ← hβb, hσ, ← resK_apply]

/-- **`hAbs` of `DStarDescent` discharged**: every continuous automorphism of `π₁(C_K)` acts on the
image of `π₁(C_K)` in `Gal(F̄/F_mod)` by conjugation by an element of `Gal(F̄/F_mod)` (`hAbs_of`,
`ckStrictSemiAbs`, `ckSemiAbsConj`). Inputs: `hEl` (`Gal(F̄/F_mod)` is very elastic, [AbsTopI]
Thm. 1.7 (iii)), `BelyiCuspSpec` (MR8), `RelIsomDGC.Exists` (MR7). -/
theorem hAbs_of_strict (hEl : Elastic.IsVeryElastic (GalG (Fmod D) D.Fbar))
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : RelIsomDGC.Exists D.Kt) (α : piCK D ≃ₜ* piCK D) :
    ∃ g : GalG (Fmod D) D.Fbar, ∀ x,
      piCmodPr D (piCKToCmod D (α x)) = g * piCmodPr D (piCKToCmod D x) * g⁻¹ :=
  hAbs_of D (ckStrictSemiAbs D hEl) (ckSemiAbsConj D hS hDGC) α

/-- **`π₁(C_{F_mod}) ≅ Aut(π₁(C_K))`** (`piCmodAutEquiv`, IUT I, Example 5.1 (i)) with `hAbs`
discharged by `hAbs_of_strict`. Inputs: `hEl` (`Gal(F̄/F_mod)` very elastic, [AbsTopI] Thm. 1.7
(iii)), `BelyiCuspSpec` (MR8), `RelIsomDGC.Exists` (MR7). -/
def piCmodAutEquivOfStrict (hEl : Elastic.IsVeryElastic (GalG (Fmod D) D.Fbar))
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) :
    piCmod D ≃* contAut (piCK D) :=
  piCmodAutEquiv D hDGC hj (hAbs_of_strict D hEl hS (hDGC D.Kt))

end HodgeTheater

end Iut
