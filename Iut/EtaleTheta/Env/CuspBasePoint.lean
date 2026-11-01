/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTemperedClass
import Iut.EtaleTheta.ThetaLevelKummer
import Iut.EtaleTheta.ThetaCuspTame
import EllipticCurves.FunctionField.ValuationAtInfinity
import EllipticCurves.FunctionField.PlaceAtInfinity
import TemperedFundamentalGroups.Tempered.GaloisSurjective

/-!
# Base points over the cusp of `X = E_q ∖ {O}` (MR15, Layer-B obligation 5)

The surjection `Π^tp_Y ↠ G_k` of [EtTh] §1 (the exact sequence `1 → Δ^tp_Y → Π^tp_Y → G_k → 1`)
holds in `tempered-fundamental-groups` (`Kummer.exists_mem_ker_character_piToGk_eq`) at a base
point `V` lying over a `k`-rational point, i.e. `V ≤ A` for a place `A ⊇ k` of `Ω` whose residues
on the function field `F` lie in `k` (a `RatPoint`). This file supplies such places for `X`
concretely: **the cusp `O` of `E_q` is a `K`-rational point**.

* `comap_embE_eq_ordInfty`: for a place `W ⊇ K` of `Ω` with `τ ∉ W` (`τ = x`), the place
  `W ∩ K(E)` is the place at infinity of `E` (`elliptic-curves`' `eq_ordInftyValuationSubring`);
* `hrat_cusp`, **`cuspRatPoint`**: such a `W` is a `K`-rational point of the Galois model `DX`
  of `X`: every function regular at infinity is an element of `K` plus a function vanishing there
  (`exists_const_ordInfty_sub_pos`, no hypothesis on `K`);
* `exists_cusp_place`, **`exists_basePoint_cusp`**: such places exist (Chevalley extension of the
  place at infinity along `K(E) ⊆ Ω`, tfg `ValuationSubring.exists_comap_eq`), and every place
  `W ⊇ K` is refined by a base point `V ≤ W` over any valuation subring `O` of `K`
  (tfg `ValuationSubring.exists_le_comap_eq`).

So the hypotheses "`V` lies under a place `W` over the cusp" of the theorems of
`Env/ThetaSystem.lean` and `Env/ThetaLTors.lean` are satisfiable, and under them `hsurj` holds
(`surj_augT_of_ratPoint`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K} [t.tateCurve.IsElliptic]

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **A place of `Ω` with `τ ∉ W` lies over the point at infinity of `E`**: `W ∩ K(E)` is the
place at infinity (`τ = x` has a pole there). -/
theorem comap_embE_eq_ordInfty {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W)
    (hτ : τ ∉ W) :
    W.comap (embE t.tateCurve).toRingHom = ordInftyValuationSubring t.tateCurve.toAffine := by
  refine eq_ordInftyValuationSubring (fun c => ?_) ?_
  · rw [ValuationSubring.mem_comap]
    change embE t.tateCurve (algebraMap K _ c) ∈ W
    rw [AlgHom.commutes]
    exact hk c
  · rw [ValuationSubring.mem_comap]
    change embE t.tateCurve (CoordinateRing.genX t.tateCurve.toAffine) ∉ W
    rw [embE_genX]
    exact hτ

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Every element of `F(DX) = K(E)` is the image of a function on `E`. -/
theorem exists_embE_eq (a : F (DX t)) : ∃ g, embE t.tateCurve g = (a : Ω) := by
  have haL : (a : Ω) ∈ (hemiData t.tateCurve).L :=
    mem_of_mem_F_fieldData (transcendental_tau t.tateCurve) _ (hemiL_open t) a
  refine ⟨funFieldEquivE t.tateCurve ((hemiEquivL t.tateCurve).symm ⟨a, haL⟩), ?_⟩
  have h1 : ((hemiEquivL t.tateCurve ((hemiEquivL t.tateCurve).symm ⟨a, haL⟩) :
      (hemiData t.tateCurve).L) : Ω) = a := by
    rw [RingEquiv.apply_symm_apply]
  refine Eq.trans ?_ h1
  rw [hemiEquivL_apply]
  change algebraMap _ Ω ((funFieldEquivE t.tateCurve).symm (funFieldEquivE t.tateCurve _)) = _
  rw [RingEquiv.symm_apply_apply]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Residues at a cusp place are rational**: for a place `W ⊇ K` of `Ω` with `τ ∉ W`, the
residue at `W` of every function of `F(DX)` regular at `W` lies in (the image of) `K`. -/
theorem hrat_cusp {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W) :
    letI := resAlg W hk
    ∀ (a : F (DX t)) (ha : (a : Ω) ∈ W),
      ∃ c : K, residue W ⟨_, ha⟩ = algebraMap K (ResidueField W) c := by
  letI := resAlg W hk
  intro a ha
  obtain ⟨g, hg⟩ := exists_embE_eq a
  have hcomap := comap_embE_eq_ordInfty hk hτ
  have hgO : g ∈ ordInftyValuationSubring t.tateCurve.toAffine := by
    rw [← hcomap, ValuationSubring.mem_comap]
    change embE t.tateCurve g ∈ W
    rw [hg]
    exact ha
  obtain ⟨c, hc⟩ := exists_const_ordInfty_sub_pos (mem_ordInftyValuationSubring.1 hgO)
  refine ⟨c, ?_⟩
  change residue W ⟨_, ha⟩ = residue W ⟨algebraMap K Ω c, hk c⟩
  rcases hc with hc | hc
  · congr 1
    apply Subtype.ext
    change (a : Ω) = algebraMap K Ω c
    rw [← hg, hc, AlgHom.commutes]
  · rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    set d := g - algebraMap K t.tateCurve.toAffine.FunctionField c with hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, ordInfty_zero] at hc
      exact lt_irrefl 0 hc
    have hdinv : d⁻¹ ∉ ordInftyValuationSubring t.tateCurve.toAffine := by
      rw [mem_ordInftyValuationSubring, ordInfty_inv]
      omega
    have himg : embE t.tateCurve d = (a : Ω) - algebraMap K Ω c := by
      rw [hd, map_sub, hg, AlgHom.commutes]
    have hne : embE t.tateCurve d ≠ 0 :=
      (map_ne_zero_iff _ (embE t.tateCurve).toRingHom.injective).2 hd0
    have hnot : (embE t.tateCurve d)⁻¹ ∉ W := by
      rw [← map_inv₀]
      intro h
      apply hdinv
      rw [← hcomap]
      exact h
    change W.valuation ((a : Ω) - algebraMap K Ω c) < 1
    rw [← himg]
    exact (valuation_lt_one_iff_inv_notMem W hne).2 hnot

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The cusp is a `K`-rational point of `X`**: a place `W ⊇ K` of `Ω` with `τ ∉ W`, as a
`RatPoint` of the Galois model `DX` (residues rational by `hrat_cusp`, hence `κ(W)` algebraic
over `K`). -/
def cuspRatPoint {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W) :
    RatPoint (DX t) where
  A := W
  hk := hk
  isIntegral := by
    letI := resAlg W hk
    haveI : Algebra.IsAlgebraic (F (DX t)) Ω := Algebra.IsAlgebraic.tower_top (K := K₀ K τ) _
    exact isIntegral_residueField_of_rational (E := F (DX t)) W (hrat_cusp hk hτ)
  hrat := hrat_cusp hk hτ

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem cuspRatPoint_A {W : ValuationSubring Ω} (hk : ∀ c : K, algebraMap K Ω c ∈ W)
    (hτ : τ ∉ W) : (cuspRatPoint hk hτ).A = W := rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Places over the cusp exist**: a Chevalley extension to `Ω` of the place at infinity of `E`
along `K(E) ⊆ Ω`. -/
theorem exists_cusp_place :
    ∃ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W := by
  letI : Algebra t.tateCurve.toAffine.FunctionField Ω := (embE t.tateCurve).toRingHom.toAlgebra
  obtain ⟨W, hW⟩ :=
    ValuationSubring.exists_comap_eq (ordInftyValuationSubring t.tateCurve.toAffine) (L := Ω)
  refine ⟨W, fun c => ?_, fun h => ?_⟩
  · have h1 : algebraMap K t.tateCurve.toAffine.FunctionField c ∈ W.comap (algebraMap _ Ω) :=
      hW ▸ algebraMap_mem_ordInftyValuationSubring c
    rw [ValuationSubring.mem_comap] at h1
    change embE t.tateCurve (algebraMap K _ c) ∈ W at h1
    rwa [AlgHom.commutes] at h1
  · apply genX_notMem_ordInftyValuationSubring (W := t.tateCurve.toAffine)
    rw [← hW, ValuationSubring.mem_comap]
    change embE t.tateCurve (CoordinateRing.genX t.tateCurve.toAffine) ∈ W
    rw [embE_genX]
    exact h

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Base points over the cusp exist**: for every valuation subring `O` of `K` there are a
place `W ⊇ K` of `Ω` over the cusp (`τ ∉ W`) and a base point `V ≤ W` with `V ∩ K = O`. -/
theorem exists_basePoint_cusp (O : ValuationSubring K) :
    ∃ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W ∧
      ∃ V : ValuationSubring Ω, V ≤ W ∧ V.comap (algebraMap K Ω) = O := by
  obtain ⟨W, hk, hτ⟩ := exists_cusp_place (t := t)
  letI := resAlg W hk
  exact ⟨W, hk, hτ, ValuationSubring.exists_le_comap_eq (A := W) (O := O) (hk := hk)
    (hkres := fun _ => rfl)⟩

end Iut.EtaleTheta.Env
