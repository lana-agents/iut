/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFPoints
import CurvesJacobian.Kummer.ClosedRestriction

/-!
# [AbsTopIII] Thm 1.9 (e): the evaluation data group-theoretically

[AbsTopIII] Thm 1.9 (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2179–2185) feeds the
subgroups `U_x = {f | f(x) = 1}` of the triple of Prop 1.3 into Uchida's algorithm. In
[AbsTopIII] they are read off from the Kummer classes via Prop 1.8: `s_x^* κ_U(f) = κ(f(x))`
(curves-jacobian `restrictClosed_kummerMapZHat`), and `κ` is injective over the finite
extension `k_x` of a torally Kummer-faithful field `k`. Here:

* **`restrictClosed_kummerMapZHat_eq_one_iff`**: for a closed point `x` of `U` (a place `A ⊇ k`
  of `Ω` with `t ∈ A`, `[k_x : k] < ∞`) and a unit `u` of `U`, `s_x^* κ_U(u) = 1` iff
  `u(x) = 1`, i.e. iff `v_A(u − 1) < 1` (`restrictClosed_kummerMapZHat_eq_one_iff_valuation`);
* **`mem_U_nfTriple_iff_restrictClosed`**: for an NF-point `W` of `Ω` which is a closed point of
  `U`, and an NF-rational function `f` which is a unit `u` of `U`, `f` lies in the subgroup `U_x`
  of the triple of `Z_NF` (`Thm19/NFPoints.lean`, `mem_U_nfTriple_iff`) iff `s_x^* κ_U(u) = 1`.
  So the evaluation data of (e) are determined by the Kummer classes and the decomposition groups.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

section Eval

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] [IsAlgClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)] (hHL : D.HL = D.H) (ht : t ∈ A)

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`s_x^* κ_U(u) = 1` iff `u(x) = 1`**, for a closed point `x` of `U` over a finite extension
`k_x` of a torally Kummer-faithful field `k`. -/
theorem restrictClosed_kummerMapZHat_eq_one_iff (htf : IsTorallyKummerFaithful k)
    [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)] (u : units D)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    restrictClosed D A hk hkres hHL ht (kummerMapZHat D u) = 1 ↔ residue A ⟨_, hu⟩ = 1 := by
  haveI := isAlgClosed_residueField A hk hkres
  haveI := isGalois_residueField A hk hkres
  haveI : IsGalois (Decomposition.pointField (F D) A hk hkres) (ResidueField A) :=
    IsGalois.tower_top_intermediateField _
  have hinj : Function.Injective
      (kummerZHat (Decomposition.pointField (F D) A hk hkres) (ResidueField A)) :=
    (kummerZHat_injective_iff _ _).2
      (Decomposition.isKummerFaithfulGm_pointField (F := F D) A hk hkres htf)
  rw [restrictClosed_kummerMapZHat D A hk hkres hHL ht u hu hu', ← map_one
    (kummerZHat (Decomposition.pointField (F D) A hk hkres) (ResidueField A)), hinj.eq_iff,
    Units.ext_iff, Units.val_one, Subtype.ext_iff, coe_unitValue]
  rfl

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
/-- `u(x) = 1` iff `v_A(u − 1) < 1`. -/
lemma residue_eq_one_iff_valuation (y : Ω) (hy : y ∈ A) :
    residue A ⟨y, hy⟩ = 1 ↔ A.valuation (y - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (residue A), ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **`s_x^* κ_U(u) = 1` iff `v_A(u − 1) < 1`.** -/
theorem restrictClosed_kummerMapZHat_eq_one_iff_valuation (htf : IsTorallyKummerFaithful k)
    [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)] (u : units D)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A) :
    restrictClosed D A hk hkres hHL ht (kummerMapZHat D u) = 1 ↔
      A.valuation ((((u : (F D)ˣ) : F D) : Ω) - 1) < 1 := by
  rw [restrictClosed_kummerMapZHat_eq_one_iff D A hk hkres hHL ht htf u hu hu',
    residue_eq_one_iff_valuation]

end Eval

section NF

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [IsAlgClosed Ω] (N : NFModel D)

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(W)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **The subgroups `U_x` of the triple of `Z_NF` from the Kummer classes**: for an NF-point `W`
of `Ω` which is a closed point of `U` (`t ∈ W`, `[k_x : k] < ∞`, `k` torally Kummer-faithful)
and an NF-rational function `f` which is a unit `u` of `U`, `f ∈ U_x` iff `s_x^* κ_U(u) = 1`. -/
theorem mem_U_nfTriple_iff_restrictClosed {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) [Algebra k (ResidueField W)]
    (hkres : ∀ c : k, residue W ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField W) c)
    [Algebra.IsIntegral k (ResidueField W)] (hHL : D.HL = D.H) (ht : t ∈ W)
    (htf : IsTorallyKummerFaithful k)
    [FiniteDimensional k (Decomposition.pointField (F D) W hk hkres)]
    (f : (fnf N)ˣ) (u : units D) (hfu : ((f : fnf N) : Ω) = (((u : (F D)ˣ) : F D) : Ω))
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ W) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    f ∈ (nfTriple N).U (nfPlace hk hW) ↔
      restrictClosed D W hk hkres hHL ht (kummerMapZHat D u) = 1 := by
  rw [mem_U_nfTriple_iff, restrictClosed_kummerMapZHat_eq_one_iff_valuation D W hk hkres hHL ht
    htf u hu hu', hfu]

end NF

end Iut.Reconstruction.Thm19

end
