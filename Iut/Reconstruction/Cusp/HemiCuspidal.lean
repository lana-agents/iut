/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.Elliptic
import CurvesJacobian.Cusp.HemiPuncturedArith
import CurvesJacobian.Cusp.HemiTwistArith
import CurvesJacobian.Cusp.Cor37b

/-!
# [AbsTopII] Cor. 3.3 (iii) for the hemi-elliptic orbicurve `X = C_{F_mod}` (MR8)

IUT I, Def. 3.1 (b) and Rem. 3.1.7 (i) apply [AbsTopII] Cor. 3.3 (iii) with base the
hemi-elliptic orbicurve `C_{F_mod} = [(E ∖ {O}) / ±1]` over `F_mod = ℚ(j)`, the open
sub-orbicurve `U_X = [(E ∖ E[N]) / ±1]` and `V = X_M = (E ∖ {O})_M` for a finite Galois extension
`M` of `F_mod`. Here we instantiate the group-theoretic step (b)
(`Iut.Reconstruction.cuspidalizationEquiv'`) with curves-jacobian's Galois-form fundamental
groups (`Π = H ⧸ ⟨⟨S⟩⟩`, SGA 1 V.8.2):

* `Π_{U_X}` of `hemiDataN E N`, `Π_C` of `hemiData E`, the filling `π = hemiFillN : Π_{U_X} ↠ Π_C`
  and `Π_V ⊴ Π_C` the image of `Π_{X_M}` (`hemiPiV`, `range_infInclC₃_normal`);
* **`fibreSubgroup_hemiFillN`**: the fibre `π⁻¹(Π_V)` is the image of
  `Π_{U_V} = Π_{(E ∖ E[N])_M}` (`comap_hemiFillN_range`);
* **`center_fibreSubgroup_hemiFillN`**: `π⁻¹(Π_V)` is centre-free: `Π_{U_V}` is cj's arithmetic
  fundamental group of the hyperbolic curve `(E ∖ E[N])_M` over the number field `M`
  (`hemiNMPiXGal`), which is centre-free because `G_M` and `Δ` are slim
  (`CuspidalExt.center_eq_bot_of_isOpen`);
* **`hemiCuspidalizationEquiv`**: `Π_{U_X} ≃* Π_{U_V} ⋊^out (Π_C / Π_V)`, compatibly with the
  projections to `Π_C / Π_V` (`hemiCuspidalizationEquiv_apply`);
* **`hemiFibreArithEquiv`**, **`hemi_fibre_fill_arith`**: `π⁻¹(Π_V)` is the arithmetic `π₁` of
  `(E ∖ E[N])_M`, and under this identification `π` restricted to `π⁻¹(Π_V)` is cj's scheme
  filling `fillPiHom` of `(E ∖ E[N])_M ⊆ (E ∖ {O})_M` followed by `Π_{X_M} ↪ Π_C`, up to an inner
  automorphism of `Π_{X_M}` (`hemiNM_fillPiHom_conj`);
* **`hemi_cor33iii_Fmod`**: the base `C_{F_mod}`. For a number field `K` (`= F_mod`) and an
  elliptic curve `E'` over `K` with `j(E') ∉ {0, 1728}` (e.g. `WeierstrassCurve.ofJ j`,
  `exists_model_of_j`), its hemi-elliptic orbicurve `C` does not see quadratic twists: for every
  elliptic curve `E` over `M` with `j(E) = j(E')` (e.g. IUT's `E_F`, with `F` realised as
  `M ⊆ K̄`), cj's arithmetic `π₁` of `E ∖ {O}` is an open subgroup of `Π_C` of
  index `2 · [M : K]` over `Gal(K̄ / K)` (`hemiTw_exists_arith_emb`), and the cuspidalisation of
  `C` along `U_X = [(E' ∖ E'[N]) / ±1]` holds with centre-free `Π_{U_V}`.

No hypotheses beyond the data (no DGC input): step (a) of Cor. 3.3 (iii) (`Π_{U_X} ↠ Π_C` from
chains) is here the explicit Galois-form filling.
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology Polynomial

noncomputable section

namespace Iut.Reconstruction.HemiCusp

universe u

section Generic

variable {G H : Type*} [Group G] [Group H]

theorem eq_one_of_commute_of_center_eq_bot (hG : Subgroup.center G = ⊥) {y : G}
    (hy : ∀ w, w * y = y * w) : y = 1 := by
  have h : y ∈ Subgroup.center G := Subgroup.mem_center_iff.2 hy
  rwa [hG, Subgroup.mem_bot] at h

/-- A group whose subgroup `⊤` is centre-free is centre-free. -/
theorem center_eq_bot_of_center_top (h : Subgroup.center (⊤ : Subgroup G) = ⊥) :
    Subgroup.center G = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hz' : (⟨z, trivial⟩ : (⊤ : Subgroup G)) ∈ Subgroup.center (⊤ : Subgroup G) :=
    Subgroup.mem_center_iff.2 fun w => Subtype.ext (Subgroup.mem_center_iff.1 hz w)
  rw [h, Subgroup.mem_bot] at hz'
  exact congrArg Subtype.val hz'

/-- Centre-freeness is invariant under isomorphisms. -/
theorem center_eq_bot_of_mulEquiv (e : G ≃* H) (hH : Subgroup.center H = ⊥) :
    Subgroup.center G = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => e.injective ?_
  rw [map_one]
  refine eq_one_of_commute_of_center_eq_bot hH fun w => ?_
  obtain ⟨w, rfl⟩ := e.surjective w
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]

/-- The image of an injective homomorphism from a centre-free group is centre-free. -/
theorem center_range_eq_bot (ι : G →* H) (hι : Function.Injective ι)
    (hG : Subgroup.center G = ⊥) : Subgroup.center ι.range = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨y, hy⟩ := z.2
  have h1 : y = 1 := eq_one_of_commute_of_center_eq_bot hG fun w => hι (by
    rw [map_mul, map_mul, hy]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨ι w, w, rfl⟩))
  exact Subtype.ext (by rw [← hy, h1, map_one]; rfl)

end Generic

section Hemi

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (N : ℕ) [NeZero N] (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E))))
  [FiniteDimensional K M] [IsGalois K M]

/-- `Π_{U_X}` for `U_X = [(E ∖ E[N]) / ±1]` (Galois form). -/
abbrev hemiPiUX : Type u :=
  GaloisPi1.pi1 (hemiDataN E N).H (hemiDataN E N).S (hemiDataN E N).isClosed_H

/-- `Π_C` for the hemi-elliptic orbicurve `C = [(E ∖ {O}) / ±1]` (Galois form). -/
abbrev hemiPiC : Type u :=
  GaloisPi1.pi1 (hemiData E).H (hemiData E).S (hemiData E).isClosed_H

/-- The filling `π : Π_{U_X} ↠ Π_C`. -/
abbrev hemiFillHom : hemiPiUX E N →* hemiPiC E := (hemiFillN E N).toMonoidHom

/-- `Π_V ⊆ Π_C`, the image of `Π_{X_M}` for `X_M = (E ∖ {O})_M`. -/
def hemiPiV : Subgroup (hemiPiC E) :=
  (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)).toMonoidHom.range

instance hemiPiV_normal : (hemiPiV E M).Normal :=
  range_infInclC₃_normal (S_subset_constFixer₃ (hemiData E) M)

/-- **The fibre `π⁻¹(Π_V)` is `Π_{U_V}`** for `U_V = (E ∖ E[N])_M`. -/
theorem fibreSubgroup_hemiFillN : fibreSubgroup (hemiFillHom E N) (hemiPiV E M) =
    (infInclC₃ (hemiDataN E N) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)).toMonoidHom.range :=
  comap_hemiFillN_range E N M

/-- **`Π_{U_V}` is centre-free** (cj's arithmetic `π₁` of the hyperbolic curve `(E ∖ E[N])_M`
over the number field `M`, `hemiNMPiXGal`; slimness of `G_M` and of `Δ`). -/
theorem center_hemiPiUV : Subgroup.center (GaloisPi1.pi1 (hemiDataNM E N M).HL
    (hemiDataNM E N M).S (hemiDataNM E N M).isClosed_HL) = ⊥ :=
  center_eq_bot_of_mulEquiv (hemiNMPiXGal E N M (AlgebraicClosure M)).symm.toMulEquiv
    (center_eq_bot_of_center_top (CuspidalExt.center_eq_bot_of_isOpen _
      (by rw [Subgroup.coe_top]; exact isOpen_univ)))

/-- **`π⁻¹(Π_V)` is centre-free.** -/
theorem center_fibreSubgroup_hemiFillN :
    Subgroup.center (fibreSubgroup (hemiFillHom E N) (hemiPiV E M)) = ⊥ := by
  rw [fibreSubgroup_hemiFillN]
  exact center_range_eq_bot _ (isOpenEmbedding_infInclC₃ (S_subset_constFixer₃ _ M)).injective
    (center_hemiPiUV E N M)

/-- **[AbsTopII] Cor. 3.3 (iii) (b) for `X = C`**: `Π_{U_X} ≃* Π_{U_V} ⋊^out (Π_C / Π_V)`,
with `Π_{U_V} = π⁻¹(Π_V)` (`fibreSubgroup_hemiFillN`) and the outer action of `Π_C / Π_V`
transported along `Π_{U_X} / Π_{U_V} ≃ Π_C / Π_V`. -/
def hemiCuspidalizationEquiv :
    hemiPiUX E N ≃* outSemidirect (cuspOuterAction (π := hemiFillHom E N)
      (hemiFillN_surjective E N) (hemiPiV E M)) :=
  cuspidalizationEquiv' (hemiFillN_surjective E N) (hemiPiV E M)
    (center_fibreSubgroup_hemiFillN E N M)

theorem hemiCuspidalizationEquiv_apply (e : hemiPiUX E N) :
    (hemiCuspidalizationEquiv E N M e : MulAut (fibreSubgroup (hemiFillHom E N) (hemiPiV E M)) ×
      (hemiPiC E ⧸ hemiPiV E M)) =
      (MulAut.conjNormal e, QuotientGroup.mk (hemiFillN E N e)) :=
  cuspidalizationEquiv'_apply _ _ _ e

variable (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic M Ω']
  [CharZero Ω']

/-- **`π⁻¹(Π_V)` is the arithmetic `π₁` of `U_V = (E ∖ E[N])_M`** (cj's `arithmeticExt` of
`hypCurveVN (E.baseChange M) N`, base point in `Ω'`). -/
def hemiFibreArithEquiv :
    (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).Pi ≃*
      fibreSubgroup (hemiFillHom E N) (hemiPiV E M) :=
  (hemiNMPiXGal E N M Ω').toMulEquiv.trans
    ((MonoidHom.ofInjective (isOpenEmbedding_infInclC₃
      (S_subset_constFixer₃ (hemiDataN E N) M)).injective).trans
      (MulEquiv.subgroupCongr (fibreSubgroup_hemiFillN E N M).symm))

lemma hemiFibreArithEquiv_apply (γ : (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N)).Pi) :
    (hemiFibreArithEquiv E N M Ω' γ : hemiPiUX E N) =
      infInclC₃ (hemiDataN E N) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)
        (hemiNMPiXGal E N M Ω' γ) := rfl

/-- **The filling on `π⁻¹(Π_V)` is the scheme filling**: under `hemiFibreArithEquiv`,
`π : π⁻¹(Π_V) → Π_V ⊆ Π_C` is cj's `fillPiHom` of `(E ∖ E[N])_M ⊆ (E ∖ {O})_M`
(`hemiFillPiNM₃`), followed by `Π_{X_M} ≅ Π_V ↪ Π_C`, up to an inner automorphism of
`Π_{X_M}`. -/
theorem hemi_fibre_fill_arith :
    ∃ x : GaloisPi1.pi1 (hemiDataM E M).HL (hemiDataM E M).S (hemiDataM E M).isClosed_HL,
      ∀ γ, hemiFillN E N (hemiFibreArithEquiv E N M Ω' γ : hemiPiUX E N) =
        infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)
          (x⁻¹ * hemiMPiXGal E M Ω' (hemiFillPiNM₃ E N M Ω' γ) * x) := by
  obtain ⟨x, hx⟩ := hemiNM_fillPiHom_conj E N M Ω'
  refine ⟨x, fun γ => ?_⟩
  rw [hemiFibreArithEquiv_apply, hemiFillN_infInclC₃, hx γ]
  congr 1
  group

end Hemi

section Fmod

/-- **`F_mod`-models exist**: for `j` in a field `K` there is an elliptic curve over `K` with
`j`-invariant `j` (mathlib's `WeierstrassCurve.ofJ`). -/
theorem exists_model_of_j {K : Type u} [Field K] (j : K) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic), E'.j = j := by
  classical
  exact ⟨WeierstrassCurve.ofJ j, inferInstance, WeierstrassCurve.ofJ_j j⟩

variable {K : Type u} [Field K] [NumberField K] (E' : WeierstrassCurve K) [E'.IsElliptic]
  (N : ℕ) [NeZero N] (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E'))))
  [FiniteDimensional K M] [IsGalois K M]
  (E : WeierstrassCurve M) [E.IsElliptic]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- Unifying with the bundled statement `hemiTw_exists_arith_emb` unfolds its large types.
/-- **[AbsTopII] Cor. 3.3 (iii) with base `X = C_{F_mod}`** (IUT I, Def. 3.1 (b),
Rem. 3.1.7 (i)). Let `K` be a number field (`F_mod`), `E'` an elliptic curve over `K` with
`j(E') ∉ {0, 1728}` (e.g. `WeierstrassCurve.ofJ j`, `exists_model_of_j`), `C` its hemi-elliptic
orbicurve (`hemiData E'`), `M ⊆ K̄` finite Galois over `K` and `E` an elliptic curve over `M` with
`j(E) = j(E')`. Then

* (`C` is the orbicurve of `E`) cj's arithmetic `π₁` of `E ∖ {O}` over `M` is an open subgroup
  of `Π_C` of index `2 · [M : K]` (with `x' = u2 x_E + r`; the twist has the same inertia as `C`,
  and the embedding is compatible with the projections to `Gal(K̄ / K)`,
  `hemiTw_exists_arith_emb`);
* (cuspidalisation) for `U_X = [(E' ∖ E'[N]) / ±1]` and `V = X_M`, `π⁻¹(Π_V)` is the arithmetic
  `π₁` of `(E' ∖ E'[N])_M`, it is centre-free, and
  `Π_{U_X} ≃* π⁻¹(Π_V) ⋊^out (Π_C / Π_V)` (`hemiCuspidalizationEquiv`). -/
theorem hemi_cor33iii_Fmod (hj : E.j = algebraMap K M E'.j) (h0 : E'.j ≠ 0)
    (h1728 : E'.j ≠ 1728) :
    (∃ (u2 r : M) (hu2 : u2 ≠ 0)
      (hΨ : (E'.baseChange M).Ψ₂Sq.comp (C u2 * X + C r) = C (u2 ^ 3) * E.Ψ₂Sq),
      IsOpenEmbedding (hemiTwEmbC E' M E r hu2 (AlgebraicClosure M) hΨ) ∧
      (hemiTwEmbC E' M E r hu2 (AlgebraicClosure M) hΨ).toMonoidHom.range.index =
        2 * Module.finrank K M) ∧
    Subgroup.center (fibreSubgroup (hemiFillHom E' N) (hemiPiV E' M)) = ⊥ ∧
    Nonempty ((arithmeticExt (AlgebraicClosure M) (hypCurveVN (E'.baseChange M) N)
      (compl_VNE_nonempty (E'.baseChange M) N)).Pi ≃*
        fibreSubgroup (hemiFillHom E' N) (hemiPiV E' M)) ∧
    Nonempty (hemiPiUX E' N ≃* outSemidirect
      (cuspOuterAction (π := hemiFillHom E' N) (hemiFillN_surjective E' N) (hemiPiV E' M))) := by
  have hj' : E.j = (E'.baseChange M).j := by
    rw [hj]
    change _ = (E'.map (algebraMap K M)).j
    rw [WeierstrassCurve.map_j]
  have hE0 : E.j ≠ 0 := by
    rw [hj]; exact (_root_.map_ne_zero _).2 h0
  have hE1728 : E.j ≠ 1728 := by
    rw [hj]; intro h
    exact h1728 ((algebraMap K M).injective (by rw [h, map_ofNat]))
  obtain ⟨u2, r, hu2, hΨ, -, he, hi, -, -⟩ :=
    hemiTw_exists_arith_emb E' M E (AlgebraicClosure M) hj' hE0 hE1728
  exact ⟨⟨u2, r, hu2, hΨ, he, hi⟩, center_fibreSubgroup_hemiFillN E' N M,
    ⟨hemiFibreArithEquiv E' N M _⟩, ⟨hemiCuspidalizationEquiv E' N M⟩⟩

end Fmod

end Iut.Reconstruction.HemiCusp
