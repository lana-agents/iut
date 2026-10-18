/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.OrhdPsiMap

/-!
# Auxiliary facts for [FrdII], Theorem 2.4(ii) for `C_v`

* `ValAux.val_eq_one_of_rel`: a multiplicative correspondence between the monoids
  `{v ≥ 0}` of two discretely valued groups which is bijective (and functional) maps elements of
  valuation `1` to elements of valuation `1` (uniformisers are the irreducible elements);
* `PAdicGalois.norm_coe_eq_nrm`: the norm of `K̄` restricts to `PadicField.nrm` on finite
  subextensions; `ord_nonneg_iff`: `ord x ≥ 0 ↔ v(x) ≥ 0`;
* `PAdicGalois.ord_mem_gammaQ`: `ord(K̄^×) ⊆ ℚ` (so every element of `K̄^×` is a rational function
  of `C_v`);
* `ContH1Aux.cocycle_eq_one_of_mk_eq`, **`PAdicGalois.root_fixed`**: for an `(n, H)`-saturated
  `X = (G_E/N, a)` with `N ⊆ H`, every `n`-th root of an element of `L = K̄^H` is fixed by `N`
  (Definition 2.2(ii)(c): `H¹(H_A, μ_n) ≅ H¹(H, μ_n)`; [FrdII], Remark 2.2.1).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace ValAux

variable {M M' : Type*} [CommGroup M] [CommGroup M'] (v : M → ℤ) (v' : M' → ℤ)

lemma val_one (hv : ∀ x y, v (x * y) = v x + v y) : v 1 = 0 := by
  have := hv 1 1
  rw [mul_one] at this
  omega

lemma val_inv (hv : ∀ x y, v (x * y) = v x + v y) (x : M) : v x⁻¹ = -v x := by
  have := hv x x⁻¹
  rw [mul_inv_cancel, val_one v hv] at this
  omega

/-- **Valuation-one elements correspond** under a bijective multiplicative correspondence of the
monoids `{v ≥ 0}`, `{v' ≥ 0}`. -/
theorem val_eq_one_of_rel (hv : ∀ x y, v (x * y) = v x + v y)
    (hv' : ∀ x y, v' (x * y) = v' x + v' y) (R : M → M' → Prop) (hR1 : R 1 1)
    (hRmul : ∀ x x' y y', R x y → R x' y' → R (x * x') (y * y'))
    (hRfun : ∀ x y y', R x y → R x y' → y = y')
    (hRinj : ∀ x x' y, 0 ≤ v x → 0 ≤ v x' → R x y → R x' y → x = x')
    (hRtot : ∀ x, 0 ≤ v x → ∃ y, R x y)
    (hRsurj : ∀ y, 0 ≤ v' y → ∃ x, 0 ≤ v x ∧ R x y)
    (hRmem : ∀ x y, 0 ≤ v x → R x y → 0 ≤ v' y)
    {π' : M'} (hπ' : v' π' = 1) {π : M} (hπ : v π = 1) {y : M'} (hy : R π y) : v' y = 1 := by
  have v1 := val_one v hv
  have v1' := val_one v' hv'
  -- an element mapping to a unit is a unit
  have key : ∀ x, 0 ≤ v x → ∀ y, R x y → v' y = 0 → v x = 0 := by
    intro x hx y hxy hy0
    obtain ⟨z, hz, hzy⟩ := hRsurj y⁻¹ (by rw [val_inv v' hv', hy0]; omega)
    have h1 := hRmul _ _ _ _ hxy hzy
    rw [mul_inv_cancel] at h1
    have h2 := hRinj _ _ _ (by rw [hv]; omega) (by omega) h1 hR1
    have h3 := congrArg v h2
    rw [hv, v1] at h3
    omega
  -- a unit maps to a unit
  have key' : ∀ x, v x = 0 → ∀ y, R x y → v' y = 0 := by
    intro x hx y hxy
    obtain ⟨y₁, hy₁⟩ := hRtot x⁻¹ (by rw [val_inv v hv, hx]; omega)
    have h1 := hRmul _ _ _ _ hxy hy₁
    rw [mul_inv_cancel] at h1
    have h2 := congrArg v' (hRfun _ _ _ h1 hR1)
    rw [hv', v1'] at h2
    have := hRmem _ _ (by omega) hxy
    have := hRmem _ _ (by rw [val_inv v hv, hx]; omega) hy₁
    omega
  have hy0 : 0 ≤ v' y := hRmem _ _ (by omega) hy
  rcases lt_trichotomy (v' y) 1 with h | h | h
  · have := key π (by omega) y hy (by omega)
    omega
  · exact h
  · exfalso
    set w := y * π'⁻¹
    have hw : v' w = v' y - 1 := by rw [hv', val_inv v' hv', hπ']; ring
    obtain ⟨x₁, hx₁, h₁⟩ := hRsurj π' (by omega)
    obtain ⟨x₂, hx₂, h₂⟩ := hRsurj w (by omega)
    have h12 := hRmul _ _ _ _ h₁ h₂
    have e : π' * w = y := by
      change π' * (y * π'⁻¹) = y
      rw [mul_comm y, mul_inv_cancel_left]
    rw [e] at h12
    have hx := hRinj _ _ _ (by rw [hv]; omega) (by omega) h12 hy
    have hvx := congrArg v hx
    rw [hv, hπ] at hvx
    rcases (show v x₁ = 0 ∨ 0 < v x₁ by omega) with h0 | h0
    · have := key' x₁ h0 π' h₁
      omega
    · have h0' : v x₂ = 0 := by omega
      have := key' x₂ h0' w h₂
      omega

end ValAux

namespace ContH1Aux

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- Cohomologous cocycles agree at an element acting trivially. -/
theorem cocycle_eq_one_of_mk_eq (c d : ContH1.cocycles G M) (h : ContH1.mk c = ContH1.mk d)
    (k : G) (hk : ∀ m : M, k • m = m) (hc : (c : G → M) k = 1) : (d : G → M) k = 1 := by
  obtain ⟨x, hx⟩ := (ContH1.mk_eq_mk_iff c d).mp h
  have h1 : k • x / x = (c : G → M) k / (d : G → M) k := hx k
  rw [hk, div_self', hc, one_div, eq_comm, inv_eq_one] at h1
  exact h1

end ContH1Aux

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField PadicField

variable {p : ℕ} [hp : Fact p.Prime] {Γ : AddSubgroup ℝ}
variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

/-- `L^× → K̄^×`. -/
noncomputable abbrev ιL (L : IntermediateField E K̄) : Lˣ →* K̄ˣ :=
  Units.map (algebraMap L K̄ : L →* K̄)

lemma ιL_injective (L : IntermediateField E K̄) : Function.Injective (ιL L) := fun _ _ h =>
  Units.ext (Subtype.ext (congrArg Units.val h))

/-- An element of `K̄^×` fixed by `H` as a unit of `K̄^H`. -/
noncomputable def unitsOfFixed (H : Subgroup (GK p E)) (y : K̄ˣ) (hy : ∀ h ∈ H, h • y = y) :
    (fixL H)ˣ :=
  Units.mk0 ⟨(y : K̄), (mem_fixedField_iff H _).mpr fun h hh => congrArg Units.val (hy h hh)⟩
    (fun h0 => y.ne_zero (congrArg Subtype.val h0))

@[simp] lemma ιL_unitsOfFixed (H : Subgroup (GK p E)) (y : K̄ˣ) (hy : ∀ h ∈ H, h • y = y) :
    ιL (fixL H) (unitsOfFixed H y hy) = y := Units.ext rfl

lemma smul_ιL (H : Subgroup (GK p E)) (x : (fixL H)ˣ) {h : GK p E} (hh : h ∈ H) :
    h • ιL (fixL H) x = ιL (fixL H) x :=
  Units.ext ((mem_fixedField_iff H _).mp (x : fixL H).2 h hh)

/-- **The norm of `K̄` on a finite subextension is `PadicField.nrm`.** -/
lemma norm_coe_eq_nrm (L : IntermediateField E K̄) [FiniteDimensional ℚ_[p] L] (x : L) :
    ‖(x : K̄)‖ = nrm p L x := by
  rw [nrm_apply, spectralNorm.eq_of_tower (K := ℚ_[p]) (L := K̄) x]
  rfl

lemma ord_units (x : K̄ˣ) : ord p (Additive.ofMul x) = -Real.logb p ‖(x : K̄)‖ := rfl

/-- `ord x ≥ 0 ↔ v(x) ≥ 0` on a finite subextension. -/
lemma ord_nonneg_iff (L : IntermediateField E K̄) [FiniteDimensional ℚ_[p] L] (x : Lˣ) :
    0 ≤ ord p (Additive.ofMul (ιL L x)) ↔ 0 ≤ v p (x : L) := by
  rw [ord_units, neg_nonneg]
  change Real.logb p ‖((x : L) : K̄)‖ ≤ 0 ↔ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx0 : ((x : L) : K̄) ≠ 0 := fun h => x.ne_zero (Subtype.ext h)
  rw [Real.logb_nonpos_iff hp1 (norm_pos_iff.mpr hx0), norm_coe_eq_nrm,
    nrm_le_one_iff_v_nonneg x.ne_zero]

/-- **`ord(K̄^×) ⊆ ℚ`.** -/
lemma ord_mem_gammaQ (x : K̄ˣ) : ord p (Additive.ofMul x) ∈ gammaQ := by
  obtain ⟨m, hm⟩ := exists_nrm_pow_natDegree_eq (p := p) (K := K̄) x.ne_zero
  set d := (minpoly ℚ_[p] (x : K̄)).natDegree
  have hd : d ≠ 0 := (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := ℚ_[p])
    (x : K̄))).ne'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
  have hn : nrm p K̄ (x : K̄) = ‖(x : K̄)‖ := rfl
  have h1 := congrArg (Real.logb p) hm
  rw [Real.logb_pow, ← Real.rpow_intCast, Real.logb_rpow hp0 hp1, hn] at h1
  refine ⟨((m : ℚ) / d), ?_⟩
  change (algebraMap ℚ ℝ) ((m : ℚ) / d) = -Real.logb p ‖(x : K̄)‖
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [map_div₀, eq_ratCast, eq_ratCast, Rat.cast_intCast, Rat.cast_natCast]
  push_cast at h1
  field_simp
  linarith

variable (N : OpenNormalSubgroup (GK p E)) (a : Γ) (H : Subgroup (GK p E))
  (hH : IsOpen (H : Set (GK p E)))

lemma galHom_eq_one {ν : GK p E} (hν : ν ∈ N) : galHom N a ν = 1 :=
  Iso.ext (galAut_hom_eq_id N a (N.toSubgroup.inv_mem hν))

/-- `N` fixes `μ_n(K̄)` when `X` is `μ_n`-saturated. -/
lemma mu_fixed (n : ℕ) [NeZero n] (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n)))
    (ζ : KummerTheory.Mu n K̄) {ν : GK p E} (hν : ν ∈ N) :
    ν • KummerTheory.Mu.val ζ = KummerTheory.Mu.val ζ := by
  obtain ⟨m, rfl⟩ := (uMu_bijective N a n hs).2 ζ
  exact rfE_fixed (show Aut (XN N a) from
    ((m : Model.ouAut (XN N a)) : WithDisc (Aut (XN N a)))).hom hν

/-- `Gal(K̄/L)` contains `N` when `N ⊆ H`. -/
noncomputable def galOfN (hNH : N.toSubgroup ≤ H) (ν : N) : K̄ ≃ₐ[fixL H] K̄ :=
  (galFixMulEquiv H hH).symm ⟨ν, hNH ν.2⟩

lemma galOfN_apply (hNH : N.toSubgroup ≤ H) (ν : N) (y : K̄) :
    galOfN N H hH hNH ν y = (ν : GK p E) y := by
  have := coe_galFixMulEquiv H hH (galOfN N H hH hNH ν)
  rw [galOfN, MulEquiv.apply_symm_apply] at this
  rw [this]
  rfl

lemma galLA_galOfN (hNH : N.toSubgroup ≤ H) (ν : N) :
    galLA N a H hH (galOfN N H hH hNH ν) = 1 := by
  apply Subtype.ext
  change galHom N a ((galFixMulEquiv H hH (galOfN N H hH hNH ν) : H) : GK p E) = 1
  rw [galOfN, MulEquiv.apply_symm_apply]
  exact galHom_eq_one N a ν.2

lemma galOfN_smul_units (hNH : N.toSubgroup ≤ H) (ν : N) (y : K̄ˣ) :
    ((galOfN N H hH hNH ν • y : K̄ˣ) : K̄) = (ν : GK p E) (y : K̄) :=
  galOfN_apply N H hH hNH ν (y : K̄)

lemma galOfN_smul_mu (n : ℕ) [NeZero n] (hs : Nonempty (muX N a n ≃* Multiplicative (ZMod n)))
    (hNH : N.toSubgroup ≤ H) (ν : N) (m : KummerTheory.Mu n K̄) :
    galOfN N H hH hNH ν • m = m := by
  apply KummerTheory.Mu.ext
  rw [KummerTheory.Mu.val_smul]
  apply Units.ext
  rw [galOfN_smul_units]
  exact congrArg Units.val (mu_fixed N a n hs m ν.2)

include hH in
/-- **`n`-th roots of elements of `L = K̄^H` lie in `K̄^N`** for an `(n, H)`-saturated
`X = (G_E/N, a)` with `N ⊆ H`. -/
theorem root_fixed [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)
    (hNH : N.toSubgroup ≤ H) (π : (fixL H)ˣ) (g : K̄ˣ)
    (hg : g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) π) {ν : GK p E} (hν : ν ∈ N) :
    ν • g = g := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
  refine ((toL_bijective N a H hH n hs).2 (KummerTheory.kummer n (fixL H) K̄ π)).elim
    fun κ hκ => ?_
  induction κ using ContH1.induction_on with | h c => ?_
  have hκ' : ContH1.mk (ContH1.cocyclesMap (galLA N a H hH) (continuous_galLA N a H hH)
      (uMu N a n) continuous_of_discreteTopology (uMu_smul_L N a H hH n) c) =
      ContH1.mk (KummerTheory.kummerCocycle g (KummerTheory.smul_pow_of_pow_eq hg)) :=
    hκ.trans (KummerTheory.kummer_eq π g hg)
  have hfix : ∀ m : KummerTheory.Mu n K̄, galOfN N H hH hNH ⟨ν, hν⟩ • m = m :=
    galOfN_smul_mu N a H hH n hs.muSat hNH ⟨ν, hν⟩
  have hc1 : (c : subA N a H → muX N a n) (galLA N a H hH (galOfN N H hH hNH ⟨ν, hν⟩)) = 1 :=
    (congrArg (c : subA N a H → muX N a n) (galLA_galOfN N a H hH hNH ⟨ν, hν⟩)).trans
      (ContH1.map_one_eq c)
  have hc : (ContH1.cocyclesMap (galLA N a H hH) (continuous_galLA N a H hH)
      (uMu N a n) continuous_of_discreteTopology (uMu_smul_L N a H hH n) c :
        (K̄ ≃ₐ[fixL H] K̄) → KummerTheory.Mu n K̄) (galOfN N H hH hNH ⟨ν, hν⟩) = 1 := by
    rw [ContH1.cocyclesMap_apply, hc1, map_one]
  have hk := ContH1Aux.cocycle_eq_one_of_mk_eq _ _ hκ' _ hfix hc
  have h2 : ((galOfN N H hH hNH ⟨ν, hν⟩ • g : K̄ˣ) : K̄) / g = 1 := by
    rw [← Units.val_div_eq_div_val]
    exact congrArg (fun z => ((KummerTheory.Mu.val z : K̄ˣ) : K̄)) hk
  rw [div_eq_one_iff_eq g.ne_zero, galOfN_smul_units] at h2
  exact Units.ext h2

end PAdicGalois

end Frobenioid

end Iut
