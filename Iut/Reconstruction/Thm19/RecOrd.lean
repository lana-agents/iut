/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecFunctionField
import ContinuousKummerTheory.Curve.TameCharInjective

/-!
# [AbsTopIII] Thm 1.9 (b), (c): `ord_x` of the reconstructed triple is determined by residues

[AbsTopIII] Prop 1.4 (i) (`Topics in Absolute Anabelian Geometry III.txt` l.1764: "the inertia
group `I_x` of `x` in `Δ_U` is naturally isomorphic to `Ẑ(1)`") and Prop 1.6 (iii) (restriction
to the inertia groups records the divisor). `Thm19/RecFunctionField.lean` proves
`res_p(κ_V(v)) = θ_p^{ord_x(f)}` (`res_kummerMapZHat_eq_tameGen_zpow`). Here the exponent is shown
to be determined by the residue, so that `ord_x` of the reconstructed triple is read off from the
Kummer classes and one nontrivial element of the inertia group:

* `zHatOne_eq_one_of_pow_eq_one`, `zHatOne_zpow_injective`: `Ẑ(1)` is torsion-free
  (characteristic `0`);
* `tameGen_apply` (the `μ_n`-components of `θ_p`), `unif_valuation_lt_one`,
  `valuation_le_unif`, and **`tameGen_ne_one`**: for `σ ≠ 1` in `I_W ∩ H` the tame generator
  `θ_p` is nontrivial (continuous-kummer-theory `eq_one_of_forall_evalTriv_kummer_eq_one`, the
  injectivity of the tame character);
* **`val_recTriple_eq_iff`**: `ord_x(f) = n` iff `res_p(κ_V(v)) = θ_p^n`, for any inertia index
  `p = (W, σ)` of a stage `V` at `x` with `σ ≠ 1`;
* **`exists_stage_inertia`** (cofinality): for every `f` and every NF-point `x` there is a stage
  `V` on which `f` is a unit, of which `x` is a cusp, whose function field contains a uniformiser
  of `Z_NF` at `x`, with a nontrivial `σ ∈ I_W ∩ H_V`; hence **`val_recTriple_eq_iff_exists`**.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

section Torsion

variable {K Ω : Type*} [Field K] [Field Ω] [CharZero K]

/-- **`Ẑ(1)` is torsion-free** (characteristic `0`). -/
theorem zHatOne_eq_one_of_pow_eq_one {x : ZHatOne K Ω} {m : ℕ} (hm : m ≠ 0) (h : x ^ m = 1) :
    x = 1 := by
  apply Subtype.ext
  funext i
  have hj : ((i.n * m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (mul_ne_zero (NeZero.ne i.n) hm)
  set j : KummerIndex K := ⟨i.n * m, hj⟩
  have hij : i ≤ j := KummerIndex.le_def.2 (dvd_mul_right _ _)
  have hdiv : j.n / i.n = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne i.n))
  have h1 : (x : ∀ i, Mu i.n Ω) i = Mu.transition hij ((x : ∀ i, Mu i.n Ω) j) :=
    (x.2 i j hij).symm
  have h2 : ((x : ∀ i, Mu i.n Ω) j) ^ m = 1 :=
    congrArg (fun y : ZHatOne K Ω => (y : ∀ i, Mu i.n Ω) j) h
  have h3 : (x : ∀ i, Mu i.n Ω) i = 1 := by
    rw [h1]
    apply Mu.ext
    rw [Mu.val_transition, hdiv, ← map_pow, h2]
    rfl
  rw [h3]
  rfl

/-- Powers of a nontrivial element of `Ẑ(1)` are distinct. -/
theorem zHatOne_zpow_injective {x : ZHatOne K Ω} (hx : x ≠ 1) {a b : ℤ} (h : x ^ a = x ^ b) :
    a = b := by
  by_contra hab
  have h1 : x ^ (a - b) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have hne : (a - b).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 hab)
  rcases Int.natAbs_eq (a - b) with h2 | h2
  · rw [h2, zpow_natCast] at h1
    exact hx (zHatOne_eq_one_of_pow_eq_one hne h1)
  · rw [h2, zpow_neg, zpow_natCast, inv_eq_one] at h1
    exact hx (zHatOne_eq_one_of_pow_eq_one hne h1)

end Torsion

section Tame

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- The `μ_n`-components of the tame generator `θ_p`: the Kummer characters of the uniformiser
`unif p` on `σ`. -/
lemma tameGen_apply (p : InertiaIndex D) (i : KummerIndex (F D)) :
    ((tameGen p : ZHatOne (F D) Ω) : ∀ i, Mu i.n Ω) i =
      ContH1.evalTriv (p.1.2 : D.H) (inertia_smul_mu p.2.1 p.2.2 i.n)
        (resMu D i.n (kummer i.n (F D) Ω (unif p))) := by
  rw [tameGen, ← map_proj_res_kummerZHat i (unif p), ContH1.evalTriv_map]
  rfl

lemma ord_unif_eq_one (p : InertiaIndex D) (hne : idxVal p ≠ ⊤) :
    (idxPlace p hne).ord ((unif p : (F D)ˣ) : F D) = 1 := by
  rw [unif, dif_pos hne]
  exact (idxPlace p hne).exists_ord_eq_one.choose_spec

/-- The uniformiser `unif p` lies in the maximal ideal of `W`. -/
lemma unif_valuation_lt_one (p : InertiaIndex D) (hne : idxVal p ≠ ⊤) :
    p.1.1.valuation (((unif p : (F D)ˣ) : F D) : Ω) < 1 := by
  by_contra h
  have h' : p.1.1.valuation (algebraMap (F D) Ω 1) ≤
      p.1.1.valuation (algebraMap (F D) Ω ((unif p : (F D)ˣ) : F D)) := by
    rw [map_one, map_one]
    exact not_lt.1 h
  have := (Place.ord_le_ord_iff (idxPlace p hne) (algebraMap (F D) Ω) rfl (unif p).ne_zero
    one_ne_zero).2 h'
  rw [ord_unif_eq_one p hne, Place.ord_one] at this
  exact absurd this (by norm_num)

/-- `unif p` has the largest value `< 1` on `F`: it is a uniformiser of `W ∩ F`. -/
lemma valuation_le_unif (p : InertiaIndex D) (hne : idxVal p ≠ ⊤) :
    ∀ f ∈ F D, p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation (((unif p : (F D)ˣ) : F D) : Ω) := by
  intro f hf hlt
  set f' : F D := ⟨f, hf⟩
  by_cases hf0 : f' = 0
  · have : f = 0 := congrArg Subtype.val hf0
    rw [this, map_zero]
    exact zero_le
  have hord : 1 ≤ (idxPlace p hne).ord f' := by
    by_contra h
    have h1 : (idxPlace p hne).ord f' ≤ (idxPlace p hne).ord 1 := by
      rw [Place.ord_one]
      omega
    have h2 := (Place.ord_le_ord_iff (idxPlace p hne) (algebraMap (F D) Ω) rfl hf0
      one_ne_zero).1 h1
    rw [map_one, map_one] at h2
    exact absurd hlt (not_lt.2 h2)
  have h3 : (idxPlace p hne).ord ((unif p : (F D)ˣ) : F D) ≤ (idxPlace p hne).ord f' := by
    rw [ord_unif_eq_one p hne]
    exact hord
  exact (Place.ord_le_ord_iff (idxPlace p hne) (algebraMap (F D) Ω) rfl (unif p).ne_zero
    hf0).1 h3

/-- **The tame generator at a nontrivial inertia element is nontrivial** ([AbsTopIII] Prop 1.4
(i): the tame character `I_W ∩ H → Ẑ(1)` is injective). -/
theorem tameGen_ne_one (p : InertiaIndex D) (hne : idxVal p ≠ ⊤) (hσ : p.1.2 ≠ 1) :
    tameGen p ≠ 1 := by
  intro h
  apply hσ
  refine eq_one_of_forall_evalTriv_kummer_eq_one p.2.1 (unif p) (unif_valuation_lt_one p hne)
    (valuation_le_unif p hne) p.2.2 fun n _ => ?_
  have := tameGen_apply p ⟨n, Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  rw [h] at this
  exact this.symm

end Tame

section Rec

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

/-- `W ∩ F_V ≠ F_V` as soon as `F_V` contains a uniformiser of `Z_NF` at the NF-point `W`. -/
lemma idxVal_ne_top_of_uniformiser {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) (s : StageIdx D)
    (p : InertiaIndex s.data) (hpW : p.1.1 = W) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F s.data) : idxVal p ≠ ⊤ := by
  have hπ0 : π ≠ 0 := fun h => by
    rw [h, (nfPlace hk hW).ord_zero] at hπ; exact zero_ne_one hπ
  intro h
  have hmem : (⟨π, hπs⟩ : F s.data)⁻¹ ∈ idxVal p := h ▸ ValuationSubring.mem_top _
  have hmem' : π⁻¹ ∈ (nfPlace hk hW).1 := by
    change ((π⁻¹ : fnf N) : Ω) ∈ W
    rw [← hpW]
    exact hmem
  have := (nfPlace hk hW).ord_nonneg_of_mem hmem'
  rw [(nfPlace hk hW).ord_inv, hπ] at this
  omega

/-- **[AbsTopIII] Thm 1.9 (b), (c), (e): `ord_x` of the reconstructed triple is determined by the
residues**: for an NF-rational function `f` which is a unit `v` on a stage `V`, an NF-point `W`
with `K ⊆ W`, a uniformiser of `Z_NF` at `x` in `F_V`, and an inertia index `p = (W, σ)` of `V`
with `σ ≠ 1`, `ord_x(f) = n` iff `res_p(κ_V(v)) = θ_p^n`. -/
theorem val_recTriple_eq_iff (f : (fnf N)ˣ) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W)
    (s : StageIdx D) (v : US D s)
    (hv : (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω))
    (p : InertiaIndex s.data) (hpW : p.1.1 = W) (hσ : p.1.2 ≠ 1) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F s.data) (n : ℤ) :
    (recTriple N hkF).val (nfPlace hk hW) (kummerNFEquiv N hkF f) = n ↔
      res s.data (kummerMapZHat s.data v) p = tameGen p ^ n := by
  rw [res_kummerMapZHat_eq_tameGen_zpow N hkF f hk hW s v hv p hpW π hπ hπs]
  constructor
  · rintro rfl
    rfl
  · exact fun h => zHatOne_zpow_injective
      (tameGen_ne_one p (idxVal_ne_top_of_uniformiser N hk hW s p hpW π hπ hπs) hσ) h

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [Fact (D.H ≤ D.HL)]
  [NumberField k] in
/-- An element of order `1` at a place cut out by `W` lies in the maximal ideal of `W`. -/
lemma valuation_lt_one_of_ord_eq_one {κ L : Type*} [Field κ] [Field L] [Algebra κ L]
    [IsFunctionField κ L] [PerfectField κ] {W : ValuationSubring Ω} (P : Place κ L)
    (φ : L →+* Ω) (hP : P.1 = W.comap φ) {π : L} (hπ : P.ord π = 1) :
    W.valuation (φ π) < 1 := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, P.ord_zero] at hπ; exact zero_ne_one hπ
  by_contra h
  have h' : W.valuation (φ 1) ≤ W.valuation (φ π) := by
    rw [map_one, map_one]
    exact not_lt.1 h
  have := (Place.ord_le_ord_iff P φ hP hπ0 one_ne_zero).2 h'
  rw [hπ, Place.ord_one] at this
  exact absurd this (by norm_num)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [Fact (D.H ≤ D.HL)]
  [NumberField k] in
/-- An element of order `1` has the largest value `< 1`: it is a uniformiser. -/
lemma valuation_le_of_ord_eq_one {κ L : Type*} [Field κ] [Field L] [Algebra κ L]
    [IsFunctionField κ L] [PerfectField κ] {W : ValuationSubring Ω} (P : Place κ L)
    (φ : L →+* Ω) (hP : P.1 = W.comap φ) {π : L} (hπ : P.ord π = 1) (g : L)
    (hg : W.valuation (φ g) < 1) : W.valuation (φ g) ≤ W.valuation (φ π) := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, P.ord_zero] at hπ; exact zero_ne_one hπ
  by_cases hg0 : g = 0
  · rw [hg0, map_zero, map_zero]
    exact zero_le
  have hord : 1 ≤ P.ord g := by
    by_contra h
    have h1 : P.ord g ≤ P.ord 1 := by
      rw [Place.ord_one]
      omega
    have h2 := (Place.ord_le_ord_iff P φ hP hg0 one_ne_zero).1 h1
    rw [map_one, map_one] at h2
    exact absurd hg (not_lt.2 h2)
  exact (Place.ord_le_ord_iff P φ hP hπ0 hg0).1 (by rw [hπ]; exact hord)

set_option maxHeartbeats 800000 in
-- the stage `V₃` is built in the proof; its Galois data unify slowly
include hkF in
/-- **Cofinality of the stages for `ord_x`**: for every NF-rational function `f` and every
NF-point `W`, there is a stage `V` (over a finite `K / k`) on which `f` is a unit, whose function
field contains a uniformiser `π` of `Z_NF` at `x`, and of which `x` is a cusp, together with a
nontrivial element `σ` of the inertia group `I_W ∩ H_V` (the tame character is onto `μ_2`,
continuous-kummer-theory `exists_inertia_tameChar`). -/
theorem exists_stage_inertia (f : (fnf N)ˣ) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) :
    ∃ (s : StageIdx D) (v : US D s) (p : InertiaIndex s.data) (π : fnf N),
      (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω) ∧ p.1.1 = W ∧ p.1.2 ≠ 1 ∧
      (nfPlace hk hW).ord π = 1 ∧ (π : Ω) ∈ F s.data := by
  have hH : D.H ≤ D.HL := Fact.out
  obtain ⟨π, hπ⟩ := (nfPlace hk hW).exists_ord_eq_one
  have hπ0 : π ≠ 0 := fun h => by
    rw [h, (nfPlace hk hW).ord_zero] at hπ; exact zero_ne_one hπ
  have hπΩ0 : (π : Ω) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  obtain ⟨K₁, hK₁, hf₁⟩ := exists_finite_mem_F_constExt D hkF (N.mem_F _ (f : fnf N).2)
  obtain ⟨K₂, hK₂, hπ₂⟩ := exists_finite_mem_F_constExt D hkF (N.mem_F _ π.2)
  set K : IntermediateField k Ω := K₁ ⊔ K₂
  have hLF : ∀ {x : Ω}, x ∈ (constExt K D).L → x ∈ F (constExt K D) := fun {x} hx => by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ (constExt_H_le D hH K hσ)
  have hfK : ((f : fnf N) : Ω) ∈ F (constExt K D) :=
    hLF (L_constExt_mono D le_sup_left (F_constExt_le_L D K₁ hf₁))
  have hπK : (π : Ω) ∈ F (constExt K D) :=
    hLF (L_constExt_mono D le_sup_right (F_constExt_le_L D K₂ hπ₂))
  have hf0 : (⟨_, hfK⟩ : F (constExt K D)) ≠ 0 := fun h =>
    f.ne_zero (Subtype.ext (congrArg Subtype.val h :))
  have hπK0 : (⟨_, hπK⟩ : F (constExt K D)) ≠ 0 := fun h => hπΩ0 (congrArg Subtype.val h :)
  obtain ⟨t₁, ht₁, htr₁, htV₁, v₁, hv₁⟩ := exists_stage_units D K (Units.mk0 _ hf0)
  obtain ⟨t₂, ht₂, htr₂, -, v₂, hv₂⟩ := exists_stage_units D K (Units.mk0 _ hπK0)
  obtain ⟨t₃, ht₃, htr₃, h₁₃, h₂₃⟩ := exists_stage_ge D K hH ht₁ htr₁ ht₂
  haveI : IsGalois (K₀ K t₃) Ω := isGalois_stage D K ht₃ htr₃
  haveI : IsGalois (K₀ K t₁) Ω := isGalois_stage D K ht₁ htr₁
  let s₁ : StageIdx D := ⟨K, t₁, ht₁, htr₁, htV₁⟩
  let s₃ : StageIdx D := ⟨K, t₃, ht₃, htr₃, mem_chartRing_trans le_rfl htV₁ h₁₃⟩
  have h13 : s₁ ≤ s₃ := ⟨le_rfl, h₁₃⟩
  have hKW : ∀ c : K, algebraMap K Ω c ∈ W := fun c =>
    mem_of_mem_kbar' hk (algebraMap_mem_kbar c)
  have hπW : W.valuation (π : Ω) < 1 :=
    valuation_lt_one_of_ord_eq_one (nfPlace hk hW) (algebraMap (fnf N) Ω) rfl hπ
  have hπinv : ¬ W.valuation ((π : Ω)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    exact not_le.2 (one_lt_inv_iff₀.2 ⟨(Valuation.pos_iff _).2 hπΩ0, hπW⟩)
  -- `x` is a cusp of `V₃`: `π` is a unit on `V₂ ⊇ V₃`, but not at `W`
  have ht₃W : t₃ ∉ W := by
    intro h3
    have ht₂W : t₂ ∈ W := mem_of_mem_chartRing W hKW h3 h₂₃
    have hinv := (units_mem (D := stage D K ht₂ htr₂) (W := W) ⟨hKW, ht₂W⟩ v₂.2).2
    rw [Units.val_inv_eq_inv_val] at hinv
    change ((((v₂ : (F (stage D K ht₂ htr₂))ˣ) : F (stage D K ht₂ htr₂)) : Ω))⁻¹ ∈ W at hinv
    rw [hv₂] at hinv
    exact hπinv ((W.valuation_le_one_iff _).2 hinv)
  have hπs : (π : Ω) ∈ F s₃.data := le_F_stage_of_constExt D K ht₃ htr₃ hπK
  -- the place of `F_{V₃}` at `W`, and the uniformiser `π`
  have hne : W.comap (algebraMap (F s₃.data) Ω) ≠ ⊤ := by
    intro h
    have hmem : (⟨π, hπs⟩ : F s₃.data)⁻¹ ∈ W.comap (algebraMap (F s₃.data) Ω) :=
      h ▸ ValuationSubring.mem_top _
    exact hπinv ((W.valuation_le_one_iff _).2 hmem)
  let P : Place s₃.K (F s₃.data) := ⟨W.comap (algebraMap (F s₃.data) Ω), hne, fun c => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hKW c⟩
  have hPπ : P.ord ⟨π, hπs⟩ = 1 := ord_stage_eq_one N hk hW s₃ P rfl π hπ hπs
  -- a nontrivial inertia element: `σ(√π) = -√π`
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (π : Ω) two_pos
  have hα0 : α ≠ 0 := fun h => hπΩ0 (by rw [← hα, h, zero_pow two_ne_zero])
  obtain ⟨σ, hσ, hσα⟩ := exists_inertia_tameChar (D := s₃.data) hKW hπs hπΩ0
    (valuation_lt_one_of_ord_eq_one P (algebraMap (F s₃.data) Ω) rfl hPπ)
    (fun g hg hlt => valuation_le_of_ord_eq_one P (algebraMap (F s₃.data) Ω) rfl hPπ ⟨g, hg⟩ hlt)
    two_pos hα (ζ := -1) (by norm_num)
  refine ⟨s₃, unitsS h13 v₁, ⟨(W, σ), hKW, hσ⟩, π, ?_, rfl, ?_, hπ, hπs⟩
  · exact (coe_unitsT s₁.data s₃.data (F_le h13) (hW_le h13) v₁).trans hv₁
  · intro h1
    have h2 : ((σ : Ω ≃ₐ[K₀ s₃.K s₃.t'] Ω)) α = α := by
      have := congrArg (fun τ : s₃.data.H => (τ : Ω ≃ₐ[K₀ s₃.K s₃.t'] Ω) α) h1
      simpa using this
    rw [hσα, neg_one_mul, neg_eq_iff_add_eq_zero, ← two_mul] at h2
    exact hα0 ((mul_eq_zero.1 h2).resolve_left two_ne_zero)

/-- **[AbsTopIII] Thm 1.9 (b), (c), (e): `ord_x` of the reconstructed triple from the residues**:
`ord_x(f) = n` iff at some stage `V` on which `f` is a unit `v` (with a uniformiser of `Z_NF` at
`x` in its function field), at some nontrivial inertia element `σ` over `x`,
`res_{(W, σ)}(κ_V(v)) = θ^n` (`exists_stage_inertia`, `val_recTriple_eq_iff`). -/
theorem val_recTriple_eq_iff_exists (f : (fnf N)ˣ) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) (n : ℤ) :
    (recTriple N hkF).val (nfPlace hk hW) (kummerNFEquiv N hkF f) = n ↔
      ∃ (s : StageIdx D) (v : US D s) (p : InertiaIndex s.data),
        (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω) ∧ p.1.1 = W ∧ p.1.2 ≠ 1 ∧
        (∃ π : fnf N, (nfPlace hk hW).ord π = 1 ∧ (π : Ω) ∈ F s.data) ∧
        res s.data (kummerMapZHat s.data v) p = tameGen p ^ n := by
  constructor
  · intro h
    obtain ⟨s, v, p, π, hv, hpW, hσ, hπ, hπs⟩ := exists_stage_inertia N hkF f hk hW
    exact ⟨s, v, p, hv, hpW, hσ, ⟨π, hπ, hπs⟩,
      (val_recTriple_eq_iff N hkF f hk hW s v hv p hpW hσ π hπ hπs n).1 h⟩
  · rintro ⟨s, v, p, hv, hpW, hσ, ⟨π, hπ, hπs⟩, hres⟩
    exact (val_recTriple_eq_iff N hkF f hk hW s v hv p hpW hσ π hπ hπs n).2 hres

end Rec

end Iut.Reconstruction.Thm19
