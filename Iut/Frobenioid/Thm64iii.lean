/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalNonRlf
import Iut.Frobenioid.GlobalPf
import Iut.NumberTheory.SixExponentials.LogPrimes
import LocalClassFieldTheory.NumberField.KroneckerDensity.Bauer

/-!
# [FrdI], Theorem 6.4(iii)

[FrdI], Theorem 6.4(iii) (p. 114–115): if the equivalence `Ψ^rlf : C₁^rlf ≅ C₂^rlf` of (ii)
arises from an equivalence `(Ψ^pf)^{un-tr}` of the unit-trivialized perfections, then
`deg(Ψ^rlf) ∈ ℚ_{>0}`, and the induced bijection `V(L₁) ≅ Prime(Φ₁) ≅ Prime(Φ₂) ≅ V(L₂)` maps a
valuation lying over a valuation `v₀` of `ℚ` to a valuation lying over `v₀`.

Here, for the global Frobenioids over `Pt`: `F : C^⊩(K) ≌ C^⊩(L)` an equivalence,
`Ψ : (C^pf)^{un-tr}(K) ≌ (C^pf)^{un-tr}(L)` an equivalence and `e : realify ⋙ F ≅ Ψ ⋙ realify`
(i.e. `F` arises from `Ψ`). The proof only uses that `Ψ_Φ(F)` and `Ψ_Φ(F⁻¹)` map divisors with
integral finite part to divisors with rational finite part (**`PreservesRatFin`**;
`preservesRatFin_of_pf`), so the theorem is stated under this hypothesis
(**`GlobalRealified.thm64iii`**) and specialised to `(C^pf)^{un-tr}` (**`thm64iii_pf`**); the
case of an equivalence of the non-realified Frobenioids is used for Theorem 6.4(iv)
(`Thm64iv.lean`):

* `deg(F) ∈ ℚ_{>0}`;
* finite places go to finite places (`placeEquiv_inl`), and `v` and its image lie over the same
  rational prime (`resChar_finMap`).

Proof (as in [FrdI]): `Ψ_Φ([v]) = q_v·[w]` with `q_v ∈ ℚ_{>0}` (the `ℚ`-structure is transported
by `Ψ`), so `deg(F)·log N(v) = q_v·log N(w)`. If `deg(F) ∉ ℚ`, then `v`, `w` always lie over
distinct primes; choosing three such pairs over six distinct primes contradicts [FrdI], Lemma
6.5(ii) (`Real.not_exists_pos_rat_log_div_eq`, from the rational six exponentials theorem).
If `deg(F) ∈ ℚ`, then `log p_w / log p_v ∈ ℚ`, so `p_w = p_v` by Lemma 6.5(i).
An archimedean image of a finite place is excluded by transporting `ℚ`-rationality back along
`F⁻¹`: the coordinate of `Ψ_Φ⁻¹(s·[u])` at `v` would be `s/t` for all real `s ≥ 0`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]

/-! ### Divisors of composites with isomorphisms over `Pt` -/

lemma comp_div_pt {X Y Z : GlobalRealified K} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).div = ψ.div + (ψ.deg : ℕ) • φ.div := rfl

lemma iso_div_deg {X Y : GlobalRealified K} (i : X ⟶ Y) [IsIso i] : i.div = 0 ∧ i.deg = 1 :=
  ⟨((Model.isIso_iff i).mp inferInstance).2.2, ((Model.isIso_iff i).mp inferInstance).1⟩

lemma div_comp_iso {X Y Z : GlobalRealified K} (φ : X ⟶ Y) (i : Y ⟶ Z) [IsIso i] :
    (φ ≫ i).div = φ.div := by
  rw [comp_div_pt, (iso_div_deg i).1, (iso_div_deg i).2, zero_add, PNat.one_coe, one_smul]

lemma div_iso_comp {X Y Z : GlobalRealified K} (i : X ⟶ Y) [IsIso i] (φ : Y ⟶ Z) :
    (i ≫ φ).div = φ.div := by
  rw [comp_div_pt, (iso_div_deg i).1, smul_zero, add_zero]

/-! ### `Ψ_Φ` of the inverse -/

lemma psiPhi_congr {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
    (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence] {z z' : ArithDiv M}
    (hz : z ∈ effCone M) (hz' : z' ∈ effCone M) (h : z = z') :
    psiPhi G z hz = psiPhi G z' hz' := by
  subst h; rfl

variable (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence]

/-- **`Ψ_Φ(F⁻¹) ∘ Ψ_Φ(F) = id`.** -/
theorem psiPhi_inv_psiPhi (z : ArithDiv K) (hz : z ∈ effCone K) :
    psiPhi F.inv (psiPhi F z hz) (psiPhi_mem F z hz) = z := by
  let X : GlobalRealified K := objOfDeg 0
  let φ := step X z hz
  have h1 : (F.map φ).div = psiPhi F z hz := div_map F φ
  have h2 : (F.inv.map (F.map φ)).div = psiPhi F.inv (F.map φ).div (F.map φ).div_mem :=
    div_map F.inv (F.map φ)
  have hn := F.asEquivalence.unit.naturality φ
  have hd := congrArg Model.Hom.div hn
  haveI : IsIso (F.asEquivalence.unit.app X) := inferInstance
  haveI : IsIso (F.asEquivalence.unit.app (stepTgt X z)) := inferInstance
  rw [div_comp_iso, div_iso_comp] at hd
  change z = (F.inv.map (F.map φ)).div at hd
  calc psiPhi F.inv (psiPhi F z hz) (psiPhi_mem F z hz)
      = psiPhi F.inv (F.map φ).div (F.map φ).div_mem :=
        divMap_congr F.inv (objOfDeg 0) _ _ h1.symm
    _ = (F.inv.map (F.map φ)).div := h2.symm
    _ = z := hd.symm

/-! ### Transport of `ℚ`-rationality -/

/-- If `G` arises from `Ψ` (`e : realify ⋙ G ≅ Ψ ⋙ realify`), `Ψ_Φ(G)` maps `Φ^pf` into `Φ^pf`. -/
theorem psiPhi_castQ_mem (G : GlobalRealified K ⥤ GlobalRealified L) [G.IsEquivalence]
    (Ψ : GlobalPf K ⥤ GlobalPf L) (e : GlobalPf.realify K ⋙ G ≅ Ψ ⋙ GlobalPf.realify L)
    (z : ArithDivQ K) (hz : z ∈ effConeQ K) :
    ∃ z' ∈ effConeQ L, psiPhi G (castQ K z) (castQ_mem_iff.mpr hz) = castQ L z' := by
  let φ := GlobalPf.stepQ z hz
  have h1 : (G.map ((GlobalPf.realify K).map φ)).div =
      psiPhi G (castQ K z) (castQ_mem_iff.mpr hz) := div_map G _
  have hn := e.hom.naturality φ
  have hd := congrArg Model.Hom.div hn
  haveI : IsIso (e.hom.app ⟨pt, 0⟩) := inferInstance
  haveI : IsIso (e.hom.app ⟨pt, z⟩) := inferInstance
  rw [div_comp_iso, div_iso_comp] at hd
  refine ⟨(Ψ.map φ).div, (Ψ.map φ).div_mem, ?_⟩
  rw [← h1]
  exact hd

/-- `e⁻¹`: if `F` arises from `Ψ`, then `F⁻¹` arises from `Ψ⁻¹`. -/
noncomputable def invCompat (Ψ : GlobalPf K ⥤ GlobalPf L) [Ψ.IsEquivalence]
    (e : GlobalPf.realify K ⋙ F ≅ Ψ ⋙ GlobalPf.realify L) :
    GlobalPf.realify L ⋙ F.inv ≅ Ψ.inv ⋙ GlobalPf.realify K :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight Ψ.asEquivalence.counitIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Ψ.inv ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.symm F.inv ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (GlobalPf.realify K) F.asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _)

/-! ### Rationality of `Ψ_Φ` -/

/-- **`Ψ_Φ(G)` maps divisors with integral finite part to divisors with rational finite part**
(the only input of Theorem 6.4(iii) beyond the realified equivalence). -/
def PreservesRatFin {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
    (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence] : Prop :=
  ∀ (z : ArithDivZ M) (hz : z ∈ effConeZ M) (w : FinitePlace N),
    ∃ q : ℚ, (psiPhi G (castDiv M z) (castDiv_mem_iff.mpr hz)).1 w = q

/-- `ℤ`-divisors as `ℚ`-divisors. -/
noncomputable def zToQ {M : Type u} [Field M] [NumberField M] (z : ArithDivZ M) : ArithDivQ M :=
  (z.1.mapRange (fun n : ℤ => (n : ℚ)) (by simp), z.2)

lemma castQ_zToQ {M : Type u} [Field M] [NumberField M] (z : ArithDivZ M) :
    castQ M (zToQ z) = castDiv M z := by
  refine Prod.ext (Finsupp.ext fun w => ?_) rfl
  simp [zToQ]

lemma zToQ_mem {M : Type u} [Field M] [NumberField M] {z : ArithDivZ M} (hz : z ∈ effConeZ M) :
    zToQ z ∈ effConeQ M := by
  rw [← castQ_mem_iff, castQ_zToQ]
  exact castDiv_mem_iff.mpr hz

/-- **If `F` arises from an equivalence of the unit-trivialized perfections, then
`PreservesRatFin F`.** -/
theorem preservesRatFin_of_pf (G : GlobalRealified K ⥤ GlobalRealified L) [G.IsEquivalence]
    (Ψ : GlobalPf K ⥤ GlobalPf L) (e : GlobalPf.realify K ⋙ G ≅ Ψ ⋙ GlobalPf.realify L) :
    PreservesRatFin G := by
  intro z hz w
  obtain ⟨z', -, hz'⟩ := psiPhi_castQ_mem G Ψ e (zToQ z) (zToQ_mem hz)
  refine ⟨z'.1 w, ?_⟩
  rw [psiPhi_congr G _ (castQ_mem_iff.mpr (zToQ_mem hz)) (castQ_zToQ z).symm, hz', castQ_fst]

/-! ### Single-place divisors -/

attribute [local instance] Classical.propDecidable

/-- `t·[v]` at an archimedean place, in `Φ^{pf,gp}`. -/
noncomputable def singleQ : Place K → ℝ → ArithDivQ K
  | Sum.inl _, _ => 0
  | Sum.inr v, t => (0, Pi.single v t)

lemma castQ_singleQ_inr (v : InfinitePlace K) (t : ℝ) :
    castQ K (singleQ (Sum.inr v) t) = single (Sum.inr v) t := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v' => ?_)
  · simp [singleQ, single]
  · rfl

lemma singleQ_inr_mem (v : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) :
    singleQ (Sum.inr v) t ∈ effConeQ K := by
  rw [← castQ_mem_iff, castQ_singleQ_inr]
  exact single_mem ht

/-- `[w]` for a finite place, with rational coordinates. -/
noncomputable def oneQ (w : FinitePlace K) : ArithDivQ K := (Finsupp.single w 1, 0)

lemma castQ_oneQ (w : FinitePlace K) : castQ K (oneQ w) = single (Sum.inl w) 1 := by
  refine Prod.ext (Finsupp.ext fun w' => ?_) (funext fun v' => ?_)
  · rw [castQ_fst]
    simp only [oneQ, single, Finsupp.single_apply]
    split_ifs <;> simp
  · rfl

lemma oneQ_mem (w : FinitePlace K) : oneQ w ∈ effConeQ K := by
  rw [← castQ_mem_iff, castQ_oneQ]
  exact single_mem zero_le_one

/-- `t·[u]` at an archimedean place, with integral (zero) finite part. -/
noncomputable def singleZ (u : InfinitePlace K) (t : ℝ) : ArithDivZ K := (0, Pi.single u t)

lemma castDiv_singleZ (u : InfinitePlace K) (t : ℝ) :
    castDiv K (singleZ u t) = single (Sum.inr u) t := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v' => ?_)
  · simp [singleZ, single]
  · rfl

lemma singleZ_mem (u : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) : singleZ u t ∈ effConeZ K := by
  rw [← castDiv_mem_iff, castDiv_singleZ]
  exact single_mem ht

/-- `[w]` for a finite place, with integral coordinates. -/
noncomputable def oneZ (w : FinitePlace K) : ArithDivZ K := (Finsupp.single w 1, 0)

lemma castDiv_oneZ (w : FinitePlace K) : castDiv K (oneZ w) = single (Sum.inl w) 1 := by
  refine Prod.ext (Finsupp.ext fun w' => ?_) (funext fun v' => ?_)
  · rw [castDiv_fst]
    simp only [oneZ, single, Finsupp.single_apply]
    split_ifs <;> simp
  · rfl

lemma oneZ_mem (w : FinitePlace K) : oneZ w ∈ effConeZ K := by
  rw [← castDiv_mem_iff, castDiv_oneZ]
  exact single_mem zero_le_one

lemma eq_single_of_supp {x : ArithDiv K} {p : Place K} (h : supp x = {p}) :
    x = single p (coord x p) := by
  refine eq_iff_coord.mpr fun q => ?_
  rw [coord_single]
  split_ifs with hq
  · rw [hq]
  · by_contra hne
    exact hq (show q ∈ ({p} : Set (Place K)) from h ▸ hne)

lemma supp_psiPhi_one (p : Place K) :
    supp (psiPhi F (single p 1) (single_mem zero_le_one)) = {placeEquiv F p} := by
  rw [supp_psiPhi, supp_single one_ne_zero, Set.image_singleton]

lemma coord_psiPhi_pos (p : Place K) :
    0 < coord (psiPhi F (single p 1) (single_mem zero_le_one)) (placeEquiv F p) := by
  have hm := (mem_effCone_iff_coord.mp (psiPhi_mem F _ (single_mem (p := p) zero_le_one)))
    (placeEquiv F p)
  refine lt_of_le_of_ne hm (Ne.symm ?_)
  have : placeEquiv F p ∈ supp (psiPhi F (single p 1) (single_mem zero_le_one)) := by
    rw [supp_psiPhi_one]; rfl
  exact this

/-! ### Finite places go to finite places -/

variable (hF : PreservesRatFin F) (hFi : PreservesRatFin F.inv)

include hFi in
/-- **A finite place is not mapped to an archimedean place.** -/
theorem placeEquiv_inl (v : FinitePlace K) : ∃ w, placeEquiv F (Sum.inl v) = Sum.inl w := by
  rcases h : placeEquiv F (Sum.inl v) with w | u
  · exact ⟨w, rfl⟩
  exfalso
  set t := coord (psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one)) (Sum.inr u)
  have ht : 0 < t := by have := coord_psiPhi_pos F (Sum.inl v); rwa [h] at this
  have hsingle : psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one) =
      single (Sum.inr u) t := by
    have := supp_psiPhi_one F (Sum.inl v); rw [h] at this
    exact eq_single_of_supp this
  -- `g(s)` = coordinate at `v` of `Ψ_Φ(F⁻¹)(s·[u])`
  let g : ℝ → ℝ := fun s => coord (psiPhi F.inv (single (Sum.inr u) (max s 0))
    (single_mem (le_max_right _ _))) (Sum.inl v)
  have hgmono : Monotone g := by
    intro s s' hss'
    have hle := (psiPhi_le_iff F.inv (single_mem (p := Sum.inr u) (le_max_right s 0))
      (single_mem (p := Sum.inr u) (le_max_right s' 0))).mpr (by
        rw [mem_effCone_iff_coord]
        intro q
        rw [coord_sub, coord_single, coord_single]
        split_ifs
        · exact sub_nonneg.mpr (max_le_max hss' le_rfl)
        · simp)
    have := (mem_effCone_iff_coord.mp hle) (Sum.inl v)
    rw [coord_sub] at this
    exact sub_nonneg.mp this
  have hgn : ∀ (n : ℕ), 0 < n → ∀ s, g (n * s) = n * g s := by
    intro n hn s
    have hmax : max ((n : ℝ) * s) 0 = n * max s 0 := by
      rcases le_total s 0 with hs | hs
      · rw [max_eq_right hs, mul_zero, max_eq_right (mul_nonpos_of_nonneg_of_nonpos
          (Nat.cast_nonneg _) hs)]
      · rw [max_eq_left hs, max_eq_left (mul_nonneg (Nat.cast_nonneg _) hs)]
    have hs : single (Sum.inr u) (max ((n : ℝ) * s) 0) = n • single (Sum.inr u) (max s 0) := by
      refine eq_iff_coord.mpr fun q => ?_
      rw [coord_nsmul, coord_single, coord_single, hmax]
      split_ifs <;> simp
    change coord (psiPhi F.inv _ _) _ = n * coord (psiPhi F.inv _ _) _
    rw [psiPhi_congr F.inv _ ((effCone L).nsmul_mem
      (single_mem (p := Sum.inr u) (le_max_right s 0)) n) hs, psiPhi_nsmul, coord_nsmul]
  have hglin := fun s (hs : 0 ≤ s) => eq_mul_of_monotone_of_nsmul hgmono hgn s hs
  -- `g(t) = 1`
  have hgt : g t = 1 := by
    have := psiPhi_inv_psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one)
    change coord (psiPhi F.inv (single (Sum.inr u) (max t 0)) _) (Sum.inl v) = 1
    rw [psiPhi_congr F.inv _ (psiPhi_mem F _ (single_mem zero_le_one))
      (show single (Sum.inr u) (max t 0) = psiPhi F (single (Sum.inl v) 1)
        (single_mem zero_le_one) by rw [max_eq_left ht.le, hsingle]),
      this, coord_single, if_pos rfl]
  -- `g(s) ∈ ℚ` for `s ≥ 0`
  have hgq : ∀ s, 0 ≤ s → ∃ q : ℚ, g s = q := by
    intro s hs
    obtain ⟨q, hq⟩ := hFi (singleZ u s) (singleZ_mem u hs) v
    refine ⟨q, ?_⟩
    change coord (psiPhi F.inv (single (Sum.inr u) (max s 0)) _) (Sum.inl v) = _
    rw [psiPhi_congr F.inv _ (castDiv_mem_iff.mpr (singleZ_mem u hs))
      (show single (Sum.inr u) (max s 0) = castDiv L (singleZ u s) by
        rw [max_eq_left hs, castDiv_singleZ]), coord_inl, hq]
  -- contradiction with `√2 ∉ ℚ`
  have hs2 : 0 ≤ t * Real.sqrt 2 := mul_nonneg ht.le (Real.sqrt_nonneg _)
  obtain ⟨q, hq⟩ := hgq _ hs2
  have hg1 : g 1 * t = 1 := by rw [← hglin t ht.le, hgt]
  rw [hglin _ hs2, ← mul_assoc, hg1, one_mul] at hq
  exact irrational_sqrt_two ⟨q, hq.symm⟩

/-- **The finite place `Ψ_Prime(v)`.** -/
noncomputable def finMap (v : FinitePlace K) : FinitePlace L :=
  (placeEquiv_inl F hFi v).choose

lemma placeEquiv_finMap (v : FinitePlace K) :
    placeEquiv F (Sum.inl v) = Sum.inl (finMap F hFi v) :=
  (placeEquiv_inl F hFi v).choose_spec

lemma finMap_injective : Function.Injective (finMap F hFi) := fun v v' h => by
  have := (placeEquiv F).injective ((placeEquiv_finMap F hFi v).trans
    (h ▸ (placeEquiv_finMap F hFi v').symm))
  exact Sum.inl_injective this

include hF in
/-- **`Ψ_Φ([v]) = q_v·[w]` with `q_v ∈ ℚ_{>0}`**, and `deg(F)·log N(v) = q_v·log N(w)`. -/
theorem exists_rat_degree (v : FinitePlace K) :
    ∃ q : ℚ, 0 < q ∧ degOf F * Real.log (primeNorm v) =
      q * Real.log (primeNorm (finMap F hFi v)) := by
  set w := finMap F hFi v
  have hsupp := supp_psiPhi_one F (Sum.inl v)
  rw [placeEquiv_finMap F hFi v] at hsupp
  have hsingle := eq_single_of_supp hsupp
  obtain ⟨q, hq⟩ := hF (oneZ v) (oneZ_mem v) w
  have e1 : psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one) =
      psiPhi F (castDiv K (oneZ v)) (castDiv_mem_iff.mpr (oneZ_mem v)) :=
    divMap_congr F (objOfDeg 0) _ _ (castDiv_oneZ v).symm
  have hcoord : coord (psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one))
      (Sum.inl w) = q := by rw [e1, coord_inl, hq]
  have hpos := coord_psiPhi_pos F (Sum.inl v)
  rw [placeEquiv_finMap F hFi v, hcoord] at hpos
  refine ⟨q, by exact_mod_cast hpos, ?_⟩
  have hdeg := degArith_psiPhi F (single (Sum.inl v) 1) (single_mem zero_le_one)
  rw [hsingle, hcoord] at hdeg
  have hds : ∀ {M : Type u} [Field M] [NumberField M] (x : FinitePlace M) (r : ℝ),
      degArith M (single (Sum.inl x) r) = r * Real.log (primeNorm x) := by
    intro M _ _ x r
    rw [degArith_apply]
    simp [single, Finsupp.sum_single_index]
  rw [hds, hds, one_mul] at hdeg
  linarith

/-! ### Residue characteristics -/

/-- The residue characteristic `p_v` of a finite place. -/
noncomputable def resChar {M : Type u} [Field M] [NumberField M] (v : FinitePlace M) : ℕ :=
  Ideal.absNorm (v.maximalIdeal.asIdeal.under ℤ)

/-- The residue degree `f_v`: `N(v) = p_v^{f_v}`. -/
noncomputable def resDeg {M : Type u} [Field M] [NumberField M] (v : FinitePlace M) : ℕ :=
  (Ideal.span {(resChar v : ℤ)}).inertiaDeg' v.maximalIdeal.asIdeal

lemma resChar_prime {M : Type u} [Field M] [NumberField M] (v : FinitePlace M) :
    (resChar v).Prime :=
  absNorm_under_prime v.maximalIdeal

lemma log_primeNorm {M : Type u} [Field M] [NumberField M] (v : FinitePlace M) :
    Real.log (primeNorm v) = resDeg v * Real.log (resChar v) := by
  rw [primeNorm, absNorm_eq_pow_absNorm_under v.maximalIdeal]
  push_cast
  rw [Real.log_pow]
  rfl

lemma resDeg_pos {M : Type u} [Field M] [NumberField M] (v : FinitePlace M) : 0 < resDeg v := by
  have h1 := one_lt_primeNorm v
  have h2 := log_primeNorm v
  rcases Nat.eq_zero_or_pos (resDeg v) with h | h
  · rw [h, Nat.cast_zero, zero_mul] at h2
    have := Real.log_pos h1
    linarith
  · exact h

lemma finite_resChar_mem {M : Type u} [Field M] [NumberField M] (S : Finset ℕ) :
    {v : FinitePlace M | resChar v ∈ S}.Finite := by
  have hS : ∀ n ∈ S, {v : FinitePlace M | resChar v = n}.Finite := fun n _ => by
    haveI := (finite_and_card_le_finrank (K := M) n).1
    have : {v : FinitePlace M | resChar v = n} ⊆
        FinitePlace.equivHeightOneSpectrum.symm ''
          (Set.range (fun P : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 M) //
            Ideal.absNorm (P.asIdeal.under ℤ) = n} => P.1)) := by
      intro v hv
      exact ⟨v.maximalIdeal, ⟨⟨v.maximalIdeal, hv⟩, rfl⟩,
        FinitePlace.equivHeightOneSpectrum.symm_apply_apply v⟩
    exact ((Set.finite_range _).image _).subset this
  have : {v : FinitePlace M | resChar v ∈ S} = ⋃ n ∈ S, {v | resChar v = n} := by
    ext v; simp
  rw [this]
  exact S.finite_toSet.biUnion hS

lemma infinite_finitePlace (M : Type u) [Field M] [NumberField M] : Infinite (FinitePlace M) := by
  haveI := (infinite_degOnePrimes M).to_subtype
  haveI : Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :=
    Infinite.of_injective _ (Subtype.val_injective (p := (· ∈ degOnePrimes M)))
  exact Infinite.of_injective _ FinitePlace.equivHeightOneSpectrum.symm.injective

lemma exists_avoid (S : Finset ℕ) :
    ∃ v : FinitePlace K, resChar v ∉ S ∧ resChar (finMap F hFi v) ∉ S := by
  have h1 := finite_resChar_mem (M := K) S
  have h2 : (finMap F hFi ⁻¹' {w : FinitePlace L | resChar w ∈ S}).Finite :=
    (finite_resChar_mem (M := L) S).preimage (finMap_injective F hFi).injOn
  haveI := infinite_finitePlace K
  obtain ⟨v, hv⟩ := (h1.union h2).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  exact ⟨v, hv⟩

/-- `log p_w / log p_v = deg(F)·(f_v / (q_v f_w))`. -/
lemma log_div (v : FinitePlace K) {q : ℚ} (hq : 0 < q)
    (h : degOf F * Real.log (primeNorm v) = q * Real.log (primeNorm (finMap F hFi v))) :
    Real.log (resChar (finMap F hFi v)) / Real.log (resChar v) =
      degOf F * ((resDeg v : ℚ) / (q * resDeg (finMap F hFi v)) : ℚ) := by
  set w := finMap F hFi v
  rw [log_primeNorm, log_primeNorm] at h
  have hv : 0 < Real.log (resChar v) := Real.log_pos (by exact_mod_cast (resChar_prime v).one_lt)
  have hfw : (0 : ℝ) < resDeg w := by exact_mod_cast resDeg_pos w
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  field_simp
  linarith

include hF in
/-- **[FrdI], Theorem 6.4(iii)** for the global Frobenioids over `Pt`, for an equivalence `F`
with `PreservesRatFin F` and `PreservesRatFin F⁻¹`. -/
theorem thm64iii :
    (∃ q : ℚ, 0 < q ∧ degOf F = q) ∧ ∀ v : FinitePlace K, resChar (finMap F hFi v) = resChar v := by
  -- a rational degree forces equal residue characteristics
  have hsame : ∀ c : ℚ, degOf F = c → ∀ v : FinitePlace K,
      resChar (finMap F hFi v) = resChar v := by
    intro c hc v
    obtain ⟨q, hq, h⟩ := exists_rat_degree F hF hFi v
    have hl := log_div F hFi v hq h
    by_contra hne
    let p : Fin 2 → ℕ := ![resChar (finMap F hFi v), resChar v]
    have hp : ∀ i, (p i).Prime := fun i => by
      fin_cases i
      · exact resChar_prime _
      · exact resChar_prime _
    have hinj : Function.Injective p := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij hne |
        exact absurd hij.symm hne
    have hv : Real.log (resChar v) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (resChar_prime v).one_lt)).ne'
    set r : ℚ := c * ((resDeg v : ℚ) / (q * resDeg (finMap F hFi v)))
    have hr : Real.log (resChar (finMap F hFi v)) = r * Real.log (resChar v) := by
      rw [hc] at hl
      rw [div_eq_iff hv] at hl
      rw [hl]; push_cast [r]; ring
    have h0 := Real.eq_zero_of_sum_rat_mul_log_prime_eq_zero hp hinj ![1, -r] (by
      simp [Fin.sum_univ_two, p, hr])
    exact one_ne_zero (h0 0)
  by_cases hc : ∃ q : ℚ, 0 < q ∧ degOf F = q
  · obtain ⟨q, -, hq⟩ := hc
    exact ⟨⟨q, by exact_mod_cast hq ▸ degOf_pos F, hq⟩, hsame q hq⟩
  exfalso
  push Not at hc
  have hdiff : ∀ v : FinitePlace K, resChar (finMap F hFi v) ≠ resChar v := by
    intro v hv
    obtain ⟨q, hq, h⟩ := exists_rat_degree F hF hFi v
    have hl := log_div F hFi v hq h
    rw [hv, div_self (Real.log_pos (by exact_mod_cast (resChar_prime v).one_lt)).ne'] at hl
    have hpos : (0 : ℚ) < (resDeg v : ℚ) / (q * resDeg (finMap F hFi v)) :=
      div_pos (by exact_mod_cast resDeg_pos v)
        (mul_pos hq (by exact_mod_cast resDeg_pos _))
    set a : ℚ := (resDeg v : ℚ) / (q * resDeg (finMap F hFi v))
    refine hc a⁻¹ (inv_pos.mpr hpos) ?_
    have ha : (a : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
    linarith
  -- three pairs over six distinct primes
  obtain ⟨v₁, -, -⟩ := exists_avoid F hFi ∅
  obtain ⟨v₃, h3, h3'⟩ := exists_avoid F hFi {resChar v₁, resChar (finMap F hFi v₁)}
  obtain ⟨v₅, h5, h5'⟩ := exists_avoid F hFi {resChar v₁, resChar (finMap F hFi v₁),
    resChar v₃, resChar (finMap F hFi v₃)}
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h3 h3' h5 h5'
  let p : Fin 6 → ℕ := ![resChar (finMap F hFi v₁), resChar v₁, resChar (finMap F hFi v₃),
    resChar v₃, resChar (finMap F hFi v₅), resChar v₅]
  have hp : ∀ i, (p i).Prime := fun i => by fin_cases i <;> exact resChar_prime _
  have d1 := hdiff v₁
  have d3 := hdiff v₃
  have d5 := hdiff v₅
  have hinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> omega
  apply Real.not_exists_pos_rat_log_div_eq hp hinj
  obtain ⟨q₁, hq₁, e₁⟩ := exists_rat_degree F hF hFi v₁
  obtain ⟨q₃, hq₃, e₃⟩ := exists_rat_degree F hF hFi v₃
  obtain ⟨q₅, hq₅, e₅⟩ := exists_rat_degree F hF hFi v₅
  have l₁ := log_div F hFi v₁ hq₁ e₁
  have l₃ := log_div F hFi v₃ hq₃ e₃
  have l₅ := log_div F hFi v₅ hq₅ e₅
  set a₁ : ℚ := (resDeg v₁ : ℚ) / (q₁ * resDeg (finMap F hFi v₁))
  set a₃ : ℚ := (resDeg v₃ : ℚ) / (q₃ * resDeg (finMap F hFi v₃))
  set a₅ : ℚ := (resDeg v₅ : ℚ) / (q₅ * resDeg (finMap F hFi v₅))
  have pos : ∀ (x : FinitePlace K) (q : ℚ), 0 < q →
      (0 : ℚ) < (resDeg x : ℚ) / (q * resDeg (finMap F hFi x)) := fun x q hq =>
    div_pos (by exact_mod_cast resDeg_pos x) (mul_pos hq (by exact_mod_cast resDeg_pos _))
  have ha₃ : (a₃ : ℝ) ≠ 0 := by exact_mod_cast (pos v₃ q₃ hq₃).ne'
  have ha₅ : (a₅ : ℝ) ≠ 0 := by exact_mod_cast (pos v₅ q₅ hq₅).ne'
  refine ⟨a₁ / a₃, a₁ / a₅, div_pos (pos v₁ q₁ hq₁) (pos v₃ q₃ hq₃),
    div_pos (pos v₁ q₁ hq₁) (pos v₅ q₅ hq₅), ?_, ?_⟩
  · simp only [p, Matrix.cons_val]
    rw [l₁, l₃]; push_cast; field_simp
  · simp only [p, Matrix.cons_val]
    rw [l₁, l₅]; push_cast; field_simp

omit hF hFi in
/-- **[FrdI], Theorem 6.4(iii)** for an equivalence `F` arising from an equivalence `Ψ` of the
unit-trivialized perfections `(C^pf)^{un-tr}`. -/
theorem thm64iii_pf (Ψ : GlobalPf K ⥤ GlobalPf L) [Ψ.IsEquivalence]
    (e : GlobalPf.realify K ⋙ F ≅ Ψ ⋙ GlobalPf.realify L) :
    (∃ q : ℚ, 0 < q ∧ degOf F = q) ∧ ∀ v : FinitePlace K,
      resChar (finMap F (preservesRatFin_of_pf F.inv Ψ.inv (invCompat F Ψ e)) v) = resChar v :=
  thm64iii F (preservesRatFin_of_pf F Ψ e) _

end GlobalRealified

end Frobenioid

end Iut
