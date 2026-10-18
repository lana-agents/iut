/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalGaloisCmp

/-!
# The realification of `C_{F̃/F}` over `B(Gal(F̃/F))⁰` ([FrdI], Example 6.3, Proposition 5.3)

[FrdI], Example 6.3 (l.6219–6326 of `~/iut-scratch/frd/FrdI.txt`) builds the model Frobenioid
`C_{F̃/F}` over `D = B(G)⁰`, `G = Gal(F̃/F)` (here `GlobalGaloisFrob F E`, `GlobalGalois.lean`).
[FrdI], Theorem 6.4 (l.6334–6419) is about its realification `C^rlf`. Over the one-morphism base
this is `GlobalRealified K` (`Global.lean`); this file builds it over `B(G)⁰`.

## Pull-back of ℝ-divisors

For `σ : K → L`, the integral pull-back `pbZ σ` (extension of fractional ideals, in the
coordinates `ArithDivZ` of `toZ`) sends `[w]` to `eZ σ w = Σ_{w'} e(w'|w)·[w']` (the counts of
`𝔭_w O_L`). **`pbR σ`** is its ℝ-linear extension (`Finsupp.linearCombination` on the basis
`[w]`), and `D ↦ D ∘ comap σ` at the archimedean places.

* `eZ_nonneg`, `eZ_ne_zero`, **`eZ_disjoint`**: the `eZ σ w` are effective, nonzero, with pairwise
  disjoint supports (`𝔭_{w₁} + 𝔭_{w₂} = O_K` for `w₁ ≠ w₂`, `primeU_sup`, so no prime of `O_L`
  contains both extensions);
* `pbR_castDiv`: `pbR` extends the integral pull-back; `span_castDiv`: the integral divisors span
  `ArithDiv K` over ℝ, so `pbR_comp`, `pbR_id`, `pbR_divOf` follow from the integral case;
* **`pbR_mem_iff`**: `σ^*` preserves and reflects effectivity (by the disjointness);
  `pbR_injective`.

## The realified Frobenioid over `B(G)⁰`

* **`phiRlfGal F E`**: `G/H ↦ Φ^rlf(E^H)` with the pull-backs `pbR (sigma f)`;
* **`bRlfGal F E`**: `G/H ↦ ℝ·div((E^H)^×)` ([FrdI], Proposition 5.3);
* **`GlobalGaloisRlf F E`** with `GlobalGaloisRlf.isFrobenioid` ([FrdI], Theorem 5.2(ii));
* **`GlobalGaloisFrob.realify : C_{F̃/F} ⥤ C_{F̃/F}^rlf`**, the natural functor of [FrdI],
  Proposition 5.3: `castG = castDiv ∘ toZ` on divisors, compatible with the pull-backs
  (`castG_pbDiv`), with effectivity (`castG_mem_iff`) and with principal divisors (`realifyU`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField FractionalIdeal

open scoped nonZeroDivisors

/-! ### Counts of fractional ideals -/

section Counts

variable {K : Type*} [Field K] [NumberField K]

lemma le_one_iff_toZFin_nonneg (x : Additive (FI K)ˣ) :
    ((Additive.toMul x : (FI K)ˣ) : FI K) ≤ 1 ↔ ∀ w, 0 ≤ toZFin K x w := by
  have h := toZ_mem_iff (K := K) (x, 0)
  rw [mem_effConeZ, mem_effG] at h
  simpa using h.symm

lemma le_iff_toZFin (x y : Additive (FI K)ˣ) :
    ((Additive.toMul x : (FI K)ˣ) : FI K) ≤ (Additive.toMul y : (FI K)ˣ) ↔
      ∀ w, toZFin K y w ≤ toZFin K x w := by
  rw [Arakelov.FracIdeal.le_iff_count_le (K := K) (unit_ne_zero _) (unit_ne_zero _)]
  simp only [toZFin_apply, FracIdealFrob.cnt]
  exact ⟨fun h w => h _, fun h v => by
    obtain ⟨w, rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective v
    exact h w⟩

lemma count_eq_toZFin (x : Additive (FI K)ˣ) (w : FinitePlace K) :
    count K (FinitePlace.equivHeightOneSpectrum w) ((Additive.toMul x : (FI K)ˣ) : FI K) =
      toZFin K x w := rfl

/-- The prime ideal `𝔭_w`, as an invertible fractional ideal. -/
noncomputable def primeU (w : FinitePlace K) : Additive (FI K)ˣ := ofZFin (Finsupp.single w 1)

lemma toZFin_primeU (w : FinitePlace K) : toZFin K (primeU w) = Finsupp.single w 1 :=
  toZFin_ofZFin _

lemma single_one_nonneg (w u : FinitePlace K) : (0 : ℤ) ≤ Finsupp.single w 1 u := by
  classical
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

lemma primeU_le_one (w : FinitePlace K) :
    ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) ≤ 1 :=
  (le_one_iff_toZFin_nonneg _).2 fun u => by rw [toZFin_primeU]; exact single_one_nonneg w u

/-- **Distinct primes are coprime**: `𝔭_{w₁} + 𝔭_{w₂} = O_K`. -/
lemma primeU_sup {w₁ w₂ : FinitePlace K} (h : w₁ ≠ w₂) :
    ((Additive.toMul (primeU w₁) : (FI K)ˣ) : FI K) ⊔
      ((Additive.toMul (primeU w₂) : (FI K)ˣ) : FI K) = 1 := by
  set P₁ : FI K := ((Additive.toMul (primeU w₁) : (FI K)ˣ) : FI K)
  set P₂ : FI K := ((Additive.toMul (primeU w₂) : (FI K)ˣ) : FI K)
  have hP₁ : P₁ ≠ 0 := unit_ne_zero _
  have hP₂ : P₂ ≠ 0 := unit_ne_zero _
  have hQ : P₁ ⊔ P₂ ≠ 0 := fun hQ => hP₁ (FractionalIdeal.le_zero_iff.mp (hQ ▸ le_sup_left))
  refine Arakelov.FracIdeal.eq_of_count_eq hQ one_ne_zero fun v => ?_
  obtain ⟨w, rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective v
  have h1 := (Arakelov.FracIdeal.le_iff_count_le hP₁ hQ).1 le_sup_left
    (FinitePlace.equivHeightOneSpectrum w)
  have h2 := (Arakelov.FracIdeal.le_iff_count_le hP₂ hQ).1 le_sup_right
    (FinitePlace.equivHeightOneSpectrum w)
  have h3 := (Arakelov.FracIdeal.le_iff_count_le hQ one_ne_zero).1
    (sup_le (primeU_le_one w₁) (primeU_le_one w₂)) (FinitePlace.equivHeightOneSpectrum w)
  rw [count_eq_toZFin, toZFin_primeU] at h1 h2
  rw [count_one] at h3 ⊢
  classical
  by_cases hw : w₁ = w
  · subst hw
    have h' : w₂ ≠ w₁ := Ne.symm h
    simp only [Finsupp.single_apply, h', if_false] at h2
    omega
  · simp only [Finsupp.single_apply, hw, if_false] at h1
    omega

variable {L : Type*} [Field L] [NumberField L]

/-- **`σ^*[w] = Σ_{w'} e(w'|w)·[w']`**: the counts of `𝔭_w O_L`. -/
noncomputable def eZ (σ : K →+* L) (w : FinitePlace K) : FinitePlace L →₀ ℤ :=
  toZFin L (Additive.ofMul (extU σ (Additive.toMul (primeU w))))

lemma eZ_nonneg (σ : K →+* L) (w : FinitePlace K) (w' : FinitePlace L) : 0 ≤ eZ σ w w' :=
  (le_one_iff_toZFin_nonneg _).1 (by
    change extIdeal σ _ ≤ 1
    rw [extIdeal_le_one_iff]
    exact primeU_le_one w) w'

lemma toZFin_injective : Function.Injective (toZFin K) :=
  Function.LeftInverse.injective ofZFin_toZFin

lemma eZ_ne_zero (σ : K →+* L) (w : FinitePlace K) : eZ σ w ≠ 0 := by
  intro h
  rw [eZ, ← map_zero (toZFin L)] at h
  have h1 := toZFin_injective h
  have h2 : extIdeal σ ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) = extIdeal σ 1 := by
    rw [map_one]
    exact congrArg (fun z : Additive (FI L)ˣ => ((Additive.toMul z : (FI L)ˣ) : FI L)) h1
  have h3 : primeU w = 0 :=
    congrArg Additive.ofMul (Units.ext (extIdeal_injective σ h2))
  have h4 := congrArg (fun z => toZFin K z w) h3
  simp [toZFin_primeU] at h4

lemma exists_eZ_pos (σ : K →+* L) (w : FinitePlace K) : ∃ w', 0 < eZ σ w w' := by
  obtain ⟨w', hw'⟩ := Finsupp.ne_iff.mp (eZ_ne_zero σ w)
  exact ⟨w', lt_of_le_of_ne (eZ_nonneg σ w w') (Ne.symm hw')⟩

/-- **The supports of `σ^*[w₁]`, `σ^*[w₂]` are disjoint** for `w₁ ≠ w₂`. -/
lemma eZ_disjoint (σ : K →+* L) {w₁ w₂ : FinitePlace K} (h : w₁ ≠ w₂) (w' : FinitePlace L)
    (h₁ : 0 < eZ σ w₁ w') (h₂ : 0 < eZ σ w₂ w') : False := by
  have key : ∀ w, 0 < eZ σ w w' → extIdeal σ ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) ≤
      ((Additive.toMul (primeU w') : (FI L)ˣ) : FI L) := fun w hw =>
    (le_iff_toZFin (Additive.ofMul (extU σ (Additive.toMul (primeU w)))) (primeU w')).2
      fun u => by
        classical
        rw [toZFin_primeU, Finsupp.single_apply]
        split_ifs with hu
        · subst hu
          exact hw
        · exact eZ_nonneg σ w u
  have hsup := congrArg (extIdeal σ) (primeU_sup h)
  rw [sup_eq_add, map_add, map_one, ← sup_eq_add] at hsup
  have hle : ((Additive.toMul (0 : Additive (FI L)ˣ) : (FI L)ˣ) : FI L) ≤
      ((Additive.toMul (primeU w') : (FI L)ˣ) : FI L) := by
    change (1 : FI L) ≤ _
    rw [← hsup]
    exact sup_le (key w₁ h₁) (key w₂ h₂)
  have := (le_iff_toZFin _ _).1 hle w'
  simp [toZFin_primeU] at this

lemma eZ_eq_zero_of_ne (σ : K →+* L) {w₁ w₂ : FinitePlace K} (h : w₁ ≠ w₂) {w' : FinitePlace L}
    (h₁ : 0 < eZ σ w₁ w') : eZ σ w₂ w' = 0 :=
  le_antisymm (not_lt.mp fun h₂ => eZ_disjoint σ h w' h₁ h₂) (eZ_nonneg σ w₂ w')

end Counts

/-! ### The integral and the realified pull-back -/

section Pullback

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M]

/-- The integral pull-back in the coordinates `ArithDivZ`. -/
noncomputable def pbZ (σ : K →+* L) : ArithDivZ K →+ ArithDivZ L :=
  (toZ L).toAddMonoidHom.comp ((pbDiv σ).comp (toZ K).symm.toAddMonoidHom)

lemma pbZ_fst (σ : K →+* L) (a : FinitePlace K →₀ ℤ) (b : InfinitePlace K → ℝ) :
    (pbZ σ (a, b)).1 = (pbZ σ (a, 0)).1 := rfl

@[simp] lemma pbZ_snd (σ : K →+* L) (y : ArithDivZ K) (w : InfinitePlace L) :
    (pbZ σ y).2 w = y.2 (w.comap σ) := rfl

lemma pbZ_single (σ : K →+* L) (w : FinitePlace K) :
    (pbZ σ (Finsupp.single w 1, 0)).1 = eZ σ w := rfl

lemma pbZ_toZ (σ : K →+* L) (x : ArithDivG K) : pbZ σ (toZ K x) = toZ L (pbDiv σ x) := by
  simp [pbZ]

lemma pbZ_comp (σ : K →+* L) (τ : L →+* M) (y : ArithDivZ K) :
    pbZ τ (pbZ σ y) = pbZ (τ.comp σ) y := by
  simp [pbZ, pbDiv_comp]

lemma pbZ_id (y : ArithDivZ K) : pbZ (RingHom.id K) y = y := by
  simp [pbZ, pbDiv_id]

lemma pbZ_divZ (σ : K →+* L) (u : Additive Kˣ) : pbZ σ (divZ K u) = divZ L (pbU σ u) := by
  have h : (toZ K).symm (divZ K u) = divG K u := by
    rw [AddEquiv.symm_apply_eq, toZ_divG]
  change toZ L (pbDiv σ ((toZ K).symm (divZ K u))) = _
  rw [h, pbDiv_divG, toZ_divG]
  rfl

/-- The cast `ℤ → ℝ` of finite parts. -/
noncomputable def castFin (K : Type*) [Field K] [NumberField K] :
    (FinitePlace K →₀ ℤ) →+ (FinitePlace K →₀ ℝ) :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℝ)

lemma castDiv_fst' (y : ArithDivZ K) : (castDiv K y).1 = castFin K y.1 := rfl

/-- The finite part of the realified pull-back: `[w] ↦ Σ_{w'} e(w'|w)·[w']`, ℝ-linearly. -/
noncomputable def pbRFin (σ : K →+* L) : (FinitePlace K →₀ ℝ) →ₗ[ℝ] (FinitePlace L →₀ ℝ) :=
  Finsupp.linearCombination ℝ fun w => castFin L (eZ σ w)

/-- **The pull-back `σ^* : Φ^rlf(K)^gp → Φ^rlf(L)^gp` of ℝ-arithmetic divisors.** -/
noncomputable def pbR (σ : K →+* L) : ArithDiv K →ₗ[ℝ] ArithDiv L :=
  LinearMap.prodMap (pbRFin σ) (LinearMap.funLeft ℝ ℝ fun w : InfinitePlace L => w.comap σ)

@[simp] lemma pbR_fst (σ : K →+* L) (x : ArithDiv K) : (pbR σ x).1 = pbRFin σ x.1 := rfl

@[simp] lemma pbR_snd (σ : K →+* L) (x : ArithDiv K) (w : InfinitePlace L) :
    (pbR σ x).2 w = x.2 (w.comap σ) := rfl

lemma pbRFin_apply (σ : K →+* L) (c : FinitePlace K →₀ ℝ) (w' : FinitePlace L) :
    pbRFin σ c w' = c.sum fun w t => t * (eZ σ w w' : ℝ) := by
  rw [pbRFin, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  simp [castFin, smul_eq_mul]

/-- On the support of `σ^*[w]`, `(σ^* c)_{w'} = c_w·e(w'|w)`. -/
lemma pbRFin_apply_of_pos (σ : K →+* L) (c : FinitePlace K →₀ ℝ) {w : FinitePlace K}
    {w' : FinitePlace L} (h : 0 < eZ σ w w') : pbRFin σ c w' = c w * (eZ σ w w' : ℝ) := by
  rw [pbRFin_apply, Finsupp.sum_eq_single w]
  · intro u _ hu
    rw [eZ_eq_zero_of_ne σ (Ne.symm hu) h]
    simp
  · simp

/-- **`pbR` extends the integral pull-back.** -/
theorem pbR_castDiv (σ : K →+* L) (y : ArithDivZ K) :
    pbR σ (castDiv K y) = castDiv L (pbZ σ y) := by
  refine Prod.ext ?_ (funext fun w => rfl)
  rw [pbR_fst, castDiv_fst', castDiv_fst', pbZ_fst]
  let g : (FinitePlace K →₀ ℤ) →+ (FinitePlace L →₀ ℝ) :=
    (pbRFin σ).toAddMonoidHom.comp (castFin K)
  let h : (FinitePlace K →₀ ℤ) →+ (FinitePlace L →₀ ℝ) :=
    (castFin L).comp ((AddMonoidHom.fst _ _).comp ((pbZ σ).comp (AddMonoidHom.inl _ _)))
  change g y.1 = h y.1
  congr 1
  refine Finsupp.addHom_ext fun w n => ?_
  have hs : Finsupp.single w n = n • Finsupp.single w (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_zsmul, map_zsmul]
  congr 1
  change pbRFin σ (castFin K (Finsupp.single w 1)) = castFin L (eZ σ w)
  simp [castFin, pbRFin]

/-- **The integral divisors span `ArithDiv K` over ℝ.** -/
theorem span_castDiv : Submodule.span ℝ (Set.range (castDiv K)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = (x.1, 0) + castDiv K (0, x.2) :=
    Prod.ext (by simp [castDiv_fst']) (funext fun v => by simp)
  rw [hx]
  refine Submodule.add_mem _ ?_ (Submodule.subset_span ⟨_, rfl⟩)
  induction x.1 using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg =>
    rw [show ((f + g, 0) : ArithDiv K) = (f, 0) + (g, 0) by simp]
    exact Submodule.add_mem _ hf hg
  | single w t =>
    have : ((Finsupp.single w t, 0) : ArithDiv K) = t • castDiv K (Finsupp.single w 1, 0) :=
      Prod.ext (by simp [castDiv_fst', castFin]) (funext fun v => by simp)
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

lemma linearMap_ext_castDiv {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f g : ArithDiv K →ₗ[ℝ] V} (h : ∀ y, f (castDiv K y) = g (castDiv K y)) : f = g :=
  LinearMap.ext_on span_castDiv (by rintro _ ⟨y, rfl⟩; exact h y)

theorem pbR_comp (σ : K →+* L) (τ : L →+* M) (x : ArithDiv K) :
    pbR τ (pbR σ x) = pbR (τ.comp σ) x := by
  have : (pbR τ).comp (pbR σ) = pbR (τ.comp σ) := linearMap_ext_castDiv fun y => by
    rw [LinearMap.comp_apply, pbR_castDiv, pbR_castDiv, pbR_castDiv, pbZ_comp]
  exact LinearMap.congr_fun this x

theorem pbR_id (x : ArithDiv K) : pbR (RingHom.id K) x = x := by
  have : pbR (RingHom.id K) = LinearMap.id := linearMap_ext_castDiv fun y => by
    rw [pbR_castDiv, pbZ_id, LinearMap.id_apply]
  exact LinearMap.congr_fun this x

/-- **`σ^*` preserves and reflects effectivity.** -/
theorem pbR_mem_iff (σ : K →+* L) (x : ArithDiv K) : pbR σ x ∈ effCone L ↔ x ∈ effCone K := by
  rw [mem_effCone, mem_effCone]
  refine and_congr ⟨fun h w => ?_, fun h w' => ?_⟩ ⟨fun h v => ?_, fun h w => h _⟩
  · obtain ⟨w', hw'⟩ := exists_eZ_pos σ w
    have := h w'
    rw [pbR_fst, pbRFin_apply_of_pos σ _ hw'] at this
    exact (mul_nonneg_iff_of_pos_right (by exact_mod_cast hw')).mp this
  · rw [pbR_fst, pbRFin_apply]
    exact Finsupp.sum_nonneg fun w _ => mul_nonneg (h w) (by exact_mod_cast eZ_nonneg σ w w')
  · letI : Algebra K L := σ.toAlgebra
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    exact h w

theorem pbR_injective (σ : K →+* L) : Function.Injective (pbR σ) := by
  refine (injective_iff_map_eq_zero (pbR σ)).mpr fun x hx => effCone_sharp ?_ ?_
  · exact (pbR_mem_iff σ x).mp (hx ▸ (effCone L).zero_mem)
  · exact (pbR_mem_iff σ (-x)).mp (by rw [map_neg, hx, neg_zero]; exact (effCone L).zero_mem)

/-- **`σ^* div(x) = div(σ x)`** for ℝ-divisors. -/
theorem pbR_divOf (σ : K →+* L) (x : Kˣ) :
    pbR σ (divOf K ⟨(x : K), x.ne_zero⟩) =
      divOf L ⟨σ (x : K), (map_ne_zero σ).mpr x.ne_zero⟩ := by
  rw [← castDiv_divZ, pbR_castDiv, pbZ_divZ]
  exact castDiv_divZ (Units.map σ.toMonoidHom x)

theorem pbR_ratFun (σ : K →+* L) {x : ArithDiv K} (hx : x ∈ ratFun K) :
    pbR σ x ∈ ratFun L := by
  have : ratFun K ≤ (ratFun L).comap (pbR σ) := Submodule.span_le.mpr <| by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have h := pbR_divOf σ (Units.mk0 x hx)
    simp only [Units.val_mk0] at h
    change pbR σ (divOf K ⟨x, hx⟩) ∈ ratFun L
    rw [h]
    exact Submodule.subset_span ⟨_, rfl⟩
  exact this hx

/-- The pull-back of realified rational functions. -/
noncomputable def pbRat (σ : K →+* L) : ratFun K →+ ratFun L :=
  ((pbR σ).restrict fun _ hx => pbR_ratFun σ hx).toAddMonoidHom

@[simp] lemma coe_pbRat (σ : K →+* L) (x : ratFun K) : (pbRat σ x : ArithDiv L) = pbR σ x := rfl

/-- The realification `Φ^gp → (Φ^rlf)^gp` in the fractional-ideal encoding. -/
noncomputable def castG (K : Type*) [Field K] [NumberField K] : ArithDivG K →+ ArithDiv K :=
  (castDiv K).comp (toZ K).toAddMonoidHom

lemma castG_apply (x : ArithDivG K) : castG K x = castDiv K (toZ K x) := rfl

theorem castG_pbDiv (σ : K →+* L) (x : ArithDivG K) : castG L (pbDiv σ x) = pbR σ (castG K x) := by
  rw [castG_apply, castG_apply, pbR_castDiv, pbZ_toZ]

theorem castG_mem_iff (x : ArithDivG K) : castG K x ∈ effCone K ↔ x ∈ effG K := by
  rw [castG_apply, castDiv_mem_iff, toZ_mem_iff]

theorem castG_divG_mem (u : Additive Kˣ) : castG K (divG K u) ∈ ratFun K := by
  rw [castG_apply, toZ_divG, show u = Additive.ofMul u.toMul from rfl, castDiv_divZ]
  exact Submodule.subset_span ⟨_, rfl⟩

end Pullback

/-! ### The realified Frobenioid over `B(Gal(E/F))⁰` -/

section Galois

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

lemma pbR_sigma_bijective {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (hf : IsFSM f) :
    Function.Bijective (pbR (sigma f)) := by
  haveI := OrbitObj.isIso_of_isFSM f hf
  refine Function.bijective_iff_has_inverse.mpr ⟨pbR (sigma (inv f)), fun x => ?_, fun y => ?_⟩
  · rw [pbR_comp, sigma_inv_comp, pbR_id]
  · rw [pbR_comp, sigma_comp_inv, pbR_id]

variable (F E) in
/-- **The realified divisor monoid `Φ^rlf` on `B(Gal(E/F))⁰`**: `G/H ↦ Φ^rlf(E^H)`. -/
noncomputable def phiRlfGal : DivMonoid.{0} (OrbitObj (GalG F E)) where
  obj A := ArithDiv (Fix A)
  pb f := (pbR (sigma f)).toAddMonoidHom
  pb_id A x := by
    change pbR (sigma (𝟙 A)) x = x
    rw [sigma_id, pbR_id]
  pb_comp f g x := by
    change pbR (sigma (f ≫ g)) x = pbR (sigma f) (pbR (sigma g) x)
    rw [sigma_comp, pbR_comp]
  pb_injective f := pbR_injective _
  pb_bijective_of_fsm f hf := pbR_sigma_bijective f hf
  pos A := effCone (Fix A)
  pb_mem f x hx := (pbR_mem_iff _ _).mpr hx
  sharp := effCone_sharp
  saturated := effCone_saturated
  generating := effCone_generating
  pos_surj_of_fsm f hf y hy := by
    obtain ⟨x, rfl⟩ := (pbR_sigma_bijective f hf).2 y
    exact ⟨x, (pbR_mem_iff _ _).mp hy, rfl⟩

variable (F E) in
/-- **The realified rational functions** `G/H ↦ ℝ·div((E^H)^×)` ([FrdI], Proposition 5.3). -/
noncomputable def bRlfGal : GrpOn.{0} (OrbitObj (GalG F E)) where
  obj A := ratFun (Fix A)
  pb f := pbRat (sigma f)
  pb_id A x := Subtype.ext <| by
    change pbR (sigma (𝟙 A)) x = x
    rw [sigma_id, pbR_id]
  pb_comp f g x := Subtype.ext <| by
    change pbR (sigma (f ≫ g)) x = pbR (sigma f) (pbR (sigma g) x)
    rw [sigma_comp, pbR_comp]
  pb_injective f _ _ h := Subtype.ext (pbR_injective _ (congrArg Subtype.val h))
  pb_bijective_of_fsm f hf := by
    haveI := OrbitObj.isIso_of_isFSM f hf
    refine Function.bijective_iff_has_inverse.mpr ⟨pbRat (sigma (inv f)), fun x => ?_,
      fun y => ?_⟩ <;> refine Subtype.ext ?_
    · change pbR (sigma (inv f)) (pbR (sigma f) x) = x
      rw [pbR_comp, sigma_inv_comp, pbR_id]
    · change pbR (sigma f) (pbR (sigma (inv f)) y) = y
      rw [pbR_comp, sigma_comp_inv, pbR_id]

variable (F E) in
/-- `Div_B : ℝ·div(L^×) ↪ Φ^rlf(L)^gp`. -/
noncomputable def divRlfGal : DivHom (bRlfGal F E) (phiRlfGal F E).toGrpOn where
  app A := (ratFun (Fix A)).subtype.toAddMonoidHom
  natural _ _ := rfl

variable (F E) in
/-- **The realification `C_{F̃/F}^rlf` of the Frobenioid of [FrdI], Example 6.3** over
`B(Gal(E/F))⁰`. -/
abbrev GlobalGaloisRlf : Type := Model (phiRlfGal F E) (bRlfGal F E) (divRlfGal F E)

variable (F E) in
/-- **`C_{F̃/F}^rlf` is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem GlobalGaloisRlf.isFrobenioid :
    IsFrobenioid (Model.toElem (phiRlfGal F E) (bRlfGal F E) (divRlfGal F E)) :=
  Model.isFrobenioid

namespace GlobalGaloisFrob

/-- `u ↦ div(u) ∈ ℝ·Φ^birat`. -/
noncomputable def realifyU (A : OrbitObj (GalG F E)) (u : (bGalNF F E).obj A) :
    (bRlfGal F E).obj A :=
  ⟨castG (Fix A) (divG (Fix A) u), castG_divG_mem u⟩

lemma realifyU_add (A : OrbitObj (GalG F E)) (u v : (bGalNF F E).obj A) :
    realifyU A (u + v) = realifyU A u + realifyU A v :=
  Subtype.ext <|
    (congrArg (castG (Fix A)) (map_add (divG (Fix A)) u v)).trans (map_add _ _ _)

lemma realifyU_nsmul (A : OrbitObj (GalG F E)) (n : ℕ) (u : (bGalNF F E).obj A) :
    realifyU A (n • u) = n • realifyU A u :=
  Subtype.ext <|
    (congrArg (castG (Fix A)) (map_nsmul (divG (Fix A)) n u)).trans (map_nsmul _ _ _)

lemma realifyU_pb {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (u : (bGalNF F E).obj B) :
    realifyU A ((bGalNF F E).pb f u) = (bRlfGal F E).pb f (realifyU B u) := by
  refine Subtype.ext ?_
  change castG _ (divG _ (pbU (sigma f) u)) = pbR (sigma f) (castG _ (divG _ u))
  rw [← castG_pbDiv, pbDiv_divG]
  rfl

variable (F E) in
/-- **The realification functor `C_{F̃/F} → C_{F̃/F}^rlf`** ([FrdI], Proposition 5.3) over
`B(Gal(E/F))⁰`: the identity on the base, `castG` on divisors. -/
noncomputable def realify : GlobalGaloisFrob F E ⥤ GlobalGaloisRlf F E where
  obj X := ⟨X.base, castG _ X.α⟩
  map {X Y} φ := Model.mk' φ.deg φ.base (castG _ φ.div) ((castG_mem_iff _).mpr φ.div_mem)
    (realifyU _ φ.u) (by
      change (φ.deg : ℕ) • castG (Fix X.base) X.α + castG (Fix X.base) φ.div =
        pbR (sigma φ.base) (castG (Fix Y.base) Y.α) + castG (Fix X.base) (divG _ φ.u)
      rw [← castG_pbDiv, ← map_nsmul, ← map_add, ← map_add]
      exact congrArg (castG (Fix X.base)) φ.rel)
  map_id X := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · exact map_zero _
    · change castG _ (divG _ 0) = 0
      rw [map_zero, map_zero]
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · exact (map_add (castG (Fix X.base)) _ _).trans
        (congrArg₂ (· + ·) (castG_pbDiv _ _) (map_nsmul _ _ _))
    · change realifyU _ ((bGalNF F E).pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u) =
        (bRlfGal F E).pb φ.base (realifyU _ ψ.u) + (ψ.deg : ℕ) • realifyU _ φ.u
      rw [realifyU_add, realifyU_nsmul, realifyU_pb]

@[simp] lemma realify_obj_base (X : GlobalGaloisFrob F E) :
    ((realify F E).obj X).base = X.base := rfl
@[simp] lemma realify_obj_α (X : GlobalGaloisFrob F E) :
    ((realify F E).obj X).α = castG _ X.α := rfl
@[simp] lemma realify_map_deg {X Y : GlobalGaloisFrob F E} (φ : X ⟶ Y) :
    ((realify F E).map φ).deg = φ.deg := rfl
@[simp] lemma realify_map_base {X Y : GlobalGaloisFrob F E} (φ : X ⟶ Y) :
    ((realify F E).map φ).base = φ.base := rfl
@[simp] lemma realify_map_div {X Y : GlobalGaloisFrob F E} (φ : X ⟶ Y) :
    ((realify F E).map φ).div = castG _ φ.div := rfl

end GlobalGaloisFrob

end Galois

end Frobenioid

end Iut
