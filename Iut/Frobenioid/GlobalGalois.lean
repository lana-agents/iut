/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisModel

/-!
# The global Frobenioid of a Galois extension ([FrdI], Example 6.3)

[FrdI], Example 6.3 (l.6219–6326 of `~/iut-scratch/frd/FrdI.txt`): for a number field `F` and a
[not necessarily finite] Galois extension `F̃/F` with `G = Gal(F̃/F)`, `D = B(G)⁰`, the
assignments `L ↦ Φ(L) = ⊕_{v ∈ V(L)} ord(O^▷_v)` (effective arithmetic divisors) and
`L ↦ B(L) = L^×` (for finite extensions `F ⊆ L ⊆ F̃`) "determine monoids on `D`", and the
principal divisor `B → Φ^gp` determines, by [FrdI], Theorem 5.2(ii), the model Frobenioid
`C_{F̃/F}`.

## Formalisation

* The object `G/H` of `B(G)⁰` (`H` open) corresponds to the finite extension `L_H = F̃^H`
  (`Fix A`, a number field: open subgroups are closed with finite-dimensional fixed field,
  `InfiniteGalois.isOpen_iff_finite`).
* A morphism `f : G/H → G/H'`, `f(H) = gH'`, gives the embedding `σ_f = g : F̃^{H'} → F̃^H`
  (`sigma f`; well defined on `F̃^{H'}`, `sigma_id`, `sigma_comp`).
* Divisors: the finite part of `Φ^gp(L)` is encoded by the group of invertible fractional ideals
  of `O_L` (`≅ ⊕_{w finite} ℤ`, effective = integral), the archimedean part by
  `V_∞(L) → ℝ` (`ArithDivG L`, `effG L`). The pull-back along `σ : K → L` is the extension of
  fractional ideals `I ↦ I·O_L` (this is `[w] ↦ Σ_{w'|w} e(w'|w)[w']`, i.e.
  `ord_{w'} = e(w'|w)·ord_w`) and `D ↦ D ∘ comap σ` at the archimedean places (`pbDiv`).
  Functoriality is `FractionalIdeal.extended_extended`; injectivity and the fact that effectivity
  is reflected are Mathlib's `extendedHom_injective`, `extendedHom_le_one_iff`.
* `divG L : L^× → Φ^gp(L)`, `x ↦ ((x), −log|x|_v)`, natural in `σ` (`pbDiv_divG`).
* **`phiGal F E`**, **`bGalNF F E`**, **`divGalNF F E`**: the divisor monoid `Φ`, the rational
  function monoid `B` and `Div_B` on `OrbitObj Gal(E/F)`; **`GlobalGaloisFrob F E`** is the model
  Frobenioid `C_{F̃/F}` of [FrdI], Example 6.3, and **`GlobalGaloisFrob.isFrobenioid`**
  ([FrdI], Theorem 5.2(ii)).
* **`divG_mem_effG_iff`**: a principal divisor is effective iff `x` is a root of unity
  (Kronecker); hence **`GlobalGaloisFrob.orhdEquiv`**, **`ounits_eq_orhd`**, **`ounitsEquiv`**:
  `O^×(A) = O^▷(A) ≅ μ(L)` ([FrdI], Example 6.3).
* **`degG`** (`deg^arith_L = log N(I) + Σ_v m_v D_v`) and **`degG_divG`**: `deg^arith_L`
  vanishes on the image of `B(L)` (product formula).

Not done here: `Prime(Φ(L)) ≅ V(L)` and perf-factoriality in this fractional-ideal encoding
(done over `Pt` with `Finsupp` coordinates in `GlobalPrimeZ.lean`), the comparison of the fibre
over `G/G` with `GlobalFrobenioid F`, the realification over `B(G)⁰`, and [FrdI], Theorem 6.4
over this base.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField FractionalIdeal

open scoped nonZeroDivisors

/-! ### Extension of fractional ideals along embeddings of number fields -/

section Ext

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M]

/-- Fractional ideals of `O_K`. -/
abbrev FI (K : Type*) [Field K] [NumberField K] : Type _ := FractionalIdeal (𝓞 K)⁰ K

omit [NumberField K] [NumberField L] in
lemma le_comap_of (σ : K →+* L) :
    (𝓞 K)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 L)⁰ :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (fun _ _ h => RingOfIntegers.ext (σ.injective (congrArg Subtype.val h)))

/-- **The extension `I ↦ I·O_L` of fractional ideals** along `σ : K → L`. -/
noncomputable def extIdeal (σ : K →+* L) : FI K →+* FI L :=
  extendedHom' L (le_comap_of σ)

/-- The localization of `mapRingHom σ` is `σ`. -/
lemma locMap_eq (σ : K →+* L) :
    (IsLocalization.map L (RingOfIntegers.mapRingHom σ) (le_comap_of σ) : K →+* L) = σ := by
  refine IsLocalization.ringHom_ext (𝓞 K)⁰ ?_
  rw [IsLocalization.map_comp]
  ext x
  rfl

lemma extIdeal_spanSingleton (σ : K →+* L) (x : K) :
    extIdeal σ (spanSingleton _ x) = spanSingleton _ (σ x) := by
  rw [extIdeal, extendedHom'_apply, extended_spanSingleton]
  congr 1
  rw [locMap_eq]

lemma extIdeal_comp (σ : K →+* L) (τ : L →+* M) (I : FI K) :
    extIdeal τ (extIdeal σ I) = extIdeal (τ.comp σ) I := by
  rw [extIdeal, extIdeal, extIdeal, extendedHom'_apply, extendedHom'_apply, extendedHom'_apply]
  exact extended_extended (L := L) (le_comap_of σ) I (le_comap_of τ)

lemma extIdeal_id (I : FI K) : extIdeal (RingHom.id K) I = I := by
  rw [extIdeal, extendedHom'_apply, ← coeToSubmodule_inj, coe_extended_eq_span]
  have : (IsLocalization.map K (RingOfIntegers.mapRingHom (RingHom.id K))
      (le_comap_of (RingHom.id K)) : K → K) = id := by
    rw [locMap_eq]; rfl
  rw [this, Set.image_id]
  exact Submodule.span_eq _

lemma extIdeal_eq_extendedHom (σ : K →+* L) :
    letI : Algebra K L := σ.toAlgebra
    extIdeal σ = extendedHom L (𝓞 L) := rfl

lemma extIdeal_injective (σ : K →+* L) : Function.Injective (extIdeal σ) := by
  letI : Algebra K L := σ.toAlgebra
  rw [extIdeal_eq_extendedHom]
  exact extendedHom_injective (𝓞 K) K L (𝓞 L)

lemma extIdeal_le_one_iff (σ : K →+* L) (I : FI K) : extIdeal σ I ≤ 1 ↔ I ≤ 1 := by
  letI : Algebra K L := σ.toAlgebra
  rw [extIdeal_eq_extendedHom]
  exact extendedHom_le_one_iff L (𝓞 L)

/-- The extension on invertible fractional ideals. -/
noncomputable def extU (σ : K →+* L) : (FI K)ˣ →* (FI L)ˣ :=
  Units.map (extIdeal σ).toMonoidHom

@[simp] lemma coe_extU (σ : K →+* L) (I : (FI K)ˣ) : (extU σ I : FI L) = extIdeal σ I := rfl

end Ext

/-! ### Arithmetic divisors with fractional-ideal finite part -/

section Div

variable (K : Type*) [Field K] [NumberField K]

/-- **`Φ^gp(K)`**: invertible fractional ideals (the finite part) and `V_∞(K) → ℝ`. -/
abbrev ArithDivG : Type _ := Additive (FI K)ˣ × (InfinitePlace K → ℝ)

/-- **`Φ(K)`**: integral ideals and nonnegative archimedean coordinates. -/
def effG : AddSubmonoid (ArithDivG K) where
  carrier := {x | ((Additive.toMul x.1 : (FI K)ˣ) : FI K) ≤ 1 ∧ ∀ v, 0 ≤ x.2 v}
  add_mem' {a b} ha hb := by
    refine ⟨?_, fun v => add_nonneg (ha.2 v) (hb.2 v)⟩
    change ((Additive.toMul a.1 * Additive.toMul b.1 : (FI K)ˣ) : FI K) ≤ 1
    rw [Units.val_mul]
    calc ((Additive.toMul a.1 : (FI K)ˣ) : FI K) * (Additive.toMul b.1 : (FI K)ˣ) ≤ 1 * 1 :=
          mul_le_mul' ha.1 hb.1
      _ = 1 := mul_one 1
  zero_mem' := ⟨le_of_eq Units.val_one, fun _ => le_rfl⟩

variable {K}

lemma mem_effG {x : ArithDivG K} :
    x ∈ effG K ↔ ((Additive.toMul x.1 : (FI K)ˣ) : FI K) ≤ 1 ∧ ∀ v, 0 ≤ x.2 v := Iff.rfl

lemma effG_sharp {x : ArithDivG K} (h : x ∈ effG K) (h' : -x ∈ effG K) : x = 0 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine Prod.ext ?_ (funext fun v => le_antisymm ?_ (h2 v))
  · set I : (FI K)ˣ := Additive.toMul x.1
    have hI' : ((I⁻¹ : (FI K)ˣ) : FI K) ≤ 1 := h1'
    have : (1 : FI K) ≤ I := by
      calc (1 : FI K) = (I : FI K) * ((I⁻¹ : (FI K)ˣ) : FI K) := by rw [Units.mul_inv]
        _ ≤ (I : FI K) * 1 := mul_le_mul_right hI' _
        _ = I := mul_one _
    have hI : I = 1 := Units.ext (le_antisymm h1 this)
    exact congrArg Additive.ofMul hI
  · have := h2' v
    simp only [Prod.snd_neg, Pi.neg_apply, Left.nonneg_neg_iff] at this
    exact this

lemma le_one_of_pow_le_one {I : FI K} (n : ℕ) (hn : 0 < n) (h : I ^ n ≤ 1) : I ≤ 1 := by
  intro x hx
  have hxn : x ^ n ∈ (I ^ n : FI K) := by
    rw [← mem_coe, coe_pow]
    exact Submodule.pow_mem_pow _ hx n
  obtain ⟨a, ha⟩ := (mem_one_iff _).mp (h hxn)
  have hint : IsIntegral (𝓞 K) x := by
    refine ⟨Polynomial.X ^ n - Polynomial.C a,
      Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    simp [ha]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact (mem_one_iff _).mpr ⟨y, hy⟩

lemma effG_saturated {x : ArithDivG K} (n : ℕ) (hn : 0 < n) (h : n • x ∈ effG K) :
    x ∈ effG K := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_one_of_pow_le_one n hn ?_, fun v => ?_⟩
  · change ((Additive.toMul (n • x.1) : (FI K)ˣ) : FI K) ≤ 1 at h1
    rwa [toMul_nsmul, Units.val_pow_eq_pow_val] at h1
  · have := h2 v
    change 0 ≤ n • x.2 v at this
    rw [nsmul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right this (by exact_mod_cast hn)

lemma effG_generating (x : ArithDivG K) : ∃ p ∈ effG K, ∃ q ∈ effG K, x = p - q := by
  set I : (FI K)ˣ := Additive.toMul x.1
  obtain ⟨a, aI, ha, hI⟩ := exists_eq_spanSingleton_mul (I : FI K)
  have ha' : algebraMap (𝓞 K) K a ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hs : spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) ≠ 0 :=
    spanSingleton_ne_zero_iff.mpr ha'
  let J : (FI K)ˣ := Units.mk0 _ hs
  have hJ : (J : FI K) ≤ 1 := by
    rw [Units.val_mk0, spanSingleton_le_iff_mem, mem_one_iff]
    exact ⟨a, rfl⟩
  have hIJ : ((I * J : (FI K)ˣ) : FI K) ≤ 1 := by
    rw [Units.val_mul, hI, Units.val_mk0, mul_comm, ← mul_assoc, spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ ha', spanSingleton_one, one_mul]
    exact coeIdeal_le_one
  refine ⟨(Additive.ofMul (I * J), fun v => max (x.2 v) 0), ⟨hIJ, fun v => le_max_right _ _⟩,
    (Additive.ofMul J, fun v => max (-x.2 v) 0), ⟨hJ, fun v => le_max_right _ _⟩, ?_⟩
  refine Prod.ext ?_ (funext fun v => ?_)
  · change x.1 = Additive.ofMul (I * J) - Additive.ofMul J
    rw [← ofMul_div, mul_div_cancel_right]
    rfl
  · change x.2 v = max (x.2 v) 0 - max (-x.2 v) 0
    rw [max_zero_sub_max_neg_zero_eq_self]

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]

/-- **The pull-back of divisors along `σ : K → L`**: extension of ideals at the finite places,
`D ↦ D ∘ comap σ` at the archimedean places. -/
noncomputable def pbDiv (σ : K →+* L) : ArithDivG K →+ ArithDivG L :=
  AddMonoidHom.prodMap (extU σ).toAdditive
    { toFun := fun D w => D (w.comap σ)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

lemma pbDiv_fst (σ : K →+* L) (x : ArithDivG K) :
    ((Additive.toMul (pbDiv σ x).1 : (FI L)ˣ) : FI L) =
      extIdeal σ (Additive.toMul x.1 : (FI K)ˣ) := rfl

@[simp] lemma pbDiv_snd (σ : K →+* L) (x : ArithDivG K) (w : InfinitePlace L) :
    (pbDiv σ x).2 w = x.2 (w.comap σ) := rfl

lemma pbDiv_comp (σ : K →+* L) (τ : L →+* M) (x : ArithDivG K) :
    pbDiv τ (pbDiv σ x) = pbDiv (τ.comp σ) x := by
  refine Prod.ext ?_ rfl
  change Additive.ofMul (extU τ (extU σ (Additive.toMul x.1))) =
    Additive.ofMul (extU (τ.comp σ) (Additive.toMul x.1))
  congr 1
  exact Units.ext (extIdeal_comp σ τ _)

lemma pbDiv_id (x : ArithDivG K) : pbDiv (RingHom.id K) x = x := by
  refine Prod.ext ?_ rfl
  change Additive.ofMul (extU (RingHom.id K) (Additive.toMul x.1)) = x.1
  rw [show extU (RingHom.id K) (Additive.toMul x.1) = Additive.toMul x.1 from
    Units.ext (extIdeal_id _)]
  rfl

lemma pbDiv_injective (σ : K →+* L) : Function.Injective (pbDiv σ) := by
  intro x y h
  refine Prod.ext ?_ (funext fun v => ?_)
  · have h1 := congrArg (fun z : ArithDivG L => ((Additive.toMul z.1 : (FI L)ˣ) : FI L)) h
    simp only [pbDiv_fst] at h1
    exact congrArg Additive.ofMul (Units.ext (extIdeal_injective σ h1))
  · letI : Algebra K L := σ.toAlgebra
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    exact congrFun (congrArg Prod.snd h) w

lemma pbDiv_mem_iff (σ : K →+* L) (x : ArithDivG K) : pbDiv σ x ∈ effG L ↔ x ∈ effG K := by
  rw [mem_effG, mem_effG, pbDiv_fst, extIdeal_le_one_iff]
  refine and_congr Iff.rfl ⟨fun h v => ?_, fun h w => h _⟩
  letI : Algebra K L := σ.toAlgebra
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  exact h w

/-! ### Principal divisors -/

variable (K) in
/-- **The principal divisor** `K^× → Φ^gp(K)`, `x ↦ ((x), −log|x|_v)`. -/
noncomputable def divG : Additive Kˣ →+ ArithDivG K where
  toFun x := (Additive.ofMul (Units.mk0 (spanSingleton (𝓞 K)⁰ (x.toMul : K))
      (spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero)),
    fun v => -Real.log (v (x.toMul : K)))
  map_zero' := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · apply Additive.toMul.injective
      ext1
      simp [spanSingleton_one]
    · simp
  map_add' x y := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · apply Additive.toMul.injective
      ext1
      simp [spanSingleton_mul_spanSingleton]
    · simp only [toMul_add, Units.val_mul, map_mul, Prod.snd_add, Pi.add_apply]
      rw [Real.log_mul (ne_of_gt (v.pos_iff.mpr x.toMul.ne_zero))
        (ne_of_gt (v.pos_iff.mpr y.toMul.ne_zero))]
      ring

lemma divG_fst (x : Kˣ) :
    ((Additive.toMul (divG K (Additive.ofMul x)).1 : (FI K)ˣ) : FI K) =
      spanSingleton (𝓞 K)⁰ (x : K) := rfl

@[simp] lemma divG_snd (x : Kˣ) (v : InfinitePlace K) :
    (divG K (Additive.ofMul x)).2 v = -Real.log (v (x : K)) := rfl

/-- **Naturality of the principal divisor**: `σ^* div(x) = div(σ x)`. -/
lemma pbDiv_divG (σ : K →+* L) (x : Additive Kˣ) :
    pbDiv σ (divG K x) = divG L (Units.map σ.toMonoidHom x.toMul |> Additive.ofMul) := by
  obtain ⟨y, rfl⟩ : ∃ y : Kˣ, Additive.ofMul y = x := ⟨x.toMul, rfl⟩
  refine Prod.ext ?_ (funext fun w => ?_)
  · apply Additive.toMul.injective
    ext1
    rw [pbDiv_fst, divG_fst, divG_fst, extIdeal_spanSingleton]
    rfl
  · rfl

/-! ### Effective principal divisors and the arithmetic degree -/

/-- **A principal divisor is effective iff `x` is a root of unity** (Kronecker). -/
theorem divG_mem_effG_iff (x : Kˣ) : divG K (Additive.ofMul x) ∈ effG K ↔ IsOfFinOrder x := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [divG_fst] at h1
    obtain ⟨a, ha⟩ := (mem_one_iff _).mp (h1 (mem_spanSingleton_self _ (x : K)))
    have hint : IsIntegral ℤ (x : K) := by
      rw [← ha]
      exact a.isIntegral_coe
    have hle : ∀ v : InfinitePlace K, v (x : K) ≤ 1 := fun v => by
      by_contra hv
      have := h2 v
      rw [divG_snd] at this
      have := Real.log_pos (lt_of_not_ge hv)
      linarith
    obtain ⟨n, hn, hxn⟩ := Embeddings.pow_eq_one_of_norm_le_one K ℂ x.ne_zero hint
      (fun φ => by rw [← InfinitePlace.apply φ]; exact hle _)
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.ext (by simpa using hxn)⟩
  · intro h
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp h
    have hxn' : (x : K) ^ n = 1 := by simpa using congrArg Units.val hxn
    refine ⟨?_, fun v => ?_⟩
    · rw [divG_fst, spanSingleton_le_iff_mem]
      have hint : IsIntegral (𝓞 K) (x : K) :=
        ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by simp [hxn']⟩
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      exact (mem_one_iff _).mpr ⟨y, hy⟩
    · have h1 : v (x : K) ^ n = 1 := by rw [← map_pow, hxn', map_one]
      have h2 : v (x : K) = 1 :=
        (pow_eq_one_iff_of_nonneg (v.pos_iff.mpr x.ne_zero).le hn.ne').mp h1
      rw [divG_snd, h2, Real.log_one, neg_zero]

lemma divG_eq_zero_of_isOfFinOrder (x : Kˣ) (h : IsOfFinOrder x) :
    divG K (Additive.ofMul x) = 0 := by
  refine effG_sharp ((divG_mem_effG_iff x).mpr h) ?_
  rw [← map_neg, ← ofMul_inv]
  exact (divG_mem_effG_iff _).mpr h.inv

lemma absNorm_unit_ne_zero (I : (FI K)ˣ) : absNorm (I : FI K) ≠ 0 := by
  intro h
  have := congrArg absNorm I.mul_inv
  rw [map_mul, h, zero_mul, map_one] at this
  exact zero_ne_one this

variable (K) in
/-- **The arithmetic degree `deg^arith : Φ^gp(K) → ℝ`**: `log N(I) + Σ_v m_v D_v`. -/
noncomputable def degG : ArithDivG K →+ ℝ where
  toFun x := Real.log (absNorm ((Additive.toMul x.1 : (FI K)ˣ) : FI K) : ℝ) +
    ∑ v, (v.mult : ℝ) * x.2 v
  map_zero' := by simp
  map_add' x y := by
    change Real.log (absNorm (((Additive.toMul x.1 * Additive.toMul y.1 : (FI K)ˣ)) : FI K) : ℝ)
      + ∑ v, (v.mult : ℝ) * (x.2 v + y.2 v) = _
    rw [Units.val_mul, map_mul, Rat.cast_mul,
      Real.log_mul (by exact_mod_cast absNorm_unit_ne_zero _)
        (by exact_mod_cast absNorm_unit_ne_zero _)]
    simp only [mul_add, Finset.sum_add_distrib]
    ring

/-- **`deg^arith` vanishes on the principal divisors** ([FrdI], Example 6.3: "`deg^arith_L`
vanishes on the image of `B(L)`"; the product formula). -/
theorem degG_divG (x : Additive Kˣ) : degG K (divG K x) = 0 := by
  change Real.log (absNorm (spanSingleton (𝓞 K)⁰ (x.toMul : K)) : ℝ) +
    ∑ v : InfinitePlace K, (v.mult : ℝ) * -Real.log (v (x.toMul : K)) = 0
  rw [absNorm_span_singleton, ← InfinitePlace.prod_eq_abs_norm,
    Real.log_prod (fun v _ => pow_ne_zero _ (v.pos_iff.mpr x.toMul.ne_zero).ne')]
  simp only [Real.log_pow, mul_neg, Finset.sum_neg_distrib, add_neg_cancel]

end Div

/-! ### The Galois base `B(Gal(E/F))⁰` -/

section Galois

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- `G = Gal(E/F)` with the Krull topology. -/
abbrev GalG : Type := E ≃ₐ[F] E

variable {F E}

/-- **`L_H = E^H`** for the object `G/H` of `B(G)⁰`. -/
abbrev Fix (A : OrbitObj (GalG F E)) : IntermediateField F E := IntermediateField.fixedField A.H

instance (A : OrbitObj (GalG F E)) : FiniteDimensional F (Fix A) := by
  have hc : IsClosed (A.H : Set (GalG F E)) := A.H.isClosed_of_isOpen A.isOpen
  have h := InfiniteGalois.fixingSubgroup_fixedField (k := F) (K := E) ⟨A.H, hc⟩
  rw [← InfiniteGalois.isOpen_iff_finite]
  change IsOpen (IntermediateField.fixedField A.H).fixingSubgroup.carrier
  have h' : (IntermediateField.fixedField A.H).fixingSubgroup = A.H := h
  rw [h']
  exact A.isOpen

instance (A : OrbitObj (GalG F E)) : NumberField (Fix A) := NumberField.of_module_finite F _

/-- The representative `g` of `f(H) = gH'`, as an element of `Gal(E/F)`. -/
noncomputable abbrev repG {A B : OrbitObj (GalG F E)} (f : A ⟶ B) : GalG F E := OrbitHom.rep f

omit [NumberField F] [IsGalois F E] in
lemma algEquiv_apply_inv (g : GalG F E) (y : E) : g (g⁻¹ y) = y := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

omit [NumberField F] [IsGalois F E] in
lemma rep_apply_mem {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (x : Fix B) :
    repG f (x : E) ∈ Fix A := by
  rw [IntermediateField.mem_fixedField_iff]
  intro h hh
  have hc := OrbitHom.conj_mem f hh
  have hx := (IntermediateField.mem_fixedField_iff _ _).mp x.2 _ hc
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at hx
  have := congrArg (repG f) hx
  rwa [algEquiv_apply_inv] at this

/-- **`σ_f = g : E^{H'} → E^H`** for `f : G/H → G/H'`, `f(H) = gH'`. -/
noncomputable def sigma {A B : OrbitObj (GalG F E)} (f : A ⟶ B) : Fix B →+* Fix A where
  toFun x := ⟨repG f (x : E), rep_apply_mem f x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ (x : E) y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ (x : E) y)

omit [NumberField F] [IsGalois F E] in
@[simp] lemma sigma_apply {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (x : Fix B) :
    ((sigma f x : Fix A) : E) = repG f (x : E) := rfl

omit [NumberField F] [IsGalois F E] in
lemma fix_apply {A : OrbitObj (GalG F E)} (x : Fix A) {h : GalG F E} (hh : h ∈ A.H) :
    h (x : E) = x :=
  (IntermediateField.mem_fixedField_iff _ _).mp x.2 _ hh

omit [NumberField F] [IsGalois F E] in
lemma sigma_id (A : OrbitObj (GalG F E)) : sigma (𝟙 A) = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (fix_apply x (OrbitHom.rep_id_mem A))

omit [NumberField F] [IsGalois F E] in
lemma sigma_comp {A B C : OrbitObj (GalG F E)} (f : A ⟶ B) (g : B ⟶ C) :
    sigma (f ≫ g) = (sigma f).comp (sigma g) := by
  refine RingHom.ext fun x => Subtype.ext ?_
  change repG (f ≫ g) (x : E) = repG f (repG g (x : E))
  have h := fix_apply x (OrbitHom.rep_comp_mem f g)
  rw [AlgEquiv.mul_apply] at h
  have := congrArg (repG f * repG g) h
  rwa [algEquiv_apply_inv, AlgEquiv.mul_apply] at this

omit [NumberField F] [IsGalois F E] in
lemma sigma_inv_comp {A B : OrbitObj (GalG F E)} (f : A ⟶ B) [IsIso f] :
    (sigma (inv f)).comp (sigma f) = RingHom.id _ := by
  rw [← sigma_comp, IsIso.inv_hom_id, sigma_id]

omit [NumberField F] [IsGalois F E] in
lemma sigma_comp_inv {A B : OrbitObj (GalG F E)} (f : A ⟶ B) [IsIso f] :
    (sigma f).comp (sigma (inv f)) = RingHom.id _ := by
  rw [← sigma_comp, IsIso.hom_inv_id, sigma_id]

lemma pbDiv_sigma_bijective {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (hf : IsFSM f) :
    Function.Bijective (pbDiv (sigma f)) := by
  haveI := OrbitObj.isIso_of_isFSM f hf
  refine Function.bijective_iff_has_inverse.mpr ⟨pbDiv (sigma (inv f)), fun x => ?_, fun y => ?_⟩
  · rw [pbDiv_comp, sigma_inv_comp, pbDiv_id]
  · rw [pbDiv_comp, sigma_comp_inv, pbDiv_id]

variable (F E) in
/-- **The divisor monoid `Φ` of [FrdI], Example 6.3 on `B(Gal(E/F))⁰`**: `G/H ↦ Φ(E^H)`. -/
noncomputable def phiGal : DivMonoid.{0} (OrbitObj (GalG F E)) where
  obj A := ArithDivG (Fix A)
  pb f := pbDiv (sigma f)
  pb_id A x := by
    change pbDiv (sigma (𝟙 A)) x = x
    rw [sigma_id, pbDiv_id]
  pb_comp f g x := by
    change pbDiv (sigma (f ≫ g)) x = pbDiv (sigma f) (pbDiv (sigma g) x)
    rw [sigma_comp, pbDiv_comp]
  pb_injective f := pbDiv_injective _
  pb_bijective_of_fsm f hf := pbDiv_sigma_bijective f hf
  pos A := effG (Fix A)
  pb_mem f x hx := (pbDiv_mem_iff _ _).mpr hx
  sharp := effG_sharp
  saturated := effG_saturated
  generating := effG_generating
  pos_surj_of_fsm f hf y hy := by
    obtain ⟨x, rfl⟩ := (pbDiv_sigma_bijective f hf).2 y
    exact ⟨x, (pbDiv_mem_iff _ _).mp hy, rfl⟩

/-- The pull-back of rational functions along `σ`. -/
noncomputable def pbU {K L : Type*} [Field K] [Field L] (σ : K →+* L) :
    Additive Kˣ →+ Additive Lˣ :=
  (Units.map σ.toMonoidHom).toAdditive

lemma pbU_apply {K L : Type*} [Field K] [Field L] (σ : K →+* L) (x : Additive Kˣ) :
    ((pbU σ x).toMul : L) = σ (x.toMul : K) := rfl

lemma pbU_comp {K L M : Type*} [Field K] [Field L] [Field M] (σ : K →+* L) (τ : L →+* M)
    (x : Additive Kˣ) : pbU τ (pbU σ x) = pbU (τ.comp σ) x := rfl

lemma pbU_id {K : Type*} [Field K] (x : Additive Kˣ) : pbU (RingHom.id K) x = x := rfl

lemma pbU_injective {K L : Type*} [Field K] [Field L] (σ : K →+* L) :
    Function.Injective (pbU σ) := fun _ _ h =>
  Additive.toMul.injective (Units.ext (σ.injective (congrArg (fun z => ((z.toMul : Lˣ) : L)) h)))

omit [NumberField F] [IsGalois F E] in
lemma pbU_sigma_bijective {A B : OrbitObj (GalG F E)} (f : A ⟶ B) (hf : IsFSM f) :
    Function.Bijective (pbU (sigma f)) := by
  haveI := OrbitObj.isIso_of_isFSM f hf
  refine Function.bijective_iff_has_inverse.mpr ⟨pbU (sigma (inv f)), fun x => ?_, fun y => ?_⟩
  · rw [pbU_comp, sigma_inv_comp, pbU_id]
  · rw [pbU_comp, sigma_comp_inv, pbU_id]

variable (F E) in
/-- **The rational function monoid `B`**: `G/H ↦ (E^H)^×`. -/
noncomputable def bGalNF : GrpOn.{0} (OrbitObj (GalG F E)) where
  obj A := Additive (Fix A)ˣ
  pb f := pbU (sigma f)
  pb_id A x := by
    change pbU (sigma (𝟙 A)) x = x
    rw [sigma_id, pbU_id]
  pb_comp f g x := by
    change pbU (sigma (f ≫ g)) x = pbU (sigma f) (pbU (sigma g) x)
    rw [sigma_comp, pbU_comp]
  pb_injective f := pbU_injective _
  pb_bijective_of_fsm f hf := pbU_sigma_bijective f hf

variable (F E) in
/-- **`Div_B : B → Φ^gp`**, the principal divisor. -/
noncomputable def divGalNF : DivHom (bGalNF F E) (phiGal F E).toGrpOn where
  app A := divG (Fix A)
  natural f x := (pbDiv_divG (sigma f) x).symm

variable (F E) in
/-- **The Frobenioid `C_{F̃/F}` of [FrdI], Example 6.3** over `B(Gal(E/F))⁰`. -/
abbrev GlobalGaloisFrob : Type := Model (phiGal F E) (bGalNF F E) (divGalNF F E)

variable (F E) in
/-- **`C_{F̃/F}` is a Frobenioid** ([FrdI], Example 6.3, via Theorem 5.2(ii)). -/
theorem GlobalGaloisFrob.isFrobenioid :
    IsFrobenioid (Model.toElem (phiGal F E) (bGalNF F E) (divGalNF F E)) :=
  Model.isFrobenioid

namespace GlobalGaloisFrob

local notation "𝐏" => Model.toElem (phiGal F E) (bGalNF F E) (divGalNF F E)

lemma div_eq_divG {X : GlobalGaloisFrob F E} (e : X ⟶ X) (hb : e.base = 𝟙 _) (h : e.deg = 1) :
    e.div = divG (Fix X.base) e.u := by
  have r := e.rel
  rw [h, hb, (phiGal F E).pb_id, PNat.one_coe, one_smul] at r
  exact add_left_cancel r

/-- **`O^▷(A) ≅ μ(L)`** ([FrdI], Example 6.3: `O^×(A) = O^▷(A) = μ(L)`). -/
noncomputable def orhdEquiv (X : GlobalGaloisFrob F E) :
    Orhd 𝐏 X ≃ CommGroup.torsion (Fix X.base)ˣ where
  toFun a := ⟨a.1.u.toMul, by
    have hd := div_eq_divG a.1 a.2.1 a.2.2
    have := a.1.div_mem
    rw [hd] at this
    exact (divG_mem_effG_iff _).mp this⟩
  invFun u := ⟨Model.mk1 (𝟙 _) (divG _ (Additive.ofMul u.1))
      ((divG_mem_effG_iff _).mpr u.2) (Additive.ofMul u.1) (by
        rw [(phiGal F E).pb_id]; rfl), rfl, rfl⟩
  left_inv a := by
    have hd := div_eq_divG a.1 a.2.1 a.2.2
    refine Subtype.ext (Model.hom_ext ?_ a.2.1.symm hd.symm ?_)
    · exact (show a.1.deg = 1 from a.2.2).symm
    · rfl
  right_inv u := rfl

/-- **`O^×(A) = O^▷(A)`** ([FrdI], Example 6.3). -/
theorem ounits_eq_orhd (X : GlobalGaloisFrob F E) : Ounits 𝐏 X = Orhd 𝐏 X := by
  ext e
  refine ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨?_, h⟩⟩
  have hb : e.base = 𝟙 _ := h.1
  have hd := div_eq_divG e hb h.2
  have ht := (orhdEquiv X ⟨e, h⟩).2
  have h0 : e.div = 0 := by
    rw [hd]
    exact divG_eq_zero_of_isOfFinOrder _ ht
  refine Model.isIso_of e h.2 ?_ h0
  rw [hb]
  infer_instance

/-- **`O^×(A) ≅ μ(L)`**. -/
noncomputable def ounitsEquiv (X : GlobalGaloisFrob F E) :
    Ounits 𝐏 X ≃ CommGroup.torsion (Fix X.base)ˣ :=
  (Equiv.setCongr (ounits_eq_orhd X)).trans (orhdEquiv X)

end GlobalGaloisFrob

end Galois

end Frobenioid

end Iut
