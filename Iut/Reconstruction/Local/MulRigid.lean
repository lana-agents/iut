/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24iiAux
import Iut.Reconstruction.Local.MulLiftOrd
import ContinuousKummerTheory.Kummer.Faithful

/-!
# [AbsTopIII], Proposition 3.2 (iv), injectivity, for `G_K ↷ \bar{ℚ}_p^×`

[AbsTopIII], Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt`,
l.4111–4124): for MLF-Galois `TM`-pairs, `Isom((Π ↷ M), (Π* ↷ M*)) → Isom(Π, Π*)` is a
bijection. The proof of the injectivity (l.4144–4147) uses the functorial algorithms of
(i), (ii) (cyclotomic rigidity and the Kummer maps), "which imply that automorphisms of
`(Π ↷ M_TM)` that act trivially on `Π` necessarily act trivially on `M_TM`". Here, for a finite
extension `K ⊆ \bar{ℚ}_p` of `ℚ_p` and the `G_K`-module `\bar{ℚ}_p^×` with `ord`:

* **`mulAut_eq_refl`** (injectivity): a `G_K`-equivariant additive automorphism `ψ` of
  `\bar{ℚ}_p^×` (written additively, `PAdicGalois.Mul p`) with `ord ∘ ψ = λ · ord`, `λ > 0`, is
  the identity. The proof is the Kummer-theoretic argument behind (i), (ii), without cohomology:
  - `ψ` maps `L^×` into itself for every finite `L ⊇ K` (fixed fields, `mem_of_fixed`);
  - `λ = 1`: `λ · ord(π_K) ∈ ord(K^×) = ord(π_K) ℤ` for `ψ` and `ψ⁻¹` (`lam_int`);
  - `ψ = id` on `μ_n` (cyclotomic rigidity, `mulAut_mu`): `ψ(ζ) = ζ^a`; for `y^n = π_L`,
    `L = K(ζ)`, the element `ψ(y) y^{-a}` is fixed by `G_L`, and comparing `ord` gives `n ∣ 1 − a`;
  - `ψ = id` (Kummer maps, `mulAut_eq_self`): for `x ∈ L^×` and `y^n = x`, `ψ(y)/y ∈ L^×`, so
    `ψ(x)/x ∈ ⋂_n (L^×)^n = 1` (Kummer-faithfulness of `p`-adic fields, CKT
    `isTorallyKummerFaithful_padic`).

All declarations live in the namespace `Iut.Frobenioid.PAdicGalois.Rigid`; `ordU`, `ιF` and
their lemmas are MR9's (`MulLiftOrd.lean`).
-/

open PadicField IntermediateField Iut.Reconstruction

set_option linter.unusedSectionVars false

noncomputable section

namespace Iut

namespace Frobenioid

namespace PAdicGalois

namespace Rigid

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

/-! ### Fixed fields -/

section Fixed

variable [FiniteDimensional ℚ_[p] E]

theorem smul_coe (g : GK p E) (x : K̄ˣ) : ((g • x : K̄ˣ) : K̄) = g (x : K̄) := rfl

theorem mem_of_fixed (L : IntermediateField E K̄) {y : K̄}
    (h : ∀ g ∈ L.fixingSubgroup, g y = y) : y ∈ L := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  exact (mem_fixedField_iff _ _).2 h

/-- An element of `K̄ˣ` lying in `L` as a unit of `L`. -/
def unitsOf (L : IntermediateField E K̄) (y : K̄ˣ) (hy : (y : K̄) ∈ L) : Lˣ :=
  Units.mk0 ⟨y, hy⟩ fun h => y.ne_zero (congrArg Subtype.val h)

@[simp] theorem ιF_unitsOf (L : IntermediateField E K̄) [FiniteDimensional ℚ_[p] L] (y : K̄ˣ)
    (hy : (y : K̄) ∈ L) : ιF (p := p) L (unitsOf L y hy) = y := Units.ext rfl

variable (ψ : (PadicAlgCl p)ˣ →* (PadicAlgCl p)ˣ)
  (hψ : ∀ (g : GK p E) (x : (PadicAlgCl p)ˣ), ψ (g • x) = g • ψ x)
include hψ

/-- `ψ` maps `L^×` into itself. -/
theorem map_mem (L : IntermediateField E K̄) {y : K̄ˣ} (hy : (y : K̄) ∈ L) : (ψ y : K̄) ∈ L := by
  refine mem_of_fixed L fun g hg => ?_
  have hgy : g • y = y := Units.ext ((IntermediateField.mem_fixingSubgroup_iff L g).1 hg _ hy)
  rw [← smul_coe, ← hψ, hgy]

/-- **The key computation**: if `ψ(η) = η^i` on `μ_n`, then for `y^n ∈ L` the element
`ψ(y) · (y^i)⁻¹` is fixed by `G_L`, hence lies in `L`. -/
theorem mem_twist (L : IntermediateField E K̄) {n i : ℕ} (y : K̄ˣ) (hy : ((y ^ n : K̄ˣ) : K̄) ∈ L)
    (hμ : ∀ η : K̄ˣ, η ^ n = 1 → ψ η = η ^ i) : ((ψ y * (y ^ i)⁻¹ : K̄ˣ) : K̄) ∈ L := by
  refine mem_of_fixed L fun g hg => ?_
  obtain ⟨η, hηdef⟩ : ∃ η : K̄ˣ, η = (g • y) * y⁻¹ := ⟨_, rfl⟩
  have hgy : g • y = η * y := by rw [hηdef, inv_mul_cancel_right]
  have hgyn : g • (y ^ n) = y ^ n :=
    Units.ext ((IntermediateField.mem_fixingSubgroup_iff L g).1 hg _ hy)
  have hη : η ^ n = 1 := by
    rw [hηdef, mul_pow, ← smul_pow', hgyn, inv_pow, mul_inv_cancel]
  have h1 : g • (ψ y * (y ^ i)⁻¹) = ψ y * (y ^ i)⁻¹ := by
    rw [smul_mul', ← hψ, smul_inv', smul_pow', hgy, map_mul, hμ η hη, mul_pow, mul_inv,
      mul_comm (η ^ i) (ψ y), mul_assoc, mul_inv_cancel_left]
  rw [← smul_coe, h1]

end Fixed

/-! ### `λ = 1` -/

section Lambda

variable [FiniteDimensional ℚ_[p] E]

/-- If `ψ` is `G_K`-equivariant with `ord ∘ ψ = λ · ord`, then `λ ∈ ℤ`. -/
theorem lam_int (ψ : K̄ˣ →* K̄ˣ) (hψ : ∀ (g : GK p E) (x : K̄ˣ), ψ (g • x) = g • ψ x) {l : ℝ}
    (hord : ∀ x, ordU (ψ x) = l * ordU x) : ∃ m : ℤ, l = m := by
  set π := uniformizer p E
  have hπ : IsUniformizer p E π := uniformizer_spec (p := p) (K := E)
  set y := ιF (p := p) E (Units.mk0 π hπ.ne_zero)
  have hy : (y : K̄) ∈ (⊥ : IntermediateField E K̄) :=
    IntermediateField.algebraMap_mem (⊥ : IntermediateField E K̄) π
  obtain ⟨b, hb⟩ := (IntermediateField.mem_bot).1 (map_mem ψ hψ ⊥ hy)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact (ψ y).ne_zero hb.symm
  have hψy : ψ y = ιF (p := p) E (Units.mk0 b hb0) := Units.ext hb.symm
  have h1 := ordU_ιF (p := p) E (Units.mk0 π hπ.ne_zero)
  have h2 := ordU_ιF (p := p) E (Units.mk0 b hb0)
  rw [Units.val_mk0, hπ, Int.cast_one] at h1
  rw [← hψy, hord, Units.val_mk0] at h2
  refine ⟨v p b, ?_⟩
  calc l = l * (ordU y * v p (p : E)) := by rw [h1, mul_one]
    _ = v p b := by rw [← mul_assoc, h2]

/-- **`λ = 1`** for a `G_K`-equivariant automorphism with `ord ∘ ψ = λ · ord`, `λ > 0`. -/
theorem lam_eq_one (ψ : K̄ˣ ≃* K̄ˣ) (hψ : ∀ (g : GK p E) (x : K̄ˣ), ψ (g • x) = g • ψ x) {l : ℝ}
    (hl : 0 < l) (hord : ∀ x, ordU (ψ x) = l * ordU x) : l = 1 := by
  have hψ' : ∀ (g : GK p E) (x : K̄ˣ), ψ.symm (g • x) = g • ψ.symm x := fun g x => by
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply, hψ, MulEquiv.apply_symm_apply]
  have hord' : ∀ x, ordU (ψ.symm x) = l⁻¹ * ordU x := fun x => by
    have h := hord (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]
  obtain ⟨m, hm⟩ := lam_int (ψ : K̄ˣ →* K̄ˣ) hψ hord
  obtain ⟨m', hm'⟩ := lam_int (ψ.symm : K̄ˣ →* K̄ˣ) hψ' hord'
  have hmm : m * m' = 1 := by
    have : (m : ℝ) * m' = 1 := by rw [← hm, ← hm', mul_inv_cancel₀ hl.ne']
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h | h
  · rw [hm, h, Int.cast_one]
  · rw [hm, h] at hl
    norm_num at hl

end Lambda

/-! ### Cyclotomic rigidity and the Kummer maps -/

section Kummer

variable [FiniteDimensional ℚ_[p] E]

variable (ψ : (PadicAlgCl p)ˣ →* (PadicAlgCl p)ˣ)
  (hψ : ∀ (g : GK p E) (x : (PadicAlgCl p)ˣ), ψ (g • x) = g • ψ x)
  (hord : ∀ x, ordU (ψ x) = ordU x)

instance finiteDimensional_adjoin (x : K̄) :
    FiniteDimensional ℚ_[p] (E⟮x⟯ : IntermediateField E K̄) :=
  haveI : Algebra.IsAlgebraic E K̄ := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) E
  haveI : FiniteDimensional E E⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  Module.Finite.trans E (E⟮x⟯ : IntermediateField E K̄)

include hψ hord in
/-- **Cyclotomic rigidity**: `ψ` is the identity on `μ_n`. -/
theorem mulAut_mu {n : ℕ} (hn : 0 < n) (η : K̄ˣ) (hη : η ^ n = 1) : ψ η = η := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K̄) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K̄ n
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  set ζu := Units.mk0 ζ hζ0
  have hζn : ζu ^ n = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hζ.pow_eq_one, Units.val_one])
  have hψn : ((ψ ζu : K̄ˣ) : K̄) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hζn, map_one, Units.val_one]
  obtain ⟨i, hin, hi⟩ := hζ.eq_pow_of_pow_eq_one hψn
  have hi' : ζu ^ i = ψ ζu := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hi])
  -- `ψ` is `η ↦ η^i` on `μ_n`
  have hμ : ∀ ξ : K̄ˣ, ξ ^ n = 1 → ψ ξ = ξ ^ i := fun ξ hξ => by
    have hξ' : (ξ : K̄) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hξ, Units.val_one]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hξ'
    have hj' : ζu ^ j = ξ := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hj])
    rw [← hj', map_pow, ← hi', ← pow_mul, ← pow_mul, mul_comm]
  -- the field `L = K(ζ)`, a uniformiser `π` of `L`, and `y^n = π`
  set L : IntermediateField E K̄ := E⟮ζ⟯
  set π := uniformizer p L
  have hπ : IsUniformizer p L π := uniformizer_spec (p := p) (K := L)
  set x := ιF (p := p) L (Units.mk0 π hπ.ne_zero)
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq (x : K̄) hn
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hY
    exact x.ne_zero hY.symm
  set y := Units.mk0 Y hY0
  have hyx : y ^ n = x := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hY])
  have hxL : ((y ^ n : K̄ˣ) : K̄) ∈ L := by
    rw [hyx]
    exact (Units.mk0 π hπ.ne_zero : Lˣ).val.2
  have hw := mem_twist ψ hψ L y hxL hμ
  set w := unitsOf L _ hw
  -- comparing `ord`: `n · ord(w) = (1 - i) · ord(π)`
  have hwn : ιF (p := p) L w ^ n = ψ x * (x ^ i)⁻¹ := by
    rw [ιF_unitsOf, mul_pow, ← map_pow, hyx, inv_pow, ← pow_mul, mul_comm i n, pow_mul, hyx]
  have hord_w := congrArg ordU hwn
  rw [ordU_pow, ordU_mul, ordU_inv, ordU_pow, hord] at hord_w
  have hvw := ordU_ιF (p := p) L w
  have hvx := ordU_ιF (p := p) L (Units.mk0 π hπ.ne_zero)
  rw [Units.val_mk0, hπ] at hvx
  have hdvd : (n : ℤ) ∣ 1 - i := by
    refine ⟨v p (w : L), ?_⟩
    have : ((1 : ℝ) - i) = n * v p (w : L) := by
      rw [← hvw, ← mul_assoc, hord_w]
      have hx' : ordU x * v p (p : L) = 1 := by exact_mod_cast hvx
      linear_combination ((i : ℝ) - 1) * hx'
    exact_mod_cast this
  have hi1 : i = 1 ∨ n = 1 := by
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · left
      have h0 : (1 - i : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
        rw [abs_lt]; constructor <;> omega)
      omega
    · right; omega
  rcases hi1 with rfl | rfl
  · rw [hμ η hη, pow_one]
  · rw [pow_one] at hη
    rw [hη, map_one]

include hψ in
/-- **The Kummer maps**: if `ψ` is the identity on all `μ_n`, then `ψ = id`. -/
theorem mulAut_eq_self (hμ : ∀ n : ℕ, 0 < n → ∀ η : K̄ˣ, η ^ n = 1 → ψ η = η) (x : K̄ˣ) :
    ψ x = x := by
  set L : IntermediateField E K̄ := E⟮(x : K̄)⟯
  have hxL : (x : K̄) ∈ L := IntermediateField.mem_adjoin_simple_self E (x : K̄)
  have hcL : ((ψ x * x⁻¹ : K̄ˣ) : K̄) ∈ L := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (map_mem ψ hψ L hxL) (inv_mem hxL)
  set c := unitsOf L _ hcL
  have hKF : KummerTheory.IsKummerFaithfulGm L :=
    KummerTheory.isTorallyKummerFaithful_padic p L
  have hc : c = 1 := by
    refine hKF c fun n hn => ?_
    obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq (x : K̄) hn
    have hY0 : Y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hY
      exact x.ne_zero hY.symm
    set y := Units.mk0 Y hY0
    have hyx : y ^ n = x := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hY])
    have hyL : ((y ^ n : K̄ˣ) : K̄) ∈ L := by rw [hyx]; exact hxL
    have hw := mem_twist (i := 1) ψ hψ L y hyL (fun η hη => by rw [pow_one]; exact hμ n hn η hη)
    refine ⟨unitsOf L _ hw, ιF_injective (p := p) L ?_⟩
    rw [map_pow, ιF_unitsOf, ιF_unitsOf, pow_one, mul_pow, ← map_pow, hyx, inv_pow, hyx]
  have h1 : ψ x * x⁻¹ = 1 := by
    have := congrArg (ιF (p := p) L) hc
    rwa [ιF_unitsOf, map_one] at this
  exact mul_inv_eq_one.1 h1

include hψ hord in
/-- **[AbsTopIII], Proposition 3.2 (iv), injectivity** (multiplicative form, `λ = 1`). -/
theorem mulHom_eq_id (x : K̄ˣ) : ψ x = x :=
  mulAut_eq_self ψ hψ (fun _ hn η hη => mulAut_mu ψ hψ hord hn η hη) x

end Kummer

/-! ### The additive statement -/

section Final

variable [FiniteDimensional ℚ_[p] E]

/-- `K̄ˣ ≃* K̄ˣ` from an additive automorphism of `Mul p = Additive K̄ˣ`. -/
def toMulAut (ψ : Mul p ≃+ Mul p) : K̄ˣ ≃* K̄ˣ where
  toFun x := Additive.toMul (ψ (Additive.ofMul x))
  invFun x := Additive.toMul (ψ.symm (Additive.ofMul x))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [ofMul_mul, toMul_add]

/-- **[AbsTopIII], Proposition 3.2 (iv), injectivity** (`T = TM`, for `G_K ↷ K̄^×` with `ord`):
a `G_K`-equivariant additive automorphism `ψ` of `K̄^×` with `ord ∘ ψ = λ · ord` for some
`λ > 0` is the identity. -/
theorem mulAut_eq_refl (ψ : Mul p ≃+ Mul p)
    (hψ : ∀ (g : GK p E) (m : Mul p), ψ (g • m) = g • ψ m) {l : ℝ} (hl : 0 < l)
    (hord : ∀ m, ord p (ψ m) = l * ord p m) : ψ = AddEquiv.refl (Mul p) := by
  set f := toMulAut ψ
  have hf : ∀ (g : GK p E) (x : K̄ˣ), f (g • x) = g • f x := fun g x =>
    congrArg Additive.toMul (hψ g (Additive.ofMul x))
  have hfo : ∀ x, ordU (f x) = l * ordU x := fun x => hord (Additive.ofMul x)
  have hl1 : l = 1 := lam_eq_one f hf hl hfo
  subst hl1
  have hfo' : ∀ x, ordU (f x) = ordU x := fun x => by rw [hfo, one_mul]
  exact AddEquiv.ext fun m =>
    congrArg Additive.ofMul (mulHom_eq_id (f : K̄ˣ →* K̄ˣ) hf hfo' m.toMul)

end Final

end Rigid

end PAdicGalois

end Frobenioid

end Iut

end
