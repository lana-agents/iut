/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Angular.Frobenioid

/-!
# Objects of the archimedean Frobenioid and `O^▷` ([FrdII], Example 3.3(ii); IUT I, Ex 3.4(i))

The remaining assertions of [FrdII], Example 3.3(ii), for the archimedean Frobenioid of angular
regions over `Pt` (`Angular.Obj`):

* "every endomorphism of a non-isotropic object of `C` is linear and co-angular; every
  endomorphism of an isotropic object of `C` is co-angular" (`endo_of_not_isotropic`,
  `endo_isCoangular`);
* "the following conditions on an object of `C` are equivalent: (a) the object is isotropic;
  (b) the object is Frobenius-trivial; (c) the object is Frobenius-ample"
  (`isIsotropic_tfae`);
* "every object of `C` is metrically trivial" (`isMetricallyTrivial`);
* "by Lemma 3.2(v), `C` is of Frobenius-isotropic type" (`isFrobeniusIsotropic`);

and, for IUT I, Example 3.4(i), the **natural isomorphism `O^▷(C_v) ≅ O^▷_{K_v}`** of monoids for
an isotropic object (`orhdEquiv`, `orhdVal_comp`: `O^▷(A) ≅ {z ∈ ℂ : 0 < |z| ≤ 1}`, with
`O^×(A) ↦ S¹`, `orhdVal_mem_ounits`), compatible with the isomorphisms `O^▷(A) ≅ O^▷(B)` induced by
co-angular pre-steps ([FrdI], Definition 1.3(iii)(c); `orhdVal_transport`). For a non-isotropic
object `O^▷(A)` is `(0, 1]` (`rot_eq_one_of_not_isotropic`).
-/

namespace Iut

namespace Frobenioid

namespace Angular

open CategoryTheory Set Pointwise

noncomputable section

/-- Every endomorphism of a non-isotropic object is linear, co-angular and has trivial angular
part ([FrdII], Example 3.3(ii), via Lemma 3.2(iv)). -/
theorem endo_of_not_isotropic {A : Obj} (hA : ¬ IsIsotropic P A) (e : A ⟶ A) :
    IsLinear P e ∧ IsCoangular P e ∧ e.rot = 1 := by
  rw [isIsotropic_iff] at hA
  obtain ⟨h1, h2⟩ := A.isAngular.eq_of_subset e.deg.ne_zero e.ang_le
  obtain ⟨hd, hv⟩ := h2 hA
  exact ⟨PNat.coe_eq_one_iff.mp hd, (isCoangular_iff e).mpr h1, hv⟩

/-- Every endomorphism of an isotropic object is co-angular ([FrdII], Example 3.3(ii)). -/
theorem endo_isCoangular {A : Obj} (hA : IsIsotropic P A) (e : A ⟶ A) : IsCoangular P e := by
  rw [isIsotropic_iff] at hA
  rw [isCoangular_iff, hA, singleton_mul_univ_pow _ e.deg.ne_zero]

/-- Endomorphisms of any object are co-angular. -/
theorem endo_isCoangular' (A : Obj) (e : A ⟶ A) : IsCoangular P e := by
  by_cases h : IsIsotropic P A
  · exact endo_isCoangular h e
  · exact (endo_of_not_isotropic h e).2.1

/-- **[FrdII], Example 3.3(ii)**: isotropic ⇔ Frobenius-trivial ⇔ Frobenius-ample. -/
theorem isIsotropic_tfae (A : Obj) :
    List.TFAE [IsIsotropic P A, IsFrobeniusTrivial P A, IsFrobeniusAmple P A] := by
  tfae_have 1 → 2 := fun h => isFrobeniusTrivial_of_univ ((isIsotropic_iff A).mp h)
  tfae_have 2 → 3 := fun ⟨ζ, _, _, h⟩ n => ⟨ζ n, (h n).1⟩
  tfae_have 3 → 1 := fun h => by
    by_contra hA
    obtain ⟨e, he⟩ := h 2
    have := (endo_of_not_isotropic hA e).1
    rw [isLinear_iff] at this
    rw [degFr_eq, this] at he
    exact absurd he (by decide)
  tfae_finish

/-- **[FrdII], Example 3.3(ii)**: every object is metrically trivial. -/
theorem isMetricallyTrivial (A : Obj) : IsMetricallyTrivial P A := by
  intro B φ hφ hφ'
  rw [isPreStep_iff] at hφ'
  rw [isCoangular_iff, hφ', PNat.one_coe, pow_one] at hφ
  exact ⟨(isoMk (B.tip - A.tip) φ.rot hφ (by ring)).symm⟩

/-- **[FrdII], Example 3.3(ii)** (via Lemma 3.2(v)): `C` is of Frobenius-isotropic type. -/
theorem isFrobeniusIsotropic (A : Obj) : IsFrobeniusIsotropic P A := by
  obtain ⟨N, hN⟩ := A.isAngular.pow_eq_univ
  let n : ℕ+ := ⟨N + 1, N.succ_pos⟩
  exact ⟨frobObj A n, frob A n, frob_isFrobeniusType A n,
    (isIsotropic_iff _).mpr (hN _ (Nat.le_succ N))⟩

/-! ### `O^▷` and `O^×` -/

/-- The element `μ = e^ρ·u ∈ ℂ^×` of a morphism. -/
def val {A A' : Obj} (f : A ⟶ A') : ℂ := (Real.exp f.rad : ℂ) * (f.rot : ℂ)

lemma val_ne_zero {A A' : Obj} (f : A ⟶ A') : val f ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') (Circle.coe_ne_zero _)

lemma norm_val {A A' : Obj} (f : A ⟶ A') : ‖val f‖ = Real.exp f.rad := by
  simp [val]

/-- Composition of linear morphisms multiplies the elements `μ`. -/
lemma val_comp {A A' A'' : Obj} (f : A ⟶ A') (g : A' ⟶ A'') (hg : g.deg = 1) :
    val (f ≫ g) = val g * val f := by
  simp only [val, comp_rad, comp_rot, hg, PNat.one_coe, pow_one, Nat.cast_one, one_mul,
    Real.exp_add, Complex.ofReal_mul, Circle.coe_mul]
  ring

/-- The element `μ` determines a linear morphism. -/
lemma eq_of_val_eq {A A' : Obj} {f g : A ⟶ A'} (hf : f.deg = 1) (hg : g.deg = 1)
    (h : val f = val g) : f = g := by
  have hr : f.rad = g.rad := by
    have := congrArg norm h
    rw [norm_val, norm_val] at this
    exact Real.exp_injective this
  refine hom_ext (hf.trans hg.symm) hr ?_
  apply Circle.ext
  have := Complex.ofReal_ne_zero.mpr (Real.exp_pos g.rad).ne'
  simp only [val, hr] at h
  exact mul_left_cancel₀ this h

/-- `O^▷`: base-identity linear endomorphisms are the linear endomorphisms. -/
lemma mem_orhd {A : Obj} (e : A ⟶ A) : e ∈ Orhd P A ↔ e.deg = 1 :=
  ⟨fun h => h.2, fun h => ⟨isBaseIdentity e, h⟩⟩

/-- `O^▷` of a non-isotropic object is `(0, 1]`: the angular part of every endomorphism is
trivial. -/
lemma rot_eq_one_of_not_isotropic {A : Obj} (hA : ¬ IsIsotropic P A) (e : A ⟶ A) : e.rot = 1 :=
  (endo_of_not_isotropic hA e).2.2

/-- `O^▷_ℂ = {z ∈ ℂ : 0 < |z| ≤ 1}` as a submonoid of `ℂ`. -/
def orhdC : Submonoid ℂ where
  carrier := {z | z ≠ 0 ∧ ‖z‖ ≤ 1}
  mul_mem' {a b} ha hb := ⟨mul_ne_zero ha.1 hb.1, by
    rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_ne_zero, by simp⟩

lemma val_mem_orhdC {A : Obj} (e : A ⟶ A) (he : e.deg = 1) : val e ∈ orhdC := by
  refine ⟨val_ne_zero e, ?_⟩
  rw [norm_val, Real.exp_le_one_iff]
  have := e.tip_le
  rw [he, PNat.one_coe, Nat.cast_one, one_mul] at this
  linarith

/-- The linear endomorphism `(1, z)` of an isotropic object, for `0 < |z| ≤ 1`. -/
def ofVal {A : Obj} (hA : A.ang = univ) (z : ℂ) (hz : z ∈ orhdC) : A ⟶ A :=
  mkHom 1 (Real.log ‖z‖) (Circle.exp (Complex.arg z)) (by rw [hA]; exact subset_univ _) (by
    have h1 : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hz.2
    simp only [PNat.one_coe, Nat.cast_one, one_mul]
    linarith)

lemma val_ofVal {A : Obj} (hA : A.ang = univ) (z : ℂ) (hz : z ∈ orhdC) :
    val (ofVal hA z hz) = z := by
  simp only [val, ofVal, mkHom_rad, mkHom_rot, Circle.coe_exp]
  rw [Real.exp_log (norm_pos_iff.mpr hz.1)]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- **The natural isomorphism `O^▷(A) ≅ O^▷_ℂ`** for an isotropic object `A` (IUT I,
Example 3.4(i)): `e = (1, μ) ↦ μ`. -/
def orhdEquiv {A : Obj} (hA : IsIsotropic P A) : Orhd P A ≃ orhdC where
  toFun e := ⟨val e.1, val_mem_orhdC e.1 ((mem_orhd _).mp e.2)⟩
  invFun z := ⟨ofVal ((isIsotropic_iff A).mp hA) z.1 z.2, (mem_orhd _).mpr rfl⟩
  left_inv e := Subtype.ext (eq_of_val_eq rfl ((mem_orhd _).mp e.2)
    (val_ofVal ((isIsotropic_iff A).mp hA) (val e.1) (val_mem_orhdC e.1 ((mem_orhd _).mp e.2))))
  right_inv z := Subtype.ext (val_ofVal ((isIsotropic_iff A).mp hA) z.1 z.2)

lemma orhdEquiv_apply {A : Obj} (hA : IsIsotropic P A) (e : Orhd P A) :
    (orhdEquiv hA e : ℂ) = val e.1 := rfl

/-- `orhdEquiv` is multiplicative: `e₁ ≫ e₂ ↦ μ₂ μ₁`. -/
lemma orhdEquiv_comp {A : Obj} (hA : IsIsotropic P A) (e₁ e₂ e : Orhd P A)
    (he : e.1 = e₁.1 ≫ e₂.1) :
    (orhdEquiv hA e : ℂ) = (orhdEquiv hA e₂ : ℂ) * (orhdEquiv hA e₁ : ℂ) := by
  change val e.1 = val e₂.1 * val e₁.1
  rw [he, val_comp _ _ ((mem_orhd _).mp e₂.2)]

/-- `O^×(A) ↦ S¹`: the units of `O^▷(A)` are the `(1, μ)` with `|μ| = 1`. -/
lemma mem_ounits_iff {A : Obj} (e : A ⟶ A) : e ∈ Ounits P A ↔ e.deg = 1 ∧ ‖val e‖ = 1 := by
  rw [norm_val, Real.exp_eq_one_iff]
  constructor
  · rintro ⟨hi, -, hl⟩
    obtain ⟨-, -, h3⟩ := (isIso_iff e).mp hi
    exact ⟨hl, by linarith⟩
  · rintro ⟨hl, hr⟩
    refine ⟨isIso_of e hl ?_ (by simp [hr]), isBaseIdentity e, hl⟩
    by_cases hA : IsIsotropic P A
    · rw [(isIsotropic_iff A).mp hA, singleton_mul_univ]
    · rw [rot_eq_one_of_not_isotropic hA e, singleton_one, one_mul]

/-- **Compatibility with [FrdI], Definition 1.3(iii)(c)**: if `φ : A → B` is a co-angular
pre-step and `e ∈ O^▷(A)`, `e' ∈ O^▷(B)` correspond (`φ ∘ e = e' ∘ φ`), then `e` and `e'` have the
same image in `O^▷_ℂ`. -/
lemma val_transport {A B : Obj} (φ : A ⟶ B) (hφ : IsPreStep P φ) {e : A ⟶ A} {e' : B ⟶ B}
    (_he : e.deg = 1) (he' : e'.deg = 1) (h : φ ≫ e' = e ≫ φ) : val e' = val e := by
  rw [isPreStep_iff] at hφ
  have := congrArg val h
  rw [val_comp _ _ he', val_comp _ _ hφ] at this
  rw [mul_comm] at this
  exact mul_left_cancel₀ (val_ne_zero φ) this

end

end Angular

end Frobenioid

end Iut
