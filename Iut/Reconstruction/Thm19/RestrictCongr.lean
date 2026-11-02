/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageIso
import Iut.Reconstruction.Thm19.NFKummer
import CurvesJacobian.Kummer.ClosedRestriction
import CurvesJacobian.Kummer.CuspInertiaZHat

/-!
# Restriction to closed points along isomorphisms of Galois models (MR9 item 4, step 4, "E")

[AbsTopIII] Prop 1.8 (`Topics in Absolute Anabelian Geometry III.txt` l.2061–2106) tests a class
`η ∈ H¹(Π_U, Ẑ(1))` by its restrictions `η|_x = s_x^*(η)` to closed points. For the functoriality
of [AbsTopIII] Thm 1.9 (d) along an isomorphism `e : Π_U ≃ Π_{U'}` (with an `e`-equivariant
`χ : Ẑ(1) ≃ Ẑ(1)'`), the vanishing of `η|_x` must be read off from the decomposition group of `x`
alone. Here, in the generic Galois models:

* `CobOn φ S c`: on `S`, the function `c` agrees modulo `ker φ` with a coboundary;
  `cobOn_conj_iff` (conjugate subgroups, for cocycles `c`) and `cobOn_map_iff` (transport along
  `e` and `χ`, if `χ` matches the kernels);
* `ZHatOne.proj_surjective` (`Ω` algebraically closed: compatible systems of roots of unity
  exist) and `proj_map_eq_one_iff` (a homomorphism `χ : Ẑ(1) → Ẑ(1)'` maps `ker proj_n` into
  `ker proj_n`, since `ker proj_n` consists of the `n`-th powers);
* `reduceMu_bijective`: `μ_n(Ω) → μ_n(κ(A))` is bijective;
* `map_map_mk_eq_one_iff` (generic level-`n` criterion), `cobOn_transport_iff` and
  `cobOn_cocyclesMap_iff` (conjugation and transport combined, in the form used by `h1Congr`);
* **`restrictClosed_mk_eq_one_iff`**: `η|_x = 0` iff at every level `n` the cocycle of `η` is a
  coboundary modulo `n` on the image of the decomposition group `D_A → Π_U`;
* **`restrictClosed_h1Congr_eq_one_iff`**: if `e` maps the decomposition group of `x` onto a
  conjugate of that of `x'`, then `η|_x = 0` iff `(h1Congr e χ η)|_{x'} = 0`.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer IsLocalRing groupCohomology

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### Coboundaries on subsets, modulo a homomorphism -/

section CobOn

variable {P M N : Type*} [Group P] [CommGroup M] [MulDistribMulAction P M] [CommGroup N]

/-- On `S`, the function `c : P → M` agrees modulo `ker φ` with a coboundary. -/
def CobOn (φ : M →* N) (S : Set P) (c : P → M) : Prop :=
  ∃ z : M, ∀ g ∈ S, φ (g • z / z) = φ (c g)

lemma cobOn_mono (φ : M →* N) {S T : Set P} (hST : S ⊆ T) {c : P → M} (h : CobOn φ T c) :
    CobOn φ S c := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun g hg => hz g (hST hg)⟩

lemma cobOn_conj_of (φ : M →* N) (hφ : ∀ (g : P) (x : M), φ x = 1 → φ (g • x) = 1)
    {c : P → M} (hc : IsMulCocycle₁ c) (S : Set P) (a : P) (h : CobOn φ S c) :
    CobOn φ ((MulAut.conj a) '' S) c := by
  obtain ⟨z, hz⟩ := h
  refine ⟨a • z * (c a)⁻¹, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  rw [MulAut.conj_apply]
  have hinv : c a⁻¹ = (a⁻¹ • c a)⁻¹ := by
    have h1 := hc a⁻¹ a
    rw [inv_mul_cancel, map_one_of_isMulCocycle₁ hc] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have e1 : c (a * s * a⁻¹) = (a * s * a⁻¹) • (c a)⁻¹ * (a • c s * c a) := by
    rw [hc (a * s) a⁻¹, hc a s, hinv, smul_inv', smul_inv', ← mul_smul,
      show a * s * a⁻¹ = a * s * a⁻¹ from rfl]
  have e2 : (a * s * a⁻¹) • (a • z * (c a)⁻¹) = a • (s • z) * (a * s * a⁻¹) • (c a)⁻¹ := by
    rw [smul_mul', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
  have hkey : φ (a • c s) = φ (a • (s • z)) / φ (a • z) := by
    have h0 : φ (c s / (s • z / z)) = 1 := by rw [map_div, hz s hs, div_self']
    have h1 := hφ a _ h0
    rw [smul_div', smul_div', map_div, map_div, div_eq_one] at h1
    exact h1
  rw [e1, e2]
  simp only [map_mul, map_div, map_inv, hkey]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- For a cocycle `c` (and `ker φ` stable under `P`), `CobOn` is invariant under conjugation of
the subset. -/
lemma cobOn_conj_iff (φ : M →* N) (hφ : ∀ (g : P) (x : M), φ x = 1 → φ (g • x) = 1)
    {c : P → M} (hc : IsMulCocycle₁ c) (S : Set P) (a : P) :
    CobOn φ ((MulAut.conj a) '' S) c ↔ CobOn φ S c := by
  refine ⟨fun h => ?_, cobOn_conj_of φ hφ hc S a⟩
  refine cobOn_mono φ ?_ (cobOn_conj_of φ hφ hc _ a⁻¹ h)
  intro s hs
  refine ⟨MulAut.conj a s, ⟨s, hs, rfl⟩, ?_⟩
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

variable {P' M' N' : Type*} [Group P'] [CommGroup M'] [MulDistribMulAction P' M'] [CommGroup N']

/-- **`CobOn` along isomorphisms** `e : P ≃ P'`, `χ : M ≃ M'` (equivariant along `e`), if `χ`
matches `ker φ` with `ker φ'`. -/
lemma cobOn_map_iff (φ : M →* N) (φ' : M' →* N') (e : P ≃* P') (χ : M ≃* M')
    (hχ : ∀ p m, χ (p • m) = e p • χ m) (hker : ∀ x, φ' (χ x) = 1 ↔ φ x = 1) (S : Set P)
    (c : P → M) :
    CobOn φ' (e '' S) (fun g => χ (c (e.symm g))) ↔ CobOn φ S c := by
  have heq : ∀ x y, φ' (χ x) = φ' (χ y) ↔ φ x = φ y := fun x y => by
    rw [← div_eq_one, ← map_div, ← map_div, hker, map_div, div_eq_one]
  have hsm : ∀ g z, χ (g • z / z) = e g • χ z / χ z := fun g z => by
    rw [map_div, hχ]
  constructor
  · rintro ⟨z', hz'⟩
    refine ⟨χ.symm z', fun g hg => ?_⟩
    have h := hz' (e g) ⟨g, hg, rfl⟩
    simp only [MulEquiv.symm_apply_apply] at h
    rw [← heq, hsm, MulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨z, hz⟩
    refine ⟨χ z, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    simp only [MulEquiv.symm_apply_apply]
    rw [← hsm, heq]
    exact hz g hg

end CobOn

/-! ### `Ẑ(1)`: surjectivity of `proj_n` and its kernel -/

section ZHat

variable {K Ω : Type*} [Field K] [Field Ω]

/-- A root of order `k + 1` of a unit of an algebraically closed field. -/
lemma exists_unit_pow_succ_eq [IsAlgClosed Ω] (v : Ωˣ) (k : ℕ) : ∃ b : Ωˣ, b ^ (k + 1) = v := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (v : Ω) (Nat.succ_pos k)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero k)] at hz
    exact v.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

/-- A sequence of successive roots: `b₀ = v`, `b_{k+1}^{k+1} = b_k`. -/
def rootSeq [IsAlgClosed Ω] (v : Ωˣ) : ℕ → Ωˣ
  | 0 => v
  | k + 1 => Classical.choose (exists_unit_pow_succ_eq (rootSeq v k) k)

lemma rootSeq_zero [IsAlgClosed Ω] (v : Ωˣ) : rootSeq v 0 = v := rfl

lemma rootSeq_succ_pow [IsAlgClosed Ω] (v : Ωˣ) (k : ℕ) :
    rootSeq v (k + 1) ^ (k + 1) = rootSeq v k :=
  Classical.choose_spec (exists_unit_pow_succ_eq (rootSeq v k) k)

lemma rootSeq_pow_factorial [IsAlgClosed Ω] (v : Ωˣ) {k l : ℕ} (hkl : k ≤ l) (e : ℕ) :
    rootSeq v l ^ (e * (l.factorial / k.factorial)) = rootSeq v k ^ e := by
  induction l, hkl using Nat.le_induction with
  | base => rw [Nat.div_self (Nat.factorial_pos k), mul_one]
  | succ l hkl ih =>
    have hd : (l + 1).factorial / k.factorial = (l + 1) * (l.factorial / k.factorial) := by
      rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hkl)]
    rw [hd, show e * ((l + 1) * (l.factorial / k.factorial)) =
      (l + 1) * (e * (l.factorial / k.factorial)) by ring, pow_mul, rootSeq_succ_pow, ih]

lemma factorial_div_mul_eq (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    n * (b.factorial / b) * (b / a) = n * (a.factorial / a) * (b.factorial / a.factorial) := by
  have hle : a ≤ b := Nat.le_of_dvd hb hab
  rw [mul_assoc, mul_assoc, Nat.div_mul_div_comm (Nat.dvd_factorial hb le_rfl) hab,
    Nat.div_mul_div_comm (Nat.dvd_factorial ha le_rfl) (Nat.factorial_dvd_factorial hle),
    mul_comm b.factorial b, Nat.mul_div_mul_left _ _ hb, mul_comm a a.factorial,
    Nat.mul_div_mul_left _ _ (Nat.factorial_pos a)]

/-- **`proj_n : Ẑ(1) → μ_n` is surjective** (`Ω` algebraically closed): a compatible system of
roots of unity through a given `ζ ∈ μ_n` is built from successive roots of `ζ`. -/
theorem zHatOne_proj_surjective [IsAlgClosed Ω] (i : KummerIndex K) :
    Function.Surjective (ZHatOne.proj i : ZHatOne K Ω →* Mu i.n Ω) := by
  intro ζ
  have hpos : ∀ j : KummerIndex K, 0 < j.n := fun j => Nat.pos_of_ne_zero j.n_ne_zero
  have h0 : ∀ e : ℕ, ∀ l : ℕ, rootSeq (Mu.val ζ) l ^ (e * l.factorial) = Mu.val ζ ^ e :=
    fun e l => by
      have := rootSeq_pow_factorial (Mu.val ζ) (Nat.zero_le l) e
      rwa [Nat.factorial_zero, Nat.div_one, rootSeq_zero] at this
  have hpow : ∀ j : KummerIndex K,
      (rootSeq (Mu.val ζ) j.n ^ (i.n * (j.n.factorial / j.n))) ^ j.n = 1 := fun j => by
    rw [← pow_mul, mul_assoc, Nat.div_mul_cancel (Nat.dvd_factorial (hpos j) le_rfl), h0]
    exact Mu.val_pow_n ζ
  refine ⟨⟨fun j => Mu.mk _ (hpow j), fun j j' h => ?_⟩, ?_⟩
  · apply Mu.ext
    rw [Mu.val_transition, Mu.val_mk, Mu.val_mk, ← pow_mul,
      factorial_div_mul_eq i.n j.n j'.n (hpos j) (hpos j') (KummerIndex.le_def.1 h)]
    exact rootSeq_pow_factorial (Mu.val ζ)
      (Nat.le_of_dvd (hpos j') (KummerIndex.le_def.1 h)) _
  · apply Mu.ext
    change Mu.val (Mu.mk _ (hpow i)) = Mu.val ζ
    rw [Mu.val_mk, Nat.mul_div_cancel' (Nat.dvd_factorial (hpos i) le_rfl), ← one_mul i.n.factorial,
      h0, pow_one]

lemma proj_map_eq_one {K' Ω' : Type*} [Field K'] [Field Ω'] (χ : ZHatOne K Ω →* ZHatOne K' Ω')
    (i : KummerIndex K) (i' : KummerIndex K') (hi : i'.n = i.n) (x : ZHatOne K Ω)
    (hx : ZHatOne.proj i x = 1) : ZHatOne.proj i' (χ x) = 1 := by
  obtain ⟨y, rfl⟩ := CurvesJacobian.CuspCentral.ZHatOne.exists_pow_eq_of_proj_eq_one i x hx
  rw [map_pow, map_pow, ← hi]
  exact Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])

/-- An isomorphism `Ẑ(1) ≃ Ẑ(1)'` matches the kernels of `proj_n` (they consist of the `n`-th
powers). -/
lemma proj_map_eq_one_iff {K' Ω' : Type*} [Field K'] [Field Ω'] (χ : ZHatOne K Ω ≃* ZHatOne K' Ω')
    (i : KummerIndex K) (i' : KummerIndex K') (hi : i'.n = i.n) (x : ZHatOne K Ω) :
    ZHatOne.proj i' (χ x) = 1 ↔ ZHatOne.proj i x = 1 := by
  refine ⟨fun h => ?_, proj_map_eq_one χ.toMonoidHom i i' hi x⟩
  have := proj_map_eq_one χ.symm.toMonoidHom i' i hi.symm (χ x) h
  rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this

/-- `ker proj_n` is stable under any multiplicative action on `Ẑ(1)` (it consists of `n`-th
powers). -/
lemma proj_smul_eq_one {P : Type*} [Monoid P] [MulDistribMulAction P (ZHatOne K Ω)]
    (i : KummerIndex K) (g : P) (x : ZHatOne K Ω) (hx : ZHatOne.proj i x = 1) :
    ZHatOne.proj i (g • x) = 1 := by
  obtain ⟨y, rfl⟩ := CurvesJacobian.CuspCentral.ZHatOne.exists_pow_eq_of_proj_eq_one i x hx
  rw [smul_pow', map_pow]
  exact Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])

end ZHat

/-- The index `n` of `Ẑ(1)` over a field of characteristic `0`. -/
def kummerIndexOf {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : n ≠ 0) : KummerIndex K :=
  ⟨n, Nat.cast_ne_zero.2 hn⟩

/-- `CobOn` modulo `proj_n` is invariant under conjugation of the subset (for cocycles). -/
lemma cobOn_proj_conj_iff {K Ω P : Type*} [Field K] [Field Ω] [Group P]
    [MulDistribMulAction P (ZHatOne K Ω)] (i : KummerIndex K) {c : P → ZHatOne K Ω}
    (hc : IsMulCocycle₁ c) (S : Set P) (a : P) :
    CobOn (ZHatOne.proj i) ((MulAut.conj a) '' S) c ↔ CobOn (ZHatOne.proj i) S c :=
  cobOn_conj_iff _ (fun g x hx => proj_smul_eq_one i g x hx) hc S a

/-- **Transport of `CobOn` modulo `proj_n`** along `e : P ≃* P'` and an `e`-equivariant
`χ : Ẑ(1) ≃* Ẑ(1)'`, when `e(S)` is a conjugate of `S'` and `c' = χ ∘ c ∘ e⁻¹` is a cocycle. -/
lemma cobOn_transport_iff {K Ω K' Ω' P P' : Type*} [Field K] [Field Ω] [Field K'] [Field Ω']
    [Group P] [Group P'] [MulDistribMulAction P (ZHatOne K Ω)]
    [MulDistribMulAction P' (ZHatOne K' Ω')] (e : P ≃* P') (χ : ZHatOne K Ω ≃* ZHatOne K' Ω')
    (hχ : ∀ p z, χ (p • z) = e p • χ z) (S : Set P) (S' : Set P') (a : P')
    (hS : e '' S = (MulAut.conj a) '' S') (c : P → ZHatOne K Ω) (c' : P' → ZHatOne K' Ω')
    (hc' : IsMulCocycle₁ c') (hcc : ∀ g, c' g = χ (c (e.symm g))) (i : KummerIndex K)
    (i' : KummerIndex K') (hi : i'.n = i.n) :
    CobOn (ZHatOne.proj i') S' c' ↔ CobOn (ZHatOne.proj i) S c := by
  have hfun : c' = fun g => χ (c (e.symm g)) := funext hcc
  rw [← cobOn_proj_conj_iff i' hc' S' a, ← hS, hfun]
  exact cobOn_map_iff _ _ e χ hχ (fun x => proj_map_eq_one_iff χ i i' hi x) S c

/-! ### Reduction of roots of unity at a place -/

section Reduce

lemma muMap_injective' (n : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (muMap n K L) := by
  intro a b h
  apply Mu.ext
  apply Units.ext
  have := congrArg (fun z ↦ ((Mu.val z : Lˣ) : L)) h
  simp only [val_muMap, Units.coe_map, MonoidHom.coe_coe] at this
  exact (algebraMap K L).injective this

lemma muMap_surjective_of_surjective' (n : ℕ) {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hs : Function.Surjective (algebraMap K L)) : Function.Surjective (muMap n K L) := by
  intro m
  obtain ⟨z, hz⟩ := hs ((Mu.val m : Lˣ) : L)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact (Mu.val m).ne_zero hz.symm
  have hzn : (Units.mk0 z hz0) ^ n = 1 := by
    apply Units.ext
    apply (algebraMap K L).injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hz, Units.val_one, map_one,
      ← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  refine ⟨Mu.mk _ hzn, Mu.ext (Units.ext ?_)⟩
  simp [hz]

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω)
  (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]

include hk hkres in
/-- Reduction `μ_n(Ω) → μ_n(κ(A))` is bijective at a place `A ⊇ k` with `κ(A)` algebraic over
`k`. -/
theorem reduceMu_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (Decomposition.reduceMu A n (NeZero.ne n)) := by
  letI := kbarAlgebra A hk
  constructor
  · intro a b h
    obtain ⟨a₀, rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n a
    obtain ⟨b₀, rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n b
    rw [reduceMu_muMap A hk n, reduceMu_muMap A hk n] at h
    rw [muMap_injective' n (kbar k Ω) (ResidueField A) h]
  · intro m
    obtain ⟨m₀, rfl⟩ := muMap_surjective_of_surjective' n (K := kbar k Ω) (L := ResidueField A)
      (kbarResidue_surjective A hk hkres) m
    exact ⟨_, reduceMu_muMap A hk n m₀⟩

end Reduce

/-! ### Level-`n` restriction along a homomorphism -/

section Level

variable {H P Z μ ν : Type*} [Group H] [TopologicalSpace H] [Group P] [TopologicalSpace P]
  [CommGroup Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MulDistribMulAction P Z]
  [CommGroup μ] [TopologicalSpace μ] [IsTopologicalGroup μ] [MulDistribMulAction P μ]
  [CommGroup ν] [TopologicalSpace ν] [IsTopologicalGroup ν] [MulDistribMulAction H ν]

/-- The class of a cocycle `c`, pushed to `μ` along `p` and pulled back along `φ : H → P` with
coefficients reduced along a bijection `r : μ → ν`, vanishes iff `c` is a coboundary modulo
`ker p` on the image of `φ` (`p` surjective). -/
lemma map_map_mk_eq_one_iff (φ : H →* P) (hφ : Continuous φ) (r : μ →* ν) (hr : Continuous r)
    (hrc : ∀ h m, r (φ h • m) = h • r m) (p : Z →* μ) (hp : Continuous p)
    (hpc : ∀ (g : P) (x : Z), p (g • x) = g • p x) (hrb : Function.Bijective r)
    (hps : Function.Surjective p) (c : ContH1.cocycles P Z) :
    ContH1.map φ hφ r hr hrc
        (ContH1.map (MonoidHom.id P) continuous_id p hp (fun g x => hpc g x) (ContH1.mk c)) = 1 ↔
      CobOn p (Set.range φ) c := by
  rw [ContH1.map_mk, ContH1.map_mk, ContH1.mk_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨ζ, rfl⟩ := hrb.2 m
    obtain ⟨z, rfl⟩ := hps ζ
    refine ⟨z, ?_⟩
    rintro _ ⟨σ, rfl⟩
    apply hrb.1
    rw [map_div, map_div, hpc, hrc]
    exact hm σ
  · rintro ⟨z, hz⟩
    refine ⟨r (p z), fun σ => ?_⟩
    rw [← hrc, ← map_div, ← hpc, ← map_div, hz _ ⟨σ, rfl⟩]
    rfl

end Level

/-! ### Restriction to closed points -/

section Closed

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)] (hHL : D.HL = D.H) (ht : t ∈ A)

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (as in `restrictClosed`)
/-- **`η|_x = 0` via the decomposition group**: for a cocycle `c` of `Π_U` with values in `Ẑ(1)`,
the restriction of its class to the closed point below `A` vanishes iff at every level `n` the
cocycle `c` is a coboundary modulo `n` on the image of `D_A → Π_U`. -/
theorem restrictClosed_mk_eq_one_iff (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω)) :
    restrictClosed D A hk hkres hHL ht (ContH1.mk c) = 1 ↔
      ∀ i : KummerIndex (F D), CobOn (ZHatOne.proj i) (Set.range (decompToPi D A)) c := by
  rw [restrictClosed_eq_one_iff]
  refine forall_congr' fun i => ?_
  letI := Decomposition.muAction (F D) A hk hkres i.n
  exact map_map_mk_eq_one_iff (decompToPi D A) (continuous_decompToPi D A)
    (Decomposition.reduceMu A i.n (NeZero.ne i.n)) continuous_of_discreteTopology
    (reduceMu_decompToPi_smul D A hk hkres i.n) (ZHatOne.proj i) (ZHatOne.continuous_proj _)
    (fun g x => proj_pi_smul _ g x) (reduceMu_bijective A hk hkres i.n)
    (zHatOne_proj_surjective i) c

end Closed


section H1Congr

variable {P P' M M' : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]
  [Group P'] [TopologicalSpace P'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction P' M']

/-- A homomorphism out of `H¹(P', M')` kills `h1Congr e χ [c]` iff it kills `[χ ∘ c ∘ e⁻¹]`. -/
lemma map_h1Congr_mk_eq_one_iff {X : Type*} [Monoid X] (f : ContH1 P' M' →* X) (e : P ≃ₜ* P')
    (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m) (c : ContH1.cocycles P M) :
    f (h1Congr e χ hχ (ContH1.mk c)) = 1 ↔
      f (ContH1.mk (ContH1.cocyclesMap e.symm.toMulEquiv.toMonoidHom e.symm.continuous
        χ.toMulEquiv.toMonoidHom χ.continuous (h1Congr_comm e χ hχ) c)) = 1 :=
  Iff.rfl

end H1Congr

/-- `CobOn` along `h1Congr`-cocycles `χ ∘ c ∘ e⁻¹` (same syntactic form as in `h1Congr`). -/
lemma cobOn_cocyclesMap_iff {K Ω K' Ω' P P' : Type*} [Field K] [Field Ω] [Field K'] [Field Ω']
    [Group P] [TopologicalSpace P] [Group P'] [TopologicalSpace P']
    [MulDistribMulAction P (ZHatOne K Ω)] [MulDistribMulAction P' (ZHatOne K' Ω')]
    (e : P ≃ₜ* P') (χ : ZHatOne K Ω ≃ₜ* ZHatOne K' Ω') (hχ : ∀ p z, χ (p • z) = e p • χ z)
    (S : Set P) (S' : Set P') (a : P') (hS : e.toMulEquiv '' S = (MulAut.conj a) '' S')
    (c : ContH1.cocycles P (ZHatOne K Ω)) (i : KummerIndex K) (i' : KummerIndex K')
    (hi : i'.n = i.n) :
    CobOn (ZHatOne.proj i') S'
        (ContH1.cocyclesMap e.symm.toMulEquiv.toMonoidHom e.symm.continuous
          χ.toMulEquiv.toMonoidHom χ.continuous (h1Congr_comm e χ hχ) c) ↔
      CobOn (ZHatOne.proj i) S c :=
  cobOn_transport_iff e.toMulEquiv χ.toMulEquiv (fun p z => hχ p z) S S' a hS c.1 _
    (ContH1.isMulCocycle₁ _) (fun _ => rfl) i i' hi

/-! ### Along isomorphisms of Galois models -/

section Congr

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)] (hHL : D.HL = D.H) (ht : t ∈ A)
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [IsGalois (K₀ k' t') Ω'] [CharZero k'] [IsAlgClosed Ω']
  (A' : ValuationSubring Ω') (hk' : ∀ c : k', algebraMap k' Ω' c ∈ A')
  [Algebra k' (ResidueField A')]
  (hkres' : ∀ c : k', residue A' ⟨algebraMap k' Ω' c, hk' c⟩ = algebraMap k' (ResidueField A') c)
  [Algebra.IsIntegral k' (ResidueField A')] (hHL' : D'.HL = D'.H) (ht' : t' ∈ A')

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (as in `restrictClosed`)
/-- **Restriction to closed points along isomorphisms of Galois models**: let
`e : Π_U ≃ₜ* Π_{U'}` and `χ : Ẑ(1) ≃ₜ* Ẑ(1)'` be `e`-equivariant, and let `e` map the image of the
decomposition group `D_A → Π_U` of the closed point `x` below `A` onto a conjugate `M (·) M⁻¹` of
the image of `D_{A'} → Π_{U'}`. Then `η|_x = 0` iff `(h1Congr e χ η)|_{x'} = 0`. -/
theorem restrictClosed_h1Congr_eq_one_iff (e : Pi D ≃ₜ* Pi D')
    (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω') (hχ : ∀ p z, χ (p • z) = e p • χ z) (M : Pi D')
    (hdec : (decompToPi D A).range.map e.toMulEquiv.toMonoidHom =
      (decompToPi D' A').range.map (MulAut.conj M).toMonoidHom)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    restrictClosed D A hk hkres hHL ht η = 1 ↔
      restrictClosed D' A' hk' hkres' hHL' ht' (h1Congr e χ hχ η) = 1 := by
  haveI : CharZero (F D) := charZero_of_injective_algebraMap (algebraMap k (F D)).injective
  haveI : CharZero (F D') := charZero_of_injective_algebraMap (algebraMap k' (F D')).injective
  have hset : e.toMulEquiv '' Set.range (decompToPi D A) =
      (MulAut.conj M) '' Set.range (decompToPi D' A') :=
    congrArg (fun H : Subgroup (Pi D') => (H : Set (Pi D'))) hdec
  induction η using ContH1.induction_on with
  | h c =>
  refine (restrictClosed_mk_eq_one_iff D A hk hkres hHL ht c).trans (Iff.trans ?_
    ((restrictClosed_mk_eq_one_iff D' A' hk' hkres' hHL' ht' _).symm.trans
      (map_h1Congr_mk_eq_one_iff (restrictClosed D' A' hk' hkres' hHL' ht') e χ hχ c).symm))
  constructor
  · intro h i'
    exact (cobOn_cocyclesMap_iff e χ hχ _ _ M hset c (kummerIndexOf i'.n i'.n_ne_zero) i'
      rfl).2 (h _)
  · intro h i
    exact (cobOn_cocyclesMap_iff e χ hχ _ _ M hset c i (kummerIndexOf i.n i.n_ne_zero)
      rfl).1 (h _)

end Congr

end Iut.Reconstruction.Thm19
