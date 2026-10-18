/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm64iii

/-!
# [FrdI], Theorem 6.4(iv)

[FrdI], Theorem 6.4(iv) (l.6406–6419 of `~/iut-scratch/frd/FrdI.txt`): "If the equivalence of
categories `Ψ^rlf` of (ii) arises from an equivalence of categories `Ψ : C₁ ≅ C₂` between `C₁, C₂`
[…], then `deg(Ψ^rlf) = 1`. If, moreover, there exists a finite extension `L₁ ⊆ F̃₁` of `F₁` which
is Galois over `ℚ`, then the corresponding […] finite extension `L₂ ⊆ F̃₂` of `F₂` is isomorphic
to `L₁` in a fashion that is compatible with an isomorphism `F₁ ≅ F₂`."

Here, for the global Frobenioids over `Pt` (trivial Galois extensions, so `L_i = F_i`):
`F : C^⊩(K) ≌ C^⊩(L)`, `Ψ : C(K) ≌ C(L)` (the non-realified Frobenioids of [FrdI], Example 6.3,
`GlobalFrobenioid`) and `e : realify ⋙ F ≅ Ψ ⋙ realify` (`F` arises from `Ψ`).

* `psiPhi_castDiv_mem`: `Ψ_Φ(F)` maps divisors with integral finite part to such divisors (they
  are divisors of morphisms of `C`); hence `PreservesRatFin F` and Theorem 6.4(iii) applies
  (`thm64iii`: residue characteristics are preserved).
* **`psiPhi_single_eq`**: `Ψ_Φ([v]) = [w]` (the coefficient is a positive integer `n` with
  `n·m = 1`, `m` the integral coefficient for `F⁻¹`), so `deg(F)·log N(v) = log N(w)`.
* Counting places over a rational prime `p` (the bijection `V(K) ≅ V(L)` preserves `p`) and a
  prime splitting completely in `K` (`NumberField.infinite_setOf_splitsCompletely`, which replaces
  the use of Chebotarev's density theorem in [FrdI]): **`finrank_eq`** (`[K:ℚ] = [L:ℚ]`) and
  **`thm64iv_deg`** (`deg(F) = 1`).
* **`thm64iv_galois`**: if `K/ℚ` is Galois, then `K ≅ L` (Bauer's theorem
  `NumberField.le_of_splitsCompletely`, proved from Kronecker's density theorem, replaces the
  second use of Chebotarev).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

namespace GlobalFrobenioid

variable {K : Type u} [Field K] [NumberField K]

/-- The pre-step `(pt, 0) → (pt, z)` of `GlobalFrobenioid K`. -/
noncomputable def stepZ (z : ArithDivZ K) (hz : z ∈ effConeZ K) :
    (⟨pt, 0⟩ : GlobalFrobenioid K) ⟶ ⟨pt, z⟩ :=
  Model.mk1 (𝟙 _) z hz 0 (by
    change (0 : ArithDivZ K) + z = z + divZ K 0
    rw [map_zero, zero_add, add_zero])

end GlobalFrobenioid

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]

/-- **`Ψ_Φ` of an equivalence arising from `C ≌ C'` maps `ℤ`-divisors to `ℤ`-divisors.** -/
theorem psiPhi_castDiv_mem {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
    (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence]
    (Ψ : GlobalFrobenioid M ⥤ GlobalFrobenioid N)
    (e : GlobalFrobenioid.realify M ⋙ G ≅ Ψ ⋙ GlobalFrobenioid.realify N)
    (z : ArithDivZ M) (hz : z ∈ effConeZ M) :
    ∃ z' ∈ effConeZ N, psiPhi G (castDiv M z) (castDiv_mem_iff.mpr hz) = castDiv N z' := by
  let φ := GlobalFrobenioid.stepZ z hz
  have h1 : (G.map ((GlobalFrobenioid.realify M).map φ)).div =
      psiPhi G (castDiv M z) (castDiv_mem_iff.mpr hz) := div_map G _
  have hn := e.hom.naturality φ
  have hd := congrArg Model.Hom.div hn
  haveI : IsIso (e.hom.app ⟨pt, 0⟩) := inferInstance
  haveI : IsIso (e.hom.app ⟨pt, z⟩) := inferInstance
  rw [div_comp_iso, div_iso_comp] at hd
  refine ⟨(Ψ.map φ).div, (Ψ.map φ).div_mem, ?_⟩
  rw [← h1]
  exact hd

theorem preservesRatFin_of_nonRlf {M N : Type u} [Field M] [NumberField M] [Field N]
    [NumberField N] (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence]
    (Ψ : GlobalFrobenioid M ⥤ GlobalFrobenioid N)
    (e : GlobalFrobenioid.realify M ⋙ G ≅ Ψ ⋙ GlobalFrobenioid.realify N) :
    PreservesRatFin G := by
  intro z hz w
  obtain ⟨z', -, hz'⟩ := psiPhi_castDiv_mem G Ψ e z hz
  exact ⟨(z'.1 w : ℚ), by rw [hz', castDiv_fst, Rat.cast_intCast]⟩

/-- `e⁻¹`: if `F` arises from `Ψ`, then `F⁻¹` arises from `Ψ⁻¹`. -/
noncomputable def invCompatZ {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
    (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence]
    (Ψ : GlobalFrobenioid M ⥤ GlobalFrobenioid N) [Ψ.IsEquivalence]
    (e : GlobalFrobenioid.realify M ⋙ G ≅ Ψ ⋙ GlobalFrobenioid.realify N) :
    GlobalFrobenioid.realify N ⋙ G.inv ≅ Ψ.inv ⋙ GlobalFrobenioid.realify M :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight Ψ.asEquivalence.counitIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Ψ.inv ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.symm G.inv ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (GlobalFrobenioid.realify M) G.asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- The coefficients of `Ψ_Φ([v])` at finite places are integers. -/
lemma exists_int_coord {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
    (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence]
    (Ψ : GlobalFrobenioid M ⥤ GlobalFrobenioid N)
    (e : GlobalFrobenioid.realify M ⋙ G ≅ Ψ ⋙ GlobalFrobenioid.realify N)
    (v : FinitePlace M) (w : FinitePlace N) :
    ∃ n : ℤ, coord (psiPhi G (single (Sum.inl v) 1) (single_mem zero_le_one)) (Sum.inl w) = n := by
  obtain ⟨z', -, hz'⟩ := psiPhi_castDiv_mem G Ψ e (oneZ v) (oneZ_mem v)
  refine ⟨z'.1 w, ?_⟩
  rw [psiPhi_congr G _ (castDiv_mem_iff.mpr (oneZ_mem v)) (castDiv_oneZ v).symm, hz', coord_inl,
    castDiv_fst]

lemma degArith_single_inl {P : Type u} [Field P] [NumberField P] (x : FinitePlace P) (r : ℝ) :
    degArith P (single (Sum.inl x) r) = r * Real.log (primeNorm x) := by
  rw [degArith_apply]
  simp [single, Finsupp.sum_single_index]

/-! ### Counting places over a rational prime -/

/-- The finite places over the rational prime `p`. -/
def fiber (P : Type u) [Field P] [NumberField P] (p : ℕ) : Set (FinitePlace P) :=
  {v | resChar v = p}

lemma fiber_finite (P : Type u) [Field P] [NumberField P] (p : ℕ) : (fiber P p).Finite := by
  have := finite_resChar_mem (M := P) {p}
  simpa [fiber] using this

lemma mem_primesOver_iff {P : Type u} [Field P] [NumberField P] {p : ℕ} (v : FinitePlace P) :
    v.maximalIdeal.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 P) ↔ resChar v = p := by
  have hprime := v.maximalIdeal.isPrime
  constructor
  · rintro ⟨-, hl⟩
    have h := hl.over
    rw [resChar, ← h, Ideal.absNorm_span_singleton]
    simp
  · intro h
    refine ⟨hprime, ⟨?_⟩⟩
    rw [← Int.ideal_span_absNorm_eq_self (v.maximalIdeal.asIdeal.under ℤ)]
    change Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((resChar v : ℕ) : ℤ)}
    rw [h]

/-- **`#{v | v ∣ p} = #primesOver(p)`.** -/
lemma ncard_fiber {P : Type u} [Field P] [NumberField P] {p : ℕ} (hp : p.Prime) :
    (fiber P p).ncard = ((Ideal.span {(p : ℤ)}).primesOver (𝓞 P)).ncard := by
  have hinj : Function.Injective fun v : FinitePlace P => v.maximalIdeal.asIdeal := fun v v' h =>
    FinitePlace.equivHeightOneSpectrum.injective (IsDedekindDomain.HeightOneSpectrum.ext h)
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext Q
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_primesOver_iff v).mpr hv
  · intro hQ
    have hQp : Q.IsPrime := hQ.1
    have hne : Q ≠ ⊥ := by
      intro h0
      have h := hQ.2.over
      rw [h0, Ideal.under_bot] at h
      exact span_natCast_ne_bot hp h
    let Q' : IsDedekindDomain.HeightOneSpectrum (𝓞 P) := ⟨Q, hQp, hne⟩
    refine ⟨FinitePlace.mk Q', ?_, by simp [FinitePlace.maximalIdeal_mk, Q']⟩
    have := (mem_primesOver_iff (FinitePlace.mk Q')).mp (by
      simpa [FinitePlace.maximalIdeal_mk, Q'] using hQ)
    exact this

section Deg

variable {M N : Type u} [Field M] [NumberField M] [Field N] [NumberField N]
  (G : GlobalRealified M ⥤ GlobalRealified N) [G.IsEquivalence]
  (Ψ : GlobalFrobenioid M ⥤ GlobalFrobenioid N) [Ψ.IsEquivalence]
  (e : GlobalFrobenioid.realify M ⋙ G ≅ Ψ ⋙ GlobalFrobenioid.realify N)

include Ψ e

/-- `PreservesRatFin G⁻¹`. -/
lemma preservesRatFin_inv : PreservesRatFin G.inv :=
  preservesRatFin_of_nonRlf G.inv Ψ.inv (invCompatZ G Ψ e)

/-- **The finite place `Ψ_Prime(v)`** for an equivalence arising from `C ≌ C'`. -/
noncomputable abbrev finMapZ (v : FinitePlace M) : FinitePlace N :=
  finMap G (preservesRatFin_inv G Ψ e) v

lemma placeEquiv_finMapZ (v : FinitePlace M) :
    placeEquiv G (Sum.inl v) = Sum.inl (finMapZ G Ψ e v) :=
  placeEquiv_finMap G _ v

/-- **Residue characteristics are preserved** (Theorem 6.4(iii)). -/
lemma resChar_finMapZ (v : FinitePlace M) : resChar (finMapZ G Ψ e v) = resChar v :=
  (thm64iii G (preservesRatFin_of_nonRlf G Ψ e) (preservesRatFin_inv G Ψ e)).2 v

lemma finMapZ_injective : Function.Injective (finMapZ G Ψ e) := finMap_injective G _

/-- **`Ψ_Φ([v]) = [w]`**: the coefficient of `Ψ_Φ([v])` at `w = Ψ_Prime(v)` is `1`. -/
theorem coord_psiPhi_eq_one (v : FinitePlace M) :
    coord (psiPhi G (single (Sum.inl v) 1) (single_mem zero_le_one))
      (Sum.inl (finMapZ G Ψ e v)) = 1 := by
  have hsupp := supp_psiPhi_one G (Sum.inl v)
  rw [placeEquiv_finMapZ G Ψ e v] at hsupp
  have hsingle := eq_single_of_supp hsupp
  obtain ⟨n, hn⟩ := exists_int_coord G Ψ e v (finMapZ G Ψ e v)
  have hpos := coord_psiPhi_pos G (Sum.inl v)
  rw [placeEquiv_finMapZ G Ψ e v, hn] at hpos
  have hn0 : 0 < n := by exact_mod_cast hpos
  rw [hn] at hsingle ⊢
  have hnat : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0.le
  obtain ⟨m, hm⟩ := exists_int_coord G.inv Ψ.inv (invCompatZ G Ψ e) (finMapZ G Ψ e v) v
  have hinv := psiPhi_inv_psiPhi G (single (Sum.inl v) 1) (single_mem zero_le_one)
  have hsm : psiPhi G (single (Sum.inl v) 1) (single_mem zero_le_one) =
      n.toNat • single (Sum.inl (finMapZ G Ψ e v)) 1 := by
    rw [hsingle]
    refine eq_iff_coord.mpr fun q => ?_
    rw [coord_nsmul, coord_single, coord_single, hnat]
    split_ifs <;> simp
  rw [psiPhi_congr G.inv _ ((effCone N).nsmul_mem (single_mem zero_le_one) _) hsm,
    psiPhi_nsmul G.inv _ (single_mem zero_le_one)] at hinv
  have h1 := congrArg (fun x => coord x (Sum.inl v)) hinv
  simp only [coord_nsmul, coord_single, hm, hnat, ite_true] at h1
  have h2 : n * m = 1 := by exact_mod_cast h1
  rw [Int.eq_one_of_mul_eq_one_right hn0.le h2, Int.cast_one]

/-- **`deg(F)·log N(v) = log N(Ψ_Prime(v))`.** -/
theorem degOf_mul_log (v : FinitePlace M) :
    degOf G * Real.log (primeNorm v) = Real.log (primeNorm (finMapZ G Ψ e v)) := by
  have hsupp := supp_psiPhi_one G (Sum.inl v)
  rw [placeEquiv_finMapZ G Ψ e v] at hsupp
  have hsingle := eq_single_of_supp hsupp
  rw [coord_psiPhi_eq_one G Ψ e v] at hsingle
  have hdeg := degArith_psiPhi G (single (Sum.inl v) 1) (single_mem zero_le_one)
  rw [hsingle, degArith_single_inl, degArith_single_inl, one_mul, one_mul] at hdeg
  exact hdeg.symm

/-- **`#{v ∣ p in M} ≤ #{w ∣ p in N}`**: `Ψ_Prime` maps the fibre over `p` injectively. -/
lemma ncard_fiber_le (p : ℕ) : (fiber M p).ncard ≤ (fiber N p).ncard :=
  Set.ncard_le_ncard_of_injOn (finMapZ G Ψ e)
    (fun v hv => by
      change resChar _ = p
      rw [resChar_finMapZ]
      exact hv)
    (finMapZ_injective G Ψ e).injOn (fiber_finite N p)

lemma finrank_le_of_splits {p : ℕ} (h : SplitsCompletely M p) :
    Module.finrank ℚ M ≤ (fiber N p).ncard := by
  rw [← h.ncard_primesOver, ← ncard_fiber h.prime]
  exact ncard_fiber_le G Ψ e p

/-- `[M:ℚ] ≤ [N:ℚ]`. -/
lemma finrank_le : Module.finrank ℚ M ≤ Module.finrank ℚ N := by
  obtain ⟨p, -, hp⟩ := (infinite_setOf_splitsCompletely M).nonempty
  refine (finrank_le_of_splits G Ψ e hp).trans ?_
  rw [ncard_fiber hp.prime]
  exact ncard_primesOver_le_finrank hp.prime

end Deg

variable (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence]
  (Ψ : GlobalFrobenioid K ⥤ GlobalFrobenioid L) [Ψ.IsEquivalence]
  (e : GlobalFrobenioid.realify K ⋙ F ≅ Ψ ⋙ GlobalFrobenioid.realify L)

include Ψ e

/-- **`[K:ℚ] = [L:ℚ]`** for an equivalence arising from `C(K) ≌ C(L)`. -/
theorem finrank_eq : Module.finrank ℚ K = Module.finrank ℚ L :=
  le_antisymm (finrank_le F Ψ e) (finrank_le F.inv Ψ.inv (invCompatZ F Ψ e))

/-- **A prime splitting completely in `K` splits completely in `L`.** -/
theorem splitsCompletely_of_splitsCompletely {p : ℕ} (h : SplitsCompletely K p) :
    SplitsCompletely L p := by
  rw [← ncard_primesOver_eq_finrank_iff h.prime, ← ncard_fiber h.prime]
  refine le_antisymm ?_ ?_
  · rw [ncard_fiber h.prime]
    exact ncard_primesOver_le_finrank h.prime
  · rw [← finrank_eq F Ψ e]
    exact finrank_le_of_splits F Ψ e h

/-- **[FrdI], Theorem 6.4(iv), first part: `deg(F) = 1`.** -/
theorem thm64iv_deg : degOf F = 1 := by
  obtain ⟨p, -, hp⟩ := (infinite_setOf_splitsCompletely K).nonempty
  have hpL := splitsCompletely_of_splitsCompletely F Ψ e hp
  -- a place `v ∣ p`
  have hne : (fiber K p).Nonempty := by
    rw [← Set.ncard_pos (fiber_finite K p), ncard_fiber hp.prime, hp.ncard_primesOver]
    exact Module.finrank_pos
  obtain ⟨v, hv⟩ := hne
  have hnorm : ∀ {P : Type u} [Field P] [NumberField P], SplitsCompletely P p →
      ∀ x : FinitePlace P, resChar x = p → primeNorm x = p := by
    intro P _ _ hs x hx
    have hmem := (mem_primesOver_iff x).mpr hx
    have h1 := (hs.2 _ hmem).2
    have := (absNorm_eq_iff_inertiaDeg_eq_one hs.prime hmem).mpr h1
    rw [primeNorm, this]
  have h := degOf_mul_log F Ψ e v
  rw [hnorm hp v hv, hnorm hpL _ ((resChar_finMapZ F Ψ e v).trans hv)] at h
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.prime.one_lt)).ne'
  have := mul_right_cancel₀ hl (h.trans (one_mul _).symm)
  exact this

/-- **`N(Ψ_Prime(v)) = N(v)`** (degree-one places correspond). -/
theorem primeNorm_finMapZ (v : FinitePlace K) : primeNorm (finMapZ F Ψ e v) = primeNorm v := by
  have h := degOf_mul_log F Ψ e v
  rw [thm64iv_deg F Ψ e, one_mul] at h
  exact Real.log_injOn_pos (Set.mem_Ioi.2 (primeNorm_pos _)) (Set.mem_Ioi.2 (primeNorm_pos _))
    h.symm

/-- **[FrdI], Theorem 6.4(iv), second part**: if `K` is Galois over `ℚ`, then `L ≅ K`.

Proof (as in [FrdI], with Chebotarev replaced by Bauer's theorem
`NumberField.le_of_splitsCompletely`): embed `K`, `L` into `ℚ̄`. If `p ∤ disc(K)` and `L` has a
prime of norm `p`, then so does `K` (`primeNorm_finMapZ` for `F⁻¹`), hence `p` splits completely in
the Galois field `K`; by Bauer `K ⊆ L` inside `ℚ̄`, and `[K:ℚ] = [L:ℚ]` (`finrank_eq`). -/
theorem thm64iv_galois [IsGalois ℚ K] : Nonempty (K ≃+* L) := by
  classical
  let σK : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let σL : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := σK.fieldRange
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := σL.fieldRange
  let eK : K ≃ₐ[ℚ] K' := AlgEquiv.ofInjectiveField σK
  let eL : L ≃ₐ[ℚ] L' := AlgEquiv.ofInjectiveField σL
  have : NumberField K' :=
    { to_finiteDimensional := (finiteDimensional_rat_iff _ _).mp
        (LinearEquiv.finiteDimensional eK.toLinearEquiv) }
  have : NumberField L' :=
    { to_finiteDimensional := (finiteDimensional_rat_iff _ _).mp
        (LinearEquiv.finiteDimensional eL.toLinearEquiv) }
  have : IsGalois ℚ K' := (isGalois_rat_iff _ _).mp (IsGalois.of_algEquiv eK)
  have hle : K' ≤ L' := by
    refine le_of_splitsCompletely K' L' ⟨(finite_setOf_dvd_discr K).toFinset,
      fun p hp hpS ⟨P, hP⟩ => ?_⟩
    obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_absNorm_eq
      (RingOfIntegers.mapRingEquiv eL.symm.toRingEquiv) P
    let w : FinitePlace L := FinitePlace.mk Q
    let v : FinitePlace K := finMapZ F.inv Ψ.inv (invCompatZ F Ψ e) w
    have hv : primeNorm v = p := by
      rw [primeNorm_finMapZ F.inv Ψ.inv (invCompatZ F Ψ e) w, primeNorm,
        FinitePlace.maximalIdeal_mk, hQ, hP]
    have habs : Ideal.absNorm v.maximalIdeal.asIdeal = p := by
      have : ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) = (p : ℝ) := hv
      exact_mod_cast this
    have := v.maximalIdeal.isPrime
    have hmem := mem_primesOver_of_absNorm_eq hp habs
    have hd : ¬ (p : ℤ) ∣ discr K := by simpa using hpS
    have hsplit : SplitsCompletely K p := splitsCompletely_of_isGalois hp _ hmem
      (ramificationIdx_eq_one_of_not_dvd_discr hp hd hmem)
      ((absNorm_eq_iff_inertiaDeg_eq_one hp hmem).mp habs)
    letI : Algebra K' K := eK.symm.toRingEquiv.toRingHom.toAlgebra
    exact SplitsCompletely.of_algebra (F := K) hsplit
  let φ : K →+* L := (eL.symm.toRingEquiv.toRingHom).comp
    ((IntermediateField.inclusion hle).toRingHom.comp eK.toRingEquiv.toRingHom)
  let ψ : K →ₐ[ℚ] L := φ.toRatAlgHom
  have hinj : Function.Injective ψ.toLinearMap := ψ.toRingHom.injective
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_eq F Ψ e)).mp hinj
  exact ⟨RingEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end GlobalRealified

end Frobenioid

end Iut
