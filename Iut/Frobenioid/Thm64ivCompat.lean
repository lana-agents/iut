/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm64ivGal

/-!
# [FrdI], Theorem 6.4(iv), last clause: compatibility with `F₁ ≅ F₂`

[FrdI], Theorem 6.4(iv) (l.5726–5735 of `~/iut-scratch/wall/txt/The Geometry of Frobenioids
I.txt`) ends: "the corresponding […] finite extension `L₂ ⊆ F̃₂` of `F₂` is isomorphic to `L₁` in a
fashion that is compatible with an isomorphism `F₁ ≅ F₂`". The proof in [FrdI] (l.5772–5795) shows
`L₁ ⊆ L₂` by Chebotarev and does not discuss the compatibility.

## Results

* `NormPrime K p`: `𝓞 K` has a prime of absolute norm `p` (invariant under ring isomorphisms,
  `normPrime_congr`).
* **`fieldRange_eq_of_normPrime`** (Bauer): for `K` Galois over `ℚ` and embeddings `σ_K, σ_L` into a
  field `Ω` of characteristic `0`, if almost every `p` with `NormPrime L p` has `NormPrime K p` and
  `[K:ℚ] = [L:ℚ]`, then `σ_K(K) = σ_L(L)`, **for every choice of the embeddings**.
* **`compat_of_normPrime`**: for `K_i → L_i` with `K₁`, `L₁` Galois over `ℚ` and the norm conditions
  at both levels, there are `φ : L₁ ≅ L₂` and `θ : K₁ ≅ K₂` with `φ ∘ ι₁ = ι₂ ∘ θ`.
* `GlobalRealified.normPrime_of_equiv`: an equivalence `C^⊩(K) ≌ C^⊩(L)` arising from
  `C(K) ≌ C(L)` transports `NormPrime` (`primeNorm_finMapZ`).
* **`GlobalRealified.thm64iv_compat`** (one-morphism base): for `K_i → L_i` and equivalences at both
  levels arising from the non-realified Frobenioids, with `K₁`, `L₁` Galois over `ℚ`, `L₁ ≅ L₂`
  compatibly with `K₁ ≅ K₂`.
* **`GlobalGaloisRlf.thm64iv_compat`** (Galois base): in the setting of `GlobalGaloisRlf.thm64iv`,
  `Ψ_Base(G₁/G₁) = G₂/G₂`, and if `L₁ = F̃₁^{H}` and `F₁` are Galois over `ℚ`, then
  `L₁ ≅ L₂ = F̃₂^{Ψ_Base(H)}` compatibly with an isomorphism `F₁ ≅ F₂` (the last clause of
  Theorem 6.4(iv) under the additional hypothesis that `F₁/ℚ` is Galois).

## Deviation: `F₁/ℚ` Galois

The clause is proved under the additional hypothesis that `F₁` is Galois over `ℚ`. Without it,
the data used here (the bijections of places at the levels `L` and `F`, preserving norms) do not
force `σ₁(F₁) = σ₂(F₂)` inside `σ₁(L₁) = σ₂(L₂)`: subfields of a Galois field with the same
splitting data need not be conjugate (arithmetically equivalent number fields). Whether every
`Ψ` forces the compatibility for non-Galois `F₁` is open here (recorded in `Plans/MR19Plan.md`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField IsDedekindDomain Arakelov Model

/-! ### Bauer's theorem for arbitrary embeddings -/

section Bauer

universe u v

/-- **`𝓞 K` has a prime of absolute norm `p`.** -/
def NormPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ P : HeightOneSpectrum (𝓞 K), Ideal.absNorm P.asIdeal = p

lemma NormPrime.congr {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K ≃+* K') {p : ℕ} (h : NormPrime K p) : NormPrime K' p := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_absNorm_eq (RingOfIntegers.mapRingEquiv e) P
  exact ⟨Q, hQ.trans hP⟩

lemma normPrime_congr {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K ≃+* K') (p : ℕ) : NormPrime K p ↔ NormPrime K' p :=
  ⟨NormPrime.congr e, NormPrime.congr e.symm⟩

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
  {Ω : Type v} [Field Ω] [CharZero Ω]

/-- The image of an embedding of a number field is a number field. -/
lemma numberField_fieldRange {M : Type*} [Field M] [NumberField M] (σ : M →ₐ[ℚ] Ω) :
    NumberField σ.fieldRange :=
  { to_finiteDimensional := (finiteDimensional_rat_iff _ _).mp
      (LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ).toLinearEquiv) }

lemma finrank_fieldRange {M : Type*} [Field M] [NumberField M] (σ : M →ₐ[ℚ] Ω) :
    Module.finrank ℚ σ.fieldRange = Module.finrank ℚ M :=
  (AlgEquiv.ofInjectiveField σ).toLinearEquiv.finrank_eq.symm

/-- **Bauer's theorem for arbitrary embeddings**: if `K` is Galois over `ℚ` and almost every
`p` with a prime of norm `p` in `L` has one in `K`, then `σ_K(K) ⊆ σ_L(L)`. -/
theorem fieldRange_le_of_normPrime [IsGalois ℚ K] (σK : K →ₐ[ℚ] Ω) (σL : L →ₐ[ℚ] Ω)
    (h : ∀ p : ℕ, p.Prime → NormPrime L p → NormPrime K p) : σK.fieldRange ≤ σL.fieldRange := by
  classical
  let eK : K ≃ₐ[ℚ] σK.fieldRange := AlgEquiv.ofInjectiveField σK
  let eL : L ≃ₐ[ℚ] σL.fieldRange := AlgEquiv.ofInjectiveField σL
  haveI := numberField_fieldRange σK
  haveI := numberField_fieldRange σL
  haveI : IsGalois ℚ σK.fieldRange := (isGalois_rat_iff _ _).mp (IsGalois.of_algEquiv eK)
  refine le_of_splitsCompletely σK.fieldRange σL.fieldRange
    ⟨(finite_setOf_dvd_discr K).toFinset, fun p hp hpS hL => ?_⟩
  obtain ⟨P, hP⟩ := h p hp (NormPrime.congr eL.symm.toRingEquiv hL)
  have := P.isPrime
  have hmem := mem_primesOver_of_absNorm_eq hp hP
  have hd : ¬ (p : ℤ) ∣ discr K := by simpa using hpS
  have hsplit : SplitsCompletely K p := splitsCompletely_of_isGalois hp _ hmem
    (ramificationIdx_eq_one_of_not_dvd_discr hp hd hmem)
    ((absNorm_eq_iff_inertiaDeg_eq_one hp hmem).mp hP)
  letI : Algebra σK.fieldRange K := eK.symm.toRingEquiv.toRingHom.toAlgebra
  exact SplitsCompletely.of_algebra (F := K) hsplit

/-- **`σ_K(K) = σ_L(L)`** under the hypotheses of `fieldRange_le_of_normPrime` and
`[K:ℚ] = [L:ℚ]`. -/
theorem fieldRange_eq_of_normPrime [IsGalois ℚ K] (σK : K →ₐ[ℚ] Ω) (σL : L →ₐ[ℚ] Ω)
    (h : ∀ p : ℕ, p.Prime → NormPrime L p → NormPrime K p)
    (hd : Module.finrank ℚ K = Module.finrank ℚ L) : σK.fieldRange = σL.fieldRange := by
  haveI := numberField_fieldRange σL
  exact IntermediateField.eq_of_le_of_finrank_eq (fieldRange_le_of_normPrime σK σL h)
    (by rw [finrank_fieldRange, finrank_fieldRange, hd])

end Bauer

section Compat

universe u

variable {K₁ L₁ K₂ L₂ : Type u} [Field K₁] [NumberField K₁] [Field L₁] [NumberField L₁]
  [Field K₂] [NumberField K₂] [Field L₂] [NumberField L₂] (ι₁ : K₁ →+* L₁) (ι₂ : K₂ →+* L₂)

/-- **Compatible isomorphisms from Bauer's theorem**: if `K₁`, `L₁` are Galois over `ℚ` and the
norm conditions hold at both levels, then `L₁ ≅ L₂` compatibly with some `K₁ ≅ K₂`, for **any**
embeddings `ι_i : K_i → L_i`. -/
theorem compat_of_normPrime [IsGalois ℚ K₁] [IsGalois ℚ L₁]
    (hL : ∀ p : ℕ, p.Prime → NormPrime L₂ p → NormPrime L₁ p)
    (hLd : Module.finrank ℚ L₁ = Module.finrank ℚ L₂)
    (hK : ∀ p : ℕ, p.Prime → NormPrime K₂ p → NormPrime K₁ p)
    (hKd : Module.finrank ℚ K₁ = Module.finrank ℚ K₂) :
    ∃ (φ : L₁ ≃+* L₂) (θ : K₁ ≃+* K₂), ∀ x, φ (ι₁ x) = ι₂ (θ x) := by
  classical
  let Ω := AlgebraicClosure ℚ
  let σL₁ : L₁ →ₐ[ℚ] Ω := IsAlgClosed.lift
  let σL₂ : L₂ →ₐ[ℚ] Ω := IsAlgClosed.lift
  let σK₁ : K₁ →ₐ[ℚ] Ω := σL₁.comp ι₁.toRatAlgHom
  let σK₂ : K₂ →ₐ[ℚ] Ω := σL₂.comp ι₂.toRatAlgHom
  have hLe : σL₁.fieldRange = σL₂.fieldRange := fieldRange_eq_of_normPrime σL₁ σL₂ hL hLd
  have hKe : σK₁.fieldRange = σK₂.fieldRange := fieldRange_eq_of_normPrime σK₁ σK₂ hK hKd
  let φ : L₁ ≃+* L₂ := ((AlgEquiv.ofInjectiveField σL₁).trans
    ((IntermediateField.equivOfEq hLe).trans (AlgEquiv.ofInjectiveField σL₂).symm)).toRingEquiv
  let θ : K₁ ≃+* K₂ := ((AlgEquiv.ofInjectiveField σK₁).trans
    ((IntermediateField.equivOfEq hKe).trans (AlgEquiv.ofInjectiveField σK₂).symm)).toRingEquiv
  have key : ∀ {M : Type u} [Field M] [NumberField M] (σ : M →ₐ[ℚ] Ω) (x : M),
      ((AlgEquiv.ofInjectiveField σ x : σ.fieldRange) : Ω) = σ x := fun _ _ => rfl
  have hφ : ∀ y, σL₂ (φ y) = σL₁ y := fun y => by
    change σL₂ ((AlgEquiv.ofInjectiveField σL₂).symm
      (IntermediateField.equivOfEq hLe (AlgEquiv.ofInjectiveField σL₁ y))) = _
    rw [← key σL₂, AlgEquiv.apply_symm_apply]
    rfl
  have hθ : ∀ x, σK₂ (θ x) = σK₁ x := fun x => by
    change σK₂ ((AlgEquiv.ofInjectiveField σK₂).symm
      (IntermediateField.equivOfEq hKe (AlgEquiv.ofInjectiveField σK₁ x))) = _
    rw [← key σK₂, AlgEquiv.apply_symm_apply]
    rfl
  refine ⟨φ, θ, fun x => σL₂.toRingHom.injective ?_⟩
  change σL₂ (φ (ι₁ x)) = σL₂ (ι₂ (θ x))
  rw [hφ]
  exact (hθ x).symm

end Compat

namespace GlobalRealified

universe u

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
  (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence]
  (Ψ : GlobalFrobenioid K ⥤ GlobalFrobenioid L) [Ψ.IsEquivalence]
  (e : GlobalFrobenioid.realify K ⋙ F ≅ Ψ ⋙ GlobalFrobenioid.realify L)

include Ψ e

/-- **Primes of norm `p` correspond** under an equivalence arising from `C(K) ≌ C(L)`. -/
theorem normPrime_of_equiv {p : ℕ} (h : NormPrime L p) : NormPrime K p := by
  obtain ⟨Q, hQ⟩ := h
  let w : FinitePlace L := FinitePlace.mk Q
  let v : FinitePlace K := finMapZ F.inv Ψ.inv (invCompatZ F Ψ e) w
  have hv : primeNorm v = p := by
    rw [primeNorm_finMapZ F.inv Ψ.inv (invCompatZ F Ψ e) w, primeNorm,
      FinitePlace.maximalIdeal_mk, hQ]
  refine ⟨v.maximalIdeal, ?_⟩
  have : ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) = (p : ℝ) := hv
  exact_mod_cast this

/-- **[FrdI], Theorem 6.4(iv), last clause, over the one-morphism base** (with `K/ℚ` Galois):
equivalences `C^⊩(K) ≌ C^⊩(L)` and `C^⊩(K') ≌ C^⊩(L')` arising from the non-realified
Frobenioids, with `K ⊆ K'`, `L ⊆ L'` (any embeddings `ι`, `ι'`) and `K'/ℚ` Galois, give `K' ≅ L'`
compatible with an isomorphism `K ≅ L`. -/
theorem thm64iv_compat {K' L' : Type u} [Field K'] [NumberField K'] [Field L'] [NumberField L']
    (ι : K →+* K') (ι' : L →+* L') [IsGalois ℚ K] [IsGalois ℚ K']
    (F' : GlobalRealified K' ⥤ GlobalRealified L') [F'.IsEquivalence]
    (Ψ' : GlobalFrobenioid K' ⥤ GlobalFrobenioid L') [Ψ'.IsEquivalence]
    (e' : GlobalFrobenioid.realify K' ⋙ F' ≅ Ψ' ⋙ GlobalFrobenioid.realify L') :
    ∃ (φ : K' ≃+* L') (θ : K ≃+* L), ∀ x, φ (ι x) = ι' (θ x) :=
  compat_of_normPrime ι ι' (fun _ _ => normPrime_of_equiv F' Ψ' e') (finrank_eq F' Ψ' e')
    (fun _ _ => normPrime_of_equiv F Ψ e) (finrank_eq F Ψ e)

end GlobalRealified


/-! ### Over the Galois base -/

section GaloisBase

variable {F E : Type} [Field F] [Field E] [Algebra F E]

instance subsingleton_quotient_topObj : Subsingleton (GalG F E ⧸ (topObj F E).H) :=
  QuotientGroup.subsingleton_quotient_top

/-- The morphism `A → G/G`. -/
def toTopObj (A : OrbitObj (GalG F E)) : A ⟶ topObj F E :=
  ⟨fun _ => QuotientGroup.mk 1, fun _ _ => Subsingleton.elim _ _⟩

/-- **An orbit object receiving a morphism from `G/G` is `G/G`** (its `H` has a `G`-fixed coset). -/
theorem eq_topObj_of_hom {A : OrbitObj (GalG F E)} (f : topObj F E ⟶ A) : A = topObj F E := by
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (f.toFun (QuotientGroup.mk 1))
  have hfix : ∀ g : GalG F E, g₀⁻¹ * g⁻¹ * g₀ ∈ A.H := by
    intro g
    have h1 : f.toFun (g • (QuotientGroup.mk 1 : GalG F E ⧸ (topObj F E).H)) =
        f.toFun (QuotientGroup.mk 1) :=
      congrArg f.toFun (Subsingleton.elim _ _)
    rw [f.map_smul, ← hg₀, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
    simpa [mul_inv_rev, mul_assoc] using h1
  have hH : A.H = ⊤ := by
    refine eq_top_iff.mpr fun h _ => ?_
    have := hfix (g₀ * h⁻¹ * g₀⁻¹)
    simpa [mul_inv_rev, mul_assoc] using this
  cases A
  simp only at hH
  subst hH
  rfl

/-- **An equivalence of bases maps `G₁/G₁` to `G₂/G₂`.** -/
theorem obj_topObj_eq {F₂ E₂ : Type} [Field F₂] [Field E₂] [Algebra F₂ E₂]
    (Gb : OrbitObj (GalG F E) ⥤ OrbitObj (GalG F₂ E₂)) [Gb.IsEquivalence] :
    Gb.obj (topObj F E) = topObj F₂ E₂ :=
  eq_topObj_of_hom ((Gb.objObjPreimageIso (topObj F₂ E₂)).inv ≫ Gb.map (toTopObj _))

end GaloisBase

lemma finrank_eq_of_ringEquiv {K K' : Type*} [Field K] [CharZero K] [Field K'] [CharZero K']
    (e : K ≃+* K') : Module.finrank ℚ K = Module.finrank ℚ K' :=
  (AlgEquiv.ofRingEquiv (f := e) (fun x => by simp)).toLinearEquiv.finrank_eq

section Final

variable {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [Algebra F₁ E₁] [IsGalois F₁ E₁]
variable {F₂ E₂ : Type} [Field F₂] [NumberField F₂] [Field E₂] [Algebra F₂ E₂] [IsGalois F₂ E₂]

/-- **[FrdI], Theorem 6.4(iv), last clause, over the Galois base** (with `F₁/ℚ` Galois). Let
`Ψ^rlf : C^rlf_{F̃₁/F₁} ≌ C^rlf_{F̃₂/F₂}` arise from `Ψ : C_{F̃₁/F₁} ≌ C_{F̃₂/F₂}`. Then `Ψ^rlf`
lies over an equivalence `Ψ_Base`, `Ψ_Base(G₁/G₁) = G₂/G₂`, and for every `A = G₁/H` with
`L₁ = F̃₁^H` Galois over `ℚ`, if `F₁` is Galois over `ℚ`, there are isomorphisms
`L₁ ≅ L₂ = F̃₂^{Ψ_Base(A)}` and `F₁ ≅ F₂` compatible with the inclusions `F_i ⊆ L_i`. -/
theorem GlobalGaloisRlf.thm64iv_compat (Ψr : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψr.IsEquivalence] (Ψ : GlobalGaloisFrob F₁ E₁ ⥤ GlobalGaloisFrob F₂ E₂) [Ψ.IsEquivalence]
    (e : GlobalGaloisFrob.realify F₁ E₁ ⋙ Ψr ≅ Ψ ⋙ GlobalGaloisFrob.realify F₂ E₂) :
    ∃ Gb : OrbitObj (GalG F₁ E₁) ⥤ OrbitObj (GalG F₂ E₂), Gb.IsEquivalence ∧
      Nonempty (Ψr ⋙ toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂) ⋙ Elem.proj ≅
        (toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁) ⋙ Elem.proj) ⋙ Gb) ∧
      Gb.obj (topObj F₁ E₁) = topObj F₂ E₂ ∧
      ∀ A : OrbitObj (GalG F₁ E₁), IsGalois ℚ (Fix A) → IsGalois ℚ F₁ →
        ∃ (φ : Fix A ≃+* Fix (Gb.obj A)) (θ : F₁ ≃+* F₂),
          ∀ x, φ (algebraMap F₁ (Fix A) x) = algebraMap F₂ (Fix (Gb.obj A)) (θ x) := by
  obtain ⟨Gb, hGb, hηr, hA⟩ := GlobalGaloisRlf.exists_fibreEquiv Ψr Ψ e
  have hTop : Gb.obj (topObj F₁ E₁) = topObj F₂ E₂ := obj_topObj_eq Gb
  refine ⟨Gb, hGb, hηr, hTop, fun A hL hK => ?_⟩
  obtain ⟨GA, _, ΨA, _, -, ⟨eA⟩⟩ := hA A
  obtain ⟨GT, _, ΨT, _, -, ⟨eT⟩⟩ := hA (topObj F₁ E₁)
  have hfix : Fix (Gb.obj (topObj F₁ E₁)) = Fix (topObj F₂ E₂) := by rw [hTop]
  let e₁ : F₁ ≃+* Fix (topObj F₁ E₁) := fixTopEquiv F₁ E₁
  let e₂ : F₂ ≃+* Fix (Gb.obj (topObj F₁ E₁)) :=
    (fixTopEquiv F₂ E₂).trans (IntermediateField.equivOfEq hfix.symm).toRingEquiv
  refine compat_of_normPrime (algebraMap F₁ (Fix A)) (algebraMap F₂ (Fix (Gb.obj A)))
    (fun _ _ => GlobalRealified.normPrime_of_equiv GA ΨA eA)
    (GlobalRealified.finrank_eq GA ΨA eA) (fun p _ h => ?_) ?_
  · exact NormPrime.congr e₁.symm
      (GlobalRealified.normPrime_of_equiv GT ΨT eT (NormPrime.congr e₂ h))
  · rw [finrank_eq_of_ringEquiv e₁, finrank_eq_of_ringEquiv e₂, GlobalRealified.finrank_eq GT ΨT eT]

end Final

end Frobenioid

end Iut
