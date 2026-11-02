/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.TateGalMero
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import TemperedFundamentalGroups.Tempered.GaloisSurjective

/-!
# The Galois part `σ : Π^tp_X → IsoAut t` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

The Tate action `tateGalDeck σ hσ` of `EllTate` takes its Galois part `σ : Π^tp_X →* IsoAut t`
as an explicit input. tempered-fundamental-groups provides `Π^tp_X → G_k = Gal(k̄/k)`
(`piToGk ∘ tempToPi`, `Tempered/GaloisSurjective.lean`). This file turns `G_k` into isometric
automorphisms of the complete algebraically closed field `K` of the analytic model, for `K` the
completion of `k̄` (`ι : k̄ →ₐ[k] K` with dense range) and `k` a complete nonarchimedean field:

* `norm_algHom_eq_spectralNorm`: every `k`-embedding `ψ : L → K` of an algebraic extension
  satisfies `‖ψ x‖ = spectralNorm k L x` (Mathlib `NormedAlgebra.norm_eq_spectralNorm` on
  `k(ψ x) ⊆ K`; the spectral norm only depends on the minimal polynomial);
  **`norm_algHom_algEquiv`**: `‖ψ (g x)‖ = ‖ψ x‖` for `g ∈ Aut(L/k)` (uniqueness of the extension
  of the norm of `k`);
* `isoExtHom ι hι τ hτ`, `isoExt`: an isometric automorphism `τ` of a field `L` with a dense
  embedding `ι : L → K` extends uniquely to an isometric automorphism of `K`
  (Mathlib `IsDenseInducing.extendRingHom` for the metric induced by `ι`); `isoExtGrp`: as a
  group homomorphism;
* **`galToIsoAut ι hι hq`** : `G_k →* IsoAut t` (`q ∈ k`), with `galToIsoAut_ι`
  (`σ(ι y) = ι(g y)`), `galToIsoAut_algebraMap` (it fixes `k`, so lies in `galL`);
* **`sigmaTemp`** : `Π^tp_X →* IsoAut t` (`galToIsoAut ∘ piToGk ∘ tempToPi`), fixing every
  `s ∈ k` (`sigmaTemp_fix`); **`tateGalDeckK`**, the Tate action with this Galois part, and
  **`galDeckHom_tateGalDeckK_dataRingHom`**: `Π^tp_X` acts trivially on the image of the
  coordinate ring of the `k`-curve of the Tate data `D` in `Mero K` (Galois part: it fixes `k`;
  deck part: the deck transformations fix `x(Ü²)`, `y(Ü²)`), and
  `galDeckHom_tateGalDeckK_kumM` (`g` acts on `√(x - e)` by the sign of `character₂ g`).

## Hypotheses (setup, not debts)

`k` carries a complete nonarchimedean norm and `K` is a normed `k`-algebra (the embedding
`k → K` is isometric); `ι : k̄ →ₐ[k] K` has dense range (`K` is the completion of `k̄`); `q` and `s`
lie in `k` (for `s = √q`: tfg's `DoubleData`, `F`-rational `2`-torsion point).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta Polynomial

universe u v

/-! ### Embeddings of algebraic extensions are isometric for the spectral norm -/

section Spectral

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {K : Type*} [NormedField K] [NormedAlgebra k K]
  {L : Type*} [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

/-- **`‖ψ x‖ = spectralNorm k L x`** for every `k`-embedding `ψ : L → K`. -/
theorem norm_algHom_eq_spectralNorm (ψ : L →ₐ[k] K) (x : L) : ‖ψ x‖ = spectralNorm k L x := by
  have hx : IsIntegral k (ψ x) := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral.map ψ
  let E := IntermediateField.adjoin k ({ψ x} : Set K)
  haveI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hx
  haveI : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.of_finite k E
  let y : E := ⟨ψ x, IntermediateField.mem_adjoin_simple_self k (ψ x)⟩
  have h1 : ‖ψ x‖ = ‖y‖ := rfl
  rw [h1, NormedAlgebra.norm_eq_spectralNorm k y]
  simp only [spectralNorm]
  have hy : minpoly k y = minpoly k x :=
    (IntermediateField.minpoly_eq y).trans (minpoly.algHom_eq ψ ψ.injective x)
  exact congrArg spectralValue hy

/-- **Automorphisms of `L/k` are isometric for every `k`-embedding `L → K`.** -/
theorem norm_algHom_algEquiv (ψ : L →ₐ[k] K) (g : L ≃ₐ[k] L) (x : L) : ‖ψ (g x)‖ = ‖ψ x‖ := by
  rw [norm_algHom_eq_spectralNorm, norm_algHom_eq_spectralNorm]
  simp only [spectralNorm]
  exact congrArg spectralValue (minpoly.algHom_eq (g : L →ₐ[k] L) g.injective x)

end Spectral

/-! ### Extension of isometric automorphisms to the completion -/

section Ext

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {L : Type*} [Field L] (ι : L →+* K) (hι : DenseRange ι)

/-- The metric on `L` induced by `ι`. -/
abbrev indMetric : PseudoMetricSpace L := PseudoMetricSpace.induced ι inferInstance

lemma isometry_ind : @Isometry L K (indMetric ι).toPseudoEMetricSpace _ ι :=
  @Isometry.of_dist_eq L K (indMetric ι) _ ι fun _ _ => rfl

lemma isometry_ind_comp (τ : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) :
    @Isometry L K (indMetric ι).toPseudoEMetricSpace _ (ι.comp τ) :=
  @Isometry.of_dist_eq L K (indMetric ι) _ (ι.comp τ) fun x y => by
    change dist (ι (τ x)) (ι (τ y)) = dist (ι x) (ι y)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, hτ, map_sub]

/-- **The extension of an isometric endomorphism `τ` of `L` to `K`** along the dense
`ι : L → K`. -/
def isoExtHom (τ : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) : K →+* K :=
  letI := indMetric ι
  IsDenseInducing.extendRingHom (isometry_ind ι).isUniformInducing hι
    (isometry_ind_comp ι τ hτ).uniformContinuous

variable {ι}

lemma isoExtHom_apply (τ : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) (a : L) :
    isoExtHom ι hι τ hτ (ι a) = ι (τ a) :=
  letI := indMetric ι
  IsDenseInducing.extend_eq ((isometry_ind ι).isUniformInducing.isDenseInducing hι)
    (isometry_ind_comp ι τ hτ).uniformContinuous.continuous a

lemma continuous_isoExtHom (τ : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) :
    Continuous (isoExtHom ι hι τ hτ) :=
  letI := indMetric ι
  (uniformContinuous_uniformly_extend (isometry_ind ι).isUniformInducing hι
    (isometry_ind_comp ι τ hτ).uniformContinuous).continuous

include hι in
/-- Two continuous maps `K → K` agreeing on `ι(L)` are equal. -/
lemma eq_of_dense {f g : K → K} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a : L, f (ι a) = g (ι a)) (x : K) : f x = g x :=
  DenseRange.induction_on hι x (isClosed_eq hf hg) h

lemma norm_isoExtHom (τ : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) (x : K) :
    ‖isoExtHom ι hι τ hτ x‖ = ‖x‖ :=
  DenseRange.induction_on hι x
    (isClosed_eq (continuous_norm.comp (continuous_isoExtHom hι τ hτ)) continuous_norm)
    fun a => by rw [isoExtHom_apply, hτ]

lemma isoExtHom_comp (τ τ' : L →+* L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖)
    (hτ' : ∀ x, ‖ι (τ' x)‖ = ‖ι x‖) (x : K) :
    isoExtHom ι hι τ hτ (isoExtHom ι hι τ' hτ' x) =
      isoExtHom ι hι (τ.comp τ') (fun y => by rw [RingHom.comp_apply, hτ, hτ']) x :=
  eq_of_dense hι ((continuous_isoExtHom hι τ hτ).comp (continuous_isoExtHom hι τ' hτ'))
    (continuous_isoExtHom hι _ _) (fun a => by
      simp only [Function.comp_apply, isoExtHom_apply, RingHom.comp_apply]) x

lemma isoExtHom_id (x : K) :
    isoExtHom ι hι (RingHom.id L) (fun _ => rfl) x = x :=
  eq_of_dense hι (continuous_isoExtHom hι _ _) continuous_id
    (fun a => by rw [isoExtHom_apply, RingHom.id_apply, id]) x

/-- **An isometric automorphism of `L` extends to an isometric automorphism of `K`.** -/
def isoExt (τ : RingAut L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) : RingAut K :=
  have hτ' : ∀ x, ‖ι (τ.symm x)‖ = ‖ι x‖ := fun x => by
    rw [← hτ (τ.symm x), RingEquiv.apply_symm_apply]
  RingEquiv.ofRingHom (isoExtHom ι hι τ.toRingHom hτ) (isoExtHom ι hι τ.symm.toRingHom hτ')
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, isoExtHom_comp, RingHom.id_apply]
      refine (eq_of_dense hι (continuous_isoExtHom hι _ _) continuous_id (fun a => ?_) x)
      rw [isoExtHom_apply, RingHom.comp_apply]
      simp)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, isoExtHom_comp, RingHom.id_apply]
      refine (eq_of_dense hι (continuous_isoExtHom hι _ _) continuous_id (fun a => ?_) x)
      rw [isoExtHom_apply, RingHom.comp_apply]
      simp)

lemma isoExt_apply (τ : RingAut L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) (a : L) :
    isoExt hι τ hτ (ι a) = ι (τ a) :=
  isoExtHom_apply hι τ.toRingHom hτ a

lemma continuous_isoExt (τ : RingAut L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) :
    Continuous (isoExt hι τ hτ) :=
  continuous_isoExtHom hι τ.toRingHom hτ

lemma norm_isoExt (τ : RingAut L) (hτ : ∀ x, ‖ι (τ x)‖ = ‖ι x‖) (x : K) :
    ‖isoExt hι τ hτ x‖ = ‖x‖ :=
  norm_isoExtHom hι τ.toRingHom hτ x

/-- **The extension as a group homomorphism** for a group acting on `L` by isometric
automorphisms. -/
def isoExtGrp {G : Type*} [Group G] (ρ : G →* RingAut L)
    (hρ : ∀ g x, ‖ι (ρ g x)‖ = ‖ι x‖) : G →* RingAut K where
  toFun g := isoExt hι (ρ g) (hρ g)
  map_one' := RingEquiv.ext fun x =>
    eq_of_dense hι (continuous_isoExt hι _ _) continuous_id (fun a => by
      rw [isoExt_apply, map_one, RingAut.one_apply]; rfl) x
  map_mul' g h := RingEquiv.ext fun x =>
    eq_of_dense hι (continuous_isoExt hι _ _)
      ((continuous_isoExt hι (ρ g) (hρ g)).comp (continuous_isoExt hι (ρ h) (hρ h))) (fun a => by
        rw [Function.comp_apply, isoExt_apply, isoExt_apply, isoExt_apply, map_mul,
          RingAut.mul_apply]) x

lemma isoExtGrp_apply {G : Type*} [Group G] (ρ : G →* RingAut L)
    (hρ : ∀ g x, ‖ι (ρ g x)‖ = ‖ι x‖) (g : G) (a : L) :
    isoExtGrp hι ρ hρ g (ι a) = ι (ρ g a) :=
  isoExt_apply hι (ρ g) (hρ g) a

lemma norm_isoExtGrp {G : Type*} [Group G] (ρ : G →* RingAut L)
    (hρ : ∀ g x, ‖ι (ρ g x)‖ = ‖ι x‖) (g : G) (x : K) :
    ‖isoExtGrp hι ρ hρ g x‖ = ‖x‖ :=
  norm_isoExt hι (ρ g) (hρ g) x

end Ext

/-! ### `G_k` acting on `K` -/

section Gal

open KummerTheory.Curve

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {Ω : Type u} [Field Ω] [Algebra k Ω]
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K]
  (ι : kbar k Ω →ₐ[k] K) (hι : DenseRange ι)

/-- `Aut(L/k) → Aut(L)` (forgetting `k`-linearity). -/
def autToRingAut (L : Type*) [Field L] [Algebra k L] : (L ≃ₐ[k] L) →* RingAut L where
  toFun g := g.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **`G_k` acting on `K`** by the isometric extensions of its elements. -/
def galToRingAut : Gk k Ω →* RingAut K :=
  isoExtGrp (ι := (ι : kbar k Ω →+* K)) hι (autToRingAut (kbar k Ω))
    (fun g x => norm_algHom_algEquiv ι g x)

variable {ι}

lemma galToRingAut_ι (g : Gk k Ω) (y : kbar k Ω) : galToRingAut ι hι g (ι y) = ι (g y) :=
  isoExtGrp_apply (ι := (ι : kbar k Ω →+* K)) hι _ _ g y

lemma norm_galToRingAut (g : Gk k Ω) (x : K) : ‖galToRingAut ι hι g x‖ = ‖x‖ :=
  norm_isoExtGrp (ι := (ι : kbar k Ω →+* K)) hι _ _ g x

/-- **`G_k` fixes `k ⊆ K`.** -/
lemma galToRingAut_algebraMap (g : Gk k Ω) (a : k) :
    galToRingAut ι hι g (algebraMap k K a) = algebraMap k K a := by
  rw [← ι.commutes a, galToRingAut_ι, AlgEquiv.commutes]

variable (t : TateParameter K)

/-- **`G_k →* IsoAut t`** when `q ∈ k`. -/
def galToIsoAut (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) : Gk k Ω →* IsoAut t :=
  (galToRingAut ι hι).codRestrict (IsoAut t) fun g =>
    ⟨norm_galToRingAut hι g, by
      obtain ⟨q₀, hq₀⟩ := hq
      rw [← hq₀]
      exact galToRingAut_algebraMap hι g q₀⟩

variable {t}

lemma galToIsoAut_apply (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : Gk k Ω) (x : K) :
    ((galToIsoAut hι t hq g : IsoAut t) : RingAut K) x = galToRingAut ι hι g x := rfl

lemma galToIsoAut_ι (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : Gk k Ω) (y : kbar k Ω) :
    ((galToIsoAut hι t hq g : IsoAut t) : RingAut K) (ι y) = ι (g y) :=
  galToRingAut_ι hι g y

lemma galToIsoAut_algebraMap (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : Gk k Ω) (a : k) :
    ((galToIsoAut hι t hq g : IsoAut t) : RingAut K) (algebraMap k K a) = algebraMap k K a :=
  galToRingAut_algebraMap hι g a

/-- The image of `G_k` lies in `Gal(K/k) = galL (algebraMap k K)`. -/
lemma galToIsoAut_mem_galL (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : Gk k Ω) :
    ((galToIsoAut hι t hq g : IsoAut t) : RingAut K) ∈ galL (algebraMap k K) :=
  ⟨(galToIsoAut hι t hq g).2.1, galToIsoAut_algebraMap hι hq g⟩

end Gal

/-! ### Deck transformations fix the `k`-curve of `D` -/

section DataDeck

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {F : Type u} [Field F] {O : ValuationSubring F} {R : Type u} [CommRing R]
  [Algebra F R]

/-- **Deck transformations fix the image of the coordinate ring of the `F`-curve of `D`.** -/
theorem scale_comp_dataRingHom (φ : F →+* K) (D : TemperedFundamentalGroups.TateObject.Data O R)
    (hT : IsTateParam φ D t) (h12 : (12 : K) ≠ 0) (c : Deck t) :
    (Mero.scale (c : Kˣ)).comp (dataRingHom t φ D hT h12) = dataRingHom t φ D hT h12 := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
  · change Mero.scale (c : Kˣ) (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (C a)))) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (C a)))
    rw [dataRingHom_mk_C, eval₂_C, RingHom.comp_apply, constHom_apply, Mero.scale_const]
  · change Mero.scale (c : Kˣ) (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ (C Polynomial.X))) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C Polynomial.X))
    rw [dataRingHom_mk_C, eval₂_X, scale_xM]
  · change Mero.scale (c : Kˣ) (dataRingHom t φ D hT h12
        (WeierstrassCurve.Affine.CoordinateRing.mk _ Polynomial.X)) =
      dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ Polynomial.X)
    rw [dataRingHom_y, scale_yM]

/-- **`GalDeck t` acts trivially on the `F`-curve of `D`** when its Galois part fixes `φ(F)`. -/
theorem galDeckHom_dataRingHom (φ : F →+* K) (D : TemperedFundamentalGroups.TateObject.Data O R)
    (hT : IsTateParam φ D t) (h12 : (12 : K) ≠ 0) (x : GalDeck t)
    (hx : ∀ a, ((x.right : IsoAut t) : RingAut K) (φ a) = φ a)
    (f : (dataCurve D).toAffine.CoordinateRing) :
    galDeckHom t x (dataRingHom t φ D hT h12 f) = dataRingHom t φ D hT h12 f := by
  rw [galDeckHom_apply, show Mero.gal x.right (dataRingHom t φ D hT h12 f) =
    dataRingHom t φ D hT h12 f from RingHom.congr_fun (gal_dataRingHom φ D hT h12 x.right hx) f]
  exact RingHom.congr_fun (scale_comp_dataRingHom φ D hT h12 x.left⁻¹) f

end DataDeck

/-! ### The Galois part `σ : Π^tp_X → IsoAut t` -/

section Pi

open CategoryTheory TemperedFundamentalGroups TemperedFundamentalGroups.Kummer
  TemperedFundamentalGroups.TateObject KummerTheory.Curve Pi1.Orbifold AffOrbicurve Iut.EtaleTheta

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {Ω : Type u} [Field Ω] [Algebra k Ω] {tΩ : Ω}
  (DG : Pi1.Orbifold.GaloisData k tΩ) [CharZero k] [IsGalois (K₀ k tΩ) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K] {ι : kbar k Ω →ₐ[k] K} (hι : DenseRange ι) {t : TateParameter K}

/-- **The Galois part `σ : Π^tp_X →* IsoAut t`**: `Π^tp_X → G_k` (tfg `piToGk ∘ tempToPi`)
followed by the isometric extension of `G_k` to `K` (`galToIsoAut`), for `q ∈ k`. -/
def sigmaTemp (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) : TempPi DG O V hV →* IsoAut t :=
  (galToIsoAut hι t hq).comp ((piToGk DG).comp (tempToPi DG O V hV))

variable {DG O V hV}

lemma sigmaTemp_ι (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : TempPi DG O V hV)
    (y : kbar k Ω) :
    ((sigmaTemp DG O V hV hι hq g : IsoAut t) : RingAut K) (ι y) =
      ι (piToGk DG (tempToPi DG O V hV g) y) :=
  galToIsoAut_ι hι hq _ y

/-- **`σ(g)` fixes `k ⊆ K`.** -/
lemma sigmaTemp_algebraMap (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q) (g : TempPi DG O V hV)
    (a : k) :
    ((sigmaTemp DG O V hV hι hq g : IsoAut t) : RingAut K) (algebraMap k K a) = algebraMap k K a :=
  galToIsoAut_algebraMap hι hq _ a

/-- **On a Galois element of the base point, `σ` is its restriction to `k̄`**: for `τ` in
the decomposition group of `V`, `σ(galoisToTempered τ)` maps `ι y` to `ι z` when `z = τ(y)`
in `Ω`. -/
lemma sigmaTemp_galoisToTempered (hq : ∃ q₀ : k, algebraMap k K q₀ = t.q)
    (τ : decompositionGroup DG.R V) {y z : kbar k Ω}
    (hyz : (z : Ω) = (τ : Ω ≃ₐ[DG.R] Ω) (y : Ω)) :
    ((sigmaTemp DG O V hV hι hq (galoisToTempered O DG.R DG.A hV τ) : IsoAut t) : RingAut K)
      (ι y) = ι z := by
  rw [sigmaTemp_ι]
  congr 1
  apply Subtype.ext
  change algebraMap (kbar k Ω) Ω (piToGk DG (tempToPi DG O V hV
    (galoisToTempered O DG.R DG.A hV τ)) y) = (z : Ω)
  rw [tempToPi_galoisToTempered, piToGk_mk, algebraMap_hToGk_apply, galoisToH_apply, hyz]

variable [IsReduced DG.R] [Subsingleton DG.A] (D : TateObject.DoubleData O DG.R) (sΩ : Ω)
  (hsΩ : sΩ ^ 2 = algebraMap DG.R Ω D.c)

lemma exists_q_of_s {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k} (hs₀ : algebraMap k K s₀ = s) :
    ∃ q₀ : k, algebraMap k K q₀ = t.q := ⟨s₀ ^ 2, by rw [map_pow, hs₀, hs]⟩

/-- **The Tate action of `Π^tp_X` on `Ÿ_∞ = 𝔾_m^an`** with the Galois part `sigmaTemp` (for
`s = √q ∈ k`): `g ↦ ⟨tateDeck g, σ(g)⟩ ∈ GalDeck t`. -/
def tateGalDeckK {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k} (hs₀ : algebraMap k K s₀ = s) :
    TempPi DG O V hV →* GalDeck t :=
  tateGalDeck V hV D sΩ hsΩ hs (sigmaTemp DG O V hV hι (exists_q_of_s hs hs₀)) fun g => by
    rw [← hs₀]; exact sigmaTemp_algebraMap hι _ g s₀

/-- **`Π^tp_X` acts trivially on the coordinate ring of the `k`-curve of `D`** (inside
`Mero K`) under the Tate action `tateGalDeckK`: its Galois part fixes `k`, its deck part fixes
`x(Ü²)`, `y(Ü²)`. -/
theorem galDeckHom_tateGalDeckK_dataRingHom {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) (hT : IsTateParam (algebraMap k K) D.toData t)
    (h12 : (12 : K) ≠ 0) (g : TempPi DG O V hV) (f : (dataCurve D.toData).toAffine.CoordinateRing) :
    galDeckHom t (tateGalDeckK hι D sΩ hsΩ hs hs₀ g)
        (dataRingHom t (algebraMap k K) D.toData hT h12 f) =
      dataRingHom t (algebraMap k K) D.toData hT h12 f :=
  galDeckHom_dataRingHom (algebraMap k K) D.toData hT h12 _ (fun a =>
    sigmaTemp_algebraMap hι (exists_q_of_s hs hs₀) g a) f

/-- **`g ∈ Π^tp_X` acts on `√(x - e)` by the sign of `character₂ g`** under `tateGalDeckK`. -/
theorem galDeckHom_tateGalDeckK_kumM {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) (g : TempPi DG O V hV) :
    galDeckHom t (tateGalDeckK hι D sΩ hsΩ hs hs₀ g) (kumM t s) =
      if (character₂ (A := DG.A) D V hV sΩ hsΩ g).2 = 1 then kumM t s else -kumM t s :=
  galDeckHom_tateGalDeck_kumM V hV D sΩ hsΩ hs _ _ g

/-- **`g ∈ Π^tp_X` acts on `K(E_t) ⊆ Mero K` by `σ(g)_*`** under `tateGalDeckK`. -/
theorem galDeckHom_tateGalDeckK_tateFieldHom (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) {s₀ : k} (hs₀ : algebraMap k K s₀ = s) (g : TempPi DG O V hV)
    (f : TateField t) :
    galDeckHom t (tateGalDeckK hι D sΩ hsΩ hs hs₀ g) (tateFieldHom t h12 f) =
      tateFieldHom t h12
        (tateFieldGal (sigmaTemp DG O V hV hι (exists_q_of_s hs hs₀) g) f) :=
  galDeckHom_tateGalDeck_tateFieldHom V hV D sΩ hsΩ h12 hs _ _ g f

/-- **A genuine Tate lift with the Galois part `sigmaTemp`** on the unramified layer
`RR = Mero K` (`isTateLift_gammaMero`; no Galois input left). -/
theorem isTateLift_gammaMeroK {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) :
    IsTateLift V hV D sΩ hsΩ hs (sigmaTemp DG O V hV hι (exists_q_of_s hs hs₀))
      (fun g => by rw [← hs₀]; exact sigmaTemp_algebraMap hι _ g s₀)
      (gammaMero V hV D sΩ hsΩ hs (sigmaTemp DG O V hV hι (exists_q_of_s hs hs₀))
        (fun g => by rw [← hs₀]; exact sigmaTemp_algebraMap hι _ g s₀)) :=
  isTateLift_gammaMero V hV D sΩ hsΩ hs _ _

end Pi

end Iut.Frobenioid.BAn
