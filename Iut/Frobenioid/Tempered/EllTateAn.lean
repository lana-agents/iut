/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.TateMero
import Iut.Frobenioid.Tempered.EllTate

/-!
# The analytic–schematic comparison for the Tate curve on `X'` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

tempered-fundamental-groups (tfg) builds `Ÿ → X` from Tate data `D` (`TateObjectDouble`): the
`ℤ`-covering `Y` of the special fibre and the Kummer covering `X' = Spec R[√c]`, `c = x - e`,
`e` the `x`-coordinate of the `2`-torsion point `√q`; its character
`character₂ : Π^tp_X → ℤ × ℤ/2` records how `g` moves the base point of the fibre of `Ÿ`, the
`ℤ/2`-part being the action on the fibre `{±√c}` of `X'`. `EllTate.tateDeck` *defines* the deck
part `Π^tp_X → Deck t` by `(n, ε) ↦ (-1)^ε s^{-n}`. Here the comparison with the analytic model
`Ÿ_∞ = 𝔾_m^an` (`Mero K`) is **proved on the function field of `X'`**:

* `scale_comp_tateFieldHom`: every deck transformation `Ü ↦ c·Ü`, `c ∈ Deck t`, fixes the image
  of `K(E_t)` (`TateMero.tateFieldHom`: `x ↦ x(Ü²)`, `y ↦ y(Ü²)`).
* **`deckHom_tateDeck_kumM`**: `g ∈ Π^tp_X` acts through `tateDeck` on the analytic Kummer
  function `√(x - e)` (`TateMero.kumM`) by the sign `(-1)^ε`, `ε` the `ℤ/2`-part of
  `character₂ g`, i.e. exactly as `g` acts on `B(X') = R[√c]` in tfg (`deck₂`, `σPow`);
  `deckHom_tateDeck_tateFieldHom`: it fixes `K(E_t)`.
* **`galois_kummer`**: for `σ` in the decomposition group of `V` (`galoisToTempered`), the analytic
  deck transformation `tateDeck σ` moves `√(x - e)` exactly as `σ` moves `√c ∈ Ω`
  (`character₂_galois` of tfg and its companion `character₂_galois_fix` proved here).
* `dataRingHom φ D t hT`: the coordinate ring of the curve of `D` maps to `Mero K` when `t` is the
  Tate parameter of `D` (`IsTateParam`); `dataToR D`: it maps to `R` (`x ↦ D.x`, `y ↦ D.y`);
  with `e = φ(e₀) = X(s)` (`dataToR_c`, `dataRingHom_c`) the Kummer parameter `c = x - e₀` goes
  to `D.c` and to `β·√(x - e)²`.
* **`gammaMero σ hσ`**: a genuine `γ : Π^tp_X →* ExtGalDeck t (Mero K)` with
  `IsTateLift` (`isTateLift_gammaMero`), on the unramified layer `RR = Mero K`.

## What is not proved

* The `ℤ`-part of `tateDeck` acts trivially on `X'` (as it must, `X'` being finite over `X`);
  its sign `-χ` is the convention matching tfg's sheet orientation with Tate's `U` ([EtTh] fixes
  `Π^tp_X ↠ ℤ` only up to `Aut(ℤ) = {±1}`, l.445–447). The comparison of *all* tempered coverings
  (André's analytic `π₁^tp` of `E_t` with tfg's schematic `Π^tp_X`) is not formalised, so
  `tateDeck` remains a definition beyond `X'`.
* The Galois part `σ : Π^tp_X → IsoAut t` is a parameter here; `TateGalSigma.sigmaTemp`
  constructs it from tfg's `Π^tp_X → G_k` (`piToGk ∘ tempToPi`) for `K` the completion of `k̄`,
  and `TateGalMero` proves its compatibility with `K(E_t) ⊆ Mero K` (`gal_comp_tateFieldHom`).
* For `RR` an algebraic closure of `Mero K` no `γ` through `ℤ × ℤ/2` exists (`EllTate`); a
  genuine one needs the full comparison.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta TemperedFundamentalGroups TemperedFundamentalGroups.TateObject
open Polynomial Iut.EtaleTheta Pi1.Orbifold

universe u

/-! ### Deck transformations on `K(E_t)` and on `√(x - e)` -/

section Deck

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

lemma Mero.scale_const (c : Kˣ) (a : K) : Mero.scale c (Mero.const a) = Mero.const a := by
  rw [Mero.scale_ofE]
  exact congrArg Mero.ofE (Entire.ext_apply fun u => by rw [Entire.coe_scale]; rfl)

/-- **Deck transformations fix `K(E_t)`.** -/
theorem scale_comp_tateFieldHom (h12 : (12 : K) ≠ 0) (c : Deck t) :
    (Mero.scale (c : Kˣ)).comp (tateFieldHom t h12) = tateFieldHom t h12 := by
  have hR : (Mero.scale (c : Kˣ)).comp (tateRingHom t h12) = tateRingHom t h12 := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
    · change Mero.scale (c : Kˣ) (tateRingHom t h12 (mkT t (C (C a)))) =
        tateRingHom t h12 (mkT t (C (C a)))
      rw [tateRingHom, RingHom.comp_apply, tateRingHomU_mk_C, eval₂_C, constHom_apply,
        Mero.sq_const, Mero.scale_const]
    · change Mero.scale (c : Kˣ) (tateRingHom t h12 (mkT t (C Polynomial.X))) =
        tateRingHom t h12 (mkT t (C Polynomial.X))
      rw [tateRingHom_x, scale_xM]
    · change Mero.scale (c : Kˣ) (tateRingHom t h12 (mkT t Polynomial.X)) =
        tateRingHom t h12 (mkT t Polynomial.X)
      rw [tateRingHom_y, scale_yM]
  refine IsLocalization.ringHom_ext (nonZeroDivisors (TateRing t)) ?_
  rw [RingHom.comp_assoc]
  change (Mero.scale (c : Kˣ)).comp ((tateFieldHom t h12).comp (algebraMap _ _)) =
    (tateFieldHom t h12).comp (algebraMap _ _)
  have h : (tateFieldHom t h12).comp (algebraMap (TateRing t) (TateField t)) =
      tateRingHom t h12 := RingHom.ext fun a => tateFieldHom_algebraMap t h12 a
  rw [h, hR]

/-- **The deck transformation `(-1)^ε s^{-n}` acts on `√(x - e)` by `(-1)^ε`.** -/
theorem scale_tateDeckOfChar_kumM {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (x : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    Mero.scale ((tateDeckOfChar hs x : Deck t) : Kˣ) (kumM t s) =
      if x.2 = 1 then kumM t s else -kumM t s := by
  rw [tateDeckOfChar, MonoidHom.coprod_apply, Subgroup.coe_mul, ← Mero.scale_scale,
    zpowersHom_apply, Subgroup.coe_zpow, Subgroup.coe_inv]
  rw [show (((Deck.gen t hs : Deck t) : Kˣ)) = s from rfl,
    Mero.scale_zpow_of_scale_eq (Mero.scale_inv_of_scale_eq (scale_s_kumM t hs))]
  rcases mult_zmod_two x.2 with h | h
  · rw [h, map_one, if_pos rfl, Subgroup.coe_one, Mero.scale_one]
  · rw [h, signHom_ofAdd_one, if_neg (by decide)]
    exact scale_neg_one_kumM t s

end Deck

/-! ### `Π^tp_X` on `X'`: tfg's deck action and the analytic one -/

section Pi

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  [IsReduced R] (D : TateObject.DoubleData O R) (sΩ : Ω) (hsΩ : sΩ ^ 2 = algebraMap R Ω D.c)

/-- **`g ∈ Π^tp_X` acts on `√(x - e)` through `tateDeck` by `(-1)^ε`**, `ε` the `ℤ/2`-part of
`character₂ g`: the action of `g` on the fibre `{±√c}` of tfg's `X'`. -/
theorem deckHom_tateDeck_kumM {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (g : temperedPi1 O R A V hV) :
    deckHom (tateDeck V hV D sΩ hsΩ hs) g (kumM t s) =
      if (character₂ (A := A) D V hV sΩ hsΩ g).2 = 1 then kumM t s else -kumM t s := by
  change Mero.scale (((tateDeck V hV D sΩ hsΩ hs g)⁻¹ : Deck t) : Kˣ) (kumM t s) = _
  rw [← map_inv, tateDeck, MonoidHom.comp_apply, map_inv, scale_tateDeckOfChar_kumM]
  simp only [Prod.snd_inv, inv_eq_one]

/-- **`g ∈ Π^tp_X` fixes `K(E_t)`** under the deck action through `tateDeck`. -/
theorem deckHom_tateDeck_tateFieldHom (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (g : temperedPi1 O R A V hV) (f : TateField t) :
    deckHom (tateDeck V hV D sΩ hsΩ hs) g (tateFieldHom t h12 f) = tateFieldHom t h12 f :=
  RingHom.congr_fun (scale_comp_tateFieldHom h12 (tateDeck V hV D sΩ hsΩ hs g)⁻¹) f

/-- **A Galois element fixing `√c` acts trivially on the fibre of `Ÿ`**: `χ_Ÿ(σ) = 1` (the
companion of tfg's `character₂_galois`). -/
theorem character₂_galois_fix (σ : decompositionGroup R V) (hσ : (σ : Ω ≃ₐ[R] Ω) sΩ = sΩ) :
    character₂ (A := A) D V hV sΩ hsΩ (galoisToTempered O R A hV σ) = 1 := by
  refine FibreAut.deckCharacterFun_eq (Yddot (A := A) D) (deck₂ D)
    (basePoint₂ (A := A) D V hV sΩ hsΩ) (isDeckTorsor₂ D V hV) ?_
  change (⟦TempObj.preMap V hV (deckHom₂ D (1, 1)) _⟧ :
    (tempFibre O R A V hV).obj (Yddot (A := A) D)) =
    ⟦TempObj.preGalois hV (Yddot (A := A) D) σ σ.2 _⟧
  refine (mk_eq_mk_iff D V hV).2 (Subtype.ext (Prod.ext ?_ ?_))
  · change (t₀ (A := A) D sΩ hsΩ).comp (σPow D 1) =
      ((σ : Ω ≃ₐ[R] Ω) : Ω →ₐ[R] Ω).comp (t₀ (A := A) D sΩ hsΩ)
    rw [σPow_one]
    refine QuadraticLevel.algHom_ext D.c ?_
    change (t₀ (A := A) D sΩ hsΩ) (QuadraticLevel.x D.c) =
      (σ : Ω ≃ₐ[R] Ω) ((t₀ (A := A) D sΩ hsΩ) (QuadraticLevel.x D.c))
    have hx : (t₀ (A := A) D sΩ hsΩ) (QuadraticLevel.x D.c) = sΩ := QuadraticLevel.lift_x _ _ _
    rw [hx]
    exact hσ.symm
  · change ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) 1) _ = _
    rw [map_one]
    rfl

/-- **The Galois action on `√c` is the analytic deck action on `√(x - e)`**: an element `σ` of
the decomposition group of `V` either fixes `√c` and `tateDeck σ` fixes `√(x - e)`, or it
negates both. -/
theorem galois_kummer {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : decompositionGroup R V) :
    ((σ : Ω ≃ₐ[R] Ω) sΩ = sΩ ∧
        deckHom (tateDeck V hV D sΩ hsΩ hs) (galoisToTempered O R A hV σ) (kumM t s) =
          kumM t s) ∨
      ((σ : Ω ≃ₐ[R] Ω) sΩ = -sΩ ∧
        deckHom (tateDeck V hV D sΩ hsΩ hs) (galoisToTempered O R A hV σ) (kumM t s) =
          -kumM t s) := by
  have h2 : ((σ : Ω ≃ₐ[R] Ω) sΩ) ^ 2 = sΩ ^ 2 := by
    rw [← map_pow, hsΩ, AlgEquiv.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · refine Or.inl ⟨h, ?_⟩
    rw [deckHom_tateDeck_kumM, character₂_galois_fix V hV D sΩ hsΩ σ h, Prod.snd_one, if_pos rfl]
  · refine Or.inr ⟨h, ?_⟩
    rw [deckHom_tateDeck_kumM, character₂_galois D V hV sΩ hsΩ σ h, if_neg (by decide)]

end Pi

/-! ### The curve of `D`: `R` and `Mero K` -/

section Data

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {F : Type u} [Field F] {O : ValuationSubring F} {R : Type u} [CommRing R] [Algebra F R]

/-- **The coordinate ring of the curve of `D` maps to `R`** (`x ↦ D.x`, `y ↦ D.y`). -/
def dataToR (D : TateObject.Data O R) : (dataCurve D).toAffine.CoordinateRing →+* R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap F R) D.x) D.y (by
    have h := D.equation
    simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C, eval₂_one, eval₂_zero, coe_eval₂RingHom, dataCurve, map_one, map_zero]
    linear_combination h)

lemma dataToR_mk_C (D : TateObject.Data O R) (p : F[X]) :
    dataToR D (WeierstrassCurve.Affine.CoordinateRing.mk _ (C p)) =
      p.eval₂ (algebraMap F R) D.x := by
  rw [dataToR, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_C,
    coe_eval₂RingHom]

/-- **`x - e₀` goes to tfg's Kummer parameter `c`** when `e = e₀ ∈ F`. -/
theorem dataToR_c (D : TateObject.DoubleData O R) {e₀ : F} (he : D.e = algebraMap F R e₀) :
    dataToR D.toData (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (X - C e₀))) = D.c := by
  rw [dataToR_mk_C, eval₂_sub, eval₂_X, eval₂_C, ← he]

variable (t : TateParameter K)

set_option synthInstance.maxHeartbeats 100000 in
-- the instance path `Field (Mero K)` is slow at the default budget (as in `tateRingHomU`)
/-- **The coordinate ring of the curve of `D` maps to `Mero K`** along `φ : F →+* K` when `t` is
the Tate parameter of `D`: `x ↦ x(Ü²)`, `y ↦ y(Ü²)`. -/
def dataRingHom (φ : F →+* K) (D : TateObject.Data O R) (hT : IsTateParam φ D t)
    (h12 : (12 : K) ≠ 0) : (dataCurve D).toAffine.CoordinateRing →+* Mero K :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (constHom.comp φ) (xM t)) (yM t) (by
    obtain ⟨h4, h6⟩ := (isTateParam_iff φ D t).mp hT
    have h := yM_sq_add t h12
    simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_X, eval₂_C, eval₂_one, eval₂_zero, coe_eval₂RingHom, dataCurve, map_one, map_zero,
      RingHom.comp_apply, h4, h6]
    linear_combination h)

lemma dataRingHom_mk_C (φ : F →+* K) (D : TateObject.Data O R) (hT : IsTateParam φ D t)
    (h12 : (12 : K) ≠ 0) (p : F[X]) :
    dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C p)) =
      p.eval₂ (constHom.comp φ) (xM t) := by
  rw [dataRingHom, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_C,
    coe_eval₂RingHom]

lemma dataRingHom_y (φ : F →+* K) (D : TateObject.Data O R) (hT : IsTateParam φ D t)
    (h12 : (12 : K) ≠ 0) :
    dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ Polynomial.X) =
      yM t := by
  rw [dataRingHom, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_X]

/-- **`c = x - e₀` goes to `β·√(x - e)²`** when `φ(e₀) = X(s)`. -/
theorem dataRingHom_c (φ : F →+* K) (D : TateObject.Data O R) (hT : IsTateParam φ D t)
    (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {e₀ : F} (he : φ e₀ = t.X s) :
    dataRingHom t φ D hT h12 (WeierstrassCurve.Affine.CoordinateRing.mk _ (C (X - C e₀))) =
      Mero.const (kumConst t hs h12) * kumM t s ^ 2 := by
  rw [dataRingHom_mk_C, eval₂_sub, eval₂_X, eval₂_C, RingHom.comp_apply, he, constHom_apply,
    kumM_sq]

end Data

/-! ### A genuine Tate lift on the unramified layer -/

section Lift

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

variable (t) in
/-- `GalDeck t` as extensions to the trivial extension `RR = Mero K`. -/
def extSelf : GalDeck t →* ExtGalDeck t (Mero K) :=
  ((MonoidHom.id (GalDeck t)).prod (galDeckHom t)).codRestrict (ExtGalDeck t (Mero K))
    fun x f => by
      change galDeckHom t x (Mero.ι (Mero K) f) = Mero.ι (Mero K) (galDeckHom t x f)
      simp only [Mero.ι, Algebra.algebraMap_self, RingHom.id_apply]

lemma extRes_extSelf (x : GalDeck t) : extRes t (Mero K) (extSelf t x) = x := by
  rw [extRes_apply]
  rfl

variable {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  [IsReduced R] (D : TateObject.DoubleData O R) (sΩ : Ω) (hsΩ : sΩ ^ 2 = algebraMap R Ω D.c)

/-- **A genuine `γ : Π^tp_X →* ExtGalDeck t (Mero K)`** lifting `tateGalDeck σ hσ` (on the
unramified layer). -/
def gammaMero {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) :
    temperedPi1 O R A V hV →* ExtGalDeck t (Mero K) :=
  (extSelf t).comp (tateGalDeck V hV D sΩ hsΩ hs σ hσ)

theorem isTateLift_gammaMero {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (σ : temperedPi1 O R A V hV →* IsoAut t) (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) :
    IsTateLift V hV D sΩ hsΩ hs σ hσ (gammaMero V hV D sΩ hsΩ hs σ hσ) :=
  MonoidHom.ext fun g => by
    rw [MonoidHom.comp_apply, gammaMero, MonoidHom.comp_apply, extRes_extSelf]

end Lift

end Iut.Frobenioid.BAn
