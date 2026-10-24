/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.Image
import CurvesJacobian.Galois.FunctionFieldF
import CurvesJacobian.Kummer.PrincipalDescent
import WeilCurves.FunctionField.LinearSystem
import CurvesJacobian.Kummer.JacobianDivExt
import CurvesJacobian.Kummer.JacobianLocalField

/-!
# [AbsTopIII] Thm 1.9 (c): `P_U` from the cuspidal principal divisors

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157): "one
constructs the subgroup `P_U ⊆ H¹(Π_U, μ_Ẑ(Π_U))` determined by the cuspidal principal divisors via
the isomorphisms of (b) and the characterization of principal divisors given in Proposition 1.6,
(ii) [cf. also the decomposition groups of (a); Proposition 1.6, (iii)]". Prop 1.6 (iii)
(l.2001–2012): for `U = X \ S`, `S ⊆ X(k)`, restriction to the inertia groups `I_x` gives the exact
sequence `1 → (k^×)^∧ → H¹(Π_U, M_X) → ⊕_{x∈S} Ẑ`, and the image of `Γ(U, 𝒪^×)` is the inverse
image of the principal divisors supported in `S`; Prop 1.6 (ii) (l.1993–2000) characterises the
principal divisors of degree `0` by the sections `t_D`.

curves-jacobian defines `P_U` through the Kummer classes of units (`Kummer/Image.lean`,
`PU = res⁻¹(res(κ_U(Γ(U, 𝒪^×))))`). Here it is identified with the set described in the paper,
in the Galois model `D` (`M_X = Ẑ(1)`):

* `tameGen p`: the **tame generator** at an inertia index `p = (W, σ)` (the residue at `σ` of the
  Kummer class of a uniformiser of the place `P_p` of `F` below `W`); `divAt E p = E(P_p)`;
* **`res_kummerMapZHat`**: `res_p(κ_U(u)) = θ_p^{ord_{P_p}(u)}` — residues of Kummer classes are
  divisors (from continuous-kummer-theory `evalTriv_kummerMapZHat`);
* `ord_eq_zero_of_mem_units`, `isIntegral_of_forall_place`, `mem_units_of_ord`: units of `U` are
  the functions without zeros and poles over `U` (the integral closure of `k[t]` in `F` is the
  intersection of the valuation rings containing it, Mathlib
  `Subring.eq_iInf_of_isIntegrallyClosedIn`);
* **`mem_PU_iff_principal`** (Prop 1.6 (iii), image part): if all cusps are `k`-rational, `η ∈ P_U`
  iff the residues of `η` are those of a principal divisor `∑ nᵢ xᵢ` supported on the cusps
  (`HasResidues η (ratDivF f)`);
* `sum_eq_zero_of_div_eq`: such a divisor has degree `0`;
* `eta_eq_one_iff_principal_curve_of_ext` (Prop 1.6 (ii) with the Jacobian input in the minimal
  form `JacDivFree X σ hσ L`) and **`mem_PU_iff_eta_curve`** (**Thm 1.9 (c)**): for a curve with
  `X(k) ≠ ∅` and rational cusps, `η ∈ P_U` iff its residues are those of a divisor `f` on the cusps
  with `deg f = 0` and `η_f = 1` (`t_f` conjugate to the identity section).

The hypothesis "all cusps rational" is that of Thm 1.9 (b) (l.2148: "the points of `Z \ U` are all
rational over the base field `k_Z` of `Z`"). The general forms take `hL : JacDivFree X σ hσ L`
(`⋂_N N · J(L) = 0` for one extension `L / k`) as a hypothesis; over number fields and finite
extensions of `ℚ_p` it is a curves-jacobian theorem (`jacDivFree_numberField`, `jacDivFree_padic`),
so **`mem_PU_iff_eta_curve_numberField`** and **`mem_PU_iff_eta_curve_padic`** are unconditional.
Not yet done: the passage from `Ẑ(1)` to `M_X = μ_Ẑ(Π_U)` coefficients via the `Π_U`-equivariant
`M_X ≅ Ẑ(1)` (curves-jacobian `h1MXEquiv`), which is how (b) enters.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
open IntermediateField.algebraAdjoinAdjoin

universe u

namespace Iut.Reconstruction.Thm19

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- The valuation subring of `F` below the place `W` of an inertia index `p = (W, σ)`. -/
def idxVal (p : InertiaIndex D) : ValuationSubring (F D) :=
  p.1.1.comap (algebraMap (F D) Ω)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
lemma algebraMap_mem_idxVal (p : InertiaIndex D) (c : k) : algebraMap k (F D) c ∈ idxVal p := by
  rw [idxVal, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
  exact p.2.1 c

/-- The place of `F` below `p` (if `W ∩ F ≠ F`). -/
def idxPlace (p : InertiaIndex D) (h : idxVal p ≠ ⊤) : Place k (F D) :=
  ⟨idxVal p, h, algebraMap_mem_idxVal p⟩

open Classical in
/-- The multiplicity of a divisor of `F` at the place below `p` (`0` if `W ∩ F = F`). -/
noncomputable def divAt (E : Divisor k (F D)) (p : InertiaIndex D) : ℤ :=
  if h : idxVal p ≠ ⊤ then E (idxPlace p h) else 0

omit [IsAlgClosed Ω] in
lemma ne_zero_of_ord_eq_one {P : Place k (F D)} {π : F D} (h : P.ord π = 1) : π ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact zero_ne_one h

open Classical in
/-- A uniformiser of the place below `p` (`1` if `W ∩ F = F`). -/
noncomputable def unif (p : InertiaIndex D) : (F D)ˣ :=
  if h : idxVal p ≠ ⊤ then
    Units.mk0 (idxPlace p h).exists_ord_eq_one.choose
      (ne_zero_of_ord_eq_one (idxPlace p h).exists_ord_eq_one.choose_spec)
  else 1

/-- **The tame generator** at `p = (W, σ)`: the residue at `σ` of the Kummer class of a
uniformiser of the place below `W`. -/
noncomputable def tameGen (p : InertiaIndex D) : ZHatOne (F D) Ω :=
  ContH1.evalTriv (p.1.2 : D.H) (inertia_smul_zHatOne p.2.1 p.2.2 (F D))
    (resZHat D (F D) (kummerZHat (F D) Ω (unif p)))

set_option maxHeartbeats 800000 in
-- `ContH1.evalTriv` terms unify slowly
/-- **Residues of Kummer classes of units are divisors**: `res_p(κ_U(u)) = θ_p^{ord_P(u)}`. -/
theorem res_kummerMapZHat (u : units D) (p : InertiaIndex D) :
    res D (kummerMapZHat D u) p = tameGen p ^ divAt (Divisor.div k ((u : (F D)ˣ) : F D)) p := by
  rw [res_apply, tameGen]
  by_cases h : idxVal p ≠ ⊤
  · set P := idxPlace p h
    have hdiv : divAt (Divisor.div k ((u : (F D)ˣ) : F D)) p = P.ord ((u : (F D)ˣ) : F D) := by
      rw [divAt, dif_pos h, Divisor.div_apply]
    have hπ : P.ord ((unif p : (F D)ˣ) : F D) = 1 := by
      rw [unif, dif_pos h]
      exact P.exists_ord_eq_one.choose_spec
    rw [hdiv]
    set m := P.ord ((u : (F D)ˣ) : F D)
    have hu0 : ((u : (F D)ˣ) : F D) ≠ 0 := (u : (F D)ˣ).ne_zero
    have hord : P.ord ((((u : (F D)ˣ) * unif p ^ (-m) : (F D)ˣ) : F D)) = 0 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, P.ord_mul hu0
        (zpow_ne_zero _ (unif p).ne_zero), P.ord_zpow, hπ]
      ring
    obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff (Units.ne_zero _)).1 hord
    refine evalTriv_kummerMapZHat p.2.1 p.2.2 u (unif p) m h1 ?_
    rw [Units.val_inv_eq_inv_val]
    exact h2
  · have htop : idxVal p = ⊤ := not_not.1 h
    have hdiv : divAt (Divisor.div k ((u : (F D)ˣ) : F D)) p = 0 := by
      rw [divAt, dif_neg h]
    rw [hdiv]
    have hmem : ∀ x : F D, ((x : F D) : Ω) ∈ p.1.1 := fun x => by
      have : x ∈ idxVal p := htop ▸ ValuationSubring.mem_top x
      exact this
    exact evalTriv_kummerMapZHat p.2.1 p.2.2 u (unif p) 0 (hmem _) (hmem _)

/-! ### Units of `U` and places of `F` -/

/-- The cusps of `U` as places of `F`: the places not containing `t`. -/
def IsCuspPlaceF (P : Place k (F D)) : Prop := CurvesJacobian.tF D ∉ P.1

omit [IsAlgClosed Ω] in
/-- **Units of `U` have no zeros or poles on `U`.** -/
theorem ord_eq_zero_of_mem_units (u : units D) (P : Place k (F D)) (hP : ¬ IsCuspPlaceF P) :
    P.ord ((u : (F D)ˣ) : F D) = 0 := by
  rw [IsCuspPlaceF, not_not] at hP
  obtain ⟨W, hW⟩ := CurvesJacobian.exists_valuationSubring_liesOver D P
  have hc : IsCentered k t W := by
    refine ⟨fun c => ?_, ?_⟩
    · have := (hW (algebraMap k (F D) c)).2 (P.2.2 c)
      exact this
    · exact (hW (CurvesJacobian.tF D)).2 hP
  obtain ⟨h1, h2⟩ := units_mem hc u.2
  exact (P.ord_eq_zero_iff (Units.ne_zero _)).2
    ⟨(hW _).1 h1, by rw [← Units.val_inv_eq_inv_val]; exact (hW _).1 h2⟩

omit [IsAlgClosed Ω] [CharZero k] [IsGalois (K₀ k t) Ω] in
/-- **An element of `F` lying in every place over `U` is integral over `k[t]`** (the integral
closure of `k[t]` in `F` is the intersection of the valuation rings containing it). -/
theorem isIntegral_of_forall_place (x : F D)
    (hx : ∀ P : Place k (F D), ¬ IsCuspPlaceF P → x ∈ P.1) : IsIntegral (A₀ k t) x := by
  have hC := Subring.eq_iInf_of_isIntegrallyClosedIn
    (R := (integralClosure (A₀ k t) (F D)).toSubring) (K := F D)
  have : x ∈ (integralClosure (A₀ k t) (F D)).toSubring := by
    rw [hC, Subring.mem_iInf]
    intro V
    by_cases hV : V.1 = ⊤
    · rw [hV]
      exact ValuationSubring.mem_top x
    · have hk : ∀ c : k, algebraMap k (F D) c ∈ V.1 := fun c => V.2 (by
        change IsIntegral (A₀ k t) (algebraMap k (F D) c)
        rw [IsScalarTower.algebraMap_apply k (A₀ k t) (F D)]
        exact isIntegral_algebraMap)
      have ht : CurvesJacobian.tF D ∈ V.1 := V.2 (by
        change IsIntegral (A₀ k t) (CurvesJacobian.tF D)
        have e : CurvesJacobian.tF D = algebraMap (A₀ k t) (F D)
            ⟨t, Algebra.subset_adjoin (Set.mem_singleton t)⟩ := rfl
        rw [e]
        exact isIntegral_algebraMap)
      exact hx ⟨V.1, hV, hk⟩ (not_not.2 ht)
  exact this

omit [IsAlgClosed Ω] in
/-- A nonzero element of `F` without zeros or poles over `U` is a unit of `U`. -/
theorem mem_units_of_ord (g : F D) (hg : g ≠ 0)
    (hord : ∀ P : Place k (F D), ¬ IsCuspPlaceF P → P.ord g = 0) : Units.mk0 g hg ∈ units D :=
  ⟨isIntegral_of_forall_place g fun P hP => ((P.ord_eq_zero_iff hg).1 (hord P hP)).1,
    isIntegral_of_forall_place _ fun P hP => ((P.ord_eq_zero_iff hg).1 (hord P hP)).2⟩



/-! ### The group-theoretic `P_U` ([AbsTopIII] Thm 1.9 (c)) -/

/-- **The residues of `η` are those of the divisor `E`**: `res_p(η) = θ_p^{E(P_p)}` for every
`p = (W, σ)`, `P_p` the place of `F` below `W`. -/
def HasResidues (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (E : Divisor k (F D)) : Prop :=
  ∀ p : InertiaIndex D, res D η p = tameGen p ^ divAt E p

/-- **[AbsTopIII] Prop 1.6 (iii), image part, with rational cusps**: if every cusp of `U` is a
`k`-rational point, then `η ∈ P_U` iff the residues of `η` are those of a principal divisor
`∑ nᵢ xᵢ` supported on the cusps. -/
theorem mem_PU_iff_principal
    (hrat : ∀ P : Place k (F D), IsCuspPlaceF P → ∃ x : RatPoint D, placeOfF x = P)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    η ∈ PU D ↔ ∃ f : RatPoint D →₀ ℤ, (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧
      ratDivF f ∈ principal k (F D) ∧ HasResidues η (ratDivF f) := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    set E := Divisor.div k ((u : (F D)ˣ) : F D) with hE
    have hsupp : ∀ P ∈ E.support, IsCuspPlaceF P := by
      intro P hP
      by_contra h
      exact (Finsupp.mem_support_iff.1 hP) (by
        rw [hE, Divisor.div_apply]
        exact ord_eq_zero_of_mem_units u P h)
    choose s hs using fun P : E.support => hrat P.1 (hsupp P.1 P.2)
    let f : RatPoint D →₀ ℤ := ∑ P ∈ E.support.attach, Finsupp.single (s P) (E P)
    have hf : ratDivF f = E := by
      rw [ratDivF, Finsupp.mapDomain_finsetSum]
      simp_rw [Finsupp.mapDomain_single, hs]
      rw [Finset.sum_attach E.support (fun P => Finsupp.single P (E P))]
      exact Finsupp.sum_single E
    refine ⟨f, fun x hx => ?_, ?_, fun p => ?_⟩
    · obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hx)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hP), hs]
      exact hsupp P.1 P.2
    · rw [hf]
      exact mem_principal.2 ⟨_, (u : (F D)ˣ).ne_zero, rfl⟩
    · rw [hf, ← res_kummerMapZHat, ← hu]
      rfl
  · rintro ⟨f, hsupp, hpr, hres⟩
    obtain ⟨g, hg0, hdiv⟩ := mem_principal.1 hpr
    have hord : ∀ P : Place k (F D), ¬ IsCuspPlaceF P → P.ord g = 0 := by
      intro P hP
      rw [← Divisor.div_apply, hdiv]
      refine Finsupp.notMem_support_iff.1 fun hPs => hP ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hPs)
      exact hsupp x hx
    let u : units D := ⟨Units.mk0 g hg0, mem_units_of_ord g hg0 hord⟩
    refine ⟨u, funext fun p => ?_⟩
    rw [MonoidHom.comp_apply, res_kummerMapZHat, hres p]
    change tameGen p ^ divAt (Divisor.div k g) p = _
    rw [hdiv]

/-- The divisor of a function supported on `k`-rational points has degree `0`. -/
theorem sum_eq_zero_of_div_eq (f : RatPoint D →₀ ℤ) {u : F D} (hu : u ≠ 0)
    (h : Divisor.div k u = ratDivF f) : (f.sum fun _ m => m) = 0 := by
  have h' := (div_ιF_eq_ratDiv_iff f hu).2 h
  have hdeg := Divisor.deg_div (k := kbar k Ω) (ιF D u)
  rw [h', ratDiv, Divisor.deg, Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)] at hdeg
  simpa [Place.deg_eq_one_of_isAlgClosed] using hdeg

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

variable {k hτ}

/-- **[AbsTopIII] Prop 1.6 (ii)** for a curve with `X(k) ≠ ∅`, with Kummer-faithfulness for the
Jacobian taken in the minimal form `⋂_N N · J(L) = 0` for one extension `L / k`
(curves-jacobian `JacDivFree`): for a degree-`0` divisor `∑ nᵢ xᵢ` on `k`-rational points,
`η_D = 0` (the section `t_D` is `Δ_X`-conjugate to the identity section) iff `D` is principal. -/
theorem eta_eq_one_iff_principal_curve_of_ext (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [Algebra k L] (hL : JacDivFree X σ hσ L)
    (f : RatPoint (curveGaloisData k hτ) →₀ ℤ) (hf : (f.sum fun _ m => m) = 0) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    eta f = 1 ↔ ratDivF f ∈ principal k (F (curveGaloisData k hτ)) :=
  letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
    fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
  eta_eq_one_iff_principal (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (fun N hN y hy => by
      obtain ⟨w, hw⟩ := exists_nsmul_eq_jacPsi k hτ σ hσ hN.ne' ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩)
    (fun N _ => weilDual_bijective_baseChange k hτ)
    (fun N _ => finite_picTorsion_baseChange k hτ) f hf

/-- **[AbsTopIII] Thm 1.9 (c) for a curve with rational cusps**: for a curve `X` with
`X(k) ≠ ∅` over a field `k` of characteristic `0` whose cusps (the poles of `τ`) are all
`k`-rational, and the Jacobian input `hL` (`⋂_N N · J(L) = 0` for one extension `L / k`), a class
`η ∈ H¹(Π_U, Ẑ(1))` lies in `P_U = κ_U(Γ(U, 𝒪^×)) · (k^×)^∧` iff there is a divisor
`f = ∑ nᵢ xᵢ` on the cusps with
* `deg f = 0` and `η_f = 1` (the group-theoretic criterion of Prop 1.6 (ii): `t_f` is
  `Δ_X`-conjugate to the identity section, a condition on the decomposition groups `s_{xᵢ}`), and
* `res_p(η) = θ_p^{f(P_p)}` at every inertia index `p = (W, σ)` (the residues of Prop 1.6 (iii),
  `θ_p` the tame generator at `p`).
-/
theorem mem_PU_iff_eta_curve (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [Algebra k L] (hL : JacDivFree X σ hσ L)
    (hrat : ∀ P : Place k (F (curveGaloisData k hτ)), IsCuspPlaceF P →
      ∃ x : RatPoint (curveGaloisData k hτ), placeOfF x = P)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X))) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    η ∈ PU (curveGaloisData k hτ) ↔ ∃ f : RatPoint (curveGaloisData k hτ) →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResidues η (ratDivF f) := by
  rw [mem_PU_iff_principal hrat]
  constructor
  · rintro ⟨f, hs, hp, hr⟩
    obtain ⟨g, hg, hd⟩ := mem_principal.1 hp
    have h0 := sum_eq_zero_of_div_eq f hg hd
    exact ⟨f, hs, h0, (eta_eq_one_iff_principal_curve_of_ext σ hσ L hL f h0).2 hp, hr⟩
  · rintro ⟨f, hs, h0, he, hr⟩
    exact ⟨f, hs, (eta_eq_one_iff_principal_curve_of_ext σ hσ L hL f h0).1 he, hr⟩

/-- **[AbsTopIII] Thm 1.9 (c) for a curve with rational cusps over a number field**,
unconditionally: `mem_PU_iff_eta_curve` with `⋂_N N · J(k) = 0` from curves-jacobian
`jacDivFree_numberField` ([AbsTopIII] Rem 1.5.4 (i), MR5 Task B). -/
theorem mem_PU_iff_eta_curve_numberField [NumberField k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hrat : ∀ P : Place k (F (curveGaloisData k hτ)), IsCuspPlaceF P →
      ∃ x : RatPoint (curveGaloisData k hτ), placeOfF x = P)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X))) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    η ∈ PU (curveGaloisData k hτ) ↔ ∃ f : RatPoint (curveGaloisData k hτ) →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResidues η (ratDivF f) :=
  mem_PU_iff_eta_curve σ hσ k (jacDivFree_numberField X σ hσ) hrat η

/-- **[AbsTopIII] Thm 1.9 (c) for a curve with rational cusps over a finite extension of `ℚ_p`**,
unconditionally: `mem_PU_iff_eta_curve` with `⋂_N N · J(k) = 0` from curves-jacobian
`jacDivFree_padic` ([AbsTopIII] Rem 1.5.4 (i), MR5 Task B). -/
theorem mem_PU_iff_eta_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hrat : ∀ P : Place k (F (curveGaloisData k hτ)), IsCuspPlaceF P →
      ∃ x : RatPoint (curveGaloisData k hτ), placeOfF x = P)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X))) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    η ∈ PU (curveGaloisData k hτ) ↔ ∃ f : RatPoint (curveGaloisData k hτ) →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResidues η (ratDivF f) :=
  mem_PU_iff_eta_curve σ hσ k (jacDivFree_padic X σ hσ p) hrat η

end Curve

end Iut.Reconstruction.Thm19
