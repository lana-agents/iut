# Frobenioids (`Iut/Frobenioid/`, roadmap P15)

A Lean formulation of the theory of **Frobenioids** of Mochizuki, *The geometry of Frobenioids I:
the general theory* (**[FrdI]**, June 2008 version) and *II: Poly-Frobenioids* (**[FrdII]**), as
far as it is used in IUT I §3–§5 and IUT II–III: the definitions, the model Frobenioids
([FrdI], Theorem 5.2), the global realified Frobenioid of a number field (IUT I, Example 3.5;
[FrdI], Example 6.3, Theorem 6.4), the `p`-adic Frobenioid of a local field ([FrdII],
Example 1.1), the shape of the tempered Frobenioids ([EtTh] §3–§5, [FrdII] Example 3.3), the
category-theoreticity statements ([FrdI], Theorem 3.4, Corollary 4.11), and the connection to
the wall (`Iut/Wall/`, roadmap-v2 M1a/M3).

The source PDFs were fetched from Mochizuki's page and read in their text extraction (the
section, definition and page numbers below are those of the PDFs).

**Status of the dependency.** No module of this directory is imported by the comparator
challenge or by `Iut/Concrete/*`.

## Plan (lemma-level milestones)

1. **Definitions** ([FrdI] §0–§1).
   * `Basic.lean`: monoids on a category `D` (`GrpOn`, `DivMonoid`, `DivMonoid.le`), the
     elementary Frobenioid `F_Φ` (`Elem Φ`, Definition 1.1(iii)) with its projection to `D`;
     the composition law of Remark 1.1.1.
   * `Defs.lean`: pre-Frobenioids (`PreFrobenioid`, Definition 1.1(iv)); `Base`, `Div`,
     `degFr`; the morphism types of Definition 1.2 (linear, isometric, base-isomorphism,
     pull-back, pre-step, co-angular, LB-invertible, Frobenius type, prime-Frobenius) and the
     object types (Frobenius-trivial, isotropic, base-trivial, …); `O×(A)`, `O▷(A)`;
     **`Frobenioid`**: Definition 1.3 (i)–(vii) as `Prop` fields.
   * General lemmas: Remark 1.2.1, the uniqueness clause of Definition 1.3(iv)(a) from (ii)
     and the pull-back property (`factorization_unique`).
2. **Model Frobenioids** ([FrdI] Theorem 5.2).
   * `Model.lean`: `Model Φ B divB` (objects `(A_D, α ∈ Φ^gp(A_D))`, morphisms
     `(deg, Base, Div, u)` with `deg·α + Div = Base^*β + div_B(u)`), its category structure
     and the functor to `F_Φ`; characterizations of isomorphisms, pull-back morphisms,
     co-angular morphisms, `O▷`, `O×`.
   * `ModelFrobenioid.lean`: **Theorem 5.2(ii)**: the model is a Frobenioid of isotropic type
     (`Model.frobenioid`); Theorem 5.1(i) for the model (`Pic_C(A) ≅ Pic_Φ(A)`,
     `Model.nonempty_iso_iff`).
3. **Concrete instances.**
   * (a) `Global.lean`: the **global realified Frobenioid** `C^⊩` of a number field `K`
     (one-morphism base, divisor monoid the effective ℝ-arithmetic divisors
     `(V_fin →₀ ℝ_{≥0}) × (V_∞ → ℝ_{≥0})`, rational functions `ℝ·div(K^×)`); the arithmetic
     degree `deg^arith` ([FrdI] Example 6.3), its vanishing on rational functions, the degree
     `δ` on objects (an isomorphism invariant, Theorem 6.4(i)); the objects of arithmetic line
     bundles (`ofBundle`) and **`degree_ofBundle : δ(ofBundle L) = deg L`** (and `degNorm`).
   * (a') `GlobalPic.lean`: **[FrdI], Theorem 6.4(i)**, `δ_A : Pic_Φ(A) ≅ ℝ`: injectivity via
     the finiteness of the class group (finite part) and Dirichlet's unit theorem
     (`unitLattice_span_eq_top`, archimedean part); objects are classified by their degree.
   * (b) `PAdic.lean`: the **`p`-adic Frobenioid** of `K_w` for a finite place `w` of a number
     field (one-morphism base, `Φ = ℤ_{≥0}`, `B = K_w^×` with `div_B = ord_w`); the objects
     `O^▷`, `O^×` and the comparison with `Iut/Concrete/LocalConstruct`.
   * (c) `TemperedBase.lean`, `Tempered.lean`: the tempered Frobenioid ([EtTh] §3) over the
     actual base category `B^temp(Π)⁰` (transitive `Π`-sets `Π/H`, `H` open; connected and
     totally epimorphic), with the theta-divisor instance of the `ℤ`-covering `Y → X` of the
     Tate curve (wall roadmap step 2, see `Iut/EtaleTheta/README.md`):
     - (c1) `OrbitObj Π`, `OrbitObj.isConnected`, `OrbitObj.totallyEpimorphic`,
       `OrbitHom.bijective_of_isFSM` (monomorphisms are injective);
     - (c2) `TemperedFrobenioidData Π` (`Φ₀`, `B₀`, `div₀` on `B^temp(Π)⁰`) and
       `TemperedFrobenioidData.isFrobenioid` without further hypotheses;
     - (c3) for a character `χ : Π → ℤ`: `divMonoid χ` (invariant `ℤ`-valued divisors on
       `(Π/H) × ℤ`, the special-fibre divisors pulled back from the `ℤ`-chain of components of
       `Y`), `thetaGrp χ` (divisors `a + b·j + c·j²` of the theta monomials `√q^a Ü^b Θ̈^{-c}`),
       `thetaData χ`, `thetaData_isFrobenioid`;
     - (c4) on `Y = Π/ker χ`: `divTheta = -j²`, `divU = j`, and the functional equation
       `pb_deck_divTheta` (divisor form of [EtTh], Prop. 1.4(ii));
     - (c5) `tateThetaData`: the instance for `Π = temperedPi1` of the Tate curve and
       `χ = TateObject.character` (`tempered-fundamental-groups`), with
       `tateThetaData_isFrobenioid`.
4. **Category-theoreticity** (`Theoreticity.lean`): precise statements of [FrdI] Theorem
   3.4(iii)/(v) (`PreservesFrobeniusStructure`, `PreservesBase`); within the model Frobenioid,
   the elementary types are characterized category-theoretically, and for the global realified
   Frobenioid the degree is invariant under the `ℝ_{>0}`-scaling automorphisms up to the scalar
   ([FrdI] Theorem 6.4(ii) for scalings). Theorem 3.4 itself is proved for the model
   Frobenioids of IUT in milestone 6 (MR16, below).
5. **The wall** (`Wall.lean`): the `q`-pilot and `Θ`-pilot objects of the global realified
   Frobenioid of `K = D.Kt` (from `Iut/Arakelov/QPilot`), their Frobenioid degrees
   `|log q|` and `s·|log q|`; equality with the pilots of `Wall.qVal`/`Wall.thetaVal`; the
   scaling automorphism carrying the Θ-pilot to the `q`-pilot has scale `1/s ≠ 1`
   (the hexagon of `Wall.hexagon_not_commutes` in Frobenioid language).

## Status (all milestones formalised; no placeholders; only `propext`, `Classical.choice`,
`Quot.sound`)

| Milestone | Files | Main results |
|---|---|---|
| 1 Definitions | `Basic.lean`, `Defs.lean` | `DivMonoid`, `Elem`, `IsFrobenioid` (Def. 1.3 (i)–(vii)), `isIso_iff_isPullback_isBaseIso` (Rem. 1.2.1), `factorization_unique_of` |
| 2 Model Frobenioids | `Model.lean`, `ModelFrobenioid.lean` | `Model.isFrobenioid` (Thm 5.2(ii)), `Model.isIso_iff`, `Model.isPullback_iff`, `Model.isIsotropic`, `Model.isCoangular`, `Model.nonempty_iso_iff` (Thm 5.1(i)) |
| 3(a) global realified | `Global.lean` | `globalRealified_isFrobenioid`, `degArith_toDiv`, `degree_ofBundle`, `degreeNorm_ofBundle`, `degArith_ratFun`, `picDeg_surjective`, `degree_eq_of_iso`, `degree_frobenius`, `ofBundle_iso_of_rel` |
| 3(a') `δ_A` iso | `GlobalPic.lean` | `ker_degArith_le` (Dirichlet + finite class group), `picDeg_injective`, `picDegEquiv` (Thm 6.4(i)), `GlobalRealified.nonempty_iso_iff_degree_eq` |
| 3(b) `p`-adic | `PAdic.lean` | `PAdic.isFrobenioid`, `PAdic.orhdEquiv` (`O^▷ = 𝒪 \ 0`), `PAdic.ounitsEquiv` (`O^× = 𝒪^×`), `PAdic.nonempty_iso` |
| 3(d) archimedean | `Arch.lean` | `Arch.isFrobenioid`, `Arch.orhd_iff` (`O^▷ = {0 < |u| ≤ 1}`), `Arch.ounits_iff` (`O^× = {|u| = 1}`) |
| 3(c) tempered | `TemperedBase.lean`, `Tempered.lean`, `TateTheta.lean` | `OrbitObj.isConnected`, `OrbitObj.totallyEpimorphic`, `OrbitHom.bijective_of_isFSM`, `TemperedFrobenioidData.isFrobenioid`, `thetaData_isFrobenioid`, `pb_deck_divTheta`, `tateThetaData_isFrobenioid`; units in `B₀`: `unitThetaData_isFrobenioid`, `ker_unitThetaDiv` (kernel of the divisor map = units); `tateY_H` (`Y` has subgroup `Π^tp_Y = TateObject.piY`), `mem_tateY_H_iff` |
| 4 category-theoreticity | `Theoreticity.lean` | statements `PreservesFrobeniusStructure`, `PreservesBase`; `scale_preserves`, `endZeroEquiv`, `inducedDegAut` |
| 6 Thm 3.4 (MR16) | `Invariance.lean`, `ModelTypes.lean`, `Thm34.lean`, `Thm34Base.lean`, `Thm34iv.lean`, `Thm34Rlf.lean`, `GaloisBase.lean`, `GaloisSlim.lean` | see "Category-theoreticity (MR16)" below: `Model.thm34_preservesFrobeniusStructure`, `Model.thm34_preservesBase`, `Model.degFr_map_eq`, `Model.mem_orhd_iff`, `OrbitObj.baseHyp`, `OrbitObj.isSlim`, `Model.thm34_galois`, `Model.thm34_galois_preservesBase`, `GlobalRealified.thm34` |
| 9 Thm 6.4(ii) (MR16) | `Thm64.lean` | `GlobalRealified.thm64ii` (`δ_{F X}([τ_X z]) = deg(Ψ)·δ_X([z])` on Frobenius-trivial `X`), `degOf_pos`, `picMap_mk`, `picDeg_picMap`, `degOf_unique`, `degree_map` (`deg(F X) = deg(Ψ)·deg X` for `deg X ≥ 0`), `isFrobeniusTrivial_iff` (Frobenius-trivial = degree `0`), `isFrobeniusTrivial_map`, `thm34_deg_id` (`Ψ_{ℕ≥1} = id`) |
| 10 Cor 4.11(iii),(iv) for `C^⊩` (MR16) | `Cor411Rlf.lean` | `GlobalRealified.psiPhi` (`Ψ_Φ`), `psiPhi_add`, `psiPhi_le_iff`, `psiPhi_surjective`, `psiPhi_injective`, `div_map` (`Div(F φ) = Ψ_Φ(Div φ)` for every `φ`), `divMap_indep`, `degree_map_eq` (`deg(F X) = deg(Ψ)·deg X` for every `X`), `degArith_psiPhi`; Thm 3.4(iii),(v): `GlobalRealified.thm34_full`, `Arch.thm34`, `preservesBase_pt` |
| 11 Prop 2.1 (MR16) | `NaiveFrob.lean` | `Model.naiveFrob` (naive Frobenius functor), `frob_comp_naiveFrob`, `naiveFrob_unique`, `naiveFrobCompIso`, `naiveFrob_map_div`/`_u`; `GlobalRealified.naiveFrobIsoScale`, `scaleEquiv`, `naiveFrob_isEquivalence` (`C^⊩` is perfect) |
| 12 Ex 6.3, Prop 5.3 (MR16) | `GlobalNonRlf.lean` | `GlobalFrobenioid K` (Ex 6.3: `Φ = ℤ_{≥0}^{(V_fin)} × ℝ_{≥0}^{V_∞}`, `B = K^×`), `globalFrobenioid_isFrobenioid`, `divZ_mem_effConeZ_iff` (effective principal divisors = roots of unity), `orhdEquiv`/`ounitsEquiv` (`O^▷ = O^× = μ(K)`), `realify` (`C → C^⊩`, Prop 5.3), `realify_essSurj` |
| 13 `Prime(C^⊩) ≅ V` (MR16) | `GlobalPrime.lean` | `preceq_iff`, `isPrimary_iff` (primary = supported at one place), `primeEquiv`, `psiPhi_isPrimary_iff`, `placeEquiv` (`Ψ_Prime`), `supp_psiPhi` |
| 14 Thm 5.1 (MR16) | `Thm51.lean` | `Model.exists_hom_iff` (5.1(ii)), `toElem_map_eq_of`, `u_sub_mem_ker` (uniqueness of unit-equivalence classes), `class_frobeniusType` (5.1(i)); `Model.nonempty_iso_iff` (5.1(i), `ModelFrobenioid.lean`) |
| 15 `p`-adic over `B(G_K)⁰` (MR17) | `GaloisModel.lean`, `PAdicGalois.lean` | `invGrpOn` (`G/H ↦ M^H`), `constPhi`, `GaloisModel` (`[FrdII]` Ex 1.1(ii)), `GaloisModel.hasAllTorsion`, `orhdEquiv`/`ounitsEquiv`, `GaloisModel.thm34`, `thm34_base`; `PAdicGalois.Frob p K` (`C^⊢_v`), `FrobPf p K` (`C_v`), `norm_smul` (Galois-invariance of the norm), `torsion` (roots of unity), `PAdicGalois.thm34`, `thm34Pf` |
| 16 `G_E` slim, Thm 3.4(v), FrdII Thm 2.4 Kummer part (MR17) | `PAdicSlim.lean`, `KummerFrob.lean` | `PAdicGalois.isSlimGroup` (via `PadicField.artin_naturality`, `artin_injective` of LCFT), `thm34_base`, `thm34Pf_base`, `orbitObj_isSlim`; `Model.conj`, `conj_u` (action of `Aut_C(A)` on `O^×(A)` through `Aut_D(A_D)`, FrdII Thm 1.2(ii)), `ounits_comm`, `Model.kummerCocycle`, `kummerCocycle_u`, `map_kummerCocycle`, `GaloisModel.galAut`, `PAdicGalois.kummerCocycle_galAut` (`κ_g(σ) = σγ/γ`), `kummerCocycle_eq_kummerFun`, `thm24_kummer` |
| 17 Thm 6.4(iii) (MR16) | `GlobalPf.lean`, `Thm64iii.lean` | `GlobalPf K` (`(C^pf)^{un-tr}`, `Φ^pf`, `ℚ·Φ^birat`), `GlobalPf.realify`; `psiPhi_inv_psiPhi`, `psiPhi_castQ_mem` (`ℚ`-structure transported), `placeEquiv_inl` (finite places go to finite places), `exists_rat_degree`, **`GlobalRealified.thm64iii`** (`deg(F) ∈ ℚ_{>0}`, residue characteristics preserved; uses `Real.not_exists_pos_rat_log_div_eq` = FrdI Lemma 6.5(ii)) |
| 18 FrdII Ex 3.3, IUT I Ex 3.4(i) (MR17) | `Angular/Circle.lean`, `Angular/Category.lean`, `Angular/Frobenioid.lean`, `Angular/Props.lean`, `Angular/Kummer.lean` | the **archimedean Frobenioid of angular regions** over `Pt` (`K = ℂ`, `V_K = ℂ`): `IsAngular` (nonempty connected open `B ⊆ S¹`), `IsAngular.pow`/`mul`/`singleton_mul` (Def 3.1(iii)), `IsAngular.rigid`/`eq_of_subset` (Lemma 3.2(iv) with rotation), `IsAngular.pow_eq_univ` (Lemma 3.2(v)), `exists_isAngular_subset`; `Angular.Obj` (`B × (0, e^τ]`), `Hom` (`(d, μ = e^ρ u)` with `u·B^{⊗d} ⊆ B'`, `ρ + dτ ≤ τ'`; equivalent to `μ·A^{⊗d} ⊆ A'`: `Hom.smul_region_pow_subset`, `hom_cond_of_subset`), `toElem` (`Div = τ' − ρ − dτ`, `Div_eq_sSup`), `isIso_iff`, `isCoangular_iff` (co-angular = naively co-angular), `isIsotropic_iff` (isotropic = naively isotropic); **`Angular.isFrobenioid`** (all clauses of FrdI Def 1.3 proved directly; pull-backs = isomorphisms); `endo_of_not_isotropic`, `endo_isCoangular`, `isIsotropic_tfae` (isotropic ⇔ Frobenius-trivial ⇔ Frobenius-ample), `isMetricallyTrivial`, `isFrobeniusIsotropic`; `orhdEquiv` (`O^▷(A) ≅ O^▷_ℂ`, multiplicative `orhdEquiv_comp`), `mem_ounits_iff`, `val_transport`; Kummer structure `kummer : O^▷(A) → A_D` into the MR10 field `RecField D p` (`kummer_injective`, `kummer_comp`, `continuous_kummer`, `range_kummer`, `kummer_transport`, `kummer_indet`: `{id, conj}`) |
| 7 FrdI §1 | `Props.lean` | Prop. 1.4(i)–(iii) (`coangular_of_isotropic`, `isPullback_iff`, `isIso_of_lbInvertible_preStep`), 1.7(i), (v), 1.8(iii), 1.9(iv), 1.11(iii), 1.12(i) |
| 8 FrdI Prop. 1.14(iii) | `Counterexample.lean` | `Counterexample.not_prop114iii` (fails when `B` has torsion of every order), `frob_not_mono` |
| 5 the wall | `Wall.lean` | `degreeNorm_qPilotObj`, `degreeNorm_thetaPilotObj` (`= s·|log q|`), `logVol_qRegion_eq_neg_degreeNorm`, `logVol_lgp_eq_neg_degreeNorm`, `scale_thetaPilotObj`, `nonempty_iso_scale_iff`, `isEmpty_iso_thetaPilot_qPilot` |

## Encoding choices and simplifications

* **Monoids.** A divisorial monoid `Φ` is recorded by its groupification `Φ^gp(A)` (abelian
  groups with pull-backs) and the cone `Φ(A) ⊆ Φ^gp(A)` (sharp, saturated, generating);
  characteristic injectivity is injectivity of the pull-backs. Rational function monoids are
  families of abelian groups (`GrpOn`). See `Basic.lean`.
* **Categories** are Mathlib categories; `C → F_Φ` is a Mathlib functor; Mathlib composes
  diagrammatically (`ψ ≫ φ = φ ∘ ψ`).
* **Definition 1.3** is recorded clause by clause; (i)(c) and (iii)(d) record the essential
  surjectivity/fullness halves of the equivalences (faithfulness and full faithfulness are
  automatic), (iii)(c) records the bijection with its intertwining property (multiplicativity
  is `Orhd.equiv_mul`). See the docstring of `Defs.lean`.
* **Not formalised** from [FrdI] §1–§4: perfections, realifications as a general construction
  (only the realified global Frobenioid is built directly as a model Frobenioid), the types
  "standard", "Frobenius-normalized", "FSMFF", base-Frobenius pairs as a structure (their
  model instance is `Model.zeroSection` and the `ζ(n) = (n, id, 0, 0)` of
  `Model.isFrobeniusTrivial_zero`).
* **Base categories** of the global, `p`-adic and archimedean instances are the one-morphism
  category `Pt` (trivial Galois extension), as in IUT I, Example 3.5(i) for `C^⊩_mod`. The
  tempered instance uses the category `B^temp(Π)⁰ = OrbitObj Π` of connected objects of a
  topological group (`TemperedBase.lean`); the same construction gives the Galois-category
  bases `B(G)⁰` of [FrdI], Example 6.3 / [FrdII], Example 1.1 for profinite `G`, but those
  instances are not built.
* **Tempered Frobenioid** (`Tempered.lean`): the base category is the genuine `B^temp(Π)⁰`.
  The monoids of the theta instance are combinatorial: `Φ₀` consists of the special-fibre
  divisors pulled back from the components of `Y` (components of `Y_H ×_X Y` over one component
  of `Y` are not separated; no cusps) and `B₀` of the divisors of theta monomials, so
  `B₀ → Φ₀^gp` is injective (in [EtTh] its kernel is `O^×`). The log-meromorphic functions on
  stable models of the universal combinatorial coverings are not available: the dependency
  `tempered-fundamental-groups` has projective models of finite levels and covering spaces of
  their special fibres, but no structure sheaf on infinite coverings.
* **Global realified Frobenioid**: `Φ^gp = (V_fin →₀ ℝ) × (V_∞ → ℝ)` with the coordinates
  `ord_w` (finite) and `−log|·|_v` (archimedean); rational functions the ℝ-span of the principal
  divisors. The non-realified Frobenioid of [FrdI], Example 6.3 (with `ℤ`-coefficients at the
  finite places and `B = K^×`) is not separately built.

## Category-theoreticity (MR16)

[FrdI], Theorem 3.4 is proved for **model Frobenioids** (every Frobenioid of IUT is built as a
model, [FrdI], Theorem 5.2) under the following hypotheses, which hold for the `p`-adic,
archimedean and tempered Frobenioids of IUT (`B(G/H) = (K̄^H)^× ⊇ μ_n` for `H` small) over the
Galois base categories
`B(G)⁰`:

* `BaseHyp D`: `D` is of FSM-type and of Aut-type (`OrbitObj.baseHyp`: true for `B(G)⁰`,
  `G` compact);
* `HasAllTorsion B`: torsion of every order occurs cofinally in `B` (for every `A`, `n ≥ 2`
  there are `A' → A` and `1 ≠ b ∈ B(A')` with `bⁿ = 1`);
* for (iv)/(v): `IsSlim D₂` ([FrdI] §0), true for `B(G)⁰` with `G` slim profinite
  (`OrbitObj.isSlim`), and for the Frobenius degree a unit of infinite order
  (`HasNonTorsionUnit`).

Results (`F : C₁ ⥤ C₂` an equivalence):

* `ModelTypes.lean`: category-theoretic characterizations: **pre-steps = FSM-morphisms**
  (`isPreStep_iff_isFSM`), base-isomorphisms = morphisms between ends of a span of pre-steps,
  pull-backs = minimal-adjoint to base-isomorphisms, linear = (pre-step) ≫ (pull-back), Frobenius
  type = minimal-coadjoint to linear, isometries = (Frobenius type) ≫ (pull-back);
  `Invariance.lean`: their transport by equivalences.
* `Thm34.lean`: `Model.thm34_preservesFrobeniusStructure` (Theorem 3.4(ii), (iii): all morphism
  types and the Frobenius degree up to an automorphism `σ` of `ℕ_{≥1}`; Prop. 1.10(i) for linear
  morphisms is `exists_linear_square`).
* `Thm34Base.lean`: `Model.base_map_eq_of_base_eq` (co-objective morphisms with the same base go
  to morphisms with the same base) and `Model.thm34_preservesBase` (Theorem 3.4(v)), by a direct
  slimness argument replacing the 2-categorical construction of [FrdI].
* `Thm34iv.lean`: `O^▷`, `O^×` are preserved (Theorem 3.4(iv)); `degFr_map_eq`: `σ = id`.
* `GaloisBase.lean`, `GaloisSlim.lean`: the hypotheses for `B(G)⁰`; `Model.thm34_galois`,
  `Model.thm34_galois_preservesBase`; `GaloisExample.lean`: a model Frobenioid over `B(G)⁰`
  satisfying all hypotheses (`GaloisExample.thm34`, `GaloisExample.thm34_base`).
* `DivOrder.lean`: Corollary 4.11(iii) as ordered sets: an equivalence matching pre-steps induces
  order isomorphisms `Model.divEquiv : Φ₁(A_X) ≃ Φ₂(A_{F X})` with `Div(F φ) = τ_X(Div φ)` for
  every pre-step `φ` out of `X` (`Model.div_map_preStep`).
* `Thm34Rlf.lean`: a second route for realified Frobenioids (torsion-free `B`) over groupoid
  bases whose divisor monoids have no irreducible elements: irreducible morphisms are the
  isometries of prime Frobenius degree (`Model.isIrreducible_of_prime`,
  `Model.not_linear_of_irreducible`), linear morphisms are those mid-adjoint to the irreducible
  ones (`Model.isLinear_iff_midAdj`); `Model.thm34_groupoid` and
  **`GlobalRealified.thm34`** (every equivalence `C^⊩(K) ≌ C^⊩(L)` of global realified
  Frobenioids, IUT I, Example 3.5, preserves the Frobenius structure).

**Erratum found on the way** (`Counterexample.lean`): [FrdI], Proposition 1.14(iii), on which
the published proof of Theorem 3.4(ii) relies, fails for Frobenioids whose rational functions
have torsion of every order (prime-Frobenius morphisms are then not monomorphisms, hence not
FSMI-morphisms). The statement of Theorem 3.4(ii) itself holds in that case (above).

## What remains

* [FrdI], Theorem 6.4(iv): its proof uses Chebotarev-type splitting (Bauer's theorem is now
  `NumberField.le_of_splitsCompletely`, `Iut/NumberTheory/KroneckerDensity`) and Theorem 3.4 for
  the non-realified `GlobalFrobenioid` over `Pt`, whose `μ(K)` is finite (Frobenius morphisms are
  not monomorphisms; neither route of `Thm34.lean`, `Thm34Rlf.lean` applies). Theorem 6.4(iii) is
  `Thm64iii.lean` (via Lemma 6.5 from `Iut/NumberTheory/SixExponentials`).
* Theorem 3.4 for Frobenioids that are not models, or (outside the realified case of
  `Thm34Rlf.lean`) whose rational functions lack torsion of some order cofinally (e.g. a
  non-realified global Frobenioid over `Pt` with finite `μ(F)`); (iv)/(v) for the realified
  case;
  Corollary 4.10, 4.11 for general Frobenioids (birationalization; `Ψ_Φ` is built for `C^⊩` in
  `Cor411Rlf.lean`); Theorem 6.4(ii) for realified Frobenioids
  over Galois bases `B(G)⁰` other than `Pt` (for `C^⊩(K)` over `Pt` it is `Thm64.lean`).
* Propositions 1.9(v)–(vii), 1.10, 1.11(iv)–(vii), 1.13, 1.14 for general Frobenioids (the
  model-level versions needed for Theorem 3.4 are in `ModelTypes.lean`, `Thm34.lean`).
* The tempered Frobenioid with the genuine monoids (log-divisors on stable models of the
  universal combinatorial coverings `Z^log_∞`, separated components and cusps; the
  log-meromorphic functions, including `Θ̈` itself rather than its divisor), see `Tempered.lean`.
* Poly-Frobenioids and prime-strips ([FrdII] §5; IUT I §5), the Θ-link as a
  poly-isomorphism of `F^{⊩▶×μ}`-prime-strips.
