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
   * (c) `Tempered.lean`: the shape of the tempered Frobenioid (base category = connected
     tempered coverings, divisor monoid of the theta-values) as an explicit interface
     structure; construction left as documented data.
4. **Category-theoreticity** (`Theoreticity.lean`): precise statements of [FrdI] Theorem
   3.4(iii)/(v) and Corollary 4.11 (`PreservesFrobeniusStructure`, …); proved: within the
   model Frobenioid, the elementary types are characterized category-theoretically
   (isomorphisms, pre-steps vs. the order on `Φ(A)`, `Pic`), and for the global realified
   Frobenioid the degree is invariant under the `ℝ_{>0}`-scaling automorphisms up to the
   scalar ([FrdI] Theorem 6.4(ii) for scalings). The general Theorem 3.4 is research-level
   (it depends on [FrdI] Propositions 1.4–1.14) and is recorded as such.
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
| 3(c) tempered | `Tempered.lean` | interface `TemperedFrobenioidData`, `TemperedFrobenioidData.isFrobenioid` |
| 4 category-theoreticity | `Theoreticity.lean` | statements `PreservesFrobeniusStructure`, `PreservesBase`; `scale_preserves`, `endZeroEquiv`, `inducedDegAut` |
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
* **Base categories** of the concrete instances are the one-morphism category `Pt` (trivial
  Galois extension), as in IUT I, Example 3.5(i) for `C^⊩_mod`. The Galois-category bases
  `B(G)⁰` of [FrdI], Example 6.3 / [FrdII], Example 1.1 are not formalised.
* **Global realified Frobenioid**: `Φ^gp = (V_fin →₀ ℝ) × (V_∞ → ℝ)` with the coordinates
  `ord_w` (finite) and `−log|·|_v` (archimedean); rational functions the ℝ-span of the principal
  divisors. The non-realified Frobenioid of [FrdI], Example 6.3 (with `ℤ`-coefficients at the
  finite places and `B = K^×`) is not separately built.

## What remains

* [FrdI], Theorem 3.4 / Corollary 4.11 for arbitrary equivalences (research-level here, see
  `Theoreticity.lean`); Theorem 6.4(ii) for arbitrary equivalences of realified Frobenioids.
* The tempered Frobenioid construction (connected tempered coverings, log-divisors on universal
  combinatorial coverings, the theta function), see `Tempered.lean`.
* Poly-Frobenioids and prime-strips ([FrdII] §5; IUT I §5), the Θ-link as a
  poly-isomorphism of `F^{⊩▶×μ}`-prime-strips.
