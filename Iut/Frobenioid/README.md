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
     `Model.iso_iff`).
3. **Concrete instances.**
   * (a) `Global.lean`: the **global realified Frobenioid** `C^⊩` of a number field `K`
     (one-morphism base, divisor monoid the effective ℝ-arithmetic divisors
     `(V_fin →₀ ℝ_{≥0}) × (V_∞ → ℝ_{≥0})`, rational functions `ℝ·div(K^×)`); the arithmetic
     degree `deg^arith` ([FrdI] Example 6.3), its vanishing on rational functions, the degree
     `δ` on objects (an isomorphism invariant, Theorem 6.4(i)); the objects of arithmetic line
     bundles (`ofBundle`) and **`degree_ofBundle : δ(ofBundle L) = deg L`** (and `degNorm`).
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

## Encoding choices and simplifications

(to be completed per milestone, see the sections below)
