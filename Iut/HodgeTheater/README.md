# Hodge theaters (`Iut/HodgeTheater/`, roadmap P18)

A Lean formulation of the **prime-strips, bridges and Hodge theaters** of IUT I, §4–§6 (with
the Frobenioid-theoretic prime-strips of IUT I, §5 and IUT II, Definition 4.9), built from initial
Θ-data `D : InitialThetaData` (`Iut/Cor312/ThetaData`) and the Frobenioids of P15
(`Iut/Frobenioid/`), and the connection to the multi-container model of the wall
(`Iut/Wall/MultiContainer.lean`).

Source: IUT I in its text extraction (`~/iut-scratch/wall/txt/`); definition, example and
proposition numbers are those of IUT I unless stated otherwise.

**Status of the dependency.** No module of this directory is imported by the comparator challenge
(`Comparator/Challenge.lean`) or by `Iut/Concrete/*`.

## Scope decisions (read first)

The definitions of IUT I §4–§6 have two layers.

1. **The objects** (categories `D_v ≃ B^temp(Π_v)^0`, Aut-holomorphic orbispaces, Frobenioids,
   …) and the **group-theoretic algorithms** which reconstruct from them their *labels*
   (`LabCusp(†D_v)`, the `±`-label classes, the evaluation sections of Example 4.4, the sign
   `Aut(†D_v) ↠ {±1}`). The reconstruction algorithms are anabelian ([AbsTopI] Lemma 4.5,
   [AbsTopIII] Theorem 1.9, [EtTh] Corollary 2.9, [SemiAnbd]) and belong to roadmap package
   **P17**; they are not formalised here.
2. **The combinatorics** of the labels: `F_ℓ^* = F_ℓ^×/{±1}`, `|F_ℓ| = F_ℓ/{±1}`,
   `F_ℓ^{⋊±} = F_ℓ ⋊ {±1}`, `F_ℓ^±`-groups and `F_ℓ^±`-torsors, the bridges as label data,
   their isomorphism sets, the symmetries, the gluings and the processions. This is the content
   of Propositions 4.2, 4.7–4.11, 6.5–6.9 and Corollaries 5.6, 6.12 that "follows immediately
   from the definitions", and it is **formalised in full** here.

Accordingly:

* **Prime-strips (object layer)** are families, indexed by `V ≅ V_mod` (the places of
  `F_mod`, `Place D.Fmod`), of objects of a *kind* (a type of objects with isomorphisms) that are
  isomorphic to a **model built from `D`**: `Π_v` (tempered at `V^bad`, étale at `V^good ∩ V^non`,
  `LocalThetaData.PivBad/PivGood`), the decomposition groups `G_v`, the `p`-adic Frobenioids of
  P15, a minimal **archimedean Frobenioid** (`Arch.lean`), the GM-data `G_v ↷ O^{×μ}` (the
  wall's `GMData`), and the global realified Frobenioid `C^⊩` of P15.
* **Labels (label layer).** A `D`-prime-strip is recorded, for the label combinatorics, by its
  `±`-label classes `LabCusp^±(†D_v)` with their `F_ℓ^±`-group structure at every `v`; a
  `+`-full poly-isomorphism is an isomorphism of `F_ℓ^±`-groups at each `v`; a *full*
  poly-isomorphism is determined by its source and target and is not recorded (it is unique),
  so capsule-full poly-isomorphisms are bijections of index sets. Poly-morphisms of bridges are
  recorded through the labels they determine (Examples 4.3, 4.4, 6.2, 6.3).
* The link "labels are reconstructed from the objects" is P17 and is not asserted.

## Plan (lemma-level milestones)

1. **Labels** (`Labels.lean`; IUT I §4 beginning, Definition 6.1(i)).
   * `FlStar ℓ = F_ℓ^×/{±1}`, `AbsFl ℓ = F_ℓ/{±1}`, `card_flStar : |F_ℓ^*| = ℓ*`,
     `card_absFl : ||F_ℓ|| = ℓ± = ℓ* + 1`, the embedding `F_ℓ^* ↪ |F_ℓ|` onto the nonzero classes,
     `absRep : |F_ℓ| ≃ {0, …, ℓ*}` (minimal representatives).
   * `FlSemi ℓ = F_ℓ^{⋊±}` (affine maps `z ↦ ±z + λ` of `F_ℓ`), `card_flSemi = 2ℓ`, the sign
     `FlSemi → {±1}`, transitivity on `F_ℓ` with stabilizers of order two (Proposition 6.8(i)).
   * `PmGroup` (`F_ℓ^±`-group), `PmTorsor` (`F_ℓ^±`-torsor), `StarTorsor` (`F_ℓ^*`-torsor) with
     their isomorphisms; `PmGroup.isoEquiv : Iso A B ≃ {±1}`,
     `PmTorsor.isoEquiv : Iso A B ≃ F_ℓ^{⋊±}`, `StarTorsor.isoEquiv : Iso A B ≃ F_ℓ^*`.
2. **Processions** (`Procession.lean`; Definition 4.10, Propositions 4.11, 6.9).
   * `prcStar`, `prcPm` (the `ℓ*`- and `ℓ±`-processions `S^*_j = {1..j}`, `S^±_t = {0..t−1}`),
     capsule cardinalities, the label-indeterminacy counts `∏ n = n!` versus `n^n`;
   * Proposition 6.9(iii): `S^*_j ↪ S^±_{j+1}`;
   * the standard procession of `Iut/Cor312/Procession.lean` (used by the container of
     `Iut/Concrete/Container.lean` and the wall) is the procession `S^±_2 ⊆ ⋯ ⊆ S^±_{ℓ±}`
     (`standard_eq_prcPm_tail`).
3. **Bridges and `D`-Hodge theaters (label layer)** (`Bridge.lean`, `PmBridge.lean`).
   * `D-NF-`, `D-Θ-bridges`, `D-ΘNF-Hodge theaters` (Definition 4.6): isomorphism sets
     `≃ F_ℓ^*`, unique, unique (Proposition 4.8(i), (ii)); gluings `≃ F_ℓ^*` (4.8(iii));
     the symmetries of Proposition 4.9; processions of `D-Θ-bridges` (4.11).
   * `D-Θ^±-`, `D-Θ^ell-bridges`, `D-Θ^{±ell}-Hodge theaters` (Definition 6.4):
     isomorphism sets `≃ {±1} × {±1}^V`, `≃ F_ℓ^{⋊±}`, `≃ {±1}` (Proposition 6.6(i)–(iii));
     the `D-Θ`-bridge of a `D-Θ^±`-bridge (Proposition 6.7); symmetries (6.8); processions
     (6.9).
   * the models of Examples 4.3, 4.4, 6.2, 6.3 built from the prime `ℓ` of `D`.
4. **Prime-strips (object layer)** (`Kind.lean`, `Arch.lean`, `PrimeStrip.lean`).
   * kinds (`Kind`), prime-strips of a kind relative to a model, isomorphisms, capsules,
     `nonempty_iso`;
   * the models built from `D`: `D`-, `D^⊢`-, `F`-, `F^⊢`-, `F^{⊢×μ}`-, `F^⊩`-prime-strips
     (Definitions 4.1, 5.2; IUT II Definition 4.9); the archimedean Frobenioid.
5. **`Θ^{±ell}NF`-Hodge theaters** (`HodgeTheater.lean`; Definitions 6.11, 6.13).
   * the structure gluing a `D-Θ^{±ell}`-Hodge theater and a `D-ΘNF`-Hodge theater along
     Proposition 6.7, with `F`-prime-strips on every index and the `F^⊩`-prime-strip;
     isomorphisms `≃ {±1}`; the theater built from `D` (`ofData`).
6. **The wall** (`Wall.lean`).
   * an η-algorithm whose Hodge theaters are `Θ^{±ell}NF`-Hodge theaters built from `D`, whose
     étale-unit BPSs are the `F^{⊢×μ}`-prime-strips of the theaters (pulled back from `V_mod` to
     the places of `F` used by the wall), and the multi-container model over it; its Kummer
     isomorphisms are those of the theaters (identities: every theater carries the arithmetic
     holomorphic structure of `D`), and the procession of its containers is the procession of
     the theaters' `±`-label capsules.

## Status

(to be filled in as the milestones are completed)
