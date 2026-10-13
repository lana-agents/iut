# Equivalent formulations of the wall (`Iut/WallEquiv/`, next-step 6)

The *wall* is the step of IUT III from Theorem 3.11 to Corollary 3.12 that the LANA report could
not reconstruct ([LANA], §9.2). This directory collects its formulations — in the sources and in
this repository — and the equivalences between them that hold in the models built here
(`Basic.lean`). Nothing here proves or refutes any formulation: the Scholze–Stix inequality
`SSIneq D` and its negation are both open in the repository.

Notation: `D` initial Θ-data, `s = sFactor ℓ*` (`s > 1`, `one_lt_wallS`), `|log q|` the `q`-pilot
degree, `VC(I)` the container, `log-vol` the procession-normalized log-volume; the *models* are
the identified-copies η-algorithm `idAlg D` / `idAlgOn D σ`, the η-algorithm over P18 Hodge
theaters `theaterAlg D H` (identified-copies output law), the multi-container models
`idModel`, `theaterModel` (all Kummer identifications the identity) and the log-theta-lattices of
P20 with unit-induced Kummer data (`LatticeKummer`, `LGPLattice`).

## Table

| # | Formulation | Source | Lean name | Equivalence proved | Scope |
|---|---|---|---|---|---|
| 1 | **Scholze–Stix inequality** `(s − 1)·\|log q\| ≤ log-vol(VC(I))` | Scholze–Stix; [LANA] §10 | `Wall.SSIneq D` | reference point | — |
| 2 | **(9-1) literal on Hodge theaters**: for every Θ-link `ThetaLinkIso D (H h₁) (H h₂)` there are `ι`, `S` with `η^anab_{ι,S} = η_q : R_val → R_ss ≅ ℝ` | [LANA] §9.2 (9-1), pp. 45–46 | `WallEquiv.Lana91 D H` | ⇔ 1: `lana91_iff_ss` | every family `H` of P18 Hodge theaters |
| 3 | **(9-1) on the BPS layer**: for every BPS-level Θ-link there are `ι`, `S` with `η^anab_{ι,S} = η_q` | [LANA] §9.2 | `Wall D A` (`Iut/Wall/EtaAlg.lean`) | ⇔ 2 for `A = theaterAlg D H`: `lana91_iff_wall`; ⇔ 1: `wall_theaterAlg_iff_ss`, `wall_idAlg_iff`, and for **every** `A` with the identified-copies output law: `wall_iff_ss_of_thetaShift` | the models; in general 3 ⇒ 7 (`variant_of_wall`) |
| 4 | **(9-1) for one `(ι, S)` as an equation of numbers**: `η^anab_{ι,S} = η_q ↔ log-vol(out ι S) = −\|log q\|` | [LANA] §9.2 | `EtaAlg.etaAnab_eq_etaQ_iff` | always (any `A`) | general |
| 5 | **∃ S with `log-vol(LGP·S) = −\|log q\|`** | [LANA] §9.2–9.3 | `WallEquiv.Exists91 D` | ⇔ 1: `exists91_iff_ss` | identified-copies law |
| 6 | **(xi)-principle** (Step (xi) of the proof of Cor. 3.12) | IUT III, Cor. 3.12, Step (xi) | `LogLink.XiPrinciple K` | ⇔ 1: `xi_iff_ss_model` (any lattice with unit-induced Kummer data), `xi_iff_ss_lgp_model` (LGP-Gaussian lattices) | P20 lattice model |
| 7 | **Corollary 3.12 variant** `−\|log q\| ≤ −\|log Θ\|` | IUT III Cor. 3.12 with IUT IV's reading of (Ind1) | `Corollary312Variant (concreteVariantData D)` | 1 ⇒ 7: `variant_of_ss`; 7 ⇔ 8 ⇔ 9: `variant_iff` | general; 7 ⇏ 1 in general (9 uses *some* algorithm) |
| 8 | **numerical (9-1)**: an adelic region in the hull of an (Ind1)-image with `η = η_q` | [LANA] §9.2 (shadow lemma) | `Wall.NumericalWall D` | ⇔ 7: `numericalWall_iff` | general |
| 9 | **∃ η-algorithm with (9-1)** | — | `∃ A, Wall D A` | ⇔ 7: `exists_wall_iff` (trivial instance) | general |
| 10 | **multi-container walls** `Wall3`, `WallOn L` | wall milestone M3 | `MultiContainer.Wall3`, `WallOn` | ⇔ 1 for `idModel`, `theaterModel`: `wall3_idModel_iff`, `wall3_theaterModel_iff`; in general `WallOn L ↔ ∀ L h₁ h₂, (s − 1)·\|log q\| − distortion ≤ log-vol(VC(I))` (`wallOn_iff_of_thetaShift`) | models with the identified-copies law |
| 11 | **`R_ss` form**: the classes of the transported output and of the `q`-pilot region agree | [LANA] §9.2 | `MultiContainer.wallOn_iff_rss` | ⇔ 10 | general |
| 12 | **Corollary 3.12 literal** (union over label permutations) | IUT III, Cor. 3.12 | `Cor312LiteralHolds` | `Cor312VariantHolds ⇒ Cor312LiteralHolds` (`cor312Literal_of_variant`) | global |
| 13 | **ABC** | — | `ClassicalABC` | `(∀ D, SSIneq D) ⇒ Cor312VariantHolds ⇒ ClassicalABC` (`classicalABC_of_ss`) | global |
| — | **hexagon** (`deg_Θ = s·(Θ-link)`): commutes iff `s = 1` | [LANA] §10.2, §10.5; Scholze–Stix | `hexagon_commutes_iff`, `InitialThetaData.hexagon_not_commutes` | proved fact (`s > 1`), the source of the factor `s` in 1 | — |
| — | **Frobenioid form**: the Θ-pilot and `q`-pilot objects of the global realified Frobenioid are not isomorphic | IUT II Cor. 4.10(v); P15 | `Frobenioid.isEmpty_iso_thetaPilot_qPilot` | proved fact | — |

All of 2, 3 (for `theaterAlg`/`idAlg`), 5, 6, 10 (for the identified-copies models) are collected
in **`WallEquiv.wallEquiv`**, with `wall_facts` for the last two rows.

## General vs model

* **General** (any η-algorithm satisfying the interface (T1)–(T3)): 3 ⇒ 7 (`variant_of_wall`),
  4, 7 ⇔ 8 ⇔ 9, 10 ⇔ 11, the distortion formula of 10, 12, 13.
* **Only in the models** (identified-copies output law, zero distortion — e.g. unit-induced Kummer
  identifications, `Iut/LogLink`): 1 ⇔ 2 ⇔ 3 ⇔ 5 ⇔ 6 ⇔ 10. A formulation different from (SS)
  needs an η-algorithm whose output law is not `LGP` acting on an (Ind3)-choice, or a transport
  with nonzero distortion (a Kummer identification that is not unit-induced).
* 7 does **not** imply 1 in general: 9 (an η-algorithm with (9-1)) holds whenever 7 holds, through
  the trivial instance, while 1 is (9-1) for the algorithms of the models.
