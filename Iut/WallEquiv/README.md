# Equivalent formulations of the wall (`Iut/WallEquiv/`, next-step 6)

The *wall* is the step of IUT III from Theorem 3.11 to Corollary 3.12 that the LANA report could
not reconstruct ([LANA], §9.2). This directory collects its formulations — in the sources and in
this repository — and the equivalences between them that hold in the models built here
(`Basic.lean`, `Forms.lean`). Nothing here proves or refutes any formulation: the Scholze–Stix inequality
`SSIneq D` and its negation are both open in the repository.

**Hull switch.** `SSIneq D` is `(s − 1)·|log q| ≤ log-vol(hull(VC(I)))`: the right-hand side is
the log-volume of the holomorphic hull of the log-shell container, IUT's container volume
(IUT III, Cor. 3.12, Step (xi-d)–(xi-f); IUT IV, Thm. 1.10; `VcI.md`), and the (Ind3)-choices
are the adelic `S ⊆ hull(VC(I))` (`Iut/Wall/Ind3.lean`). The no-hull wall `SSIneqNoHull D`
(`≤ log-vol(VC(I))`; numerically false on many Szpiro-record curves; not IUT's container) is
kept and implies `SSIneq D` (`ssIneq_of_noHull`).

Notation: `D` initial Θ-data, `s = sFactor ℓ*` (`s > 1`, `one_lt_wallS`), `|log q|` the `q`-pilot
degree, `VC(I)` the log-shell container, `hull(VC(I))` its holomorphic hull, `log-vol` the procession-normalized log-volume; the *models* are
the identified-copies η-algorithm `idAlg D` / `idAlgOn D σ`, the η-algorithm over P18 Hodge
theaters `theaterAlg D H` (identified-copies output law), the multi-container models
`idModel`, `theaterModel` (all Kummer identifications the identity) and the log-theta-lattices of
P20 with unit-induced Kummer data (`LatticeKummer`, `LGPLattice`).

## Table

| # | Formulation | Source | Lean name | Equivalence proved | Scope |
|---|---|---|---|---|---|
| 1 | **Scholze–Stix inequality** `(s − 1)·\|log q\| ≤ log-vol(hull(VC(I)))` | Scholze–Stix; [LANA] §10; container: IUT III Cor. 3.12 Step (xi-d)–(xi-f) | `Wall.SSIneq D` | reference point | — |
| 1' | **no-hull wall** `(s − 1)·\|log q\| ≤ log-vol(VC(I))` | [LANA] §6 read literally | `Wall.SSIneqNoHull D` | 1' ⇒ 1 (`ssIneq_of_noHull`); local form `ssIneqNoHull_iff_packets`, `ssNoHull_iff_lgp_vcI` | always |
| 2 | **(9-1) literal on Hodge theaters**: for every Θ-link `ThetaLinkIso D (H h₁) (H h₂)` there are `ι`, `S` with `η^anab_{ι,S} = η_q : R_val → R_ss ≅ ℝ` | [LANA] §9.2 (9-1), pp. 45–46 | `WallEquiv.Lana91 D H` | ⇔ 1: `lana91_iff_ss` | every family `H` of P18 Hodge theaters |
| 3 | **(9-1) on the BPS layer**: for every BPS-level Θ-link there are `ι`, `S` with `η^anab_{ι,S} = η_q` | [LANA] §9.2 | `Wall D A` (`Iut/Wall/EtaAlg.lean`) | ⇔ 2 for `A = theaterAlg D H`: `lana91_iff_wall`; ⇔ 1: `wall_theaterAlg_iff_ss`, `wall_idAlg_iff`, and for **every** `A` with the identified-copies output law: `wall_iff_ss_of_thetaShift` | the models; in general 3 ⇒ 7 (`variant_of_wall`) |
| 4 | **(9-1) for one `(ι, S)` as an equation of numbers**: `η^anab_{ι,S} = η_q ↔ log-vol(out ι S) = −\|log q\|` | [LANA] §9.2 | `EtaAlg.etaAnab_eq_etaQ_iff` | always (any `A`) | general |
| 5 | **∃ S with `log-vol(LGP·S) = −\|log q\|`** | [LANA] §9.2–9.3 | `WallEquiv.Exists91 D` | ⇔ 1: `exists91_iff_ss` | identified-copies law |
| 6 | **(xi)-principle** (Step (xi) of the proof of Cor. 3.12) | IUT III, Cor. 3.12, Step (xi) | `LogLink.XiPrinciple K` | ⇔ 1: `xi_iff_ss_model` (any lattice with unit-induced Kummer data), `xi_iff_ss_lgp_model` (LGP-Gaussian lattices) | P20 lattice model |
| 7 | **Corollary 3.12 variant** `−\|log q\| ≤ −\|log Θ\|` | IUT III Cor. 3.12 with IUT IV's reading of (Ind1) | `Corollary312Variant (concreteVariantData D)` | 1 ⇒ 7: `variant_of_ss`; 7 ⇔ 8 ⇔ 9: `variant_iff` | general; 7 ⇏ 1 in general (9 uses *some* algorithm) |
| 8 | **numerical (9-1)**: an adelic region in the hull of an (Ind1)-image with `η = η_q` | [LANA] §9.2 (shadow lemma) | `Wall.NumericalWall D` | ⇔ 7: `numericalWall_iff` | general |
| 9 | **∃ η-algorithm with (9-1)** | — | `∃ A, Wall D A` | ⇔ 7: `exists_wall_iff` (trivial instance) | general |
| 10 | **multi-container walls** `Wall3`, `WallOn L` | wall milestone M3 | `MultiContainer.Wall3`, `WallOn` | ⇔ 1 for `idModel`, `theaterModel`: `wall3_idModel_iff`, `wall3_theaterModel_iff`; in general `WallOn L ↔ ∀ L h₁ h₂, (s − 1)·\|log q\| − distortion ≤ log-vol(hull(VC(I)))` (`wallOn_iff_of_thetaShift`) | models with the identified-copies law |
| 11 | **`R_ss` form**: the classes of the transported output and of the `q`-pilot region agree | [LANA] §9.2 | `MultiContainer.wallOn_iff_rss` | ⇔ 10 | general |
| 12 | **Corollary 3.12 literal** (union over label permutations) | IUT III, Cor. 3.12 | `Cor312LiteralHolds` | `Cor312VariantHolds ⇒ Cor312LiteralHolds` (`cor312Literal_of_variant`) | global |
| 14 | **volume of `LGP·hull(VC(I))`**: `−\|log q\| ≤ log-vol(LGP·hull(VC(I)))` | [LANA] §9.1(i), §10 | `WallEquiv.ss_iff_lgp_vcI` | ⇔ 1 | always (uses the volume of `LGP`, `logVol_lgp`) |
| 15 | **(Ind3)-choice of volume `(s − 1)·\|log q\|`**: `∃ S ⊆ hull(VC(I))` with `log-vol(S) = (s − 1)·\|log q\|` | [LANA] §9.3 | `WallEquiv.ss_iff_exists_ind3` | ⇔ 1 | always |
| 16 | **pilot degrees**: `deg_Θ(Θ-pilot) − deg(q-pilot) ≤ log-vol(hull(VC(I)))` | [LANA] §7.1(a), §10.2 | `WallEquiv.ss_iff_pilot_degrees` (`pilot_degrees_sub`: the difference is `(s − 1)·\|log q\|`) | ⇔ 1 | always |
| 17 | **through the Θ-link**: `s·deg(Θ-link(Θ-pilot)) − deg(q-pilot) ≤ log-vol(hull(VC(I)))` | [LANA] §10.2; IUT II Cor. 4.10 | `WallEquiv.ss_iff_theta_link_degrees` | ⇔ 1 | always |
| 18 | **the gap** `Δ(D) = −\|log Θ\| − log-vol(LGP·hull(VC(I)))`: (SS) ⇔ `−\|log q\| ≤ −\|log Θ\| − Δ(D)`, (Var) ⇔ `−\|log q\| ≤ −\|log Θ\|` | — | `WallEquiv.gap D` (`Gap.lean`) | `ss_iff_le_rhs_sub_gap`, `variant_iff_le_rhs`; `gap_nonneg`; `gap_eq`: `Δ(D)` is the average of the (Ind2)-terms at the bad primes (sign beyond `≥ 0` open); the no-hull gap `gapNoHull` has `gapNoHull_pos` | always |
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

## The gap between (Var) and (SS) (`Gap.lean`)

Christian's question: *is the LANA wall any weaker than the Scholze–Stix wall?* **With the hull
(IUT's container): by `Δ(D) ≥ 0`, which consists only of the (Ind2)-terms at the bad residue
characteristics; whether it is `> 0` is open.** Against the no-hull wall the answer is "yes,
strictly, `Δ_noHull(D) > 0` for every `D`", and the difference is exactly the hull defect of the
container.

Both walls compare `−|log q|` with a log-volume:

* **(Var)** (the LANA/variant wall, row 7): `−|log q| ≤ R`, `R = −|log Θ| = log-vol(hull(Θ))`,
  the log-volume of the holomorphic hull of one (Ind1)-image of the theta-pilot region
  (`rhs_eq_logVol_image`);
* **(SS)** (row 14): `−|log q| ≤ log-vol(LGP·hull(VC(I)))`;
* (no-hull, row 1'): `−|log q| ≤ log-vol(LGP·VC(I))`.

`LGP·hull(VC(I))` lies in the hull of that (Ind1)-image (`inHullOfImage_lgp`: the hull commutes
with the unit scaling `LGP`), so `log-vol(LGP·hull(VC(I))) ≤ R` (`logVol_lgp_vcI_le_rhs`). The
**gap** is

`Δ(D) := R − log-vol(LGP·hull(VC(I))) = −|log Θ| + s·|log q| − log-vol(hull(VC(I)))`
(`WallEquiv.gap`, `gap_eq_rhs_add`),

and (`ss_iff_le_rhs_sub_gap`, `variant_iff_le_rhs`)

* (SS) ⇔ `−|log q| ≤ R − Δ(D)`, (Var) ⇔ `−|log q| ≤ R`;
* `Δ(D) = 0` would make them the same inequality (`ss_iff_variant_of_gap_eq_zero`);
* (Var) holds and (SS) fails exactly when `−|log q| ∈ (R − Δ(D), R]`, a window of length `Δ(D)`
  (`variant_and_not_ss_iff`).

**Formula** (`gap_eq`, `gapHullAt_eq`): with the tuple weights `w_c` of IUT III, Remark 3.1.1(ii),

`Δ(D) = (1/ℓ*) · ∑_{capsules i} ∑_{p} ∑_{tuples c} w_c · ind2Term(i, p, c)`,

`ind2Term = μ^log(hull(Θ_{i,p,c})) − μ^log(q^{j²}·hull(⊗𝓘)) ≥ 0`: the enlargement of the hull by
the (Ind2)-union of the images of `q^{j²}·⊗𝓘` under the indeterminacy automorphisms. With the
hull on both sides the archimedean term is `0` (both components are the least polydisc of the
log-shell, `thetaComponent_infinite`) and the shell defects cancel. `ind2Term = 0` away from the
bad residue characteristics (`gapHullAt_eq_zero`), so `Δ(D)` is a finite sum over the bad
residue characteristics; if the (Ind2)-terms vanish there, (SS) **is** (Var)
(`gap_eq_zero_of_ind2Term`, `ss_iff_variant_of_ind2Term`). **Open:** the value of the
(Ind2)-terms at the bad primes. The indeterminacy automorphisms at a prime are all
`ℤ_p`-lattice automorphisms of the factor log-shells (`tensorAut`); they do not commute with the
multiplication by `q^{j²}` in general, so `ind2Term > 0` is to be expected when `ord(q^{j²})` is
not a multiple of the ramification index, but this is not formalized.

**The no-hull gap** (`gapNoHull D := R − log-vol(LGP·VC(I))`). `gapNoHull_eq_gap_add`:
`Δ_noHull(D) = Δ(D) + (log-vol(hull(VC(I))) − log-vol(VC(I)))`. Its local formula (`gapNoHull_eq`)
has the terms

| place | local term `δ` | sign | Lean |
|---|---|---|---|
| `∞` | `archDefect`: the log-shell (the ball of radius `π^N` of the tensor-product metric) against its least polydisc `a·B_I`; the (Ind1)/(Ind2) automorphisms preserve the ball, so they contribute nothing (`thetaComponent_infinite`) | **`> 0`** for every tuple (`gapTerm_infinite_pos`) | `gapTerm_infinite`, `archDefect_pos` |
| prime `p` | `shellDefect + ind2Term`: the hull defect of `⊗_j 𝓘_{v_j}` (a discriminant/different-type term, independent of theta values and indeterminacies), plus the (Ind2)-term | both `≥ 0` | `gapTerm_finite`, `shellDefect_nonneg`, `ind2Term_nonneg` |
| `p` not a bad residue characteristic | `shellDefect` only (`ind2Term = 0`, theta values `1`) | `≥ 0` | `ind2Term_eq_zero` |
| `p` odd, unramified in `K`, not bad | `0` (the shell is `O`) | `= 0` | `gapTerm_eq_zero`, `shellDefect_eq_zero` |

and **`Δ_noHull(D) > 0` for every `D`** (`gapNoHull_pos`): `K ∋ √−1` is totally complex
(`InitialThetaData.isComplex_Kt`), every archimedean packet is a product of at least two copies
of `ℂ` (`exists_ne_maximalSpectrum`), and there the log-shell ball is strictly smaller than its
least polydisc (`componentVol_archLogShell_lt_leastHull`); `archPart_le_gapNoHull`,
`ssNoHull_imp_lt_rhs`. The shell defects and the archimedean defects are exactly the hull
defect of the container, which the hull switch removes; what remains between (SS) and (Var) is
the (Ind2)-enlargement at the bad primes.

**Not formalized.** The explicit value of the archimedean defect (`log((2^{N−1})!)/2^N` on paper,
see `VcI.md`), the exact value (or strict positivity) of the shell defect at `2` and at ramified
primes, and of the (Ind2)-term at the bad primes; only `≥ 0` is proved for these.

## Non-derivability (`NonDerivable.lean`)

**Theorem 3.11 of IUT III, as formalised here, does not imply Step (xi).** Lean-checked: no
argument that uses only the fields of `Thm311Package` proves Step (xi) (nor refutes it). That these
fields exhaust what the repository proves at the level of Theorem 3.11 is an audit (below), not a
theorem. Since Theorem 3.11 is a theorem of the model for every genuine `D`, non-derivability can
only be stated relative to such an abstraction.

* `Thm311Package`: everything the repository proves at the level of Theorem 3.11 about genuine
  initial Θ-data, with the arithmetic decoupled. Its numbers are the prime `ℓ` (prime, `≥ 5`),
  `ℓ* = (ℓ − 1)/2`, `s = sFactor ℓ*`, `log q`, `a = |log q| = log q/(2ℓ) > 0`,
  `V = log-vol(hull(VC(I)))` (the container, field `cont`), `R = −|log Θ|` and `R_lit`. Its structure is the log-volume calculus
  (integral region, archimedean scalings, mono-analytic scalings with their shift, the scaling by
  `q`), the (Ind3)-choices with volumes `(−∞, V]`, the identified-copies output law
  `vol(LGP·S) = −s·a + vol(S)` with outputs in the hull of the Θ-pilot region (volumes
  `(−∞, R]`), the `q`-pilot region (`−a`), and the log-theta-lattice `ℤ × ℤ` with log-shell
  compatible, volume-preserving (unit-induced) Kummer identifications, Θ-links, choices and
  multiradiality. The remaining conclusions of Theorem 3.11 and Theorem 1.5(v) proved in the
  model (`LogLink.thm311_full_model`) hold for every `D` and every Kummer data and do not involve
  the package's numbers; the package carries them as the field `structural`, a closed
  proposition provable outright that constrains nothing else (its numeric parts, the factor `1/s`
  of `Thm15v` and the degrees of `Thm311LGP.splitDeg`, concern the quantified `D`; their package
  counterparts are `vol_lgp`, `vol_qRegion`, `one_lt_s`, `hexagon`, `pilots_ne`).
* **Faithfulness**: `ofThetaData D K` builds the package of any lattice `K` over genuine `D`, every
  field a theorem of `main`; `xi_ofThetaData_iff : (ofThetaData D K).Xi ↔ XiPrinciple K`.
* **Sharp form**: `Thm311Package.xi_iff : P.Xi ↔ (s − 1)·a ≤ V` — over the package, Step (xi) is
  exactly the Scholze–Stix inequality.
* **Non-derivability**: `family` realises every `ℓ`, `log q > 0`, `V`, `R` with `V − s·a ≤ R` (the
  only proved relation coupling `V` with `a` and `R`; for genuine data it comes from
  `logVol_lgp`, `logVol_lgp_integral`, `inHullOfImage_lgp`, `logVol_le_rhs`; in the package it is
  `V_sub_le_R`);
  `not_xi_family`: Step (xi) fails there whenever `V < (s − 1)·a`; `exists_package_not_xi` (an
  explicit package: `ℓ = 7`, `a = 1`, `V = R = 1`), `exists_package_not_xi_nonneg` (failure with
  `0 ≤ V` for every `ℓ`, `log q`), `not_forall_xi : ¬ ∀ P, P.Xi`; and `exists_package_xi`
  (Step (xi) is not refutable either). `nonDerivability` collects faithfulness, the sharp form,
  `¬ ∀ P, P.Xi` and `¬ ∀ P, ¬ P.Xi`.
* **The missing input is ABC-strength**: `classicalABC_of_forall_xi` (Step (xi) for all genuine
  data gives `ClassicalABC`, via `classicalABC_of_thm311`).

**Audit.** The facts the repository proves about these numbers for all genuine `D` were audited
over `Iut/` (list in the module docstring). There is no lower bound on `V` and no relation
coupling `V` with `a` other than `V − s·a ≤ R`. The IUT IV estimate `R ≤ C'(D) − s'·a` with
`s' < s` (`LocalEstimate.rhs_le`) holds only under the hypothesis `LocalEstimate` /
`TowerArithmetic D` and bounds `V` from above, so it is compatible with the failure of Step (xi)
(`family` with `V` small). The bound `0 ≤ V` (mathematically `O ⊆ I`; not formalised globally)
is also compatible (`exists_package_not_xi_nonneg`), and so is every lower bound `L ≤ V` with
`L` independent of `a` (`exists_package_not_xi_ge`). **Re-audit after the hull switch**: the new
facts about `V = log-vol(hull(VC(I)))` are `log-vol(VC(I)) ≤ V` (`VC(I)` is not a package
number), the preservation of the hull by log-shell compatible scalings (`act_hull_vcI`, field
`logShell`), and the local formulas of `VcI.lean` (exact prime terms `∑ ρ_j·log p`, tame values
`d_I·log p ≥ 0`, wild sandwich bounds, `≤ |I|·log(√2π)` at `∞`). They bound `V` by the
ramification of `K`, never by `ord_v(q)`, so none couples `V` with `a`; by
`exists_package_not_xi_ge` and `not_xi_family` they cannot force Step (xi).

**What is shown, and what is not.** Shown: the formalised content of Theorem 3.11 (with
unit-induced Kummer identifications) is consistent with the failure of Step (xi), and over it
Step (xi) is equivalent to the Scholze–Stix inequality; a proof of Step (xi) must use facts about
`D` beyond this content, and Step (xi) for all genuine `D` implies ABC
(`classicalABC_of_forall_xi`). **Not shown**: that Step (xi) fails for some
genuine `D`, or that the Scholze–Stix inequality or ABC fails. The statement is about the
formalisation: the modelling inputs of the repository apply (local fields and the
log-volume calculus in place of Frobenioids, Hodge theaters with data strips (`StripKummer`,
`BiCoricKummer`, `MonoThetaKummer`), the identified-copies output law, the archimedean radial
normalization as an input; see `Iut/LogLink/README.md`). A different formalisation of
Theorem 3.11 (e.g. with an output law other than `LGP` acting on an (Ind3)-choice, or Kummer
identifications that are not unit-induced) is not covered.

## The log-volume of `VC(I)` and of its hull (`VcI.lean`, `VcI.md`)

Task VCI-CHECK. `logVol_vcI_eq` and `logVol_hull_vcI_eq` write `log-vol(VC(I))` and
`log-vol(hull(VC(I)))` as procession averages of weighted local terms. `logVol_hull_vcI_sub_eq`
writes their difference as the average of the shell defects and archimedean defects.

At a prime, `μ^log(⊗𝓘) = shellExcess + μ^log(R_I)` (`componentVol_tensorLogShell_eq`).
`μ^log(R_I) = −log[(R_I)^∼ : R_I]/n ∈ [−d_I·log p, 0]` is the packet index term. The hull is
exact at every prime: `μ^log(hull(⊗𝓘)) = ∑_j ρ_j·log p`
(`componentVol_leastHull_tensorLogShell_eq`).

At tame primes, `μ^log(hull(⊗𝓘)) = ∑_j (1 − 1/e_j)·log p` (`= d_I·log p`, IUT IV's container).
There the shell defect is exactly `−μ^log(R_I)` (`shellDefect_eq_neg_orderVol_tame`).

The verdict (`VcI.md`):

* IUT's container volume (Cor. 3.12, IUT IV Thm. 1.10) is the **hull**. **Switched**: `SSIneq` now
  uses `log-vol(hull(VC(I)))` and (Ind3) ranges over `hull(VC(I))`; the old wall is
  `SSIneqNoHull` (`ssIneqNoHull_iff_packets`; `ssIneq_iff_packets` now has the hull packets).
* At `∞` the repository keeps the log-shell of IUT III, Prop. 3.2(ii) (the unit ball of the
  tensor-product metric), whose hull exceeds the container of IUT IV, Thm. 1.10, Step (vii) by
  `((m−1)/2)·log 2` per packet of `m` factors (about `((ℓ+1)/8)·log 2` after procession
  averaging). This is conservative: the larger right-hand side only weakens `SSIneq`.
* The maximal-order normalization of `vcI` is faithful to IUT (IUT III Prop. 3.9(i), IUT IV
  Prop. 1.4(i),(iii)).
* `log-vol(VC(I))` drops the packet index term. On paper that term is `½·(d_I − d_T)·log p`,
  about ½·log-different per tensor factor beyond the first. IUT bounds this term by `0` and
  never uses it.
* Not formalized: the value of `μ^log(R_I)` (`PacketIndexFormulaGalois`), the additivity
  `shellExcess = ∑_j λ_j` (`ShellExcessAdditive`), and the exact archimedean values.
