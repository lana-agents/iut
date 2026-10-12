# The wall, Milestones 1–2 (`Iut/Wall/`)

A Lean formulation of **the wall** of the LANA interim report (July 2026; cited **[LANA]**;
PDF page numbers equal printed page numbers): the equation **(9-1)**

> there exists some suitable `S` such that `η_q = η^anab_S` ([LANA], §9.2, pp. 45–46),

together with a proof that it implies the Corollary 3.12 variant `Corollary312Variant
(concreteVariantData D)`, and checks of how much the formulation actually says. Tracked as
taxis [#1450](https://taxis.lana.merten.dev/issues/1450).

**Status of the dependency.** No module of `Iut/Wall/` is imported by the comparator challenge
(`Comparator/Challenge.lean`) or by the trusted closure of `Iut.Concrete.ThetaRegion`; the
wall is a `Prop` (`Iut.Wall`) that enters only as a hypothesis. Every theorem below uses only
`propext`, `Classical.choice` and `Quot.sound`.

## Files

* `BPS.lean` (M1a): BPSs — `GMData`, `GMIso`, `EtUnitBPS`, `ValBPS` with product formula
  `PF`, `BPS`, and their isomorphisms.
* `Pilots.lean` (M1a): `sFactor`, `qVal`, `thetaVal`, `thetaLink`, `degTheta`; the `q`-pilot
  of `D`.
* `Rss.lean` (M1b): `Region`, `IsAdelic`, `logVol`, `Rss`, `rssEquiv`, `etaQ`,
  `logVol_le_rhs`, `exists_adelic_iff`.
* `Ind3.lean` (M1b/c): the log-shell container `vcI`, the (Ind3)-choices `Ind3`.
* `EtaAlg.lean` (M1c): `EtaAlg`, `Iut.Wall`, `variant_of_wall`, `literal_of_wall`,
  `classicalABC_of_wall`.
* `Checks.lean` (M1d (i), (ii)): shadow lemma, trivial instance, LGP law (T4).
* `IdentifiedCopies.lean` (M1d (iii)): `lgp`, `idAlg`, `logVol_lgp_integral`,
  `wall_idAlg_iff`.
* `QPilotRegion.lean` (M2 (a), P21): `pow`, `qRegion`, `logVol_qRegion`, `etaQReg_eq_etaQ`,
  `etaQ_pilot_eq_mk`.
* `Constraints.lean` (M2 (b)): candidate constraints (C1)–(C10) and their status on the
  identified-copies algorithm.

## M1a: basic prime strips ([LANA], §4.1, pp. 23–24; §4.2(c), p. 26; §7.1, pp. 37–38)

* `Wall.GMData`, `Wall.GMIso` — mono-analytic GM-data `G ↷ M` with compact structure
  ([LANA], §3.9, Definition 4.1.2; IUT II, Definition 4.9).
* `Wall.EtUnitBPS model`, `Wall.EtUnitIso` — étale-unit BPSs = `F^{⊢×µ}`-prime-strips
  abstractly isomorphic to a model ([LANA], Definition 4.1.2).
* `Wall.ValBPS V bad`, `ValBPS.Iso`, `ValBPS.PF` — value-group BPSs `(C, {φ_v})`
  ([LANA], Definitions 4.1.3, 4.1.4).
* `Wall.BPS`, `BPS.Iso` ([LANA], Definition 4.1.6).
* **Lemma 4.1.7**: `ValBPS.nonempty_iso_iff`, `BPS.nonempty_iso_iff` (isomorphic iff same `PF`).
* **Remark 8.2.1** (connected groupoid; "linked" is vacuous): `BPS.Iso.refl/symm/trans`,
  `BPS.connected`; value-group isomorphisms are unique (`ValBPS.valIso_subsingleton`).
* **Remark 4.1.5** (pointed real line): `ValBPS.pilot`, `ValBPS.eta`, `ValBPS.eta_unique`,
  `ValBPS.eta_eq_eta_iff`.
* `Wall.qVal` (§4.2(c)), `Wall.thetaVal` (§7.1(a)), `Wall.PF_thetaVal` (same product
  formula), `Wall.thetaLink` (the value-group part of the Θ-link, §7.1(b)), and the scale
  factor `Wall.sFactor` = `(1² + ⋯ + ℓ*²)/ℓ*` = `(ℓ*+1)(2ℓ*+1)/6` (`sFactor_eq`),
  `> 1` for `ℓ* ≥ 2` (`one_lt_sFactor`).
* The Scholze–Stix hexagon ([LANA], §10.2, Figure 7): `degTheta_eq_smul_thetaLink`
  (the degree map of the Θ-pilot line is `s` times the Θ-link), `hexagon_commutes_iff`
  (commutes iff `s = 1`), `InitialThetaData.hexagon_not_commutes`.
* For initial Θ-data: `InitialThetaData.bpsDegrees` (local degrees on the places of `F`),
  `InitialThetaData.pilot_qVal : (qVal D.bpsDegrees).pilot = D.qPilot.absLogQ`,
  `InitialThetaData.lhs_neg : D.qPilot.lhs < 0`.

## M1b: `R_val`, `R_ss`, `η_q` ([LANA], §9.2–§9.3, pp. 45–46)

* `R_val` is the value-group line of a BPS (`ValBPS.C` with `ValBPS.pilot`).
* `Wall.Rss D` = adelic measurable regions of the concrete container modulo equal
  procession-normalized log-volume; `Wall.rssEquiv : Rss D ≃ ℝ` (log-volume is a bijection;
  surjectivity by archimedean rescaling, `logVol_archScale`).
* `Wall.etaQ D` and `Wall.logVol_etaQ_pilot`:
  `log-vol(η_q(φ_C)) = (concreteVariantData D).qPilot.lhs`.
* `Wall.logVol_le_rhs`: an adelic region in the hull of a single (Ind1)-image of the
  theta-pilot region has log-volume `≤ −|log(Θ)|` (uses `rhsDataOn_singleton`).
* `Wall.exists_adelic_iff`: the set of such log-volumes is exactly `ℝ_{≤ −|log(Θ)|}`
  (IUT III, Corollary 3.12; [LANA], §8.3).

## M1c: the η-algorithm and the wall ([LANA], §6, §9.1–§9.3; IUT III, Theorem 3.11, Step (xi))

`Wall.EtaAlg D` has opaque Hodge theaters `Side` with étale-unit BPSs, an output
`out ι S : Region D` for a choice `ι : B ≅ thetaBPS h` (Step 1) and an (Ind3)-choice `S ⊆ VC(I)`,
and the fields

* **(T1)** `ind12_acts_on_S` — automorphisms of the étale-unit portion ((Ind1), (Ind2)) act on
  the choice of `S` (IUT III, Theorem 3.11(i); [LANA], §10.4);
* **(T2)** `etUnitOnly` — the output depends only on the étale-unit portion ([LANA],
  Remark 6.2.2; a separate field);
* **(T3)** `realisation` — outputs are adelic and lie in the holomorphic hull of a *single*
  (Ind1)-image of the concrete theta-pilot region (IUT III, Theorem 3.11(ii), Corollary 3.12);
* `side_nonempty`.

`EtaAlg.etaAnab ι S` is the pointed map sending the pilot to `log-vol(out ι S)` ([LANA], §9.2).

```lean
def Iut.Wall (D : InitialThetaData.{0}) (A : Wall.EtaAlg D) : Prop :=
  ∀ (h₁ h₂ : A.Side) (_gl : BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂)),
    ∃ (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D), A.etaAnab ι S = etaQ D

theorem Iut.Wall.variant_of_wall (A : EtaAlg D) (hW : Wall D A) :
    Corollary312Variant (concreteVariantData D)
theorem Iut.Wall.literal_of_wall (A : EtaAlg D) (hW : Wall D A) :
    Corollary312Variant (concreteVariantDataLit D)
theorem Iut.Wall.cor312VariantHolds_of_wall (A : ∀ D, EtaAlg D) (hW : ∀ D, Wall D (A D)) :
    Cor312VariantHolds
theorem Iut.Wall.classicalABC_of_wall (A : ∀ D, EtaAlg D) (hW : ∀ D, Wall D (A D)) :
    ClassicalABC
```

`Wall.wall_iff_forall`: the Θ-link argument `_gl` carries no information (Remark 8.2.1).

## M1d: the checks

**(i) Shadow lemma.** `Wall.numericalWall_iff : NumericalWall D ↔ Corollary312Variant
(concreteVariantData D)`. Two pointed maps out of a pointed line agree iff they send the pilot to
the same point, so (9-1) for a given `(ι, S)` is the equation `log-vol(out ι S) = −|log(q)|`
(`EtaAlg.etaAnab_eq_etaQ_iff`). The numerical form of (9-1) is therefore circular: it is the
variant.

**(ii) The trivial instance is not excluded by (T1)–(T3).**

* `Wall.exists_isTrivial_iff`:
  `(∃ A : EtaAlg D, A.IsTrivial) ↔ Corollary312Variant (concreteVariantData D)`:
  an `EtaAlg` with `etaAnab = etaQ` for every choice (`trivialAlg`) satisfies (T1)–(T3)
  exactly when the variant holds. Excluding it is as hard as refuting the variant.
* `Wall.exists_wall_iff : (∃ A : EtaAlg D, Wall D A) ↔ Corollary312Variant (concreteVariantData D)`.
  **The interface (T1)–(T3) is too weak**: as an existential over algorithms, the wall restates
  the variant. It has content only for a *given* algorithm, i.e. once the η-algorithm is
  constructed (roadmap Milestones 2–3).
* A strengthening (**T4**, `EtaAlg.LGPLaw`): the output is `M = 1·S`, the image of `S` under
  the theta values, so `log-vol(out ι S) = κ_ι + log-vol(S)` ([LANA], §9.2). Under (T4) the
  trivial instance is excluded (`EtaAlg.not_isTrivial_of_lgpLaw`), but the wall becomes the
  numerical condition `−|log(q)| − κ_ι ≤ log-vol(VC(I))` for some `ι`
  (`EtaAlg.wall_iff_of_lgpLaw`).

**(iii) Identified copies** (Scholze–Stix; `IdentifiedCopies.lean`). `Wall.idAlg D`: one Hodge
theater, `out ι S = LGP·S` computed in the ring structure of `D` (theta value `q_{v_j}^{j²}` at
the label `j`). It satisfies (T1)–(T4) and is not trivial (`idAlg_not_isTrivial`). Proved:

* `Wall.logVol_lgp : log-vol(LGP·S) = log-vol(LGP·O) + log-vol(S)`;
* `Wall.logVol_lgp_integral : log-vol(LGP·O) = −s·|log(q)|`;
* **`Wall.wall_idAlg_iff : Wall D (idAlg D) ↔ (s − 1)·|log(q)| ≤ log-vol(VC(I))`.**

In the identified-copies model the wall is exactly the Scholze–Stix inequality (the factor
`s ~ ℓ*²/3` of the hexagon). Whether this inequality holds is **not** decided here: neither it
nor its negation is proved. No field of `EtaAlg` forbids this collapse; (T2) holds trivially
for it.

## Deviations from [LANA] and modelling choices

1. **BPSs simplified** (§0.3 of [LANA] already simplifies): one subset instead of the family
   `{N_{v,H}}_H` of compact structures; no orientation on `C`; the model étale-unit strip is a
   parameter (Galois groups of local fields are not constructed).
2. **Places**: the BPSs of `D` are indexed by the places of `F` (the indexing of
   `QPilotData`), not by `V ≅ V_mod`; only the pilot (a sum over the bad places) enters.
3. **`R_ss`** is the quotient of adelic regions of the concrete container by equal
   log-volume, with its line structure transported along `log-vol` (`rssEquiv`).
4. **`η_q`**: in M1 the class of `{q_v O_v}` was the class of log-volume `−|log(q)|` (a
   normalization, `logVol_etaQ_pilot`). Since M2 the region is constructed (`qRegion`, placed as
   the theta value for `j = 1` at the label `1` of every capsule) and `η_q` provably sends the
   pilot to its class (`etaQ_pilot_eq_mk`).
5. **(Ind1)**: [LANA] has `Ind1 = Aut(G_v)`; the concrete container follows IUT III
   (automorphisms of the procession, i.e. label permutations, `Iut/Concrete/Ind1Invariance.lean`).
   (T3) asks for a *single* label image; this is what yields the variant (IUT IV's reading)
   rather than only the literal reading.
6. **(T3) in the hull**: [LANA], §6.2(i), puts the possible images in the theta-pilot region
   itself (`InImage`); (T3) asks only for the hull (`InHullOfImage`), which is weaker, so the
   class of algorithms is larger and `variant_of_wall` stronger.
7. **`VC(I)` at a prime** is the `ℤ_p`-span of elementary tensors of log-shell elements (the
   base region of the theta-pilot region), the image of [LANA]'s `⊗_ℤ` in the tensor packet.
8. **Strength of `Wall`**: it quantifies over all pairs of Hodge theaters and all Θ-links;
   the proof of `variant_of_wall` uses one Hodge theater `h` and the pair `(h, h)`. The
   existential over `(ι, S)` realizes [LANA], §9.3 ("`η_q` belongs to an orbit generated by
   the indeterminacies").
9. **(T4)** is a strengthening introduced here (justified by [LANA], §9.2, "`M = 1·S` …
   represents `LGP·S`"); it is not a field of `EtaAlg` and nothing in M1c depends on it.

## M2 (a): the `q`-pilot region (P21; `QPilotRegion.lean`)

* `Wall.powElt D e lab`, `Wall.pow D e lab S`: `S` scaled, in capsule `i` at each prime `p` and
  tuple `c`, by `q_v^{e(i)}` in the tensor factor of the label `lab i` (`v = c(lab i)`, `q_v` the
  `2ℓ`-th root `D.qroot` of the Tate parameter, `= 1` at good places); unchanged at `∞`.
  `Wall.lgp_eq_pow`: `LGP·S` is the case `e(i) = (i+1)²`, `lab` = distinguished labels (`rfl`).
* `Wall.logVol_pow_integral : log-vol(pow D e lab O) = −(avg_i e(i))·|log(q)|` for **every**
  label placement, from `componentVol_prod_incl_smul_integral` and
  `InitialThetaData.logQAt_eq_sect` (the same machinery as `logVol_lgp_integral`).
* **Placement decision.** The `q`-pilot is the theta value for `j = 1`, i.e. the `q`-parameter
  itself (IUT III, Corollary 3.12; [LANA], §5.2(f), §9.2 "embedded diagonally"):
  `Wall.qRegion D := pow D 1 labOne O` — in every capsule (diagonal), `q_v·O` in the factor of the
  label `1` (which every capsule `{0, …, j}` contains), integral at `∞`. In the first capsule it
  *is* `LGP·O` (`Wall.qRegion_first`, `rfl`). The log-volume does not depend on the label,
  matching the (Ind1) label permutations.
* **`Wall.logVol_qRegion : logVol D (qRegion D) = (concreteVariantData D).qPilot.lhs`**
  (`= −|log(q)|`); `Wall.isAdelic_qRegion`.
* `Wall.etaQReg D` (`η_q` defined from `qRegion`), `Wall.etaQReg_eq_etaQ`, and
  **`Wall.etaQ_pilot_eq_mk`**: `(rssEquiv D).symm (etaQ D pilot) = Rss.mk D (qRegion D) _`, so
  `logVol_etaQ_pilot` is now a theorem about a constructed region
  (`Wall.logVol_etaQ_pilot_eq_qRegion`). The definition `etaQ` is kept (M1 uses it) and shown
  equal.

## M2 (b): what excludes `idAlg`? (`Constraints.lean`)

Candidate constraints from IUT III (Theorem 3.11, Remark 3.11.1(iii)–(v), Corollary 3.12
Step (xi)) and [LANA] (§6.2, Remark 6.2.2, §7.1(b)(c), §8.1–§8.3, Remark 8.2.1, §10.3, §10.5),
stated as `Prop`s on `EtaAlg D` (never assumed), with their status on the identified-copies
algorithm. `idAlgOn D σ` is `idAlg` with an arbitrary nonempty type `σ` of identified Hodge
theaters (`idAlg_eq_idAlgOn : idAlg D = idAlgOn D Unit`); its wall is the Scholze–Stix
inequality `(s − 1)·|log(q)| ≤ log-vol(VC(I))` for every `σ` (`wall_idAlgOn_iff`).

| | constraint | source | excludes idAlg? | Lean |
|---|---|---|---|---|
| C1 | IPL: the output Θ-pilot BPS is linked to the input `q`-pilot BPS by a pilot-preserving BPS isomorphism | IUT III Rem 3.11.1(iii), (xi-b)–(xi-e); [LANA] §8.2, Rem 8.2.1 | **No**: holds for every `EtaAlg` | `EtaAlg.IPL`, `EtaAlg.ipl`, `idAlgOn_ipl` |
| C2 | SHE, two-sided: the output is a function of the domain HT and of the codomain HT | IUT III Rem 3.11.1(iii); [LANA] §8.2 | **No**: with opaque HTs it is *equivalent* to side-independence, the shape of the collapse | `EtaAlg.SHESides`, `EtaAlg.sheSides_iff`, `idAlgOn_sheSides` |
| C3 | SHE as in (xi-e): some output has the class `[qRegion D]` in `R_ss` | IUT III Cor 3.12 (xi-e), (xi-f); [LANA] §8.3 | **Undecided**: equivalent to the wall; on `idAlg` to the Scholze–Stix inequality | `EtaAlg.SHEq`, `EtaAlg.sheq_iff_wall`, `sheq_idAlg_iff`, `sheq_idAlgOn_iff` |
| C4 | distinct Hodge theaters (`Nontrivial Side`) | IUT III Thm 3.11 ("distinct" HTs); [LANA] §7.1(b), §8.1 | **Literally yes, the collapse no**: `idAlg` violates it, `idAlgOn σ` (σ nontrivial) satisfies it with the same wall | `EtaAlg.DistinctSides`, `idAlg_not_distinctSides`, `idAlgOn_distinctSides`, `wall_idAlgOn_iff` |
| C5 | the wall only for Θ-links between distinct sides `h₁ ≠ h₂` | [LANA] §7.1(b) (`†HT → ‡HT`) | **No**: vacuous on `idAlg`; on `idAlgOn σ` (σ nontrivial) the Scholze–Stix inequality; with C4 it still implies the variant | `WallDistinct`, `wallDistinct_idAlg`, `wallDistinct_idAlgOn_iff`, `variant_of_wallDistinct` |
| C6 | multiradiality: outputs through any two HTs agree up to (Ind3) | IUT III Thm 3.11(i) (étale-picture symmetries); [LANA] §8.1(d) | **No**: satisfied | `EtaAlg.Multiradial`, `idAlgOn_multiradial` |
| C7 | provenance as side-dependence: the output possibilities depend on the HT used | [LANA] §10.3 | **Yes**, but incompatible with C6 | `EtaAlg.SideDependent`, `EtaAlg.not_sideDependent_of_multiradial`, `idAlgOn_not_sideDependent` |
| C8 | the input value group influences the output | [LANA] Rem 6.2.2 (the (SHE) reading) | **Yes**, but no `EtaAlg` satisfies it (it contradicts T2) | `EtaAlg.ValDependent`, `EtaAlg.not_valDependent` |
| C9 | APT: the output is not the image of `S` under one fixed set-theoretic map | IUT III Rem 3.11.1(iv); [LANA] §8.2, §8.3 | **Literally yes, the wall no**: `idAlgOn σ` violates it, but every `EtaAlg` with the identified-copies log-volumes has the Scholze–Stix wall | `EtaAlg.SetTransport`, `EtaAlg.APT`, `idAlgOn_not_apt`, `EtaAlg.wall_iff_ss_of_thetaShift` |
| C10 | mutually alien ring structures: no ring isomorphism between distinct sides is compatible with a Θ-link | [LANA] §7.1(b)(c), §10.5; IUT III Thm 3.11, (xi-a) | **No**: every `EtaAlg` carries such a structure, since `out` is not coupled to it | `HoloStructure`, `HoloStructure.Alien`, `exists_alien` |

**Outcome.** No candidate that some `EtaAlg` can satisfy excludes the collapse in the sense that
matters, namely the wall of the identified-copies model (the Scholze–Stix inequality). C1, C2,
C6 and C10 hold for it, and C3 *is* the wall. C4 and C9 exclude only the literal `idAlg`, not
algorithms with the same output log-volumes (`wall_idAlgOn_iff`, `wall_iff_ss_of_thetaShift`).
C7 and C8 exclude it but conflict with C6 and with (T2) respectively. This is a statement about
the BPS model, not about IUT: the model has one container, one ring structure and one
log-volume, so the constraints about distinct ring structures (C4, C5, C9, C10) cannot act on
the output.

**Extra structure needed (input to P15–P20).** For these constraints to bite, the interface
needs:

* for each Hodge theater `h`, a ring (local fields `K_v^{(h)}`) with its own container `VC_h`
  and log-volume `μ_h`;
* Kummer isomorphisms from the coric étale-unit data to the log-shells of each side;
* outputs through `h₁` as regions of `VC_{h₁}`;
* the Θ-link transport `VC_{h₁} → VC_{h₂}` as an isomorphism of log-shells that is
  mono-analytic (additive, topological), not a ring isomorphism;
* the wall as `μ_{h₂}(transport(out)) = μ_{h₂}(q-pilot region of h₂)`.

The identified-copies model is the case of one container, the identity transport and
`μ_{h₁} = μ_{h₂}`. In these terms the open question is whether an admissible transport or
normalization changes the log-volume shift `−s·|log(q)|` of `LGP·O`; C9 shows that only this
shift matters for the wall.
