# The Θ-link (`Iut/ThetaLink/`, roadmap P19)

A Lean formulation of the parts of IUT II (Corollaries 3.5, 3.6, 4.6, 4.10, Definition 4.9) and
IUT III (Definition 3.8) that define **Gaussian monoids**, **`F^{⊩▶×μ}`-prime-strips** and the
**Θ-link** (`Θ^{×μ}_gau`- and `Θ^{×μ}_LGP`-link) between two `Θ^{±ell}NF`-Hodge theaters, with the
**Kummer compatibilities** of its two portions. It also places the Θ-link in the multi-container
model of the wall (`Iut/Wall/MultiContainer.lean`, M3), which answers the question how much
volume distortion the Θ-link causes in that model.

Inputs: P15 (`Iut/Frobenioid/`: the global realified Frobenioid, the pilot objects,
`scale_thetaPilotObj`, `isEmpty_iso_thetaPilot_qPilot`), P16 (`Iut/EtaleTheta/`: theta values
`thetaRatio`, `lgpValue`, `pow_eq_thetaRatio_inv_iff`), P18 (`Iut/HodgeTheater/`:
`ThetaPmEllNFHT`, `FMuStrip`, `theaterAlg`, `chain`, `chainModel`), the wall
(`Iut/Wall/`: `ValBPS`, `qVal`, `thetaVal`, `thetaLink`, `degTheta_eq_smul_thetaLink`, the
multi-container model), and `continuous-kummer-theory` (`kummer`, `ker_kummer`). Sources: IUT II
and IUT III in their text extraction (`~/iut-scratch/wall/txt/`).

**Status of the dependency.** No module of this directory is imported by the comparator challenge
(`Comparator/Challenge.lean`) or by `Iut/Concrete/*`. No new hypotheses enter as global
assumptions; the deep inputs that are not formalized are explicit hypothesis fields (the
log-shell compatibility of `LinkedChain`) or are not claimed. The main theorems use only `propext`,
`Classical.choice` and `Quot.sound`.

## Scope decisions (read first)

1. **Concrete monoids, abstract strips.** The Gaussian and `q`-pilot monoids are built
   concretely at a bad place `v` of `K = D.Kt`, in `∏_{j=1}^{ℓ*} K_v`, from the theta values of
   P16 (`Gauss.lean`). The `F^{⊩▶×μ}`-prime-strips are recorded by their **unit portion** (P18's
   `F^{⊢×μ}`-prime-strip) and their **value-group portion** (the realified value-group line with
   the local pilots, the wall's `ValBPS`) (`PrimeStrip.lean`). The splitting monoids `O^▶`, the
   global realified Frobenioid `C^⊩` itself and the bijection `Prime(C^⊩) ≅ V` are recorded only
   through the realified value group and the local pilots; the pilot *objects* of `C^⊩` (P15) are
   related to the pilots by their degrees (`Link.lean`).
2. **The Θ-link is the full poly-isomorphism**, i.e. the type of all isomorphisms
   `†F^{⊩▶×μ}_gau ≅ ‡F^{⊩▶×μ}_Δ` (`ThetaLinkIso`), as in IUT II, Corollary 4.10(iii). Its
   properties are proved, not assumed.
3. **LGP = gau in the model.** The `Θ^{×μ}_LGP`-link (IUT III, Definition 3.8(ii)) differs from
   the `Θ^{×μ}_gau`-link by the log-shell-theoretic unit portion of the LGP-monoids; the strips do
   not record log-shells, so `ThetaLinkLGP := ThetaLinkIso` (IUT III, Remark 3.8.2: the results
   "generalize immediately"). The `Θ^{×μ}`-link (theta monoids, before evaluation) is not modelled
   separately: its value-group line is identified with the Gaussian one by the evaluation
   isomorphism (Corollary 4.10(ii)), which the model would record as the identity.
4. **Kummer theory on elements.** Kummer compatibility is stated for Kummer classes of elements
   of `Kˣ` (`continuous-kummer-theory`), not for étale-like monoids reconstructed from `G_v`
   (P16 scope decision S2; cyclotomic rigidity and the group-theoretic algorithms are P16/P17).
5. **The wall model.** The Kummer identifications of the theaters' log-shell containers with the
   coric container are required to preserve the log-shell (`LogShellCompat`, a hypothesis
   field), because the Θ-link only transports the unit portions and the log-shells are built from
   them (IUT III, Proposition 1.2, Definition 1.1; IUT II, Remark 4.10.3(i)). The output law is
   P18's identified-copies law (`theaterAlg`).

## Plan (lemma-level milestones) and status

| Milestone | File | Main results | Status |
|---|---|---|---|
| (1) Gaussian and `q`-pilot monoids | `Gauss.lean` | `splitMonoid`, `splitEquiv` (Cor 3.5(iii): `O^× × ℕ ≃* O^×·g^ℕ`), `norm_eq_one_iff` (units = diagonal units), `linkEquiv`, `linkEquiv_diag`, `linkEquiv_gen`, `linkEquiv_unique`; `gaussGen`, `qGen`, `gauss`, `qMonoid`, `norm_qroot_lt_one`, `gaussLink`, `gaussLink_label_one` (Rem 4.10.3(iii)), `gaussLink_ne_label`; value profiles `IsValueProfile`, `isValueProfile_iff` (`ξ_j = ζ_j q_v^{j²}`, `ζ_j^ℓ = 1`, from P16), `IsValueProfile.pow_eq`, `gauss_pow_eq` (Cor 3.5(ii): `Ψ_{ℓξ}` independent of `ξ`), `IsValueProfile.isSplitGen`; degrees `avgDeg_gaussian`, `avgDeg_gaussGen` (`= s·avgDeg(q-pilot)`), `avgDeg_gaussGen_ne` | done |
| (2) `F^{⊩▶×μ}`-prime-strips | `PrimeStrip.lean` | `RlfMuStrip`, `RlfMuStrip.Iso` (refl, symm, trans), `Iso.map_pilot`, `nonempty_iso_iff` (same product formula), `Iso.val_eq` (value part unique), `isoEquivUnit`; `qStrip` (`‡F^{⊩▶×μ}_Δ`), `gauStrip` (`†F^{⊩▶×μ}_gau`), `unit_qStrip`, `unit_gauStrip`, `unitIdent` (Cor 4.10(iv)), `pilot_qStrip` (`|log q|`), `degTheta_pilot_gauStrip` (`s·|log q|`), `qStripIso`, `gauStripIso`, `toBPS_qStrip`, `toBPS_gauStrip` (the wall's BPSs, `rfl`); groupoid laws `FMuIso.*` | done |
| (3) The Θ-link | `Link.lean` | `ThetaLinkIso`, `ThetaLinkLGP`, `nonempty_thetaLink`; `unitEquiv : ThetaLinkIso H₁ H₂ ≃ (H₁.Fmu ≅ H₂.Fmu)` (the indeterminacy is exactly the unit portion); `val_eq` (= `Wall.thetaLink`), `map_pilot` (Θ-pilot ↦ `q`-pilot), `val_apply` (`λ x = s⁻¹·deg_Θ x`), `pilot_degrees`, `val_not_degree_preserving`; `dLink`, `dLink_surjective` (Cor 4.10(iv): the `D-Θ^{±ell}NF`-link is the full poly-isomorphism); `congr`, `dLink_congr`, `nonempty_congr` (compatibility with isomorphisms of theaters); `toWallLink`, `toWallLink_val` (the wall's BPS-level Θ-link); Frobenioid: `frobenioid_degrees`, `not_iso_in_frobenioid`, `scaling_iff` (exactly the scaling `1/s`, Cor 4.10(v)); Frobenius-pictures `FrobeniusPicture`, `FrobeniusPicture.ofData`, `arrow_aut_eq_add`, `not_swap_adjacent` (Cor 4.10(vi)) | done |
| (4) Kummer compatibility | `Kummer.lean` | `kummer_splitElt`, `kummer_pow_eq_of_root`, `kummer_eq_iff` (`κ a = κ b ↔ a/b ∈ (Kˣ)ⁿ`), `kummer_compat_iff`, `kummer_gauss_compat_iff` (compatible at a label iff `ζ·q^{j²−1} ∈ (Kˣ)ⁿ`), `kummer_gauss_compat_label_one`, `kummer_link_unit` (unit portion compatible) | done |
| (5) The wall link | `Wall.lean` | `LogShellCompat`, `shift_eq_zero_of_logShellCompat`, `logShellCompat_of_comp`, `logShellCompat_negScale`, `not_logShellCompat_qScale_zpow`; `LinkedChain` (Frobenius-picture + log-shell compatible Kummer identifications), `toModel`, `wallLink`, `kummerVolCompat`, `volCompat`, **`distortion_eq_zero`**, **`wallOn_thetaRow_iff`**, `wall3_iff`, **`answer`**; `ofData`, `toModel_ofData` (= P18's `chainModel`), `negChain`, `negChain_alien`, `not_logShellCompat_chainModel`, `kum_ne_chainModel` | done |

## The answer to (5)

In the multi-container model with the sides the Hodge theaters of a Frobenius-picture and the
transports determined by Θ-links (`LinkedChain`):

* the **value-group portion** of each Θ-link sends the Θ-pilot (degree `s·|log q|`) to the
  `q`-pilot (degree `|log q|`): it rescales degrees by `1/s` (`ThetaLinkIso.val_apply`,
  `pilot_degrees`), it is unique (`val_eq`), and it is not realized inside one global realified
  Frobenioid except as the scaling `1/s` (`scaling_iff`, `not_iso_in_frobenioid`); at the level of
  monoids it is `u·{q_v^{j²}}^N ↦ u·q_v^N` (`gaussLink`), the identity at the label `1` and not at
  the other labels; it is Kummer compatible at the label `j` iff `ζ·q_v^{j²−1}` is an `n`-th power
  (`kummer_gauss_compat_iff`);
* the **unit portion** is identified: the Θ-links are exactly the isomorphisms of the
  `F^{⊢×μ}`-prime-strips (`unitEquiv`, `dLink_surjective`), and it is Kummer compatible
  (`kummer_link_unit`);
* the **transport of containers** therefore only sees the unit portion: with log-shell compatible
  Kummer identifications, **the volume compatibility C11 holds** (`kummerVolCompat`,
  `volCompat`), **the distortion along every Θ-link is `0`** (`distortion_eq_zero`), and the
  M3 analysis gives: **the wall along the Θ-links is exactly the Scholze–Stix inequality**
  `(s − 1)·|log q| ≤ log-vol(VC(I))` (`wallOn_thetaRow_iff`; also for all pairs, `wall3_iff`).
  This holds also with alien (non-ring) transports along every Θ-link (`negChain`,
  `negChain_alien`). The factor `s` enters the wall only through the output law
  (`ThetaShift`: `LGP·S` has log-volume `−s·|log q| + log-vol(S)`), not through the transport.
* The drifting rows `Wall.chainModel D k` of M3 (distortion `k·|log q|` per link, the only
  M3 mechanism by which the wall differs from the Scholze–Stix inequality) are **not** of this
  form for `k ≠ 0` (`not_logShellCompat_chainModel`, `kum_ne_chainModel`): their Kummer
  identifications multiply by powers of `q`, i.e. carry value-group data into the unit portion.

This is a statement about the model, conditional on its two modelling inputs (log-shell
compatibility of the Kummer identifications, and the identified-copies output law). It does not
decide whether IUT's actual η-algorithm (IUT III, Theorem 3.11, Corollary 3.12) has a different
output law; that question is untouched here (roadmap P20–P22). Neither `SSIneq D` nor its negation
is proved.

## Simplifications (documented)

* `F^{⊩▶×μ}`-prime-strips: unit portion = P18's `F^{⊢×μ}`-prime-strip (base-field units modulo
  torsion, trivial Galois action, P18's simplification), value-group portion = realified line
  with local pilots indexed by the places of `F` (the wall's indexing), not by `V ≅ V_mod`; the
  ×μ-Kummer structures (the `Ism`-orbits of IUT II, Definition 4.9(ii)–(v)) are not recorded.
* The natural isomorphisms `F^{⊢×μ}_Δ ≅ F^{⊢×μ}_env ≅ F^{⊢×μ}_gau` are identities (all three unit
  portions are the theater's `F^{⊢×μ}`-prime-strip).
* Value profiles use `ℓ`-th roots (P16 proves the `μ_ℓ`-indeterminacy), so `Ψ_{ℓ·ξ}` rather than
  `Ψ_{2ℓ·ξ}` is profile-independent.
* The Gaussian monoids are those of the bad places; the analogues at good and archimedean places
  (IUT II, Propositions 4.1–4.4) are not built, they enter only through the local pilots of
  `Wall.thetaVal` (whose good-place pilots are `s·deg(p_v)`).
* The degrees of `Gauss.lean` (`avgDeg`, `−log‖·‖` averaged over the labels) are not identified
  with the normalized degrees `finDeg` of the wall's `bpsDegrees`; both carry the factor `s`
  (`avgDeg_gaussGen`, `degTheta_localPilot`).
* `LogShellCompat` is a hypothesis field of `LinkedChain` (scope decision 5), not derived here.
  It is derived in P20 from unit-inducedness (`LogLink.logShellCompat_of_unitInduced`), and
  unit-inducedness is in turn derived from the anabelian origin of the Kummer identifications
  (Galois isomorphisms or automorphisms of the unit groups: `Iut/LogLink/Galois.lean`,
  `Iut/LogLink/GalKummer.lean`, `AnabelianScaling.logShellCompat`).

## What remains

* The étale-like Gaussian monoids reconstructed from `G_v`-actions (IUT II, Proposition 3.1,
  Corollaries 3.5, 3.6 with cyclotomic rigidity; P16/P17) and the Gaussian monoids at good and
  archimedean places (IUT II, Propositions 4.1–4.4).
* The `Θ^{×μ}`-link before evaluation. (The log-links, the log-theta-lattice and the local
  LGP-monoids of IUT III, Propositions 3.4, 3.5 — the pull-backs of the Gaussian monoids of
  `Gauss.lean` along the log-links, with their splitting monoids — are in `Iut/LogLink/`,
  `Split.lean`; the global Frobenioids of Proposition 3.7 are not built.)
* A derivation of log-shell compatibility from an anabelian reconstruction of the log-shells and
  of the Kummer isomorphisms (P17, P20), and an η-algorithm whose output law is not the
  identified-copies law (P20–P22).
