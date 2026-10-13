# The log-link and the log-theta-lattice (`Iut/LogLink/`, roadmap P20)

A Lean formulation of IUT III, §1 (Definition 1.1, Propositions 1.2, 1.3, Definition 1.4,
Theorem 1.5) and of the parts of §3 that the wall needs (Propositions 3.4(ii), 3.5, 3.10(ii), the
LGP-monoids, the log-Kummer correspondence and (Ind3), also at the archimedean places; Theorem
3.11 as a statement, including (ii)(b), (c)), on top of P15–P19, and the connection of Theorem
3.11 to the wall (`Iut/Wall/`).

Inputs: the `p`-adic logarithm `PadicLogVolume.padicLog` and the log-shell `Iut.logShell`
(`Iut/Concrete/LocalConstruct/LocalLogShell.lean`, `LogShell.lean`: `map_padicLog`,
`RingHom.image_logShell_subset`, `closedBall_subset_logShell`, the tensor log-shells
`LocalConstruct.tensorLogShell`), P18 (`Iut/HodgeTheater/`: `ThetaPmEllNFHT`, its label layer
`DThetaPmEllNFHT`, `FMuStrip`, `theaterAlg`), P19 (`Iut/ThetaLink/`: `ThetaLinkIso`,
`unitEquiv`, `dLink_surjective`, `FrobeniusPicture`, `LogShellCompat`, `LinkedChain`), the wall
(`Iut/Wall/`: `Scaling`, `MultiContainer`, `EtaAlg`, `Wall`, `variant_of_wallOn_of_volCompat`,
`classicalABC_of_variant`). Sources: IUT III (`~/review-iut3/iut3.txt`), the LANA report
(`~/iut-scratch/wall/txt/lana-report-2026-07.txt`, §5.3, §7.2(c), §9.1(i)).

**Status of the dependency.** No module of this directory is imported by the comparator challenge
(`Comparator/Challenge.lean`) or by `Iut/Concrete/*`. Nothing enters as a global assumption: the
contested step of Corollary 3.12 (Step (xi)) is an explicit hypothesis (`XiPrinciple`), as are
the modelling inputs listed below.

## Scope decisions (read first)

1. **Local fields, not Frobenioids.** A log-link at `v ∈ V^non` is modelled on a local field `k`
   (complete, discretely valued, characteristic `0`, residue characteristic `p`): the tautological
   log-link is the `p`-adic logarithm on the **principal units** `1 + 𝔪_k`, followed by a
   continuous ring isomorphism (the poly-isomorphism `log(†F_v) ≅ ‡F_v` of Definition 1.1(i)).
   IUT's domain `O^×_{k̄}` (with its `Π_v`-action) is replaced by the `G_v`-invariants, and these
   by their pro-`p` part `1 + 𝔪_k` (the logarithm kills the torsion, and `O^×/(1+𝔪)` is finite),
   which is also the domain of `Iut.logShell` (`(2p)⁻¹·log(1+𝔪)`, a finite-index variant of
   `(p*)⁻¹·log(O^×)`). The archimedean log-links (Definition 1.1(ii)) are modelled on `ℂ`
   (scope decision 6).
2. **Copies.** All levels of a vertical line carry copies of the same local field (as in P18 and
   M3: Hodge theaters relative to fixed initial Θ-data are isomorphs); a vertical line is a
   sequence of continuous ring automorphisms (`LogColumn`). What distinguishes the levels is the
   relation between them (log-links, Kummer isomorphisms), not the fields.
3. **Kummer isomorphisms.** The holomorphic Kummer isomorphisms of a column (`Ψ_cns(n,mF) ≅
   Ψ_cns(n,◦D)`) are continuous ring isomorphisms of the copies; the mono-analytic ones (the
   Kummer isomorphisms of the log-shell containers, Proposition 1.2(vi), Theorem 3.11(ii)(a)) are
   additive isomorphisms. A mono-analytic identification is **unit-induced** (`UnitInduced`) if it
   is induced, through the logarithm, by an isomorphism of the unit groups — this is how
   Proposition 1.2(vi), (viii) and Theorem 1.5(iii), (iv) construct `log(D^⊢_v) ≅ log(F^{⊢×μ}_v)
   ≅ log(F_v)` from the `F^{⊢×μ}`-data (an `Ism`-orbit of automorphisms of `O^{×μ}`).
4. **Hodge theaters.** A log-link of `Θ^{±ell}NF`-Hodge theaters (Proposition 1.3) is recorded as
   the isomorphism `Ξ` of the associated `D-Θ^{±ell}NF`-Hodge theaters (P18's label layer) over
   which it lies, together with the local log-links at the bad places of the column (the
   `F`-prime-strips of P18 record Frobenioids, not field elements, so the local log-links are
   attached through `LogColumn`). Full log-links are the full poly-isomorphism.
5. **Theorem 3.11 is a statement, not a theorem.** Its parts (i)–(iii) are formalised as far as the
   model objects allow, and proved in the model where the model makes them provable; the step of
   Corollary 3.12 that is disputed (Step (xi): the output, transported along the Θ-link, computes
   the `q`-pilot up to the indeterminacies) is the explicit hypothesis `XiPrinciple`.

6. **Archimedean places** (`Arch.lean`). The local field is `ℂ`; the universal covering
   `Ψ^∼ ↠ Ψ^gp` of Definition 1.1(ii) is `exp : (ℂ, +) → ℂˣ`, with deck group `2πiℤ`; a log-link
   is the principal logarithm on the units followed by a continuous ring automorphism `φ` of `ℂ`
   (the identity or the conjugation). The log-shell is the closed disc of radius `π`. The angular
   and radial log-volumes are not formalised; the archimedean lines of a lattice are separate data
   (`LGPLattice.arc`), as the non-archimedean ones.
7. **LGP-monoids** (`Split.lean`). The local LGP-monoid of `†HT` is the pull-back of its Gaussian
   monoid along the ring isomorphism `φ : log(‡F_v) ≅ †F_v` of the log-link (Proposition
   3.4(ii)); the splitting monoid `Ψ⊥` is `μ_{2ℓ}·{q_v^{j²}}^ℕ`. That the Kummer isomorphisms of
   the bad places fix the Gaussian generator (the Kummer isomorphisms of labeled data of IUT II,
   Corollary 4.6(iii), are compatible with the theta values) is a field of the data
   (`LGPColumn.kum_gen`, `LGPLattice.kum_gen`), satisfied by the tautological lines.
8. **Number fields** (`Global.lean`). `M_mod = F_mod`, read in the local fields `K_v`, `v ∈ V`, of
   the section `V_mod ≅ V` (`embFin`, `sectInf_apply`). The `F^⊛_MOD`-Frobenioids are recorded by
   what they depend on: the multiplicative group and the divisor maps `β_v` (Example 3.6(i),
   Remark 3.6.1); the Frobenioids themselves, the `F^⊛_mod`-Frobenioids (local fractional ideals)
   and the global realified LGP-/lgp-Frobenioids of Proposition 3.7 are not built.

## Plan (lemma-level milestones) and status

| Milestone | File | Main results | Status |
|---|---|---|---|
| (1) Local log-links | `Local.lean` | `prinUnits`, `logHom` (Prop 1.2(ii): `log` is a homomorphism `1+𝔪 → (k,+)`), `padicLog_mem_logShell`, `norm_padicLog_one_add` (log is an isometry on `‖a‖ ≤ ‖2p‖`: Prop 1.2(iii) at the level of radii), `exists_prinUnit_padicLog_eq`; `LocalLogLink` (Def 1.1(i)), `toFun_mul`, `image_logShell` (the log-shell is an object of the codomain), Prop 1.2(v): `logShell_bounded` (a_non), `closedBall_subset` (b_non), `toFun_mem_logShell` (c_non); Prop 1.2(iv): `not_ringHom_eq_toFun`; `exists_toFun_eq`; `UnitInduced`, `UnitInduced.symm`, `.trans`, **`image_logShell_of_unitInduced`**, `unitInduced_neg`, `prinMap`, `unitInduced_ringEquiv`, `scale_image_logShell_ne`, `not_unitInduced_scale` | done |
| (2) Vertical lines | `Column.lean` | `LogColumn`, `iter`, `shift`, `iter_shift`, `logKummer`, `logKummer_shift` (translation invariance, Prop 3.5(ii)), `kum_image_logShell` (vertical coricity of the holomorphic log-shell), `iter_subset_logShell`, **`upperSemiCompat`**, `logKummer_subset` (Prop 3.5(ii)(a), (Ind3)), `kummer_log_ne` (Prop 1.2(iv)), `exists_iter_one_norm_lt` (the images are not units), `norm_map_lt_one`, **`log_theta_not_commute`** | done |
| (3) The log-theta-lattice | `Lattice.lean` | `LogLinkHT`, `LogLinkHT.dIso`, `logLinkEquiv`, `card_logLinkHT` (= 2), `nonempty_logLinkHT` (Prop 1.3); `LogColumn.taut`; `LogThetaLattice` (Def 1.4); `vertIso`, `vertCoric` (Thm 1.5(i)), `horizCoric`, `horizCoric_full` (Thm 1.5(ii)), `biCoric` (Thm 1.5(iii)), `row` (P19 Frobenius-pictures), `col`, `not_commute`, `ofData` | done |
| (4) Log-shell compatibility derived | `Kummer.lean` | `tprod_mul_mem_tensorLogShell`, `tprod_image_tensorLogShell`, `FactorUnitInduced`, `factorMk_image_factorLogShell`, `FactorUnitInduced.image_eq`, `factorUnitInduced_one`, `factorUnitInduced_neg_one`, `tprod_image_tensorLogShell_of_unitInduced`; `UnitInducedScaling`, **`logShellCompat_of_unitInduced`**, `shift_eq_zero_of_unitInduced`, `unitInducedScaling_one`, **`unitInducedScaling_negScale`**, `not_unitInducedScaling_qScale_zpow`; `LatticeKummer` (`logShellCompat`, `toLinkedChain`, `model`, `model_kummerVolCompat`, `model_volCompat`, `distortion_eq_zero`, `distortion_horiz`, `distortion_vert`, `trivial`, `alt`) | done |
| (5) Theorem 3.11 and the chain to ABC | `Thm311.lean` | `logShellCompat_mul`, `logShellCompat_inv`, `act_lgp`, `act_le`, `ind3Map`, `ind3Act`; `horizRel`, `vertRel`; **`Thm311`**; `LatticeKummer.model_multiradial3` (Thm 3.11(i) in the model), `model_thetaShift`; **`thm311_model`**; **`XiPrinciple`**; **`variant_of_thm311`**, **`wall_of_thm311`** (the input of `Iut/Wall`), **`classicalABC_of_thm311`**, `classicalABC_of_xi`, **`xi_iff_ss`**, `xi_iff_xi`; `logVol_transport_out`, **`answer`**, `alt_alien_horiz`, `alt_alien_vert` | done |
| (6) Galois-induced identifications are unit-induced | `Galois.lean` | `norm_eq_one_of_unitInduced_scale`; `pow_q_sub_one_iff` (`U¹ = (𝒪ˣ)^{q−1}`), `logTensor_bijective`, `logEquiv` (`ℚ ⊗ 𝒪ˣ ≅ k`); `unitLogEquiv` (identification induced by `β ∈ Aut(𝒪ˣ)`), **`unitInduced_unitLogEquiv`**, `image_logShell_unitLogEquiv`, `unitLogEquiv_refl`, `unitLogEquiv_inv`, `unitLogEquiv_ne_scale`; `galUnitsEquiv` (P17's `𝒪ˣ ≅ 𝒪ˣ` from `φ ∈ Aut(G_k)`), `coe_galUnitsEquiv` (= `galEquiv_multEquiv`), `galLogEquiv`, **`galLogEquiv_transport`** (= transport of P17's `unitsQEquiv φ` through `log`), **`galLogEquiv_image_logShell`** (via `map_monoLogShell` + `image_logTensor_monoLogShell`), **`unitInduced_galLogEquiv`**, `galLogEquiv_refl`, `galLogEquiv_ne_scale`, `galEquiv_multEquiv_ne_zpow_mul` | done |
| (7) Kummer data from the reconstruction | `GalKummer.lean` | `CompGal`, `CompUnits`, `compGalLogEquiv`, `compUnitLogEquiv` (completions of `Iut/Concrete`), `unitInduced_compGalLogEquiv`, `compGalLogEquiv_image_logShell`; `FactorGalInduced`, `FactorUnitsAut`, **`FactorUnitsAut.factorUnitInduced`**, `exists_factorGalInduced_of_linear`, `norm_eq_one_of_factorUnitsAut`; `GalInducedScaling`, `AnabelianScaling`, **`AnabelianScaling.unitInduced`**, `.logShellCompat`, `.shift_eq_zero`, `galInducedScaling_one`, `anabelianScaling_negScale`; **`not_anabelianScaling_of_shift_ne_zero`**, `not_anabelianScaling_qScale_zpow`, `not_galInducedScaling_qScale_zpow`; `AnabelianKummer`, `GalKummer`, **`toLatticeKummer`**, `distortion_eq_zero`, `xi_iff_ss`, `kum_ne_qScale_zpow`, `GalKummer.trivial`, `AnabelianKummer.alt` (`= LatticeKummer.trivial`, `.alt`), `classicalABC_of_thm311_anabelian`, `classicalABC_of_thm311_gal`, `classicalABC_of_xi_gal` | done |
| (7') Galois automorphisms read off the strips (IUT I, Cor. 5.3(ii)) | `StripKummer.lean` (with `../HodgeTheater/StripLift.lean`) | `galMult_coe_units`, `compGalLogEquiv_eq_units` (the lifted Frobenioid equivalence acts on `𝒪ˣ` by `compGalUnits`, whose log-transport is `compGalLogEquiv`); `factorGal`, `factorGal_refl`; `StripScaling`, **`StripScaling.galInduced`**, `.unitInduced`, `.shift_eq_zero`, `stripScaling_one`; `StripKummer` (`gal`, **`toGalKummer`**, `toLatticeKummer`, `distortion_eq_zero`, **`xi_iff_ss`**, `kum_ne_qScale_zpow`, `liftIso`, `forget_liftIso`, `liftIso_functor`, `trivial`, `trivial_toLatticeKummer`); `classicalABC_of_thm311_strip`, `classicalABC_of_xi_strip` | done |
| (8) Splitting monoids and LGP-monoids; Thm 3.11(ii)(b) | `Split.lean` | `norm_ringEquiv_eq_one_iff`; `perpMonoid` (`Ψ⊥ = μ_r·g^ℕ`), `perpMonoid_le_splitMonoid`, `IsStrictGen`, **`perp_unit`** (units of `Ψ⊥` = torsion), `perp_norm_lt_one`, `perp_pow_eq_one_of_mem_domain`, **`LocalLogLink.perp_toFun_eq_zero`**; `piMap`, `restrictAut`; `lgpMonoid` (Prop 3.4(ii)), **`lgpMonoid_eq`**, `lgpEquiv`, `lgpPerp`, `lgpPerp_eq`; `LGPColumn` (Prop 3.5(i)), `perpKummer`, `gaussKummer`, **`lgpKummer`**, **`image_perpKummer`** (vertical coricity: equality), `image_gaussKummer`, `norm_kum_of_mem_splitMonoid`, `avgDeg_kum_of_mem_splitMonoid`, `avgDeg_lgpKummer`, `perpLogKummer`, **`perp_compat`**, `perp_compat_action` (Thm 3.11(ii)(b), Prop 3.5(ii)(c)), `perp_not_mem_domain`, `shift`, `LGPColumn.taut` | done |
| (9) Archimedean log-links | `Arch.lean` | `norm_ringEquiv`, `image_closedBall`, `norm_log_le_pi`, **`log_mul_sub_mem`** (homomorphism up to `2πiℤ`), `natCast_mul_log_root` (`μ_N` ↦ deck group), `exp_neg_log`, `exp_conj_log`, `neg_conj_mem_closedBall` ((Ind2) at `V^arc`); `ArchLogLink` (Def 1.1(ii)), `toFun_mem_closedBall`, `exp_symm_toFun`, `not_ringHom_eq_toFun`; `ArchColumn`, `iterDom`, `itF`, `back`, `itF_mem_closedBall`, `back_itF`, **`exists_surj`**, **`upperSemiCompat`** (Prop 3.5(ii)(b)), `logKummer`, `logKummer_subset`, `logKummer_shift`; packets: `archAbs_le_pi_of_mem`, **`tprod_mem_archLogShell`**, `tprod_log_mem_archLogShell` | done |
| (10) Number fields; Prop 3.10(ii), Thm 3.11(ii)(c) | `Global.lean` | `isIntegral_of_forall_finitePlace`, **`nonInterference`** (`K^× ∩ ∏_v Ψ_log = μ_K`), `nonInterference_set`, **`divisor_trivial_iff`** (Prop 3.10(iii)), `padicLog_algebraMap_root`, `natCast_mul_log_root_embedding`, **`globalLogKummer`**; `embFin`, `norm_embFin_le_one_iff`, `sectInf_apply`, `nonInterference_sect`, **`fmodLogKummer`**, `LogThetaLattice.globalLogKummer` | done |
| (11) Theorem 3.11 with LGP-monoids | `Thm311LGP.lean` | `isBadK_sectFin`, `isStrictGen_gaussGen`; `LGPLattice` (Def 3.8(iii)), `lgpCol`, `LGPLattice.ofData`; **`Thm311LGP`** (`base`, `splitCoric`, `splitCompat`, `splitDeg`, `globalCompat`, `modKernel`, `arcUpperSemi`, `arcSurj`), **`thm311LGP_model`**; **`xi_iff_ss_lgp`**, `classicalABC_of_thm311LGP`, **`answerLGP`** | done |

All theorems use only `propext`, `Classical.choice`, `Quot.sound`.

## Answers

### (3) The log-Kummer correspondence and log-shell compatibility

* **Upper semi-compatibility is proved, for every vertical line** (`LogColumn.upperSemiCompat`):
  the Kummer images of the units of every level and of all their iterated log-link images lie in
  the coric log-shell. It is only *upper* semi-compatibility: the two routes from the units of a
  level to the coric field differ (`kummer_log_ne`), and the images of the iterates are not
  units (`exists_iter_one_norm_lt`), which is why the container is the log-shell. The totality of
  the Kummer images is invariant under the translation of the column (`logKummer_shift`).
* **P19's `LogShellCompat` is derived** (`logShellCompat_of_unitInduced`) from the hypothesis that
  each Kummer identification of a log-shell container is *unit-induced*: on each tensor component
  an elementary tensor of factor scalings each of which is induced, through the logarithm, by an
  automorphism of the principal units (`UnitInducedScaling`). This is the structure IUT III gives
  these isomorphisms (tensor packets, Prop 3.2; `log(D^⊢_v) ≅ log(F^{⊢×μ}_v) ≅ log(F_v)` built
  from the `F^{⊢×μ}`-data, Prop 1.2(vi), (viii); Thm 1.5(iii), (iv)). The hypothesis is satisfied
  by the identity and by P19's alien identification `x ↦ −x` (`unitInducedScaling_negScale`),
  and fails for the `q`-power identifications of the drifting M3 rows
  (`not_unitInducedScaling_qScale_zpow`).
* **What further input is needed**: exactly the unit-inducedness of the Kummer identifications.
  The upper semi-compatibility of the log-Kummer correspondence does not imply it: it holds for
  every column (holomorphic Kummer isomorphisms), and constrains the images of units, not the
  mono-analytic scalings of the containers. In `LatticeKummer`, unit-inducedness is a field; it
  is **discharged** by the anabelian origin of the identifications (next item).

### (3') Unit-inducedness from the anabelian reconstruction (`Galois.lean`, `GalKummer.lean`)

* **Local theorem.** For a `p`-adic field `k` (both structures, `hball`) every automorphism `β`
  of the abstract group `𝒪_kˣ` induces, through the logarithm `ℚ ⊗ 𝒪_kˣ ≅ k` (`logEquiv`,
  P17's `logTensor` shown bijective), an additive automorphism `unitLogEquiv β` of `k` which is
  **unit-induced** (the principal units are the `(q−1)`-th powers of `𝒪_kˣ`, so `β` restricts
  to them, `prinOfUnits`) and hence preserves the log-shell. For a topological automorphism `φ`
  of `G_k`, P17 reconstructs `β = galUnitsEquiv φ` (the restriction of `galEquiv_multEquiv`),
  and `galLogEquiv φ` is exactly the transport of P17's `unitsQEquiv φ` on the group-theoretic
  `ℚ ⊗ 𝒪^×(G_k)` (`galLogEquiv_transport`); its log-shell preservation follows also from
  `map_monoLogShell` and `image_logTensor_monoLogShell` (`galLogEquiv_image_logShell`).
* **Model.** Kummer identifications given by their origin — elementary tensors of factor
  scalings that *are* the identifications induced by Galois automorphisms of the completions
  (`GalInducedScaling`, `D^⊢`-data) or by automorphisms of their unit groups
  (`AnabelianScaling`, `F^{⊢×μ}`-data / `Ism`) — are unit-induced (theorem), so `GalKummer`
  and `AnabelianKummer` give `LatticeKummer` data with the field discharged, and
  `distortion_eq_zero`, `xi_iff_ss` (now unconditional on the Kummer data: Theorem 3.11 holds in
  the model), `classicalABC_of_thm311` are restated for them. P20's `trivial` data come from the
  identity of the Galois groups, its `alt` data from the inversion of the units.
* **(3) What is not of this form.** Proved chain: Galois-induced ⇒ induced by `Aut(𝒪ˣ)` ⇒
  unit-induced ⇒ log-shell preserving ⇒ volume neutral (`shift = 0`). Hence every Kummer
  identification with `shift ≠ 0` does not arise from the reconstruction
  (`not_anabelianScaling_of_shift_ne_zero`), in particular `qScale^m`, `m ≠ 0`
  (`not_anabelianScaling_qScale_zpow`); at the factor level a scaling `x ↦ b·x` arising from the
  reconstruction has `‖b‖ = 1` (`norm_eq_one_of_factorUnitsAut`, `galLogEquiv_ne_scale`), and on
  the multiplicative side a Galois-induced `kˣ ≃* kˣ` never acts on a unit as multiplication by
  `q^m` (`v(q) ≠ 0`; it preserves `𝒪ˣ` and `v`: `galEquiv_multEquiv_ne_zpow_mul`). The
  converses (log-shell preserving ⇒ unit-induced; which `β` come from `Aut(G_k)`) are not
  established.
* **Remark (not formalised).** The cyclotomic character is group-theoretic ([AbsAnab],
  Prop. 1.2.1(vii)) and on `𝒪_kˣ ⊆ G_k^ab` it is `N_{k/ℚ_p}⁻¹`; so a Galois-induced
  identification preserves `Tr_{k/ℚ_p}`, and the only Galois-induced *scaling* is `b = 1`. P19's
  alien `x ↦ −x` therefore comes from the `F^{⊢×μ}`-data (`Ism`, the inversion of the units), not
  from an automorphism of `G_v`; the theorems above do not depend on this remark.
* **Galois automorphisms read off the strips (`StripKummer.lean`, `../HodgeTheater/StripLift.lean`;
  IUT I, Corollary 5.3(ii) in the model).** An automorphism `φ` of `G_v = Gal(K̄_v/K_v)` induces,
  through P17's `galEquiv_multEquiv` (which preserves `ord_v`, `ordPres_of_norm_le_one`), an
  autoequivalence `galFrob φ` of the `p`-adic Frobenioid of `K_v` (functorial in `φ`). For
  rigidified non-archimedean `D^⊢`-prime-strips with the groups `Gal(K̄_v/K_v)`
  (`RigidDGalStrip`), every isomorphism `f` lifts to the reconstructed `F^⊢`-prime-strips, with
  Frobenioid portion `galFrob (gal f v)` (`RigidDGalStrip.exists_lift`, `liftIso`, functorial);
  for unrigidified `F^⊢`-strips the lifts exist but are parametrised by arbitrary equivalences of
  the Frobenioid components (`FGalStrip.liftsEquiv`). `StripKummer L` carries rigidified
  `D^⊢`-strips at the vertices, isomorphisms `link a` to a coric strip, and Kummer
  identifications whose factor scalings are `compGalLogEquiv` of **the** automorphisms
  `gal (link a) v` read off these isomorphisms (`StripScaling`; no existential over `φ`);
  `toGalKummer`, and `distortion_eq_zero`, `xi_iff_ss`, `classicalABC_of_xi_strip` are restated.
  The lifted Frobenioid equivalence acts on `𝒪_vˣ` by `compGalUnits φ_v`, whose log-transport is
  the factor identification (`galMult_coe_units`, `compGalLogEquiv_eq_units`).
* **What remains an input.** (a) That the model's Kummer identifications are scalings (the
  equation `compGalLogEquiv φ = scale b` in the data; `exists_factorGalInduced_of_linear` builds
  `b = ψ(1)` from a `K_v`-linear `ψ`); (b) the archimedean places; (c) for Corollary 5.3(ii):
  the Galois automorphisms are now read off isomorphisms of rigidified `D^⊢`-prime-strips
  (`StripKummer`), but these strips, their rigidifications `κ_v` (the Kummer structures) and the
  isomorphisms `link a` are data of `StripKummer`, not extracted from the Hodge theaters of the
  lattice (the theaters' `F`-prime-strips are categories up to equivalence without base `G_v`);
  `Gal(K̄_v/K_v)` is used instead of the decomposition group `galModel` of P18; the uniqueness
  of the lift (the Frobenioid-theoretic part of Corollary 5.3) is not claimed; (d) the
  `G_v`-equivariance / `O^{×μ}_{k̄}` level of `Ism` (only the `G_v`-invariants `𝒪_kˣ` are used);
  P19's alien `x ↦ −x` is `F^{⊢×μ}`-data and is not strip-induced in this sense.

### (4) Theorem 3.11 and the wall

`Thm311 L K` records (i) the action of (Ind1), (Ind2) on the (Ind3)-choices and the multiradial
representation (outputs through any two vertices, transported to a common vertex, agree up to
(Ind3)), (ii) the upper semi-compatibility of the local vertical lines and the log-shell and
log-volume compatibility of the Kummer isomorphisms, (iii) the horizontal arrows inducing the full
poly-isomorphisms of the `F^{⊢×μ}`-prime-strips. **It holds in the model** (`thm311_model`); the
multiradiality is proved by moving the (Ind3)-choice along the log-shell compatible scaling
`κ_{h₁'}·κ_{h₁}⁻¹` (`ind3Act`, `act_lgp`). The contested content is Step (xi) of Corollary 3.12,
the explicit hypothesis `XiPrinciple K` (the wall of the lattice model along the horizontal
arrows). The chain: `wall_of_thm311 : Thm311 L K → XiPrinciple K → Wall D (theaterAlg D L.H)`,
then `Wall.classicalABC_of_wall`: **`classicalABC_of_thm311`** (Theorem 3.11 + Step (xi) for all
initial Θ-data ⇒ `ClassicalABC`), and `classicalABC_of_xi` (Step (xi) alone, since Theorem 3.11
holds in the model). As in M1d, this chain is bookkeeping: its content is Step (xi).

### (5) Does the log-theta-lattice give an η-algorithm with a different output law?

**No, not in this model.** `answer`: along every horizontal (Θ-link) and vertical (log-link)
arrow the distortion is `0` (unit-induced Kummer identifications are volume neutral); the
η-algorithm through any vertex has the identified-copies law `ThetaShift`, also after transport
to any vertex (`logVol_transport_out`); and **Step (xi) is the Scholze–Stix inequality**
`SSIneq D` (`xi_iff_ss`; independent of the lattice and the Kummer data, `xi_iff_xi`). This holds
for alien Kummer data, whose transports along all arrows are not ring isomorphisms
(`LatticeKummer.alt`, `alt_alien_horiz`, `alt_alien_vert`). In M3 terms: the only mechanism by
which the wall differs from SS (volume distortion of the transport) is excluded by
unit-inducedness. The log-links do act non-trivially on elements — a unit of level `m` has the
`q`-power `q^N` as its logarithm at level `m + 1`, which is why the log-link and the Gaussian
Θ-link do not commute (`log_theta_not_commute`) — but on containers they act only through the
inclusion into the log-shell ((Ind3), already the `∃ S` of the wall) and through unit-induced
identifications. A different output law would need a Kummer identification that is not
unit-induced (like `qScale^k`, moving value-group data into the unit portion) or an output that is
not `LGP` acting on an (Ind3)-choice; the structures formalised here produce neither (for the
Kummer identifications this is a theorem in the reconstruction setting: identifications arising
from Galois isomorphisms or automorphisms of the unit groups are volume neutral,
`not_anabelianScaling_of_shift_ne_zero`, `not_anabelianScaling_qScale_zpow`). This is a
statement about the model, conditional on its scope decisions; it neither proves nor refutes
`SSIneq D`, and it does not decide whether IUT's algorithm contains structure beyond the model.

### (6) LGP-monoids, Theorem 3.11(ii)(b), (c), archimedean places

(`Split.lean`, `Arch.lean`, `Global.lean`, `Thm311LGP.lean`)

* **(ii)(b), splitting monoids.** The Kummer images of `Ψ⊥` of every level are **equal** to the
  one coric `Ψ⊥` (`image_perpKummer`): the splitting monoids are vertically coric, not only upper
  semi-compatible. As `m` varies, the only elements of `Ψ⊥` in the domain of a log-link are
  `2ℓ`-th roots of unity (`perp_unit`, the units of `Ψ⊥` are its torsion), and the log-link sends
  them to `0` (`perp_compat`): multiplication by them at level `m` corresponds to addition of `0`
  at level `m + 1`, i.e. no indeterminacy. The Kummer isomorphisms of the Gaussian and LGP-monoids
  preserve the degrees (`avgDeg_kum_of_mem_splitMonoid`, `avgDeg_lgpKummer`).
* **(ii)(c), number fields.** `K^× ∩ ∏_v Ψ_log(F_v) = μ_K` (`nonInterference`, Kronecker's
  theorem via `NumberField.Embeddings.pow_eq_one_of_norm_le_one`); so the elements of `F_mod^×`
  related by the log-links of a column are roots of unity with vanishing log-link images at every
  `v ∈ V^non` (`fmodLogKummer`, `LogThetaLattice.globalLogKummer`) and logarithms in the deck group
  at `v ∈ V^arc`. The kernel of the divisor maps — the only global input of `F^⊛_MOD` besides the
  multiplicative group — is `μ_K` (`divisor_trivial_iff`), which gives the compatibility of the
  `MOD`-Frobenioids with the log-links (Proposition 3.10(iii)).
* **Archimedean (Ind3).** The log-link at `v ∈ V^arc` is a homomorphism up to the deck group
  `2πiℤ` (`log_mul_sub_mem`); the Kummer images of the units and of the closed balls of radius `π`
  lie in the coric closed ball of radius `π` (`ArchColumn.upperSemiCompat`), which contains, for
  every `m' ≥ 1`, a subset surjecting by the inverse of the `m'`-th iterate onto the units on which
  the iterate is defined (`exists_surj`) — the "`↠`" of (Ind3). For the packets of
  `Iut.LocalConstruct` the tensor products of such elements lie in `archLogShell`
  (`tprod_mem_archLogShell`).
* **(d) Re-check of Step (xi) and the distortion** (`answerLGP`, `xi_iff_ss_lgp`): unchanged. The
  distortion is `0` along all arrows and **Step (xi) is still the Scholze–Stix inequality**
  `SSIneq D`. The new structures add no source of distortion: the value-group (splitting) portion
  is precisely Kummer compatible with preserved degrees, the portions related by the log-links
  (in `Ψ⊥` and in `F_mod^×`) are roots of unity with logarithm `0`, and the archimedean (Ind3) has
  the same shape (inclusion into a log-shell, surjection) as the non-archimedean one, already
  absorbed by the `∃ S` of the wall.

## Simplifications (documented)

* At `v ∈ V^arc` (scope decision 6): only the log-links, the log-shell (closed disc of radius
  `π`) and (Ind3); the angular and radial log-volumes and the Aut-holomorphic orbispaces are not
  formalised.
* Principal units `1 + 𝔪` instead of `O^×_{k̄}` with its `Π_v`-action; `Iut.logShell` uses the
  factor `(2p)⁻¹` instead of `(p*)⁻¹` and `log(1+𝔪)` instead of `log(O^×)`.
* The poly-isomorphism `log(†F_v) ≅ ‡F_v` and the holomorphic Kummer isomorphisms are bicontinuous
  ring automorphisms of copies of one field; the `Π_v`-equivariance is not recorded.
* `LogLinkHT` records only the isomorphism `Ξ` of the `D-Θ^{±ell}NF`-Hodge theaters (P18's label
  layer); the lifting of `D^⊢`-prime-strip isomorphisms to `F^⊢`-prime-strips (IUT I,
  Corollary 5.3(ii)) is formalised only for separate rigidified non-archimedean strips
  (`../HodgeTheater/StripLift.lean`), not on the theaters, and without uniqueness. The local vertical lines of a lattice are
  separate data (`loc`), not derived from the Frobenioids of the `F`-prime-strips.
* The local LGP-monoids are the pull-backs of the Gaussian monoids along the ring isomorphism of
  the log-link (`Split.lean`); the `F_ℓ^{⋊±}`-symmetries and the processions (the capsules
  `S±_{j+1}`) are not recorded, only the labels `j = 1, …, ℓ*`. The output of the η-algorithm is
  still P18's `LGP·S` (Theorem 3.11(i)(b) in the model), not built from the LGP-monoids.
* Thm 3.11(ii)(c): the number fields and the divisor maps of the `F^⊛_MOD`-Frobenioids, not the
  Frobenioids; the `F^⊛_mod`-Frobenioids and their failure of log-link compatibility (Remark
  3.10.1) are not formalised. Thm 3.11(iii)(b)–(d) (mono-theta environments) is not expressed by
  the model objects.

## What remains

* The anabelian side beyond `Galois.lean` / `GalKummer.lean` / `StripKummer.lean`: extracting
  the rigidified `D^⊢`-prime-strips and their isomorphisms from the Hodge theaters of a lattice
  (the Galois automorphisms are read off strips that are data of `StripKummer`, IUT I,
  Corollary 5.3(ii) in the model); `Ism` at the level of `O^{×μ}_{k̄}`; the archimedean Kummer theory
  (Aut-holomorphic orbispaces) and log-volumes.
* The Frobenioids of Proposition 3.7 (`F^⊛_MOD`, `F^⊛_mod`, the global realified LGP- and
  lgp-Frobenioids) and of Theorem 1.5(v), beyond the number fields and divisor maps of
  `Global.lean`; the derivation of `LGPLattice.kum_gen` from the Kummer theory of the theta
  values (P16).
* An η-algorithm whose output is not `LGP` acting on an (Ind3)-choice, or a Kummer identification
  that is not unit-induced, with an IUT source — the only routes, in this model, to a wall
  different from `SSIneq D` (P21–P22).
