# The log-link and the log-theta-lattice (`Iut/LogLink/`, roadmap P20)

A Lean formulation of IUT III, §1 (Definition 1.1, Propositions 1.2, 1.3, Definition 1.4,
Theorem 1.5) and of the parts of §3 that the wall needs (Proposition 3.5(ii), the
log-Kummer correspondence and (Ind3); Theorem 3.11 as a statement), on top of P15–P19, and the
connection of Theorem 3.11 to the wall (`Iut/Wall/`).

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
   `(p*)⁻¹·log(O^×)`). The archimedean log-links (Definition 1.1(ii)) are not formalised.
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

## Plan (lemma-level milestones) and status

| Milestone | File | Main results | Status |
|---|---|---|---|
| (1) Local log-links | `Local.lean` | `prinUnits`, `logHom` (Prop 1.2(ii): `log` is a homomorphism `1+𝔪 → (k,+)`), `padicLog_mem_logShell`, `norm_padicLog_one_add` (log is an isometry on `‖a‖ ≤ ‖2p‖`: Prop 1.2(iii) at the level of radii), `exists_prinUnit_padicLog_eq`; `LocalLogLink` (Def 1.1(i)), `toFun_mul`, `image_logShell` (the log-shell is an object of the codomain), Prop 1.2(v): `logShell_bounded` (a_non), `closedBall_subset` (b_non), `toFun_mem_logShell` (c_non); Prop 1.2(iv): `not_ringHom_eq_toFun`; `exists_toFun_eq`; `UnitInduced`, `UnitInduced.symm`, `.trans`, **`image_logShell_of_unitInduced`**, `unitInduced_neg`, `prinMap`, `unitInduced_ringEquiv`, `scale_image_logShell_ne`, `not_unitInduced_scale` | done |
| (2) Vertical lines | `Column.lean` | `LogColumn`, `iter`, `shift`, `iter_shift`, `logKummer`, `logKummer_shift` (translation invariance, Prop 3.5(ii)), `kum_image_logShell` (vertical coricity of the holomorphic log-shell), `iter_subset_logShell`, **`upperSemiCompat`**, `logKummer_subset` (Prop 3.5(ii)(a), (Ind3)), `kummer_log_ne` (Prop 1.2(iv)), `exists_iter_one_norm_lt` (the images are not units), `norm_map_lt_one`, **`log_theta_not_commute`** | done |
| (3) The log-theta-lattice | `Lattice.lean` | `LogLinkHT`, `LogLinkHT.dIso`, `logLinkEquiv`, `card_logLinkHT` (= 2), `nonempty_logLinkHT` (Prop 1.3); `LogColumn.taut`; `LogThetaLattice` (Def 1.4); `vertIso`, `vertCoric` (Thm 1.5(i)), `horizCoric`, `horizCoric_full` (Thm 1.5(ii)), `biCoric` (Thm 1.5(iii)), `row` (P19 Frobenius-pictures), `col`, `not_commute`, `ofData` | done |
| (4) Log-shell compatibility derived | `Kummer.lean` | `tprod_mul_mem_tensorLogShell`, `tprod_image_tensorLogShell`, `FactorUnitInduced`, `factorMk_image_factorLogShell`, `FactorUnitInduced.image_eq`, `factorUnitInduced_one`, `factorUnitInduced_neg_one`, `tprod_image_tensorLogShell_of_unitInduced`; `UnitInducedScaling`, **`logShellCompat_of_unitInduced`**, `shift_eq_zero_of_unitInduced`, `unitInducedScaling_one`, **`unitInducedScaling_negScale`**, `not_unitInducedScaling_qScale_zpow`; `LatticeKummer` (`logShellCompat`, `toLinkedChain`, `model`, `model_kummerVolCompat`, `model_volCompat`, `distortion_eq_zero`, `distortion_horiz`, `distortion_vert`, `trivial`, `alt`) | done |
| (5) Theorem 3.11 and the chain to ABC | `Thm311.lean` | `logShellCompat_mul`, `logShellCompat_inv`, `act_lgp`, `act_le`, `ind3Map`, `ind3Act`; `horizRel`, `vertRel`; **`Thm311`**; `LatticeKummer.model_multiradial3` (Thm 3.11(i) in the model), `model_thetaShift`; **`thm311_model`**; **`XiPrinciple`**; **`variant_of_thm311`**, **`wall_of_thm311`** (the input of `Iut/Wall`), **`classicalABC_of_thm311`**, `classicalABC_of_xi`, **`xi_iff_ss`**, `xi_iff_xi`; `logVol_transport_out`, **`answer`**, `alt_alien_horiz`, `alt_alien_vert` | done |

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
  mono-analytic scalings of the containers. In the model, unit-inducedness is an input (a field
  of `LatticeKummer`); in IUT it is the content of the construction of the mono-analytic
  log-shells from `F^{⊢×μ}`, which is anabelian (P17) and not formalised here.

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
not `LGP` acting on an (Ind3)-choice; the structures formalised here produce neither. This is a
statement about the model, conditional on its scope decisions; it neither proves nor refutes
`SSIneq D`, and it does not decide whether IUT's algorithm contains structure beyond the model.

## Simplifications (documented)

* Only `v ∈ V^non`; the archimedean log-links (Definition 1.1(ii), complex logarithm, angular and
  radial log-volumes) are not formalised.
* Principal units `1 + 𝔪` instead of `O^×_{k̄}` with its `Π_v`-action; `Iut.logShell` uses the
  factor `(2p)⁻¹` instead of `(p*)⁻¹` and `log(1+𝔪)` instead of `log(O^×)`.
* The poly-isomorphism `log(†F_v) ≅ ‡F_v` and the holomorphic Kummer isomorphisms are bicontinuous
  ring automorphisms of copies of one field; the `Π_v`-equivariance is not recorded.
* `LogLinkHT` records only the isomorphism `Ξ` of the `D-Θ^{±ell}NF`-Hodge theaters (P18's label
  layer); the unique lifting of `D`-prime-strip isomorphisms to `F`-prime-strips (IUT I,
  Corollary 5.3(ii)) is anabelian and not formalised. The local vertical lines of a lattice are
  separate data (`loc`), not derived from the Frobenioids of the `F`-prime-strips.
* The LGP-monoids with log-shell unit portions (IUT III, Propositions 3.4–3.7) are not built; the
  output of the η-algorithm is P18's `LGP·S` (Theorem 3.11(i)(b) in the model).
* Thm 3.11(ii)(b), (c) (splitting monoids, number fields `M_mod`, global Frobenioids) and
  (iii)(b)–(d) (mono-theta environments) are not expressed by the model objects.

## What remains

* The anabelian side: reconstructing the mono-analytic log-shells and the Kummer identifications
  from `D^⊢` / `F^{⊢×μ}` (P17), which would turn `UnitInducedScaling` from an input into a
  theorem; archimedean log-links.
* The LGP-monoids of Propositions 3.4–3.7 and Theorem 3.11(ii)(b), (c); the global realified
  Frobenioids of Theorem 1.5(v).
* An η-algorithm whose output is not `LGP` acting on an (Ind3)-choice, or a Kummer identification
  that is not unit-induced, with an IUT source — the only routes, in this model, to a wall
  different from `SSIneq D` (P21–P22).
