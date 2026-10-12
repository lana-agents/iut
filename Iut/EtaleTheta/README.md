# The étale theta function and mono-theta environments (`Iut/EtaleTheta/`)

Work package P16 of the wall roadmap: the algebraic and Kummer-theoretic content of

> S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*,
> Publ. RIMS 45 (2009), §§1–2 (cited **[EtTh]**),

as far as it is reachable with the tempered and Kummer-theoretic machinery available to this
repository, and its link to the theta values used in `Iut/Wall`.

**Status of the dependency.** No module of `Iut/EtaleTheta/` is imported by the comparator
challenge (`Comparator/Challenge.lean`) or by `Iut/Concrete/*`. Every theorem uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Inputs

* `tate-curves-theta` (pinned at `d1fba94`, which adds `TateCurvesTheta/Kummer/*`): the Tate
  parameter `TateParameter K`, the theta series `θ(u) = ∑ q^{n(n+1)/2} uⁿ`, its functional
  equations, its zero divisor `-qᶻ`, the odd theta function `thetaOdd u = u·θ(-u²)`, the Kummer
  classes of theta values (`Kummer/ThetaValues.lean`) and the comparison of the Kummer class of
  the germ of `θ` with the class of its value on decomposition groups
  (`Kummer/ThetaGerm.lean`, `decomposition_kummer_thetaGerm`).
* `continuous-kummer-theory` (`98b67df`, a dependency of `tate-curves-theta`): continuous
  `H¹`, the Kummer map `kummer n K Ω : Kˣ →* H¹_cont(Gal(Ω/K), μ_n)` and its `Ẑ(1)` form.
* `tempered-fundamental-groups` (pinned `33b1c27`): the tempered fundamental group of an affine
  orbifold over integral models, André's identification and the non-degeneracy of the tempered
  group of IUT's Tate orbicurves. It does **not** provide the `ℤ`-covering `Y → X` of the Tate
  curve as a tempered covering with its Galois group, the theta quotient `Π^Θ`, or Kummer
  classes in `H¹(Π^tp, Ẑ(1))`; see the scope decisions.

## Milestones

### (1) The theta covering and the theta function `Θ̈` (`Theta.lean`)

The coverings `Ÿ → Y → X` of [EtTh], §1, are recorded through their effect on the
multiplicative coordinate (scope decision S1): `Y` is the `ℤ`-covering of the Tate curve
`X = Kˣ/qᶻ` with coordinate `U`, `Ÿ → Y` is `Ü ↦ Ü² = U`, the generator of `Gal(Y/X) ≅ ℤ` acts
on `Ü` by `Ü ↦ s·Ü` with `s² = q` (the `ℤ`-action on `Ÿ` of [EtTh], Prop. 1.4(ii)), and
`Gal(Ÿ/Y) = {±1}`.

* `etaleTheta t U = U·θ(-U²)` (`= TateParameter.thetaOdd`), [EtTh], Prop. 1.4:
  `hasSum_etaleTheta`: `Θ̈(Ü) = ∑ₙ (-1)ⁿ q^{n(n+1)/2} Ü^{2n+1}`, which is [EtTh]'s
  `q^{-1/8} ∑ (-1)ⁿ q^{(n+1/2)²/2} Ü^{2n+1}` (the exponents agree:
  `(n+1/2)²/2 - 1/8 = n(n+1)/2`).
* Prop. 1.4(ii): `etaleTheta_inv` (`Θ̈(Ü⁻¹) = -Θ̈(Ü)`), `etaleTheta_neg` (`Θ̈(-Ü) = -Θ̈(Ü)`),
  `etaleTheta_zpow_sqrt_mul` (`Θ̈(s^a·Ü) = (-1)^a·s^{-a²}·Ü^{-2a}·Θ̈(Ü)`, i.e.
  `Θ̈(q^{a/2}Ü) = (-1)^a q^{-a²/2} Ü^{-2a} Θ̈(Ü)`).
* Prop. 1.4(i), zero part: `etaleTheta_eq_zero_iff` (zeros exactly at `Ü² ∈ qᶻ`, the cusps of
  `Ÿ`).
* The automorphy factor `thetaFactor s a Ü = (-1)^a s^{-a²} Ü^{-2a}` is a `1`-cocycle of `ℤ`
  acting through `s^ℤ` (`thetaFactor_add`), the algebraic shadow of the extension
  `1 → Δ_Θ → Π^Θ → Π^ell → 1`.

### (2) The étale theta class (`KummerClass.lean`)

Scope decision S2: the class `η^Θ ∈ H¹(Π^tp_Ÿ, Δ_Θ)` lives in the cohomology of a tempered
group that is not available as a Galois group of a field extension in this repository. What is
formalized is its image on points and on germs:

* `kummer_etaleTheta_zpow_sqrt_mul`: **[EtTh], Prop. 1.5(iii) on points.** In
  `H¹_cont(Gal(Ω/K), μ_n)`, `κ(Θ̈(s^a Ü)) = κ(-1)^a·κ(s)^{-a²}·κ(Ü)^{-2a}·κ(Θ̈(Ü))`, i.e.
  `η ↦ η - 2a·log(Ü) - (a²/2)·log(q)` (plus the sign class), for every `n`; also in `Ẑ(1)` form.
* `kummer_etaleTheta_inv`, `kummer_etaleTheta_neg`: the inversion automorphism.
* `kummer_smul_etaleTheta`: scalar multiples `c·Θ̈` change the class by `κ(c)` — the
  `O^×`-indeterminacy of Prop. 1.3.
* `decomposition_kummer_etaleThetaGerm`: [EtTh], Prop. 1.4(iii), in the germ model of
  `tate-curves-theta`: the Kummer class of the germ of the regular function `Θ̈·Ü⁻¹ = θ(-U)` on
  `Y` (the function used in the proof of Prop. 1.5) at a non-cuspidal point `Ü₀` restricts, on a
  decomposition group, to the Kummer class of `Θ̈(Ü₀)·Ü₀⁻¹`.

### (3) Theta values at the torsion points (`ThetaValues.lean`)

* `etaleTheta_sqrtNeg_zpow`: with `i² = -1`, `s² = q`:
  `Θ̈(i·s^j) = s^{-j²}·Θ̈(i)`, the Gaussian `q^{-j²/2}` of [EtTh], Prop. 1.4(ii) and
  IUT I, Example 3.2(iv); `thetaRatio t s j = s^j θ(q^j)/θ(1)` is the `i`-free form
  (`etaleTheta_ratio`) and `thetaRatio_eq : thetaRatio t s j = s^{-j²}`.
* `etaleTheta_halfPeriod`: the same Gaussian through `tate-curves-theta`'s
  `theta_sqrt_zpow` at the points `√q^{2j-1}`.
* **IUT's normalization.** `Θ_v := Θ̈(i)/Θ̈(U)` (reciprocal of `Θ̈` normalized to `1` at `√-1`):
  `thetaV_value : Θ_v(i·s^j) = s^{j²}`, and for `r^ℓ = s` (`r^{2ℓ} = q`):
  `pow_eq_thetaV_iff`: the `ℓ`-th roots of `Θ_v(i·s^j)` are exactly `ζ·r^{j²}`, `ζ ∈ μ_ℓ`
  (IUT II, Remark 2.5.1: “the `μ_{2ℓ}`-orbit of `q_v^{j²}`”, `q_v = q^{1/2ℓ}`).
* `kummer_thetaRatio`: `κ(Θ̈(i s^j)/Θ̈(i)) = κ(s)^{-j²}`.
* **Rigidity of scalar multiples, algebraic core** ([EtTh], Thm. 1.10, Cor. 2.8, Def. 1.9):
  `normalized_iff`: the scalar multiples `c·Θ̈` whose value at `√-1` is a root of unity of
  order dividing `m` are exactly `c ∈ μ_m·Θ̈(i)⁻¹`; the normalized theta values at the labels
  `j` are then determined up to `μ_m` (`normalized_value`).

### (4) Mono-theta environments and rigidity (`Heisenberg.lean`, `MonoTheta.lean`,
`DiscreteRigidity.lean`)

* `Heisenberg.lean` — **the theta group.** The theta quotient `(Δ^tp_X)^Θ` is a central
  extension `1 → Δ_Θ → Δ^Θ → Δ^ell → 1` with `Δ^ell ≅ Ẑ(1) × ℤ`; its model is the Heisenberg
  group `ThetaGroup M l = M × M × ℤ` (`(c,a,b)·(c',a',b') = (c+c'+l·b·a', a+a', b+b')`, `M` the
  cyclotome, `l` the degree of the `l·ℤ`-covering of [EtTh], §2):
  `commutator_eq` (the commutator pairing `[(a,b),(a',b')] = l(b a' - b' a)`),
  `mem_center_iff` (center `= Δ_Θ` for torsion-free `M`, `l ≠ 0`),
  `commutator_eq_theta` (**[EtTh], Prop. 2.12(i)**: `[Δ^Θ, Δ^Θ] = l·Δ_Θ`),
  `cyclotomicRigidity` (**algebraic core of [EtTh], Cor. 2.19(i)**: an automorphism inducing
  `α` on the `ell`-cyclotome and `ε = ±1` on the `ℤ`-part acts on `Δ_Θ` by `ε·α`; the
  identification of the two cyclotomes `a ↦ [a, t]` is intrinsic).
* `MonoTheta.lean` — **sections of the cyclotomic envelope** `Π[μ] = μ ⋊ Π`
  ([EtTh], Def. 2.10, 2.13): `sectionOf` (homomorphic sections `↔` `1`-cocycles, `isHom_iff`,
  `eq_sectionOf`), the algebraic (tautological) section `sectionOf_one`, `conj_sectionOf_iff`
  (`μ`-conjugate sections `↔` cohomologous cocycles), `range_conj_iff` and
  `thetaClassSubgroups_eq_iff` (datum (c) of a model mono-theta environment, the `μ`-conjugacy
  class of the image of the theta section, determines and is determined by the cohomology class
  of the cocycle), `sectionOf_mul_inr_inv` (the difference of the theta and algebraic sections
  recovers the cocycle — the "isomorphism of cyclotomes" of Cor. 2.19(i)); the structure
  `MonoThetaEnv` (Def. 2.13(ii): a topological group, a subgroup of automorphisms containing the
  inner ones, and a set of subgroups) with isomorphisms `MonoThetaEnv.Iso` forming a groupoid.
* `DiscreteRigidity.lean` — **[EtTh], Prop. 2.15 (discrete rigidity)**, completely: the
  category `T` of `ℤ`-torsors `T_M` with translations by `Mℤ`, `E`-systems, (i)
  `Aut(T_M) = Mℤ`, (ii) any two `E`-systems on `T_1` are isomorphic, (iii) the invariant
  `j^S_∞` (as a compatible family of residues) is surjective and an isomorphism invariant mod
  `ℤ`, (iv) non-isomorphic `E`-systems on `T_M` exist (for `E = {(n+1)!}`; `j_∞ = ∑ (k+1)!` is
  not an integer, `jF_not_integer`).

### (5) Link to the wall (`Wall.lean`)

* `Iut.EtaleTheta.qroot_pow_ell_mul_thetaRatio`: for `D : InitialThetaData` and a bad place `v`
  of `K`, with `s = q_v^ℓ` (`sqrtQ`; `q_v = D.qroot v`, `q_v^{2ℓ} = q`), `(q_v^{j²})^ℓ` is the
  value `Θ_v(i·s^j) = (Θ̈(i s^j)/Θ̈(i))⁻¹ = (s^j θ(q^j)/θ(1))⁻¹` of IUT's normalized theta
  function; `pow_eq_thetaRatio_inv_iff`: its `ℓ`-th roots are exactly the `μ_ℓ`-multiples of
  `q_v^{j²}` (`lgpValue`). `scaleEltAt_eq`: the element placed by the wall's LGP map
  (`InitialThetaData.scaleEltAt`, used by `Iut.Wall.lgpElt`; the degrees of
  `Iut.Arakelov.thetaBundle` are those of the same `q_v^{j²}`) is `lgpValue D v (i + 1)`. So the
  LGP theta values of the wall are `ℓ`-th roots of the theta values of (3).

## Scope decisions

* **S1 (coverings as coordinate data).** The tempered covering `Ÿ → Y → X` and its special fibre
  (an infinite chain of `ℙ¹`s labelled by `ℤ`) are not constructed as objects of
  `tempered-fundamental-groups`; the covering is recorded by the action of its deck groups on the
  coordinate `Ü` of the analytic uniformization `Kˣ → Kˣ/qᶻ` (`tate-curves-theta`). The divisor
  `D_N` and the line bundles `L_N` of §1 are not formalized.
* **S2 (classes on points and germs).** The étale theta class is formalized through its
  restrictions to points (Kummer classes of values) and germs (`thetaGerm`), not as a class in
  `H¹(Π^tp_Ÿ, Δ_Θ)`.
* **S3 (group theory of the environments).** The mono-theta environment of [EtTh], Def. 2.13 is
  defined for an abstract topological group; the model environment is built from an abstract
  cocycle on an abstract group (`Π^tp_Ÿ` is not available). Theorems about the abstract
  environment (cohomology-class invariance, the groupoid) are proved; the identification of the
  model group with `Π^tp_Y[μ_N]` is not.

## Research-level, not formalized

* **Cyclotomic rigidity** ([EtTh], Cor. 2.19(i)) in full: a functorial group-theoretic
  algorithm on an abstract mono-theta environment `M•` recovering the subquotients
  `(l·Δ_Θ)[μ_N] ⊆ (Δ^tp_Y)^Θ[μ_N] ⊆ (Π^tp_Y)^Θ[μ_N]` and the two splittings. Needs
  `Π^tp_Y[μ_N]`, temp-slimness of `Π^tp_Y` ([EtTh], Prop. 2.11) and the theta quotient of the
  tempered group (Prop. 2.12). The Heisenberg-group computation above is the core step of
  Prop. 2.12/2.14(i).
* **Discrete rigidity for mono-theta environments** (Cor. 2.19(ii)): projective systems of
  mono-theta environments are isomorphic to the model system; reduces to Prop. 2.15
  (formalized) plus Cor. 2.18 (the group-theoretic construction of `Π^tp_X` from `M`).
* **Rigidity of scalar multiples** (Thm. 1.10, Cor. 2.19(iii)): the standard-type classes are
  characterized group-theoretically by their restrictions to the decomposition groups of the
  torsion points labelled `0`. Needs the tempered anabelian rigidity Thm. 1.6 (`Π^tp_X`
  determines the `ℤ`-covering and its labels) and the restriction maps to decomposition groups in
  `H¹(Π^tp)`.
* Tempered anabelian rigidity of the étale theta function (Thm. 1.6), the theta trivializations
  `τ_N` and their compatibility (Lemma 1.2), and the Frobenioid-theoretic manifestations
  (§§3–5).
