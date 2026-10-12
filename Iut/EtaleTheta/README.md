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
  group of IUT's Tate orbicurves. It provides the `ℤ`-covering `Y → X` of the Tate curve as a
  tempered covering (`TateObject.X₀`: the unrolled `2`-gon of the special fibre of a model of
  the Tate curve) with its deck group `ℤ` (`TateObject.deck`, simply transitive on the fibre)
  and the character `Π^tp_X → ℤ` (`TateObject.character`, nontrivial by Theorem B); this is
  used from step 2 on (`TemperedCovering.lean`). It does **not** provide `Ÿ → Y`, the theta
  quotient `Π^Θ`, or Kummer classes in `H¹(Π^tp, Ẑ(1))`; see the scope decisions.

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

## Step 2 of the wall roadmap: the tempered theta covering and cyclotomic rigidity

Targets: the tempered coverings `Ÿ → Y → X` of the Tate curve as tempered objects, the étale
theta class in `H¹(Π^tp_Ÿ, Δ_Θ)`, temp-slimness and the theta quotient, full cyclotomic
rigidity ([EtTh], Cor. 2.19(i)) and discrete rigidity of systems (Cor. 2.19(ii)), and the
tempered Frobenioid as an actual construction. Plan with lemma-level milestones, and status:

### (6) The `ℤ`-covering `Y → X` (`TemperedCovering.lean`) — done

Input: `TateObject.X₀ T` of `tempered-fundamental-groups` for Tate data `T` over a level
`(R, 1)` (`A` trivial).

* (6a) `TateObject.piY T V hV := ker(TateObject.character)` — **`Π^tp_Y`**; `isOpen_piY`,
  `piY_normal`.
* (6b) `mem_piY_iff`: `Π^tp_Y` is the **stabilizer of the base point of the fibre of `Y`**
  (from the simply transitive deck action; the defining property of the tempered group of a
  covering).
* (6c) `deck_injective`: `ℤ` acts faithfully on `Y`.
* (6d) `quotKerEquivInt` (a nontrivial character `G → ℤ` has `G / ker ≅ ℤ`, via
  `subgroupEquivInt`), `TateObject.piYQuotEquivInt`: **`Π^tp_X / Π^tp_Y ≅ ℤ`** when the
  character is nontrivial.
* (6e) `TateObject.exists_character_ne_one'` (good Tate data, Theorem B with
  `zariskiConnected` discharged) and, for IUT's orbicurves `E ∖ (E[ℓ] + M)` with a good Tate
  presentation over a complete DVR of mixed characteristic with perfect residue field,
  `TateOrbicurve.exists_character_ne_one`, `TateOrbicurve.piYQuotEquivInt`: **unconditionally
  `Π^tp_X / Π^tp_Y ≅ ℤ`**.

### (7) Cyclotomic envelope, temp-slimness, theta quotient (`CyclotomicEnvelope.lean`) — done
(formal parts)

* (7a) `TempSlim` (temp-slim topological groups), `TempSlim.center_eq_bot`.
* (7b) The envelope `Π[μ] = μ ⋊ Π` ([EtTh], Def. 2.10) with the product topology
  (`Envelope.instTopologicalSpace`, scoped), `Envelope.homeomorphProd`.
* (7c) **[EtTh], Prop. 2.11(ii)**: `Envelope.mem_range_inl_iff` (for `Π` temp-slim, `μ`
  discrete, open kernel of the action: `μ` = union of the centralizers of open subgroups);
  `apply_mem_range_inl_iff`, `map_range_inl`, `rightEquiv`, `rightEquiv_rightHom`: isomorphisms
  of envelopes respect `μ` and induce isomorphisms `Π_α ≅ Π_β` compatible with the surjections.
* (7d) **[EtTh], Prop. 2.11(i)**: `Envelope.center_eq_range_inl`.
* (7e) **[EtTh], Prop. 2.12(ii) from (i)**: `commutator_prod_inf`,
  `ThetaGroup.commutator_envelope_inf` (with `ThetaGroup.commutator_eq_theta` = Prop. 2.12(i)).

### (8) Cyclotomic rigidity (`CyclotomicRigidity.lean`) — done for the theta quotient

* (8a) `Env`, `Env.Iso`: abelian mono-theta environments `(Π, D, S)` (for the abelian theta
  quotient `(Δ^tp_Y)^Θ[μ_N]`, `Out = Aut` and `μ_N`-conjugacy is trivial).
* (8b) **The functorial algorithm**: `Env.mu` (torsion), `Env.taut` (generated by `γ(β) - β`,
  `γ ∈ D`, [EtTh], Prop. 2.14(i)), `Env.L`, `Env.thetaSplit`, `Env.IsCyc` (the isomorphism of
  cyclotomes as the difference of the two splittings); functoriality
  `Env.Iso.map_mu`, `map_taut`, `map_L`, `map_thetaSplit`, `isCyc_iff`.
* (8c) `ThetaGroup.tgen_zpow`, `ThetaGroup.conj_tpow`: `Gal(Y/X)` acts on
  `(Δ_Y)^Θ = Δ_Θ × (Δ_Y)^ell` by `(c, a) ↦ (c + k·l·a, a)` (conjugation in the Heisenberg group);
  `gammaK_apply`.
* (8d) The model `model M l μ red ρ` (`D = {γ_k}`, `S` = image of the theta section
  `s^Θ(c, 2a') = (-red c - ρ a', c, 2a')` on `(Δ_Ÿ)^Θ`), and the algorithm on it:
  `model_mu`, `model_taut` (**Prop. 2.14(i)**), `model_L`, `model_thetaSplit`, `model_isCyc`.
* (8e) **`cyclotomicRigidity`** ([EtTh], Cor. 2.19(i) for the theta quotient): every
  isomorphism `E ≅ model` carries the algorithmic `μ`, `taut(l·Δ_Θ)`, `(l·Δ_Θ)[μ]`, theta
  splitting and isomorphism of cyclotomes of `E` to the model ones (`-red`, the restriction of
  the theta class); `cyclotomicRigidity_aut` (automorphisms of the model preserve the
  isomorphism of cyclotomes); `model_isCyc_pow` (Remark 2.19.2: `n`-th powers give `-n·red`).

### (9) Discrete rigidity of systems (`RigidSystems.lean`) — done (formal part)

* (9a) `exists_compatible_seq` (König's lemma for sequences of finite sets).
* (9b) `exists_untwist`: `lim¹ = 1` for towers of groups with compatible surjections onto a
  fixed group with finite kernels ("the `R¹ lim` of `{Hom(ℤ/2, ℤ/N)}` vanishes").
* (9c) `Tower`, `Tower.System`, **`Tower.discreteRigidity`** ([EtTh], Cor. 2.19(ii) from
  Cor. 2.18(iv)): a projective system levelwise isomorphic to the models is isomorphic to the
  model system; `Tower.discreteRigidity_of_surjective`. Prop. 2.15 (`DiscreteRigidity.lean`)
  shows that finite kernels are needed (`exists_not_iso` for the bi-theta-type systems).

### (10) Tempered Frobenioids (`Iut/Frobenioid/TemperedBase.lean`, `Tempered.lean`) — done
(combinatorial monoids)

* (10a) `OrbitObj Π` = `B^temp(Π)⁰`, connected and totally epimorphic; FSM-morphisms bijective.
* (10b) `TemperedFrobenioidData Π` on `B^temp(Π)⁰` (replacing the earlier interface with a
  realization functor into `TempObj` and assumed connectedness/total epimorphicity);
  `isFrobenioid`.
* (10c) `thetaData χ` (divisors pulled back from the `ℤ`-chain of components of `Y`; theta
  monomial divisors `a + b·j + c·j²`), `thetaData_isFrobenioid`; `divTheta = -j²`,
  `pb_deck_divTheta` (divisor form of Prop. 1.4(ii)).
* (10d) `tateThetaData T V hV` for `Π^tp_X = temperedPi1` of the Tate curve and
  `χ = TateObject.character`; `tateThetaData_isFrobenioid`; `tateY` (its subgroup is `Π^tp_Y`
  of (6a)).

### (11) The model étale theta class in `H¹` (`ThetaClass.lean`) — done (model)

* (11a) On the discrete model `(Π^tp_Ÿ)^Θ = Δ_Θ × 2·(Δ_Y)^ell` acting trivially on `μ`, the
  cocycle `thetaCocycle red ρ : (c, a') ↦ red c + ρ a'` and its class `thetaClass red ρ` in
  `ContH1` (`continuous-kummer-theory`).
* (11b) `thetaSection_eq`: the theta section of the model environment (8d) is the tautological
  section minus the class; `thetaClass_eq_one_iff` (trivial iff `red = ρ = 0`),
  `thetaClass_ne_one`; `thetaClass_restrict` (restriction to `Δ_Θ` is `red`) and
  `model_isCyc_eq_neg_thetaClass` (the cyclotome isomorphism of (8) is minus that restriction).
* (11c) The `Gal(Y/X)`-conjugates (geometric shadow of [EtTh], Prop. 1.5(iii)): `conjK`,
  `conj_sub_thetaCocycle` (`η ∘ γ_k − η = 2kl·red(a')`), `gammaK_thetaSection`.

### (12) The arithmetic model and Prop. 2.14(i) (`ArithEnv.lean`) — done (model)

* (12a) `Arith = (μ × Δ_Θ × (Δ_Y)^ell) ⋊ G` with `G` acting through a cyclotomic character
  `χ : G → ℤˣ` (`cycAct`); the automorphisms `arithAut k κ` (`γ_k` composed with the Kummer twist
  by a Kummer cocycle `κ : G → μ`, the `K^×`-part of `D`), which are the identity on `G` and `γ_k`
  on the geometric subgroup (`arithAut_right`, `arithAut_inl`).
* (12b) **[EtTh], Prop. 2.14(i)** (`prop214`, `prop214_inter`): for center-free `G` (the input of
  Mochizuki's proof: `G_K` is center-free), the `γ(β)·β⁻¹` with `β` geometric and `γ ∈ Aut(Π)`
  whose class in `Out(Π)` lies in `D` and which is the identity on `G` form exactly the
  tautological image of `l·Δ_Θ`.

### (13) Automorphisms of the mod `N` models, discrete rigidity — done (model)

Files `ModelAut.lean`, `ModelTower.lean`.

* (13a) The groupoid of environments (`Env.Iso.refl/trans/symm/ext`, the group `Env.Iso E E`) and
  the mod `N` model `modelN N l` (`Δ_Θ = (Δ_Y)^ell = ℤ`, `μ = ℤ/N`, `ρ = 0`).
* (13b) **The analogue of [EtTh], Cor. 2.18(iv)**: `toQuot : Aut(modelN) →* Perm(ℤ²)` (the action on
  `Π/μ`), with image the upper triangular automorphisms with diagonal `±1`
  (`toQuot_mem_upper`, `range_toQuot`, `toUpper_surjective`, the lifts `liftAut`), **finite kernel**
  (`finite_ker`) and, for `l` a unit mod `N`, **kernel `≅ Hom(ℤ/2, ℤ/N)`** (`kerEquiv`, the
  automorphisms `(m, c, a) ↦ (m + a·x, c, a)`, `2x = 0`).
* (13c) Reduction of environments `Env.red e` (quotient by `e·μ`, the induced mod `e` environment),
  functorial (`Env.redIso`, `redFunctor` on `EnvCat`); `redModel`: `(modelN N' l)_N ≅ modelN N l`
  for `N ∣ N'`; `toQuot_redAut`: compatible with `toQuot`.
* (13d) **[EtTh], Cor. 2.19(ii), for the geometric theta quotient** (`LevelChain.discreteRigidity`):
  for a chain `N₀ ∣ N₁ ∣ ⋯` and `l ≠ 0`, every projective system levelwise isomorphic to the models
  is isomorphic to the natural projective system — `RigidSystems.Tower.discreteRigidity` (9c)
  instantiated with (13b), (13c).

### (15) The double covering `Ÿ → Y` (`TemperedDouble.lean`) — done (under S1')

* In `tempered-fundamental-groups` (`Andre/TateObjectDouble.lean`, pinned at `a2415c1`): the object
  `Ÿ` with deck group `ℤ × ℤ/2` acting simply transitively on its fibre, the character
  `Π^tp_X → ℤ × ℤ/2`, `χ_Y = pr₁ ∘ χ_Ÿ`.
* Here: `piYddot` (**`Π^tp_Ÿ`**, `mem_piYddot_iff`: the stabilizer of the base point of `Ÿ`;
  open, normal in `Π^tp_X`), `piYddot_le_piY` (`Π^tp_Ÿ ⊆ Π^tp_Y`), `relIndex_piYddot_le_two`
  (`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`), `relIndex_piYddot_eq_two` (`= 2` if some element of the decomposition
  group of the valuation of the geometric point moves `√(x − e)`).

### (14) Tempered Frobenioid refinements (`Iut/Frobenioid/TateTheta.lean`) — done (partial)

* `unitThetaGrp χ U`, `unitThetaDiv`, `unitThetaData`: `B₀ = U × {theta-monomial divisors}`
  with the units `U` (in [EtTh]: `O_K^×`); `ker_unitThetaDiv`: the kernel of `B₀ → Φ₀^gp` is
  exactly `U` ([EtTh], Def. 3.3); `unitThetaData_isFrobenioid`.
* `tateY_H`, `mem_tateY_H_iff`: the object `Y` of the tempered Frobenioid of the Tate curve has
  subgroup `Π^tp_Y` (6a), the stabilizer of the base point of the fibre of `X₀`.
* Not done: separating the components of `Y_H ×_X Y` (needs verticial subgroups, not provided by
  `tempered-fundamental-groups`) and the cusps.

## Scope decisions

Decisions S1–S3 were made for P16; S1'–S5 for step 2 refine them.

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

* **S1' (tempered coverings).** `Y → X` is the tempered object `TateObject.X₀` of
  `tempered-fundamental-groups` and `Π^tp_Y` is its stabilizer (6). `Ÿ → Y` is constructed (15)
  as `Y ×_X X'` for the Kummer presentation `X' = Spec R[t]/(t² − (x − e))` of the `2`-isogeny
  covering `E_{√q} → E_q` (`e` the `x`-coordinate of the `2`-torsion point `√q`), which is finite
  étale over `Spec R` only if `x − e` is a unit, i.e. if `Spec R` avoids the `2`-torsion point
  `(e, ·)` (e.g. `E ∖ E[2]`); `X = E ∖ {0}` itself would need the coordinate ring of the isogenous
  curve. The model environments use `(Δ_Ÿ)^Θ = Δ_Θ × 2·(Δ_Y)^ell` directly.
* **S2' (the étale theta class).** The class `η^Θ ∈ H¹(Π^tp_Ÿ, Δ_Θ)` stays research-level
  here, for a precise reason: `Θ̈` is not a function on any finite level — it lives on the
  rigid-analytic (formal) covering `Ÿ`, while the coverings of `tempered-fundamental-groups`
  are levels (finite étale `R`-algebras) with projective models and covering spaces of their
  special fibres, without a structure sheaf on infinite coverings; so neither `Θ̈` nor its
  `N`-th root coverings `Ÿ_N` (equivalently the line bundles `L_N` and theta trivializations
  `τ_N` of [EtTh], Lemma 1.2) are available as tempered objects, and no decomposition groups
  of points of tempered coverings are available to restrict to. What is formalized: the
  point/germ restrictions (P16, S2), the restriction of the class to `Δ_Θ` as the reduction
  `red` of the model environment (8d), and its divisor (10c).
* **S3' (environments).** Cyclotomic rigidity is proved for environments on the abelian
  geometric theta quotient `(Δ^tp_Y)^Θ[μ_N]` (8): there the algorithm needs no slimness (the
  cyclotome is the torsion subgroup). For `Π^tp_Y[μ_N]` itself the kernel `μ_N` is recovered by
  Prop. 2.11(ii), formalized for any temp-slim group (7c).
* **S4 (temp-slimness).** Temp-slimness of `Π^tp_X`, `Π^tp_Y` ([Mzk14], Example 3.10) is not
  proved: it rests on the anabelian geometry of tempered groups of hyperbolic curves (the
  verticial subgroups and their commensurable terminality, profinite slimness of `Δ`, and
  center-freeness of `G_K`). `tempered-fundamental-groups` proves the tree-tower part
  (commensurable terminality of verticial subgroups when edge stabilizers have infinite index,
  Blueprint §12) but neither the comparison of verticial subgroups with fundamental groups of
  components nor estrangement for any curve. All statements needing it take `TempSlim` as a
  hypothesis.
* **S5 (tempered Frobenioid monoids).** See `Iut/Frobenioid/README.md`: the base category is
  genuine; the monoids are the combinatorial theta divisors.

## Research-level, not formalized

* **Cyclotomic rigidity** ([EtTh], Cor. 2.19(i)) for `Π^tp_Y[μ_N]` itself (beyond the
  theta-quotient environments of (8)): the first step of the algorithm reconstructs the theta
  quotient `Π^tp_Y ↠ (Π^tp_Y)^Θ` and `Π^tp_Ÿ` from `Π^tp_X` ([EtTh], Cor. 2.18(i), via
  Props. 1.8, 2.4 and [Mzk2], Lemma 1.3.8), i.e. tempered anabelian results (the dual graph and
  the theta quotient are group-theoretic) that are not available; and it needs temp-slimness
  (S4) and `Π^tp_Ÿ` (S1'). Given those, the remaining steps are (7c) and (8).
* **Discrete rigidity for mono-theta environments** (Cor. 2.19(ii)) for the actual
  environments: (9c) reduces it to Cor. 2.18(iv) (`Aut^μ(M_N) ↠ Aut(Π_X)` with kernel
  `Hom(ℤ/2, ℤ/N)`), which needs Cor. 2.18(iii) (`Π_X = Aut(Π_Y) ×_{Out} Im(D)`, temp-slimness)
  and the cyclotomic rigidity above. For the abelian models of the geometric theta quotient the
  analogue of Cor. 2.18(iv) and the resulting Cor. 2.19(ii) are proved in (13).
* **Rigidity of scalar multiples** (Thm. 1.10, Cor. 2.19(iii)): the standard-type classes are
  characterized group-theoretically by their restrictions to the decomposition groups of the
  torsion points labelled `0`. Needs the tempered anabelian rigidity Thm. 1.6 (`Π^tp_X`
  determines the `ℤ`-covering and its labels) and the restriction maps to decomposition groups in
  `H¹(Π^tp)`.
* Tempered anabelian rigidity of the étale theta function (Thm. 1.6), the theta trivializations
  `τ_N` and their compatibility (Lemma 1.2), and the Frobenioid-theoretic manifestations
  (§§3–5).
