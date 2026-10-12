# Absolute anabelian reconstruction (`Iut/Reconstruction/`, roadmap P17)

Group-theoretic reconstruction results of Mochizuki's *Topics in Absolute Anabelian Geometry*
I–III (cited **[AbsTopI]**, **[AbsTopII]**, **[AbsTopIII]**; texts in `~/iut-scratch/abstop/`),
as used by IUT I–III. Roadmap row P17 of the LANA "wall" roadmap.

**Status of the dependency.** No module of `Iut/Reconstruction/` is imported by the comparator
challenge (`Comparator/Challenge.lean`), by `Iut/Concrete/*` or by the wall. Deep inputs that
are not formalised (the Grothendieck conjecture for hyperbolic curves over sub-`p`-adic fields,
the existence of Belyi maps with prescribed ramification, ...) enter only as explicit
hypotheses (structures whose fields are the needed statements), never as global assumptions.

## What "group-theoretic" means here

A field invariant `ι(K)` of a `p`-adic field `K` (with algebraic closure `Ω`) is
*reconstructed group-theoretically* if there is a function `F` of **topological groups** that
is invariant under isomorphisms of topological groups (`≃ₜ*`) with `F(Gal(Ω/K)) = ι(K)`. The
formal consequence used in IUT is the *invariance statement*: every isomorphism of topological
groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` forces `ι(K) = ι(K')` — even between fields over different
`ℚ_p` (which is how [AbsTopIII], Proposition 5.8 (i) / [AbsAnab], Proposition 1.2.1 are applied
in IUT I, Remark 1.9.2, and IUT III, Proposition 1.2).

The basic group-theoretic quantity is the number of continuous characters
`charCount G n = #{χ : G →* ℤ/n continuous}`. By local Tate duality (roadmap P9,
`PadicField.pairing` of `local-class-field-theory`) `charCount (Gal(Ω/K)) n = [Kˣ : (Kˣ)ⁿ]`,
and the arithmetic of `𝒪_Kˣ` turns the function `n ↦ [Kˣ : (Kˣ)ⁿ]` into `p`, `q = p^f`,
`[K : ℚ_p]` and `e`.

## Milestones

### M0 — framework (`GroupTheoretic.lean`)
* `charCount G n`, `charCount_congr` (invariance under `≃ₜ*`).

### M1 — local invariants ([AbsTopIII], Prop. 5.8 (i); [AbsAnab], Prop. 1.2.1 (i)) — done
* `Local/UnitIndex.lean`: for `K/ℚ_p` finite, `N(n) = [Kˣ : (Kˣ)ⁿ]` (`powIndex Kˣ n`):
  * `powIndex_units_eq` : `N(n) = n · [𝒪ˣ : (𝒪ˣ)ⁿ]` (valuation sequence);
  * `powIndex_integers_of_coprime`, `powIndex_of_coprime` : `[𝒪ˣ : (𝒪ˣ)ⁿ] = gcd(q − 1, n)` and
    `N(n) = n · gcd(q − 1, n)` for `p ∤ n` (Hensel + cyclicity of `𝓴ˣ`);
  * `powIndex_p_pow_le` : `[𝒪ˣ : (𝒪ˣ)^{p^k}] ≤ q^{(k+1)e+1}` (iterated Hensel in root form,
    `exists_pow_p_pow_eq`: `1 + p^{k+1}ϖw` is a `p^k`-th power);
  * `le_powIndex_p_pow` : `q^{m(k)} ≤ (q − 1) q [𝒪ˣ : (𝒪ˣ)^{p^k}]` with `m(k+1) = m(k) +
    min(e, m(k))` (`(1 + 𝔪^j)^p ⊆ 1 + 𝔪^{j + min(e, j)}`), `e(k+1) ≤ m(k) + e²`;
  * auxiliary: `v_natCast_p_eq` (`v_K(p) = e`), `q_eq_p_pow_f`, `q_pow_e` (`q^e = p^{[K:ℚ_p]}`),
    the filtration `unitFilt` with `q^m ≤ [𝒪ˣ : U^(m)] · q` and `[𝒪ˣ : U^(m)] ≤ q^m`.
* `Local/PowerIndex.lean`: exact `p`-power indices — `v_one_add_pow_p_sub_one`
  (`v((1+x)^p − 1) = v(x) + e` for `v(x) ≥ e + 1`), `eq_one_of_pow_p_pow_eq_one` (`U^(e+1)` has
  no `p`-torsion), `unitFilt_le_map_pow` (`(U^(e+1))^{p^k} = U^(e+1+ke)`), `index_unitFilt_eq`
  (`[𝒪ˣ : U^(m)] = q^m − q^{m−1}`), **`powIndex_p_pow`**:
  `[Kˣ : (Kˣ)^{p^k}] = #μ_{p^k}(K) · p^{k([K:ℚ_p]+1)}` (`muCard p K k = #μ_{p^k}(K)`).
* `Local/CharCount.lean`: `card_locChar`, `charCount_gal` — `#Hom_cont(G_K, ℤ/n) = N(n)` (left
  and right non-degeneracy of the local duality pairing of P9; `card_monoidHom_zmod_le`).
* `Local/Invariants.lean`: the algorithms `primeOf`, `qOf`, `degOf`, `fOf`, `eOf` on functions
  `ℕ → ℕ` and their correctness (`primeOf_eq`, ...); the group-theoretic algorithms `recPrime`,
  `recQ`, `recDeg`, `recF`, `recE` (`isGroupTheoretic_*`, `*_gal`); and
  **`galEquiv_invariants`**: `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` (`K/ℚ_p`, `K'/ℚ_{p'}`) forces `p = p'`,
  `[K : ℚ_p] = [K' : ℚ_{p'}]`, `q = q'`, `f = f'`, `e = e'`; `recMu`, `galEquiv_muCard`: the
  numbers `#μ_{p^k}(K)` (hence `p^m = #μ_{p^∞}(K)`) are group-theoretic.
* `Local/Inertia.lean` ([AbsAnab], Prop. 1.2.1 (ii)) — done: `fixingSubgroupContEquiv`
  (`Gal(Ω/L) ⊆ Gal(Ω/K)` with the subspace topology `≃ₜ*` `Gal(Ω/L)`), `recF_fixingSubgroup`,
  `unrOpen_iff` (`recF(Gal(Ω/L)) = [L:K] recF(G_K)` iff `L/K` unramified), `recInertia G =
  ⋂ {H open | recF(H) = [G:H] recF(G)}`, `map_recInertia` (group-theoretic), `recInertia_gal`
  (`= PadicField.absInertia p K Ω`, the genuine inertia group) and **`galEquiv_inertia`**:
  every `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` maps `I_K` onto `I_{K'}`.
* `Local/Frobenius.lean` ([AbsAnab], Prop. 1.2.1 (iv)) — done: **the Frobenius is
  group-theoretic**. `IsFrobLift G φ`: `φ` acts on every continuous character
  `χ : recInertia G → ℤ/n` with `recPrime G ∤ n` by `χ(φ τ φ⁻¹) = recQ G · χ(τ)` (tame inertia
  `I/P ≅ ∏_{ℓ≠p} ℤ_ℓ(1)` with Frobenius acting by `q`). `IsFrobLift.map` (invariance),
  **`isFrobLift_gal_iff`** (for `G = Gal(Ω/K)`: `IsFrobLift G σ ↔ σ ≡ Frob mod I_K`),
  `galEquiv_arithFrob`. Proof: `tameChar_conj` (finite level: `θ(σ τ σ⁻¹) = θ(τ)^q` for the tame
  character `θ` of `local-class-field-theory`) and `char_conj_of_frob` (a continuous character
  factors through a finite Galois level, where the wild inertia `ker θ` is a `p`-group); for
  the converse the tame Kummer character `kummerChar : I_K → μ_{q^m-1}`, `τ ↦ τ(α)/α`
  (`α^{q^m-1} = π_K`), is onto (`kummerChar_surjective`, via `v(π_K) = 1` in the unramified
  `K_k`) and satisfies `θ(σ τ σ⁻¹) = σ(θ(τ))` (`kummerRatio_conj`), so a solution acts on
  `μ_{q^m-1}` by `ζ ↦ ζ^q` for all `m`, i.e. as Frobenius on `K^ur` (`mk_eq_arithFrob_of_frobCond`).
  The **Weil group** `recWeil G = ⟨Frobenius lifts, recInertia G⟩` (`map_recWeil`;
  `mem_recWeil_gal_iff`: the preimage of `Frob^ℤ`).
* `Local/Abelianization.lean` ([AbsAnab], 1.2.1 (iv)–(v); [AbsTopIII], Prop. 5.8 (i)) — done:
  `closure_commutator_eq` (`closure [G_K, G_K] = Gal(Ω/K^ab)`; `fixedField_commutator_le`),
  **`galAbEquiv : G_K^ab ≃ₜ* Gal(K^ab/K)`** (Mathlib's `TopologicalAbelianization`);
  `abUnits G`, `abWeil G` (images of `recInertia`, `recWeil` in `G^ab`; `map_abUnits`,
  `map_abWeil`: group-theoretic); `map_abUnits_gal` (`= Gal(K^ab/K^ur) = artin(𝒪ˣ)`),
  `map_abWeil_gal` (`= artin(Kˣ)`); `unitsAbEquiv : 𝒪_Kˣ ≃* abUnits G_K`,
  `multAbEquiv : Kˣ ≃* abWeil G_K` (compatible with the Artin map); **`galEquiv_multEquiv`**:
  `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` induces `Kˣ ≃* K'ˣ` mapping `𝒪_Kˣ` onto `𝒪_{K'}ˣ`
  (`galEquiv_multEquiv_units`).

### M2 — cyclotomic rigidity ([AbsTopIII], Prop. 3.2 (i); Cor. 1.10 (i), (c)) — done
* `Local/Cyclotome.lean`: every endomorphism of `μ_n` is a power map and `G_K`-equivariant
  (`exists_pow_eq`, `map_smul_mu`); the induced map `coeffMap α` on `H²(G_K, μ_n)` is
  `β ↦ β^a` (`coeffMap_zpow`), so it multiplies the invariant `H²(G_K, μ_n) ≃ ℤ/n` (P9
  `h2MuEquiv`) by `a` (`h2MuEquiv_coeffMap`); **`cyclotomic_rigidity`**: an endomorphism of
  the cyclotome compatible with `H²(G_K, μ_n) ≃ ℤ/n` is the identity.
* `Local/Torsion.lean` (M2b) — done: `eq_one_of_pow_eq_one_unr` (`Gal(K^ur/K)` is
  torsion-free), `exists_artin_eq_of_pow_eq_one`, **`torsAbEquiv : μ(K) ≃* (G_K^ab)_tors`** and
  `torsAbEquivFixing : μ(L) ≃* (H^ab)_tors` for the open subgroups `H = Gal(Ω/L) ⊆ G_K`
  (the building blocks of `μ_{ℚ/ℤ}(G) = lim_→ (H^ab)_tors`), `map_torsion_abEquiv`; **Kummer
  rigidity** (monoid form of Prop. 3.2): `kummer_rigidity` — a power automorphism `ζ ↦ ζ^a` of
  `μ_n` whose induced map on `H¹(G_K, μ_n)` fixes the Kummer class of a uniformiser is the
  identity.
* Not done: the direct limit `μ_{ℚ/ℤ}(G) = lim_→ (H^ab)_tors` itself — its transition maps are
  the transfers `G_K^ab → G_L^ab`, which correspond to `Kˣ ⊆ Lˣ` under the Artin maps; this
  transfer property is not in `local-class-field-theory`.

### M3 — mono-analytic log-shells ([AbsTopIII], Prop. 5.8 (iii)) — normalisation done
* `Local/LogShell.lean`: `exists_muCard_eq_pow`, `muCard_le` (`#μ_{p^k}(K)` is a power of
  `p`, `≤ q^{e+1}`), `muPInf`, `mExp` (`#μ_{p^∞}(K) = p^m`, `muPInf_eq_pow`), `recMExp_gal`;
  `pStar`, `logShellConst p f e m = −1 − m/f + e log(p*)/log p`, `logShellConst_mul` (the
  volume formula `vol(𝓘_K) = p^{−(f+m)} (p*)^{[K:ℚ_p]}` it encodes) and
  **`recLogShellConst_gal`** / `isGroupTheoretic_recLogShellConst`.
* `Local/MonoAnalytic.lean` (M3b, [AbsTopIII], Prop. 5.8 (ii)) — done: `unitsQ G =
  ℚ ⊗[ℤ] 𝒪^×(G)` (`𝒪^×(G) = abUnits G`), **`monoLogShell G = (p*)⁻¹ · image(𝒪^×(G))`**
  (`p = recPrime G`), `map_monoLogShell` (group-theoretic), `image_monoLogShell_gal`
  (`𝓘(G_K) = {(p*)⁻¹ ⊗ u | u ∈ 𝒪_Kˣ}` under `ℚ ⊗ 𝒪_Kˣ ≅ ℚ ⊗ 𝒪^×(G_K)`).
* `Local/LogVolume.lean` (M3c, [AbsTopIII], Prop. 5.7 (i) (c), 5.8 (iii)) — done, in the
  valued-field framework of `Iut.logShell` (`Iut/Concrete/LocalConstruct/LocalLogShell.lean`;
  `k` complete, discretely valued, characteristic `0`, `‖p‖ < 1`, proper): `principalUnits`
  (`U = U^(1)`), `deepUnits` (`D = {‖u − 1‖ ≤ ‖2p‖}`), `logHom`, `logKer` (`T = ker log|_U`);
  `log` is injective on `D` and maps it onto `B = {‖y‖ ≤ ‖2p‖}` (`comap_logHom_ball`:
  `log⁻¹(B) = D·T`, `disjoint_deepUnits_logKer`), so `[U : D] = [log U : B] · #T`
  (`index_deepUnits_eq`); `measure_eq_relIndex_mul` (`μ(H) = [H : H'] μ(H')` for open subgroups)
  and **`card_mul_measure_logShell`**: `#T · μ(𝓘_k) = [U : D] · μ(𝒪_k)` for every
  translation-invariant measure `μ` — the normalisation `μ(𝒪) = 1` of `Iut/Concrete`'s
  `componentVol` gives `μ(𝓘_k) = [U : D]/#T`.
* For `k/ℚ_p` finite the two numbers are `[U : D] = q^{v(2p) − 1}` (`relIndex_unitFilt`, with
  `q^{v(2p)} = (p*)^d` by `q_pow_e`) and `#T = p^m` (`muPInf_eq_pow`), so
  `μ(𝓘_k)/μ(𝒪_k) = p^{−(f+m)} (p*)^d`, the volume encoded by `logShellConst`
  (`logShellConst_mul`). Not done: the formal transfer of these `local-class-field-theory`
  computations to the valued fields of `Iut/Concrete` (a comparison of the two norms), and the
  identification of `ℚ ⊗ 𝒪_Kˣ` with `K` through `log` (which would identify `monoLogShell` with
  `Iut.logShell`).

### M4 — cuspidalisation skeleta ([AbsTopII], Cor. 3.3; [AbsTopIII], Thm. 1.9)
* `Cusp/OutSemidirect.lean` (done): `inn`, `Out`, `outSemidirect ρ = Aut(N) ×_{Out(N)} Q`,
  `outerAction`, **`extensionEquivOutSemidirect`**: an extension `1 → H → E → E/H → 1` with
  center-free `H` is recovered from its outer action ([AbsTopII], §0).
* `Cusp/Elliptic.lean` (done) — [AbsTopII], Cor. 3.3 (iii): `fibreSubgroup` and
  `fibreSubgroup_surjective` (step (a′): `Π_{U_V} ↠ Π_V` as a fibre product),
  `quotientComapEquiv` (`Π_{U_X}/Π_{U_V} ≃ Π/Π_V`), **`cuspidalizationEquiv'`** (step (b):
  `Π_{U_X} ≃ Π_{U_V} ⋊^out (Π/Π_V)` compatibly with the projections, for center-free
  `Π_{U_V}`). Step (a) (chains and the relative Grothendieck conjecture) is a deep input.
* `Cusp/Belyi.lean` (done) — [AbsTopIII], Thm. 1.9 (a), step "filling in cusps":
  `CuspData` (a group with cuspidal inertia subgroups), `CuspData.kernel`, `Filled`,
  `fillMap` (`Π_U ↠ Π_Y`), `mk_inertia`, and the functoriality `CuspData.Iso`, `map_kernel`,
  `filledEquiv`, `filledEquiv_fillMap`. The existence of Belyi maps and the
  Grothendieck-conjecture characterisation of the resulting open immersions into the tripod
  group are deep inputs (the cusp data are given).
* Not done: [AbsTopI], Lemma 4.5 (the characterisation of cuspidal decomposition groups via
  weights and quasi-trivial ranks — needs `ℓ`-adic Galois representations of curves); the
  remaining steps (b)–(e) of [AbsTopIII], Thm. 1.9 (Kummer classes of functions, additive
  structure on `k_NF`); Cor. 1.10 (ii), (iii).

## Scope decisions
* `p`-adic fields are those of `local-class-field-theory` (`[Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]`, `Ω` algebraically closed and Galois over `K`), so that P8/P9
  apply directly; `local-class-field-theory` is pinned in `lakefile.toml` (same Mathlib and
  `continuous-kummer-theory` revisions as iut).
* `configuration-spaces` (P10), `generalized-albanese` (P11) and `cm-globalization` (P12) are
  not added as dependencies: their outputs enter the cuspidalisation statements only through
  hypotheses on profinite groups (e.g. exactness of Fadell–Neuwirth sequences); see M4.
