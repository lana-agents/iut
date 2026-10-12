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
* `Local/CharCount.lean`: `card_locChar`, `charCount_gal` — `#Hom_cont(G_K, ℤ/n) = N(n)` (left
  and right non-degeneracy of the local duality pairing of P9; `card_monoidHom_zmod_le`).
* `Local/Invariants.lean`: the algorithms `primeOf`, `qOf`, `degOf`, `fOf`, `eOf` on functions
  `ℕ → ℕ` and their correctness (`primeOf_eq`, ...); the group-theoretic algorithms `recPrime`,
  `recQ`, `recDeg`, `recF`, `recE` (`isGroupTheoretic_*`, `*_gal`); and
  **`galEquiv_invariants`**: `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` (`K/ℚ_p`, `K'/ℚ_{p'}`) forces `p = p'`,
  `[K : ℚ_p] = [K' : ℚ_{p'}]`, `q = q'`, `f = f'`, `e = e'`.
* (planned) the inertia subgroup and the Frobenius element ([AbsAnab], 1.2.1 (ii), (iv)):
  `I_K = ⋂ {H open : f(H) = [G_K : H] · f(G_K)}`; the order `p^m` of `μ_{p^∞}(K)`.

### M2 — cyclotomic rigidity ([AbsTopIII], Prop. 3.2 (i), (ii); Cor. 1.10 (i))
* MLF-Galois pairs `G ↷ M`, their cyclotome `μ_Ẑ(M) = Hom(ℚ/ℤ, M)` and Kummer maps; the
  natural isomorphism `H²(G, μ_n(M)) ≃ ℤ/n` (P9 `h2MuEquiv`) and its functoriality.

### M3 — mono-analytic log-shells ([AbsTopIII], Prop. 5.7, 5.8 (ii), (iii))
* The log-shell `𝓘_K = (2p)⁻¹ log(𝒪_Kˣ)` (`Iut.logShell`) and the normalised log-volume
  `−1 − m/f + e · log(p*)/log p` (in units of `f log p`) as functions of the reconstructed
  invariants.

### M4 — cuspidalisation skeleta ([AbsTopI], Lemma 4.5; [AbsTopII], Cor. 3.3;
[AbsTopIII], Thm. 1.9, Cor. 1.10)
* Out-semidirect products: an extension `1 → N → E → Q → 1` with center-free `N` is recovered
  from the outer action `Q → Out(N)` ([AbsTopII], §0; Cor. 3.3 (b)).
* The statements of elliptic and Belyi cuspidalisation with the deep inputs (Grothendieck
  conjecture, Belyi maps, the characterisation of cuspidal decomposition groups) as named
  hypotheses, and the formal parts of the algorithms proved from them.

## Scope decisions
* `p`-adic fields are those of `local-class-field-theory` (`[Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]`, `Ω` algebraically closed and Galois over `K`), so that P8/P9
  apply directly; `local-class-field-theory` is pinned in `lakefile.toml` (same Mathlib and
  `continuous-kummer-theory` revisions as iut).
* `configuration-spaces` (P10), `generalized-albanese` (P11) and `cm-globalization` (P12) are
  not added as dependencies: their outputs enter the cuspidalisation statements only through
  hypotheses on profinite groups (e.g. exactness of Fadell–Neuwirth sequences); see M4.
