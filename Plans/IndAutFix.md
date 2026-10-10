# Fix of the indeterminacy automorphisms (`indAut`)

## Problem

`LocalConstruct.indAut` (Indeterminacy.lean) consisted of the maps `⊗_j σ_j` with `σ_j` field
automorphisms of the factors. IUT IV, Proposition 1.2 lets `φ` be **any** `ℚ_p`-linear
automorphism of the packet that induces an automorphism of the lattice
`log_p(R_I^×) = ⊗_{ℤ_p} log_p(R_i^×)`; the field automorphisms are a small subset (part of
(Ind1)). With the narrow class every `φ` preserves absolute values, so the theta-pilot region
`⋃_φ φ(q^{j²}·(R_I)^∼)` collapsed to `q^{j²}·(R_I)^∼`, the right-hand side of the variant had the
closed form `((ℓ+5)/4)·log π − (ℓ(ℓ+1)/12)·|log q|`, and `Cor312VariantHolds` became an absolute
bound on `log q`, refuted by the project's own Θ-data of large height.

## The fix

* Nonarchimedean: `indAut (.finite p) c := {φ | ∃ e : Tensor ≃ₗ[ℚ_p] Tensor, ⇑e = φ ∧
  e '' tensorLogShell p c = tensorLogShell p c}`. Since `tensorLogShell = ⊗_{ℤ_p} 𝓘_i` and
  `𝓘_i = (2p)⁻¹·log_p(R_i^×)`, preserving it is the same as preserving `log_p(R_I^×)`.
* Archimedean: the maps induced by the primitive automorphisms of IUT IV, Proposition 1.5
  (complex conjugation and multiplication by `±1`, `±√−1` on each factor). These preserve `B_I`,
  so the archimedean region is unchanged.
* `RHSData.thetaPilot_le_shell` is removed: the corrected region need not lie in the packet
  log-shell at wildly ramified primes (IUT IV, Step (v), uses a larger container).

## Work packages

1. **Statement side**: new `indAut`; admissibility of `⋃_φ φ(S)` (it lies in `p^{-k}·L`, compact);
   finite support (`(R_I)^∼ = R_I` at odd unramified primes, from 4 with `d_i = 0`);
   `thetaComponent_eq_integral` for `p` odd, unramified, not bad.
2. **Prop 1.2(i)** (`LogLattice.lean`): for `K_w/ℚ_p` with ramification `e`,
   `(2p)⁻¹·p^{a}·O ⊆ 𝓘` and `𝓘 ⊆ (2p)⁻¹·p^{-b}·O`, with Mochizuki's `a`, `b`, and
   `(a + b)·log p ≤ 3 + log e` when `p − 2 < e`, `a + b ≤ 0` otherwise.
3. **Integrality** (`TensorIntegral.lean`): `∏_i incl_i(y_i) ∈ (R_I)^∼` when `∑ ord_p y_i ≥ 0`.
4. **Prop 1.1** (`Different.lean`): elements `δ_i ∈ K_{w_i}` with `ord_p δ_i ≤ d_i`
   (`differentExponent`) and `(∏ incl δ_i)·(R_I)^∼ ⊆ R_I`, via the trace-dual basis of `𝓞_K`
   (which lies in `𝔡_{K/ℚ}^{-1}`) projected to the completions.
5. **Volume of elementary scalings** (`ScaleVolume.lean`):
   `μ^log((∏ incl y_i)·(R_I)^∼) = −(∑ ord_p y_i)·log p`.
6. **Assembly**: `prop14iii_of_isOver` for the new `indAut` (Prop 1.2(ii) chain), `prop14_iv` for
   odd unramified `p`, `prop15` for the primitive automorphisms, `LocalEstimate`, Solution,
   audits, docs.
