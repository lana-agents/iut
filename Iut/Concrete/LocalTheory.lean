/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.Statement

/-!
# The local-field theory consumed by the concrete large volume container (taxis #4, #278)

The concrete instantiation of the right-hand side of the Corollary 3.12 variant over the
`ℓ`-torsion field `K` needs, for each rational place `v_ℚ` and each tuple `(v_j)_{j ∈ S}`
of places of `K` over `v_ℚ`, the tensor packet

`⊗_{j ∈ S} K_{v_j}` (over `ℚ_p`, resp. over `ℝ`),

a finite product of local fields (IUT III, Proposition 3.1), with its integral structure
`(R_I)^∼` (resp. the product of unit balls `B_I`), the tensor product of the log-shells,
the normalized Haar log-volume, the holomorphic hull, and the estimates of IUT IV,
Propositions 1.4 and 1.5. All of this is standard local-field theory that Mathlib does
not yet contain; it is delegated to `lana-agents/padic-log-volume` (taxis #4, #278) as
the single structure `Iut.LocalTheory K`, whose fields are the precise target statements.

The quantities that Mathlib *can* express are defined here concretely, not delegated:
the ramification index `e_w`, the residue degree `f_w`, the local degree
`[K_w : ℚ_p] = e_w f_w`, the normalized weights `[K_w : ℚ_p]/[K : ℚ]`, and the valuation
`ord_p` normalized by `ord_p(p) = 1` on each completion (from the norm of the adic
completion, which is normalized by `‖π_w‖ = (#𝓞_K/𝔭_w)⁻¹`).

## The indeterminacies

The theta-pilot region of the concrete variant is the union, over the automorphisms `φ`
of IUT IV, Proposition 1.2 — the concrete rendering of the indeterminacies (Ind1), (Ind2)
of IUT III, Theorem 3.11 — of the scaled integral structures `φ(q^{j²/2ℓ}·(R_I)^∼)`
(Step (v) of the proof of Theorem 1.10). The class `indAut` of these automorphisms is a
field of the local theory, together with the two statements about it that Theorem 1.10
uses: Proposition 1.4(iii),(iv) (the containment of `φ(p^λ·(R_I)^∼)` in an explicit hull
region, with the log-volume bound) and Proposition 1.5(iii),(iv) (the archimedean
container `π^{|I|}·B_I`).
-/

namespace Iut

universe u v

open NumberField IsDedekindDomain
open scoped Pointwise

variable (K : Type u) [Field K] [NumberField K]

/-- The completion `K_w` of `K` at a finite place. -/
noncomputable abbrev completionAt (w : FinitePlace K) : Type u :=
  w.maximalIdeal.adicCompletion K

/-- The ramification index `e_w` of the finite place `w` over its residue
characteristic. -/
noncomputable def ramIdx (w : FinitePlace K) : ℕ :=
  Ideal.ramificationIdx w.maximalIdeal.asIdeal ℤ

/-- The residue degree `f_w` of the finite place `w` over its residue characteristic. -/
noncomputable def inertDeg (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

/-- The local degree `[K_w : ℚ_p] = e_w · f_w`. -/
noncomputable def localDeg (w : FinitePlace K) : ℕ := ramIdx K w * inertDeg K w

/-- The normalized weight `[K_w : ℚ_p]/[K : ℚ]` of a finite place
(IUT III, Remark 3.1.1). -/
noncomputable def placeWeight (w : FinitePlace K) : ℝ :=
  (localDeg K w : ℝ) / Module.finrank ℚ K

/-- The normalized weight `[K_w : ℝ]/[K : ℚ]` of an infinite place (`mult w ∈ {1, 2}`). -/
noncomputable def infPlaceWeight (w : InfinitePlace K) : ℝ :=
  (w.mult : ℝ) / Module.finrank ℚ K

/-- The valuation `ord_p` on `K_w`, normalized by `ord_p(p) = 1`: since the norm of the
adic completion satisfies `‖p‖ = p^{−[K_w : ℚ_p]}`, `ord_p(x) = −log‖x‖/([K_w : ℚ_p]·log p)`. -/
noncomputable def ordp (w : FinitePlace K) (x : completionAt K w) : ℝ :=
  -Real.log ‖x‖ / (localDeg K w * Real.log (residueChar w))

/-- The ramification index of a place of `K` over its rational place (`1` at infinite
places, by convention). -/
noncomputable def ramIdxAt : Place K → ℕ
  | .finite w => ramIdx K w
  | .infinite _ => 1

open scoped Classical in
/-- The exponent `ord_𝔭(𝔡_{K/ℚ})` of the different ideal of `K` at the finite place `w`. -/
noncomputable def ordDifferent (w : FinitePlace K) : ℕ :=
  Multiset.count w.maximalIdeal.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K)))

/-- The **different exponent** `d_w` of `K_w` over `ℚ_p` in the normalization
`ord_p(p) = 1`: `d_w = ord_𝔭(𝔡_{K/ℚ})/e_w` (the local different at `w` is the
completion of the global one; IUT IV, Proposition 1.3). -/
noncomputable def differentExponent (w : FinitePlace K) : ℝ :=
  (ordDifferent K w : ℝ) / ramIdx K w

/-- The **tensor packets** `⊗_j K_{c j}` as topological commutative rings, indexed by a
rational place `v_ℚ` and a finite family `c` of places of `K` (meaningful when every
`c j` lies over `v_ℚ`; junk otherwise). Separated from `LocalTheory` so that the ring
structure is available as an instance for the statements about them. -/
structure LocalTensor where
  /-- The **tensor packet** `⊗_{j} K_{c j}` over `ℚ_p` (resp. `ℝ`), presented as a
  topological commutative ring (a finite product of local fields). -/
  Tensor : ∀ {ι : Type} [Fintype ι], RationalPlace → (ι → Place K) → Type v
  /-- Ring structure. -/
  [ring : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    CommRing (Tensor vQ c)]
  /-- Topology. -/
  [top : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    TopologicalSpace (Tensor vQ c)]
  /-- The archimedean packets are `ℝ`-algebras. -/
  [algR : ∀ {ι : Type} [Fintype ι] (c : ι → Place K), Algebra ℝ (Tensor .infinite c)]

attribute [instance] LocalTensor.ring LocalTensor.top LocalTensor.algR

/-- **The local-field theory of the tensor packets** over the number field `K`: the
standard-mathematics input of the concrete large volume container (taxis #4, #278).
Every field is a target statement for `lana-agents/padic-log-volume`; see the module
docstring. -/
structure LocalTheory extends LocalTensor.{u, v} K where
  /-- Residue characteristics of finite places are prime. -/
  residueChar_prime : ∀ w : FinitePlace K, (residueChar w).Prime
  /-- Finitely many finite places over each prime. -/
  fiber_finite : ∀ p : ℕ, Finite {w : FinitePlace K // residueChar w = p}
  /-- Only finitely many finite places are ramified over `ℚ`. -/
  ramified_finite : {w : FinitePlace K | ramIdx K w ≠ 1}.Finite
  /-- Local degrees are positive. -/
  localDeg_pos : ∀ w, 0 < localDeg K w
  /-- Ramification indices are positive. -/
  ramIdx_pos : ∀ w, 0 < ramIdx K w
  /-- The different exponent vanishes at unramified places (`𝔭 ∤ 𝔡_{K/ℚ}` iff `𝔭` is
  unramified). -/
  ordDifferent_eq_zero : ∀ w, ramIdx K w = 1 → ordDifferent K w = 0
  /-- `∑_{w ∣ p} [K_w : ℚ_p] = [K : ℚ]` (`Ideal.sum_ramification_inertia`). -/
  sum_localDeg : ∀ p : ℕ, p.Prime → ∀ [Fintype {w : FinitePlace K // residueChar w = p}],
    ∑ w : {w : FinitePlace K // residueChar w = p}, localDeg K w.1 = Module.finrank ℚ K
  /-- `∑_{w ∣ ∞} [K_w : ℝ] = [K : ℚ]` (`NumberField.InfinitePlace.sum_mult_eq`). -/
  sum_mult : ∑ w : InfinitePlace K, w.mult = Module.finrank ℚ K
  /-- `ord_p(p) = 1`. -/
  ordp_p : ∀ w : FinitePlace K, ordp K w (algebraMap K _ (residueChar w : K)) = 1
  /-- `ord_p` is multiplicative. -/
  ordp_mul : ∀ w (x y : completionAt K w), x ≠ 0 → y ≠ 0 →
    ordp K w (x * y) = ordp K w x + ordp K w y
  /-- The inclusion of the `j`-th tensor factor at a nonarchimedean place. -/
  incl : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) (j : ι)
    (w : FinitePlace K), c j = Place.finite w → completionAt K w →+* Tensor (.finite p) c
  /-- Units of a factor are units of the packet. -/
  isUnit_incl : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) (j : ι)
    (w : FinitePlace K) (h : c j = Place.finite w) (x : completionAt K w), x ≠ 0 →
    IsUnit (incl p c j w h x)
  /-- The **integral structure**: `(R_I)^∼`, the ring of integers of the product of local
  fields, at nonarchimedean places (IUT IV, Proposition 1.2); the product of unit balls
  `B_I` at the archimedean place (Proposition 1.5(iii)). -/
  integral : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    Set (Tensor vQ c)
  /-- `1 ∈ (R_I)^∼`. -/
  one_mem_integral : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    (1 : Tensor vQ c) ∈ integral vQ c
  /-- Scaling by an element of nonnegative `ord_p` shrinks the integral structure. -/
  smul_integral_subset : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) (j : ι)
    (w : FinitePlace K) (h : c j = Place.finite w) (x : completionAt K w), x ≠ 0 →
    0 ≤ ordp K w x → incl p c j w h x • integral (.finite p) c ⊆ integral (.finite p) c
  /-- The **tensor product of the log-shells** `⊗_j 𝓘_{c j}` (IUT III, Proposition 3.2). -/
  logShell : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    Set (Tensor vQ c)
  /-- Log-shells are relatively compact. -/
  logShell_relCompact : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    IsCompact (closure (logShell vQ c))
  /-- At nonarchimedean places the log-shell contains the integral structure
  (IUT III, Proposition 1.2). -/
  integral_subset_logShell : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    integral (.finite p) c ⊆ logShell (.finite p) c
  /-- At an odd prime unramified in every factor the log-shell is the integral structure
  (IUT I, Definition 5.4.5; IUT IV, Proposition 1.4(iv)). -/
  logShell_eq_integral : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    Odd (p : ℕ) → (∀ j w, c j = Place.finite w → ramIdx K w = 1) →
    logShell (.finite p) c = integral (.finite p) c
  /-- The **normalized Haar log-volume** on regions of a packet (IUT IV,
  Proposition 1.4(i); IUT III, Proposition 3.9). -/
  componentVol : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    Set (Tensor vQ c) → ℝ
  /-- `μ^log((R_I)^∼) = 0`. -/
  componentVol_integral : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    componentVol vQ c (integral vQ c) = 0
  /-- Monotonicity of the log-volume between hull regions `a·O ⊆ b·O` (`a`, `b` units). -/
  componentVol_mono : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)
    (a b : Tensor vQ c), IsUnit a → IsUnit b → a • integral vQ c ⊆ b • integral vQ c →
    componentVol vQ c (a • integral vQ c) ≤ componentVol vQ c (b • integral vQ c)
  /-- Archimedean radial scaling: `μ^log(t·B_I) = log t` for real `t > 0`
  (Proposition 1.5(iii) with the normalization `μ^log(B_I) = 0`). -/
  componentVol_arch_scale : ∀ {ι : Type} [Fintype ι] (c : ι → Place K) (t : ℝ), 0 < t →
    componentVol .infinite c (algebraMap ℝ (Tensor .infinite c) t • integral .infinite c) =
      Real.log t
  /-- The **admissible class** of the holomorphic hull (IUT III, Remark 3.9.5(i)):
  nonempty relatively compact regions of finite nonzero log-volume. -/
  admissible : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    Set (Set (Tensor vQ c))
  /-- Admissible regions are nonempty. -/
  admissible_nonempty : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)
    (U : Set (Tensor vQ c)), U ∈ admissible vQ c → U.Nonempty
  /-- Admissible regions are relatively compact. -/
  admissible_relCompact : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)
    (U : Set (Tensor vQ c)), U ∈ admissible vQ c → IsCompact (closure U)
  /-- The integral structure is admissible. -/
  integral_admissible : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    integral vQ c ∈ admissible vQ c
  /-- Scaled integral structures are admissible. -/
  smul_integral_admissible : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → Place K) (a : Tensor vQ c), IsUnit a → a • integral vQ c ∈ admissible vQ c
  /-- `μ^log(p⁻¹·U) = μ^log(U) + log p`, for admissible regions `U` (nonempty, relatively
  compact, of finite nonzero Haar measure) of a packet all of whose places lie over `p`
  (IUT III, Proposition 3.9(i)). The restriction to admissible regions is essential: the
  identity is false for `U = ∅` (it would give `log p = 0`) and, with a real-valued
  log-volume, for regions of zero or infinite measure. -/
  componentVol_prime_preimage : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    (∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p) →
    ∀ U ∈ admissible (.finite p) c,
    componentVol (.finite p) c ((fun x => ((p : ℕ) : Tensor (.finite p) c) * x) ⁻¹' U) =
      componentVol (.finite p) c U + Real.log p
  /-- **Existence of least hull regions at a prime** (IUT III, Remark 3.9.5(i)): every
  admissible region of a nonarchimedean packet is contained in a least region `a·(R_I)^∼`
  with `a` a unit, least among all such regions. -/
  exists_leastHull : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
    (U : Set (Tensor (.finite p) c)), U ∈ admissible (.finite p) c →
    ∃ a : Tensor (.finite p) c, IsUnit a ∧ U ⊆ a • integral (.finite p) c ∧
      ∀ b : Tensor (.finite p) c, IsUnit b → U ⊆ b • integral (.finite p) c →
        a • integral (.finite p) c ⊆ b • integral (.finite p) c
  /-- **Existence of least hull regions at the archimedean place** (IUT III,
  Remark 3.9.5(i); IUT IV, Proposition 1.5(iii)): every admissible region of an
  archimedean packet is contained in a least real radial scaling `t·B_I` (`t > 0`) of the
  product of unit balls. The hull regions at `∞` are the radial scalings only: among
  arbitrary units `b` of the packet a least `b·B_I` containing a given region need not
  exist. -/
  exists_leastHull_infinite : ∀ {ι : Type} [Fintype ι] (c : ι → Place K)
    (U : Set (Tensor .infinite c)), U ∈ admissible .infinite c →
    ∃ t : ℝ, 0 < t ∧ U ⊆ algebraMap ℝ (Tensor .infinite c) t • integral .infinite c ∧
      ∀ t' : ℝ, 0 < t' → U ⊆ algebraMap ℝ (Tensor .infinite c) t' • integral .infinite c →
        t ≤ t'
  /-- The radial scalings of `B_I` are monotone: `t·B_I ⊆ t'·B_I` for `0 < t ≤ t'`. -/
  smul_integral_infinite_mono : ∀ {ι : Type} [Fintype ι] (c : ι → Place K) (t t' : ℝ),
    0 < t → t ≤ t' →
    algebraMap ℝ (Tensor .infinite c) t • integral .infinite c ⊆
      algebraMap ℝ (Tensor .infinite c) t' • integral .infinite c
  /-- The **indeterminacy automorphisms** `φ` of IUT IV, Proposition 1.2: the
  automorphisms of the packet through which the indeterminacies (Ind1), (Ind2) act. -/
  indAut : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    Set (Tensor vQ c → Tensor vQ c)
  /-- The identity is an indeterminacy automorphism. -/
  id_mem_indAut : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    id ∈ indAut vQ c
  /-- Indeterminacy automorphisms preserve the log-shell (IUT IV, Proposition 1.2). -/
  indAut_logShell : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)
    (φ : Tensor vQ c → Tensor vQ c), φ ∈ indAut vQ c → φ '' logShell vQ c ⊆ logShell vQ c
  /-- The union of the images of a scaled integral structure under the indeterminacy
  automorphisms is admissible for the hull. -/
  theta_admissible : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)
    (s : Tensor vQ c), IsUnit s →
    (⋃ φ ∈ indAut vQ c, φ '' (s • integral vQ c)) ∈ admissible vQ c
  /-- The union of the images of the log-shell under the indeterminacy automorphisms is
  admissible for the hull. -/
  thetaShell_admissible : ∀ {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K),
    (⋃ φ ∈ indAut vQ c, φ '' logShell vQ c) ∈ admissible vQ c
  /-- **IUT IV, Proposition 1.4(iii)**: for a scaling element `x` of the `j`-th factor
  with `ord_p(x) = λ ≥ 0`, the images `φ(x·(R_I)^∼)` under all indeterminacy
  automorphisms lie in a hull region `a·(R_I)^∼` whose log-volume is at most
  `(−λ + d_I + 1)·log p + ∑_{i ∈ I*} (3 + log e_i)`, where `d_I = ∑_i d_i` is the sum of
  the different exponents (`d_i = ord_p` of a generator of the different of `K_{c i}`
  over `ℚ_p`), `e_i` the ramification indices, and `I* = {i | p − 2 < e_i}`. The
  different exponent is passed in as the function `d`. Stated, like
  `componentVol_prime_preimage`, for packets all of whose places lie over `p`: for a
  packet with a place not over `p` (the zero ring in the concrete construction) the
  log-volume is identically `0` while the bound is negative for `ord_p(x)` large. -/
  prop14_iii : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    (∀ j, ∃ w : FinitePlace K, c j = Place.finite w ∧ residueChar w = p) →
    ∀ (d : ι → ℝ) (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w), x ≠ 0 → 0 ≤ ordp K w x →
    (∀ i w', c i = Place.finite w' → d i = differentExponent K w') →
    ∃ a : Tensor (.finite p) c, IsUnit a ∧
      (∀ φ ∈ indAut (.finite p) c,
        φ '' (incl p c j w h x • integral (.finite p) c) ⊆ a • integral (.finite p) c) ∧
      componentVol (.finite p) c (a • integral (.finite p) c) ≤
        (-ordp K w x + ∑ i, d i + 1) * Real.log p +
          ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then 3 + Real.log (ramIdxAt K (c i)) else 0
  /-- **IUT IV, Proposition 1.4(iv)**: the indeterminacy automorphisms preserve the
  integral structure `(R_I)^∼` (stated there at odd primes unramified in every factor; for
  the maximal order `(R_I)^∼` — the integral closure of `ℤ_p` in the packet — it holds at
  every prime, since automorphisms of a `ℚ_p`-algebra map integral elements to integral
  elements). -/
  prop14_iv : ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K),
    ∀ φ ∈ indAut (.finite p) c, φ '' integral (.finite p) c ⊆ integral (.finite p) c
  /-- **IUT IV, Proposition 1.5(iii),(iv)**: at the archimedean place the images of the
  log-shell under the indeterminacy automorphisms lie in `π^{|I|}·B_I`. -/
  prop15 : ∀ {ι : Type} [Fintype ι] (c : ι → Place K),
    ∀ φ ∈ indAut .infinite c, φ '' logShell .infinite c ⊆
      algebraMap ℝ (Tensor .infinite c) (Real.pi ^ Fintype.card ι) • integral .infinite c


end Iut
