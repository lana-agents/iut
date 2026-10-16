/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.LogShellMono
import Iut.Reconstruction.Local.PadicValued
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Log-shells in Galois form: `k∼ = (𝒪^×_{k̄})^pf ≅ k̄` with the `G_k`-action (roadmap MR11)

[AbsTopIII], Definition 3.1 (i): for an MLF `k` with algebraic closure `k̄` and `G_k = Gal(k̄/k)`,

> "the [p-adic …] logarithm determines a `Π_k`-equivariant isomorphism
> `log_k : k∼ := (𝒪^×_{k̄})^pf ⥲ k̄` … of the topological group `k∼` onto the additive topological
> group `k̄`",

and Definition 3.1 (iv): via `log_k` the field structure of `k̄` makes `k∼` a field with
`Π_k`-action (the *log-Frobenius functor*, isomorphic to the identity), whose `Π_k`-invariants
carry the *pre-log-shell*, the image of `𝒪^×_k = (𝒪^×_{k̄})^{Π_k}`; Definition 5.4 (iii): the
log-shell is `I := (p*)⁻¹ · I* ⊆ (k∼)^{Π_k}`. IUT II, Example 1.8 (iv):

> "`Ism(G)` for the compact topological group of `G`-isometries of `O^{×μ}(G)`, i.e.,
> `G`-equivariant automorphisms of the ind-topological module `O^{×μ}(G)` that, for each open
> subgroup `H ⊆ G`, preserve the 'lattice' in `O^{×μ}(G)^H` determined by the image of
> `O^×(G)^H`".

Here `Ω` is an algebraic extension of `ℚ_p` (an algebraic closure `k̄` of `k` below) and we write
`𝒪^×_Ω = {u ∈ Ωˣ | ‖u‖ = 1}` (`unitsΩ`), `𝒪^{×μ}_Ω = 𝒪^×_Ω / torsion` (`unitsMu`) and
`k∼ = ℚ ⊗ 𝒪^{×μ}_Ω` (`kTilde`; this is the perfection `(𝒪^×_Ω)^pf`).

## Main results

* `logΩ : 𝒪^×_Ω → Ω`, the `p`-adic logarithm on `Ω` (computed in any finite subextension,
  `logΩ_eq`, with its canonical valuation `padicValued`); a homomorphism (`logΩ_mul`) whose
  kernel is the torsion (`logΩ_eq_zero_iff`);
* **`logΩ_algHom`**: for every finite extension `K/ℚ_p` (with *any* valuation structure) and
  every `ℚ_p`-embedding `f : K → Ω`, `logΩ (f u) = f (log_K u)`;
* **`logEquivMu : k∼ ≃+ Ω`**, `log_k` of [AbsTopIII], Definition 3.1 (i);
  **`logEquivMu_kTildeMap`**: it is natural in `ℚ_p`-embeddings `τ : Ω → Ω'` — in particular
  `G_k`-equivariant (`logEquivMu_galTilde`); this is the log-Frobenius compatibility of
  Definition 3.1 (iv): the log-Frobenius functor `k̄ ↦ k∼` is isomorphic to the identity;
* **`mem_range_iff_invariant`**, `mem_iff_invariant`: `log_k` identifies `(k∼)^{G_E}` with `E`;
* `lattice F`, `logShellTilde F`: the image of `𝒪^×_F` in `𝒪^{×μ}_Ω` and the log-shell
  `(p*)⁻¹ ⊗ lattice F ⊆ k∼` for a finite subextension `F`; **`image_logShellTilde`**:
  `log_k(logShellTilde F) = 𝓘_F = Iut.logShell F p`; `image_logShellTilde_base` for `k` itself
  (with its own valuation), and **`image_galoisMonoLog`**: the group-theoretic log-shell `𝓘(G)` of
  an MLF-Galois group `ψ : G ≃ₜ* G_k` lands in the `G_k`-invariants of `k∼` as the log-shell of
  `k`;
* **`Ism p Ω k`** (the `G_k`-isometries of `𝒪^{×μ}_Ω`), `ismLogEquiv`; **`ismLogEquiv_logShell`**:
  every element of `Ism` preserves the log-shells `𝓘_E` of all finite `E/k` (and the subfields
  `E`, `ismLogEquiv_mem`, and commutes with `G_k`); `inv_mem_Ism`, `ismLogEquiv_inv`.

Deviation (documented): `Ism` is defined without the continuity condition ("automorphisms of the
ind-topological module"), so it is a priori larger than IUT's `Ism(G)`; all statements about its
elements therefore hold a fortiori for IUT's `Ism`.
-/

namespace Iut.Reconstruction

open PadicLogVolume PadicField IntermediateField Iut.LogLink
open scoped Valued TensorProduct WithZero

set_option linter.unusedSectionVars false

noncomputable section

/-! ### `ℚ_p`-algebra homomorphisms commute with the logarithm -/

section Generic

variable {p : ℕ} [hp : Fact p.Prime]
variable {K K' : Type*}
  [Field K] [Valued K ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)]
  [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [CompleteSpace K] [CharZero K]
  [Field K'] [Valued K' ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation K' ℤᵐ⁰)]
  [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K'] [CompleteSpace K'] [CharZero K']

theorem norm_sub_one_lt_map (f : K →ₐ[ℚ_[p]] K') {x : K} :
    ‖f x - 1‖ < 1 ↔ ‖x - 1‖ < 1 := by
  rw [← map_one f, ← map_sub, norm_lt_one_iff' (hball_auto (p := p)),
    norm_lt_one_iff' (hball_auto (p := p)), nrm_map]

/-- **`f (log x) = log (f x)`.** -/
theorem padicLog_map (f : K →ₐ[ℚ_[p]] K') {x : K} (hx : ‖x - 1‖ < 1) :
    f (padicLog x) = padicLog (f x) := by
  have h1 := (hasSum_padicLog hp.out (norm_p_lt_one_auto (p := p)) hx).map f
    (continuous_algHom_auto f)
  have h2 : (f ∘ logTerm x) = logTerm (f x) := by
    funext n
    simp only [Function.comp, logTerm, map_div₀, map_mul, map_pow, map_neg, map_one, map_sub,
      map_add, map_natCast]
  rw [h2] at h1
  exact h1.tsum_eq.symm

/-- The map `𝒪_Kˣ → 𝒪_{K'}ˣ` induced by `f`. -/
def unitGroupMap (f : K →ₐ[ℚ_[p]] K') : unitGroup p K →* unitGroup p K' where
  toFun u := ⟨Units.map (f : K →* K') (u : Kˣ), by
    rw [mem_unitGroup, Units.coe_map]
    change nrm p K' (f _) = 1
    rw [nrm_map]
    exact u.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

omit [Valued K ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K]
  [CharZero K] [Valued K' ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation K' ℤᵐ⁰)]
  [CompleteSpace K'] [CharZero K'] in
theorem coe_unitGroupMap (f : K →ₐ[ℚ_[p]] K') (u : unitGroup p K) :
    (((unitGroupMap f u : unitGroup p K') : K'ˣ) : K') = f ((u : Kˣ) : K) := rfl

/-- `log u = N⁻¹ log(u^N)` as soon as `u^N` is a principal unit. -/
theorem logU_eq_of_pow (u : unitGroup p K) {N : ℕ} (hN : N ≠ 0)
    (h : ‖((u : Kˣ) : K) ^ N - 1‖ < 1) :
    (logU hball_auto u).toAdd = (N : K)⁻¹ * padicLog (((u : Kˣ) : K) ^ N) := by
  have hc : (((u ^ N : unitGroup p K) : Kˣ) : K) = ((u : Kˣ) : K) ^ N := by simp
  have h1 : (logU hball_auto (u ^ N)).toAdd = N * (logU hball_auto u).toAdd := by
    rw [map_pow, toAdd_pow, nsmul_eq_mul]
  rw [logU_of_principal hball_auto _ (by rw [hc]; exact h), hc] at h1
  rw [h1, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN), one_mul]

/-- **`f (log u) = log (f u)` on the units.** -/
theorem logU_map (f : K →ₐ[ℚ_[p]] K') (u : unitGroup p K) :
    f (logU hball_auto u).toAdd = (logU hball_auto (unitGroupMap f u)).toAdd := by
  have hq := one_lt_q p K
  have hN : q p K - 1 ≠ 0 := by omega
  have hpr := pow_q_sub_one_principal hball_auto u
  have hpr' : ‖(((unitGroupMap f u : unitGroup p K') : K'ˣ) : K') ^ (q p K - 1) - 1‖ < 1 := by
    rw [coe_unitGroupMap, ← map_pow, norm_sub_one_lt_map]
    exact hpr
  rw [logU_eq_of_pow u hN hpr, logU_eq_of_pow _ hN hpr', coe_unitGroupMap, map_mul, map_inv₀,
    map_natCast, padicLog_map f hpr, map_pow]

end Generic

theorem charZero_Ω (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] :
    CharZero Ω :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective

/-! ### The canonical structures on the finite subextensions -/

namespace PadicSub

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω]

scoped instance instValued (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] :
    Valued F ℤᵐ⁰ :=
  padicValued p F

scoped instance instRankOne (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] :
    Valuation.RankOne (Valued.v : Valuation F ℤᵐ⁰) :=
  padicRankOne p F

scoped instance instCompleteSpace (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] :
    CompleteSpace F :=
  completeSpace_padicValued (p := p) (K := F)

scoped instance instCharZero (F : IntermediateField ℚ_[p] Ω) : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective

end PadicSub

open PadicSub

/-! ### The logarithm on `𝒪^×_Ω` -/

section Omega

variable {p : ℕ} [hp : Fact p.Prime]
variable {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p Ω) in
/-- `𝒪^×_Ω = {u ∈ Ωˣ | ‖u‖ = 1}`. -/
def unitsΩ : Subgroup Ωˣ where
  carrier := {u | nrm p Ω (u : Ω) = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simp_all
  inv_mem' {a} ha := by simp_all [Units.val_inv_eq_inv_val]

theorem mem_unitsΩ {u : Ωˣ} : u ∈ unitsΩ p Ω ↔ nrm p Ω (u : Ω) = 1 := Iff.rfl

instance finiteDimensional_adjoin (x : Ω) : FiniteDimensional ℚ_[p] ℚ_[p]⟮x⟯ :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)

/-- A unit of `Ω` lying in a finite subextension `F`, as a unit of `𝒪_F`. -/
def finUnit (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] (u : unitsΩ p Ω)
    (hF : ((u : Ωˣ) : Ω) ∈ F) : unitGroup p F :=
  ⟨Units.mk0 ⟨(u : Ωˣ), hF⟩ fun h => (u : Ωˣ).ne_zero (congrArg Subtype.val h), by
    rw [mem_unitGroup]
    change nrm p F ⟨_, hF⟩ = 1
    rw [← nrm_map F.val]
    exact u.2⟩

theorem coe_finUnit (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F]
    (u : unitsΩ p Ω) (hF : ((u : Ωˣ) : Ω) ∈ F) :
    ((((finUnit F u hF : unitGroup p F) : Fˣ) : F) : Ω) = ((u : Ωˣ) : Ω) := rfl

variable (p) in
/-- **The logarithm `𝒪^×_Ω → Ω`**, computed in `ℚ_p(u)`. -/
def logΩ (u : unitsΩ p Ω) : Ω :=
  ((logU hball_auto (finUnit ℚ_[p]⟮((u : Ωˣ) : Ω)⟯ u (mem_adjoin_simple_self _ _))).toAdd : Ω)

/-- **The logarithm may be computed in any finite subextension containing `u`.** -/
theorem logΩ_eq (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] (u : unitsΩ p Ω)
    (hF : ((u : Ωˣ) : Ω) ∈ F) :
    logΩ p u = ((logU hball_auto (finUnit F u hF)).toAdd : Ω) := by
  set ι := IntermediateField.inclusion (adjoin_simple_le_iff.2 hF)
  have h := logU_map ι (finUnit ℚ_[p]⟮((u : Ωˣ) : Ω)⟯ u (mem_adjoin_simple_self _ _))
  have hu : unitGroupMap ι (finUnit ℚ_[p]⟮((u : Ωˣ) : Ω)⟯ u (mem_adjoin_simple_self _ _)) =
      finUnit F u hF := by
    apply Subtype.ext; apply Units.ext; rfl
  rw [hu] at h
  rw [← h]
  rfl

/-- The map `𝒪^×_K → 𝒪^×_Ω` induced by an embedding `f : K → Ω`. -/
def unitsΩOf {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (f : K →ₐ[ℚ_[p]] Ω) : unitGroup p K →* unitsΩ p Ω where
  toFun u := ⟨Units.map (f : K →* Ω) (u : Kˣ), by
    rw [mem_unitsΩ, Units.coe_map]
    change nrm p Ω (f _) = 1
    rw [nrm_map]
    exact u.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem coe_unitsΩOf {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (f : K →ₐ[ℚ_[p]] Ω) (u : unitGroup p K) :
    (((unitsΩOf f u : unitsΩ p Ω) : Ωˣ) : Ω) = f ((u : Kˣ) : K) := rfl

/-- **`log_Ω (f u) = f (log_K u)`** for every finite extension `K/ℚ_p` (with any valuation
structure) and every `ℚ_p`-embedding `f : K → Ω`. -/
theorem logΩ_algHom {K : Type*} [Field K] [Valued K ℤᵐ⁰]
    [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [CompleteSpace K] [CharZero K]
    (f : K →ₐ[ℚ_[p]] Ω) (u : unitGroup p K) :
    logΩ p (unitsΩOf f u) = f (logU hball_auto u).toAdd := by
  let g : K →ₐ[ℚ_[p]] f.fieldRange :=
    { toFun x := ⟨f x, x, rfl⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' x y := Subtype.ext (map_mul f x y)
      map_zero' := Subtype.ext (map_zero f)
      map_add' x y := Subtype.ext (map_add f x y)
      commutes' r := Subtype.ext (f.commutes r) }
  have hg : Function.Surjective g := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  haveI : FiniteDimensional ℚ_[p] f.fieldRange := Module.Finite.of_surjective g.toLinearMap hg
  have hF : (((unitsΩOf f u : unitsΩ p Ω) : Ωˣ) : Ω) ∈ f.fieldRange := ⟨_, rfl⟩
  rw [logΩ_eq f.fieldRange _ hF]
  have h := logU_map g u
  have hu : unitGroupMap g u = finUnit f.fieldRange _ hF := by
    apply Subtype.ext; apply Units.ext; rfl
  rw [hu] at h
  rw [← h]
  rfl

/-- The map `𝒪^×_Ω → 𝒪^×_{Ω'}` induced by a `ℚ_p`-embedding `τ : Ω → Ω'`. -/
def unitsΩMap {Ω' : Type*} [Field Ω'] [Algebra ℚ_[p] Ω'] [Algebra.IsAlgebraic ℚ_[p] Ω']
    (τ : Ω →ₐ[ℚ_[p]] Ω') : unitsΩ p Ω →* unitsΩ p Ω' where
  toFun u := ⟨Units.map (τ : Ω →* Ω') (u : Ωˣ), by
    rw [mem_unitsΩ, Units.coe_map]
    change nrm p Ω' (τ _) = 1
    rw [nrm_map]
    exact u.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem coe_unitsΩMap {Ω' : Type*} [Field Ω'] [Algebra ℚ_[p] Ω'] [Algebra.IsAlgebraic ℚ_[p] Ω']
    (τ : Ω →ₐ[ℚ_[p]] Ω') (u : unitsΩ p Ω) :
    (((unitsΩMap τ u : unitsΩ p Ω') : Ω'ˣ) : Ω') = τ ((u : Ωˣ) : Ω) := rfl

/-- **Naturality (equivariance) of the logarithm**: `log (τ u) = τ (log u)`. -/
theorem logΩ_unitsΩMap {Ω' : Type*} [Field Ω'] [Algebra ℚ_[p] Ω'] [Algebra.IsAlgebraic ℚ_[p] Ω']
    (τ : Ω →ₐ[ℚ_[p]] Ω') (u : unitsΩ p Ω) : logΩ p (unitsΩMap τ u) = τ (logΩ p u) := by
  set F := ℚ_[p]⟮((u : Ωˣ) : Ω)⟯
  have h := logΩ_algHom (τ.comp F.val) (finUnit F u (mem_adjoin_simple_self _ _))
  have hu : unitsΩOf (τ.comp F.val) (finUnit F u (mem_adjoin_simple_self _ _)) =
      unitsΩMap τ u := by
    apply Subtype.ext; apply Units.ext; rfl
  rw [hu] at h
  rw [h]
  rfl

theorem logΩ_mul (u v : unitsΩ p Ω) : logΩ p (u * v) = logΩ p u + logΩ p v := by
  set F := ℚ_[p]⟮((u : Ωˣ) : Ω)⟯ ⊔ ℚ_[p]⟮((v : Ωˣ) : Ω)⟯
  have hu : ((u : Ωˣ) : Ω) ∈ F := le_sup_left (a := ℚ_[p]⟮((u : Ωˣ) : Ω)⟯)
    (mem_adjoin_simple_self _ _)
  have hv : ((v : Ωˣ) : Ω) ∈ F := le_sup_right (a := ℚ_[p]⟮((u : Ωˣ) : Ω)⟯)
    (mem_adjoin_simple_self _ _)
  have huv : (((u * v : unitsΩ p Ω) : Ωˣ) : Ω) ∈ F := by
    simpa using F.mul_mem hu hv
  rw [logΩ_eq F _ huv, logΩ_eq F _ hu, logΩ_eq F _ hv]
  have : finUnit F (u * v) huv = finUnit F u hu * finUnit F v hv := by
    apply Subtype.ext; apply Units.ext; rfl
  rw [this, map_mul, toAdd_mul]
  rfl

theorem logΩ_one : logΩ p (1 : unitsΩ p Ω) = 0 := by
  have h := logΩ_mul (p := p) (1 : unitsΩ p Ω) 1
  rw [mul_one] at h
  linear_combination -h

theorem logΩ_pow (u : unitsΩ p Ω) (n : ℕ) : logΩ p (u ^ n) = n * logΩ p u := by
  induction n with
  | zero => simp [logΩ_one]
  | succ n ih => rw [pow_succ, logΩ_mul, ih]; push_cast; ring

/-- **The kernel of `log` on `𝒪^×_Ω` is the torsion.** -/
theorem logΩ_eq_zero_iff (u : unitsΩ p Ω) : logΩ p u = 0 ↔ ∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1 := by
  haveI := charZero_Ω p Ω
  constructor
  · intro h
    set F := ℚ_[p]⟮((u : Ωˣ) : Ω)⟯
    have h' : (logU hball_auto (finUnit F u (mem_adjoin_simple_self _ _))).toAdd = 0 := by
      apply Subtype.ext
      exact h
    obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_logU_eq_zero hball_auto h'
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : unitGroup p F => (((z : Fˣ) : F) : Ω)) hpow
    simpa [coe_finUnit] using this
  · rintro ⟨n, hn, hpow⟩
    have h := logΩ_pow (p := p) u n
    rw [hpow, logΩ_one] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (Nat.cast_ne_zero.2 hn)

/-- **Every element of `Ω` is a rational multiple of a logarithm.** -/
theorem exists_logΩ_eq (y : Ω) : ∃ s : ℤ, s ≠ 0 ∧ ∃ u : unitsΩ p Ω, (s : Ω) * y = logΩ p u := by
  set F := ℚ_[p]⟮y⟯
  obtain ⟨z, hz⟩ := logTensor_surjective (hball_auto (p := p) (k := F))
    ⟨y, mem_adjoin_simple_self _ _⟩
  haveI := IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
    (M := Additive (unitGroup p F))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive (unitGroup p F)) 1) z
  simp only [TensorProduct.mk_apply] at hs
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  refine ⟨s, hs0, unitsΩOf F.val a.toMul, ?_⟩
  have h1 := congrArg (logTensor (hball_auto (p := p) (k := F))) hs
  rw [Submonoid.smul_def, (Int.cast_smul_eq_zsmul ℚ _ _).symm, logTensor_smul, hz,
    show (1 : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ Additive.ofMul a.toMul from rfl,
    logTensor_one_tmul] at h1
  rw [logΩ_algHom F.val a.toMul]
  have h2 := congrArg (fun w : F => (w : Ω)) h1
  push_cast at h2
  exact h2

/-! ### `k∼ = ℚ ⊗ 𝒪^{×μ}_Ω` and `log : k∼ ≅ Ω` -/

variable (p Ω) in
/-- `𝒪^{×μ}_Ω = 𝒪^×_Ω / μ`. -/
abbrev unitsMu : Type _ := unitsΩ p Ω ⧸ CommGroup.torsion (unitsΩ p Ω)

variable (p Ω) in
/-- `k∼ = (𝒪^×_Ω)^pf = ℚ ⊗ 𝒪^{×μ}_Ω`. -/
abbrev kTilde : Type _ := ℚ ⊗[ℤ] Additive (unitsMu p Ω)

variable (p Ω) in
/-- `log` as a homomorphism to `Multiplicative Ω`. -/
def logΩHom : unitsΩ p Ω →* Multiplicative Ω where
  toFun u := Multiplicative.ofAdd (logΩ p u)
  map_one' := by rw [logΩ_one]; rfl
  map_mul' u v := by rw [logΩ_mul]; rfl

theorem torsion_le_ker : CommGroup.torsion (unitsΩ p Ω) ≤ (logΩHom p Ω).ker := by
  intro u hu
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 hu)
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (logΩ p u) = 1
  rw [(logΩ_eq_zero_iff u).2 ⟨n, hn.ne', hpow⟩]
  rfl

variable (p Ω) in
/-- `log : 𝒪^{×μ}_Ω → Ω`. -/
def logMu : Additive (unitsMu p Ω) →+ Ω :=
  (QuotientGroup.lift _ (logΩHom p Ω) torsion_le_ker).toAdditive

theorem logMu_mk (u : unitsΩ p Ω) :
    logMu p Ω (Additive.ofMul (QuotientGroup.mk u)) = logΩ p u := rfl

/-- `(c, a) ↦ c · L(a)`, `ℤ`-bilinear. -/
def scaleMulGen {A L : Type*} [AddCommGroup A] [Field L] [CharZero L] (Lg : A →+ L) :
    ℚ →ₗ[ℤ] A →ₗ[ℤ] L :=
  LinearMap.mk₂ ℤ (fun (c : ℚ) a => (c : L) * Lg a)
    (fun c c' a => by push_cast; ring)
    (fun n c a => by rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring)
    (fun c a a' => by rw [map_add, mul_add])
    (fun n c a => by rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul]; ring)

variable (p Ω) in
/-- **`log_k : k∼ → Ω`**, `c ⊗ a ↦ c · log a`. -/
def logTensorMu : kTilde p Ω →+ Ω :=
  haveI := charZero_Ω p Ω
  (TensorProduct.lift (scaleMulGen (logMu p Ω))).toAddMonoidHom

theorem logTensorMu_tmul (c : ℚ) (u : unitsΩ p Ω) :
    logTensorMu p Ω (c ⊗ₜ Additive.ofMul (QuotientGroup.mk u)) = (c : Ω) * logΩ p u := by
  simp only [logTensorMu, LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul]
  rfl

theorem logTensorMu_smul (c : ℚ) (z : kTilde p Ω) :
    logTensorMu p Ω (c • z) = (c : Ω) * logTensorMu p Ω z := by
  haveI := charZero_Ω p Ω
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x.toMul
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change logTensorMu p Ω ((c * a) ⊗ₜ Additive.ofMul (QuotientGroup.mk u)) =
      _ * logTensorMu p Ω (a ⊗ₜ Additive.ofMul (QuotientGroup.mk u))
    rw [logTensorMu_tmul, logTensorMu_tmul]
    push_cast
    ring
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

theorem logTensorMu_injective : Function.Injective (logTensorMu p Ω) := by
  haveI := charZero_Ω p Ω
  rw [injective_iff_map_eq_zero]
  intro z hz
  haveI := IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
    (M := Additive (unitsMu p Ω))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive (unitsMu p Ω)) 1) z
  simp only [TensorProduct.mk_apply] at hs
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsz : (s : ℤ) • z = ((s : ℤ) : ℚ) • z := (Int.cast_smul_eq_zsmul ℚ _ _).symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective a.toMul
  have hlog : logΩ p u = 0 := by
    have h1 := congrArg (logTensorMu p Ω) hs
    rw [Submonoid.smul_def, hsz, logTensorMu_smul, hz, mul_zero] at h1
    have : a = Additive.ofMul (QuotientGroup.mk u) := by rw [hu]; rfl
    rw [this, logTensorMu_tmul] at h1
    simpa using h1.symm
  have ha : a = 0 := by
    have hmem : u ∈ CommGroup.torsion (unitsΩ p Ω) := by
      obtain ⟨n, hn, hpow⟩ := (logΩ_eq_zero_iff u).1 hlog
      exact (CommGroup.mem_torsion _).2
        ((isOfFinOrder_iff_pow_eq_one).2 ⟨n, Nat.pos_of_ne_zero hn, hpow⟩)
    have : (QuotientGroup.mk u : unitsMu p Ω) = 1 := (QuotientGroup.eq_one_iff u).2 hmem
    rw [hu] at this
    exact congrArg Additive.ofMul this
  rw [ha, TensorProduct.tmul_zero, Submonoid.smul_def, hsz] at hs
  rcases smul_eq_zero.1 hs with h3 | h3
  · exact absurd h3 (by exact_mod_cast hs0)
  · exact h3

theorem logTensorMu_surjective : Function.Surjective (logTensorMu p Ω) := by
  haveI := charZero_Ω p Ω
  intro y
  obtain ⟨s, hs, u, hu⟩ := exists_logΩ_eq (p := p) y
  refine ⟨((s : ℚ)⁻¹) ⊗ₜ Additive.ofMul (QuotientGroup.mk u), ?_⟩
  rw [logTensorMu_tmul, ← hu]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hs), one_mul]

variable (p Ω) in
/-- **`log_k : k∼ = (𝒪^×_{k̄})^pf ≅ k̄`** ([AbsTopIII], Definition 3.1 (i)). -/
def logEquivMu : kTilde p Ω ≃+ Ω :=
  AddEquiv.ofBijective (logTensorMu p Ω) ⟨logTensorMu_injective, logTensorMu_surjective⟩

theorem logEquivMu_apply (z : kTilde p Ω) : logEquivMu p Ω z = logTensorMu p Ω z := rfl

/-! ### Naturality: the log-Frobenius functor is isomorphic to the identity -/

variable {Ω' : Type*} [Field Ω'] [Algebra ℚ_[p] Ω'] [Algebra.IsAlgebraic ℚ_[p] Ω']

theorem unitsΩMap_torsion (τ : Ω →ₐ[ℚ_[p]] Ω') :
    CommGroup.torsion (unitsΩ p Ω) ≤ (CommGroup.torsion (unitsΩ p Ω')).comap (unitsΩMap τ) := by
  intro u hu
  rw [Subgroup.mem_comap, CommGroup.mem_torsion]
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 hu)
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, h, map_one]⟩

/-- `𝒪^{×μ}_Ω → 𝒪^{×μ}_{Ω'}` induced by `τ`. -/
def unitsMuMap (τ : Ω →ₐ[ℚ_[p]] Ω') : unitsMu p Ω →* unitsMu p Ω' :=
  QuotientGroup.map _ _ (unitsΩMap τ) (unitsΩMap_torsion τ)

/-- `k∼(τ) : k∼_Ω → k∼_{Ω'}`. -/
def kTildeMap (τ : Ω →ₐ[ℚ_[p]] Ω') : kTilde p Ω →+ kTilde p Ω' :=
  (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (unitsMuMap τ).toAdditive.toIntLinearMap).toAddMonoidHom

theorem kTildeMap_tmul (τ : Ω →ₐ[ℚ_[p]] Ω') (c : ℚ) (u : unitsΩ p Ω) :
    kTildeMap τ (c ⊗ₜ Additive.ofMul (QuotientGroup.mk u)) =
      c ⊗ₜ Additive.ofMul (QuotientGroup.mk (unitsΩMap τ u)) := rfl

/-- **Naturality of `log_k`** ([AbsTopIII], Definition 3.1 (i), (iv)): for every `ℚ_p`-embedding
`τ : Ω → Ω'`, `log ∘ k∼(τ) = τ ∘ log`. Thus the log-Frobenius functor `(Ω, Galois action) ↦
(k∼, Galois action)` is isomorphic to the identity via `log`. -/
theorem logEquivMu_kTildeMap (τ : Ω →ₐ[ℚ_[p]] Ω') (z : kTilde p Ω) :
    logEquivMu p Ω' (kTildeMap τ z) = τ (logEquivMu p Ω z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x.toMul
    change logTensorMu p Ω' (kTildeMap τ (c ⊗ₜ Additive.ofMul (QuotientGroup.mk u))) =
      τ (logTensorMu p Ω (c ⊗ₜ Additive.ofMul (QuotientGroup.mk u)))
    rw [kTildeMap_tmul, logTensorMu_tmul, logTensorMu_tmul, logΩ_unitsΩMap, map_mul,
      map_ratCast]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The Galois action and its invariants -/

section Galois

variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [Algebra k Ω] [IsScalarTower ℚ_[p] k Ω]

/-- The action of `σ ∈ G_k = Gal(Ω/k)` on `k∼`. -/
def galTilde (σ : Ω ≃ₐ[k] Ω) : kTilde p Ω →+ kTilde p Ω :=
  kTildeMap ((σ.restrictScalars ℚ_[p]) : Ω →ₐ[ℚ_[p]] Ω)

/-- **`log_k` is `G_k`-equivariant.** -/
theorem logEquivMu_galTilde (σ : Ω ≃ₐ[k] Ω) (z : kTilde p Ω) :
    logEquivMu p Ω (galTilde σ z) = σ (logEquivMu p Ω z) :=
  logEquivMu_kTildeMap _ z

theorem galTilde_eq_iff (σ : Ω ≃ₐ[k] Ω) (z : kTilde p Ω) :
    galTilde σ z = z ↔ σ (logEquivMu p Ω z) = logEquivMu p Ω z := by
  rw [← logEquivMu_galTilde]
  exact (logEquivMu p Ω).injective.eq_iff.symm

/-- **The `G_E`-invariants of `k∼` correspond to `E`** (`E/k` any subextension of the Galois
extension `Ω/k`). -/
theorem mem_iff_invariant [IsGalois k Ω] (E : IntermediateField k Ω) (z : kTilde p Ω) :
    logEquivMu p Ω z ∈ E ↔ ∀ σ ∈ E.fixingSubgroup, galTilde σ z = z := by
  conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  rw [IntermediateField.mem_fixedField_iff]
  simp only [galTilde_eq_iff]

/-- **`(k∼)^{G_k}` corresponds to `k`.** -/
theorem mem_range_iff_invariant [IsGalois k Ω] (z : kTilde p Ω) :
    logEquivMu p Ω z ∈ Set.range (algebraMap k Ω) ↔ ∀ σ : Ω ≃ₐ[k] Ω, galTilde σ z = z := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  simp only [galTilde_eq_iff]

end Galois

/-! ### Lattices and log-shells -/

variable (p) in
/-- The lattice of a finite subextension `F`: the image of `𝒪^×_F = (𝒪^×_Ω)^{G_F}` in
`𝒪^{×μ}_Ω`. -/
def lattice (F : IntermediateField ℚ_[p] Ω) : Set (unitsMu p Ω) :=
  {a | ∃ u : unitsΩ p Ω, ((u : Ωˣ) : Ω) ∈ F ∧ QuotientGroup.mk u = a}

variable (p) in
/-- The log-shell `(p*)⁻¹ ⊗ lattice F ⊆ k∼` ([AbsTopIII], Definition 5.4 (iii)). -/
def logShellTilde (F : IntermediateField ℚ_[p] Ω) : Set (kTilde p Ω) :=
  {x | ∃ a ∈ lattice p F, x = ((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul a}

theorem logEquivMu_pStar (u : unitsΩ p Ω) :
    logEquivMu p Ω (((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul (QuotientGroup.mk u)) =
      (pStar p : Ω)⁻¹ * logΩ p u := by
  haveI := charZero_Ω p Ω
  rw [logEquivMu_apply, logTensorMu_tmul, Rat.cast_inv, Rat.cast_natCast]

/-- **`log_k (logShellTilde F) = 𝓘_F`**: the log-shell in `k∼` is the log-shell
`Iut.logShell F p` of IUT III, Definition 1.1 (for the canonical valuation of `F`). -/
theorem image_logShellTilde (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F] :
    logEquivMu p Ω '' logShellTilde p F = (fun y : F => (y : Ω)) '' logShell F p := by
  rw [logShell_eq_range_logU (hball_auto (p := p) (k := F))]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, logShellTilde, lattice]
  constructor
  · rintro ⟨x, ⟨a, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(pStar p : F)⁻¹ * (logU hball_auto (finUnit F u hu)).toAdd,
      ⟨finUnit F u hu, rfl⟩, ?_⟩
    rw [logEquivMu_pStar, logΩ_eq F u hu]
    push_cast
    rfl
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    set u := unitsΩOf F.val a
    have hu : ((u : Ωˣ) : Ω) ∈ F := (a : Fˣ).val.2
    refine ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, ?_⟩
    rw [logEquivMu_pStar, logΩ_algHom F.val a]
    push_cast
    rfl

/-- **The log-shell of a `p`-adic field `k ⊆ Ω` (with its own valuation)**: for an embedding
`f : k → Ω`, `log_k (logShellTilde f(k)) = f(𝓘_k)`. -/
theorem image_logShellTilde_algHom {K : Type*} [Field K] [Valued K ℤᵐ⁰]
    [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [CompleteSpace K] [CharZero K] (f : K →ₐ[ℚ_[p]] Ω) :
    logEquivMu p Ω '' logShellTilde p f.fieldRange = f '' logShell K p := by
  rw [logShell_eq_range_logU (hball_auto (p := p) (k := K))]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, logShellTilde, lattice]
  constructor
  · rintro ⟨x, ⟨a, ⟨u, ⟨w, hw⟩, rfl⟩, rfl⟩, rfl⟩
    have hw1 : nrm p K w = 1 := by
      rw [← nrm_map f]
      change nrm p Ω (f.toRingHom w) = 1
      rw [hw]
      exact u.2
    have hw0 : w ≠ 0 := by
      rintro rfl; rw [map_zero] at hw1; exact zero_ne_one hw1
    set a' : unitGroup p K := ⟨Units.mk0 w hw0, hw1⟩
    have ha' : unitsΩOf f a' = u := by
      apply Subtype.ext; apply Units.ext; exact hw
    refine ⟨_, ⟨a', rfl⟩, ?_⟩
    rw [logEquivMu_pStar, ← ha', logΩ_algHom f a', map_mul, map_inv₀, map_natCast]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨unitsΩOf f a, ⟨_, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    rw [logEquivMu_pStar, logΩ_algHom f a, map_mul, map_inv₀, map_natCast]

/-! ### `Ism`: the `G_k`-isometries of `𝒪^{×μ}_Ω` -/

section Ism

variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [Algebra k Ω] [IsScalarTower ℚ_[p] k Ω]

/-- The action of `σ ∈ G_k` on `𝒪^{×μ}_Ω`. -/
def galMu (σ : Ω ≃ₐ[k] Ω) : unitsMu p Ω →* unitsMu p Ω :=
  unitsMuMap ((σ.restrictScalars ℚ_[p]) : Ω →ₐ[ℚ_[p]] Ω)

variable (p Ω k) in
/-- **`Ism`**: the `G_k`-equivariant automorphisms of `𝒪^{×μ}_Ω` preserving, for every open
subgroup `G_E` (`E/k` finite), the lattice of `𝒪^×_E` (IUT II, Example 1.8 (iv); continuity not
imposed). -/
def Ism : Subgroup (unitsMu p Ω ≃* unitsMu p Ω) where
  carrier := {β | (∀ (σ : Ω ≃ₐ[k] Ω) a, β (galMu σ a) = galMu σ (β a)) ∧
    ∀ E : IntermediateField k Ω, FiniteDimensional k E →
      ∀ a, a ∈ lattice p (E.restrictScalars ℚ_[p]) ↔ β a ∈ lattice p (E.restrictScalars ℚ_[p])}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
  mul_mem' {β γ} hβ hγ := ⟨fun σ a => by
      change β (γ _) = _
      rw [hγ.1, hβ.1]
      rfl,
    fun E hE a => (hγ.2 E hE a).trans (hβ.2 E hE (γ a))⟩
  inv_mem' {β} hβ := ⟨fun σ a => by
      have e : ∀ x, β⁻¹ x = β.symm x := fun _ => rfl
      simp only [e]
      apply β.injective
      rw [MulEquiv.apply_symm_apply, hβ.1, MulEquiv.apply_symm_apply],
    fun E hE a => by
      have e : ∀ x, β⁻¹ x = β.symm x := fun _ => rfl
      simp only [e]
      rw [hβ.2 E hE (β.symm a), MulEquiv.apply_symm_apply]⟩

/-- `ℚ ⊗ β` on `k∼`. -/
def ismTilde (β : unitsMu p Ω ≃* unitsMu p Ω) : kTilde p Ω ≃+ kTilde p Ω :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) β.toAdditive.toIntLinearEquiv).toAddEquiv

/-- The additive automorphism of `Ω` induced by `β`, through `log_k`. -/
def ismLogEquiv (β : unitsMu p Ω ≃* unitsMu p Ω) : Ω ≃+ Ω :=
  (logEquivMu p Ω).symm.trans ((ismTilde β).trans (logEquivMu p Ω))

theorem ismLogEquiv_logEquivMu (β : unitsMu p Ω ≃* unitsMu p Ω) (z : kTilde p Ω) :
    ismLogEquiv β (logEquivMu p Ω z) = logEquivMu p Ω (ismTilde β z) := by
  change logEquivMu p Ω (ismTilde β ((logEquivMu p Ω).symm (logEquivMu p Ω z))) = _
  rw [AddEquiv.symm_apply_apply]

theorem ismTilde_galTilde {β : unitsMu p Ω ≃* unitsMu p Ω} (hβ : β ∈ Ism p Ω k)
    (σ : Ω ≃ₐ[k] Ω) (z : kTilde p Ω) : ismTilde β (galTilde σ z) = galTilde σ (ismTilde β z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    change c ⊗ₜ Additive.ofMul (β (galMu σ x.toMul)) =
      c ⊗ₜ Additive.ofMul (galMu σ (β x.toMul))
    rw [hβ.1]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Elements of `Ism` commute with `G_k`** (on `Ω`, through `log_k`). -/
theorem ismLogEquiv_comm {β : unitsMu p Ω ≃* unitsMu p Ω} (hβ : β ∈ Ism p Ω k)
    (σ : Ω ≃ₐ[k] Ω) (y : Ω) : ismLogEquiv β (σ y) = σ (ismLogEquiv β y) := by
  obtain ⟨z, rfl⟩ := (logEquivMu p Ω).surjective y
  rw [← logEquivMu_galTilde, ismLogEquiv_logEquivMu, ismLogEquiv_logEquivMu,
    ismTilde_galTilde hβ, logEquivMu_galTilde]

/-- **Elements of `Ism` preserve every subextension `E/k`.** -/
theorem ismLogEquiv_mem [IsGalois k Ω] {β : unitsMu p Ω ≃* unitsMu p Ω} (hβ : β ∈ Ism p Ω k)
    (E : IntermediateField k Ω) {y : Ω} (hy : y ∈ E) : ismLogEquiv β y ∈ E := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    at hy ⊢
  intro σ hσ
  rw [← ismLogEquiv_comm hβ, hy σ hσ]

theorem ismTilde_logShellTilde {β : unitsMu p Ω ≃* unitsMu p Ω} (hβ : β ∈ Ism p Ω k)
    (E : IntermediateField k Ω) [FiniteDimensional k E] :
    ismTilde β '' logShellTilde p (E.restrictScalars ℚ_[p]) =
      logShellTilde p (E.restrictScalars ℚ_[p]) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨β a, (hβ.2 E inferInstance a).1 ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨_, ⟨β.symm a, (hβ.2 E inferInstance _).2 (by rw [MulEquiv.apply_symm_apply]; exact ha),
      rfl⟩, ?_⟩
    change ((pStar p : ℚ)⁻¹) ⊗ₜ Additive.ofMul (β (β.symm a)) = _
    rw [MulEquiv.apply_symm_apply]

/-- **Elements of `Ism` preserve the log-shells `𝓘_E` of all finite `E/k`** (IUT III,
Proposition 1.2 (vi): the `Ism`-indeterminacy acts on the mono-analytic log-shells). -/
theorem ismLogEquiv_logShell {β : unitsMu p Ω ≃* unitsMu p Ω} (hβ : β ∈ Ism p Ω k)
    (E : IntermediateField k Ω) [FiniteDimensional k E]
    [FiniteDimensional ℚ_[p] (E.restrictScalars ℚ_[p])] :
    ismLogEquiv β '' ((fun y : E.restrictScalars ℚ_[p] => (y : Ω)) ''
        logShell (E.restrictScalars ℚ_[p]) p) =
      (fun y : E.restrictScalars ℚ_[p] => (y : Ω)) '' logShell (E.restrictScalars ℚ_[p]) p := by
  rw [← image_logShellTilde, Set.image_image]
  simp only [ismLogEquiv_logEquivMu]
  rw [← Set.image_image, ismTilde_logShellTilde hβ E]

/-- The inversion of `𝒪^{×μ}_Ω`. -/
def invMu : unitsMu p Ω ≃* unitsMu p Ω := MulEquiv.inv (unitsMu p Ω)

theorem lattice_inv (F : IntermediateField ℚ_[p] Ω) (a : unitsMu p Ω) :
    a ∈ lattice p F ↔ a⁻¹ ∈ lattice p F := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, by simpa [Units.val_inv_eq_inv_val] using F.inv_mem hu, rfl⟩
  · rintro ⟨u, hu, hua⟩
    refine ⟨u⁻¹, by simpa [Units.val_inv_eq_inv_val] using F.inv_mem hu, ?_⟩
    rw [QuotientGroup.mk_inv, hua, inv_inv]

theorem galMu_inv (σ : Ω ≃ₐ[k] Ω) (a : unitsMu p Ω) : galMu σ a⁻¹ = (galMu σ a)⁻¹ :=
  map_inv _ a

/-- **The inversion belongs to `Ism`.** -/
theorem invMu_mem_Ism : invMu ∈ Ism p Ω k :=
  ⟨fun σ a => (galMu_inv σ a).symm, fun _ _ a => lattice_inv _ a⟩

/-- **The inversion acts on `Ω` by `y ↦ −y`.** -/
theorem ismLogEquiv_inv (y : Ω) : ismLogEquiv (invMu (p := p) (Ω := Ω)) y = -y := by
  obtain ⟨z, rfl⟩ := (logEquivMu p Ω).surjective y
  rw [ismLogEquiv_logEquivMu, ← map_neg]
  congr 1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    change c ⊗ₜ Additive.ofMul (x.toMul⁻¹) = -(c ⊗ₜ x)
    rw [← TensorProduct.tmul_neg]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, neg_add]

end Ism

end Omega

/-! ### The group-theoretic log-shell inside `(k∼)^{G_k}` -/

section Mono

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation k ℤᵐ⁰)]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [CompleteSpace k] [CharZero k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The group-theoretic `ℚ ⊗ 𝒪^×(G)` inside `k∼`**, for `ψ : G ≃ₜ* G_k`: `monoLogEquiv ψ`
followed by `k ⊆ Ω` and `log_k⁻¹`. -/
def galoisMonoLog (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (x : unitsQ G) : kTilde p Ω :=
  (logEquivMu p Ω).symm (algebraMap k Ω (monoLogEquiv (p := p) ψ x))

/-- It lands in the `G_k`-invariants of `k∼`. -/
theorem galoisMonoLog_invariant (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) (x : unitsQ G) (σ : Ω ≃ₐ[k] Ω) :
    galTilde σ (galoisMonoLog (p := p) ψ x) = galoisMonoLog (p := p) ψ x := by
  revert σ
  rw [← mem_range_iff_invariant (p := p) (Ω := Ω), galoisMonoLog, AddEquiv.apply_symm_apply]
  exact ⟨_, rfl⟩

/-- **[AbsTopIII], Definition 5.4 (iii), Proposition 5.8 (ii) in Galois form**: the
group-theoretic log-shell `𝓘(G)` is mapped onto the log-shell `logShellTilde k ⊆ (k∼)^{G_k}`,
`I = (p*)⁻¹ · I*` with `I*` the image of `𝒪^×_k = (𝒪^×_{k̄})^{G_k}`. -/
theorem image_galoisMonoLog (ψ : G ≃ₜ* (Ω ≃ₐ[k] Ω)) :
    galoisMonoLog (p := p) ψ '' monoLogShell G =
      logShellTilde p (IsScalarTower.toAlgHom ℚ_[p] k Ω).fieldRange := by
  have h := image_logShellTilde_algHom (p := p) (Ω := Ω) (IsScalarTower.toAlgHom ℚ_[p] k Ω)
  have e : galoisMonoLog (p := p) ψ '' monoLogShell G =
      (logEquivMu p Ω).symm '' ((IsScalarTower.toAlgHom ℚ_[p] k Ω) ''
        (monoLogEquiv (p := p) ψ '' monoLogShell G)) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [e, image_monoLogEquiv, ← h, Set.image_image]
  simp only [AddEquiv.symm_apply_apply, Set.image_id']

end Mono

end

end Iut.Reconstruction
