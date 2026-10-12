/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Column
import Iut.ThetaLink.Gauss

/-!
# Splitting monoids and local LGP-monoids (IUT III, Propositions 3.4(ii), 3.5; Thm 3.11(ii)(b))

At a bad place `v` the Gaussian monoid of a `Θ^{±ell}NF`-Hodge theater is the splitting monoid
`O^×·g^ℕ ⊆ ∏_{j=1}^{ℓ*} K_v` of P19 (`ThetaLink.splitMonoid`), `g = {q_v^{j²}}_j` the Gaussian
generator. IUT III builds from it:

* the **local LGP-monoid** (`lgpMonoid`, Proposition 3.4(ii)): the pull-back of the Gaussian
  monoid of `†HT` along the poly-isomorphism `log(‡F_v) ≅ †F_v` of a log-link `‡HT → †HT`. In
  the model the log-link carries a bicontinuous ring isomorphism `φ` (`LocalLogLink`), so the
  LGP-monoid is the splitting monoid of the generator `φ⁻¹ ∘ g` (`lgpMonoid_eq`), isomorphic to
  the Gaussian monoid (`lgpEquiv`);
* the **splitting monoids** `Ψ⊥ ⊆ Ψ` (`perpMonoid r g = μ_r·g^ℕ`, Proposition 3.5(ii)(c); IUT III,
  Definition 2.4(i)): the submonoid given by the splitting up to torsion, whose units are the
  `r`-torsion (`r = 2ℓ` in IUT: "the subgroup of units of `Ψ⊥` consists of the `2l`-torsion
  subgroup of `Ψ`").

## Results

* `norm_ringEquiv_eq_one_iff`: bicontinuous ring automorphisms preserve the units `‖x‖ = 1`.
* **The units of `Ψ⊥` are the torsion** (`perp_unit`): an element `ζ·g^N` with a component of norm
  one has `N = 0` (for a strict generator, `IsStrictGen`: every entry has norm in `(0, 1)`, as the
  Gaussian generator `q_v^{j²}`, `isStrictGen_gaussGen`); the non-torsion elements are not units
  (`perp_norm_lt_one`).
* **Only the torsion is in the domain of the log-link** (`perp_pow_eq_one_of_mem_domain`), and the
  **log-link kills it** (`LocalLogLink.perp_toFun_eq_zero`): multiplication by these roots of unity
  at level `m` corresponds, via the log-link, to "addition by zero" at level `m + 1`.
* **Vertically coric splitting and LGP-monoids** (`LGPColumn`, Proposition 3.5(i)): a vertical line
  whose Kummer isomorphisms are compatible with the Gaussian generator (the Kummer isomorphisms of
  labeled data of IUT II, Corollary 4.6(iii)). The Kummer isomorphisms of the splitting monoids
  (`perpKummer`) and of the LGP-monoids (`lgpKummer`: `LGP(n, m) → Ψ_gau(n, ◦)`,
  `x ↦ κ_m(φ_{m−1}(x))`) are isomorphisms onto the **same** coric monoid for every `m`
  (`image_perpKummer`): unlike the unit portions, which only satisfy upper
  semi-compatibility (`LogColumn.upperSemiCompat`, an inclusion into the log-shell), the splitting
  monoids are **precisely** compatible.
* **Theorem 3.11(ii)(b) / Proposition 3.5(ii)(c)** (`LGPColumn.perp_compat`): as `m` varies, the
  Kummer isomorphisms of the splitting monoids are mutually compatible relative to the log-links:
  an element of `Ψ⊥` of level `m` whose label-`j` component lies in the domain of the log-link
  `m → m + 1` is a root of unity, and its Kummer image at level `m + 1` is `0` — its action on the
  coric `I^Q` is the identity (`perp_compat_action`).
-/

namespace Iut

namespace LogLink

open PadicLogVolume ThetaLink
open scoped Valued

universe u

noncomputable section

/-! ### Componentwise automorphisms and splitting monoids (algebraic part) -/

section Algebraic

variable {k : Type u} [Field k] {n : ℕ}

/-- **The splitting monoid** `Ψ⊥ = μ_r·g^ℕ ⊆ k^n` (IUT III, Proposition 3.5(ii)(c); Definition
2.4(i)): the submonoid determined by the splitting up to torsion of the Gaussian monoid
`O^×·g^ℕ`, whose units are the `r`-torsion (`r = 2ℓ` in IUT). -/
def perpMonoid (r : ℕ) (g : Fin n → k) : Submonoid (Fin n → k) where
  carrier := {x | ∃ ζ : k, ζ ^ r = 1 ∧ ∃ N : ℕ, x = fun j => ζ * g j ^ N}
  mul_mem' := by
    rintro _ _ ⟨ζ, hζ, N, rfl⟩ ⟨ζ', hζ', N', rfl⟩
    refine ⟨ζ * ζ', by rw [mul_pow, hζ, hζ', one_mul], N + N', funext fun j => ?_⟩
    simp only [Pi.mul_apply, pow_add]
    ring
  one_mem' := ⟨1, one_pow _, 0, funext fun _ => by simp⟩

lemma mem_perpMonoid {r : ℕ} {g : Fin n → k} {x : Fin n → k} :
    x ∈ perpMonoid r g ↔ ∃ ζ : k, ζ ^ r = 1 ∧ ∃ N : ℕ, x = fun j => ζ * g j ^ N := Iff.rfl

/-- A ring automorphism fixing `g` maps `Ψ⊥` into itself. -/
theorem map_mem_perpMonoid {r : ℕ} {g : Fin n → k} (τ : k ≃+* k) (hτg : ∀ j, τ (g j) = g j)
    {x : Fin n → k} (hx : x ∈ perpMonoid r g) : (fun j => τ (x j)) ∈ perpMonoid r g := by
  obtain ⟨ζ, hζ, N, rfl⟩ := hx
  refine ⟨τ ζ, by rw [← map_pow, hζ, map_one], N, funext fun j => ?_⟩
  simp only [map_mul, map_pow, hτg]

/-- The componentwise action of a ring automorphism on `k^n`. -/
def piMap (τ : k ≃+* k) : (Fin n → k) ≃* (Fin n → k) :=
  MulEquiv.piCongrRight fun _ => τ.toMulEquiv

@[simp] lemma piMap_apply (τ : k ≃+* k) (x : Fin n → k) (j : Fin n) :
    piMap τ x j = τ (x j) := rfl

lemma piMap_symm_piMap (τ : k ≃+* k) (x : Fin n → k) :
    piMap τ.symm (piMap τ x) = x := funext fun j => by simp

lemma piMap_piMap_symm (τ : k ≃+* k) (x : Fin n → k) :
    piMap τ (piMap τ.symm x) = x := funext fun j => by simp

/-- **Restriction to a submonoid preserved in both directions**: a ring automorphism `τ` with
`τ(M) ⊆ M` and `τ⁻¹(M) ⊆ M` induces an automorphism of `M`. -/
def restrictAut (τ : k ≃+* k) (M : Submonoid (Fin n → k))
    (h : ∀ x ∈ M, piMap τ x ∈ M) (h' : ∀ x ∈ M, piMap τ.symm x ∈ M) : M ≃* M where
  toFun x := ⟨piMap τ (x : Fin n → k), h x x.2⟩
  invFun x := ⟨piMap τ.symm (x : Fin n → k), h' x x.2⟩
  left_inv x := Subtype.ext (piMap_symm_piMap τ (x : Fin n → k))
  right_inv x := Subtype.ext (piMap_piMap_symm τ (x : Fin n → k))
  map_mul' x y := Subtype.ext (map_mul (piMap τ) (x : Fin n → k) y)

@[simp] lemma coe_restrictAut (τ : k ≃+* k) (M : Submonoid (Fin n → k)) (h h')
    (x : M) : (restrictAut τ M h h' x : Fin n → k) = piMap τ (x : Fin n → k) := rfl

/-- The image of a submonoid preserved in both directions is the submonoid itself. -/
theorem image_piMap_eq (τ : k ≃+* k) (M : Submonoid (Fin n → k))
    (h : ∀ x ∈ M, piMap τ x ∈ M) (h' : ∀ x ∈ M, piMap τ.symm x ∈ M) :
    piMap τ '' (M : Set (Fin n → k)) = M := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨piMap τ.symm x, h' x hx, piMap_piMap_symm τ x⟩
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

end Algebraic

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-! ### Bicontinuous ring automorphisms preserve the units -/

/-- A bicontinuous ring automorphism maps elements of norm one to elements of norm one. -/
theorem norm_ringEquiv_eq_one (τ : k ≃+* k) (h2 : Continuous τ.symm) {x : k} (hx : ‖x‖ = 1) :
    ‖τ x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rcases lt_trichotomy ‖τ x‖ 1 with h | h | h
  · have := norm_map_lt_one τ.symm.toRingHom h2 h
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply] at this
    linarith
  · exact h
  · have hτ0 : τ x ≠ 0 := (map_ne_zero τ).2 hx0
    have hi : ‖(τ x)⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ h
    have := norm_map_lt_one τ.symm.toRingHom h2 hi
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀,
      RingEquiv.symm_apply_apply, norm_inv, hx, inv_one] at this
    exact absurd this (lt_irrefl _)

/-- **Bicontinuous ring automorphisms preserve the units** `‖x‖ = 1`. -/
theorem norm_ringEquiv_eq_one_iff (τ : k ≃+* k) (h1 : Continuous τ) (h2 : Continuous τ.symm)
    {x : k} : ‖τ x‖ = 1 ↔ ‖x‖ = 1 := by
  refine ⟨fun h => ?_, norm_ringEquiv_eq_one τ h2⟩
  have := norm_ringEquiv_eq_one τ.symm (by simpa using h1) h
  rwa [RingEquiv.symm_apply_apply] at this

/-! ### Splitting monoids `Ψ⊥` -/

section Perp

variable {n : ℕ}

/-- `Ψ⊥ ⊆ Ψ`: the splitting monoid is a submonoid of the Gaussian (splitting) monoid. -/
theorem perpMonoid_le_splitMonoid {r : ℕ} (hr : r ≠ 0) (g : Fin n → k) :
    perpMonoid r g ≤ splitMonoid g := by
  rintro _ ⟨ζ, hζ, N, rfl⟩
  exact ⟨ζ, ThetaLink.norm_eq_one_of_pow hr hζ, N, rfl⟩

/-- A **strict generator**: every entry has norm in `(0, 1)` (as the Gaussian generator
`{q_v^{j²}}_j`). -/
def IsStrictGen (g : Fin n → k) : Prop := ∀ j, 0 < ‖g j‖ ∧ ‖g j‖ < 1

variable {r : ℕ} {g : Fin n → k}

/-- An element `ζ·g^N` of `Ψ⊥` with a component of norm one has `N = 0`. -/
theorem perp_exponent_eq_zero (hg : IsStrictGen g) (hr : r ≠ 0) {ζ : k} (hζ : ζ ^ r = 1)
    {N : ℕ} {j : Fin n} (h : ‖ζ * g j ^ N‖ = 1) : N = 0 :=
  (ThetaLink.norm_eq_one_iff (hg j).1 (hg j).2 (norm_eq_one_of_pow hr hζ) N).1 h

/-- **The units of `Ψ⊥` are the `r`-torsion** (IUT III, Proposition 3.5(ii)(c)): an element of
`Ψ⊥` with a component of norm one is a diagonal `r`-th root of unity. -/
theorem perp_unit (hg : IsStrictGen g) (hr : r ≠ 0) {x : Fin n → k} (hx : x ∈ perpMonoid r g)
    {j : Fin n} (h : ‖x j‖ = 1) : (x = fun _ => x j) ∧ x j ^ r = 1 := by
  obtain ⟨ζ, hζ, N, rfl⟩ := hx
  have hN := perp_exponent_eq_zero hg hr hζ h
  subst hN
  simp [hζ]

/-- The non-torsion elements of `Ψ⊥` are not units: `‖ζ·g_j^N‖ < 1` for `N > 0`. -/
theorem perp_norm_lt_one (hg : IsStrictGen g) (hr : r ≠ 0) {ζ : k} (hζ : ζ ^ r = 1) {N : ℕ}
    (hN : 0 < N) (j : Fin n) : ‖ζ * g j ^ N‖ < 1 := by
  rw [norm_mul, ThetaLink.norm_eq_one_of_pow hr hζ, one_mul, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (hg j).2 hN.ne'

/-- **Only the torsion of `Ψ⊥` lies in the domain of the log-link** (the principal units). -/
theorem perp_pow_eq_one_of_mem_domain (hg : IsStrictGen g) (hr : r ≠ 0) {x : Fin n → k}
    (hx : x ∈ perpMonoid r g) {j : Fin n} (h : ‖x j - 1‖ < 1) : x j ^ r = 1 :=
  (perp_unit hg hr hx (norm_eq_one_of_norm_sub_one_lt h)).2

/-- A bicontinuous ring automorphism fixing `g` maps the splitting monoid `O^×·g^ℕ` into
itself. -/
theorem map_mem_splitMonoid (τ : k ≃+* k) (h2 : Continuous τ.symm)
    (hτg : ∀ j, τ (g j) = g j) {x : Fin n → k} (hx : x ∈ splitMonoid g) :
    (fun j => τ (x j)) ∈ splitMonoid g := by
  obtain ⟨u, hu, N, rfl⟩ := hx
  refine ⟨τ u, norm_ringEquiv_eq_one τ h2 hu, N, funext fun j => ?_⟩
  simp only [map_mul, map_pow, hτg]

end Perp

/-! ### Local LGP-monoids -/

section LGP

variable {n : ℕ}

/-- **The local LGP-monoid** (IUT III, Proposition 3.4(ii)): the pull-back, along the
poly-isomorphism `φ : log(‡F_v) ≅ †F_v` of a log-link `‡HT → †HT`, of the Gaussian monoid
`O^×·g^ℕ` of `†HT`; a submonoid of the `ℓ*`-fold product of `log(‡F_v)`. -/
def lgpMonoid (L : LocalLogLink k) (g : Fin n → k) : Submonoid (Fin n → k) :=
  (splitMonoid g).comap (piMap L.φ).toMonoidHom

lemma mem_lgpMonoid {L : LocalLogLink k} {g : Fin n → k} {x : Fin n → k} :
    x ∈ lgpMonoid L g ↔ (fun j => L.φ (x j)) ∈ splitMonoid g := Iff.rfl

/-- **The LGP-monoid is the splitting monoid of the pulled-back generator** `φ⁻¹ ∘ g`: its unit
portion is the unit group of `log(‡F_v)`, its value-group portion is generated by `φ⁻¹(g)`. -/
theorem lgpMonoid_eq (L : LocalLogLink k) (g : Fin n → k) :
    lgpMonoid L g = splitMonoid fun j => L.φ.symm (g j) := by
  ext x
  rw [mem_lgpMonoid]
  constructor
  · rintro ⟨u, hu, N, h⟩
    refine ⟨L.φ.symm u, norm_ringEquiv_eq_one L.φ.symm (by simpa using L.cont) hu, N,
      funext fun j => ?_⟩
    have := congrFun h j
    rw [← map_pow, ← map_mul, ← this, RingEquiv.symm_apply_apply]
  · rintro ⟨u, hu, N, rfl⟩
    refine ⟨L.φ u, norm_ringEquiv_eq_one L.φ L.cont_symm hu, N, funext fun j => ?_⟩
    simp

/-- **The LGP-monoid is isomorphic to the Gaussian monoid**, by `φ`. -/
def lgpEquiv (L : LocalLogLink k) (g : Fin n → k) : lgpMonoid L g ≃* splitMonoid g where
  toFun x := ⟨piMap L.φ (x : Fin n → k), x.2⟩
  invFun y := ⟨piMap L.φ.symm (y : Fin n → k), by
    rw [mem_lgpMonoid]
    convert y.2 using 1
    exact piMap_piMap_symm L.φ (y : Fin n → k)⟩
  left_inv x := Subtype.ext (piMap_symm_piMap L.φ (x : Fin n → k))
  right_inv y := Subtype.ext (piMap_piMap_symm L.φ (y : Fin n → k))
  map_mul' x y := Subtype.ext (map_mul (piMap L.φ) (x : Fin n → k) y)

/-- **The splitting monoid of the LGP-monoid**: the pull-back of `Ψ⊥`. -/
def lgpPerp (L : LocalLogLink k) (r : ℕ) (g : Fin n → k) : Submonoid (Fin n → k) :=
  (perpMonoid r g).comap (piMap L.φ).toMonoidHom

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem lgpPerp_eq (L : LocalLogLink k) (r : ℕ) (g : Fin n → k) :
    lgpPerp L r g = perpMonoid r fun j => L.φ.symm (g j) := by
  ext x
  change (fun j => L.φ (x j)) ∈ perpMonoid r g ↔ _
  constructor
  · rintro ⟨ζ, hζ, N, h⟩
    refine ⟨L.φ.symm ζ, by rw [← map_pow, hζ, map_one], N, funext fun j => ?_⟩
    have := congrFun h j
    rw [← map_pow, ← map_mul, ← this, RingEquiv.symm_apply_apply]
  · rintro ⟨ζ, hζ, N, rfl⟩
    refine ⟨L.φ ζ, by rw [← map_pow, hζ, map_one], N, funext fun j => ?_⟩
    simp

theorem lgpPerp_le_lgpMonoid (L : LocalLogLink k) {r : ℕ} (hr : r ≠ 0) (g : Fin n → k) :
    lgpPerp L r g ≤ lgpMonoid L g := fun _ hx => perpMonoid_le_splitMonoid hr g hx

end LGP

/-! ### The log-link kills the torsion of `Ψ⊥` -/

section LogKill

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- **The log-link kills the part of `Ψ⊥` in its domain** (IUT III, Proposition 3.5(ii)(c)):
multiplication by these roots of unity corresponds, via the log-link, to "addition by zero". -/
theorem LocalLogLink.perp_toFun_eq_zero (L : LocalLogLink k) (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) {n r : ℕ} {g : Fin n → k} (hg : IsStrictGen g) (hr : r ≠ 0)
    {x : Fin n → k} (hx : x ∈ perpMonoid r g) {j : Fin n} (h : ‖x j - 1‖ < 1) :
    L.toFun (x j) = 0 := by
  rw [LocalLogLink.toFun, padicLog_eq_zero_of_pow_eq_one hp hpk h hr
    (perp_pow_eq_one_of_mem_domain hg hr hx h), map_zero]

end LogKill

/-! ### Vertically coric LGP-monoids and Theorem 3.11(ii)(b) -/

variable (k) in
/-- **A vertical line with Gaussian data** (IUT III, Proposition 3.5(i)): a vertical line whose
Kummer isomorphisms are compatible with the Gaussian generator (the theta values; the Kummer
isomorphisms of labeled data of IUT II, Corollary 4.6(iii)) and whose log-links are compatible
with it (the compatibility of the log-links with the `F_ℓ^{⋊±}`-symmetrizing isomorphisms,
IUT III, Remark 1.3.2, Proposition 3.4(ii): the copies of the Hodge theaters carry the same
Gaussian monoids). -/
structure LGPColumn (n : ℕ) extends LogColumn k where
  /-- The Gaussian generator `{q_v^{j²}}_j` of every level. -/
  gen : Fin n → k
  strict : IsStrictGen gen
  /-- The Kummer isomorphisms fix the Gaussian generator. -/
  kum_gen : ∀ m j, kum m (gen j) = gen j

namespace LGPColumn

variable {n : ℕ} (C : LGPColumn k n)

theorem kum_symm_gen (m : ℤ) (j : Fin n) : (C.kum m).symm (C.gen j) = C.gen j := by
  conv_lhs => rw [← C.kum_gen m j]
  exact RingEquiv.symm_apply_apply _ _

/-- **The Kummer isomorphism of the splitting monoids** `Ψ⊥_{FLGP}(n, m) ≅ Ψ⊥_{LGP}(n, ◦)`
(IUT III, Proposition 3.5(i); Theorem 3.11(ii)(b)). -/
def perpKummer (r : ℕ) (m : ℤ) : perpMonoid r C.gen ≃* perpMonoid r C.gen :=
  restrictAut (C.kum m) _ (fun _ hx => map_mem_perpMonoid _ (C.kum_gen m) hx)
    (fun _ hx => map_mem_perpMonoid _ (C.kum_symm_gen m) hx)

/-- **The Kummer isomorphism of the Gaussian monoids** `Ψ_gau(n, m) ≅ Ψ_gau(n, ◦)`. -/
def gaussKummer (m : ℤ) : splitMonoid C.gen ≃* splitMonoid C.gen :=
  restrictAut (C.kum m) _
    (fun _ hx => map_mem_splitMonoid _ (C.kum_cont_symm m) (C.kum_gen m) hx)
    (fun _ hx => map_mem_splitMonoid _ (by simpa using C.kum_cont m) (C.kum_symm_gen m) hx)

/-- **The Kummer isomorphism of the LGP-monoids** `Ψ_{FLGP}(n, m) ≅ Ψ_{LGP}(n, ◦)` (IUT III,
Proposition 3.5(i)): the LGP-monoid of level `m`, built from the log-link `m − 1 → m`, is mapped
by `x ↦ κ_m(φ_{m−1}(x))` onto the coric (Gaussian) monoid. -/
def lgpKummer (m : ℤ) : lgpMonoid (C.link (m - 1)) C.gen ≃* splitMonoid C.gen :=
  (lgpEquiv (C.link (m - 1)) C.gen).trans (C.gaussKummer m)

@[simp] lemma coe_lgpKummer (m : ℤ) (x : lgpMonoid (C.link (m - 1)) C.gen) (j : Fin n) :
    (C.lgpKummer m x : Fin n → k) j = C.kum m ((C.link (m - 1)).φ ((x : Fin n → k) j)) := rfl

/-- **The splitting monoids are vertically coric**: the Kummer images of `Ψ⊥` of every level are
the one coric splitting monoid (an equality, not only the inclusion of upper
semi-compatibility). -/
theorem image_perpKummer (r : ℕ) (m : ℤ) :
    piMap (C.kum m) '' (perpMonoid r C.gen : Set (Fin n → k)) = perpMonoid r C.gen :=
  image_piMap_eq _ _ (fun _ hx => map_mem_perpMonoid _ (C.kum_gen m) hx)
    (fun _ hx => map_mem_perpMonoid _ (C.kum_symm_gen m) hx)

/-- The Gaussian monoids are vertically coric. -/
theorem image_gaussKummer (m : ℤ) :
    piMap (C.kum m) '' (splitMonoid C.gen : Set (Fin n → k)) = splitMonoid C.gen :=
  image_piMap_eq _ _
    (fun _ hx => map_mem_splitMonoid _ (C.kum_cont_symm m) (C.kum_gen m) hx)
    (fun _ hx => map_mem_splitMonoid _ (by simpa using C.kum_cont m) (C.kum_symm_gen m) hx)

/-- **The Kummer isomorphisms of the Gaussian monoids preserve the norms of the components**:
`‖κ_m(u·g_j^N)‖ = ‖u·g_j^N‖` (the unit portion goes to units, the generator is fixed). -/
theorem norm_kum_of_mem_splitMonoid (m : ℤ) {x : Fin n → k} (hx : x ∈ splitMonoid C.gen)
    (j : Fin n) : ‖C.kum m (x j)‖ = ‖x j‖ := by
  obtain ⟨u, hu, N, rfl⟩ := hx
  simp only [map_mul, map_pow, C.kum_gen, norm_mul, hu,
    norm_ringEquiv_eq_one (C.kum m) (C.kum_cont_symm m) hu]

/-- **The Kummer isomorphisms preserve the degrees of the Gaussian monoids** (the realified
value-group portion, P19's capsule-average `avgDeg`): the value-group portion of the LGP-monoids
undergoes no distortion along the vertical lines. -/
theorem avgDeg_kum_of_mem_splitMonoid (m : ℤ) {x : Fin n → k} (hx : x ∈ splitMonoid C.gen) :
    avgDeg (piMap (C.kum m) x) = avgDeg x := by
  unfold avgDeg
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [piMap_apply, C.norm_kum_of_mem_splitMonoid m hx j]

/-- The degrees of the LGP-monoids: the Kummer isomorphism `κ_m ∘ φ_{m−1}` of an LGP-monoid
preserves degrees. -/
theorem avgDeg_lgpKummer (m : ℤ) (x : lgpMonoid (C.link (m - 1)) C.gen) :
    avgDeg (C.lgpKummer m x : Fin n → k) = avgDeg (piMap (C.link (m - 1)).φ (x : Fin n → k)) := by
  have hx : piMap (C.link (m - 1)).φ (x : Fin n → k) ∈ splitMonoid C.gen := x.2
  exact C.avgDeg_kum_of_mem_splitMonoid m hx

/-- **The log-Kummer correspondence of the splitting monoids**: the totality of the Kummer
images of `Ψ⊥` of all levels is the coric `Ψ⊥` (and is in particular invariant under the
translation of the column). -/
theorem perpLogKummer (r : ℕ) :
    (⋃ m : ℤ, piMap (C.kum m) '' (perpMonoid r C.gen : Set (Fin n → k))) = perpMonoid r C.gen := by
  simp only [image_perpKummer, Set.iUnion_const]

section LogKill

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- **Theorem 3.11(ii)(b) / Proposition 3.5(ii)(c): mutual compatibility of the Kummer
isomorphisms of the splitting monoids with the log-links.** An element of `Ψ⊥` of level `m`
whose label-`j` component lies in the domain of the log-link `m → m + 1` is a diagonal root of
unity, and its log-link image, read in the coric field through `κ_{m+1}`, is `0`. -/
theorem perp_compat (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {r : ℕ} (hr : r ≠ 0) (m : ℤ)
    {x : Fin n → k} (hx : x ∈ perpMonoid r C.gen) {j : Fin n} (h : ‖x j - 1‖ < 1) :
    (x = fun _ => x j) ∧ x j ^ r = 1 ∧ C.kum (m + 1) ((C.link m).toFun (x j)) = 0 := by
  obtain ⟨h1, h2⟩ := perp_unit C.strict hr hx (norm_eq_one_of_norm_sub_one_lt h)
  refine ⟨h1, h2, ?_⟩
  rw [(C.link m).perp_toFun_eq_zero hp hpk C.strict hr hx h, map_zero]

/-- **The action of the related portion is the identity** ("addition by zero, i.e. no
indeterminacy"): the log-link image of an element of `Ψ⊥` in the domain acts on the coric
`I^Q` (additively, after the log-link) trivially. -/
theorem perp_compat_action (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {r : ℕ} (hr : r ≠ 0) (m : ℤ)
    {x : Fin n → k} (hx : x ∈ perpMonoid r C.gen) {j : Fin n} (h : ‖x j - 1‖ < 1) (y : k) :
    y + C.kum (m + 1) ((C.link m).toFun (x j)) = y := by
  rw [(C.perp_compat hp hpk hr m hx h).2.2, add_zero]

end LogKill

/-- The elements of `Ψ⊥` outside the torsion are not in the domain of any log-link. -/
theorem perp_not_mem_domain {r : ℕ} (hr : r ≠ 0) {ζ : k} (hζ : ζ ^ r = 1) {N : ℕ} (hN : 0 < N)
    (j : Fin n) : ¬ ‖ζ * C.gen j ^ N - 1‖ < 1 := fun h =>
  (perp_norm_lt_one C.strict hr hζ hN j).ne (norm_eq_one_of_norm_sub_one_lt h)

/-- The column translated by one step. -/
def shift : LGPColumn k n :=
  { C.toLogColumn.shift with
    gen := C.gen
    strict := C.strict
    kum_gen := fun m => C.kum_gen (m + 1) }

theorem shift_toLogColumn : C.shift.toLogColumn = C.toLogColumn.shift := rfl

end LGPColumn

/-! ### The tautological vertical line -/

/-- The tautological vertical line with Gaussian data `g` (identity Kummer isomorphisms,
tautological log-links). -/
def LGPColumn.taut {n : ℕ} (g : Fin n → k) (hg : IsStrictGen g) : LGPColumn k n where
  link _ := LocalLogLink.taut
  kum _ := RingEquiv.refl k
  kum_cont _ := continuous_id
  kum_cont_symm _ := continuous_id
  gen := g
  strict := hg
  kum_gen _ _ := rfl

end

end LogLink

end Iut
