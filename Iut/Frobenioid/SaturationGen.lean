/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Saturation

/-!
# Inflation along a surjection onto a discrete group: criteria

For a continuous surjection `φ : H →* Q` onto a group `Q` with the discrete topology and a
`Q`-module `M` (`H` acting through `φ`, `Saturation.Pull φ M`):

* `infl₁_injective`, `infl₁Z_injective`: inflation `H¹(Q, −) → H¹(H, −)` is injective;
* `infl₁_surjective`, `infl₁Z_surjective`: it is surjective if every cocycle of `H` vanishes on
  `ker φ`;
* `infl₂_surjective`: `H²(Q, M) → H²(H, M)` is surjective if every class has a representative
  invariant under right translation by `ker φ × ker φ`.

These are the group-theoretic inputs for the existence of `(N, H)`-saturated objects
([FrdII], Remark 2.2.1).
-/

namespace Iut

namespace Frobenioid

namespace Saturation

open groupCohomology

variable {H Q : Type*} [Group H] [TopologicalSpace H] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (φ : H →* Q) (hφ : Continuous φ) (hφs : Function.Surjective φ)

section H1

variable (M : Type*) [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [MulDistribMulAction Q M]

omit [DiscreteTopology Q] in
include hφs in
/-- **Inflation is injective** in degree one. -/
theorem infl₁_injective : Function.Injective (infl₁ φ hφ M) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using ContH1.induction_on with | h c => ?_
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨m, hm⟩ := (ContH1.mk_eq_one_iff _).mp hx
  rw [Subgroup.mem_bot, ContH1.mk_eq_one_iff]
  refine ⟨m, fun q => ?_⟩
  obtain ⟨h, rfl⟩ := hφs q
  exact hm h

include hφs in
/-- **Inflation is surjective** in degree one if every cocycle vanishes on `ker φ`. -/
theorem infl₁_surjective
    (hker : ∀ d : ContH1.cocycles H (Pull φ M), ∀ k ∈ φ.ker, (d : H → Pull φ M) k = 1) :
    Function.Surjective (infl₁ φ hφ M) := by
  intro x
  induction x using ContH1.induction_on with | h d => ?_
  let s := Function.surjInv hφs
  have hs : ∀ q, φ (s q) = q := Function.surjInv_eq hφs
  have hd : ∀ h k, k ∈ φ.ker → (d : H → Pull φ M) (h * k) = (d : H → Pull φ M) h := by
    intro h k hk
    rw [ContH1.isMulCocycle₁ d h k, hker d k hk, smul_one, one_mul]
  have hds : ∀ h, (d : H → Pull φ M) (s (φ h)) = (d : H → Pull φ M) h := by
    intro h
    have hk : h⁻¹ * s (φ h) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, map_inv, inv_mul_cancel]
    have := hd h _ hk
    rwa [mul_inv_cancel_left] at this
  let c : Q → M := fun q => (d : H → Pull φ M) (s q)
  have hcc : IsMulCocycle₁ c := by
    intro q q'
    dsimp only [c]
    have e : (d : H → Pull φ M) (s (q * q')) = (d : H → Pull φ M) (s q * s q') := by
      rw [← hds (s q * s q'), map_mul, hs, hs]
    have key : ∀ (h : H) (m : Pull φ M), h • m = (φ h • (@id M m) : M) := fun _ _ => rfl
    rw [e, ContH1.isMulCocycle₁ d, key, hs]
    rfl
  refine ⟨ContH1.mk ⟨c, continuous_of_discreteTopology, hcc⟩, ?_⟩
  change ContH1.mk _ = _
  congr 1
  exact Subtype.ext (funext fun h => hds h)

end H1

section H1Z

variable (n : ℕ)

omit [DiscreteTopology Q] in
include hφs in
/-- **Inflation is injective** in degree one, coefficients `ℤ/n`. -/
theorem infl₁Z_injective : Function.Injective (infl₁Z φ hφ n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using ContH1.induction_on with | h c => ?_
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨m, hm⟩ := (ContH1.mk_eq_one_iff _).mp hx
  rw [Subgroup.mem_bot, ContH1.mk_eq_one_iff]
  refine ⟨m, fun q => ?_⟩
  obtain ⟨h, rfl⟩ := hφs q
  exact hm h

include hφs in
/-- **Inflation is surjective** in degree one, coefficients `ℤ/n`, if every character of `H`
vanishes on `ker φ`. -/
theorem infl₁Z_surjective
    (hker : ∀ d : ContH1.cocycles H (ZTriv n), ∀ k ∈ φ.ker, (d : H → ZTriv n) k = 1) :
    Function.Surjective (infl₁Z φ hφ n) := by
  intro x
  induction x using ContH1.induction_on with | h d => ?_
  let s := Function.surjInv hφs
  have hs : ∀ q, φ (s q) = q := Function.surjInv_eq hφs
  have hd : ∀ h k, k ∈ φ.ker → (d : H → ZTriv n) (h * k) = (d : H → ZTriv n) h := by
    intro h k hk
    rw [ContH1.isMulCocycle₁ d h k, hker d k hk, smul_one, one_mul]
  have hds : ∀ h, (d : H → ZTriv n) (s (φ h)) = (d : H → ZTriv n) h := by
    intro h
    have hk : h⁻¹ * s (φ h) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, map_inv, inv_mul_cancel]
    have := hd h _ hk
    rwa [mul_inv_cancel_left] at this
  let c : Q → ZTriv n := fun q => (d : H → ZTriv n) (s q)
  have hcc : IsMulCocycle₁ c := by
    intro q q'
    dsimp only [c]
    have e : (d : H → ZTriv n) (s (q * q')) = (d : H → ZTriv n) (s q * s q') := by
      rw [← hds (s q * s q'), map_mul, hs, hs]
    rw [e, ContH1.isMulCocycle₁ d]
    rfl
  refine ⟨ContH1.mk ⟨c, continuous_of_discreteTopology, hcc⟩, ?_⟩
  change ContH1.mk _ = _
  congr 1
  exact Subtype.ext (funext fun h => hds h)

end H1Z

section H2

variable (M : Type*) [CommGroup M] [MulDistribMulAction Q M]

include hφs in
/-- **Inflation is surjective** in degree two if every class has a representative invariant
under right translation by `ker φ × ker φ`. -/
theorem infl₂_surjective
    (hrep : ∀ x : ContH2 H (Pull φ M), ∃ c : ContH2.cocycles H (Pull φ M), ContH2.mk c = x ∧
      ∀ h h' k k', k ∈ φ.ker → k' ∈ φ.ker → c (h * k, h' * k') = c (h, h')) :
    Function.Surjective (infl₂ φ hφ M) := by
  intro x
  obtain ⟨c, rfl, hc⟩ := hrep x
  let s := Function.surjInv hφs
  have hs : ∀ q, φ (s q) = q := Function.surjInv_eq hφs
  have hk : ∀ h, h⁻¹ * s (φ h) ∈ φ.ker := fun h => by
    rw [MonoidHom.mem_ker, map_mul, hs, map_inv, inv_mul_cancel]
  have hcs : ∀ h h', c (s (φ h), s (φ h')) = c (h, h') := fun h h' => by
    have := hc h h' _ _ (hk h) (hk h')
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at this
  let cb : Q × Q → M := fun qq => c (s qq.1, s qq.2)
  have hcb : IsMulCocycle₂ cb := by
    intro q q' q''
    dsimp only [cb]
    have e1 : c (s (q * q'), s q'') = c (s q * s q', s q'') := by
      rw [← hcs (s q * s q') (s q''), map_mul, hs, hs, hs]
    have e2 : c (s q, s (q' * q'')) = c (s q, s q' * s q'') := by
      rw [← hcs (s q) (s q' * s q''), map_mul, hs, hs, hs]
    have key : ∀ (h : H) (m : Pull φ M), h • m = (φ h • (@id M m) : M) := fun _ _ => rfl
    have := ContH2.isMulCocycle₂ c (s q) (s q') (s q'')
    rw [key, hs] at this
    rw [e1, e2]
    exact this
  refine ⟨ContH2.mk ⟨cb, IsLocallyConstant.of_discrete _, hcb⟩, ?_⟩
  change ContH2.mk _ = _
  congr 1
  exact ContH2.cocycles_ext fun h h' => hcs h h'

end H2

section Reps

variable {G M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction G M']

/-- If `k` acts trivially on `M'` and all chosen representative cocycles of `H¹(G, M')` vanish at
`k`, then every cocycle with values in `M ≅ M'` vanishes at `k`. -/
theorem cocycle_eq_one_of_reps (e : M ≃* M') (he : Continuous e)
    (hes : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (r : ContH1 G M' → ContH1.cocycles G M') (hr : ∀ c, ContH1.mk (r c) = c) {k : G}
    (hk1 : ∀ m' : M', k • m' = m') (hk2 : ∀ c, (r c : G → M') k = 1)
    (d : ContH1.cocycles G M) : (d : G → M) k = 1 := by
  let d' := ContH1.cocyclesMap (MonoidHom.id G) continuous_id e.toMonoidHom he hes d
  obtain ⟨m, hm⟩ := (ContH1.mk_eq_mk_iff _ _).mp (hr (ContH1.mk d'))
  have h1 : k • m / m = (r (ContH1.mk d') : G → M') k / (d' : G → M') k := hm k
  rw [hk1, div_self', hk2, one_div, eq_comm, inv_eq_one] at h1
  apply e.injective
  rw [map_one]
  exact h1

end Reps

end Saturation

end Frobenioid

end Iut
