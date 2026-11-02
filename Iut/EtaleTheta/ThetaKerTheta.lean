/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaProp13
import Iut.EtaleTheta.TemperedLevelTwo

/-!
# [EtTh] Prop. 1.3: the theta class comes from `(Π^tp_Y)^Θ` — the reduction to a Heisenberg
condition (MR14, run 14)

[EtTh] Prop. 1.3 (ET l.1137–1270, l.1201–1210): the étale theta class `η^Θ` is a class
`∈ H¹((Π^tp_Y)^Θ, ½Δ_Θ)`; here `Π^tp_Y ↠ (Π^tp_Y)^Θ` is the quotient whose kernel is the kernel
`Kθ` of `Δ^tp_X ↠ (Δ^tp_X)^Θ = Δ_X^Θ = Δ_X/[Δ_X, [Δ_X, Δ_X]]` (ET l.480–503). Restricted to
`Π^tp_Ÿ` the class therefore **vanishes on `Π^tp_Ÿ ∩ Kθ`**; this is the hypothesis `hη13` of
MR15's Cor. 2.19(i) (`Env/CycRigidity.lean`, `modelEnv_kerTheta`).

In the finite-level model of `MR14-plan.md` (route R-alg) the class at the level `j` is the
Kummer class of a unit `η_j` of the level `L_j ⊇ L_X`, and the statement becomes: the Kummer
character `y ↦ y(α)/α` (`α^n = η_j`) kills `[[Δ, Δ], Δ]`, `Δ = H_X ∩ Gal(Ω/k̄(t))`. This file
proves it from a **Heisenberg condition** on the level, the finite-level form of "the Kummer
extension of `Θ̈` has a Galois group of nilpotency class `2` over `k̄·L_X`" (the theta group):
for some intermediate field `B ⊇ L_j`

* (F1) the commutators of `Δ` fix `B` (`k̄·B` is abelian over `k̄·L_X`; for the theta levels `B`
  is the field of the `[2N]`-covering, whose geometric Galois group is `E[2N]`), and
* (F2) for every `σ ∈ Δ`, `σ(η_j) = κ_σ · h_σ^n · η_j` with `κ_σ ∈ k̄` and `h_σ ∈ B` (the
  translation formula of [EtTh] Prop. 1.4(ii), `Θ̈(q^{a/2}Ü) = (−1)^a q^{−a²/2} Ü^{−2a} Θ̈(Ü)`,
  at the level: `Ü^{−2a}` acquires an `n`-th root on the `[2N]`-covering).

Then `y(α)/α` is a root of unity (`y` fixes `η_j`), hence fixed by `Δ`, and `c(α)/α` is
`κ_σ^{1/n}·h_σ` up to a root of unity, hence fixed by every `y ∈ Δ` fixing `B`; a two-line
computation (`commutator_apply_eq_self`) shows that `[y, c]` fixes `α` for all such `y` and all
`c ∈ Δ`, so `[[Δ, Δ], Δ] ⊆ [Δ ∩ Gal(Ω/B), Δ]` fixes `α`.

## Main results

* `commutator_apply_eq_self`, `commutator_commutator_le_stabilizer` (field automorphisms, no
  Galois theory).
* `deltaPi_smul_mu`: `Δ_U` acts trivially on `μ_n`.
* `map_thetaKernel_deltaH`, `thetaKernel_deltaH_fixes`: the theta kernel of `Δ = deltaH D_X`
  fixes `α` under (F1), (F2).
* `ambientKernel_le_ambientKernel_level`: `⟨⟨S_X⟩⟩ ⊆ ⟨⟨S_{L'}⟩⟩` for an étale level `L'`.
* **`thetaKernelTemp`**: `Kθ = Ker(Δ^tp_X ↠ Δ_X^Θ)` as a subgroup of `Π^tp_X`.
* **`classAt_eq_one_of_thetaKernel`**: under C1, (F1) and (F2) at the level `j`, for every
  `γ ∈ Π^tp_Ÿ ∩ Kθ` the theta class `classAt η j n` evaluated at `γ` is `1` — the form in which
  MR15's `hη13` consumes Prop. 1.3 (for any cocycle `c` representing the class, `c γ = 1`,
  `ContH1.evalTriv_mk`).

(F1) and (F2) for the theta system of `exists_thetaClassTemp` are **not proved here**; see
`MR14-plan.md`, run 14.
-/

open scoped commutatorElement

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### Commutators of field automorphisms fixing a Kummer generator -/

section Core

variable {P Ω : Type*} [Field P] [Field Ω] [Algebra P Ω]

theorem algEquiv_apply_inv_apply (c : Ω ≃ₐ[P] Ω) (x : Ω) : c (c⁻¹ x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem algEquiv_inv_apply_apply (c : Ω ≃ₐ[P] Ω) (x : Ω) : c⁻¹ (c x) = x := by
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- If `β = c⁻¹(α)/α` is fixed by `y` and `f = y(α)/α` is fixed by `c`, then `c y c⁻¹` and `y`
agree on `α`. -/
theorem conj_apply_eq_of {y c : Ω ≃ₐ[P] Ω} {α : Ω} (hα : α ≠ 0)
    (hβ : y (c⁻¹ α / α) = c⁻¹ α / α) (hf : c (y α / α) = y α / α) :
    (c * y * c⁻¹) α = y α := by
  set β := c⁻¹ α / α with hβdef
  set f := y α / α with hfdef
  have h1 : c⁻¹ α = β * α := by rw [hβdef, div_mul_cancel₀ _ hα]
  have h2 : y α = f * α := by rw [hfdef, div_mul_cancel₀ _ hα]
  have h3 : c β * c α = α := by rw [← map_mul, ← h1, algEquiv_apply_inv_apply]
  calc (c * y * c⁻¹) α = c (y (c⁻¹ α)) := rfl
    _ = c (y β * y α) := by rw [h1, map_mul]
    _ = c β * c α * c f := by rw [hβ, h2, map_mul, map_mul]; ring
    _ = y α := by rw [h3, hf, h2]; ring

/-- **The commutator `[y, c]` fixes `α`** if `c⁻¹(α)/α` is fixed by `y` and `y⁻¹(α)/α` by `c`. -/
theorem commutator_apply_eq_self {y c : Ω ≃ₐ[P] Ω} {α : Ω} (hα : α ≠ 0)
    (hβ : y (c⁻¹ α / α) = c⁻¹ α / α) (hf : c (y⁻¹ α / α) = y⁻¹ α / α) :
    ⁅y, c⁆ α = α := by
  have hβ' : y⁻¹ (c⁻¹ α / α) = c⁻¹ α / α := by
    conv_lhs => rw [← hβ]
    exact algEquiv_inv_apply_apply y _
  have h := conj_apply_eq_of hα hβ' hf
  rw [commutatorElement_def]
  calc (y * c * y⁻¹ * c⁻¹) α = y ((c * y⁻¹ * c⁻¹) α) := rfl
    _ = α := by rw [h, algEquiv_apply_inv_apply]

/-- **`[[G, G], G]` fixes `α`** for a subgroup `G` of `Aut(Ω/P)` and a subgroup `A` containing
`[G, G]`, if `y(α)/α` is fixed by `G` for `y ∈ A` and `c(α)/α` is fixed by `A` for `c ∈ G`. -/
theorem commutator_commutator_le_stabilizer {G A : Subgroup (Ω ≃ₐ[P] Ω)} (hGA : ⁅G, G⁆ ≤ A)
    {α : Ω} (hα : α ≠ 0) (h1 : ∀ y ∈ A, ∀ c ∈ G, c (y α / α) = y α / α)
    (h2 : ∀ c ∈ G, ∀ y ∈ A, y (c α / α) = c α / α) :
    ⁅⁅G, G⁆, G⁆ ≤ MulAction.stabilizer (Ω ≃ₐ[P] Ω) α := by
  refine (Subgroup.commutator_mono hGA le_rfl).trans ?_
  rw [Subgroup.commutator_le]
  intro y hy c hc
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  exact commutator_apply_eq_self hα (h2 c⁻¹ (inv_mem hc) y hy) (h1 y⁻¹ (inv_mem hy) c hc)

end Core

/-! ### The Galois model: `Δ`, its theta kernel and `μ_n` -/

section Galois

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- `Δ = deltaH D` as a subgroup of `Aut(Ω/k(t))`. -/
def deltaAut : Subgroup (Ω ≃ₐ[K₀ k t] Ω) := (deltaH D).map D.H.subtype

variable {D} in
omit [IsGalois (K₀ k t) Ω] in
theorem mem_deltaAut_iff {σ : Ω ≃ₐ[K₀ k t] Ω} :
    σ ∈ deltaAut D ↔ ∃ h : σ ∈ D.H, (⟨σ, h⟩ : D.H) ∈ deltaH D := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, hτ⟩
  · rintro ⟨h, hσ⟩
    exact ⟨⟨σ, h⟩, hσ, rfl⟩

/-- `Δ ↪ Aut(Ω/k(t))`. -/
def deltaHToAut : deltaH D →* (Ω ≃ₐ[K₀ k t] Ω) := D.H.subtype.comp (deltaH D).subtype

omit [IsGalois (K₀ k t) Ω] in
theorem range_deltaHToAut : (deltaHToAut D).range = deltaAut D := by
  rw [deltaHToAut, MonoidHom.range_comp, Subgroup.range_subtype, deltaAut]

omit [IsGalois (K₀ k t) Ω] in
/-- **The theta kernel of `Δ`, in `Aut(Ω/k(t))`**: `[[Δ, Δ], Δ]`. -/
theorem map_thetaKernel_deltaH :
    (thetaKernel (deltaH D)).map (deltaHToAut D) =
      ⁅⁅deltaAut D, deltaAut D⁆, deltaAut D⁆ := by
  rw [thetaKernel, commutator_def, Subgroup.map_commutator, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, range_deltaHToAut]

/-- `Δ ↠ Δ_U`, `σ ↦ σ̄`. -/
def deltaHToPi : deltaH D →* deltaPi D :=
  ((QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)).comp (deltaH D).subtype).codRestrict _
    fun σ => mk_mem_deltaPi_iff.2 σ.2

theorem deltaHToPi_surjective : Function.Surjective (deltaHToPi D) := by
  rintro ⟨x, hx⟩
  induction x using QuotientGroup.induction_on with
  | H σ => exact ⟨⟨σ, mk_mem_deltaPi_iff.1 hx⟩, rfl⟩

/-- `[[Δ_U, Δ_U], Δ_U]` is the image of `[[Δ, Δ], Δ]`. -/
theorem map_thetaKernel_deltaHToPi :
    (thetaKernel (deltaH D)).map (deltaHToPi D) = thetaKernel (deltaPi D) := by
  rw [thetaKernel, thetaKernel, commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (deltaHToPi_surjective D)]

omit [IsGalois (K₀ k t) Ω] in
variable {D} in
theorem deltaAut_fix_algebraic {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ deltaAut D) {x : Ω} (hx : IsAlgebraic k x) : σ x = x := by
  obtain ⟨h, hσ⟩ := mem_deltaAut_iff.1 hσ
  exact mem_deltaH_iff.1 hσ x hx

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
theorem isAlgebraic_of_pow_eq_one {ζ : Ω} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    IsAlgebraic k ζ := by
  refine ⟨Polynomial.X ^ n - 1, Polynomial.X_pow_sub_C_ne_zero hn 1, ?_⟩
  simp [hζ]

variable {D} in
/-- **`Δ_U` acts trivially on `μ_n`** (roots of unity are algebraic over `k`). -/
theorem deltaPi_smul_mu {g : Pi D} (hg : g ∈ deltaPi D) (n : ℕ) [NeZero n]
    (ζ : Mu n Ω) : g • ζ = ζ := by
  induction g using QuotientGroup.induction_on with
  | H σ =>
    have hσ : σ ∈ deltaH D := mk_mem_deltaPi_iff.1 hg
    change σ • ζ = ζ
    apply Mu.ext
    apply Units.ext
    exact mem_deltaH_iff.1 hσ _ (isAlgebraic_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne n))
      (by rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]))

end Galois

/-! ### (F1) + (F2) ⇒ `[[Δ, Δ], Δ]` fixes the Kummer generator -/

section Heisenberg

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

omit [IsGalois (K₀ k t) Ω] in
/-- **The Heisenberg condition fixes the Kummer generator**: if the commutators of `Δ` fix `B`
(F1) and every `σ ∈ Δ` multiplies `α^n ∈ B` by `κ_σ·h_σ^n` with `κ_σ` algebraic over `k` and
`h_σ ∈ B` (F2), then `[[Δ, Δ], Δ]` fixes `α`. -/
theorem thetaKernel_fixes {B : IntermediateField (K₀ k t) Ω} {n : ℕ} (hn : 0 < n) {α : Ω}
    (hα : α ≠ 0) (hαB : α ^ n ∈ B)
    (hF1 : ∀ σ ∈ deltaAut D, ∀ τ ∈ deltaAut D, ∀ x ∈ B, ⁅σ, τ⁆ x = x)
    (hF2 : ∀ σ ∈ deltaAut D, ∃ κ : Ω, IsAlgebraic k κ ∧ ∃ h ∈ B, σ (α ^ n) = κ * h ^ n * α ^ n)
    {x : Ω ≃ₐ[K₀ k t] Ω} (hx : x ∈ ⁅⁅deltaAut D, deltaAut D⁆, deltaAut D⁆) : x α = α := by
  set A := deltaAut D ⊓ B.fixingSubgroup
  have hGA : ⁅deltaAut D, deltaAut D⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    refine ⟨show ⁅σ, τ⁆ ∈ deltaAut D from ?_,
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 (hF1 σ hσ τ hτ)⟩
    rw [commutatorElement_def]
    exact (deltaAut D).mul_mem ((deltaAut D).mul_mem ((deltaAut D).mul_mem hσ hτ)
      ((deltaAut D).inv_mem hσ)) ((deltaAut D).inv_mem hτ)
  have hpos : α ^ n ≠ 0 := pow_ne_zero _ hα
  have h1 : ∀ y ∈ A, ∀ c ∈ deltaAut D, c (y α / α) = y α / α := by
    intro y hy c hc
    have hyB : y (α ^ n) = α ^ n :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy.2 _ hαB
    refine deltaAut_fix_algebraic hc (isAlgebraic_of_pow_eq_one hn ?_)
    rw [div_pow, ← map_pow, hyB, div_self hpos]
  have h2 : ∀ c ∈ deltaAut D, ∀ y ∈ A, y (c α / α) = c α / α := by
    intro c hc y hy
    obtain ⟨κ, hκ, h, hhB, hch⟩ := hF2 c hc
    have hh : h ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hn), mul_zero, zero_mul, map_pow] at hch
      exact hα ((map_eq_zero_iff c c.injective).1
        ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hn)).1 hch))
    set w := c α / α / h with hw
    have hwpow : w ^ n = κ := by
      rw [hw, div_pow, div_pow, ← map_pow, hch]
      field_simp
    have hwalg : IsAlgebraic k w := IsAlgebraic.of_pow hn (hwpow ▸ hκ)
    have hyw : y w = w := deltaAut_fix_algebraic hy.1 hwalg
    have hyh : y h = h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy.2 _ hhB
    have e : c α / α = w * h := by rw [hw, div_mul_cancel₀ _ hh]
    rw [e, map_mul, hyw, hyh]
  have := commutator_commutator_le_stabilizer hGA hα h1 h2 hx
  rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this

end Heisenberg

/-! ### The étale level: `⟨⟨S_X⟩⟩ ⊆ ⟨⟨S_{L'}⟩⟩` -/

section Levels

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  [IsGalois (K₀ k t) Ω] [CharZero k]
  {LX : IntermediateField (K₀ k t) Ω} (hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))

/-- **`⟨⟨S_X⟩⟩ ⊆ ⟨⟨S_{L'}⟩⟩` for an étale level `L' ⊇ L_X`**: the conjugates of the inertia
elements at the places centred on `X` fix `L'` (`ambientKernel_le_level`), so they are inertia
elements of `L'` at the same places. -/
theorem ambientKernel_le_ambientKernel_level (L' : IntermediateField (K₀ k t) Ω)
    (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) (hle : LX ≤ L')
    (het : letI := levelAlgebra ht hLX hL' hle
      Algebra.Etale (fieldData ht LX hLX).R (fieldData ht L' hL').R) :
    GaloisPi1.ambientKernel (fieldData ht LX hLX).H (fieldData ht LX hLX).S ≤
      GaloisPi1.ambientKernel (fieldData ht L' hL').H (fieldData ht L' hL').S := by
  have hS : ∀ s ∈ (fieldData ht LX hLX).S, s ∈ (fieldData ht L' hL').H := fun s hs =>
    ambientKernel_le_level ht hLX L' hL' hle het
      (Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨1, one_mem _, s, hs, by simp⟩))
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, s, hs, rfl⟩
  have hc := conj_mem_S (D := fieldData ht LX hLX) (σ := h⁻¹)
    (fun g hg => by rw [inv_inv]; exact mul_mem (mul_mem hh hg) (inv_mem hh)) hs
  rw [inv_inv] at hc
  have hc' : h * s * h⁻¹ ∈ (fieldData ht L' hL').S := ⟨hS _ hc, hc.2⟩
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure ⟨1, one_mem _, _, hc', by simp⟩)

end Levels

/-! ### `Kθ = Ker(Δ^tp_X ↠ Δ_X^Θ)` and the vanishing of the theta class on `Π^tp_Ÿ ∩ Kθ` -/

section Temp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **`Kθ = Ker(Δ^tp_U ↠ Δ_U^Θ)`** ([EtTh] l.480–503): the elements of `Π^tp_U` whose image in
`Π_U` lies in `Δ_U` and maps to `1` in `Δ_U^Θ = Δ_U/[Δ_U, [Δ_U, Δ_U]]`, i.e. the preimage of the
theta kernel of `Δ_U`. For `U = X` this is `Ker(Π^tp_Y ↠ (Π^tp_Y)^Θ)`, the subgroup `Kθ` of
MR15's Cor. 2.19(i). -/
def thetaKernelTemp : Subgroup (TempPi D O V hV) :=
  ((thetaKernel (deltaPi D)).map (deltaPi D).subtype).comap (tempToPi D O V hV)

variable {D O V hV} in
theorem tempToPi_mem_deltaPi {γ : TempPi D O V hV} (hγ : γ ∈ thetaKernelTemp D O V hV) :
    tempToPi D O V hV γ ∈ deltaPi D := by
  obtain ⟨x, -, hx⟩ := hγ
  rw [← hx]
  exact x.2

variable {D O V hV} in
theorem mem_thetaKernelTemp_iff {γ : TempPi D O V hV} :
    γ ∈ thetaKernelTemp D O V hV ↔
      ∃ hγ : tempToPi D O V hV γ ∈ deltaPi D, (⟨_, hγ⟩ : deltaPi D) ∈ thetaKernel (deltaPi D) := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hm : tempToPi D O V hV γ ∈ deltaPi D := by
      rw [← hxe]
      exact x.2
    have hx' : (⟨_, hm⟩ : deltaPi D) = x := Subtype.ext hxe.symm
    exact ⟨hm, hx' ▸ hx⟩
  · rintro ⟨hγ, h1⟩
    exact ⟨_, h1, rfl⟩

end Temp


/-! ### The Kummer class at an element fixing the Kummer root -/

section KummerEval

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

/-- `κ_n(u)` evaluated at the image of `h ∈ H` fixing the chosen root `u^{1/n}` is `1`. -/
theorem evalTriv_kummerMap_eq_one (D : Pi1.Orbifold.GaloisData k t) (n : ℕ) [NeZero n]
    (u : units D) (h : D.H) (hh : ∀ ζ : Mu n Ω, (h : Pi D) • ζ = ζ)
    (hfix : (h : Ω ≃ₐ[K₀ k t] Ω) ((kummerRoot n (F D) Ω (u : (F D)ˣ) : Ωˣ) : Ω) =
      kummerRoot n (F D) Ω (u : (F D)ˣ)) :
    ContH1.evalTriv (h : Pi D) hh (kummerMap D n u) = 1 := by
  have hh' : ∀ ζ : Mu n Ω, h • ζ = ζ := hh
  calc ContH1.evalTriv (h : Pi D) hh (kummerMap D n u)
      = ContH1.evalTriv h hh' (inflMu D n (kummerMap D n u)) :=
        (ContH1.evalTriv_map (QuotientGroup.mk' _) QuotientGroup.continuous_mk (MonoidHom.id _)
          continuous_id (fun _ _ => rfl) h hh' hh (kummerMap D n u)).symm
    _ = ContH1.evalTriv h hh' (resMu D n (kummer n (F D) Ω u)) := by
        rw [inflation_kummerMap]
    _ = 1 := by
        rw [kummer_eq (u : (F D)ˣ) _ (kummerRoot_pow n (F D) Ω (u : (F D)ˣ))]
        rw [resMu, KummerTheory.Curve.res, ContH1.map_mk, ContH1.evalTriv_mk]
        simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply, kummerCocycle_apply]
        apply Mu.ext
        apply Units.ext
        simp [val_kummerFun, AlgEquiv.smul_units_def, toGalF_apply, hfix]

end KummerEval

/-! ### The theta class on `Π^tp_Ÿ ∩ Kθ` -/

section Main

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

omit het in
/-- `Π^tp_Ÿ ∩ Kθ` acts trivially on `μ_n`. -/
theorem thetaKernelTemp_smul_mu {γ : piYddotX V hV T hL}
    (hγ : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈
      thetaKernelTemp (fieldData ht LX hLX) O V hV)
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) : γ • ζ = ζ := by
  change tempToPi (fieldData ht LX hLX) O V hV (γ : TempPi (fieldData ht LX hLX) O V hV) • ζ = ζ
  exact deltaPi_smul_mu (tempToPi_mem_deltaPi hγ) n ζ

theorem evalTriv_congr {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
    [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M] (x : ContH1 G M)
    {g g' : G} (e : g = g') (hg : ∀ m : M, g • m = m) (hg' : ∀ m : M, g' • m = m) :
    ContH1.evalTriv g hg x = ContH1.evalTriv g' hg' x := by
  subst e
  rfl

variable (η : ∀ j, units (fieldData ht (L j) (hL j)))

/-- **[EtTh] Prop. 1.3, "the class comes from `(Π^tp_Y)^Θ`", from the Heisenberg condition**
(generic levels): under C1, if at the level `j` the commutators of `Δ = H_X ∩ Gal(Ω/k̄(t))` fix
a field `B ⊇ L_j` (F1) and every `σ ∈ Δ` multiplies `η_j` by `κ_σ·h_σ^n` with `κ_σ ∈ k̄`,
`h_σ ∈ B` (F2), then the theta class `classAt η j n ∈ H¹(Π^tp_Ÿ, μ_n)` vanishes on
`Π^tp_Ÿ ∩ Kθ`, `Kθ = Ker(Δ^tp_X ↠ Δ_X^Θ)`: this is MR15's `hη13` (for every cocycle `c` of the
class, `c γ = evalTriv γ (mk c) = 1`). -/
theorem classAt_eq_one_of_thetaKernel (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (B : IntermediateField (K₀ k t) Ω) (hLB : L j ≤ B)
    (hF1 : ∀ σ ∈ deltaAut (fieldData ht LX hLX), ∀ τ ∈ deltaAut (fieldData ht LX hLX),
      ∀ x ∈ B, ⁅σ, τ⁆ x = x)
    (hF2 : ∀ σ ∈ deltaAut (fieldData ht LX hLX), ∃ κ : Ω, IsAlgebraic k κ ∧ ∃ h ∈ B,
      σ ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω)) =
        κ * h ^ n *
          (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω))
    (γ : piYddotX V hV T hL)
    (hγ : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈
      thetaKernelTemp (fieldData ht LX hLX) O V hV) :
    ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) (classAt η hC1 j n) = 1 := by
  set DX := fieldData ht LX hLX with hDX
  set Dj := fieldData ht (L j) (hL j) with hDj
  set u : (F Dj)ˣ := (η j : (F Dj)ˣ) with hu
  set α : Ωˣ := kummerRoot n (F Dj) Ω u with hαdef
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hαpow : ((α : Ω)) ^ n = ((u : F Dj) : Ω) := by
    have := congrArg (fun x : Ωˣ => (x : Ω)) (kummerRoot_pow n (F Dj) Ω u)
    simpa using this
  have huL : ((u : F Dj) : Ω) ∈ L j := by
    rw [← fieldData_L ht (L j) (hL j)]
    exact (u : F Dj).2
  -- the element of `[[Δ, Δ], Δ]` below `γ`
  have hγ' := hγ
  obtain ⟨x, hxK, hxe⟩ := hγ'
  rw [← map_thetaKernel_deltaHToPi] at hxK
  obtain ⟨k0, hk0, rfl⟩ := hxK
  have hkA : deltaHToAut DX k0 ∈ ⁅⁅deltaAut DX, deltaAut DX⁆, deltaAut DX⁆ := by
    rw [← map_thetaKernel_deltaH]
    exact ⟨k0, hk0, rfl⟩
  have hfixk : deltaHToAut DX k0 (α : Ω) = α :=
    thetaKernel_fixes hn α.ne_zero (by rw [hαpow]; exact hLB huL) hF1
      (fun σ hσ => by rw [hαpow]; exact hF2 σ hσ) hkA
  have hcomm_le : ⁅deltaAut DX, deltaAut DX⁆ ≤ (L j).fixingSubgroup := by
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact hF1 σ hσ τ hτ y (hLB hy)
  have hGG : ⁅deltaAut DX, deltaAut DX⁆ ≤ deltaAut DX := by
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
  have hkj : deltaHToAut DX k0 ∈ Dj.H :=
    hcomm_le ((Subgroup.commutator_mono hGG le_rfl) hkA)
  -- a lift of the image of `γ` in `Π_{L_j}`
  obtain ⟨hj, hhj⟩ := QuotientGroup.mk_surjective (tempToPi Dj O V hV (toLevel hC1 j γ))
  have e1 : tempToPi DX O V hV (γ : TempPi DX O V hV) =
      ((Subgroup.inclusion (fieldData_H_antitone ht hLX (hL j) (hX j).out) hj : DX.H) :
        Pi DX) := by
    conv_lhs => rw [← temperedPi1Map_toLevel hC1 j γ]
    rw [tempToPi_temperedPi1Map ht hLX (hL j) (hX j).out O V hV, ← hhj]
    rfl
  have e2 : ((Subgroup.inclusion (fieldData_H_antitone ht hLX (hL j) (hX j).out) hj : DX.H) :
      Pi DX) = ((k0 : DX.H) : Pi DX) := by
    rw [← e1, ← hxe]
    rfl
  rw [QuotientGroup.eq] at e2
  have hker : ((hj : Ω ≃ₐ[K₀ k t] Ω))⁻¹ * deltaHToAut DX k0 ∈
      GaloisPi1.ambientKernel Dj.H Dj.S :=
    ambientKernel_le_ambientKernel_level ht hLX (L j) (hL j) (hX j).out (het j) e2
  have hfix2 := eq_of_mem_ambientKernel (D := Dj) hker (η j).2 hn hαpow
  have hjfix : (hj : Ω ≃ₐ[K₀ k t] Ω) (α : Ω) = α := by
    rw [AlgEquiv.mul_apply, hfixk] at hfix2
    calc (hj : Ω ≃ₐ[K₀ k t] Ω) (α : Ω)
        = (hj : Ω ≃ₐ[K₀ k t] Ω) (((hj : Ω ≃ₐ[K₀ k t] Ω))⁻¹ (α : Ω)) := by rw [hfix2]
      _ = α := algEquiv_apply_inv_apply _ _
  -- evaluate the class
  have hsm : ∀ ζ : Mu n Ω, tempToPi Dj O V hV (toLevel hC1 j γ) • ζ = ζ := fun ζ => by
    have h := toLevel_smul hC1 j n γ ζ
    simp only [MonoidHom.id_apply] at h
    exact h.trans (thetaKernelTemp_smul_mu hγ n ζ)
  have hstep : ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) (classAt η hC1 j n) =
      ContH1.evalTriv (tempToPi Dj O V hV (toLevel hC1 j γ)) hsm (kummerMap Dj n (η j)) := by
    rw [classAt, kummerMapTempered, MonoidHom.comp_apply]
    induction kummerMap Dj n (η j) using ContH1.induction_on with
    | h c =>
      simp only [resLevel, ContH1.map_mk, ContH1.evalTriv_mk, ContH1.cocyclesMap_apply,
        MonoidHom.id_apply]
      rfl
  rw [hstep, evalTriv_congr _ hhj.symm hsm (fun ζ => hhj ▸ hsm ζ)]
  exact evalTriv_kummerMap_eq_one Dj n (η j) hj _ hjfix

end Main

/-! ### The concrete system: the class comes from `(Π^tp_Y)^Θ` -/

section Concrete

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem deltaAut_fix_hemiL {σ : Ω ≃ₐ[K₀ K τ] Ω}
    (hσ : σ ∈ deltaAut (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
      (hemiL_open t))) : ∀ z ∈ (hemiData t.tateCurve).L, σ z = z := by
  obtain ⟨h, -⟩ := mem_deltaAut_iff.mp hσ
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h

set_option maxHeartbeats 2000000 in
-- destructuring `exists_etaleThetaSystem` (concrete Tate-curve levels) is slow to unify
include h2 in
/-- **[EtTh] Prop. 1.3, "the class comes from `(Π^tp_Y)^Θ`", for the theta system** (tempered,
under C1 only): for the system of `exists_thetaClassTemp`, for every base point `V` over `O`,
under C1, every level `j` and `n ∣ N_j`, the class `classAt η j n` (`= thetaClassTemp η n`)
evaluates to `1` on `Π^tp_Ÿ ∩ Kθ`, `Kθ = Ker(Δ^tp_X ↠ Δ_X^Θ)`. This is MR15's `hη13`
(obligation 8): (F1) is `commutator_fix_mulByNField` for `B = L_{2N_j}`, (F2) is the translation
formula of `exists_etaleThetaSystem` (`translation_level`). -/
theorem exists_thetaClassTemp_thetaKernel :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (j n : ℕ) [NeZero n],
        n ∣ 2 * (j + 1) →
        ∀ (γ : piYddotX V hV (tateDataX O hO hs h12) hL)
          (hγ : (γ : TempPi (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
              (hemiL_open t)) O V hV) ∈
            thetaKernelTemp (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
              (hemiL_open t)) O V hV),
          ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) (classAt η hC1 j n) = 1 := by
  obtain ⟨L, hL, h₁, η, het, -, -, -, htr, -, hF, -⟩ := exists_etaleThetaSystem h2 h12 hs
  haveI hX : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j) := fun j => ⟨h₁ j⟩
  haveI het' : ∀ j, Algebra.Etale (DX t).R
      (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R := fun j =>
    etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) (L j) (hL j) (het j)
  refine ⟨L, hL, hX, het', η, htr, fun V hV => thetaClassCompatible_tate h12 hs O hO V hV htr,
    fun V hV hC1 j n _ hn γ hγ => ?_⟩
  obtain ⟨hLB, hF2⟩ := hF j n hn
  refine classAt_eq_one_of_thetaKernel η hC1 j n _ hLB (fun σ hσ ρ hρ x hx => ?_)
    (fun σ hσ => ?_) γ hγ
  · exact commutator_fix_mulByNField t.tateCurve _ (deltaAut_fix_hemiL hσ) (deltaAut_fix_hemiL hρ)
      (fun z hz => deltaAut_fix_algebraic hσ hz) (fun z hz => deltaAut_fix_algebraic hρ hz) x hx
  · obtain ⟨c, h, hh, e⟩ := hF2 σ (deltaAut_fix_hemiL hσ)
    exact ⟨algebraMap K Ω c, isAlgebraic_algebraMap c, h, hh, e⟩

set_option maxHeartbeats 4000000 in
-- destructuring `exists_etaleThetaSystem` (concrete Tate-curve levels) is slow to unify
include h2 in
/-- **[EtTh] Prop. 1.3 for ONE theta system** (decision D25: all conclusions of
`exists_thetaClassTemp_thetaKernel`, `exists_thetaClassTemp_cusps` and
`exists_thetaClassTemp_deltaTheta` for the same system `L, η`):
* the transitions and the compatibility of the classes;
* (Prop. 1.3, "the class comes from `(Π^tp_Y)^Θ`", under C1 only) `classAt η j n` vanishes on
  `Π^tp_Ÿ ∩ Kθ`;
* at every place `W ⊇ K` over the cusp there are base points `V ≤ W` over `O`, and for each,
  under C1, the theta class maps the cusp inertia onto
  `μ_n`;
* under the debt `CuspInertiaWeil` (G5c+G5d): there is `e : Δ_Θ ≃* Ẑ(1)` such that the cusp
  inertia maps onto `Δ_Θ`, every cusp inertia element maps into `Δ_Θ`, and the theta class on it
  is the `n`-th component of `e` (Prop. 1.3 on `Δ_Θ`);
* (MR15 obligation 13b, run 18) `Gal(Ω/L_X)` maps every level into itself (so
  `normal_piYddotX` applies);
* (TFGD runs 2, 4) under the geometric input (Z_2) (`ZM 0`, `Π^tp_Y ≤ Π^tp_{K(E_{q²})}`): Z at
  `j = 0` (`PiYIndexTwoAt`, `[Π^tp_Y : Π^tp_Ÿ] ≤ 2`, `piYIndexTwoAt_zero_of_zM`), and
  (MR15 obligation 13c(i)+(ii), [EtTh] Prop. 1.5(iii) mod `l`, run 18) under C1, given `g₁` with
  `χ(g₁) = 1` (MR15 13a): for `l` odd with `2l ∣ N_j`, every lift `σ ∈ Gal(Ω/L_X)` of the
  image of `γ ∈ Π^tp_X` with `χ(γ) = l·m` moves `η_j` by an `l`-th power,
  `σ η_j = (d·y)^l·η_j` (`d ∈ K`, `y ∈ L_j`);
* (TFGD run 3, lead decision D-T5) C1 for this system from the geometric inputs (Z_{N_j})
  (`ZM`, `Π^tp_Y ≤ Π^tp_{K(E_{q^{N_j}})}` for all `j`; `levelsDominated_of_zM`, using
  `L j ≤ L 0 ⊔ K(E_{q^{N_j}})`). -/
theorem exists_thetaClassTemp_prop13 :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))
      (hL0 : ∀ (W : ValuationSubring Ω), (∀ c : K, algebraMap K Ω c ∈ W) → τ ∉ W →
        InertiaFixesLevel (transcendental_tau t.tateCurve) (hemiL_open t) (L 0) W),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (j n : ℕ) [NeZero n],
        n ∣ 2 * (j + 1) →
        ∀ (γ : piYddotX V hV (tateDataX O hO hs h12) hL)
          (hγ : (γ : TempPi (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
              (hemiL_open t)) O V hV) ∈
            thetaKernelTemp (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
              (hemiL_open t)) O V hV),
          ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) (classAt η hC1 j n) = 1) ∧
      (∀ (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W),
        (∃ V : ValuationSubring Ω, V ≤ W ∧ V.comap (algebraMap K Ω) = O) ∧
        ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (hVW : V ≤ W)
          (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL)
          (n : ℕ) [NeZero n] (ζ : Mu n Ω), ∃ σ : inertiaGroup (DX t).R W,
            ContH1.evalTriv ⟨_, inertiaToTempered_mem_piYddotX V hV _ hL hVW σ (hL0 W hk hτ σ)⟩
                (inertiaToTempered_piYddotX_smul hk hVW σ (hL0 W hk hτ σ) n)
                (thetaClassTemp η hC1 n) = ζ) ∧
      (CuspInertiaWeil (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
          (hemiL_open t)) →
        ∃ (e : thetaSubD (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
            (hemiL_open t)) ≃* ZHatOne (F (fieldData (transcendental_tau t.tateCurve)
              (hemiData t.tateCurve).L (hemiL_open t))) Ω),
        ∀ (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W) (hτ : τ ∉ W),
          (∀ δ ∈ thetaSubD (fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
              (hemiL_open t)), ∃ σ, inertiaToTheta _ hk σ = δ) ∧
          ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (hVW : V ≤ W)
            (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL)
            (σ : inertiaGroup (DX t).R W),
            ∃ hσ : inertiaToTheta _ hk (inertiaX σ) ∈ thetaSubD (fieldData
                (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L (hemiL_open t)),
              ∀ (n : ℕ) [NeZero n],
                ContH1.evalTriv ⟨_, inertiaToTempered_mem_piYddotX V hV _ hL hVW σ (hL0 W hk hτ σ)⟩
                    (inertiaToTempered_piYddotX_smul hk hVW σ (hL0 W hk hτ σ) n)
                    (thetaClassTemp η hC1 n) =
                  ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ :
                    KummerIndex (F (fieldData (transcendental_tau t.tateCurve)
                      (hemiData t.tateCurve).L (hemiL_open t)))) (e ⟨_, hσ⟩)) ∧
      (∀ j, ∀ σ ∈ (hemiData t.tateCurve).L.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ZM h2 h12 O hO hs 0 V hV → PiYIndexTwoAt V hV (tateDataX O hO hs h12) hL 0 ∧
        ∀ (j l : ℕ), Odd l → 2 * l ∣ 2 * (j + 1) → LevelsDominated V hV (tateDataX O hO hs h12) hL →
        ∀ (g₁ : TempPi (DX t) O V hV),
          Iut.EtaleTheta.TateObject.charN (A := (DX t).A)
            (tateDataX O hO hs h12) V hV g₁ = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (γ : TempPi (DX t) O V hV) (m : ℤ),
          Iut.EtaleTheta.TateObject.charN (A := (DX t).A)
            (tateDataX O hO hs h12) V hV γ = Multiplicative.ofAdd ((l : ℤ) * m) →
        ∀ σ : (DX t).H, (σ : Pi (DX t)) = tempToPi (DX t) O V hV γ →
          MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
            (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
              F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) l) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        (∀ j, ZM h2 h12 O hO hs j V hV) → LevelsDominated V hV (tateDataX O hO hs h12) hL) := by
  obtain ⟨L, hL, h₁, η, het, -, -, -, htr, hcusp, hF, hL02, hsup, w, hw1, hw2, -, hw4⟩ :=
    exists_etaleThetaSystem h2 h12 hs
  haveI hX : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j) := fun j => ⟨h₁ j⟩
  haveI het' : ∀ j, Algebra.Etale (DX t).R
      (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R := fun j =>
    etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) (L j) (hL j) (het j)
  have hcc : ∀ (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W →
      ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (hVW : V ≤ W)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (n : ℕ) [NeZero n],
        ClassAtCusp V hV (tateDataX O hO hs h12) hL η hC1 (n - 1) n hk hVW :=
    fun W hk hτ V hV hVW hC1 n _ => classAt_cuspTame η hC1 (n - 1) n hk hVW
      (hcusp (n - 1) W hk hτ n
        ⟨2, by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))]; ring⟩)
  have hL0 : ∀ (W : ValuationSubring Ω), (∀ c : K, algebraMap K Ω c ∈ W) → τ ∉ W →
      InertiaFixesLevel (transcendental_tau t.tateCurve) (hemiL_open t) (L 0) W :=
    fun W hk hτ => inertiaFixesLevel_of_le_mulByNField_two hL02 hk hτ
  refine ⟨L, hL, hX, het', η, hL0, htr,
    fun V hV => thetaClassCompatible_tate h12 hs O hO V hV htr,
    fun V hV hC1 j n _ hn γ hγ => ?_, fun W hk hτ => ⟨exists_le_comap_eq W hk O,
      fun V hV hVW hC1 n _ ζ => classAt_cusp_surjective η hC1 (n - 1) n hk hVW (hL0 W hk hτ)
        (hcc W hk hτ V hV hVW hC1 n) ζ⟩, fun hG5 => ?_, hw2,
    fun V hV hZ2 => ⟨piYIndexTwoAt_zero_of_zM h2 h12 O hO hs hZ2 hL02,
      fun j l hl hlN hC1 g₁ hg₁ γ m hγ σ hσ => ?_⟩,
    fun V hV hZ => levelsDominated_of_zM h2 h12 O hO hs hZ hsup⟩
  · obtain ⟨hLB, hF2⟩ := hF j n hn
    refine classAt_eq_one_of_thetaKernel η hC1 j n _ hLB (fun σ hσ ρ hρ x hx => ?_)
      (fun σ hσ => ?_) γ hγ
    · exact commutator_fix_mulByNField t.tateCurve _ (deltaAut_fix_hemiL hσ)
        (deltaAut_fix_hemiL hρ) (fun z hz => deltaAut_fix_algebraic hσ hz)
        (fun z hz => deltaAut_fix_algebraic hρ hz) x hx
    · obtain ⟨c, h, hh, e⟩ := hF2 σ (deltaAut_fix_hemiL hσ)
      exact ⟨algebraMap K Ω c, isAlgebraic_algebraMap c, h, hh, e⟩
  · obtain ⟨e, he⟩ := hG5
    refine ⟨e, fun W hk hτ => ⟨(he W hk hτ).1, fun V hV hVW hC1 σ => ?_⟩⟩
    obtain ⟨hσ, -⟩ := (he W hk hτ).2 (inertiaX σ)
    refine ⟨hσ, fun n _ => ?_⟩
    obtain ⟨hσ', H⟩ := classAt_deltaTheta η hC1 (n - 1) n hk hVW (he W hk hτ).2 (hL0 W hk hτ)
      (hcc W hk hτ V hV hVW hC1 n) σ
    exact H
  · exact of_mem_piXdd (T := tateDataX O hO hs h12) j (w j) (fun σ hσ => hw1 j σ hσ)
      (fun σ => MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
        (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
          F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) l) l
      (fun σ ρ τ' h hτ' => hw4 j l hl hlN σ ρ τ' h hτ')
      (piYIndexTwoAt_of_levelsDominated (piYIndexTwoAt_zero_of_zM h2 h12 O hO hs hZ2 hL02)
        hC1 j) hg₁ hγ σ hσ

end Concrete

end Iut.EtaleTheta
