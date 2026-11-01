/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaQuotient
import ContinuousKummerTheory.Curve.CuspResidue
import ContinuousKummerTheory.Curve.InertiaZHat

/-!
# The geometric group `Δ`, its theta quotient, and cusp inertia (MR14, run 13: G5a, G5b)

[EtTh] §1 (ET l.455–475) and §2 (ET l.2262–2282): for the once-punctured elliptic curve `X`
one writes `Δ_X ⊆ Π_X` for the geometric fundamental group (the kernel of `Π_X ↠ G_K`),
`Δ_X^Θ = Δ_X/[Δ_X, [Δ_X, Δ_X]]` and `Δ_Θ ⊆ Δ_X^Θ` for the image of `∧² Δ_X^ell`
(`= [Δ_X, Δ_X]` modulo `[Δ_X, [Δ_X, Δ_X]]`); the inertia group `I_x ⊆ D_x ⊆ Π_X` of the cusp
maps isomorphically onto `Δ_Θ` (ET l.2272–2274), and `Δ_Θ ≅ Ẑ(1)` (ET l.475).

This file sets this up in the Galois model of `pi1`/continuous-kummer-theory (any Galois datum
`D` of a curve over `k`, `Ω` algebraically closed, `k̄ ⊆ Ω` the algebraic closure of `k`):

* **G5a.** `deltaH D := H ∩ Gal(Ω/k̄(t))`, the kernel of `hToGk : H → G_k` (`mem_deltaH_iff`:
  the elements of `H` fixing every element of `Ω` algebraic over `k`), and
  `deltaPi D := Ker(Π_U ↠ G_k)` (`piToGk`), the geometric fundamental group `Δ_U`
  (`mk_mem_deltaPi_iff`). Its theta quotient `deltaTheta D := thetaQuot (deltaPi D)`
  (`ThetaQuotient.lean`), the quotient map `toDeltaTheta`, and **`thetaSubD D`** `= Δ_Θ`, the
  image of `[Δ_U, Δ_U]` in `Δ_U^Θ` (central, `thetaSubD_le_center`).
* **G5b.** `inertiaH_le_deltaH`: `I_W ∩ H ≤ Δ` for every place `W ⊇ k` (inertia fixes `k̄`,
  continuous-kummer-theory `inertia_fix_algebraic`); `inertiaToDelta : I_W ∩ H →* Δ_U` and
  `inertiaToTheta : I_W ∩ H →* Δ_U^Θ`.
* **The debt G5c + G5d** (`MR14-plan.md`, owner PI1TOP/MR13): `CuspInertiaWeil D`, a `Prop`
  definition used only as an explicitly named theorem hypothesis (rule 4; it is not proved
  here). See its docstring. `CuspInertiaWeil.exists_tame`, `.surjective`, `.injective` unpack it.
-/

open scoped commutatorElement

open AffOrbicurve IntermediateField

noncomputable section

universe u

namespace Iut.EtaleTheta

open KummerTheory KummerTheory.Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-! ### G5a: `Δ = H ∩ Gal(Ω/k̄(t))`, `Δ_U`, `Δ_U^Θ` and `Δ_Θ` -/

/-- **`Δ = H ∩ Gal(Ω / k̄(t))`** (G5a): the kernel of the restriction `H → G_k = Gal(k̄/k)`. -/
def deltaH : Subgroup D.H := (hToGk D).ker

variable {D} in
omit [IsGalois (K₀ k t) Ω] in
/-- `σ ∈ Δ` iff `σ` fixes every element of `Ω` algebraic over `k`. -/
theorem mem_deltaH_iff {σ : D.H} :
    σ ∈ deltaH D ↔ ∀ x : Ω, IsAlgebraic k x → (σ : Ω ≃ₐ[K₀ k t] Ω) x = x := by
  constructor
  · intro h x hx
    have h1 : hToGk D σ = 1 := h
    have := algebraMap_hToGk_apply D σ ⟨x, mem_algebraicClosure_iff.mpr hx⟩
    rw [h1] at this
    exact this.symm
  · intro h
    change hToGk D σ = 1
    ext x
    change algebraMap (kbar k Ω) Ω (hToGk D σ x) = (x : Ω)
    rw [algebraMap_hToGk_apply]
    exact h x (mem_algebraicClosure_iff.mp x.2)

/-- **The geometric fundamental group `Δ_U = Ker(Π_U ↠ G_k)`** (G5a). -/
def deltaPi : Subgroup (Pi D) := (piToGk D).ker

variable {D} in
theorem mk_mem_deltaPi_iff {σ : D.H} : (σ : Pi D) ∈ deltaPi D ↔ σ ∈ deltaH D := by
  change piToGk D (σ : Pi D) = 1 ↔ hToGk D σ = 1
  rw [piToGk_mk]

/-- **The theta quotient `Δ_U^Θ = Δ_U / [Δ_U, [Δ_U, Δ_U]]`** ([EtTh] §1). -/
abbrev deltaTheta : Type u := thetaQuot (deltaPi D)

/-- `Δ_U ↠ Δ_U^Θ`. -/
def toDeltaTheta : deltaPi D →* deltaTheta D := QuotientGroup.mk' (thetaKernel (deltaPi D))

theorem toDeltaTheta_surjective : Function.Surjective (toDeltaTheta D) :=
  QuotientGroup.mk'_surjective _

/-- **`Δ_Θ ⊆ Δ_U^Θ`**: the image of `[Δ_U, Δ_U]` (for `Δ_U^∧` free on two generators, the image
of `∧² Δ^ell`, [EtTh] l.470–475). -/
def thetaSubD : Subgroup (deltaTheta D) :=
  (commutator (deltaPi D)).map (toDeltaTheta D)

/-- `Δ_Θ` is the commutator subgroup of `Δ_U^Θ`. -/
theorem thetaSubD_eq_commutator : thetaSubD D = commutator (deltaTheta D) := by
  rw [thetaSubD, commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (toDeltaTheta_surjective D)]

/-- `Δ_Θ` is central in `Δ_U^Θ` (class `2`). -/
theorem thetaSubD_le_center : thetaSubD D ≤ Subgroup.center (deltaTheta D) := by
  rw [thetaSubD_eq_commutator, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  exact (thetaQuot_isClassTwo (deltaPi D)).mem_center a b

/-! ### G5b: cusp inertia lies in `Δ` -/

variable {D} {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)

include hk in
/-- **G5b: `I_W ∩ H ≤ Δ`** for every place `W ⊇ k` (inertia fixes `k̄`). -/
theorem inertiaH_le_deltaH : inertiaH D W ≤ deltaH D := fun _ hσ =>
  mem_deltaH_iff.2 fun _ hx => inertia_fix_algebraic hk hσ hx

variable (D) in
include hk in
/-- `I_W ∩ H → Δ_U`. -/
def inertiaToDelta : inertiaH D W →* deltaPi D :=
  ((QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)).comp (inertiaH D W).subtype).codRestrict _
    fun σ => mk_mem_deltaPi_iff.2 (inertiaH_le_deltaH hk σ.2)

@[simp]
theorem coe_inertiaToDelta (σ : inertiaH D W) :
    (inertiaToDelta D hk σ : Pi D) = ((σ : D.H) : Pi D) := rfl

variable (D) in
include hk in
/-- **`I_W ∩ H → Δ_U^Θ`** (the cusp inertia in the theta quotient, ET l.2272). -/
def inertiaToTheta : inertiaH D W →* deltaTheta D :=
  (toDeltaTheta D).comp (inertiaToDelta D hk)

/-! ### The debt G5c + G5d -/

variable (D) in
/-- The (G5d) clause of `CuspInertiaWeil` at one place `W` for a given `e : Δ_Θ ≃* Ẑ(1)`: every
`σ ∈ I_W ∩ H` maps into `Δ_Θ`, and `e(σ)` is the tame character of every uniformiser of every
finite `F' ⊇ F` fixed by `I_W ∩ H` (a `Prop` definition, part of the debt statement only). -/
def WeilTameAt (e : thetaSubD D ≃* ZHatOne (F D) Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W) :
    Prop :=
  ∀ σ : inertiaH D W, ∃ hσ : inertiaToTheta D hk σ ∈ thetaSubD D,
        ∀ (F' : IntermediateField (K₀ k t) Ω), F D ≤ F' →
          (∀ τ : inertiaH D W, ∀ x ∈ F', ((τ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = x) →
          ∀ π' ∈ F', π' ≠ 0 → W.valuation π' < 1 →
          (∀ f ∈ F', W.valuation f < 1 → W.valuation f ≤ W.valuation π') →
          ∀ (n : ℕ) (hn : (n : F D) ≠ 0) (α : Ωˣ), (α : Ω) ^ n = π' →
            ((σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) α / α =
              ((Mu.val (ZHatOne.proj ⟨n, hn⟩ (e ⟨_, hσ⟩)) : Ωˣ) : Ω)

variable (D) in
/-- **Debt G5c + G5d** (`MR14-plan.md`, run 13; owner PI1TOP/MR13 — Riemann existence
`Δ_X^∧ ≅ Π̂_{1,1}` with the cusp loop `↦ c₁ = [a₁, b₁]⁻¹`, and the Weil pairing
`∧² Δ^ell ≅ ∧² T(E) ≅ Ẑ(1)`). This `Prop` is **not proved**; it enters only as an explicitly
named theorem hypothesis.

Statement: there is an isomorphism `e : Δ_Θ ≃* Ẑ(1)` (the natural one, [EtTh] l.475) such that
for every cusp place `W ⊇ k` of `Ω` over `t = ∞`:
* (G5c) the cusp inertia `I_W ∩ H` maps into `Δ_Θ ⊆ Δ_U^Θ` and onto it ([EtTh] l.2272–2274:
  `I_x ⊆ D_x` maps isomorphically onto `Δ_Θ`);
* (G5d) `e` agrees with the tame character: for every finite `F' ⊇ F` such that `I_W ∩ H`
  fixes `F'` (`F'` unramified over `F` at `W`), every uniformiser `π'` of `W ∩ F'`, every
  `σ ∈ I_W ∩ H`, `n > 0` and `n`-th root `α` of `π'`, `σ(α)/α` is the `n`-th component of
  `e(σ)`. (For `F' = F` this is the comparison of the Weil pairing with the tame character; for
  unramified `F'` the uniformisers of `W ∩ F'` and `W ∩ F` differ by units, which have trivial
  Kummer characters on inertia — an elementary part included so that the statement can be used
  at the theta levels.) -/
def CuspInertiaWeil : Prop :=
  ∃ e : thetaSubD D ≃* ZHatOne (F D) Ω,
    ∀ (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W), t ∉ W →
      (∀ δ ∈ thetaSubD D, ∃ σ : inertiaH D W, inertiaToTheta D hk σ = δ) ∧ WeilTameAt D e hk

variable [IsSepClosed Ω]

/-- **`CuspInertiaWeil` at `F' = F`**: `e ∘ (I_W ∩ H → Δ_Θ)` is the tame character `θ_π` of any
uniformiser `π` of `W ∩ F`. -/
theorem CuspInertiaWeil.exists_tame {e : thetaSubD D ≃* ZHatOne (F D) Ω}
    {W : ValuationSubring Ω} {hk : ∀ c : k, algebraMap k Ω c ∈ W}
    (h : WeilTameAt D e hk)
    {π : (F D)ˣ} (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω))
    (σ : inertiaH D W) :
    ∃ hσ : inertiaToTheta D hk σ ∈ thetaSubD D, e ⟨_, hσ⟩ = tameChar hk π σ := by
  obtain ⟨hσ, H⟩ := h σ
  refine ⟨hσ, Subtype.ext (funext fun i => ?_)⟩
  have hπ0 : ((π : F D) : Ω) ≠ 0 := fun h0 => π.ne_zero (Subtype.ext h0)
  have hn0 : i.n ≠ 0 := fun h0 => i.ne_zero (by rw [h0]; simp)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : F D) : Ω) (Nat.pos_of_ne_zero hn0)
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hα
    exact hπ0 hα.symm
  have h1 := H (F D) le_rfl (fun τ x hx => fixes_of_mem_F τ.1.2 ⟨x, hx⟩) _ (π : F D).2 hπ0 hπW
    hπ i.n i.ne_zero (Units.mk0 α hα0) hα
  have h2 := val_proj_tameChar hk π σ i (Units.mk0 α hα0) (Units.ext (by simpa using hα))
  apply Subtype.ext
  apply Units.ext
  change ((Mu.val (ZHatOne.proj i (e ⟨_, hσ⟩)) : Ωˣ) : Ω) =
    ((Mu.val (ZHatOne.proj i (tameChar hk π σ)) : Ωˣ) : Ω)
  rw [h2, ← h1]

/-- **`I_W ∩ H ≅ Δ_Θ`** under `CuspInertiaWeil` (injectivity, from the tame character,
[AbsTopIII] Prop. 1.4(i)): two inertia elements with the same image in `Δ_U^Θ` agree. -/
theorem CuspInertiaWeil.injective {e : thetaSubD D ≃* ZHatOne (F D) Ω}
    {W : ValuationSubring Ω} {hk : ∀ c : k, algebraMap k Ω c ∈ W}
    (h : WeilTameAt D e hk)
    {π : (F D)ˣ} (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) :
    Function.Injective (inertiaToTheta D hk) := by
  intro σ τ hστ
  obtain ⟨hσ, eσ⟩ := CuspInertiaWeil.exists_tame h hπW hπ σ
  obtain ⟨hτ, eτ⟩ := CuspInertiaWeil.exists_tame h hπW hπ τ
  apply tameChar_injective hk hπW hπ
  rw [← eσ, ← eτ]
  exact congrArg e (Subtype.ext hστ)

end Iut.EtaleTheta
