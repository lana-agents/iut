/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.CocycleExtend
import Iut.EtaleTheta.Env.ThetaTower

/-!
# The curves `X̿, X̲, Y̲, Ÿ̲` and the `l`-th root of the étale theta class ([EtTh] §2, Layer B)

[EtTh] (text of `The Etale Theta Function…`, l.2186–2620, 2756–2775, 2880–2980) constructs from
`X = E_q ∖ {O}` and an odd `l`:

* `X̿ → X` (type `(1, ℤ/lℤ)`, Def. 2.1, Def. 2.5(i)): the covering of a quotient
  `Π̲^ell_X ↠ Q ≅ ℤ/l` that factors through `Π_X ↠ Ẑ` coming from `Π^tp_X ↠ ℤ`. Here
  **`piXdd V hV T l = χ̂⁻¹(lℤ)`**, `χ̂ : Π^tp_X → ℤ` the normalised character of the
  `ℤ`-covering `Y → X` (`TateObject.charN`, `χ/m` for the image `mℤ` of `TateObject.character`,
  `Π^tp_Y = Ker χ̂`).
* `X̲ → X̿` (type `(1, (ℤ/lℤ)^Θ)`, Prop. 2.2(ii), Def. 2.3): a splitting `s` of `D̲_x ↠ G_K`
  gives `Π_X̲ = ` the preimage of `Im(s_ι)·s(G_K)` in `Π_X̿`, i.e. the kernel of the cocycle
  `cX : Π_X̿ → Π̲_X̿/Im(s_ι) ≅ D̲_x = Δ̲_Θ ⋊ s(G_K) → Δ̲_Θ ≅ μ_l`. Here **`piXu hcX`** is the
  kernel of an arbitrary continuous cocycle `cX : Π^tp_X̿ → μ_l` (`cocycleKer`): the splitting is
  data. The theorems below hold for every `cX` whose restriction to `Π^tp_Ÿ` is the mod-`l`
  reduction of the representative of the theta class used (`hcXr`); [EtTh] l.2938–2945 says that
  the splitting determines the class `η̈^Θ ⊗ ℤ/l` on `Π^tp_Ÿ` in exactly this way ("a choice of
  `η̈^Θ` up to an `(O_K^×)^l`-multiple"). That such a `cX` exists for the theta class is
  [EtTh] Prop. 2.2(ii) + the text l.2938–2945 (via Prop. 1.5(ii)); it is a Layer-B debt
  (`MR15-plan.md`, obligation 13).

  **Caveat: `hcXr` does not determine `cX`.** Two cocycles with `hcXr` differ by a cocycle that
  is trivial on `Π^tp_Ÿ`; so `hcXr` says nothing about `cX` in the `lℤ`-direction (on lifts of a
  generator of `Π^tp_X̿/Π^tp_Y ≅ lℤ`, the deck group of `Y → X̿`). The theorems below hold for
  *every* `cX` with `hcXr`. **The `cX` of [EtTh]:** for a splitting `s` of `D̲_x ↠ G_K`,
  `cX(γ) = [γ] · s(γ|_{G_K})⁻¹ ∈ Δ̲_Θ ≅ μ_l`, where `[γ]` is the image of `γ` in
  `Π̲_X̿/Im(s_ι) ≅ D̲_x` (Prop. 2.2(ii)); it kills `Im(s_ι)`. By l.2938–2945 its restriction to
  `Π^tp_Ÿ` is the theta class mod `l` up to the Kummer class of a unit `u ∈ O_K^×`. Splittings
  form a torsor under `H¹(G_K, Δ̲_Θ) ≅ K^×/(K^×)^l`, and replacing `s` by its translate by
  `u⁻¹` multiplies that restriction by `κ(u)⁻¹`. So for a suitable `s`, [EtTh]'s `cX` satisfies
  `hcXr` for a representative of the theta class of `ThetaTemperedClass.lean` itself.
* `Y̲ = Y ×_X̿ X̲`, `Ÿ̲ = Ÿ ×_X̿ X̲` (l.2925–2931: the composites of `Y, Ÿ → C` with `C̲ → C`,
  degree `l` over `Y, Ÿ`): **`piYU = Π^tp_Y ∩ Π^tp_X̲`**, **`piYddU = Π^tp_Ÿ ∩ Π^tp_X̲`**,
  as subgroups of `Π^tp_X̲` (the ambient group of the environments of `X̲`).
* **The `l`-th root `η̈^Θ̲ ∈ H¹(Π^tp_Ÿ̲, l·Δ_Θ)`** (l.2950–2965), mod `N`: if `r` represents the
  theta class mod `lN` on `Π^tp_Ÿ`, then on `Π^tp_Ÿ̲ = Ker(cX) ∩ Π^tp_Ÿ` its values lie in
  `μ_N ⊆ μ_{lN}` (`rootCocycle`, `rootClass`); `rootCocycle_pow`, `rootClass_pow`: its image under
  `l·Δ_Θ ↪ Δ_Θ` (on `μ_N`: `ζ ↦ ζ^l`) is the restriction of the theta class mod `N`
  ("`η̈^Θ̲ ↦ η̈^Θ|_Ÿ̲`"). The cyclotome `l·Δ_Θ` of `X̲` is identified with `μ_N` mod `N` through
  this root (as `Δ_Θ` with `μ_N` through the class itself).
* The input subgroups of [EtTh] Cor. 2.19(i) for `X̲`: `thetaLU = Π^tp_Ÿ̲ ∩ (preimage of Δ_Θ)`,
  which is the preimage of `l·Δ_Θ` (the root class kills exactly `l·Δ_Θ` mod `l`), and
  `thetaKU = Π^tp_Ÿ̲ ∩ Ker(Δ^tp_X ↠ Δ_X^Θ)` (this contains `Π^tp_Ÿ̲ ∩ Ker(Δ_X̲ ↠ Δ_X̲^Θ)`; the
  algorithm only needs the root class to vanish on it, which it does by Prop. 1.3 for `X`).

## Main results

* `cyclotomicRigidity_thetaEnvU`: [EtTh] Cor. 2.19(i) for the model environment
  `thetaEnvU` (`Π^tp_Y̲[μ_N]`, `D_Y̲` from `Π^tp_X̲` and `K^×`, theta section of the root
  class) and the cyclotome `l·Δ_Θ`.
* `ker_autPY_inlY_eq_thetaEnvU`: automorphisms over the identity of `Π^tp_Y̲` act trivially on
  `μ_N` (the `μ`-part of Cor. 2.18(iv) for `X̲`).
* `discreteRigidity_thetaEnvU`: [EtTh] Cor. 2.19(ii) for the projective system of the
  environments of `X̲` (levels `N_n = (n+1)!`, root classes from compatible representatives of
  the theta classes mod `N_{n+l}`).
* `exists_thetaRep_inputs` (the Tate curve): for the theta system of
  `exists_thetaClassTemp_prop13`, the inputs `hr13` (Prop. 1.3, modulo C1) and the surjectivity
  of the root class on `thetaLU` (modulo C1, `CuspInertiaWeil`) and the
  `l`-th root property `rootClass_pow` for the theta classes.
* `exists_cX_of_invariant` (obligation 13, reduced): if `Π^tp_Ÿ ⊴ Π^tp_X̿`, `e ∈ Π^tp_Y ∖ Π^tp_Ÿ`
  with `Π^tp_Y = Π^tp_Ÿ ∪ Π^tp_Ÿ e`, `χ(g) = l`, and the conjugates of `r mod l` by `e` and `g` are
  cohomologous to `r mod l` (the `μ_2 × lℤ`-invariance of `θ mod l`, Prop. 1.5(iii)), then a
  splitting cocycle `cX` with `hcXr` exists (`CocycleExtend.lean`, `l` odd).
* `exists_thetaEnvU_rigidity` (the Tate curve): all conclusions for `X̲` (`EnvUConclusions`: the
  `l`-th root property, Cor. 2.19(i), the `μ`-part of Cor. 2.18(iv)) for one theta system, via the
  generic `envUConclusions_of` applied to `exists_thetaRep_inputs`; `Π^tp_Y ↠ G_k` (obligation 5)
  holds at base points under a place over the cusp (`surj_augT_of_ratPoint`, `cuspRatPoint`).
-/

open scoped commutatorElement

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

/-! ### Kernels of cocycles -/

section CocycleKer

variable {P μ : Type*} [Group P] [CommGroup μ] {φ : P →* MulAut μ}

theorem cocycle_apply_one {c : P → μ} (hc : IsCocycle φ c) : c 1 = 1 := by
  have h := hc 1 1
  simp only [mul_one, map_one, MulAut.one_apply] at h
  exact left_eq_mul.1 h

/-- **The kernel of a cocycle** `{g | c g = 1}`: the stabilizer of `1` for the twisted action
`g · m = c(g)·(g m)`; it is a subgroup. -/
def cocycleKer {c : P → μ} (hc : IsCocycle φ c) : Subgroup P where
  carrier := {g | c g = 1}
  one_mem' := cocycle_apply_one hc
  mul_mem' := fun {a b} (ha : c a = 1) (hb : c b = 1) => by
    change c (a * b) = 1
    rw [hc a b, ha, hb, map_one, one_mul]
  inv_mem' := fun {a} (ha : c a = 1) => by
    change c a⁻¹ = 1
    have h := hc a⁻¹ a
    rw [inv_mul_cancel, cocycle_apply_one hc, ha, map_one, mul_one] at h
    exact h.symm

theorem mem_cocycleKer {c : P → μ} (hc : IsCocycle φ c) {g : P} :
    g ∈ cocycleKer hc ↔ c g = 1 := Iff.rfl

theorem isOpen_cocycleKer [TopologicalSpace P] [TopologicalSpace μ] [DiscreteTopology μ]
    {c : P → μ} (hc : IsCocycle φ c) (hcc : Continuous c) :
    IsOpen (cocycleKer hc : Set P) :=
  (isOpen_discrete ({1} : Set μ)).preimage hcc

theorem cocycle_apply_inv {c : P → μ} (hc : IsCocycle φ c) (a : P) :
    c a⁻¹ = (φ a⁻¹ (c a))⁻¹ := by
  have h := hc a⁻¹ a
  rw [inv_mul_cancel, cocycle_apply_one hc] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **The kernel of a cocycle with finite values has finite index** (`P/Ker(c) ↪ μ`, `gK ↦ c g`). -/
theorem finiteIndex_cocycleKer [Finite μ] {c : P → μ} (hc : IsCocycle φ c) :
    (cocycleKer hc).FiniteIndex := by
  haveI : Finite (P ⧸ cocycleKer hc) := by
    refine Finite.of_injective (fun q : P ⧸ cocycleKer hc => Quotient.liftOn' q c ?_) ?_
    · intro a b hab
      have hab' : c (a⁻¹ * b) = 1 := QuotientGroup.leftRel_apply.1 hab
      have e : b = a * (a⁻¹ * b) := by group
      change c a = c b
      rw [e, hc, hab', map_one, mul_one]
    · intro q q' h
      induction q using QuotientGroup.induction_on with
      | H a =>
      induction q' using QuotientGroup.induction_on with
      | H b =>
      change c a = c b at h
      refine QuotientGroup.eq.2 ?_
      change c (a⁻¹ * b) = 1
      rw [hc, cocycle_apply_inv hc, ← h]
      exact inv_mul_cancel _
  exact Subgroup.finiteIndex_of_finite_quotient
end CocycleKer

/-! ### Roots of unity -/

section Val

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- The cyclotomic characters of different levels agree on common roots of unity. -/
theorem val_psiMu_eq {n m : ℕ} [NeZero n] [NeZero m] (σ : Gk k Ω) {ζ : Mu n Ω} {ζ' : Mu m Ω}
    (h : Mu.val ζ = Mu.val ζ') : Mu.val (psiMu n σ ζ) = Mu.val (psiMu m σ ζ') := by
  obtain ⟨z, rfl⟩ := (muEquiv (k := k) (Ω := Ω) n).surjective ζ
  obtain ⟨z', rfl⟩ := (muEquiv (k := k) (Ω := Ω) m).surjective ζ'
  have hinj : Function.Injective (Units.map (algebraMap (kbar k Ω) Ω : kbar k Ω →* Ω)) :=
    Units.map_injective (fun a b hab => (algebraMap (kbar k Ω) Ω).injective hab)
  have hz : Mu.val z = Mu.val z' := hinj h
  rw [psiMu_muEquiv, psiMu_muEquiv, muEquiv_apply, muEquiv_apply, val_muMap, val_muMap,
    Mu.val_smul, Mu.val_smul, hz]

/-- `Mu.transition` is transitive. -/
theorem transition_transition {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (hc : c ≠ 0)
    (ζ : Mu c Ω) :
    Mu.transition hab (Mu.transition hbc ζ) = Mu.transition (hab.trans hbc) ζ := by
  apply Mu.ext
  rw [Mu.val_transition, Mu.val_transition, Mu.val_transition, ← pow_mul]
  congr 1
  have hb : b ≠ 0 := fun hb => hc (Nat.eq_zero_of_zero_dvd (hb ▸ hbc))
  obtain ⟨d, rfl⟩ := hab
  obtain ⟨e, rfl⟩ := hbc
  have ha : a ≠ 0 := fun ha => hb (by simp [ha])
  have hd : d ≠ 0 := fun hd => hb (by simp [hd])
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), mul_assoc,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), mul_comm]

/-- `μ_{lN} ↠ μ_l` is `ζ ↦ ζ^N`. -/
theorem val_transition_mul {l N : ℕ} [NeZero l] (ζ : Mu (l * N) Ω) :
    Mu.val (Mu.transition (Dvd.intro N rfl : l ∣ l * N) ζ) = Mu.val ζ ^ N := by
  rw [Mu.val_transition, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne l))]

/-- `μ_{lN} ↠ μ_N` is `ζ ↦ ζ^l`. -/
theorem val_transition_mul' {l N : ℕ} [NeZero N] (ζ : Mu (l * N) Ω) :
    Mu.val (Mu.transition (Dvd.intro_left l rfl : N ∣ l * N) ζ) = Mu.val ζ ^ l := by
  rw [Mu.val_transition, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne N))]

theorem mul_levelN_dvd (l n : ℕ) : l * levelN n ∣ l * levelN (n + 1) :=
  mul_dvd_mul_left l (levelN_dvd n)

end Val

/-! ### `X̿`, `X̲`, `Y̲`, `Ÿ̲` and the root class (generic levels) -/

section Levels

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]

local notation "DXg" => fieldData ht LX hLX
local notation "PXg" => TempPi (fieldData ht LX hLX) O V hV
local notation "augg" => augT (fieldData ht LX hLX) O V hV
set_option quotPrecheck false in
local notation "PYg" => Iut.EtaleTheta.TateObject.piY
  (A := (fieldData ht LX hLX).A) T V hV
local notation "PYddg" => piYddotX V hV T hL

variable (V hV T) in
/-- **`Π^tp_X̿ = χ̂⁻¹(lℤ)`** ([EtTh] Def. 2.1, Def. 2.5(i): the quotient `Q ≅ ℤ/l` factors through
`Gal(Y/X) ≅ ℤ`; `χ̂ = TateObject.charN : Π^tp_X → ℤ` is the normalised character of `Y → X`,
`χ/m` for the image `mℤ` of `χ`, so that `χ̂` induces `Π^tp_X/Π^tp_Y ≅ ℤ`; TFGD run 2). -/
def piXdd (l : ℕ) : Subgroup PXg :=
  (Subgroup.zpowers (Multiplicative.ofAdd (l : ℤ))).comap
    (Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
theorem piY_le_piXdd (l : ℕ) : PYg ≤ piXdd V hV T l := fun γ hγ => by
  change _ ∈ Subgroup.zpowers _
  rw [(Iut.EtaleTheta.TateObject.charN_eq_one_iff _ _ _ _).2 hγ]
  exact one_mem _

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
theorem piYddotX_le_piXdd (l : ℕ) : PYddg ≤ piXdd V hV T l :=
  (piYddotX_le_piY T hL).trans (piY_le_piXdd l)

variable {l : ℕ} [NeZero l] {cX : piXdd V hV T l → Mu l Ω}
  (hcX : IsCocycle (actDD (augT (fieldData ht LX hLX) O V hV) (psiMu (k := k) (Ω := Ω) l)
    (piXdd V hV T l)) cX)

include hcX in
/-- **`Π^tp_X̲ ⊆ Π^tp_X̿`** ([EtTh] Prop. 2.2(ii), Def. 2.3): the kernel of the cocycle
`cX : Π^tp_X̿ → μ_l` encoding the splitting of `D̲_x ↠ G_K`. `cX` is data. The compatibility
`hcXr` used below does not pin it down in the `lℤ`-direction; [EtTh]'s `cX` is the projection to
`Δ̲_Θ` along the splitting (see the module docstring, "Caveat"). -/
def piXu : Subgroup PXg := (cocycleKer hcX).map (piXdd V hV T l).subtype

theorem mem_piXu_iff {γ : PXg} :
    γ ∈ piXu hcX ↔ ∃ h : γ ∈ piXdd V hV T l, cX ⟨γ, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨γ, h⟩, hc, rfl⟩

theorem isOpen_piXu (hcXc : Continuous cX) : IsOpen (piXu hcX : Set PXg) := by
  have hdd : IsOpen (piXdd V hV T l : Set PXg) :=
    (isOpen_discrete (Subgroup.zpowers (Multiplicative.ofAdd (l : ℤ)) :
      Set (Multiplicative ℤ))).preimage
      (Iut.EtaleTheta.TateObject.continuous_charN T V hV)
  have : (piXu hcX : Set PXg) = Subtype.val '' (cocycleKer hcX : Set (piXdd V hV T l)) := rfl
  rw [this]
  exact hdd.isOpenMap_subtype_val _ (isOpen_cocycleKer hcX hcXc)

/-- The augmentation `Π^tp_X̲ → G_k`. -/
abbrev augU : piXu hcX →* Gk k Ω := (augg).comp (piXu hcX).subtype

/-- **`Π^tp_Y̲ = Π^tp_Y ∩ Π^tp_X̲`**, as a (normal) subgroup of `Π^tp_X̲`. -/
abbrev piYU : Subgroup (piXu hcX) := (PYg).subgroupOf (piXu hcX)

variable (hL) in
include hL in
/-- **`Π^tp_Ÿ̲ = Π^tp_Ÿ ∩ Π^tp_X̲`**, as a subgroup of `Π^tp_X̲`. -/
abbrev piYddU : Subgroup (piXu hcX) := (PYddg).subgroupOf (piXu hcX)

variable (hL) in
include hL in
/-- `Π|_{l·Δ_Θ}`: `Π^tp_Ÿ̲ ∩ (preimage of Δ_Θ)`. -/
abbrev thetaLU : Subgroup (piXu hcX) := (thetaL T hL).subgroupOf (piXu hcX)

variable (hL) in
include hL in
/-- `Π^tp_Ÿ̲ ∩ Ker(Δ^tp_X ↠ Δ_X^Θ)`. -/
abbrev thetaKU : Subgroup (piXu hcX) := (thetaK T hL).subgroupOf (piXu hcX)

variable (hL) in
theorem piYddU_le_piYU : piYddU hL hcX ≤ piYU hcX :=
  Subgroup.subgroupOf_mono _ (piYddotX_le_piY T hL)

variable (hL) in
theorem thetaKU_le_thetaLU : thetaKU hL hcX ≤ thetaLU hL hcX :=
  Subgroup.subgroupOf_mono _ thetaK_le_thetaL

variable (hL) in
theorem thetaLU_le_piYddU : thetaLU hL hcX ≤ piYddU hL hcX :=
  Subgroup.subgroupOf_mono _ thetaL_le_piYddotX

/-- `[Π^tp_Y : Π^tp_Y ∩ Π^tp_X̲] < ∞` (`≤ l`). -/
theorem finiteIndex_piXu_subgroupOf_piY : ((piXu hcX).subgroupOf PYg).FiniteIndex := by
  haveI := finiteIndex_cocycleKer hcX
  haveI : (piXu hcX).IsFiniteRelIndex (piXdd V hV T l) := by
    have e : (piXu hcX).subgroupOf (piXdd V hV T l) = cocycleKer hcX :=
      Subgroup.comap_map_eq_self_of_injective (piXdd V hV T l).subtype_injective _
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, e]
    exact inferInstance
  haveI := Subgroup.isFiniteRelIndex_of_le_right (H := piXu hcX) (piY_le_piXdd (T := T) l)
  exact Subgroup.isFiniteRelIndex_iff_finiteIndex.1 inferInstance

/-- `Π^tp_Y̲ → Π^tp_Y`. -/
def piYUtoPiY : piYU hcX →* PYg where
  toFun g := ⟨((g : piXu hcX) : PXg), Subgroup.mem_subgroupOf.1 g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem piYUtoPiY_injective : Function.Injective (piYUtoPiY hcX) := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun z : PYg => (z : PXg)) h))

theorem range_piYUtoPiY : (piYUtoPiY hcX).range = (piXu hcX).subgroupOf PYg := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (g : piXu hcX).2
  · intro hz
    exact ⟨⟨⟨z, Subgroup.mem_subgroupOf.1 hz⟩, Subgroup.mem_subgroupOf.2 z.2⟩, rfl⟩

/-- **`FISlim Π^tp_Y ⇒ FISlim Π^tp_Y̲`** (finite-index subgroups of `Π^tp_Y̲` have finite index in
`Π^tp_Y`, and a centralizing element in `Π^tp_Y̲` centralizes their image). -/
theorem fiSlim_piYU (hPY : Envelope.FISlim PYg) : Envelope.FISlim (piYU hcX) := by
  intro H hH
  haveI := finiteIndex_piXu_subgroupOf_piY hcX
  have hfin : (H.map (piYUtoPiY hcX)).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_map_of_injective H (piYUtoPiY_injective hcX), range_piYUtoPiY]
    exact mul_ne_zero hH.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hc := hPY _ hfin
  rw [eq_bot_iff]
  intro z hz
  have hz' : piYUtoPiY hcX z ∈ Subgroup.centralizer ((H.map (piYUtoPiY hcX)) : Set PYg) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hz) h hh]
  rw [hc] at hz'
  exact piYUtoPiY_injective hcX ((Subgroup.mem_bot.1 hz').trans (map_one _).symm)

theorem isOpen_ker_act_augU (N : ℕ) [NeZero N] :
    IsOpen (((act (augU hcX) (psiMu (k := k) (Ω := Ω) N)).ker : Subgroup _) :
      Set (piXu hcX)) :=
  by
    have h := (isOpen_ker_act_augT DXg O V hV N).preimage
      (continuous_subtype_val (p := (· ∈ piXu hcX)))
    convert h using 1
    ext x
    exact Iff.rfl

/-! #### The root cocycle -/

variable {N : ℕ} [NeZero N] (r : ContH1.cocycles (piYddotX V hV T hL) (Mu (l * N) Ω))
  (hcXr : ∀ (γ : piYddotX V hV T hL)
    (h : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈ piXdd V hV T l),
    cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ))

variable (hL) in
/-- An element of `Π^tp_Ÿ̲` as an element of `Π^tp_Ÿ`. -/
def toPYdd : piYddU hL hcX →* PYddg where
  toFun g := ⟨((g : piXu hcX) : PXg), Subgroup.mem_subgroupOf.1 g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (hL) in
theorem continuous_toPYdd : Continuous (toPYdd hL hcX) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

include hcXr in
theorem val_pow_rootCocycle (g : piYddU hL hcX) : Mu.val (r (toPYdd hL hcX g)) ^ N = 1 := by
  obtain ⟨h, h1⟩ := (mem_piXu_iff hcX).1 (g : piXu hcX).2
  rw [← val_transition_mul (l := l), ← hcXr (toPYdd hL hcX g) h]
  exact (congrArg Mu.val h1).trans (map_one _)

/-- **The root cocycle** `Π^tp_Ÿ̲ → μ_N`: the values of `r` on `Π^tp_Ÿ̲` lie in `μ_N ⊆ μ_{lN}`. -/
def rootCocycle (g : piYddU hL hcX) : Mu N Ω :=
  Mu.mk (Mu.val (r (toPYdd hL hcX g))) (val_pow_rootCocycle hcX r hcXr g)

theorem val_rootCocycle (g : piYddU hL hcX) :
    Mu.val (rootCocycle hcX r hcXr g) = Mu.val (r (toPYdd hL hcX g)) := rfl

theorem isCocycle_rootCocycle :
    IsCocycle (actDD (augU hcX) (psiMu (k := k) (Ω := Ω) N) (piYddU hL hcX))
      (rootCocycle hcX r hcXr) := by
  intro g h
  apply Mu.ext
  change Mu.val (r (toPYdd hL hcX g * toPYdd hL hcX h)) = Mu.val (rootCocycle hcX r hcXr g * _)
  rw [isCocycle_coe_cocycles (l * N) r, map_mul, map_mul, val_rootCocycle]
  congr 1
  exact val_psiMu_eq _ (val_rootCocycle hcX r hcXr h).symm

/-- **The `l`-th root property** ("`η̈^Θ̲ ↦ η̈^Θ|_Ÿ̲`", [EtTh] l.2958–2962) on cocycles: the
image of the root cocycle under `l·Δ_Θ ↪ Δ_Θ` (on `μ_N`: `ζ ↦ ζ^l`) is the reduction mod `N`
of `r`. -/
theorem rootCocycle_pow (g : piYddU hL hcX) :
    rootCocycle hcX r hcXr g ^ l =
      Mu.transition (Dvd.intro_left l rfl : N ∣ l * N) (r (toPYdd hL hcX g)) := by
  apply Mu.ext
  rw [map_pow, val_rootCocycle, val_transition_mul']

theorem smul_eq_act_augU (g : piXu hcX) (ζ : Mu N Ω) :
    g • ζ = act (augU hcX) (psiMu (k := k) (Ω := Ω) N) g ζ :=
  (act_augT_psiMu DXg O V hV N (g : PXg) ζ).symm

open scoped Classical in
theorem continuous_rootCocycle : Continuous (rootCocycle hcX r hcXr) := by
  have : rootCocycle hcX r hcXr = (fun ζ : Mu (l * N) Ω => (if h : Mu.val ζ ^ N = 1 then
      Mu.mk (Mu.val ζ) h else 1 : Mu N Ω)) ∘ (fun g => r g) ∘ toPYdd hL hcX := by
    funext g
    simp only [Function.comp_apply, dif_pos (val_pow_rootCocycle hcX r hcXr g)]
    rfl
  rw [this]
  exact continuous_of_discreteTopology.comp ((ContH1.continuous r).comp (continuous_toPYdd hL hcX))

/-- The root cocycle as a continuous cocycle. -/
def rootCocycles : ContH1.cocycles (piYddU hL hcX) (Mu N Ω) :=
  ContH1.mkCocycle (rootCocycle hcX r hcXr) (continuous_rootCocycle hcX r hcXr) fun g h => by
    rw [isCocycle_rootCocycle hcX r hcXr g h, mul_comm]
    exact congrArg (· * _) (smul_eq_act_augU (N := N) hcX (g : piXu hcX) _).symm

/-- **The `l`-th root class `η̈^Θ̲ mod N ∈ H¹(Π^tp_Ÿ̲, (l·Δ_Θ) ⊗ ℤ/N)`** (`(l·Δ_Θ) ⊗ ℤ/N ≅ μ_N`). -/
def rootClass : ContH1 (piYddU hL hcX) (Mu N Ω) := ContH1.mk (rootCocycles hcX r hcXr)

variable (hL) in
theorem toPYdd_smul (g : piYddU hL hcX) (ζ : Mu N Ω) :
    MonoidHom.id (Mu N Ω) (toPYdd hL hcX g • ζ) = g • MonoidHom.id (Mu N Ω) ζ := rfl

/-- **"`η̈^Θ̲ ↦ η̈^Θ|_Ÿ̲`"** ([EtTh] l.2958–2962) on classes: the `l`-th power of the root class
(the map `l·Δ_Θ ↪ Δ_Θ` mod `N`) is the restriction to `Π^tp_Ÿ̲` of the class of `r` mod `N`. -/
theorem rootClass_pow :
    rootClass hcX r hcXr ^ l =
      ContH1.map (toPYdd hL hcX) (continuous_toPYdd hL hcX) (MonoidHom.id _) continuous_id
        (toPYdd_smul hL hcX) (transTemp T hL (Dvd.intro_left l rfl : N ∣ l * N) (ContH1.mk r)) := by
  refine (map_pow ContH1.mk (rootCocycles hcX r hcXr) l).symm.trans
    (congrArg ContH1.mk (Subtype.ext (funext fun g => ?_)))
  exact rootCocycle_pow hcX r hcXr g

/-! #### The model environment of `X̲` and [EtTh] Cor. 2.19(i) -/

/-- **The model mono-theta environment of `X̲`** ([EtTh] Def. 2.13(ii)): `Π^tp_Y̲[μ_N]`, `D_Y̲`
generated by `Π^tp_X̲`-conjugation and the Kummer twists of all continuous cocycles of `G_k`, and
the `μ_N`-conjugacy class of the theta section `s^alg − η̈^Θ̲` of the root class. -/
def thetaEnvU : MonoThetaEnv.{u} :=
  modelEnv (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
    (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
    (isCocycle_rootCocycle hcX r hcXr)

theorem rootCocycle_eq_one_of_thetaKU (hr13 : ∀ γ : PYddg, (γ : PXg) ∈ thetaK T hL → r γ = 1) :
    ∀ g (hg : g ∈ piYddU hL hcX), g ∈ thetaKU hL hcX → rootCocycle hcX r hcXr ⟨g, hg⟩ = 1 :=
  fun g hg hgK => Mu.ext (by
    rw [val_rootCocycle, hr13 (toPYdd hL hcX ⟨g, hg⟩) (Subgroup.mem_subgroupOf.1 hgK), map_one,
      map_one])

variable (hL) in
theorem augU_eq_one_of_mem_thetaLU {g : piXu hcX} (hg : g ∈ thetaLU hL hcX) : augU hcX g = 1 :=
  augT_eq_one_of_mem_thetaL hg

/-- **[EtTh] Cor. 2.19(i) (cyclotomic rigidity) for `X̲` and the cyclotome `l·Δ_Θ`**: for any
mono-theta environment `M` and any isomorphism `f : M ≅ thetaEnvU` respecting the input
subgroups, the algorithmic isomorphism of cyclotomes is carried to `s^alg(g) ↦ η̈^Θ̲(g)⁻¹` on
`Π|_{l·Δ_Θ}` (`thetaLU`).

Inputs: `hr13` (Prop. 1.3: `r = 1` on `Π^tp_Ÿ ∩ Kθ`; for the theta class from MR14, modulo C1).
Named hypotheses (Layer-B debts): `hPY` (`FISlim Π^tp_Y̲`; follows from `FISlim Π^tp_Y`,
obligation 1, by `fiSlim_piYU`), `hG` (`G_k` center-free; discharged for `k/ℚ_p` finite by
`gk_center_free_padic`), `hsurj` (`Π^tp_Y̲ ↠ G_k`; follows from `Π^tp_Y ↠ G_k`, obligation 5,
which holds at a rational base point by `surj_augT_of_ratPoint`, and the surjectivity `hrL` of
`r` on `Π|_{Δ_Θ}` by `surj_piYU`), `hLgen` (Prop. 2.12(i)-type generation). -/
theorem cyclotomicRigidity_thetaEnvU (hPY : Envelope.FISlim (piYU hcX))
    (hG : ∀ τ : Gk k Ω, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : Gk k Ω, ∃ h ∈ piYU hcX, augU hcX h = σ)
    (hLgen : Subgroup.closure {c | c ∈ thetaLU hL hcX ∧ ∃ a b, augU hcX a = 1 ∧ b ∈ piYU hcX ∧
      augU hcX b = 1 ∧ c = ⁅a, b⁆} ⊔ thetaKU hL hcX = thetaLU hL hcX)
    (hr13 : ∀ γ : PYddg, (γ : PXg) ∈ thetaK T hL → r γ = 1)
    {M : MonoThetaEnv.{u}} (f : MonoThetaEnv.Iso M (thetaEnvU hcX r hcXr))
    {Lsub Ksub Dsub : Subgroup M.G}
    (hLs : Lsub.map f.hom = rightSub (augU hcX) (psiMu N) (piYU hcX) (thetaLU hL hcX))
    (hKs : Ksub.map f.hom = rightSub (augU hcX) (psiMu N) (piYU hcX) (thetaKU hL hcX))
    (hDs : Dsub.map f.hom = geomSub (augU hcX) (psiMu N) (piYU hcX)) (t m : M.G) :
    M.IsCyc Lsub Ksub Dsub t m ↔ ∃ g : piYddU hL hcX, (g : piXu hcX) ∈ thetaLU hL hcX ∧
      f.e t = algSection (augU hcX) (psiMu N) (piYddU_le_piYU hL hcX) g ∧
      f.e m = inlY (augU hcX) (psiMu N) (piYU hcX) (rootCocycle hcX r hcXr g)⁻¹ :=
  cyclotomicRigidity_env (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
    (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
    (isCocycle_rootCocycle hcX r hcXr) hPY hG hsurj (thetaLU hL hcX) (thetaKU hL hcX)
    (thetaKU_le_thetaLU hL hcX) (thetaLU_le_piYddU hL hcX)
    (fun _ hg => augU_eq_one_of_mem_thetaLU hL hcX hg)
    (rootCocycle_eq_one_of_thetaKU hcX r hcXr hr13) hLgen f hLs hKs hDs t m

/-- **The root class maps `Π|_{l·Δ_Θ}` onto `μ_N`** if `r` maps `thetaL` onto `μ_{lN}`
(for the theta class: the cusp inertia, `classAt_cusp_surjective`). -/
theorem exists_rootCocycle_eq
    (hrL : ∀ m : Mu (l * N) Ω, ∃ γ : PYddg, (γ : PXg) ∈ thetaL T hL ∧ r γ = m)
    (m : Mu N Ω) :
    ∃ g : piYddU hL hcX, (g : piXu hcX) ∈ thetaLU hL hcX ∧ rootCocycle hcX r hcXr g = m := by
  have hm : Mu.val m ^ (l * N) = 1 := by rw [pow_mul', Mu.val_pow_n, one_pow]
  obtain ⟨γ, hγL, hγ⟩ := hrL (Mu.mk (Mu.val m) hm)
  have hdd : (γ : PXg) ∈ piXdd V hV T l := piYddotX_le_piXdd l γ.2
  have hX : (γ : PXg) ∈ piXu hcX := by
    refine (mem_piXu_iff hcX).2 ⟨hdd, ?_⟩
    rw [hcXr γ hdd]
    apply Mu.ext
    rw [val_transition_mul, hγ, Mu.val_mk, Mu.val_pow_n, map_one]
  refine ⟨⟨⟨γ, hX⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, Subgroup.mem_subgroupOf.2 hγL, ?_⟩
  apply Mu.ext
  rw [val_rootCocycle]
  exact congrArg Mu.val hγ

include hcXr in
/-- **`Π^tp_Y̲ ↠ G_k` from `Π^tp_Y ↠ G_k`** when `r` maps `Π|_{Δ_Θ}` onto `μ_{lN}` (e.g. the cusp
inertia): correct a lift in `Π^tp_Y` by a geometric element of `Π^tp_Ÿ` with the right value
of `cX`. -/
theorem surj_piYU (hsurj : ∀ σ : Gk k Ω, ∃ h ∈ PYg, augg h = σ)
    (hrL : ∀ m : Mu (l * N) Ω, ∃ γ : PYddg, (γ : PXg) ∈ thetaL T hL ∧ r γ = m) :
    ∀ σ : Gk k Ω, ∃ h ∈ piYU hcX, augU hcX h = σ := by
  intro σ
  obtain ⟨h, hY, rfl⟩ := hsurj σ
  have hh : h ∈ piXdd V hV T l := piY_le_piXdd l hY
  set c := cX ⟨h, hh⟩
  obtain ⟨m', hm'⟩ := transition_surjective (F := Ω) (Dvd.intro N rfl : l ∣ l * N)
    (NeZero.ne _) ((psiMu l (augg h⁻¹)) c⁻¹)
  obtain ⟨δ, hδL, hδ⟩ := hrL m'
  have hδdd : (δ : PXg) ∈ piXdd V hV T l := piYddotX_le_piXdd l δ.2
  have hprod : h * (δ : PXg) ∈ piXu hcX := by
    refine (mem_piXu_iff hcX).2 ⟨mul_mem hh hδdd, ?_⟩
    have e := hcX ⟨h, hh⟩ ⟨δ, hδdd⟩
    change cX ⟨h * δ, _⟩ = _ at e
    rw [e, hcXr δ hδdd, hδ, hm']
    change c * (psiMu l (augg h)) ((psiMu l (augg h⁻¹)) c⁻¹) = 1
    rw [← MulAut.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
      MulAut.one_apply, mul_inv_cancel]
  refine ⟨⟨_, hprod⟩, Subgroup.mem_subgroupOf.2 (mul_mem hY (piYddotX_le_piY T hL δ.2)), ?_⟩
  change augg (h * δ) = augg h
  rw [map_mul, augT_eq_one_of_mem_thetaL hδL, mul_one]

/-- **Automorphisms of the environment of `X̲` over the identity of `Π^tp_Y̲` act trivially on
`μ_N`** ([EtTh], proof of Cor. 2.18(iv), via Cor. 2.19(i)). -/
theorem ker_autPY_inlY_eq_thetaEnvU (hPY : Envelope.FISlim (piYU hcX))
    (hG : ∀ τ : Gk k Ω, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : Gk k Ω, ∃ h ∈ piYU hcX, augU hcX h = σ)
    (hLgen : Subgroup.closure {c | c ∈ thetaLU hL hcX ∧ ∃ a b, augU hcX a = 1 ∧ b ∈ piYU hcX ∧
      augU hcX b = 1 ∧ c = ⁅a, b⁆} ⊔ thetaKU hL hcX = thetaLU hL hcX)
    (hr13 : ∀ γ : PYddg, (γ : PXg) ∈ thetaK T hL → r γ = 1)
    (hrL : ∀ m : Mu (l * N) Ω, ∃ γ : PYddg, (γ : PXg) ∈ thetaL T hL ∧ r γ = m)
    {a : CategoryTheory.Aut (thetaEnvU hcX r hcXr)}
    (ha : a ∈ (autPY (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
      (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
      (isCocycle_rootCocycle hcX r hcXr) hPY).ker) (m : Mu N Ω) :
    autE (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
      (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
      (isCocycle_rootCocycle hcX r hcXr) a (inlY (augU hcX) (psiMu N) (piYU hcX) m) =
      inlY (augU hcX) (psiMu N) (piYU hcX) m := by
  refine ker_autPY_inlY_eq (aug := augU hcX) (ψ := psiMu N) (Kum := contCocycles (psiMu N))
    (hle := piYddU_le_piYU hL hcX) (hψ := isOpen_ker_act_augU hcX N)
    (hKum := isCocycle_of_mem_contCocycles _) (hη := isCocycle_rootCocycle hcX r hcXr)
    (hPY := hPY) hG hsurj (thetaLU hL hcX) (thetaKU hL hcX) (thetaKU_le_thetaLU hL hcX)
    (thetaLU_le_piYddU hL hcX) (fun _ hg => augU_eq_one_of_mem_thetaLU hL hcX hg)
    (rootCocycle_eq_one_of_thetaKU hcX r hcXr hr13) hLgen (fun m => ?_) ha m
  obtain ⟨g, hg, hgm⟩ := exists_rootCocycle_eq hcX r hcXr hrL m⁻¹
  exact ⟨g, hg, by rw [hgm, inv_inv]⟩

/-! #### All conclusions for `X̲` at once (generic "inputs ⇒ conclusions") -/

/-- **The conclusions of [EtTh] §2 for the environment of `X̲`**, for a representative `r` of a
class mod `lN` whose reduction mod `N` is `y`, and a proposition `P` (the extra hypotheses
under which `r` is surjective on `Π|_{Δ_Θ}`):

* (`l`-th root, [EtTh] l.2958–2962) `(η̈^Θ̲)^l = y|_{Π^tp_Ÿ̲}`;
* under the named hypotheses `hPY`, `hG`, `hLgen` and `P`: the cyclotomic rigidity
  (Cor. 2.19(i), `cyclotomicRigidity_thetaEnvU`) and the triviality on `μ_N` of the
  automorphisms over the identity of `Π^tp_Y̲` (`ker_autPY_inlY_eq_thetaEnvU`). Both need
  `Π^tp_Y̲ ↠ G_k`, which follows from `Π^tp_Y ↠ G_k` and the surjectivity of `r` on `Π|_{Δ_Θ}`
  (`surj_piYU`), both available under `P`.

A `def`, so that the concrete statement (`exists_thetaEnvU_rigidity`) is checked against it by
`exact` without unfolding. -/
def EnvUConclusions (y : ContH1 PYddg (Mu N Ω)) (P : Prop) : Prop :=
  rootClass hcX r hcXr ^ l =
      ContH1.map (toPYdd hL hcX) (continuous_toPYdd hL hcX) (MonoidHom.id _) continuous_id
        (toPYdd_smul hL hcX) y ∧
    ∀ (hPY : Envelope.FISlim (piYU hcX))
      (_ : ∀ τ : Gk k Ω, (∀ σ, τ * σ = σ * τ) → τ = 1)
      (_ : Subgroup.closure {c | c ∈ thetaLU hL hcX ∧ ∃ a b, augU hcX a = 1 ∧ b ∈ piYU hcX ∧
        augU hcX b = 1 ∧ c = ⁅a, b⁆} ⊔ thetaKU hL hcX = thetaLU hL hcX), P →
      (∀ {M : MonoThetaEnv.{u}} (f : MonoThetaEnv.Iso M (thetaEnvU hcX r hcXr))
        {Lsub Ksub Dsub : Subgroup M.G}
        (_ : Lsub.map f.hom = rightSub (augU hcX) (psiMu N) (piYU hcX) (thetaLU hL hcX))
        (_ : Ksub.map f.hom = rightSub (augU hcX) (psiMu N) (piYU hcX) (thetaKU hL hcX))
        (_ : Dsub.map f.hom = geomSub (augU hcX) (psiMu N) (piYU hcX)) (t m : M.G),
        M.IsCyc Lsub Ksub Dsub t m ↔ ∃ g : piYddU hL hcX, (g : piXu hcX) ∈ thetaLU hL hcX ∧
          f.e t = algSection (augU hcX) (psiMu N) (piYddU_le_piYU hL hcX) g ∧
          f.e m = inlY (augU hcX) (psiMu N) (piYU hcX) (rootCocycle hcX r hcXr g)⁻¹) ∧
      (∀ {a : CategoryTheory.Aut (thetaEnvU hcX r hcXr)},
        a ∈ (autPY (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
          (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
          (isCocycle_rootCocycle hcX r hcXr) hPY).ker → ∀ m : Mu N Ω,
        autE (augU hcX) (psiMu N) (contCocycles (psiMu N)) (piYddU_le_piYU hL hcX)
          (isOpen_ker_act_augU hcX N) (isCocycle_of_mem_contCocycles _)
          (isCocycle_rootCocycle hcX r hcXr) a (inlY (augU hcX) (psiMu N) (piYU hcX) m) =
          inlY (augU hcX) (psiMu N) (piYU hcX) m)

/-- **Inputs ⇒ conclusions for `X̲`**: the reduction `y` of `[r]` mod `N`, Prop. 1.3 (`hr13`) and,
under `P`, `Π^tp_Y ↠ G_k` (`hsurj`) and the surjectivity of `r` on `Π|_{Δ_Θ}` (`hrL`) give
`EnvUConclusions`. -/
theorem envUConclusions_of {y : ContH1 PYddg (Mu N Ω)}
    (hy : transTemp T hL (Dvd.intro_left l rfl : N ∣ l * N) (ContH1.mk r) = y)
    (hr13 : ∀ γ : PYddg, (γ : PXg) ∈ thetaK T hL → r γ = 1) {P : Prop}
    (hsurj : P → ∀ σ : Gk k Ω, ∃ h ∈ PYg, augg h = σ)
    (hrL : P → ∀ m : Mu (l * N) Ω, ∃ γ : PYddg, (γ : PXg) ∈ thetaL T hL ∧ r γ = m) :
    EnvUConclusions hcX r hcXr y P :=
  ⟨(rootClass_pow hcX r hcXr).trans (congrArg (ContH1.map (toPYdd hL hcX)
      (continuous_toPYdd hL hcX) (MonoidHom.id _) continuous_id (toPYdd_smul hL hcX)) hy),
    fun hPY hG hLgen hP =>
      ⟨fun f _ _ _ hLs hKs hDs t m =>
        cyclotomicRigidity_thetaEnvU hcX r hcXr hPY hG
          (surj_piYU hcX r hcXr (hsurj hP) (hrL hP)) hLgen hr13 f hLs hKs hDs t m,
      fun {_} ha m =>
        ker_autPY_inlY_eq_thetaEnvU hcX r hcXr hPY hG
          (surj_piYU hcX r hcXr (hsurj hP) (hrL hP)) hLgen hr13 (hrL hP) ha m⟩⟩

/-! #### The projective system of environments of `X̲` ([EtTh] Cor. 2.19(ii)) -/

variable (rs : ∀ n, ContH1.cocycles (piYddotX V hV T hL) (Mu (l * levelN n) Ω))
  (hrs : ∀ n g, Mu.transition (mul_levelN_dvd l n) (rs (n + 1) g) = rs n g)
  (hcX0 : ∀ (γ : piYddotX V hV T hL)
    (h : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈ piXdd V hV T l),
    cX ⟨γ, h⟩ = Mu.transition (Dvd.intro (levelN 0) rfl : l ∣ l * levelN 0) (rs 0 γ))

omit [IsAlgClosed Ω] in
include hrs hcX0 in
/-- The compatibility `hcXr` at every level follows from level `0`. -/
theorem hcXr_levelN (n : ℕ) (γ : PYddg) (h : (γ : PXg) ∈ piXdd V hV T l) :
    cX ⟨γ, h⟩ = Mu.transition (Dvd.intro (levelN n) rfl : l ∣ l * levelN n) (rs n γ) := by
  induction n with
  | zero => exact hcX0 γ h
  | succ n ih =>
    rw [ih, ← hrs n γ, transition_transition _ _ (NeZero.ne _)]

/-- The root cocycles of the levels `N_n` are compatible with the reductions (`hηred`). -/
theorem rootCocycle_levelN_red (n : ℕ) (g : piYddU hL hcX) :
    rootCocycle hcX (rs n) (hcXr_levelN rs hrs hcX0 n) g =
      Mu.transition (levelN_dvd n)
        (rootCocycle hcX (rs (n + 1)) (hcXr_levelN rs hrs hcX0 (n + 1)) g) := by
  apply Mu.ext
  rw [val_rootCocycle, Mu.val_transition, val_rootCocycle, ← hrs n, Mu.val_transition,
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero (NeZero.ne l))]

variable (hPYU : Envelope.FISlim (piYU hcX))

include hcX rs hrs hcX0 hPYU in
/-- **The tower of model environments of `X̲`** (levels `N_n = (n+1)!`, root classes of the
`rs n`): the natural projective system of `Env/Tower.lean`. -/
abbrev thetaTowerU : RigidSystems.Tower.{u + 1, u} :=
  envTower (augU hcX) (fun n => psiMu (levelN n)) (fun n => Mu.transition (levelN_dvd n))
    (fun n σ m => transition_psiMu (levelN_dvd n) σ m)
    (fun n => transition_surjective (levelN_dvd n) (NeZero.ne _)) levelN
    (fun n => ker_transition (levelN_dvd n) (NeZero.ne _))
    (fun n => contCocycles (psiMu (levelN n))) (fun n => contCocycles_eq_map (levelN_dvd n))
    (piYddU_le_piYU hL hcX) (fun n => isOpen_ker_act_augU hcX (levelN n))
    (fun _ => isCocycle_of_mem_contCocycles _)
    (fun n => isCocycle_rootCocycle hcX (rs n) (hcXr_levelN rs hrs hcX0 n))
    (rootCocycle_levelN_red hcX rs hrs hcX0) hPYU

include hcX rs hrs hcX0 hPYU in
/-- The action on `Π^tp_Y̲` of the automorphisms of the level-`n` model of `thetaTowerU`. -/
abbrev thetaAutPYNU (n : ℕ) :=
  autPYN (augU hcX) (fun n => psiMu (levelN n)) (fun n => Mu.transition (levelN_dvd n))
    (fun n σ m => transition_psiMu (levelN_dvd n) σ m)
    (fun n => transition_surjective (levelN_dvd n) (NeZero.ne _)) levelN
    (fun n => ker_transition (levelN_dvd n) (NeZero.ne _))
    (fun n => contCocycles (psiMu (levelN n))) (fun n => contCocycles_eq_map (levelN_dvd n))
    (piYddU_le_piYU hL hcX) (fun n => isOpen_ker_act_augU hcX (levelN n))
    (fun _ => isCocycle_of_mem_contCocycles _)
    (fun n => isCocycle_rootCocycle hcX (rs n) (hcXr_levelN rs hrs hcX0 n))
    (rootCocycle_levelN_red hcX rs hrs hcX0) hPYU n

/-- **The level-`n` model of the tower of `X̲` is `thetaEnvU` of the root class at `N_n`.** -/
theorem thetaTowerU_model (n : ℕ) :
    (thetaTowerU hcX rs hrs hcX0 hPYU).model n =
      thetaEnvU hcX (rs n) (hcXr_levelN rs hrs hcX0 n) := rfl

/-- **`[Π^tp_Y̲ : Π^tp_Ÿ̲] < ∞`**, from `[Π^tp_Y : Π^tp_Ÿ] < ∞`. -/
theorem finiteIndex_piYddU [hfin : ((piYddotX V hV T hL).subgroupOf
      (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)).FiniteIndex] :
    ((piYddU hL hcX).subgroupOf (piYU hcX)).FiniteIndex := by
  haveI : (piYddotX V hV T hL).IsFiniteRelIndex
      (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV) :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.2 hfin
  haveI := Subgroup.isFiniteRelIndex_of_le_right (H := piYddotX V hV T hL)
    (inf_le_left : Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV ⊓
      piXu hcX ≤ _)
  refine ⟨?_⟩
  change ((piYddotX V hV T hL).subgroupOf (piXu hcX)).relIndex
    ((Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV).subgroupOf
      (piXu hcX)) ≠ 0
  rw [← Subgroup.inf_subgroupOf_right
    (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV) (piXu hcX),
    Subgroup.relIndex_subgroupOf inf_le_right]
  exact Subgroup.relIndex_ne_zero

/-- **[EtTh] Cor. 2.19(ii) (discrete rigidity) for the environments of `X̲`**: every projective
system of mod-`N_n` mono-theta environments levelwise isomorphic to the model environments of the
root classes is isomorphic to the model system. Named hypotheses: `hPYU` (`FISlim Π^tp_Y̲`) and
`hlift` (the surjectivity half of Cor. 2.18(iv), Layer-B obligation 9). -/
theorem discreteRigidity_thetaEnvU [((piYddotX V hV T hL).subgroupOf
      (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)).FiniteIndex]
    (hlift : ∀ n, (thetaAutPYNU hcX rs hrs hcX0 hPYU 0).range ≤
      (thetaAutPYNU hcX rs hrs hcX0 hPYU n).range)
    (S : (thetaTowerU hcX rs hrs hcX0 hPYU).System)
    (hS : ∀ n, Nonempty (S.X n ≅ (thetaTowerU hcX rs hrs hcX0 hPYU).model n)) : S.IsoModel :=
  haveI := finiteIndex_piYddU (V := V) (hV := hV) (T := T) (hL := hL) hcX
  discreteRigidity_env (hlift := hlift) (S := S) (hS := hS)

/-! #### Obligation 13: the splitting cocycle from the invariance of the theta class mod `l` -/

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] [NeZero l] in
theorem dvd_character_piXdd (x : piXdd V hV T l) :
    (l : ℤ) ∣ Multiplicative.toAdd
      (Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV x) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
  refine ⟨n, ?_⟩
  rw [← hn, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_comm]

/-- The mod-`l` reduction of `r` on `Π^tp_Ÿ`. -/
def redCocycle (γ : PYddg) : Mu l Ω := Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ)

theorem isCocycle_redCocycle :
    IsCocycle (actDD augg (psiMu (k := k) (Ω := Ω) l) PYddg) (redCocycle (l := l) r) := by
  intro a b
  rw [redCocycle, isCocycle_coe_cocycles (l * N) r a b, map_mul]
  exact congrArg _ (transition_psiMu _ _ _)

/-- **Obligation 13, reduced to the invariance of the theta class mod `l`** ([EtTh]
Prop. 2.2(ii), l.2938–2945). Let `e ∈ Π^tp_Y ∖ Π^tp_Ÿ` (`[Π^tp_Y : Π^tp_Ÿ] = 2`) and `g` with
`χ(g) = l` (a generator of `Π^tp_X̿/Π^tp_Y ≅ lℤ`), and assume that `Π^tp_Ÿ` is normal in
`Π^tp_X̿`. If the conjugates of `r mod l` by `e` and by `g` are cohomologous to `r mod l` (with
coboundaries of `me`, `mg`: the `μ_2 × lℤ`-invariance of `θ mod l`, Prop. 1.5(iii)), and `l` is
odd, then a splitting cocycle `cX` with `hcXr` exists (`exists_cocycle_extend`). -/
theorem exists_cX_of_invariant (hl : Odd l)
    (hHn : ∀ x ∈ piXdd V hV T l, ∀ h ∈ PYddg, x * h * x⁻¹ ∈ PYddg)
    {e g : PXg} (heY : e ∈ PYg) (he : e ∉ PYddg) (he2 : e * e ∈ PYddg)
    (hidx : ∀ y ∈ PYg, y ∈ PYddg ∨ y * e⁻¹ ∈ PYddg)
    (hg : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV g =
      Multiplicative.ofAdd (l : ℤ))
    (me mg : Mu l Ω)
    (hce : ∀ (h : PXg) (hh : h ∈ PYddg),
      redCocycle r ⟨e * h * e⁻¹, hHn e (piY_le_piXdd l heY) h hh⟩ =
        me * act augg (psiMu l) e (redCocycle r ⟨h, hh⟩) *
          (act augg (psiMu l) (e * h * e⁻¹) me)⁻¹)
    (hcg : ∀ (h : PXg) (hh : h ∈ PYddg),
      redCocycle r ⟨g * h * g⁻¹, hHn g (by
        change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _) h hh⟩ =
        mg * act augg (psiMu l) g (redCocycle r ⟨h, hh⟩) *
          (act augg (psiMu l) (g * h * g⁻¹) mg)⁻¹) :
    ∃ (cX : piXdd V hV T l → Mu l Ω)
      (_ : IsCocycle (actDD augg (psiMu (k := k) (Ω := Ω) l) (piXdd V hV T l)) cX),
      ∀ (γ : PYddg) (h : (γ : PXg) ∈ piXdd V hV T l),
        cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ) := by
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  set χ := divChar ((Iut.EtaleTheta.TateObject.charN
    (A := (fieldData ht LX hLX).A) T V hV).comp (piXdd V hV T l).subtype) (l : ℤ)
    (dvd_character_piXdd (l := l)) with hχ
  have hker : ∀ x : piXdd V hV T l, x ∈ χ.ker ↔ (x : PXg) ∈ PYg := fun x => by
    rw [MonoidHom.mem_ker, hχ, divChar_eq_one_iff hl0]
    exact Iut.EtaleTheta.TateObject.charN_eq_one_iff _ _ _ _
  set H := (piYddotX V hV T hL).subgroupOf (piXdd V hV T l) with hHdef
  have hHn' : H.Normal := ⟨fun n hn x => hHn x.1 x.2 n.1 hn⟩
  have hgdd : g ∈ piXdd V hV T l := by
    change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _
  have heg : e ∈ piXdd V hV T l := piY_le_piXdd l heY
  have hM : ∀ m : Mu l Ω, m ^ l = 1 := fun m => Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])
  obtain ⟨C, hC, hCH⟩ := exists_cocycle_extend (φ := actDD augg (psiMu (k := k) (Ω := Ω) l)
      (piXdd V hV T l)) hl hM H hHn' χ
    (fun x hx => (hker x).2 (piYddotX_le_piY T hL hx))
    (e := ⟨e, heg⟩) (g := ⟨g, hgdd⟩) he ((hker _).2 heY) he2
    (fun y hy => hidx y.1 ((hker y).1 hy))
    (divChar_eq_ofAdd_one hl0 _ hg)
    (fun h => redCocycle r ⟨h.1.1, h.2⟩)
    (fun a b => isCocycle_redCocycle r ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
    me mg (fun h hh => hce h.1 hh) (fun h hh => hcg h.1 hh)
  exact ⟨C, hC, fun γ h => hCH ⟨⟨γ, h⟩, γ.2⟩⟩

/-- **Obligation 13 when `Π^tp_Y ⊆ Π^tp_Ÿ`** (the case `[Π^tp_Y : Π^tp_Ÿ] = 1`, complementary to
`exists_cX_of_invariant`): only the `lℤ`-direction `g` (`χ(g) = l`) is needed
(`exists_cocycle_extend_ker`). -/
theorem exists_cX_of_invariant_ker
    (hHn : ∀ x ∈ piXdd V hV T l, ∀ h ∈ PYddg, x * h * x⁻¹ ∈ PYddg)
    (hYY : ∀ y ∈ PYg, y ∈ PYddg) {g : PXg}
    (hg : Iut.EtaleTheta.TateObject.charN (A := (fieldData ht LX hLX).A) T V hV g =
      Multiplicative.ofAdd (l : ℤ))
    (mg : Mu l Ω)
    (hcg : ∀ (h : PXg) (hh : h ∈ PYddg),
      redCocycle r ⟨g * h * g⁻¹, hHn g (by
        change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _) h hh⟩ =
        mg * act augg (psiMu l) g (redCocycle r ⟨h, hh⟩) *
          (act augg (psiMu l) (g * h * g⁻¹) mg)⁻¹) :
    ∃ (cX : piXdd V hV T l → Mu l Ω)
      (_ : IsCocycle (actDD augg (psiMu (k := k) (Ω := Ω) l) (piXdd V hV T l)) cX),
      ∀ (γ : PYddg) (h : (γ : PXg) ∈ piXdd V hV T l),
        cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ) := by
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  set χ := divChar ((Iut.EtaleTheta.TateObject.charN
    (A := (fieldData ht LX hLX).A) T V hV).comp (piXdd V hV T l).subtype) (l : ℤ)
    (dvd_character_piXdd (l := l)) with hχ
  have hker : ∀ x : piXdd V hV T l, x ∈ χ.ker ↔ (x : PXg) ∈ PYg := fun x => by
    rw [MonoidHom.mem_ker, hχ, divChar_eq_one_iff hl0]
    exact Iut.EtaleTheta.TateObject.charN_eq_one_iff _ _ _ _
  set H := (piYddotX V hV T hL).subgroupOf (piXdd V hV T l) with hHdef
  have hHn' : H.Normal := ⟨fun n hn x => hHn x.1 x.2 n.1 hn⟩
  have hgdd : g ∈ piXdd V hV T l := by
    change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _
  obtain ⟨C, hC, hCH⟩ := exists_cocycle_extend_ker (φ := actDD augg (psiMu (k := k) (Ω := Ω) l)
      (piXdd V hV T l)) H hHn' χ
    (fun x hx => (hker x).2 (piYddotX_le_piY T hL hx))
    (fun y hy => hYY y.1 ((hker y).1 hy)) (g := ⟨g, hgdd⟩)
    (divChar_eq_ofAdd_one hl0 _ hg)
    (fun h => redCocycle r ⟨h.1.1, h.2⟩)
    (fun a b => isCocycle_redCocycle r ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
    mg (fun h hh => hcg h.1 hh)
  exact ⟨C, hC, fun γ h => hCH ⟨⟨γ, h⟩, γ.2⟩⟩

end Levels

/-! ### Root representatives along the levels -/

section Reps

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]

local notation "PYddg" => piYddotX V hV T hL

/-- `l·N_n ∣ N_{n+l}` (`(n+1)!·l! ∣ (n+1+l)!`). -/
theorem mul_levelN_dvd_levelN_add (l : ℕ) [NeZero l] (n : ℕ) :
    l * levelN n ∣ levelN (n + l) := by
  have h1 : l ∣ l.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne l)) le_rfl
  have h2 := Nat.factorial_mul_factorial_dvd_factorial_add (n + 1) l
  rw [levelN, levelN, show n + l + 1 = n + 1 + l by omega]
  exact (Nat.mul_dvd_mul_right h1 _).trans (by rw [mul_comm]; exact h2)

variable (x : ∀ n, ContH1 (piYddotX V hV T hL) (Mu (levelN n) Ω))
  (hx : ∀ n, transTemp T hL (levelN_dvd n) (x (n + 1)) = x n) (l : ℕ) [NeZero l]

/-- **Representatives of the classes mod `l·N_n`** for the root classes of `X̲` at the levels
`N_n`: the reductions of the compatible representatives `compatRep` of `x (n + l)`. -/
def rootReps (n : ℕ) : ContH1.cocycles PYddg (Mu (l * levelN n) Ω) :=
  ContH1.mkCocycle
    (fun γ => Mu.transition (mul_levelN_dvd_levelN_add l n) ((compatRep x hx (n + l)).1 γ))
    (continuous_of_discreteTopology.comp (ContH1.continuous _)) fun g h => by
      simp only [ContH1.isMulCocycle₁ (compatRep x hx (n + l)).1 g h, map_mul,
        transition_smul_piYddotX]

theorem rootReps_apply (n : ℕ) (γ : PYddg) :
    rootReps x hx l n γ =
      Mu.transition (mul_levelN_dvd_levelN_add l n) ((compatRep x hx (n + l)).1 γ) := rfl

theorem transition_compatRep_congr {a b : ℕ} (e : a = b) {c : ℕ} (h1 : c ∣ levelN a)
    (h2 : c ∣ levelN b) (γ : PYddg) :
    Mu.transition h1 ((compatRep x hx a).1 γ) = Mu.transition h2 ((compatRep x hx b).1 γ) := by
  subst e
  rfl

theorem rootReps_red (n : ℕ) (γ : PYddg) :
    Mu.transition (mul_levelN_dvd l n) (rootReps x hx l (n + 1) γ) = rootReps x hx l n γ := by
  rw [rootReps_apply, rootReps_apply, transition_transition _ _ (NeZero.ne _),
    compatRep_red x hx (n + l) γ, transition_transition _ _ (NeZero.ne _)]
  exact transition_compatRep_congr x hx (by omega) _ _ γ

/-- `rootReps` represents `x` mod `l·N_n` reduced from `x (n + l)`. -/
theorem mk_rootReps (n : ℕ) :
    ContH1.mk (rootReps x hx l n) =
      transTemp T hL (mul_levelN_dvd_levelN_add l n) (x (n + l)) := by
  rw [← (compatRep x hx (n + l)).2]
  rfl

end Reps

/-! ### The Tate curve: the inputs from MR14 -/

section Concrete

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)
set_option quotPrecheck false in
local notation "DXc" => fieldData (transcendental_tau t.tateCurve) (hemiData t.tateCurve).L
  (hemiL_open t)

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

set_option maxHeartbeats 4000000 in
-- destructuring `exists_thetaClassTemp_prop13` (concrete Tate-curve levels) is slow to unify
include h2 in
/-- **The inputs of the theorems on `X̲` for the étale theta system of the Tate curve.** For the
theta system of `exists_thetaClassTemp_prop13`, every base point `V` over `O`, under C1, every
`n ≥ 1` and every representative `r` of the theta class mod `n` on `Π^tp_Ÿ`:

* (`hr13`, [EtTh] Prop. 1.3) `r = 1` on `Π^tp_Ÿ ∩ Kθ` (MR14, modulo C1 only);
* (`hrL`) if `V` lies under a place `W` over the cusp, then under the debt
  `CuspInertiaWeil`, `r` maps `Π^tp_Ÿ ∩ (preimage of Δ_Θ)` onto
  `μ_n` (cusp inertia).

The system also carries MR14's stability `σ(L_j) ⊆ L_j` and the tempered translation formula
(run 18, [EtTh] Prop. 1.5(iii) mod `l`), the inputs of obligation 13
(`exists_cX_of_moves`, `Env/ThetaConjLevel.lean`).

With `n = l·N`, these are the inputs `hr13`, `hrL` of `cyclotomicRigidity_thetaEnvU` and
`ker_autPY_inlY_eq_thetaEnvU`; the `l`-th root property of the root class is `rootClass_pow` with
`transTemp_thetaClassTemp` (compatibility of the theta classes in `n`). -/
theorem exists_thetaRep_inputs :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (Iut.EtaleTheta.DX t).R
        (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ j, ∀ σ ∈ (hemiData t.tateCurve).L.fixingSubgroup, ∀ x ∈ L j, σ x ∈ L j) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        PiYIndexTwoAt V hV (tateDataX O hO hs h12) hL 0 ∧
        ∀ (j l : ℕ), Odd l → 2 * l ∣ 2 * (j + 1) → LevelsDominated V hV (tateDataX O hO hs h12) hL →
        ∀ (g₁ : TempPi DXc O V hV),
          Iut.EtaleTheta.TateObject.charN (A := (DXc).A)
            (tateDataX O hO hs h12) V hV g₁ = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (γ : TempPi DXc O V hV) (m : ℤ),
          Iut.EtaleTheta.TateObject.charN (A := (DXc).A)
            (tateDataX O hO hs h12) V hV γ = Multiplicative.ofAdd ((l : ℤ) * m) →
        ∀ σ : (DXc).H, (σ : Pi (DXc)) = tempToPi DXc O V hV γ →
          MovesByPow (L j) (σ : Ω ≃ₐ[K₀ K τ] Ω)
            (((η j : (F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))ˣ) :
              F (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))) : Ω) l) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        (∀ j, ZM h2 h12 O hO hs j V hV) → LevelsDominated V hV (tateDataX O hO hs h12) hL) ∧
      ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (n : ℕ) [NeZero n]
        (r : ContH1.cocycles (piYddotX V hV (tateDataX O hO hs h12) hL) (Mu n Ω)),
        ContH1.mk r = thetaClassTemp η hC1 n →
        (∀ γ : piYddotX V hV (tateDataX O hO hs h12) hL,
          (γ : TempPi DXc O V hV) ∈ thetaK (tateDataX O hO hs h12) hL → r γ = 1) ∧
        ∀ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W → V ≤ W →
          CuspInertiaWeil (DXc) →
          ∀ m : Mu n Ω, ∃ γ : piYddotX V hV (tateDataX O hO hs h12) hL,
            (γ : TempPi DXc O V hV) ∈ thetaL (tateDataX O hO hs h12) hL ∧ r γ = m := by
  obtain ⟨L, hL, hX, het, η, hL0, htr, hcomp, hker, hcusp, hdelta, hstab, hmove, hzm⟩ :=
    exists_thetaClassTemp_prop13 h2 h12 hs O hO
  refine ⟨L, hL, hX, het, η, htr, hstab, hmove, hcomp, hzm,
    fun V hV hC1 n _ r hr => ⟨fun γ hγ => ?_,
    fun W hk hτ hVW hG5 m => ?_⟩⟩
  · have hdvd : n ∣ 2 * (n - 1 + 1) :=
      ⟨2, by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))]; ring⟩
    have h := hker V hV hC1 (n - 1) n hdvd γ hγ.2
    rw [← ContH1.evalTriv_mk γ (thetaKernelTemp_smul_mu hγ.2 n) r]
    exact (congrArg _ hr).trans h
  · obtain ⟨e, he⟩ := hdelta hG5
    obtain ⟨σ, hσ⟩ := (hcusp W hk hτ).2 V hV hVW hC1 n m
    obtain ⟨hσΘ, -⟩ := (he W hk hτ).2 V hV hVW hC1 σ
    refine ⟨⟨_, inertiaToTempered_mem_piYddotX V hV _ hL hVW σ (hL0 W hk hτ σ)⟩,
      inertiaToTempered_mem_thetaL hk hVW σ (hL0 W hk hτ σ) hσΘ, ?_⟩
    rw [← ContH1.evalTriv_mk _ (inertiaToTempered_piYddotX_smul hk hVW σ (hL0 W hk hτ σ) n) r,
      hr]
    exact hσ

set_option maxHeartbeats 1000000 in
-- unifying with `exists_thetaRep_inputs` (concrete Tate-curve levels) is slow
variable [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
include h2 in
/-- **[EtTh] §2 for `X̲` and `l·Δ_Θ`, for one étale theta system of the Tate curve** (all
conclusions in one existential; consumed by MR23). For the theta system of
`exists_thetaRep_inputs`, every base point `V` over `O`, under C1, every `l, N ≥ 1`, every
representative `r` of the theta class mod `lN` on `Π^tp_Ÿ` and every splitting cocycle
`cX : Π^tp_X̿ → μ_l` with `hcXr` (this defines `X̲`; existence of `cX`: obligation 13):
`EnvUConclusions` with `y` = the theta class mod `N` and `P` = "`V` lies under a place `W` over the
cusp, and the debt `CuspInertiaWeil` holds". That is: the `l`-th root
property `(η̈^Θ̲)^l = η̈^Θ|_{Ÿ̲}` mod `N`; under `hPY`, `hG`, `hLgen` (for `X̲`) and `P` the
cyclotomic rigidity of Cor. 2.19(i) (Prop. 1.3 input discharged modulo C1) and the triviality on
`μ_N` of the automorphisms over the identity of `Π^tp_Y̲`. `O` is a complete discrete valuation
ring. Obligation 5 (`Π^tp_Y ↠ G_k`) is discharged under `P`: the place `W` over the cusp is a
`K`-rational point (`cuspRatPoint`, `surj_augT_of_ratPoint`); with the cusp inertia this gives
`Π^tp_Y̲ ↠ G_k` (`surj_piYU`). Base points as in `P` exist (`exists_basePoint_cusp`). -/
theorem exists_thetaEnvU_rigidity :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (Iut.EtaleTheta.DX t).R
        (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        (∀ j, ZM h2 h12 O hO hs j V hV) → LevelsDominated V hV (tateDataX O hO hs h12) hL) ∧
      ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (l N : ℕ) [NeZero l] [NeZero N]
        (r : ContH1.cocycles (piYddotX V hV (tateDataX O hO hs h12) hL) (Mu (l * N) Ω)),
        ContH1.mk r = thetaClassTemp η hC1 (l * N) →
        ∀ {cX : piXdd V hV (tateDataX O hO hs h12) l → Mu l Ω}
          (hcX : IsCocycle (actDD (augT DXc O V hV) (psiMu l)
            (piXdd V hV (tateDataX O hO hs h12) l)) cX)
          (hcXr : ∀ (γ : piYddotX V hV (tateDataX O hO hs h12) hL)
            (h : (γ : TempPi DXc O V hV) ∈ piXdd V hV (tateDataX O hO hs h12) l),
            cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ)),
          EnvUConclusions hcX r hcXr (thetaClassTemp η hC1 N)
            (∃ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W ∧ V ≤ W ∧
              CuspInertiaWeil (DXc)) := by
  refine (exists_thetaRep_inputs h2 h12 hs O hO).imp fun L => Exists.imp fun hL =>
    Exists.imp fun hX => Exists.imp fun het => Exists.imp fun η h =>
      ⟨h.1, h.2.2.2.2.1, fun V hV hC1 l N _ _ r hr {_} hcX hcXr => ?_⟩
  obtain ⟨hr13, hrL⟩ := h.2.2.2.2.2 V hV hC1 (l * N) r hr
  exact envUConclusions_of hcX r hcXr
    ((congrArg (transTemp (tateDataX O hO hs h12) hL (Dvd.intro_left l rfl : N ∣ l * N)) hr).trans
      ((h.2.2.2.1 V hV hC1).2 N (l * N) (Dvd.intro_left l rfl)))
    hr13 (fun ⟨W, hk, hτ, hVW, _⟩ => surj_augT_of_ratPoint (tateDataX O hO hs h12)
      (cuspRatPoint hk hτ) hVW) fun ⟨W, hk, hτ, hVW, hG5⟩ => hrL W hk hτ hVW hG5

end Concrete

end Iut.EtaleTheta.Env
