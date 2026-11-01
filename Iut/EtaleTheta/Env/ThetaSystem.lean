/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaKerTheta
import Iut.EtaleTheta.Env.AutKernel
import Iut.EtaleTheta.Env.Prop214

/-!
# The model environment of the étale theta system ([EtTh], Cor. 2.19(i), Layer B)

This file instantiates the abstract theta setting of `Env/Model.lean` with the genuine tempered
objects of MR14 for `X = E_q ∖ {O}` (the Tate curve minus the origin, [EtTh] §1):

* `PX = Π^tp_X` (`TempPi D O V hV`, base point `V`), with the augmentation
  `augT : Π^tp_X → Π_X → G_k` (`tempToPi`, `piToGk`);
* `μ = μ_n(Ω)` with the cyclotomic character `psiMu n : G_k →* Aut(μ_n)` (the Galois action on
  `μ_n(k̄) ≅ μ_n(Ω)`, `muEquiv`); through `augT` it is the action of `Π^tp_X` on `μ_n`
  (`act_augT_psiMu`);
* `PY = Π^tp_Y` (`TateObject.piY`, the `ℤ`-covering), `PYdd = Π^tp_Ÿ` (`piYddotX`);
* `Kθ = Π^tp_Ÿ ∩ Ker(Δ^tp_X ↠ Δ_X^Θ)` (`thetaKernelTemp`, MR14) and
  `L = Π^tp_Ÿ ∩ (preimage of Δ_Θ ⊆ Δ_X^Θ)` (`thetaSubTemp`): the input `Π|_{Δ_Θ}` of [EtTh]
  Cor. 2.19(i);
* `Kum` = all continuous cocycles `G_k → μ_n` (`contCocycles`; by Kummer theory these are the
  Kummer cocycles of `k^×`);
* `η` = a representative cocycle (`repCocycle`) of a class `x ∈ H¹(Π^tp_Ÿ, μ_n)`, for `x` the
  étale theta class `thetaClassTemp η n` of MR14.

The [EtTh] statement is for the curve `X̲` of type `(1, (ℤ/lℤ)^Θ)` and the cyclotome `l·Δ_Θ`;
here everything is for `X` itself and `Δ_Θ` (the case `l = 1` of the construction, which is
the form in which MR14 provides the étale theta class). The transport to `X̲, Y̲, Ÿ̲` and
`l·Δ_Θ` is MR15 Layer-B item 9.

## Main results

* `cyclotomicRigidity_thetaEnv` (generic levels): [EtTh] Cor. 2.19(i) for the model environment
  of a class `x` vanishing on `Kθ`: the algorithmic isomorphism of cyclotomes is
  `s^alg(l) ↦ x(l)⁻¹` on `L` (`x(l)` = `ContH1.evalTriv l x`).
* `ker_autPY_inlY_eq_thetaEnv`: automorphisms of the model environment over the identity of
  `Π^tp_Y` act trivially on `μ_n` ([EtTh], proof of Cor. 2.18(iv)), for a class that also maps
  `L` onto `μ_n`.
* `cyclotomicRigidity_thetaSystem`, `ker_autPY_inlY_eq_thetaSystem` (the concrete Tate curve,
  for the system of `exists_thetaClassTemp_prop13`): the hypothesis `hη13` (Layer-B
  obligation 8) is discharged by MR14's Prop. 1.3 (`exists_thetaClassTemp_prop13`), and `hηL`
  (obligation 11) by the cusp inertia (`classAt_cusp_surjective`, `classAt_deltaTheta`).

Remaining hypotheses (Layer-B debts, `MR15-plan.md`): C1 (`LevelsDominated`, MR14/MR12),
`FISlim (piY …)` (obligation 1, M2-GEA + MR2), center-freeness of `G_k` (`hG`; for `k` a finite
extension of `ℚ_p` this is `PAdicGalois.isSlimGroup`, once `Gk k Ω` is identified with
`GK p E`), `Π^tp_Y ↠ G_k` (`hsurj`, obligation 5), the Prop. 2.12(i)-type generation `hL`, and,
for `hηL`, the debts `CuspInertiaWeil` (G5c+G5d) and `InertiaFixesLevel (L 0)` of MR14.
-/

open scoped commutatorElement

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

/-! ### The cyclotomic character `G_k → Aut(μ_n(Ω))` -/

section Cyclotomic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- `μ_n(k̄) ≅ μ_n(Ω)` (roots of unity are algebraic). -/
def muEquiv (n : ℕ) [NeZero n] : Mu n (kbar k Ω) ≃* Mu n Ω :=
  MulEquiv.ofBijective (muMap n (kbar k Ω) Ω) ⟨muMap_injective n, muMap_surjective n⟩

@[simp] theorem muEquiv_apply (n : ℕ) [NeZero n] (ζ : Mu n (kbar k Ω)) :
    muEquiv n ζ = muMap n (kbar k Ω) Ω ζ := rfl

/-- **The cyclotomic character** `G_k → Aut(μ_n(Ω))`: the Galois action on `μ_n(k̄)`, transported
along `muEquiv`. -/
def psiMu (n : ℕ) [NeZero n] : Gk k Ω →* MulAut (Mu n Ω) :=
  (MulAut.congr (muEquiv (k := k) (Ω := Ω) n)).toMonoidHom.comp
    (MulDistribMulAction.toMulAut (Gk k Ω) (Mu n (kbar k Ω)))

theorem psiMu_apply (n : ℕ) [NeZero n] (σ : Gk k Ω) (ζ : Mu n Ω) :
    psiMu n σ ζ = muEquiv (k := k) n (σ • (muEquiv (k := k) n).symm ζ) := rfl

theorem psiMu_muEquiv (n : ℕ) [NeZero n] (σ : Gk k Ω) (ζ : Mu n (kbar k Ω)) :
    psiMu n σ (muEquiv n ζ) = muEquiv n (σ • ζ) := by
  rw [psiMu_apply, MulEquiv.symm_apply_apply]

theorem psiMu_piToGk {t : Ω} (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω]
    [IsAlgClosed Ω] (n : ℕ) [NeZero n] (g : Pi D) (ζ : Mu n Ω) :
    psiMu n (piToGk D g) ζ = g • ζ := by
  obtain ⟨ζ', rfl⟩ := (muEquiv (k := k) (Ω := Ω) n).surjective ζ
  rw [psiMu_muEquiv, muEquiv_apply, muEquiv_apply, muMap_piToGk_smul]

theorem coe_val_smul_kbar (n : ℕ) (σ : Gk k Ω) (ζ : Mu n (kbar k Ω)) :
    ((Mu.val (σ • ζ) : (kbar k Ω)ˣ) : kbar k Ω) = σ ((Mu.val ζ : (kbar k Ω)ˣ) : kbar k Ω) := rfl

theorem smul_mu_eq_iff (n : ℕ) (σ : Gk k Ω) (ζ : Mu n (kbar k Ω)) :
    σ • ζ = ζ ↔
      σ ((Mu.val ζ : (kbar k Ω)ˣ) : kbar k Ω) = ((Mu.val ζ : (kbar k Ω)ˣ) : kbar k Ω) := by
  rw [← coe_val_smul_kbar]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Mu.ext (Units.ext h)

/-- The kernel of the cyclotomic character is open. -/
theorem isOpen_ker_psiMu (n : ℕ) [NeZero n] :
    IsOpen (((psiMu (k := k) (Ω := Ω) n).ker : Subgroup (Gk k Ω)) : Set (Gk k Ω)) := by
  have hset : (((psiMu (k := k) (Ω := Ω) n).ker : Subgroup (Gk k Ω)) : Set (Gk k Ω)) =
      ⋂ ζ : Mu n (kbar k Ω),
        (MulAction.stabilizer (Gk k Ω) (((Mu.val ζ : (kbar k Ω)ˣ) : kbar k Ω)) :
          Set (Gk k Ω)) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MulAction.mem_stabilizer_iff,
      AlgEquiv.smul_def]
    rw [MulEquiv.ext_iff]
    simp only [MulAut.one_apply]
    refine ((muEquiv (k := k) (Ω := Ω) n).surjective.forall).trans ?_
    refine forall_congr' fun ζ => ?_
    rw [← smul_mu_eq_iff]
    constructor
    · intro h
      rw [psiMu_muEquiv] at h
      exact (muEquiv (k := k) (Ω := Ω) n).injective h
    · intro h
      rw [psiMu_muEquiv, h]
  rw [hset]
  exact isOpen_iInter_of_finite fun ζ => stabilizer_isOpen_of_isIntegral _

/-- **Center-freeness transfers along an identification of `k̄`**: if `k̄ ⊆ Ω` is
`k`-isomorphic to `Ω'` and `Gal(Ω'/k)` is center-free, so is `G_k = Gal(k̄/k)`. -/
theorem gk_center_free_of_algEquiv {Ω' : Type*} [Field Ω'] [Algebra k Ω']
    (e : kbar k Ω ≃ₐ[k] Ω') (h : ∀ τ : Ω' ≃ₐ[k] Ω', (∀ σ, τ * σ = σ * τ) → τ = 1)
    (τ : Gk k Ω) (hτ : ∀ σ, τ * σ = σ * τ) : τ = 1 := by
  have h1 : AlgEquiv.autCongr e τ = 1 := h _ fun σ => by
    obtain ⟨σ', rfl⟩ := (AlgEquiv.autCongr e).surjective σ
    rw [← map_mul, ← map_mul, hτ σ']
  exact (AlgEquiv.autCongr e).injective (h1.trans (map_one _).symm)

set_option synthInstance.maxHeartbeats 400000 in
-- the torsion-freeness instance `E → k̄` is found only with a larger budget
/-- **`G_E` is center-free for a finite extension `E/ℚ_p`** (in the form of the hypothesis `hG`
of `cyclotomicRigidity_thetaEnv`, for `G_E = Gal(Ē/E)` with `Ē` the algebraic closure of `E` in
any field `Ω ⊇ E`): `Ē ≅ ℚ̄_p` over `E`, and `Gal(ℚ̄_p/E)` is slim (`PAdicGalois.isSlimGroup`,
via `gK_center_free`). This discharges `hG` whenever the base field of the Tate curve is a
finite extension of `ℚ_p` inside `ℚ̄_p`. -/
theorem gk_center_free_padic {p : ℕ} [Fact p.Prime]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    {Ω₀ : Type} [Field Ω₀] [Algebra E Ω₀] [IsAlgClosed Ω₀] (τ : Gk E Ω₀)
    (hτ : ∀ σ, τ * σ = σ * τ) : τ = 1 := by
  haveI : Algebra.IsAlgebraic E (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) E
  haveI : IsAlgClosure E (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosure E (kbar E Ω₀) :=
    ⟨isAlgClosed_kbar, algebraicClosure.isAlgebraic (F := E) (E := Ω₀)⟩
  exact gk_center_free_of_algEquiv (IsAlgClosure.equiv E (kbar E Ω₀) (PadicAlgCl p))
    (fun τ' hτ' => gK_center_free τ' hτ') τ hτ

end Cyclotomic

/-! ### The genuine theta setting at generic levels -/

section Setting

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **The augmentation** `Π^tp_U → Π_U → G_k`. -/
def augT : TempPi D O V hV →* Gk k Ω := (piToGk D).comp (tempToPi D O V hV)

theorem continuous_augT : Continuous (augT D O V hV) :=
  (continuous_piToGk D).comp (continuous_tempToPi D O V hV)

theorem act_augT_psiMu (n : ℕ) [NeZero n] (γ : TempPi D O V hV) (ζ : Mu n Ω) :
    act (augT D O V hV) (psiMu n) γ ζ = γ • ζ :=
  psiMu_piToGk D n (tempToPi D O V hV γ) ζ

theorem isOpen_ker_act_augT (n : ℕ) [NeZero n] :
    IsOpen (((act (augT D O V hV) (psiMu (k := k) (Ω := Ω) n)).ker : Subgroup _) :
      Set (TempPi D O V hV)) := by
  have : (((act (augT D O V hV) (psiMu (k := k) (Ω := Ω) n)).ker : Subgroup _) :
      Set (TempPi D O V hV)) = augT D O V hV ⁻¹' ((psiMu (k := k) (Ω := Ω) n).ker : Set _) := by
    ext γ
    simp [MonoidHom.mem_ker, act]
  rw [this]
  exact (isOpen_ker_psiMu n).preimage (continuous_augT D O V hV)

/-- **The preimage of `Δ_Θ` in `Π^tp_U`**: the elements whose image in `Π_U` lies in `Δ_U` and
maps into `Δ_Θ ⊆ Δ_U^Θ` (`thetaSubD`). -/
def thetaSubTemp : Subgroup (TempPi D O V hV) :=
  (((thetaSubD D).comap (toDeltaTheta D)).map (deltaPi D).subtype).comap (tempToPi D O V hV)

variable {D O V hV}

theorem thetaKernelTemp_le_thetaSubTemp : thetaKernelTemp D O V hV ≤ thetaSubTemp D O V hV := by
  rintro γ ⟨x, hx, hxe⟩
  refine ⟨x, ?_, hxe⟩
  change toDeltaTheta D x ∈ thetaSubD D
  have hk : x ∈ (toDeltaTheta D).ker := by
    rw [toDeltaTheta, QuotientGroup.ker_mk']
    exact hx
  rw [MonoidHom.mem_ker.1 hk]
  exact one_mem _

theorem augT_eq_one_of_mem_thetaSubTemp {γ : TempPi D O V hV} (hγ : γ ∈ thetaSubTemp D O V hV) :
    augT D O V hV γ = 1 := by
  obtain ⟨x, -, hxe⟩ := hγ
  change piToGk D (tempToPi D O V hV γ) = 1
  rw [← hxe]
  exact x.2

theorem smul_eq_of_mem_thetaSubTemp {γ : TempPi D O V hV} (hγ : γ ∈ thetaSubTemp D O V hV)
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) : γ • ζ = ζ := by
  rw [← act_augT_psiMu D O V hV n γ ζ]
  simp [act, augT_eq_one_of_mem_thetaSubTemp hγ]

/-- **The Kummer cocycles**: all continuous cocycles `G → μ`. For `G = G_k`, `μ = μ_n(Ω)` and
`ψ = psiMu n` these are exactly the representatives of the Kummer classes of `k^×`, by Kummer
theory `k^×/(k^×)^n ≃* H¹(G_k, μ_n)` (ckt `KummerTheory.kummer_surjective` /
`KummerTheory.kummerEquiv`): `exists_kummer_of_mem_contCocycles` (every element represents a
Kummer class `κ_n(a)`, `a ∈ k^×`) and `exists_mem_contCocycles_kummer` (every Kummer class has a
representative here), both in `Env/ThetaTower.lean`. -/
def contCocycles {G μ : Type u} [Group G] [TopologicalSpace G] [CommGroup μ] [TopologicalSpace μ]
    [IsTopologicalGroup μ] (ψ : G →* MulAut μ) : Subgroup (G → μ) where
  carrier := {κ | IsCocycle ψ κ ∧ Continuous κ}
  mul_mem' := fun ha hb => ⟨isCocycle_mul ha.1 hb.1, ha.2.mul hb.2⟩
  one_mem' := ⟨isCocycle_one, continuous_const⟩
  inv_mem' := fun ha => ⟨isCocycle_inv' ha.1, ha.2.inv⟩

theorem isCocycle_of_mem_contCocycles {G μ : Type u} [Group G] [TopologicalSpace G] [CommGroup μ]
    [TopologicalSpace μ] [IsTopologicalGroup μ] (ψ : G →* MulAut μ) :
    ∀ κ ∈ contCocycles ψ, IsCocycle ψ κ := fun _ h => h.1

end Setting

/-! ### Representative cocycles -/

section Rep

variable {P M : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]

/-- A representative cocycle of a class in `H¹_cont(P, M)`. -/
def repCocycle (x : ContH1 P M) : P → M := ((Quotient.out x : ContH1.cocycles P M) : P → M)

theorem mk_repCocycle (x : ContH1 P M) :
    ContH1.mk (Quotient.out x : ContH1.cocycles P M) = x :=
  Quotient.out_eq x

theorem repCocycle_eq_evalTriv (x : ContH1 P M) (g : P) (hg : ∀ m : M, g • m = m) :
    repCocycle x g = ContH1.evalTriv g hg x := by
  conv_rhs => rw [← mk_repCocycle x]
  rfl

/-- The representative is a cocycle for any `MulAut`-valued description `φ` of the action. -/
theorem isCocycle_repCocycle (φ : P →* MulAut M) (hφ : ∀ g m, φ g m = g • m) (x : ContH1 P M) :
    IsCocycle φ (repCocycle x) := by
  intro g h
  have := (Quotient.out x : ContH1.cocycles P M).2.2 g h
  simp only [repCocycle] at this ⊢
  rw [this, hφ, mul_comm]

end Rep

/-! ### [EtTh] Cor. 2.19(i) for the model environment of a class on `Π^tp_Ÿ` (generic levels) -/

section Generic

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

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
variable (T hL) in
/-- `Π^tp_Ÿ ≤ Π^tp_Y`. -/
theorem piYddotX_le_piY : PYddg ≤ PYg := inf_le_left

variable (T hL) in
/-- **`L = Π^tp_Ÿ ∩ (preimage of Δ_Θ)`**, the input `Π|_{Δ_Θ}` of [EtTh] Cor. 2.19(i). -/
def thetaL : Subgroup PXg := PYddg ⊓ thetaSubTemp DXg O V hV

variable (T hL) in
/-- **`Kθ = Π^tp_Ÿ ∩ Ker(Δ^tp_X ↠ Δ_X^Θ)`** ([EtTh], Prop. 1.3: the theta class comes from
`(Π^tp_Y)^Θ`). -/
def thetaK : Subgroup PXg := PYddg ⊓ thetaKernelTemp DXg O V hV

theorem thetaK_le_thetaL : thetaK T hL ≤ thetaL T hL (O := O) (V := V) (hV := hV) :=
  inf_le_inf_left _ thetaKernelTemp_le_thetaSubTemp

theorem thetaL_le_piYddotX : thetaL T hL (O := O) (V := V) (hV := hV) ≤ PYddg := inf_le_left

theorem augT_eq_one_of_mem_thetaL {γ : PXg} (hγ : γ ∈ thetaL T hL) : augg γ = 1 :=
  augT_eq_one_of_mem_thetaSubTemp hγ.2

theorem smul_eq_of_mem_thetaL {γ : PYddg} (hγ : (γ : PXg) ∈ thetaL T hL) (n : ℕ) [NeZero n]
    (ζ : Mu n Ω) : γ • ζ = ζ :=
  smul_eq_of_mem_thetaSubTemp hγ.2 n ζ

variable (n : ℕ) [NeZero n]

theorem isCocycle_repCocycle_theta (x : ContH1 PYddg (Mu n Ω)) :
    IsCocycle (actDD augg (psiMu (k := k) (Ω := Ω) n) PYddg) (repCocycle x) :=
  isCocycle_repCocycle (actDD augg (psiMu (k := k) (Ω := Ω) n) PYddg)
    (fun g m => act_augT_psiMu DXg O V hV n (g : PXg) m) x

variable (T hL) in
/-- **The model mono-theta environment of a class** `x ∈ H¹(Π^tp_Ÿ, μ_n)` ([EtTh], Def. 2.13(ii)):
`Π^tp_Y[μ_n]`, `D_Y` generated by `Π^tp_X`-conjugation and the Kummer twists of all continuous
cocycles of `G_k`, and the `μ_n`-conjugacy class of the theta section `s^alg − x`. -/
def thetaEnv (x : ContH1 PYddg (Mu n Ω)) : MonoThetaEnv.{u} :=
  modelEnv augg (psiMu n) (contCocycles (psiMu n)) (piYddotX_le_piY T hL)
    (isOpen_ker_act_augT DXg O V hV n) (isCocycle_of_mem_contCocycles _)
    (isCocycle_repCocycle_theta n x)

/-- `hη13` in the form of the abstract theorems, from the vanishing of the class on `Kθ`. -/
theorem repCocycle_eq_one_of_thetaK {x : ContH1 PYddg (Mu n Ω)}
    (hx13 : ∀ (γ : PYddg) (hγ : (γ : PXg) ∈ thetaKernelTemp DXg O V hV),
      ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) x = 1) :
    ∀ g (hg : g ∈ PYddg), g ∈ thetaK T hL → repCocycle x ⟨g, hg⟩ = 1 := fun g hg hgK =>
  (repCocycle_eq_evalTriv x _ (thetaKernelTemp_smul_mu (γ := ⟨g, hg⟩) hgK.2 n)).trans
    (hx13 ⟨g, hg⟩ hgK.2)

/-- **[EtTh], Cor. 2.19(i) (cyclotomic rigidity) for the model environment of a class on
`Π^tp_Ÿ`** (generic levels): if the class `x ∈ H¹(Π^tp_Ÿ, μ_n)` vanishes on `Π^tp_Ÿ ∩ Kθ`
([EtTh] Prop. 1.3, MR14's `classAt_eq_one_of_thetaKernel`), then for any mono-theta environment
`M` and any isomorphism `f : M ≅ thetaEnv x` respecting the input subgroups
(`Π|_{Δ_Θ}`, `Ker(Π ↠ Π|_{(Π_Y)^Θ})`, `Π|_{Δ_Y}`), the algorithmic isomorphism of cyclotomes of
`M` is carried to `s^alg(l) ↦ x(l)⁻¹` on `L = Π^tp_Ÿ ∩ (preimage of Δ_Θ)`.

Named hypotheses (Layer-B debts): `hPY` (`FISlim Π^tp_Y`, obligation 1), `hG` (`G_k`
center-free), `hsurj` (`Π^tp_Y ↠ G_k`, obligation 5), `hLgen` (Prop. 2.12(i)-type generation of
`L` by `Kθ` and geometric commutators). -/
theorem cyclotomicRigidity_thetaEnv (hPY : Envelope.FISlim PYg)
    (hG : ∀ τ : Gk k Ω, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : Gk k Ω, ∃ h ∈ PYg, augg h = σ)
    (hLgen : Subgroup.closure {c | c ∈ thetaL T hL ∧ ∃ a b, augg a = 1 ∧ b ∈ PYg ∧ augg b = 1 ∧
      c = ⁅a, b⁆} ⊔ thetaK T hL = thetaL T hL)
    {x : ContH1 PYddg (Mu n Ω)}
    (hx13 : ∀ (γ : PYddg) (hγ : (γ : PXg) ∈ thetaKernelTemp DXg O V hV),
      ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) x = 1)
    {M : MonoThetaEnv.{u}} (f : MonoThetaEnv.Iso M (thetaEnv T hL n x))
    {Lsub Ksub Dsub : Subgroup M.G}
    (hLs : Lsub.map f.hom = rightSub augg (psiMu n) PYg (thetaL T hL))
    (hKs : Ksub.map f.hom = rightSub augg (psiMu n) PYg (thetaK T hL))
    (hDs : Dsub.map f.hom = geomSub augg (psiMu n) PYg) (t m : M.G) :
    M.IsCyc Lsub Ksub Dsub t m ↔ ∃ l : PYddg, ∃ hl : (l : PXg) ∈ thetaL T hL,
      f.e t = algSection augg (psiMu n) (piYddotX_le_piY T hL) l ∧
      f.e m = inlY augg (psiMu n) PYg (ContH1.evalTriv l (smul_eq_of_mem_thetaL hl n) x)⁻¹ := by
  rw [cyclotomicRigidity_env augg (psiMu n) (contCocycles (psiMu n)) (piYddotX_le_piY T hL)
    (isOpen_ker_act_augT DXg O V hV n) (isCocycle_of_mem_contCocycles _)
    (isCocycle_repCocycle_theta n x) hPY hG hsurj (thetaL T hL) (thetaK T hL) thetaK_le_thetaL
    thetaL_le_piYddotX (fun l hl => augT_eq_one_of_mem_thetaL hl)
    (repCocycle_eq_one_of_thetaK n hx13) hLgen f hLs hKs hDs t m]
  constructor
  · rintro ⟨l, hl, h1, h2⟩
    exact ⟨l, hl, h1, h2.trans (congrArg (fun z => inlY augg (psiMu n) PYg z⁻¹)
      (repCocycle_eq_evalTriv x l (smul_eq_of_mem_thetaL hl n)))⟩
  · rintro ⟨l, hl, h1, h2⟩
    exact ⟨l, hl, h1, h2.trans (congrArg (fun z => inlY augg (psiMu n) PYg z⁻¹)
      (repCocycle_eq_evalTriv x l (smul_eq_of_mem_thetaL hl n)).symm)⟩

/-- **Automorphisms over the identity of `Π^tp_Y` act trivially on `μ_n`** ([EtTh], proof of
Cor. 2.18(iv), via Cor. 2.19(i)), for the model environment of a class `x` vanishing on `Kθ`
and mapping `L` onto `μ_n` (`hxL`: in [EtTh], the restriction of the theta class to `Δ_Θ` is
the natural surjection `Δ_Θ ↠ μ_n`, Prop. 1.3). -/
theorem ker_autPY_inlY_eq_thetaEnv (hPY : Envelope.FISlim PYg)
    (hG : ∀ τ : Gk k Ω, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : Gk k Ω, ∃ h ∈ PYg, augg h = σ)
    (hLgen : Subgroup.closure {c | c ∈ thetaL T hL ∧ ∃ a b, augg a = 1 ∧ b ∈ PYg ∧ augg b = 1 ∧
      c = ⁅a, b⁆} ⊔ thetaK T hL = thetaL T hL)
    {x : ContH1 PYddg (Mu n Ω)}
    (hx13 : ∀ (γ : PYddg) (hγ : (γ : PXg) ∈ thetaKernelTemp DXg O V hV),
      ContH1.evalTriv γ (thetaKernelTemp_smul_mu hγ n) x = 1)
    (hxL : ∀ m : Mu n Ω, ∃ l : PYddg, ∃ hl : (l : PXg) ∈ thetaL T hL,
      ContH1.evalTriv l (smul_eq_of_mem_thetaL hl n) x = m)
    {a : CategoryTheory.Aut (thetaEnv T hL n x)}
    (ha : a ∈ (autPY augg (psiMu n) (contCocycles (psiMu n)) (piYddotX_le_piY T hL)
      (isOpen_ker_act_augT DXg O V hV n) (isCocycle_of_mem_contCocycles _)
      (isCocycle_repCocycle_theta n x) hPY).ker) (m : Mu n Ω) :
    autE augg (psiMu n) (contCocycles (psiMu n)) (piYddotX_le_piY T hL)
      (isOpen_ker_act_augT DXg O V hV n) (isCocycle_of_mem_contCocycles _)
      (isCocycle_repCocycle_theta n x) a (inlY augg (psiMu n) PYg m) =
      inlY augg (psiMu n) PYg m := by
  refine ker_autPY_inlY_eq (aug := augg) (ψ := psiMu n) (Kum := contCocycles (psiMu n))
    (hle := piYddotX_le_piY T hL) (hψ := isOpen_ker_act_augT DXg O V hV n)
    (hKum := isCocycle_of_mem_contCocycles _) (hη := isCocycle_repCocycle_theta n x) (hPY := hPY)
    hG hsurj (thetaL T hL) (thetaK T hL) thetaK_le_thetaL
    thetaL_le_piYddotX (fun l hl => augT_eq_one_of_mem_thetaL hl)
    (repCocycle_eq_one_of_thetaK n hx13) hLgen (fun m => ?_) ha m
  obtain ⟨l, hl, hlm⟩ := hxL m⁻¹
  exact ⟨l, hl, by rw [repCocycle_eq_evalTriv x l (smul_eq_of_mem_thetaL hl n), hlm, inv_inv]⟩

/-- **The cusp inertia lies in `L`** once it maps into `Δ_Θ` (the `WeilTameAt` clause of the debt
`CuspInertiaWeil`). -/
theorem inertiaToTempered_mem_thetaSubTemp {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W)
    (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ : inertiaToTheta DXg hk (inertiaX σ) ∈ thetaSubD DXg) :
    inertiaToTempered O (fieldData ht LX hLX).A hV hVW σ ∈ thetaSubTemp DXg O V hV :=
  ⟨inertiaToDelta DXg hk (inertiaX σ), hσ,
    (tempToPi_inertiaToTempered DXg O hV hVW σ).symm⟩

theorem inertiaToTempered_mem_thetaL {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W)
    (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
    (hσ : inertiaToTheta DXg hk (inertiaX σ) ∈ thetaSubD DXg) :
    inertiaToTempered O (fieldData ht LX hLX).A hV hVW σ ∈ thetaL T hL :=
  ⟨inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0,
    inertiaToTempered_mem_thetaSubTemp hk hVW σ hσ⟩

end Generic

/-! ### The concrete theta system of the Tate curve -/

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
/-- **[EtTh], Cor. 2.19(i) and the `μ_n`-part of Cor. 2.18(iv) for the mono-theta environments
of the étale theta system** (`X = E_q ∖ {O}`, `Δ_Θ`; Layer B). For the theta system of
`exists_thetaClassTemp_prop13` and every base point `V` over `O`, under C1:

* (**cyclotomic rigidity**) for every `n ≥ 1`, the model environment `thetaEnv` of the theta class
  `thetaClassTemp η n` satisfies Cor. 2.19(i): for any `M ≅ thetaEnv` respecting the input
  subgroups, the algorithmic isomorphism of cyclotomes is `s^alg(l) ↦ θ_n(l)⁻¹` on
  `L = Π^tp_Ÿ ∩ (preimage of Δ_Θ)`. Obligation 8 (`hη13`) is discharged here by MR14's Prop. 1.3;
* (**no automorphisms on `μ_n`**) if `V` lies under a place `W` over the cusp, then under the
  debts `InertiaFixesLevel (L 0)` and `CuspInertiaWeil`, automorphisms of `thetaEnv` over the
  identity of `Π^tp_Y` act trivially on `μ_n`. Obligation 11 (`hηL`) is discharged here by the
  cusp inertia (`classAt_cusp_surjective`, `classAt_deltaTheta`).

The remaining hypotheses are the Layer-B debts `hPY` (`FISlim Π^tp_Y`), `hG` (`G_K`
center-free), `hsurj` (`Π^tp_Y ↠ G_K`) and `hLgen` (Prop. 2.12(i)-type generation). -/
theorem exists_thetaEnv_rigidity :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (Iut.EtaleTheta.DX t).R
        (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
        (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (n : ℕ) [NeZero n]
        (hPY : Envelope.FISlim (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV))
        (_ : ∀ τ' : Gk K Ω, (∀ σ, τ' * σ = σ * τ') → τ' = 1)
        (_ : ∀ σ : Gk K Ω, ∃ h ∈ TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV,
          augT DXc O V hV h = σ)
        (_ : Subgroup.closure {c | c ∈ thetaL (tateDataX O hO hs h12) hL ∧ ∃ a b,
            augT DXc O V hV a = 1 ∧
            b ∈ TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV ∧
            augT DXc O V hV b = 1 ∧ c = ⁅a, b⁆} ⊔ thetaK (tateDataX O hO hs h12) hL =
          thetaL (tateDataX O hO hs h12) hL),
        (∀ {M : MonoThetaEnv.{u}}
          (f : MonoThetaEnv.Iso M (thetaEnv (tateDataX O hO hs h12) hL n (thetaClassTemp η hC1 n)))
          {Lsub Ksub Dsub : Subgroup M.G}
          (_ : Lsub.map f.hom = rightSub (augT DXc O V hV) (psiMu n)
            (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV)
            (thetaL (tateDataX O hO hs h12) hL))
          (_ : Ksub.map f.hom = rightSub (augT DXc O V hV) (psiMu n)
            (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV)
            (thetaK (tateDataX O hO hs h12) hL))
          (_ : Dsub.map f.hom = geomSub (augT DXc O V hV) (psiMu n)
            (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV)) (t' m : M.G),
          M.IsCyc Lsub Ksub Dsub t' m ↔
            ∃ l : piYddotX V hV (tateDataX O hO hs h12) hL,
            ∃ hl : (l : TempPi DXc O V hV) ∈ thetaL (tateDataX O hO hs h12) hL,
              f.e t' = algSection (augT DXc O V hV) (psiMu n)
                (piYddotX_le_piY (tateDataX O hO hs h12) hL) l ∧
              f.e m = inlY (augT DXc O V hV) (psiMu n)
                (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV)
                (ContH1.evalTriv l (smul_eq_of_mem_thetaL hl n) (thetaClassTemp η hC1 n))⁻¹) ∧
        ∀ (W : ValuationSubring Ω) (_ : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W → V ≤ W →
          InertiaFixesLevel (transcendental_tau t.tateCurve) (hemiL_open t) (L 0) W →
          CuspInertiaWeil (DXc) →
          ∀ {a : CategoryTheory.Aut
              (thetaEnv (tateDataX O hO hs h12) hL n (thetaClassTemp η hC1 n))},
            a ∈ (autPY (augT DXc O V hV) (psiMu n) (contCocycles (psiMu n))
              (piYddotX_le_piY (tateDataX O hO hs h12) hL) (isOpen_ker_act_augT DXc O V hV n)
              (isCocycle_of_mem_contCocycles _)
              (isCocycle_repCocycle_theta n (thetaClassTemp η hC1 n)) hPY).ker →
            ∀ m : Mu n Ω,
              autE (augT DXc O V hV) (psiMu n) (contCocycles (psiMu n))
                (piYddotX_le_piY (tateDataX O hO hs h12) hL) (isOpen_ker_act_augT DXc O V hV n)
                (isCocycle_of_mem_contCocycles _)
                (isCocycle_repCocycle_theta n (thetaClassTemp η hC1 n)) a
                (inlY (augT DXc O V hV) (psiMu n)
                  (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV) m) =
              inlY (augT DXc O V hV) (psiMu n)
                (TateObject.piY (A := (DXc).A) (tateDataX O hO hs h12) V hV) m) := by
  obtain ⟨L, hL, hX, het, η, htr, hcomp, hker, hcusp, hdelta⟩ :=
    exists_thetaClassTemp_prop13 h2 h12 hs O hO
  refine ⟨L, hL, hX, het, η, htr, hcomp, fun V hV hC1 n _ hPY hG hsurj hLgen => ?_⟩
  have hdvd : n ∣ 2 * (n - 1 + 1) :=
    ⟨2, by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))]; ring⟩
  have hx13 := hker V hV hC1 (n - 1) n hdvd
  refine ⟨fun f _ _ _ hLs hKs hDs t' m =>
    cyclotomicRigidity_thetaEnv n hPY hG hsurj hLgen hx13 f hLs hKs hDs t' m,
    fun W hk hτ hVW hL0 hG5 a ha m => ?_⟩
  obtain ⟨e, he⟩ := hdelta hG5
  refine ker_autPY_inlY_eq_thetaEnv n hPY hG hsurj hLgen hx13 (fun m => ?_) ha m
  obtain ⟨σ, hσ⟩ := (hcusp W hk hτ).2 V hV hVW hC1 hL0 n m
  obtain ⟨hσΘ, -⟩ := (he W hk hτ).2 V hV hVW hC1 hL0 σ
  exact ⟨⟨_, inertiaToTempered_mem_piYddotX V hV _ hL hVW σ (hL0 σ)⟩,
    inertiaToTempered_mem_thetaL hk hVW σ (hL0 σ) hσΘ, hσ⟩

end Concrete

end Iut.EtaleTheta.Env
