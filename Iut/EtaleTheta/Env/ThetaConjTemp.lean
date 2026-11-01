/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.ThetaLTors

/-!
# Conjugation of classes on `Π^tp_Ÿ` and the coboundaries of obligation 13 (MR15, 13c(iii))

For `e` normalising a subgroup `H` (for us `e ∈ Π^tp_X̿`, `H = Π^tp_Ÿ`, 13b), conjugation
`h ↦ e⁻¹ h e` and the action of `e` on the coefficients give
`conjH1Sub e : H¹(H, M) → H¹(H, M)`, `c ↦ (h ↦ e · c(e⁻¹ h e))`.

* `exists_coboundary_of_conjH1Sub` (generic): a `conjH1Sub e`-invariant class has representatives
  with `c(e h e⁻¹) = m · e·c(h) · ((e h e⁻¹)·m)⁻¹`;
* **`exists_hce_of_invariant`**: hence the hypothesis `hce` (resp. `hcg`) of
  `exists_cX_of_invariant` holds for `e` (resp. `g`) as soon as the class of `r mod l` is
  invariant under `conjH1Sub e` (resp. `g`).

So 13c(iii) is reduced to the **class-level invariance** of `θ mod l` (`= thetaClassTemp η l`, by
`transTemp_thetaClassTemp`) under `conjH1Sub e` and `conjH1Sub g`: the tempered transport of the
étale `conjH1_kummerMap_of_pow` (`Env/ThetaConjModL.lean`) along the level maps `toLevel` (C1)
and the translation homomorphism `w_j` (13c(i)), with MR14's 13c(ii) as input.
-/

open scoped commutatorElement

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

/-! ### Generic: conjugation on `H¹` of a normal subgroup -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
  {M : Type*} [CommGroup M] [TopologicalSpace M] [DiscreteTopology M] [MulDistribMulAction G M]
  (e : G) (hHn : ∀ h ∈ H, e⁻¹ * h * e ∈ H)

/-- Conjugation `h ↦ e⁻¹ h e` on `H`. -/
def conjSub : H →* H where
  toFun h := ⟨e⁻¹ * (h : G) * e, hHn (h : G) h.2⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem coe_conjSub (h : H) : ((conjSub H e hHn h : H) : G) = e⁻¹ * (h : G) * e := rfl

theorem continuous_conjSub : Continuous (conjSub H e hHn) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun h : H => e⁻¹ * (h : G) * e
  fun_prop

/-- **Conjugation by `e` on `H¹(H, M)`**: `c ↦ (h ↦ e · c(e⁻¹ h e))`. -/
def conjH1Sub : ContH1 H M →* ContH1 H M :=
  ContH1.map (conjSub H e hHn) (continuous_conjSub H e hHn)
    (MulDistribMulAction.toMonoidHom M e) continuous_of_discreteTopology
    (fun h ζ => by
      change e • ((e⁻¹ * (h : G) * e) • ζ) = (h : G) • e • ζ
      rw [← mul_smul, ← mul_smul]
      congr 1
      group)

variable {H e hHn}

/-- **From class-level invariance to the coboundary form**: if the class of `c` is invariant
under `conjH1Sub e`, then `c(e h e⁻¹) = m · e·c(h) · ((e h e⁻¹)·m)⁻¹` for some `m ∈ M`. -/
theorem exists_coboundary_of_conjH1Sub (c : ContH1.cocycles H M)
    (hcl : conjH1Sub H e hHn (ContH1.mk c) = ContH1.mk c)
    (hHn' : ∀ h ∈ H, e * h * e⁻¹ ∈ H) :
    ∃ m : M, ∀ (h : G) (hh : h ∈ H),
      c ⟨e * h * e⁻¹, hHn' h hh⟩ = m * e • c ⟨h, hh⟩ * ((e * h * e⁻¹) • m)⁻¹ := by
  obtain ⟨x, hx⟩ := (ContH1.mk_eq_mk_iff _ _).1 hcl
  refine ⟨x, fun h hh => ?_⟩
  have h1 := hx ⟨e * h * e⁻¹, hHn' h hh⟩
  have harg : conjSub H e hHn ⟨e * h * e⁻¹, hHn' h hh⟩ = ⟨h, hh⟩ := by
    ext1
    simp [mul_assoc]
  change (e * h * e⁻¹) • x / x = e • c (conjSub H e hHn ⟨e * h * e⁻¹, hHn' h hh⟩) /
    c ⟨e * h * e⁻¹, hHn' h hh⟩ at h1
  rw [harg, div_eq_div_iff_mul_eq_mul] at h1
  rw [eq_mul_inv_iff_mul_eq, mul_comm x, ← h1, mul_comm]

end Generic

/-! ### The hypotheses `hce`, `hcg` of `exists_cX_of_invariant` -/

section Levels

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  {l : ℕ} [NeZero l] {N : ℕ} [NeZero N]
  (r : ContH1.cocycles (piYddotX V hV T hL) (Mu (l * N) Ω))

/-- **`hce` (and `hcg`) from the invariance of `θ mod l`**: if the class of `r mod l` on `Π^tp_Ÿ`
(`transTemp … (mk r)`; `= thetaClassTemp η l` when `[r] = θ_{lN}`) is invariant under conjugation by
`e` (`conjH1Sub`), then the hypothesis `hce` of `exists_cX_of_invariant` holds for `e` with some
`me ∈ μ_l`. -/
theorem exists_hce_of_invariant (e : TempPi (fieldData ht LX hLX) O V hV)
    (hHn : ∀ h ∈ piYddotX V hV T hL, e⁻¹ * h * e ∈ piYddotX V hV T hL)
    (hHn' : ∀ h ∈ piYddotX V hV T hL, e * h * e⁻¹ ∈ piYddotX V hV T hL)
    (hcl : conjH1Sub (piYddotX V hV T hL) e hHn
        (transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) =
      transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) :
    ∃ me : Mu l Ω, ∀ (h : TempPi (fieldData ht LX hLX) O V hV) (hh : h ∈ piYddotX V hV T hL),
      redCocycle r ⟨e * h * e⁻¹, hHn' h hh⟩ =
        me * act (augT (fieldData ht LX hLX) O V hV) (psiMu l) e (redCocycle r ⟨h, hh⟩) *
          (act (augT (fieldData ht LX hLX) O V hV) (psiMu l) (e * h * e⁻¹) me)⁻¹ := by
  obtain ⟨m, hm⟩ := exists_coboundary_of_conjH1Sub _ hcl hHn'
  refine ⟨m, fun h hh => ?_⟩
  rw [act_augT_psiMu, act_augT_psiMu]
  exact hm h hh

/-- **Obligation 13 reduced to class-level invariance**: with the structure inputs of
`exists_cX_of_invariant` (13a: `χ(g) = l`; 13b: `Π^tp_Ÿ ⊴ Π^tp_X̿`, `e`, index 2), if the class of
`r mod l` on `Π^tp_Ÿ` is invariant under conjugation by `e` and by `g` (13c: [EtTh] Prop. 1.5(iii)
mod `l` on `lℤ`, tempered form), a splitting cocycle `cX` with `hcXr` exists (`l` odd). -/
theorem exists_cX_of_classInvariant (hl : Odd l)
    (hHn : ∀ x ∈ piXdd V hV T l, ∀ h ∈ piYddotX V hV T hL, x * h * x⁻¹ ∈ piYddotX V hV T hL)
    {e g : TempPi (fieldData ht LX hLX) O V hV}
    (heY : e ∈ Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)
    (he : e ∉ piYddotX V hV T hL) (he2 : e * e ∈ piYddotX V hV T hL)
    (hidx : ∀ y ∈ Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV,
      y ∈ piYddotX V hV T hL ∨ y * e⁻¹ ∈ piYddotX V hV T hL)
    (hg : TemperedFundamentalGroups.TateObject.character (A := (fieldData ht LX hLX).A) T V hV g =
      Multiplicative.ofAdd (l : ℤ))
    (hHe : ∀ h ∈ piYddotX V hV T hL, e⁻¹ * h * e ∈ piYddotX V hV T hL)
    (hHg : ∀ h ∈ piYddotX V hV T hL, g⁻¹ * h * g ∈ piYddotX V hV T hL)
    (hcle : conjH1Sub (piYddotX V hV T hL) e hHe
        (transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) =
      transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r))
    (hclg : conjH1Sub (piYddotX V hV T hL) g hHg
        (transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) =
      transTemp T hL (Dvd.intro N rfl : l ∣ l * N) (ContH1.mk r)) :
    ∃ (cX : piXdd V hV T l → Mu l Ω)
      (_ : IsCocycle (actDD (augT (fieldData ht LX hLX) O V hV) (psiMu (k := k) (Ω := Ω) l)
        (piXdd V hV T l)) cX),
      ∀ (γ : piYddotX V hV T hL) (h : (γ : TempPi (fieldData ht LX hLX) O V hV) ∈ piXdd V hV T l),
        cX ⟨γ, h⟩ = Mu.transition (Dvd.intro N rfl : l ∣ l * N) (r γ) := by
  have hgdd : g ∈ piXdd V hV T l := by
    change _ ∈ Subgroup.zpowers _; rw [hg]; exact Subgroup.mem_zpowers _
  obtain ⟨me, hme⟩ := exists_hce_of_invariant r e hHe (hHn e (piY_le_piXdd l heY)) hcle
  obtain ⟨mg, hmg⟩ := exists_hce_of_invariant r g hHg (hHn g hgdd) hclg
  exact exists_cX_of_invariant r hl hHn heY he he2 hidx hg me mg hme hmg

end Levels

end Iut.EtaleTheta.Env
