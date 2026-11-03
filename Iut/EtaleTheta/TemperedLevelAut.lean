/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTemperedClass

/-!
# Algebra maps of a level ring into `Ω` come from Galois automorphisms

Let `F ≤ F'` be intermediate fields of `Ω / k(t)`, finite over `k(t)`, with `Ω / k(t)` Galois, and
let `R ⊆ R'` be their coordinate rings (the integral closures of `k[t]`). Every ring map
`φ : R' → Ω` restricting to the inclusion on `R` is `σ|_{R'}` for an automorphism `σ` of `Ω` over
`k(t)` fixing `F` (`exists_aut_of_ringHom`): `φ` is injective (`R'` is a domain integral over
`k[t]`, on which `φ` is the inclusion), extends to the fraction field `F'` of `R'`, is
`k(t)`-linear there, and extends to `Ω` (`AlgHom.liftNormal`); an algebraic endomorphism of `Ω`
is bijective, and `σ` fixes `F` because it fixes the coordinate ring of `F`.

`exists_aut_of_algHom` is the form for the levels `fieldData L` of `ThetaTemperedClass`
(`R'`-algebra maps over `R`, `algXL`).
-/

open Pi1.Orbifold AffOrbicurve CurvesJacobian.Cusp IntermediateField.algebraAdjoinAdjoin

noncomputable section

universe u

namespace Iut.EtaleTheta

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- **A ring map `R' → Ω` over `R` is the restriction of an automorphism of `Ω`** fixing `F`
(`R ⊆ R'` the coordinate rings of `F ≤ F'`, both finite over `k(t)`, `Ω / k(t)` Galois). -/
theorem exists_aut_of_ringHom [IsGalois (K₀ k t) Ω] {F F' : IntermediateField (K₀ k t) Ω}
    (h : F ≤ F') [FiniteDimensional (K₀ k t) F] [FiniteDimensional (K₀ k t) F']
    (φ : CoordRing k t F' →+* Ω)
    (hφ : ∀ x : CoordRing k t F,
      φ (@algebraMap _ _ _ _ (CoordRing.algOfLE h) x) = algebraMap _ Ω x) :
    ∃ σ : Ω ≃ₐ[K₀ k t] Ω, (∀ z ∈ F, σ z = z) ∧
      ∀ r : CoordRing k t F', φ r = σ (algebraMap _ Ω r) := by
  -- `φ` is the inclusion on `k[t]`
  have hA : ∀ a : A₀ k t, φ (algebraMap (A₀ k t) (CoordRing k t F') a) = (a : Ω) := by
    intro a
    have e : @algebraMap _ _ _ _ (CoordRing.algOfLE h) (algebraMap (A₀ k t) (CoordRing k t F) a) =
        algebraMap (A₀ k t) (CoordRing k t F') a := CoordRing.ext rfl
    rw [← e, hφ]
    rfl
  -- `φ` is injective
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    refine Ideal.comap_ne_bot_of_integral_mem (R := A₀ k t) (I := RingHom.ker φ) hx0
      (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hA] at ha
    exact (Submodule.mem_bot _).2 (Subtype.ext ha)
  -- the extension to the fraction field `F'`
  haveI := isFractionRing_coordRing t F'
  let g : coordRing k t F' →+* Ω := φ
  let ψ : F' →+* Ω := IsFractionRing.lift (A := coordRing k t F') (g := g) hinj
  have hψ : ∀ r : CoordRing k t F', ψ (algebraMap (coordRing k t F') F' r) = φ r :=
    fun r => IsFractionRing.lift_algebraMap (A := coordRing k t F') (g := g) hinj r
  have hK : ψ.comp (algebraMap (K₀ k t) F') = algebraMap (K₀ k t) Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A₀ k t)) (RingHom.ext fun a => ?_)
    have e : algebraMap (K₀ k t) F' (algebraMap (A₀ k t) (K₀ k t) a) =
        algebraMap (coordRing k t F') F' (algebraMap (A₀ k t) (CoordRing k t F') a) :=
      Subtype.ext rfl
    simp only [RingHom.comp_apply]
    rw [e, hψ, hA]
    rfl
  let ψ' : F' →ₐ[K₀ k t] Ω :=
    { ψ with commutes' := fun c => congrArg (fun f : K₀ k t →+* Ω => f c) hK }
  let σ' : Ω →ₐ[K₀ k t] Ω := ψ'.liftNormal Ω
  let σ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofBijective σ' (Algebra.IsAlgebraic.algHom_bijective σ')
  have key : ∀ r : CoordRing k t F', σ (algebraMap _ Ω r) = φ r := by
    intro r
    have := AlgHom.liftNormal_commutes (E := Ω) ψ' (algebraMap (coordRing k t F') F' r)
    exact this.trans (hψ r)
  refine ⟨σ, ?_, fun r => (key r).symm⟩
  have hfix : σ ∈ F.fixingSubgroup := CoordRing.mem_fixingSubgroup_of_forall σ fun x =>
    (key (@algebraMap _ _ _ _ (CoordRing.algOfLE h) x)).trans (hφ x)
  exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 hfix

end Generic

section Levels

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  {LX : IntermediateField (K₀ k t) Ω} (hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω)))
  (L' : IntermediateField (K₀ k t) Ω)
  (hL' : IsOpen (L'.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))) [hX : Fact (LX ≤ L')]

/-- **`R`-algebra maps `R' → Ω` of a change of level come from Galois automorphisms**:
`φ = σ|_{R'}` for an automorphism `σ` of `Ω` over `k(t)` fixing `L_X`
(`R`, `R'` the coordinate rings of `fieldData LX`, `fieldData L'`). -/
theorem exists_aut_of_algHom [IsGalois (K₀ k t) Ω]
    (φ : (fieldData ht L' hL').R →ₐ[(fieldData ht LX hLX).R] Ω) :
    ∃ σ : Ω ≃ₐ[K₀ k t] Ω, (∀ z ∈ LX, σ z = z) ∧ ∀ r, φ r = σ (algebraMap _ Ω r) := by
  obtain ⟨σ, h1, h2⟩ := exists_aut_of_ringHom (fieldData_L_le ht hLX hL' hX.out) φ.toRingHom
    (fun x => φ.commutes x)
  refine ⟨σ, fun z hz => h1 z ?_, h2⟩
  rwa [fieldData_L]

end Levels

end Iut.EtaleTheta
