/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.LineInertiaS
import CurvesJacobian.Cusp.CurveInertiaIso
import Mathlib.Tactic.Group

/-!
# Cuspidal generators of finite quotients of `π₁ᵉᵗ(ℙ¹ ∖ {three points})`

* **`LineCuspGenerators.ordProd_eq_one`, `closure_pair_eq_top`**: for a continuous surjection
  `h : Π̂_{0,3} ↠ G` onto a discrete group, the images `z j = h(c_j)` of the cuspidal generators
  satisfy `z₀ z₁ z₂ = 1` and any two of them generate `G`;
* **`LineCuspGenerators.exists_cusp_gen`**: with curves-jacobian's
  `exists_continuousMulEquiv_lineInertiaS` (`π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞})) ≅ Π̂_{0,3}` for `|S| = 2`,
  inertia of places over cusps ↦ conjugates of cuspidal inertia), every continuous surjection
  `f : π₁ᵉᵗ ↠ G` onto a discrete group has elements `g c` (one per cusp `c`) with product `1` (in
  the cusp numbering of `Θ`) and pairwise generating `G`, such that each `g c` is a conjugate
  `f τ · x · (f τ)⁻¹` of an element `x` of every subgroup `H` containing `f(lineGaloisS σ)` for all
  inertia elements `σ` of a given place `W_c` over `c`.

This is the group-theoretic half of MR13's B4′ (generation of the Galois group of a tame special
cover by stabilisers of special points over the cusps).
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion Pi1 Pi1.SurfaceGroup
open CurvesJacobian.Cusp AffOrbicurve

universe u

noncomputable section

namespace Iut.Reconstruction.LineCuspGenerators

open SurfaceGen

section Surface

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (h : ProfiniteSurfaceGroup 0 3 →* G)

/-- The images of the cuspidal generators. -/
def z (j : Fin 3) : G := h (etaFn (GrpCat.of (SurfaceGroup 0 3)) (cusp j))

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- **The product relation** `z₀ z₁ z₂ = 1`. -/
theorem z_prod : z h 0 * z h 1 * z h 2 = 1 := by
  have hrel := congrArg (fun x ↦ h (etaFn (GrpCat.of (SurfaceGroup 0 3)) x))
    (relation (g := 0) (r := 3))
  simp only [commProd, ordProd, List.ofFn_zero, List.prod_nil, one_mul, List.ofFn_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.prod_cons, mul_one] at hrel
  have hη : ∀ x y : SurfaceGroup 0 3, etaFn (GrpCat.of (SurfaceGroup 0 3)) (x * y) =
      etaFn (GrpCat.of (SurfaceGroup 0 3)) x * etaFn (GrpCat.of (SurfaceGroup 0 3)) y :=
    fun _ _ ↦ rfl
  have hη1 : etaFn (GrpCat.of (SurfaceGroup 0 3)) (1 : SurfaceGroup 0 3) = 1 := rfl
  rw [hη, hη, map_mul, map_mul, hη1, map_one] at hrel
  simpa [z, mul_assoc] using hrel

/-- **The cuspidal images generate**: `⟨z₀, z₁, z₂⟩ = G` for `h` continuous and onto. -/
theorem closure_range_z (hc : Continuous h) (hs : Function.Surjective h) :
    Subgroup.closure (Set.range (z h)) = ⊤ := by
  set K := Subgroup.closure (Set.range (z h))
  let e : SurfaceGroup 0 3 →* G := h.comp
    ((eta (GrpCat.of (SurfaceGroup 0 3))).hom : SurfaceGroup 0 3 →* completion _)
  have he : ∀ x, e x ∈ K := by
    have htop : (⊤ : Subgroup (SurfaceGroup 0 3)) ≤ K.comap e := by
      rw [← PresentedGroup.closure_range_of, Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      rcases s with i | i | j
      · exact i.elim0
      · exact i.elim0
      · exact Subgroup.subset_closure ⟨j, rfl⟩
    exact fun x ↦ htop (Subgroup.mem_top x)
  have hcl : IsClosed (h ⁻¹' (K : Set G)) := (isClosed_discrete _).preimage hc
  have hall : ∀ y, h y ∈ K := by
    have hsub : Set.range (etaFn (GrpCat.of (SurfaceGroup 0 3))) ⊆ h ⁻¹' (K : Set G) := by
      rintro _ ⟨x, rfl⟩
      exact he x
    have := closure_minimal hsub hcl
    rw [(denseRange (GrpCat.of (SurfaceGroup 0 3))).closure_range] at this
    exact fun y ↦ this (Set.mem_univ y)
  exact eq_top_iff.2 fun g _ ↦ by
    obtain ⟨y, rfl⟩ := hs g
    exact hall y

/-- **Any two cuspidal images generate** (`z₀ z₁ z₂ = 1`). -/
theorem closure_pair_eq_top (hc : Continuous h) (hs : Function.Surjective h) (i j : Fin 3)
    (hij : i ≠ j) : Subgroup.closure {z h i, z h j} = ⊤ := by
  have hp := z_prod h
  have h0 : z h 0 = (z h 1 * z h 2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, hp])
  have h1 : z h 1 = (z h 0)⁻¹ * (z h 2)⁻¹ := by
    calc z h 1 = (z h 0)⁻¹ * (z h 0 * z h 1 * z h 2) * (z h 2)⁻¹ := by group
      _ = (z h 0)⁻¹ * (z h 2)⁻¹ := by rw [hp, mul_one]
  have h2 : z h 2 = (z h 0 * z h 1)⁻¹ := eq_inv_of_mul_eq_one_right hp
  rw [eq_top_iff, ← closure_range_z h hc hs, Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  have hmem : ∀ x ∈ ({z h i, z h j} : Set G), x ∈ Subgroup.closure {z h i, z h j} :=
    fun x hx ↦ Subgroup.subset_closure hx
  have hi := hmem _ (Set.mem_insert _ _)
  have hj := hmem _ (Set.mem_insert_of_mem _ rfl)
  set H := Subgroup.closure {z h i, z h j}
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp at hij <;>
    first
    | exact hi
    | exact hj
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hi hj ⊢
       first
       | (rw [h0]; exact H.inv_mem (H.mul_mem hi hj))
       | (rw [h0]; exact H.inv_mem (H.mul_mem hj hi))
       | (rw [h1]; exact H.mul_mem (H.inv_mem hi) (H.inv_mem hj))
       | (rw [h1]; exact H.mul_mem (H.inv_mem hj) (H.inv_mem hi))
       | (rw [h2]; exact H.inv_mem (H.mul_mem hi hj))
       | (rw [h2]; exact H.inv_mem (H.mul_mem hj hi)))

end Surface

section Line

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω}
  [IsGalois (K₀ k t) Ω] {S : Finset k} {ht : Transcendental k t}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- **Cusp generators lie in conjugates of the images of inertia**: if `Θ ∘ conj τ` maps the
inertia group of a place `W` onto the cuspidal inertia `I_j`, then for every continuous
`f : π₁ᵉᵗ → G` and every subgroup `H` containing `f (lineGaloisS σ)` for the inertia elements `σ`
of `W`, `f (Θ⁻¹ c_j)` is `f τ · x · (f τ)⁻¹` with `x ∈ H`. -/
theorem exists_mem_conj {r : ℕ} (Θ : π₁ᵉᵗ(lineGenS S ht) ≃ₜ* ProfiniteSurfaceGroup 0 r) (j : Fin r)
    (W : ValuationSubring Ω) (τ : π₁ᵉᵗ(lineGenS S ht))
    (hτ : (lineInertiaS S ht W).map ((Θ : π₁ᵉᵗ(lineGenS S ht) →* ProfiniteSurfaceGroup 0 r).comp
      (MulAut.conj τ).toMonoidHom) = Pi1.SurfaceGroup.inertia j)
    (f : π₁ᵉᵗ(lineGenS S ht) →* G) (hf : Continuous f) (H : Subgroup G)
    (hH : ∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, f (lineGaloisS S ht σ) ∈ H) :
    ∃ x ∈ H, f (Θ.symm (etaFn (GrpCat.of (SurfaceGroup 0 r)) (cusp j))) = f τ * x * (f τ)⁻¹ := by
  have hmem : etaFn (GrpCat.of (SurfaceGroup 0 r)) (cusp j) ∈ Pi1.SurfaceGroup.inertia j :=
    Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers _)
  rw [← hτ, Subgroup.mem_map] at hmem
  obtain ⟨y, hy, hyη⟩ := hmem
  have hle : lineInertiaS S ht W ≤ H.comap f := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ((isClosed_discrete _).preimage hf)
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, rfl⟩
    exact hH σ hσ
  refine ⟨f y, hle hy, ?_⟩
  rw [← hyη]
  simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ContinuousMulEquiv.symm_apply_apply]
  rw [map_mul, map_mul, map_inv]

/-- **Cusp generators of a finite quotient of `π₁ᵉᵗ(ℙ¹ ∖ (S ∪ {∞}))`, `|S| = 2`**: for a continuous
surjection `f : π₁ᵉᵗ ↠ G` onto a discrete group there are `z : Fin 3 → G` and an injective cusp
numbering `e : Option S → Fin 3` with `z₀ z₁ z₂ = 1`, any two `z i`, `z j` (`i ≠ j`)
generating `G`, and for every cusp `c`, every place `W ⊇ k` centred at `c` and every subgroup
`H` containing the images `f (lineGaloisS σ)` of the inertia elements `σ` of `W`, `z (e c)` is a
conjugate of an element of `H`. -/
theorem exists_cusp_gen [IsAlgClosed k] [CharZero k] (hS : S.card = 2)
    (f : π₁ᵉᵗ(lineGenS S ht) →* G) (hf : Continuous f) (hs : Function.Surjective f) :
    ∃ (z : Fin 3 → G) (e : Option S → Fin 3), Function.Injective e ∧ z 0 * z 1 * z 2 = 1 ∧
      (∀ i j, i ≠ j → Subgroup.closure {z i, z j} = ⊤) ∧
      ∀ (c : Option S) (W : ValuationSubring Ω), (∀ x : k, algebraMap k Ω x ∈ W) →
        W.valuation (cuspCoordS (c.map Subtype.val) t) < 1 → ∀ H : Subgroup G,
        (∀ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, f (lineGaloisS S ht σ) ∈ H) →
        ∃ y : G, ∃ x ∈ H, z (e c) = y * x * y⁻¹ := by
  obtain ⟨σ, Θ, hΘ⟩ := exists_continuousMulEquiv_lineInertiaS S (n := 1) hS ht
  let h : ProfiniteSurfaceGroup 0 3 →* G :=
    f.comp (Θ.symm : ProfiniteSurfaceGroup 0 3 →* π₁ᵉᵗ(lineGenS S ht))
  have hc : Continuous h := hf.comp Θ.symm.continuous
  have hsurj : Function.Surjective h := hs.comp Θ.symm.surjective
  refine ⟨z h, cuspIndex σ, ?_, z_prod h, fun i j hij ↦ closure_pair_eq_top h hc hsurj i j hij,
    fun c W hW hv H hH ↦ ?_⟩
  · rintro (a | a) (b | b) hab
    · rfl
    · exact absurd hab.symm (Fin.castSucc_ne_last _)
    · exact absurd hab (Fin.castSucc_ne_last _)
    · simp only [cuspIndex_some] at hab
      rw [σ.injective (Fin.castSucc_injective _ hab)]
  · obtain ⟨τ, hτ⟩ := hΘ c W hW hv
    obtain ⟨x, hx, hxe⟩ := exists_mem_conj Θ (cuspIndex σ c) W τ hτ f hf H hH
    exact ⟨f τ, x, hx, hxe⟩

end Line

section Places

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- **Places over a rational point of a transcendental coordinate**: for `x ∈ Ω` transcendental
over `k` and `c ∈ k` there is a valuation subring `W ⊇ k` of `Ω` with `v_W(x − c) < 1` (a place
centred at `x = c`; `WeilCurves.FunctionField.exists_valuationSubring_of_prime` on `k[x]`). -/
theorem exists_place (x : Ω) (hx : Transcendental k x) (c : k) :
    ∃ W : ValuationSubring Ω, (∀ c' : k, algebraMap k Ω c' ∈ W) ∧
      W.valuation (x - algebraMap k Ω c) < 1 := by
  let e := Polynomial.algEquivOfTranscendental k x hx
  let ev : (Algebra.adjoin k {x}).toSubring →+* k :=
    (Polynomial.evalRingHom c).comp e.symm.toRingEquiv.toRingHom
  haveI : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨V, hRV, hnon, -⟩ := WeilCurves.FunctionField.exists_valuationSubring_of_prime
    (Algebra.adjoin k {x}).toSubring (RingHom.ker ev)
  refine ⟨V, fun c' ↦ hRV (Subalgebra.algebraMap_mem _ c'), ?_⟩
  have hmem : x - algebraMap k Ω c ∈ (Algebra.adjoin k {x}).toSubring :=
    Subring.sub_mem _ (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ c)
  have he : (⟨_, hmem⟩ : (Algebra.adjoin k {x}).toSubring) =
      e (Polynomial.X - Polynomial.C c) := by
    apply Subtype.ext
    simp [e, Polynomial.algEquivOfTranscendental_apply]
  have hker : (⟨_, hmem⟩ : (Algebra.adjoin k {x}).toSubring) ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker, he]
    simp [ev]
  have hnu := hnon _ hker (hRV hmem)
  exact (V.valuation_lt_one_iff ⟨_, hRV hmem⟩).1 ((IsLocalRing.mem_maximalIdeal _).2 hnu)

/-- **Places over the cusps of `ℙ¹ ∖ (S ∪ {∞})`**: for every cusp `c : Option k` there is a
valuation subring `W ⊇ k` with `v_W(u_c) < 1` for the local coordinate `u_c = cuspCoordS c t`. -/
theorem exists_place_cusp {t : Ω} (ht : Transcendental k t) (c : Option k) :
    ∃ W : ValuationSubring Ω, (∀ c' : k, algebraMap k Ω c' ∈ W) ∧
      W.valuation (cuspCoordS c t) < 1 := by
  cases c with
  | some c => exact exists_place t ht c
  | none =>
    obtain ⟨W, hW, hv⟩ := exists_place t⁻¹ (fun h ↦ ht (by simpa using IsAlgebraic.inv h)) 0
    exact ⟨W, hW, by simpa using hv⟩

end Places

end Iut.Reconstruction.LineCuspGenerators
