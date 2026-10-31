/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ConstExtThmC

/-!
# [AbsTopIII] Thm 1.9 (a): closed points of `U` are determined by their decomposition groups

[GalSect] Thm 1.3 (i) (`Galois Sections.txt` l.265–266: "the closed point `x` is completely
determined by the conjugacy class of the closed subgroup `D_x`", which "follows … formally from
[Mzk1], Theorem C", l.280–281) for closed points of the affine curve `U` over a number field `k`,
in the Galois model `Π_U = Pi D`, `D = curveGaloisData k hτ`. `Thm19/PointDecomp.lean` treats
rational points; a closed point becomes rational over a finite extension `K ⊇ κ(x)` of the
field of constants, and `U_K` has the Galois model `constExt K D` with `Π_{U_K} = pr⁻¹(G_K) ⊆ Π_U`
(curves-jacobian `piRes`), to which [LocAn] Thm C applies by `Thm19/ConstExtThmC.lean`.

A place `A` of `Ω` above a point of `U` is described by `G_K ⊆ pr(D_A)` (`GkLiftsTo D K A`,
i.e. `κ(x) ⊆ K`):

* `exists_residue_eq_constExt_of_lifts`, **`ratPointConstExt`**: then `A` is a rational point of
  `U_K` (the residues of `F_K` at `A` lie in `K`; the argument of curves-jacobian
  `exists_residue_eq_constExt`, with the lifts of `G_K` given);
* `piRes_decompToPi`, `exists_piRes_decompToPi_eq`: `D_A(U_K) = D_A(U) ∩ pr⁻¹(G_K)` inside `Π_U`;
* the conjugation `A ↦ σ • A` for `σ ∈ Gal(Ω/F)`: `hk_smul`, `isIntegral_smul`,
  `conj_mem_range_decompToPi_smul` (`γ D_A γ⁻¹ ⊆ D_{σ • A}` for `γ = [σ]`),
  `gkLiftsTo_smul` (for `K` stable under `G_k`);
* **`mem_iff_of_range_decompToPi_le`**: if `D_B ⊆ D_A` (both with `G_K ⊆ pr(D_·)` and `t` regular),
  then `A` and `B` lie over the same closed point of `U` (`A ∩ F = B ∩ F`);
* **`mem_iff_of_range_decompToPi_le_conj`**: the same for `D_B ⊆ γ D_A γ⁻¹`, `γ ∈ Π_U`, when `K`
  is stable under `G_k` (e.g. normal over `k`);
* **`exists_gkLiftsTo`**: every place `A ⊇ k` with `κ(A)` algebraic and `κ(A ∩ F)` finite over `k`
  (a closed point) satisfies `G_K ⊆ pr(D_A)` for some finite `K ⊆ k̄` stable under `G_k` (the
  normal closure of `κ(A ∩ F)`; continuous-kummer-theory `exists_decompositionMap_eq_of_fixes`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn
  Belyi Belyi.Anabelian IsLocalRing

open scoped Pointwise

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K]

/-- `g ∈ G_k` fixes `K` pointwise, i.e. `g ∈ G_K`. -/
def FixesK (g : Gk k Ω) : Prop :=
  ∀ c : K, g ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ = ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩

variable (D) in
/-- **`G_K ⊆ pr(D_A)`**: every element of `G_K` is the image in `G_k` of an element of the
decomposition group `D_A ⊆ Gal(Ω/F)` (for a place `A` above a closed point `x`: `κ(x) ⊆ K`). -/
def GkLiftsTo (A : ValuationSubring Ω) : Prop :=
  ∀ g : Gk k Ω, FixesK K g → ∃ σ : A.decompositionSubgroup (F D), piToGk D (decompToPi D A σ) = g

/-- `K` is stable under `G_k` (e.g. `K` normal over `k`). -/
def GkStable : Prop :=
  ∀ (ρ : Gk k Ω) (c : K), ∃ c' : K,
    ρ ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ = ⟨algebraMap K Ω c', algebraMap_mem_kbar c'⟩

variable {K} in
lemma GkLiftsTo.mono {K' : IntermediateField k Ω} [Algebra.IsAlgebraic k K'] (hle : K ≤ K')
    {A : ValuationSubring Ω} (h : GkLiftsTo D K A) : GkLiftsTo D K' A :=
  fun g hg => h g fun c => hg ⟨c, hle c.2⟩

/-! ### Places with `G_K ⊆ pr(D_A)` are rational points of `U_K` -/

/-- **The residues of `F_K` at `A` lie in `K`** if `G_K ⊆ pr(D_A)`. -/
theorem exists_residue_eq_constExt_of_lifts (A : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hK : GkLiftsTo D K A) (a : F (constExt K D)) (ha : (a : Ω) ∈ A) :
    ∃ c : K, residue A ⟨_, ha⟩ = residue A ⟨_, algebraMap_mem_A_constExt hk c⟩ := by
  letI := resAlg A hk
  haveI := hint
  have hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c :=
    fun _ => rfl
  obtain ⟨β, hβ⟩ := kbarResidue_surjective A hk hkres (residue A ⟨_, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_of_forall_fix_constExt (K := K) β fun g hg => by
    obtain ⟨σ, hG⟩ := hK g hg
    have hfix : ∀ c : K, ((ofGalF D σ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) =
        algebraMap K Ω c := by
      intro c
      have h1 := algebraMap_hToGk_apply D (ofGalF D σ.1) ⟨_, algebraMap_mem_kbar c⟩
      have h3 := hg c
      rw [← h1]
      change algebraMap (kbar k Ω) Ω (piToGk D (decompToPi D A σ) _) = _
      rw [hG, h3]
      rfl
    obtain ⟨σ', hσ'⟩ := exists_hRes_eq (K := K) D hfix
    have hσa : σ.1 (a : Ω) = a := by
      rw [← ofGalF_apply D σ.1, ← hσ', coe_hRes, resK_apply]
      exact (IntermediateField.mem_fixedField_iff _ _).1 a.2 _ σ'.2
    apply (kbarResidue A hk).injective
    rw [← hG, kbarResidue_piToGk_decompToPi D A hk hkres, hβ,
      Decomposition.decompositionMap_residue]
    congr 1
    exact Subtype.ext hσa
  refine ⟨c, ?_⟩
  rw [← hβ, kbarResidue_apply]
  congr 1
  exact Subtype.ext hc.symm

/-- **A place `A` with `G_K ⊆ pr(D_A)` as a rational point of `U_K`.** -/
def ratPointConstExt (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hK : GkLiftsTo D K A) : RatPoint (constExt K D) where
  A := A
  hk := algebraMap_mem_A_constExt hk
  isIntegral := by
    letI : Algebra k (ResidueField A) := resAlg A hk
    haveI : Algebra.IsIntegral k (ResidueField A) := hint
    letI := resAlg A (algebraMap_mem_A_constExt (K := K) hk)
    haveI : IsScalarTower k K (ResidueField A) := IsScalarTower.of_algebraMap_eq fun c => rfl
    exact ⟨fun y => (Algebra.IsIntegral.isIntegral (R := k) y).tower_top⟩
  hrat a ha := exists_residue_eq_constExt_of_lifts K A hk hint hK a ha

@[simp] lemma ratPointConstExt_A (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hK : GkLiftsTo D K A) : (ratPointConstExt K A hk hint hK).A = A := rfl

/-! ### `D_A(U_K) = D_A(U) ∩ pr⁻¹(G_K)` -/

lemma toGalF_hRes_mem_decomp (A : ValuationSubring Ω)
    (σ' : A.decompositionSubgroup (F (constExt K D))) :
    toGalF D (hRes K D (ofGalF (constExt K D) σ'.1)) ∈ A.decompositionSubgroup (F D) := by
  rw [mem_decompositionSubgroup_iff']
  intro z
  rw [toGalF_apply, coe_hRes, resK_apply, ofGalF_apply]
  exact (mem_decompositionSubgroup_iff' A σ'.1).1 σ'.2 z

lemma piRes_decompToPi (A : ValuationSubring Ω)
    (σ' : A.decompositionSubgroup (F (constExt K D))) :
    piRes K D (decompToPi (constExt K D) A σ') =
      decompToPi D A ⟨_, toGalF_hRes_mem_decomp K A σ'⟩ := by
  change ((hRes K D (ofGalF (constExt K D) σ'.1) : D.H) : Pi D) =
    ((ofGalF D (toGalF D (hRes K D (ofGalF (constExt K D) σ'.1))) : D.H) : Pi D)
  rw [ofGalF_toGalF]

lemma piToGk_piRes_fixesK (p : Pi (constExt K D)) : FixesK K (piToGk D (piRes K D p)) :=
  (mem_range_piRes_iff (K := K) D (piRes K D p)).1 ⟨p, rfl⟩

lemma exists_piRes_decompToPi_eq (A : ValuationSubring Ω) (σ : A.decompositionSubgroup (F D))
    (hσ : FixesK K (piToGk D (decompToPi D A σ))) :
    ∃ σ' : A.decompositionSubgroup (F (constExt K D)),
      piRes K D (decompToPi (constExt K D) A σ') = decompToPi D A σ := by
  have hfix : ∀ c : K, ((ofGalF D σ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω) (algebraMap K Ω c) =
      algebraMap K Ω c := by
    intro c
    have h1 := algebraMap_hToGk_apply D (ofGalF D σ.1) ⟨_, algebraMap_mem_kbar c⟩
    rw [← h1]
    change algebraMap (kbar k Ω) Ω (piToGk D (decompToPi D A σ) _) = _
    rw [hσ c]
    rfl
  obtain ⟨g, hg⟩ := exists_hRes_eq (K := K) D hfix
  have happ : ∀ z, toGalF (constExt K D) g z = σ.1 z := fun z => by
    rw [toGalF_apply, ← ofGalF_apply D σ.1, ← hg, coe_hRes, resK_apply]
  have hmem : toGalF (constExt K D) g ∈ A.decompositionSubgroup (F (constExt K D)) := by
    rw [mem_decompositionSubgroup_iff']
    intro z
    rw [happ]
    exact (mem_decompositionSubgroup_iff' A σ.1).1 σ.2 z
  refine ⟨⟨_, hmem⟩, ?_⟩
  change ((hRes K D (ofGalF (constExt K D) (toGalF (constExt K D) g)) : D.H) : Pi D) =
    ((ofGalF D σ.1 : D.H) : Pi D)
  rw [ofGalF_toGalF, hg]

/-! ### Sections of rational points (generic Galois model) -/

variable {K}

lemma piToGk_ratSectionGk' {D' : Pi1.Orbifold.GaloisData K t} [IsGalois (K₀ K t) Ω]
    (x : RatPoint D') (hHL : D'.HL = D'.H) (hx : t ∈ x.A) (g : Gk K Ω) :
    piToGk D' (ratSectionGk x hHL hx g) = g := by
  rw [ratSectionGk, MonoidHom.comp_apply, piToGk_ratSectionMap]
  refine AlgEquiv.ext fun y => ?_
  simp

lemma ratSectionGk_mem_range' {D' : Pi1.Orbifold.GaloisData K t} [IsGalois (K₀ K t) Ω]
    (x : RatPoint D') (hHL : D'.HL = D'.H) (hx : t ∈ x.A) (g : Gk K Ω) :
    ratSectionGk x hHL hx g ∈ (decompToPi D' x.A).range := by
  obtain ⟨σ, hσ⟩ := x.decompositionMap_surjective
    (AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres) g)
  refine ⟨σ, ?_⟩
  rw [ratSectionGk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hσ,
    ratSectionMap_decompositionMap]

lemma exists_ratSectionGk_eq' {D' : Pi1.Orbifold.GaloisData K t} [IsGalois (K₀ K t) Ω]
    (x : RatPoint D') (hHL : D'.HL = D'.H) (hx : t ∈ x.A) {d : Pi D'}
    (hd : d ∈ (decompToPi D' x.A).range) : ∃ g, ratSectionGk x hHL hx g = d := by
  obtain ⟨σ, rfl⟩ := hd
  refine ⟨(AlgEquiv.autCongr (kbarEquiv x.A x.hk x.hkres)).symm
    (Decomposition.decompositionMap (F D') x.A x.hk x.hkres σ), ?_⟩
  rw [ratSectionGk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    ratSectionMap_decompositionMap]

/-! ### Conjugate places `σ • A` -/

variable (K)

lemma hk_smul (σ : Ω ≃ₐ[F D] Ω) {A : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (c : k) : algebraMap k Ω c ∈ σ • A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap k Ω c = algebraMap k Ω c := by
    rw [AlgEquiv.smul_def, IsScalarTower.algebraMap_apply k (F D) Ω, AlgEquiv.commutes]
  rw [this]
  exact hk c

/-- `σ : A ≃ σ • A`. -/
def smulValEquiv (σ : Ω ≃ₐ[F D] Ω) (A : ValuationSubring Ω) :
    A ≃+* ↥(σ • A : ValuationSubring Ω) where
  toFun a := ⟨σ a, ValuationSubring.smul_mem_pointwise_smul_iff.2 a.2⟩
  invFun b := ⟨σ.symm b, by
    have h := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.1 b.2
    rwa [AlgEquiv.smul_def, AlgEquiv.aut_inv] at h⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply _)
  right_inv b := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ (a : Ω) b)
  map_add' a b := Subtype.ext (map_add σ (a : Ω) b)

/-- `κ(σ • A) ≅ κ(A)` over `k`, so `κ(σ • A)` is algebraic over `k` with `κ(A)`. -/
lemma isIntegral_smul (σ : Ω ≃ₐ[F D] Ω) {A : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A)) :
    letI := resAlg (σ • A : ValuationSubring Ω) (hk_smul σ hk)
    Algebra.IsIntegral k (ResidueField (σ • A : ValuationSubring Ω)) := by
  letI : Algebra k (ResidueField A) := resAlg A hk
  haveI : Algebra.IsIntegral k (ResidueField A) := hint
  letI : Algebra k (ResidueField (σ • A : ValuationSubring Ω)) :=
    resAlg (σ • A : ValuationSubring Ω) (hk_smul σ hk)
  set e := ResidueField.mapEquiv (smulValEquiv σ A)
  let f : ResidueField A →ₐ[k] ResidueField (σ • A : ValuationSubring Ω) :=
    { e.toRingHom with
      commutes' := fun c => by
        change ResidueField.map (smulValEquiv σ A : A →+* (σ • A : ValuationSubring Ω))
          (residue A ⟨algebraMap k Ω c, hk c⟩) =
            residue (σ • A : ValuationSubring Ω) ⟨algebraMap k Ω c, _⟩
        rw [ResidueField.map_residue]
        congr 1
        apply Subtype.ext
        change σ (algebraMap k Ω c) = algebraMap k Ω c
        rw [IsScalarTower.algebraMap_apply k (F D) Ω, AlgEquiv.commutes] }
  exact Algebra.IsIntegral.of_surjective f e.surjective

/-- **`γ D_A γ⁻¹ ⊆ D_{σ • A}`** for `γ = [σ] ∈ Π_U`. -/
lemma conj_mem_range_decompToPi_smul (h : D.H) {A : ValuationSubring Ω} {d : Pi D}
    (hd : d ∈ (decompToPi D A).range) :
    (h : Pi D) * d * (h : Pi D)⁻¹ ∈ (decompToPi D (toGalF D h • A)).range := by
  obtain ⟨τ, rfl⟩ := hd
  have hmem : toGalF D h * τ.1 * (toGalF D h)⁻¹ ∈
      (toGalF D h • A).decompositionSubgroup (F D) := by
    rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, mul_smul,
      mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 τ.2]
  refine ⟨⟨_, hmem⟩, ?_⟩
  change ((ofGalF D (toGalF D h * τ.1 * (toGalF D h)⁻¹) : D.H) : Pi D) =
    (h : Pi D) * ((ofGalF D τ.1 : D.H) : Pi D) * (h : Pi D)⁻¹
  rw [map_mul, map_mul, map_inv, ofGalF_toGalF]
  rfl

/-- `G_K ⊆ pr(D_A)` passes to `σ • A` if `K` is stable under `G_k`. -/
lemma gkLiftsTo_smul (hKst : GkStable K) (h : D.H) {A : ValuationSubring Ω}
    (hK : GkLiftsTo D K A) : GkLiftsTo D K (toGalF D h • A) := by
  intro g hg
  set ρ := piToGk D (h : Pi D)
  have hg' : FixesK K (ρ⁻¹ * g * ρ) := by
    intro c
    obtain ⟨c', hc'⟩ := hKst ρ c
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg c', ← hc', AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
  obtain ⟨τ, hτ⟩ := hK _ hg'
  obtain ⟨σ, hσ⟩ := conj_mem_range_decompToPi_smul h ⟨τ, rfl⟩
  refine ⟨σ, ?_⟩
  rw [hσ, map_mul, map_mul, map_inv, hτ]
  change ρ * (ρ⁻¹ * g * ρ) * ρ⁻¹ = g
  group

end Generic

/-! ### Normal closures: places above closed points satisfy `G_K ⊆ pr(D_A)` -/

section Exists

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

set_option maxHeartbeats 1000000 in
-- the normal closure inside `k̄` and its image in `Ω` elaborate slowly
/-- **Places above closed points satisfy `G_K ⊆ pr(D_A)`** for a finite extension `K` of `k`
stable under `G_k`: if `A ⊇ k`, `κ(A)` is algebraic over `k` and the residue field
`κ(A ∩ F)` (`pointField`) is finite over `k`, take for `K` the normal closure of `κ(A ∩ F)`
(pulled back to `k̄ ⊆ Ω` along `k̄ ≅ κ(A)`); every `g ∈ G_K` fixes `κ(A ∩ F)` and lifts to `D_A`
(continuous-kummer-theory `exists_decompositionMap_eq_of_fixes`). -/
theorem exists_gkLiftsTo (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hfin : letI := resAlg A hk;
      FiniteDimensional k (Decomposition.pointField (F D) A hk (fun _ => rfl)))
    (K' : IntermediateField k Ω) [FiniteDimensional k K'] :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K), K' ≤ K ∧ GkStable K ∧
      GkLiftsTo D K A := by
  letI : Algebra k (ResidueField A) := resAlg A hk
  haveI : Algebra.IsIntegral k (ResidueField A) := hint
  have hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c :=
    fun _ => rfl
  set e := kbarEquiv A hk hkres
  set P := Decomposition.pointField (F D) A hk hkres
  haveI : FiniteDimensional k P := hfin
  set P₀ : IntermediateField k (kbar k Ω) := P.map (e.symm : ResidueField A →ₐ[k] kbar k Ω)
  haveI : FiniteDimensional k P₀ :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap P _).toLinearEquiv
  set K'' : IntermediateField k (kbar k Ω) := K'.comap (kbar k Ω).val
  haveI : FiniteDimensional k K'' := by
    let ι : K'' →ₗ[k] K' :=
      { toFun x := ⟨(x : kbar k Ω), x.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    exact FiniteDimensional.of_injective ι fun x y h => Subtype.ext (Subtype.ext
      (congrArg (fun z : K' => (z : Ω)) h))
  set N : IntermediateField k (kbar k Ω) :=
    IntermediateField.normalClosure k ↥(P₀ ⊔ K'') (kbar k Ω)
  haveI : FiniteDimensional k N := inferInstance
  haveI : Normal k N := inferInstance
  set K : IntermediateField k Ω := N.map (kbar k Ω).val
  haveI hKfin : FiniteDimensional k K :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap N _).toLinearEquiv
  -- elements of `K` are the elements of `N`
  have hmemK : ∀ y : kbar k Ω, (y : Ω) ∈ K ↔ y ∈ N := fun y => by
    constructor
    · rintro ⟨n, hn, hny⟩
      rwa [show n = y from Subtype.ext hny] at hn
    · exact fun hy => ⟨y, hy, rfl⟩
  have hKN : ∀ c : K, (⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ : kbar k Ω) ∈ N := fun c =>
    (hmemK ⟨_, algebraMap_mem_kbar c⟩).1 c.2
  refine ⟨K, hKfin, fun x hx => ?_, fun ρ c => ?_, fun g hg => ?_⟩
  · -- `K' ⊆ K`
    have hxk : x ∈ kbar k Ω := algebraMap_mem_kbar (K := K') ⟨x, hx⟩
    exact (hmemK ⟨x, hxk⟩).2 (IntermediateField.le_normalClosure (P₀ ⊔ K'')
      (le_sup_right (a := P₀) (show (⟨x, hxk⟩ : kbar k Ω) ∈ K'' from hx)))
  · -- stability: `N` is normal over `k`
    have hρ := (IntermediateField.normal_iff_forall_map_le' (F := k) (K := N)).1 inferInstance ρ
    have h1 : ρ ⟨algebraMap K Ω c, algebraMap_mem_kbar c⟩ ∈ N := hρ ⟨_, hKN c, rfl⟩
    exact ⟨⟨_, (hmemK _).2 h1⟩, Subtype.ext rfl⟩
  · -- `g ∈ G_K` fixes `N`, hence `κ(A ∩ F)`, and lifts to `D_A`
    have hgN : ∀ y ∈ N, g y = y := fun y hy => by
      have := hg ⟨_, (hmemK y).2 hy⟩
      exact this
    obtain ⟨σ, hσ⟩ := Decomposition.exists_decompositionMap_eq_of_fixes (F := F D) A hk hkres
      (e.symm.trans (g.trans e)) fun a ha => by
        have hP : residue A ⟨_, ha⟩ ∈ P := ⟨a, ha, rfl⟩
        have hP₀ : e.symm (residue A ⟨_, ha⟩) ∈ N := by
          have := IntermediateField.le_normalClosure (P₀ ⊔ K'')
            (le_sup_left (b := K'') (show e.symm (residue A ⟨_, ha⟩) ∈ P₀ from ⟨_, hP, rfl⟩))
          exact this
        rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, hgN _ hP₀, AlgEquiv.apply_symm_apply]
    refine ⟨σ, AlgEquiv.ext fun y => (kbarResidue A hk).injective ?_⟩
    rw [kbarResidue_piToGk_decompToPi D A hk hkres, hσ, ← kbarEquiv_apply A hk hkres,
      ← kbarEquiv_apply A hk hkres]
    simp [e]

end Exists

/-! ### Closed points of `U` are determined by their decomposition groups -/

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  {K : IntermediateField k (FFClosure X)} [FiniteDimensional k K]

lemma smul_mem_iff_of_mem_F {D : Pi1.Orbifold.GaloisData k (coordT τ)}
    (σ : FFClosure X ≃ₐ[F D] FFClosure X) {A : ValuationSubring (FFClosure X)}
    {z : FFClosure X} (hz : z ∈ F D) : z ∈ σ • A ↔ z ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  rw [show σ⁻¹ z = z from (σ⁻¹).commutes ⟨z, hz⟩]

lemma coordT_mem_F (D : Pi1.Orbifold.GaloisData k (coordT τ)) : coordT τ ∈ F D :=
  (F D).algebraMap_mem ⟨coordT τ, IntermediateField.mem_adjoin_simple_self k _⟩

set_option maxHeartbeats 800000 in
-- the rational points of `U_K` built from `A`, `B` unfold slowly
set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient groups `Π_U`, `Π_{U_K}` is found slowly
/-- **[GalSect] Thm 1.3 (i) for closed points, containment form** (number field `k`, `X` proper
of genus `≠ 0` with a rational point): if places `A`, `B` of `Ω` with `t` regular and
`G_K ⊆ pr(D_A), pr(D_B)` satisfy `D_B ⊆ D_A` in `Π_U`, then `A ∩ F = B ∩ F`, i.e. they lie over
the same closed point of `U`. (Both become rational points of `U_K`; `D_B(U_K) ⊆ D_A(U_K)` by
`piRes`, so their sections are `Δ_{U_K}`-conjugate, and Theorem C for `U_K` applies.) -/
theorem mem_iff_of_range_decompToPi_le [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : CurvesJacobian.curveGenus k X ≠ 0)
    {A B : ValuationSubring (FFClosure X)}
    (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
    (hkB : ∀ c : k, algebraMap k (FFClosure X) c ∈ B)
    (hiA : letI := resAlg A hkA; Algebra.IsIntegral k (ResidueField A))
    (hiB : letI := resAlg B hkB; Algebra.IsIntegral k (ResidueField B))
    (hKA : GkLiftsTo (curveGaloisData k hτ) K A) (hKB : GkLiftsTo (curveGaloisData k hτ) K B)
    (htA : coordT τ ∈ A) (htB : coordT τ ∈ B)
    (h : ∀ d ∈ (decompToPi (curveGaloisData k hτ) B).range,
      d ∈ (decompToPi (curveGaloisData k hτ) A).range)
    (f : F (curveGaloisData k hτ)) : (f : FFClosure X) ∈ A ↔ (f : FFClosure X) ∈ B := by
  set x := ratPointConstExt K A hkA hiA hKA
  set y := ratPointConstExt K B hkB hiB hKB
  have hHL := constExt_HL_eq_curve k hτ K
  obtain ⟨δ, hδ, hconj⟩ := exists_conj_of_forall_exists'
    (piToGk (constExt K (curveGaloisData k hτ))) (ratSectionGk x hHL htA)
    (ratSectionGk y hHL htB)
    (piToGk_ratSectionGk' x hHL htA) (piToGk_ratSectionGk' y hHL htB) 1 (fun g ↦ by
      obtain ⟨σ', hσ'⟩ := ratSectionGk_mem_range' y hHL htB g
      obtain ⟨τ', hτ'⟩ := h _ ⟨⟨_, toGalF_hRes_mem_decomp K B σ'⟩, rfl⟩
      obtain ⟨τ'', hτ''⟩ := exists_piRes_decompToPi_eq K A τ' (by
        rw [hτ', ← piRes_decompToPi]
        exact piToGk_piRes_fixesK K _)
      obtain ⟨g', hg'⟩ := exists_ratSectionGk_eq' x hHL htA ⟨τ'', rfl⟩
      refine ⟨g', ?_⟩
      rw [one_mul, inv_one, mul_one, ← hσ', hg']
      apply piRes_injective (K := K) (curveGaloisData k hτ)
      exact ((hτ''.trans hτ').trans (piRes_decompToPi K B σ').symm).symm)
  have hp := placeOfF_eq_of_ratSectionGk_conj_constExt k hτ K σ hσ hg htA htB hδ hconj
  have e := congrArg
    (fun P : WeilCurves.FunctionField.Place K (F (constExt K (curveGaloisData k hτ))) =>
      (⟨f, le_F_constExt (curveGaloisData k hτ) f.2⟩ : F (constExt K (curveGaloisData k hτ))) ∈
        P.1) hp
  have e' := iff_of_eq e
  exact e'

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[GalSect] Thm 1.3 (i) for closed points of `U`** (Galois model, number field `k`, `X`
proper of genus `≠ 0` with a rational point, `K` finite over `k` and stable under `G_k`): if
`D_B ⊆ γ D_A γ⁻¹` for some `γ ∈ Π_U`, then `A` and `B` lie over the same closed point of `U`.
(`γ D_A γ⁻¹ ⊆ D_{σ • A}` for a lift `σ` of `γ`, and `σ • A` lies over the same point as `A`.) -/
theorem mem_iff_of_range_decompToPi_le_conj [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : CurvesJacobian.curveGenus k X ≠ 0) (hKst : GkStable K)
    {A B : ValuationSubring (FFClosure X)}
    (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
    (hkB : ∀ c : k, algebraMap k (FFClosure X) c ∈ B)
    (hiA : letI := resAlg A hkA; Algebra.IsIntegral k (ResidueField A))
    (hiB : letI := resAlg B hkB; Algebra.IsIntegral k (ResidueField B))
    (hKA : GkLiftsTo (curveGaloisData k hτ) K A) (hKB : GkLiftsTo (curveGaloisData k hτ) K B)
    (htA : coordT τ ∈ A) (htB : coordT τ ∈ B) (γ : Pi (curveGaloisData k hτ))
    (h : ∀ d ∈ (decompToPi (curveGaloisData k hτ) B).range,
      ∃ d' ∈ (decompToPi (curveGaloisData k hτ) A).range, d = γ * d' * γ⁻¹)
    (f : F (curveGaloisData k hτ)) : (f : FFClosure X) ∈ A ↔ (f : FFClosure X) ∈ B := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  have key := mem_iff_of_range_decompToPi_le σ hσ hg
    (hk_smul (toGalF (curveGaloisData k hτ) g) hkA) hkB
    (isIntegral_smul (toGalF (curveGaloisData k hτ) g) hkA hiA) hiB
    (gkLiftsTo_smul K hKst g hKA) hKB
    ((smul_mem_iff_of_mem_F _ (coordT_mem_F _)).2 htA) htB (fun d hd => by
      obtain ⟨d', hd', rfl⟩ := h d hd
      exact conj_mem_range_decompToPi_smul g hd') f
  rw [← key, smul_mem_iff_of_mem_F _ f.2]

end Curve

/-! ### The arithmetic form (curves-jacobian's `arithDecomp`) -/

section Arith

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  [CharZero (FFClosure C.Xbar)] {K₁ : IntermediateField K (FFClosure C.Xbar)}
  [FiniteDimensional K K₁]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
include hU in
/-- **[GalSect] Thm 1.3 (i) for closed points of `U`, arithmetic form**: for an affine
hyperbolic curve over a number field whose compactification has genus `≠ 0` and a rational
point, if the decomposition group (curves-jacobian `arithDecomp`) of a place `B` lies in a
`Π_U`-conjugate of that of `A` (both with `G_{K₁} ⊆ pr(D_·)` for a finite `K₁` stable under
`G_K`), then `A` and `B` lie over the same closed point of `U`. -/
theorem mem_iff_of_arithDecomp_le_conj (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0) (hKst : GkStable K₁)
    {A B : ValuationSubring (FFClosure C.Xbar)}
    (hkA : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ A)
    (hkB : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ B)
    (hiA : letI := resAlg A hkA; Algebra.IsIntegral K (ResidueField A))
    (hiB : letI := resAlg B hkB; Algebra.IsIntegral K (ResidueField B))
    (hKA : GkLiftsTo (curveGaloisData K hτ) K₁ A) (hKB : GkLiftsTo (curveGaloisData K hτ) K₁ B)
    (htA : coordT τ ∈ A) (htB : coordT τ ∈ B) (g : (arithmeticExt Ω C hc.out).Pi)
    (h : ∀ e : (arithmeticExt Ω C hc.out).Pi, e ∈ arithDecomp Ω C hc.out
        (B.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) →
      ∃ e' : (arithmeticExt Ω C hc.out).Pi, e' ∈ arithDecomp Ω C hc.out
        (A.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ∧ e = g * e' * g⁻¹)
    (f : F (curveGaloisData K hτ)) : (f : FFClosure C.Xbar) ∈ A ↔ (f : FFClosure C.Xbar) ∈ B := by
  refine mem_iff_of_range_decompToPi_le_conj σ₀ hσ₀ hg hKst hkA hkB hiA hiB hKA hKB htA htB
    ((piBridge (Ω := Ω) hτ hU).symm g) (fun d hd ↦ ?_) f
  obtain ⟨e', he', he⟩ := h _ ((piBridge_mem_arithDecomp_iff hτ hU B d).2 hd)
  obtain ⟨d', rfl⟩ := (piBridge (Ω := Ω) hτ hU).surjective e'
  refine ⟨d', (piBridge_mem_arithDecomp_iff hτ hU A d').1 he', ?_⟩
  apply (piBridge (Ω := Ω) hτ hU).injective
  rw [he, map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]

end Arith

/-! ### Closed-point data of places of `Ω` nontrivial on `F` -/

section PointData

/-- **Residue fields under algebraic extensions** (the argument of curves-jacobian
`SectionBridge.isIntegral_residueField_of_rational`, whose module is not in the import closure
here): if `Ω` is algebraic over `E` and every residue of `E ∩ A` comes from `k`, then `κ(A)` is
algebraic over `k`. -/
theorem isIntegral_residueField_of_rational' {Ω E k : Type u} [Field Ω] [Field E] [Field k]
    [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) [Algebra k (ResidueField A)]
    (hrat : ∀ (a : E) (ha : algebraMap E Ω a ∈ A),
      ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c) :
    Algebra.IsIntegral k (ResidueField A) := by
  classical
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp0, hpb⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) (b : Ω)
  obtain ⟨i₀, hi₀, hmax⟩ := p.support.exists_max_image
    (fun i ↦ A.valuation (algebraMap E Ω (p.coeff i))) (Polynomial.nonempty_support_iff.2 hp0)
  set c₀ : E := p.coeff i₀ with hc₀def
  have hc₀ : c₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  have hv₀ : A.valuation (algebraMap E Ω c₀) ≠ 0 := by
    rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap E Ω).injective]
    exact hc₀
  have hd : ∀ i, algebraMap E Ω (p.coeff i / c₀) ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_div₀, map_div₀]
    by_cases hi : i ∈ p.support
    · exact (div_le_one₀ (zero_lt_iff.2 hv₀)).2 (hmax i hi)
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero, map_zero, zero_div]
      exact zero_le
  choose c hc using fun i ↦ hrat (p.coeff i / c₀) (hd i)
  let r : Polynomial k := ∑ i ∈ p.support, Polynomial.monomial i (c i)
  have hr0 : r ≠ 0 := by
    intro h
    have h1 : r.coeff i₀ = c i₀ := by
      simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ if_neg hj) (fun h ↦ absurd hi₀ h), if_pos rfl]
    rw [h, Polynomial.coeff_zero] at h1
    have h2 := hc i₀
    rw [← h1, map_zero] at h2
    have h3 : (⟨algebraMap E Ω (p.coeff i₀ / c₀), hd i₀⟩ : A) = 1 := by
      apply Subtype.ext
      change algebraMap E Ω (p.coeff i₀ / c₀) = 1
      rw [← hc₀def, div_self hc₀, map_one]
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  refine (show IsAlgebraic k (residue A b) from ⟨r, hr0, ?_⟩).isIntegral
  have hsum : (∑ i ∈ p.support, (⟨algebraMap E Ω (p.coeff i / c₀), hd i⟩ : A) * b ^ i) = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    change ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i = 0
    have : (Polynomial.aeval (b : Ω) p) =
        ∑ i ∈ p.support, algebraMap E Ω (p.coeff i) * (b : Ω) ^ i := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have h2 : ∑ i ∈ p.support, algebraMap E Ω (p.coeff i / c₀) * (b : Ω) ^ i =
        (Polynomial.aeval (b : Ω) p) * (algebraMap E Ω c₀)⁻¹ := by
      rw [this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_div₀]
      ring
    rw [h2, hpb, zero_mul]
  have := congrArg (residue A) hsum
  rw [map_zero, map_sum] at this
  rw [← this, map_sum]
  simp only [Polynomial.aeval_monomial, map_mul, map_pow, hc]

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

variable (D) in
/-- **The place `A ∩ F` of `F`** below a place `A ⊇ k` of `Ω` nontrivial on `F`. -/
def placeBelow (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hne : ∃ f : F D, (f : Ω) ∉ A) : WeilCurves.FunctionField.Place k (F D) :=
  ⟨A.comap (algebraMap (F D) Ω), fun h => by
      obtain ⟨f, hf⟩ := hne
      have : f ∈ A.comap (algebraMap (F D) Ω) := h ▸ ValuationSubring.mem_top _
      exact hf this,
    fun c => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hk c⟩

variable (D) in
/-- `O_{A ∩ F} → κ(A)`. -/
def resBelow (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hne : ∃ f : F D, (f : Ω) ∉ A) : (placeBelow D A hk hne).1 →+* ResidueField A :=
  (residue A).comp ((algebraMap (F D) Ω).restrict (placeBelow D A hk hne).1 A fun _ hx => hx)

instance isLocalHom_resBelow (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hne : ∃ f : F D, (f : Ω) ∉ A) : IsLocalHom (resBelow D A hk hne) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : (a : F D) ∈ (placeBelow D A hk hne).1.nonunits :=
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨a.2, hna⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at h1
  have h2 : algebraMap (F D) Ω (a : F D) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    rcases h1 with h | h
    · left
      rw [h, map_zero]
    · right
      intro h'
      apply h
      change algebraMap (F D) Ω (a : F D)⁻¹ ∈ A
      rwa [map_inv₀]
  obtain ⟨hA, hmA⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 h2
  apply ha.ne_zero
  exact (residue_eq_zero_iff _).2 hmA

/-- **`κ(A ∩ F)` is finite over `k`** (it is the image of the residue field of the place
`A ∩ F` of the function field `F`, weil-curves). -/
theorem finiteDimensional_pointField (A : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ A) (hne : ∃ f : F D, (f : Ω) ∉ A) :
    letI := resAlg A hk
    FiniteDimensional k (Decomposition.pointField (F D) A hk (fun _ => rfl)) := by
  letI := resAlg A hk
  set P := placeBelow D A hk hne
  let φ : P.ResidueField →ₐ[k] ResidueField A :=
    { IsLocalRing.ResidueField.lift (resBelow D A hk hne) with
      commutes' := fun c => IsLocalRing.ResidueField.lift_residue_apply _ _ }
  have hle : Subalgebra.toSubmodule
      (Decomposition.pointField (F D) A hk (fun _ => rfl)).toSubalgebra ≤
      LinearMap.range φ.toLinearMap := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨P.residue ⟨a, ha⟩,
      IsLocalRing.ResidueField.lift_residue_apply (resBelow D A hk hne) ⟨a, ha⟩⟩
  haveI : FiniteDimensional k (LinearMap.range φ.toLinearMap) := inferInstance
  exact Submodule.finiteDimensional_of_le hle

/-- **`κ(A)` is algebraic over `k`** for a place `A ⊇ k` of `Ω` nontrivial on `F` (algebraic over
the finite extension `κ(A ∩ F)` of `k`). -/
theorem isIntegral_residueField_of_ne (A : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ A) (hne : ∃ f : F D, (f : Ω) ∉ A) :
    letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A) := by
  letI := resAlg A hk
  set P := Decomposition.pointField (F D) A hk (fun _ => rfl)
  haveI : FiniteDimensional k P := finiteDimensional_pointField A hk hne
  haveI : Algebra.IsAlgebraic (F D) Ω := Algebra.IsAlgebraic.tower_top (K := K₀ k t) (F D)
  haveI : Algebra.IsIntegral P (ResidueField A) :=
    isIntegral_residueField_of_rational' (E := F D) A fun a ha => ⟨⟨_, a, ha, rfl⟩, rfl⟩
  exact Algebra.IsIntegral.trans P

/-- **Every place `A ⊇ k` of `Ω` nontrivial on `F` satisfies `G_K ⊆ pr(D_A)`** for a finite
extension `K` of `k` stable under `G_k` (the closed-point data of `exists_gkLiftsTo`). -/
theorem exists_gkLiftsTo_of_ne (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hne : ∃ f : F D, (f : Ω) ∉ A) (K' : IntermediateField k Ω) [FiniteDimensional k K'] :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K), K' ≤ K ∧ GkStable K ∧
      GkLiftsTo D K A :=
  exists_gkLiftsTo A hk (isIntegral_residueField_of_ne A hk hne)
    (finiteDimensional_pointField A hk hne) K'

end PointData

/-! ### Closed points, final form -/

section Final

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
/-- **[GalSect] Thm 1.3 (i) for closed points of `U`** (Galois model, number field `k`, `X`
proper of genus `≠ 0` with a rational point): let `A`, `B` be places of `Ω` containing `k` and
`t`, nontrivial on the function field `F` (i.e. above closed points of `U`). If `D_B ⊆ γ D_A γ⁻¹`
for some `γ ∈ Π_U`, then `A ∩ F = B ∩ F`: `A` and `B` lie over the same closed point of `U`. -/
theorem mem_iff_of_decomp_le_conj [NumberField k]
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hg : CurvesJacobian.curveGenus k X ≠ 0)
    {A B : ValuationSubring (FFClosure X)}
    (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
    (hkB : ∀ c : k, algebraMap k (FFClosure X) c ∈ B)
    (hneA : ∃ f : F (curveGaloisData k hτ), (f : FFClosure X) ∉ A)
    (hneB : ∃ f : F (curveGaloisData k hτ), (f : FFClosure X) ∉ B)
    (htA : coordT τ ∈ A) (htB : coordT τ ∈ B) (γ : Pi (curveGaloisData k hτ))
    (h : ∀ d ∈ (decompToPi (curveGaloisData k hτ) B).range,
      ∃ d' ∈ (decompToPi (curveGaloisData k hτ) A).range, d = γ * d' * γ⁻¹)
    (f : F (curveGaloisData k hτ)) : (f : FFClosure X) ∈ A ↔ (f : FFClosure X) ∈ B := by
  obtain ⟨K₁, _, -, -, hK₁⟩ := exists_gkLiftsTo_of_ne A hkA hneA ⊥
  obtain ⟨K, _, hle, hKst, hKB⟩ := exists_gkLiftsTo_of_ne B hkB hneB K₁
  exact mem_iff_of_range_decompToPi_le_conj σ hσ hg hKst hkA hkB
    (isIntegral_residueField_of_ne A hkA hneA) (isIntegral_residueField_of_ne B hkB hneB)
    (hK₁.mono hle) hKB htA htB γ h f

end Final

/-! ### Closed points, arithmetic final form -/

section ArithFinal

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  [CharZero (FFClosure C.Xbar)]

set_option synthInstance.maxHeartbeats 400000 in
-- `Inv` on the quotient group `Π_U` is found slowly
include hU in
/-- **[GalSect] Thm 1.3 (i) for closed points of `U`, arithmetic form** (curves-jacobian's
`arithDecomp`; number field `K`, compactification of genus `≠ 0` with a rational point): for
places `A`, `B ⊇ K` of `Ω` with `t` regular and nontrivial on `F` (above closed points of `U`),
if `D_B ⊆ g D_A g⁻¹` for some `g ∈ Π_U`, then `A ∩ F = B ∩ F`. -/
theorem mem_iff_of_arithDecomp_le_conj' (σ₀ : Spec (CommRingCat.of K) ⟶ C.Xbar)
    (hσ₀ : σ₀ ≫ (C.Xbar ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)))
    (hg : CurvesJacobian.curveGenus K C.Xbar ≠ 0)
    {A B : ValuationSubring (FFClosure C.Xbar)}
    (hkA : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ A)
    (hkB : ∀ c : K, algebraMap K (FFClosure C.Xbar) c ∈ B)
    (hneA : ∃ f : F (curveGaloisData K hτ), (f : FFClosure C.Xbar) ∉ A)
    (hneB : ∃ f : F (curveGaloisData K hτ), (f : FFClosure C.Xbar) ∉ B)
    (htA : coordT τ ∈ A) (htB : coordT τ ∈ B) (g : (arithmeticExt Ω C hc.out).Pi)
    (h : ∀ e : (arithmeticExt Ω C hc.out).Pi, e ∈ arithDecomp Ω C hc.out
        (B.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) →
      ∃ e' : (arithmeticExt Ω C hc.out).Pi, e' ∈ arithDecomp Ω C hc.out
        (A.comap ((σc (Ω := Ω) (C := C)).symm :
          FFClosure (geomCurve Ω C) →+* FFClosure C.Xbar)) ∧ e = g * e' * g⁻¹)
    (f : F (curveGaloisData K hτ)) :
    (f : FFClosure C.Xbar) ∈ A ↔ (f : FFClosure C.Xbar) ∈ B := by
  obtain ⟨K₁, _, -, -, hK₁⟩ := exists_gkLiftsTo_of_ne A hkA hneA ⊥
  obtain ⟨K₂, _, hle, hKst, hKB⟩ := exists_gkLiftsTo_of_ne B hkB hneB K₁
  exact mem_iff_of_arithDecomp_le_conj hτ hU σ₀ hσ₀ hg hKst hkA hkB
    (isIntegral_residueField_of_ne A hkA hneA) (isIntegral_residueField_of_ne B hkB hneB)
    (hK₁.mono hle) hKB htA htB g h f

end ArithFinal

end Iut.Reconstruction.Thm19
