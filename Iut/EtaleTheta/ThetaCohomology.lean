/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Inflation

/-!
# Theta cohomology: the filtration of [EtTh], Prop. 1.5, and the uniqueness in Thm. 1.6(iii)

[EtTh] (Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*),
Prop. 1.5(i) (l.1369), considers the closed subgroups `Δ_Θ ⊆ (Δ^tp_Y)^Θ ⊆ (Π^tp_Y)^Θ` and the
resulting filtration `0 ⊆ F2 ⊆ F1 ⊆ F0 = H¹((Π^tp_Y)^Θ, Δ_Θ)` with

`F0/F1 ⊆ Hom(Δ_Θ, Δ_Θ)`, `F1/F2 ⊆ Hom((Δ^tp_Y)^ell/Δ_Θ, Δ_Θ)`, `F2 = H¹(G_K, Δ_Θ)`.

The proof of Thm. 1.6(iii) (l.1590–1601) then argues: "the property of mapping to `log(Θ)` in
the quotient `F0/F1` and being fixed, up to a unit multiple, under an inversion automorphism
completely determines the classes `η̈^Θ` up to a `(K̈^×)^∧`-multiple", i.e. up to `F2`.

This file proves the group-theoretic content of these two steps for an arbitrary topological
group `G` with subgroups `DΘ ≤ D` acting trivially on the coefficients `M`:

* `ContH1.resTriv S hS : ContH1 G M →* (S →* M)`: restriction to a subgroup acting trivially
  (`H¹(S, M) = Hom(S, M)`); `resTriv_conj`: for normal `S` the image consists of
  `G`-equivariant homomorphisms, `φ (g s g⁻¹) = g • φ s`.
* `ContH1.ker_resTriv_eq_range_inflation`: `F2 = ker res_D` is the image of the (injective)
  inflation from `G ⧸ D` (the identification `F2 = H¹(G_K, Δ_Θ)` of Prop. 1.5).
* `ContH1.thetaGraded`: `F1 → {φ : D →* M | φ = 1 on DΘ}` (the map to `F1/F2`) with kernel
  `F2` (`ker_thetaGraded`); `F0/F1 ↪ Hom(DΘ, M)` is `resTriv DΘ` with kernel `F1`.
* `ContH1.map_conj_eq_id`: inner automorphisms act trivially on `H¹`.
* `ContH1.pushIso`: transport of classes along an isomorphism of topological groups together
  with a compatible isomorphism of coefficients; `resTriv_pushIso`.
* `ContH1.div_mem_F2_of_inv`: **the uniqueness step of Thm. 1.6(iii)**: two classes with the same
  restriction to `DΘ` that are both fixed modulo `F2` by an automorphism `ι` differ by an
  element of `F2`, provided `D/DΘ` has no nonzero `ι`-invariant homomorphisms to `M`; this holds
  when `ι` inverts `D` modulo `DΘ`, fixes `M`, and `M` has no `2`-torsion
  (`noInvariantHom_of_inv`).
-/

open groupCohomology

namespace ContH1

section Res

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- A cocycle restricted to a subgroup acting trivially is a homomorphism. -/
theorem map_mul_of_trivial (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m)
    (c : cocycles G M) {s t : G} (hs : s ∈ S) : c (s * t) = c s * c t := by
  rw [isMulCocycle₁ c, hS s hs, mul_comm]

/-- The restriction of a cocycle to a subgroup `S` acting trivially on `M`, as a homomorphism. -/
def resCocycleHom (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m) (c : cocycles G M) :
    S →* M where
  toFun s := c s
  map_one' := map_one_eq c
  map_mul' s _ := map_mul_of_trivial S hS c s.2

/-- Restriction of cocycles to `S`, as a homomorphism of groups. -/
def resCocycles (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m) :
    cocycles G M →* (S →* M) where
  toFun := resCocycleHom S hS
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Restriction to a subgroup acting trivially**: `H¹(G, M) → H¹(S, M) = Hom(S, M)`. -/
def resTriv (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m) : ContH1 G M →* (S →* M) :=
  QuotientGroup.lift _ (resCocycles S hS) <| by
    rintro c ⟨m, hm⟩
    ext s
    change c s = 1
    rw [← hm s, hS s s.2, div_self']

@[simp]
theorem resTriv_mk (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m) (c : cocycles G M)
    (s : S) : resTriv S hS (mk c) s = c s := rfl

/-- The restriction of a class to `S` is computed by any representing cocycle. -/
theorem resTriv_apply_eq (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m) (x : ContH1 G M)
    (c : cocycles G M) (hc : mk c = x) (s : S) : resTriv S hS x s = c s := by
  rw [← hc]; rfl

/-- For a normal subgroup acting trivially, a cocycle satisfies `c (g s g⁻¹) = g • c s`. -/
theorem cocycle_conj (S : Subgroup G) [S.Normal] (hS : ∀ s ∈ S, ∀ m : M, s • m = m)
    (c : cocycles G M) (g : G) {s : G} (hs : s ∈ S) : c (g * s * g⁻¹) = g • c s := by
  have h1 : g • c g⁻¹ * c g = 1 := by
    rw [← isMulCocycle₁ c, mul_inv_cancel, map_one_eq]
  rw [isMulCocycle₁ c, isMulCocycle₁ c, mul_smul, hS s hs, mul_left_comm, h1, mul_one]

/-- **The image of restriction consists of equivariant homomorphisms**: for `S` normal and
acting trivially, `φ = res_S x` satisfies `φ (g s g⁻¹) = g • φ s`. -/
theorem resTriv_conj (S : Subgroup G) [S.Normal] (hS : ∀ s ∈ S, ∀ m : M, s • m = m)
    (x : ContH1 G M) (g : G) (s : S) :
    resTriv S hS x ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ s.2 g⟩ =
      g • resTriv S hS x s := by
  induction x using induction_on with
  | h c => exact cocycle_conj S hS c g s.2

end Res

section Inflation

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- **`F2 = H¹(G ⧸ N, M)`**: the kernel of restriction to a normal subgroup `N` acting trivially
is the image of inflation (and inflation is injective, `inflation_injective`). -/
theorem ker_resTriv_eq_range_inflation (N : Subgroup G) [N.Normal]
    (hN : ∀ n ∈ N, ∀ m : M, n • m = m) :
    letI := MulDistribMulAction.quotientOfLeKer N hN
    (resTriv N hN).ker =
      (inflation N (fun g m => MulDistribMulAction.quotientOfLeKer_smul N hN g m)).range := by
  letI := MulDistribMulAction.quotientOfLeKer N hN
  have hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m :=
    fun g m => MulDistribMulAction.quotientOfLeKer_smul N hN g m
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := mk_surjective x
    refine exists_inflation_eq hcomp (mk c) ⟨c, rfl, fun n hn => ?_⟩
    have := DFunLike.congr_fun hx ⟨n, hn⟩
    simpa using this
  · rintro ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := mk_surjective y
    ext n
    change (cocyclesMap (QuotientGroup.mk' N) QuotientGroup.continuous_mk (MonoidHom.id M)
      continuous_id (fun g m => hcomp g m) c : G → M) n = 1
    rw [cocyclesMap_apply]
    change c ((n : G) : G ⧸ N) = 1
    rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.2, map_one_eq]

end Inflation

section Filtration

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  {DΘ D : Subgroup G} (hle : DΘ ≤ D) (hD : ∀ d ∈ D, ∀ m : M, d • m = m)

omit [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] in
/-- The trivial action of `D` restricts to `DΘ`. -/
theorem trivial_of_le {DΘ D : Subgroup G} (hle : DΘ ≤ D) (hD : ∀ d ∈ D, ∀ m : M, d • m = m)
    (d : G) (hd : d ∈ DΘ) (m : M) : d • m = m := hD d (hle hd) m

/-- `F1 = ker (res to DΘ)` ([EtTh], Prop. 1.5(i)): `F0/F1 ↪ Hom(DΘ, M)`. -/
def F1 : Subgroup (ContH1 G M) := (resTriv DΘ (trivial_of_le hle hD)).ker

/-- `F2 = ker (res to D)` ([EtTh], Prop. 1.5(i)). -/
def F2 : Subgroup (ContH1 G M) := (resTriv D hD).ker

theorem F2_le_F1 : F2 hD ≤ F1 hle hD := by
  intro x hx
  rw [F2, MonoidHom.mem_ker] at hx
  rw [F1, MonoidHom.mem_ker]
  ext s
  obtain ⟨c, rfl⟩ := mk_surjective x
  have := DFunLike.congr_fun hx ⟨s, hle s.2⟩
  simpa using this

/-- Homomorphisms `D → M` vanishing on `DΘ`, i.e. `Hom(D/DΘ, M)`. -/
def homVanishing : Subgroup (D →* M) where
  carrier := {φ | ∀ d : D, (d : G) ∈ DΘ → φ d = 1}
  one_mem' _ _ := rfl
  mul_mem' hφ hψ d hd := by rw [MonoidHom.mul_apply, hφ d hd, hψ d hd, mul_one]
  inv_mem' hφ d hd := by rw [MonoidHom.inv_apply, hφ d hd, inv_one]

/-- **The graded piece `F1 → Hom(D/DΘ, M)`** ([EtTh], Prop. 1.5(i)). -/
def thetaGraded : F1 hle hD →* homVanishing (M := M) (DΘ := DΘ) (D := D) where
  toFun x := ⟨resTriv D hD x, fun d hd => by
    obtain ⟨x, hx⟩ := x
    rw [F1, MonoidHom.mem_ker] at hx
    obtain ⟨c, rfl⟩ := mk_surjective x
    have := DFunLike.congr_fun hx ⟨d, hd⟩
    simpa using this⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem coe_thetaGraded (x : F1 hle hD) : (thetaGraded hle hD x : D →* M) = resTriv D hD x :=
  rfl

/-- The kernel of `F1 → Hom(D/DΘ, M)` is `F2`. -/
theorem ker_thetaGraded (x : F1 hle hD) : thetaGraded hle hD x = 1 ↔ (x : ContH1 G M) ∈ F2 hD := by
  rw [F2, MonoidHom.mem_ker, Subtype.ext_iff]
  rfl

end Filtration

section Transport

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  {G' M' : Type*} [Group G'] [TopologicalSpace G'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction G' M']

/-- **Transport of classes** along an isomorphism of topological groups `γ : G ≃ₜ* G'` and a
compatible isomorphism of coefficients `f : M ≃* M'` (`f (g • m) = γ g • f m`):
`c ↦ f ∘ c ∘ γ⁻¹`. -/
def pushIso (γ : G ≃ₜ* G') (f : M ≃* M') (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = γ g • f m) : ContH1 G M →* ContH1 G' M' :=
  map (γ.symm : G' →* G) γ.symm.continuous f.toMonoidHom hf fun h m => by
    simp [hcomp]

@[simp]
theorem pushIso_mk (γ : G ≃ₜ* G') (f : M ≃* M') (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = γ g • f m) (c : cocycles G M) (g' : G') :
    ∃ c' : cocycles G' M', pushIso γ f hf hcomp (mk c) = mk c' ∧ c' g' = f (c (γ.symm g')) :=
  ⟨_, rfl, rfl⟩

/-- Restriction commutes with transport: `res_{γ S} (γ_* x) (γ s) = f (res_S x s)`. -/
theorem resTriv_pushIso (γ : G ≃ₜ* G') (f : M ≃* M') (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = γ g • f m)
    (S : Subgroup G) (hS : ∀ s ∈ S, ∀ m : M, s • m = m)
    (S' : Subgroup G') (hS' : ∀ s ∈ S', ∀ m : M', s • m = m) (hSS' : ∀ s ∈ S, γ s ∈ S')
    (x : ContH1 G M) (s : S) :
    resTriv S' hS' (pushIso γ f hf hcomp x) ⟨γ s, hSS' s s.2⟩ = f (resTriv S hS x s) := by
  induction x using induction_on with
  | h c =>
    change f (c (γ.symm (γ s))) = f (c s)
    rw [ContinuousMulEquiv.symm_apply_apply]

/-- **Inner automorphisms act trivially on `H¹`**: `c ↦ (h ↦ g • c (g⁻¹ h g))` does not change
the class. -/
theorem map_conj_eq_id [IsTopologicalGroup G] (g : G) (hg : Continuous fun m : M => g • m) :
    map (MulAut.conj g⁻¹).toMonoidHom (by
        change Continuous fun h : G => g⁻¹ * h * g⁻¹⁻¹
        fun_prop)
      (MulDistribMulAction.toMonoidHom M g) hg (fun h m => by
        change g • ((g⁻¹ * h * g⁻¹⁻¹) • m) = h • g • m
        rw [smul_smul, smul_smul]
        congr 1
        group) =
      MonoidHom.id (ContH1 G M) := by
  ext x
  induction x using induction_on with
  | h c =>
    simp only [map_mk, MonoidHom.id_apply]
    rw [mk_eq_mk_iff]
    refine ⟨c g, fun h => ?_⟩
    change h • c g / c g = g • c (g⁻¹ * h * g⁻¹⁻¹) / c h
    have h1 : g • c g⁻¹ * c g = 1 := by
      rw [← isMulCocycle₁ c, mul_inv_cancel, map_one_eq]
    have h2 : c (g⁻¹ * h * g) = (g⁻¹ * h) • c g * (g⁻¹ • c h * c g⁻¹) := by
      rw [isMulCocycle₁ c, isMulCocycle₁ c]
    have h3 : g • c g⁻¹ = (c g)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_inv, h2, smul_mul', smul_mul', smul_smul, smul_smul, mul_inv_cancel_left,
      mul_inv_cancel, one_smul, h3, div_eq_mul_inv, div_eq_mul_inv, mul_comm (c h)]
    group

end Transport

section Uniqueness

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  {DΘ D : Subgroup G} (hle : DΘ ≤ D) (hD : ∀ d ∈ D, ∀ m : M, d • m = m)

/-- `D/DΘ` admits no nonzero homomorphism to `M` invariant under `(ι, f)`. -/
def NoInvariantHom (ι : G ≃ₜ* G) (f : M ≃* M) (hιD : ∀ d ∈ D, ι d ∈ D) : Prop :=
  ∀ φ : D →* M, (∀ d : D, (d : G) ∈ DΘ → φ d = 1) →
    (∀ d : D, φ ⟨ι d, hιD d d.2⟩ = f (φ d)) → φ = 1

omit [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M] in
/-- **Sufficient condition** ([EtTh], Prop. 1.5(iii): the inversion automorphism acts by `−1` on
`log(Ü)` and trivially on `Δ_Θ`): if `ι` inverts `D` modulo `DΘ`, `f = id`, and `M` has no
`2`-torsion, there is no nonzero invariant homomorphism. -/
theorem noInvariantHom_of_inv (ι : G ≃ₜ* G) (hιD : ∀ d ∈ D, ι d ∈ D)
    (hinv : ∀ d ∈ D, ι d * d ∈ DΘ) (htors : ∀ m : M, m * m = 1 → m = 1) :
    NoInvariantHom (DΘ := DΘ) ι (MulEquiv.refl M) hιD := by
  intro φ hφ hinvφ
  ext d
  apply htors
  have h1 : φ (⟨ι d, hιD d d.2⟩ * d) = 1 := hφ _ (hinv d d.2)
  rw [map_mul, hinvφ] at h1
  simpa using h1

/-- **The uniqueness step of [EtTh], Thm. 1.6(iii)** (proof, l.1596–1601): classes with the same
restriction to `DΘ` (the same image `log(Θ)` in `F0/F1`) that are fixed by `ι` modulo `F2`
("fixed, up to a unit multiple, under an inversion automorphism") differ by an element of `F2`
(a `(K̈^×)^∧`-multiple), provided `NoInvariantHom`. -/
theorem div_mem_F2_of_inv (ι : G ≃ₜ* G) (f : M ≃* M) (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m) (hιD : ∀ d ∈ D, ι d ∈ D)
    (hno : NoInvariantHom (DΘ := DΘ) ι f hιD) (x y : ContH1 G M)
    (hxy : resTriv DΘ (trivial_of_le hle hD) x = resTriv DΘ (trivial_of_le hle hD) y)
    (hx : pushIso ι f hf hcomp x / x ∈ F2 hD) (hy : pushIso ι f hf hcomp y / y ∈ F2 hD) :
    x / y ∈ F2 hD := by
  rw [F2, MonoidHom.mem_ker] at hx hy ⊢
  rw [map_div, div_eq_one] at hx hy
  rw [map_div, div_eq_one]
  -- `φ := res_D (x / y)` vanishes on `DΘ` and is `ι`-invariant
  set φ : D →* M := resTriv D hD x / resTriv D hD y with hφdef
  suffices φ = 1 by rwa [hφdef, div_eq_one] at this
  apply hno
  · intro d hd
    have := DFunLike.congr_fun hxy ⟨d, hd⟩
    obtain ⟨c, rfl⟩ := mk_surjective x
    obtain ⟨e, rfl⟩ := mk_surjective y
    simp only [resTriv_mk] at this
    simp [hφdef, this]
  · intro d
    have hxd := resTriv_pushIso ι f hf hcomp D hD D hD hιD x d
    have hyd := resTriv_pushIso ι f hf hcomp D hD D hD hιD y d
    rw [hx] at hxd
    rw [hy] at hyd
    simp only [hφdef, MonoidHom.div_apply, hxd, hyd, map_div]

end Uniqueness


section ClassSet

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  {DΘ D : Subgroup G} (hle : DΘ ≤ D) (hD : ∀ d ∈ D, ∀ m : M, d • m = m)

/-- **The set of theta classes** of [EtTh], Thm. 1.6(iii) (proof): the classes whose restriction
to `DΘ` is the given `λ` ("mapping to `log(Θ)` in `F0/F1`") and which are fixed by `ι` modulo
`F2` ("fixed, up to a unit multiple, under an inversion automorphism"). -/
def thetaClassSet (lam : DΘ →* M) (ι : G ≃ₜ* G) (f : M ≃* M) (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m) : Set (ContH1 G M) :=
  {x | resTriv DΘ (trivial_of_le hle hD) x = lam ∧ pushIso ι f hf hcomp x / x ∈ F2 hD}

/-- Any two theta classes differ by an element of `F2` (`div_mem_F2_of_inv`). -/
theorem div_mem_F2_of_mem_thetaClassSet (lam : DΘ →* M) (ι : G ≃ₜ* G) (f : M ≃* M)
    (hf : Continuous f) (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m)
    (hιD : ∀ d ∈ D, ι d ∈ D) (hno : NoInvariantHom (DΘ := DΘ) ι f hιD) {x y : ContH1 G M}
    (hx : x ∈ thetaClassSet hle hD lam ι f hf hcomp)
    (hy : y ∈ thetaClassSet hle hD lam ι f hf hcomp) : x / y ∈ F2 hD :=
  div_mem_F2_of_inv hle hD ι f hf hcomp hιD hno x y (hx.1.trans hy.1.symm) hx.2 hy.2

/-- `F2` is stable under transport along `ι` when `ι` preserves `D`. -/
theorem pushIso_mem_F2 (ι : G ≃ₜ* G) (f : M ≃* M) (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m) (hιD : ∀ d ∈ D, ι.symm d ∈ D)
    {z : ContH1 G M} (hz : z ∈ F2 hD) : pushIso ι f hf hcomp z ∈ F2 hD := by
  rw [F2, MonoidHom.mem_ker] at hz ⊢
  obtain ⟨c, rfl⟩ := mk_surjective z
  ext d
  have := DFunLike.congr_fun hz ⟨ι.symm d, hιD d d.2⟩
  simp only [resTriv_mk, MonoidHom.one_apply] at this
  change f (c (ι.symm d)) = 1
  rw [this, map_one]

/-- **The theta classes form a single `F2`-coset**: multiplying a theta class by an element of
`F2` gives a theta class. -/
theorem mul_mem_thetaClassSet (lam : DΘ →* M) (ι : G ≃ₜ* G) (f : M ≃* M)
    (hf : Continuous f) (hcomp : ∀ (g : G) (m : M), f (g • m) = ι g • f m)
    (hιD : ∀ d ∈ D, ι.symm d ∈ D) {x z : ContH1 G M}
    (hx : x ∈ thetaClassSet hle hD lam ι f hf hcomp) (hz : z ∈ F2 hD) :
    x * z ∈ thetaClassSet hle hD lam ι f hf hcomp := by
  refine ⟨?_, ?_⟩
  · rw [map_mul, hx.1, F2_le_F1 hle hD hz, mul_one]
  · rw [map_mul, mul_div_mul_comm]
    exact Subgroup.mul_mem _ hx.2
      (Subgroup.div_mem _ (pushIso_mem_F2 hD ι f hf hcomp hιD hz) hz)

end ClassSet

section TransportClassSet

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]
  {G' M' : Type*} [Group G'] [TopologicalSpace G'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction G' M']

/-- Transport is functorial: `(γ ∘ ι)_* = γ_* ∘ ι_*` on representatives. -/
theorem pushIso_pushIso {G'' M'' : Type*} [Group G''] [TopologicalSpace G''] [CommGroup M'']
    [TopologicalSpace M''] [IsTopologicalGroup M''] [MulDistribMulAction G'' M'']
    (γ : G ≃ₜ* G') (f : M ≃* M') (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = γ g • f m)
    (δ : G' ≃ₜ* G'') (f' : M' ≃* M'') (hf' : Continuous f')
    (hcomp' : ∀ (g : G') (m : M'), f' (g • m) = δ g • f' m) (x : ContH1 G M) :
    pushIso δ f' hf' hcomp' (pushIso γ f hf hcomp x) =
      pushIso (γ.trans δ) (f.trans f') (hf'.comp hf)
        (fun g m => by simp [hcomp, hcomp']) x := by
  induction x using induction_on with
  | h c => rfl

/-- **Transport of theta classes ([EtTh], Thm. 1.6(iii), group-theoretic part)**: an isomorphism
`γ : G ≃ₜ* G'` with a compatible isomorphism of coefficients `f`, carrying `D`, `DΘ` to `D'`,
`DΘ'`, `λ` to `λ'`, and intertwining the automorphisms `(ι, f_ι)` and `(ι', f_ι')`, maps the set of
theta classes into the set of theta classes. -/
theorem pushIso_mem_thetaClassSet {DΘ D : Subgroup G} (hle : DΘ ≤ D)
    (hD : ∀ d ∈ D, ∀ m : M, d • m = m) {DΘ' D' : Subgroup G'} (hle' : DΘ' ≤ D')
    (hD' : ∀ d ∈ D', ∀ m : M', d • m = m)
    (γ : G ≃ₜ* G') (f : M ≃* M') (hf : Continuous f)
    (hcomp : ∀ (g : G) (m : M), f (g • m) = γ g • f m)
    (hγD : ∀ d ∈ D', γ.symm d ∈ D) (hγDΘ : ∀ d ∈ DΘ', γ.symm d ∈ DΘ)
    (lam : DΘ →* M) (lam' : DΘ' →* M')
    (hlam : ∀ d : DΘ', lam' d = f (lam ⟨γ.symm d, hγDΘ d d.2⟩))
    (ι : G ≃ₜ* G) (fι : M ≃* M) (hfι : Continuous fι)
    (hcompι : ∀ (g : G) (m : M), fι (g • m) = ι g • fι m)
    (ι' : G' ≃ₜ* G') (fι' : M' ≃* M') (hfι' : Continuous fι')
    (hcompι' : ∀ (g : G') (m : M'), fι' (g • m) = ι' g • fι' m)
    (hιγ : ∀ g, ι' (γ g) = γ (ι g)) (hfιf : ∀ m, fι' (f m) = f (fι m))
    {x : ContH1 G M} (hx : x ∈ thetaClassSet hle hD lam ι fι hfι hcompι) :
    pushIso γ f hf hcomp x ∈ thetaClassSet hle' hD' lam' ι' fι' hfι' hcompι' := by
  obtain ⟨c, rfl⟩ := mk_surjective x
  refine ⟨?_, ?_⟩
  · ext d
    have h1 := DFunLike.congr_fun hx.1 ⟨γ.symm d, hγDΘ d d.2⟩
    simp only [resTriv_mk] at h1
    rw [hlam d, ← h1]
    rfl
  · have h2 := hx.2
    rw [F2, MonoidHom.mem_ker] at h2 ⊢
    ext d
    have h3 := DFunLike.congr_fun h2 ⟨γ.symm d, hγD d d.2⟩
    have hι'sym : ∀ g', ι'.symm g' = γ (ι.symm (γ.symm g')) := by
      intro g'
      apply ι'.injective
      rw [ContinuousMulEquiv.apply_symm_apply, hιγ, ContinuousMulEquiv.apply_symm_apply,
        ContinuousMulEquiv.apply_symm_apply]
    change fι' (f (c (γ.symm (ι'.symm d)))) / f (c (γ.symm d)) = 1
    change fι (c (ι.symm (γ.symm d))) / c (γ.symm d) = 1 at h3
    rw [hι'sym, ContinuousMulEquiv.symm_apply_apply, hfιf, ← map_div, h3, map_one]

end TransportClassSet

end ContH1
