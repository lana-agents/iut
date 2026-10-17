/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisSlim
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Profinite groups from their Galois base categories

[FrdII], Theorem 2.4, starts from an equivalence of Frobenioids, which induces an equivalence
`Ψ_Base : D₁ ≌ D₂` of base categories, "hence an outer isomorphism of topological groups
`Π₁ ≅ Π₂` [cf. [Mzk2], Proposition 3.2; [Mzk2], Theorem A.4]". This file proves the profinite
case of this step for the Galois base categories `B(G)⁰ = OrbitObj G`:

* `IsGaloisObj A`: `Aut(A)` acts transitively on `Hom(B, A)` for every `B` (a purely
  category-theoretic condition, preserved by equivalences: `IsGaloisObj.map`);
* `OrbitObj.isGaloisObj_iff`: `G/H` is a Galois object iff `H` is normal;
* **`OrbitObj.exists_continuousMulEquiv`**: for profinite `G₁`, `G₂` and an equivalence
  `F : B(G₁)⁰ ≌ B(G₂)⁰`, there are an isomorphism of topological groups `α : G₁ ≅ G₂` and
  compatible base points `x_N ∈ F(G₁/N)` (`N` open normal) such that `F(G₁/N) = G₂/α(N)` and
  `F` maps the automorphism `rmul g : yN ↦ ygN` of `G₁/N` to the automorphism of `F(G₁/N)` sending
  `x_N` to `α(g)·x_N`. The choice of the base points (a section of the inverse system
  `N ↦ F(G₁/N)`, which exists by compactness) is the "outer" indeterminacy: changing it
  composes `α` with an inner automorphism.

The construction: `φ(g)` is the unique element of `G₂` lying in all the cosets
`{h : h·x_N = F(rmul g)(x_N)}` of `α(N) = Stab(x_N)` (compactness and `⋂ N = 1`); `φ` is a
homomorphism since `F` preserves composition and maps are equivariant, continuous since
`φ(N) ⊆ Stab(x_N)`, injective since `F` is faithful, and surjective since `F` is full and the
`F(G₁/N)` are cofinal among the `G₂/N'`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u u'

/-- **Galois objects**: `Aut(A)` acts transitively on `Hom(B, A)` for every `B`. -/
def IsGaloisObj {C : Type*} [Category C] (A : C) : Prop :=
  ∀ ⦃B : C⦄ (f g : B ⟶ A), ∃ σ : A ≅ A, f ≫ σ.hom = g

/-- Equivalences preserve Galois objects. -/
lemma IsGaloisObj.map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.IsEquivalence]
    {A : C} (h : IsGaloisObj A) : IsGaloisObj (F.obj A) := by
  intro B f g
  let e := F.objObjPreimageIso B
  obtain ⟨σ, hσ⟩ := h (F.preimage (e.hom ≫ f)) (F.preimage (e.hom ≫ g))
  refine ⟨F.mapIso σ, ?_⟩
  have := congrArg F.map hσ
  rw [F.map_comp, F.map_preimage, F.map_preimage, Category.assoc] at this
  exact (cancel_epi e.hom).mp this

namespace OrbitObj

section Galois

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma mem_stabilizer_mk_iff {H : Subgroup G} (c g : G) :
    g ∈ MulAction.stabilizer G (QuotientGroup.mk c : G ⧸ H) ↔ c⁻¹ * g * c ∈ H := by
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    have := H.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := H.inv_mem h
    simpa [mul_assoc] using this

omit [IsTopologicalGroup G] [TopologicalSpace G] in
/-- For normal `H`, every point of `G/H` has stabilizer `H`. -/
lemma stabilizer_eq_of_normal {H : Subgroup G} [hH : H.Normal] (x : G ⧸ H) :
    MulAction.stabilizer G x = H := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  ext g
  rw [mem_stabilizer_mk_iff]
  constructor
  · intro h
    have := hH.conj_mem _ h c
    simpa [mul_assoc] using this
  · intro h
    have := hH.conj_mem _ h c⁻¹
    simpa [mul_assoc] using this

omit [IsTopologicalGroup G] in
lemma stabilizer_le_map {A B : OrbitObj G} (f : A ⟶ B) (x : G ⧸ A.H) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (f.toFun x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← f.map_smul, hg]

/-- The automorphism `y H ↦ y c H` of `G/H` for normal `H`. -/
def rmulN (A : OrbitObj G) [A.H.Normal] (c : G) : A ⟶ A :=
  pointHom A A (QuotientGroup.mk c) (by rw [stabilizer_eq_of_normal])

omit [IsTopologicalGroup G] in
lemma rmulN_mk (A : OrbitObj G) [A.H.Normal] (c g : G) :
    (rmulN A c).toFun (QuotientGroup.mk g) = QuotientGroup.mk (g * c) := by
  rw [rmulN, pointHom_mk, MulAction.Quotient.smul_mk, smul_eq_mul]

omit [IsTopologicalGroup G] in
lemma rmulN_mul (A : OrbitObj G) [A.H.Normal] (c d : G) :
    rmulN A c ≫ rmulN A d = rmulN A (c * d) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [OrbitHom.comp_toFun, Function.comp_apply, rmulN_mk, rmulN_mk, rmulN_mk, mul_assoc]

omit [IsTopologicalGroup G] in
lemma rmulN_one (A : OrbitObj G) [A.H.Normal] : rmulN A 1 = 𝟙 A := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g => rw [rmulN_mk, mul_one]; rfl

/-- The automorphism `rmulN A c` as an isomorphism. -/
def rmulIso (A : OrbitObj G) [A.H.Normal] (c : G) : A ≅ A where
  hom := rmulN A c
  inv := rmulN A c⁻¹
  hom_inv_id := by rw [rmulN_mul, mul_inv_cancel, rmulN_one]
  inv_hom_id := by rw [rmulN_mul, inv_mul_cancel, rmulN_one]

omit [IsTopologicalGroup G] in
/-- A morphism to `G/H`, `H` normal, sending one point to `x c` … -/
lemma comp_rmulN_apply {A B : OrbitObj G} [B.H.Normal] (f : A ⟶ B) (c g : G) {x : G}
    (hx : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk x) :
    (f ≫ rmulN B c).toFun (QuotientGroup.mk g) = QuotientGroup.mk (g * x * c) := by
  rw [OrbitHom.comp_toFun, Function.comp_apply, OrbitHom.apply_mk_of_eq f hx, rmulN_mk]

/-- **`G/H` is a Galois object iff `H` is normal.** -/
theorem isGaloisObj_iff (A : OrbitObj G) : IsGaloisObj A ↔ A.H.Normal := by
  constructor
  · intro h
    refine ⟨fun n hn g => ?_⟩
    -- `B = G/(H ∩ Stab(g⁻¹H))` with the two points `H`, `g⁻¹H`
    set c : G := g⁻¹
    let B : OrbitObj G := ⟨A.H ⊓ MulAction.stabilizer G (QuotientGroup.mk c : G ⧸ A.H),
      A.isOpen.inter (isOpen_stabilizer A _)⟩
    have h1 : B.H ≤ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ A.H) := fun y hy => by
      rw [mem_stabilizer_mk_iff]; simpa using hy.1
    obtain ⟨σ, hσ⟩ := h (pointHom B A _ h1) (pointHom B A (QuotientGroup.mk c) inf_le_right)
    have e1 : σ.hom.toFun (QuotientGroup.mk 1) = QuotientGroup.mk c := by
      have := congrArg (fun f : B ⟶ A => f.toFun (QuotientGroup.mk 1)) hσ
      simpa [pointHom_mk] using this
    have e2 : σ.hom.toFun (QuotientGroup.mk n) = QuotientGroup.mk (n * c) := by
      rw [OrbitHom.apply_mk_of_eq _ e1]
    have e3 : (QuotientGroup.mk n : G ⧸ A.H) = QuotientGroup.mk 1 :=
      QuotientGroup.eq.mpr (by simpa using A.H.inv_mem hn)
    rw [e3, e1] at e2
    have := QuotientGroup.eq.mp e2.symm
    have h4 : c⁻¹ * n * c ∈ A.H := by
      have := A.H.inv_mem this
      simpa [mul_assoc] using this
    simpa [c] using h4
  · intro hH B f g
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (f.toFun (QuotientGroup.mk 1))
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (g.toFun (QuotientGroup.mk 1))
    refine ⟨rmulIso A (x⁻¹ * y), ?_⟩
    ext z
    induction z using QuotientGroup.induction_on with
    | H k =>
      change (f ≫ rmulN A (x⁻¹ * y)).toFun _ = _
      rw [comp_rmulN_apply f _ _ hx.symm, OrbitHom.apply_mk_of_eq g hy.symm]
      congr 1
      group

omit [IsTopologicalGroup G] in
/-- An endomorphism of `G/H`, `H` normal, fixing one point is the identity. -/
lemma eq_id_of_fix {A : OrbitObj G} [A.H.Normal] (f : A ⟶ A) {x : G ⧸ A.H}
    (hx : f.toFun x = x) : f = 𝟙 A := by
  ext y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
  have : (QuotientGroup.mk d : G ⧸ A.H) = (d * c⁻¹) • QuotientGroup.mk c := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]
  rw [this, f.map_smul, hx]
  rfl

omit [IsTopologicalGroup G] in
/-- An endomorphism of `G/H`, `H` normal, can send any point to any point. -/
lemma exists_endo {A : OrbitObj G} [A.H.Normal] (x y : G ⧸ A.H) :
    ∃ f : A ⟶ A, f.toFun x = y := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨rmulN A (c⁻¹ * d), ?_⟩
  rw [rmulN_mk, mul_inv_cancel_left]

end Galois

/-! ### The reconstruction of `G` -/

section Recon

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [CompactSpace G₁]
  [TotallyDisconnectedSpace G₁] [T2Space G₁]
variable {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [CompactSpace G₂] [TotallyDisconnectedSpace G₂] [T2Space G₂]
variable (F : OrbitObj G₁ ⥤ OrbitObj G₂) [F.IsEquivalence]

/-- In a profinite group, the open normal subgroups intersect in `1`. -/
lemma eq_one_of_forall_mem {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] {k : G}
    (h : ∀ N : OpenNormalSubgroup G, k ∈ N) : k = 1 := by
  by_contra hk
  obtain ⟨N, hN⟩ := exists_ons_le (isOpen_compl_singleton (x := k))
    (by simpa [eq_comm] using hk)
  exact hN (h N) rfl

/-- The image `H'_N` of `G₁/N` (with `F(G₁/N) = G₂/H'_N`). -/
abbrev Hc (N : OpenNormalSubgroup G₁) : Subgroup G₂ := (F.obj (ofONS N)).H

instance normal_Hc (N : OpenNormalSubgroup G₁) : (Hc F N).Normal :=
  (isGaloisObj_iff _).mp (((isGaloisObj_iff (ofONS N)).mpr N.isNormal').map F)

instance finite_quot (A : OrbitObj G₂) : Finite (G₂ ⧸ A.H) :=
  Subgroup.quotient_finite_of_isOpen A.H A.isOpen

/-- The projection `G₁/N → G₁/M` for `N ≤ M`. -/
noncomputable abbrev projN {N M : OpenNormalSubgroup G₁} (h : N ≤ M) : ofONS N ⟶ ofONS M :=
  proj (ofONS M) (fun _ hx => h hx)

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma projN_refl (N : OpenNormalSubgroup G₁) : projN (le_refl N) = 𝟙 _ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g => rw [proj_mk]; rfl

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma projN_comp {N M L : OpenNormalSubgroup G₁} (h : N ≤ M) (h' : M ≤ L) :
    projN h ≫ projN h' = projN (h.trans h') := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [OrbitHom.comp_toFun, Function.comp_apply, proj_mk, proj_mk, proj_mk]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma rmul_projN {N M : OpenNormalSubgroup G₁} (h : N ≤ M) (g : G₁) :
    rmul N g ≫ projN h = projN h ≫ rmul M g := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [OrbitHom.comp_toFun, OrbitHom.comp_toFun, Function.comp_apply, Function.comp_apply,
      rmul_mk, proj_mk, proj_mk, rmul_mk]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma rmul_mul (N : OpenNormalSubgroup G₁) (g₁ g₂ : G₁) :
    rmul N g₁ ≫ rmul N g₂ = rmul N (g₁ * g₂) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [OrbitHom.comp_toFun, Function.comp_apply, rmul_mk, rmul_mk, rmul_mk, mul_assoc]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma rmul_eq_id_iff (N : OpenNormalSubgroup G₁) (g : G₁) : rmul N g = 𝟙 _ ↔ g ∈ N := by
  constructor
  · intro h
    have h1 := congrArg (fun f : ofONS N ⟶ ofONS N => f.toFun (QuotientGroup.mk 1)) h
    simp only at h1
    rw [rmul_mk, one_mul] at h1
    have h2 : g⁻¹ * 1 ∈ N.toSubgroup := QuotientGroup.eq.mp h1
    rw [mul_one] at h2
    have h3 := N.toSubgroup.inv_mem h2
    rw [inv_inv] at h3
    exact h3
  · intro hg
    ext y
    induction y using QuotientGroup.induction_on with
    | H k =>
      rw [rmul_mk]
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using N.toSubgroup.inv_mem hg)

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma exists_rmul_eq (N : OpenNormalSubgroup G₁) (σ : ofONS N ⟶ ofONS N) :
    ∃ g, σ = rmul N g := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (σ.toFun (QuotientGroup.mk 1))
  refine ⟨c, ?_⟩
  ext y
  induction y using QuotientGroup.induction_on with
  | H k => rw [OrbitHom.apply_mk_of_eq σ hc.symm, rmul_mk]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] in
lemma le_of_hom {j k : (OpenNormalSubgroup G₁)ᵒᵈᵒᵖ} (f : j ⟶ k) :
    OrderDual.ofDual j.unop ≤ OrderDual.ofDual k.unop :=
  leOfHom f.unop

/-- The inverse system `N ↦ F(G₁/N)` (indexed by open normal subgroups, ordered by `⊇`). -/
noncomputable def ptSystem : (OpenNormalSubgroup G₁)ᵒᵈᵒᵖ ⥤ Type u' where
  obj j := G₂ ⧸ Hc F (OrderDual.ofDual j.unop)
  map {j k} f := TypeCat.ofHom (F.map (projN (le_of_hom f))).toFun
  map_id j := by
    rw [projN_refl, F.map_id]
    rfl
  map_comp {j k l} f g := by
    rw [← projN_comp (le_of_hom f) (le_of_hom g), F.map_comp]
    rfl

instance (j : (OpenNormalSubgroup G₁)ᵒᵈᵒᵖ) : Finite ((ptSystem F).obj j) := finite_quot _

instance (j : (OpenNormalSubgroup G₁)ᵒᵈᵒᵖ) : Nonempty ((ptSystem F).obj j) :=
  ⟨QuotientGroup.mk 1⟩

/-- **Compatible base points** `x_N ∈ F(G₁/N)` (a section of `ptSystem`, by compactness). -/
noncomputable def pt (N : OpenNormalSubgroup G₁) : G₂ ⧸ Hc F N :=
  (nonempty_sections_of_finite_inverse_system (ptSystem F)).some
    (Opposite.op (OrderDual.toDual N))

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁]
  [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma pt_compat {N M : OpenNormalSubgroup G₁} (h : N ≤ M) :
    (F.map (projN h)).toFun (pt F N) = pt F M :=
  (nonempty_sections_of_finite_inverse_system (ptSystem F)).some_mem
    (j := Opposite.op (OrderDual.toDual N)) (j' := Opposite.op (OrderDual.toDual M))
    (homOfLE (show OrderDual.toDual M ≤ OrderDual.toDual N from h)).op

/-- The coset `{h : h·x_N = F(rmul g)(x_N)}`. -/
def cosetF (g : G₁) (N : OpenNormalSubgroup G₁) : Set G₂ :=
  {h | h • pt F N = (F.map (rmul N g)).toFun (pt F N)}

omit [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁] [CompactSpace G₂]
  [TotallyDisconnectedSpace G₂] [T2Space G₂] in
lemma smul_eq_smul_iff {N : OpenNormalSubgroup G₁} (h h' : G₂) (x : G₂ ⧸ Hc F N) :
    h • x = h' • x ↔ h⁻¹ * h' ∈ Hc F N := by
  rw [← SetLike.ext_iff.mp (stabilizer_eq_of_normal (H := Hc F N) x),
    MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, eq_comm]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁]
  [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma isClosed_cosetF (g : G₁) (N : OpenNormalSubgroup G₁) : IsClosed (cosetF F g N) := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (pt F N)
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective ((F.map (rmul N g)).toFun (pt F N))
  have : cosetF F g N = (fun h => (h * c)⁻¹ * d) ⁻¹' (Hc F N : Set G₂) := by
    ext h
    simp only [cosetF, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← hd, ← hc, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  rw [this]
  exact (Subgroup.isClosed_of_isOpen _ (F.obj (ofONS N)).isOpen).preimage (by fun_prop)

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁]
  [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma cosetF_nonempty (g : G₁) (N : OpenNormalSubgroup G₁) : (cosetF F g N).Nonempty := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (pt F N)
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective ((F.map (rmul N g)).toFun (pt F N))
  refine ⟨d * c⁻¹, ?_⟩
  simp only [cosetF, Set.mem_setOf_eq]
  rw [← hd, ← hc, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]

omit [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁]
  [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma cosetF_mono (g : G₁) {N M : OpenNormalSubgroup G₁} (hNM : N ≤ M) :
    cosetF F g N ⊆ cosetF F g M := by
  intro h hh
  simp only [cosetF, Set.mem_setOf_eq] at hh ⊢
  have := congrArg (F.map (projN hNM)).toFun hh
  rw [OrbitHom.map_smul, pt_compat] at this
  rw [this]
  change ((F.map (rmul N g)) ≫ F.map (projN hNM)).toFun (pt F N) = _
  rw [← F.map_comp, rmul_projN, F.map_comp]
  change (F.map (rmul M g)).toFun ((F.map (projN hNM)).toFun (pt F N)) = _
  rw [pt_compat]

omit [T2Space G₁] [CompactSpace G₂] [TotallyDisconnectedSpace G₂] [T2Space G₂] in
/-- Cofinality: every open normal subgroup of `G₂` contains some `H'_N`. -/
lemma exists_Hc_le (K : OpenNormalSubgroup G₂) : ∃ N : OpenNormalSubgroup G₁,
    Hc F N ≤ K.toSubgroup := by
  let B := F.objPreimage (ofONS K)
  let e : F.obj B ≅ ofONS K := F.objObjPreimageIso (ofONS K)
  obtain ⟨N, hN⟩ := exists_ons_le B.isOpen B.H.one_mem
  refine ⟨N, ?_⟩
  let f : F.obj (ofONS N) ⟶ ofONS K := F.map (proj B (fun _ hx => hN hx)) ≫ e.hom
  have := stabilizer_le_map f (QuotientGroup.mk 1)
  rwa [stabilizer_eq_of_normal, stabilizer_eq_of_normal (H := K.toSubgroup)] at this

omit [T2Space G₁] in
lemma eq_of_mem_cosetF {g : G₁} {h h' : G₂} (hh : ∀ N, h ∈ cosetF F g N)
    (hh' : ∀ N, h' ∈ cosetF F g N) : h = h' := by
  have hk : ∀ N, h⁻¹ * h' ∈ Hc F N := fun N =>
    (smul_eq_smul_iff F h h' (pt F N)).mp ((hh N).trans (hh' N).symm)
  have : h⁻¹ * h' = 1 := eq_one_of_forall_mem fun K => by
    obtain ⟨N, hN⟩ := exists_Hc_le F K
    exact hN (hk N)
  exact inv_mul_eq_one.mp this

omit [T2Space G₁] [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma exists_mem_cosetF (g : G₁) : ∃ h : G₂, ∀ N, h ∈ cosetF F g N := by
  haveI : Nonempty (OpenNormalSubgroup G₁) := by
    obtain ⟨N, -⟩ := exists_ons_le (G := G₁) isOpen_univ (Set.mem_univ 1)
    exact ⟨N⟩
  have hdir : Directed (· ⊇ ·) (cosetF F g) := fun N M =>
    ⟨N ⊓ M, cosetF_mono F g inf_le_left, cosetF_mono F g inf_le_right⟩
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (cosetF F g) hdir (cosetF_nonempty F g) (fun N => (isClosed_cosetF F g N).isCompact)
    (isClosed_cosetF F g)
  exact ⟨h, Set.mem_iInter.mp hh⟩

/-- The map `φ : G₁ → G₂`. -/
noncomputable def phi₀ (g : G₁) : G₂ := (exists_mem_cosetF F g).choose

omit [T2Space G₁] [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma phi₀_mem (g : G₁) (N : OpenNormalSubgroup G₁) : phi₀ F g ∈ cosetF F g N :=
  (exists_mem_cosetF F g).choose_spec N

omit [T2Space G₁] [TotallyDisconnectedSpace G₂] [T2Space G₂] [F.IsEquivalence] in
lemma phi₀_smul (g : G₁) (N : OpenNormalSubgroup G₁) :
    phi₀ F g • pt F N = (F.map (rmul N g)).toFun (pt F N) := phi₀_mem F g N

/-- `φ` as a homomorphism. -/
noncomputable def phi : G₁ →* G₂ where
  toFun := phi₀ F
  map_one' := eq_of_mem_cosetF F (phi₀_mem F 1) fun N => by
    simp only [cosetF, Set.mem_setOf_eq, one_smul]
    rw [(rmul_eq_id_iff N 1).mpr N.toSubgroup.one_mem, F.map_id]
    rfl
  map_mul' g₁ g₂ := eq_of_mem_cosetF F (phi₀_mem F (g₁ * g₂)) fun N => by
    simp only [cosetF, Set.mem_setOf_eq]
    rw [mul_smul, phi₀_smul, ← OrbitHom.map_smul, phi₀_smul, ← rmul_mul, F.map_comp]
    rfl

omit [T2Space G₁] in
lemma phi_smul (g : G₁) (N : OpenNormalSubgroup G₁) :
    phi F g • pt F N = (F.map (rmul N g)).toFun (pt F N) := phi₀_smul F g N

omit [T2Space G₁] in
lemma phi_mem_Hc_iff (g : G₁) (N : OpenNormalSubgroup G₁) : phi F g ∈ Hc F N ↔ g ∈ N := by
  rw [← rmul_eq_id_iff]
  constructor
  · intro h
    have hfix : (F.map (rmul N g)).toFun (pt F N) = pt F N := by
      rw [← phi_smul]
      exact (smul_eq_smul_iff F (phi F g) 1 (pt F N)).mpr (by simpa using h) |>.trans
        (one_smul _ _)
    apply F.map_injective
    rw [F.map_id]
    exact eq_id_of_fix _ hfix
  · intro h
    have := phi_smul F g N
    rw [h, F.map_id] at this
    have h1 : phi F g • pt F N = (1 : G₂) • pt F N := this.trans (one_smul _ _).symm
    simpa using (smul_eq_smul_iff F _ _ _).mp h1

omit [T2Space G₁] in
lemma continuous_phi : Continuous (phi F) := by
  refine continuous_of_continuousAt_one (phi F) ?_
  intro U hU
  rw [map_one] at hU
  obtain ⟨V, hVU, hV, h1⟩ := mem_nhds_iff.mp hU
  obtain ⟨K, hK⟩ := exists_ons_le hV h1
  obtain ⟨N, hN⟩ := exists_Hc_le F K
  refine Filter.mem_map.mpr (Filter.mem_of_superset (N.isOpen.mem_nhds N.toSubgroup.one_mem)
    fun g hg => ?_)
  exact hVU (hK (hN ((phi_mem_Hc_iff F g N).mpr hg)))

lemma phi_injective : Function.Injective (phi F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_forall_mem fun N => (phi_mem_Hc_iff F g N).mp (by rw [hg]; exact one_mem _)

omit [T2Space G₁] in
lemma phi_surjective : Function.Surjective (phi F) := by
  have hcl : IsClosed (Set.range (phi F)) := (isCompact_range (continuous_phi F)).isClosed
  intro h
  suffices h ∈ closure (Set.range (phi F)) by
    rw [hcl.closure_eq] at this
    exact this
  rw [mem_closure_iff]
  intro U hU hhU
  have h1 : (1 : G₂) ∈ (h * ·) ⁻¹' U := by simpa using hhU
  obtain ⟨K, hK⟩ := exists_ons_le (hU.preimage (continuous_const_mul h)) h1
  obtain ⟨N, hN⟩ := exists_Hc_le F K
  obtain ⟨ψ, hψ⟩ := exists_endo (A := F.obj (ofONS N)) (pt F N) (h • pt F N)
  obtain ⟨g, hg⟩ := exists_rmul_eq N (F.preimage ψ)
  have hFg : F.map (rmul N g) = ψ := by rw [← hg, F.map_preimage]
  have hmem : h • pt F N = phi F g • pt F N := by rw [phi_smul, hFg, hψ]
  have hk := (smul_eq_smul_iff F _ _ _).mp hmem
  refine ⟨phi F g, ?_, g, rfl⟩
  have := hK (hN hk)
  simpa using this

/-- The isomorphism of topological groups `G₁ ≅ G₂` induced by `F`. -/
noncomputable def phiEquiv : G₁ ≃ₜ* G₂ :=
  let e : G₁ ≃* G₂ := MulEquiv.ofBijective (phi F) ⟨phi_injective F, phi_surjective F⟩
  let t : G₁ ≃ₜ G₂ := (continuous_phi F).homeoOfEquivCompactToT2 (f := e.toEquiv)
  { e with
    continuous_toFun := t.continuous
    continuous_invFun := t.symm.continuous }

lemma phiEquiv_apply (g : G₁) : phiEquiv F g = phi F g := rfl

lemma Hc_eq_map (N : OpenNormalSubgroup G₁) :
    Hc F N = N.toSubgroup.map (phiEquiv F : G₁ →* G₂) := by
  ext h
  constructor
  · intro hh
    obtain ⟨g, rfl⟩ := phi_surjective F h
    exact ⟨g, (phi_mem_Hc_iff F g N).mp hh, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (phi_mem_Hc_iff F g N).mpr hg

/-- **An equivalence `B(G₁)⁰ ≌ B(G₂)⁰` of Galois base categories of profinite groups induces an
isomorphism of topological groups** ([FrdII], Theorem 2.4, via [Mzk2], Proposition 3.2, in the
profinite case): there are `α : G₁ ≅ G₂` and compatible base points `x_N ∈ F(G₁/N)` such that
`F(G₁/N) = G₂/α(N)` and `F(rmul g)(x_N) = α(g)·x_N` for all `g`, `N`. -/
theorem exists_continuousMulEquiv : ∃ (α : G₁ ≃ₜ* G₂) (x : ∀ N, G₂ ⧸ (F.obj (ofONS N)).H),
    (∀ N, (F.obj (ofONS N)).H = N.toSubgroup.map (α : G₁ →* G₂)) ∧
    (∀ {N M : OpenNormalSubgroup G₁} (h : N ≤ M),
      (F.map (proj (ofONS M) (fun _ hx => h hx))).toFun (x N) = x M) ∧
    ∀ N g, (F.map (rmul N g)).toFun (x N) = α g • x N :=
  ⟨phiEquiv F, pt F, Hc_eq_map F, fun h => pt_compat F h, fun N g => (phi_smul F g N).symm⟩

end Recon

end OrbitObj

end Frobenioid

end Iut
