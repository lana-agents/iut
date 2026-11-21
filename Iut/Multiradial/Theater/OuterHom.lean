/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.OrbitIsoRecon

/-!
# Outer homomorphisms and the functors `B(G₁)⁰ ⥤ B(G₂)⁰` they induce (MR22 T1, part 1)

IUT I, §0 ("Monoids and Categories", l.2035–2087 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): for Galois-countable tempered
(or profinite) groups `Π₁`, `Π₂` the morphisms `B^temp(Π₁)⁰ → B^temp(Π₂)⁰` correspond to the
continuous **outer** homomorphisms `Π₁ → Π₂` (Remark 2.5.3 (ii), (E7); [SemiAnbd], Proposition
3.2). This file provides the group-theoretic side:

* `ConjRel`, `OuterHom G₁ G₂`: continuous homomorphisms modulo conjugation by `G₂`, with
  composition `OuterHom.comp` and identities;
* the functors `OrbitObj.mapFunctor` of `B(G)⁰` (`G/H ↦ G'/p(H)`) are compatible with composition
  and identities up to natural isomorphism (`mapFunctorComp`, `mapFunctorId`, `mapFunctorCongr`),
  in particular `isoFunctor (σ.trans τ) ≅ isoFunctor σ ⋙ isoFunctor τ` (`isoFunctorTrans`);
* **rigidity** (`conj_of_isoFunctor_iso`): if `isoFunctor σ ≅ isoFunctor τ` for isomorphisms of
  topological groups `σ τ : G₁ ≅ G₂`, then `τ` is `σ` followed by an inner automorphism, for `G₂`
  Hausdorff, with a basis of open normal subgroups and complete for them (`IsONSComplete`; e.g.
  profinite, `isONSComplete_of_compact`, or tempered). Conversely conjugate maps induce isomorphic
  functors (`OrbitObj.mapFunctorConjIso`);
* `OrbitEquivRecon G₁ G₂`: every equivalence `B(G₁)⁰ ≌ B(G₂)⁰` is isomorphic to `isoFunctor σ`
  for some `σ : G₁ ≅ G₂` ([Mzk2], Proposition 3.2; [SemiAnbd], Proposition 3.2), proved for
  profinite groups (`orbitEquivRecon_of_profinite`) and for tempered groups
  (`orbitEquivRecon_of_temp`) from MR21's `OrbitObj.natIsoOfBasePoints`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace Theater

open CategoryTheory Iut.Frobenioid

universe u₁ u₂ u₃

/-! ### Outer homomorphisms -/

section Outer

variable (G₁ : Type u₁) (G₂ : Type u₂) (G₃ : Type u₃) [Group G₁] [TopologicalSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [Group G₃] [TopologicalSpace G₃]

variable {G₁ G₂ G₃} in
/-- **Conjugate homomorphisms**: `g = γ f(−) γ⁻¹` for some `γ ∈ G₂`. -/
def ConjRel (f g : G₁ →ₜ* G₂) : Prop := ∃ γ : G₂, ∀ x, g x = γ * f x * γ⁻¹

/-- Conjugacy of continuous homomorphisms, as a setoid. -/
def conjSetoid : Setoid (G₁ →ₜ* G₂) where
  r := ConjRel
  iseqv := ⟨fun _ => ⟨1, fun x => by group⟩,
    fun ⟨γ, h⟩ => ⟨γ⁻¹, fun x => by rw [h]; group⟩,
    fun ⟨γ, h⟩ ⟨δ, h'⟩ => ⟨δ * γ, fun x => by rw [h', h]; group⟩⟩

/-- **Continuous outer homomorphisms `G₁ → G₂`** (IUT I, §0): continuous homomorphisms modulo
conjugation by `G₂`. -/
def OuterHom : Type _ := Quotient (conjSetoid G₁ G₂)

variable {G₁ G₂ G₃}

/-- The outer homomorphism of a continuous homomorphism. -/
def OuterHom.mk (f : G₁ →ₜ* G₂) : OuterHom G₁ G₂ := Quotient.mk (conjSetoid G₁ G₂) f

lemma OuterHom.mk_eq_mk {f g : G₁ →ₜ* G₂} : OuterHom.mk f = OuterHom.mk g ↔ ConjRel f g :=
  Quotient.eq

lemma OuterHom.mk_surjective : Function.Surjective (OuterHom.mk : (G₁ →ₜ* G₂) → _) :=
  Quotient.mk_surjective

/-- Conjugation is compatible with composition. -/
lemma ConjRel.comp {f f' : G₁ →ₜ* G₂} {g g' : G₂ →ₜ* G₃} (hg : ConjRel g g')
    (hf : ConjRel f f') : ConjRel (g.comp f) (g'.comp f') := by
  obtain ⟨γ, hγ⟩ := hf
  obtain ⟨δ, hδ⟩ := hg
  refine ⟨δ * g γ, fun x => ?_⟩
  simp only [ContinuousMonoidHom.comp_toFun, hγ, hδ, map_mul, map_inv]
  group

/-- **Composition of outer homomorphisms.** -/
def OuterHom.comp (g : OuterHom G₂ G₃) (f : OuterHom G₁ G₂) : OuterHom G₁ G₃ :=
  Quotient.map₂ (fun g f => g.comp f) (fun _ _ hg _ _ hf => ConjRel.comp hg hf) g f

@[simp] lemma OuterHom.comp_mk (g : G₂ →ₜ* G₃) (f : G₁ →ₜ* G₂) :
    (OuterHom.mk g).comp (OuterHom.mk f) = OuterHom.mk (g.comp f) := rfl

variable (G₁) in
/-- The identity outer homomorphism. -/
def OuterHom.id : OuterHom G₁ G₁ := OuterHom.mk (ContinuousMonoidHom.id G₁)

lemma OuterHom.comp_id (f : OuterHom G₁ G₂) : f.comp (OuterHom.id G₁) = f := by
  obtain ⟨f, rfl⟩ := OuterHom.mk_surjective f
  rfl

lemma OuterHom.id_comp (f : OuterHom G₁ G₂) : (OuterHom.id G₂).comp f = f := by
  obtain ⟨f, rfl⟩ := OuterHom.mk_surjective f
  rfl

lemma OuterHom.comp_assoc {G₄ : Type*} [Group G₄] [TopologicalSpace G₄] (h : OuterHom G₃ G₄)
    (g : OuterHom G₂ G₃) (f : OuterHom G₁ G₂) : (h.comp g).comp f = h.comp (g.comp f) := by
  obtain ⟨f, rfl⟩ := OuterHom.mk_surjective f
  obtain ⟨g, rfl⟩ := OuterHom.mk_surjective g
  obtain ⟨h, rfl⟩ := OuterHom.mk_surjective h
  rfl

/-- The outer isomorphism of an isomorphism of topological groups. -/
def OuterHom.ofIso (σ : G₁ ≃ₜ* G₂) : OuterHom G₁ G₂ :=
  OuterHom.mk (ContinuousMonoidHom.toContinuousMonoidHom σ)

end Outer

/-! ### Functors `B(G₁)⁰ ⥤ B(G₂)⁰` of homomorphisms -/

section MapFunctor

variable {G₁ : Type u₁} {G₂ : Type u₂} {G₃ : Type u₃} [Group G₁] [TopologicalSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [Group G₃] [TopologicalSpace G₃]

/-- Pointwise equal homomorphisms induce isomorphic functors. -/
def mapFunctorCongr (p p' : G₁ →* G₂)
    (hp : ∀ U : Subgroup G₁, IsOpen (U : Set G₁) → IsOpen (U.map p : Set G₂))
    (hp' : ∀ U : Subgroup G₁, IsOpen (U : Set G₁) → IsOpen (U.map p' : Set G₂))
    (h : ∀ x, p' x = p x) : OrbitObj.mapFunctor p' hp' ≅ OrbitObj.mapFunctor p hp :=
  OrbitObj.mapFunctorConjIso p p' hp hp' 1 fun x => by rw [h]; group

omit [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace G₃] in
lemma OrbitObj.map_comp_le (p : G₁ →* G₂) (q : G₂ →* G₃) (H : Subgroup G₁) {a : G₃} :
    a ∈ H.map (q.comp p) ↔ a ∈ (H.map p).map q := by
  rw [← Subgroup.map_map]

/-- **`B(G₁)⁰ ⥤ B(G₃)⁰` of a composite** `q ∘ p` is the composite of the functors. -/
def mapFunctorComp (p : G₁ →* G₂) (q : G₂ →* G₃)
    (hp : ∀ U : Subgroup G₁, IsOpen (U : Set G₁) → IsOpen (U.map p : Set G₂))
    (hq : ∀ U : Subgroup G₂, IsOpen (U : Set G₂) → IsOpen (U.map q : Set G₃))
    (hqp : ∀ U : Subgroup G₁, IsOpen (U : Set G₁) → IsOpen (U.map (q.comp p) : Set G₃)) :
    OrbitObj.mapFunctor (q.comp p) hqp ≅ OrbitObj.mapFunctor p hp ⋙ OrbitObj.mapFunctor q hq :=
  NatIso.ofComponents
    (fun A => OrbitObj.isoOfConj _ _ 1
      (fun a ha => by
        rw [inv_one, one_mul, mul_one]
        exact (OrbitObj.map_comp_le p q A.H).1 ha)
      (fun b hb => by
        rw [inv_one, one_mul, mul_one]
        exact (OrbitObj.map_comp_le p q A.H).2 hb))
    (fun {A B} f => by
      refine OrbitHom.ext_of_mk_one ?_
      obtain ⟨b, hb, he⟩ := OrbitHom.rep_map p hp f
      change (QuotientGroup.mk (1 * (q.comp p) (OrbitHom.rep f) * 1) : G₃ ⧸ _) =
        QuotientGroup.mk (1 * 1 * q (OrbitHom.rep (OrbitHom.map p hp f)))
      rw [he]
      refine QuotientGroup.eq.2 ?_
      have e : (1 * (q.comp p) (OrbitHom.rep f) * 1)⁻¹ *
          (1 * 1 * q (p (OrbitHom.rep f) * b)) = q b := by
        simp only [one_mul, mul_one, MonoidHom.comp_apply, map_mul, inv_mul_cancel_left]
      rw [e]
      exact Subgroup.mem_map_of_mem q hb)

/-- The identity homomorphism induces a functor isomorphic to the identity. -/
def mapFunctorId (hp : ∀ U : Subgroup G₁, IsOpen (U : Set G₁) →
    IsOpen (U.map (MonoidHom.id G₁) : Set G₁)) :
    OrbitObj.mapFunctor (MonoidHom.id G₁) hp ≅ 𝟭 (OrbitObj G₁) :=
  NatIso.ofComponents
    (fun A => OrbitObj.isoOfConj _ _ 1
      (fun a ha => by
        rw [inv_one, one_mul, mul_one]
        change a ∈ A.H.map (MonoidHom.id G₁) at ha
        rwa [Subgroup.map_id] at ha)
      (fun b hb => by
        rw [inv_one, one_mul, mul_one]
        change b ∈ A.H.map (MonoidHom.id G₁)
        rwa [Subgroup.map_id]))
    (fun {A B} f => by
      refine OrbitHom.ext_of_mk_one ?_
      change (QuotientGroup.mk (1 * OrbitHom.rep f * 1) : G₁ ⧸ B.H) =
        f.toFun (QuotientGroup.mk (1 * 1))
      rw [one_mul, mul_one, mul_one, OrbitHom.mk_rep])

/-- `isoFunctor (σ.trans τ) ≅ isoFunctor σ ⋙ isoFunctor τ`. -/
def isoFunctorTrans (σ : G₁ ≃ₜ* G₂) (τ : G₂ ≃ₜ* G₃) :
    OrbitObj.isoFunctor (σ.trans τ) ≅ OrbitObj.isoFunctor σ ⋙ OrbitObj.isoFunctor τ :=
  mapFunctorCongr ((τ : G₂ →* G₃).comp (σ : G₁ →* G₂)) _
    (fun U hU => by
      rw [← Subgroup.map_map]
      exact isOpen_map_of_continuousMulEquiv τ _ (isOpen_map_of_continuousMulEquiv σ U hU))
    _ (fun _ => rfl) ≪≫
  mapFunctorComp _ _ _ _ _

/-- `isoFunctor (refl) ≅ 𝟭`. -/
def isoFunctorRefl : OrbitObj.isoFunctor (ContinuousMulEquiv.refl G₁) ≅ 𝟭 (OrbitObj G₁) :=
  mapFunctorCongr (MonoidHom.id G₁) _ (fun U hU => by rwa [Subgroup.map_id]) _ (fun _ => rfl) ≪≫
    mapFunctorId _

/-- `isoFunctor σ ⋙ isoFunctor σ⁻¹ ≅ 𝟭`. -/
def isoFunctorSymmComp (σ : G₁ ≃ₜ* G₂) :
    OrbitObj.isoFunctor σ ⋙ OrbitObj.isoFunctor σ.symm ≅ 𝟭 (OrbitObj G₁) :=
  (OrbitObj.isoUnit σ).symm

/-- Pointwise equal isomorphisms induce isomorphic functors. -/
def isoFunctorCongr {σ τ : G₁ ≃ₜ* G₂} (h : ∀ x, τ x = σ x) :
    OrbitObj.isoFunctor τ ≅ OrbitObj.isoFunctor σ :=
  mapFunctorCongr _ _ _ _ h

end MapFunctor

/-! ### Rigidity: isomorphic functors come from conjugate isomorphisms -/

section Rigid

variable {G₁ : Type u₁} {G₂ : Type u₂} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

omit [IsTopologicalGroup G₂] in
/-- A compact group is complete for its open normal subgroups. -/
lemma isONSComplete_of_compact [CompactSpace G₂] : IsONSComplete G₂ := by
  intro S hS hdir hcl _
  haveI : Nonempty S := hS.to_subtype
  exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
    (fun s hs => (hcl s hs).1) (fun s hs => (hcl s hs).2.isCompact) (fun s hs => (hcl s hs).2)

/-- The image of an open normal subgroup under an isomorphism. -/
def onsMap (τ : G₁ ≃ₜ* G₂) (N : OpenNormalSubgroup G₁) : OpenNormalSubgroup G₂ where
  toSubgroup := N.toSubgroup.map (τ : G₁ →* G₂)
  isOpen' := isOpen_map_of_continuousMulEquiv τ _ N.isOpen
  isNormal' := Subgroup.Normal.map N.isNormal' _ τ.surjective

/-- The preimage of an open normal subgroup under an isomorphism. -/
def onsComap (τ : G₁ ≃ₜ* G₂) (N : OpenNormalSubgroup G₂) : OpenNormalSubgroup G₁ :=
  onsMap τ.symm N

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma onsMap_onsComap (τ : G₁ ≃ₜ* G₂) (N : OpenNormalSubgroup G₂) {a : G₂} :
    a ∈ (onsMap τ (onsComap τ N)).toSubgroup ↔ a ∈ N.toSubgroup := by
  change a ∈ (N.toSubgroup.map (τ.symm : G₂ →* G₁)).map (τ : G₁ →* G₂) ↔ _
  exact OrbitObj.mem_map_map_symm τ.symm N.toSubgroup

section Data

variable (σ τ : G₁ ≃ₜ* G₂) (η : OrbitObj.isoFunctor σ ≅ OrbitObj.isoFunctor τ)

/-- The coset `η(σ(N)) = c_N τ(N)`, by a representative. -/
def rigidRep (N : OpenNormalSubgroup G₁) : G₂ :=
  OrbitHom.rep (η.hom.app (OrbitObj.ofONS N))

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma rigid_app_mk (N : OpenNormalSubgroup G₁) (g : G₂) :
    (η.hom.app (OrbitObj.ofONS N)).toFun (QuotientGroup.mk g) =
      QuotientGroup.mk (g * rigidRep σ τ η N) :=
  OrbitHom.apply_mk_of_eq _ (OrbitHom.mk_rep _).symm g

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma rigid_mem_of_mem (N : OpenNormalSubgroup G₁) {n : G₁} (hn : n ∈ N.toSubgroup) :
    (rigidRep σ τ η N)⁻¹ * (σ n * rigidRep σ τ η N) ∈ N.toSubgroup.map (τ : G₁ →* G₂) := by
  have h1 : (QuotientGroup.mk (σ n) :
      G₂ ⧸ ((OrbitObj.isoFunctor σ).obj (OrbitObj.ofONS N)).H) =
      QuotientGroup.mk 1 :=
    QuotientGroup.eq.2 (by
      rw [mul_one]
      exact (N.toSubgroup.map (σ : G₁ →* G₂)).inv_mem (Subgroup.mem_map_of_mem (σ : G₁ →* G₂) hn))
  have h2 := congrArg (η.hom.app (OrbitObj.ofONS N)).toFun h1
  rw [rigid_app_mk, rigid_app_mk, one_mul] at h2
  exact QuotientGroup.eq.1 h2.symm

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma rigid_rmul (N : OpenNormalSubgroup G₁) (g : G₁) :
    (rigidRep σ τ η N * τ g)⁻¹ * (σ g * rigidRep σ τ η N) ∈
      N.toSubgroup.map (τ : G₁ →* G₂) := by
  set c := rigidRep σ τ η N
  have hnat := congrArg (fun φ => OrbitHom.toFun φ (QuotientGroup.mk 1))
    (η.hom.naturality (OrbitObj.rmul N g))
  simp only [OrbitHom.comp_toFun, Function.comp_apply] at hnat
  have hr : (QuotientGroup.mk (OrbitHom.rep (OrbitObj.rmul N g)) : G₁ ⧸ N.toSubgroup) =
      QuotientGroup.mk g := by
    rw [OrbitHom.mk_rep, OrbitObj.rmul_mk, one_mul]
  obtain ⟨n, hn, hgn⟩ : ∃ n ∈ N.toSubgroup, OrbitHom.rep (OrbitObj.rmul N g) = g * n :=
    ⟨g⁻¹ * OrbitHom.rep (OrbitObj.rmul N g), QuotientGroup.eq.1 hr.symm, by group⟩
  change (η.hom.app _).toFun ((OrbitHom.map (σ : G₁ →* G₂) _ (OrbitObj.rmul N g)).toFun
      (QuotientGroup.mk 1)) = (OrbitHom.map (τ : G₁ →* G₂) _ (OrbitObj.rmul N g)).toFun
      ((η.hom.app _).toFun (QuotientGroup.mk 1)) at hnat
  erw [OrbitHom.map_mk, rigid_app_mk, rigid_app_mk, OrbitHom.map_mk] at hnat
  rw [one_mul, one_mul, hgn] at hnat
  have h3 := QuotientGroup.eq.1 hnat.symm
  have hn' := rigid_mem_of_mem σ τ η N hn
  have hτn : τ n ∈ N.toSubgroup.map (τ : G₁ →* G₂) := Subgroup.mem_map_of_mem _ hn
  -- `(c τ(g) τ(n))⁻¹ σ(g) σ(n) c ∈ τ(N)`, `c⁻¹ σ(n) c ∈ τ(N)`
  have e : (c * τ g)⁻¹ * (σ g * c) =
      τ n * ((c * τ (g * n))⁻¹ * (σ (g * n) * c)) * (c⁻¹ * (σ n * c))⁻¹ := by
    simp only [map_mul]
    group
  rw [e]
  have h3' : (c * τ (g * n))⁻¹ * (σ (g * n) * c) ∈ N.toSubgroup.map (τ : G₁ →* G₂) := h3
  exact mul_mem (mul_mem hτn h3') (inv_mem hn')

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
lemma rigid_proj {N M : OpenNormalSubgroup G₁} (h : N ≤ M) :
    (rigidRep σ τ η M)⁻¹ * rigidRep σ τ η N ∈ M.toSubgroup.map (τ : G₁ →* G₂) := by
  have hnat := congrArg (fun φ => OrbitHom.toFun φ (QuotientGroup.mk 1))
    (η.hom.naturality (OrbitObj.proj (OrbitObj.ofONS M) (fun _ hx => h hx)))
  simp only [OrbitHom.comp_toFun, Function.comp_apply] at hnat
  set r := OrbitHom.rep (OrbitObj.proj (N := N) (OrbitObj.ofONS M) (fun _ hx => h hx))
  have hr : r ∈ M.toSubgroup := by
    have := OrbitHom.mk_rep (OrbitObj.proj (N := N) (OrbitObj.ofONS M) (fun _ hx => h hx))
    rw [OrbitObj.proj_mk] at this
    exact mk_eq_one_iff.mp this
  change (η.hom.app _).toFun ((OrbitHom.map (σ : G₁ →* G₂) _ _).toFun
      (QuotientGroup.mk 1)) = (OrbitHom.map (τ : G₁ →* G₂) _ _).toFun
      ((η.hom.app (OrbitObj.ofONS N)).toFun (QuotientGroup.mk 1)) at hnat
  erw [OrbitHom.map_mk, rigid_app_mk, rigid_app_mk, OrbitHom.map_mk] at hnat
  rw [one_mul, one_mul] at hnat
  have h3 := QuotientGroup.eq.1 hnat
  have h4 := rigid_mem_of_mem σ τ η M hr
  have hτr : τ r ∈ M.toSubgroup.map (τ : G₁ →* G₂) := Subgroup.mem_map_of_mem _ hr
  have h3' : (σ r * rigidRep σ τ η M)⁻¹ * (rigidRep σ τ η N * τ r) ∈
      M.toSubgroup.map (τ : G₁ →* G₂) := h3
  have e : (rigidRep σ τ η M)⁻¹ * rigidRep σ τ η N =
      ((rigidRep σ τ η M)⁻¹ * (σ r * rigidRep σ τ η M)) *
        ((σ r * rigidRep σ τ η M)⁻¹ * (rigidRep σ τ η N * τ r)) * (τ r)⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem h4 h3') (inv_mem hτr)

end Data

omit [IsTopologicalGroup G₁] in
/-- **Rigidity of the functors `isoFunctor`**: if `isoFunctor σ ≅ isoFunctor τ`, then
`τ = γ σ(−) γ⁻¹` for some `γ ∈ G₂` (for `G₂` Hausdorff, with a basis of open normal subgroups and
complete for them). -/
theorem conj_of_isoFunctor_iso [T2Space G₂] (hb : HasONSBasis G₂) (hc : IsONSComplete G₂)
    (σ τ : G₁ ≃ₜ* G₂) (η : OrbitObj.isoFunctor σ ≅ OrbitObj.isoFunctor τ) :
    ∃ γ : G₂, ∀ x, τ x = γ * σ x * γ⁻¹ := by
  let s : OpenNormalSubgroup G₁ → Set G₂ := fun N =>
    {x | x⁻¹ * rigidRep σ τ η N ∈ N.toSubgroup.map (τ : G₁ →* G₂)}
  have hs_mem : ∀ N, rigidRep σ τ η N ∈ s N := fun N => by
    change (rigidRep σ τ η N)⁻¹ * rigidRep σ τ η N ∈ N.toSubgroup.map (τ : G₁ →* G₂)
    rw [inv_mul_cancel]
    exact one_mem _
  have hs_coset : ∀ N x, x ∈ s N → ∀ y, y ∈ s N → x⁻¹ * y ∈ N.toSubgroup.map (τ : G₁ →* G₂) :=
    fun N x hx y hy => by
      have e : x⁻¹ * y = (x⁻¹ * rigidRep σ τ η N) * (y⁻¹ * rigidRep σ τ η N)⁻¹ := by group
      rw [e]
      exact mul_mem hx (inv_mem hy)
  have hs_closed : ∀ N, IsClosed (s N) := fun N => by
    let U := onsMap τ N
    have hU : IsClosed ((U.toSubgroup : Subgroup G₂) : Set G₂) :=
      Subgroup.isClosed_of_isOpen _ U.isOpen
    have hcont : Continuous fun x : G₂ => x⁻¹ * rigidRep σ τ η N :=
      continuous_inv.mul continuous_const
    exact hU.preimage hcont
  have hs_mono : ∀ {N M : OpenNormalSubgroup G₁}, N ≤ M → s N ⊆ s M := fun {N M} h x hx => by
    change x⁻¹ * rigidRep σ τ η M ∈ M.toSubgroup.map (τ : G₁ →* G₂)
    have hx : x⁻¹ * rigidRep σ τ η N ∈ N.toSubgroup.map (τ : G₁ →* G₂) := hx
    have hp := rigid_proj σ τ η h
    have hx' : x⁻¹ * rigidRep σ τ η N ∈ M.toSubgroup.map (τ : G₁ →* G₂) :=
      Subgroup.map_mono (f := (τ : G₁ →* G₂)) (fun _ hy => h hy) hx
    have e : x⁻¹ * rigidRep σ τ η M =
        (x⁻¹ * rigidRep σ τ η N) * ((rigidRep σ τ η M)⁻¹ * rigidRep σ τ η N)⁻¹ := by group
    rw [e]
    exact mul_mem hx' (inv_mem hp)
  obtain ⟨δ, hδ⟩ : (⋂₀ Set.range s).Nonempty := by
    let N₀ : OpenNormalSubgroup G₁ :=
      { toSubgroup := ⊤, isOpen' := isOpen_univ, isNormal' := inferInstance }
    refine hc _ ⟨s N₀, ⟨N₀, rfl⟩⟩ ?_ ?_ ?_
    · rintro _ ⟨N, rfl⟩ _ ⟨M, rfl⟩
      exact ⟨s (N ⊓ M), ⟨N ⊓ M, rfl⟩, hs_mono inf_le_left, hs_mono inf_le_right⟩
    · rintro _ ⟨N, rfl⟩
      exact ⟨⟨_, hs_mem N⟩, hs_closed N⟩
    · intro N'
      refine ⟨s (onsComap τ N'), ⟨_, rfl⟩, fun x hx y hy => ?_⟩
      exact (onsMap_onsComap τ N').1 (hs_coset _ x hx y hy)
  have hδN : ∀ N, δ ∈ s N := fun N => hδ _ ⟨N, rfl⟩
  refine ⟨δ⁻¹, fun g => ?_⟩
  -- `(δ τ(g))⁻¹ σ(g) δ` lies in every `τ(N)`.
  have hall : ∀ N : OpenNormalSubgroup G₁,
      (δ * τ g)⁻¹ * (σ g * δ) ∈ N.toSubgroup.map (τ : G₁ →* G₂) := fun N => by
    set c := rigidRep σ τ η N
    have h1 := rigid_rmul σ τ η N g
    have h2 : δ⁻¹ * c ∈ N.toSubgroup.map (τ : G₁ →* G₂) := hδN N
    have hn : (N.toSubgroup.map (τ : G₁ →* G₂)).Normal := (onsMap τ N).isNormal'
    have e : (δ * τ g)⁻¹ * (σ g * δ) =
        ((τ g)⁻¹ * (δ⁻¹ * c) * τ g) * ((c * τ g)⁻¹ * (σ g * c)) * (δ⁻¹ * c)⁻¹ := by group
    rw [e]
    refine mul_mem (mul_mem ?_ h1) (inv_mem h2)
    simpa using hn.conj_mem _ h2 (τ g)⁻¹
  have h1 : (δ * τ g)⁻¹ * (σ g * δ) = 1 := by
    refine eq_one_of_forall_mem_ons hb fun N' => ?_
    exact (onsMap_onsComap τ N').1 (hall (onsComap τ N'))
  have h2 : σ g * δ = δ * τ g := by
    have := congrArg (fun z => δ * τ g * z) h1
    simpa [mul_assoc] using this
  calc τ g = δ⁻¹ * (σ g * δ) := by rw [h2]; group
    _ = δ⁻¹ * σ g * δ⁻¹⁻¹ := by group

end Rigid

/-! ### Equivalences `B(G₁)⁰ ≌ B(G₂)⁰` come from isomorphisms of groups -/

section Recon

/-- **Functorial reconstruction of isomorphisms** ([Mzk2], Proposition 3.2; [SemiAnbd],
Proposition 3.2): every equivalence `B(G₁)⁰ ≌ B(G₂)⁰` is isomorphic to `G₁/H ↦ G₂/σ(H)` for an
isomorphism `σ` of topological groups. -/
def OrbitEquivRecon (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂]
    [TopologicalSpace G₂] : Prop :=
  ∀ e : OrbitObj G₁ ≌ OrbitObj G₂, ∃ σ : G₁ ≃ₜ* G₂, Nonempty (e.functor ≅ OrbitObj.isoFunctor σ)

/-- **[Mzk2], Proposition 3.2 in functorial form** for two profinite groups. -/
theorem orbitEquivRecon_of_profinite {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [CompactSpace G₁] [TotallyDisconnectedSpace G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [CompactSpace G₂]
    [TotallyDisconnectedSpace G₂] [T2Space G₂] : OrbitEquivRecon G₁ G₂ := fun e => by
  have hb : HasONSBasis G₁ := fun _ hU h1 =>
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  obtain ⟨σ, x, -, hpt, hrmul⟩ := OrbitObj.exists_continuousMulEquiv e.functor
  exact ⟨σ, ⟨(OrbitObj.natIsoOfBasePoints e.functor hb σ x hpt hrmul).symm⟩⟩

/-- **[SemiAnbd], Proposition 3.2 in functorial form** for two tempered groups. -/
theorem orbitEquivRecon_of_temp {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [T2Space G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [T2Space G₂] (h₁b : HasONSBasis G₁) (h₁s : HasONSChain G₁) (h₁c : IsONSComplete G₁)
    (h₂b : HasONSBasis G₂) (h₂c : IsONSComplete G₂) : OrbitEquivRecon G₁ G₂ := fun e => by
  obtain ⟨σ, x, -, hpt, hrmul⟩ :=
    OrbitObj.exists_continuousMulEquiv_temp h₁b h₁s h₁c h₂b h₂c e.functor
  exact ⟨σ, ⟨(OrbitObj.natIsoOfBasePoints e.functor h₁b σ x hpt hrmul).symm⟩⟩

/-- `OrbitIsoRecon` (MR21, self-equivalences) is `OrbitEquivRecon G G`. -/
lemma orbitIsoRecon_iff (G : Type) [Group G] [TopologicalSpace G] :
    PrimeStrip.OrbitIsoRecon G ↔ OrbitEquivRecon G G := Iff.rfl

end Recon

end Theater

end Multiradial

end Iut
