/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Cover

/-!
# The étale fundamental groups of the model orbicurves, in every characteristic

`Iut.Anabelian.Genuine.pi1Of E ℓ M ±` is the genuine arithmetic étale fundamental group of the
model orbicurve `(E, ℓ, M, ±)` over any field; that the maps induced by covers are open
embeddings is proved in characteristic `0` (`Iut.Anabelian.Genuine.isOpenEmbedding_pi1MapOf`,
through the étaleness of the covers). IUT evaluates the étale theory only over fields of
characteristic `0` (number fields, their finite extensions and completions). The étale theory
used for the instance of `Iut.Anabelian.EtalePi1Theory` is therefore

* `pi1C E ℓ M ± = pi1Of E ℓ M ±` in characteristic `0` (`pi1EquivC`), and
* **a junk value in positive characteristic**: the trivial group (the inertia generators are
  replaced by all of `Aut(Ω / F_X)`), for which every induced map is trivially an open
  embedding.
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve

open scoped Classical

noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The inertia generators: `Sgen E ℓ M` in characteristic `0`; all of `Gal E` otherwise (a junk
value making the fundamental group trivial). -/
def SgenC (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : Set (Gal E) :=
  if CharZero k then Sgen E ℓ M else Set.univ

lemma SgenC_of_charZero [CharZero k] (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    SgenC E ℓ M = Sgen E ℓ M := by
  unfold SgenC; exact if_pos ‹CharZero k›

lemma SgenC_of_not_charZero (h : ¬ CharZero k) (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    SgenC E ℓ M = Set.univ := by
  unfold SgenC; exact if_neg h

/-- **The étale fundamental group of the model orbicurve `(E, ℓ, M, ±)`** used by the instance:
`pi1Of E ℓ M ±` in characteristic `0`, trivial otherwise. -/
def pi1C (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) : ProfiniteGrp.{u} :=
  GaloisPi1.pi1 (Hgp E ℓ M pm) (SgenC E ℓ M) (isClosed_Hgp E ℓ M pm)

/-- In characteristic `0`, `pi1C` is the genuine étale fundamental group `pi1Of`. -/
def pi1EquivC [CharZero k] (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    pi1Of E ℓ M pm ≃ₜ* pi1C E ℓ M pm := by
  unfold pi1C pi1Of
  rw [SgenC_of_charZero]

omit [E.IsElliptic] in
lemma GaloisPi1_pi1_univ_subsingleton {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω]
    [IsGalois P Ω] (H : Subgroup (Ω ≃ₐ[P] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[P] Ω))) :
    Subsingleton (GaloisPi1.pi1 H Set.univ hH) := by
  have hker : GaloisPi1.kernel H Set.univ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    simp only [GaloisPi1.kernel, Subgroup.mem_subgroupOf]
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ?_)
    exact ⟨1, H.one_mem, h, Set.mem_univ _, by simp⟩
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  change (QuotientGroup.mk x : H ⧸ GaloisPi1.kernel H Set.univ) = QuotientGroup.mk y
  rw [QuotientGroup.eq, hker]
  trivial

lemma pi1C_subsingleton (h : ¬ CharZero k) (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (pm : Bool) : Subsingleton (pi1C E ℓ M pm) := by
  unfold pi1C
  rw [SgenC_of_not_charZero E h]
  exact GaloisPi1_pi1_univ_subsingleton _ _

/-- **The homomorphism of fundamental groups induced by a cover** (the inclusion
`Aut(Ω / F_X) ⊆ Aut(Ω / F_Y)`; trivial in positive characteristic). -/
def pi1MapC {ℓ ℓ' : ℕ} {M M' : AddSubgroup E.toAffine.Point} {pm pm' : Bool} :
    pi1C E ℓ M pm →* pi1C E ℓ' M' pm' :=
  if h : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' ∧ SgenC E ℓ M ⊆ SgenC E ℓ' M' then
    GaloisPi1.pi1Map (isClosed_Hgp E ℓ M pm) (isClosed_Hgp E ℓ' M' pm') h.1 h.2
  else 1

lemma continuous_pi1MapC {ℓ ℓ' : ℕ} {M M' : AddSubgroup E.toAffine.Point} {pm pm' : Bool} :
    Continuous (pi1MapC E (ℓ := ℓ) (ℓ' := ℓ') (M := M) (M' := M') (pm := pm) (pm' := pm')) := by
  unfold pi1MapC
  split_ifs with h
  · exact GaloisPi1.continuous_pi1Map _ _ _ _
  · exact continuous_const

omit [E.IsElliptic] in
lemma isOpenEmbedding_of_subsingleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Subsingleton X] [Subsingleton Y] [Nonempty X] (f : X → Y) (hf : Continuous f) :
    Topology.IsOpenEmbedding f := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf
    (fun a b _ => Subsingleton.elim a b) ?_
  intro U hU
  rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have : f '' U = Set.univ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => ⟨x, hx, Subsingleton.elim _ _⟩⟩
    rw [this]
    exact isOpen_univ

/-- **The maps induced by covers are open embeddings.** -/
theorem isOpenEmbedding_pi1MapC {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) :
    Topology.IsOpenEmbedding
      (pi1MapC E (ℓ := ℓ) (ℓ' := ℓ') (M := M) (M' := M') (pm := pm) (pm' := pm')) := by
  by_cases hk : CharZero k
  · have hc := compatible_divSys_of_charZero E
    have hS : SgenC E ℓ M = S0 E := by rw [SgenC_of_charZero, Sgen_eq_S0]
    have hS' : SgenC E ℓ' M' = S0 E := by rw [SgenC_of_charZero, Sgen_eq_S0]
    have h : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' ∧ SgenC E ℓ M ⊆ SgenC E ℓ' M' :=
      ⟨Hgp_le E hc hn hℓ hM hpm, by rw [hS, hS']⟩
    unfold pi1MapC
    rw [dif_pos h]
    refine GaloisPi1.isOpenEmbedding_pi1Map' _ _ h.1 h.2 (by rw [hS, hS']) (isOpen_Hgp E ℓ M pm) ?_
    intro g hg s hs
    rw [hS] at hs ⊢
    exact conj_mem_S0 E hc hg hs
  · haveI := pi1C_subsingleton E hk ℓ M pm
    haveI := pi1C_subsingleton E hk ℓ' M' pm'
    exact isOpenEmbedding_of_subsingleton _ (continuous_pi1MapC E)

end

end Iut.Anabelian.Genuine
