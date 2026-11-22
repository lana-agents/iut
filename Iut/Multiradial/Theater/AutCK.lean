/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.Semilinear
import Iut.Multiradial.Theater.Capsule
import Iut.HodgeTheater.DStarDescent
import Iut.HodgeTheater.DStarCKu

/-!
# `Aut(C̲_K)`, `Aut_ϵ(C̲_K)` and `Aut(C̲_K)/Aut_ϵ(C̲_K) → F_ℓ^⋇` (MR22 T6)

IUT I, Example 4.3 (i) (l.6545–6600 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): `Aut_ϵ(C̲_K) ⊆ Aut(C̲_K) ≅ Out(Π_{C̲_K}) ≅ Aut(D^⊚)` ("the first `≅` follows, for
instance, from [AbsTopIII], Theorem 1.9"), `Aut_ϵ` the elements fixing the cusp `ϵ`, and
`Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇` via the action on the rank-one quotient of `Δ_X^ab ⊗ F_ℓ`.

Following the lead decision of `MR22-plan.md` (phase 2b, session 1), `Aut(C̲_K)` is the group of
semilinear automorphisms of `C̲_K` over `C_{F_mod}`: **`AutCK D = N(π₁(C̲_K)) / π₁(C̲_K)`**, the
normaliser of the image of `π₁(C̲_K)` in `π₁(C_{F_mod}) = π₁(†D^⊛)` (`iotaCK`, through
`π₁(C̲_K) ↪ π₁(C_K) ↪ π₁(C_{F_mod})`) modulo that image.

* generic (`P ↪ G` an embedding): conjugation by the normaliser (`conjHom`, `conjCont`); for `G`
  slim and `P` open, `N(P)/P ↪ Out(P)` (**`outOf_injective`**);
* **`outCK_injective`**: `Aut(C̲_K) ↪ Out(π₁(C̲_K))` (slimness of `π₁(C_{F_mod})`);
* **`exists_normCK_eq`**, **`outCK_surjective`**: every continuous automorphism of `π₁(C̲_K)` is
  conjugation by an element of the normaliser (MR9's `hAbsCKu_of_strict`, with the named
  literature input `CKuStrictSemiAbs` = [AbsTopI] Cor. 2.8 (ii) for `C̲_K`, and the existing
  inputs `BelyiCuspSpec`, `hDGC`, `hj`);
* **`chiN`**, **`chi`**: `γ ∈ N` acts on `π₁(C_K)` (normal in `π₁(C_{F_mod})`) preserving
  `π₁(C̲_K)`, hence on `π₁(C_K)/π₁(C̲_K) ≅ Q ≅ F_ℓ` (`rhoCK`, the dihedral action of
  `CuspAction.lean`) by a scalar (`AutScalar.lean`); `π₁(C̲_K)` acts by `±1`, so
  `chi : Aut(C̲_K) → F_ℓ^⋇ = F_ℓ^×/{±1}`; **`AutEps D = ker chi`** is `Aut_ϵ(C̲_K)`;
* **`chi_surjective`** (`Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇`): semilinear automorphisms from the Borel
  subgroup of `SL₂(F_ℓ) ⊆ ρ(Gal(F̄/F))` (Def. 3.1 (c), `Semilinear.lean`), named inputs as in
  `exists_normCK_eq`;
* `autPoly`, `autEpsPoly`, `actStar`: the corresponding poly-automorphisms of `D^⊚ = B(C̲_K)⁰`,
  closure under composition (`autPoly_comp_subset`, `actStar_comp_subset`), and the instances
  **`phiNFEps`**, **`phiNFStarEps`** of `Capsule.phiNF`, `Capsule.phiNFStar`.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open CategoryTheory Topology Iut.HodgeTheater Iut.Anabelian Pi1.Profinite CurvesJacobian.Cusp
  Iut.Frobenioid Belyi.Anabelian PrimeStrip
  Iut.Reconstruction Iut.Reconstruction.Thm19

/-! ### Conjugation by the normaliser of an embedded subgroup -/

section Normaliser

variable {P G : Type} [Group P] [TopologicalSpace P] [Group G] [TopologicalSpace G]
  (ι : P →ₜ* G)

/-- The normaliser of the image of `ι`. -/
abbrev normRange : Subgroup G := Subgroup.normalizer (ι.toMonoidHom.range : Set G)

lemma exists_conj (γ : normRange ι) (x : P) : ∃ y, ι y = (γ : G) * ι x * (γ : G)⁻¹ := by
  obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.1 γ.2 (ι x)).1 ⟨x, rfl⟩
  exact ⟨y, hy⟩

/-- Conjugation by `γ ∈ N(ι(P))`, as a map of `P`. -/
def conjFun (γ : normRange ι) (x : P) : P := (exists_conj ι γ x).choose

lemma conjFun_spec (γ : normRange ι) (x : P) : ι (conjFun ι γ x) = (γ : G) * ι x * (γ : G)⁻¹ :=
  (exists_conj ι γ x).choose_spec

variable {ι} (hι : Function.Injective ι)

include hι in
lemma conjFun_mul (γ δ : normRange ι) (x : P) :
    conjFun ι (γ * δ) x = conjFun ι γ (conjFun ι δ x) :=
  hι (by rw [conjFun_spec, conjFun_spec, conjFun_spec, Subgroup.coe_mul]; group)

include hι in
lemma conjFun_one (x : P) : conjFun ι 1 x = x :=
  hι (by rw [conjFun_spec, OneMemClass.coe_one]; group)

/-- **Conjugation `N(ι(P)) → Aut(P)`.** -/
def conjHom : normRange ι →* MulAut P where
  toFun γ :=
    { toFun := conjFun ι γ
      invFun := conjFun ι γ⁻¹
      left_inv := fun x => by rw [← conjFun_mul hι, inv_mul_cancel, conjFun_one hι]
      right_inv := fun x => by rw [← conjFun_mul hι, mul_inv_cancel, conjFun_one hι]
      map_mul' := fun x y => hι (by
        rw [conjFun_spec, map_mul, map_mul, conjFun_spec, conjFun_spec]
        group) }
  map_one' := MulEquiv.ext fun x => conjFun_one hι x
  map_mul' γ δ := MulEquiv.ext fun x => conjFun_mul hι γ δ x

lemma conjHom_spec (γ : normRange ι) (x : P) :
    ι (conjHom hι γ x) = (γ : G) * ι x * (γ : G)⁻¹ :=
  conjFun_spec ι γ x

/-- An element conjugating `ι` into `ι ∘ α` (for an automorphism `α`) normalises `ι(P)`. -/
lemma mem_normRange_of_conj (α : P ≃* P) {γ : G}
    (h : ∀ x, ι (α x) = γ * ι x * γ⁻¹) : γ ∈ normRange ι := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨α x, h x⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := α.surjective y
    exact ⟨x, mul_left_cancel (mul_right_cancel ((h x).symm.trans hy))⟩

lemma conjHom_eq_of_conj (α : P ≃* P) {γ : G} (h : ∀ x, ι (α x) = γ * ι x * γ⁻¹) (x : P) :
    conjHom hι ⟨γ, mem_normRange_of_conj α h⟩ x = α x :=
  hι (by rw [conjHom_spec]; exact (h x).symm)

variable [IsTopologicalGroup G]

lemma continuous_conjHom (he : IsEmbedding ι) (γ : normRange ι) : Continuous (conjHom hι γ) := by
  refine he.continuous_iff.mpr ?_
  have h : (ι ∘ conjHom hι γ) = fun x => (γ : G) * ι x * (γ : G)⁻¹ := funext (conjHom_spec hι γ)
  rw [h]
  exact (continuous_const.mul ι.continuous).mul continuous_const

/-- Conjugation by `γ ∈ N(ι(P))`, as a continuous automorphism. -/
def conjCont (he : IsEmbedding ι) (γ : normRange ι) : P ≃ₜ* P :=
  ⟨conjHom hι γ, continuous_conjHom hι he γ, continuous_conjHom hι he γ⁻¹⟩

lemma conjCont_apply (he : IsEmbedding ι) (γ : normRange ι) (x : P) :
    conjCont hι he γ x = conjHom hι γ x := rfl

variable (ι) in
/-- The subgroup `ι(P) ∩ N(ι(P))` of the normaliser. -/
abbrev rangeIn : Subgroup (normRange ι) := ι.toMonoidHom.range.subgroupOf (normRange ι)

instance : (rangeIn ι).Normal := Subgroup.normal_in_normalizer

variable (he : IsEmbedding ι)

/-- `conjCont γ`, `conjCont δ` are conjugate by an element of `P` iff `γ⁻¹ δ ∈ ι(P)` (`G` slim,
`ι(P)` open). -/
theorem conjRel_conjCont_iff [IsTopologicalGroup P] [CompactSpace P] [T2Space G]
    (hG : IsSlim G) (ho : IsOpen (Set.range ι)) (γ δ : normRange ι) :
    ConjRel (ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he γ))
      (ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he δ)) ↔ γ⁻¹ * δ ∈ rangeIn ι := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : ∀ x, (δ : G) * ι x * (δ : G)⁻¹ = ι u * ((γ : G) * ι x * (γ : G)⁻¹) * (ι u)⁻¹ :=
      fun x => by
        have h0 : conjHom hι δ x = u * conjHom hι γ x * u⁻¹ := hu x
        have := congrArg ι h0
        rw [map_mul, map_mul, map_inv, conjHom_spec, conjHom_spec] at this
        exact this
    have h1 : (ι u * (γ : G))⁻¹ * (δ : G) = 1 :=
      eq_one_of_commute_open₄ hG ι ho (U := ⊤) isOpen_univ fun x _ => by
        have e := hu' x
        calc (ι u * (γ : G))⁻¹ * (δ : G) * ι x
            = (ι u * (γ : G))⁻¹ * ((δ : G) * ι x * (δ : G)⁻¹) * (δ : G) := by group
          _ = (ι u * (γ : G))⁻¹ * (ι u * ((γ : G) * ι x * (γ : G)⁻¹) * (ι u)⁻¹) * (δ : G) := by
              rw [e]
          _ = ι x * ((ι u * (γ : G))⁻¹ * (δ : G)) := by group
    have hδ : (δ : G) = ι u * (γ : G) := by
      calc (δ : G) = (ι u * (γ : G)) * ((ι u * (γ : G))⁻¹ * (δ : G)) := by group
        _ = ι u * (γ : G) := by rw [h1, mul_one]
    rw [Subgroup.mem_subgroupOf]
    have hγ := (Subgroup.mem_normalizer_iff.1 (γ⁻¹).2 (ι u)).1 ⟨u, rfl⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hγ ⊢
    rw [hδ]
    simpa [mul_assoc] using hγ
  · intro h
    rw [Subgroup.mem_subgroupOf] at h
    obtain ⟨u, hu⟩ := h
    have hu' : ι u = (γ : G)⁻¹ * (δ : G) := by simpa using hu
    refine ⟨conjHom hι γ u, fun x => hι ?_⟩
    change ι (conjHom hι δ x) = ι (conjHom hι γ u * conjHom hι γ x * (conjHom hι γ u)⁻¹)
    rw [map_mul, map_mul, map_inv, conjHom_spec, conjHom_spec, conjHom_spec, hu']
    group

/-- **`N(ι(P))/ι(P) → Out(P)`**, the outer automorphism of a class. -/
def outOf [IsTopologicalGroup P] [CompactSpace P] [T2Space G]
    (hG : IsSlim G) (ho : IsOpen (Set.range ι)) :
    normRange ι ⧸ rangeIn ι → OuterHom P P :=
  Quotient.lift (s := QuotientGroup.leftRel (rangeIn ι))
    (fun γ => OuterHom.mk (ContinuousMonoidHom.toContinuousMonoidHom
    (conjCont hι he γ))) fun γ δ h =>
      OuterHom.mk_eq_mk.2 ((conjRel_conjCont_iff hι he hG ho γ δ).2
        (QuotientGroup.leftRel_apply.1 h))

lemma outOf_mk [IsTopologicalGroup P] [CompactSpace P] [T2Space G]
    (hG : IsSlim G) (ho : IsOpen (Set.range ι)) (γ : normRange ι) :
    outOf hι he hG ho (QuotientGroup.mk γ) =
      OuterHom.mk (ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he γ)) := rfl

/-- **`N(ι(P))/ι(P) ↪ Out(P)`** for `G` slim and `ι(P)` open. -/
theorem outOf_injective [IsTopologicalGroup P] [CompactSpace P] [T2Space G]
    (hG : IsSlim G) (ho : IsOpen (Set.range ι)) :
    Function.Injective (outOf hι he hG ho) := by
  intro a b hab
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective b
  rw [outOf_mk, outOf_mk, OuterHom.mk_eq_mk, conjRel_conjCont_iff hι he hG ho] at hab
  exact QuotientGroup.eq.2 hab

/-! #### Poly-automorphisms of `B(P)⁰` from subsets of `N(ι(P))/ι(P)` -/

/-- The automorphism of `B(P)⁰` given by `γ ∈ N(ι(P))` (conjugation, presented with the identity
equivalences). -/
def autMorN (γ : normRange ι) : GalMor (OrbitObj P) (OrbitObj P) P P :=
  GalMor.mk ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl,
    ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he γ)⟩

/-- The poly-automorphism of `B(P)⁰` given by a set `S ⊆ N(ι(P))/ι(P)`. -/
def autPolyN (S : Set (normRange ι ⧸ rangeIn ι)) : PolyMor (OrbitObj P) (OrbitObj P) P P :=
  {m | ∃ γ : normRange ι, (QuotientGroup.mk γ : normRange ι ⧸ rangeIn ι) ∈ S ∧
    autMorN hι he γ = m}

lemma isComp_autMorN (γ δ : normRange ι) :
    IsComp (autMorN hι he γ) (autMorN hι he δ) (autMorN hι he (δ * γ)) := by
  have h := isComp_mk (⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl,
    ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he γ)⟩ :
      GalTriple (OrbitObj P) (OrbitObj P) P P)
    ⟨CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.refl,
      ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he δ)⟩ ⟨Iso.refl _⟩
  have e : ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he (δ * γ)) =
      (ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he δ)).comp
        (ContinuousMonoidHom.toContinuousMonoidHom (conjCont hι he γ)) := by
    ext x
    change conjHom hι (δ * γ) x = conjHom hι δ (conjHom hι γ x)
    rw [map_mul]
    rfl
  have e' : autMorN hι he (δ * γ) = GalMor.mk ⟨CategoryTheory.Equivalence.refl,
      CategoryTheory.Equivalence.refl, (ContinuousMonoidHom.toContinuousMonoidHom
        (conjCont hι he δ)).comp (ContinuousMonoidHom.toContinuousMonoidHom
          (conjCont hι he γ))⟩ := by
    unfold autMorN
    rw [e]
  rw [e']
  exact h

variable [IsTopologicalGroup P] [T2Space P] (hb : HasONSBasis P) (hc : IsONSComplete P)

include hb hc in
/-- **`S ∘ S ⊆ S`** for a subgroup `S`. -/
theorem autPolyN_comp_subset (S : Subgroup (normRange ι ⧸ rangeIn ι)) :
    (autPolyN hι he S).comp (autPolyN hι he S) ⊆ autPolyN hι he S := by
  rintro c ⟨a, ⟨γ, hγ, rfl⟩, b, ⟨δ, hδ, rfl⟩, hcomp⟩
  refine ⟨δ * γ, ?_, isComp_unique hb hc (isComp_autMorN hι he γ δ) hcomp⟩
  rw [QuotientGroup.mk_mul]
  exact S.mul_mem hδ hγ

variable {H : Type*} [CommGroup H] (f : normRange ι ⧸ rangeIn ι →* H)

include hb hc in
theorem autPolyN_fiber_comp_subset (j j' : H) :
    (autPolyN hι he (f ⁻¹' {j})).comp (autPolyN hι he (f ⁻¹' {j'})) ⊆
      autPolyN hι he (f ⁻¹' {j * j'}) := by
  rintro c ⟨a, ⟨γ, hγ, rfl⟩, b, ⟨δ, hδ, rfl⟩, hcomp⟩
  refine ⟨δ * γ, ?_, isComp_unique hb hc (isComp_autMorN hι he γ δ) hcomp⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hγ hδ ⊢
  rw [QuotientGroup.mk_mul, map_mul, hγ, hδ, mul_comm]

include hb hc in
/-- The fibres of a surjective homomorphism compose: `S_j ∘ S_{j'} = S_{j j'}`. -/
theorem autPolyN_fiber_comp (hs : Function.Surjective f) (j j' : H) :
    (autPolyN hι he (f ⁻¹' {j})).comp (autPolyN hι he (f ⁻¹' {j'})) =
      autPolyN hι he (f ⁻¹' {j * j'}) := by
  refine subset_antisymm (autPolyN_fiber_comp_subset hι he hb hc f j j') ?_
  rintro m ⟨ε, hε, rfl⟩
  obtain ⟨a, ha⟩ := hs j
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨autMorN hι he γ, ⟨γ, ha, rfl⟩, autMorN hι he (ε * γ⁻¹), ⟨ε * γ⁻¹, ?_, rfl⟩, ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hε ha ⊢
    rw [QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_inv, map_inv, hε, ha, mul_comm j j',
      mul_inv_cancel_right]
  · have h := isComp_autMorN hι he γ (ε * γ⁻¹)
    rwa [inv_mul_cancel_right] at h

end Normaliser

/-! ### `Aut(C̲_K)` -/

section AutCK

variable (D : InitialThetaData.{0})

/-- The prime `ℓ` of initial Θ-data is an odd prime. -/
local instance oddPrimeEllAut : HodgeTheater.OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

/-- **`π₁(C̲_K) ↪ π₁(C_K) ↪ π₁(C_{F_mod})`.** -/
def iotaCK : PiCK D →ₜ* piCmod D := (piCKToCmod D).comp (piCKuToCK D)

lemma isOpenEmbedding_iotaCK : IsOpenEmbedding (iotaCK D) := by
  have e : ⇑(iotaCK D) = piCKToCmod D ∘ piCKuToCK D := rfl
  rw [e]
  exact (isOpenEmbedding_piCKToCmod D).comp D.orb.pi1CKu_to_CK_isOpenEmbedding

/-- The normaliser `N(π₁(C̲_K))` in `π₁(C_{F_mod})`. -/
abbrev normCK : Subgroup (piCmod D) := normRange (iotaCK D)

/-- **`Aut(C̲_K) = N(π₁(C̲_K)) / π₁(C̲_K)`** (IUT I, Example 4.3 (i); semilinear automorphisms of
`C̲_K` over `C_{F_mod}`). -/
abbrev AutCK : Type := normCK D ⧸ rangeIn (iotaCK D)

/-- Conjugation `N(π₁(C̲_K)) → Aut(π₁(C̲_K))`. -/
def conjCK : normCK D →* MulAut (PiCK D) := conjHom (isOpenEmbedding_iotaCK D).injective

lemma iotaCK_conjCK (γ : normCK D) (x : PiCK D) :
    iotaCK D (conjCK D γ x) = (γ : piCmod D) * iotaCK D x * (γ : piCmod D)⁻¹ :=
  conjHom_spec _ γ x

/-- **`Aut(C̲_K) → Out(π₁(C̲_K))`.** -/
def outCK : AutCK D → OuterHom (PiCK D) (PiCK D) :=
  outOf (isOpenEmbedding_iotaCK D).injective (isOpenEmbedding_iotaCK D).isEmbedding
    (isSlim_piCmod D) (isOpenEmbedding_iotaCK D).isOpen_range

/-- **`Aut(C̲_K) ↪ Out(π₁(C̲_K))`** (`π₁(C_{F_mod})` is slim, `isSlim_piCmod`). -/
theorem outCK_injective : Function.Injective (outCK D) :=
  outOf_injective _ _ _ _

/-- **Every continuous automorphism of `π₁(C̲_K)` is conjugation by an element of
`N(π₁(C̲_K))`** (`piCmod_selfComm`; the action on the Galois image is conjugation by
`hAbsCKu_of_strict` of `DStarCKu.lean`, with the named literature input `CKuStrictSemiAbs`). -/
theorem exists_normCK_eq (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (α : PiCK D ≃ₜ* PiCK D) : ∃ γ : normCK D, ∀ x, conjCK D γ x = α x := by
  have hι := isOpenEmbedding_iotaCK D
  obtain ⟨g, hg⟩ := hAbsCKu_of_strict D hStrict hS hDGC hj α
  let f₂ : PiCK D →ₜ* piCmod D :=
    (iotaCK D).comp (ContinuousMonoidHom.toContinuousMonoidHom α)
  have hf₂ : ∀ x, f₂ x = iotaCK D (α x) := fun _ => rfl
  have hi₂ : Function.Injective f₂ := fun a b h =>
    α.injective (hι.injective (by rwa [hf₂, hf₂] at h))
  have ho₂ : IsOpen (Set.range f₂) := by
    have e : Set.range f₂ = Set.range (iotaCK D) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨α x, (hf₂ x).symm⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨z, rfl⟩ := α.surjective x
        exact ⟨z, hf₂ z⟩
    rw [e]
    exact hι.isOpen_range
  have hg' : ∀ x, piCmodPr D (f₂ x) = g * piCmodPr D (iotaCK D x) * g⁻¹ := fun x => by
    rw [hf₂]
    exact hg x
  obtain ⟨γ, hγ⟩ := piCmod_selfComm D hDGC hj (PiCK D) (iotaCK D) f₂ hι.injective
    hι.isOpen_range hi₂ ho₂ g hg'
  have hγ' : ∀ x, iotaCK D (α.toMulEquiv x) = γ * iotaCK D x * γ⁻¹ := fun x => by
    rw [← hγ x]
    rfl
  exact ⟨⟨γ, mem_normRange_of_conj α.toMulEquiv hγ'⟩,
    conjHom_eq_of_conj (isOpenEmbedding_iotaCK D).injective α.toMulEquiv hγ'⟩

/-- **`Aut(C̲_K) → Out(π₁(C̲_K))` hits every outer automorphism** (named inputs as in
`hAbsCKu_of_strict`), so `Aut(C̲_K) ≅ Out(π₁(C̲_K))` (IUT I, Example 4.3 (i)). -/
theorem outCK_surjective (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (α : PiCK D ≃ₜ* PiCK D) :
    ∃ a : AutCK D, outCK D a = OuterHom.mk (ContinuousMonoidHom.toContinuousMonoidHom α) := by
  obtain ⟨γ, hγ⟩ := exists_normCK_eq D hStrict hS hDGC hj α
  refine ⟨QuotientGroup.mk γ, ?_⟩
  change OuterHom.mk _ = _
  congr 1
  ext x
  exact hγ x

/-! ### The character `χ : Aut(C̲_K) → F_ℓ^⋇` -/

lemma CK_level : (OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime).level = 1 := by
  rw [CK_eq]; rfl

lemma CK_M : (OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime).M = ⊥ := by
  rw [CK_eq]; rfl

lemma CK_pm : (OrbicurveDataSection.CK D.F D.E D.Fbar D.VBad D.prime).pm = true := by
  rw [CK_eq]; rfl

lemma exists_rhoCK : ∃ ρ : piCK D →* Equiv.Perm (ZMod D.ℓ),
    IsDihedralQuot ρ (piCKuToCK D).toMonoidHom.range ∧ IsDihedralFull ρ ∧
      ∀ y, y ∈ ((piCKuToCK D).comp (piXKToCK D)).toMonoidHom.range ↔ ρ y = 1 :=
  exists_rho_of_covers D.orb.XKu_to_CKu D.orb.CKu_to_CK D.orb.XKu_type D.orb.CKu_type
    (CK_level D) (CK_M D) (CK_pm D) D.orb.QIso

/-- **The action of `π₁(C_K)` on `π₁(C_K)/π₁(C̲_K) ≅ Q ≅ F_ℓ`** (the cusps of `X̲_K`; dihedral,
`CuspAction.lean`, via the chosen `QIso : Q ≅ F_ℓ`), with kernel `π₁(X̲_K)`. -/
def rhoCK : piCK D →* Equiv.Perm (ZMod D.ℓ) := (exists_rhoCK D).choose

lemma isDihedralQuot_rhoCK : IsDihedralQuot (rhoCK D) (piCKuToCK D).toMonoidHom.range :=
  (exists_rhoCK D).choose_spec.1

lemma isDihedralFull_rhoCK : IsDihedralFull (rhoCK D) :=
  (exists_rhoCK D).choose_spec.2.1

lemma mem_range_XK_iff (y : piCK D) :
    y ∈ ((piCKuToCK D).comp (piXKToCK D)).toMonoidHom.range ↔ rhoCK D y = 1 :=
  (exists_rhoCK D).choose_spec.2.2 y

/-- An element of `π₁(C_{F_mod})` normalising the image of `f : P → π₁(C_K)` acts on `π₁(C_K)`
preserving `f(P)`. -/
lemma mem_stabAut_of_norm {P : Type} [Group P] (f : P →* piCK D) (γ : piCmod D)
    (hγ : γ ∈ Subgroup.normalizer (((piCKToCmod D).toMonoidHom.comp f).range : Set (piCmod D))) :
    ((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) ∈ stabAut f.range := fun x => by
  have hK := (isOpenEmbedding_piCKToCmod D).injective
  have hspec := piCKToCmod_piCmodToAut D γ x
  constructor
  · rintro ⟨u, hu⟩
    have hmem : piCKToCmod D (f u) ∈ ((piCKToCmod D).toMonoidHom.comp f).range := ⟨u, rfl⟩
    obtain ⟨u', hu'⟩ := (Subgroup.mem_normalizer_iff.1 (inv_mem hγ) _).1 hmem
    refine ⟨u', hK ?_⟩
    have e1 : piCKToCmod D (f u) = γ * piCKToCmod D x * γ⁻¹ := by rw [hu, hspec]
    change piCKToCmod D (f u') = _
    change piCKToCmod D (f u') = _ at hu'
    rw [hu', e1]
    group
  · rintro ⟨u, hu⟩
    have hmem : piCKToCmod D (f u) ∈ ((piCKToCmod D).toMonoidHom.comp f).range := ⟨u, rfl⟩
    obtain ⟨u', hu'⟩ := (Subgroup.mem_normalizer_iff.1 hγ _).1 hmem
    refine ⟨u', hK ?_⟩
    change piCKToCmod D (f u') = _ at hu'
    rw [hu', hspec, ← hu]

/-- `γ ∈ N(π₁(C̲_K))` acts on `π₁(C_K)` preserving `π₁(C̲_K)`. -/
lemma piCmodToAut_mem_stabAut (γ : normCK D) :
    ((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) ∈
      stabAut (piCKuToCK D).toMonoidHom.range :=
  mem_stabAut_of_norm D (piCKuToCK D).toMonoidHom γ γ.2

/-- `N(π₁(C̲_K)) → Aut(π₁(C_K), π₁(C̲_K))`. -/
def normToStab : normCK D →* stabAut (piCKuToCK D).toMonoidHom.range :=
  (((contAut (piCK D)).subtype.comp ((piCmodToAut D).comp (normCK D).subtype))).codRestrict _
    (piCmodToAut_mem_stabAut D)

/-- **`χ` on the normaliser**: `γ ∈ N(π₁(C̲_K))` acts on `π₁(C_K)/π₁(C̲_K) ≅ F_ℓ` by the scalar
`chiN γ` (`chiN_spec`). -/
def chiN : normCK D →* (ZMod D.ℓ)ˣ := (scalHom (isDihedralQuot_rhoCK D)).comp (normToStab D)

lemma chiN_spec (γ : normCK D) (x : piCK D) :
    rhoCK D (((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) x) 0 =
      chiN D γ * rhoCK D x 0 :=
  scalHom_spec (isDihedralQuot_rhoCK D) (normToStab D γ) x

/-- `π₁(C̲_K)` acts on `π₁(C_K)` by inner automorphisms of `π₁(C̲_K)`. -/
lemma chiN_mem_pmSub (γ : normCK D) (hγ : γ ∈ rangeIn (iotaCK D)) : chiN D γ ∈ pmSub D.ℓ := by
  rw [Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, hu⟩ := hγ
  have hu' : iotaCK D u = (γ : piCmod D) := hu
  let r : (piCKuToCK D).toMonoidHom.range := ⟨piCKuToCK D u, u, rfl⟩
  have e : normToStab D γ = ⟨MulAut.conj (r : piCK D), conj_mem_stabAut r⟩ := by
    refine Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective ?_)
    change piCKToCmod D (((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) x) =
      piCKToCmod D (piCKuToCK D u * x * (piCKuToCK D u)⁻¹)
    rw [piCKToCmod_piCmodToAut, map_mul, map_mul, map_inv]
    change _ = iotaCK D u * _ * (iotaCK D u)⁻¹
    rw [hu']
  change scalHom (isDihedralQuot_rhoCK D) (normToStab D γ) ∈ pmSub D.ℓ
  rw [e]
  exact scalHom_conj (isDihedralQuot_rhoCK D) r

/-- **`χ : Aut(C̲_K) → F_ℓ^⋇ = F_ℓ^×/{±1}`** (IUT I, Example 4.3 (i): the action on the rank-one
quotient, up to `±1`). -/
def chi : AutCK D →* FlStar D.ℓ :=
  QuotientGroup.map _ _ (chiN D) fun γ hγ => chiN_mem_pmSub D γ hγ

lemma chi_mk (γ : normCK D) : chi D (QuotientGroup.mk γ) = (chiN D γ : FlStar D.ℓ) := rfl

/-- **`Aut_ϵ(C̲_K) = ker χ`** (IUT I, Example 4.3 (i)). -/
def AutEps : Subgroup (AutCK D) := (chi D).ker

/-! ### `χ` is surjective (IUT I, Example 4.3 (i), Definition 3.1 (c)) -/

/-- The curve of `C̲_K` is `E_K`. -/
lemma CKu_E_eq : D.orb.CKu.E = D.prime.EK :=
  D.orb.CKu_to_CK.E_eq.trans (by rw [CK_eq]; rfl)

set_option maxHeartbeats 400000 in
-- the slimness argument unfolds the conjugation actions on `π₁(C_K)`
/-- **Every scalar `s ∈ F_ℓ^×` is `χ` of an element of `N(π₁(C̲_K))`**: `Gal(F̄/F)` contains an
element of the Borel subgroup of `SL₂(F_ℓ)` stabilising `M` with scalar `s` on `Q`
(`exists_semilin_data`, IUT I Def. 3.1 (c)); the induced semilinear automorphism of `π₁(C_K)`
(`exists_semilin_of_cover`) preserves `π₁(C̲_K)`; its restriction is conjugation by some
`γ ∈ N(π₁(C̲_K))` (`exists_normCK_eq`), which agrees with it on all of `π₁(C_K)` by slimness of
`π₁(C_{F_mod})`. Named inputs as in `exists_normCK_eq`. -/
theorem exists_normCK_chiN (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) (s : (ZMod D.ℓ)ˣ) :
    ∃ γ : normCK D, chiN D γ = s := by
  obtain ⟨-, hl, -, hMT, hMc, -⟩ := D.orb.CKu_type
  obtain ⟨θ, hE, f, hf, hM⟩ := exists_semilin_data D.prime D.orb.CKu.E (CKu_E_eq D)
    D.orb.CKu.M (hl ▸ hMT) hMc s
  obtain ⟨β, hβ⟩ := exists_semilin_of_cover (ℓ := D.ℓ) D.orb.CKu_to_CK D.orb.CKu_type
    (CK_level D) (CK_M D) (CK_pm D) D.orb.QIso θ hE f hf s hM
  have hβρ : ∀ x, rhoCK D (β x) 0 = s * rhoCK D x 0 := hβ (rhoCK D) (isDihedralQuot_rhoCK D)
  have hR := (isDihedralQuot_rhoCK D).2.1
  have hβR : ∀ y, β y ∈ (piCKuToCK D).toMonoidHom.range ↔
      y ∈ (piCKuToCK D).toMonoidHom.range := fun y => by
    rw [hR, hR, hβρ]
    exact Units.mul_right_eq_zero s
  have he₀ : IsOpenEmbedding (piCKuToCK D) := D.orb.pi1CKu_to_CK_isOpenEmbedding
  let α := restrictAutOfRange (piCKuToCK D) he₀.isEmbedding β hβR
  obtain ⟨γ, hγ⟩ := exists_normCK_eq D hStrict hS hDGC hj α
  have hι := isOpenEmbedding_piCKToCmod D
  let A : MulAut (piCK D) := ((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D))
  have hAu : ∀ u, A (piCKuToCK D u) = β (piCKuToCK D u) := fun u => hι.injective (by
    rw [piCKToCmod_piCmodToAut]
    have h1 := iotaCK_conjCK D γ u
    rw [hγ u] at h1
    change piCKToCmod D (piCKuToCK D (α u)) = _ at h1
    rw [restrictAutOfRange_spec] at h1
    exact h1.symm)
  have hAR : ∀ v ∈ (piCKuToCK D).toMonoidHom.range, A v = β v := by
    rintro _ ⟨u, rfl⟩
    exact hAu u
  have hA : ∀ y, A y = β y := fun y => by
    let R := (piCKuToCK D).toMonoidHom.range
    let V : Subgroup (piCK D) := R ⊓ R.comap (MulAut.conj y).toMonoidHom
    have hVo : IsOpen (V : Set (piCK D)) := by
      refine IsOpen.inter he₀.isOpen_range ?_
      exact he₀.isOpen_range.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    let U : Subgroup (piCK D) := V.map β.toMulEquiv.toMonoidHom
    have hUo : IsOpen (U : Set (piCK D)) := by
      have e : (U : Set (piCK D)) = β '' (V : Set (piCK D)) := by
        ext w
        simp only [U, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe]
        exact Iff.rfl
      rw [e]
      exact β.toHomeomorph.isOpenMap _ hVo
    have hcomm : ∀ w ∈ U, (A y)⁻¹ * β y * w = w * ((A y)⁻¹ * β y) := by
      rintro _ ⟨v, ⟨hv1, hv2⟩, rfl⟩
      have e1 := hAR v hv1
      have e2 := hAR _ hv2
      change A (y * v * y⁻¹) = β (y * v * y⁻¹) at e2
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, e1] at e2
      change (A y)⁻¹ * β y * β v = β v * ((A y)⁻¹ * β y)
      calc (A y)⁻¹ * β y * β v = (A y)⁻¹ * (β y * β v * (β y)⁻¹) * β y := by group
        _ = (A y)⁻¹ * (A y * β v * (A y)⁻¹) * β y := by rw [e2]
        _ = β v * ((A y)⁻¹ * β y) := by group
    have h1 := eq_one_of_commute_open₄ (isSlim_piCmod D) (piCKToCmod D) hι.isOpen_range hUo
      (z := piCKToCmod D ((A y)⁻¹ * β y)) fun w hw => by
        rw [← map_mul, ← map_mul, hcomm w hw]
    have h2 : (A y)⁻¹ * β y = 1 := hι.injective (h1.trans (map_one _).symm)
    calc A y = A y * ((A y)⁻¹ * β y) := by rw [h2, mul_one]
      _ = β y := by group
  refine ⟨γ, scalar_unique (isDihedralQuot_rhoCK D).2.2.choose_spec (chiN_spec D γ) fun x => ?_⟩
  change rhoCK D (A x) 0 = _
  rw [hA x]
  exact hβρ x

/-- **`χ : Aut(C̲_K) → F_ℓ^⋇` is surjective**, i.e. `Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇` (IUT I,
Example 4.3 (i)). Named inputs as in `exists_normCK_eq`. -/
theorem chi_surjective (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) : Function.Surjective (chi D) := fun j => by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective j
  obtain ⟨γ, hγ⟩ := exists_normCK_chiN D hStrict hS hDGC hj s
  exact ⟨QuotientGroup.mk γ, by rw [chi_mk, hγ]⟩

/-! ### Poly-automorphisms of `D^⊚` -/

/-- The poly-automorphism of `D^⊚ = B(C̲_K)⁰` given by a set `S ⊆ Aut(C̲_K)`. -/
def autPoly (S : Set (AutCK D)) : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D) :=
  autPolyN (isOpenEmbedding_iotaCK D).injective (isOpenEmbedding_iotaCK D).isEmbedding S

/-- **`S ∘ S ⊆ S`** for a subgroup `S ⊆ Aut(C̲_K)`. -/
theorem autPoly_comp_subset (S : Subgroup (AutCK D)) :
    (autPoly D S).comp (autPoly D S) ⊆ autPoly D S :=
  autPolyN_comp_subset _ _ (hasONSBasis_profinite D.orb.CKu.genuinePi1)
    (isONSComplete_profinite D.orb.CKu.genuinePi1) S

/-- **`Aut_ϵ(D^⊚)`** as a poly-automorphism of `D^⊚`. -/
def autEpsPoly : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D) :=
  autPoly D (AutEps D)

/-- **The poly-action of `j ∈ F_ℓ^⋇` on `D^⊚`**: the automorphisms with `χ = j`. -/
def actStar (j : FlStar D.ℓ) : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D) :=
  autPoly D (chi D ⁻¹' {j})

theorem actStar_comp_subset (j j' : FlStar D.ℓ) :
    (actStar D j).comp (actStar D j') ⊆ actStar D (j * j') :=
  autPolyN_fiber_comp_subset _ _ (hasONSBasis_profinite D.orb.CKu.genuinePi1)
    (isONSComplete_profinite D.orb.CKu.genuinePi1) (chi D) j j'

/-- **`act j ∘ act j' = act (j j')`** (IUT I, Example 4.3 (i): `Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇`,
`chi_surjective`). Named inputs as in `exists_normCK_eq`. -/
theorem actStar_comp (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) (j j' : FlStar D.ℓ) :
    (actStar D j).comp (actStar D j') = actStar D (j * j') :=
  autPolyN_fiber_comp _ _ (hasONSBasis_profinite D.orb.CKu.genuinePi1)
    (isONSComplete_profinite D.orb.CKu.genuinePi1) (chi D)
    (chi_surjective D hStrict hS hDGC hj) j j'

/-- **`φ^NF_v` for `A = Aut_ϵ(D^⊚)`** (IUT I, Example 4.3 (ii)). -/
def phiNFEps (v : NumberField.FinitePlace ↥(fieldOfModuli D.F D.E)) :
    PolyMor (Dv D v) (dCircModel D) (Piv D v).carrier (PiCK D) :=
  phiNF D (autEpsPoly D) v

/-- `φ^NF_v` is stabilised by `Aut_ϵ(D^⊚)` (IUT I, Example 4.3 (iv)). -/
theorem phiNFEps_comp_subset (v : NumberField.FinitePlace ↥(fieldOfModuli D.F D.E)) :
    (phiNFEps D v).comp (autEpsPoly D) ⊆ phiNFEps D v :=
  phiNF_comp_subset D (autPoly_comp_subset D (AutEps D)) v

/-- **`φ^NF_⋇ : D^⋇ → D^⊚`** with `Aut_ϵ(D^⊚)` and the `F_ℓ^⋇`-poly-action `actStar`
(IUT I, Example 4.3 (iv)). -/
def phiNFStarEps : CapStripPolyMor (fun (_ : FlStar D.ℓ) v => Dv D v)
    (fun _ v => (Piv D v).carrier) (dCircModel D) (PiCK D) :=
  phiNFStar D (autEpsPoly D) (actStar D)

/-- The component at `1` of `φ^NF_⋇` lies in `φ^NF_1`. -/
theorem phiNFStarEps_one_subset (v : NumberField.FinitePlace ↥(fieldOfModuli D.F D.E)) :
    phiNFStarEps D 1 v ⊆ phiNFEps D v :=
  phiNFStar_one_subset D (autPoly_comp_subset D (AutEps D)) (fun _ h => h) v

/-- **Equivariance of `φ^NF_⋇`** (IUT I, Example 4.3 (iv)). Named inputs as in
`exists_normCK_eq`. -/
theorem phiNFStarEps_postcomp (hStrict : CKuStrictSemiAbs D)
    (hS : BelyiCuspSpec (AlgebraicClosure D.Kt) (hypCurveE (EK D)) (factEK D).out)
    (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) (j j' : FlStar D.ℓ) :
    (phiNFStarEps D j).postcomp (actStar D j') = phiNFStarEps D (j * j') :=
  phiNFStar_postcomp D _ _ j j' (actStar_comp D hStrict hS hDGC hj j j')

end AutCK

end Iut.Multiradial.Theater
