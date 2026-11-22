/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Cor53Vdash
import Iut.Multiradial.PrimeStrip.Cor53Bij
import Iut.Multiradial.PrimeStrip.OrbitInner
import Iut.Multiradial.PrimeStrip.TransportNat

/-!
# `F ↦ F^⊢` on isomorphisms at `v ∈ V^non` (MR21 R7)

IUT I, Example 3.3 (iii)(d), (e) (`V^good`, l.5150–5170 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): `C^⊢_v ⊆ C_v` (the
sub-Frobenioid over `D^⊢_v ⊆ D_v` with divisor monoid `ord(ℤ_p^▷) ⊆ Φ_{C_v}`) and the splitting
`τ^⊢_v` are reconstructed category-theoretically from `F_v`, hence so is `F^⊢_v` (Remark 5.2.1
(ii), l.9827: the mono-analyticisation `‡F ↦ ‡F^⊢`). "Reconstructed category-theoretically" means
preserved by equivalences (Remark 3.2.1 (i), l.4784); so the content is: every automorphism of
`F_v` restricts to an automorphism of `F^⊢_v`, functorially. At `V^bad` the same holds by
Example 3.2 (vi)(f) (l.4769–4783: `F^⊢_v`, with its `μ_{2l}`-orbit of splittings, is
reconstructed from `C_v`). This file constructs this restriction on isomorphism classes (IUT I,
§0) at `v ∈ V^non`:

* `OrbitObj.isoFunctorTransIso`, `GaloisModel.rel_isoOfSub_trans` (composites),
  `GaloisModel.rel_isoOfSub_conj` (conjugation by `g ∈ G'`): 2-isomorphisms of the isomorphisms
  `GaloisModel.isoOfSub σ ψ` of Galois model Frobenioids (`Cor53Vdash.lean`);
* the named input **`PFixedLift D v`** (IUT I, Example 3.3 (iii)(e): `p_v` is reconstructed from
  `F_v` through the field structure on the image of the Kummer map, [AbsTopIII], Proposition 3.2
  (iii), Corollary 1.10 (h), for curves of strictly Belyi type): every automorphism of `Π_v` has
  an equivariant `ord`-preserving lift to `\bar{ℚ}_p^×` fixing `p`; it gives `TauLift D v` at
  `V^good` (`tauLift_of_pFixedLift`); at `V^bad` **`TauLift D v`** (the lift maps `q̲_v` into its
  `μ_{2l}`-orbit `tauOrbit D v`; Example 3.2 (vi)(f)) is itself the named input;
* `resIso σ̄ ψ`: the automorphism of `F^⊢_v` from `σ̄ ∈ Aut(G_v)` and `ψ` (restricted to
  `ord⁻¹(ℤ · ord τ_v)`, `subRes`; it permutes the orbit of splittings); `IsRes a b`:
  `a = [isoOf σ ψ]`, `b = [resIso σ̄ ψ]`, `σ̄` the descent of `σ` (MR9's `exists_descend_piv`);
* `exists_isRes` (every class `a ∈ Aut(C_v)` is `[isoOf σ ψ]` by Corollary 5.3 (ii), injectivity,
  and `TauLift`), **`isRes_unique`** (two such descriptions differ by an inner automorphism of
  `Π_v`, `OrbitObj.exists_conj_of_natTrans`, and the lifts by its action, `KummerRigid`),
  `isRes_trans`;
* **`vdashRes : Aut(C_v) → Aut(F^⊢_v)`** on classes with `vdashRes_trans`, `vdashRes_refl`
  (functoriality) and `vdashRes_toD` (on `D^⊢_v` it is the descent of the class on `D_v`);
* `FComp.vdashClass`: `F ↦ F^⊢` on isomorphism classes of constituents `‡F_v ≅ ‡F'_v`
  (transport to the model), functorial (`FComp.vdashClass_trans`, `FComp.vdashClass_refl`).

Inputs (`ResInputs D v`): `DeltaCharacteristic` ([AbsAnab], Lemma 1.3.8), H3
(`PiToGQuotient`), `PivCountable` at `V^bad`, and `TauLift` (from `PFixedLift` at `V^good`,
`resInputs_of_good`). At `V^bad` a fixed root `q̲_v` could not be preserved in general (an
automorphism may send `q̲_v ↦ ζ q̲_v`); this is why `τ^⊢_v` is the `μ_{2l}`-orbit
(`fVdashModel`, Example 3.2 (iv)).
-/

noncomputable section

/-! ### Composites and conjugates of isomorphisms of Galois model Frobenioids -/

namespace Iut

namespace Frobenioid

open CategoryTheory

section OrbitTrans

variable {G₁ G₂ G₃ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [Group G₃] [TopologicalSpace G₃]

/-- `G₁/H ↦ G₃/σ₂(σ₁(H))` is `G₁/H ↦ G₃/(σ₂ ∘ σ₁)(H)` (identity cosets). -/
def OrbitObj.isoFunctorTransIso (σ₁ : G₁ ≃ₜ* G₂) (σ₂ : G₂ ≃ₜ* G₃) :
    OrbitObj.isoFunctor σ₁ ⋙ OrbitObj.isoFunctor σ₂ ≅ OrbitObj.isoFunctor (σ₁.trans σ₂) :=
  NatIso.ofComponents
    (fun A => OrbitObj.isoOfConj _ _ 1
      (fun a ha => by
        rw [inv_one, one_mul, mul_one]
        change a ∈ (A.H.map (σ₁ : G₁ →* G₂)).map (σ₂ : G₂ →* G₃) at ha
        rw [Subgroup.map_map] at ha
        exact ha)
      (fun b hb => by
        rw [inv_one, one_mul, mul_one]
        change b ∈ (A.H.map (σ₁ : G₁ →* G₂)).map (σ₂ : G₂ →* G₃)
        rw [Subgroup.map_map]
        exact hb))
    (fun {A B} f => OrbitHom.hom_ext <| funext fun x => by
      induction x using QuotientGroup.induction_on with
      | H a =>
        obtain ⟨b, hb, he⟩ := OrbitHom.rep_map (σ₁ : G₁ →* G₂)
          (isOpen_map_of_continuousMulEquiv σ₁) f
        change (QuotientGroup.mk (a * σ₂ (OrbitHom.rep (OrbitHom.map (σ₁ : G₁ →* G₂)
          (isOpen_map_of_continuousMulEquiv σ₁) f)) * 1) : G₃ ⧸ _) =
          QuotientGroup.mk (a * 1 * σ₂ (σ₁ (OrbitHom.rep f)))
        rw [he]
        refine QuotientGroup.eq.2 ?_
        obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
        have hm := Subgroup.mem_map_of_mem (σ₁.trans σ₂ : G₁ →* G₃) (B.H.inv_mem hb₀)
        convert hm using 1
        all_goals first
          | rfl
          | (change _ = σ₂ (σ₁ b₀⁻¹)
             simp only [map_mul, map_inv, mul_one, MonoidHom.coe_coe]
             group))

lemma OrbitObj.isoFunctorTransIso_rep (σ₁ : G₁ ≃ₜ* G₂) (σ₂ : G₂ ≃ₜ* G₃) (A : OrbitObj G₁) :
    ((OrbitObj.isoFunctorTransIso σ₁ σ₂).hom.app A).toFun (QuotientGroup.mk 1) =
      QuotientGroup.mk 1 := by
  change (QuotientGroup.mk (1 * 1) : G₃ ⧸ _) = _
  rw [mul_one]

end OrbitTrans

end Frobenioid

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section GalRel

variable {G G' G'' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [Group G''] [TopologicalSpace G''] [IsTopologicalGroup G'']
  {M M' M'' : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
  [DistribMulAction G' M'] [AddCommGroup M''] [DistribMulAction G'' M'']
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m}
  {ℓ' : M' →+ ℝ} (hℓ' : ∀ (g : G') (m : M'), ℓ' (g • m) = ℓ' m)
  {ℓ'' : M'' →+ ℝ} (hℓ'' : ∀ (g : G'') (m : M''), ℓ'' (g • m) = ℓ'' m) {Γ : AddSubgroup ℝ}

/-- `bval` of a pull-back along a morphism with base coset `g`: `g • u`. -/
lemma bval_pb_of_mk {A B : OrbitObj G'} (f : A ⟶ B) {g : G'}
    (h : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk g) (u : (bGal G' ℓ' hℓ' Γ).obj B) :
    bval ((bGal G' ℓ' hℓ' Γ).pb f u) = g • bval u := by
  have hr : g⁻¹ * OrbitHom.rep f ∈ B.H := by
    have := OrbitHom.mk_rep f
    rw [h] at this
    exact QuotientGroup.eq.1 this.symm
  change OrbitHom.rep f • bval u = g • bval u
  have e : OrbitHom.rep f = g * (g⁻¹ * OrbitHom.rep f) := by group
  rw [e, mul_smul, (bval_mem u).2 _ hr]

/-- **Composites**: `isoOfSub σ₁ ψ₁ ∘ isoOfSub σ₂ ψ₂` is 2-isomorphic to
`isoOfSub (σ₂ ∘ σ₁) (ψ₂ ∘ ψ₁)`. -/
theorem GaloisModel.rel_isoOfSub_trans (σ₁ : G ≃ₜ* G') (ψ₁ : Γ.comap ℓ ≃+ Γ.comap ℓ')
    (hψ₁ : ∀ (g : G) (m : Γ.comap ℓ), (ψ₁ (smulSub hℓ g m) : M') = σ₁ g • (ψ₁ m : M'))
    (hψℓ₁ : ∀ m : Γ.comap ℓ, ℓ' (ψ₁ m) = ℓ m)
    (σ₂ : G' ≃ₜ* G'') (ψ₂ : Γ.comap ℓ' ≃+ Γ.comap ℓ'')
    (hψ₂ : ∀ (g : G') (m : Γ.comap ℓ'), (ψ₂ (smulSub hℓ' g m) : M'') = σ₂ g • (ψ₂ m : M''))
    (hψℓ₂ : ∀ m : Γ.comap ℓ', ℓ'' (ψ₂ m) = ℓ' m)
    (hψ₁₂ : ∀ (g : G) (m : Γ.comap ℓ),
      ((ψ₁.trans ψ₂) (smulSub hℓ g m) : M'') = (σ₁.trans σ₂) g • ((ψ₁.trans ψ₂) m : M''))
    (hψℓ₁₂ : ∀ m : Γ.comap ℓ, ℓ'' ((ψ₁.trans ψ₂) m) = ℓ m) :
    FrobCat.Iso.Rel ((GaloisModel.isoOfSub hℓ' σ₁ ψ₁ hψ₁ hψℓ₁).trans
        (GaloisModel.isoOfSub hℓ'' σ₂ ψ₂ hψ₂ hψℓ₂))
      (GaloisModel.isoOfSub hℓ'' (σ₁.trans σ₂) (ψ₁.trans ψ₂) hψ₁₂ hψℓ₁₂) := by
  refine ⟨FrobCat.Iso.hom2OfBase
    (Model.transportNatIso (OrbitObj.isoFunctorTransIso σ₁ σ₂)
      (Φ := constPhi (OrbitObj G) Γ) (B := bGal G ℓ hℓ Γ) (divB := divGal G ℓ hℓ Γ)
      (Φ' := constPhi (OrbitObj G'') Γ) (B' := bGal G'' ℓ'' hℓ'' Γ)
      (divB' := divGal G'' ℓ'' hℓ'' Γ)
      (c := fun A => ((AddEquiv.refl Γ).toAddMonoidHom).comp (AddEquiv.refl Γ).toAddMonoidHom)
      (c' := fun A => (AddEquiv.refl Γ).toAddMonoidHom)
      (cb := fun A => (bMapSub hℓ'' σ₂ ψ₂ hψ₂ _).comp (bMapSub hℓ' σ₁ ψ₁ hψ₁ A))
      (cb' := fun A => bMapSub hℓ'' (σ₁.trans σ₂) (ψ₁.trans ψ₂) hψ₁₂ A)
      (hc := fun _ _ => rfl) (hpos := fun _ _ h => h)
      (hcb := fun f u => (congrArg (bMapSub hℓ'' σ₂ ψ₂ hψ₂ _)
        (bMapSub_pb hℓ' σ₁ ψ₁ hψ₁ f u)).trans (bMapSub_pb hℓ'' σ₂ ψ₂ hψ₂ _ _))
      (hdiv := fun A u => (bMapSub_div hℓ'' σ₂ ψ₂ hψ₂ hψℓ₂ _ _).trans
        (bMapSub_div hℓ' σ₁ ψ₁ hψ₁ hψℓ₁ A u))
      (hc' := fun _ _ => rfl) (hpos' := fun _ _ h => h)
      (hcb' := fun f u => bMapSub_pb hℓ'' _ _ hψ₁₂ f u)
      (hdiv' := fun A u => bMapSub_div hℓ'' _ _ hψ₁₂ hψℓ₁₂ A u)
      (fun _ _ => rfl)
      (fun A u => PrimeStrip.bval_injective (by
        rw [bval_pb_of_mk hℓ'' _ (OrbitObj.isoFunctorTransIso_rep σ₁ σ₂ A), one_smul]
        rfl)))
    (OrbitObj.isoFunctorTransIso σ₁ σ₂) (fun _ _ => rfl) (fun A => ?_)⟩
  change (OrbitObj.isoFunctorTransIso σ₁ σ₂).hom.app A.base ≫ 𝟙 _ =
    (𝟙 _ ≫ (OrbitObj.isoFunctor σ₂).map (𝟙 _)) ≫ (OrbitObj.isoFunctorTransIso σ₁ σ₂).hom.app A.base
  rw [CategoryTheory.Functor.map_id]
  simp

end GalRel

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section GalConj

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M M' : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
  [DistribMulAction G' M']
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m}
  {ℓ' : M' →+ ℝ} (hℓ' : ∀ (g : G') (m : M'), ℓ' (g • m) = ℓ' m) {Γ : AddSubgroup ℝ}

/-- **Conjugates**: `isoOfSub σ ψ` and `isoOfSub (g⁻¹ σ(−) g) (g⁻¹ ψ)` are 2-isomorphic. -/
theorem GaloisModel.rel_isoOfSub_conj (σ : G ≃ₜ* G') (ψ : Γ.comap ℓ ≃+ Γ.comap ℓ')
    (hψ : ∀ (g : G) (m : Γ.comap ℓ), (ψ (smulSub hℓ g m) : M') = σ g • (ψ m : M'))
    (hψℓ : ∀ m : Γ.comap ℓ, ℓ' (ψ m) = ℓ m)
    (σ' : G ≃ₜ* G') (ψ' : Γ.comap ℓ ≃+ Γ.comap ℓ')
    (hψ' : ∀ (g : G) (m : Γ.comap ℓ), (ψ' (smulSub hℓ g m) : M') = σ' g • (ψ' m : M'))
    (hψℓ' : ∀ m : Γ.comap ℓ, ℓ' (ψ' m) = ℓ m) (g : G')
    (hσ : ∀ x, σ' x = g⁻¹ * σ x * g) (hψg : ∀ m, (ψ' m : M') = g⁻¹ • (ψ m : M')) :
    FrobCat.Iso.Rel (GaloisModel.isoOfSub hℓ' σ ψ hψ hψℓ)
      (GaloisModel.isoOfSub hℓ' σ' ψ' hψ' hψℓ') := by
  let β : OrbitObj.isoFunctor σ ≅ OrbitObj.isoFunctor σ' :=
    OrbitObj.mapFunctorConjIso (σ' : G →* G') (σ : G →* G')
      (isOpen_map_of_continuousMulEquiv σ') (isOpen_map_of_continuousMulEquiv σ) g
      (fun x => by rw [MonoidHom.coe_coe, MonoidHom.coe_coe, hσ]; group)
  have hrep : ∀ A, (β.hom.app A).toFun (QuotientGroup.mk 1) = QuotientGroup.mk (1 * g) :=
    fun _ => rfl
  refine ⟨FrobCat.Iso.hom2OfBase
    (Model.transportNatIso β
      (Φ := constPhi (OrbitObj G) Γ) (B := bGal G ℓ hℓ Γ) (divB := divGal G ℓ hℓ Γ)
      (Φ' := constPhi (OrbitObj G') Γ) (B' := bGal G' ℓ' hℓ' Γ)
      (divB' := divGal G' ℓ' hℓ' Γ)
      (c := fun A => (AddEquiv.refl Γ).toAddMonoidHom)
      (c' := fun A => (AddEquiv.refl Γ).toAddMonoidHom)
      (cb := fun A => bMapSub hℓ' σ ψ hψ A)
      (cb' := fun A => bMapSub hℓ' σ' ψ' hψ' A)
      (hc := fun _ _ => rfl) (hpos := fun _ _ h => h)
      (hcb := fun f u => bMapSub_pb hℓ' _ _ hψ f u)
      (hdiv := fun A u => bMapSub_div hℓ' _ _ hψ hψℓ A u)
      (hc' := fun _ _ => rfl) (hpos' := fun _ _ h => h)
      (hcb' := fun f u => bMapSub_pb hℓ' _ _ hψ' f u)
      (hdiv' := fun A u => bMapSub_div hℓ' _ _ hψ' hψℓ' A u)
      (fun _ _ => rfl)
      (fun A u => PrimeStrip.bval_injective (by
        rw [bval_pb_of_mk hℓ' _ (hrep A), one_mul]
        change g • (ψ' _ : M') = (ψ _ : M')
        rw [hψg, smul_inv_smul])))
    β (fun _ _ => rfl) (fun A => ?_)⟩
  change β.hom.app A.base ≫ 𝟙 _ = 𝟙 _ ≫ β.hom.app A.base
  simp

end GalConj

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-! ### Restriction of `ℓ`-preserving automorphisms to `ℓ⁻¹(Γ)` -/

section SubRes

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [DistribMulAction G M]
  {ℓ : M →+ ℝ} (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m) (Γ : AddSubgroup ℝ)

/-- An `ℓ`-preserving automorphism of `M`, restricted to `ℓ⁻¹(Γ)`. -/
def subRes (ψ : M ≃+ M) (hψℓ : ∀ m, ℓ (ψ m) = ℓ m) : Γ.comap ℓ ≃+ Γ.comap ℓ where
  toFun m := ⟨ψ m, show ℓ (ψ m) ∈ Γ by rw [hψℓ]; exact m.2⟩
  invFun m := ⟨ψ.symm m, show ℓ (ψ.symm m) ∈ Γ by
    rw [← hψℓ, AddEquiv.apply_symm_apply]; exact m.2⟩
  left_inv m := Subtype.ext (ψ.symm_apply_apply _)
  right_inv m := Subtype.ext (ψ.apply_symm_apply _)
  map_add' m m' := Subtype.ext (map_add ψ _ _)

@[simp] lemma coe_subRes (ψ : M ≃+ M) (hψℓ : ∀ m, ℓ (ψ m) = ℓ m) (m : Γ.comap ℓ) :
    (subRes Γ ψ hψℓ m : M) = ψ m := rfl

lemma ell_subRes (ψ : M ≃+ M) (hψℓ : ∀ m, ℓ (ψ m) = ℓ m) (m : Γ.comap ℓ) :
    ℓ (subRes Γ ψ hψℓ m) = ℓ m := hψℓ _

lemma smul_subRes {σ : G ≃* G} (ψ : M ≃+ M) (hψ : ∀ (g : G) (m : M), ψ (g • m) = σ g • ψ m)
    (hψℓ : ∀ m, ℓ (ψ m) = ℓ m) (g : G) (m : Γ.comap ℓ) :
    (subRes Γ ψ hψℓ (smulSub hℓ g m) : M) = σ g • (subRes Γ ψ hψℓ m : M) := hψ g m

lemma subRes_trans (ψ₁ ψ₂ : M ≃+ M) (h₁ : ∀ m, ℓ (ψ₁ m) = ℓ m) (h₂ : ∀ m, ℓ (ψ₂ m) = ℓ m)
    (h₁₂ : ∀ m, ℓ ((ψ₁.trans ψ₂) m) = ℓ m) :
    subRes Γ (ψ₁.trans ψ₂) h₁₂ = (subRes Γ ψ₁ h₁).trans (subRes Γ ψ₂ h₂) := rfl

end SubRes

/-! ### The restriction `Aut(F_v) → Aut(F^⊢_v)` -/

section Res

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **The splitting `τ^⊢_v` is reconstructed from `F_v`** (IUT I, Example 3.3 (iii)(e),
l.5160–5170 of `Inter-universal Teichmuller Theory I.txt`; named input): every automorphism `σ` of
the topological group `Π_v` admits a `σ`-equivariant `ord`-preserving automorphism of
`\bar{ℚ}_p^×` fixing `p`. IUT obtains `p_v` from the field structure on the image of the Kummer
map ([AbsTopIII], Proposition 3.2 (iii), l.4096ff of
`Topics in Absolute Anabelian Geometry III.txt`, via Corollary 1.10 (h), l.2512ff, for curves of
strictly Belyi type, Remark 2.8.3, l.3611): the lift of [AbsTopIII], Proposition 3.2 (iv)
(unique, `KummerRigid`) is then the restriction of an automorphism of the field
`\bar{ℚ}_p`, which fixes `p`. Only used at `v ∉ V^bad` (at `V^bad` IUT's `τ^⊢_v` is a
`μ_{2l}`-orbit of splittings, IUT I, Example 3.2 (iv), and is reconstructed through the étale
theta function, Example 3.2 (vi)(f); see `TauLift`). -/
def PFixedLift : Prop :=
  ∀ σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier, ∃ ψ : PiMul D v ≃+ PiMul D v,
    (∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ (g • m) = σ g • ψ m) ∧
      (∀ m, ordPi D v (ψ m) = ordPi D v m) ∧ ψ (pMul D v) = pMul D v

/-- `Π_v` is Hausdorff, with a basis of open normal subgroups, complete for them. -/
theorem piv_conjData :
    T2Space (Piv D v).carrier ∧ HasONSBasis (Piv D v).carrier ∧
      IsONSComplete (Piv D v).carrier := by
  by_cases hv : v ∈ D.VBad
  · obtain ⟨h1, h2, h3, -⟩ := piv_temp D v hv
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := piv_profinite D v hv
    exact ⟨h3, hasONSBasis_of_profinite, isONSComplete_of_compact⟩

/-- An automorphism of the `Π_v`-module `\bar{ℚ}_p^×` as an automorphism of `\bar{ℚ}_p^×`. -/
def psiMul (ψ : PiMul D v ≃+ PiMul D v) : PAdicGalois.Mul (pv D v) ≃+ PAdicGalois.Mul (pv D v) := ψ

/-- **The collection of splittings `τ^⊢_v` is reconstructed from `C_v`**: every automorphism `σ`
of `Π_v` admits a `σ`-equivariant `ord`-preserving automorphism `ψ` of `\bar{ℚ}_p^×` mapping
`τ_v` into the orbit `tauOrbit D v`. At `v ∉ V^bad` this follows from `PFixedLift`
(`tauLift_of_pFixedLift`). At `v ∈ V^bad` it is a **named input** (IUT I, Example 3.2 (vi)(f),
l.4769–4783 of `Inter-universal Teichmuller Theory I.txt`: `F^⊢_v`, with its `μ_{2l}`-orbit of
splittings, is reconstructed from `C_v` through the Kummer classes of the étale theta function,
which are reconstructed from `D_v` by [EtTh], Corollary 2.8 (i), with the cyclotomes of
[AbsTopIII], Corollary 1.10 (c), Remark 3.2.1; the values of `Θ_v` give `q̲_v` up to `μ_{2l}`,
Example 3.2 (ii), (iv)). By `KummerRigid` the lift is the unique Kummer lift of
[AbsTopIII], Proposition 3.2 (iv) (MR9's `kummerLift`). -/
def TauLift : Prop :=
  ∀ σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier, ∃ ψ : PiMul D v ≃+ PiMul D v,
    (∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ (g • m) = σ g • ψ m) ∧
      (∀ m, ordPi D v (ψ m) = ordPi D v m) ∧ psiMul D v ψ (tauElt D v) ∈ tauOrbit D v

/-- `τ_v = p` at `v ∉ V^bad`. -/
lemma tauElt_of_good (hv : v ∉ D.VBad) : tauElt D v = pMul D v := by
  simp only [tauElt, dif_neg hv]

lemma ord_tauElt_mem : PAdicGalois.ord (pv D v) (tauElt D v) ∈ gammaVdash D v := by
  rw [gammaVdash_eq]
  exact AddSubgroup.mem_zmultiples _

/-- At `v ∉ V^bad`, `PFixedLift` gives `TauLift` (`τ_v = p`, and `p` is in its orbit). -/
theorem tauLift_of_pFixedLift (hv : v ∉ D.VBad) (hp : PFixedLift D v) : TauLift D v := by
  intro σ
  obtain ⟨ψ, hψ, hψℓ, hpψ⟩ := hp σ
  refine ⟨ψ, hψ, hψℓ, ?_⟩
  change psiMul D v ψ (tauElt D v) ∈ GaloisModel.orbitGen (Gv D v) (tauElt D v) (nOrb D v)
  rw [tauElt_of_good D v hv, show psiMul D v ψ (pMul D v) = pMul D v from hpψ]
  exact GaloisModel.self_mem_orbitGen (G := Gv D v) (pMul D v) (nOrb D v)

variable {D v}

/-- **The automorphism of `F^⊢_v`** induced by `σ̄ ∈ Aut(G_v)` and a `σ̄`-equivariant
`ord`-preserving `ψ` fixing `τ_v` (restricted to `ord⁻¹(ℤ · ord τ_v)`). -/
def resIso (σ : Gv D v ≃ₜ* Gv D v) (ψ : PAdicGalois.Mul (pv D v) ≃+ PAdicGalois.Mul (pv D v))
    (hψ : ∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)), ψ (g • m) = σ g • ψ m)
    (hψℓ : ∀ m, PAdicGalois.ord (pv D v) (ψ m) = PAdicGalois.ord (pv D v) m)
    (hτ : ψ (tauElt D v) ∈ tauOrbit D v) :
    (fVdashModel D v).Iso (fVdashModel D v) :=
  GaloisModel.splitIsoOfSub (PAdicGalois.ord_smul (pv D v) (Lv D v)) σ
    (subRes (gammaVdash D v) ψ hψℓ)
    (smul_subRes (PAdicGalois.ord_smul (pv D v) (Lv D v)) _ (σ := (σ : Gv D v ≃* Gv D v)) ψ hψ
      hψℓ)
    (ell_subRes _ ψ hψℓ) (nOrb_ne_zero D v) (ord_tauElt_mem D v) (ord_tauElt_mem D v) hτ

lemma resIso_D (σ : Gv D v ≃ₜ* Gv D v) (ψ : PAdicGalois.Mul (pv D v) ≃+ PAdicGalois.Mul (pv D v))
    (hψ : ∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)), ψ (g • m) = σ g • ψ m)
    (hψℓ : ∀ m, PAdicGalois.ord (pv D v) (ψ m) = PAdicGalois.ord (pv D v) m)
    (hτ : ψ (tauElt D v) ∈ tauOrbit D v) :
    (resIso σ ψ hψ hψℓ hτ).iso.D = OrbitObj.equivOfIso σ := rfl

end Res

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

namespace SplitFrobCat.IsoClass

variable {X Y Z W : SplitFrobCat}

/-- The identity class. -/
def refl (X : SplitFrobCat) : IsoClass X X := mk (SplitFrobCat.Iso.refl X)

lemma mk_eq_mk {f g : X.Iso Y} : mk f = mk g ↔ FrobCat.Iso.Rel f.iso g.iso :=
  Quotient.eq (r := setoid X Y)

lemma mk_trans_mk (f : X.Iso Y) (g : Y.Iso Z) : (mk f).trans (mk g) = mk (f.trans g) := rfl

lemma trans_assoc (a : IsoClass X Y) (b : IsoClass Y Z) (c : IsoClass Z W) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  obtain ⟨h, rfl⟩ := mk_surjective c
  exact mk_eq_mk.2 (FrobCat.Iso.Rel.assoc f.iso g.iso h.iso)

lemma trans_refl (a : IsoClass X Y) : a.trans (refl Y) = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FrobCat.Iso.Rel.transRefl f.iso)

lemma trans_symm (a : IsoClass X Y) : a.trans a.symm = refl X := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (FrobCat.Iso.Rel.transSymm f.iso)

/-- An idempotent class is the identity. -/
lemma eq_refl_of_trans_self {a : IsoClass X X} (h : a.trans a = a) : a = refl X := by
  have := congrArg (·.trans a.symm) h
  simp only [trans_assoc, trans_symm, trans_refl] at this
  exact this

end SplitFrobCat.IsoClass

section Res

variable {D : InitialThetaData.{0}} {v : FinitePlace ↥(fieldOfModuli D.F D.E)}

/-- **`b` is the restriction of `a`**: `a` is the class of `isoOf σ ψ` and `b` the class of
`resIso σ̄ ψ` for an automorphism `σ` of `Π_v` with descent `σ̄` to `G_v` and its lift `ψ` to
`\bar{ℚ}_p^×` fixing `τ_v`. -/
def IsRes (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v))
    (b : SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v)) : Prop :=
  ∃ (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) (ψ : PiMul D v ≃+ PiMul D v)
    (hψ : ∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ (g • m) = σ g • ψ m)
    (hψℓ : ∀ m, ordPi D v (ψ m) = ordPi D v m) (σ' : Gv D v ≃ₜ* Gv D v)
    (_ : ∀ g, piToG D v (σ g) = σ' (piToG D v g))
    (hψ' : ∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)),
      psiMul D v ψ (g • m) = σ' g • psiMul D v ψ m)
    (hτ : psiMul D v ψ (tauElt D v) ∈ tauOrbit D v),
    a = FrobCat.IsoClass.mk (GaloisModel.isoOf (Γ := PAdicGalois.gammaQ)
      (hℓ := ordPi_smul D v) (hℓ' := ordPi_smul D v) σ ψ hψ hψℓ) ∧
      b = SplitFrobCat.IsoClass.mk (resIso σ' (psiMul D v ψ) hψ' hψℓ hτ)

end Res

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section Main

variable {D : InitialThetaData.{0}} {v : FinitePlace ↥(fieldOfModuli D.F D.E)}

/-- `isoOf σ₁ ψ₁ ∘ isoOf σ₂ ψ₂` and `isoOf (σ₂ ∘ σ₁) (ψ₂ ∘ ψ₁)` have the same class in
`Aut(C_v)` (injectivity of `F ↦ D`, `cvFrob_autRigid`). -/
theorem cv_mk_isoOf_trans (h3 : PiToGQuotient D v)
    (σ₁ σ₂ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) (ψ₁ ψ₂ : PiMul D v ≃+ PiMul D v)
    (hψ₁ : ∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ₁ (g • m) = σ₁ g • ψ₁ m)
    (hψℓ₁ : ∀ m, ordPi D v (ψ₁ m) = ordPi D v m)
    (hψ₂ : ∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ₂ (g • m) = σ₂ g • ψ₂ m)
    (hψℓ₂ : ∀ m, ordPi D v (ψ₂ m) = ordPi D v m)
    (hψ₁₂ : ∀ (g : (Piv D v).carrier) (m : PiMul D v),
      (ψ₁.trans ψ₂) (g • m) = (σ₁.trans σ₂) g • (ψ₁.trans ψ₂) m)
    (hψℓ₁₂ : ∀ m, ordPi D v ((ψ₁.trans ψ₂) m) = ordPi D v m) :
    FrobCat.IsoClass.mk (X := cvFrob D v) (Y := cvFrob D v)
        (FrobCat.Iso.trans (Y := cvFrob D v)
          (GaloisModel.isoOf (Γ := PAdicGalois.gammaQ) (hℓ := ordPi_smul D v)
            (hℓ' := ordPi_smul D v) σ₁ ψ₁ hψ₁ hψℓ₁)
          (GaloisModel.isoOf (Γ := PAdicGalois.gammaQ) (hℓ := ordPi_smul D v)
            (hℓ' := ordPi_smul D v) σ₂ ψ₂ hψ₂ hψℓ₂)) =
      FrobCat.IsoClass.mk (X := cvFrob D v) (Y := cvFrob D v)
        (GaloisModel.isoOf (Γ := PAdicGalois.gammaQ) (hℓ := ordPi_smul D v)
          (hℓ' := ordPi_smul D v) (σ₁.trans σ₂) (ψ₁.trans ψ₂) hψ₁₂ hψℓ₁₂) :=
  FrobCat.IsoClass.toD_injective (cvFrob_autRigid D v h3.1)
    (CatIsom.mk_eq_mk.2 ⟨OrbitObj.isoFunctorTransIso σ₁ σ₂⟩)

/-- **Existence of the restriction** of an automorphism class of `C_v` to `F^⊢_v`. -/
theorem exists_isRes (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (hc : v ∈ D.VBad → PivCountable D v) (ht : TauLift D v)
    (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) : ∃ b, IsRes a b := by
  obtain ⟨h, rfl⟩ := FrobCat.IsoClass.mk_surjective a
  obtain ⟨σ, ⟨β⟩⟩ := orbitIsoRecon_piv D v hc h.D
  obtain ⟨ψ, hψ, hψℓ, hτ⟩ := ht σ
  obtain ⟨σ', hσ'⟩ := exists_descend_piv D v hΔ h3 σ
  have hψ' : ∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)),
      psiMul D v ψ (g • m) = σ' g • psiMul D v ψ m := by
    intro g m
    obtain ⟨π, rfl⟩ := h3.1 g
    rw [← hσ' π]
    exact hψ π m
  exact ⟨_, σ, ψ, hψ, hψℓ, σ', hσ', hψ', hτ,
    FrobCat.IsoClass.toD_injective (cvFrob_autRigid D v h3.1) (CatIsom.mk_eq_mk.2 ⟨β⟩), rfl⟩

/-- **Uniqueness of the restriction** (up to 2-isomorphism): two descriptions of the same
automorphism class of `C_v` differ by an inner automorphism of `Π_v`
(`OrbitObj.exists_conj_of_natTrans`), the lifts to `\bar{ℚ}_p^×` by its action (`KummerRigid`),
hence the restrictions by an inner automorphism of `G_v` (`GaloisModel.rel_isoOfSub_conj`). -/
theorem isRes_unique (h3 : PiToGQuotient D v)
    {a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)}
    {b b' : SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v)} (hb : IsRes a b)
    (hb' : IsRes a b') : b = b' := by
  obtain ⟨σ, ψ, hψ, hψℓ, σ', hσ', hψ', hτ, rfl, rfl⟩ := hb
  obtain ⟨σ₂, ψ₂, hψ₂, hψℓ₂, σ₂', hσ₂', hψ₂', hτ₂, ha, rfl⟩ := hb'
  obtain ⟨⟨α, β, -, -⟩⟩ := FrobCat.IsoClass.mk_eq_mk.1 ha
  obtain ⟨ht2, hons, hcpl⟩ := piv_conjData D v
  haveI := ht2
  obtain ⟨g, hg⟩ := OrbitObj.exists_conj_of_natTrans σ σ₂ β.hom hons hcpl
  -- `ψ₂ = g⁻¹ • ψ`
  have hψg : ∀ m, ψ₂ m = g⁻¹ • ψ m := by
    let θ : PiMul D v ≃+ PiMul D v :=
      (ψ₂.trans (DistribMulAction.toAddEquiv (PiMul D v) g)).trans ψ.symm
    have hsymm : ∀ (π : (Piv D v).carrier) (x : PiMul D v), ψ.symm (σ π • x) = π • ψ.symm x :=
      fun π x => by
        apply ψ.injective
        rw [hψ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have hθ : ∀ (π : (Piv D v).carrier) (m : PiMul D v), θ (π • m) = π • θ m := fun π m => by
      change ψ.symm (g • ψ₂ (π • m)) = π • ψ.symm (g • ψ₂ m)
      rw [hψ₂, hg, ← hsymm]
      congr 1
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    have hθℓ : ∀ m, ordPi D v (θ m) = 1 * ordPi D v m := fun m => by
      change ordPi D v (ψ.symm (g • ψ₂ m)) = 1 * ordPi D v m
      rw [one_mul, ← hψℓ, AddEquiv.apply_symm_apply, ordPi_smul, hψℓ₂]
    have h1 := kummerRigid D v h3.1 θ hθ 1 one_pos hθℓ
    intro m
    have h2 : θ m = m := by rw [h1]; rfl
    change ψ.symm (g • ψ₂ m) = m at h2
    have h4 : ψ m = g • ψ₂ m := by
      have := congrArg ψ h2
      rw [AddEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h4, inv_smul_smul]
  have hσg : ∀ x, σ₂' x = (piToG D v g)⁻¹ * σ' x * piToG D v g := fun x => by
    obtain ⟨π, rfl⟩ := h3.1 x
    rw [← hσ₂' π, ← hσ' π, hg, map_mul, map_mul, map_inv]
  refine SplitFrobCat.IsoClass.mk_eq_mk.2 ?_
  exact GaloisModel.rel_isoOfSub_conj (PAdicGalois.ord_smul (pv D v) (Lv D v)) σ' _ _
    (ell_subRes _ (psiMul D v ψ) hψℓ) σ₂' _ _ (ell_subRes _ (psiMul D v ψ₂) hψℓ₂)
    (piToG D v g) hσg
    (fun m => (hψg (m : PAdicGalois.Mul (pv D v))).trans (by rw [piMul_smul, map_inv]; rfl))

/-- **The restriction is compatible with composition.** -/
theorem isRes_trans (h3 : PiToGQuotient D v)
    {a a' : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)}
    {b b' : SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v)} (hb : IsRes a b)
    (hb' : IsRes a' b') : IsRes (a.trans a') (b.trans b') := by
  obtain ⟨σ, ψ, hψ, hψℓ, σ', hσ', hψ', hτ, rfl, rfl⟩ := hb
  obtain ⟨σ₂, ψ₂, hψ₂, hψℓ₂, σ₂', hσ₂', hψ₂', hτ₂, rfl, rfl⟩ := hb'
  have h12 : ∀ (g : (Piv D v).carrier) (m : PiMul D v),
      (ψ.trans ψ₂) (g • m) = (σ.trans σ₂) g • (ψ.trans ψ₂) m := fun g m => by
    change ψ₂ (ψ (g • m)) = σ₂ (σ g) • ψ₂ (ψ m)
    rw [hψ, hψ₂]
  have hℓ12 : ∀ m, ordPi D v ((ψ.trans ψ₂) m) = ordPi D v m := fun m => by
    change ordPi D v (ψ₂ (ψ m)) = _
    rw [hψℓ₂, hψℓ]
  have hσ12 : ∀ g, piToG D v ((σ.trans σ₂) g) = (σ'.trans σ₂') (piToG D v g) := fun g => by
    change piToG D v (σ₂ (σ g)) = σ₂' (σ' (piToG D v g))
    rw [hσ₂', hσ']
  have h12' : ∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)),
      psiMul D v (ψ.trans ψ₂) (g • m) = (σ'.trans σ₂') g • psiMul D v (ψ.trans ψ₂) m :=
    fun g m => by
      change psiMul D v ψ₂ (psiMul D v ψ (g • m)) = σ₂' (σ' g) • psiMul D v ψ₂ (psiMul D v ψ m)
      rw [hψ', hψ₂']
  have hτ12 : psiMul D v (ψ.trans ψ₂) (tauElt D v) ∈ tauOrbit D v :=
    GaloisModel.map_mem_orbitGen (σ₂' : Gv D v ≃* Gv D v) (psiMul D v ψ₂) hψ₂' hτ₂ hτ
  refine ⟨σ.trans σ₂, ψ.trans ψ₂, h12, hℓ12, σ'.trans σ₂', hσ12, h12', hτ12,
    cv_mk_isoOf_trans h3 σ σ₂ ψ ψ₂ hψ hψℓ hψ₂ hψℓ₂ h12 hℓ12, ?_⟩
  refine SplitFrobCat.IsoClass.mk_eq_mk.2 ?_
  exact GaloisModel.rel_isoOfSub_trans (PAdicGalois.ord_smul (pv D v) (Lv D v))
    (PAdicGalois.ord_smul (pv D v) (Lv D v)) σ' _ _ (ell_subRes _ (psiMul D v ψ) hψℓ) σ₂' _ _
    (ell_subRes _ (psiMul D v ψ₂) hψℓ₂) _ (fun m => (hψℓ₂ _).trans (hψℓ _))

variable (D v)

/-- The inputs of the restriction `Aut(F_v) → Aut(F^⊢_v)`: `DeltaCharacteristic`, H3,
`PivCountable` at `V^bad`, and `TauLift` (from `PFixedLift` at `V^good`, `resInputs_of_good`; a
named input at `V^bad`). -/
def ResInputs : Prop :=
  DeltaCharacteristic D v ∧ PiToGQuotient D v ∧ (v ∈ D.VBad → PivCountable D v) ∧ TauLift D v

/-- The inputs at `v ∈ V^good`. -/
theorem resInputs_of_good (hv : v ∉ D.VBad) (hΔ : DeltaCharacteristic D v)
    (h3 : PiToGQuotient D v) (hp : PFixedLift D v) : ResInputs D v :=
  ⟨hΔ, h3, fun h => absurd h hv, tauLift_of_pFixedLift D v hv hp⟩

variable {D v}

/-- **The restriction `Aut(F_v) → Aut(F^⊢_v)` on isomorphism classes** (IUT I, Example 3.3
(iii)(d), (e): `C^⊢_v ⊆ C_v` and `τ^⊢_v` are reconstructed from `F_v`, so automorphisms of `F_v`
restrict to `F^⊢_v`). -/
def vdashRes (h : ResInputs D v) (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) :
    SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v) :=
  Classical.choose (exists_isRes h.1 h.2.1 h.2.2.1 h.2.2.2 a)

theorem vdashRes_isRes (h : ResInputs D v) (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) :
    IsRes a (vdashRes h a) :=
  Classical.choose_spec (exists_isRes h.1 h.2.1 h.2.2.1 h.2.2.2 a)

/-- The restriction of the class of `isoOf σ ψ` (with `ψ` fixing `p`) is the class of
`resIso σ̄ ψ` for the descent `σ̄` of `σ`. -/
theorem vdashRes_eq (h : ResInputs D v) {a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)}
    {b : SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v)} (hb : IsRes a b) :
    vdashRes h a = b :=
  isRes_unique h.2.1 (vdashRes_isRes h a) hb

/-- **Functoriality**: the restriction is compatible with composition. -/
theorem vdashRes_trans (h : ResInputs D v) (a a' : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) :
    vdashRes h (a.trans a') = (vdashRes h a).trans (vdashRes h a') :=
  vdashRes_eq h (isRes_trans h.2.1 (vdashRes_isRes h a) (vdashRes_isRes h a'))

/-- **Functoriality**: the restriction maps the identity to the identity. -/
theorem vdashRes_refl (h : ResInputs D v) :
    vdashRes h (FrobCat.IsoClass.refl (cvFrob D v)) =
      SplitFrobCat.IsoClass.refl (fVdashModel D v) :=
  SplitFrobCat.IsoClass.eq_refl_of_trans_self (by
    rw [← vdashRes_trans, FrobCat.IsoClass.refl_trans])

/-- **Compatibility with `D ↦ D^⊢`**: the class of `a` in `Aut(D_v)` is that of
`Π_v/H ↦ Π_v/σ(H)`, and the class of its restriction in `Aut(D^⊢_v)` that of
`G_v/H ↦ G_v/σ̄(H)` for the descent `σ̄` of `σ` to `G_v`. -/
theorem vdashRes_toD (h : ResInputs D v) (a : FrobCat.IsoClass (cvFrob D v) (cvFrob D v)) :
    ∃ (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) (σ' : Gv D v ≃ₜ* Gv D v),
      (∀ g, piToG D v (σ g) = σ' (piToG D v g)) ∧
        a.toD = CatIsom.mk (OrbitObj.equivOfIso σ) ∧
          (vdashRes h a).toD = CatIsom.mk (OrbitObj.equivOfIso σ') := by
  obtain ⟨σ, ψ, hψ, hψℓ, σ', hσ', hψ', hτ, ha, hb⟩ := vdashRes_isRes h a
  exact ⟨σ, σ', hσ', by rw [ha]; rfl, by rw [hb]; rfl⟩

end Main

end PrimeStrip

end Multiradial

end Iut

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section Comp

variable {D : InitialThetaData.{0}} {v : FinitePlace ↥(fieldOfModuli D.F D.E)}

lemma FrobCat.IsoClass.trans_symm_trans {X Y Z : FrobCat} (a : FrobCat.IsoClass X Y)
    (b : FrobCat.IsoClass X Z) : a.trans (a.symm.trans b) = b := by
  rw [← FrobCat.IsoClass.trans_assoc, FrobCat.IsoClass.trans_symm, FrobCat.IsoClass.refl_trans]

/-- A chosen isomorphism of a constituent `‡F_v` with the model `C_v`. -/
def FComp.model (X : FComp D v) : X.F.Iso (cvFrob D v) := Classical.choice X.equiv_model

/-- **`F ↦ F^⊢` on isomorphisms of constituents at `v ∈ V^non`** (IUT I, Example 3.3 (iii)(d),
(e); Remark 5.2.1 (ii)): the class of an isomorphism `‡F_v ≅ ‡F'_v`, transported to an
automorphism class of the model `C_v` and restricted to `F^⊢_v` (`vdashRes`). Up to isomorphism
the mono-analyticisation of every constituent is the model `F^⊢_v`; what the algorithm carries
is the action on isomorphisms (IUT I, Remark 3.2.1 (i), l.4784: "reconstructed
category-theoretically" is preservation by equivalences). -/
def FComp.vdashClass (h : ResInputs D v) {X Y : FComp D v} (a : FrobCat.IsoClass X.F Y.F) :
    SplitFrobCat.IsoClass (fVdashModel D v) (fVdashModel D v) :=
  vdashRes h (((FrobCat.IsoClass.mk X.model).symm.trans a).trans (FrobCat.IsoClass.mk Y.model))

/-- **Functoriality of `F ↦ F^⊢`**: composites. -/
theorem FComp.vdashClass_trans (h : ResInputs D v) {X Y Z : FComp D v}
    (a : FrobCat.IsoClass X.F Y.F) (b : FrobCat.IsoClass Y.F Z.F) :
    FComp.vdashClass h (a.trans b) = (FComp.vdashClass h a).trans (FComp.vdashClass h b) := by
  simp only [FComp.vdashClass]
  rw [← vdashRes_trans]
  congr 1
  simp only [FrobCat.IsoClass.trans_assoc, FrobCat.IsoClass.trans_symm_trans]

/-- **Functoriality of `F ↦ F^⊢`**: identities. -/
theorem FComp.vdashClass_refl (h : ResInputs D v) (X : FComp D v) :
    FComp.vdashClass h (FrobCat.IsoClass.refl X.F) = SplitFrobCat.IsoClass.refl _ := by
  simp only [FComp.vdashClass]
  rw [FrobCat.IsoClass.trans_refl, FrobCat.IsoClass.symm_trans, vdashRes_refl]

end Comp

end PrimeStrip

end Multiradial

end Iut
