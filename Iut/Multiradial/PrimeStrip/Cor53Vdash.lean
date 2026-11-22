/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.AutRigid
import Iut.Multiradial.PrimeStrip.OrbitIsoRecon
import Iut.Multiradial.PrimeStrip.FRlfBlack
import Iut.Multiradial.PrimeStrip.KummerLiftPf

/-!
# IUT I, Corollary 5.3 (iii) at `V^non`: surjectivity for `F^⊢`-prime-strips (MR21 R5)

IUT I, Corollary 5.3 (iii) (l.9895–9898 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): for `F^⊢`-prime-strips
`¹F^⊢`, `²F^⊢` with associated `D^⊢`-prime-strips, the natural map
`Isom(¹F^⊢, ²F^⊢) → Isom(¹D^⊢, ²D^⊢)` is surjective. The proof (l.9937–9940) cites
[AbsTopIII], Proposition 5.8 (ii), (v) (`Topics in Absolute Anabelian Geometry III.txt`
l.9044–9057: a functorial — relative to `TG^⊢` — group-theoretic algorithm `G ↦ Γ^×_non(G)`
constructing `O^×_{\bar{k}}(G) → \bar{k}^×(G)`, `k^∼(G) → (\bar{k}^×)^{pf}(G)`).

At `v ∈ V^non` the model `F^⊢_v` is the Galois model Frobenioid over `B(G_v)⁰` with
`Φ = ℤ_{≥0} · ord(τ)` and the splittings `(τ ζ)^ℕ`, `τ = p` resp. `q̲_v` fixed by `G_v`, `ζ = 1`
resp. `ζ ∈ μ_{2l}(K_v)` (the `μ_{2l}`-orbit of IUT I, Example 3.2 (iv); `fVdashModel`). An
isomorphism of split Frobenioids lifting `σ ∈ Aut(G_v)` is induced by a `σ`-equivariant
`ord`-preserving automorphism of `ord⁻¹(ℤ · ord τ) ⊆ \bar{ℚ}_p^×` mapping `τ` into its orbit, e.g.
fixing `τ`; one fixing `τ` is obtained from any `σ`-equivariant `ord`-preserving automorphism
`ψ₀` of `\bar{ℚ}_p^×` (the lift of [AbsTopIII], Proposition 3.2 (iv)) by the correction
`x ↦ ψ₀(x) · u^{-n(x)}`,
`u = ψ₀(τ)/τ ∈ O^×_{K_v}`, `ord(x) = n(x) · ord(τ)` (`exists_subLift`). This file:

* `GaloisModel.isoOfSub σ ψ`: the isomorphism of Galois model Frobenioids from `σ : G ≅ G'` and
  a `σ`-equivariant `ψ : ℓ⁻¹(Γ) ≅ ℓ'⁻¹(Γ)` with `ℓ' ∘ ψ = ℓ` (only the rational functions
  `ℓ⁻¹(Γ)^H` occur); `splitIsoOfSub`: an isomorphism of split Frobenioids (with the
  `μ_n`-orbits of splittings `splitGal π n`) if `ψ(π) ∈ μ_n · π'` (`mem_orbitGen_sub`);
* `SplitFrobCat.AutLift`, `SplitFrobCat.autLift_of_iso`, `SplitFrobCat.IsoClass.toD_surjective`;
* `splitGal_autLift` (generic) and **`FVdashStripNon.isoClassToD_surjective_of`**: Corollary 5.3
  (iii) at `V^non` from the lifts `ψ₀` of automorphisms of `G_v` (`hlift`), and
  **`FVdashStripNon.isoClassToD_surjective`**: unconditional, with MR9's
  `PAdicGalois.exists_mulLift`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-! ### Isomorphisms of Galois model Frobenioids from isomorphisms of `ℓ⁻¹(Γ)` -/

section SubIso

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M M' : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M'] [DistribMulAction G' M']
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m}
  {ℓ' : M' →+ ℝ} (hℓ' : ∀ (g : G') (m : M'), ℓ' (g • m) = ℓ' m) {Γ : AddSubgroup ℝ}

variable (hℓ) in
/-- The action of `G` on `ℓ⁻¹(Γ)`. -/
def smulSub (g : G) (m : Γ.comap ℓ) : Γ.comap ℓ :=
  ⟨g • (m : M), show ℓ (g • (m : M)) ∈ Γ by rw [hℓ]; exact m.2⟩

variable (σ : G ≃ₜ* G') (ψ : Γ.comap ℓ ≃+ Γ.comap ℓ')
  (hψ : ∀ (g : G) (m : Γ.comap ℓ), (ψ (smulSub hℓ g m) : M') = σ g • (ψ m : M'))
  (hψℓ : ∀ m : Γ.comap ℓ, ℓ' (ψ m) = ℓ m)

omit [IsTopologicalGroup G'] in
include hψ in
lemma mem_fixedSub_mapSub {A : OrbitObj G} (u : (bGal G ℓ hℓ Γ).obj A) :
    (ψ ⟨bval u, (bval_mem u).1⟩ : M') ∈
      fixedSub (preSub G' ℓ' hℓ' Γ) ((OrbitObj.isoFunctor σ).obj A) := by
  refine ⟨(ψ _).2, fun h' hh' => ?_⟩
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
  change σ h • (ψ ⟨bval u, (bval_mem u).1⟩ : M') = ψ ⟨bval u, (bval_mem u).1⟩
  rw [← hψ]
  exact congrArg (fun m => ((ψ m : Γ.comap ℓ') : M')) (Subtype.ext ((bval_mem u).2 h hh))

/-- A rational function as an element of `ℓ⁻¹(Γ)`. -/
def toSub {A : OrbitObj G} (u : (bGal G ℓ hℓ Γ).obj A) : Γ.comap ℓ := ⟨bval u, (bval_mem u).1⟩

lemma toSub_zero {A : OrbitObj G} : toSub (0 : (bGal G ℓ hℓ Γ).obj A) = 0 := rfl

lemma toSub_add {A : OrbitObj G} (u v : (bGal G ℓ hℓ Γ).obj A) :
    toSub (u + v) = toSub u + toSub v := rfl

/-- The map of rational functions `(ℓ⁻¹Γ)^H → (ℓ'⁻¹Γ)^{σ(H)}`, `u ↦ ψ(u)`. -/
def bMapSub (A : OrbitObj G) :
    (bGal G ℓ hℓ Γ).obj A →+ (bGal G' ℓ' hℓ' Γ).obj ((OrbitObj.isoFunctor σ).obj A) where
  toFun u := bmk _ (mem_fixedSub_mapSub hℓ' σ ψ hψ u)
  map_zero' := bval_injective (show ((ψ (toSub (0 : (bGal G ℓ hℓ Γ).obj A)) : Γ.comap ℓ') : M') = 0
    by rw [toSub_zero, map_zero]; rfl)
  map_add' u v := bval_injective (show ((ψ (toSub (u + v)) : Γ.comap ℓ') : M') =
    (ψ (toSub u) : M') + (ψ (toSub v) : M') by rw [toSub_add, map_add]; rfl)

lemma bval_bMapSub (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) :
    bval (bMapSub hℓ' σ ψ hψ A u) = (ψ ⟨bval u, (bval_mem u).1⟩ : M') := rfl

lemma bMapSub_pb {A A' : OrbitObj G} (f : A ⟶ A') (u : (bGal G ℓ hℓ Γ).obj A') :
    bMapSub hℓ' σ ψ hψ A ((bGal G ℓ hℓ Γ).pb f u) =
      (bGal G' ℓ' hℓ' Γ).pb ((OrbitObj.isoFunctor σ).map f) (bMapSub hℓ' σ ψ hψ A' u) := by
  obtain ⟨b, hb, he⟩ := OrbitHom.rep_map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ) f
  apply bval_injective
  change (ψ (smulSub hℓ (OrbitHom.rep f) ⟨bval u, (bval_mem u).1⟩) : M') =
    OrbitHom.rep (OrbitHom.map _ _ f) • (ψ ⟨bval u, (bval_mem u).1⟩ : M')
  rw [he, mul_smul, show b • (ψ ⟨bval u, (bval_mem u).1⟩ : M') = ψ ⟨bval u, (bval_mem u).1⟩ from
    (bval_mem (bMapSub hℓ' σ ψ hψ A' u)).2 b hb]
  exact hψ _ _

include hψℓ in
lemma bMapSub_div (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) :
    (divGal G' ℓ' hℓ' Γ).app _ (bMapSub hℓ' σ ψ hψ A u) = (divGal G ℓ hℓ Γ).app A u :=
  Subtype.ext (hψℓ _)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψ in
lemma symm_smulSub (g : G') (m : Γ.comap ℓ') :
    (ψ.symm (smulSub hℓ' g m) : M) = σ.symm g • (ψ.symm m : M) := by
  have h : ψ.symm (smulSub hℓ' g m) = smulSub hℓ (σ.symm g) (ψ.symm m) := by
    apply ψ.injective
    apply Subtype.ext
    rw [AddEquiv.apply_symm_apply, hψ, AddEquiv.apply_symm_apply,
      ContinuousMulEquiv.apply_symm_apply]
    rfl
  rw [h]
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψℓ in
lemma symm_ellSub (m : Γ.comap ℓ') : ℓ (ψ.symm m) = ℓ' m := by
  rw [← hψℓ, AddEquiv.apply_symm_apply]

/-- **The isomorphism of Galois model Frobenioids induced by `σ : G ≅ G'` and a `σ`-equivariant
`ψ : ℓ⁻¹(Γ) ≅ ℓ'⁻¹(Γ)` with `ℓ' ∘ ψ = ℓ`** (base equivalence along `σ`, identity on `Φ`). -/
def GaloisModel.isoOfSub :
    (galFrob G ℓ hℓ Γ).Iso (galFrob G' ℓ' hℓ' Γ) :=
  FrobCat.Iso.ofTransport (OrbitObj.equivOfIso σ) (fun _ => AddEquiv.refl Γ)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (bMapSub hℓ' σ ψ hψ)
    (fun f u => bMapSub_pb hℓ' σ ψ hψ f u) (fun A u => bMapSub_div hℓ' σ ψ hψ hψℓ A u)
    (fun _ => AddEquiv.refl Γ) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (bMapSub hℓ σ.symm ψ.symm (symm_smulSub hℓ' σ ψ hψ))
    (fun f u => bMapSub_pb hℓ σ.symm ψ.symm (symm_smulSub hℓ' σ ψ hψ) f u)
    (fun A u => bMapSub_div hℓ σ.symm ψ.symm (symm_smulSub hℓ' σ ψ hψ) (symm_ellSub ψ hψℓ) A u)
    (fun _ _ => rfl)
    (fun A _ => GaloisModel.pb_eq_of_mk_one _ (OrbitObj.isoUnitApp_mk σ A 1) _ _
      (congrArg Subtype.val (ψ.symm_apply_apply _)))
    (fun _ _ => rfl)
    (fun A _ => GaloisModel.pb_eq_of_mk_one _ (OrbitObj.isoUnitApp_mk σ.symm A 1) _ _
      (congrArg Subtype.val (ψ.apply_symm_apply _)))

lemma GaloisModel.isoOfSub_D :
    (GaloisModel.isoOfSub hℓ' σ ψ hψ hψℓ).D = OrbitObj.equivOfIso σ := rfl

/-! ### Splittings `π^ℕ` -/

variable (G ℓ hℓ Γ) in
/-- **The Galois model Frobenioid with the `μ_n`-orbit of splittings `(π + ζ)^ℕ`**
(`GaloisModel.orbitGen`; for `n = 1` the single splitting `π^ℕ`). -/
abbrev splitGal (π : M) (n : ℕ) : SplitFrobCat :=
  ⟨galFrob G ℓ hℓ Γ, Model.orbitSplitEnd (GaloisModel.piSplit ℓ hℓ Γ) (GaloisModel.orbitGen G π n)⟩

omit [IsTopologicalGroup G] in
/-- An `n`-torsion element has `ℓ = 0`. -/
lemma ell_eq_zero_of_nsmul {n : ℕ} (hn : n ≠ 0) {ζ : M} (hζ : n • ζ = 0) : ℓ ζ = 0 := by
  have h : (n : ℝ) * ℓ ζ = 0 := by rw [← nsmul_eq_mul, ← map_nsmul, hζ, map_zero]
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψ in
/-- **`ψ` maps the `μ_n`-orbit of `π` into that of `π'`** if it maps `π` into it. -/
lemma mem_orbitGen_sub {π : M} {π' : M'} {n : ℕ} (hn : n ≠ 0) (hπΓ : ℓ π ∈ Γ)
    (hπ : (ψ ⟨π, hπΓ⟩ : M') ∈ GaloisModel.orbitGen G' π' n) {x : M}
    (hx : x ∈ GaloisModel.orbitGen G π n) :
    ∃ hxΓ : ℓ x ∈ Γ, (ψ ⟨x, hxΓ⟩ : M') ∈ GaloisModel.orbitGen G' π' n := by
  obtain ⟨ζ, hζ, hnζ, rfl⟩ := hx
  have hℓζ : ℓ ζ = 0 := ell_eq_zero_of_nsmul hn hnζ
  have hζΓ : ζ ∈ Γ.comap ℓ := show ℓ ζ ∈ Γ by rw [hℓζ]; exact Γ.zero_mem
  have hxΓ : ℓ (π + ζ) ∈ Γ := by rw [map_add, hℓζ, add_zero]; exact hπΓ
  refine ⟨hxΓ, ?_⟩
  obtain ⟨ζ₀, hζ₀, hnζ₀, h0⟩ := hπ
  have hsplit : (⟨π + ζ, hxΓ⟩ : Γ.comap ℓ) = ⟨π, hπΓ⟩ + ⟨ζ, hζΓ⟩ := rfl
  refine ⟨ζ₀ + (ψ ⟨ζ, hζΓ⟩ : M'), fun g' => ?_, ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := σ.toMulEquiv.surjective g'
    have hfix : smulSub hℓ g ⟨ζ, hζΓ⟩ = ⟨ζ, hζΓ⟩ := Subtype.ext (hζ g)
    change σ g • (ζ₀ + (ψ ⟨ζ, hζΓ⟩ : M')) = ζ₀ + (ψ ⟨ζ, hζΓ⟩ : M')
    rw [smul_add, hζ₀, ← hψ, hfix]
  · have h1 : n • (⟨ζ, hζΓ⟩ : Γ.comap ℓ) = 0 := Subtype.ext hnζ
    have h2 : n • ψ ⟨ζ, hζΓ⟩ = 0 := by rw [← map_nsmul, h1, map_zero]
    rw [nsmul_add, hnζ₀, zero_add]
    exact congrArg Subtype.val h2
  · rw [hsplit, map_add, AddSubgroup.coe_add, h0, add_assoc]

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψ hℓ' in
/-- If `ψ(π) ∈ μ_n · π'`, then `ψ⁻¹(π') ∈ μ_n · π`. -/
lemma symm_mem_orbitGen_sub {π : M} {π' : M'} {n : ℕ} (hn : n ≠ 0) (hπΓ : ℓ π ∈ Γ)
    (hπ'Γ : ℓ' π' ∈ Γ) (hπ : (ψ ⟨π, hπΓ⟩ : M') ∈ GaloisModel.orbitGen G' π' n) :
    (ψ.symm ⟨π', hπ'Γ⟩ : M) ∈ GaloisModel.orbitGen G π n := by
  obtain ⟨ζ₀, hζ₀, hnζ₀, h0⟩ := hπ
  have hζ₀Γ : ζ₀ ∈ Γ.comap ℓ' :=
    show ℓ' ζ₀ ∈ Γ by rw [ell_eq_zero_of_nsmul hn hnζ₀]; exact Γ.zero_mem
  have hsplit : (⟨π', hπ'Γ⟩ : Γ.comap ℓ') = ψ ⟨π, hπΓ⟩ - ⟨ζ₀, hζ₀Γ⟩ :=
    Subtype.ext (by rw [AddSubgroup.coe_sub, h0]; simp)
  refine ⟨-(ψ.symm ⟨ζ₀, hζ₀Γ⟩ : M), fun g => ?_, ?_, ?_⟩
  · have hfix : smulSub hℓ' (σ g) ⟨ζ₀, hζ₀Γ⟩ = ⟨ζ₀, hζ₀Γ⟩ := Subtype.ext (hζ₀ (σ g))
    have h := symm_smulSub hℓ' σ ψ hψ (σ g) ⟨ζ₀, hζ₀Γ⟩
    rw [hfix, ContinuousMulEquiv.symm_apply_apply] at h
    rw [smul_neg, ← h]
  · have h1 : n • (⟨ζ₀, hζ₀Γ⟩ : Γ.comap ℓ') = 0 := Subtype.ext hnζ₀
    have h2 : n • ψ.symm ⟨ζ₀, hζ₀Γ⟩ = 0 := by rw [← map_nsmul, h1, map_zero]
    rw [smul_neg, neg_eq_zero]
    exact congrArg Subtype.val h2
  · rw [hsplit, map_sub, AddEquiv.symm_apply_apply, AddSubgroup.coe_sub, sub_eq_add_neg]

/-- The transport functor of model Frobenioids preserves the endomorphisms `(1, id, ·, u)` with
`u ∈ π^ℕ` if `ψ(π) = π'`. -/
lemma map_splitEnd_sub {π : M} {π' : M'} (hπΓ : ℓ π ∈ Γ)
    (hπ : (ψ ⟨π, hπΓ⟩ : M') = π') (X : GaloisModel G ℓ hℓ Γ) (e : X ⟶ X)
    (he : e ∈ Model.splitEnd (GaloisModel.piSplit ℓ hℓ Γ π) X) :
    (GaloisModel.isoOfSub hℓ' σ ψ hψ hψℓ).C.functor.map e ∈
      Model.splitEnd (GaloisModel.piSplit ℓ' hℓ' Γ π')
        ((GaloisModel.isoOfSub hℓ' σ ψ hψ hψℓ).C.functor.obj X) := by
  obtain ⟨⟨hb, hd⟩, n, hn⟩ := he
  have hb' : e.base = 𝟙 _ := hb
  refine Set.mem_setOf.mpr ⟨⟨?_, hd⟩, n, ?_⟩
  · change (OrbitObj.isoFunctor σ).map e.base = 𝟙 _
    rw [hb', CategoryTheory.Functor.map_id]
  · change (ψ ⟨bval e.u, (bval_mem e.u).1⟩ : M') = n • π'
    have h1 : (⟨bval e.u, (bval_mem e.u).1⟩ : Γ.comap ℓ) = n • ⟨π, hπΓ⟩ :=
      Subtype.ext hn
    rw [h1, map_nsmul, AddSubgroup.coe_nsmul, hπ]

/-- **The isomorphism of split Galois model Frobenioids** from `σ`, `ψ` with
`ψ(π) ∈ μ_n · π'`: it maps the `μ_n`-orbit of splittings `(π + ζ)^ℕ` onto that of `π'`. -/
def GaloisModel.splitIsoOfSub {π : M} {π' : M'} {n : ℕ} (hn : n ≠ 0) (hπΓ : ℓ π ∈ Γ)
    (hπ'Γ : ℓ' π' ∈ Γ) (hπ : (ψ ⟨π, hπΓ⟩ : M') ∈ GaloisModel.orbitGen G' π' n) :
    (splitGal G ℓ hℓ Γ π n).Iso (splitGal G' ℓ' hℓ' Γ π' n) where
  iso := GaloisModel.isoOfSub hℓ' σ ψ hψ hψℓ
  map_tau := by
    rintro s ⟨x, hx, rfl⟩
    obtain ⟨hxΓ, hx'⟩ := mem_orbitGen_sub σ ψ hψ hn hπΓ hπ hx
    exact ⟨_, ⟨_, hx', rfl⟩, map_splitEnd_sub hℓ' σ ψ hψ hψℓ hxΓ rfl⟩
  inv_tau := by
    rintro s ⟨x, hx, rfl⟩
    obtain ⟨hxΓ, hx'⟩ := mem_orbitGen_sub σ.symm ψ.symm (symm_smulSub hℓ' σ ψ hψ) hn hπ'Γ
      (symm_mem_orbitGen_sub hℓ' σ ψ hψ hn hπΓ hπ'Γ hπ) hx
    exact ⟨_, ⟨_, hx', rfl⟩, map_splitEnd_sub hℓ σ.symm ψ.symm (symm_smulSub hℓ' σ ψ hψ)
      (symm_ellSub ψ hψℓ) hxΓ rfl⟩

end SubIso

/-! ### `ψ` fixing `π` from any lift -/

section Correction

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [DistribMulAction G M]
  {ℓ : M →+ ℝ} (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m) {π : M}

/-- The integer `n` with `ℓ(x) = n · ℓ(π)`, for `x ∈ ℓ⁻¹(ℤ · ℓ(π))`. -/
def nOf (x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) : ℤ :=
  (AddSubgroup.mem_zmultiples_iff.mp (x.2 : ℓ (x : M) ∈ AddSubgroup.zmultiples (ℓ π))).choose

lemma nOf_spec (x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) :
    (nOf x : ℝ) * ℓ π = ℓ x := by
  rw [← zsmul_eq_mul]
  exact (AddSubgroup.mem_zmultiples_iff.mp
    (x.2 : ℓ (x : M) ∈ AddSubgroup.zmultiples (ℓ π))).choose_spec

lemma nOf_unique (hπ0 : ℓ π ≠ 0) {x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ} {k : ℤ}
    (hk : (k : ℝ) * ℓ π = ℓ x) : nOf x = k := by
  have h := (nOf_spec x).trans hk.symm
  exact_mod_cast mul_right_cancel₀ hπ0 h

lemma nOf_add (hπ0 : ℓ π ≠ 0) (x y : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) :
    nOf (x + y) = nOf x + nOf y :=
  nOf_unique hπ0 (by
    push_cast
    rw [add_mul, nOf_spec, nOf_spec]
    exact (map_add ℓ _ _).symm)

lemma nOf_of_eq (hπ0 : ℓ π ≠ 0) {x y : (AddSubgroup.zmultiples (ℓ π)).comap ℓ}
    (h : ℓ x = ℓ y) : nOf x = nOf y :=
  nOf_unique hπ0 ((nOf_spec y).trans h.symm)

/-- The corrected map `x ↦ ψ₀(x) − n(x) · (ψ₀(π) − π)` on `ℓ⁻¹(ℤ · ℓ(π))`. -/
def corrFun (ψ₀ : M ≃+ M) (hψ₀ℓ : ∀ m, ℓ (ψ₀ m) = ℓ m)
    (x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) : (AddSubgroup.zmultiples (ℓ π)).comap ℓ :=
  ⟨ψ₀ x - nOf x • (ψ₀ π - π), by
    change ℓ (ψ₀ x - nOf x • (ψ₀ π - π)) ∈ AddSubgroup.zmultiples (ℓ π)
    rw [map_sub, map_zsmul, map_sub, hψ₀ℓ, hψ₀ℓ, sub_self, smul_zero, sub_zero]
    exact x.2⟩

lemma ell_corrFun (ψ₀ : M ≃+ M) (hψ₀ℓ : ∀ m, ℓ (ψ₀ m) = ℓ m)
    (x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) : ℓ (corrFun ψ₀ hψ₀ℓ x) = ℓ x := by
  change ℓ (ψ₀ x - nOf x • (ψ₀ π - π)) = _
  rw [map_sub, map_zsmul, map_sub, hψ₀ℓ, hψ₀ℓ, sub_self, smul_zero, sub_zero]

lemma corrFun_corrFun (hπ0 : ℓ π ≠ 0) (ψ₀ : M ≃+ M) (hψ₀ℓ : ∀ m, ℓ (ψ₀ m) = ℓ m)
    (hψ₀ℓ' : ∀ m, ℓ (ψ₀.symm m) = ℓ m) (x : (AddSubgroup.zmultiples (ℓ π)).comap ℓ) :
    corrFun ψ₀.symm hψ₀ℓ' (corrFun ψ₀ hψ₀ℓ x) = x := by
  have hn : nOf (corrFun ψ₀ hψ₀ℓ x) = nOf x := nOf_of_eq hπ0 (ell_corrFun ψ₀ hψ₀ℓ x)
  apply Subtype.ext
  change ψ₀.symm (ψ₀ x - nOf x • (ψ₀ π - π)) - nOf (corrFun ψ₀ hψ₀ℓ x) • (ψ₀.symm π - π) = x
  rw [hn, map_sub, map_zsmul, map_sub, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    smul_sub, smul_sub]
  abel

variable (σ : G ≃* G) (hπfix : ∀ g : G, g • π = π)

include hπfix in
/-- **A lift fixing `π`**: from a `σ`-equivariant `ℓ`-preserving automorphism `ψ₀` of `M`, a
`σ`-equivariant `ℓ`-preserving automorphism of `ℓ⁻¹(ℤ · ℓ(π))` fixing `π`. -/
theorem exists_subLift (hπ0 : ℓ π ≠ 0) (ψ₀ : M ≃+ M)
    (hψ₀ : ∀ (g : G) (m : M), ψ₀ (g • m) = σ g • ψ₀ m) (hψ₀ℓ : ∀ m, ℓ (ψ₀ m) = ℓ m) :
    ∃ ψ : (AddSubgroup.zmultiples (ℓ π)).comap ℓ ≃+ (AddSubgroup.zmultiples (ℓ π)).comap ℓ,
      (∀ (g : G) (m : (AddSubgroup.zmultiples (ℓ π)).comap ℓ),
        (ψ (smulSub hℓ g m) : M) = σ g • (ψ m : M)) ∧
      (∀ m, ℓ (ψ m) = ℓ m) ∧
      ∀ hπΓ : ℓ π ∈ AddSubgroup.zmultiples (ℓ π), (ψ ⟨π, hπΓ⟩ : M) = π := by
  have hψ₀ℓ' : ∀ m, ℓ (ψ₀.symm m) = ℓ m := fun m => by
    rw [← hψ₀ℓ, AddEquiv.apply_symm_apply]
  let ψ : (AddSubgroup.zmultiples (ℓ π)).comap ℓ ≃+ (AddSubgroup.zmultiples (ℓ π)).comap ℓ :=
    { toFun := corrFun ψ₀ hψ₀ℓ
      invFun := corrFun ψ₀.symm hψ₀ℓ'
      left_inv := corrFun_corrFun hπ0 ψ₀ hψ₀ℓ hψ₀ℓ'
      right_inv := fun x => by
        have := corrFun_corrFun hπ0 ψ₀.symm hψ₀ℓ' hψ₀ℓ x
        simpa only [AddEquiv.symm_symm] using this
      map_add' := fun x y => by
        apply Subtype.ext
        change ψ₀ (x + y : M) - nOf (x + y) • (ψ₀ π - π) =
          (ψ₀ x - nOf x • (ψ₀ π - π)) + (ψ₀ y - nOf y • (ψ₀ π - π))
        rw [nOf_add hπ0, map_add, add_zsmul]
        abel }
  have hufix : ∀ g : G, σ g • (ψ₀ π - π) = ψ₀ π - π := fun g => by
    rw [smul_sub, ← hψ₀, hπfix, hπfix]
  refine ⟨ψ, fun g m => ?_, ell_corrFun ψ₀ hψ₀ℓ, fun hπΓ => ?_⟩
  · change ψ₀ (g • (m : M)) - nOf (smulSub hℓ g m) • (ψ₀ π - π) =
      σ g • (ψ₀ m - nOf m • (ψ₀ π - π))
    rw [nOf_of_eq hπ0 (hℓ g m), hψ₀, smul_sub (σ g) (ψ₀ (m : M)) (nOf m • (ψ₀ π - π)),
      smul_comm (σ g) (nOf m) (ψ₀ π - π), hufix]
  · change ψ₀ π - nOf ⟨π, hπΓ⟩ • (ψ₀ π - π) = π
    rw [nOf_unique hπ0 (k := 1) (by simp)]
    abel

end Correction

/-! ### Lifting automorphisms of `D^⊢` -/

namespace SplitFrobCat

/-- **Lifting of automorphisms of the base** for split Frobenioids. -/
def AutLift (X : SplitFrobCat) : Prop :=
  ∀ e : X.F.D ≌ X.F.D, ∃ h : X.Iso X, Nonempty (h.iso.D.functor ≅ e.functor)

/-- `AutLift` is invariant under isomorphism. -/
theorem autLift_of_iso {X Y : SplitFrobCat} (m : X.Iso Y) (hY : AutLift Y) : AutLift X := by
  intro e
  obtain ⟨h, ⟨β⟩⟩ := hY ((m.iso.D.symm.trans e).trans m.iso.D)
  refine ⟨(m.trans h).trans m.symm, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft m.iso.D.functor β) m.iso.D.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight
      m.iso.D.unitIso.symm e.functor) m.iso.D.functor ≪≫
        Functor.isoWhiskerRight (Functor.leftUnitor e.functor) m.iso.D.functor)
      m.iso.D.inverse ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.functor m.iso.D.unitIso.symm ≪≫ Functor.rightUnitor e.functor

/-- **Surjectivity of `F^⊢ ↦ D^⊢` on isomorphism classes from `AutLift`**, when `X ≅ Y`. -/
theorem IsoClass.toD_surjective {X Y : SplitFrobCat} (hX : AutLift X) (m : X.Iso Y) :
    Function.Surjective (IsoClass.toD : IsoClass X Y → CatIsom X.F.D Y.F.D) := by
  intro a
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  obtain ⟨h, ⟨β⟩⟩ := hX (e.trans m.iso.D.symm)
  refine ⟨IsoClass.mk (h.trans m), ?_⟩
  rw [IsoClass.toD_mk]
  refine CatIsom.mk_eq_mk.2 ⟨?_⟩
  exact Functor.isoWhiskerRight β m.iso.D.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.functor m.iso.D.counitIso ≪≫ Functor.rightUnitor e.functor

end SplitFrobCat

section Lift

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M]
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m} {π : M}

/-- **Automorphisms of `B(G)⁰` lift to the split Galois model Frobenioid with `Γ = ℤ · ℓ(π)`**,
from `OrbitIsoRecon G` and `σ`-equivariant `ℓ`-preserving automorphisms of `M` for every
`σ ∈ Aut(G)`. -/
theorem splitGal_autLift {Γ : AddSubgroup ℝ} {n : ℕ} (hn : n ≠ 0)
    (hΓ : Γ = AddSubgroup.zmultiples (ℓ π))
    (hπfix : ∀ g : G, g • π = π) (hπ0 : ℓ π ≠ 0) (hrec : OrbitIsoRecon G)
    (hlift : ∀ σ : G ≃ₜ* G, ∃ ψ₀ : M ≃+ M, (∀ (g : G) (m : M), ψ₀ (g • m) = σ g • ψ₀ m) ∧
      ∀ m, ℓ (ψ₀ m) = ℓ m) :
    (splitGal G ℓ hℓ Γ π n).AutLift := by
  subst hΓ
  intro e
  obtain ⟨σ, ⟨β⟩⟩ := hrec e
  obtain ⟨ψ₀, hψ₀, hψ₀ℓ⟩ := hlift σ
  obtain ⟨ψ, hψ, hψℓ, hψπ⟩ := exists_subLift hℓ (σ : G ≃* G) hπfix hπ0 ψ₀ hψ₀ hψ₀ℓ
  have hπΓ : ℓ π ∈ AddSubgroup.zmultiples (ℓ π) := AddSubgroup.mem_zmultiples _
  exact ⟨GaloisModel.splitIsoOfSub hℓ σ ψ hψ hψℓ hn hπΓ hπΓ
    ((hψπ hπΓ).symm ▸ GaloisModel.self_mem_orbitGen π n), ⟨β.symm⟩⟩

end Lift

/-! ### `F^⊢`-prime-strips -/

section Strips

variable {D : InitialThetaData.{0}}

lemma gammaVdash_eq (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    gammaVdash D v = AddSubgroup.zmultiples (PAdicGalois.ord (pv D v) (tauElt D v)) := by
  by_cases hv : v ∈ D.VBad
  · have hq := qRootExists D v hv
    have hτ : tauElt D v = toMul D v hq.choose := by simp only [tauElt, dif_pos hv]
    have hℓ : (0 : ℝ) < 2 * D.ℓ := by
      have := D.prime.ℓ_prime.pos
      have : (0 : ℝ) < D.ℓ := by exact_mod_cast this
      linarith
    have hord : PAdicGalois.ord (pv D v) (toMul D v hq.choose) =
        PAdicGalois.ord (pv D v) (toMul D v (qv D v hv)) / (2 * D.ℓ) := by
      have hqx : toMul D v (qv D v hv) = (2 * D.ℓ) • toMul D v hq.choose := by
        rw [← toMul_pow]; exact congrArg _ hq.choose_spec.symm
      rw [hqx, map_nsmul, nsmul_eq_mul, eq_div_iff hℓ.ne']
      push_cast
      ring
    rw [hτ, hord]; simp [gammaVdash, ordTau, hv]
  · have hτ : tauElt D v = pMul D v := by simp only [tauElt, dif_neg hv]
    rw [hτ, ord_pMul]; simp [gammaVdash, ordTau, hv]

/-- **`F^⊢_v` lifts automorphisms of `D^⊢_v = B(G_v)⁰`**, given lifts of the automorphisms of
`G_v` to `\bar{ℚ}_p^×`. -/
theorem fVdashModel_autLift (v : FinitePlace ↥(fieldOfModuli D.F D.E))
    (hlift : ∀ σ : Gv D v ≃ₜ* Gv D v, ∃ ψ₀ : PAdicGalois.Mul (pv D v) ≃+
      PAdicGalois.Mul (pv D v), (∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)),
        ψ₀ (g • m) = σ g • ψ₀ m) ∧ ∀ m, PAdicGalois.ord (pv D v) (ψ₀ m) =
          PAdicGalois.ord (pv D v) m) :
    (fVdashModel D v).AutLift :=
  splitGal_autLift (nOrb_ne_zero D v) (gammaVdash_eq v) (fun σ => tauElt_fixed D v σ)
    (ord_tauElt_pos D v).ne' orbitIsoRecon_of_profinite hlift

/-- **IUT I, Corollary 5.3 (iii), surjectivity** (non-archimedean part), from lifts of the
automorphisms of `G_v` to `\bar{ℚ}_p^×` ([AbsTopIII], Proposition 3.2 (iv); MR9's
`PAdicGalois.exists_mulLift`): `Isom(¹F^⊢, ²F^⊢) → Isom(¹D^⊢, ²D^⊢)` is surjective. -/
theorem FVdashStripNon.isoClassToD_surjective_of
    (hlift : ∀ v : Vnon D, ∀ σ : Gv D v ≃ₜ* Gv D v, ∃ ψ₀ : PAdicGalois.Mul (pv D v) ≃+
      PAdicGalois.Mul (pv D v), (∀ (g : Gv D v) (m : PAdicGalois.Mul (pv D v)),
        ψ₀ (g • m) = σ g • ψ₀ m) ∧ ∀ m, PAdicGalois.ord (pv D v) (ψ₀ m) =
          PAdicGalois.ord (pv D v) m)
    (P Q : FVdashStripNon D) :
    Function.Surjective (FVdashStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) := by
  intro a
  have h : ∀ v, ∃ b : SplitFrobCat.IsoClass (P.comp v).F (Q.comp v).F, b.toD = a v := fun v => by
    obtain ⟨m⟩ := (P.comp v).equiv_model
    obtain ⟨m'⟩ := (Q.comp v).equiv_model
    exact SplitFrobCat.IsoClass.toD_surjective
      (SplitFrobCat.autLift_of_iso m (fVdashModel_autLift v (hlift v))) (m.trans m'.symm) (a v)
  choose b hb using h
  exact ⟨b, funext hb⟩

/-- **IUT I, Corollary 5.3 (iii), surjectivity** (non-archimedean part):
`Isom(¹F^⊢, ²F^⊢) → Isom(¹D^⊢, ²D^⊢)` is surjective, with the lifts of [AbsTopIII],
Proposition 3.2 (iv) from MR9's `PAdicGalois.exists_mulLift`. -/
theorem FVdashStripNon.isoClassToD_surjective (P Q : FVdashStripNon D) :
    Function.Surjective (FVdashStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) :=
  FVdashStripNon.isoClassToD_surjective_of
    (fun v σ => PAdicGalois.exists_mulLift (E := Lv D v) σ) P Q

end Strips

end PrimeStrip

end Multiradial

end Iut
