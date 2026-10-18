/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24ii
import Iut.Frobenioid.UnrPairing

/-!
# `Ψ` on `O^▷` and the Galois action ([FrdII], Theorem 2.4(i), (ii))

[FrdII], Theorem 2.4, proof of (i): `Ψ` "preserves `O^▷(−)`" (`Model.map_mem_orhd`), and (ii): for
fieldwise saturated `Φ_i`, "reconstructing the multiplicative group associated to the field […] as
the groupification of the monoid `O^▷(A_i)`", `Ψ` induces compatible isomorphisms `G₁ ≅ G₂`,
`K̄₁^× ≅ K̄₂^×`. This file provides the Frobenioid-side input on `O^▷` (base-identity linear
endomorphisms) for the `p`-adic Galois-model Frobenioids `GFrob p E Γ`:

* `Model.orhd_comp_u`, `Model.conj_u_orhd`: rational functions of `O^▷` elements are additive
  under composition, and conjugation by an automorphism acts by pull-back along the base;
* `PAdicGalois.rfE e ∈ K̄^×` (the rational function of an endomorphism), `endO` (the element of
  `O^▷(Y)` with given rational function), `rfE_injective_orhd`;
* `OrbitObj.H_eq_of_iso`: isomorphic orbit objects with normal stabilizer have equal stabilizers;
* **`PAdicGalois.exists_galHom_compat_orhd`**: the strengthening of `exists_galHom_compat` to all of
  `O^▷`: `Ψ(galHom σ)` acts on the rational functions of `O^▷(Ψ X)` by `τ α(σ) τ⁻¹`, and the
  base of `Ψ X = Ψ(G_E/N, a)` is `G_{E'}/α(N)`.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

lemma orhd_base {X : Model Φ B divB} {e : X ⟶ X} (he : e ∈ Orhd 𝐏 X) : e.base = 𝟙 _ := he.1

lemma orhd_deg {X : Model Φ B divB} {e : X ⟶ X} (he : e ∈ Orhd 𝐏 X) : e.deg = 1 := he.2

lemma id_mem_orhd (X : Model Φ B divB) : 𝟙 X ∈ Orhd 𝐏 X := ⟨Base_id X, degFr_id X⟩

lemma comp_mem_orhd {X : Model Φ B divB} {e e' : X ⟶ X} (he : e ∈ Orhd 𝐏 X)
    (he' : e' ∈ Orhd 𝐏 X) : e ≫ e' ∈ Orhd 𝐏 X := by
  refine ⟨?_, ?_⟩
  · change (e ≫ e').base = 𝟙 _
    rw [comp_base, orhd_base he, orhd_base he', Category.comp_id]
  · change (e ≫ e').deg = 1
    rw [comp_deg, orhd_deg he, orhd_deg he', mul_one]

/-- `(e ∘ e').u = u_e + u_{e'}` on `O^▷`. -/
lemma orhd_comp_u {X : Model Φ B divB} {e e' : X ⟶ X} (he : e ∈ Orhd 𝐏 X)
    (he' : e' ∈ Orhd 𝐏 X) : (e ≫ e').u = e.u + e'.u := by
  simp only [comp_u, orhd_base he, GrpOn.pb_id', orhd_deg he', PNat.one_coe, one_smul]
  abel

/-- `conj` preserves `O^▷`. -/
lemma conj_mem_orhd {X : Model Φ B divB} (α : X ≅ X) {e : X ⟶ X} (he : e ∈ Orhd 𝐏 X) :
    conj α e ∈ Orhd 𝐏 X := by
  refine ⟨?_, ?_⟩
  · change (α.inv ≫ e ≫ α.hom).base = 𝟙 _
    rw [comp_base, comp_base, orhd_base he, Category.id_comp, iso_base]
  · change (α.inv ≫ e ≫ α.hom).deg = 1
    rw [comp_deg, comp_deg, orhd_deg he, (iso_deg α).1, (iso_deg α).2]
    rfl

/-- **The action of `Aut_C(A)` on `O^▷(A)` is the pull-back along the base of `α⁻¹`.** -/
theorem conj_u_orhd {X : Model Φ B divB} (α : X ≅ X) {e : X ⟶ X} (he : e ∈ Orhd 𝐏 X) :
    (conj α e).u = B.pb α.inv.base e.u := by
  have h1 : (α.inv ≫ α.hom).u = 0 := by rw [α.inv_hom_id]; rfl
  simp only [comp_u, (iso_deg α).1, PNat.one_coe, one_smul] at h1
  change (α.inv ≫ e ≫ α.hom).u = _
  simp only [comp_u, orhd_base he, GrpOn.pb_id', map_add]
  rw [comp_deg, (iso_deg α).1, orhd_deg he, mul_one, PNat.one_coe, one_smul,
    eq_neg_of_add_eq_zero_right h1]
  abel

/-- Functors commute with conjugation. -/
lemma map_conj {D' : Type*} [Category D'] {Φ' : DivMonoid.{w} D'} {B' : GrpOn.{w} D'}
    {divB' : DivHom B' Φ'.toGrpOn} (F : Model Φ B divB ⥤ Model Φ' B' divB')
    {X : Model Φ B divB} (α : X ≅ X) (e : X ⟶ X) :
    F.map (conj α e) = conj (F.mapIso α) (F.map e) := by
  simp [conj]

end Model

namespace OrbitObj

variable {G : Type} [Group G] [TopologicalSpace G]

/-- **Isomorphic orbit objects with normal stabilizer have the same stabilizer.** -/
lemma H_eq_of_iso {A B : OrbitObj G} (θ : A ≅ B) (hB : B.H.Normal) : A.H = B.H := by
  ext h
  constructor
  · intro hh
    have := OrbitHom.conj_mem θ.hom hh
    have e : h = OrbitHom.rep θ.hom * ((OrbitHom.rep θ.hom)⁻¹ * (h * OrbitHom.rep θ.hom)) *
        (OrbitHom.rep θ.hom)⁻¹ := by group
    rw [e]
    exact hB.conj_mem _ this _
  · intro hh
    set r := OrbitHom.rep θ.inv
    have hh' : r * h * r⁻¹ ∈ B.H := hB.conj_mem _ hh _
    have := OrbitHom.conj_mem θ.inv hh'
    have e : r⁻¹ * (r * h * r⁻¹ * r) = h := by group
    rw [e] at this
    exact this

end OrbitObj

namespace GaloisModel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
variable {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m} {Γ : AddSubgroup ℝ}

local notation "𝐏G" => Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)

/-- **Elements of `O^▷` are determined by their rational functions.** -/
lemma orhd_ext {X : GaloisModel G ℓ hℓ Γ} {e e' : X ⟶ X} (he : e ∈ Orhd 𝐏G X)
    (he' : e' ∈ Orhd 𝐏G X) (h : e.u = e'.u) : e = e' := by
  refine Model.hom_ext ((Model.orhd_deg he).trans (Model.orhd_deg he').symm)
    ((Model.orhd_base he).trans (Model.orhd_base he').symm) (Subtype.ext ?_) h
  rw [div_eq_ell e (Model.orhd_base he) (Model.orhd_deg he),
    div_eq_ell e' (Model.orhd_base he') (Model.orhd_deg he'), h]

lemma ell_nonneg_of_orhd {X : GaloisModel G ℓ hℓ Γ} {e : X ⟶ X} (he : e ∈ Orhd 𝐏G X) :
    0 ≤ ℓ e.u.1 := by
  rw [← div_eq_ell e (Model.orhd_base he) (Model.orhd_deg he)]
  exact e.div_mem

/-- The element of `O^▷(X)` with rational function `m` (`ℓ(m) ≥ 0`). -/
noncomputable def endO (X : GaloisModel G ℓ hℓ Γ) (m : (bGal G ℓ hℓ Γ).obj X.base)
    (hm : 0 ≤ ℓ m.1) : X ⟶ X :=
  Model.mk1 (𝟙 _) ⟨ℓ m.1, m.2.1⟩ hm m (by
    change X.α + ⟨ℓ m.1, m.2.1⟩ = X.α + ⟨ℓ m.1, m.2.1⟩; rfl)

lemma endO_mem_orhd (X : GaloisModel G ℓ hℓ Γ) (m : (bGal G ℓ hℓ Γ).obj X.base)
    (hm : 0 ≤ ℓ m.1) : endO X m hm ∈ Orhd 𝐏G X := ⟨rfl, rfl⟩

@[simp] lemma endO_u (X : GaloisModel G ℓ hℓ Γ) (m : (bGal G ℓ hℓ Γ).obj X.base)
    (hm : 0 ≤ ℓ m.1) : (endO X m hm).u = m := rfl

end GaloisModel

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime] {Γ : AddSubgroup ℝ}
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) Γ)
  (bGal (GK p E) (ord p) (ord_smul p E) Γ) (divGal (GK p E) (ord p) (ord_smul p E) Γ)

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) Γ)
  (bGal (GK p E') (ord p) (ord_smul p E') Γ)
  (divGal (GK p E') (ord p) (ord_smul p E') Γ)

/-- **The rational function `γ_e ∈ K̄^×` of an endomorphism `e` of an object of `C(E)`.** -/
noncomputable def rfE {Y : GFrob p E Γ} (e : Y ⟶ Y) : K̄ˣ := (e.u.1).toMul

lemma rfE_comp {Y : GFrob p E Γ} {e e' : Y ⟶ Y} (he : e ∈ Orhd 𝐏E Y) (he' : e' ∈ Orhd 𝐏E Y) :
    rfE (e ≫ e') = rfE e * rfE e' := by
  unfold rfE
  rw [Model.orhd_comp_u he he']
  change Additive.toMul (_ + _) = _
  rw [toMul_add]

lemma rfE_id (Y : GFrob p E Γ) : rfE (𝟙 Y) = 1 := rfl

lemma rfE_conj {Y : GFrob p E Γ} (β : Y ≅ Y) {e : Y ⟶ Y} (he : e ∈ Orhd 𝐏E Y) :
    rfE (Model.conj β e) = OrbitHom.rep β.inv.base • rfE e := by
  unfold rfE
  rw [Model.conj_u_orhd β he]
  rfl

lemma rfE_injective_orhd {Y : GFrob p E Γ} {e e' : Y ⟶ Y} (he : e ∈ Orhd 𝐏E Y)
    (he' : e' ∈ Orhd 𝐏E Y) (h : rfE e = rfE e') : e = e' :=
  GaloisModel.orhd_ext he he' (Subtype.ext (congrArg Additive.ofMul h))

lemma rfE_fixed {Y : GFrob p E Γ} (e : Y ⟶ Y) {h : GK p E} (hh : h ∈ Y.base.H) :
    h • rfE e = rfE e :=
  congrArg Additive.toMul (e.u.2.2 h hh)

lemma ord_rfE_nonneg {Y : GFrob p E Γ} {e : Y ⟶ Y} (he : e ∈ Orhd 𝐏E Y) :
    0 ≤ ord p (Additive.ofMul (rfE e)) :=
  GaloisModel.ell_nonneg_of_orhd he

lemma ord_rfE_mem {Y : GFrob p E Γ} (e : Y ⟶ Y) : ord p (Additive.ofMul (rfE e)) ∈ Γ :=
  e.u.2.1

/-- The element of `O^▷(Y)` with rational function `x`. -/
noncomputable def endY (Y : GFrob p E Γ) (x : K̄ˣ) (hfix : ∀ h ∈ Y.base.H, h • x = x)
    (hΓ : ord p (Additive.ofMul x) ∈ Γ) (h0 : 0 ≤ ord p (Additive.ofMul x)) : Y ⟶ Y :=
  GaloisModel.endO Y ⟨Additive.ofMul x, hΓ, fun h hh => congrArg Additive.ofMul (hfix h hh)⟩ h0

lemma endY_mem_orhd (Y : GFrob p E Γ) (x : K̄ˣ) (hfix : ∀ h ∈ Y.base.H, h • x = x)
    (hΓ : ord p (Additive.ofMul x) ∈ Γ) (h0 : 0 ≤ ord p (Additive.ofMul x)) :
    endY Y x hfix hΓ h0 ∈ Orhd 𝐏E Y := ⟨rfl, rfl⟩

@[simp] lemma rfE_endY (Y : GFrob p E Γ) (x : K̄ˣ) (hfix : ∀ h ∈ Y.base.H, h • x = x)
    (hΓ : ord p (Additive.ofMul x) ∈ Γ) (h0 : 0 ≤ ord p (Additive.ofMul x)) :
    rfE (endY Y x hfix hΓ h0) = x := rfl

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

/-- `Ψ` restricts to `O^▷(X) ≅ O^▷(Ψ X)`. -/
lemma mem_orhd_iff (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] {X : GFrob p E Γ}
    (e : X ⟶ X) : e ∈ Orhd 𝐏E X ↔ F.map e ∈ Orhd 𝐏E' (F.obj X) :=
  Model.mem_orhd_iff F OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E))
    OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E')) (OrbitObj.isSlim isSlimGroup)
    (OrbitObj.isSlim isSlimGroup) e

/-- **`Ψ` intertwines the Galois actions on `O^▷`** (strengthening `exists_galHom_compat` from
`O^×` to `O^▷`): for `Ψ : C(E) ≌ C(E')` there is `α : G_E ≃ₜ* G_{E'}` such that for every
`X = (G_E/N, a)`, the base of `Ψ X` is `G_{E'}/α(N)` and, for some `τ ∈ G_{E'}`, `Ψ(galHom σ)`
acts on the rational functions of `O^▷(Ψ X)` by `τ α(σ) τ⁻¹`. -/
theorem exists_galHom_compat_orhd (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E',
      ∀ (N : OpenNormalSubgroup (GK p E)) (a : Γ),
        (F.obj (XN N a)).base.H = N.toSubgroup.map (α : GK p E →* GK p E') ∧
        ∃ τ : GK p E', ∀ (σ : GK p E) (e : F.obj (XN N a) ⟶ F.obj (XN N a)),
          e ∈ Orhd 𝐏E' (F.obj (XN N a)) →
          rfE (Model.conj (show Aut (F.obj (XN N a)) from
              Model.autEquiv F (XN N a) (galHom N a σ)) e) =
            (τ * α σ * τ⁻¹) • rfE e := by
  obtain ⟨G, ⟨θ⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E)) (GaloisModel.hasAllTorsion (torsion p E')) F
  obtain ⟨G', ⟨θ'⟩⟩ := Model.thm34_galois_preservesBase isSlimGroup
    (GaloisModel.hasAllTorsion (torsion p E')) (GaloisModel.hasAllTorsion (torsion p E)) F.inv
  haveI : G.IsEquivalence :=
    isEquivalence_base (GaloisModel.isFrobenioid _ _ _ _) (GaloisModel.isFrobenioid _ _ _ _)
      F G G' θ θ'
  obtain ⟨α, x, hHα, -, hx⟩ := OrbitObj.exists_continuousMulEquiv G
  refine ⟨α, fun N a => ?_⟩
  let θX : (F.obj (XN N a)).base ≅ G.obj (OrbitObj.ofONS N) := θ.app (XN N a)
  have hnorm : (N.toSubgroup.map (α : GK p E →* GK p E')).Normal :=
    Subgroup.Normal.map inferInstance _ α.surjective
  refine ⟨(OrbitObj.H_eq_of_iso θX (by rw [hHα N]; exact hnorm)).trans (hHα N), ?_⟩
  let ξ : GK p E' := (x N).out
  refine ⟨OrbitHom.rep θX.hom * ξ⁻¹, fun σ e he => ?_⟩
  rw [rfE_conj _ he]
  have hbase : (show Aut (F.obj (XN N a)) from
      Model.autEquiv F (XN N a) (galHom N a σ)).inv.base =
      θX.hom ≫ G.map (OrbitObj.rmul N σ⁻¹⁻¹) ≫ θX.inv := by
    have nat := θ.hom.naturality (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E)
      N a σ⁻¹).inv
    rw [← Category.assoc]
    exact (θX.eq_comp_inv).mpr nat
  have hf : (G.map (OrbitObj.rmul N σ⁻¹⁻¹)).toFun (QuotientGroup.mk ξ) =
      QuotientGroup.mk (α σ⁻¹⁻¹ * ξ) := by
    have e : (QuotientGroup.mk ξ : GK p E' ⧸ (G.obj (OrbitObj.ofONS N)).H) = x N :=
      QuotientGroup.out_eq' _
    rw [e, hx, ← e, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hmem := OrbitObj.rep_conj_mem θX _ ξ _ hf
  rw [inv_inv] at hmem hbase
  have key := fixed_smul_eq_of_mem _ e.u.2 hmem
  rw [hbase]
  exact congrArg Additive.toMul key

end PAdicGalois

end Frobenioid

end Iut
