/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.PAdicSlim
import Iut.Frobenioid.Thm34iv

/-!
# Kummer cocycles of Frobenioids ([FrdII], Definition 2.1, Theorem 2.4, Kummer part)

[FrdII], Definition 2.1(ii) and Theorem 2.4(i): for a `p`-adic Frobenioid the Kummer map
`O^□(A)^H → H¹(H_A, μ_N(A))`, `f ↦ κ_f`, is built from the action of `Aut_C(A)` on `O^□(A)`
(by conjugation), the `N`-th roots `g` of `f` in `O^□(A)` and `κ_f(h) = h·g/g`; an equivalence
`Ψ : C₁ ≅ C₂` maps the Kummer maps of `C₁` to those of `C₂`.

Here, for model Frobenioids:

* `Model.conj α e = α⁻¹ ∘ e ∘ α` (the action of `Aut_C(A)` on `End_C(A)`); it preserves `O^×`
  (`conj_mem_ounits`) and acts on the rational function of a unit by the pull-back along the base
  of `α⁻¹` (`conj_u`): the action **factors through `Aut_D(A_D)`** ([FrdII], Theorem 1.2(ii));
  units commute (`ounits_comm`);
* **`Model.kummerCocycle g α = conj α g ∘ g⁻¹`**, the Frobenioid-theoretic Kummer cocycle;
  `kummerCocycle_u`: its rational function is `(α⁻¹)^*u_g − u_g`;
* **`Model.map_kummerCocycle`**: every functor maps Kummer cocycles to Kummer cocycles; with
  `Model.map_mem_ounits` ([FrdI], Theorem 3.4(iv)) this is the Kummer part of [FrdII],
  Theorem 2.4(i): `PAdicGalois.thm24_kummer` for the `p`-adic Frobenioids over `B(G_E)⁰`;
* for `GaloisModel` and `p`-adic Frobenioids: on an object over `G/N` (`N` open normal) the
  automorphism `galAut x` with base `gN ↦ gx⁻¹N` gives **`κ_g(galAut σ) = σ·γ/γ`**
  (`PAdicGalois.kummerCocycle_galAut`), i.e. the Frobenioid-theoretic Kummer cocycle is the
  Galois-theoretic one `KummerTheory.kummerFun` of `continuous-kummer-theory`
  (`PAdicGalois.kummerCocycle_eq_kummerFun`).

Not formalised: the reciprocity map `η_f` and `F_N(A) = H²(H_A, μ_N)/…` (they need the
reconstruction of `G` from `B(G)⁰` and the transport of the local duality pairing
`PadicField.pairingH1`), and the passage to cohomology classes on the finite quotients `H_A`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- **Conjugation** `α⁻¹ ∘ e ∘ α` of an endomorphism by an automorphism. -/
def conj {X : Model Φ B divB} (α : X ≅ X) (e : X ⟶ X) : X ⟶ X := α.inv ≫ e ≫ α.hom

lemma ounits_div {X : Model Φ B divB} {e : X ⟶ X} (he : e ∈ Ounits 𝐏 X) : e.div = 0 :=
  ((isIso_iff e).mp he.1).2.2

lemma ounits_deg {X : Model Φ B divB} {e : X ⟶ X} (he : e ∈ Ounits 𝐏 X) : e.deg = 1 := he.2.2

lemma ounits_base {X : Model Φ B divB} {e : X ⟶ X} (he : e ∈ Ounits 𝐏 X) : e.base = 𝟙 _ :=
  he.2.1

lemma iso_deg {X Y : Model Φ B divB} (α : X ≅ Y) : α.hom.deg = 1 ∧ α.inv.deg = 1 :=
  ⟨((isIso_iff α.hom).mp inferInstance).1, ((isIso_iff α.inv).mp inferInstance).1⟩

lemma iso_div {X Y : Model Φ B divB} (α : X ≅ Y) : α.hom.div = 0 ∧ α.inv.div = 0 :=
  ⟨((isIso_iff α.hom).mp inferInstance).2.2, ((isIso_iff α.inv).mp inferInstance).2.2⟩

lemma iso_base {X Y : Model Φ B divB} (α : X ≅ Y) : α.inv.base ≫ α.hom.base = 𝟙 _ := by
  rw [← comp_base, α.inv_hom_id, id_base]

/-- `conj` preserves `O^×`. -/
theorem conj_mem_ounits {X : Model Φ B divB} (α : X ≅ X) {e : X ⟶ X}
    (he : e ∈ Ounits 𝐏 X) : conj α e ∈ Ounits 𝐏 X := by
  haveI := he.1
  refine ⟨by unfold conj; infer_instance, ?_, ?_⟩
  · change (α.inv ≫ e ≫ α.hom).base = 𝟙 _
    rw [comp_base, comp_base, ounits_base he, Category.id_comp, iso_base]
  · change (α.inv ≫ e ≫ α.hom).deg = 1
    rw [comp_deg, comp_deg, ounits_deg he, (iso_deg α).1, (iso_deg α).2]
    rfl

/-- **The action of `Aut_C(A)` on `O^×(A)` is the pull-back along the base of `α⁻¹`**
([FrdII], Theorem 1.2(ii)). -/
theorem conj_u {X : Model Φ B divB} (α : X ≅ X) {e : X ⟶ X} (he : e ∈ Ounits 𝐏 X) :
    (conj α e).u = B.pb α.inv.base e.u := by
  have h1 : (α.inv ≫ α.hom).u = 0 := by rw [α.inv_hom_id]; rfl
  simp only [comp_u, (iso_deg α).1, PNat.one_coe, one_smul] at h1
  change (α.inv ≫ e ≫ α.hom).u = _
  simp only [comp_u, ounits_base he, GrpOn.pb_id', map_add]
  rw [comp_deg, (iso_deg α).1, ounits_deg he, mul_one, PNat.one_coe, one_smul,
    eq_neg_of_add_eq_zero_right h1]
  abel

/-- `(e ∘ e').u = u_e + u_{e'}` for units. -/
lemma ounits_comp_u {X : Model Φ B divB} {e e' : X ⟶ X} (he : e ∈ Ounits 𝐏 X)
    (he' : e' ∈ Ounits 𝐏 X) : (e ≫ e').u = e.u + e'.u := by
  simp only [comp_u, ounits_base he, GrpOn.pb_id', ounits_deg he', PNat.one_coe, one_smul]
  abel

/-- **`O^×(A)` is commutative.** -/
theorem ounits_comm {X : Model Φ B divB} {e e' : X ⟶ X} (he : e ∈ Ounits 𝐏 X)
    (he' : e' ∈ Ounits 𝐏 X) : e ≫ e' = e' ≫ e := by
  refine hom_ext ?_ ?_ ?_ ?_
  · simp [ounits_deg he, ounits_deg he']
  · simp [ounits_base he, ounits_base he']
  · simp [ounits_div he, ounits_div he', ounits_base he, ounits_base he']
  · rw [ounits_comp_u he he', ounits_comp_u he' he, add_comm]

/-- **The Frobenioid-theoretic Kummer cocycle** `κ_g(α) = α⁻¹ g α ∘ g⁻¹` of `g ∈ O^×(A)`
([FrdII], Definition 2.1(ii): `κ_f(h) = h·g/g` for an `N`-th root `g` of `f`). -/
noncomputable def kummerCocycle {X : Model Φ B divB} (g : X ⟶ X) [IsIso g] (α : X ≅ X) :
    X ⟶ X :=
  inv g ≫ conj α g

/-- The rational function of `κ_g(α)` is `(α⁻¹)^* u_g − u_g`. -/
theorem kummerCocycle_u {X : Model Φ B divB} {g : X ⟶ X} (hg : g ∈ Ounits 𝐏 X) (α : X ≅ X) :
    haveI := hg.1
    (kummerCocycle g α).u = B.pb α.inv.base g.u - g.u := by
  haveI := hg.1
  have hinv : inv g ∈ Ounits 𝐏 X := by
    refine ⟨inferInstance, ?_, ?_⟩
    · change (inv g).base = 𝟙 _
      have := congrArg Hom.base (IsIso.inv_hom_id g)
      rw [comp_base, ounits_base hg, Category.comp_id] at this
      exact this
    · change (inv g).deg = 1
      exact ((isIso_iff (inv g)).mp inferInstance).1
  have h0 : (inv g ≫ g).u = 0 := by rw [IsIso.inv_hom_id]; rfl
  rw [ounits_comp_u hinv hg] at h0
  rw [kummerCocycle, ounits_comp_u hinv (conj_mem_ounits α hg), conj_u α hg]
  rw [eq_neg_of_add_eq_zero_left h0]
  abel

/-- **Functoriality of conjugation and of Kummer cocycles**: every functor maps the Kummer
cocycle of `(g, α)` to that of `(F g, F α)` ([FrdII], Theorem 2.4(i), Kummer part, given that
`F` preserves `O^×`). -/
theorem map_kummerCocycle {D' : Type*} [Category D'] {Φ' : DivMonoid.{w} D'}
    {B' : GrpOn.{w} D'} {divB' : DivHom B' Φ'.toGrpOn} (F : Model Φ B divB ⥤ Model Φ' B' divB')
    {X : Model Φ B divB} (g : X ⟶ X) [IsIso g] (α : X ≅ X) :
    F.map (kummerCocycle g α) = kummerCocycle (F.map g) (F.mapIso α) := by
  simp [kummerCocycle, conj, Functor.map_inv]

end Model

/-! ### Galois automorphisms -/

namespace GaloisModel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
variable {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m} {Γ : AddSubgroup ℝ}

/-- **The automorphism `(1, gN ↦ g x N, 0, 0)`** of an object over `G/N`, `N` open normal. -/
noncomputable def galAut (N : OpenNormalSubgroup G) (a : Γ) (x : G) :
    (⟨OrbitObj.ofONS N, a⟩ : GaloisModel G ℓ hℓ Γ) ≅ ⟨OrbitObj.ofONS N, a⟩ where
  hom := Model.mk1 (OrbitObj.rmul N x) 0 (gammaCone Γ).zero_mem 0 (by
    change a + 0 = a + ⟨ℓ 0, _⟩
    congr 1
    exact Subtype.ext (map_zero ℓ).symm)
  inv := Model.mk1 (OrbitObj.rmul N x⁻¹) 0 (gammaCone Γ).zero_mem 0 (by
    change a + 0 = a + ⟨ℓ 0, _⟩
    congr 1
    exact Subtype.ext (map_zero ℓ).symm)
  hom_inv_id := by
    refine Model.hom_ext rfl ?_ ?_ ?_
    · ext y
      induction y using QuotientGroup.induction_on with
      | H g =>
        change (OrbitObj.rmul N x⁻¹).toFun ((OrbitObj.rmul N x).toFun (QuotientGroup.mk g)) =
          QuotientGroup.mk g
        rw [OrbitObj.rmul_mk, OrbitObj.rmul_mk, mul_inv_cancel_right]
    · simp
    · simp
  inv_hom_id := by
    refine Model.hom_ext rfl ?_ ?_ ?_
    · ext y
      induction y using QuotientGroup.induction_on with
      | H g =>
        change (OrbitObj.rmul N x).toFun ((OrbitObj.rmul N x⁻¹).toFun (QuotientGroup.mk g)) =
          QuotientGroup.mk g
        rw [OrbitObj.rmul_mk, OrbitObj.rmul_mk, inv_mul_cancel_right]
    · simp
    · simp

/-- Pull-back along the base of `(galAut x)⁻¹` is the action of `x` on `N`-invariants. -/
theorem pb_galAut_inv (N : OpenNormalSubgroup G) (a : Γ) (x : G)
    (m : (bGal G ℓ hℓ Γ).obj (OrbitObj.ofONS N)) :
    ((bGal G ℓ hℓ Γ).pb (galAut (ℓ := ℓ) (hℓ := hℓ) N a x).inv.base m).1 = x⁻¹ • m.1 := by
  change OrbitHom.rep (OrbitObj.rmul N x⁻¹) • m.1 = x⁻¹ • m.1
  refine fixed_smul_eq_of_mem _ m.2 ?_
  have h := OrbitHom.mk_rep (OrbitObj.rmul N x⁻¹)
  rw [OrbitObj.rmul_mk, one_mul] at h
  exact QuotientGroup.eq.mp h.symm

end GaloisModel

/-! ### `p`-adic Frobenioids: Frobenioid- and Galois-theoretic Kummer cocycles -/

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaZ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaZ) (divGal (GK p E) (ord p) (ord_smul p E) gammaZ)

/-- **`κ_g(galAut σ⁻¹) = σ·γ/γ`** for a unit `g` of an object over `G_E/N` with rational
function `γ ∈ (K̄^N)^×`. -/
theorem kummerCocycle_galAut (N : OpenNormalSubgroup (GK p E)) (a : gammaZ)
    {g : (⟨OrbitObj.ofONS N, a⟩ : Frob p E) ⟶ ⟨OrbitObj.ofONS N, a⟩} (hg : g ∈ Ounits 𝐏E _)
    (σ : GK p E) :
    haveI := hg.1
    (((Model.kummerCocycle g (GaloisModel.galAut N a σ⁻¹)).u.1).toMul : (PadicAlgCl p)ˣ) =
      σ • (g.u.1.toMul) / g.u.1.toMul := by
  haveI := hg.1
  rw [Model.kummerCocycle_u hg]
  erw [AddSubgroup.coe_sub, toMul_sub, GaloisModel.pb_galAut_inv, inv_inv]
  rfl

/-- **The Frobenioid-theoretic Kummer cocycle is the Galois-theoretic one**: if `γ^n ∈ E`, then
`κ_g(galAut σ⁻¹) = kummerFun γ σ` (`continuous-kummer-theory`). -/
theorem kummerCocycle_eq_kummerFun (n : ℕ) (N : OpenNormalSubgroup (GK p E)) (a : gammaZ)
    {g : (⟨OrbitObj.ofONS N, a⟩ : Frob p E) ⟶ ⟨OrbitObj.ofONS N, a⟩} (hg : g ∈ Ounits 𝐏E _)
    (hγ : ∀ σ : GK p E, σ • g.u.1.toMul ^ n = g.u.1.toMul ^ n) (σ : GK p E) :
    haveI := hg.1
    (((Model.kummerCocycle g (GaloisModel.galAut N a σ⁻¹)).u.1).toMul : (PadicAlgCl p)ˣ) =
      KummerTheory.Mu.val (KummerTheory.kummerFun (n := n) (g.u.1.toMul) hγ σ) := by
  rw [KummerTheory.val_kummerFun]
  exact kummerCocycle_galAut N a hg σ

variable {E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) gammaZ)
  (bGal (GK p E') (ord p) (ord_smul p E') gammaZ)
  (divGal (GK p E') (ord p) (ord_smul p E') gammaZ)

omit [FiniteDimensional ℚ_[p] E] in
/-- **[FrdII], Theorem 2.4(i), Kummer part**: an equivalence `Ψ : C^⊢(E) ≌ C^⊢(E')` of `p`-adic
Frobenioids maps `O^×(A)` into `O^×(Ψ A)`, and Kummer cocycles to Kummer cocycles. -/
theorem thm24_kummer (F : Frob p E ⥤ Frob p E') [F.IsEquivalence] {X : Frob p E}
    {g : X ⟶ X} (hg : g ∈ Ounits 𝐏E X) (α : X ≅ X) :
    F.map g ∈ Ounits 𝐏E' (F.obj X) ∧
      haveI := hg.1
      F.map (Model.kummerCocycle g α) = Model.kummerCocycle (F.map g) (F.mapIso α) := by
  haveI := hg.1
  refine ⟨Model.map_mem_ounits F OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E))
    OrbitObj.baseHyp (GaloisModel.hasAllTorsion (torsion p E')) (OrbitObj.isSlim isSlimGroup)
    hg, Model.map_kummerCocycle F g α⟩

end PAdicGalois

end Frobenioid

end Iut
