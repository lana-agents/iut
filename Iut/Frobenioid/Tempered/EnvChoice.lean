/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EnvTransport
import Iut.Frobenioid.Tempered.TwistEquiv

/-!
# Self-equivalences and Frobenioid-theoretic theta data ([EtTh], Thm 5.6, 5.10, Cor 5.12)

`Iut/Frobenioid/Tempered/EnvTransport.lean` transports the data `(s⊓, s⊔, σ, π)` of a
Frobenioid-theoretic theta environment along an equivalence `F` to the *image data*
`(F s⊓, F s⊔, F σ F_*^{-1}, F_* π)`. For a **self-equivalence** `Ψ` of the tempered Frobenioid,
[EtTh] compares the image data with the *original* data on the same objects: by
Proposition 5.3(vi) and Theorem 4.4 there are isomorphisms `γ₁ : Ψ(A_N) ≅ A_N`,
`β : Ψ(B_N) ≅ B_N` and automorphisms `ζ₁, ζ₂` of `B_N` with

  `γ₁ ∘ … : γ₁ ≫ s⊓ = Ψ(s⊓) ≫ β ≫ ζ₁`, `γ₁ ≫ s⊔ = Ψ(s⊔) ≫ β ≫ ζ₂`,

and an automorphism `φ` of `Π^tp_X` (the outer automorphism induced by `Ψ^bs`) with
`σ(π(φ p)) = γ₁ ∘ Ψ(σ(π p)) ∘ γ₁^{-1}` (the base-Frobenius section is unique up to conjugation by
`O^×(A_N)`, which is absorbed into `γ₁`). This file proves the formal consequences:

* `Model.liftAut_eq_conj`: lifts along pre-steps are transported by conjugation
  ([EtTh], Proposition 4.3(i),(ii)(b));
* `Model.sgp_psi`, `Model.tgp_psi`: `s⊓-gp(φ p) = Ψ_{β ≫ ζ₁}(s⊓-gp(p))`,
  `s⊔-gp(φ q) = Ψ_{β ≫ ζ₂}(s⊔-gp(q))`, where `Ψ_γ(a) = γ ∘ Ψ(a) ∘ γ^{-1}`;
* **[EtTh], Theorem 5.6** (`Model.thm56`): when `ζ₁ = 1` and `ζ₂` is a unit `u ∈ O^×(B_N)` fixed by
  the geometric element `s⊓-gp(φ q)` (the Kummer class of `u`, a function from the field of
  constants, does not affect the restriction to `l · Δ_Θ`), `δ(φ q) = Ψ_β(δ(q))`: `Ψ` transports
  the cyclotomic rigidity isomorphism `q ↦ δ(q)` of Proposition 5.5;
* **[EtTh], Theorem 5.10(ii)** (`Model.thm510ii_sgp`, `Model.thm510ii_tgp`,
  `Model.thm510ii_thetaE`): `Ψ_β` maps `Im(s⊓-gp)`, `Im(s⊔-gp)`, `E_N` to
  `ζ₁^{-1} Im(s⊓-gp) ζ₁`, `ζ₂^{-1} Im(s⊔-gp) ζ₂`, `ζ₁^{-1} E_N ζ₁` (ET's `δ₁ = ζ₁^{-1}`,
  `δ₁δ₂δ₃ = ζ₂^{-1}`);
* **[EtTh], Theorem 5.10(iii)** (`Model.thm510iii`, `Model.thm510iii_comm`): if moreover
  `ζ₁ = 1`, `ζ₂ ∈ μ_N(B_N)`, `φ` preserves `PY ⊇ PYdd` and is a homeomorphism, and
  `Ψ^birat_β = (β^{-1})^* ∘ F^birat` preserves the constants `K^×` (`Model.psiUnit`; the
  `K^×`-part of Theorem 5.10(ii), proved in [EtTh] via Proposition 3.4(ii)), then
  `γ : (e, p) ↦ (Ψ_β e, φ p)` is an automorphism of the mono-theta environment `E^Π_N` with
  `ε ∘ γ = Ψ_β ∘ ε`. [EtTh] reaches `ζ₂ ∈ μ_N` from the general `ζ₂` of Theorem 5.10(ii) by
  Corollary 2.18(iv) and `H¹(ℤ/2ℤ, O^×_K) ≅ μ_2`; that reduction is not formalised here;
* **[EtTh], Corollary 5.12(iii)** (`Model.cor512iii`): for the self-equivalence `Ξ` of
  Lemma 5.11 attached to automorphisms `κ_J` (`Model.conjFamilyFunctor`), the image data are
  `κ_B^{-1} ∘ s ∘ κ_A` and `Im(s⊓-gp) ↦ κ_B^{-1} Im(s⊓-gp) κ_B`; `Ξ` matches pre-steps and
  base-equivalent pairs (`Model.isPreStep_conjFamily_iff`, `Model.base_eq_conjFamily_iff`), so
  `Model.frobEnvMap` applies to it.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory Iut.EtaleTheta

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### Conjugation by isomorphisms -/

section Conj

lemma autMulEquivOfIso_hom {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (a : Aut Y) :
    (Aut.autMulEquivOfIso γ a).hom = γ.inv ≫ a.hom ≫ γ.hom := rfl

lemma autMulEquivOfIso_base {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (a : Aut Y) :
    (Aut.autMulEquivOfIso γ a).hom.base = γ.inv.base ≫ a.hom.base ≫ γ.hom.base := rfl

/-- Conjugation by an automorphism `ζ` of `Y`: `ζ ∘ a ∘ ζ^{-1}` in `Aut(Y)` is `ζ * a * ζ⁻¹`. -/
lemma autMulEquivOfIso_self {Y : Model Φ B divB} (ζ : Aut Y) (a : Aut Y) :
    Aut.autMulEquivOfIso ζ a = ζ * a * ζ⁻¹ := by
  ext1
  rfl

lemma autMulEquivOfIso_trans {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (ζ : Aut Y') (a : Aut Y) :
    Aut.autMulEquivOfIso (γ ≪≫ ζ) a = ζ * Aut.autMulEquivOfIso γ a * ζ⁻¹ := by
  ext1
  change (ζ.inv ≫ γ.inv) ≫ a.hom ≫ γ.hom ≫ ζ.hom = ζ.inv ≫ (γ.inv ≫ a.hom ≫ γ.hom) ≫ ζ.hom
  simp only [Category.assoc]

lemma mem_unitsAut_autMulEquivOfIso_iff {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (a : Aut Y) :
    Aut.autMulEquivOfIso γ a ∈ unitsAut Y' ↔ a ∈ unitsAut Y := by
  rw [mem_unitsAut, mem_unitsAut, autMulEquivOfIso_base]
  constructor
  · intro h
    have := congrArg (γ.hom.base ≫ · ≫ γ.inv.base) h
    simp only [Category.id_comp, ← Category.assoc, hom_base_inv_of_iso] at this
    simpa only [Category.assoc, hom_base_inv_of_iso, Category.comp_id] using this
  · intro h
    rw [h, Category.id_comp, inv_base_of_iso]

lemma mem_muN_autMulEquivOfIso_iff {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (N : ℕ) (a : Aut Y) :
    Aut.autMulEquivOfIso γ a ∈ muN Y' N ↔ a ∈ muN Y N := by
  rw [mem_muN, mem_muN, mem_unitsAut_autMulEquivOfIso_iff, ← map_pow,
    MulEquiv.map_eq_one_iff]

/-- **Lifts along pre-steps are transported by conjugation** ([EtTh], Proposition 4.3(i),
(ii)(b)): if `γ₁ ≫ s' = s ≫ γ₂` and `b` lifts `a` along `s`, then the lift of
`γ₁ ∘ a ∘ γ₁^{-1}` along `s'` is `γ₂ ∘ b ∘ γ₂^{-1}`. -/
theorem liftAut_eq_conj {X X' Y Y' : Model Φ B divB} {s : X ⟶ Y} {s' : X' ⟶ Y'} [IsIso s'.base]
    (γ₁ : X ≅ X') (γ₂ : Y ≅ Y') (hγ : γ₁.hom ≫ s' = s ≫ γ₂.hom) (hs' : s'.deg = 1)
    {a : Aut X} {b : Aut Y} (hab : s ≫ b.hom = a.hom ≫ s) (a' : Aut X')
    (ha' : a' = Aut.autMulEquivOfIso γ₁ a) (hfix : Φ.pb a'.hom.base s'.div = s'.div) :
    liftAut hs' a' hfix = Aut.autMulEquivOfIso γ₂ b := by
  ext1
  symm
  refine liftAut_unique hs' a' hfix ?_
  subst ha'
  have e : s' = γ₁.inv ≫ s ≫ γ₂.hom := by rw [← hγ, Iso.inv_hom_id_assoc]
  rw [autMulEquivOfIso_hom, autMulEquivOfIso_hom, e]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hab]

end Conj

/-! ### The data of a self-functor compared with the original data -/

section Psi

variable (F : Model Φ B divB ⥤ Model Φ B divB)

/-- **`Ψ_γ`**: apply `F`, then conjugate by `γ : F(Y) ≅ Y'`. -/
def psiAut {Y Y' : Model Φ B divB} (γ : F.obj Y ≅ Y') : Aut Y →* Aut Y' :=
  (Aut.autMulEquivOfIso γ).toMonoidHom.comp (F.mapAut Y)

lemma psiAut_apply {Y Y' : Model Φ B divB} (γ : F.obj Y ≅ Y') (a : Aut Y) :
    psiAut F γ a = Aut.autMulEquivOfIso γ (F.mapIso a) := rfl

lemma psiAut_trans {Y Y' : Model Φ B divB} (γ : F.obj Y ≅ Y') (ζ : Aut Y') (a : Aut Y) :
    psiAut F (γ ≪≫ ζ) a = ζ * psiAut F γ a * ζ⁻¹ :=
  autMulEquivOfIso_trans γ ζ _

variable {X Y : Model Φ B divB} {s t : X ⟶ Y} [IsIso s.base] [IsIso t.base]
  (hs : IsPreStep (toElem Φ B divB) s) (ht : IsPreStep (toElem Φ B divB) t)
  (hb : s.base = t.base) {σ : Aut X ⧸ unitsAut X →* Aut X} {PX : Type (max v w)} [Group PX]
  (π : PX →* Aut X ⧸ unitsAut X) (hsfix : ∀ q, Φ.pb (σ q).hom.base s.div = s.div)
  (γ₁ : F.obj X ≅ X) (φ : PX →* PX)
  (hσ : ∀ p, σ (π (φ p)) = Aut.autMulEquivOfIso γ₁ (F.mapIso (σ (π p))))

include hσ in
/-- **`s⊓-gp(φ p) = Ψ_{γ₂}(s⊓-gp(p))`** for `γ₁ ≫ s⊓ = Ψ(s⊓) ≫ γ₂` ([EtTh], Theorem 4.4(iv) and
Proposition 4.3(ii)(b)). -/
theorem sgp_psi (γ₂ : F.obj Y ≅ Y) (hγ : γ₁.hom ≫ s = F.map s ≫ γ₂.hom)
    (p : PX) : sgp hs π hsfix (φ p) = psiAut F γ₂ (sgp hs π hsfix p) := by
  change liftAut hs.1 (σ (π (φ p))) _ = _
  refine liftAut_eq_conj γ₁ γ₂ hγ hs.1 (a := F.mapIso (σ (π p))) ?_ _ (hσ p) _
  change F.map s ≫ F.map (sgp hs π hsfix p).hom = F.map (σ (π p)).hom ≫ F.map s
  rw [← F.map_comp, ← F.map_comp, liftGp_spec hs (σ.comp π) (fun p => hsfix (π p)) p]
  rfl

variable {PYdd : Subgroup PX} (htfix : ∀ p : PYdd, Φ.pb (σ (π p)).hom.base t.div = t.div)
  (hφ : ∀ q ∈ PYdd, φ q ∈ PYdd)

include hσ in
/-- **`s⊔-gp(φ q) = Ψ_{γ₂}(s⊔-gp(q))`** for `γ₁ ≫ s⊔ = Ψ(s⊔) ≫ γ₂`. -/
theorem tgp_psi (γ₂ : F.obj Y ≅ Y) (hγ : γ₁.hom ≫ t = F.map t ≫ γ₂.hom) (q : PYdd) :
    tgp ht π htfix ⟨φ q, hφ q q.2⟩ = psiAut F γ₂ (tgp ht π htfix q) := by
  change liftAut ht.1 (σ (π (φ q))) _ = _
  refine liftAut_eq_conj γ₁ γ₂ hγ ht.1 (a := F.mapIso (σ (π q))) ?_ _ (hσ q) _
  change F.map t ≫ F.map (tgp ht π htfix q).hom = F.map (σ (π q)).hom ≫ F.map t
  rw [← F.map_comp, ← F.map_comp, liftGp_spec ht ((σ.comp π).comp PYdd.subtype) htfix q]
  rfl

/-- A unit `u` commutes with every automorphism whose base fixes `u`. -/
lemma unitAut_commute {a : Aut Y} (u : B.obj Y.base) (hu0 : divB.app _ u = 0)
    (hu : B.pb a.inv.base u = u) : a * unitAut Y u hu0 = unitAut Y u hu0 * a := by
  have := conj_unitAut a u hu0
  rw [unitAut_congr hu _ hu0] at this
  have := congrArg (· * a) this
  simpa [mul_assoc] using this

variable (N : ℕ) (hFN : ∀ p : PYdd, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))

include hσ in
/-- **[EtTh], Theorem 5.6** (category-theoreticity of Frobenioid-theoretic cyclotomic rigidity):
let `Ψ` be a self-functor, `γ₁ : Ψ(A) ≅ A`, `β : Ψ(B) ≅ B` with `γ₁ ≫ s⊓ = Ψ(s⊓) ≫ β` and
`γ₁ ≫ s⊔ = Ψ(s⊔) ≫ β ≫ u` for a unit `u ∈ O^×(B)` (Proposition 5.3(vi)), and `φ` the induced
automorphism of `PX` (`σ(π(φ p)) = γ₁ Ψ(σ(π p)) γ₁^{-1}`). Then for every `q ∈ PYdd` whose image
`s⊓-gp(φ q)` fixes `u` (`q` geometric, `u` from the field of constants), `Ψ_β` maps the Kummer class
`δ(q) ∈ μ_N(B)` of Proposition 5.5 to `δ(φ q)`: `Ψ` transports the isomorphism
`(l · Δ_Θ) ⊗ ℤ/Nℤ ≅ μ_N` of Proposition 5.5. -/
theorem thm56 (β : F.obj Y ≅ Y) (hsβ : γ₁.hom ≫ s = F.map s ≫ β.hom) (u : B.obj Y.base)
    (hu0 : divB.app _ u = 0) (htβ : γ₁.hom ≫ t = F.map t ≫ β.hom ≫ (unitAut Y u hu0).hom)
    (q : PYdd) (hu : B.pb (sgp hs π hsfix (φ q)).inv.base u = u) :
    (deltaE hs ht hb π hsfix N htfix hFN ⟨φ q, hφ q q.2⟩ : Aut Y) =
      psiAut F β (deltaE hs ht hb π hsfix N htfix hFN q : Aut Y) := by
  have hT := tgp_psi F ht π γ₁ φ hσ htfix hφ (β ≪≫ unitAut Y u hu0) htβ q
  rw [psiAut_trans] at hT
  have hS := sgp_psi F hs π hsfix γ₁ φ hσ β hsβ q
  -- the unit commutes with `Ψ_β(s⊔-gp q)`, whose base is that of `s⊓-gp(φ q)`
  have hbase : (psiAut F β (tgp ht π htfix q)).inv.base = (sgp hs π hsfix (φ q)).inv.base := by
    have h1 : (tgp ht π htfix ⟨φ q, hφ q q.2⟩).hom.base = (sgp hs π hsfix (φ q)).hom.base :=
      tgp_base hs ht hb π hsfix htfix _
    have h2 : (tgp ht π htfix ⟨φ q, hφ q q.2⟩).hom.base =
        (psiAut F β (tgp ht π htfix q)).hom.base := by
      rw [hT]
      change ((unitAut Y u hu0).inv ≫ (psiAut F β (tgp ht π htfix q)).hom ≫
        (unitAut Y u hu0).hom).base = _
      have hU : (unitAut Y u hu0).hom.base = 𝟙 _ := unitAut_mem_unitsAut u hu0
      have hU' : (unitAut Y u hu0).inv.base = 𝟙 _ := by
        have := inv_base_of_iso (unitAut Y u hu0)
        rwa [hU, Category.comp_id] at this
      rw [comp_base, comp_base, hU, hU', Category.id_comp, Category.comp_id]
    have h3 : (psiAut F β (tgp ht π htfix q)).hom.base = (sgp hs π hsfix (φ q)).hom.base :=
      h2.symm.trans h1
    have e1 := inv_base_of_iso (psiAut F β (tgp ht π htfix q))
    have e2 := hom_base_inv_of_iso (sgp hs π hsfix (φ q))
    rw [h3] at e1
    have := congrArg (· ≫ (sgp hs π hsfix (φ q)).inv.base) e1
    simp only [Category.assoc, e2, Category.comp_id, Category.id_comp] at this
    exact this
  have hc := unitAut_commute u hu0 (a := psiAut F β (tgp ht π htfix q)) (by rw [hbase]; exact hu)
  change tgp ht π htfix ⟨φ q, hφ q q.2⟩ * (sgp hs π hsfix (φ q))⁻¹ =
    psiAut F β (tgp ht π htfix q * (sgp hs π hsfix q)⁻¹)
  rw [hT, hS, map_mul, map_inv, ← hc, mul_inv_cancel_right]

/-! #### [EtTh], Theorem 5.10(ii) -/

include hσ in
/-- **[EtTh], Theorem 5.10(ii)** for `Im(s⊓-gp)`: if `γ₁ ≫ s⊓ = Ψ(s⊓) ≫ β ≫ ζ₁`, then `Ψ_β` maps
`s⊓-gp(PY)` to `ζ₁^{-1} · s⊓-gp(φ(PY)) · ζ₁` (`= ζ₁^{-1} Im(s⊓-gp) ζ₁` when `φ(PY) = PY`). -/
theorem thm510ii_sgp (β : F.obj Y ≅ Y) (ζ₁ : Aut Y)
    (hsβ : γ₁.hom ≫ s = F.map s ≫ β.hom ≫ ζ₁.hom) (PY : Subgroup PX) :
    (PY.map (sgp hs π hsfix)).map (psiAut F β) =
      ((PY.map φ).map (sgp hs π hsfix)).map (MulAut.conj ζ₁⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun p => ?_
  have := sgp_psi F hs π hsfix γ₁ φ hσ (β ≪≫ ζ₁) hsβ p
  rw [psiAut_trans] at this
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, this, inv_inv]
  group

include hσ in
/-- **[EtTh], Theorem 5.10(ii)** for `Im(s⊔-gp)`: if `γ₁ ≫ s⊔ = Ψ(s⊔) ≫ β ≫ ζ₂`, then `Ψ_β` maps
`s⊔-gp(q)` to `ζ₂^{-1} · s⊔-gp(φ q) · ζ₂`. -/
theorem thm510ii_tgp (β : F.obj Y ≅ Y) (ζ₂ : Aut Y)
    (htβ : γ₁.hom ≫ t = F.map t ≫ β.hom ≫ ζ₂.hom) (q : PYdd) :
    psiAut F β (tgp ht π htfix q) = ζ₂⁻¹ * tgp ht π htfix ⟨φ q, hφ q q.2⟩ * ζ₂ := by
  have := tgp_psi F ht π γ₁ φ hσ htfix hφ (β ≪≫ ζ₂) htβ q
  rw [psiAut_trans] at this
  rw [this]
  group

include hσ in
/-- **[EtTh], Theorem 5.10(ii)** for `E_N`: if `γ₁ ≫ s⊓ = Ψ(s⊓) ≫ β ≫ ζ₁` and `Ψ_β` maps
`μ_N(B)` onto itself, then `Ψ_β(E_N) = ζ₁^{-1} E_N(φ(PY)) ζ₁`. -/
theorem thm510ii_thetaE (β : F.obj Y ≅ Y) (ζ₁ : Aut Y)
    (hsβ : γ₁.hom ≫ s = F.map s ≫ β.hom ≫ ζ₁.hom) (PY : Subgroup PX)
    (hmu : (muN Y N).map (psiAut F β) = muN Y N) :
    (thetaE hs π hsfix PY N).map (psiAut F β) =
      (thetaE hs π hsfix (PY.map φ) N).map (MulAut.conj ζ₁⁻¹).toMonoidHom := by
  have key : ∀ p, psiAut F β (sgp hs π hsfix p) = ζ₁⁻¹ * sgp hs π hsfix (φ p) * ζ₁ := by
    intro p
    have := sgp_psi F hs π hsfix γ₁ φ hσ (β ≪≫ ζ₁) hsβ p
    rw [psiAut_trans] at this
    rw [this]
    group
  have hconj : ∀ m, m ∈ muN Y N ↔ ζ₁ * m * ζ₁⁻¹ ∈ muN Y N := fun m =>
    ⟨fun h => (inferInstance : (muN Y N).Normal).conj_mem m h ζ₁, fun h => by
      simpa [mul_assoc] using (inferInstance : (muN Y N).Normal).conj_mem _ h ζ₁⁻¹⟩
  ext e
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨_, ⟨m, hm, p, hp, rfl⟩, rfl⟩
    have hm' : psiAut F β m ∈ muN Y N := hmu ▸ Subgroup.mem_map_of_mem _ hm
    refine ⟨ζ₁ * psiAut F β m * ζ₁⁻¹ * sgp hs π hsfix (φ p),
      ⟨_, (hconj _).1 hm', φ p, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
    rw [map_mul, key]
    group
  · rintro ⟨_, ⟨m, hm, _, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
    have hm' : ζ₁⁻¹ * m * ζ₁ ∈ muN Y N := by
      simpa using (inferInstance : (muN Y N).Normal).conj_mem m hm ζ₁⁻¹
    rw [← hmu] at hm'
    obtain ⟨m₀, hm₀, e₀⟩ := hm'
    refine ⟨m₀ * sgp hs π hsfix p, ⟨m₀, hm₀, p, hp, rfl⟩, ?_⟩
    rw [map_mul, key, e₀]
    group

end Psi

/-! ### [EtTh], Corollary 5.12(iii): the self-equivalences of Lemma 5.11 -/

section Cor512

variable (α : ∀ J : Model Φ B divB, J ≅ J)

lemma isPreStep_conjFamily_iff ⦃X Y : Model Φ B divB⦄ (φ : X ⟶ Y) :
    IsPreStep 𝐏 φ ↔ IsPreStep 𝐏 ((conjFamilyFunctor α).map φ) := by
  rw [conjFamilyFunctor_map]
  constructor
  · intro h
    exact isPreStep_comp₀ (isPreStep_of_isIso _) (isPreStep_comp₀ h (isPreStep_of_isIso _))
  · rintro ⟨h1, h2⟩
    haveI : IsIso (α X).inv.base := ((isIso_iff _).1 (inferInstance : IsIso (α X).inv)).2.1
    haveI : IsIso (α Y).hom.base := ((isIso_iff _).1 (inferInstance : IsIso (α Y).hom)).2.1
    refine ⟨?_, ?_⟩
    · have h1' : ((α X).inv ≫ φ ≫ (α Y).hom).deg = 1 := h1
      rw [comp_deg, comp_deg, deg_of_iso (α Y), show (α X).inv.deg = 1 from deg_of_iso (α X).symm,
        one_mul, mul_one] at h1'
      exact h1'
    · haveI : IsIso ((α X).inv.base ≫ φ.base ≫ (α Y).hom.base) := h2
      haveI : IsIso (φ.base ≫ (α Y).hom.base) := IsIso.of_isIso_comp_left (α X).inv.base _
      exact IsIso.of_isIso_comp_right φ.base (α Y).hom.base

lemma base_eq_conjFamily_iff ⦃X Y : Model Φ B divB⦄ (φ φ' : X ⟶ Y) :
    φ.base = φ'.base ↔
      ((conjFamilyFunctor α).map φ).base = ((conjFamilyFunctor α).map φ').base := by
  simp only [conjFamilyFunctor_map, comp_base]
  constructor
  · intro h
    rw [h]
  · intro h
    haveI : IsIso (α X).inv.base := ((isIso_iff _).1 (inferInstance : IsIso (α X).inv)).2.1
    haveI : IsIso (α Y).hom.base := ((isIso_iff _).1 (inferInstance : IsIso (α Y).hom)).2.1
    exact (cancel_mono _).1 ((cancel_epi _).1 h)

/-- **[EtTh], Corollary 5.12(iii)** (via Lemma 5.11): for any family of automorphisms
`α_J = κ_J^{-1}`, the self-equivalence `Ξ = conjFamilyFunctor α` (isomorphic to the identity, the
identity on objects) maps the pre-step `s⊓ : A → B` to `κ_B^{-1} ∘ s⊓ ∘ κ_A`, the bi-Kummer root
`s⊓-gp(p)` to `κ_B^{-1} ∘ s⊓-gp(p) ∘ κ_B` (the bi-Kummer root of the image data), and the
base-Frobenius section to its `κ_A`-conjugate. -/
theorem cor512iii {X Y : Model Φ B divB} {s : X ⟶ Y} [IsIso s.base]
    [IsIso ((conjFamilyFunctor α).map s).base] (hs : IsPreStep 𝐏 s)
    {σ : Aut X ⧸ unitsAut X →* Aut X} {PX : Type (max v w)} [Group PX]
    (π : PX →* Aut X ⧸ unitsAut X) (hsfix : ∀ q, Φ.pb (σ q).hom.base s.div = s.div) :
    (conjFamilyFunctor α).map s = (α X).inv ≫ s ≫ (α Y).hom ∧
      (∀ p, sgp (σ := imSigma (conjFamilyFunctor α) (base_eq_conjFamily_iff α) σ)
        ((isPreStep_conjFamily_iff α s).1 hs)
        (imPi (conjFamilyFunctor α) (base_eq_conjFamily_iff α) π)
        (imSigma_fix (conjFamilyFunctor α) (isPreStep_conjFamily_iff α)
          (base_eq_conjFamily_iff α) hs hsfix) p =
        Aut.autMulEquivOfIso (α Y) (sgp hs π hsfix p)) ∧
      (∀ q, imSigma (conjFamilyFunctor α) (base_eq_conjFamily_iff α) σ
        (quotMap (conjFamilyFunctor α) (base_eq_conjFamily_iff α) X q) =
        Aut.autMulEquivOfIso (α X) (σ q)) := by
  refine ⟨rfl, fun p => ?_, fun q => ?_⟩
  · rw [sgp_map (conjFamilyFunctor α) (isPreStep_conjFamily_iff α) (base_eq_conjFamily_iff α)
      hs π hsfix p]
    rfl
  · rw [imSigma_quotMap]
    rfl

end Cor512

/-! ### [EtTh], Theorem 5.10(iii): the automorphism of the theta environment -/

section ConjUnits

lemma autMulEquivOfIso_unitAut {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (d : B.obj Y.base)
    (hd : divB.app _ d = 0) :
    Aut.autMulEquivOfIso γ (unitAut Y d hd) =
      unitAut Y' (B.pb γ.inv.base d) (by rw [divB.natural, hd, map_zero]) := by
  have hdeg : γ.inv.deg = 1 := deg_of_iso γ.symm
  have hdiv : γ.inv.div = 0 := div_of_iso γ.symm
  have h0 := congrArg Hom.u γ.inv_hom_id
  simp only [comp_u, id_u, deg_of_iso γ, PNat.one_coe, one_smul] at h0
  ext1
  change γ.inv ≫ unitHom Y d hd ≫ γ.hom = _
  rw [unitAut_hom]
  ext
  · simp [unitHom, deg_of_iso γ, hdeg]
  · simp [unitHom, inv_base_of_iso]
  · simp [unitHom, div_of_iso γ, hdiv]
  · simp only [comp_u, comp_deg, unitHom, mk1_u, mk1_deg, mk1_base, GrpOn.pb_id',
      deg_of_iso γ, mul_one, PNat.one_coe, one_smul, map_add]
    rw [← sub_eq_zero, ← h0]
    abel

lemma pb_hom_pb_inv {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (c : B.obj Y.base) :
    B.pb γ.hom.base (B.pb γ.inv.base c) = c := by
  rw [← GrpOn.pb_comp', hom_base_inv_of_iso, GrpOn.pb_id']

lemma pb_inv_pb_hom {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (c : B.obj Y'.base) :
    B.pb γ.inv.base (B.pb γ.hom.base c) = c := by
  rw [← GrpOn.pb_comp', inv_base_of_iso, GrpOn.pb_id']

/-- **Conjugating the twist by a birational unit** by an isomorphism `γ`. -/
lemma autMulEquivOfIso_twUnit {Y Y' : Model Φ B divB} (γ : Y ≅ Y') (a : Aut Y)
    (c : B.obj Y.base) (h : Φ.pb a.hom.base (divB.app _ c) = divB.app _ c)
    (h' : Φ.pb (Aut.autMulEquivOfIso γ a).hom.base (divB.app _ (B.pb γ.inv.base c)) =
      divB.app _ (B.pb γ.inv.base c)) :
    Aut.autMulEquivOfIso γ (twUnit a c h) =
      twUnit (Aut.autMulEquivOfIso γ a) (B.pb γ.inv.base c) h' := by
  unfold twUnit
  rw [autMulEquivOfIso_unitAut]
  refine unitAut_congr ?_ _ _
  rw [autMulEquivOfIso_base, GrpOn.pb_comp', GrpOn.pb_comp', pb_hom_pb_inv, map_sub]

end ConjUnits

section Thm510iii

variable (F : Model Φ B divB ⥤ Model Φ B divB) [F.IsEquivalence]
  (hpre : ∀ ⦃X Y : Model Φ B divB⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ B divB) φ ↔ IsPreStep (toElem Φ B divB) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ B divB⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)

local notation "𝐅𝐅" => Functor.FullyFaithful.ofFullyFaithful F

variable {X Y : Model Φ B divB} (β : F.obj Y ≅ Y)

/-- **`Ψ_β = (β ∘ − ∘ β^{-1}) ∘ F : Aut_C(Y) ≅ Aut_C(Y)`** ([EtTh], Theorem 5.10(ii): "`Ψ` followed
by conjugation by `β`"). -/
noncomputable def psiEquiv : Aut Y ≃* Aut Y :=
  (autEquivFF F 𝐅𝐅 Y).trans (Aut.autMulEquivOfIso β)

lemma psiEquiv_apply (a : Aut Y) : psiEquiv F β a = psiAut F β a := rfl

include hbe in
lemma mem_unitsAut_psiEquiv_iff (a : Aut Y) :
    psiEquiv F β a ∈ unitsAut Y ↔ a ∈ unitsAut Y := by
  rw [psiEquiv, MulEquiv.trans_apply, mem_unitsAut_autMulEquivOfIso_iff]
  exact (mem_unitsAut_autEquivFF_iff F hbe Y a).symm

include hbe in
lemma mem_muN_psiEquiv_iff (N : ℕ) (a : Aut Y) : psiEquiv F β a ∈ muN Y N ↔ a ∈ muN Y N := by
  rw [psiEquiv, MulEquiv.trans_apply, mem_muN_autMulEquivOfIso_iff]
  exact (mem_muN_map_iff F hbe N a).symm

include hbe in
lemma base_eq_psiEquiv_iff (a b : Aut Y) :
    (psiEquiv F β a).hom.base = (psiEquiv F β b).hom.base ↔ a.hom.base = b.hom.base := by
  rw [base_eq_iff_mul_inv_mem, base_eq_iff_mul_inv_mem, ← map_inv, ← map_mul,
    mem_unitsAut_psiEquiv_iff F hbe]

/-- `Ψ^birat_β = (β^{-1})^* ∘ F^birat : O^×(Y^birat) ≅ O^×(Y^birat)`. -/
noncomputable def psiUnit (c : B.obj Y.base) : B.obj Y.base :=
  B.pb β.inv.base (mapUnit F hpre c)

omit [F.IsEquivalence] in
include hbe in
lemma psiUnit_nsmul (n : ℕ) (c : B.obj Y.base) :
    psiUnit F hpre β (n • c) = n • psiUnit F hpre β c := by
  rw [psiUnit, psiUnit, mapUnit_nsmul F hpre hbe, map_nsmul]

include hbe in
lemma psiUnit_surjective : Function.Surjective (psiUnit F hpre β) := by
  intro c'
  obtain ⟨d, hd⟩ := mapUnit_surjective F hpre hbe Y (B.pb β.hom.base c')
  exact ⟨d, by rw [psiUnit, hd, pb_inv_pb_hom]⟩

include hbe in
/-- `Ψ_β` transports the twists by birational units through `Ψ^birat_β`. -/
lemma psiEquiv_twUnit (a : Aut Y) (c : B.obj Y.base)
    (h : Φ.pb a.hom.base (divB.app _ c) = divB.app _ c)
    (h' : Φ.pb (psiEquiv F β a).hom.base (divB.app _ (psiUnit F hpre β c)) =
      divB.app _ (psiUnit F hpre β c)) :
    psiEquiv F β (twUnit a c h) = twUnit (psiEquiv F β a) (psiUnit F hpre β c) h' := by
  change Aut.autMulEquivOfIso β (F.mapIso (twUnit a c h)) = _
  rw [map_twUnit F hpre hbe a c h]
  exact autMulEquivOfIso_twUnit β (F.mapIso a) _ _ h'

variable {s t : X ⟶ Y} [IsIso s.base] [IsIso t.base]
  (hs : IsPreStep (toElem Φ B divB) s) (ht : IsPreStep (toElem Φ B divB) t)
  (hb : s.base = t.base) {σ : Aut X ⧸ unitsAut X →* Aut X} {PX : Type (max v w)} [Group PX]
  (π : PX →* Aut X ⧸ unitsAut X) (hsfix : ∀ q, Φ.pb (σ q).hom.base s.div = s.div)
  (N : ℕ) (γ₁ : F.obj X ≅ X) (φ : PX ≃* PX)
  (hσ : ∀ p, σ (π (φ p)) = Aut.autMulEquivOfIso γ₁ (F.mapIso (σ (π p))))
  (hsβ : γ₁.hom ≫ s = F.map s ≫ β.hom)

include hσ hsβ in
lemma psiEquiv_sgp (p : PX) : psiEquiv F β (sgp hs π hsfix p) = sgp hs π hsfix (φ p) :=
  (sgp_psi F hs π hsfix γ₁ φ.toMonoidHom hσ β hsβ p).symm

variable (PY : Subgroup PX) (hφY : ∀ p, φ p ∈ PY ↔ p ∈ PY)

include hbe hσ hsβ hφY in
lemma mem_thetaE_psiEquiv_iff (e : Aut Y) :
    psiEquiv F β e ∈ thetaE hs π hsfix PY N ↔ e ∈ thetaE hs π hsfix PY N := by
  constructor
  · rintro ⟨m', hm', p', hp', he⟩
    obtain ⟨m, rfl⟩ := (psiEquiv F β).surjective m'
    obtain ⟨p, rfl⟩ := φ.surjective p'
    refine ⟨m, (mem_muN_psiEquiv_iff F hbe β N m).1 hm', p, (hφY p).1 hp', ?_⟩
    apply (psiEquiv F β).injective
    rw [he, map_mul, psiEquiv_sgp F β hs π hsfix γ₁ φ hσ hsβ]
  · rintro ⟨m, hm, p, hp, rfl⟩
    refine ⟨psiEquiv F β m, (mem_muN_psiEquiv_iff F hbe β N m).2 hm, φ p, (hφY p).2 hp, ?_⟩
    rw [map_mul, psiEquiv_sgp F β hs π hsfix γ₁ φ hσ hsβ]

/-- `(e, p) ↦ (Ψ_β e, φ p)` on `Aut_C(Y) × PX`. -/
noncomputable abbrev psiProd : Aut Y × PX ≃* Aut Y × PX :=
  MulEquiv.prodCongr (psiEquiv F β) φ

include hbe hσ hsβ hφY in
lemma mem_thetaEPi_psiProd_iff (x : Aut Y × PX) :
    psiProd F β φ x ∈ thetaEPi hs π hsfix PY N ↔ x ∈ thetaEPi hs π hsfix PY N := by
  rw [mem_thetaEPi, mem_thetaEPi]
  refine and_congr (hφY x.2) (and_congr
    (mem_thetaE_psiEquiv_iff F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x.1) ?_)
  change (psiEquiv F β x.1).hom.base = (sgp hs π hsfix (φ x.2)).hom.base ↔ _
  rw [← psiEquiv_sgp F β hs π hsfix γ₁ φ hσ hsβ, base_eq_psiEquiv_iff F hbe β]

/-- **The automorphism `γ` of `E^Π_N`** of [EtTh], Theorem 5.10(iii): `(e, p) ↦ (Ψ_β e, φ p)`. -/
noncomputable def ePsi : thetaEPi hs π hsfix PY N ≃* thetaEPi hs π hsfix PY N where
  toFun x := ⟨psiProd F β φ x,
    (mem_thetaEPi_psiProd_iff F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x).2 x.2⟩
  invFun y := ⟨(psiProd F β φ).symm y,
    (mem_thetaEPi_psiProd_iff F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY _).1
      (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((psiProd F β φ).symm_apply_apply (x : Aut Y × PX))
  right_inv y := Subtype.ext ((psiProd F β φ).apply_symm_apply (y : Aut Y × PX))
  map_mul' x y := Subtype.ext (map_mul (psiProd F β φ) (x : Aut Y × PX) y)

@[simp] lemma coe_ePsi (x : thetaEPi hs π hsfix PY N) :
    (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x : Aut Y × PX) =
      (psiEquiv F β (x : Aut Y × PX).1, φ (x : Aut Y × PX).2) := rfl

/-! #### The theta subgroups -/

variable {PY} {PYdd : Subgroup PX} (hle : PYdd ≤ PY)
  (htfix : ∀ p : PYdd, Φ.pb (σ (π p)).hom.base t.div = t.div)
  (hFN : ∀ p : PYdd, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))
  (hφdd : ∀ p, φ p ∈ PYdd ↔ p ∈ PYdd) (ζ : Aut Y) (hζ : ζ ∈ muN Y N)
  (htβ : γ₁.hom ≫ t = F.map t ≫ β.hom ≫ ζ.hom)

include hσ htβ in
lemma psiEquiv_tgp (q : PYdd) :
    psiEquiv F β (tgp ht π htfix q) =
      ζ⁻¹ * tgp ht π htfix ⟨φ q, (hφdd q).2 q.2⟩ * ζ :=
  thm510ii_tgp F ht π γ₁ φ.toMonoidHom hσ htfix (fun q hq => (hφdd q).2 hq) β ζ htβ q

include hσ hsβ htβ in
lemma ePsi_tPi (q : PYdd) :
    ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY (tPi hs ht hb π hsfix N hle htfix hFN q) =
      MulAut.conj (inlE hs π hsfix PY N ⟨ζ⁻¹, (muN Y N).inv_mem hζ⟩)
        (tPi hs ht hb π hsfix N hle htfix hFN ⟨φ q, (hφdd q).2 q.2⟩) := by
  apply Subtype.ext
  apply Prod.ext
  · change psiEquiv F β (tgp ht π htfix q) = ζ⁻¹ * tgp ht π htfix ⟨φ q, _⟩ * ζ⁻¹⁻¹
    rw [inv_inv]
    exact psiEquiv_tgp F β ht π γ₁ φ hσ htfix hφdd ζ htβ q
  · change φ q = 1 * φ q * 1⁻¹
    group

include hσ hsβ htβ hφdd hζ in
lemma map_range_tPi_ePsi :
    (tPi hs ht hb π hsfix N hle htfix hFN).range.map
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).toMonoidHom =
      (tPi hs ht hb π hsfix N hle htfix hFN).range.map
        (MulAut.conj (inlE hs π hsfix PY N ⟨ζ⁻¹, (muN Y N).inv_mem hζ⟩)).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (ePsi_tPi F hbe β hs ht hb π hsfix N γ₁ φ hσ hsβ hφY hle htfix hFN hφdd
      ζ hζ htβ q).symm⟩
  · rintro ⟨_, ⟨q', rfl⟩, rfl⟩
    have hq : φ.symm q' ∈ PYdd := (hφdd _).1 (by rw [MulEquiv.apply_symm_apply]; exact q'.2)
    refine ⟨_, ⟨⟨φ.symm q', hq⟩, rfl⟩, ?_⟩
    have e : (⟨φ (φ.symm q'), (hφdd _).2 hq⟩ : PYdd) = q' :=
      Subtype.ext (MulEquiv.apply_symm_apply φ (q' : PX))
    rw [ePsi_tPi F hbe β hs ht hb π hsfix N γ₁ φ hσ hsβ hφY hle htfix hFN hφdd ζ hζ htβ, e]

include hσ hsβ htβ hφdd hζ in
lemma image_thetaSubgroupsE_ePsi :
    Subgroup.map (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).toMonoidHom ''
        thetaSubgroupsE hs ht hb π hsfix N hle htfix hFN =
      thetaSubgroupsE hs ht hb π hsfix N hle htfix hFN := by
  have key : ∀ m : muN Y N, ((tPi hs ht hb π hsfix N hle htfix hFN).range.map
      (MulAut.conj (inlE hs π hsfix PY N m)).toMonoidHom).map
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).toMonoidHom =
      (tPi hs ht hb π hsfix N hle htfix hFN).range.map (MulAut.conj (inlE hs π hsfix PY N
        (⟨psiEquiv F β m, (mem_muN_psiEquiv_iff F hbe β N m).2 m.2⟩ *
          ⟨ζ⁻¹, (muN Y N).inv_mem hζ⟩))).toMonoidHom := by
    intro m
    have hconj : ∀ x, ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY
        (MulAut.conj (inlE hs π hsfix PY N m) x) =
        MulAut.conj (inlE hs π hsfix PY N ⟨psiEquiv F β m, (mem_muN_psiEquiv_iff F hbe β N m).2
          m.2⟩) (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x) := by
      intro x
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      congr 2 <;> apply Subtype.ext <;> apply Prod.ext <;>
        simp [inlE]
    rw [Subgroup.map_map]
    have e1 : ((ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).toMonoidHom.comp
        (MulAut.conj (inlE hs π hsfix PY N m)).toMonoidHom) =
        (MulAut.conj (inlE hs π hsfix PY N ⟨psiEquiv F β m, (mem_muN_psiEquiv_iff F hbe β N m).2
          m.2⟩)).toMonoidHom.comp (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).toMonoidHom :=
      MonoidHom.ext hconj
    rw [e1, ← Subgroup.map_map, map_range_tPi_ePsi F hbe β hs ht hb π hsfix N γ₁ φ hσ hsβ hφY hle
      htfix hFN hφdd ζ hζ htβ, Subgroup.map_map, map_mul, MulAut.conj.map_mul]
    rfl
  ext H
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨_, (key m).symm⟩
  · rintro ⟨m', rfl⟩
    obtain ⟨m, hm⟩ := (psiEquiv F β).surjective ((m' : Aut Y) * ζ)
    have hm' : m ∈ muN Y N := (mem_muN_psiEquiv_iff F hbe β N m).1
      (hm ▸ (muN Y N).mul_mem m'.2 hζ)
    refine ⟨_, ⟨⟨m, hm'⟩, rfl⟩, ?_⟩
    rw [key]
    congr 4
    apply Subtype.ext
    change psiEquiv F β m * ζ⁻¹ = m'
    rw [hm, mul_inv_cancel_right]

/-! #### The subgroup `D`: conjugations by `E^Π_X` and twists by constants -/

omit [IsIso t.base] in
include hσ hsβ in
lemma ePsi_conjE [PY.Normal] (z : thetaEPi hs π hsfix ⊤ N) (y : thetaEPi hs π hsfix PY N) :
    ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY (conjE hs π hsfix PY N z y) =
      conjE hs π hsfix PY N
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ ⊤ (fun _ => iff_of_true trivial trivial) z)
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY y) := by
  apply Subtype.ext
  change psiProd F β φ ((z : Aut Y × PX) * (y : Aut Y × PX) * (z : Aut Y × PX)⁻¹) =
    psiProd F β φ (z : Aut Y × PX) * psiProd F β φ (y : Aut Y × PX) *
      (psiProd F β φ (z : Aut Y × PX))⁻¹
  rw [map_mul, map_mul, map_inv]

variable (Kcst : AddSubgroup (B.obj Y.base))
  (hKfix : ∀ k ∈ Kcst, ∀ p : PX, B.pb (sgp hs π hsfix p).hom.base k = k)
  (htf : ∀ a : Φ.obj Y.base, N • a = 0 → a = 0)
  (hK : ∀ k, psiUnit F hpre β k ∈ Kcst ↔ k ∈ Kcst)

omit [F.IsEquivalence] in
include hbe hK in
lemma psiUnit_mem_constRoots_iff (c : B.obj Y.base) :
    psiUnit F hpre β c ∈ constRoots N Kcst ↔ c ∈ constRoots N Kcst := by
  rw [mem_constRoots, mem_constRoots, ← psiUnit_nsmul F hpre hbe, hK]

/-- `Ψ^birat_β` on `(K^×)^{1/N}`. -/
noncomputable def psiRoot (c : constRoots N Kcst) : constRoots N Kcst :=
  ⟨psiUnit F hpre β c, (psiUnit_mem_constRoots_iff F hpre hbe β N Kcst hK c).2 c.2⟩

lemma psiRoot_surjective : Function.Surjective (psiRoot F hpre hbe β N Kcst hK) := by
  rintro ⟨c', hc'⟩
  obtain ⟨c, rfl⟩ := psiUnit_surjective F hpre hbe β c'
  exact ⟨⟨c, (psiUnit_mem_constRoots_iff F hpre hbe β N Kcst hK c).1 hc'⟩, rfl⟩

omit [IsIso t.base] in
include hσ hsβ in
lemma ePsi_twistE (c : constRoots N Kcst) (x : thetaEPi hs π hsfix PY N) :
    ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY (twistE hs π hsfix PY N Kcst hKfix htf c x) =
      twistE hs π hsfix PY N Kcst hKfix htf (psiRoot F hpre hbe β N Kcst hK c)
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x) := by
  apply Subtype.ext
  apply Prod.ext
  · change psiEquiv F β ((x : Aut Y × PX).1 * twUnit (x : Aut Y × PX).1 (c : B.obj Y.base)
        (divB_fix_of_mem hs π hsfix N Kcst hKfix htf c.2 x.2)) =
      psiEquiv F β (x : Aut Y × PX).1 * twUnit (psiEquiv F β (x : Aut Y × PX).1)
        (psiUnit F hpre β c) (divB_fix_of_mem hs π hsfix N Kcst hKfix htf
          (psiRoot F hpre hbe β N Kcst hK c).2
          (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY x).2)
    rw [map_mul, psiEquiv_twUnit F hpre hbe β]
  · rfl

omit [IsIso t.base] in
include hσ hsβ in
lemma conjAut_ePsi_conjE [PY.Normal] (z : thetaEPi hs π hsfix ⊤ N) :
    MonoThetaEnv.conjAut (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY)
        (conjE hs π hsfix PY N z) =
      conjE hs π hsfix PY N
        (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ ⊤ (fun _ => iff_of_true trivial trivial) z) := by
  ext y : 1
  obtain ⟨x, rfl⟩ := (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).surjective y
  rw [MonoThetaEnv.conjAut_apply, MulEquiv.symm_apply_apply,
    ePsi_conjE F hbe β hs π hsfix N γ₁ φ hσ hsβ hφY]

omit [IsIso t.base] in
include hσ hsβ in
lemma conjAut_ePsi_twistE (c : constRoots N Kcst) :
    MonoThetaEnv.conjAut (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY)
        (twistE hs π hsfix PY N Kcst hKfix htf c) =
      twistE hs π hsfix PY N Kcst hKfix htf (psiRoot F hpre hbe β N Kcst hK c) := by
  ext y : 1
  obtain ⟨x, rfl⟩ := (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY).surjective y
  rw [MonoThetaEnv.conjAut_apply, MulEquiv.symm_apply_apply,
    ePsi_twistE F hpre hbe β hs π hsfix N γ₁ φ hσ hsβ hφY Kcst hKfix htf hK]

omit [IsIso t.base] in
include hpre hσ hsβ hK in
lemma map_thetaD_ePsi [PY.Normal] :
    (thetaD hs π hsfix PY N Kcst hKfix htf).map
        (MonoThetaEnv.conjAut (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY)) =
      thetaD hs π hsfix PY N Kcst hKfix htf := by
  rw [thetaD, MonoidHom.map_closure, Set.image_union]
  congr 2
  · ext α
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨_, (conjAut_ePsi_conjE F hbe β hs π hsfix N γ₁ φ hσ hsβ hφY z).symm⟩
    · rintro ⟨z', rfl⟩
      obtain ⟨z, rfl⟩ := (ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ ⊤
        (fun _ => iff_of_true trivial trivial)).surjective z'
      exact ⟨_, ⟨z, rfl⟩, conjAut_ePsi_conjE F hbe β hs π hsfix N γ₁ φ hσ hsβ hφY z⟩
  · ext α
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, (conjAut_ePsi_twistE F hpre hbe β hs π hsfix N γ₁ φ hσ hsβ hφY Kcst hKfix htf
        hK c).symm⟩
    · rintro ⟨c', rfl⟩
      obtain ⟨c, rfl⟩ := psiRoot_surjective F hpre hbe β N Kcst hK c'
      exact ⟨_, ⟨c, rfl⟩, conjAut_ePsi_twistE F hpre hbe β hs π hsfix N γ₁ φ hσ hsβ hφY Kcst
        hKfix htf hK c⟩

section Top

variable [TopologicalSpace (Aut Y)] [DiscreteTopology (Aut Y)] [TopologicalSpace PX]
  [IsTopologicalGroup PX] (hφc : Continuous φ) (hφc' : Continuous φ.symm)

/-- `γ` as an automorphism of topological groups. -/
noncomputable def ePsiₜ : thetaEPi hs π hsfix PY N ≃ₜ* thetaEPi hs π hsfix PY N where
  toMulEquiv := ePsi F hbe β hs π hsfix N γ₁ φ hσ hsβ PY hφY
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun x : thetaEPi hs π hsfix PY N =>
      (psiEquiv F β (x : Aut Y × PX).1, φ (x : Aut Y × PX).2)
    exact ((continuous_of_discreteTopology (f := fun a : Aut Y => psiEquiv F β a)).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (hφc.comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun x : thetaEPi hs π hsfix PY N =>
      ((psiEquiv F β).symm (x : Aut Y × PX).1, φ.symm (x : Aut Y × PX).2)
    exact ((continuous_of_discreteTopology (f := fun a : Aut Y => (psiEquiv F β).symm a)).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (hφc'.comp (continuous_snd.comp continuous_subtype_val))

include hpre hbe hσ hsβ hφY hφdd hζ htβ hK hφc hφc' in
/-- **[EtTh], Theorem 5.10(iii)** (with the `μ_N`-normalisation of `s⊔`): let `Ψ` be a
self-equivalence matching pre-steps and base-equivalent pairs, `γ₁ : Ψ(A_N) ≅ A_N`,
`β : Ψ(B_N) ≅ B_N` with `γ₁ ≫ s⊓ = Ψ(s⊓) ≫ β`, `γ₁ ≫ s⊔ = Ψ(s⊔) ≫ β ≫ ζ` for some
`ζ ∈ μ_N(B_N)`, `φ` the induced automorphism of `PX` (preserving `PY`, `PYdd`, with
`σ(π(φ p)) = γ₁ Ψ(σ(π p)) γ₁^{-1}`), and suppose `Ψ^birat_β` preserves the constants `K^×`
(Theorem 5.10(ii)). Then `γ : (e, p) ↦ (Ψ_β e, φ p)` is an automorphism of the mono-theta
environment `E^Π_N`, and `ε ∘ γ = Ψ_β ∘ ε` (`Model.thm510iii_comm`).

[EtTh] reduces the general case (`ζ ∈ δ₂ · s⊓-gp(Aut_D)`, Theorem 5.10(ii)) to this one by
Corollary 2.18(iv) and an `H¹(ℤ/2ℤ, O^×_K) ≅ μ_2` argument. -/
noncomputable def thm510iii [PY.Normal] :
    MonoThetaEnv.Iso (frobEnv hs ht hb π hsfix N Kcst hKfix htf hle htfix hFN)
      (frobEnv hs ht hb π hsfix N Kcst hKfix htf hle htfix hFN) where
  e := ePsiₜ F hbe β hs π hsfix N γ₁ φ hσ hsβ hφY hφc hφc'
  map_D := map_thetaD_ePsi F hpre hbe β hs π hsfix N γ₁ φ hσ hsβ hφY Kcst hKfix htf hK
  map_theta := image_thetaSubgroupsE_ePsi F hbe β hs ht hb π hsfix N γ₁ φ hσ hsβ hφY hle htfix
    hFN hφdd ζ hζ htβ

/-- The commutative square of [EtTh], Theorem 5.10(iii): `ε ∘ γ = Ψ_β ∘ ε`. -/
lemma thm510iii_comm [PY.Normal] (x : thetaEPi hs π hsfix PY N) :
    (Subtype.val ((thm510iii F hpre hbe β hs ht hb π hsfix N γ₁ φ hσ hsβ hφY hle htfix hFN hφdd ζ
      hζ htβ Kcst hKfix htf hK hφc hφc').e x) : Aut Y × PX).1 =
      psiEquiv F β (x : Aut Y × PX).1 := rfl

end Top

end Thm510iii

end Model

end Frobenioid

end Iut
