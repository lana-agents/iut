/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalGaloisRlf

/-!
# The fibres of `C_{F̃/F}` and `C_{F̃/F}^rlf` over an object `G/H` of `B(G)⁰`

[FrdI], Theorem 6.4 (l.6334–6419 of `~/iut-scratch/frd/FrdI.txt`) is stated objectwise: for a
Frobenius-trivial object `A` over the object of `D = B(G)⁰` determined by a finite extension
`L ⊆ F̃` of `F`, `deg^arith_L` determines `δ_A : Pic_Φ(A) ≅ ℝ`, and (iv) compares the fields
`L₁`, `L₂` of corresponding objects. This file identifies the part of `C_{F̃/F}` (resp. of its
realification) lying over `G/H` via base-identity morphisms with the Frobenioid of the number
field `L = E^H` over the one-morphism base, generalising `fibreTop` (`G/G`, `GlobalGaloisCmp.lean`)
to every object.

* **`fibre A : GlobalFrobenioid L ⥤ GlobalGaloisFrob F E`**, `(pt, α) ↦ (G/H, α)` (divisors via
  `toZ`), `(n, Z, u) ↦ (n, id, Z, u)`: faithful (`fibre_faithful`), injective on objects, every
  object over `G/H` is in the image (`fibre_obj_mk`), and every base-identity morphism between
  objects of the image comes from a morphism of `GlobalFrobenioid L` (`fibre_preimage`).
* **`fibreRlf A : GlobalRealified L ⥤ GlobalGaloisRlf F E`**, the same for the realifications
  (here `Φ^rlf(G/H) = Φ^rlf(L)` and `B^rlf(G/H) = ℝ·div(L^×)` on the nose).
* **Compatibility with the realifications** ([FrdI], Proposition 5.3):
  `realify (fibre A X) = fibreRlf A (realify X)` on objects (`realify_fibre_obj`) and on the
  components of morphisms (`realify_fibre_map_div`, `_deg`, `_base`, `_u`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

namespace GlobalGaloisFrob

/-! ### The non-realified fibre -/

lemma toZ_symm_divZ (A : OrbitObj (GalG F E)) (u : Additive (Fix A)ˣ) :
    (toZ (Fix A)).symm (divZ (Fix A) u) = divG (Fix A) u := by
  rw [AddEquiv.symm_apply_eq, toZ_divG]

lemma toZ_symm_mem (A : OrbitObj (GalG F E)) {x : ArithDivZ (Fix A)} (hx : x ∈ effConeZ (Fix A)) :
    (toZ (Fix A)).symm x ∈ effG (Fix A) := by
  rw [← toZ_mem_iff, AddEquiv.apply_symm_apply]
  exact hx

variable (A : OrbitObj (GalG F E))

/-- **The fibre of `C_{F̃/F}` over `G/H`**: `GlobalFrobenioid (E^H) → GlobalGaloisFrob F E`,
`(pt, α) ↦ (G/H, α)`, `(n, Z, u) ↦ (n, id, Z, u)`. -/
noncomputable def fibre : GlobalFrobenioid (Fix A) ⥤ GlobalGaloisFrob F E where
  obj X := ⟨A, (toZ (Fix A)).symm X.α⟩
  map {X Y} φ := Model.mk' φ.deg (𝟙 A) ((toZ (Fix A)).symm φ.div) (toZ_symm_mem A φ.div_mem)
    φ.u (by
      have h := congrArg (toZ (Fix A)).symm φ.rel
      rw [map_add, map_add, map_nsmul] at h
      have h2 : (toZ (Fix A)).symm (divZ (Fix A) φ.u) = divG (Fix A) φ.u := toZ_symm_divZ A φ.u
      rw [h2] at h
      exact h.trans (congrArg₂ (· + ·) ((phiGal F E).pb_id A _).symm rfl))
  map_id X := Model.hom_ext rfl rfl (map_zero _) rfl
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · exact (map_add _ _ _).trans
        (congrArg₂ (· + ·) ((phiGal F E).pb_id A _).symm (map_nsmul _ _ _))
    · exact congrArg₂ (· + ·) ((bGalNF F E).pb_id A _).symm rfl

@[simp] lemma fibre_obj_base (X : GlobalFrobenioid (Fix A)) : ((fibre A).obj X).base = A := rfl

@[simp] lemma fibre_map_base {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    ((fibre A).map φ).base = 𝟙 A := rfl

@[simp] lemma fibre_map_deg {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    ((fibre A).map φ).deg = φ.deg := rfl

/-- Every object of `C_{F̃/F}` over `G/H` is in the image of `fibre`. -/
theorem fibre_obj_mk (α : (phiGal F E).obj A) :
    (fibre A).obj ⟨pt, toZ (Fix A) α⟩ = ⟨A, α⟩ := by
  change (⟨A, (toZ (Fix A)).symm (toZ (Fix A) α)⟩ : GlobalGaloisFrob F E) = _
  rw [AddEquiv.symm_apply_apply]

lemma fibre_obj_injective : Function.Injective (fibre A).obj := by
  rintro ⟨⟨⟨⟩⟩, α⟩ ⟨⟨⟨⟩⟩, β⟩ h
  have h' : (toZ (Fix A)).symm α = (toZ (Fix A)).symm β :=
    eq_of_heq (Model.mk.inj h).2
  rw [(toZ (Fix A)).symm.injective h']

instance fibre_faithful : (fibre A).Faithful where
  map_injective {X Y} φ ψ h := by
    have h1 : ((fibre A).map φ).deg = ((fibre A).map ψ).deg := by rw [h]
    have h3 : ((fibre A).map φ).div = ((fibre A).map ψ).div := by rw [h]
    have h4 : ((fibre A).map φ).u = ((fibre A).map ψ).u := by rw [h]
    change (toZ (Fix A)).symm φ.div = (toZ (Fix A)).symm ψ.div at h3
    exact Model.hom_ext h1 (Subsingleton.elim _ _) ((toZ (Fix A)).symm.injective h3) h4

/-- **Base-identity morphisms between objects of the fibre come from the fibre.** -/
theorem fibre_preimage {X Y : GlobalFrobenioid (Fix A)} (ψ : (fibre A).obj X ⟶ (fibre A).obj Y)
    (hψ : ψ.base = 𝟙 A) : ∃ φ : X ⟶ Y, (fibre A).map φ = ψ := by
  have r := ψ.rel
  have hp : (phiGal F E).pb ψ.base ((fibre A).obj Y).α = (toZ (Fix A)).symm Y.α := by
    rw [hψ]
    exact (phiGal F E).pb_id A _
  rw [hp] at r
  have r0 : (ψ.deg : ℕ) • (toZ (Fix A)).symm X.α + id (α := ArithDivG (Fix A)) ψ.div =
      (toZ (Fix A)).symm Y.α + divG (Fix A) ψ.u := r
  have r' := congrArg (toZ (Fix A)) r0
  rw [map_add, map_add, map_nsmul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    toZ_divG, id] at r'
  refine ⟨Model.mk' ψ.deg (eqToHom (Subsingleton.elim _ _)) (toZ (Fix A) ψ.div)
    ((toZ_mem_iff _).2 ψ.div_mem) ψ.u ?_, ?_⟩
  · change (ψ.deg : ℕ) • X.α + toZ (Fix A) ψ.div = Y.α + divZ (Fix A) ψ.u
    exact r'
  · exact Model.hom_ext rfl hψ.symm (AddEquiv.symm_apply_apply _ _) rfl

end GlobalGaloisFrob

/-! ### The realified fibre -/

namespace GlobalGaloisRlf

variable (A : OrbitObj (GalG F E))

/-- **The fibre of `C_{F̃/F}^rlf` over `G/H`**: `GlobalRealified (E^H) → GlobalGaloisRlf F E`,
`(pt, α) ↦ (G/H, α)`, `(n, Z, u) ↦ (n, id, Z, u)`. -/
noncomputable def fibreRlf : GlobalRealified (Fix A) ⥤ GlobalGaloisRlf F E where
  obj X := ⟨A, X.α⟩
  map {X Y} φ := Model.mk' φ.deg (𝟙 A) φ.div φ.div_mem φ.u (by
    exact φ.rel.trans (congrArg₂ (· + ·) ((phiRlfGal F E).pb_id A _).symm rfl))
  map_id X := Model.hom_ext rfl rfl rfl rfl
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · exact congrArg₂ (· + ·) ((phiRlfGal F E).pb_id A _).symm rfl
    · exact congrArg₂ (· + ·) ((bRlfGal F E).pb_id A _).symm rfl

@[simp] lemma fibreRlf_obj_base (X : GlobalRealified (Fix A)) : ((fibreRlf A).obj X).base = A :=
  rfl

@[simp] lemma fibreRlf_map_base {X Y : GlobalRealified (Fix A)} (φ : X ⟶ Y) :
    ((fibreRlf A).map φ).base = 𝟙 A := rfl

/-- Every object of `C_{F̃/F}^rlf` over `G/H` is in the image of `fibreRlf`. -/
theorem fibreRlf_obj_mk (α : (phiRlfGal F E).obj A) : (fibreRlf A).obj ⟨pt, α⟩ = ⟨A, α⟩ := rfl

instance fibreRlf_faithful : (fibreRlf A).Faithful where
  map_injective {X Y} φ ψ h := by
    have h1 : ((fibreRlf A).map φ).deg = ((fibreRlf A).map ψ).deg := by rw [h]
    have h3 : ((fibreRlf A).map φ).div = ((fibreRlf A).map ψ).div := by rw [h]
    have h4 : ((fibreRlf A).map φ).u = ((fibreRlf A).map ψ).u := by rw [h]
    exact Model.hom_ext h1 (Subsingleton.elim _ _) h3 h4

/-- **Base-identity morphisms between objects of the realified fibre come from the fibre.** -/
theorem fibreRlf_preimage {X Y : GlobalRealified (Fix A)}
    (ψ : (fibreRlf A).obj X ⟶ (fibreRlf A).obj Y) (hψ : ψ.base = 𝟙 A) :
    ∃ φ : X ⟶ Y, (fibreRlf A).map φ = ψ := by
  have r := ψ.rel
  have hp : (phiRlfGal F E).pb ψ.base ((fibreRlf A).obj Y).α = Y.α := by
    rw [hψ]
    exact (phiRlfGal F E).pb_id A _
  rw [hp] at r
  exact ⟨Model.mk' ψ.deg (eqToHom (Subsingleton.elim _ _)) ψ.div ψ.div_mem ψ.u (by exact r),
    Model.hom_ext rfl hψ.symm rfl rfl⟩

end GlobalGaloisRlf

/-! ### Compatibility with the realifications -/

namespace GlobalGaloisFrob

open GlobalGaloisRlf

variable (A : OrbitObj (GalG F E))

lemma castG_toZ_symm (x : ArithDivZ (Fix A)) : castG (Fix A) ((toZ (Fix A)).symm x) = castDiv _ x :=
  by rw [castG_apply, AddEquiv.apply_symm_apply]

/-- **`realify ∘ fibre = fibreRlf ∘ realify` on objects.** -/
theorem realify_fibre_obj (X : GlobalFrobenioid (Fix A)) :
    (realify F E).obj ((fibre A).obj X) =
      (fibreRlf A).obj ((GlobalFrobenioid.realify (Fix A)).obj X) := by
  change (⟨A, castG (Fix A) ((toZ (Fix A)).symm X.α)⟩ : GlobalGaloisRlf F E) = ⟨A, castDiv _ X.α⟩
  rw [castG_toZ_symm]

theorem realify_fibre_map_deg {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    ((realify F E).map ((fibre A).map φ)).deg =
      ((fibreRlf A).map ((GlobalFrobenioid.realify (Fix A)).map φ)).deg := rfl

theorem realify_fibre_map_base {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    ((realify F E).map ((fibre A).map φ)).base =
      ((fibreRlf A).map ((GlobalFrobenioid.realify (Fix A)).map φ)).base := rfl

theorem realify_fibre_map_div {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    ((realify F E).map ((fibre A).map φ)).div =
      ((fibreRlf A).map ((GlobalFrobenioid.realify (Fix A)).map φ)).div :=
  castG_toZ_symm A φ.div

theorem realify_fibre_map_u {X Y : GlobalFrobenioid (Fix A)} (φ : X ⟶ Y) :
    (show ratFun (Fix A) from ((realify F E).map ((fibre A).map φ)).u) =
      (show ratFun (Fix A) from ((fibreRlf A).map ((GlobalFrobenioid.realify (Fix A)).map φ)).u) :=
  Subtype.ext <| by
    change castG (Fix A) (divG (Fix A) φ.u) = castDiv _ (divZ _ φ.u)
    rw [← toZ_symm_divZ, castG_toZ_symm]

end GlobalGaloisFrob

end Frobenioid

end Iut
