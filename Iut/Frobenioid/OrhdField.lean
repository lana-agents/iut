/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24iiPf

/-!
# `O^□(A)^H ≅ O^□(L^H)` and its transport by `Ψ` ([FrdII], Remark 2.2.1, Theorem 2.4(i))

[FrdII], Remark 2.2.1: "In the notation of Definition 2.2, suppose that `A` is `(N, H)`-saturated.
Write `A_E = Spec(L)` […]. Note that `H_A` acts naturally on `L`, `O^□(A)`. Moreover, we have a
natural isomorphism `(O^□(A) ⊇) O^□(A)^H ≅ O^□(L^H)`"; and Theorem 2.4(i): `Ψ` "induces
isomorphisms of monoids/modules `O^□(A₁)^{H₁} ≅ O^□(A₂)^{H₂}`".

For `C_v = FrobPf` (fieldwise saturated, `O^□ = O^▷`), `X = (G_E/N, a)` and `N ⊆ H`
(so `L^H = K̄^H`):

* **`orhdFixEquiv`**: `O^▷(X)^{H_A} ≃ O^▷_{K̄^H} = {x ∈ (K̄^H)^× : v(x) ≥ 0}` (`e ↦ γ_e`),
  multiplicative (`orhdFixEquiv_comp`);
* **`orhdPsiEquiv`**: for `Ψ : C_v(E) ≌ C_v(E')` with `α`, `τ` as in `exists_galHom_compat_orhd`,
  `x ↦ B(e_x)` is a bijection `O^▷_{K̄^H} ≃ O^▷_{K̄^{α(H)}}`, multiplicative
  (`orhdPsiEquiv_mul`): the `O^□` part of Theorem 2.4(i) in field-theoretic form.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaQ) (divGal (GK p E) (ord p) (ord_smul p E) gammaQ)

section Fix

variable [FiniteDimensional ℚ_[p] E]
variable (N : OpenNormalSubgroup (GK p E)) (a : gammaQ) (H : Subgroup (GK p E))

/-- **`O^▷(X)^{H_A}`**: the elements of `O^▷(X)` fixed by the conjugation action of `H`. -/
def OrhdFix : Type :=
  {e : (XN N a : FrobPf p E) ⟶ XN N a //
    e ∈ Orhd 𝐏E (XN N a) ∧ ∀ h ∈ H, Model.conj (galIso N a h) e = e}

/-- **`O^▷_L = {x ∈ L^× : v(x) ≥ 0}`** for `L = K̄^H`. -/
def OrhdL [FiniteDimensional ℚ_[p] (fixL H)] : Type :=
  {x : (fixL H)ˣ // 0 ≤ v p (x : fixL H)}

variable {N a H}

lemma rfE_fixed_H {e : (XN N a : FrobPf p E) ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a))
    (hfix : ∀ h ∈ H, Model.conj (galIso N a h) e = e) : ∀ h ∈ H, h • rfE e = rfE e :=
  fun h hh => by rw [← rfE_conj_galHom N a h he, hfix h hh]

variable (hNH : N.toSubgroup ≤ H) [FiniteDimensional ℚ_[p] (fixL H)]

include hNH in
/-- **`O^▷(X)^{H_A} ≃ O^▷_{K̄^H}`** ([FrdII], Remark 2.2.1), `e ↦ γ_e`. -/
noncomputable def orhdFixEquiv : OrhdFix N a H ≃ OrhdL H where
  toFun e := ⟨unitsOfFixed H (rfE e.1) (rfE_fixed_H e.2.1 e.2.2), by
    rw [← ord_nonneg_iff, ιL_unitsOfFixed]
    exact ord_rfE_nonneg e.2.1⟩
  invFun x := ⟨endY (XN N a) (ιL (fixL H) x.1) (fun _ hν => smul_ιL H x.1 (hNH hν))
      (ord_mem_gammaQ _) ((ord_nonneg_iff _ x.1).mpr x.2),
    endY_mem_orhd _ _ _ _ _, fun h hh => rfE_injective_orhd (Model.conj_mem_orhd _
      (endY_mem_orhd _ _ _ _ _)) (endY_mem_orhd _ _ _ _ _) (by
        rw [rfE_conj_galHom N a h (endY_mem_orhd _ _ _ _ _), rfE_endY]
        exact smul_ιL H x.1 hh)⟩
  left_inv e := Subtype.ext (rfE_injective_orhd ⟨rfl, rfl⟩ e.2.1 (by
    simp only [rfE_endY, ιL_unitsOfFixed]))
  right_inv x := Subtype.ext (ιL_injective _ (by simp only [ιL_unitsOfFixed, rfE_endY]))

lemma coe_orhdFixEquiv (e : OrhdFix N a H) :
    ιL (fixL H) (orhdFixEquiv hNH e).1 = rfE e.1 :=
  ιL_unitsOfFixed H (rfE e.1) (rfE_fixed_H e.2.1 e.2.2)

/-- `orhdFixEquiv` is multiplicative (composition in `O^▷(X)`, multiplication in `L`). -/
lemma orhdFixEquiv_comp (e e' : OrhdFix N a H) (hc : OrhdFix N a H)
    (hce : hc.1 = e.1 ≫ e'.1) :
    (orhdFixEquiv hNH hc).1 = (orhdFixEquiv hNH e).1 * (orhdFixEquiv hNH e').1 := by
  apply ιL_injective
  rw [map_mul, coe_orhdFixEquiv, coe_orhdFixEquiv, coe_orhdFixEquiv, hce,
    rfE_comp e.2.1 e'.2.1]

end Fix

section Psi

variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']
variable {F : FrobPf p E ⥤ FrobPf p E'} [F.IsEquivalence] {α : GK p E ≃ₜ* GK p E'} {τ : GK p E'}
  {N : OpenNormalSubgroup (GK p E)} {a : gammaQ} (H : Subgroup (GK p E))
  (hNH : N.toSubgroup ≤ H) (hτ : OrhdCompat F α τ N a)
  [FiniteDimensional ℚ_[p] (fixL H)]
  [FiniteDimensional ℚ_[p] (fixL (H.map (α : GK p E →* GK p E')))]

/-- `e_x ∈ O^▷(X)` for `x ∈ O^▷_L`. -/
noncomputable def endL (x : OrhdL H) : (XN N a : FrobPf p E) ⟶ XN N a :=
  endY (XN N a) (ιL (fixL H) x.1) (fun _ hν => smul_ιL H x.1 (hNH hν)) (ord_mem_gammaQ _)
    ((ord_nonneg_iff _ x.1).mpr x.2)

lemma endL_mem (x : OrhdL H) : endL (a := a) H hNH x ∈ Orhd 𝐏E (XN N a) := ⟨rfl, rfl⟩

lemma rfE_endL (x : OrhdL H) : rfE (endL (a := a) H hNH x) = ιL (fixL H) x.1 := rfl

include hτ in
lemma Bmap_endL_fixed (x : OrhdL H) :
    ∀ h' ∈ H.map (α : GK p E →* GK p E'),
      h' • Bmap F τ N a (endL (a := a) H hNH x) = Bmap F τ N a (endL (a := a) H hNH x) :=
  Bmap_fixed H hτ (endL_mem H hNH x) fun h hh => by
    rw [rfE_endL]; exact smul_ιL H x.1 hh

/-- **`x ↦ B(e_x)`, `O^▷_{K̄^H} → O^▷_{K̄^{α(H)}}`** ([FrdII], Theorem 2.4(i), `O^□` part). -/
noncomputable def psiFun (x : OrhdL H) : OrhdL (H.map (α : GK p E →* GK p E')) :=
  ⟨unitsOfFixed _ _ (Bmap_endL_fixed H hNH hτ x), by
    rw [← ord_nonneg_iff, ιL_unitsOfFixed]
    exact ord_Bmap_nonneg F τ N a (endL_mem H hNH x)⟩

lemma coe_psiFun (x : OrhdL H) :
    ιL _ (psiFun H hNH hτ x).1 = Bmap F τ N a (endL (a := a) H hNH x) :=
  ιL_unitsOfFixed _ _ (Bmap_endL_fixed H hNH hτ x)

lemma psiFun_mul (x y z : OrhdL H) (hz : z.1 = x.1 * y.1) :
    (psiFun H hNH hτ z).1 = (psiFun H hNH hτ x).1 * (psiFun H hNH hτ y).1 := by
  apply ιL_injective
  have he : endL (a := a) H hNH z = endL (a := a) H hNH x ≫ endL (a := a) H hNH y :=
    rfE_injective_orhd (endL_mem H hNH z) (Model.comp_mem_orhd (endL_mem H hNH x)
      (endL_mem H hNH y)) (by
        rw [rfE_comp (endL_mem H hNH x) (endL_mem H hNH y), rfE_endL, rfE_endL, rfE_endL, hz,
          map_mul])
  rw [map_mul, coe_psiFun, coe_psiFun, coe_psiFun, he,
    Bmap_comp F τ N a (endL_mem H hNH x) (endL_mem H hNH y)]

lemma psiFun_injective : Function.Injective (psiFun H hNH hτ) := by
  intro x y hxy
  have h := congrArg (fun z => ιL _ z.1) hxy
  simp only [coe_psiFun] at h
  have he := Bmap_injective F τ N a (endL_mem H hNH x) (endL_mem H hNH y) h
  have h2 := congrArg rfE he
  rw [rfE_endL, rfE_endL] at h2
  exact Subtype.ext (ιL_injective _ h2)

include hτ in
lemma psiFun_surjective
    (hstab : (F.obj (XN N a)).base.H = N.toSubgroup.map (α : GK p E →* GK p E')) :
    Function.Surjective (psiFun H hNH hτ) := by
  intro y
  obtain ⟨e, he, hBe⟩ := exists_Bmap_eq τ hstab (ιL _ y.1)
    (fun ν hν => smul_ιL _ y.1 (Subgroup.map_mono hNH hν)) (ord_mem_gammaQ _)
    ((ord_nonneg_iff _ y.1).mpr y.2)
  have hfix := rfE_fixed_of_Bmap H hτ he (fun h' hh' => by rw [hBe]; exact smul_ιL _ y.1 hh')
  refine ⟨⟨unitsOfFixed H _ hfix, ?_⟩, Subtype.ext (ιL_injective _ ?_)⟩
  · rw [← ord_nonneg_iff, ιL_unitsOfFixed]
    exact ord_rfE_nonneg he
  · rw [coe_psiFun, ← hBe]
    congr 1
    exact rfE_injective_orhd (endL_mem H hNH _) he (by rw [rfE_endL, ιL_unitsOfFixed])

/-- **`O^▷_{K̄^H} ≃ O^▷_{K̄^{α(H)}}` induced by `Ψ`** ([FrdII], Theorem 2.4(i):
`O^□(A₁)^{H₁} ≅ O^□(A₂)^{H₂}`, with `orhdFixEquiv`), multiplicative (`psiFun_mul`). -/
noncomputable def orhdPsiEquiv
    (hstab : (F.obj (XN N a)).base.H = N.toSubgroup.map (α : GK p E →* GK p E')) :
    OrhdL H ≃ OrhdL (H.map (α : GK p E →* GK p E')) :=
  Equiv.ofBijective (psiFun H hNH hτ)
    ⟨psiFun_injective H hNH hτ, psiFun_surjective H hNH hτ hstab⟩

end Psi

end PAdicGalois

end Frobenioid

end Iut
