/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24iiAux

/-!
# [FrdII], Theorem 2.4(ii) for the perfected `p`-adic Frobenioid `C_v`

[FrdII], Theorem 2.4(ii): "If the `Φ_i` are fieldwise saturated, then the isomorphism
`F_N(A₁) ≅ F_N(A₂)` of (i) is compatible with the natural isomorphisms `F_N(A_i) ≅ ℤ/Nℤ`."

`Thm24ii.lean` reduces this (`thm24ii_of_pairing`) to one preserved unit pairing value. Here the
pairing condition is verified for `C_v = FrobPf` (`Φ = ℚ_{≥0}`, fieldwise saturated) and every
`(n, H)`-saturated `X = (G_E/N, a)` with `N ⊆ H`, following Mochizuki's proof (the field
`K̄^×` is recovered from `O^▷`, and `α` preserves the unramified quotient and Frobenius):

* `exists_unif_rel`: for a uniformiser `π` of `L = K̄^H` (whose `n`-th roots lie in `K̄^N`,
  `root_fixed`), the element `e_π ∈ O^▷(X)` is mapped by `B = τ⁻¹ γ_{Ψ(−)}` (`OrhdPsiMap.lean`)
  to a uniformiser `π'` of `L' = K̄^{α(H)}`: `B` is a multiplicative bijection
  `O^▷_L ≅ O^▷_{L'}` (`Ψ` is fully faithful, preserves `O^▷` and is `α`-equivariant) and
  uniformisers are the irreducible elements (`ValAux.val_eq_one_of_rel`);
* **`h1PairMap_kummer_unif`**: `Φ₁(κ(π)) = κ(π')` for `Φ₁ = (galPairEquiv, β_Ψ)_*` (`B` extends
  `β_Ψ` and is `α`-equivariant on `n`-th roots of `π`);
* with `χ = unrChar 1` (`UnrPairing.lean`, `pairing_unrChar_kummer`): `⟨χ, κ(π)⟩ = 1` is
  preserved, so **`thm24Pf_ii`**: for every equivalence `Ψ : C_v(E) ≌ C_v(E')` there is
  `α : G_E ≃ₜ* G_{E'}` such that, for every `(n, H)`-saturated `X = (G_E/N, a)` with `N ⊆ H`,
  `F_N(X) ≅ F_N(Ψ X) → H²(L', μ_n) ≅ ℤ/n` equals `fnEquiv : F_N(X) ≅ ℤ/n`.

The condition `N ⊆ H` is harmless: `(n, H)`-saturated objects with `N ⊆ H` exist for every `H`
(`exists_isSaturatedPf` gives all `N ⊆ N₀`). For `C^⊢_v` the statement is false in general
([FrdII], Remark 2.4.2), and `ord(K̄^×) ⊆ ℚ` (`ord_mem_gammaQ`), used to see every element of
`O^▷_L` as a rational function of `X`, is where `Γ = ℚ` enters.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaQ) (divGal (GK p E) (ord p) (ord_smul p E) gammaQ)

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) gammaQ)
  (bGal (GK p E') (ord p) (ord_smul p E') gammaQ)
  (divGal (GK p E') (ord p) (ord_smul p E') gammaQ)

variable (F : FrobPf p E ⥤ FrobPf p E') [F.IsEquivalence] (α : GK p E ≃ₜ* GK p E')
  (τ : GK p E') (N : OpenNormalSubgroup (GK p E)) (a : gammaQ)

/-- The rational-function compatibility of `exists_galHom_compat_orhd`. -/
def OrhdCompat : Prop :=
  ∀ (σ : GK p E) (e : F.obj (XN N a) ⟶ F.obj (XN N a)), e ∈ Orhd 𝐏E' (F.obj (XN N a)) →
    rfE (Model.conj (show Aut (F.obj (XN N a)) from
      Model.autEquiv F (XN N a) (galHom N a σ)) e) = (τ * α σ * τ⁻¹) • rfE e

variable {F α τ N a}

/-- The units version (`hρ` of `Thm24ii.lean`) follows from the `O^▷` version. -/
lemma ratFunTw_of_orhdCompat (hτ : OrhdCompat F α τ N a) (σ' : GK p E')
    (v : Model.ouAut (F.obj (XN N a))) :
    ratFunTw τ (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
      σ' • ratFunTw τ v := by
  have h : ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a)))
      (Model.autEquiv F (XN N a) (galHom N a (α.symm σ'))) v) =
      (τ * α (α.symm σ') * τ⁻¹) • ratFunY v := by
    unfold ratFunY
    rw [KummerClass.coe_conjU, Model.conj_hom]
    exact hτ (α.symm σ') _ ⟨v.2.2.1, v.2.2.2⟩
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  change τ⁻¹ • ratFunY (KummerClass.conjU (Model.ouAut (F.obj (XN N a)))
    (Model.autEquiv F (XN N a) (galHom N a (α.symm σ'))) v) = σ' • τ⁻¹ • ratFunY v
  rw [h, smul_smul, smul_smul]
  congr 1
  group

variable (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))

/-- `B(e)` is fixed by `α(H)` if `γ_e` is fixed by `H`. -/
lemma Bmap_fixed (hτ : OrhdCompat F α τ N a) {e : XN N a ⟶ XN N a}
    (he : e ∈ Orhd 𝐏E (XN N a)) (hfix : ∀ h ∈ H, h • rfE e = rfE e) :
    ∀ h' ∈ H.map (α : GK p E →* GK p E'), h' • Bmap F τ N a e = Bmap F τ N a e := by
  rintro _ ⟨h, hh, rfl⟩
  have hc : Model.conj (galIso N a h) e = e := rfE_injective_orhd
    (Model.conj_mem_orhd _ he) he ((rfE_conj_galHom N a h he).trans (hfix h hh))
  have := Bmap_conj hτ h he
  rw [hc] at this
  exact this.symm

/-- `γ_e` is fixed by `H` if `B(e)` is fixed by `α(H)`. -/
lemma rfE_fixed_of_Bmap (hτ : OrhdCompat F α τ N a) {e : XN N a ⟶ XN N a}
    (he : e ∈ Orhd 𝐏E (XN N a))
    (hfix : ∀ h' ∈ H.map (α : GK p E →* GK p E'), h' • Bmap F τ N a e = Bmap F τ N a e) :
    ∀ h ∈ H, h • rfE e = rfE e := by
  intro h hh
  have hc : Model.conj (galIso N a h) e = e := Bmap_injective F τ N a
    (Model.conj_mem_orhd _ he) he
    ((Bmap_conj hτ h he).trans (hfix _ ⟨h, hh, rfl⟩))
  rw [← rfE_conj_galHom N a h he, hc]

variable (hNH : N.toSubgroup ≤ H)

include hNH in
lemma ιL_fixed_N (x : (fixL H)ˣ) {ν : GK p E} (hν : ν ∈ (XN N a).base.H) :
    ν • ιL (fixL H) x = ιL (fixL H) x :=
  smul_ιL H x (hNH hν)

/-- The correspondence `x ↦ y` iff `x = γ_e`, `y = B(e)` for some `e ∈ O^▷(X)`. -/
def RelB (x : (fixL H)ˣ) (y : (fixL (H.map (α : GK p E →* GK p E')))ˣ) : Prop :=
  ∃ e : XN N a ⟶ XN N a, e ∈ Orhd 𝐏E (XN N a) ∧ rfE e = ιL (fixL H) x ∧
    Bmap F τ N a e = ιL (fixL (H.map (α : GK p E →* GK p E'))) y

include hH hNH in
/-- **`B` maps a uniformiser of `L` to a uniformiser of `L'`.** -/
theorem exists_unif_rel (hτ : OrhdCompat F α τ N a)
    (hstab : (F.obj (XN N a)).base.H = N.toSubgroup.map (α : GK p E →* GK p E'))
    (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) : Set (GK p E'))) :
    haveI := finiteDimensional_fixL_padic H hH
    haveI := finiteDimensional_fixL_padic _ hH'
    ∃ (π : (fixL H)ˣ) (π' : (fixL (H.map (α : GK p E →* GK p E')))ˣ),
      v p (π : fixL H) = 1 ∧ v p (π' : fixL (H.map (α : GK p E →* GK p E'))) = 1 ∧
      RelB (F := F) (α := α) (τ := τ) (N := N) (a := a) H π π' := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI := finiteDimensional_fixL_padic _ hH'
  set H' := H.map (α : GK p E →* GK p E')
  set R := RelB (F := F) (α := α) (τ := τ) (N := N) (a := a) H
  have hvL : ∀ x y : (fixL H)ˣ, v p ((x * y : (fixL H)ˣ) : fixL H) =
      v p (x : fixL H) + v p (y : fixL H) := fun x y => by
    rw [Units.val_mul, v_mul x.ne_zero y.ne_zero]
  have hvL' : ∀ x y : (fixL H')ˣ, v p ((x * y : (fixL H')ˣ) : fixL H') =
      v p (x : fixL H') + v p (y : fixL H') := fun x y => by
    rw [Units.val_mul, v_mul x.ne_zero y.ne_zero]
  have hR1 : R 1 1 := ⟨𝟙 _, Model.id_mem_orhd _, by rw [rfE_id, map_one],
    by rw [Bmap_id, map_one]⟩
  have hRmul : ∀ x x' y y', R x y → R x' y' → R (x * x') (y * y') := by
    rintro x x' y y' ⟨e, he, h1, h2⟩ ⟨e', he', h1', h2'⟩
    exact ⟨e ≫ e', Model.comp_mem_orhd he he', by rw [rfE_comp he he', h1, h1', map_mul],
      by rw [Bmap_comp F τ N a he he', h2, h2', map_mul]⟩
  have hRfun : ∀ x y y', R x y → R x y' → y = y' := by
    rintro x y y' ⟨e, he, h1, h2⟩ ⟨e', he', h1', h2'⟩
    have := rfE_injective_orhd he he' (h1.trans h1'.symm)
    subst this
    exact ιL_injective _ (h2.symm.trans h2')
  have hRinj : ∀ (x x' : (fixL H)ˣ) (y : (fixL H')ˣ), 0 ≤ v p (x : fixL H) →
      0 ≤ v p (x' : fixL H) → R x y → R x' y →
      x = x' := by
    rintro x x' y - - ⟨e, he, h1, h2⟩ ⟨e', he', h1', h2'⟩
    have := Bmap_injective F τ N a he he' (h2.trans h2'.symm)
    subst this
    exact ιL_injective _ (h1.symm.trans h1')
  have hRtot : ∀ x : (fixL H)ˣ, 0 ≤ v p (x : fixL H) → ∃ y, R x y := by
    intro x hx
    let e := endY (XN N a) (ιL (fixL H) x) (fun _ hν => ιL_fixed_N H hNH x hν)
      (ord_mem_gammaQ _) ((ord_nonneg_iff _ x).mpr hx)
    have he : e ∈ Orhd 𝐏E (XN N a) := endY_mem_orhd _ _ _ _ _
    have hfix := Bmap_fixed H hτ he (fun h hh => by
      rw [rfE_endY]; exact smul_ιL H x hh)
    exact ⟨unitsOfFixed H' _ hfix, e, he, rfE_endY _ _ _ _ _, (ιL_unitsOfFixed _ _ _).symm⟩
  have hRsurj : ∀ y : (fixL H')ˣ, 0 ≤ v p (y : fixL H') →
      ∃ x : (fixL H)ˣ, 0 ≤ v p (x : fixL H) ∧ R x y := by
    intro y hy
    obtain ⟨e, he, hBe⟩ := exists_Bmap_eq τ hstab (ιL (fixL H') y)
      (fun ν hν => smul_ιL H' y (Subgroup.map_mono hNH hν)) (ord_mem_gammaQ _)
      ((ord_nonneg_iff _ y).mpr hy)
    have hfix := rfE_fixed_of_Bmap H hτ he (fun h' hh' => by rw [hBe]; exact smul_ιL H' y hh')
    refine ⟨unitsOfFixed H _ hfix, ?_, e, he, (ιL_unitsOfFixed _ _ _).symm, hBe⟩
    rw [← ord_nonneg_iff, ιL_unitsOfFixed]
    exact ord_rfE_nonneg he
  have hRmem : ∀ (x : (fixL H)ˣ) (y : (fixL H')ˣ), 0 ≤ v p (x : fixL H) → R x y →
      0 ≤ v p (y : fixL H') := by
    rintro x y - ⟨e, he, -, h2⟩
    rw [← ord_nonneg_iff, ← h2]
    exact ord_Bmap_nonneg F τ N a he
  obtain ⟨π₀, hπ₀⟩ := exists_uniformizer (p := p) (K := fixL H)
  obtain ⟨π₀', hπ₀'⟩ := exists_uniformizer (p := p) (K := fixL H')
  let π := Units.mk0 π₀ hπ₀.ne_zero
  let π' := Units.mk0 π₀' hπ₀'.ne_zero
  have hπ : v p (π : fixL H) = 1 := hπ₀
  have hπ' : v p (π' : fixL H') = 1 := hπ₀'
  obtain ⟨y, hy⟩ := hRtot π (by rw [hπ]; omega)
  exact ⟨π, y, hπ, ValAux.val_eq_one_of_rel _ _ hvL hvL' R hR1 hRmul hRfun hRinj hRtot hRsurj
    hRmem hπ' hπ hy, hy⟩

end PAdicGalois

end Frobenioid

end Iut
