/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.OrhdPsi

/-!
# The map `O^▷(X) → K̄^×` induced by `Ψ` ([FrdII], Theorem 2.4(ii))

[FrdII], Theorem 2.4(ii), proof: "by varying the objects `A_i` [that correspond via `Ψ`] and
reconstructing the multiplicative group associated to the field determined by the image of `A_i`
in `B(G_i, G_i°)` as the groupification of the monoid `O^▷(A_i) = O^□(A_i)` — `Ψ` induces a pair of
compatible isomorphisms `G₁ ≅ G₂`, `K̄₁^× ≅ K̄₂^×`".

For `Ψ : C(E) ≌ C(E')`, `α`, `τ` as in `exists_galHom_compat_orhd` and `X = (G_E/N, a)`, let
`B(e) = τ⁻¹ · γ_{Ψ e} ∈ K̄^×` for `e ∈ O^▷(X)` (`Bmap`). Here:

* `Bmap_comp`, `Bmap_id`: `B` is multiplicative on `O^▷(X)`;
* **`Bmap_conj`**: `B(galHom σ · e) = α(σ) · B(e)` (`α`-equivariance), while
  `rfE_conj_galHom`: `galHom σ` acts on `γ_e` by `σ`;
* `Bmap_injective`: `B` is injective on `O^▷(X)`; `ord_Bmap_nonneg`;
* **`exists_Bmap_eq`**: every `y ∈ (K̄^{α(N)})^×` with `ord y ∈ Γ_{≥0}` is `B(e)` for some
  `e ∈ O^▷(X)` (`Ψ` is full and preserves `O^▷`);
* **`val_betaPsi`**: on roots of unity `B` is `β_Ψ` of `Thm24ii.lean`.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open CategoryTheory Saturation

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime] {Γ : AddSubgroup ℝ}
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) Γ)
  (bGal (GK p E) (ord p) (ord_smul p E) Γ) (divGal (GK p E) (ord p) (ord_smul p E) Γ)

local notation "𝐏E'" => Model.toElem (constPhi (OrbitObj (GK p E')) Γ)
  (bGal (GK p E') (ord p) (ord_smul p E') Γ)
  (divGal (GK p E') (ord p) (ord_smul p E') Γ)

variable (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] (α : GK p E ≃ₜ* GK p E')
  (τ : GK p E') (N : OpenNormalSubgroup (GK p E)) (a : Γ)

/-- `galHom σ` as an automorphism of `X`. -/
noncomputable abbrev galIso (σ : GK p E) : XN N a ≅ XN N a :=
  show Aut (XN N a) from galHom N a σ

/-- **`galHom σ` acts on rational functions of `O^▷(X)` by `σ`.** -/
lemma rfE_conj_galHom (σ : GK p E) {e : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a)) :
    rfE (Model.conj (galIso N a σ) e) = σ • rfE e := by
  have h := GaloisModel.pb_galAut_inv (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹ e.u
  rw [inv_inv] at h
  unfold rfE
  rw [Model.conj_u_orhd _ he]
  change Additive.toMul ((bGal (GK p E) (ord p) (ord_smul p E) Γ).pb
    (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹).inv.base e.u).1 = _
  rw [h]
  rfl

/-- **`B(e) = τ⁻¹ · γ_{Ψ e}`** for `e ∈ O^▷(X)`. -/
noncomputable def Bmap (e : XN N a ⟶ XN N a) : K̄ˣ := τ⁻¹ • rfE (F.map e)

lemma map_mem_orhd {e : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a)) :
    F.map e ∈ Orhd 𝐏E' (F.obj (XN N a)) :=
  (mem_orhd_iff F e).mp he

lemma Bmap_comp {e e' : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a))
    (he' : e' ∈ Orhd 𝐏E (XN N a)) :
    Bmap F τ N a (e ≫ e') = Bmap F τ N a e * Bmap F τ N a e' := by
  unfold Bmap
  rw [F.map_comp, rfE_comp (map_mem_orhd F N a he) (map_mem_orhd F N a he'), smul_mul']

lemma Bmap_id : Bmap F τ N a (𝟙 _) = 1 := by
  unfold Bmap
  rw [F.map_id, rfE_id, smul_one]

lemma mapIso_galIso (σ : GK p E) :
    F.mapIso (galIso N a σ) =
      (show Aut (F.obj (XN N a)) from Model.autEquiv F (XN N a) (galHom N a σ)) :=
  Iso.ext rfl

variable {F α τ N a} in
/-- **`α`-equivariance of `B`.** -/
lemma Bmap_conj
    (hτ : ∀ (σ : GK p E) (e : F.obj (XN N a) ⟶ F.obj (XN N a)),
      e ∈ Orhd 𝐏E' (F.obj (XN N a)) →
      rfE (Model.conj (show Aut (F.obj (XN N a)) from
          Model.autEquiv F (XN N a) (galHom N a σ)) e) = (τ * α σ * τ⁻¹) • rfE e)
    (σ : GK p E) {e : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a)) :
    Bmap F τ N a (Model.conj (galIso N a σ) e) = α σ • Bmap F τ N a e := by
  unfold Bmap
  rw [Model.map_conj, mapIso_galIso, hτ σ _ (map_mem_orhd F N a he), smul_smul, smul_smul]
  congr 1
  group

lemma Bmap_injective {e e' : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a))
    (he' : e' ∈ Orhd 𝐏E (XN N a)) (h : Bmap F τ N a e = Bmap F τ N a e') : e = e' := by
  unfold Bmap at h
  exact F.map_injective (rfE_injective_orhd (map_mem_orhd F N a he) (map_mem_orhd F N a he')
    (MulAction.injective τ⁻¹ h))

lemma ord_smul_units (σ : GK p E') (x : K̄ˣ) :
    ord p (Additive.ofMul (σ • x)) = ord p (Additive.ofMul x) :=
  ord_smul p E' σ (Additive.ofMul x)

lemma ord_Bmap_nonneg {e : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a)) :
    0 ≤ ord p (Additive.ofMul (Bmap F τ N a e)) := by
  unfold Bmap
  rw [ord_smul_units]
  exact ord_rfE_nonneg (map_mem_orhd F N a he)

variable {F α N a} in
/-- **Surjectivity of `B` onto `O^▷` of `K̄^{α(N)}`.** -/
lemma exists_Bmap_eq (hstab : (F.obj (XN N a)).base.H = N.toSubgroup.map (α : GK p E →* GK p E'))
    (y : K̄ˣ) (hy : ∀ ν ∈ N.toSubgroup.map (α : GK p E →* GK p E'), ν • y = y)
    (hΓ : ord p (Additive.ofMul y) ∈ Γ) (h0 : 0 ≤ ord p (Additive.ofMul y)) :
    ∃ e : XN N a ⟶ XN N a, e ∈ Orhd 𝐏E (XN N a) ∧ Bmap F τ N a e = y := by
  have hnorm : (N.toSubgroup.map (α : GK p E →* GK p E')).Normal :=
    Subgroup.Normal.map inferInstance _ α.surjective
  have hfix : ∀ h ∈ (F.obj (XN N a)).base.H, h • (τ • y) = τ • y := by
    intro h hh
    rw [hstab] at hh
    have : τ⁻¹ * h * τ⁻¹⁻¹ ∈ N.toSubgroup.map (α : GK p E →* GK p E') := hnorm.conj_mem _ hh _
    rw [inv_inv] at this
    calc h • τ • y = τ • (τ⁻¹ * h * τ) • y := by rw [smul_smul, smul_smul]; congr 1; group
      _ = τ • y := by rw [hy _ this]
  have hΓ' : ord p (Additive.ofMul (τ • y)) ∈ Γ := by rw [ord_smul_units]; exact hΓ
  have h0' : 0 ≤ ord p (Additive.ofMul (τ • y)) := by rw [ord_smul_units]; exact h0
  let e' := endY (F.obj (XN N a)) (τ • y) hfix hΓ' h0'
  refine ⟨F.preimage e', (mem_orhd_iff F _).mpr ?_, ?_⟩
  · rw [F.map_preimage]
    exact endY_mem_orhd _ _ hfix hΓ' h0'
  · unfold Bmap
    rw [F.map_preimage, rfE_endY, inv_smul_smul]

variable (H : Subgroup (GK p E)) (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)

/-- **On roots of unity, `B` is `β_Ψ`.** -/
lemma val_betaPsi (ζ : KummerTheory.Mu n K̄) {e : XN N a ⟶ XN N a}
    (he : e ∈ Orhd 𝐏E (XN N a)) (hζ : rfE e = KummerTheory.Mu.val ζ) :
    KummerTheory.Mu.val (betaPsi F τ N a H n hs ζ) = Bmap F τ N a e := by
  set m := (uMuE N a H n hs).symm ζ with hm
  have hζm : uMu N a n m = ζ := (uMuE N a H n hs).apply_symm_apply ζ
  have hmo : (show Aut (XN N a) from ((m : Model.ouAut (XN N a)) : WithDisc (Aut (XN N a)))).hom
      ∈ Orhd 𝐏E (XN N a) :=
    ⟨(m : Model.ouAut (XN N a)).2.2.1, (m : Model.ouAut (XN N a)).2.2.2⟩
  have heq : (show Aut (XN N a) from ((m : Model.ouAut (XN N a)) : WithDisc (Aut (XN N a)))).hom
      = e := by
    refine rfE_injective_orhd hmo he ?_
    rw [hζ, ← hζm]
    rfl
  rw [← hζm, betaPsi_uMu, ← heq]
  rfl

end PAdicGalois

end Frobenioid

end Iut
