/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Model

/-!
# The model Frobenioid is a Frobenioid ([FrdI], Theorem 5.2(ii))

**Theorem 5.2(ii)** ([FrdI], p. 101): for a connected totally epimorphic base category `D`, a
divisorial monoid `Φ`, a group-like monoid `B` and `Div_B : B → Φ^gp`, the model Frobenioid
`Model Φ B divB` (with `Model.toElem`) is a Frobenioid of isotropic type
(`Model.isFrobenioid`, `Model.isIsotropic`). [FrdI] calls the proof "a routine verification";
here every clause of Definition 1.3 is checked. The key facts are those of
`Iut/Frobenioid/Model.lean`: isometric pre-steps are isomorphisms (so every object is isotropic
and every morphism is co-angular) and pull-back morphisms are the linear isometric morphisms.

Explicit witnesses:

* (i)(a): the Frobenius-trivial objects `(A_D, 0)` with `ζ(n) = (n, id, 0, 0)` (the
  base-Frobenius pair of the proof of Theorem 5.2);
* (i)(b): for `α : A_D ≅ B_D`, the pre-steps `(A_D, −(q₁ + q₂)) → A, B` where
  `A.α = p₁ − q₁`, `α^* B.α = p₂ − q₂` (generation of `Φ^gp` by `Φ`);
* (ii): `(n, id, 0, 0) : (A_D, α) → (A_D, n·α)`;
* (iv)(a): `(A_D, α) → (A_D, n·α) → (A_D, f^*β) → (B_D, β)`, with the pre-step `(1, id, Z, u)`.

Also: Theorem 5.1(i) for the model, `Model.nonempty_iso_iff`: two objects over the same base are
isomorphic via a base-identity isomorphism iff their divisors differ by `Div_B` of a rational
function, i.e. `Pic_C(A) = Φ^gp(A)/Φ^birat(A)`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

namespace Model

local notation "𝐏" => toElem Φ B divB

/-! ### Simple characterizations -/

lemma isPreStep_iff {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsPreStep 𝐏 φ ↔ φ.deg = 1 ∧ IsIso φ.base := Iff.rfl

lemma isPreStep_mk1 {X Y : Model Φ B divB} (f : X.base ⟶ Y.base) [IsIso f] (Z hZ u h) :
    IsPreStep 𝐏 (mk1 (X := X) (Y := Y) f Z hZ u h) := ⟨rfl, ‹IsIso f›⟩

lemma isFrobeniusType_iff {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsFrobeniusType 𝐏 φ ↔ φ.div = 0 ∧ IsIso φ.base :=
  ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨isCoangular φ, h.1⟩, h.2⟩⟩

variable (Φ B divB) in
/-- The object `(A, 0)`. -/
abbrev zeroObj (A : D) : Model Φ B divB := ⟨A, 0⟩

variable (Φ B divB) in
/-- The zero section `D ⥤ Model`, `A ↦ (A, 0)`, `f ↦ (1, f, 0, 0)`. -/
def zeroSection : D ⥤ Model Φ B divB where
  obj A := zeroObj Φ B divB A
  map f := mk1 f 0 (Φ.pos _).zero_mem 0 (by simp)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-! ### `C` is connected and totally epimorphic -/

instance [TotallyEpimorphic D] : TotallyEpimorphic (Model Φ B divB) where
  epi φ := ⟨fun ψ₁ ψ₂ h => by
    have hdeg : ψ₁.deg = ψ₂.deg := mul_right_cancel (congrArg Hom.deg h)
    have hb : ψ₁.base = ψ₂.base := TotallyEpimorphic.cancel φ.base (congrArg Hom.base h)
    have hdiv := congrArg Hom.div h
    have hu := congrArg Hom.u h
    simp only [comp_div, comp_u, hdeg, add_left_inj] at hdiv hu
    exact hom_ext hdeg hb (Φ.pb_injective _ hdiv) (B.pb_injective _ hu)⟩

/-- Every object is linked by pre-steps to `(A_D, 0)`. -/
lemma zigzag_zero (X : Model Φ B divB) : Zigzag X (zeroObj Φ B divB X.base) := by
  obtain ⟨p, hp, q, hq, he⟩ := Φ.generating X.α
  have f₁ : (⟨X.base, -q⟩ : Model Φ B divB) ⟶ X := mk1 (𝟙 _) p hp 0 (by simp [he]; abel)
  have f₂ : (⟨X.base, -q⟩ : Model Φ B divB) ⟶ zeroObj Φ B divB X.base :=
    mk1 (𝟙 _) q hq 0 (by simp)
  exact (Zigzag.of_inv f₁).trans (Zigzag.of_hom f₂)

instance [IsConnected D] : IsConnected (Model Φ B divB) := by
  haveI : Nonempty (Model Φ B divB) :=
    ⟨zeroObj Φ B divB (Classical.arbitrary D)⟩
  refine zigzag_isConnected fun X Y => ?_
  exact (zigzag_zero X).trans ((zigzag_obj_of_zigzag (zeroSection Φ B divB)
    (isPreconnected_zigzag X.base Y.base)).trans (zigzag_zero Y).symm)

/-! ### Definition 1.3 (i) -/

/-- The objects `(A_D, 0)` are Frobenius-trivial. -/
theorem isFrobeniusTrivial_zero (A : D) :
    IsFrobeniusTrivial 𝐏 (zeroObj Φ B divB A) := by
  refine ⟨fun n => mk' n (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp), ?_, ?_, fun n => ?_⟩
  · ext <;> simp
  · intro m n
    ext <;> simp [mul_comm]
  · exact ⟨rfl, rfl, (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [mk'_base]; infer_instance⟩⟩

lemma preStep_span (X Y : Model Φ B divB) (α : X.base ≅ Y.base) :
    ∃ (E : Model Φ B divB) (φ : E ⟶ X) (ψ : E ⟶ Y),
      IsPreStep 𝐏 φ ∧ IsPreStep 𝐏 ψ ∧ Base 𝐏 φ ≫ α.hom = Base 𝐏 ψ := by
  obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := Φ.generating X.α
  obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := Φ.generating (Φ.pb α.hom Y.α)
  refine ⟨⟨X.base, -(q₁ + q₂)⟩, mk1 (𝟙 _) (p₁ + q₂) ((Φ.pos _).add_mem hp₁ hq₂) 0 ?_,
    mk1 α.hom (p₂ + q₁) ((Φ.pos _).add_mem hp₂ hq₁) 0 ?_, isPreStep_mk1 _ _ _ _ _,
    isPreStep_mk1 _ _ _ _ _, ?_⟩
  · simp [h₁]; abel
  · simp [h₂]; abel
  · simp

lemma pullback_surj (X : Model Φ B divB) (Y : D) (f : Y ⟶ X.base) :
    ∃ (W : Model Φ B divB) (φ : W ⟶ X) (e : Frobenioid.base 𝐏 W ≅ Y),
      IsPullback 𝐏 φ ∧ e.hom ≫ f = Base 𝐏 φ := by
  refine ⟨⟨Y, Φ.pb f X.α⟩, mk1 f 0 (Φ.pos _).zero_mem 0 (by simp), Iso.refl _,
    (isPullback_iff _).mpr ⟨rfl, rfl⟩, ?_⟩
  simp

/-! ### Definition 1.3 (ii) -/

lemma frobenius (X : Model Φ B divB) (n : ℕ+) :
    ∃ (Y : Model Φ B divB) (φ : X ⟶ Y), IsFrobeniusType 𝐏 φ ∧ degFr 𝐏 φ = n ∧
      ∀ (E : Model Φ B divB) (ψ : X ⟶ E), IsFrobeniusType 𝐏 ψ → degFr 𝐏 ψ = n →
        ∃ β : Y ≅ E, φ ≫ β.hom = ψ := by
  refine ⟨⟨X.base, (n : ℕ) • X.α⟩, mk' n (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp),
    (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [mk'_base]; infer_instance⟩, rfl, ?_⟩
  intro E ψ hψ hn
  obtain ⟨h₀, hb⟩ := (isFrobeniusType_iff ψ).mp hψ
  have hn' : ψ.deg = n := hn
  let β : (⟨X.base, (n : ℕ) • X.α⟩ : Model Φ B divB) ⟶ E :=
    mk1 ψ.base 0 (Φ.pos _).zero_mem ψ.u (by
      have := ψ.rel
      rw [hn', h₀] at this
      simpa using this)
  haveI : IsIso β := isIso_of β rfl hb rfl
  refine ⟨asIso β, ?_⟩
  ext <;> simp [β, hn', h₀]

/-! ### Definition 1.3 (iii) -/

/-- The bijection `O^▷(A) ≅ O^▷(B)` induced by a base isomorphism `f`:
`(1, id, Z, u) ↦ (1, id, (f⁻¹)^*Z, (f⁻¹)^*u)`. -/
noncomputable def orhdEquiv {X Y : Model Φ B divB} (f : X.base ⟶ Y.base) [IsIso f] :
    Orhd 𝐏 X ≃ Orhd 𝐏 Y where
  toFun a := ⟨mk' 1 (𝟙 _) (Φ.pb (inv f) a.1.div) (Φ.pb_mem _ a.1.div_mem)
      (B.pb (inv f) a.1.u) (by
        have h := a.1.rel
        rw [show a.1.deg = 1 from a.2.2, show a.1.base = 𝟙 _ from a.2.1] at h
        simp only [PNat.one_coe, one_smul, GrpOn.pb_id', add_right_inj] at h
        simp [h, divB.natural]), rfl, rfl⟩
  invFun b := ⟨mk' 1 (𝟙 _) (Φ.pb f b.1.div) (Φ.pb_mem _ b.1.div_mem)
      (B.pb f b.1.u) (by
        have h := b.1.rel
        rw [show b.1.deg = 1 from b.2.2, show b.1.base = 𝟙 _ from b.2.1] at h
        simp only [PNat.one_coe, one_smul, GrpOn.pb_id', add_right_inj] at h
        simp [h, divB.natural]), rfl, rfl⟩
  left_inv a := Subtype.ext (hom_ext (by simpa using (show a.1.deg = 1 from a.2.2).symm)
    (by simpa using (show a.1.base = 𝟙 _ from a.2.1).symm) (by simp) (by simp))
  right_inv b := Subtype.ext (hom_ext (by simpa using (show b.1.deg = 1 from b.2.2).symm)
    (by simpa using (show b.1.base = 𝟙 _ from b.2.1).symm) (by simp) (by simp))

lemma orhd_equiv {X Y : Model Φ B divB} (φ : X ⟶ Y) (hφ : IsPreStep 𝐏 φ) :
    ∃ e : Orhd 𝐏 X ≃ Orhd 𝐏 Y, ∀ φ' : X ⟶ Y, IsCoangular 𝐏 φ' → IsPreStep 𝐏 φ' →
      Base 𝐏 φ' = Base 𝐏 φ → ∀ a, φ' ≫ (e a).1 = a.1 ≫ φ' := by
  haveI : IsIso φ.base := hφ.2
  refine ⟨orhdEquiv φ.base, fun φ' _ hφ' hb a => ?_⟩
  have hb' : φ'.base = φ.base := hb
  have h1 : φ'.deg = 1 := hφ'.1
  have ha1 : a.1.deg = 1 := a.2.2
  have hab : a.1.base = 𝟙 _ := a.2.1
  ext
  · simp [orhdEquiv, h1, ha1]
  · simp [orhdEquiv, hab]
  · simp [orhdEquiv, h1, hab, hb', add_comm]
  · simp [orhdEquiv, h1, hab, hb', add_comm]

lemma coslice_surj (X : Model Φ B divB) (z : Φ.obj X.base) (hz : z ∈ Φ.pos X.base) :
    ∃ (Y : Model Φ B divB) (φ : X ⟶ Y), IsCoangular 𝐏 φ ∧ IsPreStep 𝐏 φ ∧ Div 𝐏 φ = z :=
  ⟨⟨X.base, X.α + z⟩, mk1 (𝟙 _) z hz 0 (by simp), isCoangular _, isPreStep_mk1 _ _ _ _ _, rfl⟩

lemma coslice_full {X Y₁ Y₂ : Model Φ B divB} (φ₁ : X ⟶ Y₁) (φ₂ : X ⟶ Y₂)
    (h₁ : IsPreStep 𝐏 φ₁) (h₂ : IsPreStep 𝐏 φ₂) (hle : Φ.le (Div 𝐏 φ₁) (Div 𝐏 φ₂)) :
    ∃ χ : Y₁ ⟶ Y₂, IsCoangular 𝐏 χ ∧ IsPreStep 𝐏 χ ∧ φ₁ ≫ χ = φ₂ := by
  haveI : IsIso φ₁.base := h₁.2
  haveI : IsIso φ₂.base := h₂.2
  have d₁ : φ₁.deg = 1 := h₁.1
  have d₂ : φ₂.deg = 1 := h₂.1
  let χ : Y₁ ⟶ Y₂ := mk1 (inv φ₁.base ≫ φ₂.base) (Φ.pb (inv φ₁.base) (φ₂.div - φ₁.div))
    (Φ.pb_mem _ hle) (B.pb (inv φ₁.base) (φ₂.u - φ₁.u)) (by
      have r₁ := congrArg (Φ.pb (inv φ₁.base)) φ₁.rel
      have r₂ := congrArg (Φ.pb (inv φ₁.base)) φ₂.rel
      rw [d₁] at r₁
      rw [d₂] at r₂
      simp only [PNat.one_coe, one_smul, map_add, GrpOn.pb_inv_pb, ← divB.natural] at r₁ r₂
      simp only [map_sub, GrpOn.pb_comp']
      linear_combination (norm := module) r₂ - r₁)
  refine ⟨χ, isCoangular _, isPreStep_mk1 _ _ _ _ _, ?_⟩
  ext <;> simp [χ, d₁, d₂]

lemma slice_surj (X : Model Φ B divB) (z : Φ.obj X.base) (hz : z ∈ Φ.pos X.base) :
    ∃ (Y : Model Φ B divB) (ψ : Y ⟶ X), IsCoangular 𝐏 ψ ∧ IsPreStep 𝐏 ψ ∧
      Div 𝐏 ψ = Φ.pb (Base 𝐏 ψ) z :=
  ⟨⟨X.base, X.α - z⟩, mk1 (𝟙 _) z hz 0 (by simp), isCoangular _, isPreStep_mk1 _ _ _ _ _,
    show (z : Φ.obj X.base) = Φ.pb (𝟙 X.base) z by simp⟩

lemma slice_full {X Y₁ Y₂ : Model Φ B divB} (ψ₁ : Y₁ ⟶ X) (ψ₂ : Y₂ ⟶ X) (z₁ z₂ : Φ.obj X.base)
    (h₁ : IsPreStep 𝐏 ψ₁) (h₂ : IsPreStep 𝐏 ψ₂) (e₁ : Div 𝐏 ψ₁ = Φ.pb (Base 𝐏 ψ₁) z₁)
    (e₂ : Div 𝐏 ψ₂ = Φ.pb (Base 𝐏 ψ₂) z₂) (hle : Φ.le z₂ z₁) :
    ∃ χ : Y₁ ⟶ Y₂, IsCoangular 𝐏 χ ∧ IsPreStep 𝐏 χ ∧ χ ≫ ψ₂ = ψ₁ := by
  haveI : IsIso ψ₁.base := h₁.2
  haveI : IsIso ψ₂.base := h₂.2
  have d₁ : ψ₁.deg = 1 := h₁.1
  have d₂ : ψ₂.deg = 1 := h₂.1
  have e₁' : ψ₁.div = Φ.pb ψ₁.base z₁ := e₁
  have e₂' : ψ₂.div = Φ.pb ψ₂.base z₂ := e₂
  have hg : (ψ₁.base ≫ inv ψ₂.base) ≫ ψ₂.base = ψ₁.base := by simp
  let χ : Y₁ ⟶ Y₂ := mk1 (ψ₁.base ≫ inv ψ₂.base) (Φ.pb ψ₁.base (z₁ - z₂))
    (Φ.pb_mem _ hle) (ψ₁.u - B.pb (ψ₁.base ≫ inv ψ₂.base) ψ₂.u) (by
      have r₁ := ψ₁.rel
      have r₂ := congrArg (Φ.pb (ψ₁.base ≫ inv ψ₂.base)) ψ₂.rel
      rw [d₁, e₁'] at r₁
      rw [d₂, e₂'] at r₂
      simp only [PNat.one_coe, one_smul, map_add, ← GrpOn.pb_comp', hg, ← divB.natural] at r₁ r₂
      simp only [map_sub]
      linear_combination (norm := module) r₁ - r₂)
  refine ⟨χ, isCoangular _, isPreStep_mk1 _ _ _ _ _, ?_⟩
  ext
  · simp [χ, d₁, d₂]
  · simp [χ]
  · simp only [comp_div, χ, mk1_base, mk1_div, d₂, PNat.one_coe, one_smul, e₂', e₁',
      ← GrpOn.pb_comp', hg, map_sub]
    abel
  · simp only [comp_u, χ, mk1_base, mk1_u, d₂, PNat.one_coe, one_smul]
    abel

/-! ### Definition 1.3 (iv)–(vii) -/

lemma factorization {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ∃ (X' Y' : Model Φ B divB) (γ : X ⟶ X') (β : X' ⟶ Y') (α : Y' ⟶ Y),
      IsFrobeniusType 𝐏 γ ∧ IsPreStep 𝐏 β ∧ IsPullback 𝐏 α ∧ γ ≫ β ≫ α = φ := by
  refine ⟨⟨X.base, (φ.deg : ℕ) • X.α⟩, ⟨X.base, Φ.pb φ.base Y.α⟩,
    mk' φ.deg (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp),
    mk1 (𝟙 _) φ.div φ.div_mem φ.u (by simpa using φ.rel),
    mk1 φ.base 0 (Φ.pos _).zero_mem 0 (by simp),
    (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [mk'_base]; infer_instance⟩,
    isPreStep_mk1 _ _ _ _ _, (isPullback_iff _).mpr ⟨rfl, rfl⟩,
    ?_⟩
  ext <;> simp

lemma pullback_lb {X Y : Model Φ B divB} (φ : X ⟶ Y) (h : IsPullback 𝐏 φ) :
    IsLBInvertible 𝐏 φ ∧ IsLinear 𝐏 φ :=
  ⟨⟨isCoangular φ, ((isPullback_iff φ).mp h).2⟩, ((isPullback_iff φ).mp h).1⟩

lemma preStep_mono {X Y : Model Φ B divB} (φ : X ⟶ Y) (h : IsPreStep 𝐏 φ) : Mono φ := by
  haveI : IsIso φ.base := h.2
  have d : φ.deg = 1 := h.1
  refine ⟨fun χ₁ χ₂ e => ?_⟩
  have hdeg : χ₁.deg = χ₂.deg := by simpa [d] using congrArg Hom.deg e
  have hb : χ₁.base = χ₂.base := (cancel_mono φ.base).mp (congrArg Hom.base e)
  have hdiv := congrArg Hom.div e
  have hu := congrArg Hom.u e
  simp only [comp_div, comp_u, d, PNat.one_coe, one_smul, hb, add_right_inj] at hdiv hu
  exact hom_ext hdeg hb hdiv hu

lemma isIso_of_isometric_preStep {X Y : Model Φ B divB} (φ : X ⟶ Y) (h₀ : IsIsometric 𝐏 φ)
    (h : IsPreStep 𝐏 φ) : IsIso φ := isIsotropic X Y φ h₀ h

lemma units {X Y : Model Φ B divB} (φ ψ : X ⟶ Y) (hφ : IsPreStep 𝐏 φ) (hψ : IsPreStep 𝐏 ψ)
    (hb : Base 𝐏 φ = Base 𝐏 ψ) (hd : Div 𝐏 φ = Div 𝐏 ψ) : ∃ a ∈ Ounits 𝐏 Y, φ = ψ ≫ a := by
  haveI : IsIso φ.base := hφ.2
  have hb' : ψ.base = φ.base := hb.symm
  have hd' : ψ.div = φ.div := hd.symm
  have d₁ : φ.deg = 1 := hφ.1
  have d₂ : ψ.deg = 1 := hψ.1
  have hdu : divB.app X.base φ.u = divB.app X.base ψ.u := by
    have r₁ := φ.rel
    have r₂ := ψ.rel
    rw [d₁] at r₁
    rw [d₂, hb', hd'] at r₂
    exact add_left_cancel (r₁.symm.trans r₂)
  let a : Y ⟶ Y := mk1 (𝟙 _) 0 (Φ.pos _).zero_mem (B.pb (inv φ.base) (φ.u - ψ.u)) (by
    simp [divB.natural, hdu])
  refine ⟨a, ⟨isIso_of a rfl (inferInstanceAs (IsIso (𝟙 Y.base))) rfl, rfl, rfl⟩, ?_⟩
  ext
  · simp [a, d₁, d₂]
  · simp [a, hb']
  · simp [a, hd']
  · simp [a, hb']

/-! ### Theorem 5.2(ii) -/

/-- **[FrdI], Theorem 5.2(ii)**: the model Frobenioid is a Frobenioid (of isotropic type). -/
theorem isFrobenioid [IsConnected D] [TotallyEpimorphic D] : IsFrobenioid 𝐏 where
  connected_D := inferInstance
  epi_D := inferInstance
  connected_C := inferInstance
  epi_C := inferInstance
  base_surj X := ⟨_, isFrobeniusTrivial_zero X, ⟨Iso.refl _⟩⟩
  preStep_span := preStep_span
  pullback_surj := pullback_surj
  frobenius := frobenius
  coangular_comp φ ψ _ _ := isCoangular _
  coangular_of_preStep _ ψ _ _ := isCoangular ψ
  orhd_equiv φ _ hφ := orhd_equiv φ hφ
  coslice_surj := coslice_surj
  coslice_full φ₁ φ₂ _ h₁ _ h₂ hle := coslice_full φ₁ φ₂ h₁ h₂ hle
  slice_surj := slice_surj
  slice_full ψ₁ ψ₂ z₁ z₂ _ h₁ _ h₂ e₁ e₂ hle := slice_full ψ₁ ψ₂ z₁ z₂ h₁ h₂ e₁ e₂ hle
  factorization := factorization
  factorization_unique γ β α γ' β' α' hγ hβ hα hγ' hβ' hα' h := by
    refine factorization_unique_of (P := 𝐏) (fun {A X X'} γ γ' hγ hγ' hdeg => ?_)
      γ β α γ' β' α' hγ hβ hα hγ' hβ' hα' (pullback_lb α hα).2 (pullback_lb α' hα').2 h
    obtain ⟨Y, φ, -, -, hu⟩ := frobenius A (degFr 𝐏 γ)
    obtain ⟨b₁, hb₁⟩ := hu X γ hγ rfl
    obtain ⟨b₂, hb₂⟩ := hu X' γ' hγ' hdeg.symm
    exact ⟨b₁.symm ≪≫ b₂, by simp [← hb₁, ← hb₂]⟩
  pullback_lb := pullback_lb
  preStep_mono := preStep_mono
  preStep_factor φ hφ := ⟨_, φ, 𝟙 _, Div_id _, ⟨rfl, isIso_Base (P := 𝐏) (𝟙 _)⟩,
    isCoangular φ, hφ, Category.comp_id _⟩
  preStep_factor_unique β α β' α' h₀ hα _ _ h₀' hα' _ _ h := by
    haveI := isIso_of_isometric_preStep α h₀ hα
    haveI := isIso_of_isometric_preStep α' h₀' hα'
    refine ⟨asIso α' ≪≫ (asIso α).symm, by simp, ?_⟩
    simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv]
    rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  preStep_factor' φ hφ := ⟨_, 𝟙 _, φ, isCoangular φ, hφ, Div_id _,
    ⟨rfl, isIso_Base (P := 𝐏) (𝟙 _)⟩, Category.id_comp _⟩
  preStep_factor'_unique β α β' α' _ _ h₀ hβ _ _ h₀' hβ' h := by
    haveI := isIso_of_isometric_preStep β h₀ hβ
    haveI := isIso_of_isometric_preStep β' h₀' hβ'
    refine ⟨(asIso β').symm ≪≫ asIso β, ?_, by simp⟩
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc, h]
    simp
  units φ ψ _ hφ _ hψ hb hd := units φ ψ hφ hψ hb hd
  isotropicHull A := ⟨A, 𝟙 A, Div_id _, ⟨rfl, isIso_Base (P := 𝐏) (𝟙 _)⟩,
    isIsotropic A, fun _ γ _ => ⟨γ, Category.id_comp γ, fun _ h => by simpa using h⟩⟩
  isotropic_cod _ _ := isIsotropic _

/-! ### Theorem 5.1(i) for the model: `Pic_C(A) = Φ^gp(A)/Φ^birat(A)` -/

/-- **Isomorphism classes over a fixed base** ([FrdI], Theorem 5.1(i)): `(A_D, α)` and
`(A_D, α')` are isomorphic by a base-identity isomorphism iff `α − α' = Div_B(u)` for some
rational function `u ∈ B(A_D)`. -/
theorem nonempty_iso_iff (A : D) (α α' : Φ.obj A) :
    (∃ e : (⟨A, α⟩ : Model Φ B divB) ≅ ⟨A, α'⟩, e.hom.base = 𝟙 A) ↔
      ∃ u : B.obj A, α - α' = divB.app A u := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨h₁, -, h₃⟩ := (isIso_iff e.hom).mp inferInstance
    have r := e.hom.rel
    rw [h₁, h₃, he] at r
    refine ⟨e.hom.u, ?_⟩
    simp only [PNat.one_coe, one_smul, add_zero, GrpOn.pb_id'] at r
    exact sub_eq_of_eq_add' r
  · rintro ⟨u, hu⟩
    let φ : (⟨A, α⟩ : Model Φ B divB) ⟶ ⟨A, α'⟩ :=
      mk1 (𝟙 _) 0 (Φ.pos _).zero_mem u (by simp [← hu])
    haveI := isIso_of φ rfl (inferInstanceAs (IsIso (𝟙 A))) rfl
    exact ⟨asIso φ, rfl⟩

end Model

end Frobenioid

end Iut
