/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Angular.Category

/-!
# The archimedean Frobenioid is a Frobenioid ([FrdII], Example 3.3(ii))

[FrdII], Example 3.3(ii): "a routine verification reveals that `C` satisfies the conditions of
[Mzk5], Definition 1.3, hence that `C` is a Frobenioid". This file carries out that verification
for the archimedean Frobenioid of angular regions over `Pt` (`Angular.Obj`, `Angular.toElem`):
**`Angular.isFrobenioid : IsFrobenioid toElem`**, clause by clause. `C` is not a model Frobenioid,
so each clause of [FrdI], Definition 1.3 is proved directly. The non-formal input is the
rigidity of angular parts under `z ↦ v·z^d` ([FrdII], Lemma 3.2(iv); `IsAngular.eq_of_subset`),
used for (iii)(b), and the existence of small arcs (`exists_isAngular_subset`), used for (i)(b).

Shape of the verification (all morphisms are base-isomorphisms over `Pt`):

* pull-back morphisms are exactly the isomorphisms (`isPullback_iff`);
* the morphism of Frobenius type of degree `n` out of `A = B × (0, e^τ]` is
  `(n, 1) : A → B^{⊗n} × (0, e^{nτ}]` (`frob`);
* pre-steps are the linear morphisms; a pre-step factors through `u·B × (0, λ']`
  (co-angular, then isometric) or through `u⁻¹·B' × (0, λ]` (isometric, then co-angular);
* `O^▷(A)` consists of the `(1, μ)` with `u·B ⊆ B`, `|μ| ≤ 1`;
* the isotropic hull of `A` is `(1, 1) : A → S¹ × (0, λ]`.
-/

namespace Iut

namespace Frobenioid

namespace Angular

open CategoryTheory Set Pointwise

noncomputable section

/-- Every object of `Pt` is isomorphic to every other. -/
def ptIso (X Y : Pt) : X ≅ Y where
  hom := Discrete.eqToHom (Subsingleton.elim _ _)
  inv := Discrete.eqToHom (Subsingleton.elim _ _)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Pull-back morphisms are the isomorphisms. -/
lemma isPullback_iff {A A' : Obj} (f : A ⟶ A') : IsPullback P f ↔ IsIso f :=
  ⟨fun h => (isIso_iff_isPullback_isBaseIso f).mpr ⟨h, isBaseIso f⟩,
    fun _ => isPullback_of_isIso f⟩

/-- The Frobenius twist `B^{⊗n} × (0, e^{nτ}]`. -/
def frobObj (A : Obj) (n : ℕ+) : Obj :=
  ⟨A.ang ^ (n : ℕ), A.isAngular.pow n.ne_zero, n * A.tip⟩

/-- The morphism `(n, 1) : A → A^{⊗n}` of Frobenius type. -/
def frob (A : Obj) (n : ℕ+) : A ⟶ frobObj A n :=
  mkHom n 0 1 (by simp [frobObj]) (by simp [frobObj])

lemma isFrobeniusType_iff {A A' : Obj} (f : A ⟶ A') :
    IsFrobeniusType P f ↔ {f.rot} * A.ang ^ (f.deg : ℕ) = A'.ang ∧
      f.rad + f.deg * A.tip = A'.tip := by
  rw [IsFrobeniusType, IsLBInvertible, isCoangular_iff, isIsometric_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, isBaseIso f⟩⟩

lemma frob_isFrobeniusType (A : Obj) (n : ℕ+) : IsFrobeniusType P (frob A n) :=
  (isFrobeniusType_iff _).mpr ⟨by simp [frob, frobObj], by simp [frob, frobObj]⟩

/-- (ii): Frobenius-type morphisms of degree `n` out of `A` are `frob A n` up to isomorphism. -/
lemma frob_unique {A E : Obj} (n : ℕ+) (ψ : A ⟶ E) (hψ : IsFrobeniusType P ψ)
    (hn : degFr P ψ = n) : ∃ β : frobObj A n ≅ E, frob A n ≫ β.hom = ψ := by
  rw [isFrobeniusType_iff] at hψ
  rw [degFr_eq] at hn
  subst hn
  refine ⟨isoMk ψ.rad ψ.rot (by simpa [frobObj] using hψ.1) (by simpa [frobObj] using hψ.2), ?_⟩
  ext <;> simp [frob]

/-- Two morphisms of Frobenius type of the same degree out of `A` differ by an isomorphism. -/
lemma frob_iso_of_eq {A X X' : Obj} (γ : A ⟶ X) (γ' : A ⟶ X') (hγ : IsFrobeniusType P γ)
    (hγ' : IsFrobeniusType P γ') {n : ℕ+} (hn : degFr P γ = n) (hn' : degFr P γ' = n) :
    ∃ e : X ≅ X', γ ≫ e.hom = γ' := by
  obtain ⟨e, he⟩ := frob_unique n γ hγ hn
  obtain ⟨e', he'⟩ := frob_unique n γ' hγ' hn'
  refine ⟨e.symm ≪≫ e', ?_⟩
  rw [← he, ← he']
  simp

/-- Frobenius-trivial objects: the isotropic ones (`ζ(n) = (n, e^{(1−n)τ})`). -/
lemma isFrobeniusTrivial_of_univ {A : Obj} (h : A.ang = univ) : IsFrobeniusTrivial P A := by
  let ζ : ℕ+ → (A ⟶ A) := fun n => mkHom n ((1 - n) * A.tip) 1
    (by rw [h]; exact subset_univ _) (le_of_eq (by ring))
  refine ⟨ζ, ?_, fun m n => ?_, fun n => ⟨rfl, isBaseIdentity _, ?_⟩⟩
  · ext <;> simp [ζ]
  · ext
    · simp [ζ, mul_comm]
    · simp only [ζ, comp_rad, mkHom_rad, mkHom_deg, PNat.mul_coe, Nat.cast_mul]; ring
    · simp [ζ]
  · rw [isFrobeniusType_iff]
    refine ⟨by simp [ζ, h], by simp [ζ]; ring⟩

/-- The coslice/slice objects: `B × (0, e^{τ + s}]`. -/
def shift (A : Obj) (s : ℝ) : Obj := ⟨A.ang, A.isAngular, A.tip + s⟩

/-- **[FrdII], Example 3.3(ii)**: the archimedean Frobenioid of angular regions satisfies the
conditions of [FrdI], Definition 1.3. -/
theorem isFrobenioid : IsFrobenioid P where
  connected_D := inferInstance
  epi_D := inferInstance
  connected_C := inferInstance
  epi_C := inferInstance
  base_surj X := ⟨iso 0, isFrobeniusTrivial_of_univ rfl, ⟨ptIso _ _⟩⟩
  preStep_span A B _ := by
    obtain ⟨z, hz⟩ := A.isAngular.2.2
    obtain ⟨w, hw⟩ := B.isAngular.2.2
    let W := A.ang ∩ (w * z⁻¹ * ·) ⁻¹' B.ang
    have hW : IsOpen W := A.isAngular.1.inter
      (B.isAngular.1.preimage (continuous_const_mul _))
    obtain ⟨E, hE, hEW, -⟩ := exists_isAngular_subset hW
      (show z ∈ W from ⟨hz, by simpa using hw⟩)
    let e : Obj := ⟨E, hE, min A.tip B.tip⟩
    refine ⟨e, mkHom 1 0 1 ?_ (by simp [e]), mkHom 1 0 (w * z⁻¹) ?_ (by simp [e]),
      (isPreStep_iff _).mpr rfl, (isPreStep_iff _).mpr rfl, Subsingleton.elim _ _⟩
    · intro x hx
      rw [pow_pnat_one, singleton_one, one_mul] at hx
      exact (hEW hx).1
    · rintro _ ⟨_, rfl, x, hx, rfl⟩
      rw [pow_pnat_one] at hx
      exact (hEW hx).2
  pullback_surj A X _ := ⟨A, 𝟙 A, ptIso _ _, isPullback_of_isIso _, Subsingleton.elim _ _⟩
  frobenius A n := ⟨frobObj A n, frob A n, frob_isFrobeniusType A n, rfl,
    fun E ψ hψ hn => frob_unique n ψ hψ hn⟩
  coangular_comp {A B E} φ ψ hφ hψ := by
    rw [isCoangular_iff] at *
    rw [comp_rot, comp_deg, PNat.mul_coe, rot_pow_eq, hφ, hψ]
  coangular_of_preStep {A' A} φ ψ hφ hφ' := by
    rw [isCoangular_iff] at *
    rw [isPreStep_iff] at hφ'
    rw [hφ', PNat.one_coe, pow_one] at hφ
    have hsub := ψ.ang_le
    rw [← hφ] at hsub
    -- `{φ⁻¹ ψ}·A'^d ⊆ A'`
    have h2 : {φ.rot⁻¹ * ψ.rot} * A'.ang ^ (ψ.deg : ℕ) ⊆ A'.ang := by
      have := mul_subset_mul_left (s := ({φ.rot⁻¹} : Set Circle)) hsub
      rwa [← mul_assoc, ← mul_assoc, singleton_mul_singleton, singleton_mul_singleton,
        inv_mul_cancel, singleton_one, one_mul] at this
    have h3 := (A'.isAngular.eq_of_subset ψ.deg.ne_zero h2).1
    rw [← hφ]
    conv_rhs => rw [← h3]
    rw [← mul_assoc, singleton_mul_singleton, mul_inv_cancel_left]
  orhd_equiv {A B} φ hφ hφ' := by
    rw [isCoangular_iff] at hφ
    rw [isPreStep_iff] at hφ'
    rw [hφ', PNat.one_coe, pow_one] at hφ
    -- transport of linear endomorphisms along `B = u·A`
    have key : ∀ {X Y : Obj} (v : Circle), {v} * X.ang = Y.ang → ∀ e : Orhd P X,
        {(e.1).rot} * Y.ang ^ ((1 : ℕ+) : ℕ) ⊆ Y.ang ∧ (e.1).rad + (1 : ℕ+) * Y.tip ≤ Y.tip :=
      fun {X Y} v hv e => by
        have h1 : (e.1).deg = 1 := e.2.2
        have ha := (e.1).ang_le
        have ht := (e.1).tip_le
        rw [h1] at ha ht
        simp only [PNat.one_coe, pow_one, Nat.cast_one, one_mul] at ha ht ⊢
        refine ⟨?_, by linarith⟩
        rw [← hv, ← mul_assoc, singleton_mul_singleton, mul_comm (e.1).rot v,
          ← singleton_mul_singleton, mul_assoc]
        exact mul_subset_mul_left ha
    let fwd : Orhd P A → Orhd P B := fun e =>
      ⟨mkHom 1 (e.1).rad (e.1).rot (key φ.rot hφ e).1 (key φ.rot hφ e).2,
        isBaseIdentity _, rfl⟩
    have hφ'' : {φ.rot⁻¹} * B.ang = A.ang := (singleton_mul_eq_iff.mp hφ).symm
    let bwd : Orhd P B → Orhd P A := fun e =>
      ⟨mkHom 1 (e.1).rad (e.1).rot (key φ.rot⁻¹ hφ'' e).1 (key φ.rot⁻¹ hφ'' e).2,
        isBaseIdentity _, rfl⟩
    have hdeg : ∀ {X : Obj} (e : Orhd P X), (e.1).deg = 1 := fun e => e.2.2
    refine ⟨⟨fwd, bwd, fun e => ?_, fun e => ?_⟩, fun φ' _ hφ'2 _ e => ?_⟩
    · exact Subtype.ext (hom_ext (by simp [bwd, fwd, hdeg e]) (by simp [bwd, fwd])
        (by simp [bwd, fwd]))
    · exact Subtype.ext (hom_ext (by simp [bwd, fwd, hdeg e]) (by simp [bwd, fwd])
        (by simp [bwd, fwd]))
    · rw [isPreStep_iff] at hφ'2
      ext
      · simp [fwd, hdeg e, hφ'2]
      · simp [fwd, hφ'2]; ring
      · simp [fwd, hφ'2, mul_comm]
  coslice_surj A z hz := by
    refine ⟨shift A z.down, mkHom 1 0 1 (by simp [shift])
      (by simpa [shift] using mem_realCone.mp hz), ?_,
      (isPreStep_iff _).mpr rfl, ?_⟩
    · rw [isCoangular_iff]; simp [shift]
    · apply ULift.ext; change divVal _ = _; simp [divVal, shift]
  coslice_full {A B₁ B₂} φ₁ φ₂ h₁ h₁' h₂ h₂' hle := by
    rw [isCoangular_iff] at h₁ h₂
    rw [isPreStep_iff] at h₁' h₂'
    rw [h₁', PNat.one_coe, pow_one] at h₁
    rw [h₂', PNat.one_coe, pow_one] at h₂
    have hle' : 0 ≤ divVal φ₂ - divVal φ₁ := hle
    simp only [divVal, h₁', h₂', PNat.one_coe, Nat.cast_one, one_mul] at hle'
    have hang : {φ₂.rot * φ₁.rot⁻¹} * B₁.ang = B₂.ang := by
      rw [← h₁, ← h₂, ← mul_assoc, singleton_mul_singleton, inv_mul_cancel_right]
    refine ⟨mkHom 1 (φ₂.rad - φ₁.rad) (φ₂.rot * φ₁.rot⁻¹) (by rw [pow_pnat_one, hang])
      (by rw [PNat.one_coe, Nat.cast_one, one_mul]; linarith),
      ?_, (isPreStep_iff _).mpr rfl, ?_⟩
    · rw [isCoangular_iff]; simpa using hang
    · ext <;> simp [h₁', h₂']
  slice_surj A z hz := by
    refine ⟨shift A (-z.down), mkHom 1 0 1 (by simp [shift])
      (by simpa [shift] using mem_realCone.mp hz), ?_,
      (isPreStep_iff _).mpr rfl, ?_⟩
    · rw [isCoangular_iff]; simp [shift]
    · apply ULift.ext; change divVal _ = _; simp [divVal, shift]
  slice_full {A B₁ B₂} ψ₁ ψ₂ z₁ z₂ h₁ h₁' h₂ h₂' hz₁ hz₂ hle := by
    rw [isCoangular_iff] at h₁ h₂
    rw [isPreStep_iff] at h₁' h₂'
    rw [h₁', PNat.one_coe, pow_one] at h₁
    rw [h₂', PNat.one_coe, pow_one] at h₂
    have e₁ : divVal ψ₁ = z₁.down := congrArg ULift.down hz₁
    have e₂ : divVal ψ₂ = z₂.down := congrArg ULift.down hz₂
    have hle' : 0 ≤ z₁.down - z₂.down := hle
    simp only [divVal, h₁', h₂', PNat.one_coe, Nat.cast_one, one_mul] at e₁ e₂
    have hang : {ψ₂.rot⁻¹ * ψ₁.rot} * B₁.ang = B₂.ang := by
      rw [← singleton_mul_singleton, mul_assoc, h₁, ← h₂, ← mul_assoc, singleton_mul_singleton,
        inv_mul_cancel, singleton_one, one_mul]
    refine ⟨mkHom 1 (ψ₁.rad - ψ₂.rad) (ψ₂.rot⁻¹ * ψ₁.rot) (by rw [pow_pnat_one, hang])
      (by rw [PNat.one_coe, Nat.cast_one, one_mul]; linarith), ?_, (isPreStep_iff _).mpr rfl, ?_⟩
    · rw [isCoangular_iff]; simpa using hang
    · ext <;> simp [h₁', h₂']
  factorization {A B} φ := by
    refine ⟨frobObj A φ.deg, B, frob A φ.deg, mkHom 1 φ.rad φ.rot ?_ ?_, 𝟙 B,
      frob_isFrobeniusType A φ.deg, (isPreStep_iff _).mpr rfl, isPullback_of_isIso _, ?_⟩
    · simpa [frobObj] using φ.ang_le
    · simpa [frobObj] using φ.tip_le
    · ext <;> simp [frob]
  factorization_unique γ β α γ' β' α' hγ hβ hα hγ' hβ' hα' h := by
    refine factorization_unique_of (fun γ γ' hγ hγ' hd => ?_) γ β α γ' β' α' hγ hβ hα hγ' hβ'
      hα' ?_ ?_ h
    · exact frob_iso_of_eq γ γ' hγ hγ' rfl hd.symm
    · haveI := (isPullback_iff α).mp hα; exact degFr_of_isIso α
    · haveI := (isPullback_iff α').mp hα'; exact degFr_of_isIso α'
  pullback_lb φ hφ := by
    haveI := (isPullback_iff φ).mp hφ
    obtain ⟨h₁, h₂, -⟩ := (isIso_iff φ).mp this
    exact ⟨⟨(isCoangular_iff φ).mpr (by simpa [h₁] using h₂), Div_of_isIso φ⟩,
      degFr_of_isIso φ⟩
  preStep_mono φ hφ := by
    rw [isPreStep_iff] at hφ
    refine ⟨fun g h e => ?_⟩
    have e1 := congrArg Hom.deg e
    have e2 := congrArg Hom.rad e
    have e3 := congrArg Hom.rot e
    simp only [comp_deg, comp_rad, comp_rot, hφ, one_mul, PNat.one_coe, pow_one,
      Nat.cast_one] at e1 e2 e3
    exact hom_ext e1 (by linarith) (mul_left_cancel e3)
  preStep_factor {A B} φ hφ := by
    rw [isPreStep_iff] at hφ
    have ha := φ.ang_le
    have ht := φ.tip_le
    simp only [hφ, PNat.one_coe, pow_one, Nat.cast_one, one_mul] at ha ht
    let X : Obj := ⟨{φ.rot} * A.ang, A.isAngular.singleton_mul _, B.tip⟩
    refine ⟨X, mkHom 1 φ.rad φ.rot (by simp [X]) (by simpa [X] using ht),
      mkHom 1 0 1 (by simpa [X] using ha) (by simp [X]), (isIsometric_iff _).mpr (by simp [X]),
      (isPreStep_iff _).mpr rfl, (isCoangular_iff _).mpr (by simp [X]),
      (isPreStep_iff _).mpr rfl, ?_⟩
    ext <;> simp [hφ]
  preStep_factor_unique {A B X X'} β α β' α' hα hα' hβ hβ' hα₂ hα₂' hβ₂ hβ₂' h := by
    rw [isPreStep_iff] at hα' hβ' hα₂' hβ₂'
    rw [isIsometric_iff, hα'] at hα
    rw [isIsometric_iff, hα₂'] at hα₂
    rw [isCoangular_iff, hβ', PNat.one_coe, pow_one] at hβ
    rw [isCoangular_iff, hβ₂', PNat.one_coe, pow_one] at hβ₂
    have er := congrArg Hom.rad h
    have eu := congrArg Hom.rot h
    simp only [comp_rad, comp_rot, hα', hα₂', PNat.one_coe, pow_one, Nat.cast_one,
      one_mul] at er eu hα hα₂
    have hu : α'.rot * α.rot⁻¹ * β'.rot = β.rot := by
      have h' := congrArg (fun x : Circle => (x : ℂ)) eu
      have := Circle.coe_ne_zero α.rot
      apply Circle.ext
      simp only [Circle.coe_mul, Circle.coe_inv] at h' ⊢
      field_simp
      linear_combination -h'
    have hang : {α'.rot * α.rot⁻¹} * X'.ang = X.ang := by
      rw [← hβ, ← hβ₂, ← mul_assoc, singleton_mul_singleton, hu]
    refine ⟨isoMk (α'.rad - α.rad) (α'.rot * α.rot⁻¹) hang (by linarith), ?_, ?_⟩
    · refine hom_ext (by simp [hα', hα₂']) (by simp [hα']) ?_
      simp only [comp_rot, isoMk_hom_rot, hα', PNat.one_coe, pow_one]
      circ_ring
    · refine hom_ext (by simp [hβ', hβ₂']) (by simp; linarith) ?_
      simp only [comp_rot, isoMk_inv_rot, isoMk_inv_deg, PNat.one_coe, pow_one]
      rw [← hu]
      circ_ring
  preStep_factor' {A B} φ hφ := by
    rw [isPreStep_iff] at hφ
    have ha := φ.ang_le
    have ht := φ.tip_le
    simp only [hφ, PNat.one_coe, pow_one, Nat.cast_one, one_mul] at ha ht
    let X : Obj := ⟨{φ.rot⁻¹} * B.ang, B.isAngular.singleton_mul _, A.tip⟩
    have hX : {φ.rot} * X.ang = B.ang := by
      simp only [X, ← mul_assoc, singleton_mul_singleton, mul_inv_cancel, singleton_one, one_mul]
    refine ⟨X, mkHom 1 0 1 ?_ (by simp [X]), mkHom 1 φ.rad φ.rot (by rw [pow_pnat_one, hX])
      (by simpa [X] using ht), (isCoangular_iff _).mpr (by simpa using hX),
      (isPreStep_iff _).mpr rfl, (isIsometric_iff _).mpr (by simp [mkHom, X]),
      (isPreStep_iff _).mpr rfl, ?_⟩
    · simp only [PNat.one_coe, pow_one, singleton_one, one_mul, X]
      exact singleton_mul_cancel (u := φ.rot) (by
        rw [← mul_assoc, singleton_mul_singleton, mul_inv_cancel, singleton_one, one_mul]
        exact ha)
    · ext <;> simp [hφ]
  preStep_factor'_unique {A B X X'} β α β' α' hα hα' hβ hβ' hα₂ hα₂' hβ₂ hβ₂' h := by
    rw [isPreStep_iff] at hα' hβ' hα₂' hβ₂'
    rw [isCoangular_iff, hα', PNat.one_coe, pow_one] at hα
    rw [isCoangular_iff, hα₂', PNat.one_coe, pow_one] at hα₂
    rw [isIsometric_iff, hβ'] at hβ
    rw [isIsometric_iff, hβ₂'] at hβ₂
    have er := congrArg Hom.rad h
    have eu := congrArg Hom.rot h
    simp only [comp_rad, comp_rot, hα', hα₂', PNat.one_coe, pow_one, Nat.cast_one,
      one_mul] at er eu hβ hβ₂
    have hu : α'.rot * α.rot⁻¹ * β'.rot = β.rot := by
      have h' := congrArg (fun x : Circle => (x : ℂ)) eu
      have := Circle.coe_ne_zero α.rot
      apply Circle.ext
      simp only [Circle.coe_mul, Circle.coe_inv] at h' ⊢
      field_simp
      linear_combination -h'
    have hang : {α'.rot * α.rot⁻¹} * X'.ang = X.ang := by
      rw [singleton_mul_eq_iff.mp hα, singleton_mul_eq_iff.mp hα₂, ← mul_assoc,
        singleton_mul_singleton]
      congr 2
      circ_ring
    refine ⟨isoMk (α'.rad - α.rad) (α'.rot * α.rot⁻¹) hang (by linarith), ?_, ?_⟩
    · refine hom_ext (by simp [hα', hα₂']) (by simp [hα']) ?_
      simp only [comp_rot, isoMk_hom_rot, hα', PNat.one_coe, pow_one]
      circ_ring
    · refine hom_ext (by simp [hβ', hβ₂']) (by simp; linarith) ?_
      simp only [comp_rot, isoMk_inv_rot, isoMk_inv_deg, PNat.one_coe, pow_one]
      rw [← hu]
      circ_ring
  units {A B} φ ψ hφ hφ' hψ hψ' _ hD := by
    rw [isPreStep_iff] at hφ' hψ'
    rw [isCoangular_iff, hφ', PNat.one_coe, pow_one] at hφ
    rw [isCoangular_iff, hψ', PNat.one_coe, pow_one] at hψ
    have hr : φ.rad = ψ.rad := by
      have := congrArg ULift.down hD
      change divVal φ = divVal ψ at this
      simp only [divVal, hφ', hψ'] at this
      linarith
    have hang : {φ.rot * ψ.rot⁻¹} * B.ang = B.ang := by
      conv_lhs => rw [← hψ]
      rw [← mul_assoc, singleton_mul_singleton, inv_mul_cancel_right, hφ]
    let a := isoMk (A := B) 0 (φ.rot * ψ.rot⁻¹) hang (by simp)
    refine ⟨a.hom, ⟨inferInstance, isBaseIdentity _, rfl⟩, ?_⟩
    ext <;> simp [a, hψ', hφ', hr]
  isotropicHull A := by
    refine ⟨iso A.tip, toIso A le_rfl, (isIsometric_iff _).mpr (by simp [toIso, iso]),
      (isPreStep_iff _).mpr rfl, (isIsotropic_iff _).mpr rfl, fun E γ hE => ?_⟩
    rw [isIsotropic_iff] at hE
    refine ⟨mkHom γ.deg γ.rad γ.rot (by rw [hE]; exact subset_univ _)
      (by simpa [iso] using γ.tip_le), ?_, ?_⟩
    · ext <;> simp [toIso]
    · intro β hβ
      refine TotallyEpimorphic.cancel (toIso A le_rfl) ?_
      rw [hβ]
      ext <;> simp [toIso]
  isotropic_cod {A E} f hA := by
    rw [isIsotropic_iff] at *
    have := f.ang_le
    rw [hA, singleton_mul_univ_pow _ f.deg.ne_zero] at this
    exact univ_subset_iff.mp this

end

end Angular

end Frobenioid

end Iut
