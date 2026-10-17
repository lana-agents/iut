/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Angular.Circle
import Iut.Frobenioid.Arch

/-!
# The archimedean Frobenioid of angular regions ([FrdII], Example 3.3(i))

[FrdII], Example 3.3(i), for the base category `D = Pt` mapping to `Spec(ℂ) ∈ D₀` (the case of
IUT I, Example 3.4(i): "the archimedean Frobenioid as in [FrdII], Example 3.3, (ii)" with base
category "the one-morphism category determined by `Spec(K_v)`"; `K_v ≅ ℂ`).

**Objects.** [FrdII]: triples `(Spec K, V_K, A_K)` with `V_K` a one-dimensional `K`-vector space
and `A_K ⊆ V_K` an angular region (Definition 3.1(iii)). Every such pair is isomorphic to one with
`V_K = ℂ`, and we take `V_K = ℂ` (this is an equivalent full subcategory). By the canonical
decomposition `ℂ^× = S¹ × ord(ℂ^×)` (Definition 3.1(ii)) an angular region `A = B × (0, λ]` is
recorded by its angular part `B ⊆ S¹` (`IsAngular`: nonempty connected open) and the logarithm
`τ = log λ ∈ ℝ` of its tip (`Obj`); the region itself is `Obj.region A ⊆ ℂ`.

**Morphisms** `A → A'` ([FrdII], Example 3.3(i)(a)–(c)): `Base = id`, a Frobenius degree
`d ∈ ℕ_{≥1}`, and an isomorphism `V^{⊗d} = ℂ → ℂ`, i.e. multiplication by `μ ∈ ℂ^×`, mapping
`A^{⊗d}` into `A'`. Writing `μ = e^ρ·u` (`ρ = log|μ|`, `u ∈ S¹`), the condition
`μ·A^{⊗d} ⊆ A'` is `{u}·B^d ⊆ B'` and `ρ + d·τ ≤ τ'` (`Hom`; the comparison with the
literal subsets of `ℂ` is `Hom.smul_region_pow_subset` and its converse
`hom_cond_of_subset`). Composition is
`(d', μ') ∘ (d, μ) = (d d', μ' μ^{d'})`.

**The pre-Frobenioid structure** `C → F_Φ`, `Φ = ℝ_{≥0}` (`phiReal`): `Div(φ) = log λ` for the
largest `λ` with `λ·μ·A^{⊗d} ⊆ A'`, i.e. `Div(φ) = τ' − ρ − d·τ` (`toElem`; `Div_eq_sSup`
records the "largest `λ`" description), `degFr(φ) = d`.

Basic structure proved here: the isomorphisms (`isIso_iff`), the co-angular morphisms
(`isCoangular_iff`: **co-angular = naively co-angular**, [FrdII], Example 3.3(ii)), the isotropic
objects (`isIsotropic_iff`: **isotropic = naively isotropic**), and `C` is connected and totally
epimorphic.
-/

namespace Iut

namespace Frobenioid

namespace Angular

open CategoryTheory Set Pointwise

/-- Prove an identity in the commutative group `S¹` by computing in `ℂ`. -/
macro "circ_ring" : tactic => `(tactic| (apply Circle.ext; simp only [Circle.coe_mul,
  Circle.coe_inv, Circle.coe_pow, Circle.coe_one]; field_simp))

noncomputable section

/-- An angular region `B × (0, e^τ] ⊆ ℂ^×` ([FrdII], Definition 3.1(iii), `K = ℂ`). -/
@[ext]
structure Obj where
  /-- The angular part `B ⊆ S¹`. -/
  ang : Set Circle
  isAngular : IsAngular ang
  /-- The logarithm `τ = log λ` of the tip `λ`. -/
  tip : ℝ

namespace Obj

/-- The angular region as a subset of `ℂ`: `{z ≠ 0 : z/|z| ∈ B, |z| ≤ e^τ}`. -/
def region (A : Obj) : Set ℂ :=
  {z | ∃ u ∈ A.ang, ∃ r : ℝ, r ≤ A.tip ∧ z = Real.exp r * (u : ℂ)}

/-- The angular region of `A` is `B × (0, λ]` with respect to `ℂ^× = S¹ × ℝ_{>0}`. -/
lemma mem_region {A : Obj} {z : ℂ} :
    z ∈ A.region ↔ ∃ u ∈ A.ang, ∃ r : ℝ, r ≤ A.tip ∧ z = Real.exp r * (u : ℂ) := Iff.rfl

/-- An isotropic angular region (`B = S¹`). -/
def IsNaivelyIsotropic (A : Obj) : Prop := A.ang = univ

end Obj

/-- A morphism `(d, μ = e^ρ·u)` with `μ·A^{⊗d} ⊆ A'` ([FrdII], Example 3.3(i)). -/
@[ext]
structure Hom (A A' : Obj) where
  /-- The Frobenius degree `d`. -/
  deg : ℕ+
  /-- `ρ = log|μ|`. -/
  rad : ℝ
  /-- `u = μ/|μ|`. -/
  rot : Circle
  ang_le : {rot} * A.ang ^ (deg : ℕ) ⊆ A'.ang
  tip_le : rad + deg * A.tip ≤ A'.tip

/-- `{v·u^n}·S^{mn} = {v}·({u}·S^m)^n`. -/
lemma rot_pow_eq (u v : Circle) (S : Set Circle) (m n : ℕ) :
    ({v * u ^ n} : Set Circle) * S ^ (n * m) = {v} * ({u} * S ^ m) ^ n := by
  rw [mul_pow, singleton_pow, ← pow_mul, mul_comm m n, ← singleton_mul_singleton, mul_assoc]

/-- The identity `(1, 1)`. -/
def Hom.id (A : Obj) : Hom A A where
  deg := 1
  rad := 0
  rot := 1
  ang_le := by simp
  tip_le := by simp

/-- Composition `(d', μ') ∘ (d, μ) = (d d', μ' μ^{d'})`. -/
def Hom.comp {A A' A'' : Obj} (f : Hom A A') (g : Hom A' A'') : Hom A A'' where
  deg := g.deg * f.deg
  rad := g.rad + g.deg * f.rad
  rot := g.rot * f.rot ^ (g.deg : ℕ)
  ang_le := by
    rw [PNat.mul_coe, rot_pow_eq]
    exact (mul_subset_mul_left (pow_subset_pow_left f.ang_le)).trans g.ang_le
  tip_le := by
    have h1 := f.tip_le
    have h2 := g.tip_le
    have hg : (0 : ℝ) ≤ g.deg := by positivity
    have := mul_le_mul_of_nonneg_left h1 hg
    push_cast
    nlinarith

instance : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext <;> simp [Hom.comp, Hom.id]
  comp_id f := by
    apply Hom.ext <;> simp [Hom.comp, Hom.id]
  assoc f g h := by
    apply Hom.ext
    · simp [Hom.comp, mul_assoc]
    · simp only [Hom.comp, PNat.mul_coe, Nat.cast_mul]; ring
    · simp only [Hom.comp, PNat.mul_coe, mul_pow, ← pow_mul, mul_assoc, mul_comm (g.deg : ℕ)]

@[ext] lemma hom_ext {A A' : Obj} {f g : A ⟶ A'} (h₁ : f.deg = g.deg) (h₂ : f.rad = g.rad)
    (h₃ : f.rot = g.rot) : f = g := Hom.ext h₁ h₂ h₃

@[simp] lemma id_deg (A : Obj) : (𝟙 A : A ⟶ A).deg = 1 := rfl
@[simp] lemma id_rad (A : Obj) : (𝟙 A : A ⟶ A).rad = 0 := rfl
@[simp] lemma id_rot (A : Obj) : (𝟙 A : A ⟶ A).rot = 1 := rfl
@[simp] lemma comp_deg {A A' A'' : Obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    (f ≫ g).deg = g.deg * f.deg := rfl
@[simp] lemma comp_rad {A A' A'' : Obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    (f ≫ g).rad = g.rad + g.deg * f.rad := rfl
@[simp] lemma comp_rot {A A' A'' : Obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    (f ≫ g).rot = g.rot * f.rot ^ (g.deg : ℕ) := rfl

@[simp] lemma pow_pnat_one (S : Set Circle) : S ^ ((1 : ℕ+) : ℕ) = S := by simp

/-- A morphism from data. -/
def mkHom {A A' : Obj} (d : ℕ+) (ρ : ℝ) (u : Circle) (h₁ : {u} * A.ang ^ (d : ℕ) ⊆ A'.ang)
    (h₂ : ρ + d * A.tip ≤ A'.tip) : A ⟶ A' := ⟨d, ρ, u, h₁, h₂⟩

@[simp] lemma mkHom_deg {A A' : Obj} (d : ℕ+) (ρ : ℝ) (u : Circle) h₁ h₂ :
    (mkHom (A := A) (A' := A') d ρ u h₁ h₂).deg = d := rfl
@[simp] lemma mkHom_rad {A A' : Obj} (d : ℕ+) (ρ : ℝ) (u : Circle) h₁ h₂ :
    (mkHom (A := A) (A' := A') d ρ u h₁ h₂).rad = ρ := rfl
@[simp] lemma mkHom_rot {A A' : Obj} (d : ℕ+) (ρ : ℝ) (u : Circle) h₁ h₂ :
    (mkHom (A := A) (A' := A') d ρ u h₁ h₂).rot = u := rfl

/-! ### Comparison with the angular regions in `ℂ` -/

/-- `μ·A^{⊗d}` for `μ = e^ρ·u`: the subset `{μ·a₁⋯a_d}` of `ℂ`. -/
lemma Hom.smul_region_pow_subset {A A' : Obj} (f : A ⟶ A') {a : Fin f.deg → ℂ}
    (ha : ∀ i, a i ∈ A.region) :
    (Real.exp f.rad * (f.rot : ℂ)) * ∏ i, a i ∈ A'.region := by
  choose u hu r hr hz using ha
  refine ⟨f.rot * ∏ i, u i, f.ang_le (mul_mem_mul rfl ?_), f.rad + ∑ i, r i, ?_, ?_⟩
  · exact Set.mem_pow_iff_prod.mpr ⟨u, hu, rfl⟩
  · have h1 : ∑ i, r i ≤ ∑ _i : Fin f.deg, A.tip := Finset.sum_le_sum fun i _ => hr i
    have h2 := f.tip_le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  · have hc : ((∏ i, u i : Circle) : ℂ) = ∏ i, (u i : ℂ) := map_prod Circle.coeHom _ _
    rw [Finset.prod_congr rfl (fun i _ => hz i), Finset.prod_mul_distrib, Real.exp_add,
      Real.exp_sum, Circle.coe_mul, hc]
    push_cast
    ring

/-- Uniqueness of the polar decomposition `ℂ^× = ℝ_{>0} × S¹`. -/
lemma polar_unique {r s : ℝ} {w v : Circle} (h : (Real.exp r : ℂ) * w = Real.exp s * v) :
    r = s ∧ w = v := by
  have hn := congrArg norm h
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Circle.norm_coe, mul_one] at hn
  have hrs := Real.exp_injective hn
  subst hrs
  exact ⟨rfl, Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos r).ne') h)⟩

/-- Conversely, `μ·A^{⊗d} ⊆ A'` (for `μ = e^ρ·u`) implies the conditions defining `Hom A A'`:
the morphisms of `Obj` are exactly the `(d, μ)` of [FrdII], Example 3.3(i)(b), (c). -/
lemma hom_cond_of_subset {A A' : Obj} (d : ℕ+) (ρ : ℝ) (u : Circle)
    (H : ∀ a : Fin d → ℂ, (∀ i, a i ∈ A.region) →
      (Real.exp ρ * (u : ℂ)) * ∏ i, a i ∈ A'.region) :
    {u} * A.ang ^ (d : ℕ) ⊆ A'.ang ∧ ρ + d * A.tip ≤ A'.tip := by
  have key : ∀ b ∈ A.ang ^ (d : ℕ), u * b ∈ A'.ang ∧ ρ + d * A.tip ≤ A'.tip := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Set.mem_pow_iff_prod.mp hb
    obtain ⟨w, hw, r, hr, he⟩ := H (fun i => Real.exp A.tip * (c i : ℂ))
      (fun i => ⟨c i, hc i, A.tip, le_rfl, rfl⟩)
    have hcp : ((∏ i, c i : Circle) : ℂ) = ∏ i, (c i : ℂ) := map_prod Circle.coeHom _ _
    have e : (Real.exp (ρ + d * A.tip) : ℂ) * ((u * ∏ i, c i : Circle) : ℂ) =
        Real.exp r * w := by
      rw [← he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Circle.coe_mul, hcp, Real.exp_add, Real.exp_nat_mul]
      push_cast
      ring
    obtain ⟨h1, h2⟩ := polar_unique e
    exact ⟨h2 ▸ hw, h1 ▸ hr⟩
  obtain ⟨b, hb⟩ := (A.isAngular.pow d.ne_zero).2.2
  refine ⟨?_, (key b hb).2⟩
  rintro _ ⟨_, rfl, b, hb, rfl⟩
  exact (key b hb).1

/-! ### The pre-Frobenioid structure -/

/-- `Div(φ) = τ' − ρ − d·τ ≥ 0`. -/
def divVal {A A' : Obj} (f : A ⟶ A') : ℝ := A'.tip - f.rad - f.deg * A.tip

lemma divVal_nonneg {A A' : Obj} (f : A ⟶ A') : 0 ≤ divVal f := by
  have := f.tip_le; unfold divVal; linarith

/-- **[FrdII], Example 3.3(i)**: `Div(φ) = log λ` for the largest `λ > 0` with
`λ·μ·A^{⊗d} ⊆ A'`, i.e. the largest `log λ` such that the tip condition still holds. -/
lemma Div_eq_sSup {A A' : Obj} (f : A ⟶ A') :
    IsGreatest {s : ℝ | s + f.rad + f.deg * A.tip ≤ A'.tip} (divVal f) :=
  ⟨by simp only [mem_setOf_eq, divVal]; linarith,
    fun s hs => by simp only [mem_setOf_eq] at hs; unfold divVal; linarith⟩

/-- The pre-Frobenioid structure `C → F_Φ`, `φ ↦ (id, Div(φ), degFr(φ))`. -/
def toElem : Obj ⥤ Elem phiReal.{0} where
  obj _ := ⟨pt⟩
  map f := ⟨𝟙 pt, ⟨divVal f⟩, divVal_nonneg f, f.deg⟩
  map_id A := Elem.hom_ext rfl (by ext; simp [divVal]) rfl
  map_comp f g := Elem.hom_ext (Subsingleton.elim _ _)
    (by
      ext
      rw [Elem.comp_div]
      simp only [ULift.add_down]
      rw [ULift.smul_down, nsmul_eq_mul]
      change divVal (f ≫ g) = divVal g + _ * divVal f
      simp only [divVal, comp_deg, comp_rad, PNat.mul_coe, Nat.cast_mul]
      ring)
    rfl

/-- The projection functor. -/
abbrev P : Obj ⥤ Elem phiReal.{0} := toElem

@[simp] lemma degFr_eq {A A' : Obj} (f : A ⟶ A') : degFr P f = f.deg := rfl
@[simp] lemma Div_eq {A A' : Obj} (f : A ⟶ A') : (Div P f).down = divVal f := rfl

lemma isBaseIso {A A' : Obj} (f : A ⟶ A') : IsBaseIso P f := isIso_pt _

lemma isBaseIdentity {A : Obj} (f : A ⟶ A) : IsBaseIdentity P f := Subsingleton.elim _ _

lemma isLinear_iff {A A' : Obj} (f : A ⟶ A') : IsLinear P f ↔ f.deg = 1 := Iff.rfl

lemma isIsometric_iff {A A' : Obj} (f : A ⟶ A') :
    IsIsometric P f ↔ f.rad + f.deg * A.tip = A'.tip := by
  constructor
  · intro h
    have := congrArg ULift.down h
    change divVal f = 0 at this
    unfold divVal at this; linarith
  · intro h
    apply ULift.ext
    change divVal f = 0
    unfold divVal; linarith

lemma isPreStep_iff {A A' : Obj} (f : A ⟶ A') : IsPreStep P f ↔ f.deg = 1 :=
  ⟨fun h => h.1, fun h => ⟨h, isBaseIso f⟩⟩

/-! ### Basic properties of the category -/

lemma comp_left_cancel {A A' A'' : Obj} (f : A ⟶ A') {g h : A' ⟶ A''} (e : f ≫ g = f ≫ h) :
    g = h := by
  have e1 : g.deg = h.deg := mul_right_cancel (congrArg Hom.deg e)
  have e2 := congrArg Hom.rad e
  have e3 := congrArg Hom.rot e
  simp only [comp_rad, comp_rot, e1] at e2 e3
  exact hom_ext e1 (by linarith) (mul_right_cancel e3)

instance : TotallyEpimorphic Obj := ⟨fun f => ⟨fun _ _ e => comp_left_cancel f e⟩⟩

/-- The isotropic region `S¹ × (0, e^τ]`. -/
def iso (τ : ℝ) : Obj := ⟨univ, isAngular_univ, τ⟩

/-- `A → S¹ × (0, e^τ']` for `τ ≤ τ'` (the morphism `(1, 1)`). -/
def toIso (A : Obj) {τ : ℝ} (h : A.tip ≤ τ) : A ⟶ iso τ :=
  mkHom 1 0 1 (subset_univ _) (by simpa [iso] using h)

instance : Nonempty Obj := ⟨iso 0⟩

instance : IsConnected Obj :=
  zigzag_isConnected fun A B =>
    Zigzag.of_hom_inv (toIso A (le_max_left A.tip B.tip)) (toIso B (le_max_right A.tip B.tip))

/-- `{u}`-cancellation of pointwise products. -/
lemma singleton_mul_cancel {u : Circle} {S T : Set Circle} (h : {u} * S ⊆ {u} * T) : S ⊆ T := by
  have := mul_subset_mul_left (s := ({u⁻¹} : Set Circle)) h
  rwa [← mul_assoc, ← mul_assoc, singleton_mul_singleton, inv_mul_cancel, singleton_one,
    one_mul, one_mul] at this

lemma singleton_mul_eq_iff {u : Circle} {S T : Set Circle} : {u} * S = T ↔ S = {u⁻¹} * T := by
  constructor <;> rintro rfl <;>
    rw [← mul_assoc, singleton_mul_singleton] <;> simp

/-- A morphism `(1, μ)` with `μ·A = A'` is an isomorphism. -/
lemma isIso_of {A A' : Obj} (f : A ⟶ A') (h₁ : f.deg = 1) (h₂ : {f.rot} * A.ang = A'.ang)
    (h₃ : f.rad + A.tip = A'.tip) : IsIso f := by
  refine ⟨mkHom 1 (-f.rad) f.rot⁻¹ ?_ (by simp; linarith), ?_, ?_⟩
  · rw [PNat.one_coe, pow_one, ← h₂, ← mul_assoc, singleton_mul_singleton, inv_mul_cancel,
      singleton_one, one_mul]
  · ext <;> simp [h₁]
  · ext <;> simp [h₁]

/-- The isomorphism with data `(1, e^ρ u)`, with explicit inverse `(1, e^{−ρ} u⁻¹)`. -/
def isoMk {A A' : Obj} (ρ : ℝ) (u : Circle) (h₂ : {u} * A.ang = A'.ang)
    (h₃ : ρ + A.tip = A'.tip) : A ≅ A' where
  hom := mkHom 1 ρ u (by simp [h₂]) (by simp; linarith)
  inv := mkHom 1 (-ρ) u⁻¹ (by
      rw [PNat.one_coe, pow_one, ← h₂, ← mul_assoc, singleton_mul_singleton, inv_mul_cancel,
        singleton_one, one_mul]) (by simp; linarith)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

@[simp] lemma isoMk_hom_deg {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).hom.deg = 1 := rfl
@[simp] lemma isoMk_hom_rad {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).hom.rad = ρ := rfl
@[simp] lemma isoMk_hom_rot {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).hom.rot = u := rfl
@[simp] lemma isoMk_inv_deg {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).inv.deg = 1 := rfl
@[simp] lemma isoMk_inv_rad {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).inv.rad = -ρ := rfl
@[simp] lemma isoMk_inv_rot {A A' : Obj} (ρ : ℝ) (u : Circle) h₂ h₃ :
    (isoMk (A := A) (A' := A') ρ u h₂ h₃).inv.rot = u⁻¹ := rfl

/-- **The isomorphisms** are the `(1, μ)` with `μ·A = A'`. -/
theorem isIso_iff {A A' : Obj} (f : A ⟶ A') :
    IsIso f ↔ f.deg = 1 ∧ {f.rot} * A.ang = A'.ang ∧ f.rad + A.tip = A'.tip := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂, h₃⟩ => isIso_of f h₁ h₂ h₃⟩
  set g := inv f
  have e₁ : f ≫ g = 𝟙 A := IsIso.hom_inv_id f
  have e₂ : g ≫ f = 𝟙 A' := IsIso.inv_hom_id f
  have hd : f.deg = 1 ∧ g.deg = 1 := by
    have := congrArg Hom.deg e₁
    simp only [comp_deg, id_deg] at this
    exact ⟨PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val this)),
      PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val this))⟩
  have hr := congrArg Hom.rad e₁
  have hu := congrArg Hom.rot e₁
  simp only [comp_rad, comp_rot, hd.2, id_rad, id_rot, PNat.one_coe, pow_one,
    Nat.cast_one, one_mul] at hr hu
  have hf := f.ang_le
  have hg := g.ang_le
  have tf := f.tip_le
  have tg := g.tip_le
  simp only [hd.1, hd.2, PNat.one_coe, pow_one, Nat.cast_one, one_mul] at hf hg tf tg
  refine ⟨hd.1, subset_antisymm hf ?_, by linarith⟩
  have := mul_subset_mul_left (s := ({f.rot} : Set Circle)) hg
  rwa [← mul_assoc, singleton_mul_singleton, show f.rot * g.rot = 1 by rw [mul_comm]; exact hu,
    singleton_one, one_mul] at this

/-- **Co-angular = naively co-angular** ([FrdII], Example 3.3(ii)): `φ = (d, μ)` is co-angular
iff `u·B^{⊗d} = B'`. -/
theorem isCoangular_iff {A A' : Obj} (f : A ⟶ A') :
    IsCoangular P f ↔ {f.rot} * A.ang ^ (f.deg : ℕ) = A'.ang := by
  constructor
  · intro h
    let X : Obj := ⟨{f.rot} * A.ang ^ (f.deg : ℕ),
      (A.isAngular.pow f.deg.ne_zero).singleton_mul _, f.rad + f.deg * A.tip⟩
    let Y : Obj := ⟨A'.ang, A'.isAngular, f.rad + f.deg * A.tip⟩
    let γ : A ⟶ X := mkHom f.deg f.rad f.rot subset_rfl le_rfl
    let β : X ⟶ Y := mkHom 1 0 1 (by simpa [X] using f.ang_le) (by simp [X, Y])
    let α : Y ⟶ A' := mkHom 1 0 1 (by simp [Y]) (by simpa [Y] using f.tip_le)
    have hfac : γ ≫ β ≫ α = f := by ext <;> simp [γ, β, α]
    have hβ := h γ β α hfac rfl ((isIsometric_iff β).mpr (by simp [β, X, Y]))
      ((isPreStep_iff β).mpr rfl) (Or.inl (isBaseIso α))
    have := ((isIso_iff β).mp hβ).2.1
    simpa [X, Y, β] using this
  · intro h X Y γ β α hfac hα hβ hβ' _
    rw [isLinear_iff] at hα
    rw [isPreStep_iff] at hβ'
    rw [isIsometric_iff, hβ'] at hβ
    refine isIso_of β hβ' (subset_antisymm ?_ ?_) (by simpa using hβ)
    · simpa [hβ'] using β.ang_le
    · -- `{α}·Y ⊆ A' = {f.rot}·A^d ⊆ {α}{β}·X`
      have e1 : f.deg = γ.deg := by rw [← hfac]; simp [hα, hβ']
      have e2 : f.rot = α.rot * β.rot * γ.rot := by rw [← hfac]; simp [hα, hβ', mul_assoc]
      have hY := α.ang_le
      simp only [hα, PNat.one_coe, pow_one] at hY
      rw [← h, e2, e1, ← singleton_mul_singleton, ← singleton_mul_singleton, mul_assoc,
        mul_assoc] at hY
      apply singleton_mul_cancel (u := α.rot)
      refine hY.trans (mul_subset_mul_left (mul_subset_mul_left ?_))
      exact γ.ang_le

/-- **Isotropic = naively isotropic** ([FrdII], Example 3.3(ii)). -/
theorem isIsotropic_iff (A : Obj) : IsIsotropic P A ↔ A.ang = univ := by
  constructor
  · intro h
    have := h _ (toIso A le_rfl) ((isIsometric_iff _).mpr (by simp [toIso, iso]))
      ((isPreStep_iff _).mpr rfl)
    have := ((isIso_iff _).mp this).2.1
    simpa [toIso, iso] using this
  · intro h B φ hφ hφ'
    rw [isPreStep_iff] at hφ'
    rw [isIsometric_iff, hφ'] at hφ
    have hB : B.ang = univ := by
      have := φ.ang_le
      rw [h, hφ', PNat.one_coe, pow_one, singleton_mul_univ] at this
      exact univ_subset_iff.mp this
    exact isIso_of φ hφ' (by rw [h, hB, singleton_mul_univ]) (by simpa using hφ)

end

end Angular

end Frobenioid

end Iut
