/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34
import Iut.Frobenioid.Wall

/-!
# The naive Frobenius functor ([FrdI], Proposition 2.1) for model Frobenioids

[FrdI], Proposition 2.1 (p. 44): for `d ∈ ℕ_{≥1}`, the assignment `A ↦ A'`, `φ ↦ φ'`, where
`α : A → A'`, `β : B → B'` are morphisms of Frobenius type of degree `d` and `φ'` is the unique
morphism with `φ' ∘ α = β ∘ φ`, is a functor `Ψ : C → C` (the *naive Frobenius functor* of degree
`d`); the composite of those of degrees `d₁`, `d₂` is that of degree `d₁·d₂`; (ii) `Ψ` is
1-compatible with the Frobenius functor of `F_Φ` (multiplication by `d` on `Φ`), and on `O^▷(A)`
it is raising to the `d`-th power; (iii) `C` is of perfect type iff `Ψ` is an equivalence.

For a model Frobenioid ([FrdI], Theorem 5.2) with the morphisms of Frobenius type
`frob X d = (d, id, 0, 0) : (A, α) → (A, d·α)` this file proves:

* `Model.naiveFrob d`: `(A, α) ↦ (A, d·α)`, `(n, f, Z, u) ↦ (n, f, d·Z, d·u)`;
* `Model.frob_comp_naiveFrob`: `frob ≫ Ψ(φ) = φ ≫ frob` (`φ' ∘ α = β ∘ φ`), and
  `Model.naiveFrob_unique`: `Ψ(φ)` is the only such morphism ((i));
* `Model.naiveFrobCompIso`: `Ψ_{d₁} ⋙ Ψ_{d₂} ≅ Ψ_{d₁ d₂}` ((i));
* `Model.naiveFrob_map_deg`, `_base`, `_div`, `_u`: 1-compatibility with the Frobenius functor of
  `F_Φ` and raising to the `d`-th power on rational functions, in particular on `O^▷` ((ii));
* `GlobalRealified.naiveFrobIsoScale`: on `C^⊩(K)` the naive Frobenius functor of degree `d` is
  the scaling by `d`, and `GlobalRealified.naiveFrob_isEquivalence`: it is an equivalence
  (`C^⊩` is perfect, (iii)).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

/-- **The naive Frobenius functor of degree `d`** ([FrdI], Proposition 2.1(i)) on a model
Frobenioid. -/
def naiveFrob (d : ℕ+) : Model Φ B divB ⥤ Model Φ B divB where
  obj X := ⟨X.base, (d : ℕ) • X.α⟩
  map φ := mk' φ.deg φ.base ((d : ℕ) • φ.div) ((Φ.pos _).nsmul_mem φ.div_mem _)
    ((d : ℕ) • φ.u) (by
      rw [map_nsmul, map_nsmul, smul_comm, ← smul_add, φ.rel, smul_add])
  map_id X := by ext <;> simp
  map_comp φ ψ := by
    ext
    · rfl
    · rfl
    · simp only [mk'_div, comp_div, mk'_base, mk'_deg, map_nsmul, smul_add]
      rw [smul_comm]
    · simp only [mk'_u, comp_u, mk'_base, mk'_deg, map_nsmul, smul_add]
      rw [smul_comm]

@[simp] lemma naiveFrob_obj_base (d : ℕ+) (X : Model Φ B divB) :
    ((naiveFrob d).obj X).base = X.base := rfl
@[simp] lemma naiveFrob_obj_α (d : ℕ+) (X : Model Φ B divB) :
    ((naiveFrob d).obj X).α = (d : ℕ) • X.α := rfl

/-- **Compatibility with the Frobenius functor of `F_Φ`** ([FrdI], Proposition 2.1(ii)):
`Ψ` preserves Frobenius degrees and projections and multiplies zero divisors by `d`. -/
@[simp] lemma naiveFrob_map_deg (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((naiveFrob d).map φ).deg = φ.deg := rfl
@[simp] lemma naiveFrob_map_base (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((naiveFrob d).map φ).base = φ.base := rfl
@[simp] lemma naiveFrob_map_div (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((naiveFrob d).map φ).div = (d : ℕ) • φ.div := rfl
/-- On rational functions (in particular on `O^▷(A)`), `Ψ` is raising to the `d`-th power
([FrdI], Proposition 2.1(ii); additive notation). -/
@[simp] lemma naiveFrob_map_u (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((naiveFrob d).map φ).u = (d : ℕ) • φ.u := rfl

/-- **`φ' ∘ α = β ∘ φ`** for `α = frob X d`, `β = frob Y d`, `φ' = Ψ(φ)`. -/
theorem frob_comp_naiveFrob (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    frob X d ≫ (naiveFrob d).map φ = φ ≫ frob Y d := by
  ext
  · exact mul_comm _ _
  · simp [frob]
  · simp [frob]
  · simp [frob]

/-- **Uniqueness** ([FrdI], Proposition 2.1(i), via Proposition 1.10(i)): `Ψ(φ)` is the only
morphism `ψ` with `ψ ∘ frob = frob ∘ φ`. -/
theorem naiveFrob_unique (d : ℕ+) {X Y : Model Φ B divB} (φ : X ⟶ Y)
    (ψ : (naiveFrob d).obj X ⟶ (naiveFrob d).obj Y) (h : frob X d ≫ ψ = φ ≫ frob Y d) :
    ψ = (naiveFrob d).map φ := by
  have hdeg := congrArg Hom.deg h
  have hbase := congrArg Hom.base h
  have hdiv := congrArg Hom.div h
  have hu := congrArg Hom.u h
  simp only [frob, comp_deg, comp_base, comp_div, comp_u, mk'_deg, mk'_base, mk'_div,
    mk'_u, Category.id_comp, Category.comp_id, GrpOn.pb_id', smul_zero, add_zero, map_zero,
    zero_add] at hdeg hbase hdiv hu
  ext
  · exact mul_right_cancel (hdeg.trans (mul_comm _ _))
  · exact hbase
  · exact hdiv
  · exact hu

/-- The isomorphism `(A, e·(d·α)) ≅ (A, (d e)·α)`. -/
def naiveFrobCompHom (d e : ℕ+) (X : Model Φ B divB) :
    (naiveFrob e).obj ((naiveFrob d).obj X) ⟶ (naiveFrob (d * e)).obj X :=
  mk1 (X := ⟨X.base, (e : ℕ) • (d : ℕ) • X.α⟩) (Y := ⟨X.base, ((d * e : ℕ+) : ℕ) • X.α⟩)
    (𝟙 X.base) 0 (Φ.pos _).zero_mem 0 (by
      rw [GrpOn.pb_id', map_zero, add_zero, add_zero, PNat.mul_coe, smul_smul, mul_comm])

lemma naiveFrobCompHom_isIso (d e : ℕ+) (X : Model Φ B divB) : IsIso (naiveFrobCompHom d e X) :=
  isIso_of _ rfl (by change IsIso (𝟙 X.base); infer_instance) rfl

/-- **`Ψ_{d} ⋙ Ψ_{e} ≅ Ψ_{d e}`** ([FrdI], Proposition 2.1(i)). -/
noncomputable def naiveFrobCompIso (d e : ℕ+) :
    naiveFrob d ⋙ naiveFrob e ≅ (naiveFrob (d * e) : Model Φ B divB ⥤ _) :=
  NatIso.ofComponents
    (fun X => @asIso _ _ _ _ (naiveFrobCompHom d e X) (naiveFrobCompHom_isIso d e X))
    (fun {X Y} φ => by
    ext
    · change 1 * φ.deg = φ.deg * 1
      rw [one_mul, mul_one]
    · change φ.base ≫ 𝟙 Y.base = 𝟙 X.base ≫ φ.base
      simp
    · change Φ.pb φ.base 0 + (1 : ℕ) • ((e : ℕ) • (d : ℕ) • φ.div) =
        Φ.pb (𝟙 X.base) (((d * e : ℕ+) : ℕ) • φ.div) + (φ.deg : ℕ) • 0
      rw [map_zero, zero_add, one_smul, GrpOn.pb_id', smul_zero, add_zero, PNat.mul_coe,
        smul_smul, mul_comm]
    · change B.pb φ.base 0 + (1 : ℕ) • ((e : ℕ) • (d : ℕ) • φ.u) =
        B.pb (𝟙 X.base) (((d * e : ℕ+) : ℕ) • φ.u) + (φ.deg : ℕ) • 0
      rw [map_zero, zero_add, one_smul, GrpOn.pb_id', smul_zero, add_zero, PNat.mul_coe,
        smul_smul, mul_comm])

end Model

/-! ### The global realified Frobenioid is perfect -/

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K]

/-- `(A, d·α) ≅ (A, (d : ℝ)·α)`. -/
noncomputable def naiveFrobScaleHom (d : ℕ+) (X : GlobalRealified K) :
    (Model.naiveFrob d).obj X ⟶ (scale (d : ℝ) (by exact_mod_cast d.pos)).obj X :=
  Model.mk1 (𝟙 _) 0 (effCone K).zero_mem 0 (by
    change (d : ℕ) • X.α + 0 = (d : ℝ) • X.α + 0
    rw [Nat.cast_smul_eq_nsmul])

lemma naiveFrobScaleHom_isIso (d : ℕ+) (X : GlobalRealified K) : IsIso (naiveFrobScaleHom d X) :=
  Model.isIso_of _ rfl (isIso_pt _) rfl

/-- **On `C^⊩(K)` the naive Frobenius functor of degree `d` is the scaling by `d`.** -/
noncomputable def naiveFrobIsoScale (d : ℕ+) :
    (Model.naiveFrob d : GlobalRealified K ⥤ _) ≅ scale (d : ℝ) (by exact_mod_cast d.pos) :=
  NatIso.ofComponents
    (fun X => @asIso _ _ _ _ (naiveFrobScaleHom d X) (naiveFrobScaleHom_isIso d X))
    (fun {X Y} φ => by
    refine Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ (Subtype.ext ?_)
    · change 1 * φ.deg = φ.deg * 1; simp
    · change (0 : ArithDiv K) + (1 : ℕ) • ((d : ℕ) • φ.div) =
        (d : ℝ) • φ.div + (φ.deg : ℕ) • (0 : ArithDiv K)
      simp [Nat.cast_smul_eq_nsmul]
    · change (0 : ArithDiv K) + (1 : ℕ) • ((d : ℕ) • (φ.u : ArithDiv K)) =
        (d : ℝ) • (φ.u : ArithDiv K) + (φ.deg : ℕ) • (0 : ArithDiv K)
      simp [Nat.cast_smul_eq_nsmul])

/-- `(A, c⁻¹·(c·α)) ≅ (A, α)`. -/
noncomputable def scaleInvHom (c : ℝ) (hc : 0 < c) (X : GlobalRealified K) :
    (scale c hc ⋙ scale c⁻¹ (inv_pos.mpr hc)).obj X ⟶ X :=
  Model.mk1 (𝟙 _) 0 (effCone K).zero_mem 0 (by
    change c⁻¹ • c • X.α + 0 = X.α + 0
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul])

lemma scaleInvHom_isIso (c : ℝ) (hc : 0 < c) (X : GlobalRealified K) : IsIso (scaleInvHom c hc X) :=
  Model.isIso_of _ rfl (isIso_pt _) rfl

/-- `scale c ⋙ scale c⁻¹ ≅ 𝟭`. -/
noncomputable def scaleInvIso (c : ℝ) (hc : 0 < c) :
    scale c hc ⋙ scale c⁻¹ (inv_pos.mpr hc) ≅ 𝟭 (GlobalRealified K) :=
  NatIso.ofComponents
    (fun X => @asIso _ _ _ _ (scaleInvHom c hc X) (scaleInvHom_isIso c hc X))
    (fun {X Y} φ => by
    refine Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ (Subtype.ext ?_)
    · change 1 * φ.deg = φ.deg * 1; simp
    · change (0 : ArithDiv K) + (1 : ℕ) • (c⁻¹ • c • φ.div) = φ.div + (φ.deg : ℕ) • 0
      rw [smul_smul, inv_mul_cancel₀ hc.ne']
      simp
    · change (0 : ArithDiv K) + (1 : ℕ) • (c⁻¹ • c • (φ.u : ArithDiv K)) =
        (φ.u : ArithDiv K) + (φ.deg : ℕ) • 0
      rw [smul_smul, inv_mul_cancel₀ hc.ne']
      simp)

/-- **The scalings are autoequivalences of `C^⊩(K)`.** -/
noncomputable def scaleEquiv (c : ℝ) (hc : 0 < c) : GlobalRealified K ≌ GlobalRealified K :=
  CategoryTheory.Equivalence.mk (scale c hc) (scale c⁻¹ (inv_pos.mpr hc))
    (scaleInvIso c hc).symm (by
      have := scaleInvIso (K := K) c⁻¹ (inv_pos.mpr hc)
      simp only [inv_inv] at this
      exact this)

instance (c : ℝ) (hc : 0 < c) : (scale (K := K) c hc).IsEquivalence :=
  (scaleEquiv c hc).isEquivalence_functor

/-- **`C^⊩(K)` is perfect** ([FrdI], Proposition 2.1(iii)): the naive Frobenius functors are
equivalences of categories. -/
instance naiveFrob_isEquivalence (d : ℕ+) :
    (Model.naiveFrob d : GlobalRealified K ⥤ _).IsEquivalence :=
  Functor.isEquivalence_of_iso (naiveFrobIsoScale d).symm

end GlobalRealified

end Frobenioid

end Iut
