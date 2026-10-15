/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.PlaneField
import Mathlib.Algebra.Field.TransferInstance

/-!
# The reconstructed field `RecField A p ≅ ℂ`

For an Aut-holomorphic space `(X, A)` isomorphic to the Aut-holomorphic plane (`IsPlane A`, as a
`Fact`) and `p ∈ X`:

* `RecField A p`: the set `A_p ∪ {0} ⊆ (X → X)` of `Reconstruct.lean`, with the topology of
  pointwise convergence;
* its **field structure**, whose operations are the model-implicit ones (`add_val`: pointwise
  `+_p`; `mul_val`: composition; `neg_val`, `inv_val`, `zero_val`, `one_val`);
* `recEquiv ψ hψ p : RecField A p ≃+* ℂ` for **every** isomorphism `ψ : (X, A) ≅ ℂ`, a
  homeomorphism (`recEquiv_continuous`, `recEquiv_symm_continuous`): **the reconstructed field is
  a topological field isomorphic to `ℂ`** — the "done when" statement `recField_equiv` of MR10 for
  the planar case;
* `stabEquivUnits`: `A_p ≅ (A_p ∪ {0})ˣ ≅ ℂ^×` ([AbsTopIII], Proposition 2.6(a): the natural
  isomorphism `ℂ^× ≅ A_p`).
-/

namespace Iut

namespace AutHol

open Set

variable {X : Type*} [TopologicalSpace X]

/-- **The field reconstructed from an Aut-holomorphic space `(X, A)` at `p`**: the set
`A_p ∪ {0}` of self-maps of `X`. -/
def RecField (A : AutHolStr X) (p : X) : Type _ := Kset A.global p

instance (A : AutHolStr X) (p : X) : TopologicalSpace (RecField A p) :=
  inferInstanceAs (TopologicalSpace (Kset A.global p))

namespace RecField

variable {A : AutHolStr X} {p : X}

/-- The underlying self-map of `X`. -/
def val (a : RecField A p) : X → X := Subtype.val a

theorem val_mem (a : RecField A p) : a.val ∈ Kset A.global p := a.2

theorem val_injective : Function.Injective (val : RecField A p → X → X) := Subtype.val_injective

theorem continuous_val : Continuous (val : RecField A p → X → X) := continuous_subtype_val

end RecField

/-- **The coefficient equivalence** `A_p ∪ {0} ≃ ℂ` attached to an isomorphism `ψ : (X, A) ≅ ℂ`. -/
noncomputable def coeffEquiv {A : AutHolStr X} {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X) :
    RecField A p ≃ ℂ where
  toFun f := coeff ψ p f.val
  invFun c := ⟨ofCoeff ψ p c, ofCoeff_mem hψ p c⟩
  left_inv f := Subtype.ext (ofCoeff_coeff hψ p f.2)
  right_inv c := coeff_ofCoeff ψ p c

theorem coeffEquiv_apply {A : AutHolStr X} {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X)
    (f : RecField A p) : coeffEquiv hψ p f = coeff ψ p f.val := rfl

theorem coeffEquiv_symm_val {A : AutHolStr X} {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X)
    (c : ℂ) : ((coeffEquiv hψ p).symm c).val = ofCoeff ψ p c := rfl

section Field

variable (A : AutHolStr X) [hA : Fact (IsPlane A)] (p : X)

/-- A chosen isomorphism `(X, A) ≅ ℂ` (used only to verify the field laws). -/
noncomputable def chosenIso : X ≃ₜ ℂ := hA.out.choose

theorem chosenIso_spec : IsIso A plane (chosenIso A) := hA.out.choose_spec

noncomputable instance : Field (RecField A p) := (coeffEquiv (chosenIso_spec A) p).field

variable {A p}

/-- **Addition is pointwise `+_p`.** -/
theorem add_val (a b : RecField A p) : (a + b).val = kAdd A.global p a.val b.val := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm (e a + e b)).val = _
  rw [coeffEquiv_symm_val, coeffEquiv_apply, coeffEquiv_apply,
    ← coeff_kAdd (chosenIso_spec A) p a.val_mem b.val_mem,
    ofCoeff_coeff (chosenIso_spec A) p (kAdd_mem (chosenIso_spec A) p a.val_mem b.val_mem)]

/-- **Multiplication is composition.** -/
theorem mul_val (a b : RecField A p) : (a * b).val = kMul a.val b.val := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm (e a * e b)).val = _
  rw [coeffEquiv_symm_val, coeffEquiv_apply, coeffEquiv_apply,
    ← coeff_kMul (chosenIso_spec A) p a.val_mem b.val_mem,
    ofCoeff_coeff (chosenIso_spec A) p (kMul_mem (chosenIso_spec A) p a.val_mem b.val_mem)]

theorem neg_val (a : RecField A p) : (-a).val = kNeg A.global p a.val := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm (-e a)).val = _
  rw [coeffEquiv_symm_val, coeffEquiv_apply, ← coeff_kNeg (chosenIso_spec A) p a.val_mem,
    ofCoeff_coeff (chosenIso_spec A) p (kNeg_mem (chosenIso_spec A) p a.val_mem)]

theorem inv_val (a : RecField A p) : (a⁻¹).val = kInv A.global p a.val := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm (e a)⁻¹).val = _
  rw [coeffEquiv_symm_val, coeffEquiv_apply, ← coeff_kInv (chosenIso_spec A) p a.val_mem,
    ofCoeff_coeff (chosenIso_spec A) p (kInv_mem (chosenIso_spec A) p a.val_mem)]

theorem zero_val : (0 : RecField A p).val = kZero p := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm 0).val = _
  rw [coeffEquiv_symm_val, ← coeff_kZero (chosenIso A) p,
    ofCoeff_coeff (chosenIso_spec A) p (kZero_mem A p)]

theorem one_val : (1 : RecField A p).val = kOne := by
  set e := coeffEquiv (chosenIso_spec A) p
  change (e.symm 1).val = _
  rw [coeffEquiv_symm_val, ← coeff_kOne (chosenIso A) p,
    ofCoeff_coeff (chosenIso_spec A) p (kOne_mem A p)]

/-- **The reconstructed field is isomorphic to `ℂ`**, via any isomorphism `ψ : (X, A) ≅ ℂ`. -/
noncomputable def recEquiv {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X) : RecField A p ≃+* ℂ where
  toEquiv := coeffEquiv hψ p
  map_add' a b := by
    change coeff ψ p (a + b).val = coeff ψ p a.val + coeff ψ p b.val
    rw [add_val, coeff_kAdd hψ p a.val_mem b.val_mem]
  map_mul' a b := by
    change coeff ψ p (a * b).val = coeff ψ p a.val * coeff ψ p b.val
    rw [mul_val, coeff_kMul hψ p a.val_mem b.val_mem]

theorem recEquiv_apply {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (a : RecField A p) :
    recEquiv hψ p a = ψ (a.val (ψ.symm (ψ p + 1))) - ψ p := rfl

theorem recEquiv_symm_val {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (c : ℂ) (x : X) :
    ((recEquiv hψ p).symm c).val x = ψ.symm (ψ p + c * (ψ x - ψ p)) := rfl

/-- `recEquiv` is continuous (pointwise topology on `RecField A p`). -/
theorem recEquiv_continuous {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) :
    Continuous (recEquiv hψ p) := by
  change Continuous fun a : RecField A p => ψ (a.val (ψ.symm (ψ p + 1))) - ψ p
  exact (ψ.continuous.comp ((continuous_apply _).comp RecField.continuous_val)).sub
    continuous_const

/-- The inverse of `recEquiv` is continuous. -/
theorem recEquiv_symm_continuous {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) :
    Continuous (recEquiv hψ p).symm := by
  have : Continuous fun c : ℂ => ((recEquiv hψ p).symm c).val := by
    refine continuous_pi fun x => ?_
    simp only [recEquiv_symm_val]
    fun_prop
  exact this.subtype_mk _

/-- **`RecField A p ≅ ℂ` as topological fields.** -/
noncomputable def recHomeo {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (p : X) : RecField A p ≃ₜ ℂ where
  toEquiv := (recEquiv hψ p).toEquiv
  continuous_toFun := recEquiv_continuous hψ
  continuous_invFun := recEquiv_symm_continuous hψ

/-! ### The stabiliser `A_p ≅ ℂ^×` -/

variable (A p) in
/-- The stabiliser `A_p` of `p` in `A_X(X)`. -/
def stab : Subgroup (X ≃ₜ X) where
  carrier := {g | g ∈ A.global ∧ g p = p}
  mul_mem' hg hh := ⟨A.global.mul_mem hg.1 hh.1, by simp [hg.2, hh.2]⟩
  one_mem' := ⟨A.global.one_mem, rfl⟩
  inv_mem' hg := ⟨A.global.inv_mem hg.1, by
    simp only [Homeomorph.inv_apply]
    rw [Homeomorph.symm_apply_eq, hg.2]⟩

omit hA in
theorem exists_ne_of_isPlane (h : IsPlane A) (p : X) : ∃ x : X, x ≠ p := by
  obtain ⟨ψ, -⟩ := h
  exact ⟨ψ.symm (ψ p + 1), fun h => by
    have := congrArg ψ h
    simp at this⟩

/-- The element of `RecField A p` given by `g ∈ A_p`. -/
def ofStab (g : stab A p) : RecField A p := ⟨⇑g.1, Or.inl ⟨g.1, g.2.1, g.2.2, rfl⟩⟩

theorem ofStab_ne_zero (g : stab A p) : ofStab g ≠ 0 := by
  intro h
  have h1 := congrArg RecField.val h
  rw [zero_val] at h1
  obtain ⟨x, hx⟩ := exists_ne_of_isPlane hA.out p
  apply hx
  have := congrFun h1 ((g.1).symm x)
  simpa [ofStab, RecField.val, kZero] using this

/-- `A_p → (A_p ∪ {0})ˣ`. -/
noncomputable def stabToUnits : stab A p →* (RecField A p)ˣ where
  toFun g := Units.mk0 (ofStab g) (ofStab_ne_zero g)
  map_one' := by
    ext1
    apply RecField.val_injective
    rw [Units.val_mk0, Units.val_one, one_val]
    rfl
  map_mul' g h := by
    ext1
    apply RecField.val_injective
    rw [Units.val_mk0, Units.val_mul, mul_val, Units.val_mk0, Units.val_mk0]
    rfl

/-- **`A_p ≅ (A_p ∪ {0})ˣ`** ([AbsTopIII], Proposition 2.6(a)). -/
noncomputable def stabEquivUnits : stab A p ≃* (RecField A p)ˣ :=
  MulEquiv.ofBijective stabToUnits (by
    constructor
    · intro g h hgh
      have := congrArg (fun u : (RecField A p)ˣ => (u : RecField A p).val) hgh
      simp only [stabToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at this
      exact Subtype.ext (DFunLike.coe_injective this)
    · intro u
      rcases (u : RecField A p).2 with ⟨g, hg, hgp, hgu⟩ | h0
      · refine ⟨⟨g, hg, hgp⟩, ?_⟩
        ext1
        exact Subtype.ext hgu
      · exfalso
        apply u.ne_zero
        apply RecField.val_injective
        rw [zero_val]
        exact h0)

/-- **`A_p ≅ ℂ^×`**, via any isomorphism `ψ : (X, A) ≅ ℂ`. -/
noncomputable def stabEquivUnitsComplex {ψ : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) :
    stab A p ≃* ℂˣ :=
  stabEquivUnits.trans (Units.mapEquiv (recEquiv hψ p).toMulEquiv)

end Field

end AutHol

end Iut
