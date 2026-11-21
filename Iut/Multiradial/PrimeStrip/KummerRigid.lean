/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Components
import Iut.Reconstruction.Local.MulRigid

/-!
# [AbsTopIII], Proposition 3.2 (iv), injectivity, for `Π_v ↷ \bar{ℚ}_p^×` (MR21 R3)

[AbsTopIII], Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt`,
l.4111–4124): for MLF-Galois `T`-pairs, the natural map
`Isom_{C^MLF_T}((Π ↷ M_T), (Π* ↷ M*_T)) → Isom_TG(Π, Π*)` is injective (a bijection if `T = TM`).
For `T = TM` and the `Π_v`-module `\bar{ℚ}_p^×` (`PiMul D v`, `Π_v` acting through `Π_v → G_v`),
the injectivity says that an automorphism acting trivially on `Π_v` acts trivially on
`\bar{ℚ}_p^×`:

* **`KummerRigid D v`**: every `Π_v`-equivariant additive automorphism `ψ` of `PiMul D v` with
  `ordPi ∘ ψ = λ · ordPi` for some `λ > 0` is the identity;
* **`kummerRigid`**: `KummerRigid D v` holds if `Π_v → G_v` is surjective (the first half of the
  quotient property `PiToGQuotient D v`, debt H3 of the MR20 plan). The proof is the elementary
  Kummer argument of `Iut.Frobenioid.PAdicGalois.Rigid.mulAut_eq_refl` (`MulRigid.lean`) for
  `G_v = Gal(\bar{ℚ}_p / L_v)`, `L_v = ι(K_v)` finite over `ℚ_{p_v}` (`finiteDimensional_Lv_rigid`).
  Surjectivity enters only to turn `Π_v`-equivariance into `G_v`-equivariance; an open image
  of `Π_v → G_v` would suffice as well (apply `mulAut_eq_refl` to its fixed field).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`L_v = ι(K_v)` is finite over `ℚ_{p_v}`** (`K_v ≃ L_v`,
`LocalConstruct.finite_padicAlgebra`). -/
theorem finiteDimensional_Lv_rigid : FiniteDimensional ℚ_[pv D v] (Lv D v) := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  haveI : FiniteDimensional ℚ_[pv D v] (Kv D v) :=
    LocalConstruct.finite_padicAlgebra (p := pv D v) rfl
  exact LinearEquiv.finiteDimensional (eL (pv D v) (Kv D v)).toLinearEquiv

/-- **[AbsTopIII], Proposition 3.2 (iv), injectivity, `T = TM`**
(`Topics in Absolute Anabelian Geometry III.txt` l.4111–4124), for `Π_v ↷ \bar{ℚ}_p^×`:
a `Π_v`-equivariant additive automorphism `ψ` of `\bar{ℚ}_p^×` (`PiMul D v`) with
`ord ∘ ψ = λ · ord` for some `λ > 0` is the identity. -/
def KummerRigid : Prop :=
  ∀ ψ : PiMul D v ≃+ PiMul D v, (∀ (g : (Piv D v).carrier) (m : PiMul D v), ψ (g • m) = g • ψ m) →
    ∀ l : ℝ, 0 < l → (∀ m, ordPi D v (ψ m) = l * ordPi D v m) → ψ = AddEquiv.refl _

/-- **`KummerRigid D v`** from the surjectivity of `Π_v → G_v` (`Rigid.mulAut_eq_refl` for
`G_v = Gal(\bar{ℚ}_p / L_v)`). -/
theorem kummerRigid (h : Function.Surjective (piToG D v)) : KummerRigid D v := by
  intro ψ hψ l hl hord
  haveI := finiteDimensional_Lv_rigid D v
  refine PAdicGalois.Rigid.mulAut_eq_refl (p := pv D v) (E := Lv D v) ψ (fun g m => ?_) hl hord
  obtain ⟨π, rfl⟩ := h g
  exact hψ π m

end PrimeStrip

end Multiradial

end Iut

end
