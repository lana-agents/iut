/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.PmBridge

/-!
# Gluing `D-Θ^±`- and `D-Θ^ell`-bridges (IUT I, Proposition 6.6(iv), Corollary 6.12(ii))

Given a `D-Θ^±`-bridge `P` and a `D-Θ^ell`-bridge `E` (label layer, `PmBridge.lean`), a **gluing**
is a capsule-`+`-full poly-isomorphism between their capsules — an isomorphism of `F_ℓ^±`-torsors
`σ : T_P ≅ T_E` of index sets together with `+`-full poly-isomorphisms
`α_{t,v} : †D_{t,v} ≅ ‡D_{σ(t),v}` — such that the glued data (`glued`) is a
`D-Θ^{±ell}`-Hodge theater, i.e. satisfies the sign condition `pos`.

**IUT I, Proposition 6.6(iv)** (`glueEquiv`): the gluings form a torsor over
`F_ℓ^{⋊±} × {±1}^V`, the first factor being the induced isomorphism of `F_ℓ^±`-torsors of index
sets and the second the signs of the `α_{0,v}` (`glueEquivSemi`).
-/

namespace Iut

namespace HodgeTheater

open PmTorsor

universe u

variable {ℓ : ℕ} [OddPrime ℓ] {V : Type u}

namespace DThetaPmEllHT

/-- A gluing of a `D-Θ^±`-bridge and a `D-Θ^ell`-bridge (IUT I, Proposition 6.6(iv)). -/
def Glue (P : DThetaPmBridge ℓ V) (E : DThetaEllBridge ℓ V) : Type u :=
  {p : (σ : PmTorsor.Iso P.T E.T) × (∀ t v, GrpIso (P.cap t v) (E.cap (σ t) v)) //
    ∃ κ : V → ℤˣ, ∀ t v,
      ((P.φ t v).1.symm.trans ((p.2 t v).1.trans (E.θ (p.1 t) v))).sign = κ v}

lemma zero_of_grpIso {A B : PmGroup ℓ} (f : GrpIso A B) : f.1 A.zero = B.zero :=
  (shift_eq_zero_iff f.1).mp f.2

/-- **The `D-Θ^{±ell}`-Hodge theater of a gluing.** -/
noncomputable def glued {P : DThetaPmBridge ℓ V} {E : DThetaEllBridge ℓ V} (g : Glue P E) :
    DThetaPmEllHT ℓ V where
  T := P.T
  cap := P.cap
  tgt := P.tgt
  φ := P.φ
  glob := E.glob
  ε := g.1.1.trans E.ε
  θ t v := (g.1.2 t v).1.trans (E.θ (g.1.1 t) v)
  θ_zero t v := by
    simp only [PmTorsor.Iso.trans_apply]
    rw [zero_of_grpIso, E.θ_zero]
  κ := g.2.choose
  pos := g.2.choose_spec

/-- The sign of a composite `φ^{-1}·α·θ`. -/
lemma sign_comp {A B C D' : PmTorsor ℓ} (φ : PmTorsor.Iso A B) (α : PmTorsor.Iso A C)
    (θ : PmTorsor.Iso C D') : (φ.symm.trans (α.trans θ)).sign = θ.sign * α.sign * φ.sign := by
  simp only [PmTorsor.Iso.trans_sign, PmTorsor.Iso.symm_sign, mul_assoc]

/-- The sign of `α_{t,v}` forced by `σ` and the sign `b v` of `α_{0,v}`. -/
noncomputable def alphaSign (P : DThetaPmBridge ℓ V) (E : DThetaEllBridge ℓ V)
    (σ : PmTorsor.Iso P.T E.T) (b : V → ℤˣ) (t : P.T.carrier) (v : V) : ℤˣ :=
  ((E.θ (σ P.T.zero) v).sign * b v * (P.φ P.T.zero v).1.sign) * (P.φ t v).1.sign *
    (E.θ (σ t) v).sign

lemma units_aux (a b c d e : ℤˣ) : e * (a * b * c * d * e) * d = a * b * c := by
  calc e * (a * b * c * d * e) * d = a * b * c * (d * d) * (e * e) := by ac_rfl
    _ = a * b * c := by rw [Int.units_mul_self, Int.units_mul_self, mul_one, mul_one]

lemma units_aux' (a b c : ℤˣ) : a * b * c * c * a = b := by
  calc a * b * c * c * a = b * (a * a) * (c * c) := by ac_rfl
    _ = b := by rw [Int.units_mul_self, Int.units_mul_self, mul_one, mul_one]

lemma units_aux'' (d e g κ : ℤˣ) (ht : e * g * d = κ) : g = κ * d * e := by
  rw [← ht]
  calc g = g * (d * d) * (e * e) := by rw [Int.units_mul_self, Int.units_mul_self, mul_one,
        mul_one]
    _ = e * g * d * d * e := by ac_rfl

/-- The gluing with given isomorphism of index sets and signs at `0`. -/
noncomputable def glueOf (P : DThetaPmBridge ℓ V) (E : DThetaEllBridge ℓ V)
    (σ : PmTorsor.Iso P.T E.T) (b : V → ℤˣ) : Glue P E :=
  ⟨⟨σ, fun t v => (GrpIso.equiv _ _).symm (alphaSign P E σ b t v)⟩,
    fun v => (E.θ (σ P.T.zero) v).sign * b v * (P.φ P.T.zero v).1.sign, fun t v => by
      rw [sign_comp, GrpIso.equiv_symm_sign]
      exact units_aux _ _ _ _ _⟩

/-- **IUT I, Proposition 6.6(iv)**: the gluings of a `D-Θ^±`-bridge and a `D-Θ^ell`-bridge form a
torsor over (the isomorphisms of `F_ℓ^±`-torsors of index sets) `× {±1}^V`. -/
noncomputable def glueEquiv (P : DThetaPmBridge ℓ V) (E : DThetaEllBridge ℓ V) :
    Glue P E ≃ PmTorsor.Iso P.T E.T × (V → ℤˣ) where
  toFun g := (g.1.1, fun v => (g.1.2 P.T.zero v).1.sign)
  invFun q := glueOf P E q.1 q.2
  left_inv g := by
    obtain ⟨⟨σ, α⟩, κ, hκ⟩ := g
    apply Subtype.ext
    simp only [glueOf]
    congr 1
    funext t v
    apply GrpIso.ext_sign
    rw [GrpIso.equiv_symm_sign]
    unfold alphaSign
    have h0 := hκ P.T.zero v
    have ht := hκ t v
    rw [sign_comp] at h0 ht
    rw [h0]
    exact (units_aux'' _ _ _ _ ht).symm
  right_inv q := by
    obtain ⟨σ, b⟩ := q
    simp only [glueOf, GrpIso.equiv_symm_sign, Prod.mk.injEq, true_and]
    funext v
    exact units_aux' _ _ _

/-- **IUT I, Proposition 6.6(iv)**: the gluings form an `F_ℓ^{⋊±} × {±1}^V`-torsor. -/
noncomputable def glueEquivSemi (P : DThetaPmBridge ℓ V) (E : DThetaEllBridge ℓ V) :
    Glue P E ≃ FlSemi ℓ × (V → ℤˣ) :=
  (glueEquiv P E).trans (Equiv.prodCongr (PmTorsor.isoEquivSemi _ _) (Equiv.refl _))

/-- The glued theater has the given `D-Θ^±`-bridge. -/
theorem glued_toPm {P : DThetaPmBridge ℓ V} {E : DThetaEllBridge ℓ V} (g : Glue P E) :
    (glued g).toPm = P := rfl

end DThetaPmEllHT

end HodgeTheater

end Iut
