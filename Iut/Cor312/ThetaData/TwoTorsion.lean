/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.GlobalField
import Iut.Torsion.Count
import Iut.Tower.IntegralTorsion

/-!
# The `2`-torsion of the curve of initial Θ-data is rational

`Iut.card_torsionBy_eq_sq'`: over an algebraically closed field of characteristic `0`, the
`n`-torsion of an elliptic curve has `n²` elements (`Iut.Torsion.card_torsionBy_eq_sq` after
completing the square, `Iut.IntegralTorsion.completeSquare`).

`Iut.four_le_card_torsionBy_two`: if the `6`-torsion of `E` is rational over the number field
`F` (IUT I, Definition 3.1(b), `Iut.SixTorsionRational`), then `E(F)[2]` has (at least) four
elements.
-/

namespace Iut

open WeierstrassCurve

/-- Membership in the `n`-torsion subgroup, for an integer `n`. -/
lemma mem_torsionBy_iff' {A : Type*} [AddCommGroup A] (n : ℤ) (x : A) :
    x ∈ AddSubgroup.torsionBy A n ↔ n • x = 0 :=
  Submodule.mem_torsionBy_iff ..

/-- Transport of the `n`-torsion along an isomorphism of point groups. -/
lemma card_torsionBy_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℤ) :
    Nat.card (AddSubgroup.torsionBy A n) = Nat.card (AddSubgroup.torsionBy B n) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun P => ?_)
  simp only [mem_torsionBy_iff', AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    ← map_zsmul, AddEquiv.map_eq_zero_iff]

open scoped Classical in
/-- **`|E[n]| = n²` over an algebraically closed field of characteristic `0`**, for every
Weierstrass model. -/
theorem card_torsionBy_eq_sq' {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point (n : ℤ)) = n ^ 2 := by
  haveI : NeZero (2 : K) := ⟨two_ne_zero⟩
  rw [card_torsionBy_congr (Anabelian.vcEquiv (IntegralTorsion.completeSquare W) W)]
  exact Torsion.card_torsionBy_eq_sq (W := (IntegralTorsion.completeSquare W • W).toAffine)
    (IntegralTorsion.completeSquare_a₁ W) (IntegralTorsion.completeSquare_a₃ W) n hn

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type*} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

open scoped Classical in
/-- **Rational `6`-torsion gives four rational `2`-torsion points**: `|E(F)[2]| ≥ 4`. -/
theorem four_le_card_torsionBy_two (h6 : SixTorsionRational F E Fbar) :
    2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ)) := by
  haveI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed F
  haveI : CharZero Fbar := charZero_of_injective_algebraMap (algebraMap F Fbar).injective
  have hE : E.baseChange F = E := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  haveI : (E.baseChange Fbar).IsElliptic := inferInstanceAs (E.map (algebraMap F Fbar)).IsElliptic
  set f := Affine.Point.baseChange (W' := E) F Fbar with hf
  have hinj : Function.Injective f := Affine.Point.map_injective _
  have hcard : Nat.card ↥(AddSubgroup.torsionBy (E.baseChange Fbar).toAffine.Point ((2 : ℕ) : ℤ))
      = 2 ^ 2 := card_torsionBy_eq_sq' (E.baseChange Fbar) 2 two_ne_zero
  -- every `2`-torsion point over `F̄` is the image of a `2`-torsion point over `F`
  have hlift : ∀ P : ↥(AddSubgroup.torsionBy (E.baseChange Fbar).toAffine.Point ((2 : ℕ) : ℤ)),
      ∃ Q : ↥(AddSubgroup.torsionBy (E.baseChange F).toAffine.Point ((2 : ℕ) : ℤ)), f Q = P := by
    intro P
    have hP6 : (P : (E.baseChange Fbar).toAffine.Point) ∈
        AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) 6 := by
      have h2 := P.2
      rw [mem_torsionBy_iff'] at h2 ⊢
      have : (6 : ℤ) • (P : (E.baseChange Fbar).toAffine.Point) =
          (3 : ℤ) • (((2 : ℕ) : ℤ) • (P : (E.baseChange Fbar).toAffine.Point)) := by
        rw [smul_smul]; norm_num
      rw [this, h2, smul_zero]
    obtain ⟨Q, hQ⟩ := h6 _ hP6
    refine ⟨⟨Q, ?_⟩, hQ⟩
    rw [mem_torsionBy_iff']
    apply hinj
    rw [map_zsmul, map_zero, hQ]
    exact (mem_torsionBy_iff' _ _).mp P.2
  choose g hg using hlift
  have hginj : Function.Injective g := fun P P' h => Subtype.ext (by rw [← hg P, ← hg P', h])
  haveI : Finite ↥(AddSubgroup.torsionBy (E.baseChange Fbar).toAffine.Point ((2 : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite ↥(AddSubgroup.torsionBy (E.baseChange F).toAffine.Point ((2 : ℕ) : ℤ)) := by
    refine Finite.of_injective (fun Q => (⟨f Q, ?_⟩ :
      ↥(AddSubgroup.torsionBy (E.baseChange Fbar).toAffine.Point ((2 : ℕ) : ℤ)))) ?_
    · rw [mem_torsionBy_iff', ← map_zsmul, (mem_torsionBy_iff' _ _).mp Q.2,
        map_zero]
    · intro Q Q' h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
  have key := Nat.card_le_card_of_injective g hginj
  rw [hcard] at key
  have h' : Nat.card ↥(AddSubgroup.torsionBy (E.baseChange F).toAffine.Point ((2 : ℕ) : ℤ)) =
      Nat.card ↥(AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ)) := by
    rw [hE]
  rw [← h']
  omega

end Iut
