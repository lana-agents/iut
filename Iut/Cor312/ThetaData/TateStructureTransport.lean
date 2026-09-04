/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructureOfIso

/-!
# Transport of Tate structures along isometric isomorphisms

For an isometric field isomorphism `k ≃ k'` of complete rank-one valued fields, written as a
bijective `algebraMap k k'` of a normed algebra, a Tate structure on `E` over `k` transports to a
Tate structure on `E ×_k k'` (`Iut.TateStructure.baseChange`): the Tate parameter, the change of
variables and the points are mapped along the isomorphism, and the coordinate pins transport by
the naturality of the Tate parametrization (`TateCurvesTheta`, `algebraMap_X`, `algebraMap_Y`).
The graph line and the canonical generators of the transported structure are the images of
those of the original one (`graphLine_baseChange`, `isCanonical_baseChange`).
-/

namespace Iut

open WeierstrassCurve TateCurvesTheta Iut.Anabelian
open scoped Classical Valued

universe u v

noncomputable section

section PointMapEquiv

variable {k : Type u} {k' : Type v} [Field k] [Field k'] (E : WeierstrassCurve k)
  (f : k →+* k') (hbij : Function.Bijective f)

/-- The isomorphism on points induced by a bijective ring homomorphism. -/
def pointMapEquiv : E.toAffine.Point ≃+ (E.map f).toAffine.Point :=
  AddEquiv.ofBijective (pointMap E f) ⟨pointMap_injective E f, fun P => by
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x' y' h =>
      obtain ⟨x, rfl⟩ := hbij.2 x'
      obtain ⟨y, rfl⟩ := hbij.2 y'
      exact ⟨.some x y ((E.toAffine.map_nonsingular hbij.1 x y).mp h), rfl⟩⟩

@[simp] lemma pointMapEquiv_apply (P : E.toAffine.Point) :
    pointMapEquiv E f hbij P = pointMap E f P := rfl

/-- Coordinates in the model `C • E` are natural in the base field. -/
lemma xCoord_pointMap (C : VariableChange k) (P : E.toAffine.Point) :
    xCoord (C.map f) (pointMap E f P) = f (xCoord C P) := by
  cases P with
  | zero =>
    change (0 : k') = f 0
    rw [map_zero]
  | some x y h =>
    rw [pointMap_some]
    change (f x - f C.r) / ((Units.map (f : k →* k') C.u : k') ^ 2) = f ((x - C.r) / (C.u : k) ^ 2)
    rw [Units.coe_map, map_div₀, map_sub, map_pow]
    rfl

lemma yCoord_pointMap (C : VariableChange k) (P : E.toAffine.Point) :
    yCoord (C.map f) (pointMap E f P) = f (yCoord C P) := by
  cases P with
  | zero =>
    change (0 : k') = f 0
    rw [map_zero]
  | some x y h =>
    rw [pointMap_some]
    change (f y - f C.t - f C.s * (f x - f C.r)) / ((Units.map (f : k →* k') C.u : k') ^ 3) =
      f ((y - C.t - C.s * (x - C.r)) / (C.u : k) ^ 3)
    rw [Units.coe_map, map_div₀, map_sub, map_sub, map_mul, map_sub, map_pow]
    rfl

end PointMapEquiv

section Transport

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {k' : Type v} [Field k'] [Valued k' (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k' (WithZero (Multiplicative ℤ)))] [CompleteSpace k']
variable [NormedAlgebra k k'] (hbij : Function.Bijective (algebraMap k k'))

/-- The isomorphism on units induced by a bijective `algebraMap`. -/
def unitsEquiv : kˣ ≃* k'ˣ :=
  Units.mapEquiv (MulEquiv.ofBijective (algebraMap k k' : k →* k') hbij)

omit [CompleteSpace k] [CompleteSpace k'] in
@[simp] lemma unitsEquiv_apply (u : kˣ) :
    unitsEquiv hbij u = Units.map (algebraMap k k').toMonoidHom u := rfl

omit [CompleteSpace k] [CompleteSpace k'] in
lemma coe_unitsEquiv (u : kˣ) : ((unitsEquiv hbij u : k'ˣ) : k') = algebraMap k k' u := rfl

variable (t : TateParameter k)

omit [CompleteSpace k] [CompleteSpace k'] in
lemma map_zpowers_q :
    (Subgroup.zpowers t.q).map (unitsEquiv hbij).toMonoidHom = Subgroup.zpowers (t.baseChange k').q := by
  rw [MonoidHom.map_zpowers]
  congr 1

/-- The isomorphism of analytic quotients `kˣ/qᶻ ≃ k'ˣ/q'ᶻ`. -/
def quotEquiv : kˣ ⧸ Subgroup.zpowers t.q ≃* k'ˣ ⧸ Subgroup.zpowers (t.baseChange k').q :=
  QuotientGroup.congr _ _ (unitsEquiv hbij) (map_zpowers_q hbij t)

omit [CompleteSpace k] [CompleteSpace k'] in
lemma quotEquiv_mk (u : kˣ) :
    quotEquiv hbij t (QuotientGroup.mk u) = QuotientGroup.mk (unitsEquiv hbij u) := rfl

lemma notMem_of_notMem {u : kˣ} (hu : ∀ n : ℤ, ((t.baseChange k').q : k') ^ n *
    ((unitsEquiv hbij u : k'ˣ) : k') ≠ 1) : ∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1 := by
  intro n hn
  apply hu n
  rw [TateParameter.baseChange_q_coe, coe_unitsEquiv, ← map_zpow₀ (algebraMap k k'),
    ← map_mul (algebraMap k k'), hn, map_one]

variable {E : WeierstrassCurve k}

namespace TateStructure

/-- **Transport of a Tate structure** along a bijective isometric base change. -/
def baseChange (S : TateStructure E) : TateStructure (E.map (algebraMap k k')) where
  t := S.t.baseChange k'
  C := S.C.map (algebraMap k k')
  hC := by rw [map_variableChange, S.hC, S.t.map_tateCurve k']
  iso := (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm.trans
    (S.iso.trans (pointMapEquiv E (algebraMap k k') hbij))
  iso_x u' hu' := by
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    have hu := notMem_of_notMem hbij S.t hu'
    have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
        (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
        Additive.ofMul (QuotientGroup.mk u) := by
      rw [← quotEquiv_mk]
      exact (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm_apply_apply _
    simp only [AddEquiv.trans_apply]
    rw [h1, pointMapEquiv_apply, xCoord_pointMap, S.iso_x u hu, S.t.algebraMap_X k']
    rfl
  iso_y u' hu' := by
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    have hu := notMem_of_notMem hbij S.t hu'
    have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
        (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
        Additive.ofMul (QuotientGroup.mk u) := by
      rw [← quotEquiv_mk]
      exact (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm_apply_apply _
    simp only [AddEquiv.trans_apply]
    rw [h1, pointMapEquiv_apply, yCoord_pointMap, S.iso_y u hu, S.t.algebraMap_Y k']
    rfl

variable (S : TateStructure E)

@[simp] lemma baseChange_t : (S.baseChange hbij).t = S.t.baseChange k' := rfl

lemma baseChange_ofUnit (u : kˣ) :
    (S.baseChange hbij).ofUnit (unitsEquiv hbij u) = pointMap E (algebraMap k k') (S.ofUnit u) := by
  unfold ofUnit
  change ((MulEquiv.toAdditive (quotEquiv hbij S.t)).symm.trans
    (S.iso.trans (pointMapEquiv E (algebraMap k k') hbij)))
      (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u) :
        k'ˣ ⧸ Subgroup.zpowers (S.t.baseChange k').q)) = _
  have h1 : (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm
      (Additive.ofMul (QuotientGroup.mk (unitsEquiv hbij u))) =
      Additive.ofMul (QuotientGroup.mk u) := by
    rw [← quotEquiv_mk]
    exact (MulEquiv.toAdditive (quotEquiv hbij S.t)).symm_apply_apply _
  simp only [AddEquiv.trans_apply]
  rw [h1]
  rfl

omit [CompleteSpace k] [CompleteSpace k'] in
lemma unitsEquiv_pow_eq_one_iff (u : kˣ) (ℓ : ℕ) :
    unitsEquiv hbij u ^ ℓ = 1 ↔ u ^ ℓ = 1 := by
  rw [← map_pow, ← map_one (unitsEquiv hbij)]
  exact (unitsEquiv hbij).injective.eq_iff

/-- The graph line of the transported structure is the image of the graph line. -/
theorem graphLine_baseChange (ℓ : ℕ) :
    (S.baseChange hbij).graphLine ℓ = (S.graphLine ℓ).map (pointMap E (algebraMap k k')) := by
  ext P'
  rw [AddSubgroup.mem_map]
  simp only [mem_graphLine_iff]
  constructor
  · rintro ⟨u', hu', rfl⟩
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    rw [unitsEquiv_pow_eq_one_iff] at hu'
    exact ⟨S.ofUnit u, ⟨u, hu', rfl⟩, (S.baseChange_ofUnit hbij u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨unitsEquiv hbij u, (unitsEquiv_pow_eq_one_iff hbij u ℓ).mpr hu,
      S.baseChange_ofUnit hbij u⟩

omit [CompleteSpace k] [CompleteSpace k'] in
lemma unitsEquiv_pow_eq_zpow_iff (u : kˣ) (ℓ : ℕ) (m : ℤ) :
    unitsEquiv hbij u ^ ℓ = (S.t.baseChange k').q ^ m ↔ u ^ ℓ = S.t.q ^ m := by
  have hq : (S.t.baseChange k').q = unitsEquiv hbij S.t.q := rfl
  rw [hq, ← map_pow, ← map_zpow]
  exact (unitsEquiv hbij).injective.eq_iff

/-- The canonical generators of the transported structure are the images of the canonical
generators. -/
theorem isCanonical_baseChange (ℓ : ℕ) (P : E.toAffine.Point) :
    (S.baseChange hbij).IsCanonical ℓ (pointMap E (algebraMap k k') P) ↔ S.IsCanonical ℓ P := by
  unfold IsCanonical
  rw [baseChange_t]
  constructor
  · rintro ⟨u', hu', m, hm⟩
    obtain ⟨u, rfl⟩ := (unitsEquiv hbij).surjective u'
    rw [S.baseChange_ofUnit hbij u] at hu'
    refine ⟨u, pointMap_injective E _ hu', m, ?_⟩
    rw [unitsEquiv_pow_eq_zpow_iff, unitsEquiv_pow_eq_zpow_iff] at hm
    exact hm
  · rintro ⟨u, hu, m, hm⟩
    refine ⟨unitsEquiv hbij u, by rw [S.baseChange_ofUnit hbij u, hu], m, ?_⟩
    rw [unitsEquiv_pow_eq_zpow_iff, unitsEquiv_pow_eq_zpow_iff]
    exact hm

end TateStructure

end Transport

end

end Iut
