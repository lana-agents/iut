/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered
import Iut.EtaleTheta.TemperedCovering

/-!
# Tempered Frobenioids with units, and `Y = Π^tp_Y` (step 2, milestone (14))

Two refinements of the tempered Frobenioid of theta divisors (`Tempered.lean`, [EtTh] §3):

* **The unit part of `B₀`** ([EtTh], Definition 3.3: the kernel of the divisor map
  `B₀ → Φ₀^gp` of a tempered Frobenioid is the group of units `O^×`). `unitThetaGrp χ U` is
  `B₀ = U × {theta-monomial divisors}` for an abelian group `U` (in [EtTh]: `O_K^×`, the
  units of the base field, which are the same on every covering, so pull-backs are the identity
  on `U`), with the divisor map `(u, f) ↦ f` (`unitThetaDiv`). `ker_unitThetaDiv`: **its kernel is
  exactly `U`**; `unitThetaData_isFrobenioid`: the resulting tempered Frobenioid is a Frobenioid.
* **The object `Y` of the tempered Frobenioid of the Tate curve is the `ℤ`-covering of
  `tempered-fundamental-groups`**: `tateY_H` (its subgroup is `Π^tp_Y = TateObject.piY`,
  `TemperedCovering.lean`) and `mem_tateY_H_iff` (it is the stabilizer of the base point of the
  fibre of `Y = X₀`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-! ### The unit part of `B₀` -/

section Units

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* Multiplicative ℤ) (U : Type u) [AddCommGroup U]

/-- **`B₀ = U × {theta-monomial divisors}`**: the units `U` (pull-backs act trivially on them)
and the divisors of the theta monomials. -/
def unitThetaGrp : GrpOn.{u} (OrbitObj G) where
  obj A := U × thetaGp χ A
  pb f := (AddMonoidHom.id U).prodMap ((thetaGrp χ).pb f)
  pb_id A x := Prod.ext rfl ((thetaGrp χ).pb_id A x.2)
  pb_comp f g x := Prod.ext rfl ((thetaGrp χ).pb_comp f g x.2)
  pb_injective f x y h := by
    have h1 : x.1 = y.1 := by simpa using congrArg Prod.fst h
    exact Prod.ext h1 ((thetaGrp χ).pb_injective f (congrArg Prod.snd h))
  pb_bijective_of_fsm f hf := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · have h1 : x.1 = y.1 := by simpa using congrArg Prod.fst h
      exact Prod.ext h1 ((thetaGrp χ).pb_injective f (congrArg Prod.snd h))
    obtain ⟨x, hx⟩ := ((thetaGrp χ).pb_bijective_of_fsm f hf).2 y.2
    exact ⟨(y.1, x), Prod.ext rfl hx⟩

/-- **The divisor map** `B₀ → Φ₀^gp`, `(u, f) ↦ f`. -/
def unitThetaDiv : DivHom (unitThetaGrp χ U) (divMonoid χ).toGrpOn where
  app A := (thetaGp χ A).subtype.comp (AddMonoidHom.snd U (thetaGp χ A))
  natural _ _ := rfl

/-- **The tempered Frobenioid of theta divisors with units.** -/
def unitThetaData : TemperedFrobenioidData G where
  Φ₀ := divMonoid χ
  B₀ := unitThetaGrp χ U
  div₀ := unitThetaDiv χ U

/-- **It is a Frobenioid.** -/
theorem unitThetaData_isFrobenioid :
    IsFrobenioid (Model.toElem (unitThetaData χ U).Φ₀ (unitThetaData χ U).B₀
      (unitThetaData χ U).div₀) :=
  (unitThetaData χ U).isFrobenioid

/-- **The kernel of the divisor map is the group of units** ([EtTh], Definition 3.3). -/
theorem ker_unitThetaDiv (A : OrbitObj G) :
    ((unitThetaDiv χ U).app A).ker = (AddMonoidHom.inl U (thetaGp χ A)).range := by
  ext ⟨u, f⟩
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    have hf : f = 0 := Subtype.ext h
    exact ⟨u, by rw [hf]; rfl⟩
  · rintro ⟨v, hv⟩
    have hf : f = 0 := (congrArg Prod.snd hv).symm
    change ((f : divGp χ A)) = 0
    rw [hf]
    rfl

end Units

/-! ### `Y` is the `ℤ`-covering of the Tate curve -/

section Tate

open TemperedFundamentalGroups

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (T : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The subgroup of the object `Y` of the tempered Frobenioid of the Tate curve is
`Π^tp_Y`** (`EtaleTheta.TateObject.piY`). -/
theorem tateY_H : (tateY (A := A) T V hV).H = EtaleTheta.TateObject.piY (A := A) T V hV := rfl

/-- **`Y` is the stabilizer of the base point of the fibre of the `ℤ`-covering `X₀`.** -/
theorem mem_tateY_H_iff (α : temperedPi1 O R A V hV) :
    α ∈ (tateY (A := A) T V hV).H ↔
      α.app (TateObject.X₀ T) (TateObject.basePoint T V hV) = TateObject.basePoint T V hV := by
  rw [tateY_H]
  exact EtaleTheta.TateObject.mem_piY_iff T V hV α

end Tate

end Frobenioid

end Iut
