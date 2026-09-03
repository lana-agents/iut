/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Points of Weierstrass curves along ring homomorphisms

`Iut.Anabelian.pointMap E f : E(k) →+ (E.map f)(K)` for a ring homomorphism of fields
`f : k →+* K` (Mathlib's `WeierstrassCurve.Affine.Point.map` for the base change `E.map f`),
with its basic properties.
-/

namespace Iut.Anabelian

open WeierstrassCurve
open scoped Classical

/-! ## Points of Weierstrass curves along ring homomorphisms -/

section PointMap

variable {k K L : Type*} [Field k] [Field K] [Field L]

/-- The group homomorphism on points induced by a ring homomorphism of fields
(`WeierstrassCurve.Affine.Point.map` for the base change `E.map f`). -/
noncomputable def pointMap (E : WeierstrassCurve k) (f : k →+* K) :
    E.toAffine.Point →+ (E.map f).toAffine.Point :=
  letI := f.toAlgebra
  Affine.Point.map (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

variable (E : WeierstrassCurve k) (f : k →+* K)

@[simp] lemma pointMap_zero : pointMap E f 0 = 0 := rfl

lemma pointMap_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    pointMap E f (Affine.Point.some x y h) =
      Affine.Point.some (f x) (f y) ((E.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

lemma pointMap_injective : Function.Injective (pointMap E f) := by
  letI := f.toAlgebra
  exact Affine.Point.map_injective (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

lemma pointMap_map (g : K →+* L) (P : E.toAffine.Point) :
    pointMap (E.map f) g (pointMap E f P) = pointMap E (g.comp f) P := by
  cases P <;> rfl

lemma pointMap_id (P : E.toAffine.Point) : pointMap E (RingHom.id k) P = P := by
  cases P <;> rfl

end PointMap


end Iut.Anabelian
