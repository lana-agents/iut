/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.Genuine.Homs
import Pi1.Orbicurve.Pullback

/-!
# Cores of the model orbicurves

Over a field `k` of characteristic `0`, the model orbicurve `X = (E, ℓ, M, ±)` is the affine
orbicurve `realize E ℓ M ±` (`Iut.Anabelian.Genuine.Realize`), and `C` is **the `k`-core** of `X`
(`genuineHasCore X C`) if `realize C` is the `k`-core of `realize X` in the sense of [CanLift], §2
(`AffOrbicurve.IsCoreOf`: a terminal object of `\overline{Loc}_k(realize X)`).

A cover `X → Y` of model orbicurves is realized by a finite étale morphism of affine orbicurves
(`realizeHomFF`, `realizeHomFT`, `realizeHomTT`) along an inclusion of function fields, and every
finite étale cover of `realize Y` is dominated by one of `realize X`
(`AffOrbicurve.pullback_ofSubfield`); hence `X` and `Y` have the same cores
(`isCoreOf_realize_iff`).
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve AffOrbicurve IntermediateField

noncomputable section

attribute [local instance 2000] Classical.propDecidable

section Cover

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

instance normal_K₀ : Normal (K₀ k (xG E)) (Ω E) := IsGalois.to_normal

set_option maxHeartbeats 1000000 in
/-- **A cover `(E, ℓ, M, ±) → (E, ℓ', M', ±')` does not change the cores.** -/
theorem isCoreOf_realize_iff {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) (C : AffOrbicurve k) :
    IsCoreOf (realize E ℓ M pm) C ↔ IsCoreOf (realize E ℓ' M' pm') C := by
  cases pm <;> cases pm'
  · exact isCoreOf_ofSubfield_iff (xG E) (transcendental_xG E) _
      (realizeHomFF E hn hℓ hM).etale C
  · exact isCoreOf_ofSubfield_iff (xG E) (transcendental_xG E) _
      (realizeHomFT E hn hℓ hM).etale C
  · exact absurd (hpm rfl) (by simp)
  · exact isCoreOf_ofSubfield_iff (xG E) (transcendental_xG E) _
      (realizeHomTT E hn hℓ hM).etale C

end Cover

end

end Iut.Anabelian.Genuine
