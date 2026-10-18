/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.PrimeStrip
import Iut.Frobenioid.GlobalRho
import Iut.Frobenioid.GlobalPrimeZ

/-!
# The global part of `F^⊩_mod` (IUT I, Example 3.5(i), (ii))

IUT I, Example 3.5(ii) (l.5654–5665): "`F⊩_mod def= (C⊩_mod, Prime(C⊩_mod) ∼→ V, {F⊢_v}v∈V,
{ρv}v∈V)`". `HodgeTheater/PrimeStrip.lean`'s `FRlfStrip` (shell #8) records only a category
equivalent to `C^⊩_mod` and an unrelated `F^⊢`-prime-strip. This file constructs, from initial
Θ-data `D`, the global data of `F^⊩_mod` that do not involve the local Frobenioids `F^⊢_v`
(those are MR20):

* `FRlfMod.sectPlace D v ∈ V ⊆ V(K)`: the place of the section over `v ∈ V_mod`;
* **`FRlfGlobal D`**: `C^⊩_mod` (with its identity equivalence to `rlfModel D`), the bijection
  `Prime(C^⊩_mod) ≅ V` (`GlobalRealified.primeEquiv`, `V ≅ V_mod` by the section), and the maps
  `ρ_v : Φ_{C^⊩_mod,v} → ℝ_{≥0}` (`GlobalRealified.rho`) — data only, no Prop fields;
* **`FRlfMod.rho_logMod`**: `ρ_v(log⊢_mod(p_v)) = logΦ(p_v)/[K_v : (F_mod)_v]` for every `v ∈ V_mod`
  (IUT I, Example 3.5(i));
* **`FRlfMod.degArith_eq_vol_rho`**: `deg^arith_{F_mod}(z) = vol_{K_v}(ρ_v z)` for `z ∈ Φ_v` (the
  "volume interpretation");
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace HodgeTheater

open NumberField Frobenioid Frobenioid.GlobalRealified

universe u

variable (D : InitialThetaData.{u})

namespace FRlfMod

/-- The place `v̲ ∈ V ⊆ V(K)` lying over `v ∈ V_mod` (IUT I, Definition 3.1(e)). -/
noncomputable def sectPlace : Vp D → GlobalRealified.Place D.Kt
  | Sum.inl v => Sum.inl (D.V.sectFin v)
  | Sum.inr v => Sum.inr (D.V.sectInf v)

/-- `ρ_v` of `F^⊩_mod`: `Φ_{C^⊩_mod} → ℝ` (`ρ_v` on `Φ_v`). -/
noncomputable def rhoMod (v : Vp D) : ArithDiv ↥(fieldOfModuli D.F D.E) → ℝ :=
  GlobalRealified.rho (sectPlace D v) v

end FRlfMod

/-- **The global data of `F^⊩_mod`** (IUT I, Example 3.5(ii)): the Frobenioid `C^⊩_mod`, an
equivalence with the model, the bijection `Prime(C^⊩_mod) ≅ V` and the maps `ρ_v`. -/
structure FRlfGlobal where
  /-- The global realified Frobenioid. -/
  C : CategoryTheory.Cat.{u, u}
  /-- Its identification with `C^⊩_mod`. -/
  equiv : C ≌ rlfModel D
  /-- `Prime(C^⊩_mod) ≅ V` (`V ≅ V_mod`). -/
  prime : GlobalRealified.Prime ↥(fieldOfModuli D.F D.E) ≃ Vp D
  /-- The local-global maps `ρ_v : Φ_{C^⊩_mod,v} → ℝ_{≥0}`. -/
  rho : Vp D → ArithDiv ↥(fieldOfModuli D.F D.E) → ℝ

/-- **`F^⊩_mod`** (global part), constructed from the Θ-data. -/
noncomputable def FRlfGlobal.ofThetaData : FRlfGlobal D where
  C := rlfModel D
  equiv := CategoryTheory.Equivalence.refl
  prime := GlobalRealified.primeEquiv
  rho := FRlfMod.rhoMod D

namespace FRlfMod

/-- **`ρ_v(log⊢_mod(p_v)) = logΦ(p_v)/[K_v : (F_mod)_v]`** (IUT I, Example 3.5(i)), for every
`v ∈ V_mod`. -/
theorem rho_logMod (v : Vp D) :
    (FRlfGlobal.ofThetaData D).rho v (GlobalRealified.logMod v) =
      GlobalRealified.logPhi (K := D.Kt) v (sectPlace D v) /
        GlobalRealified.localDeg (sectPlace D v) v := by
  rcases v with v | v
  · exact GlobalRealified.rho_logMod_fin (D.V.sectFin_liesOver v)
  · exact GlobalRealified.rho_logMod_inf

/-- **The volume interpretation** (IUT I, Example 3.5(i)): `deg^arith_{F_mod}(z) = vol_{K_v}(ρ_v z)`
for `z ∈ Φ_{C^⊩_mod,v}`. -/
theorem degArith_eq_vol_rho (v : Vp D) {z : ArithDiv ↥(fieldOfModuli D.F D.E)}
    (hz : z ∈ GlobalRealified.phiAt v) :
    degArith _ z = GlobalRealified.vol (sectPlace D v) ((FRlfGlobal.ofThetaData D).rho v z) := by
  rcases v with v | v
  · exact GlobalRealified.degArith_eq_vol_rho_fin (D.V.sectFin_liesOver v) hz
  · exact GlobalRealified.degArith_eq_vol_rho_inf hz

/-- `ρ_v` is additive and nonnegative on `Φ_v`. -/
lemma rho_add (v : Vp D) (a b : ArithDiv ↥(fieldOfModuli D.F D.E)) :
    (FRlfGlobal.ofThetaData D).rho v (a + b) =
      (FRlfGlobal.ofThetaData D).rho v a + (FRlfGlobal.ofThetaData D).rho v b :=
  GlobalRealified.rho_add _ _ a b

lemma rho_nonneg (v : Vp D) {z : ArithDiv ↥(fieldOfModuli D.F D.E)} (hz : z ∈ effCone _) :
    0 ≤ (FRlfGlobal.ofThetaData D).rho v z :=
  GlobalRealified.rho_nonneg _ _ hz

end FRlfMod

end HodgeTheater

end Iut
