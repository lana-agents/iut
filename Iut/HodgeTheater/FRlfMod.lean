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
{ρv}v∈V)`". The global data of `F^⊩_mod` that do not involve the local Frobenioids `F^⊢_v` (those
are MR20) are defined in `HodgeTheater/PrimeStrip.lean`, where `FRlfStrip` carries them:

* `FRlfMod.sectPlace D v ∈ V ⊆ V(K)`: the place of the section over `v ∈ V_mod`;
* **`FRlfGlobal D`**: `C^⊩_mod` (with its identity equivalence to `rlfModel D`), the bijection
  `Prime(C^⊩_mod) ≅ V` (`GlobalRealified.primeEquiv`, `V ≅ V_mod` by the section), and the maps
  `ρ_v : Φ_{C^⊩_mod,v} → ℝ_{≥0}` (`GlobalRealified.rho`) — data only, no Prop fields;

This file proves their properties:

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
