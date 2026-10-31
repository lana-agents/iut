/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.CuspResidue

/-!
# Cusp inertia and the tame character (MR14, [EtTh] Prop. 1.3, finite-level form)

[EtTh] Prop. 1.3 (`The Etale Theta Function ….txt`, l.1137–1270) says that the restriction of the
étale theta class to `Δ_Θ` is the natural isomorphism; through `I_x ≅ Δ_Θ` for the cusp `x`
([EtTh] l.2268–2282: the decomposition group `D_x` maps into `Π^Θ_X`, the inertia group `I_x`
isomorphically onto `Δ_Θ`) and the cusps of `Ÿ` being the zeros of `Θ̈`, each of multiplicity `1`
([EtTh] Prop. 1.4(i), l.1322–1324), its finite-level form is: **the restriction of `κ_n(η)` to the
inertia group of every cusp of the level is the tame character mod `n`**, for a unit `η` whose order
at that cusp is `≡ 1 mod n`.

This file is the étale (Galois-theoretic) half of that reduction, for any `pi1` Galois datum `D`:

* `evalTriv_kummerMap_eq_tame`: if `v·π^{-m}` is a unit at the place `W ⊇ k` and `m ≡ 1 mod n`,
  then on `I_W ∩ H` the class `κ_n(v)` agrees with the Kummer character `σ ↦ σ(π^{1/n})/π^{1/n}`
  of `π` (continuous-kummer-theory `evalTriv_kummerMap`);
* `evalTriv_tame_eq_of_unit`: that character does not depend on the uniformiser.

The order computation for the theta level functions is `ThetaCuspOrder.lean`.
-/

universe u

open AffOrbicurve

namespace Iut.EtaleTheta

open KummerTheory KummerTheory.Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
  {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (n : ℕ) [NeZero n]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] [NeZero n] in
theorem mu_zpow_eq_self {x : Mu n Ω} {m : ℤ} (hm : (n : ℤ) ∣ m - 1) : x ^ m = x := by
  obtain ⟨c, hc⟩ := hm
  have hx : x ^ n = 1 := by
    let y : rootsOfUnity n Ω := x
    change y ^ n = 1
    exact Subtype.ext (by simpa using (mem_rootsOfUnity n (y : Ωˣ)).mp y.2)
  rw [show m = 1 + n * c by omega, zpow_add, zpow_one, zpow_mul, zpow_natCast, hx, one_zpow,
    mul_one]

include hk hσ in
/-- **Cusp inertia sees the tame character.** If `v·π^{-m}` is a unit at the place `W ⊇ k` and
`m ≡ 1 mod n`, then `κ_n(v)` evaluated at `σ ∈ I_W ∩ H` is the Kummer character of `π` at `σ`; for a
uniformiser `π` of `W ∩ F` this is the tame character of the cusp `W` mod `n`
(continuous-kummer-theory `exists_inertia_tameChar`: it maps `I_W ∩ H` onto `μ_n`). -/
theorem evalTriv_kummerMap_eq_tame (v : units D) (π : (F D)ˣ) (m : ℤ)
    (hv : ((((v : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : (((((v : (F D)ˣ) * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W)
    (hm : (n : ℤ) ∣ m - 1) :
    ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n) (kummerMap D n v) =
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) := by
  rw [evalTriv_kummerMap hk hσ n v π m hv hv', mu_zpow_eq_self n hm]

include hk hσ in
/-- **The tame character does not depend on the uniformiser**: if `π'·π⁻¹` is a unit at `W`, the
Kummer characters of `π` and `π'` agree on `I_W ∩ H`. -/
theorem evalTriv_tame_eq_of_unit (π π' : (F D)ˣ)
    (h : (((π' * π⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W)
    (h' : ((((π' * π⁻¹)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π')) =
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) := by
  have e := evalTriv_res_kummer_eq_zpow hk hσ n π' π 1 (by simpa using h) (by simpa using h')
  rwa [zpow_one] at e

end Iut.EtaleTheta
