/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTemperedPoint
import ContinuousKummerTheory.Curve.InertiaZHat

/-!
# The tempered étale theta class on cusp inertia (MR14, run 12)

[EtTh] Prop. 1.4(i) (ET l.1322–1323): the zeroes of `Θ̈` on `Ÿ` are the cusps, each of
multiplicity `1`; so the Kummer class of `Θ̈` restricted to the inertia group of a cusp is the
Kummer character of a uniformiser, i.e. the tame character (ET l.2272–2282: `I_x ↪ D_x` maps
isomorphically onto `Δ_Θ`). `ThetaCuspTame.lean` proves the étale form (`CuspTameAt`, part of
`exists_etaleThetaSystem`). This file transfers it to `Π^tp_Ÿ`.

In `tempered-fundamental-groups` (`Tempered/CuspInertia.lean`) the inertia group of a place `W`
is `inertiaGroup R W` (`σ(W) = W`, trivial on the residue field), and for a base point `V ≤ W`
it maps to `Π^tp` by `inertiaToTempered` (Galois elements of `D_V`).

* `inertiaLevel`: an inertia element over `X` fixing `L j` as an inertia element of the level.
* `inertiaToTempered_mem_piYddotX`: inertia elements fixing `L 0` lie in `Π^tp_Ÿ`;
  `toLevel_inertiaToTempered`: under C1 they map to the inertia elements of the level.
* **`classAt_inertia`**: `classAt η j n` evaluated at such an element is the étale class
  `κ_n(η_j)` evaluated at the inertia element of `H_j` (`evalTriv_kummerMapTempered_inertia`).
* **`classAt_cuspTame`**: from `CuspTameAt`, the value is the Kummer character of one uniformiser
  `π` of `W ∩ F_j` (`ClassAtCusp`, a `Prop` def used only as a conclusion).
* `ClassAtCusp.exists_inertiaZHatEquiv`: the same value is the `n`-th component of
  `inertiaZHatEquiv : I_W ∩ H_j ≃ₜ* Ẑ(1)` (continuous-kummer-theory, [AbsTopIII] Prop. 1.4(i)).
* Concrete: **`exists_thetaClassTemp_cusps`** — for the system of `exists_thetaClassTemp`, at
  every place `W ⊇ K` with `τ ∉ W` (over the cusp of `X`), for every base point `V ≤ W` over `O`
  (such `V` exist), under C1 and for `n ∣ N_j`, `ClassAtCusp` holds.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

section Cusp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V W : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

variable (hL) in
/-- An inertia element of `W` over `X` fixing the level `L j`, as an inertia element of the
level. -/
def inertiaLevel (j : ℕ) (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    inertiaGroup (fieldData ht (L j) (hL j)).R W :=
  ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv) fun r =>
      hσ _ ((fieldData_L ht (L j) (hL j)).le (CoordRing.algebraMap_mem r)),
    fun a ha => (mem_inertiaGroup.1 σ.2).1 a ha, fun a ha => (mem_inertiaGroup.1 σ.2).2 a ha⟩

omit [CharZero k] [IsSepClosed Ω] hX het in
@[simp]
theorem inertiaLevel_apply (j : ℕ) (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) (x : Ω) :
    ((inertiaLevel hL j σ hσ : inertiaGroup (fieldData ht (L j) (hL j)).R W) :
      Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω) x = (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x := rfl

omit [CharZero k] [IsSepClosed Ω] het in
variable (V hV T hL) in
/-- **Inertia elements fixing `Ÿ'_2` lie in `Π^tp_Ÿ`** (base point `V ≤ W`). -/
theorem inertiaToTempered_mem_piYddotX (hVW : V ≤ W) (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    inertiaToTempered O (fieldData ht LX hLX).A hV hVW σ ∈ piYddotX V hV T hL :=
  galoisToTempered_mem_piYddotX V hV T hL _ hσ0

omit [IsSepClosed Ω] in
/-- Under C1, the inertia element of `σ` in `Π^tp_Ÿ` maps to the inertia element of the level. -/
theorem toLevel_inertiaToTempered (hC1 : LevelsDominated V hV T hL) (j : ℕ) (hVW : V ≤ W)
    (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
    (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    toLevel hC1 j ⟨_, inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0⟩ =
      inertiaToTempered O _ hV hVW (inertiaLevel hL j σ hσj) :=
  toLevel_galoisToTempered hC1 j _ hσ0 hσj

omit [IsSepClosed Ω] het in
/-- The inertia elements in `Π^tp_Ÿ` act trivially on `μ_n` (`W ⊇ k`). -/
theorem inertiaToTempered_piYddotX_smul (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W)
    (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) (n : ℕ) [NeZero n]
    (ζ : Mu n Ω) :
    (⟨_, inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0⟩ : piYddotX V hV T hL) • ζ = ζ :=
  inertiaToTempered_smul_mu (fieldData ht LX hLX) O hV hVW hk σ n ζ

variable (η : ∀ j, units (fieldData ht (L j) (hL j)))

/-- **The tempered theta class on cusp inertia, at the level `j`**: `classAt η j n` evaluated at
the inertia element of `σ ∈ I_W` (fixing `L 0` and `L j`) in `Π^tp_Ÿ` is the étale Kummer class
`κ_n(η_j)` evaluated at `σ ∈ I_W ∩ H_j`. -/
theorem classAt_inertia (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W)
    (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
    (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    ContH1.evalTriv ⟨_, inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0⟩
        (inertiaToTempered_piYddotX_smul hk hVW σ hσ0 n) (classAt η hC1 j n) =
      ContH1.evalTriv ((galoisToH ((inertiaLevel hL j σ hσj :
          inertiaGroup (fieldData ht (L j) (hL j)).R W) :
            Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω) : (fieldData ht (L j) (hL j)).H) :
          Pi (fieldData ht (L j) (hL j)))
        (galoisToH_inertia_smul_mu hk _ n) (kummerMap (fieldData ht (L j) (hL j)) n (η j)) := by
  obtain ⟨c, hc⟩ := ContH1.mk_surjective
    (kummerMapTempered (fieldData ht (L j) (hL j)) O V hV n (η j))
  have h := evalTriv_kummerMapTempered_inertia (fieldData ht (L j) (hL j)) O hV hVW hk
    (inertiaLevel hL j σ hσj) n (η j)
  rw [← hc, ContH1.evalTriv_mk] at h
  rw [← h, classAt, resLevel, ← hc, ContH1.map_mk, ContH1.evalTriv_mk,
    ContH1.cocyclesMap_apply, MonoidHom.id_apply, toLevel_inertiaToTempered hC1 j hVW σ hσ0 hσj]

variable (V hV T hL) in
/-- **The tempered theta class at a cusp** (a `Prop` def used only as a conclusion, like
`ClassAtPoint`): there is a uniformiser `π` of `W ∩ F_j` such that for every `σ ∈ I_W` fixing
`L 0` and `L j`, `classAt η j n` at the inertia element of `σ` in `Π^tp_Ÿ` is the Kummer
character `σ ↦ σ(π^{1/n})/π^{1/n}` of `π` at `σ` (the tame character of `W` mod `n`). -/
def ClassAtCusp (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W) : Prop :=
  ∃ π : (F (fieldData ht (L j) (hL j)))ˣ,
    W.valuation ((π : F (fieldData ht (L j) (hL j))) : Ω) < 1 ∧
    (∀ f ∈ F (fieldData ht (L j) (hL j)), W.valuation f < 1 →
      W.valuation f ≤ W.valuation ((π : F (fieldData ht (L j) (hL j))) : Ω)) ∧
    ∀ (σ : inertiaGroup (fieldData ht LX hLX).R W)
      (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
      (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
      ContH1.evalTriv ⟨_, inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0⟩
          (inertiaToTempered_piYddotX_smul hk hVW σ hσ0 n) (classAt η hC1 j n) =
        ContH1.evalTriv (galoisToH ((inertiaLevel hL j σ hσj :
            inertiaGroup (fieldData ht (L j) (hL j)).R W) :
              Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω) : (fieldData ht (L j) (hL j)).H)
          (inertia_smul_mu hk (galoisToH_mem_inertia_iff (D := (fieldData ht (L j) (hL j))).2
            (mem_inertiaGroup.1 (inertiaLevel hL j σ hσj).2).1) n)
          (resMu (fieldData ht (L j) (hL j)) n (kummer n (F (fieldData ht (L j) (hL j))) Ω π))

/-- **`CuspTameAt` on `Π^tp_Ÿ`** (tempered [EtTh] Prop. 1.4(i) at the cusp, under C1): the
étale statement `CuspTameAt` at the level `j` gives `ClassAtCusp`. -/
theorem classAt_cuspTame (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hVW : V ≤ W)
    (hcusp : CuspTameAt (fieldData ht (L j) (hL j)) (η j) W hk n) :
    ClassAtCusp V hV T hL η hC1 j n hk hVW := by
  obtain ⟨π, hπ1, hπ2, hπ⟩ := hcusp
  exact ⟨π, hπ1, hπ2, fun σ hσ0 hσj => (classAt_inertia η hC1 j n hk hVW σ hσ0 hσj).trans
    (hπ _ (galoisToH_mem_inertia_iff.2 (mem_inertiaGroup.1 (inertiaLevel hL j σ hσj).2).1))⟩

omit [CharZero k] [IsSepClosed Ω] hX het in
/-- The inertia element of the level lies in `I_W ∩ H_j`. -/
theorem galoisToH_inertiaLevel_mem (j : ℕ) (σ : inertiaGroup (fieldData ht LX hLX).R W)
    (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    galoisToH ((inertiaLevel hL j σ hσj : inertiaGroup (fieldData ht (L j) (hL j)).R W) :
      Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω) ∈ inertiaH (fieldData ht (L j) (hL j)) W :=
  (mem_inertiaGroup.1 (inertiaLevel hL j σ hσj).2).1

/-- **`ClassAtCusp` through `I_W ∩ H_j ≅ Ẑ(1)`** ([EtTh] ET l.2272–2282, `I_x ≅ Δ_Θ`, compared
with the tame character): the value of `classAt η j n` at the inertia element of `σ` is the
`n`-th component of the image of `σ` under continuous-kummer-theory's
`inertiaZHatEquiv : I_W ∩ H_j ≃ₜ* Ẑ(1)` (the tame character of the uniformiser `π`). -/
theorem ClassAtCusp.exists_inertiaZHatEquiv {hC1 : LevelsDominated V hV T hL} {j n : ℕ}
    [NeZero n] {hk : ∀ c : k, algebraMap k Ω c ∈ W} {hVW : V ≤ W}
    (h : ClassAtCusp V hV T hL η hC1 j n hk hVW) :
    ∃ (π : (F (fieldData ht (L j) (hL j)))ˣ)
      (hπW : W.valuation ((π : F (fieldData ht (L j) (hL j))) : Ω) < 1)
      (hπ : ∀ f ∈ F (fieldData ht (L j) (hL j)), W.valuation f < 1 →
        W.valuation f ≤ W.valuation ((π : F (fieldData ht (L j) (hL j))) : Ω)),
      ∀ (σ : inertiaGroup (fieldData ht LX hLX).R W)
        (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
        (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
        ContH1.evalTriv ⟨_, inertiaToTempered_mem_piYddotX V hV T hL hVW σ hσ0⟩
            (inertiaToTempered_piYddotX_smul hk hVW σ hσ0 n) (classAt η hC1 j n) =
          ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ :
              KummerIndex (F (fieldData ht (L j) (hL j))))
            (inertiaZHatEquiv hk hπW hπ ⟨_, galoisToH_inertiaLevel_mem j σ hσj⟩) := by
  obtain ⟨π, hπW, hπ, H⟩ := h
  refine ⟨π, hπW, hπ, fun σ hσ0 hσj => ?_⟩
  rw [H σ hσ0 hσj, inertiaZHatEquiv_apply, proj_tameChar]

end Cusp

/-! ### The concrete system: the class at the cusp -/

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

section Main

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

set_option maxHeartbeats 2000000 in
-- destructuring `exists_etaleThetaSystem` (concrete Tate-curve levels) is slow to unify
include h2 in
/-- **The tempered étale theta class at the cusp** ([EtTh] Prop. 1.4(i), ET l.1322–1323, and
ET l.2272–2282, tempered form, under C1): for the system of `exists_thetaClassTemp`, at every
place `W ⊇ K` of `Ω` with `τ ∉ W` (a place over the cusp of `X = E_q ∖ {O}`) there are base
points `V ≤ W` over `O`, and for each of them, under C1 and for every `n ∣ N_j`, the class
`classAt η j n` (`= thetaClassTemp η n` by `ThetaClassCompatible`) on the inertia elements of
`W` in `Π^tp_Ÿ` is the Kummer character of a uniformiser of `W` (`ClassAtCusp`). Also: the
level `L 0` lies in the source `L_2` of `[2]` (used for `InertiaFixesLevel`, `ThetaProp13.lean`). -/
theorem exists_thetaClassTemp_cusps :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      (∀ (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W), τ ∉ W →
        (∃ V : ValuationSubring Ω, V ≤ W ∧ V.comap (algebraMap K Ω) = O) ∧
        ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (hVW : V ≤ W)
          (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (j n : ℕ) [NeZero n],
          n ∣ 2 * (j + 1) →
          ClassAtCusp V hV (tateDataX O hO hs h12) hL η hC1 j n hk hVW) ∧
      L 0 ≤ mulByNField t.tateCurve 2 := by
  obtain ⟨L, hL, h₁, η, het, -, -, -, htr, hcusp, -, hL02, -⟩ := exists_etaleThetaSystem h2 h12 hs
  haveI hX : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j) := fun j => ⟨h₁ j⟩
  haveI het' : ∀ j, Algebra.Etale (DX t).R
      (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R := fun j =>
    etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) (L j) (hL j) (het j)
  refine ⟨L, hL, hX, het', η, htr, fun V hV => thetaClassCompatible_tate h12 hs O hO V hV htr,
    fun W hk hτ => ⟨exists_le_comap_eq W hk O, fun V hV hVW hC1 j n _ hn => ?_⟩, hL02⟩
  exact classAt_cuspTame η hC1 j n hk hVW (hcusp j W hk hτ n hn)

end Main

end Iut.EtaleTheta
