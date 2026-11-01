/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.ThetaSystem
import Iut.EtaleTheta.Env.Tower

/-!
# The projective system of theta environments ([EtTh], Cor. 2.19(ii), Layer B)

The tower data of `Env/Tower.lean` for the genuine theta setting of `Env/ThetaSystem.lean`:
levels `N_n = (n+1)!` (cofinal for divisibility), cyclotomes `μ_{N_n}(Ω)` with the cyclotomic
characters `psiMu`, reductions `Mu.transition : μ_{N_{n+1}} ↠ μ_{N_n}` (`ζ ↦ ζ^{N_{n+1}/N_n}`).
Discharged here (Layer-B obligation 10):

* `hred` (`transition_psiMu`), `hs` (`transition_surjective`), `hker` (`ker_transition`: the
  kernel is the `N_n`-th powers) — roots of unity in an algebraically closed field;
* `hKumRed` (`contCocycles_eq_map`): every continuous cocycle `G_k → μ_N` lifts to `μ_{N'}`, by
  Kummer theory (`kummer_surjective`, `h1Transition_kummer`) and lifting of coboundaries
  (`exists_lift_cocycle`);
* `hηred` (`compatRep`): representative cocycles of a compatible system of classes
  (`thetaClassTemp η N_n`, `transTemp_thetaClassTemp`) can be chosen compatibly.

Main result: `discreteRigidity_thetaEnv` ([EtTh], Cor. 2.19(ii)) for the projective system of
model environments of the étale theta classes, and its concrete form for the Tate curve. The
remaining hypotheses are `hPY` (`FISlim Π^tp_Y`), `hfin` (`[Π^tp_Y : Π^tp_Ÿ] < ∞`) and `hlift`
(the surjectivity half of Cor. 2.18(iv)).
-/

open scoped commutatorElement

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta.Env

/-! ### Roots of unity in an algebraically closed field -/

section Roots

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- `μ_n ↠ μ_m`, `ζ ↦ ζ^{n/m}`, is surjective (`m ∣ n`, `n ≠ 0`). -/
theorem transition_surjective {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) :
    Function.Surjective (Mu.transition (Ω := F) h) := by
  intro ζ
  have hd : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h)
    (Nat.pos_of_ne_zero fun hm => hn (by simpa [hm] using h))
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((Mu.val ζ : Fˣ) : F) hd
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hα
    exact (Mu.val ζ).ne_zero hα.symm
  have hu : Units.mk0 α hα0 ^ (n / m) = Mu.val ζ := Units.ext (by simpa using hα)
  have hpow : Units.mk0 α hα0 ^ n = 1 := by
    rw [← Nat.div_mul_cancel h, pow_mul, hu, Mu.val_pow_n]
  exact ⟨Mu.mk _ hpow, Mu.ext (by rw [Mu.val_transition, Mu.val_mk, hu])⟩

/-- The kernel of `μ_n ↠ μ_m` is the group of `m`-th powers (`m ∣ n`, `m ≠ 0`). -/
theorem ker_transition {m n : ℕ} (h : m ∣ n) (hm : m ≠ 0) :
    (Mu.transition (Ω := F) h).ker = (powMonoidHom m : Mu n F →* Mu n F).range := by
  ext ζ
  rw [MonoidHom.mem_ker]
  constructor
  · intro hζ
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq ((Mu.val ζ : Fˣ) : F)
      (Nat.pos_of_ne_zero hm)
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow hm] at hβ
      exact (Mu.val ζ).ne_zero hβ.symm
    have hu : Units.mk0 β hβ0 ^ m = Mu.val ζ := Units.ext (by simpa using hβ)
    have h1 : Mu.val ζ ^ (n / m) = 1 := by
      have := congrArg Mu.val hζ
      simpa using this
    have hpow : Units.mk0 β hβ0 ^ n = 1 := by
      rw [← Nat.mul_div_cancel' h, pow_mul, hu, h1]
    exact ⟨Mu.mk _ hpow, Mu.ext (by simp [powMonoidHom_apply, Mu.val_mk, hu])⟩
  · rintro ⟨β, rfl⟩
    apply Mu.ext
    rw [powMonoidHom_apply, Mu.val_transition, map_pow, ← pow_mul, Nat.mul_div_cancel' h,
      Mu.val_pow_n, map_one]

end Roots

/-! ### Lifting cocycles along a surjection of coefficients -/

section Lift

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M] [CommGroup N] [TopologicalSpace N]
  [IsTopologicalGroup N] [MulDistribMulAction G N]

/-- **Lifting a cocycle along a surjection of coefficients within its class**: if `f : M ↠ N`
maps the class of `c` to the class of `d`, then some cocycle `c'` cohomologous to `c` maps to
`d` on the nose. -/
theorem exists_lift_cocycle (f : M →* N) (hf : Continuous f) (hfs : Function.Surjective f)
    (hcomp : ∀ g m, f (g • m) = g • f m) (hcont : ∀ y : M, Continuous fun g : G => g • y)
    (c : ContH1.cocycles G M) (d : ContH1.cocycles G N)
    (h : ContH1.mk (ContH1.cocyclesMap (MonoidHom.id G) continuous_id f hf
      (fun g m => hcomp g m) c) = ContH1.mk d) :
    ∃ c' : ContH1.cocycles G M, ContH1.mk c' = ContH1.mk c ∧ ∀ g, f (c' g) = d g := by
  rw [ContH1.mk_eq_mk_iff] at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, rfl⟩ := hfs x
  let b : ContH1.cocycles G M := ContH1.mkCocycle (fun g => g • y / y)
    ((hcont y).div' continuous_const) fun g g' => by
      have key : ∀ a b : M, g • (a / b) = g • a / g • b := by
        intro a b
        rw [div_eq_mul_inv, div_eq_mul_inv, smul_mul', smul_inv']
      dsimp only
      rw [key, mul_smul]
      simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
  refine ⟨c / b, ?_, fun g => ?_⟩
  · rw [_root_.map_div, div_eq_self, ContH1.mk_eq_one_iff]
    exact ⟨y, fun g => rfl⟩
  · have := hx g
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply] at this
    change f (c g / (g • y / y)) = d g
    rw [_root_.map_div, _root_.map_div, hcomp, this, div_div_cancel]

end Lift

/-! ### The levels and the reductions -/

section Levels

/-- **The levels** `N_n = (n+1)!` (cofinal for divisibility). -/
def levelN (n : ℕ) : ℕ := (n + 1).factorial

instance (n : ℕ) : NeZero (levelN n) := ⟨Nat.factorial_ne_zero _⟩

theorem levelN_dvd (n : ℕ) : levelN n ∣ levelN (n + 1) :=
  Nat.factorial_dvd_factorial (by omega)

/-- Every `m ≥ 1` divides a level. -/
theorem dvd_levelN {m : ℕ} (hm : 0 < m) : m ∣ levelN (m - 1) := by
  rw [levelN, Nat.sub_add_cancel hm]
  exact Nat.dvd_factorial hm le_rfl

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

theorem transition_psiMu {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (σ : Gk k Ω)
    (ζ : Mu n Ω) : Mu.transition h (psiMu n σ ζ) = psiMu m σ (Mu.transition h ζ) := by
  obtain ⟨ζ', rfl⟩ := (muEquiv (k := k) (Ω := Ω) n).surjective ζ
  have e : ∀ z : Mu n (kbar k Ω), Mu.transition h (muEquiv (k := k) (Ω := Ω) n z) =
      muEquiv m (Mu.transition h z) := fun z => (muMap_transition h z).symm
  rw [psiMu_muEquiv, e, e, Mu.transition_smul, psiMu_muEquiv]

theorem continuous_psiMu_apply (n : ℕ) [NeZero n] (y : Mu n Ω) :
    Continuous fun σ : Gk k Ω => psiMu n σ y := by
  refine continuous_iff_continuousAt.2 fun σ => ?_
  have hU := isOpen_ker_psiMu (k := k) (Ω := Ω) n
  have hmem : (fun τ : Gk k Ω => σ⁻¹ * τ) ⁻¹'
      (((psiMu (k := k) (Ω := Ω) n).ker : Subgroup (Gk k Ω)) : Set (Gk k Ω)) ∈ nhds σ := by
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds (one_mem _)
  have hev : ∀ᶠ τ in nhds σ, psiMu n σ y = psiMu n τ y := by
    filter_upwards [hmem] with τ hτ
    have h1 : psiMu (k := k) (Ω := Ω) n (σ⁻¹ * τ) = 1 := hτ
    have h2 : τ = σ * (σ⁻¹ * τ) := by group
    rw [h2, map_mul, MulAut.mul_apply, h1, MulAut.one_apply]
  exact continuousAt_const.congr hev

end Levels

/-! ### Kummer cocycles lift along the reductions -/

section Kummer

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]

omit [CharZero k] [IsAlgClosed Ω] in
theorem muEquiv_symm_psiMu (n : ℕ) [NeZero n] (σ : Gk k Ω) (z : Mu n Ω) :
    (muEquiv (k := k) (Ω := Ω) n).symm (psiMu n σ z) = σ • (muEquiv n).symm z := by
  rw [psiMu_apply, MulEquiv.symm_apply_apply]

omit [CharZero k] [IsAlgClosed Ω] in
theorem continuous_smul_mu_kbar (n : ℕ) [NeZero n] (y : Mu n (kbar k Ω)) :
    Continuous fun σ : Gk k Ω => σ • y := by
  have : (fun σ : Gk k Ω => σ • y) =
      fun σ => (muEquiv (k := k) (Ω := Ω) n).symm (psiMu n σ (muEquiv n y)) := by
    funext σ
    rw [muEquiv_symm_psiMu, MulEquiv.symm_apply_apply]
  rw [this]
  exact (continuous_of_discreteTopology (f := ⇑(muEquiv (k := k) (Ω := Ω) n).symm)).comp
    (continuous_psiMu_apply n _)

omit [CharZero k] [IsAlgClosed Ω] in
/-- A continuous cocycle `G_k → μ_n(Ω)` (an element of `contCocycles (psiMu n)`), transported to
`μ_n(k̄)` along `muEquiv`: an element of ckt's `ContH1.cocycles (Gk k Ω) (Mu n (kbar k Ω))`. -/
def toKbarCocycle {n : ℕ} [NeZero n] (κ : Gk k Ω → Mu n Ω) (hκ : IsCocycle (psiMu n) κ)
    (hκc : Continuous κ) : ContH1.cocycles (Gk k Ω) (Mu n (kbar k Ω)) :=
  ContH1.mkCocycle (fun σ => (muEquiv (k := k) (Ω := Ω) n).symm (κ σ))
    ((continuous_of_discreteTopology (f := ⇑(muEquiv (k := k) (Ω := Ω) n).symm)).comp hκc)
    fun σ τ => by
      simp only [hκ σ τ, map_mul, muEquiv_symm_psiMu]
      exact mul_comm _ _

/-- **`contCocycles` are Kummer cocycles** (Kummer theory, ckt `kummer_surjective`, i.e.
`kummerEquiv : k^×/(k^×)^n ≃* H¹(G_k, μ_n)`): the class of every continuous cocycle
`G_k → μ_n(Ω)` (transported to `μ_n(k̄)`) is the Kummer class of some `a ∈ k^×`. -/
theorem exists_kummer_of_mem_contCocycles {n : ℕ} [NeZero n] {κ : Gk k Ω → Mu n Ω}
    (hκ : κ ∈ contCocycles (psiMu (k := k) (Ω := Ω) n)) :
    ∃ a : kˣ, ContH1.mk (toKbarCocycle κ hκ.1 hκ.2) = kummer n k (kbar k Ω) a := by
  haveI : NeZero ((n : ℕ) : k) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  obtain ⟨a, ha⟩ := kummer_surjective n k (kbar k Ω) (ContH1.mk (toKbarCocycle κ hκ.1 hκ.2))
  exact ⟨a, ha.symm⟩

/-- **Every Kummer class is represented in `contCocycles`** (the converse of
`exists_kummer_of_mem_contCocycles`): for `a ∈ k^×` some element of `contCocycles (psiMu n)`
represents `κ_n(a)`. -/
theorem exists_mem_contCocycles_kummer {n : ℕ} [NeZero n] (a : kˣ) :
    ∃ (κ : Gk k Ω → Mu n Ω) (hκ : κ ∈ contCocycles (psiMu (k := k) (Ω := Ω) n)),
      ContH1.mk (toKbarCocycle κ hκ.1 hκ.2) = kummer n k (kbar k Ω) a := by
  haveI : NeZero ((n : ℕ) : k) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  let c : ContH1.cocycles (Gk k Ω) (Mu n (kbar k Ω)) := Quotient.out (kummer n k (kbar k Ω) a)
  have h1 : IsCocycle (psiMu (k := k) (Ω := Ω) n) fun σ => muEquiv n (c σ) := fun σ τ => by
    simp only [ContH1.isMulCocycle₁ c σ τ, map_mul, ← psiMu_muEquiv]
    exact mul_comm _ _
  have h2 : Continuous fun σ => muEquiv (k := k) (Ω := Ω) n (c σ) :=
    (continuous_of_discreteTopology (f := ⇑(muEquiv (k := k) (Ω := Ω) n))).comp
      (ContH1.continuous c)
  refine ⟨fun σ => muEquiv n (c σ), ⟨h1, h2⟩, ?_⟩
  have e : toKbarCocycle (fun σ => muEquiv (k := k) (Ω := Ω) n (c σ)) h1 h2 = c :=
    Subtype.ext (funext fun σ => (muEquiv (k := k) (Ω := Ω) n).symm_apply_apply (c σ))
  rw [e]
  exact Quotient.out_eq _

/-- **Every continuous cocycle `G_k → μ_m` lifts to `μ_n`** (`m ∣ n`) on the nose: its class is a
Kummer class (`kummer_surjective`, Hilbert 90), Kummer classes are compatible with the
reductions (`h1Transition_kummer`), and a cohomologous lift is adjusted by a coboundary
(`exists_lift_cocycle`). -/
theorem exists_lift_psiMu_cocycle {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (κ : Gk k Ω → Mu m Ω) (hκ : IsCocycle (psiMu m) κ) (hκc : Continuous κ) :
    ∃ κ' : Gk k Ω → Mu n Ω, IsCocycle (psiMu n) κ' ∧ Continuous κ' ∧
      ∀ σ, Mu.transition h (κ' σ) = κ σ := by
  haveI : NeZero ((m : ℕ) : k) := ⟨Nat.cast_ne_zero.2 (NeZero.ne m)⟩
  haveI : NeZero ((n : ℕ) : k) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  let κt : ContH1.cocycles (Gk k Ω) (Mu m (kbar k Ω)) :=
    ContH1.mkCocycle (fun σ => (muEquiv (k := k) (Ω := Ω) m).symm (κ σ))
      ((continuous_of_discreteTopology (f := ⇑(muEquiv (k := k) (Ω := Ω) m).symm)).comp hκc)
      fun σ τ => by
        simp only [hκ σ τ, map_mul, muEquiv_symm_psiMu]
        exact mul_comm _ _
  obtain ⟨a, ha⟩ := kummer_surjective m k (kbar k Ω) (ContH1.mk κt)
  let c : ContH1.cocycles (Gk k Ω) (Mu n (kbar k Ω)) := Quotient.out (kummer n k (kbar k Ω) a)
  have hc : ContH1.mk (ContH1.cocyclesMap (MonoidHom.id (Gk k Ω)) continuous_id
      (Mu.transition h) continuous_of_discreteTopology
      (fun σ ζ => Mu.transition_smul h σ ζ) c) = ContH1.mk κt := by
    rw [← ha, ← h1Transition_kummer h a, ← Quotient.out_eq (kummer n k (kbar k Ω) a)]
    rfl
  obtain ⟨c', -, hc'⟩ := exists_lift_cocycle (Mu.transition h) continuous_of_discreteTopology
    (transition_surjective h (NeZero.ne n)) (fun σ ζ => Mu.transition_smul h σ ζ)
    (continuous_smul_mu_kbar n) c κt hc
  refine ⟨fun σ => muEquiv n (c' σ), fun σ τ => ?_,
    (continuous_of_discreteTopology (f := ⇑(muEquiv (k := k) (Ω := Ω) n))).comp
      (ContH1.continuous c'), fun σ => ?_⟩
  · simp only [ContH1.isMulCocycle₁ c' σ τ, map_mul, ← psiMu_muEquiv]
    exact mul_comm _ _
  · change Mu.transition h (muEquiv n (c' σ)) = κ σ
    rw [muEquiv_apply, ← muMap_transition, hc' σ]
    exact (muEquiv (k := k) (Ω := Ω) m).apply_symm_apply (κ σ)

/-- **`hKumRed` for the genuine tower**: the continuous cocycles `G_k → μ_m` are exactly the
reductions of the continuous cocycles `G_k → μ_n` (`m ∣ n`). -/
theorem contCocycles_eq_map {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    contCocycles (psiMu (k := k) (Ω := Ω) m) =
      (contCocycles (psiMu (k := k) (Ω := Ω) n)).map
        (MonoidHom.compLeft (Mu.transition h) (Gk k Ω)) := by
  ext κ
  constructor
  · intro hκ
    obtain ⟨κ', h1, h2, h3⟩ := exists_lift_psiMu_cocycle h κ hκ.1 hκ.2
    exact ⟨κ', ⟨h1, h2⟩, funext h3⟩
  · rintro ⟨κ', ⟨h1, h2⟩, rfl⟩
    refine ⟨fun σ τ => ?_, (continuous_of_discreteTopology
      (f := ⇑(Mu.transition (Ω := Ω) h))).comp h2⟩
    simp only [MonoidHom.compLeft_apply, Function.comp_apply, h1 σ τ, map_mul,
      transition_psiMu]

end Kummer

/-! ### Compatible representative cocycles and the tower of theta environments -/

section Compat

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]

local notation "DXg" => fieldData ht LX hLX
local notation "PXg" => TempPi (fieldData ht LX hLX) O V hV
local notation "augg" => augT (fieldData ht LX hLX) O V hV
set_option quotPrecheck false in
local notation "PYg" => Iut.EtaleTheta.TateObject.piY
  (A := (fieldData ht LX hLX).A) T V hV
local notation "PYddg" => piYddotX V hV T hL

theorem smul_piYddotX_eq (n : ℕ) [NeZero n] (γ : PYddg) (ζ : Mu n Ω) :
    γ • ζ = psiMu n (augg (γ : PXg)) ζ :=
  (act_augT_psiMu DXg O V hV n (γ : PXg) ζ).symm

theorem continuous_smul_piYddotX (n : ℕ) [NeZero n] (y : Mu n Ω) :
    Continuous fun γ : PYddg => γ • y := by
  have : (fun γ : PYddg => γ • y) = fun γ : PYddg => psiMu n (augg (γ : PXg)) y :=
    funext fun γ => smul_piYddotX_eq n γ y
  rw [this]
  exact (continuous_psiMu_apply n y).comp ((continuous_augT DXg O V hV).comp continuous_subtype_val)

theorem transition_smul_piYddotX {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (γ : PYddg)
    (ζ : Mu n Ω) : Mu.transition h (γ • ζ) = γ • Mu.transition h ζ := by
  rw [smul_piYddotX_eq, smul_piYddotX_eq, transition_psiMu]

theorem isCocycle_coe_cocycles (n : ℕ) [NeZero n] (c : ContH1.cocycles PYddg (Mu n Ω)) :
    IsCocycle (actDD augg (psiMu (k := k) (Ω := Ω) n) PYddg) c := by
  intro g g'
  rw [ContH1.isMulCocycle₁ c g g', mul_comm]
  exact congrArg _ (act_augT_psiMu DXg O V hV n (g : PXg) _).symm

variable (x : ∀ n, ContH1 (piYddotX V hV T hL) (Mu (levelN n) Ω))
  (hx : ∀ n, transTemp T hL (levelN_dvd n) (x (n + 1)) = x n)

include hx in
theorem exists_liftStep (n : ℕ)
    (c : {c : ContH1.cocycles PYddg (Mu (levelN n) Ω) // ContH1.mk c = x n}) :
    ∃ c' : ContH1.cocycles PYddg (Mu (levelN (n + 1)) Ω),
      ContH1.mk c' = x (n + 1) ∧ ∀ g, Mu.transition (levelN_dvd n) (c' g) = c.1 g := by
  obtain ⟨c', h1, h2⟩ := exists_lift_cocycle (G := PYddg) (M := Mu (levelN (n + 1)) Ω)
    (N := Mu (levelN n) Ω) (Mu.transition (levelN_dvd n))
    continuous_of_discreteTopology (transition_surjective (levelN_dvd n) (NeZero.ne _))
    (fun γ ζ => by
      change Mu.transition (levelN_dvd n) (tempToPi DXg O V hV (γ : PXg) • ζ) =
        tempToPi DXg O V hV (γ : PXg) • Mu.transition (levelN_dvd n) ζ
      induction tempToPi DXg O V hV (γ : PXg) using QuotientGroup.induction_on with
      | H g => exact Mu.transition_smul (K := K₀ k t) (levelN_dvd n) (g : Ω ≃ₐ[K₀ k t] Ω) ζ)
    (fun y => by
      change Continuous fun γ : PYddg => tempToPi DXg O V hV (γ : PXg) • y
      have e : (fun γ : PYddg => tempToPi DXg O V hV (γ : PXg) • y) =
          fun γ : PYddg => psiMu (levelN (n + 1)) (piToGk DXg (tempToPi DXg O V hV (γ : PXg))) y :=
        funext fun γ => (psiMu_piToGk DXg (levelN (n + 1)) _ y).symm
      rw [e]
      exact (continuous_psiMu_apply _ y).comp ((continuous_piToGk DXg).comp
        ((continuous_tempToPi DXg O V hV).comp continuous_subtype_val)))
    (Quotient.out (x (n + 1))) c.1
    (((congrArg (transTemp T hL (levelN_dvd n)) (mk_repCocycle (x (n + 1)))).trans
      ((hx n).trans c.2.symm)))
  exact ⟨c', h1.trans (mk_repCocycle _), h2⟩

/-- One lifting step: a representative of `x (n+1)` lying over a given representative of
`x n`. -/
def liftStep (n : ℕ) (c : {c : ContH1.cocycles PYddg (Mu (levelN n) Ω) // ContH1.mk c = x n}) :
    {c' : ContH1.cocycles PYddg (Mu (levelN (n + 1)) Ω) //
      ContH1.mk c' = x (n + 1) ∧ ∀ g, Mu.transition (levelN_dvd n) (c' g) = c.1 g} :=
  ⟨(exists_liftStep x hx n c).choose, (exists_liftStep x hx n c).choose_spec⟩

/-- **Compatible representative cocycles** of a compatible system of classes `x n` (for the
theta classes: `transTemp_thetaClassTemp`), chosen upwards by `liftStep`. -/
def compatRep : ∀ n, {c : ContH1.cocycles PYddg (Mu (levelN n) Ω) // ContH1.mk c = x n}
  | 0 => ⟨Quotient.out (x 0), Quotient.out_eq _⟩
  | n + 1 => ⟨(liftStep x hx n (compatRep n)).1, (liftStep x hx n (compatRep n)).2.1⟩

/-- `hηred`: the representatives are compatible with the reductions. -/
theorem compatRep_red (n : ℕ) (g : PYddg) :
    ((compatRep x hx n).1 : PYddg → Mu (levelN n) Ω) g =
      Mu.transition (levelN_dvd n) ((compatRep x hx (n + 1)).1 g) :=
  ((liftStep x hx n (compatRep x hx n)).2.2 g).symm

variable (hPY : Envelope.FISlim
  (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV))

/-- **The tower of model environments of the classes `x n`** ([EtTh], Cor. 2.19(ii)): the
natural projective system of `Env/Tower.lean` for the genuine theta setting. -/
abbrev thetaTower : RigidSystems.Tower.{u + 1, u} :=
  envTower augg (fun n => psiMu (levelN n)) (fun n => Mu.transition (levelN_dvd n))
    (fun n σ m => transition_psiMu (levelN_dvd n) σ m)
    (fun n => transition_surjective (levelN_dvd n) (NeZero.ne _)) levelN
    (fun n => ker_transition (levelN_dvd n) (NeZero.ne _))
    (fun n => contCocycles (psiMu (levelN n))) (fun n => contCocycles_eq_map (levelN_dvd n))
    (piYddotX_le_piY T hL) (fun n => isOpen_ker_act_augT DXg O V hV (levelN n))
    (fun _ => isCocycle_of_mem_contCocycles _)
    (fun n => isCocycle_coe_cocycles (levelN n) (compatRep x hx n).1)
    (compatRep_red x hx) hPY

/-- The action on `Π^tp_Y` of the automorphisms of the level-`n` model of `thetaTower`. -/
abbrev thetaAutPYN (n : ℕ) :=
  autPYN augg (fun n => psiMu (levelN n)) (fun n => Mu.transition (levelN_dvd n))
    (fun n σ m => transition_psiMu (levelN_dvd n) σ m)
    (fun n => transition_surjective (levelN_dvd n) (NeZero.ne _)) levelN
    (fun n => ker_transition (levelN_dvd n) (NeZero.ne _))
    (fun n => contCocycles (psiMu (levelN n))) (fun n => contCocycles_eq_map (levelN_dvd n))
    (piYddotX_le_piY T hL) (fun n => isOpen_ker_act_augT DXg O V hV (levelN n))
    (fun _ => isCocycle_of_mem_contCocycles _)
    (fun n => isCocycle_coe_cocycles (levelN n) (compatRep x hx n).1)
    (compatRep_red x hx) hPY n

/-- **The level-`n` model of the tower is the theta environment of `x n`** (`thetaEnv`, built
from an arbitrary representative): cohomologous cocycles give the same environment. -/
theorem thetaTower_model (n : ℕ) :
    (thetaTower x hx hPY).model n = thetaEnv T hL (levelN n) (x n) := by
  apply modelEnv_eq_of_cohomologous
  have h := (compatRep x hx n).2.trans (mk_repCocycle (x n)).symm
  rw [ContH1.mk_eq_mk_iff] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨z, fun g => ?_⟩
  have e : g • z / z = (compatRep x hx n).1 g / repCocycle (x n) g := hz g
  rw [div_eq_div_iff_mul_eq_mul] at e
  change repCocycle (x n) g = z * (compatRep x hx n).1 g *
    (act augg (psiMu (levelN n)) (g : PXg) z)⁻¹
  rw [act_augT_psiMu]
  change repCocycle (x n) g = z * (compatRep x hx n).1 g * (g • z)⁻¹
  rw [eq_mul_inv_iff_mul_eq, mul_comm (repCocycle (x n) g), e, mul_comm]

/-- **[EtTh], Cor. 2.19(ii) (discrete rigidity) for the theta environments**: every projective
system of mod-`N_n` mono-theta environments levelwise isomorphic to the model environments of
the classes `x n` is isomorphic to the model system. Obligation 10 (the tower data `hred`,
`hs`, `hker`, `hKumRed`, `hηred`) is discharged; the named hypotheses are `hPY`
(`FISlim Π^tp_Y`), the index `[Π^tp_Y : Π^tp_Ÿ] < ∞` and `hlift` (the surjectivity half of
Cor. 2.18(iv), Layer-B obligation 9). -/
theorem discreteRigidity_thetaEnv [((piYddotX V hV T hL).subgroupOf
      (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)).FiniteIndex]
    (hlift : ∀ n, (thetaAutPYN x hx hPY 0).range ≤ (thetaAutPYN x hx hPY n).range)
    (S : (thetaTower x hx hPY).System)
    (hS : ∀ n, Nonempty (S.X n ≅ (thetaTower x hx hPY).model n)) : S.IsoModel :=
  discreteRigidity_env (hlift := hlift) (S := S) (hS := hS)

end Compat

section Classes

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

/-- **The étale theta classes form a compatible system along the levels `N_n`**: the input
`hx` of `thetaTower` for `x n = thetaClassTemp η N_n` (MR14, `transTemp_thetaClassTemp`). -/
theorem transTemp_thetaClassTemp_levelN {η : ∀ j, units (fieldData ht (L j) (hL j))}
    (hC1 : LevelsDominated V hV T hL) (htr : ThetaTransitions ht hL η) (n : ℕ) :
    transTemp T hL (levelN_dvd n) (thetaClassTemp η hC1 (levelN (n + 1))) =
      thetaClassTemp η hC1 (levelN n) :=
  transTemp_thetaClassTemp hC1 htr (levelN_dvd n)

omit [IsAlgClosed Ω] in
/-- **`[Π^tp_Y : Π^tp_Ÿ] < ∞`** (the index hypothesis of `discreteRigidity_env`): `Π^tp_Ÿ` is the
intersection of `Π^tp_Y` with the image of the tempered group of the finite étale level `L 0`,
which has finite index (tfg `finiteIndex_range_temperedPi1Map`). -/
theorem finiteIndex_piYddotX :
    ((piYddotX V hV T hL).subgroupOf
      (Iut.EtaleTheta.TateObject.piY (A := (fieldData ht LX hLX).A) T V hV)).FiniteIndex := by
  haveI := finiteIndex_range_temperedPi1Map (O := O) V hV (muL ht hLX (L 0) (hL 0))
  rw [piYddotX, Subgroup.inf_subgroupOf_left]
  infer_instance

end Classes

end Iut.EtaleTheta.Env
