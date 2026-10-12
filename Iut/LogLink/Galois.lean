/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Local
import Iut.Reconstruction.Local.LogShellIdent
import Iut.Reconstruction.Local.Valuation

/-!
# Galois-induced identifications are unit-induced

P20 (`Iut/LogLink/Local.lean`) calls an additive automorphism `ψ` of a local field `k`
**unit-induced** (`LogLink.UnitInduced`) if `ψ ∘ log = log ∘ α` on the principal units for an
automorphism `α` of the principal units. Here we show that the identifications of the
log-shells produced by the anabelian reconstruction of P17 (`Iut/Reconstruction/`) are of this
form (IUT III, Proposition 1.2(vi), (viii); [AbsTopIII], Proposition 5.8 (i), (ii)).

The field `k` carries both the valuation of `Iut/Concrete` and the `ℚ_p`-algebra structure of
`local-class-field-theory`, with the same unit ball (`hball`), as in P17, M3d–M3f.

## Main results

* `pow_q_sub_one_iff`: **the principal units are the `(q − 1)`-th powers of `𝒪_kˣ`**, so every
  automorphism of the abstract group `𝒪_kˣ` preserves them (`prinOfUnits`);
* `logTensor_bijective`, `logEquiv`: the logarithm `ℚ ⊗ 𝒪_kˣ → k` of P17 (`logTensor`) is an
  isomorphism (its kernel is the torsion, `exists_pow_eq_one_of_logU_eq_zero`);
* `unitLogEquiv β`: the additive automorphism of `k` induced by an automorphism `β` of `𝒪_kˣ`
  (`ℚ ⊗ β` transported along `logEquiv`); **`unitInduced_unitLogEquiv`**: it is unit-induced,
  hence preserves the log-shell (`image_logShell_unitLogEquiv`); `unitLogEquiv_refl`,
  `unitLogEquiv_inv` (the inversion of the units induces `x ↦ −x`);
* for `G_k = Gal(Ω/k)` and a topological automorphism `φ` of `G_k`: `galUnitsEquiv φ`, the
  automorphism of `𝒪_kˣ` reconstructed by P17 (it is the restriction of `galEquiv_multEquiv`,
  `coe_galUnitsEquiv`), and `galLogEquiv φ = unitLogEquiv (galUnitsEquiv φ)`;
  **`galLogEquiv_transport`**: `galLogEquiv φ` is the transport, through
  `log : ℚ ⊗ 𝒪^×(G_k) ≅ k`, of P17's isomorphism `unitsQEquiv φ` of the group-theoretic
  `ℚ ⊗ 𝒪^×(G_k)`, which carries `monoLogShell` onto itself (`map_monoLogShell`); hence
  **`galLogEquiv_image_logShell`** (from the transport and `image_logTensor_monoLogShell`) and
  **`unitInduced_galLogEquiv`**: every identification induced by a Galois isomorphism is
  unit-induced; `galLogEquiv_refl`;
* obstructions: `norm_eq_one_of_unitInduced_scale` (a unit-induced scaling `x ↦ b·x` has
  `‖b‖ = 1`), `galLogEquiv_ne_scale`; on the multiplicative side
  `galEquiv_multEquiv_ne_zpow_mul` (a Galois-induced `kˣ ≃* kˣ` never acts on a unit as
  multiplication by `q^m`, `v(q) ≠ 0`, `m ≠ 0`: it preserves `𝒪ˣ` and `v`).
-/

namespace Iut

namespace LogLink

open PadicLogVolume PadicField IsLocalRing Iut.Reconstruction
open scoped Valued TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Scalings that are unit-induced -/

section Scale

variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CompleteSpace k] [CharZero k] {p : ℕ}

omit [CompleteSpace k] [CharZero k] in
theorem scale_symm (b : kˣ) : (scale b).symm = scale b⁻¹ := rfl

/-- **A unit-induced scaling `x ↦ b·x` has `‖b‖ = 1`.** -/
theorem norm_eq_one_of_unitInduced_scale (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {b : kˣ}
    (h : UnitInduced (scale b)) : ‖(b : k)‖ = 1 := by
  rcases lt_trichotomy ‖(b : k)‖ 1 with hb | hb | hb
  · exact absurd h (not_unitInduced_scale hp hpk hb)
  · exact hb
  · have h' := h.symm
    rw [scale_symm] at h'
    refine absurd h' (not_unitInduced_scale hp hpk ?_)
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_lt_one_of_one_lt₀ hb

end Scale

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k] [CompleteSpace k] [CharZero k]

/-! ### The principal units are the `(q − 1)`-th powers -/

theorem coprime_q_sub_one : p.Coprime (q p k - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have hq := one_lt_q p k
  have hpq : p ∣ q p k := by
    rw [q_eq_p_pow_f]
    have hf : f p ℚ_[p] k ≠ 0 := by
      intro h0
      have := q_eq_p_pow_f (p := p) (K := k)
      rw [h0, pow_zero] at this
      omega
    exact dvd_pow_self p hf
  have h1 : p ∣ q p k - (q p k - 1) := Nat.dvd_sub hpq h
  rw [show q p k - (q p k - 1) = 1 by omega] at h1
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)

variable (hball : ∀ x : k, ‖x‖ ≤ 1 ↔ nrm p k x ≤ 1)
include hball

/-- **The principal units are the `(q − 1)`-th powers of `𝒪_kˣ`** (`𝒪_kˣ = μ_{q−1} × U¹`, and
`U¹` is uniquely `n`-divisible for `p ∤ n`). -/
theorem pow_q_sub_one_iff (u : unitGroup p k) :
    ‖((u : kˣ) : k) - 1‖ < 1 ↔ ∃ y : unitGroup p k, y ^ (q p k - 1) = u := by
  constructor
  · intro hw
    set w' := unitGroupToInt u
    have hker : w' ∈ (resUnits p k).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change residue (𝒪 p k) (w' : 𝒪 p k) = residue (𝒪 p k) 1
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Integers.mem_maximalIdeal_iff]
      rw [← norm_lt_one_iff' hball]
      simpa [w', coe_unitGroupToInt] using hw
    have hq := one_lt_q p k
    obtain ⟨v', hv'⟩ := ker_resUnits_le_powRange (coprime_q_sub_one (k := k)) (by omega) hker
    refine ⟨⟨Units.mk0 ((v' : 𝒪 p k) : k) (by
          intro h0
          exact v'.ne_zero (Integers.ext (by rw [h0]; rfl))),
        Integers.isUnit_iff_nrm_eq_one.1 v'.isUnit⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun z : (𝒪 p k)ˣ => ((z : 𝒪 p k) : k)) hv'
    simpa [w', coe_unitGroupToInt] using this
  · rintro ⟨y, rfl⟩
    simpa using pow_q_sub_one_principal hball y

/-! ### The logarithm `ℚ ⊗ 𝒪_kˣ ≅ k` -/

theorem logTensor_smul (c : ℚ) (z : ℚ ⊗[ℤ] Additive (unitGroup p k)) :
    logTensor hball (c • z) = (c : k) * logTensor hball z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change logTensor hball ((c * a) ⊗ₜ Additive.ofMul u.toMul) =
      _ * logTensor hball (a ⊗ₜ Additive.ofMul u.toMul)
    rw [logTensor_tmul, logTensor_tmul]
    push_cast
    ring
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

theorem logTensor_one_tmul (u : unitGroup p k) :
    logTensor hball ((1 : ℚ) ⊗ₜ Additive.ofMul u) = (logU hball u).toAdd := by
  rw [logTensor_tmul]
  push_cast
  rw [one_mul]

/-- **The kernel of `logU` is the torsion of `𝒪_kˣ`.** -/
theorem exists_pow_eq_one_of_logU_eq_zero {u : unitGroup p k} (h : (logU hball u).toAdd = 0) :
    ∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1 := by
  have hq := one_lt_q p k
  have hpr := pow_q_sub_one_principal hball u
  set w : principalUnits k := ⟨((u : kˣ) ^ (q p k - 1)), by
    change ‖(((u : kˣ) ^ (q p k - 1) : kˣ) : k) - 1‖ < 1
    rw [Units.val_pow_eq_pow_val]
    exact hpr⟩
  have hlog : padicLog (((u : kˣ) : k) ^ (q p k - 1)) = 0 := by
    rw [logU_apply] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd (inv_eq_zero.1 h0) (q_sub_one_ne_zero (p := p))
    · exact h0
  have hw : w ∈ logKer hp.out (norm_p_lt_one hball) := by
    rw [logKer, MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [Reconstruction.logHom_apply]
    simpa [w] using hlog
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem_logKer hball hw
  refine ⟨(q p k - 1) * p ^ j, Nat.mul_ne_zero (by omega) (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  apply Subtype.ext
  have := congrArg (fun z : principalUnits k => ((z : kˣ))) hj
  simpa [w, pow_mul] using this

theorem logTensor_injective : Function.Injective (logTensor hball) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  haveI := IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
    (M := Additive (unitGroup p k))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (Additive (unitGroup p k)) 1) z
  simp only [TensorProduct.mk_apply] at hs
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsz : (s : ℤ) • z = ((s : ℤ) : ℚ) • z := (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hlog : (logU hball a.toMul).toAdd = 0 := by
    have h1 := congrArg (logTensor hball) hs
    rw [← logTensor_one_tmul]
    change _ = logTensor hball ((1 : ℚ) ⊗ₜ Additive.ofMul a.toMul) at h1
    rw [← h1, Submonoid.smul_def, hsz, logTensor_smul, hz, mul_zero]
  obtain ⟨n, hn0, hn⟩ := exists_pow_eq_one_of_logU_eq_zero hball hlog
  have h2 : (n : ℤ) • ((s : ℤ) • z) = 0 := by
    rw [← Submonoid.smul_def, hs, ← TensorProduct.tmul_smul]
    have : (n : ℤ) • a = 0 := by
      rw [natCast_zsmul]
      change Additive.ofMul (a.toMul ^ n) = _
      rw [hn]
      rfl
    rw [this, TensorProduct.tmul_zero]
  rw [hsz, ← Int.cast_smul_eq_zsmul ℚ, smul_smul] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have : ((n : ℤ) : ℚ) * ((s : ℤ) : ℚ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn0) (by exact_mod_cast hs0)
    exact this h3
  · exact h3

theorem logTensor_surjective : Function.Surjective (logTensor hball) := by
  intro y
  have hpk := norm_p_lt_one hball
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hpk
  have hy : (p : k) ^ N * y ∈ logShell k p := by
    refine closedBall_subset_logShell hp.out hpk ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_pow]
    calc ‖(p : k)‖ ^ N * ‖y‖ ≤ 1 / (‖y‖ + 1) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hN.le (norm_nonneg _)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          linarith
  rw [← image_logTensor hball] at hy
  obtain ⟨x, -, hx⟩ := hy
  refine ⟨((p : ℚ) ^ N)⁻¹ • x, ?_⟩
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [logTensor_smul, hx]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]

theorem logTensor_bijective : Function.Bijective (logTensor hball) :=
  ⟨logTensor_injective hball, logTensor_surjective hball⟩

/-- **The logarithm `ℚ ⊗ 𝒪_kˣ ≅ k`** ([AbsTopIII], Proposition 5.8 (ii)). -/
def logEquiv : ℚ ⊗[ℤ] Additive (unitGroup p k) ≃+ k :=
  AddEquiv.ofBijective (logTensor hball) (logTensor_bijective hball)

@[simp] theorem logEquiv_apply (z : ℚ ⊗[ℤ] Additive (unitGroup p k)) :
    logEquiv hball z = logTensor hball z := rfl

/-! ### Identifications induced by automorphisms of `𝒪_kˣ` -/

omit hball in
/-- `ℚ ⊗ β` for an automorphism `β` of `𝒪_kˣ`. -/
def unitsTensorEquiv (β : unitGroup p k ≃* unitGroup p k) :
    ℚ ⊗[ℤ] Additive (unitGroup p k) ≃ₗ[ℤ] ℚ ⊗[ℤ] Additive (unitGroup p k) :=
  TensorProduct.congr (LinearEquiv.refl ℤ ℚ) β.toAdditive.toIntLinearEquiv

omit hball in
theorem unitsTensorEquiv_tmul (β : unitGroup p k ≃* unitGroup p k) (c : ℚ)
    (u : unitGroup p k) :
    unitsTensorEquiv β (c ⊗ₜ Additive.ofMul u) = c ⊗ₜ Additive.ofMul (β u) := rfl

/-- **The identification of `k` induced by an automorphism `β` of `𝒪_kˣ`**: `ℚ ⊗ β`, transported
along the logarithm `ℚ ⊗ 𝒪_kˣ ≅ k`. -/
def unitLogEquiv (β : unitGroup p k ≃* unitGroup p k) : k ≃+ k :=
  (logEquiv hball).symm.trans ((unitsTensorEquiv β).toAddEquiv.trans (logEquiv hball))

theorem unitLogEquiv_logEquiv (β : unitGroup p k ≃* unitGroup p k)
    (z : ℚ ⊗[ℤ] Additive (unitGroup p k)) :
    unitLogEquiv hball β (logEquiv hball z) = logEquiv hball (unitsTensorEquiv β z) := by
  simp only [unitLogEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

/-- `ψ_β(log u) = log(β u)` on `𝒪_kˣ`. -/
theorem unitLogEquiv_logU (β : unitGroup p k ≃* unitGroup p k) (u : unitGroup p k) :
    unitLogEquiv hball β (logU hball u).toAdd = (logU hball (β u)).toAdd := by
  rw [← logTensor_one_tmul, ← logEquiv_apply, unitLogEquiv_logEquiv, unitsTensorEquiv_tmul,
    logEquiv_apply, logTensor_one_tmul]

theorem unitLogEquiv_refl : unitLogEquiv hball (MulEquiv.refl (unitGroup p k)) =
    AddEquiv.refl k := by
  ext y
  obtain ⟨z, rfl⟩ := (logEquiv hball).surjective y
  rw [unitLogEquiv_logEquiv]
  have : unitsTensorEquiv (MulEquiv.refl (unitGroup p k)) z = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a u => rfl
    | add x y hx hy => rw [map_add, hx, hy]
  rw [this]
  rfl

/-- **The inversion of the units induces `x ↦ −x`.** -/
theorem unitLogEquiv_inv : unitLogEquiv hball (MulEquiv.inv (unitGroup p k)) =
    AddEquiv.neg k := by
  ext y
  obtain ⟨z, rfl⟩ := (logEquiv hball).surjective y
  rw [unitLogEquiv_logEquiv, AddEquiv.neg_apply, ← map_neg]
  have : unitsTensorEquiv (MulEquiv.inv (unitGroup p k)) z = -z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      change a ⊗ₜ Additive.ofMul (u.toMul)⁻¹ = _
      rw [ofMul_inv, TensorProduct.tmul_neg]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, neg_add]
  rw [this]

/-! ### Restriction to the principal units -/

theorem mem_unitGroup_of_prin (u : prinUnits k) : (u : kˣ) ∈ unitGroup p k :=
  (norm_eq_one_iff_nrm hball _).1 (norm_eq_one_of_norm_sub_one_lt u.2)

/-- A principal unit as an element of `𝒪_kˣ`. -/
def prinToUnits (u : prinUnits k) : unitGroup p k := ⟨u, mem_unitGroup_of_prin hball u⟩

theorem prin_map (β : unitGroup p k ≃* unitGroup p k) (u : prinUnits k) :
    ‖(((β (prinToUnits hball u) : unitGroup p k) : kˣ) : k) - 1‖ < 1 := by
  obtain ⟨y, hy⟩ := (pow_q_sub_one_iff hball (prinToUnits hball u)).1 u.2
  refine (pow_q_sub_one_iff hball _).2 ⟨β y, ?_⟩
  rw [← map_pow, hy]

/-- The restriction of `β` to the principal units, as a homomorphism. -/
def prinHom (β : unitGroup p k ≃* unitGroup p k) : prinUnits k →* prinUnits k where
  toFun u := ⟨(β (prinToUnits hball u) : kˣ), prin_map hball β u⟩
  map_one' := by
    apply Subtype.ext
    have : prinToUnits hball (1 : prinUnits k) = 1 := rfl
    simp [this]
  map_mul' x y := by
    apply Subtype.ext
    have : prinToUnits hball (x * y) = prinToUnits hball x * prinToUnits hball y := rfl
    simp [this]

/-- **Every automorphism of `𝒪_kˣ` restricts to an automorphism of the principal units.** -/
def prinOfUnits (β : unitGroup p k ≃* unitGroup p k) : prinUnits k ≃* prinUnits k where
  toFun := prinHom hball β
  invFun := prinHom hball β.symm
  left_inv u := by
    apply Subtype.ext
    change ((β.symm (prinToUnits hball _) : unitGroup p k) : kˣ) = u
    have : prinToUnits hball (prinHom hball β u) = β (prinToUnits hball u) := rfl
    rw [this, MulEquiv.symm_apply_apply]
    rfl
  right_inv u := by
    apply Subtype.ext
    change ((β (prinToUnits hball _) : unitGroup p k) : kˣ) = u
    have : prinToUnits hball (prinHom hball β.symm u) = β.symm (prinToUnits hball u) := rfl
    rw [this, MulEquiv.apply_symm_apply]
    rfl
  map_mul' := (prinHom hball β).map_mul

theorem pval_prinOfUnits (β : unitGroup p k ≃* unitGroup p k) (u : prinUnits k) :
    pval (prinOfUnits hball β u) = (((β (prinToUnits hball u) : unitGroup p k) : kˣ) : k) :=
  rfl

/-- **Identifications induced by automorphisms of `𝒪_kˣ` are unit-induced.** -/
theorem unitInduced_unitLogEquiv (β : unitGroup p k ≃* unitGroup p k) :
    UnitInduced (unitLogEquiv hball β) := by
  refine ⟨prinOfUnits hball β, fun u => ?_⟩
  have h1 : padicLog (pval u) = (logU hball (prinToUnits hball u)).toAdd :=
    (logU_of_principal hball (prinToUnits hball u) u.2).symm
  rw [h1, unitLogEquiv_logU, pval_prinOfUnits, logU_of_principal hball _ (prin_map hball β u)]

/-- **They preserve the log-shell.** -/
theorem image_logShell_unitLogEquiv (β : unitGroup p k ≃* unitGroup p k) :
    unitLogEquiv hball β '' logShell k p = logShell k p :=
  image_logShell_of_unitInduced hp.out (unitInduced_unitLogEquiv hball β)

/-- **A scaling by `b` with `‖b‖ ≠ 1` is not induced by an automorphism of `𝒪_kˣ`.** -/
theorem unitLogEquiv_ne_scale (β : unitGroup p k ≃* unitGroup p k) {b : kˣ}
    (hb : ‖(b : k)‖ ≠ 1) : unitLogEquiv hball β ≠ scale b := fun h =>
  hb (norm_eq_one_of_unitInduced_scale hp.out (norm_p_lt_one hball)
    (h ▸ unitInduced_unitLogEquiv hball β))

/-! ### Identifications induced by Galois isomorphisms -/

variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

omit hball in
variable (p) in
/-- **The automorphism of `𝒪_kˣ` reconstructed from a topological automorphism `φ` of
`G_k = Gal(Ω/k)`** ([AbsTopIII], Proposition 5.8 (i)): through the image `𝒪^×(G_k)` of the
inertia in `G_k^ab` (P17, `abUnitsEquiv`, `unitsAbEquiv`). -/
def galUnitsEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) : unitGroup p k ≃* unitGroup p k :=
  (unitsAbEquiv p k Ω).trans ((abUnitsEquiv φ).trans (unitsAbEquiv p k Ω).symm)

omit hball in
theorem unitsAbEquiv_galUnitsEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) (u : unitGroup p k) :
    unitsAbEquiv p k Ω (galUnitsEquiv p φ u) = abUnitsEquiv φ (unitsAbEquiv p k Ω u) := by
  simp [galUnitsEquiv]

omit hball in
theorem multAbEquiv_coe_unit (u : unitGroup p k) :
    (multAbEquiv p k Ω (u : kˣ) : TopologicalAbelianization (Ω ≃ₐ[k] Ω)) =
      unitsAbEquiv p k Ω u := by
  apply (galAbEquiv p k Ω).injective
  rw [galAbEquiv_multAbEquiv, galAbEquiv_unitsAbEquiv]

omit hball in
/-- **`galUnitsEquiv` is the restriction to `𝒪_kˣ` of P17's `galEquiv_multEquiv`.** -/
theorem coe_galUnitsEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) (u : unitGroup p k) :
    ((galUnitsEquiv p φ u : unitGroup p k) : kˣ) = galEquiv_multEquiv p p φ (u : kˣ) := by
  apply (multAbEquiv p k Ω).injective
  apply Subtype.ext
  rw [multAbEquiv_galEquiv_multEquiv, multAbEquiv_coe_unit, multAbEquiv_coe_unit,
    unitsAbEquiv_galUnitsEquiv]
  rfl

omit hball in
theorem galUnitsEquiv_refl :
    galUnitsEquiv p (ContinuousMulEquiv.refl (Ω ≃ₐ[k] Ω)) = MulEquiv.refl _ := by
  ext u
  have h : abUnitsEquiv (ContinuousMulEquiv.refl (Ω ≃ₐ[k] Ω)) (unitsAbEquiv p k Ω u) =
      unitsAbEquiv p k Ω u := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      ((unitsAbEquiv p k Ω u : abUnits _) : TopologicalAbelianization (Ω ≃ₐ[k] Ω))
    change abEquiv _ _ = _
    rw [← hx]
    rfl
  simp [galUnitsEquiv, h]

/-- **The identification of `k` induced by a topological automorphism `φ` of `G_k`.** -/
def galLogEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) : k ≃+ k :=
  unitLogEquiv hball (galUnitsEquiv p φ)

omit hball in
theorem unitsQGalEquiv_unitsTensorEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω))
    (z : ℚ ⊗[ℤ] Additive (unitGroup p k)) :
    unitsQGalEquiv p k Ω (unitsTensorEquiv (galUnitsEquiv p φ) z) =
      unitsQEquiv φ (unitsQGalEquiv p k Ω z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    change a ⊗ₜ Additive.ofMul (unitsAbEquiv p k Ω (galUnitsEquiv p φ u.toMul)) =
      a ⊗ₜ Additive.ofMul (abUnitsEquiv φ (unitsAbEquiv p k Ω u.toMul))
    rw [unitsAbEquiv_galUnitsEquiv]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **`galLogEquiv φ` is the transport of the group-theoretic `ℚ ⊗ 𝒪^×(G_k) ≅ ℚ ⊗ 𝒪^×(G_k)`
induced by `φ`** (P17, `unitsQEquiv`) along the logarithm `ℚ ⊗ 𝒪^×(G_k) ≅ ℚ ⊗ 𝒪_kˣ ≅ k` of
`image_logTensor_monoLogShell`. -/
theorem galLogEquiv_transport (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω))
    (x : unitsQ (Ω ≃ₐ[k] Ω)) :
    galLogEquiv hball φ (logTensor hball ((unitsQGalEquiv p k Ω).symm x)) =
      logTensor hball ((unitsQGalEquiv p k Ω).symm (unitsQEquiv φ x)) := by
  rw [← logEquiv_apply, galLogEquiv, unitLogEquiv_logEquiv, logEquiv_apply]
  congr 1
  apply (unitsQGalEquiv p k Ω).injective
  rw [unitsQGalEquiv_unitsTensorEquiv, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **The Galois-induced identification preserves the log-shell**, read off from the
group-theoretic log-shell: `φ` carries `monoLogShell (G_k)` onto itself (`map_monoLogShell`), and
the logarithm carries `monoLogShell (G_k)` onto `Iut.logShell k p`
(`image_logTensor_monoLogShell`). -/
theorem galLogEquiv_image_logShell (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) :
    galLogEquiv hball φ '' logShell k p = logShell k p := by
  rw [← image_logTensor_monoLogShell hball Ω, Set.image_image]
  simp_rw [galLogEquiv_transport]
  conv_rhs => rw [← map_monoLogShell φ]
  rw [Set.image_image]

/-- **Every identification induced by a Galois isomorphism is unit-induced.** -/
theorem unitInduced_galLogEquiv (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) :
    UnitInduced (galLogEquiv hball φ) :=
  unitInduced_unitLogEquiv hball _

theorem galLogEquiv_refl :
    galLogEquiv hball (ContinuousMulEquiv.refl (Ω ≃ₐ[k] Ω)) = AddEquiv.refl k := by
  rw [galLogEquiv, galUnitsEquiv_refl, unitLogEquiv_refl]

/-- **A scaling by `b` with `‖b‖ ≠ 1` (e.g. a nonzero power of a Tate parameter) is not induced
by a Galois isomorphism.** -/
theorem galLogEquiv_ne_scale (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) {b : kˣ}
    (hb : ‖(b : k)‖ ≠ 1) : galLogEquiv hball φ ≠ scale b :=
  unitLogEquiv_ne_scale hball _ hb

omit hball in
/-- **On the multiplicative side**: the isomorphism `kˣ ≃* kˣ` induced by a Galois isomorphism
never acts on a unit as multiplication by `q^m` with `v(q) ≠ 0`, `m ≠ 0` (it preserves the
valuation, `v_galEquiv_multEquiv`; `q^m·u` is not a unit). -/
theorem galEquiv_multEquiv_ne_zpow_mul (φ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω ≃ₐ[k] Ω)) {qt : kˣ}
    (hq : v p (qt : k) ≠ 0) {m : ℤ} (hm : m ≠ 0) (u : unitGroup p k) :
    galEquiv_multEquiv p p φ (u : kˣ) ≠ qt ^ m * u := by
  intro h
  have h1 := v_galEquiv_multEquiv (p := p) (p' := p) φ (u : kˣ)
  have hu : v p (((u : kˣ) : k)) = 0 := by
    rw [← coe_unitGroupToInt u]
    exact v_unit _
  rw [h, hu, Units.val_mul, Units.val_zpow_eq_zpow_val,
    v_mul (zpow_ne_zero _ qt.ne_zero) (u : kˣ).ne_zero, v_zpow qt.ne_zero, hu, add_zero] at h1
  exact mul_ne_zero hm hq h1

end

end LogLink

end Iut
