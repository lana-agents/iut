/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.CuspAction
import Iut.Reconstruction.Cusp.HemiGenuineField
import Iut.Anabelian.Torsion

/-!
# Semilinear automorphisms of `C_K` and their action on the cusps of `X̲_K` (MR22 T6)

IUT I, Example 4.3 (i) (l.6545–6600 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): `Aut(C̲_K)/Aut_ϵ(C̲_K) ≅ F_ℓ^⋇`. The surjectivity comes from the field: for
`θ ∈ Gal(K/F)` stabilising the line `M ⊆ E(K)[ℓ]` and acting on `Q = E(K)[ℓ]/M` by a scalar
`s`, a semilinear automorphism of `Ω = K(E)^alg` over `θ` fixing `x`, `y` conjugates
`π₁(C_K)` into itself and acts on `π₁(C_K)/π₁(C̲_K) ≅ Q ≅ F_ℓ` by `s` (up to a translation,
removed by an inner automorphism). By Definition 3.1 (c) (`AdmissiblePrimeData.sl_le_range`:
the image of `Gal(F̄/F)` in `GL₂(F_ℓ)` contains `SL₂(F_ℓ)`, l.3979–3982) the Borel subgroup of
`SL₂(F_ℓ)` stabilising `M` realises every scalar `s`.

* `ptCast`, `IsSemilin`, **`exists_isSemilin`** (from `mapOmegaEquiv`), `psi` (conjugation by
  `τ` on `Gal(Ω / k(x))`), `betaC` (on `π₁(C) = pi1C E 1 ⊥ true`), `tauPt` (the action of `τ` on
  `E(Ω)`), `act_psi_tauPt`, `tauPt_base`;
* `sgnTr_psi`, **`rhoGal_psi`**: `ρ(τ σ τ⁻¹) = A ρ(σ) A⁻¹` for the affine map `A z = s z − c`;
* **`exists_beta`**, **`exists_semilin_of_cover`**: a continuous automorphism `β` of `π₁(C)` with
  `ρ(β x)(0) = s · ρ(x)(0)` for every dihedral action `ρ` with stabiliser `π₁(C̲)`
  (`scalar_transfer`: the scalar does not depend on `ρ`);
* **`exists_borel`**, `exists_semilin_data`: for initial Θ-data, every `s ∈ F_ℓ^×` is realised
  by some `θ = σ|_K`, `σ ∈ Gal(F̄/F)`, with `ρ(σ) ∈ SL₂(F_ℓ)` in the Borel subgroup of `M`.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open WeierstrassCurve Iut.Anabelian Iut.Anabelian.Genuine Iut.HodgeTheater
  Iut.Reconstruction.HemiGenuine

universe u

attribute [local instance low] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### The scalar does not depend on the dihedral action -/

section Transfer

variable {ℓ : ℕ} [OddPrime ℓ] {G : Type*} [Group G]

/-- Two dihedral actions with the same stabiliser `R` of `0` differ on the orbit of `0` by a
scalar. -/
theorem exists_mul_of_stab {ρ ρ' : G →* Equiv.Perm (ZMod ℓ)} {R : Subgroup G}
    (h : IsDihedralQuot ρ R) (h' : IsDihedralQuot ρ' R) :
    ∃ b : (ZMod ℓ)ˣ, ∀ g, ρ' g 0 = b * ρ g 0 := by
  obtain ⟨-, hR, x₁, hx₁⟩ := h
  obtain ⟨hS', hR', -⟩ := h'
  obtain ⟨ε, b, hg₁⟩ := hS' x₁
  have hb : ρ' x₁ 0 = b := by rw [hg₁]; simp
  have step : ∀ g, ρ' (x₁ * g) 0 = sgn ℓ ε * ρ' g 0 + b := fun g => by
    rw [map_mul, Equiv.Perm.mul_apply, hg₁, affPerm_apply]
  have hρx : ∀ g, ρ (x₁ * g) 0 = ρ g 0 + 1 := fun g => by
    rw [map_mul, Equiv.Perm.mul_apply, hx₁, affPerm_apply, sgn_one, one_mul]
  have hx₁0 : ρ x₁ 0 = 1 := by rw [hx₁]; simp
  have hε : ε = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · exact h
    exfalso
    have h2 : ρ' (x₁ * x₁) 0 = 0 := by
      rw [step, hb, h, sgn_neg_one]
      ring
    have h3 := (hR _).1 ((hR' _).2 h2)
    rw [hρx, hx₁0] at h3
    exact two_ne_zero_zmod (ℓ := ℓ) (by linear_combination h3)
  subst hε
  have hn : ∀ n : ℕ, ∀ g, ρ g 0 = n → ρ' g 0 = n * b := by
    intro n
    induction n with
    | zero =>
      intro g hg
      rw [Nat.cast_zero] at hg ⊢
      rw [zero_mul]
      exact (hR' _).1 ((hR g).2 hg)
    | succ n ih =>
      intro g hg
      have e1 : ρ (x₁⁻¹ * g) 0 = n := by
        have := hρx (x₁⁻¹ * g)
        rw [mul_inv_cancel_left] at this
        push_cast at hg
        linear_combination hg - this
      have e2 := step (x₁⁻¹ * g)
      rw [mul_inv_cancel_left] at e2
      rw [e2, ih _ e1, sgn_one]
      push_cast
      ring
  have hb0 : b ≠ 0 := by
    intro h0
    have hmem : x₁ ∈ R := (hR' _).2 (by rw [hb, h0])
    have := (hR _).1 hmem
    rw [hx₁0] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 b hb0, fun g => ?_⟩
  have := hn (ρ g 0).val g (by rw [ZMod.natCast_zmod_val])
  rw [this, ZMod.natCast_zmod_val, Units.val_mk0, mul_comm]

/-- **The scalar of a map is independent of the dihedral action**: if `ρ(α g)(0) = s ρ(g)(0)`
for one dihedral action with stabiliser `R`, then also for every other one. -/
theorem scalar_transfer {ρ ρ' : G →* Equiv.Perm (ZMod ℓ)} {R : Subgroup G}
    (h : IsDihedralQuot ρ R) (h' : IsDihedralQuot ρ' R) {α : G → G} {s : (ZMod ℓ)ˣ}
    (hs : ∀ g, ρ (α g) 0 = s * ρ g 0) (g : G) : ρ' (α g) 0 = s * ρ' g 0 := by
  obtain ⟨b, hb⟩ := exists_mul_of_stab h h'
  rw [hb, hb, hs]
  ring

end Transfer

/-! ### Points under an equality of curves -/

section PtCast

variable {R : Type*} [Field R] [DecidableEq R]

/-- `W(R) ≃ W'(R)` for `W = W'`. -/
def ptCast {W W' : WeierstrassCurve R} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point :=
  h ▸ AddEquiv.refl _

lemma ptCast_some {W W' : WeierstrassCurve R} (h : W = W') {x y : R}
    (hn : W.toAffine.Nonsingular x y) (hn' : W'.toAffine.Nonsingular x y) :
    ptCast h (.some x y hn) = .some x y hn' := by
  subst h
  rfl

end PtCast

/-! ### Semilinear automorphisms of `Ω = k(E)^alg` -/

section Tau

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]

variable (E) in
/-- **`τ : Ω ≃ Ω` is semilinear over `θ : k ≃ k` and fixes `x`, `y`.** -/
def IsSemilin (θ : k ≃+* k) (τ : Ω E ≃+* Ω E) : Prop :=
  (∀ c : k, τ (algebraMap k (Ω E) c) = algebraMap k (Ω E) (θ c)) ∧ τ (xG E) = xG E ∧
    τ (yG E) = yG E

/-- **A semilinear automorphism of `Ω` over `θ` fixing `x`, `y` exists** when `E` is defined over
the fixed field of `θ` (`E.map θ = E`; `mapOmegaEquiv`). -/
theorem exists_isSemilin (θ : k ≃+* k) (hE : E.map (θ : k →+* k) = E) :
    ∃ τ, IsSemilin E θ τ := by
  suffices h : ∀ E' : WeierstrassCurve k, mapE θ E = E' → ∃ φ : Ω E ≃+* Ω E',
      (∀ c : k, φ (algebraMap k (Ω E) c) = algebraMap k (Ω E') (θ c)) ∧ φ (xG E) = xG E' ∧
        φ (yG E) = yG E' from h E hE
  rintro E' rfl
  exact ⟨mapOmegaEquiv θ E, mapOmegaEquiv_algebraMap θ E, mapOmegaEquiv_xG θ E,
    mapOmegaEquiv_yG θ E⟩

variable {θ : k ≃+* k} {τ : Ω E ≃+* Ω E} (hτ : IsSemilin E θ τ)

include hτ in
lemma tau_symm_algebraMap (c : k) :
    τ.symm (algebraMap k (Ω E) c) = algebraMap k (Ω E) (θ.symm c) := by
  rw [RingEquiv.symm_apply_eq, hτ.1, RingEquiv.apply_symm_apply]

include hτ in
lemma tau_symm_xG : τ.symm (xG E) = xG E := by
  rw [RingEquiv.symm_apply_eq, hτ.2.1]

include hτ in
lemma tau_symm_yG : τ.symm (yG E) = yG E := by
  rw [RingEquiv.symm_apply_eq, hτ.2.2]

include hτ in
/-- `τ(k(x)) = k(x)`. -/
lemma map_K₀_tau : (AffOrbicurve.K₀ k (xG E)).toSubfield.map τ.toRingHom =
    (AffOrbicurve.K₀ k (xG E)).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, RingHom.map_field_closure]
  congr 1
  ext y
  simp only [Set.image_union, Set.image_singleton, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro (⟨_, ⟨c, rfl⟩, rfl⟩ | rfl)
    · exact Or.inl ⟨θ c, (hτ.1 c).symm⟩
    · exact Or.inr hτ.2.1
  · rintro (⟨c, rfl⟩ | rfl)
    · exact Or.inl ⟨_, ⟨θ.symm c, rfl⟩, by
        rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hτ.1, RingEquiv.apply_symm_apply]⟩
    · exact Or.inr hτ.2.1.symm

include hτ in
/-- `τ` maps `k(x)` onto `k(x)`. -/
lemma tau_mem_range (z : Ω E) :
    z ∈ (algebraMap (baseField E) (Ω E)).range ↔
      τ z ∈ (algebraMap (baseField E) (Ω E)).range := by
  have h1 : ∀ z : Ω E, z ∈ (algebraMap (baseField E) (Ω E)).range ↔ z ∈ baseField E :=
    fun z => ⟨by rintro ⟨c, rfl⟩; exact c.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  rw [h1, h1, hbase E, ← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield]
  conv_rhs => rw [← map_K₀_tau hτ]
  rw [Subfield.mem_map]
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    rwa [τ.injective hyz] at hy

/-- **Conjugation by `τ`** on `Gal(Ω / k(x))`. -/
def psi : Gal E ≃ₜ* Gal E := galConj τ (tau_mem_range hτ)

lemma psi_apply' (σ : Gal E) (z : Ω E) : psi hτ σ (τ z) = τ (σ z) :=
  galConj_apply' _ _ σ z

/-- **`τ` preserves the inertia generators of `C = (E ∖ {O})/{±1}`.** -/
lemma mem_SgenC_psi_iff (σ : Gal E) : σ ∈ SgenC E 1 ⊥ ↔ psi hτ σ ∈ SgenC E 1 ⊥ := by
  rw [SgenC_of_charZero, Sgen_eq_S0]
  change (act E σ (Genuine.genericPoint E) = Genuine.genericPoint E ∧ _) ↔
    (act E _ (Genuine.genericPoint E) = Genuine.genericPoint E ∧ _)
  rw [act_generic_eq_iff_yG, act_generic_eq_iff_yG]
  have hy : psi hτ σ (yG E) = yG E ↔ σ (yG E) = yG E := by
    have e : psi hτ σ (yG E) = τ (σ (yG E)) := by
      conv_lhs => rw [← hτ.2.2]
      exact psi_apply' hτ σ _
    rw [e]
    constructor
    · intro h
      exact τ.injective (h.trans hτ.2.2.symm)
    · intro h
      rw [h, hτ.2.2]
  rw [hy]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨W, hk, hx, hσ⟩
    refine ⟨W.comap τ.symm.toRingHom, fun c => ?_, ?_, ?_⟩
    · rw [ValuationSubring.mem_comap]
      simpa [tau_symm_algebraMap hτ] using hk (θ.symm c)
    · rw [ValuationSubring.mem_comap]
      simpa [tau_symm_xG hτ] using hx
    · exact (galConj_mem_inertia_iff _ _ σ W).2 hσ
  · rintro ⟨W', hk, hx, hσ⟩
    let W := W'.comap τ.toRingHom
    have hW : W.comap τ.symm.toRingHom = W' := by
      ext z
      simp [W, ValuationSubring.mem_comap]
    refine ⟨W, fun c => ?_, ?_, ?_⟩
    · simpa [W, ValuationSubring.mem_comap, hτ.1] using hk (θ c)
    · simpa [W, ValuationSubring.mem_comap, hτ.2.1] using hx
    · rw [← galConj_mem_inertia_iff τ (tau_mem_range hτ) σ W]
      change psi hτ σ ∈ _
      rw [hW]
      exact hσ

/-- **The automorphism of `π₁(C)` induced by `τ`** (`C = (E ∖ {O})/{±1}`). -/
def betaC : pi1C E 1 ⊥ true ≃ₜ* pi1C E 1 ⊥ true :=
  pi1Congr (psi hτ) (isClosed_Hgp E 1 ⊥ true) (isClosed_Hgp E 1 ⊥ true)
    (fun σ => iff_of_true (mem_Hgp_one_bot_true E σ) (mem_Hgp_one_bot_true E _))
    (mem_SgenC_psi_iff hτ)

lemma betaC_mk (h : Hgp E 1 ⊥ true) :
    betaC hτ (QuotientGroup.mk h : Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _) =
      (QuotientGroup.mk ⟨psi hτ h, mem_Hgp_one_bot_true E _⟩ :
        Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _) := rfl

/-! #### The action of `τ` on `E(Ω)` -/

variable (hE : E.map (θ : k →+* k) = E)

include hτ hE in
/-- `E_Ω` is defined over the fixed field of `τ`. -/
lemma map_baseChange_tau : (E⁄(Ω E)).map (τ : Ω E →+* Ω E) = E⁄(Ω E) := by
  have hc : ∀ a : k, θ a = a → τ (algebraMap k (Ω E) a) = algebraMap k (Ω E) a := fun a ha => by
    rw [hτ.1, ha]
  ext
  · exact hc _ (congrArg WeierstrassCurve.a₁ hE)
  · exact hc _ (congrArg WeierstrassCurve.a₂ hE)
  · exact hc _ (congrArg WeierstrassCurve.a₃ hE)
  · exact hc _ (congrArg WeierstrassCurve.a₄ hE)
  · exact hc _ (congrArg WeierstrassCurve.a₆ hE)

include hτ hE in
lemma nonsingular_tau {x y : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular x y) :
    (E⁄(Ω E)).toAffine.Nonsingular (τ x) (τ y) := by
  have h2 : ((E⁄(Ω E)).map (τ : Ω E →+* Ω E)).toAffine.Nonsingular (τ x) (τ y) :=
    ((E⁄(Ω E)).toAffine.map_nonsingular (f := (τ : Ω E →+* Ω E)) τ.injective x y).2 h
  rwa [map_baseChange_tau hτ hE] at h2

/-- **The action of `τ` on `E(Ω)`.** -/
def tauPt : Pt E →+ Pt E :=
  (ptCast (map_baseChange_tau hτ hE)).toAddMonoidHom.comp
    (pointMap (E⁄(Ω E)) (τ : Ω E →+* Ω E))

lemma tauPt_some {x y : Ω E} (h : (E⁄(Ω E)).toAffine.Nonsingular x y) :
    tauPt hτ hE (.some x y h) = .some (τ x) (τ y) (nonsingular_tau hτ hE h) := by
  unfold tauPt
  rw [AddMonoidHom.comp_apply, pointMap_some]
  exact ptCast_some _ _ _

lemma some_congr {x y x' y' : Ω E} (hx : x = x') (hy : y = y')
    (h : (E⁄(Ω E)).toAffine.Nonsingular x y) (h' : (E⁄(Ω E)).toAffine.Nonsingular x' y') :
    (WeierstrassCurve.Affine.Point.some x y h : Pt E) = .some x' y' h' := by
  subst hx hy
  rfl

/-- **`τ σ τ⁻¹` acts on `τ(P)` as `σ` on `P`.** -/
lemma act_psi_tauPt (σ : Gal E) (P : Pt E) :
    act E (psi hτ σ) (tauPt hτ hE P) = tauPt hτ hE (act E σ P) := by
  cases P with
  | zero => simp only [show (Affine.Point.zero : Pt E) = 0 from rfl, map_zero]
  | some x y h =>
    have hσ : (E⁄(Ω E)).toAffine.Nonsingular (σ x) (σ y) :=
      ((E.toAffine.baseChange_nonsingular (σk E σ).injective x y).2 h)
    rw [tauPt_some, act_some E (psi hτ σ) (nonsingular_tau hτ hE h) (by
      rw [psi_apply', psi_apply']; exact nonsingular_tau hτ hE hσ),
      act_some E σ h hσ, tauPt_some]
    exact some_congr (psi_apply' hτ σ x) (psi_apply' hτ σ y) _ _

/-- `τ` fixes the generic point. -/
lemma tauPt_genericPoint : tauPt hτ hE (genericPoint E) = genericPoint E := by
  change tauPt hτ hE (.some (xG E) (yG E) (nonsingular_generic E)) = _
  rw [tauPt_some]
  exact some_congr hτ.2.1 hτ.2.2 _ _

/-- **`τ` on `k`-rational points** is the action `f` of `θ` on `E(k)`. -/
lemma tauPt_base (f : E.toAffine.Point →+ E.toAffine.Point)
    (hf : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ h',
      f (.some x y h) = .some (θ x) (θ y) h') (T : E.toAffine.Point) :
    tauPt hτ hE (base E T) = base E (f T) := by
  cases T with
  | zero =>
    simp only [show (Affine.Point.zero : E.toAffine.Point) = 0 from rfl, map_zero]
  | some x y h =>
    obtain ⟨h', hf'⟩ := hf x y h
    rw [hf']
    change tauPt hτ hE (.some (algebraMap k (Ω E) x) (algebraMap k (Ω E) y) _) =
      .some (algebraMap k (Ω E) (θ x)) (algebraMap k (Ω E) (θ y)) _
    rw [tauPt_some]
    exact some_congr (hτ.1 x) (hτ.1 y) _ _

/-! #### The sign and translation of `τ σ τ⁻¹` -/

variable {ℓ : ℕ} [OddPrime ℓ] (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2)

include hcard in
/-- `τ(Q_ℓ) = Q_ℓ + T` with `T ∈ E(k)[ℓ]`. -/
lemma exists_tauPt_Qpt : ∃ T : Tor E ℓ, tauPt hτ hE (Qpt E ℓ) = Qpt E ℓ + base E T := by
  have hD : ℓ • (tauPt hτ hE (Qpt E ℓ) - Qpt E ℓ) = 0 := by
    rw [nsmul_sub, ← map_nsmul, GenuineBaseChange.nsmul_Qpt E ell_ne_zero, tauPt_genericPoint,
      sub_self]
  obtain ⟨T, hT⟩ := exists_base_of_nsmul E ell_ne_zero hcard hD
  have hTt : ℓ • T = 0 := by
    apply pointMap_injective E (algebraMap k (Ω E))
    change base E (ℓ • T) = base E 0
    rw [map_nsmul, hT, hD, map_zero]
  exact ⟨⟨T, mem_tor.2 hTt⟩, by rw [hT]; abel⟩

variable (f : E.toAffine.Point →+ E.toAffine.Point)
  (hf : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ h',
      f (.some x y h) = .some (θ x) (θ y) h')

/-- `f` on `E(k)[ℓ]`. -/
def fTor : Tor E ℓ →+ Tor E ℓ :=
  (f.comp (Tor E ℓ).subtype).codRestrict _ fun S => mem_tor.2 (by
    rw [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← map_nsmul, mem_tor.1 S.2,
      map_zero])

lemma coe_fTor (S : Tor E ℓ) : (fTor f S : E.toAffine.Point) = f S := rfl

include hf in
/-- **`τ σ τ⁻¹(Q_ℓ) = ε Q_ℓ + (f(S) + ε T − T)`** for `σ(Q_ℓ) = ε Q_ℓ + S`. -/
lemma sgnTr_psi (σ : Gal E) {T : Tor E ℓ} (hT : tauPt hτ hE (Qpt E ℓ) = Qpt E ℓ + base E T) :
    sgnTr hcard (psi hτ σ) = ((sgnTr hcard σ).1,
      fTor f (sgnTr hcard σ).2 + ((sgnTr hcard σ).1 : ℤ) • T - T) := by
  apply sgnTr_eq
  have key := act_psi_tauPt hτ hE σ (Qpt E ℓ)
  rw [hT, map_add, act_base, sgnTr_spec hcard σ, map_add, map_zsmul, hT,
    tauPt_base hτ hE f hf] at key
  rw [eq_sub_of_add_eq key]
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, coe_fTor, map_sub,
    map_add, map_zsmul]
  module

variable (M : AddSubgroup E.toAffine.Point) (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ)

lemma qOf_sub (S T : Tor E ℓ) : qOf M e (S - T) = qOf M e S - qOf M e T := by
  simp [qOf]

variable (s : (ZMod ℓ)ˣ) (hM : ∀ S : E.toAffine.Point, ℓ • S = 0 → f S - (s : ZMod ℓ).val • S ∈ M)

include hM in
lemma qOf_fTor (S : Tor E ℓ) : qOf M e (fTor f S) = s * qOf M e S := by
  have h0 : qOf M e (fTor f S - (s : ZMod ℓ).val • S) = 0 := by
    rw [qOf_eq_zero_iff]
    simpa [coe_fTor] using hM S (mem_tor.1 S.2)
  rw [qOf_sub, ← natCast_zsmul, qOf_zsmul, Int.cast_natCast, ZMod.natCast_zmod_val] at h0
  linear_combination h0

include hf hM in
/-- **`ρ(τ σ τ⁻¹) = A ρ(σ) A⁻¹`** for the affine map `A z = s z − c`, `c = [T]`. -/
theorem rhoGal_psi (σ : Gal E) {T : Tor E ℓ}
    (hT : tauPt hτ hE (Qpt E ℓ) = Qpt E ℓ + base E T) (z : ZMod ℓ) :
    rhoGal hcard M e (psi hτ σ) (s * z - qOf M e T) =
      s * rhoGal hcard M e σ z - qOf M e T := by
  rw [rhoGal_apply, rhoGal_apply, sgnTr_psi hτ hE hcard f hf σ hT]
  simp only
  rw [qOf_sub, qOf_add, qOf_zsmul, qOf_fTor f M e s hM]
  have h := sgn_mul_self (ℓ := ℓ) (sgnTr hcard σ).1
  simp only [sgn] at h ⊢
  linear_combination (-qOf M e T) * h

end Tau

/-! ### The automorphism `β` of `π₁(C)` -/

section Beta

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by `g`, as a continuous automorphism. -/
def conjCME (g : G) : G ≃ₜ* G where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by group
  right_inv x := by group
  map_mul' x y := by group
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma conjCME_apply (g x : G) : conjCME g x = g * x * g⁻¹ := rfl

variable {k : Type u} [Field k] [CharZero k] {E : WeierstrassCurve k} [E.IsElliptic]
  {ℓ : ℕ} [OddPrime ℓ]

/-- **A continuous automorphism of `π₁(C)` acting on `Q ≅ F_ℓ` by the scalar `s`**, given
`θ : k ≃ k` fixing the coefficients of `E` whose action `f` on `E(k)` stabilises `M` and acts on
`E(k)[ℓ]/M` by `s`. -/
theorem exists_beta (hcard : Nat.card (Tor E ℓ) = ℓ ^ 2) (M : AddSubgroup E.toAffine.Point)
    (e : Tor E ℓ ⧸ M.addSubgroupOf (Tor E ℓ) ≃+ ZMod ℓ) (θ : k ≃+* k)
    (hE : E.map (θ : k →+* k) = E) (f : E.toAffine.Point →+ E.toAffine.Point)
    (hf : ∀ (x y : k) (h : E.toAffine.Nonsingular x y), ∃ h',
      f (.some x y h) = .some (θ x) (θ y) h') (s : (ZMod ℓ)ˣ)
    (hM : ∀ S : E.toAffine.Point, ℓ • S = 0 → f S - (s : ZMod ℓ).val • S ∈ M) :
    ∃ β : pi1C E 1 ⊥ true ≃ₜ* pi1C E 1 ⊥ true,
      ∀ x, rhoC hcard M e (β x) 0 = s * rhoC hcard M e x 0 := by
  obtain ⟨τ, hτ⟩ := exists_isSemilin θ hE
  obtain ⟨T, hT⟩ := exists_tauPt_Qpt hτ hE hcard
  set c := qOf M e T
  obtain ⟨σ₁, hσ₁⟩ := exists_rhoGal_translation hcard M e
  let y₀ : pi1C E 1 ⊥ true := (QuotientGroup.mk ⟨σ₁ ^ c.val, mem_Hgp_one_bot E _⟩ :
    Hgp E 1 ⊥ true ⧸ GaloisPi1.kernel _ _)
  have hy₀ : rhoC hcard M e y₀ = affPerm ℓ 1 c := by
    change rhoGal hcard M e (σ₁ ^ c.val) = _
    rw [map_pow, hσ₁, affPerm_one_pow, ZMod.natCast_zmod_val]
  have hy₀' : (rhoC hcard M e y₀)⁻¹ 0 = -c := by
    rw [Equiv.Perm.inv_eq_iff_eq, hy₀, affPerm_apply, sgn_one]
    ring
  refine ⟨(betaC hτ).trans (conjCME y₀), fun x => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have e1 : rhoC hcard M e (betaC hτ (QuotientGroup.mk h)) (-c) =
      s * rhoC hcard M e (QuotientGroup.mk h) 0 - c := by
    rw [betaC_mk]
    change rhoGal hcard M e (psi hτ h) (-c) = s * rhoGal hcard M e h 0 - c
    have := rhoGal_psi hτ hE hcard f hf M e s hM (h : Gal E) hT 0
    rwa [mul_zero, zero_sub] at this
  change rhoC hcard M e (y₀ * betaC hτ (QuotientGroup.mk h) * y₀⁻¹) 0 =
    s * rhoC hcard M e (QuotientGroup.mk h) 0
  rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hy₀', e1, hy₀,
    affPerm_apply, sgn_one]
  ring

end Beta

/-! ### Model orbicurves -/

section Cover

variable {k : Type u} [Field k] [CharZero k] {ℓ : ℕ} [OddPrime ℓ]

/-- **A semilinear automorphism of `π₁(C)` for a covering `C̲ → C`** of model orbicurves
(`C̲` of type `(1, ℓ-tors)^±`, `C = (E ∖ {0})/{±1}`): given `θ : k ≃ k` fixing the coefficients of
`E` whose action `f` on `E(k)` stabilises `M` and acts on `E(k)[ℓ]/M` by `s`, there is a continuous
automorphism `β` of `π₁(C)` with `ρ(β x)(0) = s · ρ(x)(0)` for every dihedral action `ρ` of
`π₁(C)` on `F_ℓ` with stabiliser of `0` the image of `π₁(C̲)`. -/
theorem exists_semilin_of_cover {X Y : Orbicurve k} (c : Orbicurve.Cover X Y)
    (hX : X.IsTypeOneEllTorsPM ℓ) (hY1 : Y.level = 1) (hY2 : Y.M = ⊥) (hY3 : Y.pm = true)
    (e : X.Q ≃+ ZMod ℓ) (θ : k ≃+* k) (hE : X.E.map (θ : k →+* k) = X.E)
    (f : X.E.toAffine.Point →+ X.E.toAffine.Point)
    (hf : ∀ (x y : k) (h : X.E.toAffine.Nonsingular x y), ∃ h',
      f (.some x y h) = .some (θ x) (θ y) h') (s : (ZMod ℓ)ˣ)
    (hM : ∀ S : X.E.toAffine.Point, ℓ • S = 0 → f S - (s : ZMod ℓ).val • S ∈ X.M) :
    ∃ β : Y.genuinePi1 ≃ₜ* Y.genuinePi1, ∀ ρ : Y.genuinePi1 →* Equiv.Perm (ZMod ℓ),
      IsDihedralQuot ρ (genuinePi1Cover c).range → ∀ x, ρ (β x) 0 = s * ρ x 0 := by
  cases X with | @mk E hEl ℓX M pm =>
  cases Y with | @mk E' hE' ℓY M' pm' =>
  obtain ⟨h, n, hn, hmul, hM', hpm⟩ := c
  change E = E' at h
  subst h
  change ℓY = 1 at hY1
  change M' = ⊥ at hY2
  change pm' = true at hY3
  subst ℓY M' pm'
  obtain ⟨-, hl, hpmX, hMT, -, hcard⟩ := hX
  change ℓX = ℓ at hl
  change pm = true at hpmX
  subst ℓX pm
  obtain ⟨β, hβ⟩ := exists_beta hcard M e θ hE f hf s hM
  exact ⟨β, fun ρ hρ x => scalar_transfer (isDihedralQuot_rhoC hcard M e hMT) hρ hβ x⟩

end Cover

/-! ### The Borel subgroup of `SL₂(F_ℓ)` (IUT I, Definition 3.1 (c)) -/

section Borel

/-- The classical decidable equality on an intermediate field (as used by the model orbicurves
and by `Iut.AdmissiblePrimeData.EK`). -/
local instance (priority := high) decEqIntermediateField {F Fbar : Type*} [Field F] [Field Fbar]
    [Algebra F Fbar] (K : IntermediateField F Fbar) : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

/-- **The Borel subgroup of `SL₂(F_ℓ)` stabilising a line `F_ℓ m` realises every scalar on the
quotient**: `A v − s v ∈ F_ℓ m` for all `v`. -/
theorem exists_borel_matrix {ℓ : ℕ} [Fact ℓ.Prime] (m : Fin 2 → ZMod ℓ) (hm : m ≠ 0)
    (s : (ZMod ℓ)ˣ) : ∃ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), ∀ v,
      ∃ a : ZMod ℓ, (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec v - (s : ZMod ℓ) • v = a • m := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 2 → ZMod ℓ, m 0 * φ 0 + m 1 * φ 1 = 1 := by
    by_cases h0 : m 0 = 0
    · have h1 : m 1 ≠ 0 := fun h1 => hm (funext fun i => by fin_cases i <;> simp [h0, h1])
      exact ⟨![0, (m 1)⁻¹], by simp [mul_inv_cancel₀ h1]⟩
    · exact ⟨![(m 0)⁻¹, 0], by simp [mul_inv_cancel₀ h0]⟩
  set c : ZMod ℓ := ((s⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ) - s
  have hs : (s : ZMod ℓ) * ((s⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let A : Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    !![s + c * m 0 * φ 0, c * m 0 * φ 1; c * m 1 * φ 0, s + c * m 1 * φ 1]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two_of]
    have : (s : ZMod ℓ) * s + s * c * (m 0 * φ 0 + m 1 * φ 1) = 1 := by
      rw [hφ]
      simp only [c]
      linear_combination hs
    linear_combination this
  refine ⟨⟨A, hdet⟩, fun v => ⟨c * (φ 0 * v 0 + φ 1 * v 1), ?_⟩⟩
  ext i
  fin_cases i <;>
    simp [A, dotProduct, Fin.sum_univ_two] <;> ring

open Iut.AdmissiblePrimeData NumberField in
/-- **IUT I, Definition 3.1 (c)**: for a line `M ⊆ E(K)[ℓ]` and `s ∈ F_ℓ^×` there is
`σ ∈ Gal(F̄/F)` (with `ρ(σ)` in the Borel subgroup of `SL₂(F_ℓ)` stabilising `M`) acting on
`E(K)[ℓ]` with `σ(S) − s S ∈ M`. -/
theorem exists_borel {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F}
    [E.IsElliptic] {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} (P : Iut.AdmissiblePrimeData F E Fbar VBad)
    (M : AddSubgroup P.EK.toAffine.Point) (hMT : M ≤ P.TK) (hMc : Nat.card M = P.ℓ)
    (s : (ZMod P.ℓ)ˣ) : ∃ σ : Fbar ≃ₐ[F] Fbar, ∀ S ∈ P.TK,
      P.galK (P.restrictK σ) S - (s : ZMod P.ℓ).val • S ∈ M := by
  haveI : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩
  obtain ⟨m₀, hm₀, hm₀0⟩ : ∃ m₀ ∈ M, m₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : M = ⊥ := (AddSubgroup.eq_bot_iff_forall M).2 hcon
    rw [hbot, AddSubgroup.card_bot] at hMc
    exact P.ℓ_prime.one_lt.ne hMc
  let m : P.TK := ⟨m₀, hMT hm₀⟩
  have hm : P.basisK m ≠ 0 := fun h => hm₀0 (by
    have := P.basisK.injective (h.trans (map_zero _).symm)
    exact congrArg Subtype.val this)
  obtain ⟨A, hA⟩ := exists_borel_matrix (P.basisK m) hm s
  obtain ⟨σ, hσ⟩ := P.sl_le_range A
  refine ⟨σ, fun S hS => ?_⟩
  obtain ⟨a, ha⟩ := hA (P.basisK ⟨S, hS⟩)
  have key : P.galTK (P.restrictK σ) ⟨S, hS⟩ - (s : ZMod P.ℓ).val • ⟨S, hS⟩ = a.val • m := by
    apply P.basisK.injective
    rw [map_sub, map_nsmul, map_nsmul, basisK_galTK, hσ, ← Nat.cast_smul_eq_nsmul (ZMod P.ℓ),
      ← Nat.cast_smul_eq_nsmul (ZMod P.ℓ), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact ha
  have := congrArg Subtype.val key
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_nsmul, coe_galTK] at this
  rw [this]
  exact AddSubgroup.nsmul_mem _ hm₀ _

open Iut.AdmissiblePrimeData NumberField in
/-- **The semilinear data for `C̲_K`**: for a curve `W = E_K` over the torsion field, a line
`M ⊆ W(K)[ℓ]` and `s ∈ F_ℓ^×`, an automorphism `θ` of `K` (restriction of some `σ ∈ Gal(F̄/F)`)
fixing the coefficients of `W`, whose action `f` on `W(K)` stabilises `M` and acts on
`W(K)[ℓ]/M` by `s`. -/
theorem exists_semilin_data {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F}
    [E.IsElliptic] {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} (P : Iut.AdmissiblePrimeData F E Fbar VBad)
    (W : WeierstrassCurve ↥P.torsionField) (hW : W = P.EK) (M : AddSubgroup W.toAffine.Point)
    (hMT : M ≤ AddSubgroup.torsionBy W.toAffine.Point P.ℓ) (hMc : Nat.card M = P.ℓ)
    (s : (ZMod P.ℓ)ˣ) : ∃ θ : ↥P.torsionField ≃+* ↥P.torsionField,
      ∃ _ : W.map (θ : ↥P.torsionField →+* ↥P.torsionField) = W,
      ∃ f : W.toAffine.Point →+ W.toAffine.Point,
        (∀ (x y : ↥P.torsionField) (h : W.toAffine.Nonsingular x y), ∃ h',
          f (.some x y h) = .some (θ x) (θ y) h') ∧
        ∀ S : W.toAffine.Point, P.ℓ • S = 0 → f S - (s : ZMod P.ℓ).val • S ∈ M := by
  subst hW
  obtain ⟨σ, hσ⟩ := exists_borel P M hMT hMc s
  refine ⟨(P.restrictK σ).toRingEquiv, ?_, P.galK (P.restrictK σ), fun x y h => ⟨_, rfl⟩,
    fun S hS => hσ S (AddSubgroup.torsionBy.nsmul_iff.2 hS)⟩
  have hc : ∀ a : F, (P.restrictK σ) (algebraMap F ↥P.torsionField a) =
      algebraMap F ↥P.torsionField a := fun a => (P.restrictK σ).commutes a
  ext : 1
  · exact hc _
  · exact hc _
  · exact hc _
  · exact hc _
  · exact hc _

end Borel

end Iut.Multiradial.Theater
