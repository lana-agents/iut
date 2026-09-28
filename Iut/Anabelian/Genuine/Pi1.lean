/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Basic
import Iut.Torsion.Divisible

/-!
# The étale fundamental groups of the model orbicurves

Fix an elliptic curve `E / k` and the ambient data of `Iut.Anabelian.Genuine.Basic`: an algebraic
closure `Ω` of `k(E)`, the generic point `G ∈ E(Ω)`, the perfect closure `P` of `k(x)` and
`Gal E = Gal(Ω / P)` (the automorphisms of `Ω` over `k(x)`).

## Function fields of the model orbicurves

Choose a compatible system of division points of the generic point: `Q_ℓ ∈ E(Ω)` with
`ℓ Q_ℓ = G` and `n Q_{nℓ} = Q_ℓ` (`divSys`; it exists because `E(Ω)` is divisible, which is
proved here in characteristic `0`, `compatible_divSys`). The model orbicurve
`X = (E, ℓ, M, ±)` is `X_M = (E/M) ∖ (E[ℓ]/M)` (or its quotient stack by `{±1}`), where
`M ⊆ E(k)[ℓ]`. The map `E ∖ E[ℓ] → E ∖ {0}` induced by `[ℓ]` identifies the function field of
`E ∖ E[ℓ]` with `k(Q_ℓ) ⊆ Ω` (the generic point of the source maps to `Q_ℓ`), the translations
by `T ∈ M` act on it by `Q_ℓ ↦ Q_ℓ + T`, `[-1]` by `Q_ℓ ↦ -Q_ℓ`, and the function field of `X_M`
is `L_X = k(Q_ℓ)^M`, that of the coarse space of `X_M / {±1}` is `F_X = k(Q_ℓ)^{⟨M, ±1⟩}`.
By Galois theory, the automorphism groups `Aut(Ω / L_X) ⊆ Aut(Ω / F_X) ⊆ Gal(Ω / k(x))` are

* `geomGroup E ℓ M = {σ | σ(Q_ℓ) − Q_ℓ ∈ M}` (the automorphisms fixing `L_X`),
* `Hgp E ℓ M pm = {σ | σ(Q_ℓ) ∓ Q_ℓ ∈ M}` (signs `−` only when `pm` is set; the automorphisms
  fixing `F_X`).

(`M` is intersected with `E(k)[ℓ]`; the degenerate level `ℓ = 0` is replaced by `ℓ = 1`.)

## The fundamental groups

The places of `L_X` centered on `X_M` are those whose valuation ring contains `k` and `x`
(`X_M` is the normalization of the `x`-line `A¹` in `L_X`: `X_M → E ∖ {0} → A¹` is finite and
the cusps `E[ℓ]/M` are exactly the points over `x = ∞`). Their inertia groups are the inertia
groups `GaloisPi1.inertia W` of the valuation subrings `W ⊆ Ω` with `k ⊆ W`, `x ∈ W`,
intersected with `Aut(Ω / L_X)` (`Sgen E ℓ M`). Hence (`GaloisPi1`)

  `π₁(X_M) = Aut(Ω / L_X) ⧸ ⟨⟨inertia over X_M⟩⟩ = Gal(Ω_X / L_X)`,
  `π₁([X_M / {±1}]) = Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩ = Gal(Ω_X / F_X)`,

with `Ω_X` the maximal extension of `L_X` unramified over `X_M` (the arithmetic étale
fundamental group of `X_M`, resp. of the quotient stack: the Galois category of
`{±1}`-equivariant finite étale covers of `X_M`). This is `pi1Of E ℓ M pm`.
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial

open scoped Classical

noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The points of `E` over `Ω`. -/
abbrev Pt : Type u := (E⁄(Ω E)).toAffine.Point

/-! ### Division points of the generic point -/

/-- A **compatible system of division points** of the generic point: `Q₁ = G` and
`n Q_{nℓ} = Q_ℓ`. -/
def Compatible (Q : ℕ → Pt E) : Prop :=
  Q 1 = genericPoint E ∧ ∀ n ℓ : ℕ, 0 < n → 0 < ℓ → n • Q (n * ℓ) = Q ℓ

/-- **The chosen compatible system of division points** of the generic point (one exists
since `E(Ω)` is divisible; see `compatible_divSys`). -/
def divSys : ℕ → Pt E :=
  if h : ∃ Q, Compatible E Q then h.choose else fun _ => genericPoint E

lemma exists_compatible (hdiv : ∀ n : ℕ, 0 < n → ∀ Q : Pt E, ∃ R : Pt E, n • R = Q) :
    ∃ Q, Compatible E Q := by
  -- `R m` with `(m + 1) • R (m + 1) = R m`, `R 0 = G`
  let R : ℕ → Pt E := fun m => Nat.rec (genericPoint E)
    (fun m Rm => (hdiv (m + 1) m.succ_pos Rm).choose) m
  have hR : ∀ m, (m + 1) • R (m + 1) = R m := fun m =>
    (hdiv (m + 1) m.succ_pos (R m)).choose_spec
  have hasc : ∀ b d, (b + 1).ascFactorial d • R (b + d) = R b := by
    intro b d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.ascFactorial_succ, mul_comm, mul_smul, ← add_assoc,
        show b + 1 + d = b + d + 1 by omega, hR, ih]
  have hfac : ∀ m, m.factorial • R m = genericPoint E := by
    intro m
    have := hasc 0 m
    simp only [zero_add, Nat.one_ascFactorial] at this
    exact this
  refine ⟨fun ℓ => (ℓ - 1).factorial • R ℓ, ?_, ?_⟩
  · simp only [Nat.sub_self, Nat.factorial_zero, one_smul]
    simpa using hfac 1
  · intro n ℓ hn hℓ
    simp only
    have hle : ℓ ≤ n * ℓ := Nat.le_mul_of_pos_left ℓ hn
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have key : n * (n * ℓ - 1).factorial = (ℓ - 1).factorial * (ℓ + 1).ascFactorial d := by
      have h1 := Nat.factorial_mul_ascFactorial ℓ d
      rw [← hd] at h1
      have h2 : (n * ℓ).factorial = n * ℓ * (n * ℓ - 1).factorial := by
        rw [← Nat.mul_factorial_pred (Nat.mul_pos hn hℓ).ne']
      have h3 : ℓ.factorial = ℓ * (ℓ - 1).factorial := by
        rw [← Nat.mul_factorial_pred hℓ.ne']
      rw [h2, h3] at h1
      have : ℓ * (n * (n * ℓ - 1).factorial) =
          ℓ * ((ℓ - 1).factorial * (ℓ + 1).ascFactorial d) :=
        calc ℓ * (n * (n * ℓ - 1).factorial) = n * ℓ * (n * ℓ - 1).factorial := by ring
          _ = ℓ * (ℓ - 1).factorial * (ℓ + 1).ascFactorial d := h1.symm
          _ = ℓ * ((ℓ - 1).factorial * (ℓ + 1).ascFactorial d) := by ring
      exact Nat.eq_of_mul_eq_mul_left hℓ this
    rw [smul_smul, key, mul_smul, hd, hasc]

lemma compatible_divSys (hdiv : ∀ n : ℕ, 0 < n → ∀ Q : Pt E, ∃ R : Pt E, n • R = Q) :
    Compatible E (divSys E) := by
  have h := exists_compatible E hdiv
  rw [divSys, dif_pos h]
  exact h.choose_spec

instance [CharZero k] : CharZero (Ω E) :=
  charZero_of_injective_algebraMap (algebraMap k (Ω E)).injective

lemma divisible [CharZero k] (n : ℕ) (hn : 0 < n) (Q : Pt E) : ∃ R : Pt E, n • R = Q :=
  haveI : CharZero (Ω E) := charZero_of_injective_algebraMap (algebraMap k (Ω E)).injective
  Torsion.nsmul_surjective (E⁄(Ω E)) n hn.ne' Q

lemma compatible_divSys_of_charZero [CharZero k] : Compatible E (divSys E) :=
  compatible_divSys E (fun n hn Q => divisible E n hn Q)

/-! ### The subgroups `Aut(Ω / L_X)`, `Aut(Ω / F_X)` -/

/-- The effective level (the degenerate level `0` is replaced by `1`). -/
def effLevel (ℓ : ℕ) : ℕ := if ℓ = 0 then 1 else ℓ

lemma effLevel_pos (ℓ : ℕ) : 0 < effLevel ℓ := by
  unfold effLevel; split_ifs with h
  · exact one_pos
  · exact Nat.pos_of_ne_zero h

/-- The division point `Q_ℓ` at the effective level. -/
def Qpt (ℓ : ℕ) : Pt E := divSys E (effLevel ℓ)

/-- The subgroup `M ∩ E(k)[ℓ]`, as a subgroup of `E(Ω)`. -/
def Mbar (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : AddSubgroup (Pt E) :=
  (M ⊓ AddSubgroup.torsionBy E.toAffine.Point (effLevel ℓ)).map (base E)

/-- The admissible signs: `+1`, and `−1` when the `±`-flag is set. -/
def SignOK (pm : Bool) (ε : ℤ) : Prop := ε = 1 ∨ (pm = true ∧ ε = -1)

omit [E.IsElliptic] in
lemma act_mem_Mbar (σ : Gal E) {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {T : Pt E}
    (hT : T ∈ Mbar E ℓ M) : act E σ T = T := by
  obtain ⟨T', -, rfl⟩ := hT
  exact act_base E σ T'

/-- **`Aut(Ω / F_X)`** for `X = (E, ℓ, M, ±)`: the automorphisms `σ` with
`σ(Q_ℓ) = ±Q_ℓ + T`, `T ∈ M` (sign `−` only with the `±`-flag). -/
def Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) : Subgroup (Gal E) where
  carrier := {σ | ∃ ε : ℤ, SignOK pm ε ∧ act E σ (Qpt E ℓ) - ε • Qpt E ℓ ∈ Mbar E ℓ M}
  one_mem' := ⟨1, Or.inl rfl, by simp [act_one]⟩
  mul_mem' := by
    rintro σ τ ⟨ε, hε, hσ⟩ ⟨η, hη, hτ⟩
    refine ⟨ε * η, ?_, ?_⟩
    · rcases hε with rfl | ⟨hpm, rfl⟩ <;> rcases hη with rfl | ⟨hpm', rfl⟩ <;>
        simp_all [SignOK]
    · set T := act E σ (Qpt E ℓ) - ε • Qpt E ℓ
      set T' := act E τ (Qpt E ℓ) - η • Qpt E ℓ
      have hτQ : act E τ (Qpt E ℓ) = η • Qpt E ℓ + T' := by simp [T']
      have hσQ : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + T := by simp [T]
      have : act E (σ * τ) (Qpt E ℓ) - (ε * η) • Qpt E ℓ = η • T + T' := by
        rw [act_mul, hτQ, map_add, map_zsmul, hσQ, act_mem_Mbar E σ hτ]
        module
      rw [this]
      exact add_mem (zsmul_mem hσ η) hτ
  inv_mem' := by
    rintro σ ⟨ε, hε, hσ⟩
    refine ⟨ε, hε, ?_⟩
    set T := act E σ (Qpt E ℓ) - ε • Qpt E ℓ
    have hσQ : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + T := by simp [T]
    have hεε : ε * ε = 1 := by rcases hε with rfl | ⟨-, rfl⟩ <;> norm_num
    have h1 : Qpt E ℓ = act E σ⁻¹ (act E σ (Qpt E ℓ)) := by rw [← act_mul, inv_mul_cancel, act_one]
    have e : Qpt E ℓ = ε • act E σ⁻¹ (Qpt E ℓ) + T := by
      conv_lhs => rw [h1]
      rw [hσQ, map_add, map_zsmul, act_mem_Mbar E σ⁻¹ hσ]
    have : act E σ⁻¹ (Qpt E ℓ) - ε • Qpt E ℓ = -(ε • T) := by
      nth_rw 2 [e]
      simp only [zsmul_add, smul_smul, hεε, one_smul]
      abel
    rw [this]
    exact neg_mem (zsmul_mem hσ ε)


/-! ### Openness -/

/-- The subfield generated over `P` by the coordinates of `Q_ℓ`. -/
def QField (ℓ : ℕ) : IntermediateField (baseField E) (Ω E) :=
  IntermediateField.adjoin (baseField E) {ptX (Qpt E ℓ), ptY (Qpt E ℓ)}

instance (ℓ : ℕ) : FiniteDimensional (baseField E) (QField E ℓ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := baseField E) x).isIntegral)

omit [E.IsElliptic] in
lemma act_eq_self_of_fix (σ : Gal E) (Q : Pt E) (hx : σ (ptX Q) = ptX Q)
    (hy : σ (ptY Q) = ptY Q) : act E σ Q = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · change Affine.Point.some _ _ _ = _
    simp only [ptX, ptY] at hx hy
    congr 1

lemma QField_fixing_le (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (QField E ℓ).fixingSubgroup ≤ Hgp E ℓ M pm := by
  intro σ hσ
  have hfix : ∀ a ∈ ({ptX (Qpt E ℓ), ptY (Qpt E ℓ)} : Set (Ω E)), σ a = a := fun a ha =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ a
      (IntermediateField.subset_adjoin _ _ ha)
  refine ⟨1, Or.inl rfl, ?_⟩
  rw [act_eq_self_of_fix E σ _ (hfix _ (by simp)) (hfix _ (by simp)), one_smul, sub_self]
  exact zero_mem _

lemma isOpen_Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsOpen (Hgp E ℓ M pm : Set (Gal E)) :=
  Subgroup.isOpen_mono (QField_fixing_le E ℓ M pm) (QField E ℓ).fixingSubgroup_isOpen

lemma isClosed_Hgp (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsClosed (Hgp E ℓ M pm : Set (Gal E)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_Hgp E ℓ M pm)

/-! ### Inertia and the fundamental groups -/

/-- **The inertia generators of `X_M`**: the automorphisms of `Ω` over `L_X` (`σ(Q_ℓ) − Q_ℓ ∈ M`)
lying in the inertia group of a valuation subring `W ⊆ Ω` centered on `X_M` (`k ⊆ W`,
`x ∈ W`). -/
def Sgen (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) : Set (Gal E) :=
  {σ | act E σ (Qpt E ℓ) - Qpt E ℓ ∈ Mbar E ℓ M ∧ ∃ W : ValuationSubring (Ω E),
    (∀ c : k, algebraMap k (Ω E) c ∈ W) ∧ xG E ∈ W ∧ σ ∈ GaloisPi1.inertia W}

/-- **The arithmetic étale fundamental group of the model orbicurve `(E, ℓ, M, ±)`**:
`Aut(Ω / F_X) ⧸ ⟨⟨inertia over X_M⟩⟩`. -/
def pi1Of (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) : ProfiniteGrp.{u} :=
  GaloisPi1.pi1 (Hgp E ℓ M pm) (Sgen E ℓ M) (isClosed_Hgp E ℓ M pm)

/-! ### Covers -/

lemma Qpt_of_compatible (hc : Compatible E (divSys E)) {n ℓ ℓ' : ℕ} (hn : 0 < n)
    (hℓ : n * ℓ' = ℓ) (hℓ' : 0 < ℓ') : Qpt E ℓ' = n • Qpt E ℓ := by
  have hℓ0 : ℓ ≠ 0 := by subst hℓ; exact (Nat.mul_pos hn hℓ').ne'
  simp only [Qpt, effLevel, if_neg hℓ0, if_neg hℓ'.ne']
  rw [← hℓ, hc.2 n ℓ' hn hℓ']

omit [E.IsElliptic] in
lemma nsmul_mem_Mbar {n ℓ ℓ' : ℕ} (hℓ : n * ℓ' = ℓ) (hℓ' : 0 < ℓ')
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {T : Pt E}
    (hT : T ∈ Mbar E ℓ M) : n • T ∈ Mbar E ℓ' M' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_nsmul]; exact zero_mem _
  have hℓ0 : ℓ ≠ 0 := by subst hℓ; exact (Nat.mul_pos hn hℓ').ne'
  obtain ⟨T₀, ⟨hT₀M, hT₀t⟩, rfl⟩ := hT
  have e1 : effLevel ℓ = ℓ := if_neg hℓ0
  have e2 : effLevel ℓ' = ℓ' := if_neg hℓ'.ne'
  refine ⟨n • T₀, ⟨hM T₀ hT₀M, ?_⟩, map_nsmul _ _ _⟩
  rw [e1] at hT₀t
  rw [e2]
  have h1 := (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀t
  refine (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mpr ?_
  rw [smul_smul, mul_comm, hℓ, h1]

omit [E.IsElliptic] in
lemma Mbar_zero (M : AddSubgroup E.toAffine.Point) {T : Pt E} (hT : T ∈ Mbar E 0 M) : T = 0 := by
  obtain ⟨T₀, ⟨-, hT₀t⟩, rfl⟩ := hT
  have e : effLevel 0 = 1 := if_pos rfl
  rw [e] at hT₀t
  have h1 := (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀t
  rw [one_smul] at h1
  rw [h1, map_zero]

/-- The groups attached to a cover are nested (for a compatible system of division points). -/
theorem Hgp_le (hc : Compatible E (divSys E)) {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' := by
  rintro σ ⟨ε, hε, hσ⟩
  have hε' : SignOK pm' ε := by
    rcases hε with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨hpm h, h'⟩
  rcases Nat.eq_zero_or_pos ℓ' with rfl | hℓ'
  · have hℓ0 : ℓ = 0 := by simpa using hℓ.symm
    subst hℓ0
    refine ⟨ε, hε', ?_⟩
    rw [Mbar_zero E M hσ]
    exact zero_mem _
  · refine ⟨ε, hε', ?_⟩
    rw [Qpt_of_compatible E hc hn hℓ hℓ', map_nsmul]
    have e : n • act E σ (Qpt E ℓ) - ε • (n • Qpt E ℓ) =
        n • (act E σ (Qpt E ℓ) - ε • Qpt E ℓ) := by module
    rw [e]
    exact nsmul_mem_Mbar E hℓ hℓ' hM hσ

/-- The inertia generators attached to a cover are nested. -/
theorem Sgen_subset (hc : Compatible E (divSys E)) {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') :
    Sgen E ℓ M ⊆ Sgen E ℓ' M' := by
  rintro σ ⟨hσ, hW⟩
  refine ⟨?_, hW⟩
  rcases Nat.eq_zero_or_pos ℓ' with rfl | hℓ'
  · have hℓ0 : ℓ = 0 := by simpa using hℓ.symm
    subst hℓ0
    rw [Mbar_zero E M hσ]
    exact zero_mem _
  · rw [Qpt_of_compatible E hc hn hℓ hℓ', map_nsmul, ← nsmul_sub]
    exact nsmul_mem_Mbar E hℓ hℓ' hM hσ

/-- **The homomorphism of fundamental groups induced by a cover** `(E, ℓ, M, ±) → (E, ℓ', M', ±')`
(the map induced by `[n]`, `ℓ = n ℓ'`, `[n] M ⊆ M'`): induced by the inclusions
`Aut(Ω / F_X) ⊆ Aut(Ω / F_Y)` (the embeddings `F_Y ⊆ F_X` of function fields are compatible with
the chosen division points `Q_{ℓ'} = n Q_ℓ`). -/
def pi1MapOf {ℓ ℓ' : ℕ} {M M' : AddSubgroup E.toAffine.Point} {pm pm' : Bool} :
    pi1Of E ℓ M pm →* pi1Of E ℓ' M' pm' :=
  if h : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' ∧ Sgen E ℓ M ⊆ Sgen E ℓ' M' then
    GaloisPi1.pi1Map (isClosed_Hgp E ℓ M pm) (isClosed_Hgp E ℓ' M' pm') h.1 h.2
  else 1

lemma continuous_pi1MapOf {ℓ ℓ' : ℕ} {M M' : AddSubgroup E.toAffine.Point} {pm pm' : Bool} :
    Continuous (pi1MapOf E (ℓ := ℓ) (ℓ' := ℓ') (M := M) (M' := M') (pm := pm) (pm' := pm')) := by
  unfold pi1MapOf
  split_ifs with h
  · exact GaloisPi1.continuous_pi1Map _ _ _ _
  · exact continuous_const

end

end Iut.Anabelian.Genuine
