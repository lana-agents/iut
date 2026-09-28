/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Inertia

/-!
# Covers induce open embeddings of fundamental groups (characteristic `0`)

For a cover `X = (E, ℓ, M, ±) → Y = (E, ℓ', M', ±')` of model orbicurves, the induced map
`π₁(X) → π₁(Y)` is an open embedding. By `Iut.Anabelian.Genuine.inertia_fixes_division`, the
inertia generators of every model orbicurve over `E` are the same set `S0 E`: the automorphisms
of `Ω` fixing `k(E)` which lie in the inertia group of a place centered on `E ∖ {0}` — i.e. the
covers `X_M → E ∖ {0}` are étale, so a place of `L_X` over `X_M` is unramified over `E ∖ {0}`.
`S0 E` is stable under conjugation by `Aut(Ω / k(x))`-elements normalizing the generic point up
to sign, and `Aut(Ω / F_X)` is open in `Aut(Ω / F_Y)`, so `GaloisPi1.isOpenEmbedding_pi1Map'`
applies.
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial

open scoped Classical

noncomputable section

section Valuation

variable {K : Type u} [Field K] (W : ValuationSubring K)

lemma valuation_lt_one_iff_mem (z : K) :
    W.valuation z < 1 ↔ z ∈ W ∧ (z = 0 ∨ z⁻¹ ∉ W) := by
  by_cases hz : z = 0
  · subst hz; simp
  have hpos : 0 < W.valuation z := (Valuation.pos_iff _).mpr hz
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀, inv_le_one₀ hpos]
  simp only [hz, false_or, not_le]
  exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

/-- The inertia group of the conjugate valuation subring. -/
lemma conj_mem_inertia {P : Type u} [Field P] [Algebra P K] (h s : K ≃ₐ[P] K)
    (hs : s ∈ GaloisPi1.inertia W) :
    h * s * h⁻¹ ∈ GaloisPi1.inertia (W.comap (h⁻¹ : K ≃ₐ[P] K).toRingEquiv.toRingHom) := by
  intro a ha
  rw [ValuationSubring.mem_comap] at ha
  have key := hs _ ha
  rw [valuation_lt_one_iff_mem] at key ⊢
  have e : (h⁻¹ : K ≃ₐ[P] K).toRingEquiv.toRingHom ((h * s * h⁻¹) a - a) =
      s ((h⁻¹ : K ≃ₐ[P] K) a) - (h⁻¹ : K ≃ₐ[P] K) a := by
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
    change h⁻¹ (h (s (h⁻¹ a))) - h⁻¹ a = _
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine ⟨?_, ?_⟩
  · rw [ValuationSubring.mem_comap, e]; exact key.1
  · rcases key.2 with h0 | h0
    · left
      apply (h⁻¹ : K ≃ₐ[P] K).injective
      simpa [RingEquiv.toRingHom_eq_coe] using e.trans h0
    · right
      rw [ValuationSubring.mem_comap, map_inv₀, e]
      exact h0

end Valuation

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- **The inertia generators over `E ∖ {0}`**: the automorphisms of `Ω` fixing the generic point
and lying in the inertia group of a valuation subring `W ⊇ k` with `x ∈ W`. -/
def S0 : Set (Gal E) :=
  {σ | act E σ (genericPoint E) = genericPoint E ∧ ∃ W : ValuationSubring (Ω E),
    (∀ c : k, algebraMap k (Ω E) c ∈ W) ∧ xG E ∈ W ∧ σ ∈ GaloisPi1.inertia W}

lemma effLevel_smul_Qpt (hc : Compatible E (divSys E)) (ℓ : ℕ) :
    effLevel ℓ • Qpt E ℓ = genericPoint E := by
  have := hc.2 (effLevel ℓ) 1 (effLevel_pos ℓ) one_pos
  rw [mul_one, hc.1] at this
  exact this

omit [E.IsElliptic] in
lemma effLevel_smul_Mbar {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {T : Pt E}
    (hT : T ∈ Mbar E ℓ M) : effLevel ℓ • T = 0 := by
  obtain ⟨T₀, ⟨-, hT₀⟩, rfl⟩ := hT
  rw [← map_nsmul, (AddSubgroup.torsionBy.nsmul_iff (A := E.toAffine.Point)).mp hT₀, map_zero]

lemma act_generic_of_mem_Hgp (hc : Compatible E (divSys E)) {ℓ : ℕ}
    {M : AddSubgroup E.toAffine.Point} {pm : Bool} {σ : Gal E} (hσ : σ ∈ Hgp E ℓ M pm) :
    ∃ ε : ℤ, ε * ε = 1 ∧ act E σ (genericPoint E) = ε • genericPoint E := by
  obtain ⟨ε, hε, hT⟩ := hσ
  refine ⟨ε, by rcases hε with rfl | ⟨-, rfl⟩ <;> norm_num, ?_⟩
  rw [← effLevel_smul_Qpt E hc ℓ, map_nsmul]
  have : act E σ (Qpt E ℓ) = ε • Qpt E ℓ + (act E σ (Qpt E ℓ) - ε • Qpt E ℓ) := by abel
  rw [this]
  have e : effLevel ℓ • (ε • Qpt E ℓ + (act E σ (Qpt E ℓ) - ε • Qpt E ℓ)) =
      ε • (effLevel ℓ • Qpt E ℓ) + effLevel ℓ • (act E σ (Qpt E ℓ) - ε • Qpt E ℓ) := by module
  rw [e, effLevel_smul_Mbar E hT, add_zero]

lemma Sgen_subset_S0 (hc : Compatible E (divSys E)) (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Sgen E ℓ M ⊆ S0 E := by
  rintro σ ⟨hT, hW⟩
  refine ⟨?_, hW⟩
  rw [← effLevel_smul_Qpt E hc ℓ, map_nsmul]
  have : act E σ (Qpt E ℓ) = Qpt E ℓ + (act E σ (Qpt E ℓ) - Qpt E ℓ) := by abel
  rw [this, nsmul_add, effLevel_smul_Mbar E hT, add_zero]

lemma S0_subset_Sgen [CharZero k] (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    S0 E ⊆ Sgen E ℓ M := by
  rintro σ ⟨hG, W, hk, hx, hσ⟩
  refine ⟨?_, W, hk, hx, hσ⟩
  rw [inertia_fixes_division E σ W hk hx hσ hG (Qpt E ℓ) (effLevel ℓ) (effLevel_pos ℓ)
    (effLevel_smul_Qpt E (compatible_divSys_of_charZero E) ℓ), sub_self]
  exact zero_mem _

lemma Sgen_eq_S0 [CharZero k] (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Sgen E ℓ M = S0 E :=
  subset_antisymm (Sgen_subset_S0 E (compatible_divSys_of_charZero E) ℓ M)
    (S0_subset_Sgen E ℓ M)

/-- `S0 E` is stable under conjugation by the automorphisms in `Aut(Ω / F_Y)`. -/
lemma conj_mem_S0 (hc : Compatible E (divSys E)) {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point}
    {pm : Bool} {h : Gal E} (hh : h ∈ Hgp E ℓ M pm) {s : Gal E} (hs : s ∈ S0 E) :
    h * s * h⁻¹ ∈ S0 E := by
  obtain ⟨hsG, W, hk, hx, hsW⟩ := hs
  obtain ⟨η, -, hh'G⟩ := act_generic_of_mem_Hgp E hc ((Hgp E ℓ M pm).inv_mem hh)
  refine ⟨?_, W.comap (h⁻¹ : Gal E).toRingEquiv.toRingHom, ?_, ?_, conj_mem_inertia W h s hsW⟩
  · rw [act_mul, act_mul, hh'G, map_zsmul, hsG, ← hh'G, ← act_mul, mul_inv_cancel, act_one]
  · intro c
    rw [ValuationSubring.mem_comap]
    have : (h⁻¹ : Gal E) (algebraMap k (Ω E) c) = algebraMap k (Ω E) c :=
      (h⁻¹ : Gal E).commutes' ⟨_, (baseField E).algebraMap_mem c⟩
    change (h⁻¹ : Gal E) _ ∈ W
    rw [this]; exact hk c
  · rw [ValuationSubring.mem_comap]
    have : (h⁻¹ : Gal E) (xG E) = xG E :=
      (h⁻¹ : Gal E).commutes' ⟨_, xG_mem_baseField E⟩
    change (h⁻¹ : Gal E) _ ∈ W
    rw [this]; exact hx

/-- **The map of fundamental groups induced by a cover is an open embedding** (characteristic
`0`). -/
theorem isOpenEmbedding_pi1MapOf [CharZero k] {n ℓ ℓ' : ℕ} (hn : 0 < n) (hℓ : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M') {pm pm' : Bool}
    (hpm : pm = true → pm' = true) :
    Topology.IsOpenEmbedding
      (pi1MapOf E (ℓ := ℓ) (ℓ' := ℓ') (M := M) (M' := M') (pm := pm) (pm' := pm')) := by
  have hc := compatible_divSys_of_charZero E
  have h : Hgp E ℓ M pm ≤ Hgp E ℓ' M' pm' ∧ Sgen E ℓ M ⊆ Sgen E ℓ' M' :=
    ⟨Hgp_le E hc hn hℓ hM hpm, Sgen_subset E hc hn hℓ hM⟩
  unfold pi1MapOf
  rw [dif_pos h]
  refine GaloisPi1.isOpenEmbedding_pi1Map' _ _ h.1 h.2 ?_ (isOpen_Hgp E ℓ M pm) ?_
  · rw [Sgen_eq_S0, Sgen_eq_S0]
  · intro g hg s hs
    rw [Sgen_eq_S0] at hs ⊢
    exact conj_mem_S0 E hc hg hs

end

end Iut.Anabelian.Genuine
