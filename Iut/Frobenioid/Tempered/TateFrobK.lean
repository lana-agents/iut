/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.TateGalSigma
import Iut.Frobenioid.Tempered.EllDescent

/-!
# The tempered Frobenioid of `Π^tp_X` over `k` with the Tate action (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

`EllDescent.radDataL φ hφ γ` is the B-an tempered Frobenioid over a field `L` ([EtTh] Def 3.3,
Prop 3.4(ii) over `L`) for any action `γ : G →* GalDeck t` *defined over `L`* (`IsLRat φ γ`: its
Galois part fixes `φ(L)`, its deck part lies in `φ(L)^×`). For `G = Π^tp_X` and the Tate action
`tateGalDeckK` of `TateGalSigma` (Galois part `sigmaTemp` from tfg's `Π^tp_X → G_k`, deck part
`tateDeck`) this holds over `L = k`:

* `tateDeckOfChar_mem_range`: the deck transformations `(-1)^ε s^{-n}` lie in `k^×` (`s ∈ k`);
* **`isLRat_tateGalDeckK`**: the Tate action is defined over `k`;
* **`tateFrobK`**: the tempered Frobenioid data on `Π^tp_X` over `k` (`B₀` = log-meromorphic
  functions on `Ÿ_∞` defined over `k`, `Φ₀` = `ℚ`-divisors on the elliptic prime set),
  `tateFrobK_isFrobenioid`, **`tateFrobK_div_eq_zero_iff`** (kernel of the divisor map `O_k^×`),
  `tateFrobK_gal` (`B₀` is fixed by `Gal(K/k)`).

This is the unramified layer `n = 1` (functions on `Ÿ_∞` itself, no roots); the radical layers
need a Tate lift to an algebraic closure of `Mero K`, which needs the comparison of all tempered
coverings (T7c debt, `EllTate`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta TemperedFundamentalGroups TemperedFundamentalGroups.Kummer
  TemperedFundamentalGroups.TateObject KummerTheory.Curve Pi1.Orbifold AffOrbicurve

universe u

/-! ### The deck part lies in `k^×` -/

section DeckRat

variable {k : Type u} [Field k] {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [Algebra k K] {t : TateParameter K}

/-- **The deck transformations `(-1)^ε s^{-n}` are `k`-rational** when `s ∈ k`. -/
lemma tateDeckOfChar_mem_range {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) (x : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    ∃ c : kˣ, Units.map (algebraMap k K).toMonoidHom c = ((tateDeckOfChar hs x : Deck t) : Kˣ) := by
  let H : Subgroup (Deck t) :=
    (Units.map (algebraMap k K).toMonoidHom).range.comap (Deck t).subtype
  have hs0 : s₀ ≠ 0 := fun h => s.ne_zero (by rw [← hs₀, h, map_zero])
  have hgen : Deck.gen t hs ∈ H :=
    ⟨Units.mk0 s₀ hs0, Units.ext (by
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0, hs₀]
      rfl)⟩
  have hneg : Deck.neg t ∈ H :=
    ⟨-1, Units.ext (by
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_neg,
        Units.val_one, map_neg, map_one]
      rfl)⟩
  have hmem : tateDeckOfChar hs x ∈ H := by
    rw [tateDeckOfChar, MonoidHom.coprod_apply]
    refine H.mul_mem ?_ ?_
    · rw [zpowersHom_apply]
      exact H.zpow_mem (H.inv_mem hgen) _
    · rcases mult_zmod_two x.2 with h | h
      · rw [h, map_one]; exact H.one_mem
      · rw [h, signHom_ofAdd_one]; exact hneg
  exact hmem

end DeckRat

/-! ### The tempered Frobenioid over `k` -/

section Frob

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {Ω : Type u} [Field Ω] [Algebra k Ω] {tΩ : Ω}
  (DG : Pi1.Orbifold.GaloisData k tΩ) [CharZero k] [IsGalois (K₀ k tΩ) Ω] [IsAlgClosed Ω]
  {O : ValuationSubring k} (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K] {ι : kbar k Ω →ₐ[k] K} (hι : DenseRange ι) {t : TateParameter K}
  [IsReduced DG.R] [Subsingleton DG.A] (D : TateObject.DoubleData O DG.R) (sΩ : Ω)
  (hsΩ : sΩ ^ 2 = algebraMap DG.R Ω D.c)

/-- **The Tate action `tateGalDeckK` is defined over `k`.** -/
theorem isLRat_tateGalDeckK {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) :
    IsLRat (algebraMap k K)
      (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) := fun g =>
  ⟨⟨(sigmaTemp DG O V hV hι (exists_q_of_s hs hs₀) g).2.1,
    sigmaTemp_algebraMap hι (exists_q_of_s hs hs₀) g⟩,
    tateDeckOfChar_mem_range hs hs₀ _⟩

lemma norm_algebraMap_k (a : k) : ‖algebraMap k K a‖ = ‖a‖ := norm_algebraMap' K a

/-- **The tempered Frobenioid data on `Π^tp_X` over `k`** for the Tate action (the unramified
layer: `B₀` = log-meromorphic functions on `Ÿ_∞ = 𝔾_m^an` defined over `k`). -/
abbrev tateFrobK (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) : TemperedFrobenioidData (TempPi DG O V hV) :=
  radDataL (algebraMap k K) norm_algebraMap_k
    (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) s hval hs
    (isLRat_tateGalDeckK DG V hV hι D sΩ hsΩ hs hs₀)

theorem tateFrobK_isFrobenioid (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    {s₀ : k} (hs₀ : algebraMap k K s₀ = s) :
    IsFrobenioid (Model.toElem (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).Φ₀
      (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀
      (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).div₀) :=
  radDataL_isFrobenioid s hval hs _

/-- **The kernel of the divisor map of `tateFrobK` is `O_k^×`** ([EtTh] Prop 3.4(ii) over `k`). -/
theorem tateFrobK_div_eq_zero_iff [IsAlgClosed K] (hval : ValueGroupRat t) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) {s₀ : k} (hs₀ : algebraMap k K s₀ = s)
    {A : OrbitObj (TempPi DG O V hV)}
    (x : (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj A) :
    (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).div₀.app A x = 0 ↔
      ∃ c : k, ‖c‖ = 1 ∧ rv x.1 = Mero.const (algebraMap k K c) :=
  radDivL_eq_zero_iff s hval hs _ x

/-- **The elements of `B₀` are fixed by `Gal(K/k)`.** -/
theorem tateFrobK_gal (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) {A : OrbitObj (TempPi DG O V hV)}
    (x : (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj A) (σ : IsoAut t)
    (hσ : (σ : RingAut K) ∈ galL (algebraMap k K)) :
    Mero.gal σ (rv (R := GalDeckMero
      (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀)) x.1) = rv x.1 :=
  gal_rv_radBL s hval hs (isLRat_tateGalDeckK DG V hV hι D sΩ hsΩ hs hs₀) x σ hσ

end Frob

end Iut.Frobenioid.BAn
