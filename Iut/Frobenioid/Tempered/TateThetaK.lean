/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.TateFrobK
import Iut.Frobenioid.Tempered.EllTheta

/-!
# `Θ̈`, `Ü`, `q^{1/2}` in `B₀(Ÿ)` of the tempered Frobenioid over `k` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

`TateFrobK.tateFrobK` is the tempered Frobenioid data on `Π^tp_X` over `k` for the Tate action
(Galois part `sigmaTemp`, deck part `tateDeck`). Under this action `Π^tp_Ÿ = ker character₂`
(tfg `piYddot`, open: `isOpen_piYddot`) acts trivially on every function defined over `k`: its
deck part is `tateDeckOfChar 1 = 1` and its Galois part fixes `k`. Hence:

* `objYdd`: the object `Ÿ = Π^tp_X / Π^tp_Ÿ` of the base category;
* **`thetaEltK z hz`**: every log-meromorphic function `f = z ⊗ K` defined over `k` is an element of
  `B₀(Ÿ)` (`rv_thetaEltK`);
* **`bThetaK`** (`Θ̈`, coefficients `(-1)^m q^{e(m)}` in `k` when `q ∈ k`, `map_thetaDdK`),
  `bUK` (`Ü`), `bOneK` (`q^{1/2} = s ∈ k`): the theta function and the coordinate are elements of
  `B₀(Ÿ)` of the tempered Frobenioid over `k` ([EtTh] Ex 3.9(iv): `Φ^ell_α` is rational because of
  the theta functions, l.6176–6204; Prop 1.4(i) for the zeros of `Θ̈`).
* **`div_thetaEltK`**: the divisor of `thetaEltK z` at `(gΠ^tp_Ÿ, p)` is `div(f)(g⁻¹ • p)`;
  **`div_bThetaK_inl`** (`-(a + χ(g))²/2` on the component `a`), `div_bThetaK_inr` (`1` at the
  cusps): [EtTh] Prop 1.4(i) in `B₀(Ÿ)` over `k`.
* **[EtTh] Prop 1.4(ii) for the Tate action** (l.1324–1328): `gal_thetaDd` (`Θ̈` has `σ`-fixed
  coefficients), `scale_tateDeckOfChar_thetaDd`, **`galDeckHom_tateGalDeckK_thetaDd`**: `g ∈ Π^tp_X`
  maps `Θ̈` to `(-1)^ε (-1)^n s^{-n²} Ü^{-2n} Θ̈`, `(n, ε) = character₂ g`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta TemperedFundamentalGroups TemperedFundamentalGroups.Kummer
  TemperedFundamentalGroups.TateObject KummerTheory.Curve Pi1.Orbifold AffOrbicurve

universe u

/-! ### `Θ̈` over `k` -/

section ThetaK

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K] {t : TateParameter K}

/-- The Tate parameter `q₀ ∈ k` with `q₀ ↦ q`. -/
def tateParamK {q₀ : k} (hq₀ : algebraMap k K q₀ = t.q) : TateParameter k where
  q := Units.mk0 q₀ fun h => t.q.ne_zero (by rw [← hq₀, h, map_zero])
  norm_lt_one := by
    rw [Units.val_mk0, ← norm_algebraMap' K q₀, hq₀]
    exact t.norm_lt_one

/-- **`Θ̈` is defined over `k`**: its coefficients `(-1)^m q^{e(m)}` lie in `k` when `q ∈ k`. -/
theorem map_thetaDdK {q₀ : k} (hq₀ : algebraMap k K q₀ = t.q) :
    Entire.map (algebraMap k K) (norm_algebraMap' K) (thetaDd (tateParamK hq₀)) = thetaDd t := by
  refine Entire.ext_coeff (funext fun n => ?_)
  rw [Entire.coeff_map, coeff_thetaDd, coeff_thetaDd]
  by_cases hn : ∃ m, oddEmb m = n
  · obtain ⟨m, rfl⟩ := hn
    simp only [oddEmb, thetaDdCoeff_odd, thetaDdOdd, map_mul, map_zpow₀, map_neg, map_one]
    congr 2
  · simp only [thetaDdCoeff_of_notMem _ hn, map_zero]

end ThetaK

/-! ### Elements of `B₀(Ÿ)` -/

section Elts

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {Ω : Type u} [Field Ω] [Algebra k Ω] {tΩ : Ω}
  (DG : Pi1.Orbifold.GaloisData k tΩ) [CharZero k] [IsGalois (K₀ k tΩ) Ω] [IsAlgClosed Ω]
  {O : ValuationSubring k} (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K] {ι : kbar k Ω →ₐ[k] K} (hι : DenseRange ι) {t : TateParameter K}
  [IsReduced DG.R] [Subsingleton DG.A] (D : TateObject.DoubleData O DG.R) (sΩ : Ω)
  (hsΩ : sΩ ^ 2 = algebraMap DG.R Ω D.c)

/-- **`Π^tp_Ÿ = ker character₂` is open.** -/
lemma isOpen_piYddot :
    IsOpen (piYddot (A := DG.A) D V hV sΩ hsΩ : Set (TempPi DG O V hV)) := by
  letI : TopologicalSpace (Multiplicative ℤ × Multiplicative (ZMod 2)) := ⊥
  haveI : DiscreteTopology (Multiplicative ℤ × Multiplicative (ZMod 2)) := ⟨rfl⟩
  have hc : Continuous (character₂ (A := DG.A) D V hV sΩ hsΩ) :=
    FibreAut.continuous_deckCharacter _ _ _ _
  exact hc.isOpen_preimage {1} (isOpen_discrete _)

/-- **The object `Ÿ`** (`Π^tp_X / Π^tp_Ÿ`). -/
abbrev objYdd : OrbitObj (TempPi DG O V hV) :=
  ⟨piYddot (A := DG.A) D V hV sΩ hsΩ, isOpen_piYddot DG V hV D sΩ hsΩ⟩

variable (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
  (hs₀ : algebraMap k K s₀ = s)

/-- `Π^tp_Ÿ` acts trivially on the functions defined over `k`. -/
lemma smul_map_of_mem_piYddot {h : TempPi DG O V hV}
    (hh : h ∈ piYddot (A := DG.A) D V hV sΩ hsΩ) (z : Mero k) :
    h • (show GalDeckMero (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) from
      Mero.map (algebraMap k K) norm_algebraMap_k z) =
      Mero.map (algebraMap k K) norm_algebraMap_k z := by
  change galDeckHom t (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀ h)
    (Mero.map (algebraMap k K) norm_algebraMap_k z) = _
  rw [galDeckHom_apply]
  have hσ := (isLRat_tateGalDeckK DG V hV hι D sΩ hsΩ hs hs₀ h).1
  rw [Mero.gal_map_of_fix _ _ _ hσ]
  have hd : ((tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀ h).left) = 1 := by
    change tateDeckOfChar hs (character₂ (A := DG.A) D V hV sΩ hsΩ h) = 1
    rw [show character₂ (A := DG.A) D V hV sΩ hsΩ h = 1 from hh, map_one]
  rw [hd, inv_one, Subgroup.coe_one, Mero.scale_one]

/-- **A log-meromorphic function defined over `k` as an element of `B₀(Ÿ)`** of `tateFrobK`. -/
def thetaEltK (z : Mero k) (hz : IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k z)) :
    (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj (objYdd DG V hV D sΩ hsΩ) :=
  ⟨Additive.ofMul ⟨Units.mk0 (show GalDeckMero
      (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) from
        Mero.map (algebraMap k K) norm_algebraMap_k z) hz.1,
    Mero.isRad_ι _, fun α hα => by
      have h := Mero.rord_ι (R := GalDeckMero
        (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀)) hz.1 α
      rw [hz.2 α hα, Int.cast_zero] at h
      exact h,
    fun _ hh => smul_map_of_mem_piYddot DG V hV hι D sΩ hsΩ hs hs₀ hh z⟩, z, rfl⟩

lemma rv_thetaEltK (z : Mero k)
    (hz : IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k z)) :
    rv (thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ z hz).1 =
      (show GalDeckMero (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) from
        Mero.map (algebraMap k K) norm_algebraMap_k z) := rfl

include hs hs₀ in
lemma q_of_s : algebraMap k K (s₀ ^ 2) = t.q := by rw [map_pow, hs₀, hs]

include hs hs₀ in
lemma isLogMero_map_thetaDdK :
    IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k
      (Mero.ofE (thetaDd (tateParamK (q_of_s hs hs₀))))) := by
  rw [Mero.map_ofE, map_thetaDdK]
  exact isLogMero_thetaDd

/-- **`Θ̈ ∈ B₀(Ÿ)`** of the tempered Frobenioid over `k`. -/
def bThetaK : (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj (objYdd DG V hV D sΩ hsΩ) :=
  thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ _ (isLogMero_map_thetaDdK hs hs₀)

lemma rv_bThetaK :
    rv (bThetaK DG V hV hι D sΩ hsΩ hval hs hs₀).1 =
      (show GalDeckMero (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀) from
        Mero.ofE (thetaDd t)) := by
  rw [bThetaK, rv_thetaEltK]
  change Mero.map _ _ (Mero.ofE _) = _
  rw [Mero.map_ofE, map_thetaDdK]

lemma isLogMero_map_mono :
    IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k (Mero.ofE (Entire.mono 1))) := by
  rw [Mero.map_ofE, Entire.map_mono]
  exact isLogMero_mono

/-- **`Ü ∈ B₀(Ÿ)`** of the tempered Frobenioid over `k`. -/
def bUK : (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj (objYdd DG V hV D sΩ hsΩ) :=
  thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ _ isLogMero_map_mono

include hs₀ in
lemma isLogMero_map_s :
    IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k (Mero.const s₀)) := by
  rw [Mero.map_const, hs₀]
  exact isLogMero_const s.ne_zero

/-- **`q^{1/2} = s ∈ B₀(Ÿ)`** of the tempered Frobenioid over `k`. -/
def bOneK : (tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).B₀.obj (objYdd DG V hV D sΩ hsΩ) :=
  thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ _ (isLogMero_map_s hs₀)

/-- **The divisor of `thetaEltK z` in `tateFrobK`**: at the point `(g Π^tp_Ÿ, p)` it is the
divisor of `f = z ⊗ K` at `g⁻¹ • p` (`g` acting on the elliptic prime set through the Tate
action). -/
theorem div_thetaEltK (z : Mero k)
    (hz : IsLogMero t (Mero.map (algebraMap k K) norm_algebraMap_k z))
    (g : TempPi DG O V hV)
    (p : PrimeAct ((galDeckPerm t).comp
      (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀))) :
    ((tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).div₀.app (objYdd DG V hV D sΩ hsΩ)
        (thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ z hz)).1 (QuotientGroup.mk g, p) =
      ellDiv t s (Mero.map (algebraMap k K) norm_algebraMap_k z)
        (show EllPrime t from g⁻¹ • p) := by
  change radDivFun s _ _ (rv (thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ z hz).1)
    (QuotientGroup.mk g, p) = _
  rw [radDivFun_mk (actCompat_galDeck _ hval hs) (rv_ne_zero _) (rv_isRad _) (rv_isLogRad _)
    (rv_fix _)]
  exact congrFun (rEllDiv_ι (R := GalDeckMero
    (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀)) hval hs hz.1) _

lemma bThetaK_eq :
    bThetaK DG V hV hι D sΩ hsΩ hval hs hs₀ =
      thetaEltK DG V hV hι D sΩ hsΩ hval hs hs₀ _ (isLogMero_map_thetaDdK hs hs₀) := rfl

lemma map_ofE_thetaDdK :
    Mero.map (algebraMap k K) norm_algebraMap_k
      (Mero.ofE (thetaDd (tateParamK (q_of_s hs hs₀)))) = Mero.ofE (thetaDd t) := by
  rw [Mero.map_ofE, map_thetaDdK]

/-- **The divisor of `Θ̈ ∈ B₀(Ÿ)` on the components** ([EtTh] Prop 1.4(i)): at `(g Π^tp_Ÿ, a)` it
is `-(a + χ(g))²/2` (`χ` the character of `Y`). -/
theorem div_bThetaK_inl (h2 : (2 : K) ≠ 0) (g : TempPi DG O V hV) (a : ℤ) :
    ((tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).div₀.app (objYdd DG V hV D sΩ hsΩ)
        (bThetaK DG V hV hι D sΩ hsΩ hval hs hs₀)).1 (QuotientGroup.mk g, Sum.inl a) =
      -(((a + Multiplicative.toAdd (character (A := DG.A) D.toData V hV g) : ℤ) : ℚ) ^ 2) / 2 := by
  rw [bThetaK_eq, div_thetaEltK, map_ofE_thetaDdK hs hs₀, ellDiv_thetaDd h2 hs]
  change (Sum.elim (fun a : ℤ => -((a : ℚ) ^ 2) / 2) fun _ => 1 : EllPrime t → ℚ)
    (Sum.inl (a + Deck.idx (tateDeck V hV D sΩ hsΩ hs g⁻¹))) = _
  rw [Sum.elim_inl, idx_tateDeck, map_inv, toAdd_inv, neg_neg]

/-- **The divisor of `Θ̈ ∈ B₀(Ÿ)` at the cusps is `1`** ([EtTh] Prop 1.4(i)). -/
theorem div_bThetaK_inr (h2 : (2 : K) ≠ 0) (g : TempPi DG O V hV) (α : Cusp t) :
    ((tateFrobK DG V hV hι D sΩ hsΩ hval hs hs₀).div₀.app (objYdd DG V hV D sΩ hsΩ)
        (bThetaK DG V hV hι D sΩ hsΩ hval hs hs₀)).1 (QuotientGroup.mk g, Sum.inr α) = 1 := by
  rw [bThetaK_eq, div_thetaEltK, map_ofE_thetaDdK hs hs₀, ellDiv_thetaDd h2 hs]
  rfl

end Elts

/-! ### [EtTh] Prop 1.4(ii) for the Tate action of `Π^tp_X` -/

section Prop14

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

/-- `σ ∈ IsoAut t` fixes `Θ̈` (its coefficients are powers of `q`). -/
lemma gal_thetaDd (σ : IsoAut t) : Mero.gal σ (Mero.ofE (thetaDd t)) = Mero.ofE (thetaDd t) := by
  rw [Mero.gal_ofE]
  congr 1
  refine Entire.ext_coeff (funext fun n => ?_)
  rw [Entire.coeff_map, coeff_thetaDd]
  by_cases hn : ∃ m, oddEmb m = n
  · obtain ⟨m, rfl⟩ := hn
    simp only [oddEmb, thetaDdCoeff_odd, thetaDdOdd, map_mul, map_zpow₀, map_neg, map_one]
    congr 2
    exact IsoAut.q σ
  · simp only [thetaDdCoeff_of_notMem _ hn, map_zero]

/-- `Ü ↦ -Ü` negates `Θ̈`. -/
lemma scale_neg_one_thetaDd :
    Mero.scale (-1) (Mero.ofE (thetaDd t)) = -Mero.ofE (thetaDd t) := by
  rw [Mero.scale_ofE, ← Mero.ofE_neg]
  congr 1
  refine Entire.ext_apply fun u => ?_
  rw [Entire.coe_scale, neg_one_mul, thetaDd_neg]
  rfl

lemma scale_neg_one_mono_zpow (m : ℤ) :
    Mero.scale (-1) (Mero.ofE (Entire.mono 1 : Entire K) ^ (2 * m)) =
      Mero.ofE (Entire.mono 1 : Entire K) ^ (2 * m) := by
  have h1 : Mero.scale (-1) (Mero.ofE (Entire.mono 1 : Entire K)) = -Mero.ofE (Entire.mono 1) := by
    rw [Mero.scale_ofE, ← Mero.ofE_neg]
    congr 1
    refine Entire.ext_apply fun u => ?_
    rw [Entire.coe_scale, Entire.coe_neg_apply, Entire.coe_mono_apply, Entire.coe_mono_apply,
      zpow_one, zpow_one, neg_one_mul, Units.val_neg]
  rw [map_zpow₀, h1, Even.neg_zpow ⟨m, two_mul m⟩]

/-- **[EtTh] Prop 1.4(ii) under the deck part of the Tate action**: for
`x = (n, ε) ∈ ℤ × ℤ/2`, `Θ̈((tateDeckOfChar x)⁻¹·Ü) = (-1)^ε (-1)^n s^{-n²} Ü^{-2n} Θ̈(Ü)`. -/
theorem scale_tateDeckOfChar_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (x : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    Mero.scale (((tateDeckOfChar hs x)⁻¹ : Deck t) : Kˣ) (Mero.ofE (thetaDd t)) =
      Mero.const ((if x.2 = 1 then 1 else -1) * (-1 : K) ^ Multiplicative.toAdd x.1 *
          (s : K) ^ (-(Multiplicative.toAdd x.1 ^ 2))) *
        Mero.ofE (thetaDd t) * Mero.ofE (Entire.mono 1) ^ (2 * -Multiplicative.toAdd x.1) := by
  rw [← map_inv, tateDeckOfChar, MonoidHom.coprod_apply, Subgroup.coe_mul, Mero.scale_mul_apply,
    zpowersHom_apply, Subgroup.coe_zpow, Subgroup.coe_inv,
    show (((Deck.gen t hs : Deck t) : Kˣ)) = s from rfl, inv_zpow', Prod.fst_inv, toAdd_inv,
    neg_neg]
  have e := Iut.Frobenioid.scale_thetaDd_mero hs (-Multiplicative.toAdd x.1)
  rw [neg_neg] at e
  rw [e]
  have hx2 : x.2⁻¹ = x.2 := by rcases mult_zmod_two x.2 with h | h <;> rw [h] <;> decide
  rw [Prod.snd_inv, hx2]
  rcases mult_zmod_two x.2 with h | h
  · rw [h, map_one, Subgroup.coe_one, Mero.scale_one, if_pos rfl, one_mul, Mero.const_mul,
      Iut.Frobenioid.const_zpow, Iut.Frobenioid.const_zpow, neg_sq]
    ring
  · rw [h, signHom_ofAdd_one, if_neg (by decide)]
    change Mero.scale (-1) _ = _
    rw [map_mul, map_mul, map_mul, scale_neg_one_mono_zpow, map_zpow₀, Mero.scale_const,
      Mero.scale_const, scale_neg_one_thetaDd, Mero.const_mul, Mero.const_mul,
      Iut.Frobenioid.const_zpow, Iut.Frobenioid.const_zpow, neg_sq]
    have hm1 : Mero.const (-1 : K) = -1 := by
      change Mero.ofE (algebraMap K (Entire K) (-1)) = -1
      rw [map_neg, map_one, Mero.ofE_neg, Mero.ofE_one]
    rw [hm1]
    ring

end Prop14

section Prop14Pi

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {Ω : Type u} [Field Ω] [Algebra k Ω] {tΩ : Ω}
  (DG : Pi1.Orbifold.GaloisData k tΩ) [CharZero k] [IsGalois (K₀ k tΩ) Ω] [IsAlgClosed Ω]
  {O : ValuationSubring k} (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra k K] {ι : kbar k Ω →ₐ[k] K} (hι : DenseRange ι) {t : TateParameter K}
  [IsReduced DG.R] [Subsingleton DG.A] (D : TateObject.DoubleData O DG.R) (sΩ : Ω)
  (hsΩ : sΩ ^ 2 = algebraMap DG.R Ω D.c)

/-- **[EtTh] Prop 1.4(ii) for the Tate action of `Π^tp_X`**: `g` maps `Θ̈` to
`(-1)^ε (-1)^n s^{-n²} Ü^{-2n} Θ̈`, `(n, ε) = character₂ g`. -/
theorem galDeckHom_tateGalDeckK_thetaDd {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {s₀ : k}
    (hs₀ : algebraMap k K s₀ = s) (g : TempPi DG O V hV) :
    galDeckHom t (tateGalDeckK (DG := DG) (V := V) (hV := hV) hι D sΩ hsΩ hs hs₀ g)
        (Mero.ofE (thetaDd t)) =
      Mero.const ((if (character₂ (A := DG.A) D V hV sΩ hsΩ g).2 = 1 then 1 else -1) *
          (-1 : K) ^ Multiplicative.toAdd (character₂ (A := DG.A) D V hV sΩ hsΩ g).1 *
          (s : K) ^ (-(Multiplicative.toAdd (character₂ (A := DG.A) D V hV sΩ hsΩ g).1 ^ 2))) *
        Mero.ofE (thetaDd t) *
        Mero.ofE (Entire.mono 1) ^
          (2 * -Multiplicative.toAdd (character₂ (A := DG.A) D V hV sΩ hsΩ g).1) := by
  rw [galDeckHom_apply, gal_thetaDd]
  exact scale_tateDeckOfChar_thetaDd hs _

end Prop14Pi

end Iut.Frobenioid.BAn
