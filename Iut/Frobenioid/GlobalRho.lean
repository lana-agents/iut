/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalPrime
import Iut.Cor312.ThetaData.ValuationTransfer

/-!
# The local-global isomorphisms `ρ_v` of IUT I, Example 3.5(i)

IUT I, Example 3.5(i) (l.5487–5543): "the submonoid `Φ_{C⊩_mod,v}` of `Φ_{C⊩_mod}` corresponding to
`v ∈ V_mod` is naturally isomorphic to `ord(O▷_{(F_mod)_v})^pf ⊗ R≥0 (≅ R≥0)` […] `p_v`
determines an
element `log⊢_mod(p_v) ∈ Φ_{C⊩_mod,v}` […] the realiﬁcation `Φ^rlf_{C⊢_v}` of the divisor monoid of
`C⊢_v` […] may be regarded as a single abstract monoid isomorphic to `R≥0`. Write
`logΦ(p_v) ∈ Φ^rlf_{C⊢_v}` for the element deﬁned by `p_v` […] the isomorphism of topological
monoids `ρ_v : Φ_{C⊩_mod,v} ≅ Φ^rlf_{C⊢_v}` […] which, by considering the natural "volume
interpretations" of the arithmetic divisors involved, is easily computed to be given by the
assignment `log⊢_mod(p_v) ↦ (1/[K_v:(F_mod)_v]) logΦ(p_v)`." (IUT I §0, l.2109–2112: `p_v` is the
residue characteristic for nonarchimedean `v`, and `e` for archimedean `v`.)

For number fields `k ⊆ K` (`k = F_mod`, `K` the `ℓ`-torsion field) and a place `w` of `K` over a
place `v` of `k` (`w = sect v`):

* `phiAt v = Φ_{C⊩(k),v}`: the effective divisors supported at `v`; `phiAtEquiv : Φ_v ≃ ℝ≥0`
  (`z ↦ coord_v z`);
* `logMod v = log⊢(p_v)`: the `v`-part of `div(p_v)` (`ord_v(p_v)·[v]`) if `v` is finite, `1·[v]`
  (`log e = 1`) if `v` is infinite;
* the local realified divisor monoid `Φ^rlf_{C⊢_w} = ℝ≥0` in the coordinate `ord_{K_w}` (resp.
  `−log|·|_w`); `logPhi w = logΦ(p_v)`: `ord_w(p_v)` (computed from `div_K(p_v)`), resp. `1`;
* `localDeg w v = [K_w : k_v]` (`e(w|v)·f(w|v)`, resp. `mult w / mult v`);
* **`rho`** `ρ_v : Φ_v → ℝ≥0` (as an isomorphism `Φ_v ≅ ℝ≥0`: `rhoEquivFin`, `rhoEquivInf`),
  the unique additive map with **`rho_logMod`**
  `ρ_v(log⊢(p_v)) = logΦ(p_v)/[K_w : k_v]`;
* **`degArith_eq_vol_rho`** (the "volume interpretation"): for `z ∈ Φ_v`,
  `deg^arith_k(z) = vol_w(ρ_v z)`, where `vol_w(y) = y·log N(w)` (finite) and `[K_w : ℝ]·y`
  (archimedean): the local volume of `ρ_v(z)` is the global arithmetic degree of `z`. The finite
  case uses `ord_w(x) = e(w|v)·ord_v(x)` (`ord_algebraMap`) and `N(w) = N(v)^{f(w|v)}`
  (`primeNorm_liesOver`).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open NumberField Arakelov

universe u

namespace GlobalRealified

attribute [local instance] Classical.propDecidable

/-! ### Orders under extension -/

section Ord

variable {k K : Type u} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)

/-- `ord_w(x) = −log v_w(x)` for the principal bundle. -/
lemma ord_principal_eq (x : K) (hx : x ≠ 0) (w : FinitePlace K) :
    (ArithLineBundle.principal x hx).ord w = -WithZero.log (w.maximalIdeal.valuation K x) := by
  simp only [ArithLineBundle.ord, ArithLineBundle.principal, FinitePlace.embedding_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

include hwv in
/-- **`ord_w(x) = e(w|v)·ord_v(x)`** for `x ∈ k^×`. -/
theorem ord_algebraMap (x : k) (hx : x ≠ 0) :
    (ArithLineBundle.principal (algebraMap k K x)
        ((map_ne_zero (algebraMap k K)).mpr hx)).ord w =
      (v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal : ℤ) *
        (ArithLineBundle.principal x hx).ord v := by
  rw [ord_principal_eq, ord_principal_eq, valuation_algebraMap_eq_pow hwv, WithZero.log_pow,
    nsmul_eq_mul, mul_neg]

include hwv in
/-- **`N(w) = N(v)^{f(w|v)}`**. -/
theorem primeNorm_liesOver :
    primeNorm w =
      primeNorm v ^ (v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal) := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  unfold primeNorm
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal v.maximalIdeal.isPrime v.maximalIdeal.ne_bot]
  push_cast
  rfl

end Ord

/-! ### `Φ_v`, `log⊢(p_v)`, `logΦ(p_v)` and `ρ_v` -/

variable {k : Type u} [Field k] [NumberField k]

/-- **`Φ_{C⊩,v}`**: the effective divisors supported at `v`. -/
def phiAt (v : Place k) : AddSubmonoid (ArithDiv k) where
  carrier := {z | z ∈ effCone k ∧ supp z ⊆ {v}}
  add_mem' {a b} ha hb := ⟨(effCone k).add_mem ha.1 hb.1, fun p hp => by
    by_contra hpv
    have h1 := coord_eq_zero_of_not_mem (fun h => hpv (ha.2 h))
    have h2 := coord_eq_zero_of_not_mem (fun h => hpv (hb.2 h))
    exact hp (by rw [coord_add, h1, h2, add_zero])⟩
  zero_mem' := ⟨(effCone k).zero_mem, fun p hp => (hp (coord_zero p)).elim⟩

lemma eq_single_of_mem_phiAt {v : Place k} {z : ArithDiv k} (hz : z ∈ phiAt v) :
    z = single v (coord z v) := by
  refine eq_iff_coord.mpr fun q => ?_
  rw [coord_single]
  split_ifs with h
  · rw [h]
  · exact coord_eq_zero_of_not_mem fun hq => h (hz.2 hq)

lemma single_mem_phiAt (v : Place k) {t : ℝ} (ht : 0 ≤ t) : single v t ∈ phiAt v := by
  refine ⟨single_mem ht, fun q hq => ?_⟩
  by_contra h
  exact hq (by rw [coord_single, if_neg (by simpa using h)])

/-- **`Φ_v ≅ ℝ_{≥0}`** (`z ↦ coord_v z`). -/
noncomputable def phiAtEquiv (v : Place k) : phiAt v ≃+ NNReal where
  toFun z := ⟨coord z.1 v, (mem_effCone_iff_coord.mp z.2.1) v⟩
  invFun t := ⟨single v t, single_mem_phiAt v t.2⟩
  left_inv z := Subtype.ext (eq_single_of_mem_phiAt z.2).symm
  right_inv t := NNReal.eq (by change coord (single v t) v = t; simp [coord_single])
  map_add' a b := NNReal.eq (by change coord (a.1 + b.1) v = coord a.1 v + coord b.1 v; simp)

/-- The residue characteristic `p_v` of a finite place, as an element of `k`. -/
noncomputable def pv (v : FinitePlace k) : k :=
  ((Ideal.absNorm (v.maximalIdeal.asIdeal.under ℤ) : ℕ) : k)

/-- **`log⊢(p_v) ∈ Φ_v`**: the `v`-part `ord_v(p_v)·[v]` of `div(p_v)` for finite `v`, and
`(log e)·[v] = [v]` for infinite `v`. -/
noncomputable def logMod : Place k → ArithDiv k
  | Sum.inl v => single (Sum.inl v)
      (if h : pv v ≠ 0 then ((ArithLineBundle.principal (pv v) h).ord v : ℝ) else 0)
  | Sum.inr v => single (Sum.inr v) 1

variable {K : Type u} [Field K] [NumberField K] [Algebra k K]

/-- **`logΦ(p_v)`** in the local coordinate of `K_w`: `ord_w(p_v)` for finite `w`, `log e = 1` for
infinite `w`. -/
noncomputable def logPhi (v : Place k) : Place K → ℝ
  | Sum.inl w => match v with
    | Sum.inl v => if h : pv v ≠ 0 then
        ((ArithLineBundle.principal (algebraMap k K (pv v))
          ((map_ne_zero (algebraMap k K)).mpr h)).ord w : ℝ) else 0
    | Sum.inr _ => 0
  | Sum.inr _ => 1

/-- **The local degree `[K_w : k_v]`**: `e(w|v)·f(w|v)` (finite), `mult w / mult v` (infinite). -/
noncomputable def localDeg : Place K → Place k → ℝ
  | Sum.inl w, Sum.inl v => (v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal *
      v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal : ℕ)
  | Sum.inr w, Sum.inr v => (w.mult : ℝ) / v.mult
  | _, _ => 1

/-- **The local volume** `vol_w(y)`: `y·log N(w)` (finite `w`), `[K_w : ℝ]·y` (infinite `w`). -/
noncomputable def vol : Place K → ℝ → ℝ
  | Sum.inl w, y => y * Real.log (primeNorm w)
  | Sum.inr w, y => (w.mult : ℝ) * y

omit [Algebra k K] in
lemma coord_logMod_inr (v : InfinitePlace k) : coord (logMod (Sum.inr v)) (Sum.inr v) = 1 := by
  simp [logMod, single]

omit [Algebra k K] in
lemma coord_logMod_inl (v : FinitePlace k) (h : pv v ≠ 0) :
    coord (logMod (Sum.inl v)) (Sum.inl v) = (ArithLineBundle.principal (pv v) h).ord v := by
  simp [logMod, single, h]

/-- **`ρ_v : Φ_v → Φ^rlf_{C⊢_w} = ℝ_{≥0}`** in coordinates: `c·[v] ↦ c/f(w|v)` (finite: in units of
`ord_{K_w}`), `c·[v] ↦ c·[k_v : ℝ]/[K_w : ℝ]` (infinite). `rho_logMod_fin`, `rho_logMod_inf`: this
is
the assignment `log⊢(p_v) ↦ logΦ(p_v)/[K_w : k_v]` of IUT I, Example 3.5(i). -/
noncomputable def rho : Place K → Place k → ArithDiv k → ℝ
  | Sum.inl w, Sum.inl v, z => coord z (Sum.inl v) /
      (v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal : ℕ)
  | Sum.inr w, Sum.inr v, z => coord z (Sum.inr v) * v.mult / w.mult
  | _, _, _ => 0

/-- `ρ_v` is additive. -/
lemma rho_add (w : Place K) (v : Place k) (a b : ArithDiv k) :
    rho w v (a + b) = rho w v a + rho w v b := by
  rcases w with w | w <;> rcases v with v | v <;> simp only [rho, coord_add] <;> ring

/-- `ρ_v` maps `Φ_v` to `ℝ_{≥0}`. -/
lemma rho_nonneg (w : Place K) (v : Place k) {z : ArithDiv k} (hz : z ∈ effCone k) :
    0 ≤ rho w v z := by
  have h := mem_effCone_iff_coord.mp hz
  rcases w with w | w <;> rcases v with v | v <;> simp only [rho, le_refl]
  · exact div_nonneg (h _) (Nat.cast_nonneg _)
  · exact div_nonneg (mul_nonneg (h _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

section LiesOver

variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

lemma inertiaDeg'_ne_zero :
    v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal ≠ 0 := by
  intro h
  have h1 := primeNorm_liesOver hwv
  rw [h, pow_zero] at h1
  exact (one_lt_primeNorm w).ne' h1

/-- **`ρ_v(log⊢(p_v)) = logΦ(p_v)/[K_w : k_v]`** (finite places; IUT I, Example 3.5(i)). -/
theorem rho_logMod_fin :
    rho (Sum.inl w) (Sum.inl v) (logMod (Sum.inl v)) =
      logPhi (K := K) (Sum.inl v) (Sum.inl w) / localDeg (Sum.inl w) (Sum.inl v) := by
  have he : (v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ramificationIdx'_ne_zero hwv)
  simp only [rho, logPhi, localDeg]
  by_cases h : pv v ≠ 0
  · rw [coord_logMod_inl v h, dif_pos h, ord_algebraMap hwv (pv v) h]
    push_cast
    field_simp
  · simp [logMod, h, single]

/-- **The volume interpretation** (finite places): `deg^arith_k(z) = ρ_v(z)·log N(w)` for
`z ∈ Φ_v`. -/
theorem degArith_eq_vol_rho_fin {z : ArithDiv k} (hz : z ∈ phiAt (Sum.inl v)) :
    degArith k z = vol (Sum.inl w) (rho (Sum.inl w) (Sum.inl v) z) := by
  have hf : (v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (inertiaDeg'_ne_zero hwv)
  rw [eq_single_of_mem_phiAt hz]
  simp only [vol, rho, coord_single, primeNorm_liesOver hwv, Real.log_pow]
  rw [degArith_apply]
  simp [single]
  field_simp

end LiesOver

section LiesOverInf

variable {w : InfinitePlace K} {v : InfinitePlace k}

/-- **`ρ_v(log⊢(p_v)) = logΦ(p_v)/[K_w : k_v]`** (infinite places: `log e = 1`). -/
theorem rho_logMod_inf :
    rho (Sum.inr w) (Sum.inr v) (logMod (Sum.inr v)) =
      logPhi (K := K) (Sum.inr v) (Sum.inr w) / localDeg (Sum.inr w) (Sum.inr v) := by
  have hw : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  have hv : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  simp only [rho, logPhi, localDeg, coord_logMod_inr]
  field_simp

/-- **The volume interpretation** (infinite places): `deg^arith_k(z) = [K_w : ℝ]·ρ_v(z)` for
`z ∈ Φ_v`. -/
theorem degArith_eq_vol_rho_inf {z : ArithDiv k} (hz : z ∈ phiAt (Sum.inr v)) :
    degArith k z = vol (Sum.inr w) (rho (Sum.inr w) (Sum.inr v) z) := by
  have hw : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  rw [eq_single_of_mem_phiAt hz]
  simp only [vol, rho, coord_single, if_true]
  rw [show single (Sum.inr v) (coord z (Sum.inr v)) =
    ((0 : FinitePlace k →₀ ℝ), Pi.single v (coord z (Sum.inr v))) from rfl, degArith_single_inf]
  field_simp

end LiesOverInf

/-! ### `ρ_v` as an isomorphism `Φ_v ≅ ℝ_{≥0}` -/

/-- Scaling by a positive real is an automorphism of `ℝ_{≥0}`. -/
noncomputable def nnScale (c : ℝ) (hc : 0 < c) : NNReal ≃+ NNReal where
  toFun t := ⟨c * t, mul_nonneg hc.le t.2⟩
  invFun t := ⟨t / c, div_nonneg t.2 hc.le⟩
  left_inv t := NNReal.eq (by change c * t / c = t; field_simp)
  right_inv t := NNReal.eq (by change c * (t / c) = t; field_simp)
  map_add' a b := NNReal.eq (by change c * (a + b : ℝ) = c * a + c * b; ring)

/-- **`ρ_v : Φ_v ≅ ℝ_{≥0}`** (finite places), an isomorphism of monoids. -/
noncomputable def rhoEquivFin {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : phiAt (Sum.inl v) ≃+ NNReal :=
  (phiAtEquiv (Sum.inl v)).trans (nnScale _ (inv_pos.mpr (Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (inertiaDeg'_ne_zero hwv)))))

lemma coe_rhoEquivFin {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
    (z : phiAt (Sum.inl v)) : (rhoEquivFin hwv z : ℝ) = rho (Sum.inl w) (Sum.inl v) z.1 := by
  change _ * coord z.1 (Sum.inl v) = _
  simp only [rho]
  ring

/-- **`ρ_v : Φ_v ≅ ℝ_{≥0}`** (infinite places), an isomorphism of monoids. -/
noncomputable def rhoEquivInf (w : InfinitePlace K) (v : InfinitePlace k) :
    phiAt (Sum.inr v) ≃+ NNReal :=
  (phiAtEquiv (Sum.inr v)).trans (nnScale ((v.mult : ℝ) / w.mult)
    (div_pos (Nat.cast_pos.mpr InfinitePlace.mult_pos) (Nat.cast_pos.mpr InfinitePlace.mult_pos)))

lemma coe_rhoEquivInf (w : InfinitePlace K) (v : InfinitePlace k) (z : phiAt (Sum.inr v)) :
    (rhoEquivInf w v z : ℝ) = rho (Sum.inr w) (Sum.inr v) z.1 := by
  change _ * coord z.1 (Sum.inr v) = _
  simp only [rho]
  ring

end GlobalRealified

end Frobenioid

end Iut
