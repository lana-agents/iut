/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Lattice
import Iut.LogLink.Arch
import Iut.Concrete.SectionAverage

/-!
# Global log-Kummer correspondence (IUT III, Proposition 3.10(ii), (iii); Thm 3.11(ii)(c))

IUT III, Proposition 3.10(ii) ("non-interference with local integers") computes

`(M^⊛_MOD)_α ∩ ∏_{v ∈ V} Ψ_log(A,αF_v) = (M^⊛μ_MOD)_α`,

the nonzero elements of the number field which are integral at every place are the roots of
unity ([Lang], p. 144; Kronecker). Hence, when the nonzero elements of the number fields of the
vertices `(n, m)` act on the coric `I^Q(S±_{j+1}F(n,◦D≻)_{V_ℚ})` through the totality of the
pre-composites of the Kummer isomorphisms with the iterated log-links, the only elements related
by a log-link (the elements in the domain of the log-links at every place) are roots of unity,
whose logarithms are `0` at `v ∈ V^non` and lie in the deck group of the covering of
`Ψ^gp/μ_N` at `v ∈ V^arc`: the actions are mutually compatible up to "identity
indeterminacies". This is the **log-Kummer correspondence for the number fields** (Theorem
3.11(ii)(c), first line of its first display), and it gives the compatibility of the
`F^⊛_MOD`-Frobenioids, which depend only on `M^×` and the divisor maps `β_v` (Example 3.6(i);
Proposition 3.10(iii)): the related portion has trivial divisor.

## Results

* `isIntegral_of_forall_finitePlace`: `|x|_w ≤ 1` at every finite place ⇒ `x ∈ 𝓞_K`.
* **`nonInterference`** (Proposition 3.10(ii)): for `x ≠ 0`, `x` is integral at every finite and
  every infinite place iff `x` is a root of unity; `nonInterference_set` as an equality of sets.
* **`divisor_trivial_iff`** (Example 3.6(i), Proposition 3.10(iii)): the kernel of the divisor
  maps `β_v` (all `|x|_v = 1`) is the group of roots of unity.
* **The logarithms of global roots of unity vanish**: `padicLog_algebraMap_root` at the finite
  places, `natCast_mul_log_root_embedding` (deck group of `Ψ^gp/μ_N`) at the infinite places.
* **`globalLogKummer`** (Theorem 3.11(ii)(c), Proposition 3.10(ii)): for vertical lines at the
  finite places of a number field, an element of `K^×` in the domain of the log-links at every
  place is a root of unity, and the Kummer images of its log-link images vanish at every finite
  place: the global actions are mutually compatible.
* **Initial Θ-data** (`InitialThetaData`): the same statements for `F_mod` read in the local fields
  `K_v`, `v ∈ V`, of the section `V_mod ≅ V` (`nonInterference_sect`, `fmodLogKummer`); a log-theta
  lattice `L` gives the global log-Kummer correspondence of its columns
  (`LogThetaLattice.globalLogKummer`).
-/

namespace Iut

namespace LogLink

open NumberField IsDedekindDomain PadicLogVolume HodgeTheater
open scoped Valued

noncomputable section

section Global

variable {K : Type*} [Field K] [NumberField K]

/-- `|x|_w ≤ 1` at a finite place is `v_w(x) ≤ 1`. -/
theorem valuation_le_one_of_finitePlace_le_one {x : K} (v : HeightOneSpectrum (𝓞 K))
    (h : FinitePlace.mk v x ≤ 1) : v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def] at h
  exact (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).1 (by exact_mod_cast h)

/-- **An element integral at every finite place is an algebraic integer.** -/
theorem isIntegral_of_forall_finitePlace {x : K} (h : ∀ w : FinitePlace K, w x ≤ 1) :
    IsIntegral ℤ x := by
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x fun v =>
    valuation_le_one_of_finitePlace_le_one v (h _)
  exact y.isIntegral_coe

theorem finitePlace_eq_one_of_pow {x : K} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1)
    (w : FinitePlace K) : w x = 1 := by
  have e := congrArg w h
  rw [map_pow, map_one] at e
  exact (pow_eq_one_iff_of_nonneg (by positivity) hn.ne').1 e

omit [NumberField K] in
theorem infinitePlace_eq_one_of_pow {x : K} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1)
    (v : InfinitePlace K) : v x = 1 := by
  have e := congrArg v h
  rw [map_pow, map_one] at e
  exact (pow_eq_one_iff_of_nonneg (by positivity) hn.ne').1 e

/-- **Non-interference with local integers** (IUT III, Proposition 3.10(ii)): a nonzero element
of a number field which is integral at every place is a root of unity, and conversely. -/
theorem nonInterference {x : K} (hx : x ≠ 0) :
    ((∀ w : FinitePlace K, w x ≤ 1) ∧ ∀ v : InfinitePlace K, v x ≤ 1) ↔
      ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  constructor
  · rintro ⟨hfin, hinf⟩
    obtain ⟨n, hn, h⟩ := Embeddings.pow_eq_one_of_norm_le_one K ℂ hx
      (isIntegral_of_forall_finitePlace hfin) fun φ => by
        simpa [InfinitePlace.apply] using hinf (InfinitePlace.mk φ)
    exact ⟨n, hn, h⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨fun w => (finitePlace_eq_one_of_pow hn h w).le,
      fun v => (infinitePlace_eq_one_of_pow hn h v).le⟩

/-- **Proposition 3.10(ii) as an equality of sets**: `K^× ∩ ∏_v Ψ_log(F_v) = μ_K`. -/
theorem nonInterference_set :
    {x : K | x ≠ 0 ∧ (∀ w : FinitePlace K, w x ≤ 1) ∧ ∀ v : InfinitePlace K, v x ≤ 1} =
      {x : K | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact (nonInterference hx).1 h
  · rintro ⟨n, hn, h⟩
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
    exact ⟨hx, (nonInterference hx).2 ⟨n, hn, h⟩⟩

/-- **The kernel of the divisor maps is the group of roots of unity** (IUT III, Example 3.6(i),
Remark 3.6.1, Proposition 3.10(iii)): the `F^⊛_MOD`-Frobenioid only sees `M^×` through the
divisor maps `β_v`, which are trivial exactly on the roots of unity. -/
theorem divisor_trivial_iff {x : K} (hx : x ≠ 0) :
    ((∀ w : FinitePlace K, w x = 1) ∧ ∀ v : InfinitePlace K, v x = 1) ↔
      ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  constructor
  · rintro ⟨hfin, hinf⟩
    exact (nonInterference hx).1 ⟨fun w => (hfin w).le, fun v => (hinf v).le⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨finitePlace_eq_one_of_pow hn h, infinitePlace_eq_one_of_pow hn h⟩

omit [NumberField K] in
/-- **The logarithm of a global root of unity vanishes at every finite place** where it is a
principal unit. -/
theorem padicLog_algebraMap_root {L : Type*} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))] [CompleteSpace L]
    [CharZero L]
    (ι : K →+* L) {p : ℕ} (hp : p.Prime) (hpk : ‖(p : L)‖ < 1) {x : K} {n : ℕ} (hn : 0 < n)
    (h : x ^ n = 1) (hx : ‖ι x - 1‖ < 1) : padicLog (ι x) = 0 :=
  padicLog_eq_zero_of_pow_eq_one hp hpk hx hn.ne' (by rw [← map_pow, h, map_one])

omit [NumberField K] in
/-- **At an infinite place the logarithm of a global root of unity lies in the deck group of the
covering of `Ψ^gp/μ_N`** (IUT III, Definition 1.1(ii)). -/
theorem natCast_mul_log_root_embedding (φ : K →+* ℂ) {x : K} {n : ℕ} (h : x ^ n = 1) :
    ∃ N : ℤ, (n : ℂ) * Complex.log (φ x) = N * (2 * Real.pi * Complex.I) :=
  natCast_mul_log_root (by rw [← map_pow, h, map_one])

/-- **The global log-Kummer correspondence** (IUT III, Theorem 3.11(ii)(c), Proposition
3.10(ii)): let `C w` be vertical lines at the finite places `w` of a number field `K`, with
local fields `L w` and embeddings `ι w : K → L w` compatible with the norms of the places. An
element of `K^×` which lies in the domain of the log-links at every place (integral at every
finite and every infinite place) is a root of unity, and at every finite place where it is a
principal unit, the Kummer image of its log-link image vanishes: the actions of `K^×` through
the totality of the Kummer isomorphisms and the iterated log-links are mutually compatible up to
identity indeterminacies. -/
theorem globalLogKummer {L : FinitePlace K → Type*} [∀ w, Field (L w)]
    [∀ w, Valued (L w) (WithZero (Multiplicative ℤ))]
    [∀ w, Valuation.RankOne (Valued.v : Valuation (L w) (WithZero (Multiplicative ℤ)))]
    [∀ w, CompleteSpace (L w)] [∀ w, CharZero (L w)] (C : ∀ w, LogColumn (L w))
    (ι : ∀ w, K →+* L w) {x : K} (hx : x ≠ 0) (hfin : ∀ w : FinitePlace K, w x ≤ 1)
    (hinf : ∀ v : InfinitePlace K, v x ≤ 1) :
    (∃ n : ℕ, 0 < n ∧ x ^ n = 1) ∧
      ∀ (w : FinitePlace K) (m : ℤ) {p : ℕ}, p.Prime → ‖(p : L w)‖ < 1 → ‖ι w x - 1‖ < 1 →
        (C w).kum (m + 1) (((C w).link m).toFun (ι w x)) = 0 := by
  obtain ⟨n, hn, h⟩ := (nonInterference hx).1 ⟨hfin, hinf⟩
  refine ⟨⟨n, hn, h⟩, fun w m p hp hpk hxw => ?_⟩
  rw [LocalLogLink.toFun, padicLog_algebraMap_root (ι w) hp hpk hn h hxw, map_zero, map_zero]

end Global

/-! ### Initial Θ-data: `F_mod` in the local fields of `V` -/

section ThetaData

variable (D : InitialThetaData.{0})

/-- The image of `x ∈ F_mod` in the local field `K_v` at the place `v = v(w) ∈ V` over a finite
place `w` of `F_mod`. -/
def embFin (w : FinitePlace D.Fmod) (x : D.Fmod) : Kfin D w :=
  FinitePlace.embedding (D.V.sectFin w).maximalIdeal (algebraMap D.Fmod D.Kt x)

/-- The image of `x ∈ F_mod` in `K_v` is integral iff `x` is integral at `w`. -/
theorem norm_embFin_le_one_iff (w : FinitePlace D.Fmod) (x : D.Fmod) :
    ‖embFin D w x‖ ≤ 1 ↔ w x ≤ 1 := by
  rw [embFin, norm_emb_algebraMap_le_one_iff (D.V.sectFin_liesOver w),
    FinitePlace.norm_embedding_eq]

/-- The absolute value at the place `v(w) ∈ V` over an infinite place `w` of `F_mod`. -/
theorem sectInf_apply (w : InfinitePlace D.Fmod) (x : D.Fmod) :
    D.V.sectInf w (algebraMap D.Fmod D.Kt x) = w x := by
  have := (D.V.sectInf_liesOver w).comp_eq
  exact congrArg (fun f : AbsoluteValue D.Fmod ℝ => f x) this

/-- **Proposition 3.10(ii) for `F_mod`, read in the local fields of `V`**: a nonzero `x ∈ F_mod`
whose images in all `K_v`, `v ∈ V`, are integral is a root of unity, and conversely. -/
theorem nonInterference_sect {x : D.Fmod} (hx : x ≠ 0) :
    ((∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1) ∧
      ∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1) ↔
      ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  simp only [norm_embFin_le_one_iff, sectInf_apply]
  exact nonInterference hx

/-- **The log-Kummer correspondence for `F_mod`** (IUT III, Theorem 3.11(ii)(c)): for vertical
lines at the places of `V`, an element of `F_mod^×` whose images lie in the domain of the
log-links at every place of `V` is a root of unity, and the Kummer images of its log-link images
vanish at every `v ∈ V^non` where it is a principal unit. -/
theorem fmodLogKummer (C : ∀ w : FinitePlace D.Fmod, LogColumn (Kfin D w)) {x : D.Fmod}
    (hx : x ≠ 0) (hfin : ∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1)
    (hinf : ∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1) :
    (∃ n : ℕ, 0 < n ∧ x ^ n = 1) ∧
      ∀ (w : FinitePlace D.Fmod) (m : ℤ) {p : ℕ}, p.Prime → ‖(p : Kfin D w)‖ < 1 →
        ‖embFin D w x - 1‖ < 1 → (C w).kum (m + 1) (((C w).link m).toFun (embFin D w x)) = 0 := by
  obtain ⟨n, hn, h⟩ := (nonInterference_sect D hx).1 ⟨hfin, hinf⟩
  refine ⟨⟨n, hn, h⟩, fun w m p hp hpk hxw => ?_⟩
  have hroot : embFin D w x ^ n = 1 := by
    rw [embFin, ← map_pow, ← map_pow, h, map_one, map_one]
  rw [LocalLogLink.toFun, padicLog_eq_zero_of_pow_eq_one hp hpk hxw hn.ne' hroot, map_zero,
    map_zero]

end ThetaData

/-- **The global log-Kummer correspondence of a log-theta-lattice** (IUT III, Theorem
3.11(ii)(c)): along the `n`-th column, the elements of `F_mod^×` related by the log-links are
roots of unity, with vanishing log-link images. -/
theorem LogThetaLattice.globalLogKummer {D : InitialThetaData.{0}} (L : LogThetaLattice D)
    (n : ℤ) {x : D.Fmod} (hx : x ≠ 0) (hfin : ∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1)
    (hinf : ∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1) :
    (∃ k : ℕ, 0 < k ∧ x ^ k = 1) ∧
      ∀ (w : FinitePlace D.Fmod) (m : ℤ) {p : ℕ}, p.Prime → ‖(p : Kfin D w)‖ < 1 →
        ‖embFin D w x - 1‖ < 1 →
          (L.loc n w).kum (m + 1) (((L.loc n w).link m).toFun (embFin D w x)) = 0 :=
  fmodLogKummer D (L.loc n) hx hfin hinf

end

end LogLink

end Iut
