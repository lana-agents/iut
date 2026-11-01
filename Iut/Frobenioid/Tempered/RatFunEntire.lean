/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Theta.LaurentUnitSphere
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent

/-!
# Entire Laurent series on `𝔾_m^an` (MR18 T8, route B-an)

[EtTh] §3 (Definition 3.1, Proposition 3.2, Definition 3.3) builds the rational function monoid
`B` of a tempered Frobenioid from meromorphic functions on the *universal combinatorial covering*
`Z_∞` of a stable model. For the coverings of the elliptic curve of [EtTh] Example 3.9 (unramified
over the cusps), `Z_∞` is analytically the punctured plane `𝔾_m^an` (coordinate `U`, the special
fibre being the infinite chain of projective lines of [EtTh] §1). Lead decision O2 (MR18 plan): `B`
is built from genuine analytic functions there ("B-an").

This file sets up the ring `E(K)` of **entire Laurent series**: the functions `Kˣ → K` of the form
`u ↦ ∑ₙ cₙ uⁿ` with `∑ₙ cₙ uⁿ` summable for every `u ∈ Kˣ`, over a complete ultrametric
nontrivially normed field `K`. It is a `K`-subalgebra of the function algebra `Kˣ → K` (`entire`);
the ring structure is that of functions, closure under products is the ultrametric Cauchy product
of tate-curves-theta (`hasSum_laurentConvolution`). Coefficients are well defined by the
unconditional Laurent coefficient uniqueness of tate-curves-theta (`laurentCoeffUnique`).

## Main definitions and results

* `IsEntire c`, `lsum c`: everywhere convergence of a coefficient family and its function.
* `entire K`: the subalgebra `E(K)`; `Entire.coeff`, `Entire.coeff_spec`, `Entire.eq_coeff`,
  `Entire.ext_coeff`.
* `Entire.coeff_add`, `coeff_neg`, `coeff_smul`, `coeff_algebraMap`, `coeff_mul` (the convolution).
* `Entire.mono k` (the monomial `Uᵏ`), `coeff_mono`, `mono_add`, `coeff_mono_mul` (shift).
* `Entire.ofCoeff c hc` (the element with prescribed coefficients).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **Everywhere convergence** of a two-sided Laurent coefficient family on `Kˣ`. -/
def IsEntire (c : ℤ → K) : Prop := ∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n

/-- The function `u ↦ ∑ₙ cₙ uⁿ` of a coefficient family. -/
def lsum (c : ℤ → K) (u : Kˣ) : K := ∑' n : ℤ, c n * (u : K) ^ n

/-- The convolution of two coefficient families (the coefficients of a product). -/
def conv (c d : ℤ → K) (l : ℤ) : K := ∑' m : ℤ, c (l - m) * d m

lemma IsEntire.hasSum {c : ℤ → K} (hc : IsEntire c) (u : Kˣ) :
    HasSum (fun n : ℤ => c n * (u : K) ^ n) (lsum c u) := (hc u).hasSum

lemma isEntire_zero : IsEntire (0 : ℤ → K) := fun _ => by simp [summable_zero]

lemma IsEntire.add {c d : ℤ → K} (hc : IsEntire c) (hd : IsEntire d) : IsEntire (c + d) :=
  fun u => by simpa [add_mul] using (hc u).add (hd u)

lemma IsEntire.neg {c : ℤ → K} (hc : IsEntire c) : IsEntire (-c) :=
  fun u => by simpa [neg_mul] using (hc u).neg

lemma IsEntire.smul {c : ℤ → K} (hc : IsEntire c) (a : K) : IsEntire (a • c) :=
  fun u => by simpa [mul_assoc] using (hc u).mul_left a

lemma isEntire_single (k : ℤ) (a : K) : IsEntire (Pi.single k a) := by
  intro u
  refine (hasSum_single k fun n hn => ?_).summable
  simp [hn]

lemma hasSum_single_lsum (k : ℤ) (a : K) (u : Kˣ) :
    HasSum (fun n : ℤ => (Pi.single k a : ℤ → K) n * (u : K) ^ n) (a * (u : K) ^ k) := by
  convert hasSum_single (f := fun n : ℤ => (Pi.single k a : ℤ → K) n * (u : K) ^ n) k
    (fun n hn => by simp [hn]) using 1
  simp

lemma conv_hasSum {c d : ℤ → K} (hc : IsEntire c) (hd : IsEntire d) (u : Kˣ) :
    HasSum (fun l : ℤ => conv c d l * (u : K) ^ l) (lsum c u * lsum d u) :=
  TateParameter.hasSum_laurentConvolution u (hc.hasSum u) (hd.hasSum u)

lemma IsEntire.conv {c d : ℤ → K} (hc : IsEntire c) (hd : IsEntire d) : IsEntire (conv c d) :=
  fun u => (conv_hasSum hc hd u).summable

/-- A Tate parameter from a nontrivially normed field (only used to invoke tate-curves-theta's
coefficient uniqueness, whose proof uses the norm-one units `1 + qᵏ⁺¹`). -/
def auxParam : TateParameter K :=
  let h := NormedField.exists_norm_lt_one K
  ⟨Units.mk0 h.choose (norm_pos_iff.mp h.choose_spec.1), h.choose_spec.2⟩

/-- **Coefficient uniqueness** (tate-curves-theta `laurentCoeffUnique`, unconditional). -/
lemma eq_of_lsum_eq {c d : ℤ → K} (hc : IsEntire c) (hd : IsEntire d)
    (h : lsum c = lsum d) : c = d :=
  (auxParam (K := K)).laurentCoeffUnique c d hc hd fun u => congrFun h u

variable (K) in
/-- **The ring `E(K)` of entire Laurent series** on `𝔾_m^an`, as a `K`-subalgebra of `Kˣ → K`. -/
def entire : Subalgebra K (Kˣ → K) where
  carrier := {f | ∃ c : ℤ → K, IsEntire c ∧ f = lsum c}
  zero_mem' := ⟨0, isEntire_zero, by funext u; simp [lsum]⟩
  add_mem' := by
    rintro f g ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c + d, hc.add hd, funext fun u => ?_⟩
    exact (((hc.hasSum u).add (hd.hasSum u)).congr_fun (fun n => by simp [add_mul])).tsum_eq.symm
  mul_mem' := by
    rintro f g ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨conv c d, hc.conv hd, funext fun u => (conv_hasSum hc hd u).tsum_eq.symm⟩
  algebraMap_mem' a := by
    refine ⟨Pi.single 0 a, isEntire_single 0 a, funext fun u => ?_⟩
    rw [lsum, (hasSum_single_lsum 0 a u).tsum_eq]
    simp

/-- The type `E(K)`. -/
abbrev Entire (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :=
  entire K

namespace Entire

/-- The coefficients of an entire Laurent series. -/
def coeff (f : Entire K) : ℤ → K := f.2.choose

lemma isEntire_coeff (f : Entire K) : IsEntire (coeff f) := f.2.choose_spec.1

lemma coe_eq_lsum (f : Entire K) : (f : Kˣ → K) = lsum (coeff f) := f.2.choose_spec.2

lemma coeff_spec (f : Entire K) (u : Kˣ) :
    HasSum (fun n : ℤ => coeff f n * (u : K) ^ n) ((f : Kˣ → K) u) := by
  rw [coe_eq_lsum]; exact (isEntire_coeff f).hasSum u

/-- The coefficients are the unique ones representing `f`. -/
lemma eq_coeff {f : Entire K} {c : ℤ → K} (hc : IsEntire c) (h : (f : Kˣ → K) = lsum c) :
    coeff f = c :=
  eq_of_lsum_eq (isEntire_coeff f) hc ((coe_eq_lsum f).symm.trans h)

lemma ext_coeff {f g : Entire K} (h : coeff f = coeff g) : f = g :=
  Subtype.ext ((coe_eq_lsum f).trans (h ▸ (coe_eq_lsum g).symm))

lemma ext_coeff_iff {f g : Entire K} : f = g ↔ coeff f = coeff g :=
  ⟨fun h => h ▸ rfl, ext_coeff⟩

/-- The element with prescribed (everywhere convergent) coefficients. -/
def ofCoeff (c : ℤ → K) (hc : IsEntire c) : Entire K := ⟨lsum c, c, hc, rfl⟩

@[simp] lemma coeff_ofCoeff (c : ℤ → K) (hc : IsEntire c) : coeff (ofCoeff c hc) = c :=
  eq_coeff hc rfl

lemma coe_add (f g : Entire K) : ((f + g : Entire K) : Kˣ → K) = f + g := rfl

lemma coe_mul (f g : Entire K) : ((f * g : Entire K) : Kˣ → K) = f * g := rfl

lemma coeff_add (f g : Entire K) : coeff (f + g) = coeff f + coeff g := by
  refine eq_coeff ((isEntire_coeff f).add (isEntire_coeff g)) (funext fun u => ?_)
  rw [coe_add, Pi.add_apply]
  exact ((((coeff_spec f u).add (coeff_spec g u)).congr_fun
    (fun n => by simp [add_mul])).tsum_eq).symm

lemma coeff_zero : coeff (0 : Entire K) = 0 :=
  eq_coeff isEntire_zero (funext fun u => by simp [lsum])

lemma coeff_neg (f : Entire K) : coeff (-f) = -coeff f := by
  have h := coeff_add f (-f)
  rw [add_neg_cancel, coeff_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma coeff_mul (f g : Entire K) : coeff (f * g) = conv (coeff f) (coeff g) := by
  refine eq_coeff ((isEntire_coeff f).conv (isEntire_coeff g)) (funext fun u => ?_)
  rw [coe_mul, Pi.mul_apply, coe_eq_lsum f, coe_eq_lsum g]
  exact (conv_hasSum (isEntire_coeff f) (isEntire_coeff g) u).tsum_eq.symm

lemma coe_algebraMap (a : K) : ((algebraMap K (Entire K) a : Entire K) : Kˣ → K) = fun _ => a :=
  rfl

lemma coeff_algebraMap (a : K) : coeff (algebraMap K (Entire K) a) = Pi.single 0 a := by
  refine eq_coeff (isEntire_single 0 a) (funext fun u => ?_)
  rw [coe_algebraMap, lsum, (hasSum_single_lsum 0 a u).tsum_eq]
  simp

lemma coeff_one : coeff (1 : Entire K) = Pi.single 0 1 := by
  rw [← map_one (algebraMap K (Entire K)), coeff_algebraMap]

lemma coeff_smul (a : K) (f : Entire K) : coeff (a • f) = a • coeff f := by
  rw [Algebra.smul_def, coeff_mul, coeff_algebraMap]
  funext l
  have : conv (Pi.single 0 a) (coeff f) l = a * coeff f l := by
    rw [conv]
    rw [tsum_eq_single l fun m hm => by simp [sub_eq_zero, Ne.symm hm]]
    simp
  simpa using this

/-- **The monomial `Uᵏ`.** -/
def mono (k : ℤ) : Entire K := ofCoeff (Pi.single k 1) (isEntire_single k 1)

lemma coe_mono (k : ℤ) : ((mono k : Entire K) : Kˣ → K) = fun u : Kˣ => (u : K) ^ k := by
  funext u
  change lsum _ u = _
  rw [lsum, (hasSum_single_lsum k 1 u).tsum_eq, one_mul]

@[simp] lemma coeff_mono (k : ℤ) : coeff (mono k : Entire K) = Pi.single k 1 := coeff_ofCoeff _ _

lemma mono_zero : (mono 0 : Entire K) = 1 :=
  ext_coeff (by rw [coeff_mono, coeff_one])

lemma mono_add (j k : ℤ) : (mono (j + k) : Entire K) = mono j * mono k := by
  refine Subtype.ext ?_
  rw [coe_mul, coe_mono, coe_mono, coe_mono]
  funext u
  simp [zpow_add₀ (Units.ne_zero u)]

/-- Multiplication by `Uᵏ` shifts the coefficients. -/
lemma coeff_mono_mul (k : ℤ) (f : Entire K) (l : ℤ) :
    coeff (mono k * f) l = coeff f (l - k) := by
  rw [coeff_mul, coeff_mono, conv,
    tsum_eq_single (l - k) fun m hm => by
      simp [sub_eq_iff_eq_add, show ¬ l = k + m from fun h => hm (by omega)]]
  simp

lemma isUnit_mono (k : ℤ) : IsUnit (mono k : Entire K) :=
  isUnit_iff_exists_inv.mpr ⟨mono (-k), by rw [← mono_add, add_neg_cancel, mono_zero]⟩

end Entire

end Iut.Frobenioid.BAn
