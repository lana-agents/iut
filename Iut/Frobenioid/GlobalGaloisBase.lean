/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalGaloisRlf
import Iut.Frobenioid.Thm34Irr
import Iut.Frobenioid.Thm34DivSlim
import Mathlib.FieldTheory.Galois.Profinite
import LocalClassFieldTheory.NumberField.KroneckerDensity.Bauer

/-!
# The base of the realified global Frobenioid over `B(Gal(F̃/F))⁰` is category-theoretic

[FrdI], Theorem 6.4(iv) (l.5726–5735 of `~/iut-scratch/wall/txt/The Geometry of Frobenioids
I.txt`) uses "the equivalence `D₁ ≅ D₂` induced by `Ψ` — cf. (i); Corollary 4.11(ii)". By
[FrdI], Theorem 6.4(i) (proof, l.5752–5756), `D = B(G)⁰` is Div-slim because "any automorphism of
a number field that fixes all of the valuations of the number field is clearly equal to the
identity automorphism", and `D` need not be slim (`G` finite nontrivial). This file proves:

**`GlobalGaloisRlf.preservesBase`**: every equivalence `Ψ : C^rlf_{F̃₁/F₁} ≌ C^rlf_{F̃₂/F₂}` of the
realified Frobenioids of [FrdI], Example 6.3 lies over a functor `B(G₁)⁰ → B(G₂)⁰`
(`PreservesBase`), and preserves the Frobenius structure (`GlobalGaloisRlf.thm34`).

## Ingredients

* [FrdI], Theorem 3.4(ii), (iii) via irreducible morphisms (`Model.typeCorresp_irr`,
  `Thm34Irr.lean`): `B(G)⁰` has irreducible factorizations and effective ℝ-divisors have no
  irreducible elements (`phiRlfGal_noIrreducible`);
* the order-theoretic hypotheses `GoodDiv` of `Thm34DivSlim.lean` for the cones of effective
  ℝ-divisors (`phiRlfGal_goodDiv`: coordinatewise arguments);
* **Div-slimness** (`phiRlfGal_autFaithful`). An automorphism `h` of `G/H` acts on
  `L = F̃^H` by `σ = sigma h`; if `σ^*[w]` meets `[w]` for every finite place `w`, then
  `σ(𝔭_w) ⊆ 𝔭_w` for every prime `𝔭_w` of `O_L` (`map_le_of_eZ_pos`). At a prime of degree one
  (`O_L/𝔭 ≅ 𝔽_p`, on which every ring endomorphism is the identity) this gives
  `σ(a) ≡ a mod 𝔭` for all `a ∈ O_L` (`sub_mem_of_map_le`); there are infinitely many primes of
  degree one (`NumberField.infinite_degOnePrimes`, LCFT), and a nonzero element lies in only
  finitely many primes, so `σ = id` (**`eq_id_of_map_le`**). Finally `sigma h = id` forces
  `h = id` by infinite Galois theory (`fixingSubgroup_fixedField`; `eq_id_of_sigma_eq`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField FractionalIdeal IsDedekindDomain

open scoped nonZeroDivisors

/-! ### Automorphisms of a number field fixing all primes -/

section FixPrimes

variable {K : Type*} [Field K] [NumberField K]

/-- `primeU w` is the prime ideal `𝔭_w`, as a fractional ideal. -/
lemma primeU_eq (w : FinitePlace K) :
    ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) =
      ((FinitePlace.equivHeightOneSpectrum w).asIdeal : FI K) := by
  refine Arakelov.FracIdeal.eq_of_count_eq (unit_ne_zero _)
    (coeIdeal_ne_zero.mpr (HeightOneSpectrum.ne_bot _)) fun v => ?_
  obtain ⟨w', rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective v
  rw [count_eq_toZFin, toZFin_primeU]
  classical
  by_cases h : w = w'
  · subst h
    rw [Finsupp.single_eq_same, count_self]
  · rw [Finsupp.single_apply, if_neg h, count_maximal_coprime]
    exact fun h' => h (FinitePlace.equivHeightOneSpectrum.injective h')

/-- If `σ^*[w]` contains `[w]`, then `σ(𝔭_w) ⊆ 𝔭_w`. -/
lemma map_le_of_eZ_pos (σ : K →+* K) (w : FinitePlace K) (h : 0 < eZ σ w w) :
    Ideal.map (RingOfIntegers.mapRingHom σ) (FinitePlace.equivHeightOneSpectrum w).asIdeal ≤
      (FinitePlace.equivHeightOneSpectrum w).asIdeal := by
  have key : extIdeal σ ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) ≤
      ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) :=
    (le_iff_toZFin (Additive.ofMul (extU σ (Additive.toMul (primeU w)))) (primeU w)).2
      fun u => by
        classical
        rw [toZFin_primeU, Finsupp.single_apply]
        split_ifs with hu
        · subst hu
          exact h
        · exact eZ_nonneg σ w u
  rw [primeU_eq, extIdeal, extendedHom'_apply, extended_coeIdeal_eq_map] at key
  exact (coeIdeal_le_coeIdeal K).mp key

/-- **At a prime of degree one fixed by `σ`, `σ` induces the identity on `O_K/𝔭 ≅ 𝔽_p`.** -/
lemma sub_mem_of_map_le (σ : K →+* K) (P : HeightOneSpectrum (𝓞 K))
    (hP : (Ideal.absNorm P.asIdeal).Prime)
    (hle : Ideal.map (RingOfIntegers.mapRingHom σ) P.asIdeal ≤ P.asIdeal) (a : 𝓞 K) :
    RingOfIntegers.mapRingHom σ a - a ∈ P.asIdeal := by
  set p := Ideal.absNorm P.asIdeal
  haveI : Fact p.Prime := ⟨hP⟩
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 K ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact (Submodule.cardQuot_apply _).symm
  haveI : CharP (𝓞 K ⧸ P.asIdeal) p := charP_of_card_eq_prime hcard
  let ψ := Ideal.quotientMap P.asIdeal (RingOfIntegers.mapRingHom σ)
    (Ideal.map_le_iff_le_comap.mp hle)
  let ι := ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P.asIdeal)
  have hι : Function.Surjective ι :=
    ((Fintype.bijective_iff_injective_and_card ι).mpr
      ⟨ι.injective, by rw [ZMod.card, hcard]⟩).2
  have hψ : ψ.comp ι = ι := RingHom.ext_zmod _ _
  obtain ⟨z, hz⟩ := hι (Ideal.Quotient.mk _ a)
  have h1 := congrArg (fun f => f z) hψ
  simp only [RingHom.comp_apply, hz, ψ, Ideal.quotientMap_mk] at h1
  exact Ideal.Quotient.eq.mp h1

/-- **A ring endomorphism of a number field mapping every prime of `O_K` into itself is the
identity.** -/
theorem eq_id_of_map_le (σ : K →+* K)
    (h : ∀ P : HeightOneSpectrum (𝓞 K),
      Ideal.map (RingOfIntegers.mapRingHom σ) P.asIdeal ≤ P.asIdeal) :
    σ = RingHom.id K := by
  have hint : ∀ a : 𝓞 K, RingOfIntegers.mapRingHom σ a = a := by
    intro a
    by_contra hne
    have hy : RingOfIntegers.mapRingHom σ a - a ≠ 0 := sub_ne_zero.mpr hne
    have hfin := Ideal.finite_factors (I := Ideal.span {RingOfIntegers.mapRingHom σ a - a})
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
    exact NumberField.infinite_degOnePrimes K (hfin.subset fun P hP =>
      Ideal.dvd_span_singleton.mpr (sub_mem_of_map_le σ P hP (h P) a))
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have ha := congrArg (fun y : 𝓞 K => (y : K)) (hint a)
  have hb' := congrArg (fun y : 𝓞 K => (y : K)) (hint b)
  simp only [RingOfIntegers.mapRingHom_apply] at ha hb'
  rw [map_div₀, RingHom.id_apply]
  change σ (a : K) / σ (b : K) = (a : K) / (b : K)
  rw [ha, hb']

/-- **If `σ^*[w]` meets `[w]` at every finite place, then `σ = id`.** -/
theorem eq_id_of_eZ_pos (σ : K →+* K) (h : ∀ w : FinitePlace K, 0 < eZ σ w w) :
    σ = RingHom.id K := by
  refine eq_id_of_map_le σ fun P => ?_
  obtain ⟨w, rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective P
  exact map_le_of_eZ_pos σ w (h w)

end FixPrimes

/-! ### The order of effective ℝ-divisors -/

section EffOrder

variable {K : Type*} [Field K] [NumberField K]

/-- `a ≤ b` for ℝ-arithmetic divisors. -/
def LeR (a b : ArithDiv K) : Prop := b - a ∈ effCone K

lemma leR_iff {a b : ArithDiv K} : LeR a b ↔ (∀ w, a.1 w ≤ b.1 w) ∧ ∀ v, a.2 v ≤ b.2 v := by
  unfold LeR
  rw [mem_effCone]
  simp only [Prod.fst_sub, Prod.snd_sub, Finsupp.coe_sub, Pi.sub_apply, sub_nonneg]

/-- The divisor `t·[w]` at a finite place. -/
noncomputable def sF (w : FinitePlace K) (t : ℝ) : ArithDiv K := (Finsupp.single w t, 0)

lemma sF_mem {w : FinitePlace K} {t : ℝ} (ht : 0 ≤ t) : sF w t ∈ effCone K := by
  classical
  rw [mem_effCone]
  refine ⟨fun u => ?_, fun v => le_rfl⟩
  simp only [sF, Finsupp.single_apply]
  split_ifs <;> simp [ht]

lemma sF_ne_zero {w : FinitePlace K} {t : ℝ} (ht : t ≠ 0) : sF w t ≠ 0 := by
  intro h
  have : t = 0 := by simpa [sF] using congrArg (fun x : ArithDiv K => x.1 w) h
  exact ht this

lemma sF_le {w : FinitePlace K} {t : ℝ} {a : ArithDiv K} (ha : a ∈ effCone K)
    (h : t ≤ a.1 w) : LeR (sF w t) a := by
  classical
  rw [mem_effCone] at ha
  rw [leR_iff]
  refine ⟨fun u => ?_, fun v => by simpa [sF] using ha.2 v⟩
  simp only [sF, Finsupp.single_apply]
  split_ifs with hu
  · subst hu; exact h
  · exact ha.1 u

open Classical in
/-- The divisor `t·[v]` at an infinite place. -/
noncomputable def sI (v : InfinitePlace K) (t : ℝ) : ArithDiv K :=
  (0, fun v' => if v' = v then t else 0)

lemma sI_mem {v : InfinitePlace K} {t : ℝ} (ht : 0 ≤ t) : sI v t ∈ effCone K := by
  classical
  rw [mem_effCone]
  refine ⟨fun u => le_rfl, fun v' => ?_⟩
  simp only [sI]
  split_ifs <;> simp [ht]

lemma sI_ne_zero {v : InfinitePlace K} {t : ℝ} (ht : t ≠ 0) : sI v t ≠ 0 := by
  classical
  intro h
  have : t = 0 := by simpa [sI] using congrFun (congrArg (fun x : ArithDiv K => x.2) h) v
  exact ht this

lemma sI_le {v : InfinitePlace K} {t : ℝ} {a : ArithDiv K} (ha : a ∈ effCone K)
    (h : t ≤ a.2 v) : LeR (sI v t) a := by
  classical
  rw [mem_effCone] at ha
  rw [leR_iff]
  refine ⟨fun u => by simpa [sI] using ha.1 u, fun v' => ?_⟩
  simp only [sI]
  split_ifs with hv
  · subst hv; exact h
  · exact ha.2 v'

end EffOrder

/-! ### Chain-primes, Riesz decomposition, archimedean property -/

section EffGood

variable {K : Type*} [Field K] [NumberField K]

/-- Disjointness for ℝ-arithmetic divisors. -/
def DisjR (a b : ArithDiv K) : Prop := ∀ r ∈ effCone K, LeR r a → LeR r b → r = 0

/-- Chain-primes for ℝ-arithmetic divisors. -/
def ChainR (a : ArithDiv K) : Prop :=
  a ∈ effCone K ∧ a ≠ 0 ∧ ∀ b ∈ effCone K, ∀ c ∈ effCone K, LeR b a → LeR c a → LeR b c ∨ LeR c b

lemma chainR_nsmul {a : ArithDiv K} (ha : ChainR a) {n : ℕ} (hn : 0 < n) : ChainR (n • a) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨(effCone K).nsmul_mem ha.1 n, fun h0 => ha.2.1 ?_, fun b hb c hc hbc hcc => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul ℝ] at h0
    exact (smul_eq_zero.mp h0).resolve_left (by positivity)
  have sc : ∀ z : ArithDiv K, z ∈ effCone K → LeR z (n • a) →
      ((1 / (n : ℝ)) • z) ∈ effCone K ∧ LeR ((1 / (n : ℝ)) • z) a := by
    intro z hz hza
    rw [mem_effCone] at hz
    rw [leR_iff] at hza
    refine ⟨mem_effCone.mpr ⟨fun w => ?_, fun v => ?_⟩, leR_iff.mpr ⟨fun w => ?_, fun v => ?_⟩⟩
    · simp only [Prod.smul_fst, Finsupp.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hz.1 w)
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hz.2 v)
    · have := hza.1 w
      simp only [Prod.smul_fst, Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']
      linarith
    · have := hza.2 v
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']
      linarith
  obtain ⟨hb', hba⟩ := sc b hb hbc
  obtain ⟨hc', hca⟩ := sc c hc hcc
  have back : ∀ z z' : ArithDiv K, LeR ((1 / (n : ℝ)) • z) ((1 / (n : ℝ)) • z') → LeR z z' := by
    intro z z' h
    rw [leR_iff] at h ⊢
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have := h.1 w
      simp only [Prod.smul_fst, Finsupp.smul_apply, smul_eq_mul] at this
      exact le_of_mul_le_mul_left this (by positivity)
    · have := h.2 v
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul] at this
      exact le_of_mul_le_mul_left this (by positivity)
  rcases ha.2.2 _ hb' _ hc' hba hca with h | h
  · exact Or.inl (back b c h)
  · exact Or.inr (back c b h)

lemma riesz_R {p x y : ArithDiv K} (hp : p ∈ effCone K) (hx : x ∈ effCone K)
    (hy : y ∈ effCone K) (hle : LeR p (x + y)) (hd : DisjR p x) : LeR p y := by
  have hp' := mem_effCone.mp hp
  have hx' := mem_effCone.mp hx
  have hy' := mem_effCone.mp hy
  rw [leR_iff] at hle ⊢
  simp only [Prod.fst_add, Prod.snd_add, Finsupp.coe_add, Pi.add_apply] at hle
  refine ⟨fun w => ?_, fun v => ?_⟩
  · by_contra hlt
    push Not at hlt
    have h0 := hd (sF w (p.1 w - y.1 w)) (sF_mem (by linarith))
      (sF_le hp (by linarith [hy'.1 w])) (sF_le hx (by linarith [hle.1 w]))
    exact sF_ne_zero (by linarith) h0
  · by_contra hlt
    push Not at hlt
    have h0 := hd (sI v (p.2 v - y.2 v)) (sI_mem (by linarith))
      (sI_le hp (by linarith [hy'.2 v])) (sI_le hx (by linarith [hle.2 v]))
    exact sI_ne_zero (by linarith) h0

lemma arch_R {d e : ArithDiv K} (hd : d ∈ effCone K) (hk : ∀ k : ℕ, LeR (k • d) e) : d = 0 := by
  have hd' := mem_effCone.mp hd
  have hk' : ∀ k : ℕ, (∀ w, (k : ℝ) * d.1 w ≤ e.1 w) ∧ ∀ v, (k : ℝ) * d.2 v ≤ e.2 v := by
    intro k
    have := leR_iff.mp (hk k)
    simpa only [Prod.smul_fst, Prod.smul_snd, Finsupp.smul_apply, Pi.smul_apply,
      nsmul_eq_mul] using this
  have key : ∀ t s : ℝ, 0 ≤ t → (∀ k : ℕ, (k : ℝ) * t ≤ s) → t = 0 := by
    intro t s ht h
    by_contra hne
    have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (s / t)
    have := h k
    rw [div_lt_iff₀ hpos] at hk
    linarith
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · exact key _ _ (hd'.1 w) fun k => (hk' k).1 w
  · exact key _ _ (hd'.2 v) fun k => (hk' k).2 v

lemma sF_le_sF_iff {w : FinitePlace K} {b : ArithDiv K} (hb : b ∈ effCone K)
    (hbw : LeR b (sF w 1)) : (∀ u, u ≠ w → b.1 u = 0) ∧ ∀ v, b.2 v = 0 := by
  classical
  have hb' := mem_effCone.mp hb
  rw [leR_iff] at hbw
  refine ⟨fun u hu => le_antisymm ?_ (hb'.1 u), fun v => le_antisymm ?_ (hb'.2 v)⟩
  · have := hbw.1 u
    simpa [sF, Finsupp.single_apply, Ne.symm hu] using this
  · simpa [sF] using hbw.2 v

/-- `[w]` is a chain-prime. -/
lemma sF_one_chainR (w : FinitePlace K) : ChainR (sF w 1) := by
  refine ⟨sF_mem zero_le_one, sF_ne_zero one_ne_zero, fun b hb c hc hbw hcw => ?_⟩
  obtain ⟨hb1, hb2⟩ := sF_le_sF_iff hb hbw
  obtain ⟨hc1, hc2⟩ := sF_le_sF_iff hc hcw
  have hb' := mem_effCone.mp hb
  have hc' := mem_effCone.mp hc
  rcases le_total (b.1 w) (c.1 w) with h | h
  · left
    rw [leR_iff]
    refine ⟨fun u => ?_, fun v => by rw [hb2 v, hc2 v]⟩
    by_cases hu : u = w
    · subst hu; exact h
    · rw [hb1 u hu]; exact hc'.1 u
  · right
    rw [leR_iff]
    refine ⟨fun u => ?_, fun v => by rw [hb2 v, hc2 v]⟩
    by_cases hu : u = w
    · subst hu; exact h
    · rw [hc1 u hu]; exact hb'.1 u

/-- If `r ≠ 0` is effective with `r ≤ [w]`, then `r_w > 0`. -/
lemma pos_of_le_sF {w : FinitePlace K} {r : ArithDiv K} (hr : r ∈ effCone K) (hr0 : r ≠ 0)
    (hrw : LeR r (sF w 1)) : 0 < r.1 w := by
  obtain ⟨h1, h2⟩ := sF_le_sF_iff hr hrw
  refine lt_of_le_of_ne ((mem_effCone.mp hr).1 w) fun h0 => hr0 ?_
  refine Prod.ext (Finsupp.ext fun u => ?_) (funext fun v => h2 v)
  by_cases hu : u = w
  · subst hu; simp [← h0]
  · exact h1 u hu

end EffGood

/-! ### The divisor monoid `Φ^rlf` over `B(G)⁰` is good and Div-slim -/

section Good

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- Effective ℝ-divisors have no irreducible elements. -/
theorem phiRlfGal_noIrreducible : NoIrreducible (phiRlfGal F E) :=
  fun A z hz h0 => GlobalRealified.phiRlf_noIrreducible (Fix A) pt z hz h0

/-- **The divisor monoids `Φ^rlf(E^H)` are good**: chain-primes are stable under `n ≥ 1`,
Riesz decomposition, archimedean. -/
theorem phiRlfGal_goodDiv : (phiRlfGal F E).GoodDiv :=
  ⟨fun A _ _ ha hn => chainR_nsmul (K := Fix A) ha hn,
    fun A _ _ _ hp hx hy hle hd => riesz_R (K := Fix A) hp hx hy hle hd,
    fun A _ _ hd _ hk => arch_R (K := Fix A) hd hk⟩

omit [NumberField F] in
variable {F E} in
/-- **`sigma h = id` forces `h = id`** (infinite Galois theory: the open subgroup `H` is the
fixing subgroup of its fixed field). -/
lemma eq_id_of_sigma_eq {A : OrbitObj (GalG F E)} (h : A ⟶ A)
    (hs : sigma h = RingHom.id (Fix A)) : h = 𝟙 A := by
  have hmem : repG h ∈ A.H := by
    have hc : IsClosed (A.H : Set (GalG F E)) := Subgroup.isClosed_of_isOpen _ A.isOpen
    have := InfiniteGalois.fixingSubgroup_fixedField (k := F) (K := E) ⟨A.H, hc⟩
    change repG h ∈ ((⟨A.H, hc⟩ : ClosedSubgroup (GalG F E)) : Subgroup (GalG F E))
    rw [← this, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun y : Fix A => (y : E)) (RingHom.congr_fun hs ⟨x, hx⟩)
    simpa using this
  have h1 : h.toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
    rw [← OrbitHom.mk_rep h]
    exact QuotientGroup.eq.mpr (by simpa using hmem)
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [OrbitHom.apply_mk, h1]
  change _ = QuotientGroup.mk g
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- **`B(G)⁰` is Div-slim with respect to `Φ^rlf`** ([FrdI], Theorem 6.4(i)): an automorphism
of `G/H` fixing every place of `E^H` is the identity. -/
theorem phiRlfGal_autFaithful : (phiRlfGal F E).AutFaithful := by
  intro A h _ hfix
  refine eq_id_of_sigma_eq h (eq_id_of_eZ_pos (sigma h) fun w => ?_)
  obtain ⟨r, hr, hr₁, hr₂, hr0⟩ :=
    DivMonoid.not_disj_iff.mp (hfix (sF w 1) (sF_one_chainR (K := Fix A) w))
  have hpos := pos_of_le_sF (K := Fix A) hr hr0 hr₂
  have h1 := (leR_iff.mp hr₁).1 w
  change r.1 w ≤ pbRFin (sigma h) (Finsupp.single w 1) w at h1
  rw [pbRFin_apply, Finsupp.sum_single_index (by simp), one_mul] at h1
  exact_mod_cast hpos.trans_le h1

end Good

/-! ### The base functor -/

section Main

variable {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [Algebra F₁ E₁] [IsGalois F₁ E₁]
variable {F₂ E₂ : Type} [Field F₂] [NumberField F₂] [Field E₂] [Algebra F₂ E₂] [IsGalois F₂ E₂]

/-- **[FrdI], Theorem 3.4(ii), (iii) (types)** for the realified Frobenioids of [FrdI],
Example 6.3 over `B(G)⁰`. -/
theorem GlobalGaloisRlf.typeCorresp (Ψ : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψ.IsEquivalence] : Model.TypeCorresp Ψ :=
  Model.typeCorresp_irr OrbitObj.baseHyp OrbitObj.irredBase (phiRlfGal_noIrreducible F₁ E₁)
    OrbitObj.baseHyp OrbitObj.irredBase (phiRlfGal_noIrreducible F₂ E₂) Ψ

/-- **[FrdI], Theorem 3.4(iii)** for the realified Frobenioids of [FrdI], Example 6.3 over
`B(G)⁰`: every equivalence preserves the Frobenius structure. -/
theorem GlobalGaloisRlf.thm34 (Ψ : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψ.IsEquivalence] :
    PreservesFrobeniusStructure (Model.toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁))
      (Model.toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂)) Ψ :=
  Model.thm34_irr OrbitObj.baseHyp OrbitObj.irredBase (phiRlfGal_noIrreducible F₁ E₁)
    OrbitObj.baseHyp OrbitObj.irredBase (phiRlfGal_noIrreducible F₂ E₂) Ψ

/-- **The base is category-theoretic** ([FrdI], Corollary 4.11(ii), used in Theorem 6.4(iv)):
every equivalence `C^rlf_{F̃₁/F₁} ≌ C^rlf_{F̃₂/F₂}` lies over a functor
`B(Gal(F̃₁/F₁))⁰ → B(Gal(F̃₂/F₂))⁰`. -/
theorem GlobalGaloisRlf.preservesBase (Ψ : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψ.IsEquivalence] :
    PreservesBase (Model.toElem (phiRlfGal F₁ E₁) (bRlfGal F₁ E₁) (divRlfGal F₁ E₁))
      (Model.toElem (phiRlfGal F₂ E₂) (bRlfGal F₂ E₂) (divRlfGal F₂ E₂)) Ψ :=
  Model.preservesBase_divSlim Ψ (GlobalGaloisRlf.typeCorresp Ψ) (phiRlfGal_goodDiv F₁ E₁)
    (phiRlfGal_goodDiv F₂ E₂) (phiRlfGal_autFaithful F₂ E₂)

/-- **Morphisms with the same base are mapped to morphisms with the same base.** -/
theorem GlobalGaloisRlf.base_map_eq (Ψ : GlobalGaloisRlf F₁ E₁ ⥤ GlobalGaloisRlf F₂ E₂)
    [Ψ.IsEquivalence] {X Y : GlobalGaloisRlf F₁ E₁} (φ φ' : X ⟶ Y) (h : φ.base = φ'.base) :
    (Ψ.map φ).base = (Ψ.map φ').base :=
  Model.base_map_eq_of_base_eq_divSlim Ψ (GlobalGaloisRlf.typeCorresp Ψ)
    (phiRlfGal_goodDiv F₁ E₁) (phiRlfGal_goodDiv F₂ E₂) (phiRlfGal_autFaithful F₂ E₂) φ φ' h

end Main

end Frobenioid

end Iut
