import Iut.EtaleTheta.CurveDivisorAux

/-!
# Counting the cusp orders

A pure counting statement on a Weierstrass curve: if `R = n / d` with `deg n, deg d ≤ 4N` has the
same even order at every point of a set `Z` of `2N` degree-one points, and `f` has order `≥ 1` at
all points of `Z` other than `none` and `P₀`, equal orders at `none` and `P₀`, and no zeros or poles
where `R` has no pole, then the poles of `R` are exactly in `Z`, `f` has order `1` at the points of
`Z ∖ {none, P₀}`, and order `1 - N` at `none` and `P₀`.
-/

namespace Iut.EtaleTheta

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **Cusp count**, with the lower bound `1 - N ≤ ord_∞ f` on the order at infinity. -/
theorem cusp_orders_of_count_of_le {N : ℕ} (hN : 2 ≤ N) {f R : W.FunctionField} (hf : f ≠ 0)
    {n d : W.CoordinateRing} (hn : n ≠ 0) (hd : d ≠ 0) (hnk : deg W n ≤ 4 * N)
    (hdk : deg W d ≤ 4 * N)
    (hR : R = algebraMap W.CoordinateRing W.FunctionField n /
      algebraMap W.CoordinateRing W.FunctionField d)
    (Z : Finset (ProjPoint W)) (hZ : Z.card = 2 * N) (hZdeg : ∀ p ∈ Z, degProjPt W p = 1)
    (P₀ : ProjPoint W) (hO : none ∈ Z) (hP₀ : P₀ ∈ Z) (hP₀O : P₀ ≠ none)
    (hA : ∀ p ∈ Z, p ≠ none → p ≠ P₀ → 1 ≤ divisorProj W f p)
    (hRZ : ∀ p ∈ Z, divisorProj W R p = divisorProj W R none)
    (hReven : Even (divisorProj W R none))
    (hfP₀ : divisorProj W f P₀ = divisorProj W f none)
    (hflow : 1 - (N : ℤ) ≤ divisorProj W f none)
    (hU : ∀ p, 0 ≤ divisorProj W R p → divisorProj W f p = 0) :
    ∀ p, divisorProj W R p < 0 → p ∈ Z ∧
      ((p ≠ none ∧ p ≠ P₀ ∧ divisorProj W f p = 1) ∨
        ((p = none ∨ p = P₀) ∧ divisorProj W f p = 1 - N)) := by
  classical
  set A := (Z.erase none).erase P₀ with hAdef
  have hAcard : A.card = 2 * N - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hP₀O, hP₀⟩),
      Finset.card_erase_of_mem hO, hZ]
    omega
  have hmemA : ∀ p, p ∈ A ↔ p ∈ Z ∧ p ≠ none ∧ p ≠ P₀ := by
    intro p; simp only [hAdef, Finset.mem_erase]; tauto
  obtain ⟨q, hq⟩ : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  obtain ⟨hqZ, hqO, hqP⟩ := (hmemA q).mp hq
  have hRq : divisorProj W R q < 0 := by
    by_contra h
    have h1 := hU q (not_lt.mp h)
    have h2 := hA q hqZ hqO hqP
    omega
  set r := divisorProj W R none with hr
  have hr2 : r ≤ -2 := by
    rw [hRZ q hqZ] at hRq
    obtain ⟨k, hk⟩ := hReven
    omega
  have hsumZ : ∑ p ∈ Z, (-divisorProj W R p) * (degProjPt W p : ℤ) = 2 * N * (-r) := by
    rw [Finset.sum_congr rfl (g := fun _ => -r) (fun p hp => by rw [hRZ p hp, hZdeg p hp]; simp)]
    simp [hZ]
  have hpoles : ∀ p, divisorProj W R p < 0 → p ∈ Z := by
    intro p hp
    by_contra hpZ
    have h := sum_pole_le hn hd hnk hdk hR (insert p Z)
    rw [Finset.sum_insert hpZ, hsumZ] at h
    have h1 : (1 : ℤ) ≤ (-divisorProj W R p) * (degProjPt W p : ℤ) :=
      one_le_mul_of_one_le_of_one_le (by omega) (by exact_mod_cast degProjPt_pos (W := W) p)
    push_cast at h
    nlinarith
  have hsupp : (divisorProj W f).support ⊆ Z := by
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    exact hpoles p (by by_contra h; exact hp (hU p (not_lt.mp h)))
  have hdeg0 : ∑ p ∈ Z, divisorProj W f p = 0 := by
    have h := degProj_divisorProj hf
    rw [degProj, Finsupp.sum_of_support_subset _ hsupp (fun p n => n * (degProjPt W p : ℤ))
      (fun _ _ => zero_mul _)] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun p hp => by rw [hZdeg p hp]; simp)
  set m := divisorProj W f none with hm
  have hsplit : ∑ p ∈ Z, divisorProj W f p = ∑ p ∈ A, divisorProj W f p + 2 * m := by
    rw [← Finset.sum_erase_add _ _ hO,
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hP₀O, hP₀⟩), hfP₀]
    ring
  have hAge : ∀ p ∈ A, 1 ≤ divisorProj W f p := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := (hmemA p).mp hp; exact hA p h1 h2 h3
  have hAsum : (A.card : ℤ) ≤ ∑ p ∈ A, divisorProj W f p := by
    simpa using Finset.card_nsmul_le_sum A _ 1 hAge
  have hNA : (A.card : ℤ) = 2 * N - 2 := by rw [hAcard]; omega
  have hm1 : m = 1 - N := by omega
  have hAeq : ∀ p ∈ A, divisorProj W f p = 1 := by
    have hsumA : ∑ p ∈ A, divisorProj W f p = A.card := by omega
    by_contra hne
    push Not at hne
    obtain ⟨p₁, hp₁, hne1⟩ := hne
    have hlt : ∑ p ∈ A, (1 : ℤ) < ∑ p ∈ A, divisorProj W f p :=
      Finset.sum_lt_sum hAge ⟨p₁, hp₁, lt_of_le_of_ne (hAge p₁ hp₁) (Ne.symm hne1)⟩
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
    omega
  intro p hp
  have hpZ := hpoles p hp
  refine ⟨hpZ, ?_⟩
  by_cases h1 : p = none
  · exact Or.inr ⟨Or.inl h1, by rw [h1]; exact hm1⟩
  by_cases h2 : p = P₀
  · exact Or.inr ⟨Or.inr h2, by rw [h2, hfP₀]; exact hm1⟩
  exact Or.inl ⟨h1, h2, hAeq p ((hmemA p).mpr ⟨hpZ, h1, h2⟩)⟩

/-- **Cusp count**: the parity form.  For even `N`, an odd order `ord_∞ f ≥ -N` is `≥ 1 - N`. -/
theorem cusp_orders_of_count {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N) {f R : W.FunctionField}
    (hf : f ≠ 0) {n d : W.CoordinateRing} (hn : n ≠ 0) (hd : d ≠ 0) (hnk : deg W n ≤ 4 * N)
    (hdk : deg W d ≤ 4 * N)
    (hR : R = algebraMap W.CoordinateRing W.FunctionField n /
      algebraMap W.CoordinateRing W.FunctionField d)
    (Z : Finset (ProjPoint W)) (hZ : Z.card = 2 * N) (hZdeg : ∀ p ∈ Z, degProjPt W p = 1)
    (P₀ : ProjPoint W) (hO : none ∈ Z) (hP₀ : P₀ ∈ Z) (hP₀O : P₀ ≠ none)
    (hA : ∀ p ∈ Z, p ≠ none → p ≠ P₀ → 1 ≤ divisorProj W f p)
    (hRZ : ∀ p ∈ Z, divisorProj W R p = divisorProj W R none)
    (hReven : Even (divisorProj W R none))
    (hfodd : Odd (divisorProj W f none))
    (hfP₀ : divisorProj W f P₀ = divisorProj W f none)
    (hflow : -(N : ℤ) ≤ divisorProj W f none)
    (hU : ∀ p, 0 ≤ divisorProj W R p → divisorProj W f p = 0) :
    ∀ p, divisorProj W R p < 0 → p ∈ Z ∧
      ((p ≠ none ∧ p ≠ P₀ ∧ divisorProj W f p = 1) ∨
        ((p = none ∨ p = P₀) ∧ divisorProj W f p = 1 - N)) := by
  refine cusp_orders_of_count_of_le hN hf hn hd hnk hdk hR Z hZ hZdeg P₀ hO hP₀ hP₀O hA hRZ
    hReven hfP₀ ?_ hU
  obtain ⟨a, ha⟩ := hfodd
  obtain ⟨b, hb⟩ := hNeven
  omega

end Iut.EtaleTheta
