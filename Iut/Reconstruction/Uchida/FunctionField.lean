/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Uchida.Basic
import WeilCurves.FunctionField.LinearSystem

/-!
# Uchida's lemma: correctness for function fields of curves ([AbsTopIII], Proposition 1.3)

[AbsTopIII], Proposition 1.3 (l.1700–1721 of `~/iut-scratch/papers/txt/Topics in Absolute
Anabelian Geometry III.txt`): for a proper curve `X` over an algebraically closed field `k`,
"there exists a functorial algorithm for constructing the additive structure on `K_X^× ∪ {0}`
[i.e., arising from the field structure of `K_X`]" from the triple
`(K_X^×, {ord_x}_{x ∈ X(k)}, {U_x})`. The algorithm itself is `ValEvalData.AddRel`
(`Iut/Reconstruction/Uchida/Basic.lean`, MR9 step U1). This file is the **bridge** of MR9 step
U2: it builds the triple of a function field `K / k` (`ofFunctionField k K`: the group `Kˣ`, the
places of `K / k` — the points of the proper curve — with `ord_P` and the principal units
`U_P = {f | f(P) = 1}`), and proves that the algorithm returns the field addition:

* **`ofFunctionField.addRel_iff`**: `AddRel a b c ↔ a + b = c` in `K` (via
  `WithZero Kˣ ≃* K`);
* **`ofFunctionField.addRel_iso_iff`**: the same for any abstract triple isomorphic to
  `(Kˣ, {ord_P}, {U_P})` (combined with the functoriality `ValEvalData.Iso.addRel_iff` of U1).

The curve-side input is `WeilCurves.FunctionField.LinearSystem` (in `weil-curves`, which has the
Riemann–Roch theory of function fields): values at places, Proposition 1.1(ii)
(`Divisor.ell_eq_sInf`), Proposition 1.2(i) (`Divisor.exists_uchidaConfig`) and the two-point
evaluation behind Proposition 1.2(ii), (iii) (`Divisor.existsUnique_isValue_two`). Here we only
translate:

* `mem_consts_iff`: the constants `⋂ Ker(ord_P)` are `kˣ`;
* `evalAt_iff`: `EvalAt P f c` iff `f(P) = c ≠ 0`;
* `mem_gamma_iff`, `ell_eq`: `Γ^×(E) = L(E) \ {0}` and the `l(E)` of the algorithm is
  `dim_k L(E)`;
* `isConstSum_iff`: the characterisation of `λ + μ` in Proposition 1.2(iii) is correct;
* `isNegOne_iff`: the algorithm's `−1` is `−1`.
-/

namespace Iut.Reconstruction.Uchida

universe u

open WeilCurves.FunctionField

variable (k : Type*) (K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [IsFunctionField k K]

/-- `ord_P` as a homomorphism `Kˣ → ℤ`. -/
noncomputable def ordHom (P : Place k K) : Kˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (P.ord f)
  map_one' := by simp [P.ord_one]
  map_mul' f g := by
    simp [P.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

/-- **The triple of [AbsTopIII], Proposition 1.3(a)–(c) for a function field** `K / k`:
`(Kˣ, {ord_P}, {U_P})` with `U_P` the principal units at `P` (`f(P) = 1`). -/
noncomputable abbrev ofFunctionField : ValEvalData.{u} where
  G := Kˣ
  P := Place k K
  ord := ordHom k K
  U P := P.1.principalUnitGroup

namespace ofFunctionField

variable {k K}

/-- Shorthand for the triple. -/
local notation "𝒟" => ofFunctionField k K

lemma val_eq (P : Place k K) (f : Kˣ) : (𝒟).val P f = P.ord f := rfl

/-- The constants `⋂ Ker(ord_P)` are the elements of `kˣ`. -/
lemma mem_consts_iff (c : Kˣ) : c ∈ (𝒟).consts ↔ ∃ a : k, algebraMap k K a = c := by
  rw [ValEvalData.mem_consts_iff, exists_algebraMap_iff_forall_ord_eq_zero]
  rfl

lemma mem_U_iff (P : Place k K) (f : Kˣ) :
    f ∈ (𝒟).U P ↔ ((f : K) - 1) ∈ P.1.nonunits := by
  change f ∈ P.1.principalUnitGroup ↔ _
  rw [ValuationSubring.mem_principalUnitGroup_iff, ValuationSubring.mem_nonunits_iff]

/-- **Evaluation**: `EvalAt P f c` iff `c = a ∈ kˣ` and `f(P) = a`. -/
lemma evalAt_iff (P : Place k K) (f c : Kˣ) :
    (𝒟).EvalAt P f c ↔ ∃ a : k, a ≠ 0 ∧ algebraMap k K a = c ∧ P.IsValue f a := by
  unfold ValEvalData.EvalAt
  rw [val_eq, mem_consts_iff, mem_U_iff]
  constructor
  · rintro ⟨h0, ⟨a, ha⟩, hU⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [← ha, map_zero])
    refine ⟨a, ha0, ha, (P.isValue_iff_div_sub_one_mem ha0).mpr ?_⟩
    simpa [ha, div_eq_mul_inv] using hU
  · rintro ⟨a, ha0, ha, hv⟩
    refine ⟨(P.ord_eq_zero_iff_isValue f.ne_zero).mpr ⟨a, ha0, hv⟩, ⟨a, ha⟩, ?_⟩
    have := (P.isValue_iff_div_sub_one_mem ha0).mp hv
    simpa [ha, div_eq_mul_inv] using this

/-- `Γ^×(E) = L(E) \ {0}`. -/
lemma mem_gamma_iff (E : Place k K →₀ ℤ) (f : Kˣ) :
    f ∈ (𝒟).Gamma E ↔ (f : K) ∈ Divisor.L E := by
  rw [Divisor.mem_L, or_iff_right f.ne_zero]
  simp only [ValEvalData.Gamma, Set.mem_setOf_eq, val_eq]
  exact forall_congr' fun P ↦ by omega

lemma gamma_eq_empty_iff (E : Place k K →₀ ℤ) : (𝒟).Gamma E = ∅ ↔ Divisor.L E = ⊥ := by
  rw [Set.eq_empty_iff_forall_notMem, Submodule.eq_bot_iff]
  constructor
  · intro h f hf
    by_contra hf0
    exact h (Units.mk0 f hf0) ((mem_gamma_iff E _).mpr hf)
  · intro h f hf
    exact f.ne_zero (h f ((mem_gamma_iff E f).mp hf))

lemma deg_eq (E : Place k K →₀ ℤ) : (𝒟).deg E = Divisor.deg E := by
  simp only [ValEvalData.deg, Divisor.deg, Place.deg_eq_one_of_isAlgClosed, Nat.cast_one,
    mul_one]

/-- The `l(E)` of the algorithm (Proposition 1.1(ii)) is `dim_k L(E)`. -/
lemma ell_eq (E : Place k K →₀ ℤ) : (𝒟).ell E = Divisor.ell E := by
  rw [Divisor.ell_eq_sInf, ValEvalData.ell]
  congr 1
  ext d
  simp only [ValEvalData.ellSet, Set.mem_setOf_eq, deg_eq]
  exact exists_congr fun E' ↦ and_congr_right' (and_congr_right' (gamma_eq_empty_iff _))

lemma isConfig_iff (E : Place k K →₀ ℤ) (x y₁ y₂ : Place k K) :
    (𝒟).IsConfig E x y₁ y₂ ↔ x ≠ y₁ ∧ x ≠ y₂ ∧ y₁ ≠ y₂ ∧ E x = 0 ∧ E y₁ = 0 ∧ E y₂ = 0 ∧
      Divisor.ell E = 2 ∧ Divisor.L (E - Finsupp.single x 1 - Finsupp.single y₁ 1) = ⊥ ∧
      Divisor.L (E - Finsupp.single x 1 - Finsupp.single y₂ 1) = ⊥ ∧
      Divisor.L (E - Finsupp.single y₁ 1 - Finsupp.single y₂ 1) = ⊥ := by
  simp only [ValEvalData.IsConfig, ell_eq, Divisor.ell_eq_zero_iff]

/-- A unit with a value `a ≠ 0`, as an element of `Kˣ`. -/
noncomputable def constUnit {a : k} (ha : a ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap k K a) (by simpa using ha)

omit [IsAlgClosed k] [IsFunctionField k K] in
@[simp] lemma coe_constUnit {a : k} (ha : a ≠ 0) :
    (constUnit (K := K) ha : K) = algebraMap k K a := rfl

lemma evalAt_constUnit {P : Place k K} {f : Kˣ} {a : k} (ha : a ≠ 0) (h : P.IsValue f a) :
    (𝒟).EvalAt P f (constUnit ha) :=
  (evalAt_iff P f _).mpr ⟨a, ha, rfl, h⟩

/-- **[AbsTopIII], Proposition 1.2(iii)** (l.1667–1673): the algorithm's `IsConstSum` is the
addition of constants. -/
theorem isConstSum_iff {u v w : Kˣ} {a b c : k} (ha : algebraMap k K a = u)
    (hb : algebraMap k K b = v) (hc : algebraMap k K c = w) :
    (𝒟).IsConstSum u v w ↔ a + b = c := by
  have ha0 : a ≠ 0 := by rintro rfl; exact u.ne_zero (by rw [← ha, map_zero])
  have hb0 : b ≠ 0 := by rintro rfl; exact v.ne_zero (by rw [← hb, map_zero])
  have hc0 : c ≠ 0 := by rintro rfl; exact w.ne_zero (by rw [← hc, map_zero])
  have hinj := (algebraMap k K).injective
  constructor
  · rintro ⟨E, x, y₁, y₂, hC, f₁, f₂, g, a₁, a₂, ⟨h1Γ, h1x, h1y, h1y'⟩, ⟨h2Γ, h2x, h2y, h2y'⟩,
      hgΓ, h3, h4, h5, h6, h7⟩
    rw [isConfig_iff] at hC
    obtain ⟨-, -, h12, -, hE₁, hE₂, hell, -, -, hL⟩ := hC
    rw [mem_gamma_iff] at h1Γ h2Γ hgΓ
    rw [evalAt_iff] at h1x h2x h3 h4 h5 h6 h7
    obtain ⟨a', -, ha', hv1x⟩ := h1x
    obtain ⟨b', -, hb', hv2x⟩ := h2x
    obtain ⟨p₁, -, hp₁, hv1y⟩ := h3
    obtain ⟨p₁', -, hp₁', hvgy₁⟩ := h4
    obtain ⟨p₂, -, hp₂, hv2y⟩ := h5
    obtain ⟨p₂', -, hp₂', hvgy₂⟩ := h6
    obtain ⟨c', -, hc', hvgx⟩ := h7
    have e1 : a' = a := hinj (ha'.trans ha.symm)
    have e2 : b' = b := hinj (hb'.trans hb.symm)
    have e3 : p₁' = p₁ := hinj (hp₁'.trans hp₁.symm)
    have e4 : p₂' = p₂ := hinj (hp₂'.trans hp₂.symm)
    have e5 : c' = c := hinj (hc'.trans hc.symm)
    subst e1 e2 e3 e4 e5
    -- `f₁(y₂) = 0`, `f₂(y₁) = 0`
    rw [val_eq] at h1y' h2y'
    have z1 : y₂.IsValue (f₁ : K) 0 :=
      y₂.isValue_zero_iff.mpr ((y₂.ord_pos_iff (f := (f₁ : K))).mp h1y').2
    have z2 : y₁.IsValue (f₂ : K) 0 :=
      y₁.isValue_zero_iff.mpr ((y₁.ord_pos_iff (f := (f₂ : K))).mp h2y').2
    -- `g = f₁ + f₂` by two-point uniqueness
    obtain ⟨F, -, hF⟩ :=
      Divisor.existsUnique_isValue_two h12 hE₁ hE₂ hell hL p₁' p₂'
    have hsum : ((g : K)) = f₁ + f₂ := by
      have hg := hF g ⟨hgΓ, hvgy₁, hvgy₂⟩
      have hf := hF ((f₁ : K) + f₂) ⟨add_mem h1Γ h2Γ, by simpa using hv1y.add z2,
        by simpa using z1.add hv2y⟩
      rw [hg, hf]
    rw [hsum] at hvgx
    exact (hv1x.add hv2x).unique hvgx
  · rintro rfl
    obtain ⟨E, x, y₁, y₂, hxy₁, hxy₂, h12, hEx, hE₁, hE₂, hell, hLx₁, hLx₂, hL⟩ :=
      Divisor.exists_uchidaConfig (k := k) (K := K)
    -- `f₁ = f_{a,1}`: `f₁(x) = a`, `f₁(y₂) = 0`; `f₂ = f_{b,2}`: `f₂(x) = b`, `f₂(y₁) = 0`
    obtain ⟨f₁, ⟨hf₁, hf₁x, hf₁y₂⟩, -⟩ :=
      Divisor.existsUnique_isValue_two hxy₂ hEx hE₂ hell hLx₂ a 0
    obtain ⟨f₂, ⟨hf₂, hf₂x, hf₂y₁⟩, -⟩ :=
      Divisor.existsUnique_isValue_two hxy₁ hEx hE₁ hell hLx₁ b 0
    obtain ⟨F0, -, hU⟩ := Divisor.existsUnique_isValue_two h12 hE₁ hE₂ hell hL 0 0
    -- their values at the other point are nonzero (else they would vanish at `y₁, y₂`)
    have hne : ∀ {f : K} {d : k} {y y' : Place k K}, f ∈ Divisor.L E → x.IsValue f d → d ≠ 0 →
        y.IsValue f (y.value f) → y'.IsValue f 0 →
        (∀ g, g ∈ Divisor.L E ∧ y.IsValue g 0 ∧ y'.IsValue g 0 → g = 0) → y.value f ≠ 0 := by
      intro f d y y' hf hfx hd hfy hfy' hU' h0
      rw [h0] at hfy
      have := hU' f ⟨hf, hfy, hfy'⟩
      subst this
      exact hd ((x.isValue_algebraMap 0).unique (by simpa using hfx)).symm
    have hU₁ : ∀ g, g ∈ Divisor.L E ∧ y₁.IsValue g 0 ∧ y₂.IsValue g 0 → g = 0 := fun g hg ↦
      (hU g hg).trans (hU 0 ⟨zero_mem _, by simpa using y₁.isValue_algebraMap (K := K) 0,
        by simpa using y₂.isValue_algebraMap (K := K) 0⟩).symm
    have hU₂ : ∀ g, g ∈ Divisor.L E ∧ y₂.IsValue g 0 ∧ y₁.IsValue g 0 → g = 0 :=
      fun g ⟨h1, h2, h3⟩ ↦ hU₁ g ⟨h1, h3, h2⟩
    have hm₁ := Divisor.mem_place_of_mem_L hE₁ hf₁
    have hm₂ := Divisor.mem_place_of_mem_L hE₂ hf₂
    have hv₁ := y₁.isValue_value hm₁
    have hv₂ := y₂.isValue_value hm₂
    have hn₁ := hne hf₁ hf₁x ha0 hv₁ hf₁y₂ hU₁
    have hn₂ := hne hf₂ hf₂x hb0 hv₂ hf₂y₁ hU₂
    have hf₁0 : f₁ ≠ 0 := by
      rintro rfl; exact ha0 ((x.isValue_algebraMap 0).unique (by simpa using hf₁x)).symm
    have hf₂0 : f₂ ≠ 0 := by
      rintro rfl; exact hb0 ((x.isValue_algebraMap 0).unique (by simpa using hf₂x)).symm
    have hgx := hf₁x.add hf₂x
    have hg0 : f₁ + f₂ ≠ 0 := by
      intro h; rw [h] at hgx
      exact hc0 ((x.isValue_algebraMap 0).unique (by simpa using hgx)).symm
    refine ⟨E, x, y₁, y₂, (isConfig_iff E x y₁ y₂).mpr
      ⟨hxy₁, hxy₂, h12, hEx, hE₁, hE₂, hell, hLx₁, hLx₂, hL⟩,
      Units.mk0 f₁ hf₁0, Units.mk0 f₂ hf₂0, Units.mk0 (f₁ + f₂) hg0,
      constUnit hn₁, constUnit hn₂, ⟨(mem_gamma_iff E _).mpr hf₁, ?_, ?_, ?_⟩,
      ⟨(mem_gamma_iff E _).mpr hf₂, ?_, ?_, ?_⟩, (mem_gamma_iff E _).mpr (add_mem hf₁ hf₂),
      evalAt_constUnit hn₁ hv₁, evalAt_constUnit hn₁ (by simpa using hv₁.add hf₂y₁),
      evalAt_constUnit hn₂ hv₂, evalAt_constUnit hn₂ (by simpa using hf₁y₂.add hv₂),
      (evalAt_iff x _ _).mpr ⟨a + b, hc0, hc, hgx⟩⟩
    · exact (evalAt_iff x _ _).mpr ⟨a, ha0, ha, hf₁x⟩
    · rw [val_eq]
      exact (y₁.ord_eq_zero_iff_isValue hf₁0).mpr ⟨_, hn₁, hv₁⟩
    · rw [val_eq]
      exact (y₂.ord_pos_iff (f := f₁)).mpr ⟨hf₁0, y₂.isValue_zero_iff.mp hf₁y₂⟩
    · exact (evalAt_iff x _ _).mpr ⟨b, hb0, hb, hf₂x⟩
    · rw [val_eq]
      exact (y₂.ord_eq_zero_iff_isValue hf₂0).mpr ⟨_, hn₂, hv₂⟩
    · rw [val_eq]
      exact (y₁.ord_pos_iff (f := f₂)).mpr ⟨hf₂0, y₁.isValue_zero_iff.mp hf₂y₁⟩

/-- The algorithm's `−1` (`IsNegOne`) is `−1`. -/
theorem isNegOne_iff (u : Kˣ) : (𝒟).IsNegOne u ↔ (u : K) = -1 := by
  have hm1 : (-1 : Kˣ) ∈ (𝒟).consts :=
    (mem_consts_iff _).mpr ⟨-1, by simp⟩
  constructor
  · rintro ⟨-, hsq, h1⟩
    have hsq' : ((u : K) - 1) * ((u : K) + 1) = 0 := by
      have := congrArg Units.val hsq
      simp only [Units.val_mul, Units.val_one] at this
      linear_combination this
    rcases mul_eq_zero.mp hsq' with h | h
    · have hu : u = 1 := Units.ext (by simpa [sub_eq_zero] using h)
      have := h1 hu (-1) hm1 (by simp)
      rw [hu]
      have h' := congrArg Units.val this
      simp only [Units.val_neg, Units.val_one] at h'
      rw [Units.val_one]
      exact h'.symm
    · exact eq_neg_of_add_eq_zero_left h
  · intro hu
    have hu' : u = -1 := Units.ext (by simpa using hu)
    subst hu'
    refine ⟨hm1, by simp, fun h c _ hc ↦ ?_⟩
    have hc' : ((c : K) - 1) * ((c : K) + 1) = 0 := by
      have := congrArg Units.val hc
      simp only [Units.val_mul, Units.val_one] at this
      linear_combination this
    have h2 : (-1 : K) = 1 := by simpa using congrArg Units.val h
    rcases mul_eq_zero.mp hc' with h' | h'
    · exact Units.ext (by simpa [sub_eq_zero] using h')
    · exact Units.ext (by rw [eq_neg_of_add_eq_zero_left h', h2, Units.val_one])

/-- The algorithm agrees with the addition of units: for `f, g, h ∈ Kˣ`, `AddRel f g h` (the
last clause: `f(P) + g(P) = h(P)` wherever all three are units) iff `f + g = h`. -/
theorem forall_isConstSum_iff (f g h : Kˣ) :
    (∀ (x : Place k K) (u v w : Kˣ), (𝒟).EvalAt x f u → (𝒟).EvalAt x g v →
      (𝒟).EvalAt x h w → (𝒟).IsConstSum u v w) ↔ (f : K) + g = h := by
  classical
  constructor
  · intro H
    by_contra hne
    have hd : (f : K) + g - h ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨x, -, hx⟩ := Place.exists_ord_eq_zero (k := k) (K := K) Set.finite_empty
      {(f : K), (g : K), (h : K), (f : K) + g - h}
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hx
    obtain ⟨hfx, hgx, hhx, hdx⟩ := hx
    obtain ⟨a, ha0, hva⟩ := (x.ord_eq_zero_iff_isValue f.ne_zero).mp hfx
    obtain ⟨b, hb0, hvb⟩ := (x.ord_eq_zero_iff_isValue g.ne_zero).mp hgx
    obtain ⟨c, hc0, hvc⟩ := (x.ord_eq_zero_iff_isValue h.ne_zero).mp hhx
    obtain ⟨d, hd0, hvd⟩ := (x.ord_eq_zero_iff_isValue hd).mp hdx
    have hs := H x _ _ _ (evalAt_constUnit ha0 hva) (evalAt_constUnit hb0 hvb)
      (evalAt_constUnit hc0 hvc)
    rw [isConstSum_iff rfl rfl rfl] at hs
    have := ((hva.add hvb).sub hvc).unique hvd
    rw [hs, sub_self] at this
    exact hd0 this.symm
  · intro hfgh x u v w hu hv hw
    rw [evalAt_iff] at hu hv hw
    obtain ⟨a, -, ha, hva⟩ := hu
    obtain ⟨b, -, hb, hvb⟩ := hv
    obtain ⟨c, -, hc, hvc⟩ := hw
    rw [isConstSum_iff ha hb hc]
    rw [← hfgh] at hvc
    exact (hva.add hvb).unique hvc

open Classical in
/-- **Correctness of Uchida's algorithm** ([AbsTopIII], Proposition 1.3, for the function field
`K` of a proper curve over an algebraically closed field `k`): under `WithZero Kˣ ≃* K`, the
reconstructed relation `AddRel a b c` is `a + b = c`. -/
theorem addRel_iff (a b c : WithZero Kˣ) :
    (𝒟).AddRel a b c ↔
      WithZero.withZeroUnitsEquiv a + WithZero.withZeroUnitsEquiv b =
        WithZero.withZeroUnitsEquiv c := by
  have e0 : WithZero.withZeroUnitsEquiv (0 : WithZero Kˣ) = 0 := rfl
  have ec : ∀ f : Kˣ, WithZero.withZeroUnitsEquiv (f : WithZero Kˣ) = (f : K) := fun _ ↦ rfl
  have hinj : ∀ a b : WithZero Kˣ,
      WithZero.withZeroUnitsEquiv a = WithZero.withZeroUnitsEquiv b ↔ a = b :=
    fun a b ↦ WithZero.withZeroUnitsEquiv.injective.eq_iff
  unfold ValEvalData.AddRel
  induction a using WithZero.recZeroCoe with
  | zero =>
    rw [e0, zero_add, hinj]
    simp only [true_and, ne_eq, not_true_eq_false, false_and, and_false, or_false,
      WithZero.zero_ne_coe, false_and, exists_false]
    exact eq_comm
  | coe f =>
    induction b using WithZero.recZeroCoe with
    | zero =>
      rw [e0, add_zero, hinj]
      simp only [WithZero.coe_ne_zero, false_and, true_and, ne_eq, not_false_eq_true,
        WithZero.zero_ne_coe, and_false, exists_false, or_false, false_or]
      exact eq_comm
    | coe g =>
      induction c using WithZero.recZeroCoe with
      | zero =>
        rw [e0, ec, ec]
        simp only [WithZero.coe_ne_zero, false_and, WithZero.coe_inj, exists_and_left,
          exists_eq_left', true_and, false_or, WithZero.zero_ne_coe, and_false, exists_false,
          or_false]
        rw [isNegOne_iff]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        constructor
        · intro h
          have := congrArg (· * (f : K)) h
          simp only [inv_mul_cancel_right₀ f.ne_zero] at this
          linear_combination this
        · intro h
          field_simp
          linear_combination h
      | coe h =>
        rw [ec, ec, ec, ← forall_isConstSum_iff (k := k)]
        simp only [WithZero.coe_ne_zero, false_and, WithZero.coe_inj, exists_and_left,
          exists_eq_left', false_or, and_false, exists_false]

open Classical in
/-- **Uchida's lemma** ([AbsTopIII], Proposition 1.3): the additive structure of `K` is
recovered from **any** triple isomorphic to `(Kˣ, {ord_P}, {U_P})`: for an isomorphism of triples
`e`, the relation `AddRel` of the abstract triple, transported back along `e`, is the addition of
`K`. -/
theorem addRel_iso_iff {D' : ValEvalData.{u}} (e : ValEvalData.Iso (𝒟) D') (x y z : K) :
    D'.AddRel (e.mapZ (WithZero.withZeroUnitsEquiv.symm x))
        (e.mapZ (WithZero.withZeroUnitsEquiv.symm y))
        (e.mapZ (WithZero.withZeroUnitsEquiv.symm z)) ↔ x + y = z := by
  rw [e.addRel_iff, addRel_iff]
  simp only [MulEquiv.apply_symm_apply]

end ofFunctionField

end Iut.Reconstruction.Uchida
