/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.DivOrder
import Iut.Frobenioid.GlobalPic
import Iut.Frobenioid.Thm34Rlf

/-!
# [FrdI], Theorem 6.4(ii): the degree of an equivalence of global realified Frobenioids

[FrdI], Theorem 6.4(ii) (p. 114): for an equivalence of categories `Ψ^rlf : C₁^rlf ≅ C₂^rlf` of
realified arithmetic Frobenioids there is `deg(Ψ^rlf) ∈ ℝ_{>0}` such that for all
Frobenius-trivial `A₁`, `A₂ = Ψ^rlf(A₁)`, the composite of `δ_{A₂}` with the isomorphism
`Pic_Φ(A₁) ≅ Pic_Φ(A₂)` determined by `Ψ^rlf` (via Corollary 4.10, 4.11(iii)) equals
`deg(Ψ^rlf)·δ_{A₁}`.

Here this is proved for the global realified Frobenioids `C^⊩(K)` of IUT I, Example 3.5 (the
case `F̃ = F` of [FrdI], Theorem 6.4, base category `Pt`), for **every** equivalence
`F : C^⊩(K) ≌ C^⊩(L)`. The isomorphism `Pic_Φ(A₁) → Pic_Φ(A₂)` is the one induced on divisor
classes by `τ_X : Φ₁(A_X) → Φ₂(A_{F X})` (`Model.divMap`, [FrdI], Corollary 4.11(iii),
`Iut/Frobenioid/DivOrder.lean`), which sends `Div(φ)` to `Div(F φ)` for every pre-step `φ`.

* `GlobalRealified.isFrobeniusTrivial_iff`: the Frobenius-trivial objects are exactly the objects
  of degree `0`.
* `GlobalRealified.degOf F` (`= deg(Ψ^rlf)`), `degOf_pos`;
* `GlobalRealified.degree_map`: `deg(F X) = deg(Ψ)·deg(X)` for every object of degree `≥ 0`;
* `GlobalRealified.isFrobeniusTrivial_map`: `F` preserves Frobenius-trivial objects;
* **`GlobalRealified.thm64ii`**: `δ_{F X}([τ_X z]) = deg(Ψ)·δ_X([z])` for Frobenius-trivial `X`
  and every effective `z`; `picMap_mk`: the classes `[τ_X z]` are the values of the
  `ℝ`-linear isomorphism `Pic_Φ(A₁) ≅ Pic_Φ(A₂)`, `δ_{A₂} ∘ picMap = deg(Ψ)·δ_{A₁}`;
* `GlobalRealified.thm34_deg_id`: the automorphism `Ψ_{ℕ≥1}` of Theorem 3.4(iii) is the
  identity for these Frobenioids.

The proof: `X ↦ deg(F X)` factors through a strictly increasing `g : ℝ → ℝ` (objects are
classified by their degree, `nonempty_iso_iff_degree_eq`, and linear morphisms `X → Y` exist iff
`deg X ≤ deg Y`), and `g(n·t) = σ(n)·g(t)` by the Frobenius morphisms; monotonicity forces
`σ = id` and `g(t) = g(1)·t` for `t ≥ 0`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

/-! ### Monotone homogeneous functions on `ℝ_{≥0}` -/

/-- A monotone `g : ℝ → ℝ` with `g(n·t) = n·g(t)` for `n ≥ 1` is linear on `ℝ_{≥0}`. -/
theorem eq_mul_of_monotone_of_nsmul {g : ℝ → ℝ} (hm : Monotone g)
    (hn : ∀ (n : ℕ), 0 < n → ∀ t, g (n * t) = n * g t) (t : ℝ) (ht : 0 ≤ t) :
    g t = g 1 * t := by
  have h0 : g 0 = 0 := by
    have := hn 2 two_pos 0
    simp only [mul_zero] at this
    push_cast at this
    linarith
  have hinv : ∀ n : ℕ, 0 < n → g (1 / n) = g 1 / n := by
    intro n hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    have := hn n hn0 (1 / n)
    rw [mul_one_div_cancel hn'] at this
    field_simp
    linarith
  have hq : ∀ q : ℚ, 0 < q → g q = g 1 * q := by
    intro q hq0
    have hnum : 0 < q.num := Rat.num_pos.mpr hq0
    have hq' : (q : ℝ) = (q.num.toNat : ℕ) * (1 / (q.den : ℕ)) := by
      rw [Rat.cast_def]
      have : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnum.le
      rw [this]
      ring
    rw [hq', hn _ (by omega) _, hinv _ q.den_pos]
    ring
  have hc : 0 ≤ g 1 := h0 ▸ hm zero_le_one
  rcases ht.eq_or_lt with rfl | ht
  · rw [h0, mul_zero]
  rcases lt_trichotomy (g t) (g 1 * t) with hlt | heq | hgt
  · exfalso
    rcases hc.eq_or_lt with hc0 | hc0
    · rw [← hc0, zero_mul] at hlt
      exact absurd (h0 ▸ hm ht.le) (not_le.mpr hlt)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (g t / g 1) < t from
      max_lt ht ((div_lt_iff₀ hc0).mpr (by linarith)))
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
    have h1 : g t / g 1 < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have h2 := hm hq2.le
    rw [hq q (by exact_mod_cast hq0)] at h2
    rw [div_lt_iff₀ hc0] at h1
    linarith
  · exact heq
  · exfalso
    have hc0 : 0 < g 1 := by
      rcases hc.eq_or_lt with hc0 | hc0
      · exfalso
        have := hq 1 one_pos
        have h2 := hm (show t ≤ (⌈t⌉₊ : ℕ) from Nat.le_ceil t)
        have hceil : 0 < ⌈t⌉₊ := Nat.ceil_pos.mpr ht
        rw [show ((⌈t⌉₊ : ℕ) : ℝ) = (⌈t⌉₊ : ℕ) * 1 by ring, hn _ hceil, ← hc0] at h2
        rw [← hc0, zero_mul] at hgt
        linarith
      · exact hc0
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < g t / g 1 from
      (lt_div_iff₀ hc0).mpr (by linarith))
    have hq0 : (0 : ℝ) < q := ht.trans hq1
    have h2 := hm hq1.le
    rw [hq q (by exact_mod_cast hq0)] at h2
    rw [lt_div_iff₀ hc0] at hq2
    linarith

/-- A strictly increasing multiplicative bijection of `ℕ_{≥1}` is the identity. -/
theorem pnat_mulEquiv_eq_of_strictMono (σ : ℕ+ ≃* ℕ+) (hσ : StrictMono σ) (n : ℕ+) :
    σ n = n := by
  have h₁ : n ≤ σ n := hσ.id_le n
  have hσ' : StrictMono σ.symm := fun a b hab => by
    by_contra h
    exact (not_lt.mpr (hσ.monotone (not_lt.mp h))) (by simpa using hab)
  have h₂ : σ n ≤ σ (σ.symm n) := hσ.monotone (hσ'.id_le n)
  rw [MulEquiv.apply_symm_apply] at h₂
  exact le_antisymm h₂ h₁

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]

local notation "𝐏₁" => Model.toElem (phiRlf K) (bRlf K) (divBRlf K)
local notation "𝐏₂" => Model.toElem (phiRlf L) (bRlf L) (divBRlf L)

/-! ### Frobenius-trivial objects -/

/-- **The Frobenius-trivial objects of `C^⊩` are the objects of degree `0`.** -/
theorem isFrobeniusTrivial_iff (X : GlobalRealified K) :
    IsFrobeniusTrivial 𝐏₁ X ↔ X.degree = 0 := by
  constructor
  · rintro ⟨ζ, -, -, hζ⟩
    obtain ⟨h₂, -, hF⟩ := hζ 2
    have := degree_frobenius (ζ 2) hF
    rw [show (ζ 2).deg = 2 from h₂] at this
    push_cast at this
    linarith
  · intro h
    have hα : X.α ∈ ratFun K := ker_degArith_le h
    have hmem : ∀ n : ℕ, (n • X.α - X.α) ∈ ratFun K := fun n =>
      (ratFun K).sub_mem ((ratFun K).nsmul_mem hα n) hα
    let ζ : ℕ+ → (X ⟶ X) := fun n =>
      Model.mk' n (𝟙 _) 0 (effCone K).zero_mem ⟨_, hmem n⟩ (by
        change (n : ℕ) • X.α + 0 = X.α + ((n : ℕ) • X.α - X.α)
        abel)
    refine ⟨ζ, ?_, fun m n => ?_, fun n => ⟨rfl, rfl, ?_⟩⟩
    · refine Model.hom_ext rfl rfl rfl (Subtype.ext ?_)
      change (1 : ℕ) • X.α - X.α = 0
      simp
    · refine Model.hom_ext (mul_comm _ _) (Subsingleton.elim _ _) ?_ (Subtype.ext ?_)
      · change (0 : ArithDiv K) = 0 + (n : ℕ) • 0
        simp
      · change ((m * n : ℕ+) : ℕ) • X.α - X.α =
          ((n : ℕ) • X.α - X.α) + (n : ℕ) • ((m : ℕ) • X.α - X.α)
        rw [PNat.mul_coe, smul_sub, ← mul_smul, mul_comm]
        abel
    · exact (Model.isFrobeniusType_iff _).mpr ⟨rfl, isIso_pt _⟩

/-! ### The degree function of an equivalence -/

/-- The object `(pt, t·[v₀]/m_{v₀})` of degree `t` (for a fixed archimedean place `v₀`). -/
noncomputable def objOfDeg (t : ℝ) : GlobalRealified K :=
  open scoped Classical in
  ⟨pt, (0, Pi.single (Classical.arbitrary (NumberField.InfinitePlace K))
    (t / (Classical.arbitrary (NumberField.InfinitePlace K)).mult))⟩

lemma degree_objOfDeg (t : ℝ) : (objOfDeg (K := K) t).degree = t := by
  classical
  have hm : ((Classical.arbitrary (NumberField.InfinitePlace K)).mult : ℝ) ≠ 0 := by
    exact_mod_cast (Classical.arbitrary (NumberField.InfinitePlace K)).mult_pos.ne'
  change degArith K (0, Pi.single _ _) = t
  convert degArith_single_inf (K := K) (Classical.arbitrary _) _ using 1
  field_simp

lemma iso_objOfDeg (X : GlobalRealified K) : Nonempty (X ≅ objOfDeg X.degree) :=
  (nonempty_iso_iff_degree_eq _ _).mpr (degree_objOfDeg _).symm

/-- An effective divisor of degree `t ≥ 0`. -/
lemma exists_eff_of_degree {t : ℝ} (ht : 0 ≤ t) :
    ∃ z ∈ effCone K, degArith K z = t := by
  classical
  refine ⟨(objOfDeg (K := K) t).α, ?_, degree_objOfDeg t⟩
  rw [mem_effCone]
  refine ⟨fun w => le_refl _, fun v => ?_⟩
  change 0 ≤ Pi.single (M := fun _ => ℝ) _ _ v
  rw [Pi.single_apply]
  split_ifs
  · exact div_nonneg ht (by exact_mod_cast (Nat.zero_le _))
  · exact le_refl _

/-- The object `(pt, α_X + z)`. -/
noncomputable abbrev stepTgt (X : GlobalRealified K) (z : ArithDiv K) : GlobalRealified K :=
  ⟨pt, X.α + z⟩

/-- **The pre-step `X → (pt, α_X + z)`** for an effective `z`. -/
noncomputable def step (X : GlobalRealified K) (z : ArithDiv K) (hz : z ∈ effCone K) :
    X ⟶ stepTgt X z :=
  Model.mk1 (𝟙 _) z hz 0 (by change X.α + z = X.α + z + 0; rw [add_zero])

lemma degree_step_target (X : GlobalRealified K) (z : ArithDiv K) :
    (stepTgt X z).degree = X.degree + degArith K z :=
  map_add _ _ _

variable (F : GlobalRealified K ⥤ GlobalRealified L)

/-- `g(t) = deg(F(pt, t))`. -/
noncomputable def degFun (t : ℝ) : ℝ := (F.obj (objOfDeg t)).degree

lemma degree_map_eq_degFun (X : GlobalRealified K) :
    (F.obj X).degree = degFun F X.degree := by
  obtain ⟨e⟩ := iso_objOfDeg X
  exact degree_eq_of_iso (F.mapIso e)

lemma linear_map (hP : PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F) {X Y : GlobalRealified K}
    (φ : X ⟶ Y) (h : φ.deg = 1) : (F.map φ).deg = 1 :=
  (hP.2.1 φ).1 h

lemma degree_map_le (hP : PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F) {X Y : GlobalRealified K}
    (φ : X ⟶ Y) (h : φ.deg = 1) : (F.obj X).degree ≤ (F.obj Y).degree := by
  have := mul_degree_le (F.map φ)
  rwa [linear_map F hP φ h, PNat.one_coe, Nat.cast_one, one_mul] at this

variable [F.IsEquivalence]

lemma degFun_strictMono (hP : PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F) :
    StrictMono (degFun F) := by
  intro s t hst
  obtain ⟨z, hz, hdz⟩ := exists_eff_of_degree (K := K) (sub_nonneg.mpr hst.le)
  let X : GlobalRealified K := objOfDeg s
  have hY : (stepTgt X z).degree = t := by
    rw [degree_step_target, hdz, degree_objOfDeg]; ring
  have hle := degree_map_le F hP (step X z hz) rfl
  rw [degree_map_eq_degFun, degree_map_eq_degFun, hY, degree_objOfDeg] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  have : Nonempty (F.obj (objOfDeg (K := K) s) ≅ F.obj (objOfDeg t)) :=
    (nonempty_iso_iff_degree_eq _ _).mpr heq
  obtain ⟨e⟩ := this
  have := degree_eq_of_iso (F.preimageIso e)
  rw [degree_objOfDeg, degree_objOfDeg] at this
  exact hst.ne this

omit [F.IsEquivalence] in
lemma degFun_frob (hP : PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F) (σ : ℕ+ ≃* ℕ+)
    (hσ : ∀ {A B : GlobalRealified K} (φ : A ⟶ B), degFr 𝐏₂ (F.map φ) = σ (degFr 𝐏₁ φ))
    (n : ℕ+) (t : ℝ) : degFun F (n * t) = σ n * degFun F t := by
  let X : GlobalRealified K := objOfDeg t
  have hF := (hP.1 (Model.frob X n)).1 (Model.frob_isFrobeniusType X n)
  have h := degree_frobenius _ hF
  have hd : (F.map (Model.frob X n)).deg = σ n := hσ (Model.frob X n)
  rw [hd, degree_map_eq_degFun, degree_map_eq_degFun, degree_objOfDeg] at h
  have hX : GlobalRealified.degree (K := K) ⟨X.base, (n : ℕ) • X.α⟩ = n * t := by
    change degArith K ((n : ℕ) • X.α) = _
    rw [map_nsmul, nsmul_eq_mul]
    exact congrArg _ (degree_objOfDeg t)
  rwa [hX] at h

/-- **The Frobenius degree is preserved**: the automorphism `Ψ_{ℕ≥1}` of [FrdI], Theorem
3.4(iii), is the identity for every equivalence of global realified Frobenioids. -/
theorem thm34_deg_id {X Y : GlobalRealified K} (φ : X ⟶ Y) : (F.map φ).deg = φ.deg := by
  have hP := thm34 F
  obtain ⟨σ, hσ⟩ := hP.2.2.2.2.2.2.2
  have hg := degFun_strictMono F hP
  have h0 : degFun F 0 = 0 := by
    have := degFun_frob F hP σ hσ 2 0
    rw [mul_zero] at this
    have h2 : σ 2 ≠ 1 := fun h => by
      have := σ.injective (h.trans (map_one σ).symm)
      exact absurd this (by decide)
    have : ((σ 2 : ℕ) : ℝ) ≠ 1 := by
      intro h'
      exact h2 (PNat.eq (by exact_mod_cast h'))
    have h3 : (1 - ((σ 2 : ℕ) : ℝ)) * degFun F 0 = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by linarith : ((σ 2 : ℕ) : ℝ) = 1) this
    · exact h
  have h1 : 0 < degFun F 1 := h0 ▸ hg one_pos
  have hmono : StrictMono σ := by
    intro m n hmn
    have := hg (show ((m : ℕ) : ℝ) * 1 < (n : ℕ) * 1 by
      rw [mul_one, mul_one]; exact_mod_cast hmn)
    rw [degFun_frob F hP σ hσ, degFun_frob F hP σ hσ] at this
    have := lt_of_mul_lt_mul_right this h1.le
    exact_mod_cast this
  rw [show (F.map φ).deg = degFr 𝐏₂ (F.map φ) from rfl, hσ,
    pnat_mulEquiv_eq_of_strictMono σ hmono]
  rfl

lemma degFun_nsmul (n : ℕ) (hn : 0 < n) (t : ℝ) : degFun F (n * t) = n * degFun F t := by
  have hP := thm34 F
  obtain ⟨σ, hσ⟩ := hP.2.2.2.2.2.2.2
  have h := degFun_frob F hP σ hσ ⟨n, hn⟩ t
  have hd : σ ⟨n, hn⟩ = ⟨n, hn⟩ := by
    let φ := Model.frob (objOfDeg (K := K) t) ⟨n, hn⟩
    have h1 := thm34_deg_id F φ
    have h2 : (F.map φ).deg = σ φ.deg := hσ φ
    rw [h1] at h2
    exact h2.symm
  rw [hd] at h
  exact h

/-- **`deg(Ψ^rlf)`** ([FrdI], Theorem 6.4(ii)): the degree of `F` applied to an object of
degree `1`. -/
noncomputable def degOf : ℝ := degFun F 1

theorem degOf_pos : 0 < degOf F := by
  have hg := degFun_strictMono F (thm34 F)
  have h0 : degFun F 0 = 0 := by
    have := degFun_nsmul F 2 two_pos 0
    simp only [mul_zero] at this
    push_cast at this
    linarith
  exact h0 ▸ hg one_pos

/-- **`deg(F X) = deg(Ψ)·deg(X)`** for every object of nonnegative degree. -/
theorem degree_map {X : GlobalRealified K} (hX : 0 ≤ X.degree) :
    (F.obj X).degree = degOf F * X.degree := by
  rw [degree_map_eq_degFun]
  exact eq_mul_of_monotone_of_nsmul (degFun_strictMono F (thm34 F)).monotone
    (degFun_nsmul F) _ hX

/-- **`F` preserves Frobenius-trivial objects** ([FrdI], Theorem 6.4(ii): "`Ψ^rlf` preserves
Frobenius-trivial objects"). -/
theorem isFrobeniusTrivial_map {X : GlobalRealified K} (hX : IsFrobeniusTrivial 𝐏₁ X) :
    IsFrobeniusTrivial 𝐏₂ (F.obj X) := by
  rw [isFrobeniusTrivial_iff] at hX ⊢
  rw [degree_map F hX.ge, hX, mul_zero]

/-- `δ(τ_X(z)) = deg(Ψ)·δ(z)` for every object `X` of nonnegative degree and effective `z`. -/
theorem degArith_divMap {X : GlobalRealified K} (hX : 0 ≤ X.degree) (z : ArithDiv K)
    (hz : z ∈ effCone K) :
    degArith L (Model.divMap F X z hz) = degOf F * degArith K z := by
  have hlin := linear_map F (thm34 F) (step X z hz) rfl
  have h := degree_hom (F.map (step X z hz))
  rw [hlin, PNat.one_coe, Nat.cast_one, one_mul] at h
  have hz0 := degArith_nonneg hz
  have hY : 0 ≤ (stepTgt X z).degree := by
    rw [degree_step_target]; linarith
  rw [degree_map F hX, degree_map F hY, degree_step_target] at h
  change degArith L (F.map (Model.stepTo X z hz)).div = _
  have : Model.stepTo X z hz = step X z hz := rfl
  rw [this]
  linarith

/-- **The isomorphism `Pic_Φ(A₁) ≅ Pic_Φ(A₂)` determined by `F`**: `δ_{A₂}⁻¹ ∘ deg(Ψ) ∘ δ_{A₁}`;
by `picMap_mk` it sends the class of every effective `z` to the class of `τ_X(z)` (for `X`
Frobenius-trivial), so it is the unique additive map with this property (effective divisors
generate `Pic_Φ`). -/
noncomputable def picMap : (ArithDiv K ⧸ ratFun K) ≃ₗ[ℝ] (ArithDiv L ⧸ ratFun L) :=
  (picDegEquiv K).trans ((LinearEquiv.smulOfNeZero ℝ ℝ (degOf F) (degOf_pos F).ne').trans
    (picDegEquiv L).symm)

/-- **[FrdI], Theorem 6.4(ii)** for the global realified Frobenioids: for every equivalence
`F : C^⊩(K) ≌ C^⊩(L)` there is `deg(Ψ) > 0` such that for every Frobenius-trivial `X` and every
effective divisor `z` on `A_X`, `δ_{F X}([τ_X z]) = deg(Ψ)·δ_X([z])`, where
`τ_X(Div φ) = Div(F φ)` for all pre-steps `φ` out of `X` (`Model.div_map_preStep`). -/
theorem thm64ii : 0 < degOf F ∧ ∀ (X : GlobalRealified K), IsFrobeniusTrivial 𝐏₁ X →
    IsFrobeniusTrivial 𝐏₂ (F.obj X) ∧
    ∀ (z : ArithDiv K) (hz : z ∈ effCone K),
      picDeg L (Submodule.Quotient.mk (Model.divMap F X z hz)) =
        degOf F * picDeg K (Submodule.Quotient.mk z) := by
  refine ⟨degOf_pos F, fun X hX => ⟨isFrobeniusTrivial_map F hX, fun z hz => ?_⟩⟩
  rw [picDeg_mk, picDeg_mk]
  exact degArith_divMap F ((isFrobeniusTrivial_iff X).mp hX).ge z hz

/-- `picMap` sends `[z]` to `[τ_X z]` (for `X` Frobenius-trivial and `z` effective). -/
theorem picMap_mk {X : GlobalRealified K} (hX : IsFrobeniusTrivial 𝐏₁ X) (z : ArithDiv K)
    (hz : z ∈ effCone K) :
    picMap F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (Model.divMap F X z hz) := by
  apply (picDegEquiv L).injective
  simp only [picMap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.smulOfNeZero_apply, picDegEquiv_apply, smul_eq_mul]
  exact ((thm64ii F).2 X hX).2 z hz |>.symm

/-- `δ_{A₂} ∘ picMap = deg(Ψ)·δ_{A₁}`. -/
theorem picDeg_picMap (x : ArithDiv K ⧸ ratFun K) :
    picDeg L (picMap F x) = degOf F * picDeg K x := by
  rw [← picDegEquiv_apply, picMap]
  simp

/-- `deg(Ψ)` is unique: it is determined by any effective divisor of nonzero degree on a
Frobenius-trivial object. -/
theorem degOf_unique {c : ℝ} {X : GlobalRealified K} (hX : IsFrobeniusTrivial 𝐏₁ X)
    {z : ArithDiv K} (hz : z ∈ effCone K) (hz0 : degArith K z ≠ 0)
    (h : degArith L (Model.divMap F X z hz) = c * degArith K z) : c = degOf F := by
  rw [degArith_divMap F ((isFrobeniusTrivial_iff X).mp hX).ge z hz] at h
  exact (mul_right_cancel₀ hz0 h).symm

end GlobalRealified

end Frobenioid

end Iut
