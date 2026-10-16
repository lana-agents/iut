/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Arch
import Iut.Frobenioid.Thm64

/-!
# [FrdI], Corollary 4.11(iii), (iv) for the global realified Frobenioids

[FrdI], Corollary 4.11(iii) (p. 92): for Frobenioids of rationally standard type, an equivalence
`Ψ : C₁ ≅ C₂` induces an isomorphism of monoids `Ψ_Φ : Φ₁ ≅ Φ₂` over `Ψ_Base`; (iv): the square
`C₁ → F_{Φ₁} → F_{Φ₂}`, `C₁ → C₂ → F_{Φ₂}` 1-commutes, i.e. `Div(Ψ(φ)) = Ψ_Φ(Div(φ))` and
`degFr(Ψ(φ)) = degFr(φ)`. By [FrdI], Theorem 6.4(i), the realified arithmetic Frobenioids are of
rationally standard type.

For the global realified Frobenioids `C^⊩(K)` (IUT I, Example 3.5) over `Pt` this is proved here
for **every** equivalence `F : C^⊩(K) ≌ C^⊩(L)`, by a direct argument:

* the order isomorphisms `τ_X : Φ_K → Φ_L` of `Iut/Frobenioid/DivOrder.lean` satisfy
  `τ_X(a + z) = τ_X(a) + τ_{X+a}(z)` (`divMap_add`), depend only on the isomorphism class of `X`
  (`divMap_iso`), and are additive on *disjoint* pairs (`divMap_add_of_disjoint`: in the cone
  `ℝ_{≥0}^{(V_fin)} × ℝ_{≥0}^{V_∞}` the sum of disjoint elements is their least upper bound,
  which an order isomorphism preserves);
* hence `τ_{X+a}(z) = τ_X(z)` when `a, z` are disjoint, and since every degree is the degree of
  an effective divisor disjoint from `z_fin` (resp. `z_∞`), `τ_X` does not depend on `X`
  (`divMap_indep`).

Results (`F : C^⊩(K) ⥤ C^⊩(L)` an equivalence):

* `psiPhi F : effCone K → ArithDiv L` (`Ψ_Φ`), `psiPhi_mem`, `psiPhi_add`, `psiPhi_zero`,
  `psiPhi_le_iff` (an order isomorphism), `psiPhi_surjective`, `psiPhi_injective`;
* **`div_map`**: `Div(F φ) = Ψ_Φ(Div φ)` for **every** morphism `φ` (Corollary 4.11(iv));
  `deg_map`: `degFr(F φ) = degFr(φ)` (`thm34_deg_id`);
* **`degree_map_eq`**: `deg(F X) = deg(Ψ)·deg(X)` for **every** object `X` and
  `degArith_psiPhi`: `deg^arith(Ψ_Φ z) = deg(Ψ)·deg^arith(z)` ([FrdI], Theorem 6.4(ii)).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]

local notation "𝐏₁" => Model.toElem (phiRlf K) (bRlf K) (divBRlf K)
local notation "𝐏₂" => Model.toElem (phiRlf L) (bRlf L) (divBRlf L)

/-! ### Disjoint effective divisors -/

/-- `p, q` are **disjoint**: `0` is their only common effective lower bound. -/
def DisjointEff (p q : ArithDiv K) : Prop :=
  ∀ r ∈ effCone K, p - r ∈ effCone K → q - r ∈ effCone K → r = 0

/-- The coordinatewise minimum. -/
noncomputable def inf (p q : ArithDiv K) : ArithDiv K :=
  (Finsupp.zipWith min (min_self 0) p.1 q.1, fun v => min (p.2 v) (q.2 v))

lemma inf_fst (p q : ArithDiv K) (w : NumberField.FinitePlace K) :
    (inf p q).1 w = min (p.1 w) (q.1 w) := by
  simp only [inf, Finsupp.zipWith_apply]

lemma inf_snd (p q : ArithDiv K) (v : NumberField.InfinitePlace K) :
    (inf p q).2 v = min (p.2 v) (q.2 v) := rfl

lemma min_eq_zero_of_disjoint {p q : ArithDiv K} (hp : p ∈ effCone K) (hq : q ∈ effCone K)
    (h : DisjointEff p q) :
    (∀ w, min (p.1 w) (q.1 w) = 0) ∧ ∀ v, min (p.2 v) (q.2 v) = 0 := by
  have h0 : inf p q = 0 := by
    refine h _ ⟨fun w => ?_, fun v => ?_⟩ ⟨fun w => ?_, fun v => ?_⟩ ⟨fun w => ?_, fun v => ?_⟩
    · rw [inf_fst]; exact le_min (hp.1 w) (hq.1 w)
    · rw [inf_snd]; exact le_min (hp.2 v) (hq.2 v)
    · change 0 ≤ p.1 w - (inf p q).1 w
      rw [inf_fst]; exact sub_nonneg.mpr (min_le_left _ _)
    · change 0 ≤ p.2 v - (inf p q).2 v
      rw [inf_snd]; exact sub_nonneg.mpr (min_le_left _ _)
    · change 0 ≤ q.1 w - (inf p q).1 w
      rw [inf_fst]; exact sub_nonneg.mpr (min_le_right _ _)
    · change 0 ≤ q.2 v - (inf p q).2 v
      rw [inf_snd]; exact sub_nonneg.mpr (min_le_right _ _)
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [← inf_fst, h0]; rfl
  · rw [← inf_snd, h0]; rfl

lemma coord_add_le {a b c : ℝ} (h : min a b = 0) (hac : a ≤ c)
    (hbc : b ≤ c) : a + b ≤ c := by
  rcases min_eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1, zero_add]; exact hbc
  · rw [h1, add_zero]; exact hac

/-- **The sum of disjoint effective divisors is their least upper bound.** -/
lemma add_le_of_disjoint {p q r : ArithDiv K} (hp : p ∈ effCone K) (hq : q ∈ effCone K)
    (h : DisjointEff p q) (hpr : r - p ∈ effCone K) (hqr : r - q ∈ effCone K) :
    r - (p + q) ∈ effCone K := by
  obtain ⟨h1, h2⟩ := min_eq_zero_of_disjoint hp hq h
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have a := hpr.1 w
    have b := hqr.1 w
    change 0 ≤ r.1 w - p.1 w at a
    change 0 ≤ r.1 w - q.1 w at b
    change 0 ≤ r.1 w - (p.1 w + q.1 w)
    exact sub_nonneg.mpr (coord_add_le (h1 w) (sub_nonneg.mp a)
      (sub_nonneg.mp b))
  · have a := hpr.2 v
    have b := hqr.2 v
    change 0 ≤ r.2 v - p.2 v at a
    change 0 ≤ r.2 v - q.2 v at b
    change 0 ≤ r.2 v - (p.2 v + q.2 v)
    exact sub_nonneg.mpr (coord_add_le (h2 v) (sub_nonneg.mp a)
      (sub_nonneg.mp b))

/-- Divisors with complementary supports are disjoint. -/
lemma disjoint_of_coord {p q : ArithDiv K} (h1 : ∀ w, p.1 w = 0 ∨ q.1 w = 0)
    (h2 : ∀ v, p.2 v = 0 ∨ q.2 v = 0) : DisjointEff p q := by
  intro r hr hpr hqr
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · have a := hpr.1 w
    have b := hqr.1 w
    change 0 ≤ p.1 w - r.1 w at a
    change 0 ≤ q.1 w - r.1 w at b
    change r.1 w = 0
    rcases h1 w with h | h
    · rw [h] at a; linarith [hr.1 w]
    · rw [h] at b; linarith [hr.1 w]
  · have a := hpr.2 v
    have b := hqr.2 v
    change 0 ≤ p.2 v - r.2 v at a
    change 0 ≤ q.2 v - r.2 v at b
    change r.2 v = 0
    rcases h2 v with h | h
    · rw [h] at a; linarith [hr.2 v]
    · rw [h] at b; linarith [hr.2 v]

lemma nonempty_finitePlace : Nonempty (NumberField.FinitePlace K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers K)
  exact ⟨NumberField.FinitePlace.mk ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩⟩

/-- An effective divisor of every degree `t ≥ 0` supported at one finite place. -/
lemma exists_fin_of_degree {t : ℝ} (ht : 0 ≤ t) :
    ∃ a ∈ effCone K, a.2 = 0 ∧ (∃ w, ∀ w', w' ≠ w → a.1 w' = 0) ∧ degArith K a = t := by
  classical
  obtain ⟨w⟩ := nonempty_finitePlace (K := K)
  have hl : 0 < Real.log (primeNorm w) := Real.log_pos (one_lt_primeNorm w)
  refine ⟨(Finsupp.single w (t / Real.log (primeNorm w)), 0), ⟨fun w' => ?_, fun _ => le_rfl⟩,
    rfl, ⟨w, fun w' hw' => Finsupp.single_eq_of_ne hw'⟩, ?_⟩
  · rw [Finsupp.single_apply]
    split_ifs
    · exact div_nonneg ht hl.le
    · exact le_rfl
  · rw [degArith_apply, Finsupp.sum_single_index (by simp)]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    field_simp

/-- An effective divisor of every degree `t ≥ 0` supported at the archimedean places. -/
lemma exists_inf_of_degree {t : ℝ} (ht : 0 ≤ t) :
    ∃ a ∈ effCone K, a.1 = 0 ∧ degArith K a = t := by
  obtain ⟨a, ha, hd⟩ := exists_eff_of_degree (K := K) ht
  refine ⟨(objOfDeg (K := K) t).α, ?_, rfl, degree_objOfDeg t⟩
  obtain ⟨-, -⟩ := And.intro ha hd
  refine ⟨fun w => le_rfl, fun v => ?_⟩
  classical
  change 0 ≤ Pi.single (M := fun _ => ℝ) _ _ v
  rw [Pi.single_apply]
  split_ifs
  · exact div_nonneg ht (by exact_mod_cast (Nat.zero_le _))
  · exact le_rfl

/-! ### The maps `τ_X` -/

variable (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence]

lemma corresp_preStep : Corresp F (fun _ _ φ => IsPreStep 𝐏₁ φ)
    (fun _ _ φ => IsPreStep 𝐏₂ φ) := fun _ _ φ =>
  (Model.isPreStep_iff_linear pt_isGroupoidBase φ).trans (((thm34 F).2.1 φ).trans
    (Model.isPreStep_iff_linear pt_isGroupoidBase _).symm)

omit [F.IsEquivalence] in
lemma divMap_congr (X : GlobalRealified K) {z z' : ArithDiv K} (hz : z ∈ effCone K)
    (hz' : z' ∈ effCone K) (h : z = z') : Model.divMap F X z hz = Model.divMap F X z' hz' := by
  subst h; rfl

lemma isPreStep_iff' {X Y : GlobalRealified K} (φ : X ⟶ Y) : IsPreStep 𝐏₁ φ ↔ φ.deg = 1 :=
  Model.isPreStep_iff_linear pt_isGroupoidBase φ

/-- `τ_X(a + z) = τ_X(a) + τ_{X+a}(z)`. -/
lemma divMap_add (X : GlobalRealified K) {a z : ArithDiv K} (ha : a ∈ effCone K)
    (hz : z ∈ effCone K) :
    Model.divMap F X (a + z) ((effCone K).add_mem ha hz) =
      Model.divMap F X a ha + Model.divMap F (stepTgt X a) z hz := by
  let φ := Model.stepTo X a ha ≫ Model.stepTo (stepTgt X a) z hz
  have hφ : IsPreStep 𝐏₁ φ := (isPreStep_iff' φ).mpr rfl
  have h := Model.div_map_preStep F φ hφ
  have hlin : (F.map (Model.stepTo (stepTgt X a) z hz)).deg = 1 :=
    linear_map F (thm34 F) _ rfl
  rw [F.map_comp, Model.comp_div, hlin, PNat.one_coe, one_smul] at h
  rw [divMap_congr F X _ φ.div_mem (show a + z = φ.div by
    change a + z = z + (1 : ℕ) • a; rw [one_smul, add_comm]), ← h]
  change _ = _ + (F.map (Model.stepTo (stepTgt X a) z hz)).div
  rw [add_comm]
  rfl

/-- `τ_Y = τ_{Y'}` for isomorphic `Y ≅ Y'`. -/
lemma divMap_iso {Y Y' : GlobalRealified K} (e : Y ≅ Y') (z : ArithDiv K) (hz : z ∈ effCone K) :
    Model.divMap F Y z hz = Model.divMap F Y' z hz := by
  have he1 : e.hom.deg = 1 := degFr_of_isIso (P := 𝐏₁) e.hom
  have he0 : e.hom.div = 0 := Div_of_isIso (P := 𝐏₁) e.hom
  let φ := e.hom ≫ Model.stepTo Y' z hz
  have hφ : IsPreStep 𝐏₁ φ := (isPreStep_iff' φ).mpr (by
    change (1 : ℕ+) * e.hom.deg = 1; rw [he1]; rfl)
  have h := Model.div_map_preStep F φ hφ
  obtain ⟨hd, -⟩ := Model.map_iso_div_deg F e.hom
  have hlin : (F.map (Model.stepTo Y' z hz)).deg = 1 := linear_map F (thm34 F) _ rfl
  rw [F.map_comp, Model.comp_div, hd, smul_zero, add_zero] at h
  rw [divMap_congr F Y _ φ.div_mem (show z = φ.div by
    change z = z + (1 : ℕ) • e.hom.div; rw [he0, smul_zero, add_zero]), ← h]
  rfl

/-- `τ_X` is additive on disjoint pairs. -/
lemma divMap_add_of_disjoint (X : GlobalRealified K) {a z : ArithDiv K} (ha : a ∈ effCone K)
    (hz : z ∈ effCone K) (hd : DisjointEff a z) :
    Model.divMap F X (a + z) ((effCone K).add_mem ha hz) =
      Model.divMap F X a ha + Model.divMap F X z hz := by
  have hpre := corresp_preStep F
  have hle := fun {z z' : ArithDiv K} (hz : z ∈ effCone K) (hz' : z' ∈ effCone K) =>
    Model.divMap_le_iff F hpre X hz hz'
  have hτa := Model.divMap_mem F X a ha
  have hτz := Model.divMap_mem F X z hz
  have haz := (effCone K).add_mem ha hz
  -- the images are disjoint
  have hd' : DisjointEff (Model.divMap F X a ha) (Model.divMap F X z hz) := by
    intro r hr h1 h2
    obtain ⟨s, hs, rfl⟩ := Model.divMap_surjective F hpre X (y := r) hr
    have s1 : (phiRlf K).le s a := (hle hs ha).mp h1
    have s2 : (phiRlf K).le s z := (hle hs hz).mp h2
    have : s = 0 := hd s hs s1 s2
    subst this
    exact Model.divMap_zero F X
  -- `τa + τz ≤ τ(a + z)`
  have up1 : (phiRlf L).le (Model.divMap F X a ha) (Model.divMap F X (a + z) haz) :=
    (hle ha haz).mpr (by change a + z - a ∈ effCone K; rwa [add_sub_cancel_left])
  have up2 : (phiRlf L).le (Model.divMap F X z hz) (Model.divMap F X (a + z) haz) :=
    (hle hz haz).mpr (by change a + z - z ∈ effCone K; rwa [add_sub_cancel_right])
  have l1 := add_le_of_disjoint hτa hτz hd' up1 up2
  -- `τ(a + z) ≤ τa + τz`
  obtain ⟨s, hs, hsτ⟩ := Model.divMap_surjective F hpre X (y := Model.divMap F X a ha +
    Model.divMap F X z hz) ((effCone L).add_mem hτa hτz)
  have t1 : (phiRlf K).le a s := (hle ha hs).mp (by
    change _ - _ ∈ effCone L; rw [hsτ, add_sub_cancel_left]; exact hτz)
  have t2 : (phiRlf K).le z s := (hle hz hs).mp (by
    change _ - _ ∈ effCone L; rw [hsτ, add_sub_cancel_right]; exact hτa)
  have l2 : (phiRlf L).le (Model.divMap F X (a + z) haz) (Model.divMap F X s hs) :=
    (hle haz hs).mpr (add_le_of_disjoint ha hz hd t1 t2)
  rw [hsτ] at l2
  exact (phiRlf L).le_antisymm l2 l1

/-- `τ_{X+a}(z) = τ_X(z)` for `a` disjoint from `z`. -/
lemma divMap_shift (X : GlobalRealified K) {a z : ArithDiv K} (ha : a ∈ effCone K)
    (hz : z ∈ effCone K) (hd : DisjointEff a z) :
    Model.divMap F (stepTgt X a) z hz = Model.divMap F X z hz := by
  have h1 := divMap_add F X ha hz
  rw [divMap_add_of_disjoint F X ha hz hd] at h1
  exact (add_left_cancel h1).symm

/-- `τ_X(z) = τ_{X'}(z)` if effective divisors of every degree disjoint from `z` exist. -/
lemma divMap_indep_of (z : ArithDiv K) (hz : z ∈ effCone K)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ a ∈ effCone K, DisjointEff a z ∧ degArith K a = t)
    (X X' : GlobalRealified K) : Model.divMap F X z hz = Model.divMap F X' z hz := by
  set M := max X.degree X'.degree
  obtain ⟨a, ha, had, hda⟩ := hex (M - X.degree) (sub_nonneg.mpr (le_max_left _ _))
  obtain ⟨a', ha', had', hda'⟩ := hex (M - X'.degree) (sub_nonneg.mpr (le_max_right _ _))
  have hiso : Nonempty (stepTgt X a ≅ stepTgt X' a') := by
    rw [nonempty_iso_iff_degree_eq, degree_step_target, degree_step_target, hda, hda']
    ring
  obtain ⟨e⟩ := hiso
  rw [← divMap_shift F X ha hz had, divMap_iso F e, divMap_shift F X' ha' hz had']

/-- **`τ_X` does not depend on `X`.** -/
theorem divMap_indep (z : ArithDiv K) (hz : z ∈ effCone K) (X X' : GlobalRealified K) :
    Model.divMap F X z hz = Model.divMap F X' z hz := by
  let zf : ArithDiv K := (z.1, 0)
  let zi : ArithDiv K := (0, z.2)
  have hzf : zf ∈ effCone K := ⟨hz.1, fun _ => le_rfl⟩
  have hzi : zi ∈ effCone K := ⟨fun _ => le_rfl, hz.2⟩
  have hsplit : z = zf + zi := by ext <;> simp [zf, zi]
  have hdisj : DisjointEff zf zi := disjoint_of_coord (fun _ => Or.inr rfl) (fun _ => Or.inl rfl)
  have key : ∀ Y : GlobalRealified K, Model.divMap F Y z hz =
      Model.divMap F Y zf hzf + Model.divMap F Y zi hzi := fun Y => by
    rw [divMap_congr F Y hz ((effCone K).add_mem hzf hzi) hsplit]
    exact divMap_add_of_disjoint F Y hzf hzi hdisj
  have hf : Model.divMap F X zf hzf = Model.divMap F X' zf hzf := by
    refine divMap_indep_of F zf hzf (fun t ht => ?_) X X'
    obtain ⟨a, ha, ha1, hda⟩ := exists_inf_of_degree (K := K) ht
    exact ⟨a, ha, disjoint_of_coord (fun w => Or.inl (by rw [ha1]; rfl))
      (fun _ => Or.inr rfl), hda⟩
  have hi : Model.divMap F X zi hzi = Model.divMap F X' zi hzi := by
    refine divMap_indep_of F zi hzi (fun t ht => ?_) X X'
    obtain ⟨a, ha, ha2, -, hda⟩ := exists_fin_of_degree (K := K) ht
    exact ⟨a, ha, disjoint_of_coord (fun _ => Or.inr rfl)
      (fun v => Or.inl (by rw [ha2]; rfl)), hda⟩
  rw [key, key, hf, hi]

/-! ### `Ψ_Φ` -/

/-- **`Ψ_Φ : Φ_K → Φ_L`** ([FrdI], Corollary 4.11(iii)): `τ_X` for any object `X`. -/
noncomputable def psiPhi (z : ArithDiv K) (hz : z ∈ effCone K) : ArithDiv L :=
  Model.divMap F (objOfDeg 0) z hz

lemma psiPhi_eq (X : GlobalRealified K) (z : ArithDiv K) (hz : z ∈ effCone K) :
    psiPhi F z hz = Model.divMap F X z hz :=
  divMap_indep F z hz _ X

omit [F.IsEquivalence] in
lemma psiPhi_mem (z : ArithDiv K) (hz : z ∈ effCone K) : psiPhi F z hz ∈ effCone L :=
  Model.divMap_mem F _ z hz

/-- **`Ψ_Φ` is additive.** -/
theorem psiPhi_add {a z : ArithDiv K} (ha : a ∈ effCone K) (hz : z ∈ effCone K) :
    psiPhi F (a + z) ((effCone K).add_mem ha hz) = psiPhi F a ha + psiPhi F z hz := by
  rw [psiPhi, divMap_add F _ ha hz, psiPhi, psiPhi_eq F (stepTgt (objOfDeg 0) a)]

omit [F.IsEquivalence] in
theorem psiPhi_zero : psiPhi F 0 (effCone K).zero_mem = 0 := Model.divMap_zero F _

/-- **`Ψ_Φ` is an order isomorphism.** -/
theorem psiPhi_le_iff {z z' : ArithDiv K} (hz : z ∈ effCone K) (hz' : z' ∈ effCone K) :
    psiPhi F z' hz' - psiPhi F z hz ∈ effCone L ↔ z' - z ∈ effCone K :=
  Model.divMap_le_iff F (corresp_preStep F) _ hz hz'

theorem psiPhi_surjective {y : ArithDiv L} (hy : y ∈ effCone L) :
    ∃ (z : ArithDiv K) (hz : z ∈ effCone K), psiPhi F z hz = y :=
  Model.divMap_surjective F (corresp_preStep F) (objOfDeg 0) hy

theorem psiPhi_injective {z z' : ArithDiv K} (hz : z ∈ effCone K) (hz' : z' ∈ effCone K)
    (h : psiPhi F z hz = psiPhi F z' hz') : z = z' := by
  refine (phiRlf K).le_antisymm (A := pt) ((psiPhi_le_iff F hz hz').mp ?_)
    ((psiPhi_le_iff F hz' hz).mp ?_)
  · rw [h, sub_self]; exact (effCone L).zero_mem
  · rw [h, sub_self]; exact (effCone L).zero_mem

/-- **[FrdI], Corollary 4.11(iv)** for `C^⊩`: `Div(F φ) = Ψ_Φ(Div φ)` for every morphism `φ`. -/
theorem div_map {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    (F.map φ).div = psiPhi F φ.div φ.div_mem := by
  -- `φ = frob ≫ step ≫ ι` with `ι` an isomorphism
  let Xn : GlobalRealified K := ⟨X.base, (φ.deg : ℕ) • X.α⟩
  let s := Model.stepTo Xn φ.div φ.div_mem
  let ι : stepTgt Xn φ.div ⟶ Y := Model.mk1 (𝟙 _) 0 (effCone K).zero_mem φ.u (by
    have r := φ.rel
    change (φ.deg : ℕ) • X.α + φ.div + 0 = Y.α + (φ.u : ArithDiv K)
    rw [add_zero]
    exact r)
  haveI : IsIso ι := Model.isIso_of ι rfl (isIso_pt _) rfl
  have hφ : φ = Model.frob X φ.deg ≫ s ≫ ι := by
    refine Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ (Subtype.ext ?_)
    · simp [Model.frob, s, ι, Model.stepTo]
    · simp [Model.frob, s, ι, Model.stepTo]
    · simp [Model.frob, s, ι, Model.stepTo]
  obtain ⟨hd, hg⟩ := Model.map_iso_div_deg F ι
  have hF := ((thm34 F).1 (Model.frob X φ.deg)).1 (Model.frob_isFrobeniusType X φ.deg)
  have hfd : (F.map (Model.frob X φ.deg)).div = 0 := hF.1.2
  have hs : (F.map s).div = psiPhi F φ.div φ.div_mem :=
    (Model.div_map_preStep F s ((isPreStep_iff' s).mpr rfl)).trans (psiPhi_eq F Xn _ _).symm
  have hsl : (F.map s).deg = 1 := linear_map F (thm34 F) s rfl
  conv_lhs => rw [hφ]
  rw [F.map_comp, F.map_comp, Model.comp_div, Model.comp_div, hd, hfd, hg, hs]
  simp only [PNat.one_coe, one_smul, smul_zero, add_zero, map_zero, zero_add]
  rfl

/-- `degFr(F φ) = degFr(φ)` ([FrdI], Corollary 4.11(iv), Frobenius degrees). -/
theorem deg_map {X Y : GlobalRealified K} (φ : X ⟶ Y) : (F.map φ).deg = φ.deg :=
  thm34_deg_id F φ

/-- **[FrdI], Theorem 6.4(ii)** on all of `Φ`: `deg^arith(Ψ_Φ z) = deg(Ψ)·deg^arith(z)`. -/
theorem degArith_psiPhi (z : ArithDiv K) (hz : z ∈ effCone K) :
    degArith L (psiPhi F z hz) = degOf F * degArith K z := by
  rw [psiPhi]
  exact degArith_divMap F (by rw [degree_objOfDeg]) z hz

/-- **`deg(F X) = deg(Ψ)·deg(X)` for every object `X`.** -/
theorem degree_map_eq (X : GlobalRealified K) : (F.obj X).degree = degOf F * X.degree := by
  rcases le_or_gt 0 X.degree with h | h
  · exact degree_map F h
  -- `X → X + z` with `deg z = -deg X`; the target has degree `0`
  obtain ⟨z, hz, hdz⟩ := exists_eff_of_degree (K := K) (neg_nonneg.mpr h.le)
  have hY : (stepTgt X z).degree = 0 := by rw [degree_step_target, hdz]; ring
  have h1 := degree_hom (F.map (step X z hz))
  rw [linear_map F (thm34 F) _ rfl, PNat.one_coe, Nat.cast_one, one_mul,
    degree_map F hY.ge, hY, mul_zero] at h1
  have h2 : (F.map (step X z hz)).div = psiPhi F z hz :=
    (Model.div_map_preStep F (step X z hz) ((isPreStep_iff' _).mpr rfl)).trans
      (psiPhi_eq F X z hz).symm
  rw [h2, degArith_psiPhi, hdz] at h1
  linarith

end GlobalRealified

/-! ### Theorem 3.4 over `Pt`: the global realified and the archimedean Frobenioids -/

/-- **[FrdI], Theorem 3.4(v) over `Pt`**: every functor between Frobenioids over `Pt` lies over
the identity of `Pt`. -/
theorem preservesBase_pt {Φ₁ Φ₂ : DivMonoid.{u} Pt} {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (P₁ : C₁ ⥤ Elem Φ₁) (P₂ : C₂ ⥤ Elem Φ₂) (F : C₁ ⥤ C₂) : PreservesBase P₁ P₂ F :=
  ⟨𝟭 Pt, ⟨Functor.punitExt _ _⟩⟩

/-- **[FrdI], Theorem 3.4(iii), (v) for the global realified Frobenioids** (IUT I, Example
3.5): every equivalence `C^⊩(K) ≌ C^⊩(L)` preserves the Frobenius structure and the base. -/
theorem GlobalRealified.thm34_full {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] (F : GlobalRealified K ⥤ GlobalRealified L) [F.IsEquivalence] :
    PreservesFrobeniusStructure (Model.toElem (phiRlf K) (bRlf K) (divBRlf K))
      (Model.toElem (phiRlf L) (bRlf L) (divBRlf L)) F ∧
    PreservesBase (Model.toElem (phiRlf K) (bRlf K) (divBRlf K))
      (Model.toElem (phiRlf L) (bRlf L) (divBRlf L)) F :=
  ⟨GlobalRealified.thm34 F, preservesBase_pt _ _ F⟩

namespace Arch

/-- `ℝ_{≥0}` has no irreducible elements. -/
lemma phiReal_noIrreducible : NoIrreducible phiReal.{u} := by
  intro _ z hz h0
  have hz' : 0 ≤ z.down := hz
  have hne : z.down ≠ 0 := fun h => h0 (ULift.ext _ _ h)
  have hh : (⟨z.down / 2⟩ : ULift.{u} ℝ) ∈ realCone := by
    rw [mem_realCone]; change 0 ≤ z.down / 2; linarith
  have hh0 : (⟨z.down / 2⟩ : ULift.{u} ℝ) ≠ 0 := fun h => by
    have := congrArg ULift.down h
    change z.down / 2 = 0 at this
    exact hne (by linarith)
  refine ⟨_, hh, _, hh, hh0, hh0, ULift.ext _ _ ?_⟩
  change z.down = z.down / 2 + z.down / 2
  ring

/-- **[FrdI], Theorem 3.4(iii), (v) for the archimedean Frobenioids** (IUT I, Example 3.4):
every equivalence between the archimedean Frobenioids of two infinite places (of possibly
different number fields) preserves the Frobenius structure and the base. -/
theorem thm34 {K L : Type u} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)
    (F : Arch v ⥤ Arch w) [F.IsEquivalence] :
    PreservesFrobeniusStructure (Model.toElem phiReal (bArch v) (divArch v))
      (Model.toElem phiReal (bArch w) (divArch w)) F ∧
    PreservesBase (Model.toElem phiReal (bArch v) (divArch v))
      (Model.toElem phiReal (bArch w) (divArch w)) F :=
  ⟨Model.thm34_groupoid GlobalRealified.pt_isGroupoidBase phiReal_noIrreducible
    GlobalRealified.pt_isGroupoidBase phiReal_noIrreducible F, preservesBase_pt _ _ F⟩

end Arch

end Frobenioid

end Iut
