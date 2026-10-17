/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalPrime
import Iut.Frobenioid.GlobalNonRlf

/-!
# The unit-trivialized perfection `(C^pf)^{un-tr}` of the global Frobenioid

[FrdI], Theorem 6.4(iii) concerns equivalences `Ψ^rlf : C₁^rlf ≅ C₂^rlf` that arise from
equivalences `(Ψ^pf)^{un-tr} : (C₁^pf)^{un-tr} ≅ (C₂^pf)^{un-tr}` of the unit-trivialized
perfections. By [FrdI], Proposition 5.3, `(C^pf)^{un-tr}` is the model Frobenioid of the divisor
monoid `Φ^pf` and the rational function monoid `ℚ·Φ^birat`; for the global Frobenioid of
[FrdI], Example 6.3 over `Pt` this is:

* `ArithDivQ K = (V_fin →₀ ℚ) × (V_∞ → ℝ)`, `effConeQ K`, `phiQ K`;
* `ratFunQ K = ℚ·div(K^×)`, `GlobalPf K = Model (phiQ K) (bQ K) (divBQ K)`;
* **`GlobalPf.realify : GlobalPf K ⥤ C^⊩(K)`** (`Φ^pf ⊆ Φ^rlf`, `ℚ·Φ^birat ⊆ ℝ·Φ^birat`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- `Φ^{pf,gp} = (V_fin →₀ ℚ) × (V_∞ → ℝ)`. -/
abbrev ArithDivQ : Type u := (FinitePlace K →₀ ℚ) × (InfinitePlace K → ℝ)

/-- `Φ^pf`: effective divisors. -/
def effConeQ : AddSubmonoid (ArithDivQ K) where
  carrier := {x | (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v}
  add_mem' {a b} ha hb := ⟨fun w => by simpa using add_nonneg (ha.1 w) (hb.1 w),
    fun v => by simpa using add_nonneg (ha.2 v) (hb.2 v)⟩
  zero_mem' := ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-- The realification map `Φ^{pf,gp} → (Φ^rlf)^gp`. -/
noncomputable def castQ : ArithDivQ K →+ ArithDiv K where
  toFun x := (x.1.mapRange (fun q : ℚ => (q : ℝ)) (by simp), x.2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

variable {K}

@[simp] lemma castQ_fst (x : ArithDivQ K) (w : FinitePlace K) : (castQ K x).1 w = x.1 w := by
  simp [castQ]

@[simp] lemma castQ_snd (x : ArithDivQ K) (v : InfinitePlace K) : (castQ K x).2 v = x.2 v :=
  rfl

lemma castQ_injective : Function.Injective (castQ K) := by
  intro x y h
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · have := congrArg (fun z => z.1 w) h
    simpa using this
  · exact congrArg (fun z => z.2 v) h

lemma castQ_mem_iff {x : ArithDivQ K} : castQ K x ∈ effCone K ↔ x ∈ effConeQ K := by
  rw [mem_effCone]
  change _ ↔ (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v
  simp

lemma castQ_smul (q : ℚ) (x : ArithDivQ K) : castQ K (q • x) = (q : ℝ) • castQ K x := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp
  · change q • x.2 v = (q : ℝ) * x.2 v
    rw [Rat.smul_def]

lemma effConeQ_sharp {x : ArithDivQ K} (h : x ∈ effConeQ K) (h' : -x ∈ effConeQ K) : x = 0 := by
  refine castQ_injective ?_
  rw [map_zero]
  refine effCone_sharp (castQ_mem_iff.mpr h) ?_
  rw [← map_neg]
  exact castQ_mem_iff.mpr h'

lemma effConeQ_saturated {x : ArithDivQ K} (n : ℕ) (hn : 0 < n) (h : n • x ∈ effConeQ K) :
    x ∈ effConeQ K := by
  rw [← castQ_mem_iff] at h ⊢
  rw [map_nsmul] at h
  exact effCone_saturated n hn h

lemma effConeQ_generating (x : ArithDivQ K) :
    ∃ p ∈ effConeQ K, ∃ q ∈ effConeQ K, x = p - q := by
  let p : ArithDivQ K := (x.1.mapRange (fun t => max t 0) (by simp), fun v => max (x.2 v) 0)
  let q : ArithDivQ K := (x.1.mapRange (fun t => max (-t) 0) (by simp), fun v => max (-x.2 v) 0)
  refine ⟨p, ⟨fun w => by simp [p], fun v => by simp [p]⟩, q,
    ⟨fun w => by simp [q], fun v => by simp [q]⟩, ?_⟩
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp only [p, q, Prod.fst_sub, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]
  · simp only [p, q, Prod.snd_sub, Pi.sub_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]

/-- The principal divisor of `x ∈ K^×` with rational finite coordinates. -/
noncomputable def divOfQ (x : Kˣ) : ArithDivQ K :=
  ((ordZ x).mapRange (fun n : ℤ => (n : ℚ)) (by simp), fun v => -Real.log (v (x : K)))

lemma castQ_divOfQ (x : Kˣ) : castQ K (divOfQ x) = divOf K ⟨(x : K), x.ne_zero⟩ := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · rw [castQ_fst]
    simp only [divOfQ, Finsupp.mapRange_apply, Rat.cast_intCast]
    rfl
  · rfl

variable (K) in
/-- **`ℚ·Φ^birat`**: the `ℚ`-span of the principal divisors. -/
noncomputable def ratFunQ : Submodule ℚ (ArithDivQ K) := Submodule.span ℚ (Set.range divOfQ)

lemma castQ_mem_ratFun {x : ArithDivQ K} (hx : x ∈ ratFunQ K) : castQ K x ∈ ratFun K := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    rw [castQ_divOfQ]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [map_zero]; exact (ratFun K).zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact (ratFun K).add_mem ha hb
  | smul q a _ ha => rw [castQ_smul]; exact (ratFun K).smul_mem _ ha

variable (K) in
/-- The divisor monoid `Φ^pf`. -/
noncomputable abbrev phiQ : DivMonoid.{u} Pt :=
  constDivMonoid (ArithDivQ K) (effConeQ K) effConeQ_sharp effConeQ_saturated
    effConeQ_generating

variable (K) in
/-- The rational function monoid `ℚ·Φ^birat`. -/
noncomputable abbrev bQ : GrpOn.{u} Pt := constGrpOn (ratFunQ K)

variable (K) in
/-- `ℚ·Φ^birat ↪ Φ^{pf,gp}`. -/
noncomputable abbrev divBQ : DivHom (bQ K) (phiQ K).toGrpOn :=
  constDivHom (ratFunQ K).subtype.toAddMonoidHom

variable (K) in
/-- **`(C^pf)^{un-tr}`** of the global Frobenioid of `K` ([FrdI], Example 6.3, Proposition 5.3). -/
abbrev GlobalPf : Type u := Model (phiQ K) (bQ K) (divBQ K)

variable (K) in
theorem globalPf_isFrobenioid : IsFrobenioid (Model.toElem (phiQ K) (bQ K) (divBQ K)) :=
  Model.isFrobenioid

namespace GlobalPf

variable (K) in
/-- **The realification `(C^pf)^{un-tr} → C^rlf = C^⊩`** ([FrdI], Proposition 5.3). -/
noncomputable def realify : GlobalPf K ⥤ GlobalRealified K where
  obj X := ⟨X.base, castQ K X.α⟩
  map φ := Model.mk' φ.deg φ.base (castQ K φ.div) (castQ_mem_iff.mpr φ.div_mem)
    ⟨castQ K φ.u, castQ_mem_ratFun φ.u.2⟩ (by
      have h := congrArg (castQ K) φ.rel
      rw [map_add, map_add, map_nsmul] at h
      exact h)
  map_id X := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · exact map_zero _
    · exact map_zero _
  map_comp φ ψ := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · change castQ K (ψ.div + (ψ.deg : ℕ) • φ.div) =
        castQ K ψ.div + (ψ.deg : ℕ) • castQ K φ.div
      rw [map_add, map_nsmul]
    · change castQ K ((ψ.u : ArithDivQ K) + (ψ.deg : ℕ) • (φ.u : ArithDivQ K)) =
        castQ K ψ.u + (ψ.deg : ℕ) • castQ K φ.u
      rw [map_add, map_nsmul]

@[simp] lemma realify_map_div {X Y : GlobalPf K} (φ : X ⟶ Y) :
    ((realify K).map φ).div = castQ K φ.div := rfl

@[simp] lemma realify_map_deg {X Y : GlobalPf K} (φ : X ⟶ Y) :
    ((realify K).map φ).deg = φ.deg := rfl

/-- The pre-step `(pt, 0) → (pt, z)` of `GlobalPf K`. -/
noncomputable def stepQ (z : ArithDivQ K) (hz : z ∈ effConeQ K) :
    (⟨pt, 0⟩ : GlobalPf K) ⟶ ⟨pt, z⟩ :=
  Model.mk1 (𝟙 _) z hz 0 (by change (0 : ArithDivQ K) + z = z + 0; simp)

end GlobalPf

end Frobenioid

end Iut
