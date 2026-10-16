/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Cor411Rlf

/-!
# The global Frobenioid of a number field ([FrdI], Example 6.3) and its realification

[FrdI], Example 6.3 (p. 112–114): for a number field `F`, `Φ(F) = ⊕_{v ∈ V(F)} ord(O^▷_v)` (the
*effective arithmetic divisors*: `ℤ_{≥0}` at the nonarchimedean, `ℝ_{≥0}` at the archimedean
places), `B(F) = F^×` and `B → Φ^gp` the principal divisor; the associated model Frobenioid
(Theorem 5.2) has `O^×(A) = O^▷(A) = μ(F)`. IUT I, Example 3.5(i) takes the trivial Galois
extension (base category `Pt`) for `F = F_mod`, and defines `C^⊩_mod` as its realification
([FrdI], Proposition 5.3).

This file builds, for a number field `K` and the trivial Galois extension:

* `ArithDivZ K = (V_fin →₀ ℤ) × (V_∞ → ℝ)`, `effConeZ K`, `phiZ K` (the divisor monoid);
* `divZ : K^× → Φ^gp` (`ord_w` at finite, `−log|·|_v` at infinite places), `bZ K = K^×`;
* **`GlobalFrobenioid K`** `= Model (phiZ K) (bZ K) (divBZ K)` and
  `globalFrobenioid_isFrobenioid` ([FrdI], Theorem 5.2(ii));
* **`GlobalFrobenioid.orhdEquiv`**, **`ounitsEquiv`**: `O^▷(A) ≃ μ(K)`, `O^×(A) ≃ μ(K)`
  ([FrdI], Example 6.3: `O^×(A) = O^▷(A) = μ(L)`), via `divZ_mem_effConeZ_iff`: a principal
  divisor is effective iff `x` is a root of unity (product formula + Kronecker);
* **`GlobalFrobenioid.realify`**: the natural functor `C → C^⊩ = C^rlf` of [FrdI], Proposition
  5.3 (`Φ ↦ Φ^rlf`, `B ↦ ℝ·Φ^birat`), compatible with Frobenius degrees, projections and zero
  divisors (`realify_map_deg`, `realify_map_div`), with the degrees (`degree_realify`), and
  essentially surjective (`realify_essSurj`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

variable (K : Type u) [Field K] [NumberField K]

/-! ### Divisors with integral finite part -/

/-- **Arithmetic divisors** ([FrdI], Example 6.3): `(V_fin →₀ ℤ) × (V_∞ → ℝ)`. -/
abbrev ArithDivZ : Type u := (FinitePlace K →₀ ℤ) × (InfinitePlace K → ℝ)

/-- **Effective arithmetic divisors**. -/
def effConeZ : AddSubmonoid (ArithDivZ K) where
  carrier := {x | (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v}
  add_mem' {a b} ha hb := ⟨fun w => by simpa using add_nonneg (ha.1 w) (hb.1 w),
    fun v => by simpa using add_nonneg (ha.2 v) (hb.2 v)⟩
  zero_mem' := ⟨fun _ => le_rfl, fun _ => le_rfl⟩

variable {K}

lemma mem_effConeZ {x : ArithDivZ K} : x ∈ effConeZ K ↔ (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v :=
  Iff.rfl

variable (K) in
/-- The realification map `Φ^gp → (Φ^rlf)^gp`. -/
noncomputable def castDiv : ArithDivZ K →+ ArithDiv K where
  toFun x := (x.1.mapRange (fun n : ℤ => (n : ℝ)) (by simp), x.2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma castDiv_fst (x : ArithDivZ K) (w : FinitePlace K) :
    (castDiv K x).1 w = x.1 w := by simp [castDiv]

@[simp] lemma castDiv_snd (x : ArithDivZ K) (v : InfinitePlace K) :
    (castDiv K x).2 v = x.2 v := rfl

lemma castDiv_injective : Function.Injective (castDiv K) := by
  intro x y h
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · have := congrArg (fun z => z.1 w) h
    simpa using this
  · exact congrArg (fun z => z.2 v) h

lemma castDiv_mem_iff {x : ArithDivZ K} : castDiv K x ∈ effCone K ↔ x ∈ effConeZ K := by
  rw [mem_effCone, mem_effConeZ]
  simp

lemma effConeZ_sharp {x : ArithDivZ K} (h : x ∈ effConeZ K) (h' : -x ∈ effConeZ K) : x = 0 := by
  refine castDiv_injective ?_
  rw [map_zero]
  refine effCone_sharp (castDiv_mem_iff.mpr h) ?_
  rw [← map_neg]
  exact castDiv_mem_iff.mpr h'

lemma effConeZ_saturated {x : ArithDivZ K} (n : ℕ) (hn : 0 < n) (h : n • x ∈ effConeZ K) :
    x ∈ effConeZ K := by
  rw [← castDiv_mem_iff] at h ⊢
  rw [map_nsmul] at h
  exact effCone_saturated n hn h

lemma effConeZ_generating (x : ArithDivZ K) :
    ∃ p ∈ effConeZ K, ∃ q ∈ effConeZ K, x = p - q := by
  let p : ArithDivZ K := (x.1.mapRange (fun t => max t 0) (by simp), fun v => max (x.2 v) 0)
  let q : ArithDivZ K := (x.1.mapRange (fun t => max (-t) 0) (by simp), fun v => max (-x.2 v) 0)
  refine ⟨p, ⟨fun w => by simp [p], fun v => by simp [p]⟩, q,
    ⟨fun w => by simp [q], fun v => by simp [q]⟩, ?_⟩
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp only [p, q, Prod.fst_sub, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]
  · simp only [p, q, Prod.snd_sub, Pi.sub_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]

/-! ### Principal divisors -/

/-- `ord_w(x)` for `x ∈ K^×`, as a finitely supported function. -/
noncomputable def ordZ (x : Kˣ) : FinitePlace K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun w => (ArithLineBundle.principal (x : K) x.ne_zero).ord w)
    (ArithLineBundle.finite_support_ord _)

lemma ordZ_apply (x : Kˣ) (w : FinitePlace K) :
    ordZ x w = (ArithLineBundle.principal (x : K) x.ne_zero).ord w := rfl

lemma ordZ_mul (x y : Kˣ) : ordZ (x * y) = ordZ x + ordZ y := by
  ext w
  simp only [ordZ_apply, Finsupp.coe_add, Pi.add_apply]
  rw [← ArithLineBundle.ord_mul]
  refine ArithLineBundle.ord_eq_of_norm_eq _ _ w ?_
  simp [ArithLineBundle.principal, ArithLineBundle.mul]

variable (K) in
/-- **The principal divisor** `K^× → Φ^gp` ([FrdI], Example 6.3). -/
noncomputable def divZ : Additive Kˣ →+ ArithDivZ K where
  toFun x := (ordZ x.toMul, fun v => -Real.log (v (x.toMul : K)))
  map_zero' := by
    refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
    · simp only [toMul_zero, ordZ_apply]
      exact ArithLineBundle.ord_eq_zero_of_norm _ _ (by simp [ArithLineBundle.principal])
    · simp
  map_add' x y := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · exact ordZ_mul _ _
    · simp only [toMul_add, Units.val_mul, map_mul, Prod.snd_add, Pi.add_apply]
      rw [Real.log_mul (ne_of_gt (v.pos_iff.mpr x.toMul.ne_zero))
        (ne_of_gt (v.pos_iff.mpr y.toMul.ne_zero))]
      ring

/-- The realification of the principal divisor is `divOf`. -/
lemma castDiv_divZ (x : Kˣ) :
    castDiv K (divZ K (Additive.ofMul x)) = divOf K ⟨(x : K), x.ne_zero⟩ := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · rw [castDiv_fst]
    rfl
  · rfl

variable (K) in
/-- The divisor monoid `Φ` of [FrdI], Example 6.3 (trivial Galois extension). -/
noncomputable abbrev phiZ : DivMonoid.{u} Pt :=
  constDivMonoid (ArithDivZ K) (effConeZ K) effConeZ_sharp effConeZ_saturated
    effConeZ_generating

variable (K) in
/-- The rational function monoid `B = K^×`. -/
noncomputable abbrev bZ : GrpOn.{u} Pt := constGrpOn (Additive Kˣ)

variable (K) in
/-- `Div_B : K^× → Φ^gp`. -/
noncomputable abbrev divBZ : DivHom (bZ K) (phiZ K).toGrpOn := constDivHom (divZ K)

variable (K) in
/-- **The global Frobenioid of `K`** ([FrdI], Example 6.3, trivial Galois extension). -/
abbrev GlobalFrobenioid : Type u := Model (phiZ K) (bZ K) (divBZ K)

variable (K) in
/-- **The global Frobenioid is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem globalFrobenioid_isFrobenioid :
    IsFrobenioid (Model.toElem (phiZ K) (bZ K) (divBZ K)) :=
  Model.isFrobenioid

/-! ### Effective principal divisors are those of roots of unity -/

/-- The principal divisor of a root of unity vanishes. -/
lemma divZ_eq_zero_of_isOfFinOrder (x : Kˣ) (h : IsOfFinOrder x) :
    divZ K (Additive.ofMul x) = 0 := by
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  have h1 : n • divZ K (Additive.ofMul x) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hxn, ofMul_one, map_zero]
  refine castDiv_injective ?_
  have h3 := congrArg (castDiv K) h1
  rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℝ] at h3
  rw [map_zero]
  exact (smul_eq_zero.mp h3).resolve_left (by exact_mod_cast hn.ne')

/-- **A principal divisor is effective iff it is zero iff `x` is a root of unity** (product
formula and Kronecker's theorem). -/
theorem divZ_mem_effConeZ_iff (x : Kˣ) :
    divZ K (Additive.ofMul x) ∈ effConeZ K ↔ IsOfFinOrder x := by
  constructor
  · intro h
    have h1 : divOf K ⟨(x : K), x.ne_zero⟩ ∈ effCone K := by
      rw [← castDiv_divZ]; exact castDiv_mem_iff.mpr h
    have h0 : divOf K ⟨(x : K), x.ne_zero⟩ = 0 :=
      GlobalRealified.eq_zero_of_degArith_eq_zero h1
        (degArith_ratFun (Submodule.subset_span ⟨_, rfl⟩))
    -- archimedean places: `|x|_v = 1`
    have hinf : ∀ v : InfinitePlace K, v (x : K) = 1 := fun v => by
      have := congrArg (fun z => z.2 v) h0
      change -Real.log (v (x : K)) = 0 at this
      have hp : 0 < v (x : K) := v.pos_iff.mpr x.ne_zero
      exact Real.eq_one_of_pos_of_log_eq_zero hp (neg_eq_zero.mp this)
    -- finite places: `x` is integral
    have hint : IsIntegral ℤ (x : K) := by
      have hv : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), P.valuation K (x : K) ≤ 1 := by
        intro P
        let w : FinitePlace K := FinitePlace.mk P
        have h2 := congrArg (fun z => z.1 w) h0
        change ((ArithLineBundle.principal (x : K) x.ne_zero).ord w : ℝ) = 0 at h2
        have h3 : (ArithLineBundle.principal (x : K) x.ne_zero).ord w = 0 := by exact_mod_cast h2
        have h4 := ArithLineBundle.norm_fin_eq (ArithLineBundle.principal (x : K) x.ne_zero) w
        rw [h3, neg_zero, zpow_zero] at h4
        change ‖FinitePlace.embedding w.maximalIdeal (x : K)‖ = 1 at h4
        rw [show w.maximalIdeal = P from FinitePlace.maximalIdeal_mk P,
          FinitePlace.norm_embedding'] at h4
        have hb := NumberField.HeightOneSpectrum.absNorm_ne_zero P
        have h5 : WithZeroMulInt.toNNReal hb (P.valuation K (x : K)) ≤
            WithZeroMulInt.toNNReal hb 1 := by
          rw [map_one]; exact_mod_cast h4.le
        exact (WithZeroMulInt.toNNReal_strictMono
          (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)).le_iff_le.mp h5
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        (R := 𝓞 K) K (x : K) hv
      rw [← hy, ← RingOfIntegers.coe_eq_algebraMap]
      exact y.isIntegral_coe
    obtain ⟨n, hn, hxn⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hint
      (fun φ => by rw [← InfinitePlace.apply φ]; exact hinf _)
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.ext (by simpa using hxn)⟩
  · intro h
    rw [divZ_eq_zero_of_isOfFinOrder x h]
    exact (effConeZ K).zero_mem

namespace GlobalFrobenioid

local notation "𝐏" => Model.toElem (phiZ K) (bZ K) (divBZ K)

lemma div_eq_divZ {X : GlobalFrobenioid K} (e : X ⟶ X) (h : e.deg = 1) :
    e.div = divZ K e.u := by
  have r := e.rel
  rw [h] at r
  change (1 : ℕ) • X.α + e.div = X.α + divZ K e.u at r
  rw [one_smul] at r
  exact add_left_cancel r

/-- **`O^▷(A) ≅ μ(K)`** ([FrdI], Example 6.3): the base-identity linear endomorphisms are the
`(1, id, div(u), u)` with `u` a root of unity. -/
noncomputable def orhdEquiv (X : GlobalFrobenioid K) :
    Orhd 𝐏 X ≃ CommGroup.torsion Kˣ where
  toFun a := ⟨a.1.u.toMul, by
    have hd := div_eq_divZ a.1 a.2.2
    have := a.1.div_mem
    rw [hd] at this
    exact (divZ_mem_effConeZ_iff _).mp this⟩
  invFun u := ⟨Model.mk1 (𝟙 _) (divZ K (Additive.ofMul u.1))
      ((divZ_mem_effConeZ_iff _).mpr u.2) (Additive.ofMul u.1) rfl, Subsingleton.elim _ _, rfl⟩
  left_inv a := by
    have hd := div_eq_divZ a.1 a.2.2
    refine Subtype.ext (Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ ?_)
    · exact (show a.1.deg = 1 from a.2.2).symm
    · exact hd.symm
    · simp
  right_inv u := rfl

/-- **`O^×(A) = O^▷(A)`** ([FrdI], Example 6.3). -/
theorem ounits_eq_orhd (X : GlobalFrobenioid K) : Ounits 𝐏 X = Orhd 𝐏 X := by
  ext e
  refine ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨?_, h⟩⟩
  have hd := div_eq_divZ e h.2
  have ht := (orhdEquiv X ⟨e, h⟩).2
  have h0 : e.div = 0 := by
    rw [hd]
    exact divZ_eq_zero_of_isOfFinOrder _ ht
  exact Model.isIso_of e h.2 (isIso_pt _) h0

/-- **`O^×(A) ≅ μ(K)`**. -/
noncomputable def ounitsEquiv (X : GlobalFrobenioid K) :
    Ounits 𝐏 X ≃ CommGroup.torsion Kˣ :=
  (Equiv.setCongr (ounits_eq_orhd X)).trans (orhdEquiv X)

/-! ### The realification ([FrdI], Proposition 5.3) -/

/-- `u ↦ div(u) ∈ ℝ·Φ^birat`. -/
noncomputable def realifyU (u : Additive Kˣ) : ratFun K :=
  ⟨castDiv K (divZ K u), by
    rw [show u = Additive.ofMul u.toMul from rfl, castDiv_divZ]
    exact Submodule.subset_span ⟨_, rfl⟩⟩

variable (K) in
/-- **The realification functor `C → C^rlf = C^⊩`** ([FrdI], Proposition 5.3). -/
noncomputable def realify : GlobalFrobenioid K ⥤ GlobalRealified K where
  obj X := ⟨X.base, castDiv K X.α⟩
  map φ := Model.mk' φ.deg φ.base (castDiv K φ.div) (castDiv_mem_iff.mpr φ.div_mem)
    (realifyU φ.u) (by
      have h := congrArg (castDiv K) φ.rel
      rw [map_add, map_add, map_nsmul] at h
      exact h)
  map_id X := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · exact map_zero _
    · change castDiv K (divZ K 0) = 0
      rw [map_zero, map_zero]
  map_comp φ ψ := by
    refine Model.hom_ext rfl rfl ?_ (Subtype.ext ?_)
    · change castDiv K (ψ.div + (ψ.deg : ℕ) • φ.div) =
        castDiv K ψ.div + (ψ.deg : ℕ) • castDiv K φ.div
      rw [map_add, map_nsmul]
    · change castDiv K (divZ K (ψ.u + (ψ.deg : ℕ) • φ.u)) =
        castDiv K (divZ K ψ.u) + (ψ.deg : ℕ) • castDiv K (divZ K φ.u)
      rw [map_add, map_nsmul, map_add, map_nsmul]

/-- **Compatibility with `F_Φ → F_{Φ^rlf}`** ([FrdI], Proposition 5.3: the realification
1-commutes with the functors to the elementary Frobenioids). -/
@[simp] lemma realify_map_deg {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    ((realify K).map φ).deg = φ.deg := rfl
@[simp] lemma realify_map_base {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    ((realify K).map φ).base = φ.base := rfl
@[simp] lemma realify_map_div {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    ((realify K).map φ).div = castDiv K φ.div := rfl

/-- The degree of an object of `C`: `deg^arith(α)`. -/
noncomputable def degree (X : GlobalFrobenioid K) : ℝ := degArith K (castDiv K X.α)

lemma degree_realify (X : GlobalFrobenioid K) :
    ((realify K).obj X).degree = X.degree := rfl

/-- **The realification is essentially surjective**: every object of `C^⊩` is isomorphic to the
realification of an object of `C`. -/
instance realify_essSurj : (realify K).EssSurj where
  mem_essImage Y := by
    classical
    let v₀ := Classical.arbitrary (InfinitePlace K)
    let X : GlobalFrobenioid K := ⟨pt, (0, Pi.single v₀ (Y.degree / v₀.mult))⟩
    have hX : ((realify K).obj X).degree = Y.degree := by
      have hm : (v₀.mult : ℝ) ≠ 0 := by exact_mod_cast v₀.mult_pos.ne'
      change degArith K (castDiv K (0, Pi.single v₀ (Y.degree / v₀.mult))) = _
      have : castDiv K (0, Pi.single v₀ (Y.degree / v₀.mult)) =
          (0, Pi.single v₀ (Y.degree / v₀.mult)) :=
        Prod.ext (Finsupp.ext fun w => by simp) rfl
      rw [this, degArith_single_inf]
      field_simp
    obtain ⟨e⟩ := (GlobalRealified.nonempty_iso_iff_degree_eq _ _).mpr hX
    exact ⟨X, ⟨e⟩⟩

end GlobalFrobenioid

end Frobenioid

end Iut
