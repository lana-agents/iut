/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelFrobenioid
import Iut.Arakelov.FractionalIdeal

/-!
# The global realified Frobenioid of a number field (IUT I, Example 3.5; [FrdI], Ex. 6.3)

[FrdI], Example 6.3: for a number field `K` and the trivial Galois extension (so that the base
category is a one-morphism category, IUT I, Example 3.5(i)), the Frobenioid `C_K` is the model
Frobenioid with divisor monoid the **effective arithmetic divisors** `⊕_v ord(𝒪^▷_v)` and
rational functions `K^×`. Its **realification** `C^⊩` ([FrdI], Proposition 5.3, Theorem
6.4(ii); IUT I, Example 3.5(i): "the realification of the Frobenioid of [FrdI], Example 6.3")
is the model Frobenioid with

* base category `Pt` (one object, one morphism);
* divisor monoid the effective **ℝ-arithmetic divisors**: `Φ^gp = (V_fin →₀ ℝ) × (V_∞ → ℝ)`
  (`ArithDiv K`), `Φ = ℝ_{≥0}`-coefficients (`effCone K`); the coordinate of the divisor of a
  local element `λ` is `ord_w(λ)` at a finite place and `−log|λ|_v` at an archimedean place
  (`ord(𝒪^▷_v) ≅ ℝ_{≥0}`);
* rational function monoid `ℝ·div(K^×) ⊆ Φ^gp` (`ratFun K`, [FrdI], Proposition 5.3).

## The arithmetic degree

`deg^arith(x) = Σ_w x_w·log N(𝔭_w) + Σ_v [K_v : ℝ]·x_v` (`degArith`; [FrdI], Example 6.3: the
image of `λ ∈ 𝒪^▷_w` goes to `log #(𝒪_w/λ)`, of `λ ∈ ℝ_{>0}` to `−[K_v : ℝ]·log λ`). It vanishes
on rational functions (the product formula, `degArith_ratFun`), so it descends to
`Pic_Φ = Φ^gp/Φ^birat` (`picDeg`, surjective; [FrdI], Theorem 6.4(i) asserts that it is an
isomorphism `δ_A : Pic_Φ(A) ≅ ℝ`, which needs the unit theorem and the finiteness of the class
group; proved in `GlobalPic.lean`, `picDegEquiv`).

## Objects and degrees

* `degree X = deg^arith(X.α)`, `degreeNorm X = degree X/[K : ℚ]`;
* `degree_eq_of_iso`: the degree is an isomorphism invariant; `degree_hom`: for `φ : X → Y`,
  `degFr(φ)·deg X + deg^arith(Div φ) = deg Y`; `mul_degree_le`, `degree_frobenius` (morphisms
  of Frobenius type multiply the degree by the Frobenius degree, [FrdI], Theorem 5.1(i));
* **arithmetic line bundles** (`Iut/Arakelov`): `toDiv L = ((ord_w L)_w, (−log r_v)_v)`,
  `ofBundle L = (pt, toDiv L)`; **`degree_ofBundle : degree (ofBundle L) = L.deg`**,
  **`degreeNorm_ofBundle : degreeNorm (ofBundle L) = L.degNorm`** (the Arakelov degree of
  `Iut/Arakelov/LineBundle.lean`), `ofBundle_iso_of_rel` (isomorphic bundles give isomorphic
  objects), so `ArithPic K → {objects}/≅` with `degree ∘ ofBundle = ArithPic.deg`
  (`degree_ofBundle_eq_picDeg`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe w u

/-! ### The one-morphism base category and fixed-value monoids -/

/-- **The one-morphism category** (base category of a Frobenioid over the trivial Galois
extension, IUT I, Example 3.5(i)). -/
abbrev Pt : Type := Discrete PUnit.{1}

/-- The object of `Pt`. -/
abbrev pt : Pt := ⟨PUnit.unit⟩

instance : IsConnected Pt :=
  zigzag_isConnected fun a b => by rw [Subsingleton.elim a b]

/-- Every morphism of `Pt` is an isomorphism. -/
lemma isIso_pt {a b : Pt} (f : a ⟶ b) : IsIso f :=
  ⟨⟨Discrete.eqToHom (Subsingleton.elim _ _), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

instance : TotallyEpimorphic Pt := ⟨fun _ => ⟨fun _ _ _ => Subsingleton.elim _ _⟩⟩

/-- The fixed-value group-like monoid with value `V` on `Pt`. -/
abbrev constGrpOn (V : Type w) [AddCommGroup V] : GrpOn.{w} Pt where
  obj _ := V
  pb _ := AddMonoidHom.id V
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective _ := Function.injective_id
  pb_bijective_of_fsm _ _ := Function.bijective_id

/-- The fixed-value divisorial monoid on `Pt` given by a sharp, saturated, generating cone. -/
abbrev constDivMonoid (V : Type w) [AddCommGroup V] (S : AddSubmonoid V)
    (sharp : ∀ {x : V}, x ∈ S → -x ∈ S → x = 0)
    (saturated : ∀ {x : V} (n : ℕ), 0 < n → n • x ∈ S → x ∈ S)
    (generating : ∀ x : V, ∃ p ∈ S, ∃ q ∈ S, x = p - q) : DivMonoid.{w} Pt where
  toGrpOn := constGrpOn V
  pos _ := S
  pb_mem _ _ h := h
  sharp := sharp
  saturated := saturated
  generating := generating
  pos_surj_of_fsm _ _ y hy := ⟨y, hy, rfl⟩

/-- A fixed-value homomorphism of monoids on `Pt`. -/
abbrev constDivHom {V W : Type w} [AddCommGroup V] [AddCommGroup W] (f : W →+ V) :
    DivHom (constGrpOn W) (constGrpOn V) :=
  ⟨fun _ => f, fun _ _ => rfl⟩

/-! ### ℝ-arithmetic divisors -/

variable (K : Type u) [Field K] [NumberField K]

/-- **ℝ-arithmetic divisors** on `K`: `(V_fin →₀ ℝ) × (V_∞ → ℝ)`. -/
abbrev ArithDiv : Type u := (FinitePlace K →₀ ℝ) × (InfinitePlace K → ℝ)

/-- **Effective ℝ-arithmetic divisors**: nonnegative coordinates. -/
def effCone : AddSubmonoid (ArithDiv K) where
  carrier := {x | (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v}
  add_mem' {a b} ha hb := ⟨fun w => by simpa using add_nonneg (ha.1 w) (hb.1 w),
    fun v => by simpa using add_nonneg (ha.2 v) (hb.2 v)⟩
  zero_mem' := ⟨fun _ => le_rfl, fun _ => le_rfl⟩

variable {K}

lemma mem_effCone {x : ArithDiv K} : x ∈ effCone K ↔ (∀ w, 0 ≤ x.1 w) ∧ ∀ v, 0 ≤ x.2 v :=
  Iff.rfl

lemma effCone_sharp {x : ArithDiv K} (h : x ∈ effCone K) (h' : -x ∈ effCone K) : x = 0 := by
  rw [mem_effCone] at h h'
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · have := h'.1 w
    simp only [Prod.fst_neg, Finsupp.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff] at this
    exact le_antisymm this (h.1 w)
  · have := h'.2 v
    simp only [Prod.snd_neg, Pi.neg_apply, Left.nonneg_neg_iff] at this
    exact le_antisymm this (h.2 v)

lemma effCone_saturated {x : ArithDiv K} (n : ℕ) (hn : 0 < n) (h : n • x ∈ effCone K) :
    x ∈ effCone K := by
  rw [mem_effCone] at h ⊢
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have := h.1 w
    simp only [Prod.smul_fst, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hn'
  · have := h.2 v
    simp only [Prod.smul_snd, Pi.smul_apply, nsmul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hn'

lemma effCone_generating (x : ArithDiv K) : ∃ p ∈ effCone K, ∃ q ∈ effCone K, x = p - q := by
  let p : ArithDiv K := (x.1.mapRange (fun t => max t 0) (by simp), fun v => max (x.2 v) 0)
  let q : ArithDiv K := (x.1.mapRange (fun t => max (-t) 0) (by simp), fun v => max (-x.2 v) 0)
  refine ⟨p, ⟨fun w => by simp [p], fun v => by simp [p]⟩, q,
    ⟨fun w => by simp [q], fun v => by simp [q]⟩, ?_⟩
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp only [p, q, Prod.fst_sub, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]
  · simp only [p, q, Prod.snd_sub, Pi.sub_apply]
    rw [max_zero_sub_max_neg_zero_eq_self]

/-! ### Divisors of arithmetic line bundles -/

namespace ArithLineBundle'

open ArithLineBundle

/-- **The arithmetic divisor of an arithmetic line bundle** (with its chosen section):
`Σ_w ord_w(a_w)·[w] + Σ_v (−log r_v)·[v]`. -/
noncomputable def toDiv (L : ArithLineBundle K) : ArithDiv K :=
  (Finsupp.ofSupportFinite (fun w => (L.ord w : ℝ))
    (L.finite_support_ord.subset fun w hw => by simpa using hw),
   fun v => -Real.log (L.inf v))

@[simp] lemma toDiv_fst_apply (L : ArithLineBundle K) (w : FinitePlace K) :
    (toDiv L).1 w = L.ord w := rfl

@[simp] lemma toDiv_snd_apply (L : ArithLineBundle K) (v : InfinitePlace K) :
    (toDiv L).2 v = -Real.log (L.inf v) := rfl

lemma toDiv_mul (L M : ArithLineBundle K) : toDiv (L.mul M) = toDiv L + toDiv M := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp [ord_mul]
  · simp only [toDiv_snd_apply, Prod.snd_add, Pi.add_apply]
    rw [show (L.mul M).inf v = L.inf v * M.inf v from rfl,
      Real.log_mul (L.inf_pos v).ne' (M.inf_pos v).ne']
    ring

/-- The divisor depends only on the local norms and metrics. -/
lemma toDiv_congr (L M : ArithLineBundle K) (hfin : ∀ w, ‖L.fin w‖ = ‖M.fin w‖)
    (hinf : ∀ v, L.inf v = M.inf v) : toDiv L = toDiv M := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp [ord_eq_of_norm_eq L M w (hfin w)]
  · simp [hinf v]

end ArithLineBundle'

open ArithLineBundle'

variable (K) in
/-- **The principal divisor** `div(x)` of `x ∈ K^×`. -/
noncomputable def divOf (x : {x : K // x ≠ 0}) : ArithDiv K :=
  toDiv (ArithLineBundle.principal x.1 x.2)

variable (K) in
/-- **The realified rational functions** `ℝ·div(K^×) ⊆ Φ^gp` ([FrdI], Proposition 5.3). -/
noncomputable def ratFun : Submodule ℝ (ArithDiv K) := Submodule.span ℝ (Set.range (divOf K))

/-! ### The arithmetic degree -/

variable (K) in
/-- **The arithmetic degree** `deg^arith : Φ^gp → ℝ` ([FrdI], Example 6.3):
`x ↦ Σ_w x_w·log N(𝔭_w) + Σ_v [K_v : ℝ]·x_v`. -/
noncomputable def degArith : ArithDiv K →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ fun w : FinitePlace K => Real.log (primeNorm w)) ∘ₗ
      LinearMap.fst ℝ _ _ +
    (∑ v : InfinitePlace K, (v.mult : ℝ) • LinearMap.proj v) ∘ₗ LinearMap.snd ℝ _ _

lemma degArith_apply (x : ArithDiv K) :
    degArith K x = (x.1.sum fun w t => t * Real.log (primeNorm w)) +
      ∑ v, (v.mult : ℝ) * x.2 v := by
  simp [degArith, Finsupp.linearCombination_apply, smul_eq_mul]

/-- **`deg^arith` of the divisor of a bundle is its Arakelov degree.** -/
theorem degArith_toDiv (L : ArithLineBundle K) : degArith K (toDiv L) = L.deg := by
  rw [degArith_apply, ArithLineBundle.deg]
  congr 1
  · rw [finsum_eq_sum_of_support_subset _ (s := (toDiv L).1.support) (fun w hw => by
      rw [Function.mem_support, ArithLineBundle.finDeg_eq_ord] at hw
      simpa using left_ne_zero_of_mul hw)]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ArithLineBundle.finDeg_eq_ord, toDiv_fst_apply]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [ArithLineBundle.infDeg, toDiv_snd_apply]
    ring

/-- The arithmetic degree is nonnegative on effective divisors. -/
lemma degArith_nonneg {x : ArithDiv K} (hx : x ∈ effCone K) : 0 ≤ degArith K x := by
  rw [degArith_apply]
  refine add_nonneg (Finset.sum_nonneg fun w _ => mul_nonneg (hx.1 w)
    (Real.log_pos (one_lt_primeNorm w)).le) (Finset.sum_nonneg fun v _ => mul_nonneg
      (by exact_mod_cast (Nat.zero_le _)) (hx.2 v))

/-- **The product formula**: `deg^arith` vanishes on (realified) rational functions. -/
theorem degArith_ratFun {x : ArithDiv K} (hx : x ∈ ratFun K) : degArith K x = 0 := by
  have : ratFun K ≤ LinearMap.ker (degArith K) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, divOf, degArith_toDiv]
    exact ArithLineBundle.deg_principal x.1 x.2
  exact this hx

variable (K) in
/-- **The degree on `Pic_Φ = Φ^gp/Φ^birat`** ([FrdI], Theorem 6.4(i), `δ_A`). -/
noncomputable def picDeg : (ArithDiv K ⧸ ratFun K) →ₗ[ℝ] ℝ :=
  (ratFun K).liftQ (degArith K) fun _ hx => degArith_ratFun hx

lemma picDeg_mk (x : ArithDiv K) : picDeg K (Submodule.Quotient.mk x) = degArith K x := rfl

open scoped Classical in
/-- An archimedean divisor of every degree. -/
lemma degArith_single_inf (v : InfinitePlace K) (t : ℝ) :
    degArith K (0, Pi.single v t) = v.mult * t := by
  rw [degArith_apply]
  simp [Pi.single_apply]

/-- `δ_A` is surjective. -/
theorem picDeg_surjective : Function.Surjective (picDeg K) := by
  classical
  intro y
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hm : (v.mult : ℝ) ≠ 0 := by exact_mod_cast v.mult_pos.ne'
  refine ⟨Submodule.Quotient.mk (0, Pi.single v (y / v.mult)), ?_⟩
  rw [picDeg_mk, degArith_single_inf]
  field_simp

/-! ### The global realified Frobenioid -/

variable (K) in
/-- The divisor monoid `Φ^rlf` of the global realified Frobenioid. -/
noncomputable abbrev phiRlf : DivMonoid.{u} Pt :=
  constDivMonoid (ArithDiv K) (effCone K) effCone_sharp effCone_saturated effCone_generating

variable (K) in
/-- The rational function monoid `ℝ·div(K^×)`. -/
noncomputable abbrev bRlf : GrpOn.{u} Pt := constGrpOn (ratFun K)

variable (K) in
/-- `Div_B : ℝ·div(K^×) ↪ Φ^gp`. -/
noncomputable abbrev divBRlf : DivHom (bRlf K) (phiRlf K).toGrpOn :=
  constDivHom (ratFun K).subtype.toAddMonoidHom

variable (K) in
/-- **The global realified Frobenioid `C^⊩` of `K`** (IUT I, Example 3.5(i)). -/
abbrev GlobalRealified : Type u := Model (phiRlf K) (bRlf K) (divBRlf K)

variable (K) in
/-- **`C^⊩` is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem globalRealified_isFrobenioid :
    IsFrobenioid (Model.toElem (phiRlf K) (bRlf K) (divBRlf K)) :=
  Model.isFrobenioid

namespace GlobalRealified

/-- **The degree of an object** `deg^arith(α)` ([FrdI], Theorem 6.4(i)). -/
noncomputable def degree (X : GlobalRealified K) : ℝ := degArith K X.α

/-- The normalized degree `deg/[K : ℚ]`. -/
noncomputable def degreeNorm (X : GlobalRealified K) : ℝ := X.degree / Module.finrank ℚ K

/-- **Degrees along a morphism**: `degFr(φ)·deg(X) + deg^arith(Div φ) = deg(Y)`. -/
theorem degree_hom {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    (φ.deg : ℝ) * X.degree + degArith K φ.div = Y.degree := by
  have h := congrArg (degArith K) φ.rel
  rw [map_add, map_add, map_nsmul, nsmul_eq_mul] at h
  have hu : degArith K (φ.u : ArithDiv K) = 0 := degArith_ratFun φ.u.2
  change _ = degArith K Y.α + degArith K (φ.u : ArithDiv K) at h
  rw [hu, add_zero] at h
  exact h

/-- `degFr(φ)·deg(X) ≤ deg(Y)`. -/
theorem mul_degree_le {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    (φ.deg : ℝ) * X.degree ≤ Y.degree := by
  rw [← degree_hom φ]
  exact le_add_of_nonneg_right (degArith_nonneg φ.div_mem)

/-- **The degree is an isomorphism invariant.** -/
theorem degree_eq_of_iso {X Y : GlobalRealified K} (e : X ≅ Y) : X.degree = Y.degree := by
  obtain ⟨h₁, -, h₃⟩ := (Model.isIso_iff e.hom).mp inferInstance
  have := degree_hom e.hom
  rw [h₁, h₃, map_zero, PNat.one_coe, Nat.cast_one, one_mul, add_zero] at this
  exact this

/-- **Morphisms of Frobenius type multiply the degree by the Frobenius degree.** -/
theorem degree_frobenius {X Y : GlobalRealified K} (φ : X ⟶ Y)
    (h : IsFrobeniusType (Model.toElem (phiRlf K) (bRlf K) (divBRlf K)) φ) :
    Y.degree = φ.deg * X.degree := by
  have h₀ : φ.div = 0 := h.1.2
  rw [← degree_hom φ, h₀, map_zero, add_zero]

/-- **The object of an arithmetic line bundle**: `(pt, div(s))`. -/
noncomputable def ofBundle (L : ArithLineBundle K) : GlobalRealified K := ⟨pt, toDiv L⟩

/-- **The Frobenioid degree of the object of `L` is the Arakelov degree of `L`.** -/
theorem degree_ofBundle (L : ArithLineBundle K) : (ofBundle L).degree = L.deg :=
  degArith_toDiv L

/-- **The normalized degree is `degNorm`** (IUT III, Proposition 3.9(iii) normalization). -/
theorem degreeNorm_ofBundle (L : ArithLineBundle K) : (ofBundle L).degreeNorm = L.degNorm := by
  rw [degreeNorm, degree_ofBundle, ArithLineBundle.degNorm]

/-- **Isomorphic arithmetic line bundles give isomorphic objects** (a base-identity
isomorphism, whose rational function is `div(x)⁻¹`). -/
theorem ofBundle_iso_of_rel {L M : ArithLineBundle K} (h : ArithLineBundle.Rel L M) :
    Nonempty (ofBundle L ≅ ofBundle M) := by
  obtain ⟨x, hx, hf, hi⟩ := (ArithLineBundle.rel_iff_mul_principal L M).mp h
  have hM : toDiv M = toDiv L + divOf K ⟨x, hx⟩ := by
    rw [divOf, ← toDiv_mul]
    exact toDiv_congr _ _ hf hi
  let u : ratFun K := ⟨-divOf K ⟨x, hx⟩, (ratFun K).neg_mem (Submodule.subset_span ⟨_, rfl⟩)⟩
  let φ : ofBundle L ⟶ ofBundle M := Model.mk1 (𝟙 _) 0 (effCone K).zero_mem u (by
    change toDiv L + 0 = toDiv M + (-divOf K ⟨x, hx⟩)
    rw [hM]
    abel)
  haveI := Model.isIso_of φ rfl (inferInstanceAs (IsIso (𝟙 pt))) rfl
  exact ⟨asIso φ⟩

/-- `degree ∘ ofBundle` is the degree on the arithmetic Picard group. -/
theorem degree_ofBundle_eq_picDeg (L : ArithLineBundle K) :
    (ofBundle L).degree = (ArithPic.mk L).deg := by
  rw [degree_ofBundle, ArithPic.deg_mk]

end GlobalRealified

end Frobenioid

end Iut
