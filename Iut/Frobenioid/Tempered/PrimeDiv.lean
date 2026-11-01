/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.Thm34Temp
import Iut.Frobenioid.TemperedBase

/-!
# Divisor monoids from a set of prime log-divisors (MR18 T7, [EtTh] Prop 3.2(i), Prop 3.4(i))

In [EtTh] §3, for a connected tempered covering `Y` with `Δ^fil`-closure `Z_∞ → Y`, the divisor
monoid is `Φ₀(Y) = lim→ Div₊(Z_∞)^{Gal(Z_∞/Y)}` (Def 3.3(iii)). Its perfection is the monoid of
`Gal`-invariant `ℚ_{≥0}`-linear combinations of prime log-divisors of `Z_∞` (Prop 3.2(i): `DIV₊^pf`
is "a direct product of copies of `ℚ_{≥0}`, indexed by the cusps and irreducible components of the
special fiber"); its primes are the `Gal(Z_∞/Y)`-orbits of prime log-divisors (Rem 3.3.1), and
different `Δ^fil`-closures give the same primes on perfections (Rem 3.3.1, Ex 3.9(iii)).

This file formalises this monoid-theoretic layer for an arbitrary topological group `G` (the
tempered fundamental group) and an arbitrary `G`-set `P` (the prime log-divisors of the universal
combinatorial covering, on which `Π^tp` acts through `Gal(Z_∞/X)`), with coefficients in an
ordered ring `Λ` (`ℤ`, or `ℚ` for the perfection, `ℝ` for the realification):

* `PrimeDiv.divMonoid G P Λ`: the divisorial monoid on `D₀ = B^temp(G)⁰ = OrbitObj G` with
  `Φ^gp(G/H)` = `G`-invariant functions `(G/H) × P → Λ` (equivalently: `H`-invariant functions
  on `P`, i.e. `Gal`-invariant divisors) and `Φ(G/H)` the nonnegative ones; pull-backs are
  composition.
* `factorEquiv`: `Φ^gp(A) ≃+ (orbits → Λ)`, the **factorization** of [FrdI] Def 2.4(i)(c) — the
  product over the `G`-orbits of `(G/H) × P` (abstract form of [EtTh] Prop 3.2(i)), with
  `mem_pos_iff_factor` (effective ⇔ all components `≥ 0`).
* `isPrimary_iff`: the **primary elements** ([FrdI] §0) are the positive multiples `c • ind z` of
  orbit indicators; `preceq_ind_iff`: `ind z ≼ ind w` iff `z, w` lie in one orbit. Hence the primes
  of `Φ(A)` are the `G`-orbits of `(G/H) × P` ([EtTh] Rem 3.3.1).
* `nonDilating`: **`Φ` is non-dilating** ([EtTh] Prop 3.4(i); [FrdI] Def 1.1(i),(ii)) in the sense
  `DivMonoid.NonDilating` used by `BsFldPreserve.lean` and `EnvTransport.lean`; no finiteness or
  surjectivity hypothesis is needed. `nowhereGroupLike` for nonempty `P`.
* The **cuspidal/non-cuspidal splitting** for `P = Pₙ ⊕ P_c` (components ⊕ cusps):
  `ncspPart`, `cspPart`, `ncspPart_add_cspPart`, compatible with pull-backs, and the primes split
  accordingly (`IsCuspidalOrbit`).

The geometric input — the `Π^tp`-set of components and cusps of the universal combinatorial
covering of the elliptic coverings — is the parameter `P`; it is not provided by
`tempered-fundamental-groups` yet (see the MR18 plan, T7 scoping, 2026-11-01).
-/

namespace Iut

namespace Frobenioid

namespace PrimeDiv

open CategoryTheory

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] (P : Type u) [MulAction G P]
variable (Λ : Type) [CommRing Λ] [LinearOrder Λ] [IsStrictOrderedRing Λ]

/-- **`Φ^gp(G/H)`**: the `G`-invariant functions `(G/H) × P → Λ` (diagonal action), i.e. the
`Gal`-invariant `Λ`-linear combinations of prime log-divisors. -/
def divGp (A : OrbitObj G) : AddSubgroup ((G ⧸ A.H) × P → Λ) where
  carrier := {f | ∀ (g : G) (z : (G ⧸ A.H) × P), f (g • z) = f z}
  add_mem' {f f'} hf hf' g z := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hf hf' ⊢
    rw [hf, hf']
  zero_mem' _ _ := rfl
  neg_mem' {f} hf g z := by
    simp only [Set.mem_setOf_eq, Pi.neg_apply] at hf ⊢
    rw [hf]

variable {G P Λ}

/-- The pull-back along an equivariant map `G/H → G/H'`: composition in the first variable. -/
def pbFun {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF : ∀ (g : G) x, F (g • x) = g • F x) :
    divGp G P Λ B →+ divGp G P Λ A where
  toFun f := ⟨fun z => f.1 (F z.1, z.2), fun g z => by
    change f.1 (F (g • z.1), g • z.2) = _
    rw [hF]
    exact f.2 g (F z.1, z.2)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [LinearOrder Λ] [IsStrictOrderedRing Λ] in
lemma pbFun_apply {A B : OrbitObj G} (F : G ⧸ A.H → G ⧸ B.H) (hF) (f : divGp G P Λ B) (z) :
    (pbFun F hF f).1 z = f.1 (F z.1, z.2) := rfl

omit [LinearOrder Λ] [IsStrictOrderedRing Λ] in
lemma pbFun_injective {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF)
    (hs : Function.Surjective F) : Function.Injective (pbFun (P := P) (Λ := Λ) F hF) := by
  intro f f' h
  apply Subtype.ext
  funext ⟨y, n⟩
  obtain ⟨x, rfl⟩ := hs y
  exact congrFun (congrArg Subtype.val h) (x, n)

/-- The inverse of a bijective equivariant map is equivariant. -/
lemma symm_smul {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF : ∀ (g : G) x, F (g • x) = g • F x)
    (hb : Function.Bijective F) (g : G) (y : G ⧸ B.H) :
    (Equiv.ofBijective F hb).symm (g • y) = g • (Equiv.ofBijective F hb).symm y := by
  apply (Equiv.ofBijective F hb).injective
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, hF, ← Equiv.ofBijective_apply F hb,
    Equiv.apply_symm_apply]

omit [LinearOrder Λ] [IsStrictOrderedRing Λ] in
lemma pbFun_bijective {A B : OrbitObj G} {F : G ⧸ A.H → G ⧸ B.H} (hF)
    (hb : Function.Bijective F) : Function.Bijective (pbFun (P := P) (Λ := Λ) F hF) := by
  refine ⟨pbFun_injective hF hb.2, fun f => ⟨pbFun _ (symm_smul hF hb) f, ?_⟩⟩
  apply Subtype.ext
  funext ⟨x, n⟩
  change f.1 ((Equiv.ofBijective F hb).symm (F x), n) = f.1 (x, n)
  rw [← Equiv.ofBijective_apply F hb, Equiv.symm_apply_apply]

/-- The effective divisors: the nonnegative functions. -/
def nonneg (A : OrbitObj G) : AddSubmonoid (divGp G P Λ A) where
  carrier := {f | ∀ z, 0 ≤ f.1 z}
  add_mem' hf hf' z := add_nonneg (hf z) (hf' z)
  zero_mem' _ := le_refl 0

/-- The positive part `max(f, 0)` of an invariant function. -/
def posPart {A : OrbitObj G} (f : divGp G P Λ A) : divGp G P Λ A :=
  ⟨fun z => max (f.1 z) 0, fun g z => by simp only [f.2 g z]⟩

lemma sharp_aux {A : OrbitObj G} {x : divGp G P Λ A} (hx : ∀ z, 0 ≤ x.1 z)
    (hx' : ∀ z, 0 ≤ (-x).1 z) : x = 0 := by
  refine Subtype.ext (funext fun z => le_antisymm ?_ (hx z))
  have := hx' z
  simp only [AddSubgroup.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff] at this
  exact this

lemma saturated_aux {A : OrbitObj G} {x : divGp G P Λ A} (n : ℕ) (hn : 0 < n)
    (h : ∀ z, 0 ≤ (n • x).1 z) (z) : 0 ≤ x.1 z := by
  have := h z
  simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
  exact nonneg_of_mul_nonneg_right this (by exact_mod_cast hn)

lemma generating_aux {A : OrbitObj G} (x : divGp G P Λ A) : x = posPart x - posPart (-x) := by
  refine Subtype.ext (funext fun z => ?_)
  change x.1 z = max (x.1 z) 0 - max (-x.1 z) 0
  rcases le_total (x.1 z) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    ring

variable [IsTopologicalGroup G]

variable (G P Λ) in
/-- **`Φ^gp` as a group-like monoid on `B^temp(G)⁰`.** -/
abbrev divGrp : GrpOn.{u} (OrbitObj G) where
  obj A := divGp G P Λ A
  pb f := pbFun f.toFun f.map_smul
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective f := pbFun_injective f.map_smul f.surjective
  pb_bijective_of_fsm _ hf := pbFun_bijective _ (OrbitHom.bijective_of_isFSM hf)

variable (G P Λ) in
/-- **The divisor monoid `Φ` of `Gal`-invariant effective `Λ`-divisors** ([EtTh] Def 3.3(iii);
for `Λ = ℚ` its perfection, [EtTh] Prop 3.2(i)). -/
abbrev divMonoid : DivMonoid.{u} (OrbitObj G) where
  toGrpOn := divGrp G P Λ
  pos A := nonneg A
  pb_mem _ _ hx z := hx _
  sharp hx hx' := sharp_aux hx hx'
  saturated n hn h := saturated_aux n hn h
  generating x := ⟨posPart x, fun _ => le_max_right _ _, posPart (-x),
    fun _ => le_max_right _ _, generating_aux x⟩
  pos_surj_of_fsm {A B} f hf y hy := by
    obtain ⟨x, hx⟩ := (divGrp G P Λ).pb_bijective_of_fsm f hf |>.2 y
    refine ⟨x, fun z => ?_, hx⟩
    obtain ⟨w, hw⟩ := (OrbitHom.bijective_of_isFSM hf).2 z.1
    have := hy (w, z.2)
    rw [← hx] at this
    change 0 ≤ x.1 (f.toFun w, z.2) at this
    rwa [hw] at this

lemma divMonoid_obj (A : OrbitObj G) : (divMonoid G P Λ).obj A = divGp G P Λ A := rfl

lemma mem_pos_iff {A : OrbitObj G} (x : (divMonoid G P Λ).obj A) :
    x ∈ (divMonoid G P Λ).pos A ↔ ∀ z, 0 ≤ x.1 z := Iff.rfl

lemma pb_apply {A B : OrbitObj G} (f : A ⟶ B) (x : (divMonoid G P Λ).obj B) (z) :
    ((divMonoid G P Λ).pb f x).1 z = x.1 (f.toFun z.1, z.2) := rfl

/-! ### The factorization: products over orbits ([EtTh] Prop 3.2(i), [FrdI] Def 2.4(i)(c)) -/

/-- The set of `G`-orbits of `(G/H) × P` (= the `H`-orbits of `P`, the primes of `Φ(G/H)`). -/
abbrev Orbits (A : OrbitObj G) : Type u := MulAction.orbitRel.Quotient G ((G ⧸ A.H) × P)

variable (P Λ) in
/-- **The factorization isomorphism** `Φ^gp(A) ≃+ ∏_{orbits} Λ`. -/
noncomputable def factorEquiv (A : OrbitObj G) :
    (divMonoid G P Λ).obj A ≃+ (Orbits (P := P) A → Λ) where
  toFun x o := x.1 o.out
  invFun φ := ⟨fun z => φ (Quotient.mk _ z), fun g z => by
    exact congrArg φ (Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit z g)))⟩
  left_inv x := by
    apply Subtype.ext
    funext z
    change x.1 (Quotient.mk (MulAction.orbitRel G _) z).out = x.1 z
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp
      (Quotient.mk_out (s := MulAction.orbitRel G ((G ⧸ A.H) × P)) z)
    rw [← hg, x.2]
  right_inv φ := by
    funext o
    change φ (Quotient.mk _ o.out) = φ o
    rw [Quotient.out_eq]
  map_add' _ _ := rfl

lemma factorEquiv_apply_mk {A : OrbitObj G} (x : (divMonoid G P Λ).obj A) (z) :
    factorEquiv P Λ A x (Quotient.mk _ z) = x.1 z := by
  change x.1 (Quotient.mk (MulAction.orbitRel G _) z).out = x.1 z
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp
    (Quotient.mk_out (s := MulAction.orbitRel G ((G ⧸ A.H) × P)) z)
  rw [← hg, x.2]

/-- Effective divisors are exactly those with nonnegative components. -/
lemma mem_pos_iff_factor {A : OrbitObj G} (x : (divMonoid G P Λ).obj A) :
    x ∈ (divMonoid G P Λ).pos A ↔ ∀ o, 0 ≤ factorEquiv P Λ A x o := by
  refine ⟨fun h o => h _, fun h z => ?_⟩
  rw [← factorEquiv_apply_mk]
  exact h _

/-! ### Orbit indicators and primary elements -/

open Classical in
/-- **The prime divisor attached to an orbit**: the indicator of the `G`-orbit of `z`. -/
noncomputable def ind {A : OrbitObj G} (z : (G ⧸ A.H) × P) : (divMonoid G P Λ).obj A :=
  ⟨fun w => if w ∈ MulAction.orbit G z then 1 else 0, fun g w => by
    simp only [← MulAction.orbit_eq_iff, MulAction.orbit_smul]⟩

open Classical in
lemma ind_apply {A : OrbitObj G} (z w : (G ⧸ A.H) × P) :
    (ind (Λ := Λ) z).1 w = if w ∈ MulAction.orbit G z then 1 else 0 := rfl

lemma ind_self {A : OrbitObj G} (z : (G ⧸ A.H) × P) : (ind (Λ := Λ) z).1 z = 1 := by
  rw [ind_apply, if_pos (MulAction.mem_orbit_self z)]

lemma ind_nonneg {A : OrbitObj G} (z w : (G ⧸ A.H) × P) : 0 ≤ (ind (Λ := Λ) z).1 w := by
  rw [ind_apply]; split_ifs <;> simp

lemma ind_mem_pos {A : OrbitObj G} (z : (G ⧸ A.H) × P) :
    ind (Λ := Λ) z ∈ (divMonoid G P Λ).pos A := ind_nonneg z

lemma ind_ne_zero {A : OrbitObj G} (z : (G ⧸ A.H) × P) : ind (Λ := Λ) z ≠ 0 := by
  intro h
  have := ind_self (Λ := Λ) z
  rw [h] at this
  exact zero_ne_one this

/-- Invariant functions take one value on each orbit. -/
lemma apply_eq_of_mem_orbit {A : OrbitObj G} (x : (divMonoid G P Λ).obj A)
    {z w : (G ⧸ A.H) × P} (h : w ∈ MulAction.orbit G z) : x.1 w = x.1 z := by
  obtain ⟨g, rfl⟩ := h
  exact x.2 g z

/-- An element `≼ ind z` vanishes off the orbit of `z`. -/
lemma eq_zero_of_preceq_ind {A : OrbitObj G} {b : (divMonoid G P Λ).obj A}
    (hb : b ∈ (divMonoid G P Λ).pos A) {z w : (G ⧸ A.H) × P}
    (h : (divMonoid G P Λ).preceq b (ind z)) (hw : w ∉ MulAction.orbit G z) : b.1 w = 0 := by
  obtain ⟨n, -, hn⟩ := h
  have h1 := hn w
  change 0 ≤ (n • ind (Λ := Λ) z).1 w - b.1 w at h1
  simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, ind_apply, if_neg hw, smul_zero,
    zero_sub, Left.nonneg_neg_iff] at h1
  exact le_antisymm h1 (hb w)

/-- An element vanishing off the orbit of `z` is `b(z) • ind z`. -/
lemma eq_smul_ind {A : OrbitObj G} {b : (divMonoid G P Λ).obj A} {z : (G ⧸ A.H) × P}
    (h : ∀ w, w ∉ MulAction.orbit G z → b.1 w = 0) (w) :
    b.1 w = b.1 z * (ind (Λ := Λ) z).1 w := by
  rw [ind_apply]
  split_ifs with hw
  · rw [mul_one, apply_eq_of_mem_orbit b hw]
  · rw [mul_zero, h w hw]

variable [Archimedean Λ]

omit [Archimedean Λ] in
/-- `ind z ≼ ind w` iff `z` and `w` lie in one orbit. -/
lemma preceq_ind_iff {A : OrbitObj G} (z w : (G ⧸ A.H) × P) :
    (divMonoid G P Λ).preceq (ind z) (ind w) ↔ z ∈ MulAction.orbit G w := by
  constructor
  · intro h
    by_contra hz
    have := eq_zero_of_preceq_ind (ind_mem_pos z) h hz
    rw [ind_self] at this
    exact one_ne_zero this
  · intro h
    refine ⟨1, one_pos, fun v => ?_⟩
    change 0 ≤ ((1 : ℕ) • ind (Λ := Λ) w).1 v - (ind (Λ := Λ) z).1 v
    have : MulAction.orbit G z = MulAction.orbit G w := MulAction.orbit_eq_iff.mpr h
    rw [one_smul, ind_apply, ind_apply, this, sub_self]

/-- An element `0 ≤ b ≤ n • (c • ind z)` with `b ≠ 0` dominates a multiple of `ind z`. -/
lemma preceq_of_le_ind {A : OrbitObj G} {a b : (divMonoid G P Λ).obj A} {z : (G ⧸ A.H) × P}
    (ha : ∀ w, w ∉ MulAction.orbit G z → a.1 w = 0)
    (hb : ∀ w, w ∉ MulAction.orbit G z → b.1 w = 0) (hb0 : 0 < b.1 z) :
    (divMonoid G P Λ).preceq a b := by
  obtain ⟨n, hn⟩ := Archimedean.arch (a.1 z) hb0
  refine ⟨n + 1, Nat.succ_pos n, fun w => ?_⟩
  change 0 ≤ ((n + 1) • b).1 w - a.1 w
  simp only [AddSubgroup.coe_nsmul, Pi.smul_apply]
  rw [eq_smul_ind (Λ := Λ) ha w, eq_smul_ind (Λ := Λ) hb w]
  have hi := ind_nonneg (Λ := Λ) z w
  have : a.1 z ≤ (n + 1) • b.1 z := hn.trans (by
    rw [succ_nsmul]; exact le_add_of_nonneg_right hb0.le)
  rw [← smul_mul_assoc, sub_nonneg]
  exact mul_le_mul_of_nonneg_right this hi

/-- **The primary elements of `Φ(A)`** ([FrdI] §0) are the positive multiples of orbit
indicators; with `preceq_ind_iff`, the primes of `Φ(A)` are the `G`-orbits of `(G/H) × P`
([EtTh] Rem 3.3.1). -/
theorem isPrimary_iff {A : OrbitObj G} (a : (divMonoid G P Λ).obj A) :
    (divMonoid G P Λ).IsPrimary a ↔
      a ∈ (divMonoid G P Λ).pos A ∧ ∃ z, 0 < a.1 z ∧ ∀ w, w ∉ MulAction.orbit G z → a.1 w = 0 := by
  constructor
  · rintro ⟨ha, ha0, hprim⟩
    refine ⟨ha, ?_⟩
    have : ∃ z, a.1 z ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (Subtype.ext (funext h))
    obtain ⟨z, hz⟩ := this
    have hpos : 0 < a.1 z := lt_of_le_of_ne (ha z) (Ne.symm hz)
    -- `b = a(z) • ind z ≤ a`
    let b : (divMonoid G P Λ).obj A :=
      ⟨fun w => a.1 z * (ind (Λ := Λ) z).1 w, fun g w => by
        change a.1 z * (ind (Λ := Λ) z).1 (g • w) = a.1 z * (ind (Λ := Λ) z).1 w
        rw [(ind (Λ := Λ) z).2 g w]⟩
    have hbpos : b ∈ (divMonoid G P Λ).pos A := fun w => mul_nonneg hpos.le (ind_nonneg z w)
    have hb0 : b ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) z
      change a.1 z * (ind (Λ := Λ) z).1 z = 0 at this
      rw [ind_self, mul_one] at this
      exact hz this
    have hba : (divMonoid G P Λ).preceq b a := by
      refine ⟨1, one_pos, fun w => ?_⟩
      change 0 ≤ ((1 : ℕ) • a).1 w - a.1 z * (ind (Λ := Λ) z).1 w
      rw [one_smul, ind_apply]
      split_ifs with hw
      · rw [mul_one, apply_eq_of_mem_orbit a hw, sub_self]
      · rw [mul_zero, sub_zero]; exact ha w
    obtain ⟨n, -, hn⟩ := hprim b hbpos hb0 hba
    refine ⟨z, hpos, fun w hw => le_antisymm ?_ (ha w)⟩
    have h1 := hn w
    change 0 ≤ (n • b).1 w - a.1 w at h1
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply] at h1
    change 0 ≤ n • (a.1 z * (ind (Λ := Λ) z).1 w) - a.1 w at h1
    rw [ind_apply, if_neg hw, mul_zero, smul_zero, zero_sub, Left.nonneg_neg_iff] at h1
    exact h1
  · rintro ⟨ha, z, hz, hsupp⟩
    refine ⟨ha, fun h => by rw [h] at hz; exact lt_irrefl _ hz, fun b hb hb0 hba => ?_⟩
    have hbs : ∀ w, w ∉ MulAction.orbit G z → b.1 w = 0 := by
      intro w hw
      obtain ⟨n, -, hn⟩ := hba
      have h1 := hn w
      change 0 ≤ (n • a).1 w - b.1 w at h1
      simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, hsupp w hw, smul_zero, zero_sub,
        Left.nonneg_neg_iff] at h1
      exact le_antisymm h1 (hb w)
    have hbz : 0 < b.1 z := by
      rcases (hb z).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hb0
        refine Subtype.ext (funext fun w => ?_)
        rw [eq_smul_ind (Λ := Λ) hbs w, ← h, zero_mul]
        rfl
    exact preceq_of_le_ind hsupp hbs hbz

/-- The orbit indicators are primary. -/
lemma isPrimary_ind {A : OrbitObj G} (z : (G ⧸ A.H) × P) :
    (divMonoid G P Λ).IsPrimary (ind z) :=
  (isPrimary_iff _).2 ⟨ind_mem_pos z, z, by rw [ind_self]; exact one_pos, fun w hw => by
    rw [ind_apply, if_neg hw]⟩

omit [Archimedean Λ] in
/-- **`Φ` is non-dilating** ([EtTh] Prop 3.4(i)): an endomorphism `f` of `A` with `f^*(a) ≼ a`
for all primary `a` fixes every element of `Φ^gp(A)`. -/
theorem pb_eq_self_of_preceq {A : OrbitObj G} (f : A ⟶ A)
    (h : ∀ z : (G ⧸ A.H) × P, (divMonoid G P Λ).preceq ((divMonoid G P Λ).pb f (ind z)) (ind z))
    (x : (divMonoid G P Λ).obj A) : (divMonoid G P Λ).pb f x = x := by
  refine Subtype.ext (funext fun w => ?_)
  change x.1 (f.toFun w.1, w.2) = x.1 w
  set z : (G ⧸ A.H) × P := (f.toFun w.1, w.2)
  have hw : w ∈ MulAction.orbit G z := by
    by_contra hw
    have := eq_zero_of_preceq_ind (fun v => ind_nonneg z (f.toFun v.1, v.2)) (h z) hw
    change (ind (Λ := Λ) z).1 z = 0 at this
    rw [ind_self] at this
    exact one_ne_zero this
  exact (apply_eq_of_mem_orbit x hw).symm

theorem nonDilating : (divMonoid G P Λ).NonDilating := fun _ f hf x _ =>
  pb_eq_self_of_preceq f (fun z => hf _ (isPrimary_ind z)) x

omit [Archimedean Λ] in
theorem nowhereGroupLike [Nonempty P] : (divMonoid G P Λ).NowhereGroupLike := fun A =>
  ⟨ind ((QuotientGroup.mk 1 : G ⧸ A.H), Classical.arbitrary P), ind_mem_pos _, ind_ne_zero _⟩

/-! ### Cuspidal and non-cuspidal parts (`P = components ⊕ cusps`) -/

section Cusp

omit [Archimedean Λ]

variable {Pn Pc : Type u} [MulAction G Pn] [MulAction G Pc]

/-- An orbit is **cuspidal** if its prime log-divisors are cusps. -/
def IsCuspidal {A : OrbitObj G} (z : (G ⧸ A.H) × (Pn ⊕ Pc)) : Prop := z.2.isRight

instance {A : OrbitObj G} (z : (G ⧸ A.H) × (Pn ⊕ Pc)) : Decidable (IsCuspidal z) :=
  inferInstanceAs (Decidable (z.2.isRight = true))

omit [IsTopologicalGroup G] in
lemma isCuspidal_smul {A : OrbitObj G} (g : G) (z : (G ⧸ A.H) × (Pn ⊕ Pc)) :
    IsCuspidal (g • z) ↔ IsCuspidal z := by
  rcases z with ⟨x, p | p⟩ <;> rfl

/-- The **cuspidal part** of a divisor (restriction to the cusps). -/
noncomputable def cspPart {A : OrbitObj G} (x : (divMonoid G (Pn ⊕ Pc) Λ).obj A) :
    (divMonoid G (Pn ⊕ Pc) Λ).obj A :=
  ⟨fun z => if IsCuspidal z then x.1 z else 0, fun g z => by
    simp only [isCuspidal_smul, x.2 g z]⟩

/-- The **non-cuspidal part** of a divisor (restriction to the components of the special
fibre). -/
noncomputable def ncspPart {A : OrbitObj G} (x : (divMonoid G (Pn ⊕ Pc) Λ).obj A) :
    (divMonoid G (Pn ⊕ Pc) Λ).obj A :=
  ⟨fun z => if IsCuspidal z then 0 else x.1 z, fun g z => by
    simp only [isCuspidal_smul, x.2 g z]⟩

lemma ncspPart_add_cspPart {A : OrbitObj G} (x : (divMonoid G (Pn ⊕ Pc) Λ).obj A) :
    ncspPart x + cspPart x = x := by
  refine Subtype.ext (funext fun z => ?_)
  change (if IsCuspidal z then 0 else x.1 z) + (if IsCuspidal z then x.1 z else 0) = x.1 z
  split_ifs <;> simp

lemma cspPart_mem_pos {A : OrbitObj G} {x : (divMonoid G (Pn ⊕ Pc) Λ).obj A}
    (hx : x ∈ (divMonoid G (Pn ⊕ Pc) Λ).pos A) : cspPart x ∈ (divMonoid G (Pn ⊕ Pc) Λ).pos A :=
  fun z => by
    change 0 ≤ if IsCuspidal z then x.1 z else 0
    split_ifs
    exacts [hx z, le_refl 0]

lemma ncspPart_mem_pos {A : OrbitObj G} {x : (divMonoid G (Pn ⊕ Pc) Λ).obj A}
    (hx : x ∈ (divMonoid G (Pn ⊕ Pc) Λ).pos A) : ncspPart x ∈ (divMonoid G (Pn ⊕ Pc) Λ).pos A :=
  fun z => by
    change 0 ≤ if IsCuspidal z then 0 else x.1 z
    split_ifs
    exacts [le_refl 0, hx z]

/-- Pull-backs respect the cuspidal part (coverings map cusps to cusps and components to
components). -/
lemma pb_cspPart {A B : OrbitObj G} (f : A ⟶ B) (x : (divMonoid G (Pn ⊕ Pc) Λ).obj B) :
    (divMonoid G (Pn ⊕ Pc) Λ).pb f (cspPart x) = cspPart ((divMonoid G (Pn ⊕ Pc) Λ).pb f x) :=
  rfl

lemma pb_ncspPart {A B : OrbitObj G} (f : A ⟶ B) (x : (divMonoid G (Pn ⊕ Pc) Λ).obj B) :
    (divMonoid G (Pn ⊕ Pc) Λ).pb f (ncspPart x) = ncspPart ((divMonoid G (Pn ⊕ Pc) Λ).pb f x) :=
  rfl

end Cusp

end PrimeDiv

end Frobenioid

end Iut
