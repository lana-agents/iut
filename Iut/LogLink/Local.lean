/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LogShell

/-!
# Local log-links (IUT III, Definition 1.1(i), Proposition 1.2 at `v ∈ V^non`)

Let `k` be a complete discretely valued field of characteristic `0` with residue characteristic
`p` (`‖p‖ < 1`). Following the scope decisions of `Iut/LogLink/README.md`:

* the **principal units** `1 + 𝔪_k` form a subgroup `prinUnits k` of `kˣ`, and the `p`-adic
  logarithm is a homomorphism `logHom : 1 + 𝔪_k → (k, +)` (IUT III, Proposition 1.2(ii): the
  log-link is compatible with the multiplicative structure of the domain and the additive
  structure of the codomain); near `1` it is an isometry (`norm_padicLog_one_add`), the
  radius form of the compatibility with log-volumes (Proposition 1.2(iii));
* a **local log-link** `†F_v → ‡F_v` (`LocalLogLink`) is the tautological log-link
  `u ↦ log u` followed by a poly-isomorphism `log(†F_v) ≅ ‡F_v`, modelled by a bicontinuous ring
  isomorphism `φ` (Definition 1.1(i));
* **holomorphic log-shells** (Proposition 1.2(v)): the log-shell, read in the codomain of any
  log-link, is the log-shell `Iut.logShell k p` of the codomain (`LocalLogLink.image_logShell`);
  it is bounded (`(a_non)`), contains the integers of the codomain (`(b_non)`), and contains the
  image of the units of the domain (`(c_non)`, `LocalLogLink.toFun_mem_logShell`);
* **Kummer non-compatibility** (Proposition 1.2(iv)): no ring homomorphism agrees with a log-link
  on the principal units (`LocalLogLink.not_ringHom_eq_toFun`);
* **unit-induced identifications** (Proposition 1.2(vi), (viii)): an additive automorphism `ψ`
  of `k` is unit-induced if `ψ ∘ log = log ∘ α` for an automorphism `α` of the principal units.
  **Unit-induced identifications preserve the log-shell** (`image_logShell_of_unitInduced`).
  Examples: `x ↦ −x` (induced by the inversion of the units, `unitInduced_neg`) and every
  bicontinuous ring automorphism (`unitInduced_ringEquiv`). Multiplication by an element `q` with
  `0 < ‖q‖ < 1` (e.g. a Tate parameter) does not preserve the log-shell
  (`scale_image_logShell_ne`), hence is not unit-induced (`not_unitInduced_scale`).
-/

namespace Iut

namespace LogLink

open PadicLogVolume Filter Topology
open scoped Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-! ### Principal units and the logarithm -/

section PrinUnits

variable (k)

/-- **The principal units** `1 + 𝔪_k` as a subgroup of `kˣ`. -/
def prinUnits : Subgroup kˣ where
  carrier := {x | ‖(x : k) - 1‖ < 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    exact norm_mul_sub_one_lt ha hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] at ha ⊢
    exact norm_inv_sub_one_lt ha

variable {k}

/-- The underlying element of `k` of a principal unit. -/
abbrev pval (u : prinUnits k) : k := ((u : kˣ) : k)

lemma norm_pval_sub_one_lt (u : prinUnits k) : ‖pval u - 1‖ < 1 := u.2

/-- A principal unit given by an element `x` with `‖x − 1‖ < 1`. -/
def prinUnit (x : k) (hx : ‖x - 1‖ < 1) : prinUnits k :=
  ⟨Units.mk0 x (ne_zero_of_norm_sub_one_lt hx), hx⟩

@[simp] lemma pval_prinUnit (x : k) (hx : ‖x - 1‖ < 1) : pval (prinUnit x hx) = x := rfl

@[simp] lemma pval_mul (u v : prinUnits k) : pval (u * v) = pval u * pval v := rfl

@[simp] lemma pval_one : pval (1 : prinUnits k) = 1 := rfl

@[simp] lemma pval_inv (u : prinUnits k) : pval u⁻¹ = (pval u)⁻¹ := by
  simp [pval, Units.val_inv_eq_inv_val]

end PrinUnits

variable [CompleteSpace k] [CharZero k] {p : ℕ}

/-- **The logarithm is a homomorphism** from the principal units to the additive group of `k`
(IUT III, Proposition 1.2(ii)). -/
def logHom (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) : Additive (prinUnits k) →+ k where
  toFun x := padicLog (pval x.toMul)
  map_zero' := by simp
  map_add' x y := padicLog_mul hp hpk x.toMul.2 y.toMul.2

@[simp] lemma logHom_apply (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (u : prinUnits k) :
    logHom hp hpk (Additive.ofMul u) = padicLog (pval u) := rfl

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k] in
/-- `(n⁻¹)·x` is preserved by additive maps of fields of characteristic `0`. -/
lemma map_natCast_inv_mul (ψ : k →+ k) {n : ℕ} (hn : n ≠ 0) (x : k) :
    ψ ((n : k)⁻¹ * x) = (n : k)⁻¹ * ψ x := by
  have hn' : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : ψ x = (n : k) * ψ ((n : k)⁻¹ * x) := by
    conv_lhs => rw [← mul_inv_cancel_left₀ hn' x]
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  rw [h, inv_mul_cancel_left₀ hn']

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
  [CharZero k] in
lemma two_mul_natCast (p : ℕ) : (2 * (p : k)) = ((2 * p : ℕ) : k) := by push_cast; ring

/-- **The logarithm of a principal unit lies in the log-shell** (`log u = (2p)⁻¹·log(u^{2p})`). -/
theorem padicLog_mem_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {u : k} (hu : ‖u - 1‖ < 1) :
    padicLog u ∈ logShell k p := by
  refine ⟨u ^ (2 * p), norm_pow_sub_one_lt hu _, ?_⟩
  rw [padicLog_pow hp hpk hu, two_mul_natCast, inv_mul_cancel_left₀]
  exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero two_ne_zero hp.ne_zero)

/-- **The logarithm is an isometry near `1`**: `‖log(1 + a)‖ = ‖a‖` for `‖a‖ ≤ ‖2p‖` (the radius
form of the compatibility of the log-link with log-volumes, IUT III, Proposition 1.2(iii)). -/
theorem norm_padicLog_one_add (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) : ‖padicLog (1 + a)‖ = ‖a‖ := by
  have ha1 : ‖a‖ < 1 := ha.trans_lt (norm_two_mul_lt_one hpk)
  rw [padicLog_one_add hp hpk ha1]
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hr := norm_logRem_le hp hpk ha
  have hlt : ‖logRem a‖ < ‖a‖ := hr.trans_lt
    (mul_lt_of_lt_one_left (norm_pos_iff.2 ha0) hpk)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- **Every small element is a logarithm**: `‖y‖ ≤ ‖2p‖ → y = log u` for a principal unit `u`. -/
theorem exists_prinUnit_padicLog_eq (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k}
    (hy : ‖y‖ ≤ ‖2 * (p : k)‖) : ∃ u : prinUnits k, padicLog (pval u) = y := by
  obtain ⟨a, ha, hlog⟩ := exists_padicLog_eq hp hpk hy
  exact ⟨prinUnit (1 + a) (by simpa using ha.trans_lt (norm_two_mul_lt_one hpk)), hlog⟩

/-! ### Local log-links -/

variable (k) in
/-- **A local log-link** `†F_v → ‡F_v` (IUT III, Definition 1.1(i)): the tautological log-link
`u ↦ log u` on the principal units of the domain, followed by the poly-isomorphism
`log(†F_v) ≅ ‡F_v`, modelled by a bicontinuous ring isomorphism `φ` of the copies of `k`. -/
structure LocalLogLink where
  /-- The isomorphism `log(†F_v) ≅ ‡F_v`. -/
  φ : k ≃+* k
  cont : Continuous φ
  cont_symm : Continuous φ.symm

namespace LocalLogLink

variable (L : LocalLogLink k)

/-- **The tautological log-link** (`φ = id`). -/
def taut : LocalLogLink k := ⟨RingEquiv.refl k, continuous_id, continuous_id⟩

/-- The log-link as a map on the principal units of the domain: `u ↦ φ(log u)`. -/
def toFun (u : k) : k := L.φ (padicLog u)

/-- **The log-link is a homomorphism** `(1 + 𝔪, ·) → (k, +)` (Proposition 1.2(ii)). -/
theorem toFun_mul (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x y : k} (hx : ‖x - 1‖ < 1)
    (hy : ‖y - 1‖ < 1) : L.toFun (x * y) = L.toFun x + L.toFun y := by
  simp only [toFun, padicLog_mul hp hpk hx hy, map_add]

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CompleteSpace k] [CharZero k] in
@[simp] theorem toFun_one : L.toFun 1 = 0 := by simp [toFun]

/-- Bicontinuous ring automorphisms preserve the log-shell. -/
theorem ringEquiv_image_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (τ : k ≃+* k)
    (h1 : Continuous τ) (h2 : Continuous τ.symm) : τ '' logShell k p = logShell k p := by
  refine (RingHom.image_logShell_subset hp hpk τ.toRingHom h1).antisymm fun y hy => ?_
  refine ⟨τ.symm y, RingHom.image_logShell_subset hp hpk τ.symm.toRingHom h2 ⟨y, hy, rfl⟩, ?_⟩
  exact τ.apply_symm_apply y

/-- **The holomorphic log-shell of the domain, read in the codomain of the log-link, is the
log-shell of the codomain** (IUT III, Definition 1.1(i): an object associated to the codomain of
any, not necessarily tautological, log-link). -/
theorem image_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    L.φ '' logShell k p = logShell k p :=
  ringEquiv_image_logShell hp hpk L.φ L.cont L.cont_symm

/-- **(a_non)** The log-shell is bounded (compact closure, finite log-volume). -/
theorem logShell_bounded (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Bornology.IsBounded (L.φ '' logShell k p) := by
  rw [L.image_logShell hp hpk]
  exact logShell_isBounded hp hpk

/-- **(b_non)** The log-shell contains the integers of the codomain. -/
theorem closedBall_subset (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    Metric.closedBall (0 : k) 1 ⊆ L.φ '' logShell k p := by
  rw [L.image_logShell hp hpk]
  exact closedBall_subset_logShell hp hpk

/-- **(c_non)** The log-shell contains the image of the units of the domain. -/
theorem toFun_mem_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {u : k} (hu : ‖u - 1‖ < 1) :
    L.toFun u ∈ L.φ '' logShell k p :=
  ⟨padicLog u, padicLog_mem_logShell hp hpk hu, rfl⟩

omit [CompleteSpace k] in
/-- **Kummer non-compatibility** (IUT III, Proposition 1.2(iv)): no ring homomorphism (in
particular no composite of Kummer isomorphisms with the coric identification) agrees with the
log-link on the principal units of the domain. -/
theorem not_ringHom_eq_toFun (κ : k →+* k) : ¬ ∀ u : k, ‖u - 1‖ < 1 → κ u = L.toFun u := by
  intro h
  have := h 1 (by simp)
  rw [map_one, toFun_one] at this
  exact one_ne_zero this

/-- The image of the log-link contains every element of norm `≤ ‖2p‖` of the codomain: units of
the domain become non-units (indeed elements of every small norm) of the codomain. -/
theorem exists_toFun_eq (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k}
    (hy : ‖L.φ.symm y‖ ≤ ‖2 * (p : k)‖) : ∃ u : prinUnits k, L.toFun (pval u) = y := by
  obtain ⟨u, hu⟩ := exists_prinUnit_padicLog_eq hp hpk hy
  exact ⟨u, by rw [toFun, hu, RingEquiv.apply_symm_apply]⟩

end LocalLogLink

/-! ### Unit-induced identifications -/

/-- **A unit-induced identification** (IUT III, Proposition 1.2(vi), (viii); Theorem 1.5(iii),
(iv)): an additive automorphism `ψ` of `k` which is induced, through the logarithm, by an
automorphism `α` of the principal units: `ψ(log u) = log(α u)`. -/
def UnitInduced (ψ : k ≃+ k) : Prop :=
  ∃ α : prinUnits k ≃* prinUnits k, ∀ u : prinUnits k, ψ (padicLog (pval u)) = padicLog (pval (α u))

omit [CompleteSpace k] [CharZero k] in
theorem UnitInduced.symm {ψ : k ≃+ k} (h : UnitInduced ψ) : UnitInduced ψ.symm := by
  obtain ⟨α, hα⟩ := h
  refine ⟨α.symm, fun u => ?_⟩
  have := hα (α.symm u)
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this, AddEquiv.symm_apply_apply]

omit [CompleteSpace k] [CharZero k] in
theorem UnitInduced.trans {ψ χ : k ≃+ k} (h : UnitInduced ψ) (h' : UnitInduced χ) :
    UnitInduced (ψ.trans χ) := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨β, hβ⟩ := h'
  exact ⟨α.trans β, fun u => by simp only [AddEquiv.trans_apply, hα, hβ, MulEquiv.trans_apply]⟩

omit [CompleteSpace k] [CharZero k] in
theorem unitInduced_refl : UnitInduced (AddEquiv.refl k) := ⟨MulEquiv.refl _, fun _ => rfl⟩

omit [CompleteSpace k] in
/-- A unit-induced identification maps the log-shell into the log-shell. -/
theorem image_logShell_subset_of_unitInduced (hp : p.Prime) {ψ : k ≃+ k} (h : UnitInduced ψ) :
    ψ '' logShell k p ⊆ logShell k p := by
  obtain ⟨α, hα⟩ := h
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have h2p : 2 * p ≠ 0 := Nat.mul_ne_zero two_ne_zero hp.ne_zero
  refine ⟨pval (α (prinUnit u hu)), (α (prinUnit u hu)).2, ?_⟩
  have e := map_natCast_inv_mul ψ.toAddMonoidHom h2p (padicLog u)
  simp only [AddEquiv.coe_toAddMonoidHom] at e
  rw [two_mul_natCast, e]
  congr 1
  exact hα (prinUnit u hu)

omit [CompleteSpace k] in
/-- **Unit-induced identifications preserve the log-shell** (the log-shell is constructed from
the unit portion alone). -/
theorem image_logShell_of_unitInduced (hp : p.Prime) {ψ : k ≃+ k} (h : UnitInduced ψ) :
    ψ '' logShell k p = logShell k p := by
  refine (image_logShell_subset_of_unitInduced hp h).antisymm fun y hy => ?_
  exact ⟨ψ.symm y, image_logShell_subset_of_unitInduced hp h.symm ⟨y, hy, rfl⟩,
    ψ.apply_symm_apply y⟩

/-- **`x ↦ −x` is unit-induced**, by the inversion `u ↦ u⁻¹` of the units. -/
theorem unitInduced_neg (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) : UnitInduced (AddEquiv.neg k) :=
  ⟨MulEquiv.inv _, fun u => by
    simp only [AddEquiv.neg_apply, MulEquiv.inv_apply, pval_inv]
    rw [padicLog_inv hp hpk u.2]⟩

/-- The principal units are preserved by bicontinuous ring automorphisms. -/
def prinMap (τ : k ≃+* k) (h1 : Continuous τ) (h2 : Continuous τ.symm) :
    prinUnits k ≃* prinUnits k where
  toFun u := prinUnit (τ (pval u)) (norm_map_sub_one_lt τ.toRingHom h1 u.2)
  invFun u := prinUnit (τ.symm (pval u)) (norm_map_sub_one_lt τ.symm.toRingHom h2 u.2)
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp [prinUnit, pval]
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp [prinUnit, pval]
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    simp [prinUnit, pval]

/-- **Bicontinuous ring automorphisms are unit-induced** (the holomorphic case: they commute
with the logarithm, `map_padicLog`). -/
theorem unitInduced_ringEquiv (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (τ : k ≃+* k)
    (h1 : Continuous τ) (h2 : Continuous τ.symm) : UnitInduced τ.toAddEquiv :=
  ⟨prinMap τ h1 h2, fun u => by
    change τ (padicLog (pval u)) = padicLog (τ (pval u))
    exact map_padicLog hp hpk τ.toRingHom h1 u.2⟩

/-! ### Scalings -/

/-- Multiplication by a unit `q`, as an additive automorphism. -/
def scale (q : kˣ) : k ≃+ k where
  toFun x := (q : k) * x
  invFun x := ((q⁻¹ : kˣ) : k) * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := mul_add _ _ _

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
  [CharZero k] in
@[simp] lemma scale_apply (q : kˣ) (x : k) : scale q x = (q : k) * x := rfl

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
  [CharZero k] in
/-- If `q·I = I`, then every element of `I` is `q^n` times an element of `I`. -/
lemma exists_pow_mul_of_image_eq {q : k} {I : Set k} (h : (fun x => q * x) '' I = I)
    (n : ℕ) {y : k} (hy : y ∈ I) : ∃ z ∈ I, y = q ^ n * z := by
  induction n generalizing y with
  | zero => exact ⟨y, hy, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz, rfl⟩ := ih hy
    rw [← h] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨z', hz', by ring⟩

/-- **Multiplication by an element `q` with `‖q‖ < 1` does not preserve the log-shell** (it
contains `1` and is bounded). -/
theorem scale_image_logShell_ne (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {q : k} (hq : ‖q‖ < 1) :
    (fun x => q * x) '' logShell k p ≠ logShell k p := by
  intro h
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (logShell_isBounded (k := k) hp hpk)
  have h1 : (1 : k) ∈ logShell k p := closedBall_subset_logShell hp hpk (by simp)
  have hM1 : 1 ≤ M := by simpa using hM 1 h1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (M + 1) by positivity) hq
  obtain ⟨z, hz, hz1⟩ := exists_pow_mul_of_image_eq h n h1
  have hnorm : ‖q‖ ^ n * ‖z‖ = 1 := by rw [← norm_pow, ← norm_mul, ← hz1, norm_one]
  have hzM := hM z hz
  have : ‖q‖ ^ n * ‖z‖ < 1 := by
    calc ‖q‖ ^ n * ‖z‖ ≤ 1 / (M + 1) * M :=
          mul_le_mul hn.le hzM (norm_nonneg _) (by positivity)
      _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  linarith

/-- **Multiplication by an element `q` with `‖q‖ < 1` is not unit-induced.** -/
theorem not_unitInduced_scale (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {q : kˣ} (hq : ‖(q : k)‖ < 1) :
    ¬ UnitInduced (scale q) := fun h =>
  scale_image_logShell_ne hp hpk hq (image_logShell_of_unitInduced hp h)

end

end LogLink

end Iut
