/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFKummer
import Iut.Reconstruction.Thm19.CuspPrincipal
import CurvesJacobian.Kummer.ChernDivisor

/-!
# [AbsTopIII] Thm 1.9 (d): removing the "positive multiple"

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) embeds
`K^×_{Z_NF}` into `lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` running over the open subschemes of `Z ×_{k_Z} k′`
for finite extensions `k′` of `k_Z`. Prop 1.8 (i) (`Thm19/NFKummer.lean`,
`isNFKummerTest_iff`) only characterises the classes `η ∈ P_U` of which **some positive multiple**
`η^M` is the Kummer class of a nonconstant NF-rational unit `w`. Over `k` this is the exact
statement; the passage to a finite extension `k′` removes the multiple. Here is the algebra of
that step, at one stage:

* **`exists_toKummerCompletion_eq_of_pow_eq_one`**: the `M`-torsion of the Kummer completion
  `(K^×)^∧ = lim_n K^×/K^{×n}` of any field `K` (`M` invertible in `K`) consists of the classes of
  the `M`-th roots of unity of `K` (compactness: the sets of roots of unity representing the
  levels are finite, nonempty and decreasing);
* `constUnit_mul`, `constUnit_pow`: the constants as units of `U`;
* `exists_constUnit_eq_of_kummerMapZHat_eq`: a unit whose Kummer class comes from `(k^×)^∧`
  lies in `k^×` (all its orders vanish, curves-jacobian/continuous-kummer-theory
  `eq_zero_of_kummerMapZHat_eq_constMapZHat`);
* **`exists_kummerMapZHat_eq_of_pow_eq`**: if `η ∈ P_U` and `η^M = κ_U(w)` (`M > 0`), then
  `w = u^M · b` for a unit `u` of `U` and an element `b ∈ k^×`, and as soon as `b` has an `M`-th
  root `β` in the base field, `η = κ_U(v)` with `v^M = w`. In the colimit of Thm 1.9 (d) this
  happens over the finite extension `k′ = k(b^{1/M})`;
* `exists_kummerMapZHat_eq_of_isNFKummerTest_numberField`: combined with Prop 1.8 (i), for a curve
  over a number field: a class passing the test is a Kummer class `κ_U(v)` of an `M`-th root `v`
  of a nonconstant NF-rational unit once `k` contains `b^{1/M}`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

namespace Iut.Reconstruction.Thm19

/-! ### Torsion of the Kummer completion -/

section Torsion

variable (K : Type*) [Field K]

/-- The level-`n` component of the class of `a ∈ Kˣ` in `(Kˣ)^∧`. -/
lemma toKummerCompletion_apply (a : Kˣ) (i : KummerIndex K) :
    (toKummerCompletion K a : ∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range) i =
      QuotientGroup.mk a := rfl

variable {K}

/-- The transition maps send the class of `a` to the class of `a`. -/
lemma quotTransition_mk {m n : ℕ} (h : m ∣ n) (a : Kˣ) :
    quotTransition K h (QuotientGroup.mk a) = QuotientGroup.mk a := rfl

/-- **The `M`-torsion of `(Kˣ)^∧` is the image of `μ_M(K)`**, for `M` invertible in `K`. -/
theorem exists_toKummerCompletion_eq_of_pow_eq_one {M : ℕ} (hM : (M : K) ≠ 0)
    (d : KummerCompletion K) (hd : d ^ M = 1) :
    ∃ ζ : Kˣ, ζ ^ M = 1 ∧ toKummerCompletion K ζ = d := by
  classical
  have hM0 : M ≠ 0 := fun h => hM (by rw [h, Nat.cast_zero])
  haveI : NeZero M := ⟨hM0⟩
  let R := rootsOfUnity M K
  haveI : Fintype R := Fintype.ofFinite R
  let dd : ∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range := fun i => d.1 i
  have hdd : ∀ (i i' : KummerIndex K) (h : i.n ∣ i'.n), quotTransition K h (dd i') = dd i :=
    fun i i' h => d.2 i i' h
  -- the roots of unity representing the level `i`
  let S : KummerIndex K → Set R := fun i => {ζ | QuotientGroup.mk (ζ : Kˣ) = dd i}
  have hS_anti : ∀ i i' : KummerIndex K, i.n ∣ i'.n → S i' ⊆ S i := by
    intro i i' h ζ hζ
    change QuotientGroup.mk (ζ : Kˣ) = dd i
    rw [← hdd i i' h, ← quotTransition_mk h]
    exact congrArg _ hζ
  have hS_ne : ∀ i, (S i).Nonempty := by
    intro i
    let j : KummerIndex K := ⟨i.n * M, by push_cast; exact mul_ne_zero i.ne_zero hM⟩
    obtain ⟨δ, hδ⟩ := QuotientGroup.mk_surjective (dd j)
    have hpow : (QuotientGroup.mk (δ ^ M) : Kˣ ⧸ (powMonoidHom j.n : Kˣ →* Kˣ).range) = 1 := by
      rw [QuotientGroup.mk_pow, hδ]
      have := congrArg (fun x : KummerCompletion K =>
        (x : ∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range) j) hd
      simpa using this
    obtain ⟨ε, hε⟩ := (QuotientGroup.eq_one_iff _).1 hpow
    rw [powMonoidHom_apply] at hε
    set ζ : Kˣ := δ * (ε ^ i.n)⁻¹
    have hζ : ζ ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, show i.n * M = j.n from rfl, hε, mul_inv_cancel]
    refine ⟨⟨ζ, (mem_rootsOfUnity M ζ).2 hζ⟩, ?_⟩
    change QuotientGroup.mk ζ = dd i
    rw [← hdd i j (dvd_mul_right i.n M), ← hδ, quotTransition_mk, QuotientGroup.eq]
    exact ⟨ε, by simp [ζ, powMonoidHom_apply]⟩
  -- the intersection of the `S i` is nonempty
  obtain ⟨ζ, hζ⟩ : ∃ ζ : R, ∀ i, ζ ∈ S i := by
    by_contra hne
    push Not at hne
    choose f hf using hne
    let I : KummerIndex K := ⟨∏ ζ : R, (f ζ).n, by
      push_cast
      exact Finset.prod_ne_zero_iff.2 fun ζ _ => (f ζ).ne_zero⟩
    obtain ⟨ζ₀, hζ₀⟩ := hS_ne I
    exact hf ζ₀ (hS_anti (f ζ₀) I (Finset.dvd_prod_of_mem _ (Finset.mem_univ ζ₀)) hζ₀)
  refine ⟨ζ, (mem_rootsOfUnity M (ζ : Kˣ)).1 ζ.2, Subtype.ext (funext fun i => ?_)⟩
  exact hζ i

end Torsion

/-! ### One stage of Thm 1.9 (d) -/

section Stage

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
lemma constUnit_mul (a b : kˣ) : constUnit D (a * b) = constUnit D a * constUnit D b :=
  Subtype.ext (Units.ext (map_mul (algebraMap k (F D)) _ _))

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
lemma constUnit_pow (a : kˣ) (M : ℕ) : constUnit D (a ^ M) = constUnit D a ^ M := by
  induction M with
  | zero =>
    simp only [pow_zero]
    exact Subtype.ext (Units.ext (map_one (algebraMap k (F D))))
  | succ M ih => rw [pow_succ, constUnit_mul, ih, pow_succ]

set_option maxHeartbeats 1600000 in
-- the `ord`/valuation conversions unfold slowly
/-- **A unit of `U` whose Kummer class comes from `(k^×)^∧` lies in `k^×`**: its order at every
place vanishes (`eq_zero_of_kummerMapZHat_eq_constMapZHat`), so it is algebraic over `k`, hence
in `k` (`k` algebraically closed in `F`). -/
theorem exists_constUnit_eq_of_kummerMapZHat_eq
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (w : units D) (c : KummerCompletion k) (h : kummerMapZHat D w = constMapZHat D c) :
    ∃ b : kˣ, w = constUnit D b := by
  have hord : ∀ P : Place k (F D), P.ord ((w : (F D)ˣ) : F D) = 0 := by
    intro P
    obtain ⟨W, hW⟩ := CurvesJacobian.exists_valuationSubring_liesOver D P
    have hkW : ∀ c : k, algebraMap k Ω c ∈ W := fun c => by
      rw [IsScalarTower.algebraMap_apply k (F D) Ω]
      exact (hW _).2 (P.algebraMap_mem c)
    obtain ⟨π, hπ1, hπW, hπ⟩ := CurvesJacobian.ChernClass.exists_uniformiser hW
    set m := P.ord ((w : (F D)ˣ) : F D)
    have hv0 : (((w : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) ≠ 0 := Units.ne_zero _
    have hvord : P.ord ((((w : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D)) = 0 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, P.ord_mul (Units.ne_zero _)
        (zpow_ne_zero _ π.ne_zero), P.ord_zpow, hπ1]
      ring
    obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hv0).1 hvord
    refine eq_zero_of_kummerMapZHat_eq_constMapZHat hkW w c h π hπW hπ m ((hW _).2 h1) ?_
    rw [Units.val_inv_eq_inv_val]
    exact (hW _).2 h2
  obtain ⟨b, hb⟩ := hkF _ (Place.isAlgebraic_iff_forall_ord_eq_zero.2 hord)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact (w : (F D)ˣ).ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Subtype.ext (Units.ext hb.symm)⟩

set_option maxHeartbeats 800000 in
-- `ContH1` terms over `Pi D` unify slowly
/-- **[AbsTopIII] Thm 1.9 (d), one stage: the positive multiple disappears once the scalar
`b` has an `M`-th root.** If `η ∈ P_U` and `η^M = κ_U(w)` with `M > 0`, then `w = u^M · b` for a
unit `u` of `U` and `b ∈ k^×`, and for every `β ∈ k^×` with `β^M = b` there is a unit `v` of `U`
with `η = κ_U(v)` and `v^M = w`. (In the colimit over finite extensions `k′` of the base field,
`k′ = k(b^{1/M})` is such a stage.) -/
theorem exists_kummerMapZHat_eq_of_pow_eq (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {η : ContH1 (Pi D) (ZHatOne (F D) Ω)} (hη : η ∈ PU D) {M : ℕ} (hM : 0 < M)
    {w : units D} (hw : η ^ M = kummerMapZHat D w) :
    ∃ (u : units D) (b : kˣ), w = u ^ M * constUnit D b ∧
      ∀ β : kˣ, β ^ M = b → ∃ v : units D, η = kummerMapZHat D v ∧ v ^ M = w := by
  obtain ⟨u, hu⟩ := hη
  have hker : η * (kummerMapZHat D u)⁻¹ ∈ (res D).ker := by
    have hu' : res D (kummerMapZHat D u) = res D η := hu
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hu', mul_inv_cancel]
  obtain ⟨c, hc⟩ := (mem_range_constMapZHat_iff hJ hkF _).2 hker
  have hηc : η = kummerMapZHat D u * constMapZHat D c := by
    rw [hc, mul_comm η, ← mul_assoc, mul_inv_cancel, one_mul]
  have hconst : kummerMapZHat D (w * (u ^ M)⁻¹) = constMapZHat D (c ^ M) := by
    rw [map_mul, map_inv, map_pow, ← hw, hηc, mul_pow, map_pow, mul_inv_eq_iff_eq_mul, mul_comm]
  obtain ⟨b, hb⟩ := exists_constUnit_eq_of_kummerMapZHat_eq hkF _ _ hconst
  have hw' : w = u ^ M * constUnit D b := by
    rw [← hb, mul_comm w, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨u, b, hw', fun β hβ => ?_⟩
  have hcM : c ^ M = toKummerCompletion k b :=
    constMapZHat_injective D hkF (by rw [← hconst, hb, constMapZHat_toKummerCompletion])
  have hd : (c * (toKummerCompletion k β)⁻¹) ^ M = 1 := by
    rw [mul_pow, inv_pow, hcM, ← map_pow, hβ, mul_inv_cancel]
  obtain ⟨ζ, hζ, hζd⟩ := exists_toKummerCompletion_eq_of_pow_eq_one
    (Nat.cast_ne_zero.2 hM.ne') _ hd
  have hc' : c = toKummerCompletion k (β * ζ) := by
    rw [map_mul, hζd, mul_comm c, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨u * constUnit D (β * ζ), ?_, ?_⟩
  · rw [hηc, hc', constMapZHat_toKummerCompletion, map_mul]
  · rw [mul_pow, ← constUnit_pow, mul_pow, hβ, hζ, mul_one, hw']

end Stage

/-! ### The curve form over a number field -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

variable {k hτ}

/-- **[AbsTopIII] Prop 1.8 (i) and Thm 1.9 (d), one stage, over a number field**: if `η ∈ P_U`
passes the test of Prop 1.8 (i), there are `M > 0`, a nonconstant NF-rational unit `w` and a
scalar `b ∈ k^×` such that `η^M = κ_U(w)`, and as soon as `b` has an `M`-th root in `k`, `η`
is itself the Kummer class `κ_U(v)` of an `M`-th root `v` of `w`. -/
theorem exists_kummerMapZHat_eq_of_isNFKummerTest_numberField [NumberField k]
    (N : NFModel (curveGaloisData k hτ)) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ)) (htest : IsNFKummerTest N rfl η) :
    ∃ M : ℕ, 0 < M ∧ ∃ (w : units (curveGaloisData k hτ)) (b : kˣ),
      η ^ M = kummerMapZHat (curveGaloisData k hτ) w ∧
      w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
      N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
      ∀ β : kˣ, β ^ M = b → ∃ v : units (curveGaloisData k hτ),
        η = kummerMapZHat (curveGaloisData k hτ) v ∧ v ^ M = w := by
  obtain ⟨M, hM, w, hw, hwc, hwNF⟩ :=
    (isNFKummerTest_iff_curve_numberField N σ hσ η hη).1 htest
  obtain ⟨u, b, -, hb⟩ := exists_kummerMapZHat_eq_of_pow_eq
    (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ k (jacDivFree_numberField X σ hσ))
    (mem_range_of_isAlgebraic_F k hτ) hη hM hw
  exact ⟨M, hM, w, b, hw, hwc, hwNF, hb⟩

end Curve

end Iut.Reconstruction.Thm19
