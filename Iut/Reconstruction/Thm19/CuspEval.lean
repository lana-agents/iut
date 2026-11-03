/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RestrictCongr
import Iut.Reconstruction.Thm19.NFEval

/-!
# `U_x` at cusps from the decomposition groups (MR9 item 4, step 5)

[AbsTopIII] Thm 1.9 (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2179–2185) feeds the
subgroups `U_x = {f | f(x) = 1}` of the triple of Prop 1.3 into Uchida's algorithm. At a closed
point `x` of `U` they are read off from `s_x^* κ(f) = κ(f(x))` (`mem_U_recTriple_iff`). At a
cusp `x` of `U` there is no section `s_x` through `Π_U` (the inertia does not die), but for
`ord_x f = 0` the restriction of `κ(f)` to the decomposition group `D_x` is inflated from
`κ(f(x)) ∈ H¹(G_{k_x}, Ẑ(1))` (continuous-kummer-theory `decompToPi_kummerMap_eq_one_iff`, which
needs no assumption `t ∈ A`). Here, for a Galois model `D` and a place `A ⊇ k` of `Ω` (a closed
point or a cusp):

* `decompRes`, the Prop-valued def **`DecompTriv D A η`**: at every level `n` the restriction of
  `η ∈ H¹(Π_U, Ẑ(1))` along `D_A → Π_U` (coefficients reduced modulo `𝔪_A`) vanishes;
  `decompTriv_mk_iff` (coboundaries on the image of `D_A`, `map_map_mk_eq_one_iff`);
* **`decompTriv_h1Congr_iff`**: `DecompTriv` is carried along isomorphisms of Galois models which
  map the image of `D_A` onto a conjugate of the image of `D_{A'}`;
* **`decompTriv_kummer`**: `u(x) = 1` implies `DecompTriv (κ(u))` (any place, units at `A`);
* `proj_constMapZHat_congr`, **`exists_kummer_of_decompTriv`**: at a rational point `x` (cusps
  included), if `κ(u) · c` (`c ∈ (k^×)^∧` a class of constants) satisfies `DecompTriv`, then
  `c = κ(a)` for some `a ∈ k^×` and `(u a)(x) = 1`;
* `ratPointOfComap`: a place with the same trace on `F` as a rational point is rational.
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer IsLocalRing groupCohomology

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

section Decomp

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

/-- The level-`n` restriction along `D_A → Π_U`, coefficients reduced modulo `𝔪_A`. -/
def decompRes (n : ℕ) [NeZero n] :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1 (Pi D) (Mu n Ω) →* ContH1 (A.decompositionSubgroup (F D)) (Mu n (ResidueField A)) :=
  letI := Decomposition.muAction (F D) A hk hkres n
  ContH1.map (decompToPi D A) (continuous_decompToPi D A)
    (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
    (reduceMu_decompToPi_smul D A hk hkres n)

/-- **`η` restricts trivially to the decomposition group of `A`**: at every level `n`, the
restriction of the `μ_n`-component of `η` along `D_A → Π_U` vanishes. For a closed point of `U`
this is `η|_x = 0` (`restrictClosed_eq_one_iff`); it makes sense at cusps as well. -/
def DecompTriv (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) : Prop :=
  ∀ i : KummerIndex (F D),
    decompRes D A hk hkres i.n
      (ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i)
        (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) η) = 1

variable [Algebra.IsIntegral k (ResidueField A)]

/-- `DecompTriv` of a cocycle class: at every level the cocycle is a coboundary modulo `n` on the
image of `D_A → Π_U`. -/
theorem decompTriv_mk_iff (c : ContH1.cocycles (Pi D) (ZHatOne (F D) Ω)) :
    DecompTriv D A hk hkres (ContH1.mk c) ↔
      ∀ i : KummerIndex (F D), CobOn (ZHatOne.proj i) (Set.range (decompToPi D A)) c :=
  forall_congr' fun i => by
    letI := Decomposition.muAction (F D) A hk hkres i.n
    exact map_map_mk_eq_one_iff (decompToPi D A) (continuous_decompToPi D A)
      (Decomposition.reduceMu A i.n (NeZero.ne i.n)) continuous_of_discreteTopology
      (reduceMu_decompToPi_smul D A hk hkres i.n) (ZHatOne.proj i) (ZHatOne.continuous_proj _)
      (fun g x => proj_pi_smul _ g x) (reduceMu_bijective A hk hkres i.n)
      (zHatOne_proj_surjective i) c

omit [Algebra.IsIntegral k (ResidueField A)] in
/-- **`u(x) = 1` ⇒ `κ(u)` restricts trivially to `D_A`**, at any place `A ⊇ k` (closed point or
cusp) at which `u` is a unit. -/
theorem decompTriv_kummer (u : units D) (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (h1 : A.valuation ((((u : (F D)ˣ) : F D) : Ω) - 1) < 1) :
    DecompTriv D A hk hkres (kummerMapZHat D u) := by
  intro i
  rw [map_proj_kummerMapZHat]
  exact (decompToPi_kummerMap_eq_one_iff D A hk hkres i.n u hu hu').2
    ⟨1, fun σ => map_one _, by
      rw [one_pow]
      exact ((residue_eq_one_iff_valuation A _ hu).2 h1).symm⟩

end Decomp

/-! ### Along isomorphisms of Galois models -/

section Congr

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [IsGalois (K₀ k' t') Ω'] [CharZero k'] [IsAlgClosed Ω']
  (A' : ValuationSubring Ω') (hk' : ∀ c : k', algebraMap k' Ω' c ∈ A')
  [Algebra k' (ResidueField A')]
  (hkres' : ∀ c : k', residue A' ⟨algebraMap k' Ω' c, hk' c⟩ = algebraMap k' (ResidueField A') c)
  [Algebra.IsIntegral k' (ResidueField A')]

/-- **`DecompTriv` along isomorphisms of Galois models**: let `e : Π_U ≃ₜ* Π_{U'}` and an
`e`-equivariant `χ : Ẑ(1) ≃ₜ* Ẑ(1)'` be given, and let `e` map the image of `D_A → Π_U` onto a
conjugate of the image of `D_{A'} → Π_{U'}` (for cusps: `LiftData.map_decompH_constIso`). Then
`η` restricts trivially to `D_A` iff `h1Congr e χ η` restricts trivially to `D_{A'}`. -/
theorem decompTriv_h1Congr_iff (e : Pi D ≃ₜ* Pi D')
    (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω') (hχ : ∀ p z, χ (p • z) = e p • χ z) (M : Pi D')
    (hdec : (decompToPi D A).range.map e.toMulEquiv.toMonoidHom =
      (decompToPi D' A').range.map (MulAut.conj M).toMonoidHom)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    DecompTriv D A hk hkres η ↔ DecompTriv D' A' hk' hkres' (h1Congr e χ hχ η) := by
  haveI : CharZero (F D) := charZero_of_injective_algebraMap (algebraMap k (F D)).injective
  haveI : CharZero (F D') := charZero_of_injective_algebraMap (algebraMap k' (F D')).injective
  have hset : e.toMulEquiv '' Set.range (decompToPi D A) =
      (MulAut.conj M) '' Set.range (decompToPi D' A') :=
    congrArg (fun H : Subgroup (Pi D') => (H : Set (Pi D'))) hdec
  induction η using ContH1.induction_on with
  | h c =>
  refine (decompTriv_mk_iff D A hk hkres c).trans (Iff.trans ?_
    (decompTriv_mk_iff D' A' hk' hkres' (ContH1.cocyclesMap e.symm.toMulEquiv.toMonoidHom
      e.symm.continuous χ.toMulEquiv.toMonoidHom χ.continuous (h1Congr_comm e χ hχ) c)).symm)
  constructor
  · intro h i'
    exact (cobOn_cocyclesMap_iff e χ hχ _ _ M hset c (kummerIndexOf i'.n i'.n_ne_zero) i'
      rfl).2 (h _)
  · intro h i
    exact (cobOn_cocyclesMap_iff e χ hχ _ _ M hset c i (kummerIndexOf i.n i.n_ne_zero)
      rfl).1 (h _)

end Congr

/-! ### Rational points: classes of constants -/

section Rat

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω]

/-- The `μ_n`-component of a class of constants depends only on its `n`-th component. -/
lemma proj_constMapZHat_congr (i : KummerIndex (F D)) {c c' : KummerCompletion k}
    (h : c.1 (toIndex i) = c'.1 (toIndex i)) :
    ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i) (ZHatOne.continuous_proj _)
        (fun g x => proj_pi_smul _ g x) (constMapZHat D c) =
      ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i) (ZHatOne.continuous_proj _)
        (fun g x => proj_pi_smul _ g x) (constMapZHat D c') := by
  have hproj : ∀ X : ContH1 (Gk k Ω) (ZHatOne k (kbar k Ω)),
      ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i) (ZHatOne.continuous_proj _)
          (fun g x => proj_pi_smul _ g x)
          (ContH1.map (piToGk D) (continuous_piToGk D) (zHatMap (F D))
            (continuous_zHatMap (F D)) (zHatMap_piToGk_smul D (F D)) X) =
        ContH1.map (piToGk D) (continuous_piToGk D) (muMap i.n (kbar k Ω) Ω)
          continuous_of_discreteTopology (muMap_piToGk_smul D i.n)
          (h1Proj k (kbar k Ω) (toIndex i) X) := fun X => by
    induction X using ContH1.induction_on with
    | h c' => rfl
  have h2 : ∀ c₀ : KummerCompletion k, h1Proj k (kbar k Ω) (toIndex i)
      ((kummerZHatEquiv k (kbar k Ω)).symm c₀) =
        kummerEquiv (toIndex (k := k) i).n k (kbar k Ω) (c₀.1 (toIndex i)) := fun c₀ => by
    change ((h1ZHatOneEquiv k (kbar k Ω)) ((h1ZHatOneEquiv k (kbar k Ω)).symm
      (kummerLimitEquiv k (kbar k Ω) c₀))).1 (toIndex i) = _
    rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]
  rw [constMapZHat_apply, constMapZHat_apply, hproj, hproj, h2, h2, h]

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma coe_units_inv (w : units D) :
    ((((w : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) = ((((w : (F D)ˣ)) : F D) : Ω)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma coe_mul_constUnit (w : units D) (b : kˣ) :
    ((((w * constUnit D b : units D) : (F D)ˣ) : F D) : Ω) =
      ((((w : (F D)ˣ)) : F D) : Ω) * algebraMap k Ω (b : k) := by
  change (((((w : (F D)ˣ) : F D) * algebraMap k (F D) (b : k) : F D)) : Ω) = _
  rw [IntermediateField.coe_mul, IsScalarTower.algebraMap_apply k (F D) Ω]
  rfl

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma residue_mul_mem (A : ValuationSubring Ω) {y z : Ω} (hy : y ∈ A) (hz : z ∈ A) :
    residue A ⟨y * z, A.mul_mem _ _ hy hz⟩ = residue A ⟨y, hy⟩ * residue A ⟨z, hz⟩ := by
  rw [← map_mul]
  rfl

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma residue_eq_residue_iff (A : ValuationSubring Ω) {y z : Ω} (hy : y ∈ A) (hz : z ∈ A) :
    residue A ⟨y, hy⟩ = residue A ⟨z, hz⟩ ↔ A.valuation (y - z) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  rfl

set_option maxHeartbeats 800000 in
-- the restrictions along `D_A → Π_U` at level `n` unify slowly
/-- **`DecompTriv` at a rational point for a Kummer class times a class of constants**: if
`κ(u) · c` (`u` a unit at the rational point `x`, a cusp or a closed point; `c ∈ (k^×)^∧`) restricts
trivially to `D_x`, then `c = κ(a)` for some `a ∈ k^×` (namely `a = u(x)⁻¹`) and `(u a)(x) = 1`
(at level `n`: `u(x) c_n` is an `n`-th power in `k_x = k`). -/
theorem exists_kummer_of_decompTriv (x : RatPoint D) (u : units D)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ x.A)
    (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ x.A) (c : KummerCompletion k)
    (h : DecompTriv D x.A x.hk x.hkres (kummerMapZHat D u * constMapZHat D c)) :
    ∃ a : kˣ, kummerMapZHat D u * constMapZHat D c = kummerMapZHat D (u * constUnit D a) ∧
      x.A.valuation (((((u * constUnit D a : units D) : (F D)ˣ) : F D) : Ω) - 1) < 1 := by
  haveI : CharZero (F D) := charZero_of_injective_algebraMap (algebraMap k (F D)).injective
  have hmem : ∀ b : kˣ, ((((u * constUnit D b : units D) : (F D)ˣ) : F D) : Ω) ∈ x.A :=
    fun b => by
      rw [coe_mul_constUnit]
      exact x.A.mul_mem _ _ hu (x.hk _)
  have hmem' : ∀ b : kˣ,
      (((((u * constUnit D b : units D) : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ x.A := fun b => by
    rw [coe_units_inv, coe_mul_constUnit, mul_inv, ← map_inv₀, ← coe_units_inv]
    exact x.A.mul_mem _ _ hu' (x.hk _)
  obtain ⟨a₀, ha₀⟩ := x.hrat _ hu
  have hres1 : residue x.A ⟨_, hu⟩ * residue x.A ⟨_, hu'⟩ = 1 := by
    rw [← residue_mul_mem, ← map_one (residue x.A)]
    congr 1
    apply Subtype.ext
    change _ * _ = (1 : Ω)
    rw [coe_units_inv, mul_inv_cancel₀]
    exact fun h0 => (u : (F D)ˣ).ne_zero (Subtype.ext h0)
  have ha₀0 : a₀ ≠ 0 := fun h0 => by
    rw [ha₀, h0, map_zero, zero_mul] at hres1
    exact zero_ne_one hres1
  obtain ⟨a, ha⟩ : ∃ a : kˣ, (a : k) = a₀⁻¹ := ⟨(Units.mk0 a₀ ha₀0)⁻¹, rfl⟩
  have hres : ∀ b : kˣ, residue x.A ⟨_, hmem b⟩ = algebraMap k (ResidueField x.A) (a₀ * b) :=
    fun b => by
      rw [map_mul, ← ha₀, ← x.hkres, ← residue_mul_mem]
      congr 1
  have hc : c = toKummerCompletion k a := by
    apply Subtype.ext
    funext j
    let i : KummerIndex (F D) := ⟨j.n, Nat.cast_ne_zero.mpr j.n_ne_zero⟩
    obtain ⟨b', hb'⟩ := QuotientGroup.mk_surjective (c.1 j)
    have hcb : c.1 (toIndex i) = (toKummerCompletion k b').1 (toIndex i) := hb'.symm
    have e1 : ContH1.map (MonoidHom.id (Pi D)) continuous_id (ZHatOne.proj i)
        (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x)
        (kummerMapZHat D u * constMapZHat D c) = kummerMap D i.n (u * constUnit D b') := by
      rw [map_mul, map_proj_kummerMapZHat, proj_constMapZHat_congr D i hcb,
        constMapZHat_toKummerCompletion, map_proj_kummerMapZHat, ← map_mul]
    have hi := h i
    rw [e1] at hi
    obtain ⟨e, he, hen⟩ := (decompToPi_kummerMap_eq_one_iff D x.A x.hk x.hkres i.n
      (u * constUnit D b') (hmem b') (hmem' b')).1 hi
    haveI := isGalois_residueField x.A x.hk x.hkres
    obtain ⟨z, hz, hze⟩ := (Decomposition.mem_pointField_iff (F D) x.A x.hk x.hkres e).2 he
    obtain ⟨e₀, he₀⟩ := x.hrat z hz
    have heq : e₀ ^ j.n = a₀ * b' := (algebraMap k (ResidueField x.A)).injective (by
      rw [map_pow, ← he₀]
      exact (congrArg (· ^ j.n) hze).trans (hen.trans (hres b')))
    have he₀0 : e₀ ≠ 0 := fun h0 => by
      rw [h0, zero_pow j.n_ne_zero] at heq
      exact mul_ne_zero ha₀0 b'.ne_zero heq.symm
    rw [← hb']
    change (QuotientGroup.mk b' : kˣ ⧸ (powMonoidHom j.n : kˣ →* kˣ).range) = QuotientGroup.mk a
    rw [QuotientGroup.eq]
    refine ⟨(Units.mk0 e₀ he₀0)⁻¹, Units.ext ?_⟩
    simp only [powMonoidHom_apply, inv_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_mul, Units.val_mk0, ha, heq]
    rw [mul_inv, mul_comm]
  refine ⟨a, ?_, ?_⟩
  · rw [hc, constMapZHat_toKummerCompletion, ← map_mul]
  · rw [← residue_eq_one_iff_valuation x.A _ (hmem a), hres, ha, mul_inv_cancel₀ ha₀0, map_one]

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
lemma valuation_lt_one_iff_of_ne {V : ValuationSubring Ω} {y : Ω} (hy : y ≠ 0) :
    V.valuation y < 1 ↔ y ∈ V ∧ y⁻¹ ∉ V := by
  refine ⟨fun h => ⟨(V.valuation_le_one_iff y).1 h.le, fun hi => ?_⟩,
    fun h => lt_of_le_of_ne ((V.valuation_le_one_iff y).2 h.1) fun heq => h.2 ?_⟩
  · have h1 := (V.valuation_le_one_iff _).2 hi
    rw [map_inv₀] at h1
    have h2 : V.valuation y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h3 := mul_lt_mul_of_pos_right h (zero_lt_iff.2 (inv_ne_zero h2))
    rw [mul_inv_cancel₀ h2, one_mul] at h3
    exact absurd h1 (not_le.2 h3)
  · exact (V.valuation_le_one_iff _).1 (by rw [map_inv₀, heq, inv_one])

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsAlgClosed Ω] in
/-- Two places with the same trace on `F` have the same elements of `F` of value `< 1`. -/
lemma valuation_lt_one_iff_of_comap {V V' : ValuationSubring Ω}
    (hV : ∀ y : F D, (y : Ω) ∈ V ↔ (y : Ω) ∈ V') (y : F D) :
    V.valuation (y : Ω) < 1 ↔ V'.valuation (y : Ω) < 1 := by
  by_cases h0 : y = 0
  · rw [h0, IntermediateField.coe_zero, map_zero, map_zero]
    exact iff_of_true zero_lt_one zero_lt_one
  have h0' : (y : Ω) ≠ 0 := fun h => h0 (Subtype.ext h)
  have hinv : (y : Ω)⁻¹ = ((y⁻¹ : F D) : Ω) := (map_inv₀ (algebraMap (F D) Ω) y).symm
  rw [valuation_lt_one_iff_of_ne h0', valuation_lt_one_iff_of_ne h0', hinv, hV y, hV y⁻¹]

/-- **A place with the same trace on `F` as a rational point is a rational point.** -/
def ratPointOfComap (x : RatPoint D) (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hA : ∀ y : F D, (y : Ω) ∈ A ↔ (y : Ω) ∈ x.A) : RatPoint D where
  A := A
  hk := hk
  isIntegral := hint
  hrat a ha := by
    letI := resAlg A hk
    obtain ⟨c, hc⟩ := x.hrat a ((hA a).1 ha)
    refine ⟨c, ?_⟩
    have hz : ((a - algebraMap k (F D) c : F D) : Ω) = (a : Ω) - algebraMap k Ω c := by
      change algebraMap (F D) Ω (a - algebraMap k (F D) c) = _
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
      rfl
    have h1 : x.A.valuation ((a : Ω) - algebraMap k Ω c) < 1 :=
      (residue_eq_residue_iff x.A ((hA a).1 ha) (x.hk c)).1 (hc.trans (x.hkres c).symm)
    rw [← hz] at h1
    have h2 := (valuation_lt_one_iff_of_comap D hA _).2 h1
    rw [hz] at h2
    exact (residue_eq_residue_iff A ha (hk c)).2 h2

@[simp] lemma ratPointOfComap_A (x : RatPoint D) (A : ValuationSubring Ω)
    (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (hA : ∀ y : F D, (y : Ω) ∈ A ↔ (y : Ω) ∈ x.A) : (ratPointOfComap D x A hk hint hA).A = A := rfl

end Rat

end Iut.Reconstruction.Thm19
