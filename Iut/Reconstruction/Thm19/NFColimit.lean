/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFStage
import CurvesJacobian.LocAn.ThmCConstExt
import CurvesJacobian.Kummer.CompletionMap

/-!
# [AbsTopIII] Thm 1.9 (d): the colimit over finite extensions `k′`

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) embeds
`K^×_{Z_NF}` into `lim→_V H¹(Π_V, μ_Ẑ(Π_U))`, `V` running over the open subschemes of
`Z ×_{k_Z} k′` for finite extensions `k′` of `k_Z`. Over `k` itself, Prop 1.8 (i) only
characterises the classes of which some positive multiple is a Kummer class
(`Thm19/NFStage.lean`). Here the multiple is removed in the colimit over `k′`:

* `zHatRes`: `Ẑ(1)_K → Ẑ(1)_L` for fields of characteristic `0` and an embedding `Ω_K → Ω_L`
  (the identity at every level `n`), compatible with `galRestrict`;
* **`kummerZHatEquiv_symm_completionMap`**: restriction `H¹(G_K, Ẑ(1)) → H¹(G_L, Ẑ(1))` is the
  map `(K^×)^∧ → (L^×)^∧` (`completionMap`) under the Kummer isomorphisms, for any extension
  `L / K` of fields of characteristic `0`; in particular `res(κ_K(a)) = κ_L(a)`
  (`kummerZHat_restrict`);
* `resKH1 K D : H¹(Π_U, Ẑ(1)) → H¹(Π_{U_K}, Ẑ(1))`, the pull-back along curves-jacobian's
  `piRes K D : Π_{U_K} → Π_U` for the base change `U_K` of `U` to an algebraic extension
  `k ⊆ K ⊆ Ω` (`constExt K D`);
* **`resKH1_kummerMapZHat`**: `resKH1 (κ_U(u)) = κ_{U_K}(u)`;
* **`resKH1_constMapZHat`**: `resKH1 (c) = c|_{G_K}` for `c ∈ (k^×)^∧` (classes from `G_k`);
* **`exists_resKH1_eq_kummerMapZHat`**: if `η ∈ P_U` and `η^M = κ_U(w)` (`M > 0`), then
  `w = u^M b` with `b ∈ k^×`, and over every algebraic extension `K` in which `b` has an `M`-th
  root, `η|_{Π_{U_K}} = κ_{U_K}(v)` with `v^M = w`. No Kummer-faithfulness over `K` is used;
* **`exists_finite_resKH1_eq_kummerMapZHat`**: such a `K` exists and is finite over `k`
  (`K = k(b^{1/M})`): in the colimit over the finite extensions `k′` the class `η` is a Kummer
  class;
* `exists_finite_resKH1_eq_kummerMapZHat_of_isNFKummerTest_numberField`: the curve form over a
  number field, combined with Prop 1.8 (i): a class passing the test becomes, over a finite
  extension `k′`, the Kummer class of an `M`-th root of a nonconstant NF-rational unit.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer
open IntermediateField.algebraAdjoinAdjoin

universe u

namespace Iut.Reconstruction.Thm19

/-! ### Restriction of `Ẑ(1)`-Kummer classes along a field extension -/

section Generic

variable (K L ΩK ΩL : Type*) [Field K] [Field L] [Field ΩK] [Field ΩL] [CharZero K] [CharZero L]
  [Algebra ΩK ΩL]

lemma muMap_transition' {m n : ℕ} (h : m ∣ n) (ζ : Mu n ΩK) :
    muMap m ΩK ΩL (Mu.transition h ζ) = Mu.transition h (muMap n ΩK ΩL ζ) := by
  apply Mu.ext
  apply Units.ext
  simp

/-- `Ẑ(1)_K → Ẑ(1)_L` along `Ω_K → Ω_L` (characteristic `0`: the levels of both are all
`n ≥ 1`). -/
noncomputable def zHatRes : ZHatOne K ΩK →* ZHatOne L ΩL where
  toFun x := ⟨fun i => muMap i.n ΩK ΩL ((x : ∀ j, Mu j.n ΩK) (reindex (k := K) i)),
    fun i j h => by
      refine (muMap_transition' ΩK ΩL (m := i.n) (n := j.n) h _).symm.trans ?_
      exact congrArg (muMap i.n ΩK ΩL)
        (x.2 (reindex (k := K) i) (reindex (k := K) j) h)⟩
  map_one' := Subtype.ext (funext fun i => map_one (muMap i.n ΩK ΩL))
  map_mul' a b := by
    apply Subtype.ext
    funext i
    exact map_mul (muMap i.n ΩK ΩL) _ _

omit [CharZero L] in
lemma zHatRes_apply (x : ZHatOne K ΩK) (i : KummerIndex L) :
    ((zHatRes K L ΩK ΩL x : ZHatOne L ΩL) : ∀ i, Mu i.n ΩL) i =
      muMap i.n ΩK ΩL ((x : ∀ j, Mu j.n ΩK) (reindex (k := K) i)) := rfl

omit [CharZero L] in
lemma continuous_zHatRes : Continuous (zHatRes K L ΩK ΩL) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact continuous_of_discreteTopology.comp
    ((continuous_apply (reindex (k := K) i)).comp continuous_subtype_val)

variable [Algebra K L] [Algebra K ΩK] [Algebra L ΩL] [Algebra K ΩL] [IsScalarTower K L ΩL]
  [IsScalarTower K ΩK ΩL] [Normal K ΩK]

omit [CharZero L] in
lemma zHatRes_galRestrict_smul (σ : Gal(ΩL/L)) (x : ZHatOne K ΩK) :
    zHatRes K L ΩK ΩL (galRestrict K L ΩK ΩL σ • x) = σ • zHatRes K L ΩK ΩL x := by
  apply Subtype.ext
  funext i
  exact muMap_galRestrict_smul i.n σ _

variable [Algebra.IsIntegral L ΩL]

/-- Restriction `H¹(G_K, Ẑ(1)) → H¹(G_L, Ẑ(1))`. -/
noncomputable abbrev restrictZHat :
    ContH1 Gal(ΩK/K) (ZHatOne K ΩK) →* ContH1 Gal(ΩL/L) (ZHatOne L ΩL) :=
  ContH1.map (galRestrict K L ΩK ΩL) (continuous_galRestrict K L ΩK ΩL) (zHatRes K L ΩK ΩL)
    (continuous_zHatRes K L ΩK ΩL) (zHatRes_galRestrict_smul K L ΩK ΩL)

variable {K L ΩK ΩL}

omit [CharZero L] in
lemma h1Proj_restrictZHat (j : KummerIndex L) (y : ContH1 Gal(ΩK/K) (ZHatOne K ΩK)) :
    h1Proj L ΩL j (restrictZHat K L ΩK ΩL y) =
      restriction K L ΩK ΩL j.n (h1Proj K ΩK (reindex (k := K) j) y) := by
  induction y using ContH1.induction_on with
  | h c => rfl

variable [IsGalois K ΩK] [IsSepClosed ΩK]

omit [CharZero K] [Algebra ΩK ΩL] [Algebra K L] [Algebra K ΩL] [IsScalarTower K L ΩL]
  [IsScalarTower K ΩK ΩL] [Normal K ΩK] [Algebra.IsIntegral L ΩL] in
lemma h1Proj_kummerZHatEquiv_symm (j : KummerIndex K) (c : KummerCompletion K) :
    h1Proj K ΩK j ((kummerZHatEquiv K ΩK).symm c) = kummerEquiv j.n K ΩK (c.1 j) := by
  change ((h1ZHatOneEquiv K ΩK) ((h1ZHatOneEquiv K ΩK).symm
    (kummerLimitEquiv K ΩK c))).1 j = _
  rw [MulEquiv.apply_symm_apply, kummerLimitEquiv_apply]

variable [IsGalois L ΩL] [IsSepClosed ΩL]

omit [CharZero L] in
/-- **Restriction of `Ẑ(1)`-Kummer classes is `(K^×)^∧ → (L^×)^∧`.** -/
theorem kummerZHatEquiv_symm_completionMap (c : KummerCompletion K) :
    (kummerZHatEquiv L ΩL).symm (completionMap (algebraMap K L) c) =
      restrictZHat K L ΩK ΩL ((kummerZHatEquiv K ΩK).symm c) := by
  refine h1ToLimit_injective L ΩL (Subtype.ext (funext fun j => ?_))
  haveI : NeZero (j.n : K) := ⟨(reindex (k := K) j).ne_zero⟩
  change h1Proj L ΩL j _ = h1Proj L ΩL j _
  rw [h1Proj_restrictZHat, h1Proj_kummerZHatEquiv_symm, h1Proj_kummerZHatEquiv_symm,
    completionMap_apply]
  exact (restriction_kummerEquiv (K := K) (L := L) (ΩK := ΩK) (ΩL := ΩL) j.n
    (c.1 (reindex (k := K) j))).symm

omit [CharZero L] in
/-- `res(κ_K(a)) = κ_L(a)` for `Ẑ(1)`-Kummer classes. -/
theorem kummerZHat_restrict (a : Kˣ) :
    kummerZHat L ΩL (Units.map (algebraMap K L : K →* L) a) =
      restrictZHat K L ΩK ΩL (kummerZHat K ΩK a) := by
  change (kummerZHatEquiv L ΩL).symm (toKummerCompletion L _) =
    restrictZHat K L ΩK ΩL ((kummerZHatEquiv K ΩK).symm (toKummerCompletion K a))
  rw [← kummerZHatEquiv_symm_completionMap, completionMap_toKummerCompletion]

end Generic

/-! ### Restriction to the base change `U_K` -/

section ConstExt

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (K : IntermediateField k Ω)
  [Algebra.IsAlgebraic k K] (D : Pi1.Orbifold.GaloisData k t) [CharZero k]
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- The inclusion `F ⊆ F K` of function fields. -/
noncomputable def fRes : F D →+* F (constExt K D) where
  toFun x := ⟨x, le_F_constExt D x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `F K` as an `F`-algebra (local instance). -/
@[reducible] noncomputable def algebraFRes : Algebra (F D) (F (constExt K D)) :=
  (fRes K D).toAlgebra

attribute [local instance] algebraFRes

instance isScalarTower_fRes : IsScalarTower (F D) (F (constExt K D)) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [CharZero k] [IsAlgClosed Ω] in
lemma algebraMap_fRes (x : F D) :
    algebraMap (F D) (F (constExt K D)) x = ⟨x, le_F_constExt D x.2⟩ := rfl

omit [CharZero k] [IsAlgClosed Ω] in
-- `Subtype.coe_mk` instead of `rfl`: the kernel would compare the predicates of `F K` and `F`
@[simp]
lemma coe_algebraMap_fRes (x : F D) :
    ((algebraMap (F D) (F (constExt K D)) x : F (constExt K D)) : Ω) = x := by
  rw [algebraMap_fRes, Subtype.coe_mk]

/-- The coefficients `Ẑ(1)_F → Ẑ(1)_{F K}` (the identity at every level). -/
noncomputable abbrev zK : ZHatOne (F D) Ω →* ZHatOne (F (constExt K D)) Ω :=
  zHatRes (F D) (F (constExt K D)) Ω Ω

omit [IsAlgClosed Ω] in
lemma zK_hRes_smul (σ : (constExt K D).H) (x : ZHatOne (F D) Ω) :
    zK K D (hRes K D σ • x) = σ • zK K D x := by
  apply Subtype.ext
  funext i
  change muMap i.n Ω Ω ((hRes K D σ : Ω ≃ₐ[K₀ k t] Ω) •
      (x : ∀ j, Mu j.n Ω) (reindex (k := F D) i)) =
    (σ : Ω ≃ₐ[K₀ K t] Ω) • muMap i.n Ω Ω ((x : ∀ j, Mu j.n Ω) (reindex (k := F D) i))
  apply Mu.ext
  apply Units.ext
  simp [AlgEquiv.smul_units_def]
  rfl

omit [IsAlgClosed Ω] in
lemma zK_piRes_smul (p : Pi (constExt K D)) (x : ZHatOne (F D) Ω) :
    zK K D (piRes K D p • x) = p • zK K D x := by
  induction p using QuotientGroup.induction_on with
  | H σ => exact zK_hRes_smul K D σ x

/-- **Restriction `H¹(Π_U, Ẑ(1)) → H¹(Π_{U_K}, Ẑ(1))`** along `piRes K D : Π_{U_K} → Π_U`. -/
noncomputable def resKH1 :
    ContH1 (Pi D) (ZHatOne (F D) Ω) →* ContH1 (Pi (constExt K D)) (ZHatOne (F (constExt K D)) Ω) :=
  ContH1.map (piRes K D) (continuous_piRes D) (zK K D)
    (continuous_zHatRes (F D) (F (constExt K D)) Ω Ω) (zK_piRes_smul K D)

variable {K D}

omit [CharZero k] [IsAlgClosed Ω] in
lemma isIntegral_A₀_constExt {x : F D} (hx : IsIntegral (A₀ k t) x) :
    IsIntegral (A₀ K t) (algebraMap (F D) (F (constExt K D)) x) := by
  haveI : IsScalarTower (A₀ k t) (F D) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A₀ K t) (F (constExt K D)) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (A₀ k t) (x : Ω) := hx.map (IsScalarTower.toAlgHom (A₀ k t) (F D) Ω)
  have h2 : IsIntegral (A₀ K t) (x : Ω) := isIntegral_A₀_of t h1
  rw [← coe_algebraMap_fRes K D x] at h2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (A₀ K t) (F (constExt K D)) Ω)
    (algebraMap (F (constExt K D)) Ω).injective).1 h2

variable (K D) in
/-- **Units of `U` are units of `U_K`.** -/
noncomputable def unitsRes : units D →* units (constExt K D) where
  toFun u := ⟨Units.map (algebraMap (F D) (F (constExt K D)) : F D →* F (constExt K D)) u,
    isIntegral_A₀_constExt u.2.1, by
      rw [← map_inv]
      exact isIntegral_A₀_constExt u.2.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

omit [CharZero k] [IsAlgClosed Ω] in
lemma val_unitsRes (u : units D) :
    ((unitsRes K D u : units (constExt K D)) : (F (constExt K D))ˣ) =
      Units.map (algebraMap (F D) (F (constExt K D)) : F D →* F (constExt K D)) (u : (F D)ˣ) :=
  rfl

omit [CharZero k] [IsAlgClosed Ω] in
@[simp]
lemma coe_unitsRes (u : units D) :
    ((((unitsRes K D u : units (constExt K D)) : (F (constExt K D))ˣ) : F (constExt K D)) : Ω) =
      (((u : (F D)ˣ) : F D) : Ω) := by
  change ((algebraMap (F D) (F (constExt K D)) ((u : (F D)ˣ) : F D) : F (constExt K D)) : Ω) = _
  exact coe_algebraMap_fRes K D _

omit [CharZero k] [IsAlgClosed Ω] in
lemma unitsRes_constUnit (b : kˣ) :
    unitsRes K D (constUnit D b) =
      constUnit (constExt K D) (Units.map (algebraMap k K : k →* K) b) := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  change ((algebraMap (F D) (F (constExt K D)) (algebraMap k (F D) b) : F (constExt K D)) : Ω) =
    ((algebraMap K (F (constExt K D)) (algebraMap k K b) : F (constExt K D)) : Ω)
  rw [coe_algebraMap_fRes]
  have h1 : ((algebraMap k (F D) b : F D) : Ω) = algebraMap k Ω b := rfl
  have h2 : ((algebraMap K (F (constExt K D)) (algebraMap k K b) : F (constExt K D)) : Ω) =
    algebraMap k Ω b := rfl
  exact h1.trans h2.symm

omit [CharZero k] [IsAlgClosed Ω] in
lemma toGalF_hRes (σ : (constExt K D).H) :
    toGalF D (hRes K D σ) =
      galRestrict (F D) (F (constExt K D)) Ω Ω (toGalF (constExt K D) σ) := by
  ext x
  have := algebraMap_galRestrict_apply (K := F D) (L := F (constExt K D)) (ΩK := Ω) (ΩL := Ω)
    (toGalF (constExt K D) σ) x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [this]
  rfl

variable (K D) in
/-- Restriction `H¹(H, Ẑ(1)) → H¹(H_K, Ẑ(1))` along `hRes K D`. -/
noncomputable def resHH1 :
    ContH1 D.H (ZHatOne (F D) Ω) →* ContH1 (constExt K D).H (ZHatOne (F (constExt K D)) Ω) :=
  ContH1.map (hRes K D) (continuous_hRes D) (zK K D)
    (continuous_zHatRes (F D) (F (constExt K D)) Ω Ω) (zK_hRes_smul K D)

omit [IsAlgClosed Ω] in
lemma inflZHat_resKH1 (x : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    inflZHat (constExt K D) (F (constExt K D)) (resKH1 K D x) =
      resHH1 K D (inflZHat D (F D) x) := by
  induction x using ContH1.induction_on with
  | h c => rfl

end ConstExt

section A
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {K : IntermediateField k Ω}
  [Algebra.IsAlgebraic k K] {D : Pi1.Orbifold.GaloisData k t} [CharZero k]
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] algebraFRes

omit [IsAlgClosed Ω] in
lemma resHH1_resZHat (X : ContH1 (Ω ≃ₐ[F D] Ω) (ZHatOne (F D) Ω)) :
    resHH1 K D (resZHat D (F D) X) =
      resZHat (constExt K D) (F (constExt K D)) (restrictZHat (F D) (F (constExt K D)) Ω Ω X) := by
  induction X using ContH1.induction_on with
  | h c =>
    simp only [resHH1, resZHat, Curve.res, restrictZHat, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply, toGalF_hRes, MonoidHom.id_apply]

set_option maxHeartbeats 1600000 in
-- the action instances of `inflation_injective` and of `inflZHat` are unified slowly
/-- **The restriction of `κ_U(u)` to `Π_{U_K}` is `κ_{U_K}(u)`.** -/
theorem resKH1_kummerMapZHat (u : units D) :
    resKH1 K D (kummerMapZHat D u) = kummerMapZHat (constExt K D) (unitsRes K D u) := by
  apply ContH1.inflation_injective (N := GaloisPi1.kernel (constExt K D).H (constExt K D).S)
    (fun _ _ => rfl)
  rw [inflation_kummerMapZHat, inflZHat_resKH1, inflation_kummerMapZHat]
  simp only [val_unitsRes, kummerZHat_restrict (ΩK := Ω) (ΩL := Ω)]
  exact resHH1_resZHat _

end A

/-! ### Constants: `k̄ ⊆ K̄` -/

section Constants

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {K : IntermediateField k Ω}
  [Algebra.IsAlgebraic k K] {D : Pi1.Orbifold.GaloisData k t} [CharZero k]
  [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] algebraFRes

variable (K) in
/-- The inclusion `k̄ ⊆ K̄` of algebraic closures in `Ω`. -/
noncomputable def kbarRes : kbar k Ω →+* kbar K Ω where
  toFun y := ⟨y, mem_kbarK y⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (K) in
/-- `K̄` as a `k̄`-algebra (local instance). -/
@[reducible] noncomputable def algebraKbarRes : Algebra (kbar k Ω) (kbar K Ω) :=
  (kbarRes K).toAlgebra

attribute [local instance] algebraKbarRes

omit [Algebra.IsAlgebraic k K] [CharZero k] [IsAlgClosed Ω] in
lemma algebraMap_kbarRes (y : kbar k Ω) :
    algebraMap (kbar k Ω) (kbar K Ω) y = ⟨y, mem_kbarK y⟩ := rfl

omit [Algebra.IsAlgebraic k K] [CharZero k] [IsAlgClosed Ω] in
lemma coe_algebraMap_kbarRes (y : kbar k Ω) :
    algebraMap (kbar K Ω) Ω (algebraMap (kbar k Ω) (kbar K Ω) y) = algebraMap (kbar k Ω) Ω y := by
  change ((⟨(y : Ω), mem_kbarK y⟩ : kbar K Ω) : Ω) = (y : Ω)
  exact Subtype.coe_mk _ _

omit [Algebra.IsAlgebraic k K] [CharZero k] [IsAlgClosed Ω] in
instance isScalarTower_kbarRes : IsScalarTower k (kbar k Ω) (kbar K Ω) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    apply (algebraMap (kbar K Ω) Ω).injective
    rw [coe_algebraMap_kbarRes]
    have h1 : algebraMap (kbar K Ω) Ω (algebraMap k (kbar K Ω) c) = algebraMap k Ω c := rfl
    have h2 : algebraMap (kbar k Ω) Ω (algebraMap k (kbar k Ω) c) = algebraMap k Ω c := rfl
    rw [h1, h2]

omit [Algebra.IsAlgebraic k K] in
lemma coe_galRestrict_kbar (g : Gk K Ω) (y : kbar k Ω) :
    algebraMap (kbar k Ω) Ω (galRestrict k K (kbar k Ω) (kbar K Ω) g y) =
      algebraMap (kbar K Ω) Ω (g (algebraMap (kbar k Ω) (kbar K Ω) y)) := by
  rw [← coe_algebraMap_kbarRes (K := K), KummerTheory.algebraMap_galRestrict_apply]

/-- `Π_{U_K} → Π_U → G_k` is `Π_{U_K} → G_K → G_k`. -/
lemma piToGk_piRes (p : Pi (constExt K D)) :
    piToGk D (piRes K D p) =
      galRestrict k K (kbar k Ω) (kbar K Ω) (piToGk (constExt K D) p) := by
  induction p using QuotientGroup.induction_on with
  | H σ =>
    ext y
    change algebraMap (kbar k Ω) Ω (hToGk D (hRes K D σ) y) = algebraMap (kbar k Ω) Ω
      (galRestrict k K (kbar k Ω) (kbar K Ω) (hToGk (constExt K D) σ) y)
    rw [algebraMap_hToGk_apply, coe_hRes, resK_apply, coe_galRestrict_kbar,
      algebraMap_hToGk_apply]
    exact congrArg _ (coe_algebraMap_kbarRes (K := K) y).symm

omit [IsAlgClosed Ω] in
/-- The coefficient maps `Ẑ(1)_{k̄} → Ẑ(1)_F → Ẑ(1)_{F K}` and `Ẑ(1)_{k̄} → Ẑ(1)_{K̄} → Ẑ(1)_{F K}`
agree. -/
lemma zK_zHatMap (x : ZHatOne k (kbar k Ω)) :
    zK K D (zHatMap (F D) x) =
      zHatMap (F (constExt K D)) (zHatRes k K (kbar k Ω) (kbar K Ω) x) := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  change algebraMap Ω Ω (algebraMap (kbar k Ω) Ω ((Mu.val ((x : ∀ j, Mu j.n (kbar k Ω))
      (toIndex (k := k) (reindex (k := F D) i))) : (kbar k Ω)ˣ) : kbar k Ω)) =
    algebraMap (kbar K Ω) Ω (algebraMap (kbar k Ω) (kbar K Ω) ((Mu.val ((x : ∀ j, Mu j.n (kbar k Ω))
      (toIndex (k := k) (reindex (k := F D) i))) : (kbar k Ω)ˣ) : kbar k Ω))
  rw [coe_algebraMap_kbarRes]
  rfl

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over `constExt K D` unify slowly
/-- **The restriction of a class from `G_k` to `Π_{U_K}` is its restriction to `G_K`**:
`resKH1 (c) = c|_{G_K}` for `c ∈ (k^×)^∧`. -/
theorem resKH1_constMapZHat (c : KummerCompletion k) :
    resKH1 K D (constMapZHat D c) =
      constMapZHat (constExt K D) (completionMap (algebraMap k K) c) := by
  rw [constMapZHat_apply, constMapZHat_apply,
    kummerZHatEquiv_symm_completionMap (ΩK := kbar k Ω) (ΩL := kbar K Ω)]
  generalize (kummerZHatEquiv k (kbar k Ω)).symm c = X
  induction X using ContH1.induction_on with
  | h c' =>
    simp only [resKH1, restrictZHat, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext p
    simp only [ContH1.cocyclesMap_apply, piToGk_piRes, zK_zHatMap]

end Constants

/-! ### Thm 1.9 (d) in the colimit over `k′` -/

section Colimit

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

set_option maxHeartbeats 800000 in
-- `ContH1` terms over `Pi D` unify slowly
/-- `η ∈ P_U` with `η^M = κ_U(w)` is `κ_U(u) · c` with `c ∈ (k^×)^∧`, `c^M = b ∈ k^×` and
`w = u^M b`. -/
theorem exists_eq_kummerMapZHat_mul_constMapZHat (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {η : ContH1 (Pi D) (ZHatOne (F D) Ω)} (hη : η ∈ PU D) {M : ℕ}
    {w : units D} (hw : η ^ M = kummerMapZHat D w) :
    ∃ (u : units D) (c : KummerCompletion k) (b : kˣ),
      η = kummerMapZHat D u * constMapZHat D c ∧ c ^ M = toKummerCompletion k b ∧
        w = u ^ M * constUnit D b := by
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
  refine ⟨u, c, b, hηc, ?_, ?_⟩
  · exact constMapZHat_injective D hkF (by rw [← hconst, hb, constMapZHat_toKummerCompletion])
  · rw [← hb, mul_comm w, ← mul_assoc, mul_inv_cancel, one_mul]

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over `constExt K D` unify slowly
/-- **[AbsTopIII] Thm 1.9 (d): over an extension of the base field the positive multiple
disappears.** If `η ∈ P_U` and `η^M = κ_U(w)` with `M > 0`, then `w = u^M · b` for a unit `u` of
`U` and `b ∈ k^×`, and for every algebraic extension `k ⊆ K ⊆ Ω` and every `β ∈ K^×` with
`β^M = b`, the restriction of `η` to `Π_{U_K}` is the Kummer class `κ_{U_K}(v)` of a unit `v` of
`U_K` with `v^M = w`. (No Kummer-faithfulness over `K` is needed.) -/
theorem exists_resKH1_eq_kummerMapZHat (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {η : ContH1 (Pi D) (ZHatOne (F D) Ω)} (hη : η ∈ PU D) {M : ℕ} (hM : 0 < M)
    {w : units D} (hw : η ^ M = kummerMapZHat D w) :
    ∃ (u : units D) (b : kˣ), w = u ^ M * constUnit D b ∧
      ∀ (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] (β : Kˣ),
        β ^ M = Units.map (algebraMap k K : k →* K) b →
        ∃ v : units (constExt K D), resKH1 K D η = kummerMapZHat (constExt K D) v ∧
          v ^ M = unitsRes K D w := by
  obtain ⟨u, c, b, hηc, hcM, hw'⟩ := exists_eq_kummerMapZHat_mul_constMapZHat hJ hkF hη hw
  refine ⟨u, b, hw', fun K _ β hβ => ?_⟩
  have hres : resKH1 K D η = kummerMapZHat (constExt K D) (unitsRes K D u) *
      constMapZHat (constExt K D) (completionMap (algebraMap k K) c) := by
    rw [hηc, map_mul, resKH1_kummerMapZHat, resKH1_constMapZHat]
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hdM : (completionMap (algebraMap k K) c * (toKummerCompletion K β)⁻¹) ^ M = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hcM, completionMap_toKummerCompletion, ← map_pow, hβ,
      mul_inv_cancel]
  obtain ⟨ζ, hζ, hζd⟩ := exists_toKummerCompletion_eq_of_pow_eq_one
    (Nat.cast_ne_zero.2 hM.ne' : (M : K) ≠ 0) _ hdM
  have hd : completionMap (algebraMap k K) c = toKummerCompletion K (β * ζ) := by
    rw [map_mul, hζd, mul_comm (completionMap (algebraMap k K) c), ← mul_assoc, mul_inv_cancel,
      one_mul]
  refine ⟨unitsRes K D u * constUnit (constExt K D) (β * ζ), ?_, ?_⟩
  · rw [hres, hd, constMapZHat_toKummerCompletion, map_mul]
  · rw [mul_pow, ← constUnit_pow, mul_pow, hβ, hζ, mul_one, hw', map_mul, map_pow,
      unitsRes_constUnit]

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over `constExt K D` unify slowly
/-- **[AbsTopIII] Thm 1.9 (d), the colimit over finite `k′`**: if `η ∈ P_U` and
`η^M = κ_U(w)` with `M > 0`, there is a finite extension `k ⊆ k′ ⊆ Ω` (namely `k(b^{1/M})`)
over which `η` becomes the Kummer class `κ_{U_{k′}}(v)` of an `M`-th root `v` of `w`. -/
theorem exists_finite_resKH1_eq_kummerMapZHat (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {η : ContH1 (Pi D) (ZHatOne (F D) Ω)} (hη : η ∈ PU D) {M : ℕ} (hM : 0 < M)
    {w : units D} (hw : η ^ M = kummerMapZHat D w) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K) (v : units (constExt K D)),
      resKH1 K D η = kummerMapZHat (constExt K D) v ∧ v ^ M = unitsRes K D w := by
  obtain ⟨u, b, -, hb⟩ := exists_resKH1_eq_kummerMapZHat hJ hkF hη hM hw
  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω b) hM
  have hint : IsIntegral k β₀ :=
    IsIntegral.of_pow hM (hβ₀ ▸ isIntegral_algebraMap)
  haveI hfin : FiniteDimensional k (IntermediateField.adjoin k {β₀}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hβ0 : β₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hβ₀
    exact b.ne_zero ((algebraMap k Ω).injective (by rw [← hβ₀, map_zero]))
  let β : (IntermediateField.adjoin k {β₀})ˣ :=
    Units.mk0 ⟨β₀, IntermediateField.mem_adjoin_simple_self k β₀⟩
    (fun h => hβ0 (congrArg Subtype.val h))
  have hβ : β ^ M = Units.map (algebraMap k (IntermediateField.adjoin k {β₀}) :
      k →* IntermediateField.adjoin k {β₀}) b := by
    apply Units.ext
    apply Subtype.ext
    change β₀ ^ M = algebraMap k Ω b
    exact hβ₀
  obtain ⟨v, hv, hvM⟩ := hb (IntermediateField.adjoin k {β₀}) β hβ
  exact ⟨(IntermediateField.adjoin k {β₀}), hfin, v, hv, hvM⟩

end Colimit

/-! ### The curve form over a number field -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian CurvesJacobian.Cusp

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over `constExt K D` unify slowly
/-- **[AbsTopIII] Prop 1.8 (i) and Thm 1.9 (d) over a number field**: if `η ∈ P_U` passes the
test of Prop 1.8 (i), there are `M > 0` and a nonconstant NF-rational unit `w` with
`η^M = κ_U(w)`, and over a finite extension `k′` of `k` the restriction of `η` to `Π_{U_{k′}}`
is the Kummer class of an `M`-th root of `w`. -/
theorem exists_finite_resKH1_eq_kummerMapZHat_of_isNFKummerTest_numberField [NumberField k]
    (N : NFModel (curveGaloisData k hτ)) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ)) (htest : IsNFKummerTest N rfl η) :
    ∃ M : ℕ, 0 < M ∧ ∃ w : units (curveGaloisData k hτ),
      η ^ M = kummerMapZHat (curveGaloisData k hτ) w ∧
      w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
      N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
      ∃ (K : IntermediateField k (FFClosure X)) (_ : FiniteDimensional k K)
        (v : units (constExt K (curveGaloisData k hτ))),
        resKH1 K (curveGaloisData k hτ) η = kummerMapZHat (constExt K (curveGaloisData k hτ)) v ∧
          v ^ M = unitsRes K (curveGaloisData k hτ) w := by
  obtain ⟨M, hM, w, hw, hwc, hwNF⟩ :=
    (isNFKummerTest_iff_curve_numberField N σ hσ η hη).1 htest
  exact ⟨M, hM, w, hw, hwc, hwNF, exists_finite_resKH1_eq_kummerMapZHat
    (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ k (jacDivFree_numberField X σ hσ))
    (mem_range_of_isAlgebraic_F k hτ) hη hM hw⟩

end Curve

end Iut.Reconstruction.Thm19
