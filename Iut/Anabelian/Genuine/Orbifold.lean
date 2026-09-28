/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Genuine.Pi1
import Pi1.Orbifold.Comparison
import TemperedFundamentalGroups.Setup.Orbifold

/-!
# The model orbicurves as orbifold quotients `[Spec R / A]` (characteristic `0`)

Let `E / k` be an elliptic curve over a field of characteristic `0` and `X = (E, ℓ, M, ±)` a
model orbicurve. In characteristic `0` the base field `P = baseField E` of
`Iut.Anabelian.Genuine.Basic` is `k(x) = K₀ k (xG E)` (the perfect closure of a field of
characteristic `0` is the field itself; `hbase`), so `Gal E = Aut(Ω / P)` is the Galois group
`Aut(Ω / k(x))` of `Pi1.Orbifold` (`galEquiv`, a topological group isomorphism which is the
identity on the underlying automorphisms of `Ω`). Transporting along it:

* `galoisData E ℓ M pm : Pi1.Orbifold.GaloisData k (xG E)`, with `H = Hgp E ℓ M pm`
  (`Aut(Ω / F_X)`), `H_L = Hgp E ℓ M false` (`Aut(Ω / L_X)`, the automorphisms with
  `σ(Q_ℓ) − Q_ℓ ∈ M`: open, normal in `H`), and inertia set `S = Sgen E ℓ M`;
* `pi1Equiv E ℓ M pm : pi1Of E ℓ M pm ≃ₜ* GaloisPi1.pi1 D.H D.S _` (the same Galois-theoretic
  group, transported);
* `orbifold E ℓ M pm`: the affine orbifold `[Spec R / A]` of the tempered-fundamental-groups
  project, `R` the integral closure of `k[x]` in `L_X`, `A = H ⧸ H_L`, at the geometric point
  `R ⊆ Ω`;
* `etaleEquiv E ℓ M pm : etalePi1 R A Ω ≃ₜ* pi1Of E ℓ M pm`: the étale fundamental group of
  `[Spec R / A]` is the genuine étale fundamental group of `X` (SGA 1 V.8.2 with a finite group
  action, `Pi1.Orbifold.GaloisData.equivPi1`).
-/

namespace Iut.Anabelian.Genuine

universe u

open WeierstrassCurve Polynomial AffOrbicurve Pi1.Orbifold

noncomputable section

-- the same decidability instances as in `Iut.Anabelian.Genuine.Pi1` (points of `E` need
-- `DecidableEq k`)
attribute [local instance low] Classical.propDecidable

/-! ### Galois groups over equal subfields -/

section Transport

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- The Galois groups of `Ω` over equal intermediate fields are isomorphic topological groups
(by the identity on automorphisms of `Ω`). -/
@[irreducible] def galEquivOfEq {F F' : IntermediateField K Ω} (h : F = F') :
    (Ω ≃ₐ[F] Ω) ≃ₜ* (Ω ≃ₐ[F'] Ω) := by
  subst h
  exact ContinuousMulEquiv.refl _

@[simp] lemma galEquivOfEq_apply {F F' : IntermediateField K Ω} (h : F = F') (σ : Ω ≃ₐ[F] Ω)
    (x : Ω) : galEquivOfEq h σ x = σ x := by
  subst h
  with_unfolding_all rfl

@[simp] lemma galEquivOfEq_symm_apply {F F' : IntermediateField K Ω} (h : F = F')
    (σ : Ω ≃ₐ[F'] Ω) (x : Ω) : (galEquivOfEq h).symm σ x = σ x := by
  subst h
  with_unfolding_all rfl

/-- The Galois-theoretic fundamental groups `H ⧸ ⟨⟨S⟩⟩` over equal intermediate fields, for
corresponding subgroups and sets. -/
def pi1EquivOfEq {F F' : IntermediateField K Ω} (h : F = F') [IsGalois F Ω] [IsGalois F' Ω]
    {H : Subgroup (Ω ≃ₐ[F] Ω)} {S : Set (Ω ≃ₐ[F] Ω)} (hH : IsClosed (H : Set (Ω ≃ₐ[F] Ω)))
    {H' : Subgroup (Ω ≃ₐ[F'] Ω)} {S' : Set (Ω ≃ₐ[F'] Ω)}
    (hH' : IsClosed (H' : Set (Ω ≃ₐ[F'] Ω)))
    (hHH : ∀ σ, σ ∈ H ↔ galEquivOfEq h σ ∈ H') (hSS : ∀ σ, σ ∈ S ↔ galEquivOfEq h σ ∈ S') :
    GaloisPi1.pi1 H S hH ≃ₜ* GaloisPi1.pi1 H' S' hH' := by
  subst h
  have e : ∀ σ, galEquivOfEq (rfl : F = F) σ = σ := fun σ =>
    AlgEquiv.ext fun x => galEquivOfEq_apply rfl σ x
  simp only [e] at hHH hSS
  obtain rfl : H = H' := Subgroup.ext hHH
  obtain rfl : S = S' := Set.ext hSS
  exact ContinuousMulEquiv.refl _

end Transport

/-! ### The base field in characteristic `0` -/

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- In characteristic `0` the base field `P` (the perfect closure of `k(x)`) is `k(x)`. -/
lemma hbase [CharZero k] : baseField E = K₀ k (xG E) := by
  haveI : Algebra.IsSeparable (xLine E) (Ω E) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  change (perfectClosure (xLine E) (Ω E)).restrictScalars k = xLine E
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.restrictScalars_bot_eq_self]

instance isGalois_K₀ [CharZero k] : IsGalois (K₀ k (xG E)) (Ω E) := by
  rw [← hbase E]
  infer_instance

/-- `Gal E = Aut(Ω / P) ≃ₜ* Aut(Ω / k(x))` in characteristic `0`. -/
def galEquiv [CharZero k] : Gal E ≃ₜ* (Ω E ≃ₐ[K₀ k (xG E)] Ω E) := galEquivOfEq (hbase E)

@[simp] lemma galEquiv_apply [CharZero k] (σ : Gal E) (x : Ω E) : galEquiv E σ x = σ x :=
  galEquivOfEq_apply _ σ x

/-- `Aut(Ω / k(x)) →* Gal E`, the inverse of `galEquiv`. -/
def galHom [CharZero k] : (Ω E ≃ₐ[K₀ k (xG E)] Ω E) →* Gal E :=
  (galEquiv E).symm.toMulEquiv.toMonoidHom

lemma continuous_galHom [CharZero k] : Continuous (galHom E) := (galEquiv E).symm.continuous

@[simp] lemma galHom_galEquiv [CharZero k] (σ : Gal E) : galHom E (galEquiv E σ) = σ :=
  (galEquiv E).symm_apply_apply σ

@[simp] lemma galEquiv_symm_apply [CharZero k] (σ : Ω E ≃ₐ[K₀ k (xG E)] Ω E) (x : Ω E) :
    (galEquiv E).symm σ x = σ x :=
  galEquivOfEq_symm_apply _ σ x

/-- The coordinate `x` of the generic point is transcendental over `k`. -/
lemma transcendental_xG [CharZero k] [E.IsElliptic] : Transcendental k (xG E) := by
  rintro ⟨p, hp, h⟩
  have hx : aeval (xF E) p = algebraMap k[X] E.toAffine.FunctionField p := by
    have hX : algebraMap k[X] E.toAffine.FunctionField Polynomial.X = xF E := by
      rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing]
      rfl
    rw [← hX, aeval_algebraMap_apply, aeval_X_left_apply]
  have h' : ιF E (algebraMap k[X] E.toAffine.FunctionField p) = 0 := by
    rw [← hx, ← Polynomial.aeval_algHom_apply]
    exact h
  have hinj : Function.Injective (algebraMap k[X] E.toAffine.CoordinateRing) := by
    intro p q h
    have h' : (p - q) • (1 : E.toAffine.CoordinateRing) + (0 : k[X]) •
        Affine.CoordinateRing.mk E.toAffine Polynomial.X = 0 := by
      rw [zero_smul, add_zero, sub_smul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero h').1
  have h'' := (ιF E).injective (h'.trans (map_zero _).symm)
  rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing] at h''
  refine hp (hinj ?_)
  rw [map_zero]
  exact IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField
    (h''.trans (map_zero _).symm)

/-! ### The geometric subgroup `Aut(Ω / L_X)` -/

variable [E.IsElliptic]

lemma mem_Hgp_false {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {σ : Gal E} :
    σ ∈ Hgp E ℓ M false ↔ act E σ (Qpt E ℓ) - Qpt E ℓ ∈ Mbar E ℓ M := by
  constructor
  · rintro ⟨ε, hε, h⟩
    rcases hε with rfl | ⟨h', -⟩
    · simpa using h
    · exact absurd h' Bool.false_ne_true
  · intro h
    exact ⟨1, Or.inl rfl, by simpa using h⟩

lemma Hgp_false_le (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Hgp E ℓ M false ≤ Hgp E ℓ M pm := by
  rintro σ ⟨ε, hε, h⟩
  refine ⟨ε, ?_, h⟩
  rcases hε with h' | ⟨h', -⟩
  · exact Or.inl h'
  · exact absurd h' Bool.false_ne_true

/-- `Aut(Ω / L_X)` is normal in `Aut(Ω / F_X)`. -/
lemma conj_mem_Hgp_false {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {pm : Bool} {σ n : Gal E}
    (hσ : σ ∈ Hgp E ℓ M pm) (hn : n ∈ Hgp E ℓ M false) : σ * n * σ⁻¹ ∈ Hgp E ℓ M false := by
  rw [mem_Hgp_false] at hn ⊢
  obtain ⟨η, -, hη⟩ := (Hgp E ℓ M pm).inv_mem hσ
  have h1 : act E σ⁻¹ (Qpt E ℓ) =
      η • Qpt E ℓ + (act E σ⁻¹ (Qpt E ℓ) - η • Qpt E ℓ) := by abel
  have h2 : act E n (Qpt E ℓ) = Qpt E ℓ + (act E n (Qpt E ℓ) - Qpt E ℓ) := by abel
  have hQ : η • act E σ (Qpt E ℓ) + (act E σ⁻¹ (Qpt E ℓ) - η • Qpt E ℓ) = Qpt E ℓ := by
    have := congrArg (act E σ) h1
    rw [← act_mul, mul_inv_cancel, act_one, map_add, map_zsmul, act_mem_Mbar E σ hη] at this
    exact this.symm
  rw [act_mul, act_mul, h1, map_add (act E n), map_zsmul, h2, act_mem_Mbar E n hη, map_add,
    map_zsmul, map_add, act_mem_Mbar E σ hn, act_mem_Mbar E σ hη]
  have e : η • (act E σ (Qpt E ℓ) + (act E n (Qpt E ℓ) - Qpt E ℓ)) +
      (act E σ⁻¹ (Qpt E ℓ) - η • Qpt E ℓ) - Qpt E ℓ =
      η • (act E n (Qpt E ℓ) - Qpt E ℓ) := by
    conv_lhs => rw [zsmul_add, add_comm (η • act E σ (Qpt E ℓ)), add_assoc, hQ]
    abel
  rw [e]
  exact zsmul_mem hn η

/-! ### The Galois data and the orbifold -/

variable [CharZero k]

/-- **The Galois data of the model orbicurve** `(E, ℓ, M, ±)`: `H = Aut(Ω / F_X)`,
`H_L = Aut(Ω / L_X)`, as subgroups of `Aut(Ω / k(x))`. -/
def galoisData (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) : GaloisData k (xG E) where
  H := (Hgp E ℓ M pm).comap (galHom E)
  HL := (Hgp E ℓ M false).comap (galHom E)
  le := Subgroup.comap_mono (Hgp_false_le E ℓ M pm)
  isOpen_HL := by
    rw [Subgroup.coe_comap]
    exact (isOpen_Hgp E ℓ M false).preimage (continuous_galHom E)
  conj_mem h hh n hn := by
    change galHom E (h * n * h⁻¹) ∈ Hgp E ℓ M false
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_Hgp_false E hh hn
  transcendental := transcendental_xG E

lemma mem_galoisData_H {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {pm : Bool} (σ : Gal E) :
    galEquiv E σ ∈ (galoisData E ℓ M pm).H ↔ σ ∈ Hgp E ℓ M pm := by
  change galHom E (galEquiv E σ) ∈ Hgp E ℓ M pm ↔ _
  rw [galHom_galEquiv]

lemma mem_galoisData_S {ℓ : ℕ} {M : AddSubgroup E.toAffine.Point} {pm : Bool} (σ : Gal E) :
    galEquiv E σ ∈ (galoisData E ℓ M pm).S ↔ σ ∈ Sgen E ℓ M := by
  have hHL : galEquiv E σ ∈ (galoisData E ℓ M pm).HL ↔ σ ∈ Hgp E ℓ M false := by
    change galHom E (galEquiv E σ) ∈ Hgp E ℓ M false ↔ _
    rw [galHom_galEquiv]
  have hI : ∀ W : ValuationSubring (Ω E),
      galEquiv E σ ∈ GaloisPi1.inertia W ↔ σ ∈ GaloisPi1.inertia W := fun W => by
    simp only [GaloisPi1.inertia, Set.mem_setOf_eq, galEquiv_apply]
  simp only [GaloisData.S, Sgen, Set.mem_setOf_eq, hHL, mem_Hgp_false, hI]

/-- **The genuine étale fundamental group is the Galois-theoretic group of the Galois data**. -/
def pi1Equiv (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    pi1Of E ℓ M pm ≃ₜ* GaloisPi1.pi1 (galoisData E ℓ M pm).H (galoisData E ℓ M pm).S
      (galoisData E ℓ M pm).isClosed_H :=
  pi1EquivOfEq (hbase E) _ _ (fun σ => (mem_galoisData_H E σ).symm)
    (fun σ => (mem_galoisData_S E σ).symm)

/-- The coordinate ring `R` of `[Spec R / A]` is a `k`-algebra (through `k[x] ⊆ R`). -/
instance algebraCoordRing {t : Ω E} (F : IntermediateField (K₀ k t) (Ω E)) :
    Algebra k (CoordRing k t F) :=
  ((algebraMap (A₀ k t) (CoordRing k t F)).comp (algebraMap k (A₀ k t))).toAlgebra

instance isScalarTower_coordRing {t : Ω E} (F : IntermediateField (K₀ k t) (Ω E)) :
    IsScalarTower k (CoordRing k t F) (Ω E) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap (CoordRing k t F) (Ω E)
      (algebraMap (A₀ k t) (CoordRing k t F) (algebraMap k (A₀ k t) c))
    rw [← IsScalarTower.algebraMap_apply]
    rfl

/-- The finite group `A = H ⧸ H_L` acts `k`-linearly on `R`. -/
instance smulCommClass_galoisData {t : Ω E} (D : GaloisData k t) : SMulCommClass D.A k D.R where
  smul_comm a c r := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    refine CoordRing.ext ?_
    rw [GaloisData.algebraMap_smul, ← IsScalarTower.algebraMap_apply]
    exact (h : Ω E ≃ₐ[K₀ k t] Ω E).commutes ⟨_, (K₀ k t).algebraMap_mem c⟩

/-- **The model orbicurve `(E, ℓ, M, ±)` as the affine orbifold** `[Spec R / A]`
(`R` the integral closure of `k[x]` in `L_X`, `A = Aut(Ω / F_X) ⧸ Aut(Ω / L_X)`) at the
geometric point `R ⊆ Ω`. -/
def orbifold (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    TemperedFundamentalGroups.AffineOrbifold k where
  R := (galoisData E ℓ M pm).R
  A := (galoisData E ℓ M pm).A
  Ω := Ω E

/-- **The étale fundamental group of `[Spec R / A]` is the genuine étale fundamental group** of
the model orbicurve (SGA 1 V.8.2, `Pi1.Orbifold.GaloisData.equivPi1`). -/
def etaleEquiv (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    (orbifold E ℓ M pm).etalePi1 ≃ₜ* pi1Of E ℓ M pm :=
  (galoisData E ℓ M pm).equivPi1.trans (pi1Equiv E ℓ M pm).symm

end

end Iut.Anabelian.Genuine
