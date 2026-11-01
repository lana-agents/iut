/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTemperedClass
import TemperedFundamentalGroups.SemistableReduction.CompositeValuation
import TemperedFundamentalGroups.Andre.TateCuspInertia

/-!
# The tempered étale theta class on decomposition groups of points (MR14, runs 8–9, R4)

[EtTh] Prop. 1.4(iii) (ET l.1334–1347): for a non-cuspidal point `y ∈ Ÿ(L)` the restriction of
the étale theta class to the decomposition group of `y` is the Kummer class of the value
`Θ̈(y)`. This file proves the tempered version for the class `thetaClassTemp η n` of
`ThetaTemperedClass.lean`.

In `tempered-fundamental-groups` the decomposition groups are `galoisToTempered`: for a valuation
subring `V ⊆ Ω` (the "base point") the group `decompositionGroup R V` of `R`-automorphisms of `Ω`
preserving `V` acts on every fibre by `t ↦ σ ∘ t`. When `V` is centred on a point of the curve
(a composite of a place `A` over the point with a valuation of the residue field over `O`), this
is the decomposition group of the point (for the base point `V`).

* Generic, now in `tempered-fundamental-groups` (`Tempered/CuspInertia.lean`,
  `Andre/TateCuspInertia.lean`): `temperedPi1Map_galoisToTempered` (`galoisToTempered` is natural
  in maps of orbifolds), `character_galoisToTempered` (Galois elements lie in `Π^tp_Y`) and
  `exists_le_comap_eq`; here only `galoisToTempered_mem_piY`.
* The class on Galois elements: for `σ ∈ D_V` fixing `L 0` and `L j`, `galoisToTempered σ ∈ Π^tp_Ÿ`
  (`galoisToTempered_mem_piYddotX`), `toLevel j (galoisToTempered σ)` is the Galois element of
  the level `j` (`toLevel_galoisToTempered`), and **`classAt_galois`**: every representative of
  `classAt η j n` is, on these elements, `σ ↦ σ(α)/α` up to a coboundary (`α^n = η_j`).
* Places: `mem_place_iff` (Galois elements preserving `V` preserve `A`, when the residue field
  of `A` is algebraic over `k`: `exists_monic_lt_one`, `exists_mul_mem`), `exists_kummer_close`
  (Kummer cocycles of units congruent mod `𝔪_A` differ by a coboundary; residue characteristic
  `0`).
* **`classAt_place`**, `classAt_place_mul`: if `η_j` is integral at `A` with residue `b ∈ k^×`,
  the class restricted to the decomposition group is the Kummer cocycle of `b`
  (`ClassAtPoint`, a `Prop` def used only as a conclusion).
* Concrete: **`exists_thetaClassTemp_points`** — for the system of `exists_thetaClassTemp`, at
  every Tate point `u` the class mod `n ∣ N_j` on the decomposition group is the Kummer cocycle
  of `Θ̈(u^{N_j})` (C1 = `LevelsDominated` as hypothesis, as everywhere on `Π^tp_Ÿ`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve IsLocalRing KummerTheory KummerTheory.Curve CurvesJacobian.Kummer
open CurvesJacobian.Cusp TateCurvesTheta TateParameter WeierstrassCurve.Affine
open TemperedFundamentalGroups TemperedFundamentalGroups.Kummer

noncomputable section

universe u

namespace Iut.EtaleTheta

/-! ### Galois elements lie in `Π^tp_Y` -/

section CharacterGalois

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O) (T : TateObject.Data O R)

theorem galoisToTempered_mem_piY (σ : decompositionGroup R V) :
    galoisToTempered O R A hV σ ∈ TateObject.piY (A := A) T V hV :=
  character_galoisToTempered hV T σ

end CharacterGalois

/-! ### The theta class on Galois elements -/

section Class

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]

variable (hL) in
/-- A Galois element over `X` fixing the level `L j`, as a Galois element of the level. -/
def decompLevel (j : ℕ) (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    decompositionGroup (fieldData ht (L j) (hL j)).R V :=
  ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv) fun r => by
      exact hσ _ ((fieldData_L ht (L j) (hL j)).le (CoordRing.algebraMap_mem r)),
    fun x => σ.2 x⟩

omit [CharZero k] [IsSepClosed Ω] het in
theorem decompRestrict_decompLevel (j : ℕ) (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    decompRestrict (R := (fieldData ht LX hLX).R) (decompLevel hL j σ hσ) = σ :=
  Subtype.ext (AlgEquiv.ext fun _ => rfl)

omit [CharZero k] [IsSepClosed Ω] het in
theorem galoisToTempered_level (j : ℕ) (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    temperedPi1Map (muL ht hLX (L j) (hL j)) V hV
        (galoisToTempered O _ _ hV (decompLevel hL j σ hσ)) =
      galoisToTempered O _ _ hV σ := by
  rw [temperedPi1Map_galoisToTempered, decompRestrict_decompLevel]

omit [CharZero k] [IsSepClosed Ω] het in
variable (V hV T hL) in
/-- **Galois elements fixing `Ÿ'_2` lie in `Π^tp_Ÿ`.** -/
theorem galoisToTempered_mem_piYddotX (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    galoisToTempered O _ _ hV σ ∈ piYddotX V hV T hL :=
  ⟨galoisToTempered_mem_piY hV T σ,
    ⟨galoisToTempered O _ _ hV (decompLevel hL 0 σ hσ), galoisToTempered_level 0 σ hσ⟩⟩

omit [IsSepClosed Ω] in
theorem toLevel_galoisToTempered (hC1 : LevelsDominated V hV T hL) (j : ℕ)
    (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
    (hσj : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) :
    toLevel hC1 j ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩ =
      galoisToTempered O _ _ hV (decompLevel hL j σ hσj) := by
  apply temperedPi1Map_injective V hV (muL ht hLX (L j) (hL j))
  rw [temperedPi1Map_toLevel, galoisToTempered_level]

variable (η : ∀ j, units (fieldData ht (L j) (hL j)))

omit [IsSepClosed Ω] in
/-- The action of a Galois element of `Π^tp` on `μ_n` is the action of the automorphism. -/
theorem val_galoisToTempered_smul (D : GaloisData k t) (n : ℕ) [NeZero n]
    (σ : decompositionGroup D.R V) (ζ : Mu n Ω) :
    ((Mu.val (galoisToTempered O D.R D.A hV σ • ζ) : Ωˣ) : Ω) =
      (σ : Ω ≃ₐ[D.R] Ω) (Mu.val ζ : Ω) := by
  change ((Mu.val (tempToPi D O V hV (galoisToTempered O D.R D.A hV σ) • ζ) : Ωˣ) : Ω) = _
  rw [tempToPi_galoisToTempered]
  rfl

omit [CharZero k] [IsSepClosed Ω] in
theorem val_galoisToH_smul (D : GaloisData k t) (n : ℕ) (σ : Ω ≃ₐ[D.R] Ω) (ζ : Mu n Ω) :
    ((Mu.val (galoisToH σ • ζ) : Ωˣ) : Ω) = σ (Mu.val ζ : Ω) := rfl

omit [CharZero k] [IsSepClosed Ω] in
theorem val_toGalF_galoisToH_smul (D : GaloisData k t) (σ : Ω ≃ₐ[D.R] Ω) (α : Ωˣ) :
    ((toGalF D (galoisToH σ) • α : Ωˣ) : Ω) = σ (α : Ω) := rfl

omit [CharZero k] [IsSepClosed Ω] hX het in
@[simp]
theorem decompLevel_apply (j : ℕ) (σ : decompositionGroup (fieldData ht LX hLX).R V)
    (hσ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x) (x : Ω) :
    ((decompLevel hL j σ hσ : decompositionGroup (fieldData ht (L j) (hL j)).R V) :
      Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω) x = (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x := rfl

/-- **The theta class at the level `j` on Galois elements**: every representative `c` of
`classAt η j n` is, on the Galois elements `σ ∈ D_V` fixing `L 0` and `L j`, the Kummer cocycle
`σ ↦ σ(α)/α` of an `n`-th root `α` of `η_j`, up to a coboundary. -/
theorem classAt_galois (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (c : ContH1.cocycles (piYddotX V hV T hL) (Mu n Ω))
    (hc : ContH1.mk c = classAt η hC1 j n) :
    ∃ (α : Ω) (_ : α ^ n = (((η j : (F (fieldData ht (L j) (hL j)))ˣ) :
        F (fieldData ht (L j) (hL j))) : Ω)) (_ : α ≠ 0) (M : Mu n Ω),
      ∀ (σ : decompositionGroup (fieldData ht LX hLX).R V)
        (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
        (_ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
        ((Mu.val (c ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩) : Ωˣ) : Ω) =
          (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) α / α *
            ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) (Mu.val M : Ω) / (Mu.val M : Ω)) := by
  obtain ⟨cj, hcj⟩ := ContH1.mk_surjective
    (kummerMapTempered (fieldData ht (L j) (hL j)) O V hV n (η j))
  obtain ⟨M₁, hM₁⟩ := kummerMapTempered_galoisToTempered (fieldData ht (L j) (hL j)) O V hV n
    (η j) cj hcj
  have hres := hc
  rw [classAt, ← hcj, resLevel, ContH1.map_mk, ContH1.mk_eq_mk_iff] at hres
  obtain ⟨m, hm⟩ := hres
  obtain ⟨α, hαdef⟩ : ∃ α, α = kummerRoot n (F (fieldData ht (L j) (hL j))) Ω
      ((η j : (F (fieldData ht (L j) (hL j)))ˣ)) := ⟨_, rfl⟩
  have hα := kummerRoot_pow n (F (fieldData ht (L j) (hL j))) Ω
    ((η j : (F (fieldData ht (L j) (hL j)))ˣ))
  rw [← hαdef] at hα
  refine ⟨(α : Ω), ?_, α.ne_zero, M₁ * m, fun σ hσ0 hσj => ?_⟩
  · have := congrArg (fun z : Ωˣ => (z : Ω)) hα
    simpa using this
  have h1 := hm ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩
  have h2 := hM₁ (decompLevel hL j σ hσj)
  simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply] at h1
  rw [toLevel_galoisToTempered hC1 j σ hσ0 hσj, h2] at h1
  rw [eq_div_iff_mul_eq'] at h1
  rw [← h1]
  have hγ : ∀ ζ : Mu n Ω, ((Mu.val ((⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩ :
      piYddotX V hV T hL) • ζ) : Ωˣ) : Ω) =
      (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) (Mu.val ζ : Ω) := fun ζ =>
    val_galoisToTempered_smul (D := fieldData ht LX hLX) n σ ζ
  simp only [map_mul, _root_.map_div, Units.val_mul, Units.val_div_eq_div_val, hγ,
    val_galoisToH_smul, val_kummerFun, val_toGalF_galoisToH_smul, decompLevel_apply]
  rw [← hαdef]
  have hm0 := (Mu.val m).ne_zero
  have hM0 := (Mu.val M₁).ne_zero
  have hα0 := α.ne_zero
  field_simp

end Class

/-! ### Places over points and base points through them -/

section Place

open TemperedFundamentalGroups.SemistableReduction

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

variable {A V : ValuationSubring Ω}

/-- Elements of `A` with inverse in `A` have valuation `1`. -/
theorem valuation_eq_one_of_mem {z : Ω} (hz : z ∈ A) (hz' : z⁻¹ ∈ A) (hz0 : z ≠ 0) :
    A.valuation z = 1 := by
  have := A.valuation_unit (Units.mk ⟨z, hz⟩ ⟨z⁻¹, hz'⟩ (Subtype.ext (mul_inv_cancel₀ hz0))
    (Subtype.ext (inv_mul_cancel₀ hz0)))
  simpa using this

/-- In a valuation ring, `x^n ∈ A` (`n > 0`) implies `x ∈ A`. -/
theorem mem_of_pow_mem {x : Ω} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ A) : x ∈ A := by
  by_contra hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
  have hi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
  have hlt : A.valuation x⁻¹ < 1 := by
    rw [CentreGerms.valuation_lt_one_iff_inv, inv_inv]; exact .inr hx
  have h1 : A.valuation (x ^ n) ≤ 1 := (A.valuation_le_one_iff _).2 h
  have h2 : A.valuation (x ^ n * x⁻¹ ^ n) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow, map_one]
  rw [map_mul, map_pow (A.valuation) x⁻¹] at h2
  have h3 : A.valuation x⁻¹ ^ n < 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    rw [pow_succ]
    calc A.valuation x⁻¹ ^ (0 + m) * A.valuation x⁻¹ ≤ 1 * A.valuation x⁻¹ :=
          mul_le_mul_left (pow_le_one' hlt.le _) _
      _ < 1 := by rw [one_mul]; exact hlt
  have : A.valuation (x ^ n) * A.valuation x⁻¹ ^ n < 1 :=
    lt_of_le_of_lt (mul_le_mul_left h1 _) (by rwa [one_mul])
  exact absurd h2 this.ne

/-- Units of `Ω` that are `1` modulo `𝔪_A` stay so under automorphisms preserving `A`. -/
theorem valuation_lt_one_map (σ : Ω ≃+* Ω) (hσA : ∀ x, σ x ∈ A ↔ x ∈ A) {z : Ω}
    (hz : A.valuation z < 1) : A.valuation (σ z) < 1 := by
  rw [CentreGerms.valuation_lt_one_iff_inv] at hz ⊢
  rcases hz with h | h
  · exact .inl (by rw [h, map_zero])
  · exact .inr (by rw [← map_inv₀, hσA]; exact h)

/-- **For `V ≤ A`, multiples of elements of `A` by nonzero elements of `k` lie in `V`**, when
`x` is a root mod `𝔪_A` of a monic polynomial over `k` and `V ∩ k = O`. -/
theorem exists_mul_mem (hVA : V ≤ A) {O : ValuationSubring k}
    (hO : V.comap (algebraMap k Ω) = O) (hk : ∀ c : k, algebraMap k Ω c ∈ A) {x : Ω}
    (hx : x ∈ A) {p : k[X]} (hp : p.Monic) (hpx : A.valuation (aeval x p) < 1) :
    ∃ c : k, c ≠ 0 ∧ algebraMap k Ω c * x ∈ V := by
  -- a common denominator `c` of the coefficients
  have hdc : ∀ a : k, ∃ d : k, d ≠ 0 ∧ d ∈ O ∧ d * a ∈ O := fun a => by
    by_cases ha : a ∈ O
    · exact ⟨1, one_ne_zero, O.one_mem, by rwa [one_mul]⟩
    · have ha0 : a ≠ 0 := by rintro rfl; exact ha O.zero_mem
      exact ⟨a⁻¹, inv_ne_zero ha0, (O.mem_or_inv_mem a).resolve_left ha,
        by rw [inv_mul_cancel₀ ha0]; exact O.one_mem⟩
  choose d hd0 hdO hda using hdc
  set S := Finset.range (p.natDegree + 1) with hS
  set c : k := ∏ i ∈ S, d (p.coeff i) with hc_def
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd0 _
  have hcO : c ∈ O := prod_mem fun i _ => hdO _
  have hca : ∀ i ∈ S, c * p.coeff i ∈ O := fun i hi => by
    rw [hc_def, ← Finset.mul_prod_erase S _ hi, mul_comm (d _), mul_assoc]
    exact mul_mem (prod_mem fun j _ => hdO _) (hda _)
  have hOV : ∀ a ∈ O, algebraMap k Ω a ∈ V := fun a ha => by
    rw [← hO] at ha; exact ha
  refine ⟨c, hc0, ?_⟩
  by_contra hy
  obtain ⟨y, hCxy⟩ : ∃ y, algebraMap k Ω c * x = y := ⟨_, rfl⟩
  rw [hCxy] at hy
  set C := algebraMap k Ω c with hC
  have hC0 : C ≠ 0 := (_root_.map_ne_zero _).2 hc0
  have hy0 : y ≠ 0 := by rintro rfl; exact hy V.zero_mem
  -- `y⁻¹ ∈ 𝔪_V`
  have hyinv : V.valuation y⁻¹ < 1 := by
    rw [CentreGerms.valuation_lt_one_iff_inv, inv_inv]; exact .inr hy
  -- `y` is a unit of `A`
  have hyA : y ∈ A := hCxy ▸ mul_mem (hk c) hx
  have hyinvA : y⁻¹ ∈ A := by
    by_contra h
    have hlt : A.valuation y < 1 := by
      rw [CentreGerms.valuation_lt_one_iff_inv]; exact .inr h
    exact hy ((V.valuation_le_one_iff y).1
      (CompositeValuation.valuation_lt_one_of_le hVA hlt).le)
  have hCA : A.valuation C = 1 :=
    valuation_eq_one_of_mem (hk c) (by rw [hC, ← map_inv₀]; exact hk _) hC0
  have hyA1 : A.valuation y⁻¹ = 1 :=
    valuation_eq_one_of_mem hyinvA (by rwa [inv_inv]) (inv_ne_zero hy0)
  -- the identity `C^d P y^{-d} = Σ_{i<d} C^{d-i} a_i y^{-(d-i)} + 1`
  set n := p.natDegree with hn
  have hterm : ∀ i m : ℕ, C ^ (m + i) * (p.coeff i • x ^ i) * y⁻¹ ^ (m + i) =
      algebraMap k Ω (c ^ m * p.coeff i) * y⁻¹ ^ m := by
    intro i m
    rw [Algebra.smul_def, map_mul, map_pow, ← hC]
    calc C ^ (m + i) * (algebraMap k Ω (p.coeff i) * x ^ i) * y⁻¹ ^ (m + i) =
        C ^ m * algebraMap k Ω (p.coeff i) * y⁻¹ ^ m * (C * x * y⁻¹) ^ i := by ring
      _ = _ := by rw [hCxy, mul_inv_cancel₀ hy0, one_pow, mul_one]
  have hid : C ^ n * aeval x p * y⁻¹ ^ n =
      (∑ i ∈ Finset.range n, algebraMap k Ω (c ^ (n - i) * p.coeff i) * y⁻¹ ^ (n - i)) + 1 := by
    rw [aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : n - i + i = n := Nat.sub_add_cancel (Finset.mem_range.1 hi).le
      rw [← hterm i (n - i), hi']
    · have := hterm n 0
      rw [zero_add, pow_zero, one_mul, pow_zero, mul_one] at this
      rw [this, hp.coeff_natDegree, map_one]
  -- valuations
  have hsum : V.valuation
      (∑ i ∈ Finset.range n, algebraMap k Ω (c ^ (n - i) * p.coeff i) * y⁻¹ ^ (n - i)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
    have hb : c ^ (n - i) * p.coeff i ∈ O := by
      rw [hm, pow_succ, mul_assoc]
      exact mul_mem (pow_mem hcO _) (hca i (Finset.mem_range.2 (by omega)))
    rw [map_mul, map_pow]
    generalize c ^ (n - i) * p.coeff i = b at hb ⊢
    rw [hm, pow_succ]
    calc V.valuation (algebraMap k Ω b) *
          (V.valuation y⁻¹ ^ m * V.valuation y⁻¹) ≤ 1 * (1 * V.valuation y⁻¹) :=
          mul_le_mul' ((V.valuation_le_one_iff _).2 (hOV _ hb))
            (mul_le_mul_left (pow_le_one' hyinv.le _) _)
      _ < 1 := by rw [one_mul, one_mul]; exact hyinv
  have hrhs : V.valuation
      ((∑ i ∈ Finset.range n, algebraMap k Ω (c ^ (n - i) * p.coeff i) * y⁻¹ ^ (n - i)) + 1) =
        1 := by
    rw [Valuation.map_add_eq_of_lt_right _ (by rw [map_one]; exact hsum), map_one]
  have hlhs : A.valuation (C ^ n * aeval x p * y⁻¹ ^ n) < 1 := by
    rw [map_mul, map_mul, map_pow, map_pow, hCA, hyA1, one_pow, one_mul, mul_one]
    exact hpx
  have := CompositeValuation.valuation_lt_one_of_le hVA hlhs
  rw [hid, hrhs] at this
  exact lt_irrefl _ this

/-- Elements of a place `A ⊇ k` whose residue field is algebraic over `k` are roots mod `𝔪_A` of
monic polynomials over `k`. -/
theorem exists_monic_lt_one (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A)) {x : Ω} (hx : x ∈ A) :
    ∃ p : k[X], p.Monic ∧ A.valuation (aeval x p) < 1 := by
  letI := resAlg A hk
  obtain ⟨p, hp, hpx⟩ := Algebra.IsIntegral.isIntegral (R := k) (residue A ⟨x, hx⟩)
  refine ⟨p, hp, ?_⟩
  have hmem : aeval x p ∈ A := by
    rw [aeval_eq_sum_range]
    exact sum_mem fun i _ => by
      rw [Algebra.smul_def]; exact mul_mem (hk _) (pow_mem hx _)
  have he : (⟨_, hmem⟩ : A) = ∑ i ∈ Finset.range (p.natDegree + 1),
      toW hk (p.coeff i) * (⟨x, hx⟩ : A) ^ i := by
    apply Subtype.ext
    simp only [aeval_eq_sum_range, Algebra.smul_def]
    push_cast
    rfl
  have h0 : residue A ⟨_, hmem⟩ = 0 := by
    rw [he, map_sum]
    simp only [map_mul, map_pow]
    rw [← hpx, eval₂_eq_sum_range]
    rfl
  exact (A.valuation_lt_one_iff ⟨_, hmem⟩).1 ((residue_eq_zero_iff _).1 h0)

/-- **Automorphisms preserving `V` and fixing `k` preserve the place `A ⊇ V`**, given that every
element of `A` has a multiple in `V` by a nonzero element of `k`. -/
theorem mem_place_of_mem (hVA : V ≤ A) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hmul : ∀ x ∈ A, ∃ c : k, c ≠ 0 ∧ algebraMap k Ω c * x ∈ V) (σ : Ω ≃+* Ω)
    (hσk : ∀ c : k, σ (algebraMap k Ω c) = algebraMap k Ω c) (hσV : ∀ x, σ x ∈ V ↔ x ∈ V)
    {x : Ω} (hx : x ∈ A) : σ x ∈ A := by
  obtain ⟨c, hc0, hcx⟩ := hmul x hx
  have h1 : σ (algebraMap k Ω c * x) ∈ V := (hσV _).2 hcx
  rw [map_mul, hσk] at h1
  have hC0 : algebraMap k Ω c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  have : σ x = algebraMap k Ω c⁻¹ * (algebraMap k Ω c * σ x) := by
    rw [map_inv₀, ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
  rw [this]
  exact mul_mem (hk _) (hVA h1)

theorem mem_place_iff (hVA : V ≤ A) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
    (hmul : ∀ x ∈ A, ∃ c : k, c ≠ 0 ∧ algebraMap k Ω c * x ∈ V) (σ : Ω ≃+* Ω)
    (hσk : ∀ c : k, σ (algebraMap k Ω c) = algebraMap k Ω c) (hσV : ∀ x, σ x ∈ V ↔ x ∈ V)
    (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  refine ⟨fun h => ?_, mem_place_of_mem hVA hk hmul σ hσk hσV⟩
  have hk' : ∀ c : k, σ.symm (algebraMap k Ω c) = algebraMap k Ω c := fun c => by
    rw [RingEquiv.symm_apply_eq, hσk]
  have hV' : ∀ z, σ.symm z ∈ V ↔ z ∈ V := fun z => by
    rw [← hσV (σ.symm z), RingEquiv.apply_symm_apply]
  simpa using mem_place_of_mem hVA hk hmul σ.symm hk' hV' h

/-- **Roots of unity in residue characteristic `0`**: an `n`-th root of unity which is `1`
modulo `𝔪_A` is `1` (`k ⊆ A` of characteristic `0`). -/
theorem eq_one_of_pow_eq_one [CharZero k] (hk : ∀ c : k, algebraMap k Ω c ∈ A) {n : ℕ}
    (hn : 0 < n) {ζ : Ω} (hζ : ζ ^ n = 1) (h : A.valuation (ζ - 1) < 1) : ζ = 1 := by
  by_contra hne
  have hζA : ζ ∈ A := mem_of_pow_mem hn (by rw [hζ]; exact A.one_mem)
  have hgeom : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have := geom_sum_mul ζ n
    rw [hζ, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  -- `n = Σ_{i<n} (1 - ζ^i)` has valuation `< 1`
  have hsum : A.valuation (∑ i ∈ Finset.range n, (1 - ζ ^ i)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    have e : 1 - ζ ^ i = -((∑ j ∈ Finset.range i, ζ ^ j) * (ζ - 1)) := by
      rw [geom_sum_mul]; ring
    rw [e, Valuation.map_neg, map_mul]
    calc A.valuation (∑ j ∈ Finset.range i, ζ ^ j) * A.valuation (ζ - 1) ≤
          1 * A.valuation (ζ - 1) :=
          mul_le_mul_left ((A.valuation_le_one_iff _).2
            (sum_mem fun j _ => pow_mem hζA j)) _
      _ < 1 := by rw [one_mul]; exact h
  have hn' : ∑ i ∈ Finset.range n, (1 - ζ ^ i) = algebraMap k Ω n := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_natCast]
  rw [hn'] at hsum
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have := valuation_eq_one_of_mem (A := A) (hk n) (by rw [← map_inv₀]; exact hk _)
    ((_root_.map_ne_zero _).2 hn0)
  exact absurd this hsum.ne

/-- **A root of unity close to an `n`-th root of a principal unit** (`Ω` separably closed of
characteristic `0`): if `w^n ≡ 1 mod 𝔪_A`, some `n`-th root of unity `ζ` has `w ≡ ζ`. -/
theorem exists_root_of_unity_close [CharZero k] [IsSepClosed Ω] {n : ℕ} (hn : 0 < n) {w : Ω}
    (hw : A.valuation (w ^ n - 1) < 1) :
    ∃ ζ : Ω, ζ ^ n = 1 ∧ A.valuation (w * ζ⁻¹ - 1) < 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hprod := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hn hζ₀)
  rw [eval_sub, eval_pow, eval_X, eval_one, eval_prod] at hprod
  simp only [eval_sub, eval_X, eval_C] at hprod
  -- `w ∈ A`
  have hwA : w ∈ A := by
    refine mem_of_pow_mem hn ?_
    have : w ^ n = (w ^ n - 1) + 1 := by ring
    rw [this]
    exact add_mem ((A.valuation_le_one_iff _).1 hw.le) A.one_mem
  -- some factor `w - ζ` lies in `𝔪_A`
  have hroot : ∀ ζ ∈ Polynomial.nthRootsFinset n (1 : Ω), ζ ^ n = 1 := fun ζ hζ =>
    (Polynomial.mem_nthRootsFinset hn 1).1 hζ
  have hζA : ∀ ζ ∈ Polynomial.nthRootsFinset n (1 : Ω), ζ ∈ A := fun ζ hζ =>
    mem_of_pow_mem hn (by rw [hroot ζ hζ]; exact A.one_mem)
  obtain ⟨ζ, hζ, hlt⟩ : ∃ ζ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (w - ζ) < 1 := by
    by_contra hall
    push Not at hall
    have h1 : ∀ ζ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (w - ζ) = 1 :=
      fun ζ hζ => le_antisymm ((A.valuation_le_one_iff _).2 (sub_mem hwA (hζA ζ hζ)))
        (hall ζ hζ)
    have : A.valuation (w ^ n - 1) = 1 := by
      rw [hprod, map_prod, Finset.prod_eq_one h1]
    exact absurd this hw.ne
  have hζ1 := hroot ζ hζ
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hζ1; exact zero_ne_one hζ1
  refine ⟨ζ, hζ1, ?_⟩
  have hv : A.valuation ζ⁻¹ = 1 := valuation_eq_one_of_mem
    (mem_of_pow_mem hn (by rw [inv_pow, hζ1, inv_one]; exact A.one_mem))
    (by rw [inv_inv]; exact hζA ζ hζ) (inv_ne_zero hζ0)
  have e : w * ζ⁻¹ - 1 = (w - ζ) * ζ⁻¹ := by field_simp
  rw [e, map_mul, hv, mul_one]
  exact hlt

/-- **Kummer cocycles of elements close to a unit of the place**: if `α^n = e`, `β^n = b` with
`e ≡ b mod 𝔪_A` (`b ≠ 0`), there is `ζ ∈ μ_n` such that for every automorphism `σ` preserving
`A`, fixing `e`, `b` and `k`: `σα/α = σβ/β · σζ/ζ`. -/
theorem exists_kummer_close [CharZero k] [IsSepClosed Ω]
    (hk : ∀ c : k, algebraMap k Ω c ∈ A) {n : ℕ} (hn : 0 < n) {α β e b : Ω}
    (hα : α ^ n = e) (hβ : β ^ n = b) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (heb : A.valuation (e / b - 1) < 1) :
    ∃ ζ : Ω, ζ ^ n = 1 ∧ ζ ≠ 0 ∧ ∀ σ : Ω ≃+* Ω, (∀ x, σ x ∈ A ↔ x ∈ A) → σ e = e → σ b = b →
      σ α / α = σ β / β * (σ ζ / ζ) := by
  have hw : A.valuation ((α / β) ^ n - 1) < 1 := by rwa [div_pow, hα, hβ]
  obtain ⟨ζ, hζ, hwζ⟩ := exists_root_of_unity_close (k := k) hn hw
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨ζ, hζ, hζ0, fun σ hσA hσe hσb => ?_⟩
  set w' := α / β * ζ⁻¹ with hw'
  have hw'0 : w' ≠ 0 := mul_ne_zero (div_ne_zero hα0 hβ0) (inv_ne_zero hζ0)
  -- `ρ = σw'/w'` is an `n`-th root of unity which is `1` mod `𝔪_A`
  have hρn : (σ w' / w') ^ n = 1 := by
    rw [div_pow, ← map_pow]
    have : w' ^ n = e / b := by
      rw [hw', mul_pow, div_pow, hα, hβ, inv_pow, hζ, inv_one, mul_one]
    rw [this, map_div₀, hσe, hσb, div_self (div_ne_zero (hα ▸ pow_ne_zero _ hα0)
      (hβ ▸ pow_ne_zero _ hβ0))]
  have hw'A : A.valuation w' = 1 := by
    have : w' = (w' - 1) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rw [map_one]; exact hwζ), map_one]
  have hρ1 : A.valuation (σ w' / w' - 1) < 1 := by
    have e1 : σ w' / w' - 1 = (σ (w' - 1) - (w' - 1)) * w'⁻¹ := by
      rw [map_sub, map_one]; field_simp; ring
    rw [e1, map_mul, map_inv₀, hw'A, inv_one, mul_one]
    exact Valuation.map_sub_lt _ (valuation_lt_one_map σ hσA hwζ) hwζ
  have hρ := eq_one_of_pow_eq_one hk hn hρn hρ1
  have hσw' : σ w' = w' := by
    rw [div_eq_one_iff_eq hw'0] at hρ; exact hρ
  have hα' : α = β * ζ * w' := by rw [hw']; field_simp
  have hσα : σ α = σ β * σ ζ * w' := by rw [hα', map_mul, map_mul, hσw']
  rw [hσα, hα']
  have hσζ0 : σ ζ ≠ 0 := (_root_.map_ne_zero σ).2 hζ0
  field_simp

end Place

/-! ### The theta class on decomposition groups of points -/

section Point

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {ht : Transcendental k t}
  [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω]
  {LX : IntermediateField (K₀ k t) Ω} {hLX : IsOpen (LX.fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  {O : ValuationSubring k} {V : ValuationSubring Ω} {hV : V.comap (algebraMap k Ω) = O}
  {T : TemperedFundamentalGroups.TateObject.Data O (fieldData ht LX hLX).R}
  {L : ℕ → IntermediateField (K₀ k t) Ω}
  {hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ k t] Ω))}
  [hX : ∀ j, Fact (LX ≤ L j)]
  [het : ∀ j, Algebra.Etale (fieldData ht LX hLX).R (fieldData ht (L j) (hL j)).R]
  (η : ∀ j, units (fieldData ht (L j) (hL j)))

/-- **[EtTh] Prop. 1.4(iii) on decomposition groups, tempered, at the level `j`**: let `A` be a
place of `Ω` over a `k`-rational point of `Ÿ'_{N_j}` (`k ⊆ A`, residue field algebraic over `k`)
at which `η_j` is integral with residue `b ∈ k^×`, and let the base point `V ≤ A` lie over `O`.
Then every representative `c` of `classAt η j n` is, on the decomposition group
`{σ ∈ D_V | σ fixes L 0 and L j}`, the Kummer cocycle `σ ↦ σβ/β` of an `n`-th root `β` of `b`,
up to a coboundary `σ ↦ σζ/ζ` (`ζ^n = 1`). -/
theorem classAt_place (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (c : ContH1.cocycles (piYddotX V hV T hL) (Mu n Ω))
    (hc : ContH1.mk c = classAt η hC1 j n)
    (A : ValuationSubring Ω) (hVA : V ≤ A) (hk : ∀ a : k, algebraMap k Ω a ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (b : k) (hb : b ≠ 0)
    (hηA : (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω) ∈ A)
    (hres : residue A ⟨_, hηA⟩ = residue A ⟨_, hk b⟩) :
    ∃ (β ζ : Ω), β ^ n = algebraMap k Ω b ∧ β ≠ 0 ∧ ζ ^ n = 1 ∧ ζ ≠ 0 ∧
      ∀ (σ : decompositionGroup (fieldData ht LX hLX).R V)
        (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
        (_ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
        ((Mu.val (c ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩) : Ωˣ) : Ω) =
          (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) β / β *
            ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) ζ / ζ) := by
  obtain ⟨α, hαn, hα0, M, hM⟩ := classAt_galois η hC1 j n c hc
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap k Ω b) n
  have hb' : algebraMap k Ω b ≠ 0 := (_root_.map_ne_zero _).2 hb
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hβ; exact hb' hβ.symm
  -- `η_j ≡ b mod 𝔪_A`
  have heb : A.valuation ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) :
      F (fieldData ht (L j) (hL j))) : Ω) / algebraMap k Ω b - 1) < 1 := by
    have hsub : residue A ⟨_, sub_mem hηA (hk b)⟩ = 0 := by
      rw [show (⟨_, sub_mem hηA (hk b)⟩ : A) = ⟨_, hηA⟩ - ⟨_, hk b⟩ from rfl, map_sub, hres,
        sub_self]
    have h1 := (A.valuation_lt_one_iff ⟨_, sub_mem hηA (hk b)⟩).1 ((residue_eq_zero_iff _).1 hsub)
    have hbinv : A.valuation (algebraMap k Ω b)⁻¹ = 1 :=
      valuation_eq_one_of_mem (by rw [← map_inv₀]; exact hk _) (by rw [inv_inv]; exact hk b)
        (inv_ne_zero hb')
    have e : (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω) /
        algebraMap k Ω b - 1 = ((((η j : (F (fieldData ht (L j) (hL j)))ˣ) :
          F (fieldData ht (L j) (hL j))) : Ω) - algebraMap k Ω b) * (algebraMap k Ω b)⁻¹ := by
      field_simp
    rw [e, map_mul, hbinv, mul_one]
    exact h1
  obtain ⟨ζ₀, hζ₀n, hζ₀0, hK⟩ := exists_kummer_close hk hn hαn hβ hα0 hβ0 heb
  have hMn : (Mu.val M : Ω) ^ n = 1 := by
    have := congrArg (fun z : Ωˣ => (z : Ω)) (Mu.val_pow_n M)
    simpa using this
  have hM0 := (Mu.val M).ne_zero
  refine ⟨β, ζ₀ * (Mu.val M : Ω), hβ, hβ0, by rw [mul_pow, hζ₀n, hMn, one_mul],
    mul_ne_zero hζ₀0 hM0, fun σ hσ0 hσj => ?_⟩
  have hmul : ∀ x ∈ A, ∃ a : k, a ≠ 0 ∧ algebraMap k Ω a * x ∈ V := fun x hx => by
    obtain ⟨p, hp, hpx⟩ := exists_monic_lt_one hk hint hx
    exact exists_mul_mem hVA hV hk hx hp hpx
  have hσk : ∀ a : k, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv (algebraMap k Ω a) =
      algebraMap k Ω a := fun a => by
    change (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) (algebraMap k Ω a) = algebraMap k Ω a
    rw [IsScalarTower.algebraMap_apply k (fieldData ht LX hLX).R Ω]
    exact (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).commutes _
  have hσV : ∀ x, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv x ∈ V ↔ x ∈ V := σ.2
  have hσA := mem_place_iff hVA hk hmul _ hσk hσV
  have hσe : (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv
      (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω) =
      (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω) :=
    (IntermediateField.mem_fixedField_iff _ _).1
      ((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))).2 _
      (galoisToH (D := fieldData ht (L j) (hL j))
        (decompLevel hL j σ hσj : Ω ≃ₐ[(fieldData ht (L j) (hL j)).R] Ω)).2
  have h := hK _ hσA hσe (hσk b)
  rw [hM σ hσ0 hσj]
  change _ = (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv β / β * _
  change (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv α / α * _ = _
  rw [h]
  change _ = _ * ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv (ζ₀ * (Mu.val M : Ω)) / _)
  rw [map_mul]
  have hσζ0 : (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv ζ₀ ≠ 0 :=
    (_root_.map_ne_zero _).2 hζ₀0
  change _ * ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).toRingEquiv (Mu.val M : Ω) / _) = _
  field_simp

/-- `classAt_place` for a residue `b·g^n` (`g ∈ k^×`): the Kummer cocycle of `b`. -/
theorem classAt_place_mul (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n]
    (c : ContH1.cocycles (piYddotX V hV T hL) (Mu n Ω))
    (hc : ContH1.mk c = classAt η hC1 j n)
    (A : ValuationSubring Ω) (hVA : V ≤ A) (hk : ∀ a : k, algebraMap k Ω a ∈ A)
    (hint : letI := resAlg A hk; Algebra.IsIntegral k (ResidueField A))
    (b g : k) (hb : b ≠ 0) (hg : g ≠ 0)
    (hηA : (((η j : (F (fieldData ht (L j) (hL j)))ˣ) : F (fieldData ht (L j) (hL j))) : Ω) ∈ A)
    (hres : residue A ⟨_, hηA⟩ = residue A ⟨_, hk (b * g ^ n)⟩) :
    ∃ (β ζ : Ω), β ^ n = algebraMap k Ω b ∧ β ≠ 0 ∧ ζ ^ n = 1 ∧ ζ ≠ 0 ∧
      ∀ (σ : decompositionGroup (fieldData ht LX hLX).R V)
        (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
        (_ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
        ((Mu.val (c ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩) : Ωˣ) : Ω) =
          (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) β / β *
            ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) ζ / ζ) := by
  obtain ⟨β', ζ, hβ', hβ'0, hζ, hζ0, H⟩ := classAt_place η hC1 j n c hc A hVA hk hint (b * g ^ n)
    (mul_ne_zero hb (pow_ne_zero _ hg)) hηA hres
  have hg' : algebraMap k Ω g ≠ 0 := (_root_.map_ne_zero _).2 hg
  refine ⟨β' / algebraMap k Ω g, ζ, ?_, div_ne_zero hβ'0 hg', hζ, hζ0, fun σ hσ0 hσj => ?_⟩
  · rw [div_pow, hβ', ← map_pow, ← map_div₀, mul_div_cancel_right₀ _ (pow_ne_zero _ hg)]
  rw [H σ hσ0 hσj, map_div₀]
  have hσg : (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) (algebraMap k Ω g) = algebraMap k Ω g := by
    rw [IsScalarTower.algebraMap_apply k (fieldData ht LX hLX).R Ω]
    exact (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω).commutes _
  rw [hσg]
  have hσβ : (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) β' ≠ 0 := (_root_.map_ne_zero _).2 hβ'0
  field_simp


variable (V hV T hL) in
/-- **The tempered theta class at a point** (a `Prop` def used only as a conclusion, like
`EtaleThetaAtPoint`): every representative `c` of `classAt η j n` is, on the Galois elements
`σ ∈ D_V` fixing `L 0` and `L j`, the Kummer cocycle `σ ↦ σβ/β` of an `n`-th root `β` of `b`,
up to a coboundary `σ ↦ σζ/ζ`. -/
def ClassAtPoint (hC1 : LevelsDominated V hV T hL) (j n : ℕ) [NeZero n] (b : k) : Prop :=
  ∀ c : ContH1.cocycles (piYddotX V hV T hL) (Mu n Ω), ContH1.mk c = classAt η hC1 j n →
    ∃ (β ζ : Ω), β ^ n = algebraMap k Ω b ∧ β ≠ 0 ∧ ζ ^ n = 1 ∧ ζ ≠ 0 ∧
      ∀ (σ : decompositionGroup (fieldData ht LX hLX).R V)
        (hσ0 : ∀ x ∈ L 0, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x)
        (_ : ∀ x ∈ L j, (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) x = x),
        ((Mu.val (c ⟨_, galoisToTempered_mem_piYddotX V hV T hL σ hσ0⟩) : Ωˣ) : Ω) =
          (σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) β / β *
            ((σ : Ω ≃ₐ[(fieldData ht LX hLX).R] Ω) ζ / ζ)

end Point

/-! ### The concrete system: the class at Tate points -/

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

local notation "Ω" => FFClosure (curveE t.tateCurve)
local notation "τ" => coordT (xN t.tateCurve)

section Main

variable [t.tateCurve.IsElliptic] (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
  (hs : s ^ 2 = t.q) (O : ValuationSubring K) (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)

set_option maxHeartbeats 2000000 in
-- destructuring `exists_etaleThetaSystem` (concrete Tate-curve levels) is slow to unify
include h2 in
/-- **The tempered étale theta class at Tate points** ([EtTh] Prop. 1.4(iii), ET l.1334–1347,
tempered form, under C1): for the system of `exists_thetaClassTemp`, every Tate point `u`
(`u` off the `q`-orbits of the cusps, `ψ_{4N}(u) ≠ 0`, `N = N_j = 2(j+1)`) has a `K`-rational
point `x` of `Ÿ'_N` over it (residues of the functions on `L_{2N}` are their values at `u`); for
every base point `V ≤ x.A` over `O` (such `V` exist) and every `n ∣ N`, every representative `c`
of `classAt η j n` (`= thetaClassTemp η n` by `ThetaClassCompatible`) is, on the decomposition
group `{σ ∈ D_V | σ fixes L 0, L j}` of the point, the Kummer cocycle `σ ↦ σβ/β` of an `n`-th
root `β` of `Θ̈(u^N)`, up to a coboundary (`ClassAtPoint`). -/
theorem exists_thetaClassTemp_points :
    ∃ (L : ℕ → IntermediateField (K₀ K τ) Ω)
      (hL : ∀ j, IsOpen ((L j).fixingSubgroup : Set (Ω ≃ₐ[K₀ K τ] Ω)))
      (_ : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j))
      (_ : ∀ j, Algebra.Etale (DX t).R (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R)
      (η : ∀ j, units (fieldData (transcendental_tau t.tateCurve) (L j) (hL j))),
      ThetaTransitions (transcendental_tau t.tateCurve) hL η ∧
      (∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O),
        ThetaClassCompatible (ht := transcendental_tau t.tateCurve)
          (LX := (hemiData t.tateCurve).L) (hLX := hemiL_open t) V hV (tateDataX O hO hs h12) η) ∧
      ∀ (j : ℕ) (u : Kˣ) (hu : OffOrbit t u)
        (hψ : evalTate t h12 hu (psiN t.tateCurve (2 * (2 * (j + 1)))) ≠ 0),
        etaleTheta t (u ^ (2 * (j + 1))) ≠ 0 ∧
        ∃ (x : RatPoint (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)))
          (hmem : ∀ b : coverRingN t.tateCurve (2 * (2 * (j + 1))),
            mulByNEmb t.tateCurve (2 * (2 * (j + 1))) (algebraMap _ _ b) ∈ x.A),
          (∀ b : coverRingN t.tateCurve (2 * (2 * (j + 1))), residue x.A ⟨_, hmem b⟩ =
            algebraMap K (ResidueField x.A) (evalCover (2 * (2 * (j + 1))) hu hψ b)) ∧
          (∃ V : ValuationSubring Ω, V ≤ x.A ∧ V.comap (algebraMap K Ω) = O) ∧
          ∀ (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O), V ≤ x.A →
          ∀ (hC1 : LevelsDominated V hV (tateDataX O hO hs h12) hL) (n : ℕ) [NeZero n],
            n ∣ 2 * (j + 1) →
            ClassAtPoint V hV (tateDataX O hO hs h12) hL η hC1 j n
              (etaleTheta t (u ^ (2 * (j + 1)))) := by
  obtain ⟨L, hL, h₁, η, het, -, hval, -, htr, -⟩ := exists_etaleThetaSystem h2 h12 hs
  haveI hX : ∀ j, Fact ((hemiData t.tateCurve).L ≤ L j) := fun j => ⟨h₁ j⟩
  haveI het' : ∀ j, Algebra.Etale (DX t).R
      (fieldData (transcendental_tau t.tateCurve) (L j) (hL j)).R := fun j =>
    etale_fieldData (transcendental_tau t.tateCurve) (hemiL_open t) (L j) (hL j) (het j)
  refine ⟨L, hL, hX, het', η, htr, fun V hV => thetaClassCompatible_tate h12 hs O hO V hV htr,
    fun j u hu hψ => ?_⟩
  obtain ⟨hU, x, hmem, hηA, hresb, hres⟩ := hval j u hu hψ
  refine ⟨hU, x, hmem, hresb, exists_le_comap_eq x.A x.hk O,
    fun V hV hVA hC1 n _ hn c hc => ?_⟩
  obtain ⟨d, hd⟩ := hn
  have hN : 0 < 2 * (j + 1) := by omega
  have hg := etaleTheta_tatePow_ne_zero t (2 * (j + 1)) hN hU
  have hf : thetaLevel t (2 * (j + 1)) hN (u ^ (2 * (j + 1))) = etaleTheta t (u ^ (2 * (j + 1))) *
      ((etaleTheta (tatePow t (2 * (j + 1)) hN) (u ^ (2 * (j + 1))) ^ d)⁻¹) ^ n := by
    unfold thetaLevel
    rw [inv_pow, ← pow_mul, mul_comm d n, ← hd, div_eq_mul_inv]
  exact classAt_place_mul η hC1 j n c hc x.A hVA x.hk x.isIntegral _ _ hU
    (inv_ne_zero (pow_ne_zero _ hg)) hηA (by rw [hres, hf]; rfl)

end Main

end Iut.EtaleTheta
