/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.HemiPi1
import CurvesJacobian.Cusp.EllipticMulByN
import Pi1.Orbicurve.EtaleInertia
import Pi1.Orbicurve.BaseChange
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.TranslationDoublingCommGeneral

/-!
# The cover `[m] : E ∖ E[m] → E ∖ {O}` inside `Ω = K(E)^alg` (MR14, G1 step 2)

Let `E` be an elliptic curve over a field `K` of characteristic `0`, `Ω = K(Ē)^alg`, `τ = x` the
Weierstrass coordinate, and `hemiData E` the Galois data of `curves-jacobian` whose function field
`L_X = (hemiData E).L` is `K(E) ⊆ Ω` (embedded by `embE`), with coordinate ring `K[E]`. We embed
the source of `[m]` into `Ω`:

* `pb E m = [m]^* : K(E) → K(E)` (`elliptic-curves`' `mulByNEndoAlgHom`), with the composition
  law `pb_mul : [a·b]^* = [a]^* ∘ [b]^*`;
* `mulByNEmb E m : K(E) →ₐ[K] Ω` with `mulByNEmb ∘ [m]^* = embE` (`mulByNEmb_comp_pb`,
  `mulByNEmb_mulByNHom`): `K(E)` is algebraic over `[m]^* K(E)` and `Ω` is algebraically closed.
  The embeddings are **compatible in `m`** (`mulByNEmb_comp_pb_mul`:
  `mulByNEmb (r·m) ∘ [r]^* = mulByNEmb m`): they are read off one tower `chainEmb` of embeddings
  of the sources of `[(k+1)!]`, `e_{k+1} ∘ [k+2]^* = e_k`;
* `mulByNField E m`: its image `L_m`, an intermediate field of `Ω / K(τ)` containing `L_X`
  (`hemiL_le_mulByNField`), whose coordinate ring (the integral closure of `K[τ]`) is the image of
  `K[E][1/ψ_m]` (`mem_coordRing_mulByNField_iff`);
* **`etale_mulByNField`**: `coordRing L_X → coordRing L_m` is étale — the finite étale map
  `[m]^* : K[E] → K[E][1/ψ_m]` of `curves-jacobian` (`isFiniteEtale_spec_mulByNHom`);
* **`etale_of_le_mulByNField`**: hence, by `pi1`'s inertia criterion
  (`AffOrbicurve.etale_iff_inertia`), every intermediate field `L_X ≤ L' ≤ L_m` gives an étale
  `coordRing L_X → coordRing L'`. This is how the level `Ÿ'_N` of the étale theta function
  (`L' = ψ^*K(E_Q)` with `m = 2N`) is shown to be étale over `X = E ∖ {O}`.
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open IntermediateField AffOrbicurve

noncomputable section

universe u

namespace CurvesJacobian.Cusp

variable {K : Type u} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

local notation "CR" => E.toAffine.CoordinateRing
local notation "FF" => E.toAffine.FunctionField
local notation "Ω" => FFClosure (curveE E)
local notation "τ" => coordT (xN E)

/-- `K[E] ⊆ K(E) ↪ Ω`. -/
def rhoA : CR →+* Ω := (embE E).toRingHom.comp (algebraMap CR FF)

lemma rhoA_injective : Function.Injective (rhoA E) :=
  (embE E).toRingHom.injective.comp (IsFractionRing.injective CR FF)

lemma mem_hemiL_iff (z : Ω) : z ∈ (hemiData E).L ↔ ∃ f : FF, embE E f = z := by
  constructor
  · intro hz
    refine ⟨funFieldEquivE E ((hemiEquivL E).symm ⟨z, hz⟩), ?_⟩
    change algebraMap _ _ ((funFieldEquivE E).symm (funFieldEquivE E _)) = z
    rw [RingEquiv.symm_apply_apply, ← hemiEquivL_apply, RingEquiv.apply_symm_apply]
  · rintro ⟨f, rfl⟩
    change algebraMap _ _ ((funFieldEquivE E).symm f) ∈ (hemiData E).L
    rw [← hemiEquivL_apply]
    exact SetLike.coe_mem _

/-- `K[E] ≅ R` of `hemiData E` is compatible with `embE`. -/
lemma algebraMap_hemiREquiv' (a : CR) :
    algebraMap (hemiData E).R Ω (hemiREquiv E a) = embE E (algebraMap CR FF a) := by
  change algebraMap (hemiData E).R Ω
    (sectionsXEHemiAlgEquiv E ((sectionsXEAlgEquiv E).symm a)) = _
  rw [algebraMap_sectionsXEHemiAlgEquiv]
  have h := funFieldEquivE_germ E ((sectionsXEAlgEquiv E).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  change _ = algebraMap _ _ ((funFieldEquivE E).symm (algebraMap CR FF a))
  rw [← h, RingEquiv.symm_apply_apply]

lemma isIntegral_rhoA (a : CR) : IsIntegral (A₀ K (coordT (xN E))) (rhoA E a) := by
  have := CoordRing.isIntegral_algebraMap (hemiREquiv E a)
  rwa [algebraMap_hemiREquiv'] at this

/-! ### `[m]^*` on `K(E)` and a compatible system of embeddings -/

section Pullback

/-- **`[m]^* : K(E) → K(E)`**, `elliptic-curves`' pullback along `P ↦ m • P`
(`mulByNEndoAlgHom`). -/
def pb (m : ℕ) [NeZero m] : FF →ₐ[K] FF :=
  WeierstrassCurve.Affine.CoordinateRing.mulByNEndoAlgHom (W := E.toAffine) m (transcendental_N E m)

/-- `cj`'s `[m]^* : K[E] → K[E][1/ψ_m]` is `pb m` on `K[E] ⊆ K(E)`. -/
lemma algebraMap_mulByNHom_eq_pb (m : ℕ) [NeZero m] (a : CR) :
    algebraMap (coverRingN E m) FF (mulByNHom E m a) = pb E m (algebraMap CR FF a) :=
  algebraMap_mulByNHom E m a

lemma genPointHom_pb (m : ℕ) [NeZero m] :
    WeierstrassCurve.Affine.CoordinateRing.genPointHom (pb E m)
        WeierstrassCurve.Affine.CoordinateRing.genericPoint =
      m • WeierstrassCurve.Affine.CoordinateRing.genericPoint (W := E.toAffine) :=
  (WeierstrassCurve.Affine.CoordinateRing.nsmul_genericPoint_eq m (transcendental_N E m)).symm

/-- **The composition law** `[a·b]^* = [a]^* ∘ [b]^*` (through the generic point, as in
`elliptic-curves`' `mulByNEndoAlgHom_mul`). -/
lemma pb_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    pb E (a * b) = (pb E a).comp (pb E b) := by
  refine WeierstrassCurve.Affine.CoordinateRing.algHom_ext_of_genPointHom ?_
  rw [← WeierstrassCurve.Affine.CoordinateRing.genPointHom_comp, genPointHom_pb, genPointHom_pb,
    map_nsmul, genPointHom_pb, smul_smul, mul_comm]

lemma pb_one : pb E 1 = AlgHom.id K FF := by
  refine WeierstrassCurve.Affine.CoordinateRing.algHom_ext_of_genPointHom ?_
  rw [genPointHom_pb, one_smul]
  rfl

lemma pb_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) : pb E a = pb E b := by
  subst h; rfl

lemma pb_comp_pb (a b c : ℕ) [NeZero a] [NeZero b] [NeZero c] (h : a * b = c) :
    (pb E a).comp (pb E b) = pb E c := by
  haveI : NeZero (a * b) := ⟨by rw [h]; exact NeZero.ne c⟩
  rw [← pb_mul, pb_congr E h]

/-- `K(E)` is integral over `[m]^*K(E)` on `K[E][1/ψ_m]`. -/
lemma isIntegral_pb (m : ℕ) [NeZero m] (b : coverRingN E m) :
    IsIntegral (pb E m).fieldRange (algebraMap (coverRingN E m) FF b) := by
  obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := CR) (toMulByNB E m b)
  let ρ : CR →+* (pb E m).fieldRange :=
    ((pb E m).toRingHom.comp (algebraMap CR FF)).codRestrict
      (pb E m).fieldRange.toSubfield.toSubring fun a => ⟨_, rfl⟩
  let g : MulByNB E m →+* FF :=
    (algebraMap (coverRingN E m) FF).comp (toMulByNB E m).symm.toRingEquiv.toRingHom
  have hg : (algebraMap (pb E m).fieldRange FF).comp ρ =
      g.comp (algebraMap CR (MulByNB E m)) := by
    refine RingHom.ext fun a => ?_
    change pb E m (algebraMap CR FF a) = algebraMap (coverRingN E m) FF ((toMulByNB E m).symm
      (algebraMap CR (MulByNB E m) a))
    rw [algebraMap_mulByNB, AlgEquiv.symm_apply_apply, algebraMap_mulByNHom_eq_pb]
  have hb : algebraMap (coverRingN E m) FF b = g (toMulByNB E m b) := by
    change _ = algebraMap (coverRingN E m) FF ((toMulByNB E m).symm (toMulByNB E m b))
    rw [AlgEquiv.symm_apply_apply]
  refine ⟨p.map ρ, hp.map ρ, ?_⟩
  rw [eval₂_map, hg, hb, ← Polynomial.hom_eval₂, hpb, map_zero]

instance isAlgebraic_pb (m : ℕ) [NeZero m] : Algebra.IsAlgebraic (pb E m).fieldRange FF := by
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := coverRingN E m) z
  rw [div_eq_mul_inv]
  exact (isIntegral_pb E m a).isAlgebraic.mul (isIntegral_pb E m b).isAlgebraic.inv

/-- **Extending an embedding of `K(E)` along `[r]^*`** (`Ω` is algebraically closed and `K(E)`
is algebraic over `[r]^*K(E)`). -/
lemma exists_extend (r : ℕ) [NeZero r] (e : FF →ₐ[K] Ω) :
    ∃ e' : FF →ₐ[K] Ω, e'.comp (pb E r) = e := by
  let iso : FF ≃ₐ[K] (pb E r).fieldRange := AlgEquiv.ofInjectiveField (pb E r)
  let f : (pb E r).fieldRange →+* Ω := e.toRingHom.comp iso.symm.toRingEquiv.toRingHom
  letI : Algebra (pb E r).fieldRange Ω := f.toAlgebra
  haveI : Module.IsTorsionFree (pb E r).fieldRange FF :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap (pb E r).fieldRange FF).injective
  haveI : Module.IsTorsionFree (pb E r).fieldRange Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr f.injective
  let g : FF →ₐ[(pb E r).fieldRange] Ω := IsAlgClosed.lift
  have hg : ∀ z : FF, g (pb E r z) = e z := fun z => by
    have h := g.commutes (iso z)
    change g (pb E r z) = f (iso z) at h
    rw [h]
    change e (iso.symm (iso z)) = e z
    rw [AlgEquiv.symm_apply_apply]
  refine ⟨{ g.toRingHom with commutes' := fun c => ?_ }, AlgHom.ext fun z => hg z⟩
  have h := hg (algebraMap K FF c)
  rw [AlgHom.commutes, AlgHom.commutes] at h
  exact h

/-- The extension of `e` along `[r]^*` (a choice). -/
def extendEmb (r : ℕ) [NeZero r] (e : FF →ₐ[K] Ω) : FF →ₐ[K] Ω :=
  (exists_extend E r e).choose

lemma extendEmb_comp (r : ℕ) [NeZero r] (e : FF →ₐ[K] Ω) :
    (extendEmb E r e).comp (pb E r) = e :=
  (exists_extend E r e).choose_spec

/-- **The tower of embeddings** `e_k` of the source of `[(k+1)!]` into `Ω`:
`e_0 = embE`, `e_{k+1} ∘ [k+2]^* = e_k`. -/
def chainEmb : ℕ → (FF →ₐ[K] Ω)
  | 0 => embE E
  | k + 1 => extendEmb E (k + 2) (chainEmb k)

instance neZero_factorial (k : ℕ) : NeZero k.factorial := ⟨Nat.factorial_ne_zero _⟩

lemma chainEmb_comp_pb (k : ℕ) : (chainEmb E k).comp (pb E (k + 1).factorial) = embE E := by
  induction k with
  | zero =>
    change (embE E).comp (pb E 1) = embE E
    rw [pb_one]; rfl
  | succ k ih =>
    rw [← pb_comp_pb E (k + 2) (k + 1).factorial _ (Nat.factorial_succ (k + 1)).symm,
      ← AlgHom.comp_assoc]
    change ((extendEmb E (k + 2) (chainEmb E k)).comp (pb E (k + 2))).comp _ = _
    rw [extendEmb_comp, ih]

lemma factorial_div_pos (k j : ℕ) : 0 < (k + j + 1).factorial / (k + 1).factorial :=
  Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos _)

lemma chainEmb_comp_pb_le (k j : ℕ) :
    haveI : NeZero ((k + j + 1).factorial / (k + 1).factorial) :=
      ⟨(factorial_div_pos k j).ne'⟩
    (chainEmb E (k + j)).comp (pb E ((k + j + 1).factorial / (k + 1).factorial)) =
      chainEmb E k := by
  induction j with
  | zero =>
    haveI : NeZero ((k + 0 + 1).factorial / (k + 1).factorial) := ⟨(factorial_div_pos k 0).ne'⟩
    rw [pb_congr E (Nat.div_self (Nat.factorial_pos _)), pb_one]; rfl
  | succ j ih =>
    haveI : NeZero ((k + j + 1).factorial / (k + 1).factorial) :=
      ⟨(factorial_div_pos k j).ne'⟩
    haveI : NeZero ((k + (j + 1) + 1).factorial / (k + 1).factorial) :=
      ⟨(factorial_div_pos k (j + 1)).ne'⟩
    have hf : (k + (j + 1) + 1).factorial = (k + j + 2) * (k + j + 1).factorial :=
      Nat.factorial_succ (k + j + 1)
    have e : (k + j + 2) * ((k + j + 1).factorial / (k + 1).factorial) =
        (k + (j + 1) + 1).factorial / (k + 1).factorial := by
      rw [hf, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by omega))]
    rw [← pb_comp_pb E _ _ _ e, ← AlgHom.comp_assoc]
    change ((extendEmb E (k + j + 2) (chainEmb E (k + j))).comp (pb E (k + j + 2))).comp _ = _
    rw [extendEmb_comp, ih]

lemma chainEmb_comp_pb_le' (k n : ℕ) (h : k ≤ n)
    [NeZero ((n + 1).factorial / (k + 1).factorial)] :
    (chainEmb E n).comp (pb E ((n + 1).factorial / (k + 1).factorial)) = chainEmb E k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact chainEmb_comp_pb_le E k j

variable (m : ℕ) [NeZero m]

/-- The cofactor `(m+1)!/m` with `[(m+1)!] = [cof m] ∘ [m]`. -/
def cof : ℕ := (m + 1).factorial / m

lemma cof_mul : cof m * m = (m + 1).factorial :=
  Nat.div_mul_cancel (Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne m)) (by omega))

instance : NeZero (cof m) := ⟨fun h => by
  have := cof_mul m
  rw [h, zero_mul] at this
  exact Nat.factorial_ne_zero _ this.symm⟩

/-- **The source of `[m]` in `Ω`**: `K(E) ↪ Ω` with `[m]^* f ↦ embE f`. The embeddings are
chosen compatibly in `m` (`mulByNEmb_comp_pb`): `mulByNEmb m = e_m ∘ [(m+1)!/m]^*` for the
tower `chainEmb`. -/
def mulByNEmb : FF →ₐ[K] Ω := (chainEmb E m).comp (pb E (cof m))

/-- `mulByNEmb ∘ [m]^* = embE` on `K(E)`. -/
lemma mulByNEmb_comp_pb : (mulByNEmb E m).comp (pb E m) = embE E := by
  rw [mulByNEmb, AlgHom.comp_assoc, pb_comp_pb E _ _ _ (cof_mul m), chainEmb_comp_pb]

/-- `mulByNEmb ∘ [m]^* = embE` on `K[E]`. -/
lemma mulByNEmb_mulByNHom (a : CR) :
    mulByNEmb E m (algebraMap (coverRingN E m) FF (mulByNHom E m a)) =
      embE E (algebraMap CR FF a) := by
  rw [algebraMap_mulByNHom_eq_pb, ← AlgHom.comp_apply, mulByNEmb_comp_pb]

/-- **Compatibility of the embeddings in `m`**: `mulByNEmb (r·m) ∘ [r]^* = mulByNEmb m` (the
source of `[r·m]` maps to the source of `[m]` by `[r]`). -/
lemma mulByNEmb_comp_pb_mul (r : ℕ) [NeZero r] [NeZero (r * m)] :
    (mulByNEmb E (r * m)).comp (pb E r) = mulByNEmb E m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hle : m ≤ r * m := Nat.le_mul_of_pos_left m hr
  have hA : 0 < (r * m + 1).factorial / (m + 1).factorial :=
    Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos _)
  haveI : NeZero ((r * m + 1).factorial / (m + 1).factorial) := ⟨hA.ne'⟩
  haveI : NeZero (cof (r * m) * r) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne r)⟩
  haveI : NeZero ((r * m + 1).factorial / (m + 1).factorial * cof m) :=
    ⟨mul_ne_zero hA.ne' (NeZero.ne _)⟩
  have e : cof (r * m) * r = (r * m + 1).factorial / (m + 1).factorial * cof m := by
    refine Nat.eq_of_mul_eq_mul_right hm ?_
    rw [mul_assoc, cof_mul (r * m), mul_assoc, cof_mul m,
      Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by omega))]
  rw [mulByNEmb, mulByNEmb, AlgHom.comp_assoc,
    pb_comp_pb E (cof (r * m)) r (cof (r * m) * r) rfl, pb_congr E e,
    ← pb_comp_pb E ((r * m + 1).factorial / (m + 1).factorial) (cof m) _ rfl,
    ← AlgHom.comp_assoc, chainEmb_comp_pb_le' E m (r * m) hle]

/-- Elements of `K[E][1/ψ_m]` are integral over `K[τ]` in `Ω`. -/
lemma isIntegral_mulByNEmb' (b : coverRingN E m) :
    IsIntegral (A₀ K (coordT (xN E))) (mulByNEmb E m (algebraMap (coverRingN E m) FF b)) := by
  obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := CR) (toMulByNB E m b)
  let T := integralClosure (A₀ K (coordT (xN E))) Ω
  have hT : ∀ a : CR, rhoA E a ∈ T := isIntegral_rhoA E
  let r : CR →+* T := (rhoA E).codRestrict T.toSubring hT
  let g : MulByNB E m →+* Ω := (mulByNEmb E m).toRingHom.comp
    ((algebraMap (coverRingN E m) FF).comp (toMulByNB E m).symm.toRingEquiv.toRingHom)
  have hrr : (algebraMap T Ω).comp r = g.comp (algebraMap CR (MulByNB E m)) := by
    refine RingHom.ext fun a => ?_
    change rhoA E a = mulByNEmb E m (algebraMap (coverRingN E m) FF ((toMulByNB E m).symm
      (algebraMap CR (MulByNB E m) a)))
    rw [algebraMap_mulByNB, AlgEquiv.symm_apply_apply, mulByNEmb_mulByNHom]
    rfl
  have hb : mulByNEmb E m (algebraMap (coverRingN E m) FF b) = g (toMulByNB E m b) := by
    change _ = mulByNEmb E m (algebraMap (coverRingN E m) FF
      ((toMulByNB E m).symm (toMulByNB E m b)))
    rw [AlgEquiv.symm_apply_apply]
  have hint : IsIntegral T (mulByNEmb E m (algebraMap (coverRingN E m) FF b)) := by
    refine ⟨p.map r, hp.map r, ?_⟩
    rw [eval₂_map, hrr, hb, ← Polynomial.hom_eval₂, hpb, map_zero]
  exact isIntegral_trans _ hint

end Pullback

variable (m : ℕ) [NeZero m]

/-! ### The intermediate field `L_m = mulByNEmb(K(E))` -/

section Galois

local notation "φ" => mulByNEmb E m
local notation "ι" => algebraMap (coverRingN E m) FF

lemma transcendental_tau : Transcendental K τ := (hemiData E).transcendental

lemma tau_eq : φ (ι (mulByNHom E m (xE E))) = τ := by
  rw [mulByNEmb_mulByNHom, ← embE_genX]; rfl

lemma K₀_le_fieldRange : K₀ K τ ≤ (mulByNEmb E m).fieldRange := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact ⟨_, tau_eq E m⟩

/-- **`L_m`**: the image of the source `K(E)` of `[m]` in `Ω`, over `K(τ)`. -/
def mulByNField : IntermediateField (K₀ K τ) Ω :=
  (mulByNEmb E m).fieldRange.toSubfield.toIntermediateField fun x =>
    K₀_le_fieldRange E m x.2

lemma mem_mulByNField_iff (z : Ω) : z ∈ mulByNField E m ↔ ∃ f : FF, φ f = z := Iff.rfl

lemma hemiL_le_mulByNField : (hemiData E).L ≤ mulByNField E m := by
  intro z hz
  obtain ⟨f, rfl⟩ := (mem_hemiL_iff E z).mp hz
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
  refine ⟨ι (mulByNHom E m a) / ι (mulByNHom E m b), ?_⟩
  change φ _ = _
  rw [map_div₀, map_div₀, mulByNEmb_mulByNHom, mulByNEmb_mulByNHom]

/-- `K[τ] ≅ K[X] → K[E][1/ψ_m]`, `τ ↦ [m]^*x`. -/
def liftA₀ : A₀ K τ →ₐ[K] coverRingN E m :=
  (aeval (mulByNHom E m (xE E))).comp
    (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E)).symm.toAlgHom

lemma liftA₀_spec (c : A₀ K τ) : φ (ι (liftA₀ E m c)) = c := by
  obtain ⟨p, rfl⟩ := (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E)).surjective c
  have e : liftA₀ E m (Polynomial.algEquivOfTranscendental K τ (transcendental_tau E) p) =
      aeval (mulByNHom E m (xE E)) p := by
    simp [liftA₀]
  rw [e, coe_algEquivOfTranscendental (transcendental_tau E) p, ← tau_eq E m]
  exact (Polynomial.aeval_algHom_apply
    ((mulByNEmb E m).comp (IsScalarTower.toAlgHom K (coverRingN E m) FF)) _ p).symm

lemma isIntegral_mulByNEmb (b : coverRingN E m) : IsIntegral (A₀ K τ) (φ (ι b)) :=
  isIntegral_mulByNEmb' E m b

lemma exists_of_isIntegral {f : FF} (hf : IsIntegral (A₀ K τ) (φ f)) :
    ∃ b : coverRingN E m, ι b = f := by
  haveI : IsIntegrallyClosed (coverRingN E m) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (psiN E m))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (psiN_ne_zero_of_neZero E m))
  obtain ⟨p, hp, hpf⟩ := hf
  have hint : IsIntegral (coverRingN E m) f := by
    refine ⟨p.map (liftA₀ E m).toRingHom, hp.map _, ?_⟩
    apply (mulByNEmb E m).toRingHom.injective
    rw [map_zero, Polynomial.hom_eval₂, eval₂_map, ← hpf]
    congr 1
    ext c
    exact liftA₀_spec E m c
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

/-- **The coordinate ring of `L_m` is `K[E][1/ψ_m]`.** -/
lemma mem_coordRing_mulByNField_iff (z : Ω) :
    (z ∈ mulByNField E m ∧ IsIntegral (A₀ K τ) z) ↔ ∃ b : coverRingN E m, φ (ι b) = z := by
  constructor
  · rintro ⟨⟨f, rfl⟩, hz⟩
    obtain ⟨b, rfl⟩ := exists_of_isIntegral E m hz
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨_, rfl⟩, isIntegral_mulByNEmb E m b⟩

lemma mulByNField_eq_adjoin :
    mulByNField E m = IntermediateField.adjoin (K₀ K τ)
      {φ (algebraMap CR FF (xE E)), φ (algebraMap CR FF (yE E))} := by
  refine le_antisymm ?_ (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro z ⟨f, rfl⟩
    set S := IntermediateField.adjoin (K₀ K τ)
      ({φ (algebraMap CR FF (xE E)), φ (algebraMap CR FF (yE E))} : Set Ω)
    have hx : φ (algebraMap CR FF (xE E)) ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have hy : φ (algebraMap CR FF (yE E)) ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have hK : ∀ c : K, algebraMap K Ω c ∈ S := fun c => by
      have := S.algebraMap_mem (algebraMap K (K₀ K τ) c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    have hpoly : ∀ p : K[X], φ (algebraMap CR FF (aeval (xE E) p)) ∈ S := fun p => by
      induction p using Polynomial.induction_on with
      | C c => rw [aeval_C, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]; exact hK c
      | add p q hp hq => rw [map_add, map_add, map_add]; exact add_mem hp hq
      | monomial n c _ =>
        rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_mul, map_pow, map_pow,
          ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
        exact mul_mem (hK c) (pow_mem hx _)
    have hA : ∀ a : CR, φ (algebraMap CR FF a) ∈ S := fun a => by
      obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, algebraMap_polynomial_eq_aeval_xE,
        algebraMap_polynomial_eq_aeval_xE, map_add, map_add, map_mul, map_mul]
      exact add_mem (hpoly p) (mul_mem (hpoly q) hy)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
    rw [map_div₀]
    exact div_mem (hA a) (hA b)
  · rintro z (rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

instance finiteDimensional_mulByNField : FiniteDimensional (K₀ K τ) (mulByNField E m) := by
  rw [mulByNField_eq_adjoin]
  refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
  have hz' : ∃ a : CR, z = φ (ι (algebraMap CR (coverRingN E m) a)) := by
    rcases hz with rfl | rfl
    · exact ⟨xE E, by rw [← IsScalarTower.algebraMap_apply]⟩
    · exact ⟨yE E, by rw [← IsScalarTower.algebraMap_apply]⟩
  obtain ⟨a, rfl⟩ := hz'
  exact (isIntegral_mulByNEmb E m _).tower_top

/-- `K[E][1/ψ_m] ≅ coordRing L_m`. -/
def coverToCoordRing : coverRingN E m →+* coordRing K τ (mulByNField E m) where
  toFun b := ⟨⟨φ (ι b), ⟨_, rfl⟩⟩,
    (CoordRing.isIntegral_coe_iff (F := mulByNField E m) _).1 (isIntegral_mulByNEmb E m b)⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

lemma coe_coverToCoordRing (b : coverRingN E m) :
    ((coverToCoordRing E m b : mulByNField E m) : Ω) = φ (ι b) := rfl

def coverEquivCoordRing : coverRingN E m ≃+* coordRing K τ (mulByNField E m) :=
  RingEquiv.ofBijective (coverToCoordRing E m)
    ⟨fun b b' h => by
      have h' := congrArg (fun z : coordRing K τ (mulByNField E m) => ((z : mulByNField E m) : Ω)) h
      exact IsFractionRing.injective (coverRingN E m) FF ((mulByNEmb E m).injective h'),
     fun z => by
      obtain ⟨b, hb⟩ := (mem_coordRing_mulByNField_iff E m _).mp
        ⟨(z : mulByNField E m).2, (CoordRing.isIntegral_coe_iff (F := mulByNField E m) _).2 z.2⟩
      exact ⟨b, Subtype.ext (Subtype.ext hb)⟩⟩

lemma coe_coverEquivCoordRing (b : coverRingN E m) :
    ((coverEquivCoordRing E m b : mulByNField E m) : Ω) = φ (ι b) := rfl

/-- **`coordRing L_X → coordRing L_m` is étale**: it is `[m]^* : K[E] → K[E][1/ψ_m]`. -/
theorem etale_mulByNField :
    (ringMap τ (hemiL_le_mulByNField E m)).toRingHom.Etale := by
  have hcomp : (ringMap τ (hemiL_le_mulByNField E m)).toRingHom =
      ((coverEquivCoordRing E m).toRingHom.comp (mulByNHom E m)).comp
        (hemiREquiv E).symm.toRingEquiv.toRingHom := by
    ext z
    change ((z : (hemiData E).L) : Ω) = φ (ι (mulByNHom E m ((hemiREquiv E).symm z)))
    rw [mulByNEmb_mulByNHom, ← algebraMap_hemiREquiv', AlgEquiv.apply_symm_apply]
    rfl
  rw [hcomp]
  refine RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (hemiREquiv E).symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ ?_
      (RingHom.Etale.of_bijective (coverEquivCoordRing E m).bijective))
  exact (inferInstance : Algebra.Etale CR (MulByNB E m))

/-- **Intermediate levels are étale over `X`**: for `L_X ≤ L' ≤ L_m`,
`coordRing L_X → coordRing L'` is étale (`pi1`'s inertia criterion). -/
theorem etale_of_le_mulByNField {L' : IntermediateField (K₀ K τ) Ω} (h₁ : (hemiData E).L ≤ L')
    (h₂ : L' ≤ mulByNField E m) : (ringMap τ h₁).toRingHom.Etale := by
  haveI : FiniteDimensional (K₀ K τ) L' :=
    FiniteDimensional.of_injective (IntermediateField.inclusion h₂).toLinearMap
      (IntermediateField.inclusion h₂).injective
  have hm := (etale_iff_inertia (transcendental_tau E) (hemiL_le_mulByNField E m)).mp
    (etale_mulByNField E m)
  exact (etale_iff_inertia (transcendental_tau E) h₁).mpr fun W hW σ hσ =>
    IntermediateField.fixingSubgroup_antitone h₂ (hm W hW hσ)

/-! ### Levels between `X` and `[m]` given by generators -/

lemma mem_adjoin_image {S : Set FF} {g : FF} (hg : g ∈ IntermediateField.adjoin K S) :
    φ g ∈ IntermediateField.adjoin (K₀ K τ) (φ '' S) := by
  have h1 : φ g ∈ (IntermediateField.adjoin K S).map (mulByNEmb E m) := ⟨g, hg, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin K (φ '' S) ≤
      (IntermediateField.adjoin (K₀ K τ) (φ '' S)).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin (K₀ K τ) (φ '' S))
  exact h2 h1

/-- A level generated by `S ⊆ K(E)` containing `[m]^*K[E]` lies over `L_X`. -/
lemma hemiL_le_adjoin {S : Set FF}
    (hS : ∀ a : CR, ι (mulByNHom E m a) ∈ IntermediateField.adjoin K S) :
    (hemiData E).L ≤ IntermediateField.adjoin (K₀ K τ) (φ '' S) := by
  intro z hz
  obtain ⟨f, rfl⟩ := (mem_hemiL_iff E z).mp hz
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CR) f
  rw [map_div₀, ← mulByNEmb_mulByNHom E m, ← mulByNEmb_mulByNHom E m]
  exact div_mem (mem_adjoin_image E m (hS a)) (mem_adjoin_image E m (hS b))

lemma adjoin_image_le_mulByNField (S : Set FF) :
    IntermediateField.adjoin (K₀ K τ) (φ '' S) ≤ mulByNField E m := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

/-- **Étaleness of a level given by generators**: if `S ⊆ K(E)` generates a subfield containing
`[m]^* K[E]`, then `L' = K(τ)(φ(S))` satisfies `L_X ≤ L' ≤ L_m`, it is finite over `K(τ)`, and
`coordRing L_X → coordRing L'` is étale. -/
theorem etale_adjoin_image {S : Set FF}
    (hS : ∀ a : CR, ι (mulByNHom E m a) ∈ IntermediateField.adjoin K S) :
    (ringMap τ (hemiL_le_adjoin E m hS)).toRingHom.Etale :=
  etale_of_le_mulByNField E m _ (adjoin_image_le_mulByNField E m S)

instance finiteDimensional_adjoin_image (S : Set FF) :
    FiniteDimensional (K₀ K τ) (IntermediateField.adjoin (K₀ K τ) (φ '' S)) :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (adjoin_image_le_mulByNField E m S)).toLinearMap
    (IntermediateField.inclusion (adjoin_image_le_mulByNField E m S)).injective

end Galois


end CurvesJacobian.Cusp
