/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Constraints

/-!
# Mono-analytic scalings of the log-shell container (the wall, Milestone 3, part 1)

Milestone 2 (`Iut/Wall/Constraints.lean`) found that the constraints of IUT III and of the LANA
interim report ([LANA]) that are about distinct ring structures cannot act on the wall as long as
there is a single container with a single log-volume. Milestone 3 gives every Hodge theater its
own copy of the container, identified with the common coric container by a **Kummer
isomorphism**. This file supplies the isomorphisms used for that: **scalings**.

## Scalings

A `Scaling D` is a unit `u_{i,p,c}` of every tensor component `⊗_{l} K_{c(l)}` of the packet of
capsule `i` at the prime `p` (tuple `c` of places), equal to `1` at the primes that are not
residue characteristics of bad places (so that adelic regions stay adelic); nothing happens at
`∞`. It acts on regions of the concrete container (`act`) by `x ↦ u·x` on each component.

* **Mono-analytic, not ring-theoretic.** On each component the map `x ↦ u·x` is an additive
  isomorphism (`kummerAddEquiv`) and a homeomorphism (`continuous_kummer`,
  `continuous_kummer_symm`): it is an isomorphism of the additive topological group, i.e. of the
  mono-analytic structure of the log-shell ([LANA], §5.1(c), (d); IUT III, Proposition 3.2,
  Proposition 3.9(ii)). It is multiplicative, i.e. a ring isomorphism, **iff `u = 1`**
  (`units_mul_hom_iff`).
* **Induced ring structures.** Transporting the ring structure of a copy along `x ↦ u·x` gives
  the multiplication `x *_u y = u·x·y` on the common additive group (`kummer_kmul`), and two
  scalings induce the same multiplication iff they are equal (`kmul_eq_iff`). So distinct
  scalings give distinct (mutually alien, [LANA], §7.1(b)(c)) ring structures on one
  mono-analytic object.
* **Log-volume.** Scalings shift the procession-normalized log-volume by a fixed amount
  (`logVol_act : log-vol(u·S) = shift u + log-vol(S)`, `shift u := log-vol(u·O)`), and `shift`
  is a homomorphism (`shift_mul`, `shift_inv`, `shift_zpow`). This is the multiplicative case
  of the general fact that an additive automorphism of a locally compact group scales Haar
  measure by its modulus; `shift u` is the logarithm of the (normalized) modulus.
* **Examples.** `qScale D` (multiplication by `q_v` in the factor of the label `1`), with
  `shift = −|log(q)|` (`shift_qScale`), and `negScale D` (multiplication by `−1` at the bad
  primes, the map induced on log-shells by the inversion `x ↦ x⁻¹` of the unit group, an
  automorphism of `O^×_v` of the kind of (Ind2) in [LANA], §6), with `shift = 0`
  (`shift_negScale`) but `negScale D ≠ 1` (`negScale_ne_one`).

Ring isomorphisms of the local fields other than the identity (Galois conjugations) are not
scalings; they preserve Haar measure, so they would have shift `0` as well. This is not
formalized (a documented restriction of the model, `Iut/Wall/README.md`, M3).
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

namespace Wall

/-! ### One tensor component -/

section Component

variable {T : Type*} [CommRing T]

/-- **A scaling is a ring homomorphism iff it is the identity.** -/
theorem units_mul_hom_iff (w : Tˣ) :
    (∀ x y : T, (w : T) * (x * y) = ((w : T) * x) * ((w : T) * y)) ↔ w = 1 := by
  constructor
  · intro h
    have h1 : (w : T) * 1 = (w : T) * w := by simpa using h 1 1
    exact Units.ext ((Units.mul_right_inj w).mp h1).symm
  · rintro rfl x y
    simp

/-- The ring structure induced on a component by the Kummer scaling `x ↦ u·x`:
`x *_u y = u⁻¹·((u·x)·(u·y)) = u·x·y`. -/
def kmul (u : Tˣ) (x y : T) : T := (u : T) * x * y

/-- The scaling `x ↦ u·x` is a ring isomorphism from `(T, *_u)` to `(T, *)`. -/
theorem kummer_kmul (u : Tˣ) (x y : T) : (u : T) * kmul u x y = ((u : T) * x) * ((u : T) * y) := by
  unfold kmul
  ring

/-- **Distinct scalings induce distinct ring structures.** -/
theorem kmul_eq_iff (u v : Tˣ) : kmul u = kmul v ↔ u = v := by
  constructor
  · intro h
    have := congrFun (congrFun h 1) 1
    simp only [kmul, mul_one] at this
    exact Units.ext this
  · rintro rfl
    rfl

/-- **The scaling `x ↦ u·x` as an additive isomorphism** (mono-analytic). -/
def kummerAddEquiv (u : Tˣ) : T ≃+ T where
  toFun x := (u : T) * x
  invFun x := ((u⁻¹ : Tˣ) : T) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ _ _

theorem continuous_kummer [TopologicalSpace T] [IsTopologicalRing T] (u : Tˣ) :
    Continuous (kummerAddEquiv u) :=
  continuous_const.mul continuous_id

theorem continuous_kummer_symm [TopologicalSpace T] [IsTopologicalRing T] (u : Tˣ) :
    Continuous (kummerAddEquiv u).symm :=
  continuous_const.mul continuous_id

end Component

variable (D : InitialThetaData.{0})

/-- The tensor component of the packet of capsule `i` at the prime `p` and the tuple `c`. -/
abbrev Comp (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) : Type :=
  LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)

/-- **A scaling**: a unit of every tensor component of the container, trivial at the primes that
are not residue characteristics of bad places (see the module docstring). -/
@[ext]
structure Scaling where
  /-- The unit at capsule `i`, prime `p`, tuple `c`. -/
  u : ∀ (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)), (Comp D i p c)ˣ
  /-- Trivial at the good primes. -/
  good : ∀ (i : Fin (nC D)) (p : Nat.Primes) c, (p : ℕ) ∉ D.badChars → u i p c = 1

namespace Scaling

variable {D}

noncomputable instance : Mul (Scaling D) where
  mul a b := ⟨fun i p c => a.u i p c * b.u i p c, fun i p c h => by
    rw [a.good i p c h, b.good i p c h, one_mul]⟩

noncomputable instance : One (Scaling D) where
  one := ⟨fun _ _ _ => 1, fun _ _ _ _ => rfl⟩

noncomputable instance : Inv (Scaling D) where
  inv a := ⟨fun i p c => (a.u i p c)⁻¹, fun i p c h => by rw [a.good i p c h, inv_one]⟩

@[simp] lemma mul_u (a b : Scaling D) (i p c) : (a * b).u i p c = a.u i p c * b.u i p c := rfl
@[simp] lemma one_u (i p c) : (1 : Scaling D).u i p c = 1 := rfl
@[simp] lemma inv_u (a : Scaling D) (i p c) : a⁻¹.u i p c = (a.u i p c)⁻¹ := rfl

noncomputable instance : Group (Scaling D) where
  mul_assoc a b d := Scaling.ext (by funext i p c; simp [mul_assoc])
  one_mul a := Scaling.ext (by funext i p c; simp)
  mul_one a := Scaling.ext (by funext i p c; simp)
  inv_mul_cancel a := Scaling.ext (by funext i p c; simp)

end Scaling

/-! ### The action on regions -/

variable (w : Scaling D)

/-- Multiplication by the scaling on the packet of capsule `i` at `p`. -/
noncomputable def actMap (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total :=
  fun x c => @HMul.hMul (Comp D i p c) (Comp D i p c) (Comp D i p c) instHMul
    ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) (x c)

lemma actMap_eq_id (i : Fin (nC D)) (p : Nat.Primes) (hbad : (p : ℕ) ∉ D.badChars) :
    actMap D w i p = id := by
  funext x c
  have h1 : ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) = 1 := by
    rw [w.good i p c hbad, Units.val_one]
  simp only [actMap, h1, one_mul, id]

lemma actMap_mul (a b : Scaling D) (i : Fin (nC D)) (p : Nat.Primes) :
    actMap D (a * b) i p = actMap D a i p ∘ actMap D b i p := by
  funext x c
  simp only [actMap, Function.comp, Scaling.mul_u, Units.val_mul]
  exact mul_assoc _ _ _

lemma actMap_one (i : Fin (nC D)) (p : Nat.Primes) : actMap D 1 i p = id := by
  funext x c
  simp only [actMap, Scaling.one_u, Units.val_one, one_mul, id]

/-- The packet regions of `w·R`. -/
noncomputable def actRegion (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => actMap D w i p '' R.region (.finite p)
  | .infinite => R.region .infinite

/-- `w·R` at capsule `i`. -/
noncomputable def actAt (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := actRegion D w i R
  finiteSupport := by
    refine (R.finiteSupport.union ((D.badChars.finite_toSet.image
      fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite))).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · by_cases hbad : (p : ℕ) ∈ D.badChars
      · exact Or.inr ⟨p, hbad, by simp [p.2]⟩
      · refine Or.inl fun h => hvQ ?_
        change actMap D w i p '' R.region (.finite p) = _
        rw [actMap_eq_id D w i p hbad, Set.image_id]
        exact h
    · exact Or.inl hvQ

/-- **The region `S` scaled by `w`** (the image of `S` under the Kummer scaling). -/
noncomputable def act (S : Region D) : Region D := fun i => actAt D w i (S i)

lemma admissibleRegion_ext {i : Fin (VC D).proc.length} {R R' : (VC D).AdmissibleRegion i}
    (h : R.region = R'.region) : R = R' := by
  cases R
  cases R'
  cases h
  rfl

/-- `act` is an action: `(a·b)·S = a·(b·S)`. -/
theorem act_mul (a b : Scaling D) (S : Region D) : act D (a * b) S = act D a (act D b S) := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D (a * b) i p '' _ = actMap D a i p '' (actMap D b i p '' _)
    rw [actMap_mul, Set.image_comp]
  · rfl

/-- `1·S = S`. -/
theorem act_one (S : Region D) : act D 1 S = S := by
  funext i
  refine admissibleRegion_ext D (funext fun vQ => ?_)
  rcases vQ with p | _
  · change actMap D 1 i p '' _ = _
    rw [actMap_one, Set.image_id]
  · rfl

theorem act_inv_act (S : Region D) : act D w⁻¹ (act D w S) = S := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (S : Region D) : act D w (act D w⁻¹ S) = S := by
  rw [← act_mul, mul_inv_cancel, act_one]

lemma proj_act (S : Region D) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.proj D.placeSect (.finite p) c ((act D w S i).region (.finite p)) =
      ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) • LocalTheory.proj D.placeSect
        (.finite p) c ((S i).region (.finite p)) := by
  change (fun x => x c) '' (actMap D w i p '' (S i).region (.finite p)) = _
  rw [Set.image_image]
  unfold LocalTheory.proj
  rw [← Set.image_smul, Set.image_image]
  rfl

/-- `w·S` is adelic for adelic `S`. -/
theorem isAdelic_act {S : Region D} (hS : IsAdelic D S) : IsAdelic D (act D w S) := by
  intro i vQ
  rcases vQ with p | _
  · obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    refine ⟨fun c => ((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) • fam c, fun c =>
      LocalConstruct.units_smul_mem_admissible (w.u i p c).isUnit (hfam c), ?_⟩
    change actMap D w i p '' (S i).region (.finite p) = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩
  · exact hS i .infinite

/-- `w·S` is adelic iff `S` is. -/
theorem isAdelic_act_iff {S : Region D} : IsAdelic D (act D w S) ↔ IsAdelic D S :=
  ⟨fun h => act_inv_act D w S ▸ isAdelic_act D w⁻¹ h, isAdelic_act D w⟩

/-! ### The log-volume of `w·S` -/

/-- Packetwise, `w` shifts the log-volume by that of `w·O`. -/
theorem packetVol_act {S : Region D} (hS : IsAdelic D S) (i : Fin (nC D))
    (vQ : RationalPlace) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((act D w S i).region vQ) =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((act D w (integralRegion D) i).region vQ) +
        (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((S i).region vQ) := by
  rcases vQ with p | _
  · rw [LocalTheory.packetVol_eq, LocalTheory.packetVol_eq, LocalTheory.packetVol_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    have hpS : LocalTheory.proj D.placeSect (.finite p) c ((S i).region (.finite p)) = fam c := by
      rw [hR, LocalTheory.proj_productRegion D.placeSect _ fam
        (fun c => LocalTheory.admissible_nonempty D.Kt _ _ _ (hfam c))]
    have hpO : LocalTheory.proj D.placeSect (.finite p) c
        ((integralRegion D i).region (.finite p)) =
        LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
      LocalTheory.proj_productRegion D.placeSect _ _
        (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
    rw [proj_act, proj_act, hpS, hpO]
    change _ * LocalConstruct.componentVol (.finite p) _
        (((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) • fam c) =
      _ * LocalConstruct.componentVol (.finite p) _
          (((w.u i p c : (Comp D i p c)ˣ) : Comp D i p c) •
            LocalConstruct.integralAt (.finite p) _) +
        _ * LocalConstruct.componentVol (.finite p) _ (fam c)
    rw [LocalConstruct.componentVol_units_smul (w.u i p c).isUnit (hfam c).2.2.2.1
      (hfam c).2.2.2.2]
    ring
  · change (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite ((S i).region .infinite) =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite
        ((VC D).packet i .infinite).integralRegion + _
    rw [(LocalTheory.vol D.placeSect (nC D)).packetVol_integral, zero_add]

/-- **The log-volume shift of a scaling**: `shift w = log-vol(w·O)`. -/
noncomputable def shift : ℝ := logVol D (act D w (integralRegion D))

/-- **A scaling shifts log-volumes by a fixed amount**: `log-vol(w·S) = shift w + log-vol(S)`. -/
theorem logVol_act {S : Region D} (hS : IsAdelic D S) :
    logVol D (act D w S) = shift D w + logVol D S := by
  unfold shift logVol LogVolumeData.processionVol
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold LogVolumeData.globalVol
  rw [← finsum_add_distrib ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)]
  exact finsum_congr fun vQ => packetVol_act D w hS i vQ

theorem shift_one : shift D 1 = 0 := by
  rw [shift, act_one, logVol_integralRegion]

theorem shift_mul (a b : Scaling D) : shift D (a * b) = shift D a + shift D b := by
  rw [shift, act_mul, logVol_act D a (isAdelic_act D b (isAdelic_integralRegion D))]
  rfl

theorem shift_inv : shift D w⁻¹ = -shift D w := by
  have h := shift_mul D w w⁻¹
  rw [mul_inv_cancel, shift_one] at h
  linarith

/-- `shift` as a homomorphism to `Multiplicative ℝ`. -/
noncomputable def shiftHom : Scaling D →* Multiplicative ℝ :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (shift D a)) fun a b => by
    rw [shift_mul]
    rfl

theorem shift_zpow (n : ℤ) : shift D (w ^ n) = n * shift D w := by
  have h := map_zpow (shiftHom D) w n
  change Multiplicative.ofAdd (shift D (w ^ n)) = (Multiplicative.ofAdd (shift D w)) ^ n at h
  rw [← ofAdd_zsmul] at h
  rw [Multiplicative.ofAdd.injective h, zsmul_eq_mul]

/-- A scaling with nonzero shift is not the identity. -/
theorem ne_one_of_shift_ne_zero (h : shift D w ≠ 0) : w ≠ 1 := by
  rintro rfl
  exact h (shift_one D)

/-! ### Examples -/

lemma powElt_good (e : Fin (nC D) → ℕ) (lab : ∀ i, InitialThetaData.Lab (nC D) i)
    (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    (hbad : (p : ℕ) ∉ D.badChars) : powElt D e lab i p c = 1 := by
  unfold powElt
  rw [D.qroot_eq_one _ (by rw [LocalTheory.residueChar_sectPlace D.placeSect]; exact hbad),
    one_pow, map_one]

/-- **Multiplication by `q_v` in the tensor factor of the label `1`.** -/
noncomputable def qScale : Scaling D where
  u i p c := (isUnit_powElt D (fun _ => 1) (labOne D) i p c).unit
  good i p c h := by
    rw [Units.ext_iff, IsUnit.unit_spec, Units.val_one]
    exact powElt_good D _ _ i p c h

/-- `qScale·S` is the region `pow D 1 labOne S`; in particular `qScale·O` is the `q`-pilot
region. -/
theorem act_qScale (S : Region D) : act D (qScale D) S = pow D (fun _ => 1) (labOne D) S :=
  rfl

/-- **`shift(qScale) = −|log(q)|`.** -/
theorem shift_qScale : shift D (qScale D) = -D.qPilot.absLogQ := by
  rw [shift, act_qScale]
  exact logVol_qRegion D

lemma absLogQ_pos : 0 < D.qPilot.absLogQ := by
  have := D.lhs_neg
  unfold QPilotData.lhs at this
  linarith

theorem qScale_ne_one : qScale D ≠ 1 :=
  ne_one_of_shift_ne_zero D _ (by rw [shift_qScale]; exact neg_ne_zero.mpr (absLogQ_pos D).ne')

/-- **Multiplication by `−1` at the bad primes** (the map induced on log-shells by the inversion
of the unit group). -/
noncomputable def negScale : Scaling D where
  u _ p _ := if (p : ℕ) ∈ D.badChars then -1 else 1
  good _ _ _ h := if_neg h

lemma negScale_mul_self : negScale D * negScale D = 1 := by
  ext i p c
  simp only [Scaling.mul_u, negScale, Scaling.one_u]
  split_ifs <;> simp

/-- **`negScale` preserves log-volumes**: `shift(negScale) = 0`. -/
theorem shift_negScale : shift D (negScale D) = 0 := by
  have h := shift_mul D (negScale D) (negScale D)
  rw [negScale_mul_self, shift_one] at h
  linarith

/-- In a nontrivial algebra over `ℚ_p`, `−1 ≠ 1`. -/
lemma neg_one_ne_one_comp (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p))
    [Nontrivial (Comp D i p c)] : (-1 : Comp D i p c) ≠ 1 := by
  intro h
  have h2 : (2 : Comp D i p c) = 0 := by
    have : (1 : Comp D i p c) + 1 = 0 := by
      nth_rewrite 1 [← h]
      exact neg_add_cancel 1
    rw [← this]
    norm_num
  have h2' : algebraMap ℚ_[p] (Comp D i p c) 2 = 0 := by
    rw [map_ofNat]
    exact h2
  have hinj := (algebraMap ℚ_[p] (Comp D i p c)).injective
  have : (2 : ℚ_[p]) = 0 := hinj (by rw [h2', map_zero])
  exact two_ne_zero this

/-- **`negScale` is not the identity.** -/
theorem negScale_ne_one : negScale D ≠ 1 := by
  intro hneg
  apply qScale_ne_one D
  ext i p c
  by_cases hbad : (p : ℕ) ∈ D.badChars
  · by_contra hne
    have hnt : Nontrivial (Comp D i p c) := ⟨⟨_, _, hne⟩⟩
    have h := congrArg (fun a : Scaling D => ((a.u i p c : (Comp D i p c)ˣ) : Comp D i p c)) hneg
    simp only [negScale, if_pos hbad, Units.val_neg, Units.val_one, Scaling.one_u] at h
    exact neg_one_ne_one_comp D i p c h
  · rw [(qScale D).good i p c hbad, Scaling.one_u]

end Wall

end Iut
