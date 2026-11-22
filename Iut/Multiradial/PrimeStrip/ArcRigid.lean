/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.ArcCor53

/-!
# IUT I, Corollary 5.3 (ii) at `v ∈ V^arc`: injectivity (MR21, session 8)

IUT I, Corollary 5.3 (ii) (`Inter-universal Teichmuller Theory I.txt`, l.9891–9894) cites
[AbsTopIII], Proposition 4.2 (i) (`Topics in Absolute Anabelian Geometry III.txt`,
l.6210–6225) at `V^arc`: `Isom(‡F_v, ‡F'_v) → Isom(‡D_v, ‡D'_v)` is bijective. Surjectivity is
`ArcCor53.lean`. Injectivity reduces (groupoid laws) to: an automorphism `f` of
`F_v = (C_v, E_{Λ₀}, κ_v)` over the identity of `D_v` is 2-isomorphic to the identity. Since
`f` is compatible with `κ_v`, it acts trivially on `μ` of the linear endomorphisms of the
isotropic objects; the content is a natural isomorphism `F ≅ 𝟭` for the autoequivalence `F`
of the Frobenioid of angular regions ([FrdII], Example 3.3).

## Contents

* `eq_of_rel` (**rigidity of systems of angular parts**): two families `b`, `b'` of angular
  parts of `S¹` with the same incidences `{u}·b_i^d ⊆ b_j` (both families exhausting all
  angular parts, `b'` up to rotation, and with the same members equal to `S¹`) coincide. Proof:
  the maximal angular parts `≠ S¹` are the `S¹ ∖ {p}` (`isAngular_compl_singleton`), so the
  incidences determine a bijection `p ↦ h(p)` of points with `p ∈ b_i ⟺ h(p) ∈ b'_i`;
  compatibility with rotations gives `h(p) = r·p`, and compatibility with squaring
  (`IsAngular.eq_of_subset` applied to `B₀²`, `B₀` a quarter arc, `sq_arcQ_ne_univ`)
  gives `r = 1`.
* `isoIdOfRigid`: an autoequivalence `F` of the Frobenioid of angular regions which preserves
  Frobenius degrees and divisors (`Div`), acts trivially on the rotation part of the linear
  endomorphisms of `S¹ × (0, 1]` and preserves and reflects isotropic objects is isomorphic to
  the identity. The rotations `v_A` (`vA`) are read off from `F` applied to the morphism
  `A → S¹ × (0, 1]` with `μ = e^{−τ_A}` and to the Frobenius endomorphism `z ↦ z²`; the
  transformation rule `rot(F k)·v_A = rot(k)·v_X^d` (`rot_map_mul`) and the incidences
  `{u}·B_X^d ⊆ B_A ⟺ {u}·(v_X B_{FX})^d ⊆ v_A B_{FA}` (`incid_iff`) feed `eq_of_rel`.
* `FArcData.Iso.hom2OfConjId`: for `f : Aut(F_v)` with `c_S = id`, a 2-isomorphism
  `f.F ⟹ id`; **`FArcData.IsoClass.toD_injective_model`**, **`FArcComp.isoClassToD_injective`**,
  `FArcComp.isoClassToD_bijective`;
* **`FStrip.isoClassToD_bijective`**: IUT I, Corollary 5.3 (ii) over all of `V` (inputs at
  `V^non` as in `FStripNon.isoClassToD_bijective`; none at `V^arc`; deviation H5 unchanged).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

namespace Angular

open CategoryTheory Iut.Frobenioid Iut.Frobenioid.Angular Set Pointwise Real

/-! ### Angular parts: complements of points, a quarter arc -/

/-- `S¹ ∖ {−1}` is the image of `(−π, π)`. -/
lemma compl_neg_one_eq : ({-1} : Set Circle)ᶜ = Circle.exp '' Ioo (-π) π := by
  ext z
  simp only [mem_compl_iff, mem_singleton_iff, mem_image, mem_Ioo]
  constructor
  · intro hz
    refine ⟨Complex.arg z, ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩,
      Circle.exp_arg z⟩
    intro h
    apply hz
    rw [← Circle.exp_arg z, h]
    exact Circle.ext (by simp [Circle.coe_exp, Complex.exp_pi_mul_I])
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩ h
    have := congrArg (fun w : Circle => Complex.arg w) h
    simp only [Circle.arg_exp h1 h2.le, Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one] at this
    exact h2.ne this

/-- `{u}·(S¹ ∖ {p}) = S¹ ∖ {u p}`. -/
lemma singleton_mul_compl (u p : Circle) :
    ({u} : Set Circle) * ({p}ᶜ) = ({u * p}ᶜ : Set Circle) := by
  ext z
  simp only [mem_compl_iff, mem_singleton_iff, singleton_mul, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩ h
    exact hx (mul_left_cancel h)
  · intro hz
    exact ⟨u⁻¹ * z, fun h => hz (by rw [← h, mul_inv_cancel_left]), mul_inv_cancel_left u z⟩

/-- **`S¹ ∖ {p}` is an angular part.** -/
lemma isAngular_compl_singleton (p : Circle) : IsAngular ({p}ᶜ : Set Circle) := by
  have h : ({p}ᶜ : Set Circle) = {-p} * ({-1} : Set Circle)ᶜ := by
    rw [singleton_mul_compl]
    congr 2
    simp
  have h1 : IsAngular ({-1} : Set Circle)ᶜ := by
    refine ⟨isOpen_compl_singleton, ?_, ⟨1, ?_⟩⟩
    · rw [compl_neg_one_eq]
      exact isPreconnected_Ioo.image _ Circle.exp.continuous.continuousOn
    · intro h
      have := congrArg (fun w : Circle => (w : ℂ)) h
      simp only [Circle.coe_one, Circle.coe_neg] at this
      norm_num at this
  rw [h]
  exact h1.singleton_mul _

/-- The quarter arc `exp(i(−π/4, π/4))`. -/
def arcQ : Set Circle := Circle.centeredArc (π / 4)

lemma isAngular_arcQ : IsAngular arcQ := isAngular_centeredArc (by positivity)

/-- **`B₀² ≠ S¹`** for the quarter arc `B₀`: `−1 ∉ B₀²`. -/
lemma sq_arcQ_ne_univ : arcQ ^ 2 ≠ univ := by
  intro h
  have hm : (-1 : Circle) ∈ arcQ ^ 2 := h ▸ mem_univ _
  rw [pow_two] at hm
  obtain ⟨x, ⟨a, ha, rfl⟩, y, ⟨c, hc, rfl⟩, hxy⟩ := hm
  simp only [mem_setOf_eq] at ha hc
  change Circle.exp a * Circle.exp c = -1 at hxy
  rw [← Circle.exp_add] at hxy
  have hb := abs_lt.mp ha
  have hb' := abs_lt.mp hc
  have := congrArg (fun w : Circle => Complex.arg w) hxy
  simp only [Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one] at this
  rw [Circle.arg_exp (by linarith [pi_pos]) (by linarith [pi_pos])] at this
  linarith [pi_pos]

/-! ### Rigidity of systems of angular parts -/

lemma singleton_mul_subset_iff {u : Circle} {S T : Set Circle} :
    {u} * S ⊆ T ↔ S ⊆ {u⁻¹} * T := by
  constructor
  · intro h x hx
    exact mem_mul.mpr ⟨u⁻¹, rfl, u * x, h (mem_mul.mpr ⟨u, rfl, x, hx, rfl⟩), by group⟩
  · intro h x hx
    obtain ⟨_, rfl, y, hy, rfl⟩ := mem_mul.mp hx
    obtain ⟨_, rfl, z, hz, rfl⟩ := mem_mul.mp (h hy)
    simpa using hz

lemma mem_singleton_mul' {u z : Circle} {S : Set Circle} :
    z ∈ ({u} : Set Circle) * S ↔ u⁻¹ * z ∈ S := by
  rw [singleton_mul, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, mul_inv_cancel_left u z⟩

lemma singleton_mul_singleton_mul (u v : Circle) (S : Set Circle) :
    ({u} : Set Circle) * ({v} * S) = {u * v} * S := by
  rw [← mul_assoc, singleton_mul_singleton]

lemma singleton_mul_pow (u : Circle) (S : Set Circle) (d : ℕ) :
    (({u} : Set Circle) * S) ^ d = {u ^ d} * S ^ d := by
  rw [mul_pow, singleton_pow]

lemma singleton_mul_eq_univ {u : Circle} {S : Set Circle} : {u} * S = univ ↔ S = univ := by
  rw [singleton_mul_eq_iff, singleton_mul_univ]

/-- **Rigidity of systems of angular parts.** Two families `b`, `b'` of angular parts with the
same incidences `{u}·b_i^d ⊆ b_j`, both exhausting the angular parts (`b'` up to rotation),
with the same members equal to `S¹`, coincide. -/
theorem eq_of_rel {ι : Type*} (b b' : ι → Set Circle) (hb : ∀ i, IsAngular (b i))
    (hrel : ∀ i j (d : ℕ) (u : Circle), d ≠ 0 → ({u} * b i ^ d ⊆ b j ↔ {u} * b' i ^ d ⊆ b' j))
    (hsurj : ∀ C, IsAngular C → ∃ i, b i = C)
    (hsurj' : ∀ C, IsAngular C → ∃ i c, b' i = {c} * C)
    (huniv : ∀ i, b i = univ ↔ b' i = univ) (i : ι) : b' i = b i := by
  have hsub : ∀ i j, b i ⊆ b j ↔ b' i ⊆ b' j := fun i j => by
    simpa using hrel i j 1 1 one_ne_zero
  have hrot : ∀ i j u, b j = {u} * b i → b' j = {u} * b' i := by
    intro i j u h
    refine subset_antisymm ?_ ?_
    · have h2 : {u⁻¹} * b j ^ 1 ⊆ b i := by
        rw [pow_one, h, singleton_mul_singleton_mul, inv_mul_cancel, singleton_one, one_mul]
      have := (hrel j i 1 u⁻¹ one_ne_zero).mp h2
      rw [pow_one, singleton_mul_subset_iff, inv_inv] at this
      exact this
    · have h1 : {u} * b i ^ 1 ⊆ b j := by rw [pow_one, h]
      simpa using (hrel i j 1 u one_ne_zero).mp h1
  have hsurj'' : ∀ C, IsAngular C → ∃ i, b' i = C := by
    intro C hC
    obtain ⟨i, c, hi⟩ := hsurj' C hC
    obtain ⟨j, hj⟩ := hsurj _ ((hb i).singleton_mul c⁻¹)
    refine ⟨j, ?_⟩
    rw [hrot i j c⁻¹ hj, hi, singleton_mul_singleton_mul, inv_mul_cancel, singleton_one, one_mul]
  -- the points `p ↦ h(p)`
  choose ip hip using fun p : Circle => hsurj _ (isAngular_compl_singleton p)
  have hcompl_ne : ∀ q : Circle, ({q}ᶜ : Set Circle) ≠ univ := fun q h =>
    (h ▸ mem_univ q : q ∈ ({q}ᶜ : Set Circle)) rfl
  have hex : ∀ p, ∃ q, b' (ip p) = {q}ᶜ := by
    intro p
    have hne : b' (ip p) ≠ univ := fun h => hcompl_ne p ((hip p).symm.trans ((huniv _).mpr h))
    obtain ⟨q, hq⟩ := (ne_univ_iff_exists_notMem _).mp hne
    obtain ⟨j, hj⟩ := hsurj'' _ (isAngular_compl_singleton q)
    have h1 : b' (ip p) ⊆ b' j := by rw [hj]; exact subset_compl_singleton_iff.mpr hq
    have h2 : b (ip p) ⊆ b j := (hsub _ _).mpr h1
    rw [hip] at h2
    have h3 : b j ≠ univ := fun h => hcompl_ne q (hj ▸ (huniv j).mp h)
    have h4 : b j = b (ip p) := by
      rw [hip]
      refine subset_antisymm ?_ h2
      intro x hx
      by_contra hxp
      apply h3
      refine eq_univ_of_forall fun y => ?_
      by_cases hy : y = p
      · rw [hy]; simp only [mem_compl_iff, mem_singleton_iff, not_not] at hxp; exact hxp ▸ hx
      · exact h2 hy
    refine ⟨q, ?_⟩
    rw [← hj]
    exact subset_antisymm ((hsub _ _).mp h4.symm.le) ((hsub _ _).mp h4.le)
  choose h hh using hex
  have hmem : ∀ i p, p ∈ b i ↔ h p ∈ b' i := by
    intro i p
    rw [← not_iff_not, ← subset_compl_singleton_iff, ← subset_compl_singleton_iff, ← hip, ← hh]
    exact hsub _ _
  have hcomm : ∀ u p, h (u * p) = u * h p := by
    intro u p
    have e : b (ip (u * p)) = {u} * b (ip p) := by rw [hip, hip, singleton_mul_compl]
    have e' := hrot _ _ u e
    rw [hh, hh, singleton_mul_compl] at e'
    exact Set.singleton_injective (compl_injective e')
  have hlin : ∀ p, h p = p * h 1 := fun p => by simpa using hcomm p 1
  have hr : ∀ i, b' i = {h 1} * b i := by
    intro i
    ext z
    rw [mem_singleton_mul', hmem, hlin, mul_comm (h 1)⁻¹ z, inv_mul_cancel_right]
  -- `r = 1` from the squares of the quarter arc
  obtain ⟨i0, hi0⟩ := hsurj _ isAngular_arcQ
  obtain ⟨j0, hj0⟩ := hsurj _ (isAngular_arcQ.pow two_ne_zero)
  have h1 : {1} * b i0 ^ 2 ⊆ b j0 := by rw [hi0, hj0, singleton_one, one_mul]
  have h2 := (hrel i0 j0 2 1 two_ne_zero).mp h1
  rw [hr, hr, hi0, hj0, singleton_mul_pow, singleton_mul_singleton_mul, one_mul, pow_two,
    ← singleton_mul_singleton_mul] at h2
  have h3 : {h 1} * (arcQ ^ 2) ^ 1 ⊆ arcQ ^ 2 := by
    rw [pow_one]; exact singleton_mul_cancel h2
  obtain ⟨-, h4⟩ := (isAngular_arcQ.pow two_ne_zero).eq_of_subset one_ne_zero h3
  rw [hr, (h4 sq_arcQ_ne_univ).2, singleton_one, one_mul]

/-! ### Autoequivalences of the Frobenioid of angular regions -/

/-- The morphism `A → S¹ × (0, 1]` with `μ = e^{−τ_A}` (of degree `1`). -/
def toI (A : Obj) : A ⟶ iso 0 :=
  mkHom 1 (-A.tip) 1 (subset_univ _) (by simp [iso])

/-- The Frobenius endomorphism `(d, 1)` of `S¹ × (0, 1]`. -/
def frobI (d : ℕ+) : (iso 0 : Obj) ⟶ iso 0 :=
  mkHom d 0 1 (subset_univ _) (by simp [iso])

/-- The linear endomorphism of `S¹ × (0, 1]` with the same `μ` as `e`. -/
def linI (e : (iso 0 : Obj) ⟶ iso 0) : (iso 0 : Obj) ⟶ iso 0 :=
  mkHom 1 e.rad e.rot (subset_univ _) (by
    have := e.tip_le
    simp only [iso, mul_zero, add_zero] at this
    simp [iso, this])

@[simp] lemma toI_deg (A : Obj) : (toI A).deg = 1 := rfl
@[simp] lemma toI_rad (A : Obj) : (toI A).rad = -A.tip := rfl
@[simp] lemma toI_rot (A : Obj) : (toI A).rot = 1 := rfl
@[simp] lemma frobI_deg (d : ℕ+) : (frobI d).deg = d := rfl
@[simp] lemma frobI_rad (d : ℕ+) : (frobI d).rad = 0 := rfl
@[simp] lemma frobI_rot (d : ℕ+) : (frobI d).rot = 1 := rfl
@[simp] lemma linI_deg (e : (iso 0 : Obj) ⟶ iso 0) : (linI e).deg = 1 := rfl
@[simp] lemma linI_rad (e : (iso 0 : Obj) ⟶ iso 0) : (linI e).rad = e.rad := rfl
@[simp] lemma linI_rot (e : (iso 0 : Obj) ⟶ iso 0) : (linI e).rot = e.rot := rfl

/-- Every endomorphism of `S¹ × (0, 1]` is a Frobenius endomorphism followed by a linear one. -/
lemma frobI_comp_linI (e : (iso 0 : Obj) ⟶ iso 0) : frobI e.deg ≫ linI e = e := by
  ext <;> simp

/-- `w_F = rot F(z ↦ z²)`. -/
def wF (F : Obj ⥤ Obj) : Circle := (F.map (frobI 2)).rot

/-- **The rotation `v_A`** attached to `F` at `A`. -/
def vA (F : Obj ⥤ Obj) (A : Obj) : Circle := wF F * (F.map (toI A)).rot

section Auto

variable {F : Obj ⥤ Obj} (hdeg : ∀ {X A : Obj} (k : X ⟶ A), (F.map k).deg = k.deg)
  (hrot : ∀ e : (iso 0 : Obj) ⟶ iso 0, e.deg = 1 → (F.map e).rot = e.rot)

include hdeg in
lemma rot_frobI (d : ℕ+) : (F.map (frobI d)).rot * wF F = wF F ^ (d : ℕ) := by
  have e : frobI d ≫ frobI 2 = frobI 2 ≫ frobI d := by ext <;> simp [mul_comm]
  have h := congrArg Hom.rot ((F.map_comp _ _).symm.trans ((congrArg F.map e).trans
    (F.map_comp _ _)))
  simp only [comp_rot, hdeg, frobI_deg] at h
  apply mul_left_cancel (a := (F.map (frobI d)).rot)
  calc (F.map (frobI d)).rot * ((F.map (frobI d)).rot * wF F)
      = (F.map (frobI 2)).rot * (F.map (frobI d)).rot ^ ((2 : ℕ+) : ℕ) := by
        rw [PNat.val_ofNat, pow_two, wF]; ac_rfl
    _ = _ := by rw [h, wF]

include hdeg hrot in
/-- `rot F(e)·w = rot(e)·w^d` for the endomorphisms `e` of `S¹ × (0, 1]`. -/
lemma rot_endI (e : (iso 0 : Obj) ⟶ iso 0) :
    (F.map e).rot * wF F = e.rot * wF F ^ (e.deg : ℕ) := by
  have h := congrArg Hom.rot (F.map_comp (frobI e.deg) (linI e))
  rw [frobI_comp_linI] at h
  simp only [comp_rot, hdeg, linI_deg, PNat.one_coe, pow_one] at h
  rw [h, hrot _ (linI_deg e), linI_rot, mul_assoc, rot_frobI hdeg]

include hdeg hrot in
/-- **The transformation rule of rotations**: `rot F(k)·v_A = rot(k)·v_X^d` for `k : X → A` of
degree `d`. -/
lemma rot_map_mul {X A : Obj} (k : X ⟶ A) :
    (F.map k).rot * vA F A = k.rot * vA F X ^ (k.deg : ℕ) := by
  let ζ : (iso 0 : Obj) ⟶ iso 0 := mkHom k.deg (k.rad - A.tip + k.deg * X.tip) k.rot
    (subset_univ _) (by have := k.tip_le; simp only [iso, mul_zero, add_zero]; linarith)
  have e : k ≫ toI A = toI X ≫ ζ := by
    ext
    · simp [ζ]
    · simp [ζ]; ring
    · simp [ζ]
  have h := congrArg Hom.rot ((F.map_comp _ _).symm.trans ((congrArg F.map e).trans
    (F.map_comp _ _)))
  simp only [comp_rot, hdeg, toI_deg, PNat.one_coe, pow_one] at h
  have hζ := rot_endI hdeg hrot ζ
  simp only [ζ, mkHom_rot, mkHom_deg] at hζ
  calc (F.map k).rot * vA F A
      = wF F * ((F.map (toI A)).rot * (F.map k).rot) := by rw [vA]; ac_rfl
    _ = (F.map ζ).rot * wF F * (F.map (toI X)).rot ^ (k.deg : ℕ) := by
        rw [h, show ζ.deg = k.deg from rfl]; ac_rfl
    _ = k.rot * vA F X ^ (k.deg : ℕ) := by
        rw [hζ, vA, mul_pow, mul_assoc]

variable (hdiv : ∀ {X A : Obj} (k : X ⟶ A), divVal (F.map k) = divVal k)

include hdeg hrot in
/-- **Incidences**: `{u}·B_X^d ⊆ B_A ⟺ {u}·(v_X B_{FX})^d ⊆ v_A B_{FA}` (`F` full). -/
lemma incid_iff [F.Full] (X A : Obj) (d : ℕ) (u : Circle) (hd : d ≠ 0) :
    {u} * X.ang ^ d ⊆ A.ang ↔
      {u} * ({vA F X} * (F.obj X).ang) ^ d ⊆ {vA F A} * (F.obj A).ang := by
  set d' : ℕ+ := ⟨d, Nat.pos_of_ne_zero hd⟩
  have hd' : (d' : ℕ) = d := rfl
  rw [singleton_mul_pow, singleton_mul_singleton_mul]
  constructor
  · intro h
    let k : X ⟶ A := mkHom d' (A.tip - d * X.tip) u (show {u} * X.ang ^ (d' : ℕ) ⊆ A.ang from h)
      (by simp [hd'])
    have hk := (F.map k).ang_le
    have hR := rot_map_mul hdeg hrot k
    rw [hdeg] at hk
    simp only [k, mkHom_rot, mkHom_deg, hd'] at hk hR
    rw [← hR, mul_comm _ (vA F A), ← singleton_mul_singleton_mul]
    exact mul_subset_mul_left hk
  · intro h
    have h' : {u * vA F X ^ d * (vA F A)⁻¹} * (F.obj X).ang ^ (d' : ℕ) ⊆ (F.obj A).ang := by
      apply singleton_mul_cancel (u := vA F A)
      rw [singleton_mul_singleton_mul, hd']
      convert h using 3
      rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    let g : F.obj X ⟶ F.obj A := mkHom d' ((F.obj A).tip - d * (F.obj X).tip) _ h'
      (by simp [hd'])
    set k := F.preimage g
    have hFk : F.map k = g := F.map_preimage g
    have hkd : k.deg = d' := (hdeg k).symm.trans (by rw [hFk]; rfl)
    have hR := rot_map_mul hdeg hrot k
    rw [hFk, hkd] at hR
    simp only [g, mkHom_rot, hd'] at hR
    have hku : k.rot = u := by
      apply mul_right_cancel (b := vA F X ^ d)
      rw [← hR, mul_assoc, inv_mul_cancel, mul_one]
    have := k.ang_le
    rwa [hku, hkd, hd'] at this

include hdeg hrot in
/-- **`v_A·B_{F A} = B_A`** for every object `A`. -/
theorem ang_eq [F.Full] [F.EssSurj] (hiso : ∀ A, (F.obj A).ang = univ ↔ A.ang = univ) (A : Obj) :
    {vA F A} * (F.obj A).ang = A.ang := by
  refine eq_of_rel Obj.ang (fun A => {vA F A} * (F.obj A).ang) (fun A => A.isAngular)
    (fun X A d u hd => incid_iff hdeg hrot X A d u hd) (fun C hC => ⟨⟨C, hC, 0⟩, rfl⟩)
    (fun C hC => ?_) (fun A => ?_) A
  · let Y : Obj := ⟨C, hC, 0⟩
    have hi := ((isIso_iff (F.objObjPreimageIso Y).hom).mp inferInstance).2.1
    refine ⟨F.objPreimage Y, vA F (F.objPreimage Y) * (F.objObjPreimageIso Y).hom.rot⁻¹, ?_⟩
    rw [singleton_mul_eq_iff] at hi
    rw [hi, singleton_mul_singleton_mul]
  · rw [singleton_mul_eq_univ]
    exact (hiso A).symm

include hdeg hrot hdiv in
/-- **An autoequivalence of the Frobenioid of angular regions preserving degrees, `Div`,
isotropy, and acting trivially on the rotations of the linear endomorphisms of
`S¹ × (0, 1]`, is isomorphic to the identity** (components `(1, e^{τ_A − τ_{FA}} v_A)`). -/
def isoIdOfRigid [F.Full] [F.EssSurj] (hiso : ∀ A, (F.obj A).ang = univ ↔ A.ang = univ) :
    F ≅ 𝟭 Obj :=
  NatIso.ofComponents
    (fun A => isoMk (A.tip - (F.obj A).tip) (vA F A) (ang_eq hdeg hrot hiso A)
      (by change _ = A.tip; ring))
    (fun {X A} k => by
      have hR := rot_map_mul hdeg hrot k
      have hD := hdiv k
      simp only [divVal, hdeg] at hD
      apply hom_ext
      · simp [hdeg, mul_comm]
      · simp only [comp_rad, isoMk_hom_rad, isoMk_hom_deg, Functor.id_map, PNat.one_coe,
          Nat.cast_one, one_mul]
        linarith
      · simp only [comp_rot, isoMk_hom_rot, isoMk_hom_deg, Functor.id_map, PNat.one_coe,
          pow_one]
        rw [mul_comm]
        exact hR)

end Auto

end Angular

/-! ### Automorphisms of `F_v` over the identity of `D_v` -/

open CategoryTheory Iut.Frobenioid Set

/-- In `F_{ℝ_{≥0}}` over `Pt`: morphisms conjugate by isomorphisms have the same degree and
divisor. -/
lemma elem_deg_div_of_comm {a a' b b' : Elem phiReal.{0}} (η : a ⟶ b) (η' : a' ⟶ b') [IsIso η]
    [IsIso η'] (x : a ⟶ a') (y : b ⟶ b') (h : x ≫ η' = η ≫ y) : x.deg = y.deg ∧ x.div = y.div := by
  obtain ⟨hη0, hη1⟩ := elem_isIso_div_deg η
  obtain ⟨hη0', hη1'⟩ := elem_isIso_div_deg η'
  have hd := congrArg Elem.Hom.deg h
  have hv := congrArg (fun φ : a ⟶ b' => (Elem.Hom.div φ).down) h
  simp only [Elem.comp_deg, hη1, hη1', one_mul, mul_one] at hd
  simp only [Elem.comp_div, hη1', PNat.one_coe, one_smul, ULift.add_down] at hv
  refine ⟨hd, ULift.ext _ _ ?_⟩
  change η'.div.down + x.div.down = y.div.down + (y.deg : ℕ) • η.div.down at hv
  rw [hη0, hη0'] at hv
  change (0 : ℝ) + x.div.down = y.div.down + (y.deg : ℕ) • (0 : ℝ) at hv
  rw [smul_zero] at hv
  linarith

namespace FArcData.Iso

open Angular

variable (f : FArcData.Iso fArcModel fArcModel)

/-- `f` preserves Frobenius degrees and `Div` of all morphisms (`commP`, `phi_apply`). -/
theorem deg_divVal_map {X A : Obj} (k : X ⟶ A) :
    (f.F.C.functor.map k).deg = k.deg ∧ divVal (f.F.C.functor.map k) = divVal k := by
  have h := elem_deg_div_of_comm ((FrobCat.sqIso f.F.commP).hom.app X)
    ((FrobCat.sqIso f.F.commP).hom.app A) _ _ ((FrobCat.sqIso f.F.commP).hom.naturality k)
  refine ⟨h.1, ?_⟩
  have h2 := congrArg ULift.down h.2
  refine h2.trans ?_
  change (f.F.phi _ ⟨divVal k⟩).down = divVal k
  rw [f.phi_apply]

/-- If `c_S = id`, `f` acts trivially on the rotations of the linear endomorphisms of
`S¹ × (0, 1]`. -/
theorem rot_map_of_conjC (hc : ∀ z, f.conjC z = z) (e : (iso 0 : Obj) ⟶ iso 0) (he : e.deg = 1) :
    (f.F.C.functor.map e).rot = e.rot := by
  have h := f.val_map_conjC (iso 0) isIsotropic_iso0 ⟨e, (mem_orhd e).mpr he⟩
  rw [hc] at h
  exact (polar_unique h).2

/-- `f` preserves and reflects isotropic objects. -/
theorem ang_univ_iff (A : Obj) : (f.F.C.functor.obj A).ang = univ ↔ A.ang = univ := by
  constructor
  · intro h
    exact (isIsotropic_iff _).mp (isIsotropic_of_iso (f.F.C.unitIso.app A)
      (f.inv_iso _ ((isIsotropic_iff _).mpr h)))
  · intro h
    exact (isIsotropic_iff _).mp (f.map_iso A ((isIsotropic_iff A).mpr h))

/-- **The natural isomorphism `F ≅ 𝟭`** for an automorphism `f` of `F_v` with `c_S = id`. -/
def isoId (hc : ∀ z, f.conjC z = z) : (f.F.C.functor : Obj ⥤ Obj) ≅ 𝟭 Obj :=
  isoIdOfRigid (F := (f.F.C.functor : Obj ⥤ Obj)) (fun k => (f.deg_divVal_map k).1)
    (f.rot_map_of_conjC hc) (fun k => (f.deg_divVal_map k).2) f.ang_univ_iff

/-- **An automorphism of `F_v` with `c_S = id` is 2-isomorphic to the identity** (its
Frobenioid part). -/
def hom2OfConjId (hc : ∀ z, f.conjC z = z) : FrobCat.Iso.Hom2 f.F (FrobCat.Iso.refl _) where
  α := f.isoId hc
  β := NatIso.ofComponents (fun _ => Discrete.eqToIso (Subsingleton.elim _ _))
    (fun _ => rfl)
  phi_compat A x := (f.phi_apply A x).symm
  commP_compat x := elem_iso_hom_eq
    (fArcModel.F.P.mapIso ((f.isoId hc).app x) ≪≫
      (FrobCat.sqIso (FrobCat.Iso.refl fArcModel.F).commP).app x)
    ((FrobCat.sqIso f.F.commP).app x ≪≫ FrobCat.elemIsoOfBase _)

end FArcData.Iso

namespace FArcData.IsoClass

variable {X Y Z : FArcData}

lemma toD_trans (a : IsoClass X Y) (b : IsoClass Y Z) : (a.trans b).toD = a.toD.trans b.toD := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  rfl

lemma toD_symm (a : IsoClass X Y) : a.symm.toD = a.toD.symm := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  rfl

/-- **IUT I, Corollary 5.3 (ii), injectivity at `v ∈ V^arc`, for the model**: an automorphism of
`F_v` is determined, up to 2-isomorphism, by the induced automorphism of `D_v`. -/
theorem toD_injective_model :
    Function.Injective (toD : IsoClass fArcModel fArcModel → ellModel.Iso ellModel) := by
  have key : ∀ a : IsoClass fArcModel fArcModel, a.toD = EllSp.Iso.refl _ → a = refl _ := by
    intro a ha
    obtain ⟨f, rfl⟩ := mk_surjective a
    rw [toD_mk] at ha
    have hS : ∀ x, f.S.e x = x := fun x => by rw [ha]; rfl
    exact mk_eq_mk.2 ⟨⟨f.hom2OfConjId fun z => ellConj_of_id f.S hS ptE z⟩, by rw [ha]; rfl⟩
  intro a b h
  have h1 : (a.trans b.symm).toD = EllSp.Iso.refl _ := by
    rw [toD_trans, toD_symm, h]
    exact EllSp.Iso.ext' b.toD.e.self_trans_symm
  calc a = (a.trans b.symm).trans b := by rw [trans_assoc, symm_trans, trans_refl]
    _ = b := by rw [key _ h1, refl_trans]

end FArcData.IsoClass

/-- **IUT I, Corollary 5.3 (ii), injectivity at `v ∈ V^arc`**. -/
theorem FArcComp.isoClassToD_injective (X Y : FArcComp) :
    Function.Injective (FArcData.IsoClass.toD : FArcData.IsoClass X.X Y.X → X.X.S.Iso Y.X.S) := by
  intro a b h
  set mX := FArcData.IsoClass.mk X.model
  set mY := FArcData.IsoClass.mk Y.model
  have key : mX.symm.trans (a.trans mY) = mX.symm.trans (b.trans mY) := by
    apply FArcData.IsoClass.toD_injective_model
    rw [FArcData.IsoClass.toD_trans, FArcData.IsoClass.toD_trans, FArcData.IsoClass.toD_trans,
      FArcData.IsoClass.toD_trans, h]
  have e : ∀ c : FArcData.IsoClass X.X Y.X, c = mX.trans ((mX.symm.trans (c.trans mY)).trans
      mY.symm) := fun c => by
    rw [FArcData.IsoClass.trans_assoc, FArcData.IsoClass.trans_assoc,
      FArcData.IsoClass.trans_symm, FArcData.IsoClass.trans_refl,
      FArcData.IsoClass.trans_symm_trans]
  rw [e a, e b, key]

/-- **IUT I, Corollary 5.3 (ii) at `v ∈ V^arc`** ([AbsTopIII], Proposition 4.2 (i)):
`Isom(‡F_v, ‡F'_v) → Isom(‡D_v, ‡D'_v)` is bijective. -/
theorem FArcComp.isoClassToD_bijective (X Y : FArcComp) :
    Function.Bijective (FArcData.IsoClass.toD : FArcData.IsoClass X.X Y.X → X.X.S.Iso Y.X.S) :=
  ⟨FArcComp.isoClassToD_injective X Y, FArcComp.isoClassToD_surjective X Y⟩

/-- **IUT I, Corollary 5.3 (ii), over all of `V`** (l.9891–9894):
`Isom(¹F, ²F) → Isom(¹D, ²D)` is bijective. Inputs at `V^non` as in
`FStripNon.isoClassToD_bijective` (`DeltaCharacteristic`, H3, `PivCountable` at `V^bad`); none at
`V^arc`. -/
theorem FStrip.isoClassToD_bijective {D : InitialThetaData.{0}}
    (hΔ : ∀ v : Vnon D, DeltaCharacteristic D v) (h3 : ∀ v : Vnon D, PiToGQuotient D v)
    (hc : ∀ v : Vnon D, v ∈ D.VBad → PivCountable D v) (P Q : FStrip D) :
    Function.Bijective (FStrip.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) := by
  refine ⟨fun a b h => ?_, FStrip.isoClassToD_surjective hΔ h3 hc P Q⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext ((FStripNon.isoClassToD_bijective hΔ h3 hc P.non Q.non).1 h1) (funext fun v => ?_)
  exact FArcComp.isoClassToD_injective (P.arc v) (Q.arc v) (congrFun h2 v)

end PrimeStrip

end Multiradial

end Iut
