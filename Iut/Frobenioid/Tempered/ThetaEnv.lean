/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BiKummer
import Iut.EtaleTheta.MonoTheta

/-!
# Frobenioid-theoretic theta environments ([EtTh], §5: `E_N`, Lemma 5.9(i),(ii),(iv))

[EtTh], discussion after Remark 5.7.1: for the `N`-th root `s⊓_N, s⊔_N : A_N → B_N` of a right
fraction-pair of an `l`-th root of the theta function and the homomorphism `str^trv_N` of a
base-Frobenius pair of `A_N`, the bi-Kummer root `s⊓-gp_N : Aut_D(B^bs_N) → Aut_C(B_N)` (defined on
all of `Aut_D(B^bs_N)`, since `Div(s⊓_N)` descends to `A`) and `s⊔-gp_N : H_{B_N} → Aut_C(B_N)`
define

  `E_N := s⊓-gp_N(Im Π^tp_Y) · μ_N(B_N) ⊆ Aut_C(B_N)`, `E^Π_N := E_N ×_{Im Π^tp_Y} Π^tp_Y`,

and Lemma 5.9 states: (i) `s⊓-gp_N|_{H_{B_N}}`, `s⊔-gp_N` factor through `E_N`; (ii)
`1 → μ_N(B_N) → E_N → Im(Π^tp_Y) → 1` is exact; (iv) the inclusions `μ_N(B_N) ↪ E_N`,
`Im(Π^tp_Y) ⊆ E_N` (via `s⊓-gp_N`) give an isomorphism `E^Π_N ≅ Π^tp_Y[μ_N]`, under which the
homomorphism `s⊔-Π_N : Π^tp_Ÿ → E^Π_N` determined by `s⊔-gp_N` gives the theta section (the
mono-theta environment).

Here, for a model Frobenioid `C = Model Φ B divB`, with abstract inputs (a group `PX` standing for
`Π^tp_X`, a homomorphism `π : PX → Aut_C(X)/O^×(X)` standing for the outer homomorphism
`Π^tp_X → Aut_D(A^bs_N)`, a section `σ` from a base-Frobenius pair, and subgroups
`PYdd ≤ PY ≤ PX` standing for `Π^tp_Ÿ ⊆ Π^tp_Y ⊆ Π^tp_X`):

* `Model.muN Y N`: `μ_N(Y) ⊆ O^×(Y)`, a normal subgroup of `Aut_C(Y)` (`Model.units_comm`: units
  commute);
* `Model.thetaE`: `E_N = sgp(PY) · μ_N(Y)`, with `Model.mem_unitsAut_iff_mem_muN`
  (**Lemma 5.9(ii)**: `E_N ∩ O^×(Y) = μ_N(Y)`, the kernel of `E_N → Im(PY)`), and
  `Model.tgp_mem_thetaE` (**Lemma 5.9(i)** for `s⊔-gp`; for `s⊓-gp` it is `Model.sgp_mem_thetaE`);
* `Model.thetaEPi`: `E^Π_N` as a subgroup of `Aut_C(Y) × PX`, and `Model.ePiEquiv`
  (**Lemma 5.9(iv)**, group-theoretic part): `μ_N(Y) ⋊ PY ≅ E^Π_N`, `(m, p) ↦ (m · sgp(p), p)`;
* `Model.ePiEquiv_thetaSection` (**Lemma 5.9(iv)**, theta part): `s⊔-Π_N : PYdd → E^Π_N`
  corresponds under `ePiEquiv` to the section `p ↦ (η(p), p)` over `PYdd` for the cocycle
  `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1} ∈ μ_N(Y)`, which is the conjugate of the inverse Kummer unit
  of [EtTh], Proposition 4.3(iii) (`Model.eta_eq`; `Model.eta_mem_muN`).

The topology of `E^Π_N`, the subgroup `D` (outer actions of `l·ℤ` and of `K^×`, Lemma 5.8), the
comparison with MR15's `Env.modelEnv`, Lemma 5.9(iii),(v) and Proposition 5.5 are in
`Iut/Frobenioid/Tempered/ThetaEnvModel.lean`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### `μ_N(Y)` -/

/-- **Units of a model Frobenioid commute** (`O^×(Y) ≅ ker Div_B` is abelian). -/
lemma units_comm {Y : Model Φ B divB} {a b : Aut Y} (ha : a ∈ unitsAut Y) (hb : b ∈ unitsAut Y) :
    a * b = b * a := by
  ext1
  change b.hom ≫ a.hom = a.hom ≫ b.hom
  have ha' : a.hom.base = 𝟙 _ := ha
  have hb' : b.hom.base = 𝟙 _ := hb
  ext
  · simp [mul_comm]
  · simp [ha', hb']
  · simp [div_of_iso, deg_of_iso]
  · simp [ha', hb', deg_of_iso, add_comm]

/-- **`μ_N(Y) ⊆ O^×(Y)`**: the units of order dividing `N` ([FrdII], Definition 2.1(i)). -/
def muN (Y : Model Φ B divB) (N : ℕ) : Subgroup (Aut Y) where
  carrier := {a | a ∈ unitsAut Y ∧ a ^ N = 1}
  mul_mem' {a b} ha hb := ⟨(unitsAut Y).mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (units_comm ha.1 hb.1) N), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨(unitsAut Y).one_mem, one_pow N⟩
  inv_mem' {a} ha := ⟨(unitsAut Y).inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

lemma mem_muN {Y : Model Φ B divB} {N : ℕ} {a : Aut Y} :
    a ∈ muN Y N ↔ a ∈ unitsAut Y ∧ a ^ N = 1 := Iff.rfl

instance (Y : Model Φ B divB) (N : ℕ) : (muN Y N).Normal :=
  ⟨fun a ha g => ⟨(inferInstance : (unitsAut Y).Normal).conj_mem a ha.1 g, by
    rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩

/-- The unit `(1, id, 0, d)` as an element of the group `Aut_C(Y)`. -/
def unitAut (Y : Model Φ B divB) (d : B.obj Y.base) (hd : divB.app _ d = 0) : Aut Y :=
  unitIso Y d hd

lemma unitIso_pow (Y : Model Φ B divB) (d : B.obj Y.base) (hd : divB.app _ d = 0) (n : ℕ) :
    ((unitAut Y d hd) ^ n).hom =
      unitHom Y (n • d) (by rw [map_nsmul, hd, smul_zero]) := by
  induction n with
  | zero =>
    ext
    · rfl
    · rfl
    · rfl
    · change (0 : B.obj Y.base) = 0 • d
      rw [zero_smul]
  | succ n ih =>
    rw [pow_succ]
    change (unitIso Y d hd).hom ≫ ((unitAut Y d hd) ^ n).hom = _
    rw [ih]
    change unitHom Y d hd ≫ _ = _
    rw [unitHom_comp]
    congr 1
    rw [succ_nsmul, add_comm]

/-! ### `E_N` and `E^Π_N` -/

section Theta

variable {X Y : Model Φ B divB} {s t : X ⟶ Y} [IsIso s.base] [IsIso t.base]
  (hs : IsPreStep (toElem Φ B divB) s)
  (ht : IsPreStep (toElem Φ B divB) t) (hb : s.base = t.base)
  {σ : Aut X ⧸ unitsAut X →* Aut X}
  (hsec : ∀ q, (QuotientGroup.mk (σ q) : Aut X ⧸ unitsAut X) = q)
  {PX : Type*} [Group PX] (π : PX →* Aut X ⧸ unitsAut X)
  (hsfix : ∀ q, Φ.pb (σ q).hom.base s.div = s.div) (PY : Subgroup PX) (N : ℕ)

/-- `s⊓-gp` on `PX`: the bi-Kummer root of `σ ∘ π` along `s` ([EtTh], Proposition 4.3(i)). -/
noncomputable abbrev sgp : PX →* Aut Y := liftGp hs (σ.comp π) (fun p => hsfix (π p))

include hsec in
/-- `s⊓-gp(p)` is a unit only for `p ∈ ker π`, in which case it is `1`. -/
lemma sgp_eq_one_of_mem {p : PX} (hp : sgp hs π hsfix p ∈ unitsAut Y) :
    sgp hs π hsfix p = 1 := by
  have hbase : (sgp hs π hsfix p).hom.base = 𝟙 _ := hp
  change (liftHom s hs.1 (σ (π p)) (hsfix (π p))).base = 𝟙 _ at hbase
  simp only [liftHom, mk1_base] at hbase
  have h1 : (σ (π p)).hom.base = 𝟙 _ := by
    have := congrArg (fun f => s.base ≫ f ≫ inv s.base) hbase
    simpa using this
  have hq : π p = 1 := by
    rw [← hsec (π p)]
    exact (QuotientGroup.eq_one_iff _).2 h1
  have h1' : σ (π p) = 1 := by rw [hq, map_one]
  ext1
  apply cancel_preStep_left hs
  rw [liftGp_spec hs (σ.comp π) (fun p => hsfix (π p)) p, MonoidHom.comp_apply, h1']
  change 𝟙 X ≫ s = s ≫ 𝟙 Y
  simp

lemma sgp_eq_one_of_ker {p : PX} (hp : π p = 1) : sgp hs π hsfix p = 1 := by
  ext1
  apply cancel_preStep_left hs
  rw [liftGp_spec hs (σ.comp π) (fun p => hsfix (π p)) p, MonoidHom.comp_apply, hp, map_one]
  change 𝟙 X ≫ s = s ≫ 𝟙 Y
  simp

/-- **`E_N = s⊓-gp(PY) · μ_N(Y)`** ([EtTh], §5, before Lemma 5.8). -/
def thetaE : Subgroup (Aut Y) where
  carrier := {e | ∃ m ∈ muN Y N, ∃ p ∈ PY, e = m * sgp hs π hsfix p}
  mul_mem' := by
    rintro _ _ ⟨m, hm, p, hp, rfl⟩ ⟨m', hm', p', hp', rfl⟩
    refine ⟨m * (sgp hs π hsfix p * m' * (sgp hs π hsfix p)⁻¹),
      (muN Y N).mul_mem hm ((inferInstance : (muN Y N).Normal).conj_mem m' hm' _), p * p',
      PY.mul_mem hp hp', ?_⟩
    rw [map_mul]
    group
  one_mem' := ⟨1, (muN Y N).one_mem, 1, PY.one_mem, by rw [map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨m, hm, p, hp, rfl⟩
    refine ⟨(sgp hs π hsfix p)⁻¹ * m⁻¹ * sgp hs π hsfix p,
      (by simpa using (inferInstance : (muN Y N).Normal).conj_mem m⁻¹ ((muN Y N).inv_mem hm)
            (sgp hs π hsfix p)⁻¹), p⁻¹, PY.inv_mem hp, ?_⟩
    rw [map_inv]
    group

lemma muN_le_thetaE : muN Y N ≤ thetaE hs π hsfix PY N :=
  fun m hm => ⟨m, hm, 1, PY.one_mem, by rw [map_one, mul_one]⟩

lemma sgp_mem_thetaE {p : PX} (hp : p ∈ PY) : sgp hs π hsfix p ∈ thetaE hs π hsfix PY N :=
  ⟨1, (muN Y N).one_mem, p, hp, by rw [one_mul]⟩

include hsec in
/-- **[EtTh], Lemma 5.9(ii)**: the kernel of `E_N → Im(PY)` (the units in `E_N`) is `μ_N(Y)`. -/
theorem mem_unitsAut_iff_mem_muN {e : Aut Y} (he : e ∈ thetaE hs π hsfix PY N) :
    e ∈ unitsAut Y ↔ e ∈ muN Y N := by
  refine ⟨fun hu => ?_, fun hm => hm.1⟩
  obtain ⟨m, hm, p, -, rfl⟩ := he
  have hp : sgp hs π hsfix p ∈ unitsAut Y := by
    have := (unitsAut Y).mul_mem ((unitsAut Y).inv_mem hm.1) hu
    rwa [inv_mul_cancel_left] at this
  rw [sgp_eq_one_of_mem hs hsec π hsfix hp, mul_one]
  exact hm

/-- **`E^Π_N = E_N ×_{Im PY} PY`** ([EtTh], Lemma 5.9(iv)), as the subgroup of `Aut_C(Y) × PX` of
pairs `(e, p)` with `p ∈ PY`, `e ∈ E_N` lying over the image of `p` (`Base(e) = Base(s⊓-gp(p))`).
For `PY = ⊤` this is the corresponding extension of all of `PX` (the group through which the
outer action of `PX/PY` of [EtTh], Lemma 5.9(iii), acts). -/
def thetaEPi : Subgroup (Aut Y × PX) where
  carrier := {x | x.2 ∈ PY ∧ x.1 ∈ thetaE hs π hsfix PY N ∧
    x.1.hom.base = (sgp hs π hsfix x.2).hom.base}
  mul_mem' {x y} hx hy := ⟨PY.mul_mem hx.1 hy.1,
    (thetaE hs π hsfix PY N).mul_mem hx.2.1 hy.2.1, by
    change (y.1.hom ≫ x.1.hom).base = (sgp hs π hsfix (x.2 * y.2)).hom.base
    rw [map_mul]
    change (y.1.hom ≫ x.1.hom).base = ((sgp hs π hsfix y.2).hom ≫ (sgp hs π hsfix x.2).hom).base
    rw [comp_base, comp_base, hx.2.2, hy.2.2]⟩
  one_mem' := ⟨PY.one_mem, (thetaE hs π hsfix PY N).one_mem, by
    change (1 : Aut Y).hom.base = (sgp hs π hsfix 1).hom.base
    rw [map_one]⟩
  inv_mem' {x} hx := ⟨PY.inv_mem hx.1, (thetaE hs π hsfix PY N).inv_mem hx.2.1, by
    change x.1.inv.base = (sgp hs π hsfix x.2⁻¹).hom.base
    rw [map_inv]
    change x.1.inv.base = (sgp hs π hsfix x.2).inv.base
    have h1 := hom_base_inv_of_iso x.1
    have h2 := inv_base_of_iso (sgp hs π hsfix x.2)
    rw [hx.2.2] at h1
    have := congrArg ((sgp hs π hsfix x.2).inv.base ≫ ·) h1
    simp only [← Category.assoc, h2, Category.id_comp, Category.comp_id] at this
    exact this⟩

lemma mem_thetaEPi {x : Aut Y × PX} : x ∈ thetaEPi hs π hsfix PY N ↔ x.2 ∈ PY ∧
    x.1 ∈ thetaE hs π hsfix PY N ∧ x.1.hom.base = (sgp hs π hsfix x.2).hom.base := Iff.rfl

/-- The conjugation action of `PY` on `μ_N(Y)` through `s⊓-gp`. -/
noncomputable abbrev muAct : PY →* MulAut (muN Y N) :=
  (MulAut.conjNormal (H := muN Y N)).comp ((sgp hs π hsfix).comp PY.subtype)

/-- The map `μ_N(Y) ⋊ PY → E^Π_N`, `(m, p) ↦ (m · s⊓-gp(p), p)`. -/
noncomputable def ePiHom : muN Y N ⋊[muAct hs π hsfix PY N] PY →* thetaEPi hs π hsfix PY N where
  toFun x := ⟨((x.left : Aut Y) * sgp hs π hsfix x.right, x.right),
    ⟨x.right.2, ⟨x.left, x.left.2, x.right, x.right.2, rfl⟩, by
      change ((sgp hs π hsfix x.right).hom ≫ (x.left : Aut Y).hom).base = _
      rw [comp_base, show (x.left : Aut Y).hom.base = 𝟙 _ from x.left.2.1, Category.comp_id]⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · change ((1 : muN Y N) : Aut Y) * sgp hs π hsfix ((1 : PY) : PX) = 1
      simp
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change ((x * y).left : Aut Y) * sgp hs π hsfix ((x * y).right : PX) =
        ((x.left : Aut Y) * sgp hs π hsfix x.right) * ((y.left : Aut Y) * sgp hs π hsfix y.right)
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
        MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply, map_mul,
        Subgroup.coe_subtype]
      group
    · rfl

include hsec in
lemma ePiHom_bijective : Function.Bijective (ePiHom hs π hsfix PY N) := by
  constructor
  · intro x y h
    have h' := congrArg Subtype.val h
    have h1 : (x.left : Aut Y) * sgp hs π hsfix x.right =
        (y.left : Aut Y) * sgp hs π hsfix y.right :=
      congrArg Prod.fst h'
    have h2 : (x.right : PX) = y.right := congrArg Prod.snd h'
    rw [h2, mul_left_inj] at h1
    exact SemidirectProduct.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨⟨e, p⟩, hp, he, hbase⟩
    have hm : e * (sgp hs π hsfix p)⁻¹ ∈ muN Y N := by
      refine (mem_unitsAut_iff_mem_muN hs hsec π hsfix PY N
        ((thetaE hs π hsfix PY N).mul_mem he
          ((thetaE hs π hsfix PY N).inv_mem (sgp_mem_thetaE hs π hsfix PY N hp)))).1 ?_
      change ((sgp hs π hsfix p)⁻¹.hom ≫ e.hom).base = 𝟙 _
      change ((sgp hs π hsfix p).inv ≫ e.hom).base = 𝟙 _
      rw [comp_base, hbase, inv_base_of_iso]
    refine ⟨⟨⟨_, hm⟩, ⟨p, hp⟩⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change e * (sgp hs π hsfix p)⁻¹ * sgp hs π hsfix p = e
      group
    · rfl

/-- **[EtTh], Lemma 5.9(iv)** (group-theoretic part): `μ_N(Y) ⋊ PY ≅ E^Π_N`,
`(m, p) ↦ (m · s⊓-gp(p), p)`. -/
noncomputable def ePiEquiv : muN Y N ⋊[muAct hs π hsfix PY N] PY ≃* thetaEPi hs π hsfix PY N :=
  MulEquiv.ofBijective (ePiHom hs π hsfix PY N) (ePiHom_bijective hs hsec π hsfix PY N)

lemma ePiEquiv_apply (x : muN Y N ⋊[muAct hs π hsfix PY N] PY) :
    ((ePiEquiv hs hsec π hsfix PY N x : thetaEPi hs π hsfix PY N) : Aut Y × PX) =
      ((x.left : Aut Y) * sgp hs π hsfix x.right, (x.right : PX)) := rfl

/-! ### The theta section (`s⊔-Π`) -/

variable {PY} {PYdd : Subgroup PX} (hle : PYdd ≤ PY)
  (htfix : ∀ p : PYdd, Φ.pb (σ (π p)).hom.base t.div = t.div)

/-- `s⊔-gp` on `PYdd`: the bi-Kummer root of `σ ∘ π` along `t`. -/
noncomputable abbrev tgp : PYdd →* Aut Y :=
  liftGp ht ((σ.comp π).comp PYdd.subtype) htfix

include hb in
lemma tgp_base (p : PYdd) : (tgp ht π htfix p).hom.base = (sgp hs π hsfix p).hom.base := by
  change (liftHom t ht.1 (σ (π p)) (htfix p)).base = (liftHom s hs.1 (σ (π p)) (hsfix (π p))).base
  simp only [liftHom, mk1_base, hb]

include hb in
/-- `s⊔-gp(p) · s⊓-gp(p)^{-1}` is a unit of `Y`. -/
lemma tgp_mul_sgp_inv_mem_units (p : PYdd) :
    tgp ht π htfix p * (sgp hs π hsfix p)⁻¹ ∈ unitsAut Y := by
  change ((sgp hs π hsfix p).inv ≫ (tgp ht π htfix p).hom).base = 𝟙 _
  rw [comp_base, tgp_base hs ht hb π hsfix htfix, inv_base_of_iso]

/-- **The theta cocycle** `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1}`. -/
noncomputable def eta (p : PYdd) : Aut Y := tgp ht π htfix p * (sgp hs π hsfix (p : PX) : Aut Y)⁻¹

include hb in
/-- **`η` is the conjugate of the inverse Kummer unit** ([EtTh], Proposition 4.3(iii)):
`η(p) = s⊓-gp(p) · κ(p)^{-1} · s⊓-gp(p)^{-1}` with `κ(p) = (1, id, 0, kummerUnit s t (σ π p))`. -/
theorem eta_eq (p : PYdd) :
      eta hs ht π hsfix htfix p = sgp hs π hsfix p *
      (unitAut Y (kummerUnit s t (σ (π p)))
        (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p)))⁻¹ *
        (sgp hs π hsfix (p : PX) : Aut Y)⁻¹ := by
  rw [eta, mul_left_inj]
  -- `κ ≫ s⊔-gp = s⊓-gp`, i.e. `s⊓-gp = s⊔-gp * κ` in `Aut Y`
  have key : sgp hs π hsfix p = tgp ht π htfix p *
      unitAut Y (kummerUnit s t (σ (π p))) (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p)) := by
    ext1
    exact (unit_comp_liftAut hs ht hb (σ (π p)) (hsfix _) (htfix p)).symm
  rw [key, mul_inv_cancel_right]

include hb in
/-- `η(p)` lies in `μ_N(Y)` when `Base(σ π p)` fixes `N·F`, `F = u_s − u_t` (the fraction of the
`N`-th root, whose `N`-th power `f` is fixed by `PYdd`). -/
lemma eta_mem_muN (hFN : ∀ p : PYdd, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))
    (p : PYdd) : eta hs ht π hsfix htfix p ∈ muN Y N := by
  refine ⟨tgp_mul_sgp_inv_mem_units hs ht hb π hsfix htfix p, ?_⟩
  rw [eta_eq hs ht hb π hsfix htfix p, conj_pow, inv_pow]
  have hκ : (unitAut Y (kummerUnit s t (σ (π p)))
      (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p))) ^ N = 1 := by
    ext1
    rw [unitIso_pow]
    have h0 : N • kummerUnit s t (σ (π p)) = 0 := nsmul_kummerUnit _ N (hFN p)
    change unitHom Y _ _ = 𝟙 Y
    simp only [h0]
    ext <;> simp [unitHom]
  rw [hκ, inv_one, mul_one, mul_inv_cancel]

variable (hFN : ∀ p : PYdd, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))

include hb hle hFN in
/-- **[EtTh], Lemma 5.9(i)** for `s⊔-gp`: its values lie in `E_N`. -/
lemma tgp_mem_thetaE (p : PYdd) : tgp ht π htfix p ∈ thetaE hs π hsfix PY N :=
  ⟨_, eta_mem_muN hs ht hb π hsfix N htfix hFN p, p, hle p.2,
    by rw [eta, inv_mul_cancel_right]⟩

/-- **`s⊔-Π : PYdd → E^Π_N`**, `p ↦ (s⊔-gp(p), p)` ([EtTh], Lemma 5.9(iv)). -/
noncomputable def tPi : PYdd →* thetaEPi hs π hsfix PY N where
  toFun p := ⟨(tgp ht π htfix p, p), hle p.2, tgp_mem_thetaE hs ht hb π hsfix N hle htfix hFN p,
    tgp_base hs ht hb π hsfix htfix p⟩
  map_one' := by ext <;> simp
  map_mul' p p' := by ext <;> simp

/-- **[EtTh], Lemma 5.9(iv)** (theta part): under `μ_N(Y) ⋊ PY ≅ E^Π_N`, `s⊔-Π` is the section
`p ↦ (η(p), p)` over `PYdd`, `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1} ∈ μ_N(Y)` (`eta_eq`: the conjugate
of the inverse Kummer unit). -/
theorem ePiEquiv_thetaSection (p : PYdd) :
    ePiEquiv hs hsec π hsfix PY N
      ⟨⟨eta hs ht π hsfix htfix p, eta_mem_muN hs ht hb π hsfix N htfix hFN p⟩, ⟨p, hle p.2⟩⟩ =
      tPi hs ht hb π hsfix N hle htfix hFN p := by
  apply Subtype.ext
  rw [ePiEquiv_apply]
  change (eta hs ht π hsfix htfix p * sgp hs π hsfix p, (p : PX)) = (tgp ht π htfix p, (p : PX))
  rw [eta, inv_mul_cancel_right]

end Theta

end Model

end Frobenioid

end Iut
