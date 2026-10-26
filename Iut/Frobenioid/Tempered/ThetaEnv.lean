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

Here, for a model Frobenioid `C = Model Φ B divB`, with abstract inputs (a group `P` standing for
`Π^tp_Y`, a homomorphism `π : P → Aut_C(X)/O^×(X)` standing for `Π^tp_Y → Aut_D(A^bs_N)`, a
section `σ` from a base-Frobenius pair, and a subgroup `Q ≤ P` standing for `Π^tp_Ÿ`):

* `Model.muN Y N`: `μ_N(Y) ⊆ O^×(Y)`, a normal subgroup of `Aut_C(Y)` (`Model.units_comm`: units
  commute);
* `Model.thetaE`: `E_N = sgp(P) · μ_N(Y)`, with `Model.mem_unitsAut_iff_mem_muN`
  (**Lemma 5.9(ii)**: `E_N ∩ O^×(Y) = μ_N(Y)`, the kernel of `E_N → Im(P)`), and
  `Model.tgp_mem_thetaE` (**Lemma 5.9(i)** for `s⊔-gp`; for `s⊓-gp` it is `Model.sgp_mem_thetaE`);
* `Model.thetaEPi`: `E^Π_N` as a subgroup of `Aut_C(Y) × P`, and `Model.ePiEquiv`
  (**Lemma 5.9(iv)**, group-theoretic part): `μ_N(Y) ⋊ P ≅ E^Π_N`, `(m, p) ↦ (m · sgp(p), p)`;
* `Model.ePiEquiv_thetaSection` (**Lemma 5.9(iv)**, theta part): `s⊔-Π_N : Q → E^Π_N` corresponds
  under `ePiEquiv` to the section `sectionOf η` of `μ_N(Y) ⋊ P` over `Q` for the cocycle
  `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1} ∈ μ_N(Y)`, which is the conjugate of the inverse Kummer unit
  of [EtTh], Proposition 4.3(iii) (`Model.eta_eq`; `Model.eta_mem_muN`).

Not yet done: the topology of `E^Π_N`, the subgroup `D` of [EtTh], Lemma 5.9(iv) (outer actions
of `l·ℤ` and of `K^×`, Lemma 5.8), the comparison with MR15's `Env.modelEnv`, and Lemma 5.9(v) /
Proposition 5.5 (cyclotomic rigidity, needing [EtTh], Proposition 5.2(iii)).
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
  {P : Type*} [Group P] (π : P →* Aut X ⧸ unitsAut X)
  (hsfix : ∀ q, Φ.pb (σ q).hom.base s.div = s.div) (N : ℕ)

/-- `s⊓-gp` on `P`: the bi-Kummer root of `σ ∘ π` along `s` ([EtTh], Proposition 4.3(i)). -/
noncomputable abbrev sgp : P →* Aut Y := liftGp hs (σ.comp π) (fun p => hsfix (π p))

include hsec in
/-- `s⊓-gp(p)` is a unit only for `p ∈ ker π`, in which case it is `1`. -/
lemma sgp_eq_one_of_mem {p : P} (hp : sgp hs π hsfix p ∈ unitsAut Y) :
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

/-- **`E_N = s⊓-gp(P) · μ_N(Y)`** ([EtTh], §5, before Lemma 5.8). -/
def thetaE : Subgroup (Aut Y) where
  carrier := {e | ∃ m ∈ muN Y N, ∃ p, e = m * sgp hs π hsfix p}
  mul_mem' := by
    rintro _ _ ⟨m, hm, p, rfl⟩ ⟨m', hm', p', rfl⟩
    refine ⟨m * (sgp hs π hsfix p * m' * (sgp hs π hsfix p)⁻¹),
      (muN Y N).mul_mem hm ((inferInstance : (muN Y N).Normal).conj_mem m' hm' _), p * p', ?_⟩
    rw [map_mul]
    group
  one_mem' := ⟨1, (muN Y N).one_mem, 1, by rw [map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨m, hm, p, rfl⟩
    refine ⟨(sgp hs π hsfix p)⁻¹ * m⁻¹ * sgp hs π hsfix p,
      (by simpa using (inferInstance : (muN Y N).Normal).conj_mem m⁻¹ ((muN Y N).inv_mem hm)
            (sgp hs π hsfix p)⁻¹), p⁻¹, ?_⟩
    rw [map_inv]
    group

lemma muN_le_thetaE : muN Y N ≤ thetaE hs π hsfix N :=
  fun m hm => ⟨m, hm, 1, by rw [map_one, mul_one]⟩

lemma sgp_mem_thetaE (p : P) : sgp hs π hsfix p ∈ thetaE hs π hsfix N :=
  ⟨1, (muN Y N).one_mem, p, by rw [one_mul]⟩

include hsec in
/-- **[EtTh], Lemma 5.9(ii)**: the kernel of `E_N → Im(P)` (the units in `E_N`) is `μ_N(Y)`. -/
theorem mem_unitsAut_iff_mem_muN {e : Aut Y} (he : e ∈ thetaE hs π hsfix N) :
    e ∈ unitsAut Y ↔ e ∈ muN Y N := by
  refine ⟨fun hu => ?_, fun hm => hm.1⟩
  obtain ⟨m, hm, p, rfl⟩ := he
  have hp : sgp hs π hsfix p ∈ unitsAut Y := by
    have := (unitsAut Y).mul_mem ((unitsAut Y).inv_mem hm.1) hu
    rwa [inv_mul_cancel_left] at this
  rw [sgp_eq_one_of_mem hs hsec π hsfix hp, mul_one]
  exact hm

/-- **`E^Π_N = E_N ×_{Im P} P`** ([EtTh], Lemma 5.9(iv)), as the subgroup of `Aut_C(Y) × P` of
pairs `(e, p)` with `e ∈ E_N` lying over the image of `p` (`Base(e) = Base(s⊓-gp(p))`). -/
def thetaEPi : Subgroup (Aut Y × P) where
  carrier := {x | x.1 ∈ thetaE hs π hsfix N ∧ x.1.hom.base = (sgp hs π hsfix x.2).hom.base}
  mul_mem' {x y} hx hy := ⟨(thetaE hs π hsfix N).mul_mem hx.1 hy.1, by
    change (y.1.hom ≫ x.1.hom).base = (sgp hs π hsfix (x.2 * y.2)).hom.base
    rw [map_mul]
    change (y.1.hom ≫ x.1.hom).base = ((sgp hs π hsfix y.2).hom ≫ (sgp hs π hsfix x.2).hom).base
    rw [comp_base, comp_base, hx.2, hy.2]⟩
  one_mem' := ⟨(thetaE hs π hsfix N).one_mem, by
    change (1 : Aut Y).hom.base = (sgp hs π hsfix 1).hom.base
    rw [map_one]⟩
  inv_mem' {x} hx := ⟨(thetaE hs π hsfix N).inv_mem hx.1, by
    change x.1.inv.base = (sgp hs π hsfix x.2⁻¹).hom.base
    rw [map_inv]
    change x.1.inv.base = (sgp hs π hsfix x.2).inv.base
    have h1 := hom_base_inv_of_iso x.1
    have h2 := inv_base_of_iso (sgp hs π hsfix x.2)
    rw [hx.2] at h1
    have := congrArg ((sgp hs π hsfix x.2).inv.base ≫ ·) h1
    simp only [← Category.assoc, h2, Category.id_comp, Category.comp_id] at this
    exact this⟩

/-- The conjugation action of `P` on `μ_N(Y)` through `s⊓-gp`. -/
noncomputable abbrev muAct : P →* MulAut (muN Y N) :=
  (MulAut.conjNormal (H := muN Y N)).comp (sgp hs π hsfix)

/-- The map `μ_N(Y) ⋊ P → E^Π_N`, `(m, p) ↦ (m · s⊓-gp(p), p)`. -/
noncomputable def ePiHom : muN Y N ⋊[muAct hs π hsfix N] P →* thetaEPi hs π hsfix N where
  toFun x := ⟨((x.left : Aut Y) * sgp hs π hsfix x.right, x.right),
    ⟨⟨x.left, x.left.2, x.right, rfl⟩, by
      change ((sgp hs π hsfix x.right).hom ≫ (x.left : Aut Y).hom).base = _
      rw [comp_base, show (x.left : Aut Y).hom.base = 𝟙 _ from x.left.2.1, Category.comp_id]⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · change ((1 : muN Y N) : Aut Y) * sgp hs π hsfix 1 = 1
      simp
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change ((x * y).left : Aut Y) * sgp hs π hsfix (x * y).right =
        ((x.left : Aut Y) * sgp hs π hsfix x.right) * ((y.left : Aut Y) * sgp hs π hsfix y.right)
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
        MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply, map_mul]
      group
    · rfl

include hsec in
lemma ePiHom_bijective : Function.Bijective (ePiHom hs π hsfix N) := by
  constructor
  · intro x y h
    have h' := congrArg Subtype.val h
    have h1 : (x.left : Aut Y) * sgp hs π hsfix x.right =
        (y.left : Aut Y) * sgp hs π hsfix y.right :=
      congrArg Prod.fst h'
    have h2 : x.right = y.right := congrArg Prod.snd h'
    rw [h2, mul_left_inj] at h1
    exact SemidirectProduct.ext (Subtype.ext h1) h2
  · rintro ⟨⟨e, p⟩, he, hbase⟩
    have hm : e * (sgp hs π hsfix p)⁻¹ ∈ muN Y N := by
      refine (mem_unitsAut_iff_mem_muN hs hsec π hsfix N
        ((thetaE hs π hsfix N).mul_mem he
          ((thetaE hs π hsfix N).inv_mem (sgp_mem_thetaE hs π hsfix N p)))).1 ?_
      change ((sgp hs π hsfix p)⁻¹.hom ≫ e.hom).base = 𝟙 _
      change ((sgp hs π hsfix p).inv ≫ e.hom).base = 𝟙 _
      rw [comp_base, hbase, inv_base_of_iso]
    refine ⟨⟨⟨_, hm⟩, p⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change e * (sgp hs π hsfix p)⁻¹ * sgp hs π hsfix p = e
      group
    · rfl

/-- **[EtTh], Lemma 5.9(iv)** (group-theoretic part): `μ_N(Y) ⋊ P ≅ E^Π_N`,
`(m, p) ↦ (m · s⊓-gp(p), p)`. -/
noncomputable def ePiEquiv : muN Y N ⋊[muAct hs π hsfix N] P ≃* thetaEPi hs π hsfix N :=
  MulEquiv.ofBijective (ePiHom hs π hsfix N) (ePiHom_bijective hs hsec π hsfix N)

lemma ePiEquiv_apply (x : muN Y N ⋊[muAct hs π hsfix N] P) :
    ((ePiEquiv hs hsec π hsfix N x : thetaEPi hs π hsfix N) : Aut Y × P) =
      ((x.left : Aut Y) * sgp hs π hsfix x.right, x.right) := rfl

/-! ### The theta section (`s⊔-Π`) -/

variable (Q : Subgroup P) (htfix : ∀ p : Q, Φ.pb (σ (π p)).hom.base t.div = t.div)

/-- `s⊔-gp` on `Q`: the bi-Kummer root of `σ ∘ π` along `t`. -/
noncomputable abbrev tgp : Q →* Aut Y :=
  liftGp ht ((σ.comp π).comp Q.subtype) htfix

include hb in
lemma tgp_base (p : Q) : (tgp ht π Q htfix p).hom.base = (sgp hs π hsfix p).hom.base := by
  change (liftHom t ht.1 (σ (π p)) (htfix p)).base = (liftHom s hs.1 (σ (π p)) (hsfix (π p))).base
  simp only [liftHom, mk1_base, hb]

include hb in
/-- `s⊔-gp(p) · s⊓-gp(p)^{-1}` is a unit of `Y`. -/
lemma tgp_mul_sgp_inv_mem_units (p : Q) :
    tgp ht π Q htfix p * (sgp hs π hsfix p)⁻¹ ∈ unitsAut Y := by
  change ((sgp hs π hsfix p).inv ≫ (tgp ht π Q htfix p).hom).base = 𝟙 _
  rw [comp_base, tgp_base hs ht hb π hsfix Q htfix, inv_base_of_iso]

/-- **The theta cocycle** `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1}`. -/
noncomputable def eta (p : Q) : Aut Y := tgp ht π Q htfix p * (sgp hs π hsfix (p : P) : Aut Y)⁻¹

include hb in
/-- **`η` is the conjugate of the inverse Kummer unit** ([EtTh], Proposition 4.3(iii)):
`η(p) = s⊓-gp(p) · κ(p)^{-1} · s⊓-gp(p)^{-1}` with `κ(p) = (1, id, 0, kummerUnit s t (σ π p))`. -/
theorem eta_eq (p : Q) :
      eta hs ht π hsfix Q htfix p = sgp hs π hsfix p *
      (unitAut Y (kummerUnit s t (σ (π p)))
        (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p)))⁻¹ *
        (sgp hs π hsfix (p : P) : Aut Y)⁻¹ := by
  rw [eta, mul_left_inj]
  -- `κ ≫ s⊔-gp = s⊓-gp`, i.e. `s⊓-gp = s⊔-gp * κ` in `Aut Y`
  have key : sgp hs π hsfix p = tgp ht π Q htfix p *
      unitAut Y (kummerUnit s t (σ (π p))) (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p)) := by
    ext1
    exact (unit_comp_liftAut hs ht hb (σ (π p)) (hsfix _) (htfix p)).symm
  rw [key, mul_inv_cancel_right]

include hb in
/-- `η(p)` lies in `μ_N(Y)` when `Base(σ π p)` fixes `N·F`, `F = u_s − u_t` (the fraction of the
`N`-th root, whose `N`-th power `f` is fixed by `Q`). -/
lemma eta_mem_muN (hFN : ∀ p : Q, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))
    (p : Q) : eta hs ht π hsfix Q htfix p ∈ muN Y N := by
  refine ⟨tgp_mul_sgp_inv_mem_units hs ht hb π hsfix Q htfix p, ?_⟩
  rw [eta_eq hs ht hb π hsfix Q htfix p, conj_pow, inv_pow]
  have hκ : (unitAut Y (kummerUnit s t (σ (π p)))
      (divB_kummerUnit hs ht hb _ (hsfix _) (htfix p))) ^ N = 1 := by
    ext1
    rw [unitIso_pow]
    have h0 : N • kummerUnit s t (σ (π p)) = 0 := nsmul_kummerUnit _ N (hFN p)
    change unitHom Y _ _ = 𝟙 Y
    simp only [h0]
    ext <;> simp [unitHom]
  rw [hκ, inv_one, mul_one, mul_inv_cancel]

variable (hFN : ∀ p : Q, B.pb (σ (π p)).hom.base (N • (s.u - t.u)) = N • (s.u - t.u))

include hb hFN in
/-- **[EtTh], Lemma 5.9(i)** for `s⊔-gp`: its values lie in `E_N`. -/
lemma tgp_mem_thetaE (p : Q) : tgp ht π Q htfix p ∈ thetaE hs π hsfix N :=
  ⟨_, eta_mem_muN hs ht hb π hsfix N Q htfix hFN p, p, by rw [eta, inv_mul_cancel_right]⟩

/-- **`s⊔-Π : Q → E^Π_N`**, `p ↦ (s⊔-gp(p), p)` ([EtTh], Lemma 5.9(iv)). -/
noncomputable def tPi : Q →* thetaEPi hs π hsfix N where
  toFun p := ⟨(tgp ht π Q htfix p, p), tgp_mem_thetaE hs ht hb π hsfix N Q htfix hFN p,
    tgp_base hs ht hb π hsfix Q htfix p⟩
  map_one' := by ext <;> simp
  map_mul' p p' := by ext <;> simp

/-- **[EtTh], Lemma 5.9(iv)** (theta part): under `μ_N(Y) ⋊ P ≅ E^Π_N`, `s⊔-Π` is the section
`p ↦ (η(p), p)` over `Q`, `η(p) = s⊔-gp(p) · s⊓-gp(p)^{-1} ∈ μ_N(Y)` (`eta_eq`: the conjugate of
the inverse Kummer unit). -/
theorem ePiEquiv_thetaSection (p : Q) :
    ePiEquiv hs hsec π hsfix N
      ⟨⟨eta hs ht π hsfix Q htfix p, eta_mem_muN hs ht hb π hsfix N Q htfix hFN p⟩, p⟩ =
      tPi hs ht hb π hsfix N Q htfix hFN p := by
  apply Subtype.ext
  rw [ePiEquiv_apply]
  change (eta hs ht π hsfix Q htfix p * sgp hs π hsfix p, (p : P)) = (tgp ht π Q htfix p, (p : P))
  rw [eta, inv_mul_cancel_right]

end Theta

end Model

end Frobenioid

end Iut
