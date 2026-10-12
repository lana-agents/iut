/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.CyclotomicRigidity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Automorphisms of the mod `N` model environments ([EtTh], Cor. 2.18(iv); step 2, milestone (13))

[EtTh], Cor. 2.18(iv): the homomorphisms `Aut^μ(M_N) → Aut(Π_X)` from the automorphisms of the
mod `N` model mono-theta environments are surjective, with kernel `Hom(Π_Y/Π_Ÿ, μ_N) ≅
Hom(ℤ/2, ℤ/N)`; this is the input of discrete rigidity (`RigidSystems.Tower.discreteRigidity`).

Here this is computed for the **mod `N` model of the geometric theta quotient**
(`modelN N l = model ℤ l (ZMod N) red 0`: `Δ_Θ = (Δ_Y)^ell = ℤ`, `μ = ℤ/N`, `red` the reduction
mod `N`, the Kummer class `ρ` of `Ü` trivial). An automorphism of an environment acts on the
torsion-free quotient `Π/μ = Δ_Θ × (Δ_Y)^ell ≅ ℤ²` (`toQuot`, a homomorphism
`Aut(modelN) →* AddAut (ℤ × ℤ)`); this plays the role of `Aut(Π_X)` (it records the action on
`Gal(Y/X)`, through `D`, and on the labels).

## Results

* `Env.Iso.refl`, `trans`, `symm`, `ext`; the group `Env.Aut E` of automorphisms of an
  environment.
* `toQuot_mem_upper`: the induced automorphism of `ℤ²` is upper triangular with diagonal entries
  `±1` (`Upper`): `(c, a) ↦ (ε₁c + b·a, ε₂a)` — from the invariance of `D` (the conjugations by
  `Gal(Y/X)`).
* **`toQuot_surjective`**: every such automorphism of `ℤ²` lifts to an automorphism of the
  environment (`liftAut`: `(m, c, a) ↦ (ε₁m − b·a, ε₁c + b·a, ε₂a)`).
* **`finite_ker`**: the kernel is finite (an automorphism in the kernel is determined by the
  `ℤ/N`-components of the images of the three generators).
* **`kerEquiv`** (`l` prime to `N`): the kernel is `Hom(ℤ/2, ℤ/N) = {x ∈ ℤ/N | 2x = 0}`, the
  automorphisms `(m, c, a) ↦ (m + a·x, c, a)` — exactly the kernel of [EtTh], Cor. 2.18(iv).
-/

namespace Iut.EtaleTheta

universe u

namespace Env

/-! ### The groupoid of environments -/

namespace Iso

variable {E E' E'' : Env.{u}}

@[ext] theorem ext {f g : Iso E E'} (h : f.e = g.e) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity. -/
def refl (E : Env.{u}) : Iso E E where
  e := AddEquiv.refl _
  map_D γ := by
    have : (AddEquiv.refl E.carrier).trans (γ.trans (AddEquiv.refl E.carrier).symm) = γ := by
      ext; rfl
    rw [this]
  map_S := by
    ext x
    simp

/-- Composition. -/
def trans (f : Iso E E') (g : Iso E' E'') : Iso E E'' where
  e := f.e.trans g.e
  map_D γ := by
    rw [g.map_D, f.map_D]
    have : f.e.trans ((g.e.trans (γ.trans g.e.symm)).trans f.e.symm) =
        (f.e.trans g.e).trans (γ.trans (f.e.trans g.e).symm) := by
      ext; rfl
    rw [this]
  map_S := by
    rw [← g.map_S, ← f.map_S, AddSubgroup.map_map]
    rfl

/-- The inverse. -/
def symm (f : Iso E E') : Iso E' E where
  e := f.e.symm
  map_D γ := by
    rw [f.map_D]
    have : f.e.trans ((f.e.symm.trans (γ.trans f.e.symm.symm)).trans f.e.symm) = γ := by
      ext; simp
    rw [this]
  map_S := by
    rw [← f.map_S, AddSubgroup.map_map]
    convert AddSubgroup.map_id E.S using 2
    ext; simp

@[simp] lemma refl_e (E : Env.{u}) : (refl E).e = AddEquiv.refl _ := rfl
@[simp] lemma trans_e (f : Iso E E') (g : Iso E' E'') : (f.trans g).e = f.e.trans g.e := rfl
@[simp] lemma symm_e (f : Iso E E') : f.symm.e = f.e.symm := rfl

end Iso

/-- **The automorphism group of an environment**, with `(f * g).e = f.e ∘ g.e`. -/
instance (E : Env.{u}) : Group (Iso E E) where
  mul f g := g.trans f
  one := Iso.refl E
  inv f := f.symm
  mul_assoc _ _ _ := Iso.ext rfl
  one_mul _ := Iso.ext rfl
  mul_one _ := Iso.ext rfl
  inv_mul_cancel f := Iso.ext (AddEquiv.ext fun x => f.e.symm_apply_apply x)

@[simp] lemma Iso.mul_e {E : Env.{u}} (f g : Iso E E) (x : E.carrier) :
    (f * g).e x = f.e (g.e x) := rfl

@[simp] lemma Iso.one_e {E : Env.{u}} (x : E.carrier) : (1 : Iso E E).e x = x := rfl

end Env

/-! ### The mod `N` model -/

/-- The reduction `ℤ → ℤ/N`. -/
def redN (N : ℕ) : ℤ →+ ZMod N := Int.castAddHom (ZMod N)

/-- **The mod `N` model environment** of the geometric theta quotient. -/
abbrev modelN (N : ℕ) (l : ℤ) : Env.{0} := model ℤ l (ZMod N) (redN N) 0

variable {N : ℕ} {l : ℤ}

section Quot

variable [NeZero N]

/-- Elements `(m, 0, 0)` are torsion. -/
lemma isOfFinAddOrder_inl (m : ZMod N) : IsOfFinAddOrder ((m, 0, 0) : ZMod N × ℤ × ℤ) :=
  (isOfFinAddOrder_of_finite m).prod_mk IsOfFinAddOrder.zero

/-- An automorphism kills the `ℤ²`-part of the torsion: `(f(m, 0, 0)).2 = 0`. -/
lemma snd_e_inl (f : Env.Iso (modelN N l) (modelN N l)) (m : ZMod N) :
    (f.e (m, 0, 0)).2 = 0 := by
  have h := f.e.toAddMonoidHom.isOfFinAddOrder (isOfFinAddOrder_inl m)
  have h2 := (AddMonoidHom.snd (ZMod N) (ℤ × ℤ)).isOfFinAddOrder h
  exact (isOfFinAddOrder_iff_eq_zero _).1 h2

/-- The `ℤ²`-part of `f(0, x)`. -/
def quotFun (f : Env.Iso (modelN N l) (modelN N l)) (x : ℤ × ℤ) : ℤ × ℤ := (f.e (0, x)).2

lemma snd_e (f : Env.Iso (modelN N l) (modelN N l)) (m : ZMod N) (x : ℤ × ℤ) :
    (f.e (m, x)).2 = quotFun f x := by
  have : ((m, x) : ZMod N × ℤ × ℤ) = (m, 0, 0) + (0, x) := by ext <;> simp
  rw [this, map_add, Prod.snd_add, snd_e_inl, zero_add]
  rfl

omit [NeZero N] in
lemma quotFun_add (f : Env.Iso (modelN N l) (modelN N l)) (x y : ℤ × ℤ) :
    quotFun f (x + y) = quotFun f x + quotFun f y := by
  have : ((0, x + y) : ZMod N × ℤ × ℤ) = (0, x) + (0, y) := by ext <;> simp
  simp only [quotFun, this, map_add, Prod.snd_add]

lemma quotFun_mul (f g : Env.Iso (modelN N l) (modelN N l)) (x : ℤ × ℤ) :
    quotFun (f * g) x = quotFun f (quotFun g x) := by
  rw [quotFun, Env.Iso.mul_e, ← snd_e f (g.e (0, x)).1, quotFun]

omit [NeZero N] in
lemma quotFun_one (x : ℤ × ℤ) : quotFun (1 : Env.Iso (modelN N l) (modelN N l)) x = x := rfl

/-- **The induced automorphism of `Π/μ = ℤ²`** (as a permutation; it is additive,
`toQuot_add`). -/
def toQuot : Env.Iso (modelN N l) (modelN N l) →* Equiv.Perm (ℤ × ℤ) where
  toFun f :=
    { toFun := quotFun f
      invFun := quotFun f⁻¹
      left_inv x := by
        rw [← quotFun_mul, inv_mul_cancel, quotFun_one]
      right_inv x := by
        rw [← quotFun_mul, mul_inv_cancel, quotFun_one] }
  map_one' := rfl
  map_mul' f g := Equiv.ext fun x => quotFun_mul f g x

lemma toQuot_apply (f : Env.Iso (modelN N l) (modelN N l)) (x : ℤ × ℤ) :
    toQuot f x = (f.e (0, x)).2 := rfl

lemma toQuot_add (f : Env.Iso (modelN N l) (modelN N l)) (x y : ℤ × ℤ) :
    toQuot f (x + y) = toQuot f x + toQuot f y := quotFun_add f x y

end Quot

/-! ### The image: upper triangular automorphisms of `ℤ²` -/

/-- An upper triangular automorphism of `ℤ²` with diagonal `(ε₁, ε₂)` and corner `b`. -/
def upperFun (ε₁ ε₂ : ℤˣ) (b : ℤ) (x : ℤ × ℤ) : ℤ × ℤ := ((ε₁ : ℤ) * x.1 + b * x.2, (ε₂ : ℤ) * x.2)

/-- **The upper triangular automorphisms of `ℤ²` with diagonal entries `±1`**
(`(c, a) ↦ (ε₁c + b·a, ε₂a)`): the image of `toQuot`. -/
def Upper : Subgroup (Equiv.Perm (ℤ × ℤ)) where
  carrier := {σ | ∃ (ε₁ ε₂ : ℤˣ) (b : ℤ), ∀ x, σ x = upperFun ε₁ ε₂ b x}
  mul_mem' := by
    rintro σ τ ⟨ε₁, ε₂, b, hσ⟩ ⟨η₁, η₂, β, hτ⟩
    refine ⟨ε₁ * η₁, ε₂ * η₂, (ε₁ : ℤ) * β + b * η₂, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, hτ, hσ]
    simp only [upperFun, Units.val_mul, Prod.mk.injEq]
    constructor <;> ring
  one_mem' := ⟨1, 1, 0, fun x => by simp [upperFun]⟩
  inv_mem' := by
    rintro σ ⟨ε₁, ε₂, b, hσ⟩
    refine ⟨ε₁⁻¹, ε₂⁻¹, -((ε₁⁻¹ : ℤˣ) : ℤ) * b * ((ε₂⁻¹ : ℤˣ) : ℤ), fun x => ?_⟩
    apply σ.injective
    change σ (σ.symm x) = _
    rw [Equiv.apply_symm_apply, hσ]
    simp only [upperFun]
    have h1 : (ε₁ : ℤ) * ((ε₁⁻¹ : ℤˣ) : ℤ) = 1 := by rw [← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    have h2 : (ε₂ : ℤ) * ((ε₂⁻¹ : ℤˣ) : ℤ) = 1 := by rw [← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    ext
    · linear_combination (b * ((ε₂⁻¹ : ℤˣ) : ℤ) * x.2 - x.1) * h1
    · linear_combination (-(x.2 : ℤ)) * h2

section Image

variable [NeZero N]

/-- An additive permutation of `ℤ²` is given by its values on the basis. -/
lemma additive_apply {σ : Equiv.Perm (ℤ × ℤ)} (hσ : ∀ x y, σ (x + y) = σ x + σ y)
    (x : ℤ × ℤ) : σ x = x.1 • σ (1, 0) + x.2 • σ (0, 1) := by
  let φ : ℤ × ℤ →+ ℤ × ℤ := AddMonoidHom.mk' σ hσ
  have hx : x = x.1 • ((1, 0) : ℤ × ℤ) + x.2 • (0, 1) := by ext <;> simp
  change φ x = x.1 • φ (1, 0) + x.2 • φ (0, 1)
  conv_lhs => rw [hx]
  rw [map_add, map_zsmul, map_zsmul]

omit [NeZero N] in
/-- An automorphism of the environment commutes with `γ_1` up to some `γ_k`. -/
lemma exists_gammaK_comm (f : Env.Iso (modelN N l) (modelN N l)) :
    ∃ k : ℤ, ∀ x, f.e (gammaK ℤ l (ZMod N) k x) = gammaK ℤ l (ZMod N) 1 (f.e x) := by
  have h := (f.map_D (gammaK ℤ l (ZMod N) 1)).1 ⟨1, rfl⟩
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun x => ?_⟩
  have := DFunLike.congr_fun hk x
  simp only [AddEquiv.trans_apply] at this
  rw [this, AddEquiv.apply_symm_apply]

/-- The induced automorphism in coordinates. -/
lemma toQuot_lin (f : Env.Iso (modelN N l) (modelN N l)) (c a : ℤ) :
    toQuot f (c, a) = (c * (toQuot f (1, 0)).1 + a * (toQuot f (0, 1)).1,
      c * (toQuot f (1, 0)).2 + a * (toQuot f (0, 1)).2) := by
  rw [additive_apply (toQuot_add f)]
  ext <;> simp

/-- The lower left entry of the induced automorphism vanishes. -/
lemma toQuot_entry21 (hl : l ≠ 0) (f : Env.Iso (modelN N l) (modelN N l)) :
    (toQuot f (1, 0)).2 = 0 := by
  obtain ⟨k, hk⟩ := exists_gammaK_comm f
  have := congrArg Prod.snd (hk (0, 1, 0))
  simp only [gammaK, AddEquiv.coe_mk, Equiv.coe_fn_mk, smul_eq_mul, mul_zero, add_zero] at this
  have h := congrArg Prod.fst this
  simp only at h
  have h' : l * (f.e (0, 1, 0)).2.2 = 0 := by linarith
  exact (mul_eq_zero.1 h').resolve_left hl

/-- **The induced automorphism of `ℤ²` is upper triangular with diagonal `±1`.** -/
theorem toQuot_mem_upper (hl : l ≠ 0) (f : Env.Iso (modelN N l) (modelN N l)) :
    toQuot f ∈ Upper := by
  have h21 := toQuot_entry21 hl f
  have g21 := toQuot_entry21 hl f⁻¹
  have hfg : ∀ x, toQuot f (toQuot f⁻¹ x) = x := fun x => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have e1 := hfg (1, 0)
  have e2 := hfg (0, 1)
  rw [toQuot_lin f⁻¹ 1 0, toQuot_lin f] at e1
  rw [toQuot_lin f⁻¹ 0 1, toQuot_lin f] at e2
  simp only [one_mul, zero_mul, add_zero, zero_add, g21, h21, mul_zero, Prod.mk.injEq] at e1 e2
  have u1 : (toQuot f (1, 0)).1 * (toQuot f⁻¹ (1, 0)).1 = 1 := by linarith [e1.1]
  have u2 : (toQuot f (0, 1)).2 * (toQuot f⁻¹ (0, 1)).2 = 1 := by linarith [e2.2]
  refine ⟨Units.mkOfMulEqOne _ _ u1, Units.mkOfMulEqOne _ _ u2, (toQuot f (0, 1)).1,
    fun x => ?_⟩
  rw [show x = (x.1, x.2) from rfl, toQuot_lin, h21]
  simp only [upperFun, Units.val_mkOfMulEqOne, Prod.mk.injEq]
  constructor <;> ring

end Image

/-! ### Lifting: surjectivity onto `Upper` -/

section Lift

/-- `(m, c, a) ↦ (ε₁m − b·a, ε₁c + b·a, ε₂a)`. -/
def liftFun (ε₁ ε₂ : ℤˣ) (b : ℤ) (x : ZMod N × ℤ × ℤ) : ZMod N × ℤ × ℤ :=
  ((ε₁ : ℤ) • x.1 - ((b * x.2.2 : ℤ) : ZMod N), ε₁ * x.2.1 + b * x.2.2, ε₂ * x.2.2)

/-- The inverse of `liftFun` (`ε⁻¹ = ε` in `ℤˣ`). -/
def liftInv (ε₁ ε₂ : ℤˣ) (b : ℤ) (y : ZMod N × ℤ × ℤ) : ZMod N × ℤ × ℤ :=
  ((ε₁ : ℤ) • (y.1 + ((b * (ε₂ * y.2.2) : ℤ) : ZMod N)), ε₁ * (y.2.1 - b * (ε₂ * y.2.2)),
    ε₂ * y.2.2)

lemma units_mul_self_apply (ε : ℤˣ) (a : ℤ) : (ε : ℤ) * (ε * a) = a := by
  rw [← mul_assoc, Int.units_coe_mul_self, one_mul]

lemma units_smul_smul (ε : ℤˣ) (m : ZMod N) : (ε : ℤ) • ((ε : ℤ) • m) = m := by
  rw [smul_smul, Int.units_coe_mul_self, one_smul]

/-- The additive automorphism `liftFun ε₁ ε₂ b`. -/
def liftEquiv (ε₁ ε₂ : ℤˣ) (b : ℤ) : (ZMod N × ℤ × ℤ) ≃+ (ZMod N × ℤ × ℤ) where
  toFun := liftFun ε₁ ε₂ b
  invFun := liftInv ε₁ ε₂ b
  left_inv x := by
    obtain ⟨m, c, a⟩ := x
    simp only [liftFun, liftInv, units_mul_self_apply, sub_add_cancel, add_sub_cancel_right,
      units_smul_smul]
  right_inv y := by
    obtain ⟨m, c, a⟩ := y
    simp only [liftFun, liftInv, units_mul_self_apply, add_sub_cancel_right, sub_add_cancel,
      units_smul_smul]
  map_add' x y := by
    obtain ⟨m, c, a⟩ := x
    obtain ⟨m', c', a'⟩ := y
    simp only [liftFun, Prod.mk_add_mk, smul_add, mul_add, Int.cast_add, Prod.mk.injEq]
    exact ⟨by abel, by ring, trivial⟩

lemma liftEquiv_apply (ε₁ ε₂ : ℤˣ) (b : ℤ) (x : ZMod N × ℤ × ℤ) :
    liftEquiv ε₁ ε₂ b x = liftFun ε₁ ε₂ b x := rfl

/-- `liftFun` intertwines `γ_k` and `γ_j` when `ε₁k = jε₂`. -/
lemma liftFun_gammaK (ε₁ ε₂ : ℤˣ) (b : ℤ) {j k : ℤ} (h : (ε₁ : ℤ) * k = j * ε₂)
    (x : ZMod N × ℤ × ℤ) :
    liftFun ε₁ ε₂ b (gammaK ℤ l (ZMod N) k x) = gammaK ℤ l (ZMod N) j (liftFun ε₁ ε₂ b x) := by
  obtain ⟨m, c, a⟩ := x
  simp only [liftFun, gammaK, AddEquiv.coe_mk, Equiv.coe_fn_mk, smul_eq_mul, Prod.mk.injEq,
    true_and, and_true]
  linear_combination l * a * h

/-- **The lift of an upper triangular automorphism** to an automorphism of the environment. -/
def liftAut (ε₁ ε₂ : ℤˣ) (b : ℤ) : Env.Iso (modelN N l) (modelN N l) where
  e := liftEquiv ε₁ ε₂ b
  map_D γ := by
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j * ε₂ * ε₁, AddEquiv.ext fun x => ?_⟩
      simp only [AddEquiv.trans_apply]
      rw [AddEquiv.eq_symm_apply, liftEquiv_apply, liftEquiv_apply, liftFun_gammaK]
      linear_combination (j * ε₂) * Int.units_coe_mul_self ε₁
    · rintro ⟨k, hk⟩
      refine ⟨k * ε₁ * ε₂, AddEquiv.ext fun x => ?_⟩
      have := DFunLike.congr_fun hk ((liftEquiv ε₁ ε₂ b).symm x)
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at this
      rw [AddEquiv.eq_symm_apply] at this
      rw [← this, liftEquiv_apply, liftFun_gammaK ε₁ ε₂ b (j := k * ε₁ * ε₂),
        ← liftEquiv_apply, AddEquiv.apply_symm_apply]
      linear_combination (-(k * ε₁)) * Int.units_coe_mul_self ε₂
  map_S := by
    have key : ∀ c a : ℤ, liftEquiv ε₁ ε₂ b (thetaSection ℤ (ZMod N) (redN N) 0 (c, a)) =
        thetaSection ℤ (ZMod N) (redN N) 0 (ε₁ * c + 2 * b * a, ε₂ * a) := by
      intro c a
      simp only [liftEquiv_apply, liftFun, thetaSection, redN, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, Int.coe_castAddHom, AddMonoidHom.zero_apply, sub_zero, Prod.mk.injEq,
        nsmul_eq_mul, Nat.cast_ofNat]
      refine ⟨?_, by ring, by ring⟩
      push_cast
      rw [zsmul_eq_mul]
      ring
    apply le_antisymm
    · rintro _ ⟨_, ⟨⟨c, a⟩, rfl⟩, rfl⟩
      exact ⟨_, (key c a).symm⟩
    · rintro _ ⟨⟨c, a⟩, rfl⟩
      refine ⟨_, ⟨(ε₁ * (c - 2 * b * (ε₂ * a)), ε₂ * a), rfl⟩, ?_⟩
      change liftEquiv ε₁ ε₂ b _ = _
      rw [key, units_mul_self_apply, units_mul_self_apply, sub_add_cancel]

lemma toQuot_liftAut [NeZero N] (ε₁ ε₂ : ℤˣ) (b : ℤ) (x : ℤ × ℤ) :
    toQuot (N := N) (liftAut (N := N) (l := l) ε₁ ε₂ b) x = upperFun ε₁ ε₂ b x := by
  rw [toQuot_apply]
  simp [liftAut, liftEquiv_apply, liftFun, upperFun]

/-- **The image of `toQuot` is `Upper`** ([EtTh], Cor. 2.18(iv): surjectivity). -/
theorem range_toQuot [NeZero N] (hl : l ≠ 0) :
    (toQuot (N := N) (l := l)).range = Upper := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact toQuot_mem_upper hl f
  · rintro σ ⟨ε₁, ε₂, b, hσ⟩
    exact ⟨liftAut ε₁ ε₂ b, Equiv.ext fun x => by rw [toQuot_liftAut, hσ]⟩

/-- `toQuot` as a surjection onto `Upper`. -/
def toUpper [NeZero N] (hl : l ≠ 0) : Env.Iso (modelN N l) (modelN N l) →* Upper :=
  toQuot.codRestrict Upper (toQuot_mem_upper hl)

theorem toUpper_surjective [NeZero N] (hl : l ≠ 0) :
    Function.Surjective (toUpper (N := N) hl) := by
  rintro ⟨σ, hσ⟩
  rw [← range_toQuot (N := N) hl] at hσ
  obtain ⟨f, rfl⟩ := hσ
  exact ⟨f, rfl⟩

end Lift

/-! ### The kernel -/

section Kernel

variable [NeZero N]

/-- **Additive maps on `ℤ/N × ℤ × ℤ` are determined by the images of the generators.** -/
lemma addEquiv_apply (e : (ZMod N × ℤ × ℤ) ≃+ (ZMod N × ℤ × ℤ)) (m : ZMod N) (c a : ℤ) :
    e (m, c, a) = m.val • e (1, 0, 0) + c • e (0, 1, 0) + a • e (0, 0, 1) := by
  have hx : ((m, c, a) : ZMod N × ℤ × ℤ) =
      m.val • ((1, 0, 0) : ZMod N × ℤ × ℤ) + c • (0, 1, 0) + a • (0, 0, 1) := by
    ext <;> simp
  rw [hx, map_add, map_add, map_nsmul, map_zsmul, map_zsmul]

/-- Elements of the kernel act as the identity on the `ℤ²`-coordinates. -/
lemma mem_ker_iff (f : Env.Iso (modelN N l) (modelN N l)) :
    f ∈ (toQuot (N := N) (l := l)).ker ↔ ∀ x : ℤ × ℤ, (f.e (0, x)).2 = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    have := Equiv.ext_iff.1 h x
    rwa [toQuot_apply] at this
  · intro h
    exact Equiv.ext fun x => by rw [toQuot_apply, h]; rfl

/-- The three `ℤ/N`-coordinates of the images of the generators. -/
def kerCoords (f : Env.Iso (modelN N l) (modelN N l)) : ZMod N × ZMod N × ZMod N :=
  ((f.e (1, 0, 0)).1, (f.e (0, 1, 0)).1, (f.e (0, 0, 1)).1)

lemma kerCoords_injective :
    Function.Injective fun f : (toQuot (N := N) (l := l)).ker =>
      kerCoords (f : Env.Iso (modelN N l) (modelN N l)) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  simp only [kerCoords, Prod.mk.injEq] at h
  rw [mem_ker_iff] at hf hg
  apply Subtype.ext
  apply Env.Iso.ext
  apply AddEquiv.ext
  rintro ⟨m, c, a⟩
  have g1 : ∀ e : Env.Iso (modelN N l) (modelN N l), e.e (1, 0, 0) = ((e.e (1, 0, 0)).1, 0) :=
    fun e => Prod.ext rfl (snd_e_inl e 1)
  have g2 : f.e (0, 1, 0) = ((f.e (0, 1, 0)).1, (1, 0)) := Prod.ext rfl (hf (1, 0))
  have g3 : f.e (0, 0, 1) = ((f.e (0, 0, 1)).1, (0, 1)) := Prod.ext rfl (hf (0, 1))
  have g2' : g.e (0, 1, 0) = ((g.e (0, 1, 0)).1, (1, 0)) := Prod.ext rfl (hg (1, 0))
  have g3' : g.e (0, 0, 1) = ((g.e (0, 0, 1)).1, (0, 1)) := Prod.ext rfl (hg (0, 1))
  rw [addEquiv_apply f.e, addEquiv_apply g.e, g1 f, g1 g, g2, g3, g2', g3', h.1, h.2.1, h.2.2]

/-- **The kernel of `Aut(modelN) → Upper` is finite** ([EtTh], Cor. 2.18(iv)). -/
instance finite_ker : Finite (toQuot (N := N) (l := l)).ker :=
  Finite.of_injective _ kerCoords_injective

theorem ker_toUpper (hl : l ≠ 0) :
    (toUpper (N := N) hl).ker = (toQuot (N := N) (l := l)).ker := by
  ext f
  simp only [MonoidHom.mem_ker, toUpper]
  rw [← Subtype.coe_inj]
  rfl

instance finite_ker_toUpper (hl : l ≠ 0) : Finite (toUpper (N := N) hl).ker := by
  rw [ker_toUpper]
  infer_instance

/-- The automorphism `(m, c, a) ↦ (m + a·x, c, a)` for `2x = 0`. -/
def kerElt (x : ZMod N) (hx : 2 • x = 0) : Env.Iso (modelN N l) (modelN N l) where
  e :=
    { toFun := fun y => (y.1 + y.2.2 • x, y.2)
      invFun := fun y => (y.1 - y.2.2 • x, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      map_add' := fun y z => by
        ext
        · simp only [Prod.fst_add, Prod.snd_add, add_smul]
          abel
        · rfl
        · rfl }
  map_D γ := by
    have comm : ∀ k, (fun y : ZMod N × ℤ × ℤ => (y.1 + y.2.2 • x, y.2)) ∘
        gammaK ℤ l (ZMod N) k = gammaK ℤ l (ZMod N) k ∘
          fun y : ZMod N × ℤ × ℤ => (y.1 + y.2.2 • x, y.2) := fun k => by
      funext y
      simp [gammaK]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, AddEquiv.ext fun y => ?_⟩
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.eq_symm_apply]
      exact (congrFun (comm k) y).symm
    · rintro ⟨k, hk⟩
      refine ⟨k, AddEquiv.ext fun y => ?_⟩
      have := DFunLike.congr_fun hk (y.1 - y.2.2 • x, y.2)
      simp only [AddEquiv.trans_apply, AddEquiv.coe_mk, Equiv.coe_fn_mk] at this
      rw [AddEquiv.eq_symm_apply] at this
      simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, sub_add_cancel] at this
      rw [← this]
      have h2 := congrFun (comm k) (y.1 - y.2.2 • x, y.2)
      simp only [Function.comp_apply, sub_add_cancel] at h2
      rw [h2]
  map_S := by
    have key : ∀ c a : ℤ, (fun y : ZMod N × ℤ × ℤ => (y.1 + y.2.2 • x, y.2))
        (thetaSection ℤ (ZMod N) (redN N) 0 (c, a)) =
          thetaSection ℤ (ZMod N) (redN N) 0 (c, a) := by
      intro c a
      simp only [thetaSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq, and_true]
      rw [smul_assoc, smul_comm, hx, smul_zero, add_zero]
    apply le_antisymm
    · rintro _ ⟨_, ⟨⟨c, a⟩, rfl⟩, rfl⟩
      exact ⟨(c, a), (key c a).symm⟩
    · rintro _ ⟨⟨c, a⟩, rfl⟩
      exact ⟨_, ⟨(c, a), rfl⟩, key c a⟩

lemma kerElt_mem (x : ZMod N) (hx : 2 • x = 0) :
    kerElt (l := l) x hx ∈ (toQuot (N := N) (l := l)).ker := by
  rw [mem_ker_iff]
  intro y
  rfl

/-- The generator values of an element of the kernel. -/
lemma ker_gens {f : Env.Iso (modelN N l) (modelN N l)} (hf : f ∈ (toQuot (N := N) (l := l)).ker) :
    f.e (1, 0, 0) = ((f.e (1, 0, 0)).1, 0) ∧ f.e (0, 1, 0) = ((f.e (0, 1, 0)).1, (1, 0)) ∧
      f.e (0, 0, 1) = ((f.e (0, 0, 1)).1, (0, 1)) := by
  rw [mem_ker_iff] at hf
  exact ⟨Prod.ext rfl (snd_e_inl f 1), Prod.ext rfl (hf (1, 0)), Prod.ext rfl (hf (0, 1))⟩

omit [NeZero N] in
/-- An automorphism maps the theta section into itself. -/
lemma mem_S_of_iso (f : Env.Iso (modelN N l) (modelN N l)) (c a : ℤ) :
    ∃ y : ℤ × ℤ, thetaSection ℤ (ZMod N) (redN N) 0 y =
      f.e (thetaSection ℤ (ZMod N) (redN N) 0 (c, a)) := by
  have h : f.e (thetaSection ℤ (ZMod N) (redN N) 0 (c, a)) ∈ (modelN N l).S := by
    rw [← f.map_S]
    exact ⟨_, ⟨(c, a), rfl⟩, rfl⟩
  exact h

/-- **The kernel elements are the `kerElt x`, `2x = 0`**, if `l` is a unit mod `N`. -/
theorem ker_eq_kerElt (hl : l ≠ 0) (hu : IsUnit (l : ZMod N))
    {f : Env.Iso (modelN N l) (modelN N l)} (hf : f ∈ (toQuot (N := N) (l := l)).ker) :
    ∃ hx : 2 • (f.e (0, 0, 1)).1 = 0, f = kerElt (f.e (0, 0, 1)).1 hx := by
  obtain ⟨g1, g2, g3⟩ := ker_gens hf
  set A := (f.e (1, 0, 0)).1 with hA
  set d1 := (f.e (0, 1, 0)).1 with hd1
  set d2 := (f.e (0, 0, 1)).1 with hd2
  -- `2·d2 = 0`, from the theta section at `(0, 1)`
  have hx : 2 • d2 = 0 := by
    obtain ⟨⟨c, a⟩, h⟩ := mem_S_of_iso f 0 1
    have e : thetaSection ℤ (ZMod N) (redN N) 0 (0, 1) = 2 • ((0, 0, 1) : ZMod N × ℤ × ℤ) := by
      ext <;> simp [thetaSection]
    rw [e, map_nsmul, g3] at h
    simp only [thetaSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply,
      sub_zero, Prod.smul_mk, Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    subst h2
    rw [← h1]
    simp [redN]
  -- `d1 = A − 1`, from the theta section at `(1, 0)`
  have hd : -A + d1 = -1 := by
    obtain ⟨⟨c, a⟩, h⟩ := mem_S_of_iso f 1 0
    have e : thetaSection ℤ (ZMod N) (redN N) 0 (1, 0) =
        -((1, 0, 0) : ZMod N × ℤ × ℤ) + (0, 1, 0) := by
      ext <;> simp [thetaSection, redN]
    rw [e, map_add, map_neg, g1, g2] at h
    simp only [thetaSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply,
      sub_zero, Prod.neg_mk, Prod.mk_add_mk, neg_zero, zero_add, Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    subst h2
    rw [← h1]
    simp [redN]
  -- `l·d1 = 0`, from the invariance of `D`
  have hld : (l : ZMod N) * d1 = 0 := by
    obtain ⟨k, hk⟩ := exists_gammaK_comm f
    have h := hk (0, 0, 1)
    have e : gammaK ℤ l (ZMod N) k (0, 0, 1) =
        (k * l) • ((0, 1, 0) : ZMod N × ℤ × ℤ) + (0, 0, 1) := by
      ext <;> simp [gammaK]
    rw [e, map_add, map_zsmul, g2, g3] at h
    simp only [gammaK, AddEquiv.coe_mk, Equiv.coe_fn_mk, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h
    obtain ⟨h1, h2, -⟩ := h
    have hk1 : k = 1 := by
      have : (k - 1) * l = 0 := by linarith
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hl)
    subst hk1
    simp only [one_mul, add_eq_right] at h1
    rw [← zsmul_eq_mul]
    exact h1
  have hd10 : d1 = 0 := hu.mul_right_eq_zero.1 hld
  have hA1 : A = 1 := by
    rw [hd10, add_zero, neg_inj] at hd
    exact hd
  refine ⟨hx, ?_⟩
  have := kerCoords_injective (N := N) (l := l) (a₁ := ⟨f, hf⟩)
    (a₂ := ⟨kerElt d2 hx, kerElt_mem d2 hx⟩) ?_
  · exact congrArg Subtype.val this
  · simp only [kerCoords, kerElt, AddEquiv.coe_mk, Equiv.coe_fn_mk, zero_smul, add_zero,
      one_smul, zero_add, Prod.mk.injEq]
    exact ⟨hA1, hd10, rfl⟩

/-- **The kernel of `Aut(modelN) ↠ Upper` is `Hom(ℤ/2, ℤ/N)`** ([EtTh], Cor. 2.18(iv)), for
`l` a unit mod `N`. -/
def kerEquiv (hl : l ≠ 0) (hu : IsUnit (l : ZMod N)) :
    (toQuot (N := N) (l := l)).ker ≃ {x : ZMod N // 2 • x = 0} where
  toFun f := ⟨((f : Env.Iso (modelN N l) (modelN N l)).e (0, 0, 1)).1,
    (ker_eq_kerElt hl hu f.2).1⟩
  invFun x := ⟨kerElt x.1 x.2, kerElt_mem x.1 x.2⟩
  left_inv f := Subtype.ext (ker_eq_kerElt hl hu f.2).2.symm
  right_inv x := Subtype.ext (by simp [kerElt])

end Kernel

end Iut.EtaleTheta
