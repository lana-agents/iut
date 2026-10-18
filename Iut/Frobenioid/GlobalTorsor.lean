/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalFracIdeal

/-!
# The rational-function-torsor version of the global Frobenioid (IUT III, Example 3.6(i))

IUT III, Example 3.6(i) (l.7096–7147 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory III.txt`): "For each `v ∈ V`, the valuation on `K_v` determined by `v` determines a group
homomorphism `β_v : F_mod^× → K_v^×/O^×_{K_v}`. Then let us define a category `F^⊛_MOD` as follows.
An object `T = (T, {t_v}_{v∈V})` of `F^⊛_MOD` consists of a collection of data (a) an
`F_mod^×`-torsor `T`; (b) for each `v ∈ V`, a trivialization `t_v` of the torsor `T_v` obtained
from `T` by executing the "change of structure group" operation determined by the homomorphism
`β_v` subject to the condition that there exists an element `t ∈ T` such that `t_v` coincides with
the trivialization of `T_v` determined by `t` for all but finitely many `v`. An elementary
morphism `T_1 → T_2` […] is defined to be an isomorphism `T_1 ≅ T_2` of `F_mod^×`-torsors which is
integral at each `v ∈ V`, i.e., maps the trivialization `t_{1,v}` to an element of the
`O^▷_{K_v}`-orbit of `t_{2,v}`. […] A morphism `T_1 → T_2` […] is defined to consist of a positive
integer `n` and an elementary morphism `(T_1)^{⊗n} → T_2`. […] there exists a natural isomorphism
of Frobenioids `F^⊛_mod ≅ F^⊛_MOD` that induces the identity morphism `F_mod^× → F_mod^×` on the
associated rational function monoids".

## Formalisation

We work over an arbitrary number field `K` (`= F_mod`) and its own places, as in
`GlobalFracIdeal.lean` (see the remark on ramification there).

* `K_v^×/O^×_{K_v}` is `ℤ` (by `ord_v`) at finite `v` and `ℝ` (by `−log|·|_v`) at archimedean `v`,
  so the family `{β_v}` is the principal divisor `divZ K : K^× → ArithDivZ K`.
* A trivialization of the `β_v`-pushout `T_v = T ×^{K^×} (K_v^×/O^×)` is the same as a
  `K^×`-equivariant map `τ_v : T → K_v^×/O^×` (`τ_v(f·t) = β_v(f) + τ_v(t)`). The condition that
  `t_v` is the trivialization determined by one `t ∈ T` for almost all `v` says that `τ_v(t) = 0`
  for almost all `v`, i.e. `(τ_v(t))_v ∈ ArithDivZ K` (finitely supported at the finite places;
  there are finitely many archimedean places). So an object is a `K^×`-torsor `T` with an
  equivariant `τ : T → ArithDivZ K` (`TorsorObj`).
* An elementary morphism `T_1^{⊗n} → T_2` is an `n`-equivariant map `ψ : T_1 → T_2`
  (`ψ(f·t) = f^n·ψ(t)`); it is integral iff `τ_2(ψ t) − n·τ_1(t)` is effective (`t_{1,v}^{⊗n}` is
  mapped into the `O^▷`-orbit of `t_{2,v}`); this does not depend on `t`.

Main results:

* **`TorsorFrob K`**, the category `F^⊛_MOD`;
* **`TorsorFrob.ofModel : GlobalFrobenioid K ⥤ TorsorFrob K`** (`α ↦` the trivial torsor `K^×` with
  `τ(f) = div(f) + α`), which is **fully faithful and essentially surjective**
  (`TorsorFrob.equivModel`), preserves Frobenius degrees (`ofModel_map_deg`) and **induces the
  identity on `K^×`** (`ofModel_map_one`: the morphism attached to `(n, u)` sends `1 ↦ u`);
* **IUT III, Example 3.6(iii)** (first half): composing with Example 3.6(ii),
  `FracIdealFrob K ≌ TorsorFrob K` (`fracIdealEquivTorsor`), compatible with Frobenius degrees and
  with the identity on `K^×`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory Arakelov

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **An object of `F^⊛_MOD`** (IUT III, Example 3.6(i)): a `K^×`-torsor `T` with the
trivializations of its pushouts along the `β_v`, encoded as an equivariant
`τ : T → ArithDivZ K`. -/
structure TorsorObj where
  /-- The torsor. -/
  T : Type u
  [act : MulAction Kˣ T]
  /-- A torsor is nonempty. -/
  nonempty : Nonempty T
  /-- The action is free. -/
  free : ∀ (f : Kˣ) (t : T), f • t = t → f = 1
  /-- The action is transitive. -/
  trans : ∀ t t' : T, ∃ f : Kˣ, f • t = t'
  /-- The trivializations `t_v` (`τ_v(t)` is the coordinate of `t` in the trivialized `T_v`). -/
  τ : T → ArithDivZ K
  /-- `τ_v(f·t) = β_v(f) + τ_v(t)`. -/
  τ_smul : ∀ (f : Kˣ) (t : T), τ (f • t) = divZ K (Additive.ofMul f) + τ t

attribute [instance] TorsorObj.act

variable {K}

/-- **A morphism `T_1 → T_2` of `F^⊛_MOD`**: a Frobenius degree `n` and an integral elementary
morphism `T_1^{⊗n} → T_2`, i.e. an integral `n`-equivariant map. -/
@[ext]
structure TorsorHom (T₁ T₂ : TorsorObj K) where
  /-- The Frobenius degree. -/
  deg : ℕ+
  /-- The elementary morphism `T_1^{⊗n} → T_2`. -/
  ψ : T₁.T → T₂.T
  ψ_smul : ∀ (f : Kˣ) (t : T₁.T), ψ (f • t) = f ^ (deg : ℕ) • ψ t
  /-- Integrality at every `v ∈ V`. -/
  integral : ∀ t : T₁.T, T₂.τ (ψ t) - (deg : ℕ) • T₁.τ t ∈ effConeZ K

variable (K) in
/-- **The category `F^⊛_MOD`** of IUT III, Example 3.6(i). -/
abbrev TorsorFrob : Type (u + 1) := TorsorObj K

namespace TorsorFrob

instance : Category (TorsorFrob K) where
  Hom := TorsorHom
  id T := ⟨1, id, fun f t => by simp, fun t => by simp [zero_mem]⟩
  comp φ ψ := ⟨ψ.deg * φ.deg, ψ.ψ ∘ φ.ψ, fun f t => by
      simp only [Function.comp_apply, φ.ψ_smul, ψ.ψ_smul, PNat.mul_coe, pow_mul'],
    fun t => by
      have h := (effConeZ K).add_mem (ψ.integral (φ.ψ t))
        ((effConeZ K).nsmul_mem (φ.integral t) (ψ.deg : ℕ))
      convert h using 1
      simp only [Function.comp_apply, PNat.mul_coe, smul_sub, mul_smul]
      abel⟩
  id_comp φ := TorsorHom.ext (mul_one _) rfl
  comp_id φ := TorsorHom.ext (one_mul _) rfl
  assoc φ ψ χ := TorsorHom.ext (mul_assoc _ _ _).symm rfl

@[ext] lemma hom_ext {T₁ T₂ : TorsorFrob K} {φ ψ : T₁ ⟶ T₂} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.ψ = ψ.ψ) : φ = ψ :=
  TorsorHom.ext h₁ h₂

@[simp] lemma id_deg (T : TorsorFrob K) : TorsorHom.deg (𝟙 T) = 1 := rfl
@[simp] lemma id_ψ (T : TorsorFrob K) : TorsorHom.ψ (𝟙 T) = id := rfl
@[simp] lemma comp_deg {T₁ T₂ T₃ : TorsorFrob K} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ T₃) :
    TorsorHom.deg (φ ≫ ψ) = ψ.deg * φ.deg := rfl
@[simp] lemma comp_ψ {T₁ T₂ T₃ : TorsorFrob K} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ T₃) :
    TorsorHom.ψ (φ ≫ ψ) = ψ.ψ ∘ φ.ψ := rfl

/-! ### The trivial torsors -/

/-- The trivial torsor `K^×` with `τ(f) = div(f) + α`. -/
noncomputable abbrev triv (α : ArithDivZ K) : TorsorFrob K where
  T := Kˣ
  nonempty := ⟨1⟩
  free f t h := by simpa using h
  trans t t' := ⟨t' * t⁻¹, by simp⟩
  τ f := divZ K (Additive.ofMul f) + α
  τ_smul f t := by
    change divZ K (Additive.ofMul (f * t)) + α = divZ K (Additive.ofMul f) + (divZ K _ + α)
    rw [ofMul_mul, map_add, add_assoc]

lemma triv_τ (α : ArithDivZ K) (f : Kˣ) :
    (triv α).τ f = divZ K (Additive.ofMul f) + α := rfl

variable (K) in
/-- **`F^⊛_mod ([FrdI] Ex 6.3) → F^⊛_MOD`**: `α ↦ triv α`, and the morphism `(n, Z, u)` goes to
the `n`-equivariant map `f ↦ u·f^n`. -/
noncomputable abbrev ofModel : GlobalFrobenioid K ⥤ TorsorFrob K where
  obj X := triv X.α
  map {X Y} φ := ⟨φ.deg, fun (f : Kˣ) => (Additive.toMul (α := Kˣ) φ.u * f ^ (φ.deg : ℕ) :
      Kˣ), fun f t => by
      change Additive.toMul (α := Kˣ) φ.u * (f * t) ^ (φ.deg : ℕ) = f ^ (φ.deg : ℕ) * _
      rw [mul_pow, mul_left_comm],
    fun t => by
      have r := φ.rel
      change (φ.deg : ℕ) • X.α + φ.div = Y.α + divZ K φ.u at r
      have hd : φ.div = Y.α + divZ K φ.u - (φ.deg : ℕ) • X.α := by rw [← r]; abel
      change divZ K (Additive.ofMul (Additive.toMul (α := Kˣ) φ.u * t ^ (φ.deg : ℕ))) + Y.α -
        (φ.deg : ℕ) • (divZ K (Additive.ofMul t) + X.α) ∈ effConeZ K
      convert φ.div_mem using 1
      rw [hd, ofMul_mul, ofMul_pow, ofMul_toMul, map_add, map_nsmul, smul_add]
      abel⟩
  map_id X := hom_ext rfl (funext fun f => by
    change Additive.toMul (0 : Additive Kˣ) * f ^ 1 = f
    simp)
  map_comp {X Y Z} φ ψ := hom_ext rfl (funext fun f => by
    change Additive.toMul (α := Kˣ) (ψ.u + (ψ.deg : ℕ) • φ.u) * f ^ ((ψ.deg * φ.deg : ℕ+) : ℕ) =
      Additive.toMul (α := Kˣ) ψ.u * (Additive.toMul (α := Kˣ) φ.u * f ^ (φ.deg : ℕ)) ^ (ψ.deg : ℕ)
    rw [toMul_add, toMul_nsmul, mul_pow, ← pow_mul, PNat.mul_coe, mul_comm (ψ.deg : ℕ), mul_assoc])

@[simp] lemma ofModel_obj_τ (X : GlobalFrobenioid K) (f : Kˣ) :
    ((ofModel K).obj X).τ f = divZ K (Additive.ofMul f) + X.α := rfl

/-- **`ofModel` preserves Frobenius degrees.** -/
@[simp] lemma ofModel_map_deg {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    ((ofModel K).map φ).deg = φ.deg := rfl

lemma ofModel_map_ψ {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) (f : Kˣ) :
    ((ofModel K).map φ).ψ f = Additive.toMul (α := Kˣ) φ.u * f ^ (φ.deg : ℕ) := rfl

/-- **`ofModel` induces the identity on `K^×`**: the morphism attached to `(n, Z, u)` sends the
base point `1` of the trivial torsor to `u`. -/
@[simp] lemma ofModel_map_one {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    ((ofModel K).map φ).ψ (1 : Kˣ) = Additive.toMul (α := Kˣ) φ.u := by
  rw [ofModel_map_ψ, one_pow, mul_one]

lemma div_eq_of_rel {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    φ.div = Y.α + divZ K φ.u - (φ.deg : ℕ) • X.α := by
  have r := φ.rel
  change (φ.deg : ℕ) • X.α + φ.div = Y.α + divZ K φ.u at r
  rw [← r]
  abel

instance : (ofModel K).Faithful where
  map_injective {X Y} φ ψ h := by
    have h1 : φ.deg = ψ.deg := congrArg TorsorHom.deg h
    have h2 := congrFun (congrArg TorsorHom.ψ h) (1 : Kˣ)
    rw [ofModel_map_one, ofModel_map_one] at h2
    have hu : φ.u = ψ.u := Additive.toMul.injective h2
    refine Model.hom_ext h1 (Subsingleton.elim _ _) ?_ hu
    rw [div_eq_of_rel, div_eq_of_rel, hu, h1]

instance : (ofModel K).Full where
  map_surjective {X Y} χ := by
    have hint := χ.integral (1 : Kˣ)
    set u : Additive Kˣ := Additive.ofMul (χ.ψ (1 : Kˣ))
    refine ⟨Model.mk' χ.deg (Discrete.eqToHom (Subsingleton.elim _ _))
      (Y.α + divZ K u - (χ.deg : ℕ) • X.α) ?_ u ?_, ?_⟩
    · convert hint using 1
      change _ = divZ K (Additive.ofMul (χ.ψ (1 : Kˣ))) + Y.α -
        (χ.deg : ℕ) • (divZ K (Additive.ofMul (1 : Kˣ)) + X.α)
      rw [ofMul_one, map_zero, zero_add]
      abel
    · change (χ.deg : ℕ) • X.α + (Y.α + divZ K u - (χ.deg : ℕ) • X.α) = Y.α + divZ K u
      abel
    · refine hom_ext rfl (funext fun (f : Kˣ) => ?_)
      rw [ofModel_map_ψ (K := K), Model.mk'_u, Model.mk'_deg]
      have := χ.ψ_smul f (1 : Kˣ)
      change χ.ψ (f * 1) = f ^ (χ.deg : ℕ) * χ.ψ (1 : Kˣ) at this
      rw [mul_one] at this
      rw [this, mul_comm]
      rfl

lemma TorsorObj.smul_left_injective (T : TorsorObj K) (t : T.T) :
    Function.Injective fun f : Kˣ => f • t := fun f g h => by
  have := T.free (g⁻¹ * f) t (by rw [mul_smul]; simp only at h; rw [h, inv_smul_smul])
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- Every object is isomorphic to a trivial one: `T ≅ triv (τ t₀)` via `f ↦ f·t₀`. -/
noncomputable def isoTriv (T : TorsorFrob K) (t₀ : T.T) : (ofModel K).obj ⟨pt, T.τ t₀⟩ ≅ T where
  hom := ⟨1, fun f => f • t₀, fun f g => by
      change (f * g) • t₀ = f ^ 1 • g • t₀
      rw [pow_one, mul_smul],
    fun f => by
      change T.τ (f • t₀) - (1 : ℕ) • (divZ K (Additive.ofMul f) + T.τ t₀) ∈ effConeZ K
      rw [T.τ_smul, one_smul, sub_self]
      exact zero_mem _⟩
  inv := ⟨1, fun t => (T.trans t₀ t).choose, fun f t => by
      apply TorsorObj.smul_left_injective T t₀
      change (T.trans t₀ (f • t)).choose • t₀ = (f ^ 1 * (T.trans t₀ t).choose) • t₀
      rw [(T.trans t₀ (f • t)).choose_spec, pow_one, mul_smul, (T.trans t₀ t).choose_spec],
    fun t => by
      have hτ : T.τ t = divZ K (Additive.ofMul (T.trans t₀ t).choose) + T.τ t₀ := by
        conv_lhs => rw [← (T.trans t₀ t).choose_spec]
        exact T.τ_smul _ _
      change divZ K (Additive.ofMul (T.trans t₀ t).choose) + T.τ t₀ - (1 : ℕ) • T.τ t ∈
        effConeZ K
      rw [hτ, one_smul, sub_self]
      exact zero_mem _⟩
  hom_inv_id := hom_ext rfl (funext fun f => by
    apply TorsorObj.smul_left_injective T t₀
    exact (T.trans t₀ (f • t₀)).choose_spec)
  inv_hom_id := hom_ext rfl (funext fun t => (T.trans t₀ t).choose_spec)

instance : (ofModel K).EssSurj where
  mem_essImage T := ⟨⟨pt, T.τ T.nonempty.some⟩, ⟨isoTriv T T.nonempty.some⟩⟩

instance : (ofModel K).IsEquivalence where

variable (K) in
/-- **IUT III, Example 3.6(i)**: `F^⊛_mod ([FrdI] Ex 6.3) ≌ F^⊛_MOD`, compatible with Frobenius
degrees (`ofModel_map_deg`) and with the identity on `K^×` (`ofModel_map_one`). -/
noncomputable def equivModel : GlobalFrobenioid K ≌ TorsorFrob K := (ofModel K).asEquivalence

variable (K) in
/-- **IUT III, Example 3.6(iii)**: composing (ii) and (i), the fractional-ideal version and the
torsor version are equivalent, `F^⊛_mod (fractional ideals) ≌ F^⊛_MOD`. -/
noncomputable def fracIdealEquivTorsor : FracIdealFrob K ≌ TorsorFrob K :=
  (FracIdealFrob.equivModel K).trans (equivModel K)

/-- The composite of (iii) preserves Frobenius degrees. -/
lemma fracIdealToTorsor_map_deg {J₁ J₂ : FracIdealFrob K} (φ : J₁ ⟶ J₂) :
    ((FracIdealFrob.toModel K ⋙ ofModel K).map φ).deg = φ.deg := rfl

/-- **The composite of (iii) induces the identity on `K^×`**: `(n, f) ↦` the `n`-equivariant map
sending `1 ↦ f`. -/
lemma fracIdealToTorsor_map_one {J₁ J₂ : FracIdealFrob K} (φ : J₁ ⟶ J₂) :
    ((FracIdealFrob.toModel K ⋙ ofModel K).map φ).ψ (1 : Kˣ) = FracIdealHom.f φ := by
  change ((ofModel K).map ((FracIdealFrob.toModel K).map φ)).ψ (1 : Kˣ) = FracIdealHom.f φ
  rw [ofModel_map_one, FracIdealFrob.toModel_map_u]
  rfl

end TorsorFrob

end Frobenioid

end Iut
