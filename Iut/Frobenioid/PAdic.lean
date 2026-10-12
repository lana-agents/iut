/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Global

/-!
# The `p`-adic Frobenioid of a local field ([FrdII], Example 1.1; IUT I, Example 3.2)

For a finite place `w` of a number field `K`, the local field `K_w = completionAt K w` (the
concrete local fields of `Iut/Concrete/LocalTheory.lean` and `Iut/Concrete/LocalConstruct`),
the **`p`-adic Frobenioid** of `K_w` over the trivial Galois extension ([FrdII], Example 1.1(ii),
with `Π = Gal(K̄_w/K_w)` replaced by the trivial group; IUT I, Example 3.2(i) uses the
corresponding Frobenioid `C_v` over the base category of the decomposition group) is the model
Frobenioid with

* base category `Pt`;
* divisor monoid `ord(𝒪^▷) ≅ ℤ_{≥0}` (`Φ^gp = ℤ`, `natCone`);
* rational functions `K_w^×` with `Div_B = ord_w : K_w^× → ℤ` (`ordHom`).

Objects `(pt, n)` correspond to the fractional ideals `𝔭_w^{-n}`, i.e. line bundles on
`Spec 𝒪_w`.

Proved here (cf. [FrdII], Example 1.1(ii) and IUT I, Example 3.2(i), where these monoids are
`𝒪^▷_{K_w} \ {0}` and `𝒪^×_{K_w}`):

* `PAdic.isFrobenioid`: it is a Frobenioid ([FrdI], Theorem 5.2(ii));
* **`PAdic.orhdEquiv`**: `O^▷(A) ≃ {u ∈ K_w^× : ‖u‖ ≤ 1} = 𝒪_w \ {0}`;
* **`PAdic.ounitsEquiv`**: `O^×(A) ≃ {u ∈ K_w^× : ‖u‖ = 1} = 𝒪_w^×`;
* `PAdic.nonempty_iso_iff`: all objects are isomorphic (`Pic_Φ = ℤ/ord(K_w^×) = 0`; the
  model is of base-trivial type).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

/-! ### The divisor monoid `ℤ_{≥0}` -/

/-- `ℤ_{≥0} ⊆ ℤ` (lifted to the universe of the local field). -/
def natCone : AddSubmonoid (ULift.{u} ℤ) where
  carrier := {n | 0 ≤ n.down}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, ULift.add_down] at ha hb ⊢
    exact add_nonneg ha hb
  zero_mem' := le_refl (0 : ℤ)

lemma mem_natCone {n : ULift.{u} ℤ} : n ∈ natCone ↔ 0 ≤ n.down := Iff.rfl

/-- The divisor monoid `ord(𝒪^▷) ≅ ℤ_{≥0}` on `Pt`. -/
abbrev phiNat : DivMonoid.{u} Pt :=
  constDivMonoid (ULift.{u} ℤ) natCone
    (fun {x} h h' => by
      rw [mem_natCone] at h h'
      ext
      simp only [ULift.neg_down, Left.nonneg_neg_iff] at h'
      exact le_antisymm h' h)
    (fun {x} n hn h => by
      rw [mem_natCone] at h ⊢
      rw [ULift.smul_down, nsmul_eq_mul] at h
      exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hn))
    (fun x => ⟨⟨max x.down 0⟩, by simp [mem_natCone], ⟨max (-x.down) 0⟩, by simp [mem_natCone], by
      ext
      simp⟩)

variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)

/-! ### The valuation as a homomorphism -/

/-- `ord_w : K_w^× → ℤ` (`v_w(x) = exp(−ord_w x)`), as a homomorphism of additive groups. -/
noncomputable def ordHom : Additive (completionAt K w)ˣ →+ ULift.{u} ℤ where
  toFun x := ⟨-WithZero.log (Valued.v ((x.toMul : (completionAt K w)ˣ) : completionAt K w))⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp only [toMul_add, Units.val_mul, map_mul, ULift.add_down]
    rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.toMul.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.toMul.ne_zero)]
    ring

lemma norm_eq_ordHom (x : (completionAt K w)ˣ) :
    ‖(x : completionAt K w)‖ = primeNorm w ^ (-(ordHom w (Additive.ofMul x)).down) := by
  rw [norm_eq_primeNorm_zpow w _ x.ne_zero]
  simp [ordHom]

lemma ordHom_nonneg_iff (x : (completionAt K w)ˣ) :
    0 ≤ (ordHom w (Additive.ofMul x)).down ↔ ‖(x : completionAt K w)‖ ≤ 1 := by
  rw [norm_eq_ordHom]
  have h := one_lt_primeNorm w
  constructor
  · intro hx
    exact zpow_le_one_of_nonpos₀ (by linarith) (by linarith)
  · intro hx
    by_contra hneg
    have : 1 < primeNorm w ^ (-(ordHom w (Additive.ofMul x)).down) :=
      one_lt_zpow₀ h (by linarith)
    linarith

lemma ordHom_eq_zero_iff (x : (completionAt K w)ˣ) :
    (ordHom w (Additive.ofMul x)).down = 0 ↔ ‖(x : completionAt K w)‖ = 1 := by
  rw [norm_eq_ordHom]
  have h := one_lt_primeNorm w
  constructor
  · intro hx
    rw [hx, neg_zero, zpow_zero]
  · intro hx
    have := (zpow_right_injective₀ (by linarith : (0 : ℝ) < primeNorm w) h.ne').eq_iff.mp
      (hx.trans (zpow_zero _).symm)
    linarith

/-! ### The `p`-adic Frobenioid -/

/-- The rational functions `K_w^×`. -/
noncomputable abbrev bLoc : GrpOn.{u} Pt := constGrpOn (Additive (completionAt K w)ˣ)

/-- `Div_B = ord_w`. -/
noncomputable abbrev divLoc : DivHom (bLoc w) (phiNat).toGrpOn := constDivHom (ordHom w)

/-- **The `p`-adic Frobenioid of `K_w`** (over the trivial Galois extension). -/
abbrev PAdic : Type u := Model phiNat (bLoc w) (divLoc w)

namespace PAdic

local notation "𝐏" => Model.toElem phiNat (bLoc w) (divLoc w)

/-- **The `p`-adic Frobenioid is a Frobenioid** ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid : IsFrobenioid 𝐏 := Model.isFrobenioid

variable {w}

lemma base_ext {X Y : PAdic w} (f g : X.base ⟶ Y.base) : f = g := Subsingleton.elim f g

/-- **`O^▷(A) = 𝒪_w \ {0}`**: a base-identity linear endomorphism `(1, id, Z, u)` of `A`
satisfies `Z = ord(u)`, so it is determined by `u ∈ K_w^×` with `‖u‖ ≤ 1`. -/
noncomputable def orhdEquiv (X : PAdic w) :
    Orhd 𝐏 X ≃ {u : (completionAt K w)ˣ // ‖(u : completionAt K w)‖ ≤ 1} where
  toFun a := ⟨a.1.u.toMul, by
    rw [← ordHom_nonneg_iff]
    have h := a.1.rel
    rw [show a.1.deg = 1 from a.2.2] at h
    have hd : a.1.div = ordHom w a.1.u := by
      simpa using h
    have := a.1.div_mem
    rw [hd] at this
    exact mem_natCone.mp this⟩
  invFun u := ⟨Model.mk1 (𝟙 _) (ordHom w (Additive.ofMul u.1))
      (by simpa [mem_natCone] using (ordHom_nonneg_iff w u.1).mpr u.2) (Additive.ofMul u.1)
      rfl, rfl, rfl⟩
  left_inv a := by
    have h := a.1.rel
    rw [show a.1.deg = 1 from a.2.2] at h
    have hd : a.1.div = ordHom w a.1.u := by simpa using h
    refine Subtype.ext (Model.hom_ext ?_ (base_ext _ _) ?_ ?_)
    · exact (show a.1.deg = 1 from a.2.2).symm
    · exact hd.symm
    · simp
  right_inv u := rfl

/-- **`O^×(A) = 𝒪_w^×`**: the base-identity linear automorphisms are the `(1, id, 0, u)` with
`‖u‖ = 1`. -/
noncomputable def ounitsEquiv (X : PAdic w) :
    Ounits 𝐏 X ≃ {u : (completionAt K w)ˣ // ‖(u : completionAt K w)‖ = 1} where
  toFun a := ⟨a.1.u.toMul, by
    obtain ⟨h₁, -, h₃⟩ := (Model.isIso_iff a.1).mp a.2.1
    have h := a.1.rel
    rw [h₁, h₃] at h
    rw [← ordHom_eq_zero_iff]
    have hd : ordHom w a.1.u = 0 := by simpa using h
    exact congrArg ULift.down hd⟩
  invFun u :=
    let φ : X ⟶ X := Model.mk1 (𝟙 _) 0 (natCone.{u}.zero_mem) (Additive.ofMul u.1) (by
      have := (ordHom_eq_zero_iff w u.1).mpr u.2
      change X.α + 0 = X.α + ordHom w (Additive.ofMul u.1)
      rw [show ordHom w (Additive.ofMul u.1) = 0 from ULift.ext _ _ this])
    ⟨φ, Model.isIso_of φ rfl (inferInstanceAs (IsIso (𝟙 pt))) rfl, rfl, rfl⟩
  left_inv a := by
    obtain ⟨h₁, -, h₃⟩ := (Model.isIso_iff a.1).mp a.2.1
    refine Subtype.ext (Model.hom_ext h₁.symm (base_ext _ _) h₃.symm ?_)
    simp
  right_inv u := rfl

/-- **All objects are isomorphic** (`Pic_Φ(A) = ℤ/ord(K_w^×) = 0`, as `ord` is surjective). -/
theorem nonempty_iso (X Y : PAdic w) : Nonempty (X ≅ Y) := by
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer K
  have hv : Valued.v (π : w.maximalIdeal.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hne : (π : w.maximalIdeal.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let U : (completionAt K w)ˣ := Units.mk0 _ hne
  have hU : ordHom w (Additive.ofMul U) = ⟨1⟩ := by
    ext
    simp [ordHom, U, hπ]
  let m : ℤ := X.α.down - Y.α.down
  have hm : ordHom w (Additive.ofMul (U ^ m)) = ⟨m⟩ := by
    rw [ofMul_zpow, map_zsmul, hU]
    ext
    simp
  let φ : X ⟶ Y := Model.mk1 (Discrete.eqToHom (Subsingleton.elim _ _)) 0 (natCone.{u}.zero_mem)
      (Additive.ofMul (U ^ m)) (by
    change X.α + 0 = Y.α + ordHom w (Additive.ofMul (U ^ m))
    rw [hm]
    ext
    simp [m])
  haveI := Model.isIso_of φ rfl (isIso_pt _) rfl
  exact ⟨asIso φ⟩

end PAdic

end Frobenioid

end Iut
