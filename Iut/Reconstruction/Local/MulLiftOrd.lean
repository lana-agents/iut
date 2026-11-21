/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.MulLift
import Iut.Frobenioid.Thm24iiAux

/-!
# [AbsTopIII], Proposition 3.2 (iv), surjectivity, for `G_K ↷ \bar{ℚ}_p^×` with `ord`

[AbsTopIII], Proposition 3.2 (iv) (`Topics in Absolute Anabelian Geometry III.txt`,
l.4111–4124): for MLF-Galois `TM`-pairs, `Isom((Π ↷ M), (Π* ↷ M*)) → Isom(Π, Π*)` is a
bijection; the surjectivity (proof, l.4150–4155) comes from the copy of `O^▷_k` in the
abelianizations of the open subgroups of `G_k` (local class field theory). For a finite
extension `K ⊆ \bar{ℚ}_p` of `ℚ_p`:

* `ordU_ιF`: `ord(ι x) · v(p) = v(x)` for `x` in a finite extension `F` of `ℚ_p`;
* **`ord_mulLift`**: the lift `mulLift φ` of `φ ∈ Aut(G_K)` (`MulLift.lean`) preserves `ord`
  (it preserves the units and `ord` on `K^×`, and `ord(\bar{ℚ}_p^×) ⊆ ℚ`);
* **`exists_mulLift`**: every automorphism `φ` of the topological group `G_K` has a
  `φ`-equivariant additive automorphism `ψ` of `\bar{ℚ}_p^×` (`PAdicGalois.Mul p`) with
  `ord ∘ ψ = ord`.
-/

open PadicField IntermediateField Iut.Reconstruction

set_option linter.unusedSectionVars false

noncomputable section

namespace Iut

namespace Frobenioid

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

/-! ### `ord` on finite subextensions -/

section Ord

/-- `ord` on `K̄ˣ` (multiplicative notation). -/
abbrev ordU (x : K̄ˣ) : ℝ := ord p (Additive.ofMul x)

theorem ordU_mul (x y : K̄ˣ) : ordU (x * y) = ordU x + ordU y := by
  rw [ordU, ofMul_mul, map_add]

theorem ordU_pow (x : K̄ˣ) (n : ℕ) : ordU (x ^ n) = n * ordU x := by
  rw [ordU, ofMul_pow, map_nsmul, nsmul_eq_mul]

theorem ordU_inv (x : K̄ˣ) : ordU x⁻¹ = -ordU x := by
  rw [ordU, ofMul_inv, map_neg]

theorem ordU_zpow (x : K̄ˣ) (n : ℤ) : ordU (x ^ n) = n * ordU x := by
  rw [ordU, ofMul_zpow, map_zsmul, zsmul_eq_mul]

theorem ordU_eq_zero_iff (x : K̄ˣ) : ordU x = 0 ↔ ‖(x : K̄)‖ = 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx : 0 < ‖(x : K̄)‖ := norm_pos_iff.2 x.ne_zero
  change -Real.logb p ‖(x : K̄)‖ = 0 ↔ _
  rw [neg_eq_zero, Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact absurd h (by positivity)
    · exact absurd h hp1.ne'
    · linarith
    · exact absurd h hx.ne'
    · exact h
    · linarith
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [Algebra F (PadicAlgCl p)] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]

/-- `ι : Fˣ → K̄ˣ`. -/
abbrev ιF : Fˣ →* K̄ˣ := Units.map (algebraMap F K̄ : F →* K̄)

theorem ιF_injective : Function.Injective (ιF (p := p) F) := fun _ _ h =>
  Units.ext ((algebraMap F K̄).injective (congrArg Units.val h))

theorem norm_algebraMap_eq_nrm (x : F) : ‖algebraMap F K̄ x‖ = nrm p F x := by
  rw [nrm_apply, spectralNorm.eq_of_tower (K := ℚ_[p]) (L := K̄) x]
  rfl

theorem p_ne_zero' : (p : F) ≠ 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  exact Nat.cast_ne_zero.2 hp.out.ne_zero

theorem nrm_p : nrm p F (p : F) = (p : ℝ)⁻¹ := by
  have h := nrm_algebraMap (p := p) (K := F) (p : ℚ_[p])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]

theorem v_p_pos : 0 < v p (p : F) := by
  rw [← nrm_lt_one_iff_v_pos (p_ne_zero' (p := p) F), nrm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- **`ord(ι x) · v(p) = v(x)`** for `x ∈ F^×`. -/
theorem ordU_ιF (x : Fˣ) : ordU (ιF (p := p) F x) * v p (p : F) = v p (x : F) := by
  set π := uniformizer p F
  have hπ : IsUniformizer p F π := uniformizer_spec
  have hπ0 : 0 < nrm p F π := nrm_pos_iff.2 hπ.ne_zero
  have hn : ‖algebraMap F K̄ (x : F)‖ = nrm p F π ^ v p (x : F) :=
    (norm_algebraMap_eq_nrm (p := p) F _).trans (nrm_eq_nrm_uniformizer_zpow hπ x.ne_zero)
  have hpn : (p : ℝ)⁻¹ = nrm p F π ^ v p (p : F) :=
    (nrm_p (p := p) F).symm.trans (nrm_eq_nrm_uniformizer_zpow hπ (p_ne_zero' (p := p) F))
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hlog : -Real.log p = (v p (p : F) : ℝ) * Real.log (nrm p F π) := by
    rw [← Real.log_inv, hpn, Real.log_zpow]
  change -Real.logb p ‖algebraMap F K̄ (x : F)‖ * _ = _
  rw [hn, Real.logb, Real.log_zpow]
  field_simp
  linear_combination (v p (x : F) : ℝ) * hlog

theorem ordU_ιF_p : ordU (ιF (p := p) F (Units.mk0 (p : F) (p_ne_zero' (p := p) F))) = 1 := by
  have h := ordU_ιF (p := p) F (Units.mk0 (p : F) (p_ne_zero' (p := p) F))
  have hv : (0 : ℝ) < v p (p : F) := by exact_mod_cast v_p_pos (p := p) F
  rw [Units.val_mk0] at h
  exact (mul_eq_right₀ hv.ne').1 h

end Ord

/-! ### The lift preserves `ord`; the additive statements -/

section Final

variable [FiniteDimensional ℚ_[p] E]

/-- **`mulLift φ` preserves `ord`** (it preserves the units and `ord` on `K^×`, and
`ord(K̄^×) ⊆ ℚ`). -/
theorem ord_mulLift (φ : GK p E ≃ₜ* GK p E) (x : K̄ˣ) : ordU (mulLift p φ x) = ordU x := by
  set pu : Eˣ := Units.mk0 (p : E) (p_ne_zero' (p := p) E)
  have hp1 : ordU (ιF E pu) = 1 := ordU_ιF_p (p := p) E
  have hp2 : ordU (mulLift p φ (ιF E pu)) = 1 := by
    rw [← hp1]
    change -Real.logb p ‖_‖ = -Real.logb p ‖_‖
    exact congrArg (fun t => -Real.logb p t) (nrm_mulLift_algebraMap (p := p) φ pu)
  obtain ⟨q, hq⟩ := ord_mem_gammaQ (p := p) x
  change ((q : ℝ)) = ordU x at hq
  set u := x ^ q.den * (ιF E pu) ^ (-q.num)
  have hu : ordU u = 0 := by
    rw [ordU_mul, ordU_pow, ordU_zpow, hp1, ← hq]
    have := Rat.mul_den_eq_num q
    have h' : (q : ℝ) * q.den = q.num := by exact_mod_cast this
    push_cast
    linarith
  have hu' : ordU (mulLift p φ u) = 0 := by
    rw [ordU_eq_zero_iff] at hu ⊢
    exact (mulLift_mem_unitsΩ (p := p) φ (x := u) hu)
  rw [map_mul, map_pow, map_zpow, ordU_mul, ordU_pow, ordU_zpow, hp2] at hu'
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have h' : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  push_cast at hu'
  have h0 : (q.den : ℝ) * (ordU (mulLift p φ x) - q) = 0 := by linear_combination hu' - h'
  rw [← hq]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hden.ne')

/-- `Additive K̄ˣ ≃+ Additive K̄ˣ` from a multiplicative automorphism. -/
def ofMulAut (ψ : K̄ˣ ≃* K̄ˣ) : Mul p ≃+ Mul p := MulEquiv.toAdditive ψ

/-- **[AbsTopIII], Proposition 3.2 (iv), surjectivity** (`T = TM`, for `G_K ↷ K̄^×` with
`ord`): every automorphism `φ` of the topological group `G_K` lifts to a `φ`-equivariant
additive automorphism of `K̄^×` preserving `ord`. -/
theorem exists_mulLift (φ : GK p E ≃ₜ* GK p E) :
    ∃ ψ : Mul p ≃+ Mul p, (∀ (g : GK p E) (m : Mul p), ψ (g • m) = φ g • ψ m) ∧
      ∀ m, ord p (ψ m) = ord p m := by
  refine ⟨ofMulAut (mulLift p φ), fun g m => ?_, fun m => ord_mulLift φ m.toMul⟩
  apply Additive.toMul.injective
  apply Units.ext
  exact mulLift_smul φ g m.toMul (g • m.toMul) rfl

end Final

end PAdicGalois

end Frobenioid

end Iut

end
