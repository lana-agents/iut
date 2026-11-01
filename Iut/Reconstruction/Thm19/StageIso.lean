/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ConstRestrict
import Iut.Reconstruction.Thm19.NFColimit

/-!
# Stage isomorphisms over `ψ` (MR9 item 3, step 5): the generic part

For [AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) over
an isomorphism `Π_U ≃ Π_{U'}`, each stage `V_{K₁}` (an open `V ⊆ U` and a finite extension `K₁` of
the field of constants) needs an isomorphism `H¹(Π_{V_{K₁}}, Ẑ(1)) ≃* H¹(Π_{V'_{K₁'}}, Ẑ(1))`. In
the Galois models this is generic:

* **`h1Congr`**: `H¹(P, M) ≃* H¹(P', M')` from `e : P ≃ₜ* P'` and an `e`-equivariant
  `χ : M ≃ₜ* M'`;
* `zHatResEquiv`: the identification `Ẑ(1)_K ≃ₜ* Ẑ(1)_L` (characteristic `0`, same `Ω`; the
  identity at every level), and `zKEquiv` for the base change `U_K`;
* **`smul_eq_of_piToGk_eq`**: `Π_U` acts on `Ẑ(1)` through `G_k` (roots of unity are
  algebraic, `muMap_surjective`, `muMap_piToGk_smul`);
* **`constH1Iso`**: for `e : Π_U ≃ₜ* Π_{U'}` over `ψ : G_k ≃* G_{k'}` and `χ : Ẑ(1) ≃ₜ* Ẑ(1)'`
  equivariant along `e`, and `K / k` finite, the isomorphism
  `H¹(Π_{U_K}, Ẑ(1)) ≃* H¹(Π_{U'_{K'}}, Ẑ(1))` with `G_{K'} = ψ(G_K)` (`constIso`, coefficients
  `zK' ∘ χ ∘ zK⁻¹`).
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### `H¹` along an isomorphism of groups and coefficients -/

section H1Congr

variable {P P' M M' : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]
  [Group P'] [TopologicalSpace P'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction P' M']

omit [IsTopologicalGroup M] [IsTopologicalGroup M'] in
lemma h1Congr_comm (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m)
    (g : P') (m : M) :
    χ.toMulEquiv.toMonoidHom (e.symm.toMulEquiv.toMonoidHom g • m) =
      g • χ.toMulEquiv.toMonoidHom m := by
  change χ (e.symm g • m) = g • χ m
  rw [hχ, ContinuousMulEquiv.apply_symm_apply]

omit [IsTopologicalGroup M] [IsTopologicalGroup M'] in
lemma h1Congr_comm_symm (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m)
    (g : P) (m : M') :
    χ.symm.toMulEquiv.toMonoidHom (e.toMulEquiv.toMonoidHom g • m) =
      g • χ.symm.toMulEquiv.toMonoidHom m := by
  change χ.symm (e g • m) = g • χ.symm m
  rw [ContinuousMulEquiv.symm_apply_eq, hχ, ContinuousMulEquiv.apply_symm_apply]

/-- **`H¹(P, M) ≃* H¹(P', M')`** from `e : P ≃ₜ* P'` and an `e`-equivariant `χ : M ≃ₜ* M'`
(cocycles `c ↦ χ ∘ c ∘ e⁻¹`). -/
def h1Congr (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m) :
    ContH1 P M ≃* ContH1 P' M' where
  toFun := ContH1.map e.symm.toMulEquiv.toMonoidHom e.symm.continuous
    χ.toMulEquiv.toMonoidHom χ.continuous (h1Congr_comm e χ hχ)
  invFun := ContH1.map e.toMulEquiv.toMonoidHom e.continuous
    χ.symm.toMulEquiv.toMonoidHom χ.symm.continuous (h1Congr_comm_symm e χ hχ)
  left_inv x := by
    induction x using ContH1.induction_on with
    | h c =>
      simp only [ContH1.map_mk]
      congr 1
      apply Subtype.ext
      funext g
      simp only [ContH1.cocyclesMap_apply]
      exact (χ.symm_apply_apply _).trans (congrArg _ (e.symm_apply_apply g))
  right_inv x := by
    induction x using ContH1.induction_on with
    | h c =>
      simp only [ContH1.map_mk]
      congr 1
      apply Subtype.ext
      funext g
      simp only [ContH1.cocyclesMap_apply]
      exact (χ.apply_symm_apply _).trans (congrArg _ (e.apply_symm_apply g))
  map_mul' := map_mul _

lemma h1Congr_apply (e : P ≃ₜ* P') (χ : M ≃ₜ* M') (hχ : ∀ p m, χ (p • m) = e p • χ m)
    (x : ContH1 P M) :
    h1Congr e χ hχ x = ContH1.map e.symm.toMulEquiv.toMonoidHom e.symm.continuous
      χ.toMulEquiv.toMonoidHom χ.continuous (h1Congr_comm e χ hχ) x := rfl

end H1Congr

/-! ### `Ẑ(1)` over different fields of characteristic `0` -/

section ZHat

variable {Ω : Type*} [Field Ω]

lemma muMap_self (n : ℕ) (ζ : Mu n Ω) : muMap n Ω Ω ζ = ζ := Mu.ext (Units.ext rfl)

variable (K L M : Type*) [Field K] [Field L] [Field M] [CharZero K] [CharZero L] [CharZero M]

omit [CharZero M] in
lemma zHatRes_zHatRes (x : ZHatOne K Ω) :
    zHatRes L M Ω Ω (zHatRes K L Ω Ω x) = zHatRes K M Ω Ω x := by
  apply Subtype.ext
  funext i
  rw [zHatRes_apply, zHatRes_apply, zHatRes_apply, muMap_self, muMap_self, muMap_self]
  rfl

lemma zHatRes_self (x : ZHatOne K Ω) : zHatRes K K Ω Ω x = x := by
  apply Subtype.ext
  funext i
  rw [zHatRes_apply, muMap_self]
  rfl

variable (Ω) in
/-- **`Ẑ(1)_K ≃ₜ* Ẑ(1)_L`** (characteristic `0`, the same `Ω`: the identity at every level). -/
def zHatResEquiv : ZHatOne K Ω ≃ₜ* ZHatOne L Ω where
  toFun := zHatRes K L Ω Ω
  invFun := zHatRes L K Ω Ω
  left_inv x := (zHatRes_zHatRes K L K x).trans (zHatRes_self K x)
  right_inv x := (zHatRes_zHatRes L K L x).trans (zHatRes_self L x)
  map_mul' := map_mul _
  continuous_toFun := continuous_zHatRes K L Ω Ω
  continuous_invFun := continuous_zHatRes L K Ω Ω

@[simp] lemma zHatResEquiv_apply (x : ZHatOne K Ω) :
    zHatResEquiv Ω K L x = zHatRes K L Ω Ω x := rfl

@[simp] lemma zHatResEquiv_symm_apply (x : ZHatOne L Ω) :
    (zHatResEquiv Ω K L).symm x = zHatRes L K Ω Ω x := rfl

end ZHat

/-! ### `Π_U` acts on `Ẑ(1)` through `G_k` -/

section Action

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

lemma mu_smul_eq_of_piToGk_eq (n : ℕ) [NeZero n] {g₁ g₂ : Pi D}
    (h : piToGk D g₁ = piToGk D g₂) (ζ : Mu n Ω) : g₁ • ζ = g₂ • ζ := by
  obtain ⟨ζ', rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n ζ
  rw [← muMap_piToGk_smul D n g₁ ζ', ← muMap_piToGk_smul D n g₂ ζ', h]

omit [IsAlgClosed Ω] in
lemma coe_smul_zHatOne (L : Type*) [Field L] (g : Pi D) (x : ZHatOne L Ω) (i : KummerIndex L) :
    ((g • x : ZHatOne L Ω) : ∀ j : KummerIndex L, Mu j.n Ω) i =
      g • (x : ∀ j : KummerIndex L, Mu j.n Ω) i := by
  induction g using QuotientGroup.induction_on with
  | H h => rfl

/-- **`Π_U` acts on `Ẑ(1)` through `G_k`.** -/
theorem smul_eq_of_piToGk_eq (L : Type*) [Field L] {g₁ g₂ : Pi D}
    (h : piToGk D g₁ = piToGk D g₂) (x : ZHatOne L Ω) : g₁ • x = g₂ • x := by
  apply Subtype.ext
  funext i
  rw [coe_smul_zHatOne, coe_smul_zHatOne]
  exact mu_smul_eq_of_piToGk_eq D i.n h _

/-- **The Galois-model transition maps lie over `G_k`** (same `k`). -/
lemma piToGk_piT {t₁ t₂ : Ω} (D₁ : Pi1.Orbifold.GaloisData k t₁) (D₂ : Pi1.Orbifold.GaloisData k t₂)
    [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω] (hF : ∀ x ∈ F D₁, x ∈ F D₂)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t₁ ∈ W) (hH₁ : D₁.H ≤ D₁.HL) (p : Pi D₂) :
    piToGk D₁ (piT D₁ D₂ hF hW hH₁ p) = piToGk D₂ p := by
  induction p using QuotientGroup.induction_on with
  | H σ =>
    rw [piT_mk, piToGk_mk, piToGk_mk]
    ext x
    change algebraMap (kbar k Ω) Ω _ = algebraMap (kbar k Ω) Ω _
    rw [algebraMap_hToGk_apply, algebraMap_hToGk_apply]
    rfl

end Action

/-! ### Restriction to the base change along `ψ` -/

section Const

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))
  (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω') (hχ : ∀ p z, χ (p • z) = e p • χ z)
  (K : IntermediateField k Ω) [FiniteDimensional k K] [FiniteDimensional k' (constField ψ K)]

attribute [local instance] CurvesJacobian.isFunctionField_F

variable (D) in
/-- `Ẑ(1)_F ≃ₜ* Ẑ(1)_{F K}` for the base change `U_K` (`zK` with its inverse). -/
abbrev zKEquiv : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F (constExt K D)) Ω :=
  zHatResEquiv Ω (F D) (F (constExt K D))

/-- The coefficients of `constH1Iso`: `zK' ∘ χ ∘ zK⁻¹`. -/
abbrev constCyclo :
    ZHatOne (F (constExt K D)) Ω ≃ₜ* ZHatOne (F (constExt (constField ψ K) D')) Ω' :=
  (zKEquiv D K).symm.trans (χ.trans (zKEquiv D' (constField ψ K)))

set_option maxHeartbeats 1600000 in
-- the coefficients of the base change are unified slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_{U_K}` on `Ẑ(1)` is found slowly
include hχ in
lemma constCyclo_smul (q : Pi (constExt K D)) (z : ZHatOne (F (constExt K D)) Ω) :
    constCyclo ψ χ K (q • z) = constIso e ψ he hs K q • constCyclo ψ χ K z := by
  obtain ⟨w, rfl⟩ := (zKEquiv D K).surjective z
  have hz : _ = q • zKEquiv D K w := zK_piRes_smul K D q w
  have e1 := (congrArg (zKEquiv D K).symm hz.symm).trans ((zKEquiv D K).symm_apply_apply _)
  simp only [constCyclo, ContinuousMulEquiv.trans_apply]
  rewrite [e1, (zKEquiv D K).symm_apply_apply w, hχ, ← piRes_constIso e ψ he hs K q]
  exact zK_piRes_smul (constField ψ K) D' _ _

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_{U_K}` on `Ẑ(1)` is found slowly
include hχ in
/-- **`H¹(Π_{U_K}, Ẑ(1)) ≃* H¹(Π_{U'_{K'}}, Ẑ(1))`** for `e : Π_U ≃ₜ* Π_{U'}` over
`ψ : G_k ≃* G_{k'}` and `e`-equivariant coefficients `χ`, with `G_{K'} = ψ(G_K)`. -/
def constH1Iso :
    ContH1 (Pi (constExt K D)) (ZHatOne (F (constExt K D)) Ω) ≃*
      ContH1 (Pi (constExt (constField ψ K) D')) (ZHatOne (F (constExt (constField ψ K) D')) Ω') :=
  h1Congr (constIso e ψ he hs K) (constCyclo ψ χ K) (constCyclo_smul e ψ he hs χ hχ K)

end Const

end Iut.Reconstruction.Thm19
