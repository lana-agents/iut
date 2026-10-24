/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NFCurve
import CurvesJacobian.Kummer.KummerCurve
import CurvesJacobian.Kummer.JacobianDivExt
import CurvesJacobian.Kummer.JacobianLocalField

/-!
# [AbsTopIII] Thm 1.9 (d): Kummer classes of NF-functions and NF-constants inside `P_U`

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178)
reconstructs `k̄_NF^× ⊆ K^×_{Z_NF} ↪ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` "via the subgroups of (c) and the
characterizations of Kummer classes of nonconstant NF-rational functions and NF-constants given in
Proposition 1.8, (i), (ii) [cf. also the decomposition groups of (a)]". Prop 1.8 (l.2061–2106)
reads:

* (i) "A class `η ∈ P_U` is the Kummer class of a nonconstant NF-rational function if and only if
  there exist a positive multiple `η†` of `η` and NF-points `xᵢ ∈ U(k_x)`, `i = 1, 2`, […] such
  that […] `η†|x₁ = 0`, `η†|x₂ ≠ 0`."
* (ii) (paraphrased; the paper's word for the elements of `k^×` that descend to `k̄_NF` is the
  one formalised as `IsNFConstant`): if nonconstant NF-rational functions in `Γ(U, 𝒪_U^×)`
  exist, a class `η ∈ P_U ⋂ H¹(G_k, M_X) ≅ (k^×)^∧` is the Kummer class of such an element of
  `k^×` iff there exist a nonconstant NF-rational function `f ∈ Γ(U, 𝒪_U^×)` and an NF-point
  `x ∈ U(k_x)` such that `κ_U(f)|x = η|G_{k_x}`.

Here both are assembled from curves-jacobian's MR5 results (`Kummer/NFCharacterization.lean`,
`Kummer/NFCurve.lean`) as **equivalences** whose right-hand sides only use `P_U`, the restrictions
`η|_x = s_x^*(η)` to the decomposition groups of NF-points (`restrictClosed`) and the
`(k^×)^∧`-part, i.e. the data that steps (a)–(c) of Thm 1.9 provide:

* `RestrictTrivAt N hHL η` / `RestrictNontrivAt N hHL η`: `η|_x = 0` (resp. `≠ 0`) at some
  NF-point `x ∈ U(k_x)`, `[k_x : k] < ∞`; `IsNFKummerTest N hHL η`: the test of Prop 1.8 (i) for
  some positive multiple `η† = η^M`;
* **`isNFKummerTest_iff`** (Prop 1.8 (i)): for `η ∈ P_U`, the test holds iff some positive
  multiple of `η` is the Kummer class of a nonconstant NF-rational unit of `U`;
* **`exists_restrictClosed_eq_iff`** (Prop 1.8 (ii)): for `c ∈ (k^×)^∧`, the class of `c` passes
  the test of (ii) iff `c` is the Kummer class of some `b ∈ k^×` with `IsNFConstant b`;
* `isNFKummerTest_iff_curve` (given `⋂_N N · J(L) = 0` for one extension `L / k`, curves-jacobian
  `JacDivFree`), `isNFKummerTest_iff_curve_numberField` (unconditional, via curves-jacobian
  `jacDivFree_numberField`),
  `isNFKummerTest_iff_curve_of_isKummerFaithful` and `exists_restrictClosed_eq_iff_curve` (no
  Jacobian input): the same for the Galois model
  `curveGaloisData k hτ` of a curve `X` with `X(k) ≠ ∅` over a torally Kummer-faithful field `k`
  (number fields and finite extensions of `ℚ_p` are, unconditionally).

**On "positive multiple".** The paper's (i) has `η†` only on the test side. The "if" direction
for `η` itself does not follow from the argument over `k`: if `η^M = κ_U(w)`, then
`η = κ_U(v) · c` with `c ∈ (k^×)^∧` and `c^M ∈ k^×`, and nothing says that `c` comes from
`k^×`. It does become a Kummer class after the finite extension `k' = k(c^{1/M})`, which
Thm 1.9 (d) allows (`V` ranges over curves over finite extensions `k'` of `k_Z`). So the exact
statement over `k` is the one proved here:
"some positive multiple of `η` is the Kummer class of a nonconstant NF-rational function".

**Jacobian input.** Prop 1.8 (i) ("if") uses Kummer-faithfulness of the Jacobian through
Prop 1.6 (iii). The general curve version takes `JacDivFree X σ hσ L` (`⋂_N N · J(L) = 0` for one
field extension `L / k`) as a hypothesis; over number fields it is the curves-jacobian theorem
`jacDivFree_numberField` (MR5 Task B), so `isNFKummerTest_iff_curve_numberField` has no Jacobian
hypothesis. Prop 1.8 (ii) needs no such input.
-/

open KummerTheory Curve AffOrbicurve IsLocalRing CurvesJacobian.Kummer

universe u

namespace Iut.Reconstruction.Thm19

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [IsAlgClosed Ω] (N : NFModel D) (hHL : D.HL = D.H)

/-- `η|_x = 0` for some NF-point `x ∈ U(k_x)` with `[k_x : k] < ∞` (the restriction
`s_x^* : H¹(Π_U, Ẑ(1)) → H¹(G_{k_x}, Ẑ(1))` along the decomposition group of `x`). -/
def RestrictTrivAt (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) : Prop :=
  ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
    N.IsNFPoint A ∧
    letI := Decomposition.residueAlgebra A hk
    ∃ (_ : Algebra.IsIntegral k (ResidueField A))
      (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
        (Decomposition.residue_algebraMap_residueAlgebra A hk))),
      restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht η = 1

/-- `η|_x ≠ 0` for some NF-point `x ∈ U(k_x)` with `[k_x : k] < ∞`. -/
def RestrictNontrivAt (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) : Prop :=
  ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
    N.IsNFPoint A ∧
    letI := Decomposition.residueAlgebra A hk
    ∃ (_ : Algebra.IsIntegral k (ResidueField A))
      (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
        (Decomposition.residue_algebraMap_residueAlgebra A hk))),
      restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht η ≠ 1

/-- **The test of [AbsTopIII] Prop 1.8 (i)**: some positive multiple `η† = η^M` restricts
trivially to one NF-point and nontrivially to another. -/
def IsNFKummerTest (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ RestrictTrivAt N hHL (η ^ M) ∧ RestrictNontrivAt N hHL (η ^ M)

omit [IsAlgClosed Ω] [CharZero Ω] [IsGalois (K₀ k t) Ω] [CharZero k] in
/-- A unit of `U` that is not in the image of `kˣ` is transcendental over `k`, if `k` is
algebraically closed in `F`. -/
lemma transcendental_of_not_mem_range_constUnit
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (w : units D) (hw : w ∉ Set.range (constUnit D)) :
    Transcendental k ((w : (F D)ˣ) : F D) := by
  intro halg
  obtain ⟨c, hc⟩ := hkF _ halg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (w : (F D)ˣ).ne_zero hc.symm
  refine hw ⟨Units.mk0 c hc0, Subtype.ext (Units.ext ?_)⟩
  exact hc

variable {N hHL}

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop 1.8 (i)** (generic Galois model): a class `η ∈ P_U` passes the test of
(i) iff some positive multiple of `η` is the Kummer class of a nonconstant NF-rational unit of
`U`. -/
theorem isNFKummerTest_iff (htf : IsTorallyKummerFaithful k) (hJ : IsKummerFaithfulJac D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) (hη : η ∈ PU D) :
    IsNFKummerTest N hHL η ↔
      ∃ M : ℕ, 0 < M ∧ ∃ w : units D, η ^ M = kummerMapZHat D w ∧
        w ∉ Set.range (constUnit D) ∧ N.IsNFFunction ((w : (F D)ˣ) : F D) := by
  constructor
  · rintro ⟨M, hM, ⟨A₁, hk₁, ht₁, hA₁, hint₁, hfin₁, h₁⟩, ⟨A₂, hk₂, ht₂, -, hint₂, hfin₂, h₂⟩⟩
    letI := Decomposition.residueAlgebra A₁ hk₁
    letI := Decomposition.residueAlgebra A₂ hk₂
    haveI := hint₁
    haveI := hint₂
    haveI := hfin₁
    haveI := hfin₂
    obtain ⟨w, hw, hwc, hwNF⟩ := N.exists_eq_kummerMapZHat_of_restrictClosed htf hJ hkF hHL
      (η ^ M) (Subgroup.pow_mem _ hη M) A₁ hk₁
      (Decomposition.residue_algebraMap_residueAlgebra A₁ hk₁) ht₁ hA₁ A₂ hk₂
      (Decomposition.residue_algebraMap_residueAlgebra A₂ hk₂) ht₂ h₁ h₂
    exact ⟨M, hM, w, hw, hwc, hwNF⟩
  · rintro ⟨M, hM, w, hw, hwc, hwNF⟩
    obtain ⟨M', hM', h₁, h₂⟩ := N.exists_restrictClosed_of_isNF htf hHL w
      (transcendental_of_not_mem_range_constUnit hkF w hwc) hwNF
    refine ⟨M * M', Nat.mul_pos hM hM', ?_, ?_⟩
    · rw [pow_mul, hw, ← map_pow]
      exact h₁
    · rw [pow_mul, hw, ← map_pow]
      exact h₂

set_option maxHeartbeats 1000000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **[AbsTopIII] Prop 1.8 (ii)** (generic Galois model): if `U` has a nonconstant NF-rational
unit `f₀`, then the class of `c ∈ (k^×)^∧` (an element of `P_U ∩ H¹(G_k, Ẑ(1))`) is the Kummer
class of some `b ∈ k^×` with `IsNFConstant b` iff `κ_U(f)|_x = c|_{G_{k_x}}` for some
nonconstant NF-rational unit `f` and some NF-point `x ∈ U(k_x)`, `[k_x : k] < ∞`. -/
theorem exists_restrictClosed_eq_iff (htf : IsTorallyKummerFaithful k) (f₀ : units D)
    (hf₀ : Transcendental k ((f₀ : (F D)ˣ) : F D)) (hNF₀ : N.IsNFFunction ((f₀ : (F D)ˣ) : F D))
    (c : KummerCompletion k) :
    (∃ b : kˣ, IsNFConstant Ω (b : k) ∧ c = toKummerCompletion k b) ↔
      ∃ f : units D, Transcendental k ((f : (F D)ˣ) : F D) ∧
        N.IsNFFunction ((f : (F D)ˣ) : F D) ∧
        ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
          N.IsNFPoint A ∧
          letI := Decomposition.residueAlgebra A hk
          ∃ (_ : Algebra.IsIntegral k (ResidueField A))
            (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
              (Decomposition.residue_algebraMap_residueAlgebra A hk))),
            restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
                (kummerMapZHat D f) =
              restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
                (constMapZHat D c) := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact N.exists_restrictClosed_eq_of_isNFConstant htf hHL f₀ hf₀ hNF₀ b hb
  · rintro ⟨f, -, hfNF, A, hk, ht, hA, hint, hfin, h⟩
    letI := Decomposition.residueAlgebra A hk
    haveI := hint
    haveI := hfin
    obtain ⟨b, hb, hbNF, -⟩ := N.eq_toKummerCompletion_of_restrictClosed_eq htf hHL f hfNF A hk
      (Decomposition.residue_algebraMap_residueAlgebra A hk) ht hA c h
    exact ⟨b, hbNF, hb⟩

end Generic

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian CurvesJacobian.Cusp

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)] [IsAlgClosed (FFClosure X)]

variable {k hτ}

/-- **[AbsTopIII] Prop 1.8 (i) for an NF-curve `X` over a torally Kummer-faithful field `k`**
with `X(k) ≠ ∅` (Galois model `curveGaloisData k hτ`, `U` the open where `τ` is regular), given
`⋂_N N · J(L) = 0` for the Jacobian over **some** field extension `L / k` (curves-jacobian
`JacDivFree`; for a number field `k` one takes `L` a finite extension of `ℚ_p`): `η ∈ P_U` passes
the test of (i) iff some positive multiple of `η` is the Kummer class of a nonconstant
NF-rational unit of `U`. -/
theorem isNFKummerTest_iff_curve (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [Algebra k L] (hL : JacDivFree X σ hσ L)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ)) :
    IsNFKummerTest N rfl η ↔
      ∃ M : ℕ, 0 < M ∧ ∃ w : units (curveGaloisData k hτ),
        η ^ M = kummerMapZHat (curveGaloisData k hτ) w ∧
        w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) :=
  isNFKummerTest_iff htf (isKummerFaithfulJac_curveGaloisData_of_ext k hτ σ hσ L hL)
    (mem_range_of_isAlgebraic_F k hτ) η hη

/-- **[AbsTopIII] Prop 1.8 (i) for an NF-curve over a number field** `k` with `X(k) ≠ ∅`,
unconditionally: `⋂_N N · J(k) = 0` is curves-jacobian `jacDivFree_numberField`
([AbsTopIII] Rem 1.5.4 (i), MR5 Task B). -/
theorem isNFKummerTest_iff_curve_numberField [NumberField k] (N : NFModel (curveGaloisData k hτ))
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ)) :
    IsNFKummerTest N rfl η ↔
      ∃ M : ℕ, 0 < M ∧ ∃ w : units (curveGaloisData k hτ),
        η ^ M = kummerMapZHat (curveGaloisData k hτ) w ∧
        w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) :=
  isNFKummerTest_iff_curve N (NumberField.isTorallyKummerFaithful k) σ hσ k
    (jacDivFree_numberField X σ hσ) η hη

/-- **[AbsTopIII] Prop 1.8 (i) over a Kummer-faithful field** ([AbsTopIII] Def 1.5). -/
theorem isNFKummerTest_iff_curve_of_isKummerFaithful (N : NFModel (curveGaloisData k hτ))
    (hk : IsKummerFaithful k) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (hη : η ∈ PU (curveGaloisData k hτ)) :
    IsNFKummerTest N rfl η ↔
      ∃ M : ℕ, 0 < M ∧ ∃ w : units (curveGaloisData k hτ),
        η ^ M = kummerMapZHat (curveGaloisData k hτ) w ∧
        w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) :=
  isNFKummerTest_iff hk.isTorallyKummerFaithful
    (isKummerFaithfulJac_of_isKummerFaithful k hτ hk σ hσ) (mem_range_of_isAlgebraic_F k hτ) η hη

/-- **[AbsTopIII] Prop 1.8 (ii) for an NF-curve `X` over a torally Kummer-faithful field `k`**:
if `U` has a nonconstant NF-rational unit, the class of `c ∈ (k^×)^∧` is the Kummer class of an
`IsNFConstant` element of `kˣ` iff it passes the test of (ii). No Jacobian input is needed. -/
theorem exists_restrictClosed_eq_iff_curve (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (f₀ : units (curveGaloisData k hτ))
    (hf₀ : Transcendental k ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (hNF₀ : N.IsNFFunction ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (c : KummerCompletion k) :
    (∃ b : kˣ, IsNFConstant (FFClosure X) (b : k) ∧ c = toKummerCompletion k b) ↔
      ∃ f : units (curveGaloisData k hτ),
        Transcendental k ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
        ∃ (A : ValuationSubring (FFClosure X)) (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
          (ht : coordT τ ∈ A),
          N.IsNFPoint A ∧
          letI := Decomposition.residueAlgebra A hkA
          ∃ (_ : Algebra.IsIntegral k (ResidueField A))
            (_ : FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hkA
              (Decomposition.residue_algebraMap_residueAlgebra A hkA))),
            restrictClosed (curveGaloisData k hτ) A hkA
                (Decomposition.residue_algebraMap_residueAlgebra A hkA) rfl ht
                (kummerMapZHat (curveGaloisData k hτ) f) =
              restrictClosed (curveGaloisData k hτ) A hkA
                (Decomposition.residue_algebraMap_residueAlgebra A hkA) rfl ht
                (constMapZHat (curveGaloisData k hτ) c) :=
  exists_restrictClosed_eq_iff htf f₀ hf₀ hNF₀ c

end Curve

end Iut.Reconstruction.Thm19
