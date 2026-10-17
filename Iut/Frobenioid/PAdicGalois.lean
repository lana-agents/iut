/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisModel
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# `p`-adic Frobenioids over `B(G_K)⁰` ([FrdII], Example 1.1; IUT I, Example 3.3)

Let `K̄ = PadicAlgCl p` (an algebraic closure of `ℚ_p`, with the spectral norm), `K ⊆ K̄` an
intermediate field and `G_K = Gal(K̄/K)` with the Krull topology. For an open subgroup `H`,
the object `G_K/H` of `D = B(G_K)⁰` corresponds to `Spec(K̄^H)`, and `(K̄^H)^×` is the
`H`-invariants of the `G_K`-module `K̄^×`. With `ord = −log_p‖·‖` (so `ord(p) = 1`):

* **`PAdicGalois.Frob p K`** (`C^⊢_v` of IUT I, Example 3.3(i)): `Φ = ord(ℤ_p^▷) ≅ ℤ_{≥0}`
  (absolutely primitive), `B(G/H) = (K̄^H)^× ×_{ord} ℤ`, `Div_B = ord`;
* **`PAdicGalois.FrobPf p K`** (`C_v`): `Φ = ord(O^▷)^{pf} ≅ ℚ_{≥0}`,
  `B(G/H) = (K̄^H)^× ×_{ord} ℚ`;
* both are Frobenioids ([FrdI], Theorem 5.2(ii)); `O^▷` and `O^×` are the `H`-invariant elements
  of norm `≤ 1`, resp. `= 1` (`GaloisModel.orhdEquiv`, `ounitsEquiv`);
* **`PAdicGalois.thm34`**, `thm34Pf`: [FrdI], Theorem 3.4(ii), (iii) for them: every
  autoequivalence preserves the Frobenius structure. The input is that the roots of unity of `K̄`
  have open stabilizers and norm `1` (`PAdicGalois.torsion`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

namespace PAdicGalois

variable (p : ℕ) [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `G_K = Gal(K̄/K)`. -/
abbrev GK : Type := PadicAlgCl p ≃ₐ[K] PadicAlgCl p

/-- The `G_K`-module `K̄^×`, written additively. -/
abbrev Mul : Type := Additive (PadicAlgCl p)ˣ

noncomputable instance : DistribMulAction (GK p K) (Mul p) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := by change Additive.ofMul ((1 : GK p K) • x.toMul) = x; rw [one_smul]; rfl
  mul_smul σ τ x := by
    change Additive.ofMul ((σ * τ) • x.toMul) = Additive.ofMul (σ • (τ • x.toMul))
    rw [mul_smul]
  smul_zero σ := by
    change Additive.ofMul (σ • (1 : (PadicAlgCl p)ˣ)) = Additive.ofMul 1
    rw [smul_one]
  smul_add σ x y := by
    change Additive.ofMul (σ • (x.toMul * y.toMul)) =
      Additive.ofMul (σ • x.toMul * σ • y.toMul)
    rw [smul_mul']

lemma smul_toMul (σ : GK p K) (x : Mul p) :
    ((Additive.toMul (σ • x) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ (x.toMul : PadicAlgCl p) :=
  rfl

/-- `ord = −log_p ‖·‖ : K̄^× → ℝ`. -/
noncomputable def ord : Mul p →+ ℝ where
  toFun x := -Real.logb p ‖(x.toMul : PadicAlgCl p)‖
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, Units.val_mul, norm_mul]
    rw [Real.logb_mul (norm_ne_zero_iff.mpr x.toMul.ne_zero)
      (norm_ne_zero_iff.mpr y.toMul.ne_zero)]
    ring

/-- **The norm of `K̄` is `G_K`-invariant**, hence so is `ord`. -/
lemma norm_smul (σ : GK p K) (y : PadicAlgCl p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) y).symm

lemma ord_smul (σ : GK p K) (x : Mul p) : ord p (σ • x) = ord p x := by
  change -Real.logb p ‖σ (x.toMul : PadicAlgCl p)‖ = -Real.logb p ‖(x.toMul : PadicAlgCl p)‖
  rw [norm_smul]

/-- `ℤ ⊆ ℝ` (`ord(ℤ_p^▷)^gp`). -/
def gammaZ : AddSubgroup ℝ := AddSubgroup.zmultiples 1

/-- `ℚ ⊆ ℝ` (`ord(O^▷)^{pf,gp}`). -/
noncomputable def gammaQ : AddSubgroup ℝ := (algebraMap ℚ ℝ).toAddMonoidHom.range

/-- The `p`-adic Galois-model Frobenioid over `B(G_K)⁰` with divisor monoid `Γ ⊆ ℝ` (`Frob` for
`Γ = ℤ`, `FrobPf` for `Γ = ℚ`). -/
abbrev GFrob (Γ : AddSubgroup ℝ) : Type := GaloisModel (GK p K) (ord p) (ord_smul p K) Γ

/-- **The `p`-adic Frobenioid `C^⊢_v`** over `B(G_K)⁰` ([FrdII], Example 1.1(ii) with `Λ = ℤ`,
absolutely primitive; IUT I, Example 3.3(i)). -/
abbrev Frob : Type := GaloisModel (GK p K) (ord p) (ord_smul p K) (gammaZ)

/-- **The `p`-adic Frobenioid `C_v`** over `B(G_K)⁰` (`Φ = ord(O^▷)^{pf}`). -/
abbrev FrobPf : Type := GaloisModel (GK p K) (ord p) (ord_smul p K) (gammaQ)

theorem frob_isFrobenioid :
    IsFrobenioid (Model.toElem (constPhi (OrbitObj (GK p K)) gammaZ)
      (bGal (GK p K) (ord p) (ord_smul p K) gammaZ)
      (divGal (GK p K) (ord p) (ord_smul p K) gammaZ)) :=
  GaloisModel.isFrobenioid _ _ _ _

instance : Algebra.IsIntegral K (PadicAlgCl p) :=
  Algebra.IsIntegral.tower_top (R := ℚ_[p])

/-- **Roots of unity**: for every `n ≥ 2`, `K̄^×` has a nontrivial `n`-torsion element of norm `1`
with open stabilizer in `G_K`. -/
theorem torsion (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : Mul p, m ≠ 0 ∧ n • m = 0 ∧ ord p m = 0 ∧
      IsOpen (MulAction.stabilizer (GK p K) m : Set (GK p K)) := by
  haveI : NeZero (n : ℚ_[p]) := ⟨by exact_mod_cast (show n ≠ 0 by omega)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  let u : (PadicAlgCl p)ˣ := Units.mk0 ζ hζ0
  refine ⟨Additive.ofMul u, fun h => ?_, ?_, ?_, ?_⟩
  · have h1 : ζ = 1 := by
      have := congrArg (fun x : Mul p => ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)) h
      simpa [u] using this
    exact (hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by omega)) (by rw [pow_one]; exact h1)
  · change Additive.ofMul (u ^ n) = Additive.ofMul 1
    congr 1
    exact Units.ext (by simp [u, hζ.pow_eq_one])
  · change -Real.logb p ‖ζ‖ = 0
    have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
    have h2 : ‖ζ‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
    rw [h2, Real.logb_one, neg_zero]
  · have hst : (MulAction.stabilizer (GK p K) (Additive.ofMul u) : Set (GK p K)) =
        MulAction.stabilizer (GK p K) ζ := by
      ext σ
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        have := congrArg (fun x : Mul p => ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)) h
        simpa [smul_toMul, u] using this
      · intro h
        apply congrArg Additive.ofMul
        exact Units.ext (by simpa [u] using h)
    rw [hst]
    exact stabilizer_isOpen_of_isIntegral ζ

instance : IsGalois K (PadicAlgCl p) := by
  haveI : IsAlgClosure K (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  haveI : Normal K (PadicAlgCl p) := IsAlgClosure.normal K (PadicAlgCl p)
  exact IsGalois.mk

/-- **[FrdI], Theorem 3.4(ii), (iii) for `C^⊢_v` over `B(G_K)⁰`**. -/
theorem thm34 (F : Frob p K ⥤ Frob p K) [F.IsEquivalence] :
    PreservesFrobeniusStructure
      (Model.toElem (constPhi (OrbitObj (GK p K)) gammaZ)
        (bGal (GK p K) (ord p) (ord_smul p K) gammaZ)
        (divGal (GK p K) (ord p) (ord_smul p K) gammaZ))
      (Model.toElem (constPhi (OrbitObj (GK p K)) gammaZ)
        (bGal (GK p K) (ord p) (ord_smul p K) gammaZ)
        (divGal (GK p K) (ord p) (ord_smul p K) gammaZ)) F :=
  GaloisModel.thm34 (torsion p K) F

/-- **[FrdI], Theorem 3.4(ii), (iii) for `C_v` over `B(G_K)⁰`**. -/
theorem thm34Pf (F : FrobPf p K ⥤ FrobPf p K) [F.IsEquivalence] :
    PreservesFrobeniusStructure
      (Model.toElem (constPhi (OrbitObj (GK p K)) gammaQ)
        (bGal (GK p K) (ord p) (ord_smul p K) gammaQ)
        (divGal (GK p K) (ord p) (ord_smul p K) gammaQ))
      (Model.toElem (constPhi (OrbitObj (GK p K)) gammaQ)
        (bGal (GK p K) (ord p) (ord_smul p K) gammaQ)
        (divGal (GK p K) (ord p) (ord_smul p K) gammaQ)) F :=
  GaloisModel.thm34 (torsion p K) F

end PAdicGalois

end Frobenioid

end Iut
