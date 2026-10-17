/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.FNEquiv
import LocalClassFieldTheory.Brauer.DualityH1

/-!
# The reciprocity map ([FrdII], Remark 2.2.1, Definition 2.3)

[FrdII], Remark 2.2.1: "by the well-known duality theory of nonarchimedean [mixed-characteristic]
local fields [cf., e.g., [NSW], Chapter 7, Theorem 7.2.6], the cup product on group cohomology
determines an isomorphism `H¹(H, μ_N(A)) ≅ H^ab ⊗ H²(H, μ_N(A))` hence [in light of the condition
of Definition 2.2, (ii), (c)] an isomorphism [induced by the cup product on group cohomology]
`H¹(H_A, μ_N(A)) ≅ H_A^ab ⊗ F_N(A)` […]. Write `η_f ∈ H_A^ab ⊗ F_N(A)` for the image of `κ_f` via
this last isomorphism." Definition 2.3: "`f ↦ κ_f`, `f ↦ η_f` […] we shall refer to as the Kummer
and reciprocity maps".

For the `p`-adic Frobenioid `C^⊢(E)`, `X = (G_E/N, a)`, `H ⊆ G_E` open with `L = K̄^H`:

* `toL : H¹(H_A, μ_N(X)) → H¹(L, μ_N)` (along `Gal(K̄/L) ≅ H ↠ H_A` and `μ_N(X) → μ_N(K̄)`);
  **`toL_kummerClass`**: the Frobenioid Kummer class of `g` with `γ_g^N = x ∈ L^×` goes to
  `KummerTheory.kummer N L K̄ x`;
* `charL`: a character `χ ∈ H¹(H_A, ℤ/N) = Hom(H_A, ℤ/N)` as a character of `Gal(K̄/L)`;
* **`recip`**: `η(κ)`, as the element `χ ↦ χ ∪ κ ∈ F_N(X)` of
  `Hom(H¹(H_A, ℤ/N), F_N(X)) ≅ H_A^ab ⊗ F_N(X)`, the cup product taken over `L`
  (`Brauer.cupH1`) and `H²(L, μ_N) ≅ F_N(X)` (`fnEquivH2L`);
* **`fnEquiv_recip_kummerClass`** (reciprocity): for `κ = κ_f` the Kummer class of `f = g^N` with
  `γ_g^N = x ∈ L^×`, `η_f(χ) ∈ F_N(X) ≅ ℤ/N` is `χ(artin x)` (`PadicField.artinChar`), by
  `PadicField.pairingH1_kummer`.
-/

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (H : Subgroup (GK p E))
  (hH : IsOpen (H : Set (GK p E)))

local notation "K̄" => PadicAlgCl p

/-- `Gal(K̄/L) ≅ H ↠ H_A`. -/
noncomputable def galLA : (K̄ ≃ₐ[fixL H] K̄) →* subA N a H :=
  (subHom N a H).comp (galFixMulEquiv H hH).toMonoidHom

lemma continuous_galLA : Continuous (galLA N a H hH) :=
  (continuous_subHom N a H).comp (continuous_galFixMulEquiv H hH)

lemma uMu_smul_L (n : ℕ) (k : K̄ ≃ₐ[fixL H] K̄) (m : muX N a n) :
    uMu N a n (galLA N a H hH k • m) = k • uMu N a n m :=
  uMu_smul N a n (Brauer.resScalars (fixL H) k) m

/-- **`H¹(H_A, μ_N(X)) → H¹(L, μ_N)`**. -/
noncomputable def toL (n : ℕ) :
    ContH1 (subA N a H) (muX N a n) →* ContH1 (K̄ ≃ₐ[fixL H] K̄) (KummerTheory.Mu n K̄) :=
  ContH1.map (galLA N a H hH) (continuous_galLA N a H hH) (uMu N a n)
    continuous_of_discreteTopology (uMu_smul_L N a H hH n)

lemma ratFun_kfun_L (n : ℕ) (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ subA N a H, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (k : K̄ ≃ₐ[fixL H] K̄) :
    ratFun N a (KummerClass.kfun (Model.ouAut (XN N a)) (subA N a H) n g hg (galLA N a H hH k)) =
      k • ratFun N a g / ratFun N a g := by
  have e : (KummerClass.kfun (Model.ouAut (XN N a)) (subA N a H) n g hg (galLA N a H hH k) :
      Model.ouAut (XN N a)) = KummerClass.conjU (Model.ouAut (XN N a))
        (galHom N a (Brauer.resScalars (fixL H) k)) g / g := rfl
  apply Units.ext
  rw [e]
  change ((ratFunHom N a (KummerClass.conjU (Model.ouAut (XN N a))
    (galHom N a (Brauer.resScalars (fixL H) k)) g / g) : K̄ˣ) : K̄) = _
  rw [map_div, Units.val_div_eq_div_val, Units.val_div_eq_div_val]
  congr 1
  exact ratFun_conj N a (Brauer.resScalars (fixL H) k) g

/-- **The Frobenioid Kummer class of `g` over `H_A` is the Kummer class of `γ_g^N` over `L`.** -/
theorem toL_kummerClass (n : ℕ) [NeZero (n : fixL H)] (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ subA N a H, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (x : (fixL H)ˣ)
    (hx : ratFun N a g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) x) :
    toL N a H hH n (Model.frobKummerClass (XN N a) (subA N a H) n g hg) =
      KummerTheory.kummer n (fixL H) K̄ x := by
  have hγ : ∀ σ : K̄ ≃ₐ[fixL H] K̄, σ • ratFun N a g ^ n = ratFun N a g ^ n := fun σ => by
    rw [hx]
    exact Units.ext (σ.commutes (x : fixL H))
  refine (KummerClass.map_kummerClass_eq_mk (g := g) (hg := hg)
    (c := KummerTheory.kummerCocycle (ratFun N a g) hγ)
    (hc := fun k => KummerTheory.Mu.ext (ratFun_kfun_L N a H hH n g hg k)) ..).trans
    (KummerTheory.kummer_eq x _ hx).symm

/-- A character `χ : H_A → ℤ/N` (`H¹(H_A, ℤ/N)`) as a character of `Gal(K̄/L)`. -/
noncomputable def charL (n : ℕ) (χ : subA N a H →* Multiplicative (ZMod n)) :
    Brauer.LocChar (fixL H) K̄ n :=
  ⟨χ.comp (galLA N a H hH),
    (IsLocallyConstant.of_discrete χ).comp_continuous (continuous_galLA N a H hH)⟩

/-- **The reciprocity map** `κ ↦ η(κ)` ([FrdII], Remark 2.2.1), with
`η(κ) ∈ H_A^ab ⊗ F_N(X) ≅ Hom(H¹(H_A, ℤ/N), F_N(X))` given by `χ ↦ χ ∪ κ` (cup product over `L`,
`H²(L, μ_N) ≅ F_N(X)`). -/
noncomputable def recip (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)
    (κ : ContH1 (subA N a H) (muX N a n)) (χ : subA N a H →* Multiplicative (ZMod n)) :
    FN N a H n :=
  (fnEquivH2L N a H hH n hs).symm (Brauer.cupH1 n (charL N a H hH n χ) (toL N a H hH n κ))

/-- `F_N(X) ≅ ℤ/N` turns `η(κ)(χ)` into LCFT's pairing `⟨χ, κ⟩`. -/
theorem fnEquiv_recip [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n] (hs : IsSaturated N a H n)
    (κ : ContH1 (subA N a H) (muX N a n)) (χ : subA N a H →* Multiplicative (ZMod n)) :
    haveI := finiteDimensional_fixL_padic H hH
    fnEquiv N a H hH n hs (recip N a H hH n hs κ χ) =
      Multiplicative.ofAdd (PadicField.pairingH1 (p := p) n (charL N a H hH n χ)
        (toL N a H hH n κ)) := by
  simp only [fnEquiv, recip, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

/-- **Reciprocity** ([FrdII], Definition 2.3): for `f = g^N` with `γ_g^N = x ∈ L^×`, the reciprocity
class `η_f`, paired with `χ ∈ Hom(H_A, ℤ/N)` and read in `F_N(X) ≅ ℤ/N`, is `χ(artin x)`. -/
theorem fnEquiv_recip_kummerClass [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ subA N a H, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (x : (fixL H)ˣ)
    (hx : ratFun N a g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) x)
    (χ : subA N a H →* Multiplicative (ZMod n)) :
    haveI := finiteDimensional_fixL_padic H hH
    fnEquiv N a H hH n hs
        (recip N a H hH n hs (Model.frobKummerClass (XN N a) (subA N a H) n g hg) χ) =
      Multiplicative.ofAdd (PadicField.artinChar (p := p) n (charL N a H hH n χ) x) := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI : NeZero (n : fixL H) := ⟨by exact_mod_cast NeZero.ne n⟩
  rw [fnEquiv_recip, toL_kummerClass N a H hH n g hg x hx, PadicField.pairingH1_kummer]

end PAdicGalois

end Frobenioid

end Iut
