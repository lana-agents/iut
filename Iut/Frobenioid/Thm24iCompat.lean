/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24iiPfMain
import Iut.Frobenioid.OrhdField
import Iut.Frobenioid.KummerEquivariance

/-!
# [FrdII], Theorem 2.4(i) for `C_v`: Kummer maps on all of `O^▷` and `G_A/H_A`-equivariance

[FrdII], Theorem 2.4(i): the isomorphisms `O^□(A₁)^{H₁} ≅ O^□(A₂)^{H₂}`,
`H¹((H₁)_{A₁}, μ_N(A₁)) ≅ H¹((H₂)_{A₂}, μ_N(A₂))`, … induced by `Ψ` "are compatible with the
respective Kummer […] maps `O^□(A_i)^{H_i} → H¹((H_i)_{A_i}, μ_N(A_i))` […] as well as with the
various natural actions of `(G₁)_{A₁}/(H₁)_{A₁}`, `(G₂)_{A₂}/(H₂)_{A₂}`". For `C_v = FrobPf`
(fieldwise saturated, so `O^□ = O^▷`, Kummer map defined on all of `O^▷(A)^H` by Remark 2.2.1)
and `X = (G_E/N, a)` `(n, H)`-saturated with `N ⊆ H`, in field-theoretic form
(`O^▷(X)^{H_A} ≅ O^▷_{K̄^H}` is `orhdFixEquiv`, `H¹(H_A, μ_n(X)) ≅ H¹(K̄^H, μ_n)` is `toL`):

* **`kummer_psiFun`**: `Φ₁(κ(x)) = κ(Ψ x)` for every `x ∈ O^▷_{K̄^H}` (`Ψ x = orhdPsiEquiv x`,
  `Φ₁ = (galPairEquiv, β_Ψ)_*`): the Kummer maps on all of `O^▷` are compatible with `Ψ`
  (`h1PairMap_kummer_unif` was the case of a uniformiser);
* **`psiFun_galois`**: `Ψ(σ x) = α(σ) Ψ(x)` for `σ ∈ G_E` (the `G_A`-equivariance of
  `O^▷_{K̄^H} ≅ O^▷_{K̄^{α(H)}}`);
* **`orhdFixEquiv_conj`**: `orhdFixEquiv` intertwines the conjugation action of `galHom σ` on
  `O^▷(X)^{H_A}` with the Galois action of `σ` on `K̄^H`.

The group-theoretic `G_A/H_A`-statements for `H¹(H_A, μ_n)`, `H²(H_A, μ_n)` and the Kummer map
(`KummerClass.kummerClass_conjU`, `conjH1_of_mem`, `Saturation.h1Equiv_conjH1`,
`h2Equiv_conjH2`) are in `KummerEquivariance.lean`; they apply to `Ψ` with
`φ = Model.autEquiv F X` (as in `thm24Pf`).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaQ) (divGal (GK p E) (ord p) (ord_smul p E) gammaQ)

variable {F : FrobPf p E ⥤ FrobPf p E'} [F.IsEquivalence] {α : GK p E ≃ₜ* GK p E'}
  {τ : GK p E'} {N : OpenNormalSubgroup (GK p E)} {a : gammaQ}

/-- `x ∈ O^▷_L` and its image `Ψ x` are related by `B` (`RelB`). -/
lemma relB_psiFun (H : Subgroup (GK p E)) (hNH : N.toSubgroup ≤ H) (hτ : OrhdCompat F α τ N a)
    [FiniteDimensional ℚ_[p] (fixL H)]
    [FiniteDimensional ℚ_[p] (fixL (H.map (α : GK p E →* GK p E')))] (x : OrhdL H) :
    RelB (F := F) (α := α) (τ := τ) (N := N) (a := a) H x.1 (psiFun H hNH hτ x).1 :=
  ⟨endL H hNH x, endL_mem H hNH x, rfE_endL H hNH x, (coe_psiFun H hNH hτ x).symm⟩

/-- **Kummer compatibility of `O^▷_{K̄^H} ≅ O^▷_{K̄^{α(H)}}` on all of `O^▷`** ([FrdII],
Theorem 2.4(i), Kummer maps, `C_v`): `Φ₁(κ(x)) = κ(Ψ x)`. -/
theorem kummer_psiFun (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))
    (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) : Set (GK p E')))
    (hNH : N.toSubgroup ≤ H) (hτ : OrhdCompat F α τ N a) (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) [FiniteDimensional ℚ_[p] (fixL H)]
    [FiniteDimensional ℚ_[p] (fixL (H.map (α : GK p E →* GK p E')))] (x : OrhdL H) :
    haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
    haveI := hasKummerRoots (K := fixL (H.map (α : GK p E →* GK p E'))) (Ω := K̄) n
    PairCompat.h1PairMap n (galPairEquiv α H hH hH') (betaPsi F τ N a H n hs)
        (betaPsi_smul F α τ N a (ratFunTw_of_orhdCompat hτ) H hH hH' n hs)
        (KummerTheory.kummer n (fixL H) K̄ x.1) =
      KummerTheory.kummer n (fixL (H.map (α : GK p E →* GK p E'))) K̄
        (psiFun H hNH hτ x).1 :=
  h1PairMap_kummer_unif H hH hH' hNH hτ n hs x.1 _ (relB_psiFun H hNH hτ x)

/-- **`G_E`-equivariance of `O^▷_{K̄^H} ≅ O^▷_{K̄^{α(H)}}`**: if `y = σ x` then
`Ψ y = α(σ) Ψ x` ([FrdII], Theorem 2.4(i): compatibility with the actions of `G_A/H_A`). -/
theorem psiFun_galois (H : Subgroup (GK p E)) (hNH : N.toSubgroup ≤ H)
    (hτ : OrhdCompat F α τ N a) [FiniteDimensional ℚ_[p] (fixL H)]
    [FiniteDimensional ℚ_[p] (fixL (H.map (α : GK p E →* GK p E')))] (σ : GK p E)
    (x y : OrhdL H) (hxy : ιL (fixL H) y.1 = σ • ιL (fixL H) x.1) :
    ιL _ (psiFun H hNH hτ y).1 = α σ • ιL _ (psiFun H hNH hτ x).1 := by
  have he : endL (a := a) H hNH y = Model.conj (galIso N a σ) (endL (a := a) H hNH x) :=
    rfE_injective_orhd (endL_mem H hNH y) (Model.conj_mem_orhd _ (endL_mem H hNH x)) (by
      rw [rfE_conj_galHom N a σ (endL_mem H hNH x), rfE_endL, rfE_endL, hxy])
  rw [coe_psiFun, coe_psiFun, he, Bmap_conj hτ σ (endL_mem H hNH x)]

/-- **`orhdFixEquiv` is `G_E`-equivariant**: the conjugation action of `galHom σ` on
`O^▷(X)^{H_A}` corresponds to the Galois action of `σ` on `K̄^H`. -/
theorem orhdFixEquiv_conj (H : Subgroup (GK p E)) (hNH : N.toSubgroup ≤ H)
    [FiniteDimensional ℚ_[p] (fixL H)] (σ : GK p E) (e e' : OrhdFix N a H)
    (he : e'.1 = Model.conj (galIso N a σ) e.1) :
    ιL (fixL H) (orhdFixEquiv hNH e').1 = σ • ιL (fixL H) (orhdFixEquiv hNH e).1 := by
  rw [coe_orhdFixEquiv, coe_orhdFixEquiv, he, rfE_conj_galHom N a σ e.2.1]

end PAdicGalois

end Frobenioid

end Iut
