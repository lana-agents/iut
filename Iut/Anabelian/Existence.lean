/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Geometry
import Iut.Anabelian.Torsion
import Iut.Anabelian.Linear
import Iut.Anabelian.LocalInputs
import Iut.Concrete.Existence

/-!
# Existence of the anabelian part of initial Θ-data for the model (taxis #1469)

`Iut.Anabelian.anabelianExistence` proves `Iut.AnabelianExistence` for the linear-algebraic
model of the anabelian interface (`Iut.Anabelian.modelAG`, `Iut.Anabelian.modelTG`): for
admissible prime data `P` over global data whose once-punctured curve admits the core
`C_F = X_F/{±1}`, the orbicurve data `C̲_K`, `X̲_K`, `ε` (IUT I, Definition 3.1(d), (f))
and the local theta data `V` (Definition 3.1(e), (f)) exist.

## The construction (IUT IV, proof of Corollary 2.2, (P7))

Let `K = F(E[ℓ])` and identify `E(K)[ℓ] ≅ 𝔽_ℓ²` through the chosen basis
(`Iut.AdmissiblePrimeData.basisK`). Put `M = ⟨e₁⟩` and `q = e₂ mod M`; then
`C̲_K = (E_K, ℓ, M, ±)`, `X̲_K = (E_K, ℓ, M, −)`, `ε = cusp of q`. The covering diagram
`X̲_K → X_K`, `X̲_K → C̲_K`, `X_K → C_K`, `C̲_K → C_K` is the `±`-quotient square of the
model. `C̲_K` has core `C_K` because `X_F` has core `C_F` (residual stability of cores).

For the local data, at a place `v ∈ V_mod^bad` one needs a place `w` of `K` over `v` at
which the **graph line** (the ℓ-torsion of the kernel of reduction, `μ_ℓ` under the Tate
uniformization) is `M` and the **canonical generators** `q^{±1/ℓ}` of the graph quotient
are `±e₂ mod M`. Starting from any place `w₀` over `v`, the graph line `L₀` at `w₀` and a
canonical generator `g₀` give a line and a vector of `𝔽_ℓ²`; since the image of the
mod-ℓ representation contains `SL₂(𝔽_ℓ)` (Definition 3.1(c), (P6)), some `σ ∈ Gal(K/F)`
moves `(L₀, g₀)` to `(M, ±e₂)` (`Iut.Anabelian.exists_sl2`), and `w = σ·w₀` works by the
Galois equivariance of the graph line and of the canonical generators. This is the
mechanism behind "the crucial existence of data `V` and `ε` … follows … as a consequence
of the fact that the Galois action on ℓ-torsion points contains `SL₂(𝔽_ℓ)`" (IUT IV,
proof of Corollary 2.2).

## The reduction-theoretic inputs

`Iut.Anabelian.LocalInputs P` collects the standard facts about places of `K` and about
the reduction of `E` at the places over `V_mod^bad` that the construction consumes:
places of `K` over places of `F_mod`, the action of `Gal(K/F)` on the places of `K`,
extensions of places to `F̄` (decomposition groups), and — at the places over
`V_mod^bad` — split multiplicative reduction, the rationality of the local ℓ-torsion, the
graph line as a subgroup of order `ℓ` (from `ℓ ∤ ord(q)`, Definition 3.1(c)), the
characterization of the canonical generators, and the Galois equivariance of both. These
are the targets of the elliptic-reduction and Tate-curve projects (taxis #5, #13).
-/

namespace Iut.AdmissiblePrimeData

universe u

open WeierstrassCurve NumberField Iut Iut.Anabelian OrbicurveDataSection
open scoped Classical

noncomputable section

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : Iut.AdmissiblePrimeData F E Fbar VBad)
variable [NumberField ↥P.torsionField]

attribute [local instance 1100] instDecidableEqK

/-- `ℓ` is prime. -/
local instance instFactPrime : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

/-! ## The chosen line and cusp -/

/-- The first basis vector `e₁ ∈ E(K)[ℓ]`. -/
def e₁ : ↥P.TK := P.basisK.symm (Pi.single 0 1)

/-- The second basis vector `e₂ ∈ E(K)[ℓ]`. -/
def e₂ : ↥P.TK := P.basisK.symm (Pi.single 1 1)

/-- **The line `M = ⟨e₁⟩ ⊆ E(K)[ℓ]`** defining `C̲_K`. -/
def M : AddSubgroup P.EK.toAffine.Point := AddSubgroup.zmultiples (P.e₁ : P.EK.toAffine.Point)

/-- The line `⟨(1, 0)⟩ ⊆ 𝔽_ℓ²`. -/
def M₀ : AddSubgroup (Fin 2 → ZMod P.ℓ) := AddSubgroup.zmultiples (Pi.single 0 1)

lemma fact_prime : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

/-- The image in `𝔽_ℓ²` of a subgroup of `E(K)[ℓ]`. -/
def toV (L : AddSubgroup P.EK.toAffine.Point) : AddSubgroup (Fin 2 → ZMod P.ℓ) :=
  (L.addSubgroupOf P.TK).map P.basisK.toAddMonoidHom

lemma mem_toV_iff (L : AddSubgroup P.EK.toAffine.Point) (R : ↥P.TK) :
    P.basisK R ∈ P.toV L ↔ (R : P.EK.toAffine.Point) ∈ L := by
  unfold toV
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, hSR⟩
    have : S = R := P.basisK.injective hSR
    subst this
    exact (AddSubgroup.mem_addSubgroupOf).mp hS
  · intro h
    exact ⟨R, (AddSubgroup.mem_addSubgroupOf).mpr h, rfl⟩

lemma toV_injective {L L' : AddSubgroup P.EK.toAffine.Point} (hL : L ≤ P.TK) (hL' : L' ≤ P.TK)
    (h : P.toV L = P.toV L') : L = L' := by
  ext R
  constructor
  · intro hR
    have hRT : R ∈ P.TK := hL hR
    have := (P.mem_toV_iff L ⟨R, hRT⟩).mpr hR
    rw [h] at this
    exact (P.mem_toV_iff L' ⟨R, hRT⟩).mp this
  · intro hR
    have hRT : R ∈ P.TK := hL' hR
    have := (P.mem_toV_iff L' ⟨R, hRT⟩).mpr hR
    rw [← h] at this
    exact (P.mem_toV_iff L ⟨R, hRT⟩).mp this

lemma card_toV {L : AddSubgroup P.EK.toAffine.Point} (hL : L ≤ P.TK) :
    Nat.card (P.toV L) = Nat.card L := by
  unfold toV
  rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ P.basisK.injective).symm.toEquiv,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hL).toEquiv]

lemma toV_map_galK (σ : Fbar ≃ₐ[F] Fbar) {L : AddSubgroup P.EK.toAffine.Point}
    (hL : L ≤ P.TK) :
    P.toV (L.map (P.galK (P.restrictK σ))) =
      (P.toV L).map (mulVecHom (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ))) := by
  ext v
  constructor
  · intro hv
    unfold toV at hv
    rw [AddSubgroup.mem_map] at hv
    obtain ⟨S, hS, rfl⟩ := hv
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map] at hS
    obtain ⟨R, hR, hRS⟩ := hS
    have hRT : R ∈ P.TK := hL hR
    have hS' : S = P.galTK (P.restrictK σ) ⟨R, hRT⟩ := Subtype.ext hRS.symm
    rw [AddSubgroup.mem_map]
    refine ⟨P.basisK ⟨R, hRT⟩, (P.mem_toV_iff L ⟨R, hRT⟩).mpr hR, ?_⟩
    rw [mulVecHom_apply, ← P.basisK_galTK, hS']
    rfl
  · intro hv
    rw [AddSubgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    unfold toV at hu
    rw [AddSubgroup.mem_map] at hu
    obtain ⟨R, hR, rfl⟩ := hu
    rw [AddSubgroup.mem_addSubgroupOf] at hR
    rw [mulVecHom_apply]
    change (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec (P.basisK R) ∈ _
    rw [← P.basisK_galTK]
    exact (P.mem_toV_iff _ _).mpr (AddSubgroup.mem_map_of_mem _ hR)

lemma e₁_ne_zero : (P.e₁ : P.EK.toAffine.Point) ≠ 0 := by
  haveI := P.fact_prime
  intro h
  have h1 : P.e₁ = 0 := Subtype.ext h
  have := congrArg P.basisK h1
  simp only [e₁, AddEquiv.apply_symm_apply, map_zero] at this
  have := congrFun this 0
  simp at this

lemma e₁_mem_TK : (P.e₁ : P.EK.toAffine.Point) ∈ P.TK := P.e₁.2

lemma M_le_TK : P.M ≤ P.TK := (AddSubgroup.zmultiples_le).mpr P.e₁_mem_TK

lemma card_M : Nat.card P.M = P.ℓ := by
  haveI := P.fact_prime
  unfold M
  rw [Nat.card_zmultiples]
  refine addOrderOf_eq_prime ?_ P.e₁_ne_zero
  exact (AddSubgroup.torsionBy.nsmul_iff).mp P.e₁_mem_TK

lemma toV_M : P.toV P.M = P.M₀ := by
  ext v
  unfold toV M M₀
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hS
    obtain ⟨n, hn⟩ := hS
    have : S = n • P.e₁ := Subtype.ext hn.symm
    rw [this, map_zsmul]
    simp only [e₁, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
  · intro hv
    rw [AddSubgroup.mem_zmultiples_iff] at hv
    obtain ⟨n, rfl⟩ := hv
    refine ⟨n • P.e₁, ?_, ?_⟩
    · rw [AddSubgroup.mem_addSubgroupOf]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
    · simp only [map_zsmul, e₁, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]

lemma card_M₀ : Nat.card P.M₀ = P.ℓ := by
  rw [← P.toV_M, P.card_toV P.M_le_TK, P.card_M]

lemma e₂_not_mem_M : (P.e₂ : P.EK.toAffine.Point) ∉ P.M := by
  haveI := P.fact_prime
  intro h
  have := (P.mem_toV_iff P.M P.e₂).mpr h
  rw [P.toV_M] at this
  simp only [e₂, AddEquiv.apply_symm_apply, M₀] at this
  rw [AddSubgroup.mem_zmultiples_iff] at this
  obtain ⟨n, hn⟩ := this
  have := congrFun hn 1
  simp at this

lemma single_one_not_mem_M₀ : (Pi.single 1 1 : Fin 2 → ZMod P.ℓ) ∉ P.M₀ := by
  have := P.e₂_not_mem_M
  rwa [← P.mem_toV_iff P.M P.e₂, P.toV_M, e₂, AddEquiv.apply_symm_apply] at this

/-! ## The orbicurve data -/

/-- **`C̲_K = (E_K, ℓ, M, ±)`.** -/
def CKu : Orbicurve ↥P.torsionField := ⟨P.EK, P.ℓ, P.M, true⟩

/-- **`X̲_K = (E_K, ℓ, M, −)`.** -/
def XKu : Orbicurve ↥P.torsionField := ⟨P.EK, P.ℓ, P.M, false⟩

lemma nsmul_mem_of_mem_M (R : P.EK.toAffine.Point) (hR : R ∈ P.M) : P.ℓ • R = 0 :=
  (AddSubgroup.torsionBy.nsmul_iff).mp (P.M_le_TK hR)

lemma nsmul_mem_of_mem_M' (R : P.EK.toAffine.Point) (hR : R ∈ P.M)
    (S : AddSubgroup P.EK.toAffine.Point) : P.ℓ • R ∈ S := by
  rw [P.nsmul_mem_of_mem_M R hR]
  exact zero_mem _

/-- `X_K` in the model. -/
abbrev XK' : Orbicurve ↥P.torsionField :=
  (Orbicurve.oncePunctured E).baseChange (algebraMap F ↥P.torsionField)

/-- `C_K` in the model. -/
abbrev CK' : Orbicurve ↥P.torsionField :=
  (Orbicurve.pmQuotient (Orbicurve.oncePunctured E)).baseChange (algebraMap F ↥P.torsionField)

/-- `X̲_K → X_K`. -/
def coverXKu_XK : Orbicurve.Cover P.XKu P.XK' where
  E_eq := rfl
  n := P.ℓ
  mul := mul_one _
  M_le R hR := P.nsmul_mem_of_mem_M' R hR _
  pm_le h := absurd h Bool.false_ne_true

/-- `X̲_K → C̲_K`. -/
def coverXKu_CKu : Orbicurve.Cover P.XKu P.CKu where
  E_eq := rfl
  n := 1
  mul := one_mul _
  M_le R hR := by
    change (1 : ℕ) • R ∈ P.M
    rw [one_smul]
    exact hR
  pm_le _ := rfl

/-- `X_K → C_K`. -/
def coverXK_CK : Orbicurve.Cover P.XK' P.CK' where
  E_eq := rfl
  n := 1
  mul := one_mul _
  M_le R hR := by
    change (1 : ℕ) • R ∈ P.CK'.M
    rw [one_smul]
    exact hR
  pm_le _ := rfl

/-- `C̲_K → C_K`. -/
def coverCKu_CK : Orbicurve.Cover P.CKu P.CK' where
  E_eq := rfl
  n := P.ℓ
  mul := mul_one _
  M_le R hR := P.nsmul_mem_of_mem_M' R hR _
  pm_le _ := rfl

variable (Pi1 : EtalePi1Theory.{u})

/-- The second coordinate `E(K)[ℓ] → 𝔽_ℓ`, with kernel `M`. -/
def coord₂ : ↥P.TK →+ ZMod P.ℓ :=
  (Pi.evalAddMonoidHom (fun _ => ZMod P.ℓ) 1).comp P.basisK.toAddMonoidHom

lemma coord₂_ker : P.coord₂.ker = P.M.addSubgroupOf P.TK := by
  ext R
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, ← P.mem_toV_iff, P.toV_M]
  unfold M₀ coord₂
  rw [AddSubgroup.mem_zmultiples_iff]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
    AddEquiv.coe_toAddMonoidHom]
  constructor
  · intro h
    refine ⟨(P.basisK R 0).cast, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp [h]
  · rintro ⟨n, hn⟩
    have := congrFun hn 1
    simpa using this.symm

lemma coord₂_surjective : Function.Surjective P.coord₂ := by
  intro a
  refine ⟨P.basisK.symm (Pi.single 1 a), ?_⟩
  simp [coord₂]

/-- **The identification `Q = E(K)[ℓ]/M ≃ ℤ/ℓℤ`.** -/
def QIso : P.CKu.Q ≃ ZMod P.ℓ :=
  ((QuotientAddGroup.quotientAddEquivOfEq P.coord₂_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective P.coord₂ P.coord₂_surjective)).toEquiv

lemma QIso_toQ (R : ↥P.TK) : P.QIso (P.CKu.toQ R) = P.coord₂ R := rfl

/-- **The element `q = e₂ mod M`.** -/
def q : P.CKu.Q := P.CKu.toQ P.e₂

lemma QIso_q : P.QIso P.q = 1 := by
  rw [q, QIso_toQ]
  simp [coord₂, e₂]

/-- **The orbicurve data** `C̲_K`, `X̲_K`, `ε` of IUT I, Definition 3.1(d), (f), for the
model. -/
def orbicurveData (hcore : Pi1.HasCore (Orbicurve.oncePunctured E)
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E))) :
    OrbicurveData (modelAG Pi1) F E Fbar VBad P where
  CKu := P.CKu
  CKu_type := ⟨P.ℓ_prime, rfl, rfl, P.M_le_TK, P.card_M, P.card_TK⟩
  CKu_core := by
    have h1 := Pi1.hasCore_baseChange (algebraMap F ↥P.torsionField) hcore
    have h2 := (Pi1.hasCore_iff_of_cover P.coverXK_CK).mp h1
    exact (Pi1.hasCore_iff_of_cover P.coverCKu_CK).mpr h2
  XKu := P.XKu
  XKu_type := ⟨P.ℓ_prime, rfl, rfl, P.M_le_TK, P.card_M, P.card_TK⟩
  XKu_to_XK := P.coverXKu_XK
  XKu_to_CKu := P.coverXKu_CKu
  XK_to_CK := P.coverXK_CK
  CKu_to_CK := P.coverCKu_CK
  diagram_cartesian := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  QIso := P.QIso
  q := P.q
  q_ne_zero := by
    show P.QIso P.q ≠ 0
    rw [P.QIso_q]
    exact one_ne_zero
  epsilon := P.CKu.cuspOf P.q
  epsilon_spec := rfl

/-- `F̄` is algebraic over `K`. -/
instance : Algebra.IsIntegral ↥P.torsionField Fbar :=
  have : Algebra.IsAlgebraic F Fbar := IsAlgClosure.isAlgebraic
  (Algebra.IsAlgebraic.tower_top (K := F) ↥P.torsionField).isIntegral

/-! ## The choice of places -/

variable (TF : TateFamily E P.torsionField P.ℓ VBad)

lemma map_map_symm (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField)
    (R : (Affine.baseChange E ↥P.torsionField).Point) :
    Affine.Point.map (W' := E) (S := F) (σ : ↥P.torsionField →ₐ[F] ↥P.torsionField)
      (Affine.Point.map (W' := E) (S := F) (σ.symm : ↥P.torsionField →ₐ[F] ↥P.torsionField) R) =
      R := by
  rw [Affine.Point.map_map]
  have : (σ : ↥P.torsionField →ₐ[F] ↥P.torsionField).comp
      (σ.symm : ↥P.torsionField →ₐ[F] ↥P.torsionField) = AlgHom.id F ↥P.torsionField := by
    ext x; simp
  rw [this]
  exact Affine.Point.map_id R

lemma galK_galK_symm (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) (R : P.EK.toAffine.Point) :
    P.galK σ (P.galK σ.symm R) = R :=
  P.map_map_symm σ R

lemma galK_eq (σ : ↥P.torsionField ≃ₐ[F] ↥P.torsionField) :
    Iut.galK E P.torsionField σ = P.galK σ := rfl

/-- **The good place over `v ∈ V_mod^bad`**: a place at which the graph line is `M` and the
canonical generators are `±e₂ (mod M)`. -/
theorem exists_good_place {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    ∃ w : FinitePlace ↥P.torsionField, ∃ hwv : FinitePlace.LiesOver w v,
      TF.graphLineAt w ⟨v, hv, hwv⟩ = P.M ∧
      ∀ R, TF.IsCanonicalAt w ⟨v, hv, hwv⟩ R → (R - P.e₂ ∈ P.M ∨ R + P.e₂ ∈ P.M) := by
  haveI := P.fact_prime
  obtain ⟨w₀, hw₀⟩ := FinitePlace.exists_liesOver (K := ↥P.torsionField) v
  have hb₀ : IsBadPlace E P.torsionField VBad w₀ := ⟨v, hv, hw₀⟩
  have hL₀le := TF.graphLineAt_le_TK P hb₀
  have hL₀card := TF.card_graphLineAt P hb₀
  obtain ⟨g₀, hg₀T, hg₀L, hg₀⟩ := TF.exists_canonical P hb₀
  have hcardV : Nat.card (P.toV (TF.graphLineAt w₀ hb₀)) = P.ℓ := by
    rw [P.card_toV hL₀le, hL₀card]
  have hgV : P.basisK ⟨g₀, hg₀T⟩ ∉ P.toV (TF.graphLineAt w₀ hb₀) := fun h =>
    hg₀L ((P.mem_toV_iff _ _).mp h)
  obtain ⟨A, hAL, hAg⟩ := exists_sl2 (P.toV (TF.graphLineAt w₀ hb₀)) P.M₀ hcardV P.card_M₀ hgV
    P.single_one_not_mem_M₀
  obtain ⟨τ, hτ⟩ := P.sl_le_range A
  set σ := P.restrictK τ with hσ
  have hA : (P.rep τ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)) = A := by
    rw [hτ]; rfl
  have hwv : FinitePlace.LiesOver (galPlace σ w₀) v := galPlace_liesOver (fun _ => rfl) σ hw₀
  have hb : IsBadPlace E P.torsionField VBad (galPlace σ w₀) := ⟨v, hv, hwv⟩
  have hgl : TF.graphLineAt (galPlace σ w₀) hb = (TF.graphLineAt w₀ hb₀).map (P.galK σ) :=
    TF.graphLine_galPlace w₀ hb₀ σ
  have hLM : (TF.graphLineAt w₀ hb₀).map (P.galK σ) = P.M := by
    apply P.toV_injective (by
      rintro _ ⟨R, hR, rfl⟩
      exact P.galK_mem_TK σ (hL₀le hR)) P.M_le_TK
    rw [hσ, P.toV_map_galK τ hL₀le, hA, hAL, P.toV_M]
  refine ⟨galPlace σ w₀, hwv, hgl.trans hLM, ?_⟩
  intro R hR
  have hR₀ : TF.IsCanonicalAt w₀ hb₀ (P.galK σ.symm R) := by
    have h := TF.isCanonical_galPlace w₀ hb₀ σ (P.galK σ.symm R)
    rw [galK_eq, P.galK_galK_symm] at h
    exact h.mp hR
  -- `σ g₀ ≡ e₂ (mod M)`
  have hσg : P.galK σ g₀ - P.e₂ ∈ P.M := by
    have h1 : P.basisK (P.galTK σ ⟨g₀, hg₀T⟩ - P.e₂) ∈ P.M₀ := by
      rw [map_sub, hσ, P.basisK_galTK, hA, e₂, AddEquiv.apply_symm_apply]
      exact hAg
    rw [← P.toV_M] at h1
    have h2 := (P.mem_toV_iff P.M _).mp h1
    simpa using h2
  rcases (hg₀ _).mp hR₀ with h | h
  · left
    have := AddSubgroup.mem_map_of_mem (P.galK σ) h
    rw [map_sub, P.galK_galK_symm, hLM] at this
    have := P.M.add_mem this hσg
    rwa [sub_add_sub_cancel] at this
  · right
    have := AddSubgroup.mem_map_of_mem (P.galK σ) h
    rw [map_add, P.galK_galK_symm, hLM] at this
    have h3 := P.M.sub_mem this hσg
    have h4 : R + P.galK σ g₀ - (P.galK σ g₀ - P.e₂) = R + P.e₂ := by abel
    rwa [h4] at h3

/-- The chosen finite place of `K` over a finite place of `F_mod`. -/
def sectFin (v : FinitePlace ↥(fieldOfModuli F E)) : FinitePlace ↥P.torsionField :=
  if hv : v ∈ VBad then (P.exists_good_place TF hv).choose
  else (FinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose

lemma sectFin_liesOver (v : FinitePlace ↥(fieldOfModuli F E)) :
    FinitePlace.LiesOver (P.sectFin TF v) v := by
  unfold sectFin
  split_ifs with hv
  · exact (P.exists_good_place TF hv).choose_spec.choose
  · exact (FinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose_spec

lemma sectFin_isBad {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    IsBadPlace E P.torsionField VBad (P.sectFin TF v) :=
  ⟨v, hv, P.sectFin_liesOver TF v⟩

lemma sectFin_eq {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    P.sectFin TF v = (P.exists_good_place TF hv).choose := by
  unfold sectFin
  rw [dif_pos hv]

lemma _root_.Iut.TateFamily.graphLineAt_congr {w w' : FinitePlace ↥P.torsionField} (h : w = w')
    (hw : IsBadPlace E P.torsionField VBad w) (hw' : IsBadPlace E P.torsionField VBad w') :
    TF.graphLineAt w hw = TF.graphLineAt w' hw' := by
  subst h
  rfl

lemma _root_.Iut.TateFamily.isCanonicalAt_congr {w w' : FinitePlace ↥P.torsionField} (h : w = w')
    (hw : IsBadPlace E P.torsionField VBad w) (hw' : IsBadPlace E P.torsionField VBad w')
    (R : P.EK.toAffine.Point) : TF.IsCanonicalAt w hw R ↔ TF.IsCanonicalAt w' hw' R := by
  subst h
  exact Iff.rfl

lemma sectFin_graphLine {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) :
    TF.graphLineAt (P.sectFin TF v) (P.sectFin_isBad TF hv) = P.M :=
  (TF.graphLineAt_congr P (P.sectFin_eq TF hv) _ _).trans
    (P.exists_good_place TF hv).choose_spec.choose_spec.1

lemma sectFin_canonical {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) (R)
    (hR : TF.IsCanonicalAt (P.sectFin TF v) (P.sectFin_isBad TF hv) R) :
    R - P.e₂ ∈ P.M ∨ R + P.e₂ ∈ P.M :=
  (P.exists_good_place TF hv).choose_spec.choose_spec.2 R
    ((TF.isCanonicalAt_congr P (P.sectFin_eq TF hv) _ _ R).mp hR)

/-- **The valuation section `V ⊆ V(K)`** (IUT I, Definition 3.1(e)). -/
def sect : ValuationSection F E Fbar VBad P where
  sectFin := P.sectFin TF
  sectInf v := (InfinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose
  sectFin_liesOver := P.sectFin_liesOver TF
  sectInf_liesOver v := (InfinitePlace.exists_liesOver (K := ↥P.torsionField) v).choose_spec

/-! ## The local conditions at the bad places -/

variable {P TF}

/-- The bad-place conditions hold at the chosen place. -/
lemma localType {v : FinitePlace ↥(fieldOfModuli F E)} (hv : v ∈ VBad) (b : Bool) :
    Orbicurve.IsTypeOneZModPM P.ℓ
      ((⟨P.EK, P.ℓ, P.M, b⟩ : Orbicurve ↥P.torsionField).baseChange
        (emb P.torsionField (P.sectFin TF v)))
      (TF.S _ (P.sectFin_isBad TF hv)) := by
  refine ⟨P.ℓ_prime, rfl, ?_, ?_⟩
  · change P.M.map (pointMap P.EK (emb P.torsionField (P.sectFin TF v))) = _
    rw [← P.sectFin_graphLine TF hv]
    exact TF.map_graphLineAt P (P.sectFin_isBad TF hv)
  · rw [Orbicurve.baseChange_M, ← P.card_M]
    exact (Nat.card_congr (AddSubgroup.equivMapOfInjective P.M _
      (pointMap_injective P.EK (emb P.torsionField (P.sectFin TF v)))).toEquiv).symm

variable (P TF)

/-- **The local theta data** `V` with the local conditions of IUT I, Definition 3.1(e), (f),
for the model. -/
def localThetaData (hcore : Pi1.HasCore (Orbicurve.oncePunctured E)
    (Orbicurve.pmQuotient (Orbicurve.oncePunctured E))) (T : TemperedPi1Theory Pi1) :
    LocalThetaData (modelAG Pi1) (modelTG Pi1 T) F E Fbar VBad P (P.orbicurveData Pi1 hcore) where
  sect := P.sect TF
  local_diagram_cartesian _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  decomp w := decompGroup ↥P.torsionField Fbar w
  decomp_isClosed w := decompGroup_isClosed ↥P.torsionField Fbar w
  tateX v hv := TF.S _ (P.sectFin_isBad TF hv)
  tateC v hv := TF.S _ (P.sectFin_isBad TF hv)
  bad_type v hv := localType hv false
  bad_theta_model v hv := localType hv false
  epsilon_graph v hv := by
    change P.CKu.cuspBaseChange (emb P.torsionField (P.sectFin TF v)) (P.CKu.cuspOf P.q) =
      Orbicurve.canonicalGraphCusp (P.CKu.baseChange (emb P.torsionField (P.sectFin TF v)))
        (TF.S _ (P.sectFin_isBad TF hv))
    have hb := P.sectFin_isBad TF hv
    rw [Orbicurve.cuspBaseChange_cuspOf]
    unfold Orbicurve.canonicalGraphCusp
    obtain ⟨g, hgT, -, hg⟩ := TF.exists_canonical P hb
    have hgc : TF.IsCanonicalAt (P.sectFin TF v) hb g :=
      (hg g).mpr (Or.inl (by rw [sub_self]; exact zero_mem _))
    split_ifs with hex
    · obtain ⟨R, hRT, hR⟩ := TF.exists_toLocal_eq P hb (by exact hex.choose.2)
      have hRc : TF.IsCanonicalAt (P.sectFin TF v) hb R := by
        unfold TateFamily.IsCanonicalAt
        change (TF.S (P.sectFin TF v) hb).IsCanonical P.ℓ
          (TateFamily.toLocal P (P.sectFin TF v) R)
        rw [hR]
        exact hex.choose_spec
      have hchoose : hex.choose =
          P.CKu.mapTorsion (emb P.torsionField (P.sectFin TF v)) ⟨R, hRT⟩ := by
        apply Subtype.ext
        rw [Orbicurve.coe_mapTorsion]
        exact hR.symm
      rw [hchoose, ← Orbicurve.mapQ_toQ]
      rcases P.sectFin_canonical TF hv R hRc with h | h
      · congr 2
        apply (QuotientAddGroup.eq).mpr
        rw [AddSubgroup.mem_addSubgroupOf]
        change -(P.e₂ : P.EK.toAffine.Point) + R ∈ P.M
        rw [neg_add_eq_sub]
        exact h
      · have hq : P.CKu.toQ ⟨R, hRT⟩ = -P.q := by
          rw [q, ← map_neg]
          apply (QuotientAddGroup.eq).mpr
          rw [AddSubgroup.mem_addSubgroupOf]
          change -R + -(P.e₂ : P.EK.toAffine.Point) ∈ P.M
          rw [← neg_add]
          exact P.M.neg_mem h
        rw [hq, map_neg, Orbicurve.cuspOf_neg _ rfl]
    · exact absurd ⟨⟨pointMap P.EK (emb P.torsionField (P.sectFin TF v)) g,
        P.CKu.pointMap_mem_torsion _ hgT⟩, hgc⟩ hex

end

end Iut.AdmissiblePrimeData

namespace Iut.Anabelian

universe v

open WeierstrassCurve NumberField Iut Iut.AdmissiblePrimeData

/-! ## The existence theorem -/

/-- **The anabelian part of initial Θ-data exists for the model** (IUT I, Definition
3.1(d)–(f); (P7) in the proof of IUT IV, Corollary 2.2), given the residual fundamental
group theories. -/
theorem anabelianExistence (Pi1 : EtalePi1Theory.{u}) (T : TemperedPi1Theory Pi1) :
    AnabelianExistence (modelAG Pi1) (modelTG Pi1 T) where
  exists_data F _ _ E _ Fbar _ _ _ _ P _ TF _ hcore :=
    ⟨P.orbicurveData Pi1 hcore, ⟨P.localThetaData Pi1 TF hcore T⟩⟩

/-- **The Corollary 3.12 variant for the model implies ABC**: with the anabelian interface
instantiated by the linear-algebraic model, the existence of initial Θ-data is a theorem,
and the remaining hypotheses are the residual fundamental-group theories, the curve inputs
of Corollary 2.2, the universal providers of the local theory, the local theta data and the
tower arithmetic, the analytic inputs, and the Corollary 3.12 variant itself. -/
theorem cor312Variant_implies_abc_model {T : Genl.HeightTheory} (Pi1 : EtalePi1Theory.{u})
    (Tp : TemperedPi1Theory Pi1)
    (A : T.ProofPackage) (CI : ∀ (K : T.CBS) (d : ℕ), CurveInputs.{u} T (modelAG Pi1) K d)
    (LTp : ∀ D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp), LocalTheory.{u, v} D.Kt)
    (TLp : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp))
      (LT : LocalTheory.{u, v} D.Kt), ThetaLocalData D LT)
    (TAp : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp))
      (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT), TowerArithmetic D LT TL)
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp))
      (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{u, v} D LT TL QI)) :
    ABC T :=
  cor312Variant_implies_abc_curves A CI (anabelianExistence Pi1 Tp) LTp TLp TAp cheb pnt h312

end Iut.Anabelian
