/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TheoremBUnfolded
import TemperedFundamentalGroups.SemistableReduction.ZariskiConnectedProof

/-!
# The `ℤ`-covering `Y → X` of the Tate curve as a tempered covering ([EtTh], §1)

[EtTh] §1 starts from the Tate curve `X` over a `p`-adic field and the tempered covering
`Y → X` with Galois group `ℤ`: the universal covering of the dual graph of the special fibre
(a loop), pulled back to `X`. Its tempered fundamental group is
`Π^tp_Y = Ker(Π^tp_X ↠ Gal(Y/X) ≅ ℤ)`.

The dependency `tempered-fundamental-groups` constructs this covering for a Tate curve
`y² + xy = x³ + π² b₄ x + π² b₆` over the valuation ring `O` (`TateObject.X₀`): a level `(R, 1)`
(no finite étale part) with the projective model `V(F) ⊆ ℙ²_O` whose special fibre is a line
and a conic meeting in two points (a `2`-gon; the dual graph is a loop), and the `ℤ`-covering of
the special fibre obtained by unrolling the loop. `ℤ` acts by deck transformations
(`TateObject.deck`) simply transitively on the fibre (`TateObject.isDeckTorsor`), whence a
continuous character `χ = TateObject.character : Π^tp_X → ℤ`.

Here `X` is `[Spec R / A]` (for `A` trivial) and `Π^tp_X = temperedPi1 O R A V hV`.

## Main definitions and results

* `TateObject.piY T V hV := ker χ`, **the tempered fundamental group `Π^tp_Y`**: an open
  (`isOpen_piY`) normal (`piY_normal`) subgroup, the **stabilizer of the base point of the
  fibre of `Y`** (`mem_piY_iff`).
* `TateObject.deck_injective`: `ℤ` acts faithfully on `Y` by deck transformations.
* `quotKerEquivInt`: for a nontrivial character `G → ℤ`, `G / ker ≃* ℤ`.
* `TateObject.piYQuotEquivInt`: **`Π^tp_X / Π^tp_Y ≅ ℤ`** whenever `χ ≠ 1`; and
  `TateObject.exists_character_ne_one'`, `TateOrbicurve.exists_character_ne_one`: `χ ≠ 1`
  holds unconditionally for good Tate data (Theorem B of `tempered-fundamental-groups`, via
  Zariski connectedness), in particular for IUT's orbicurves `E ∖ (E[ℓ] + M)` with a good Tate
  presentation (`TateOrbicurve.piYQuotEquivInt`).

The image of `χ` is `nℤ` for some `n ≠ 0`; that `n = 1` (transitivity of `Π^tp_X` on the fibre
of the connected covering `Y`) is not available from the dependency, and is not needed for
`Π^tp_X / Π^tp_Y ≅ ℤ`.

The covering `Ÿ → Y` (`Ü² = U`) is not constructed: its finite étale level is the `2`-isogeny
`E_{√q} ∖ {±1} → E_q ∖ {0}`, which would need the `TateObject` construction over a nontrivial
finite étale level (see `README.md`, scope decision S1').
-/

namespace Iut.EtaleTheta

open TemperedFundamentalGroups CategoryTheory

/-! ### Characters to `ℤ` -/

section Character

variable {G : Type*} [Group G]

/-- A nontrivial subgroup of `ℤ` is isomorphic to `ℤ`. -/
noncomputable def subgroupEquivInt (H : Subgroup (Multiplicative ℤ)) (hH : H ≠ ⊥) :
    H ≃* Multiplicative ℤ := by
  classical
  have hgen := IsCyclic.exists_generator (α := H)
  let g := hgen.choose
  have hg : ∀ x : H, x ∈ Subgroup.zpowers g := hgen.choose_spec
  have hg1 : (g : Multiplicative ℤ).toAdd ≠ 0 := by
    intro h0
    apply hH
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
    have : (g : Multiplicative ℤ) = 1 := by
      change Multiplicative.ofAdd (g : Multiplicative ℤ).toAdd = 1
      rw [h0]
      rfl
    have hk' := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow, this, one_zpow] at hk'
    rw [Subgroup.mem_bot, ← hk']
  refine (MulEquiv.ofBijective (zpowersHom H g) ⟨?_, ?_⟩).symm
  · intro a b hab
    have h := congrArg (fun x : H => (x : Multiplicative ℤ).toAdd) hab
    simp only [zpowersHom_apply, SubgroupClass.coe_zpow, toAdd_zpow] at h
    have : a.toAdd = b.toAdd := mul_right_cancel₀ hg1 h
    exact this
  · intro x
    obtain ⟨k, hk⟩ := hg x
    exact ⟨Multiplicative.ofAdd k, by simpa using hk⟩

/-- **A nontrivial character `χ : G → ℤ` has `G / ker χ ≅ ℤ`.** -/
noncomputable def quotKerEquivInt (χ : G →* Multiplicative ℤ) (h : ∃ g, χ g ≠ 1) :
    G ⧸ χ.ker ≃* Multiplicative ℤ :=
  (QuotientGroup.quotientKerEquivRange χ).trans (subgroupEquivInt _ (by
    obtain ⟨g, hg⟩ := h
    intro hb
    exact hg ((Subgroup.mem_bot).1 (hb ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩))))

lemma isOpen_ker_of_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G →* Multiplicative ℤ) (hχ : Continuous χ) : IsOpen (χ.ker : Set G) :=
  (isOpen_discrete ({1} : Set (Multiplicative ℤ))).preimage hχ

end Character

/-! ### The `ℤ`-covering of the Tate curve -/

namespace TateObject

open TemperedFundamentalGroups.TateObject FibreAut

universe u

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] (T : Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The tempered fundamental group `Π^tp_Y` of the `ℤ`-covering `Y → X` of the Tate curve**
([EtTh], §1): the kernel of the character `Π^tp_X → Gal(Y/X) = ℤ` of the deck torsor
`Y = X₀`. -/
noncomputable def piY : Subgroup (temperedPi1 O R A V hV) := (character (A := A) T V hV).ker

instance piY_normal : (piY (A := A) T V hV).Normal := MonoidHom.normal_ker _

lemma isOpen_piY : IsOpen (piY (A := A) T V hV : Set (temperedPi1 O R A V hV)) :=
  isOpen_ker_of_continuous _ (continuous_character T V hV)

/-- **`Π^tp_Y` is the stabilizer of the base point of the fibre of `Y`**: an automorphism of the
fibre functor lies in `Π^tp_Y` iff it fixes the base point `x₀` of the fibre of `Y = X₀`. -/
theorem mem_piY_iff (α : temperedPi1 O R A V hV) :
    α ∈ piY (A := A) T V hV ↔ α.app (X₀ T) (basePoint T V hV) = basePoint T V hV := by
  rw [piY, MonoidHom.mem_ker]
  have h := deckAct_deckCharacter (F := tempFibre O R A V hV) (X₀ (A := A) T) (deck T)
    (basePoint T V hV) (isDeckTorsor T V hV) α
  change deckAct _ _ (character (A := A) T V hV α) _ = _ at h
  constructor
  · intro h1
    rw [← h, h1, deckAct_one]
  · intro h1
    rw [h1] at h
    exact (isDeckTorsor (A := A) T V hV _ _).unique h (deckAct_one _ _ _)

include V hV in
/-- **The deck group `ℤ` acts faithfully on `Y`.** -/
theorem deck_injective : Function.Injective (deck (A := A) T) := by
  intro d e hde
  have hd : deckAct (F := tempFibre O R A V hV) (X₀ (A := A) T) (deck T) d (basePoint T V hV) =
      deckAct (X₀ (A := A) T) (deck T) e (basePoint T V hV) := by
    simp only [deckAct, hde]
  exact (isDeckTorsor (A := A) T V hV _ _).unique hd rfl

/-- **`Π^tp_X / Π^tp_Y ≅ ℤ`** as soon as the character of `Y` is nontrivial. -/
noncomputable def piYQuotEquivInt (h : ∃ α, character (A := A) T V hV α ≠ 1) :
    temperedPi1 O R A V hV ⧸ piY (A := A) T V hV ≃* Multiplicative ℤ :=
  quotKerEquivInt _ h

end TateObject

/-! ### Unconditional non-triviality for good Tate data -/

namespace TateObject

open TemperedFundamentalGroups.TateObject

universe u

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] (T : Data O R)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The character of `Y → X` is nontrivial** for good Tate data (Theorem B of
`tempered-fundamental-groups`, `TateObject.exists_character_ne_one_of_zariski`, with Zariski
connectedness `SemistableReduction.Statement.zariskiConnected` discharged). -/
theorem exists_character_ne_one' [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (ϖ : O) (hϖ : Irreducible ϖ) (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hb : IsUnit T.b₆ ∨ (T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0 ∧ T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π))
    (hx : Transcendental K T.x) :
    ∃ α : temperedPi1 O R A V hV, character T V hV α ≠ 1 :=
  exists_character_ne_one_of_zariski T V hV SemistableReduction.Statement.zariskiConnected
    p hp hpm hR ϖ hϖ hd hb hx

end TateObject

namespace TateOrbicurve

open TemperedFundamentalGroups.TateOrbicurve Orbicurve

universe u

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {W : WeierstrassCurve K} [W.IsElliptic]
  [DecidableEq K] (A : Type u) [Group A] [Subsingleton A]
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point} [MulSemiringAction A (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The `ℤ`-covering of IUT's Tate orbicurves is nontrivial**: for `X = E ∖ (E[ℓ] + M)`
(`ℓ ≥ 1`, `M` finite) with a good Tate presentation over a complete DVR of mixed characteristic
with perfect residue field, the character `Π^tp_X → ℤ` of `Y → X` is nontrivial. -/
theorem exists_character_ne_one [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) (ϖ : O) (hϖ : Irreducible ϖ) {π b₄ b₆ : O}
    (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0) (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hb : IsUnit b₆ ∨ (b₆ - π ^ 2 * b₄ ^ 2 ≠ 0 ∧ b₆ - π ^ 2 * b₄ ^ 2 ∣ π)) :
    ∃ α, character A ℓ M V hV hW hπ hπm α ≠ 1 := by
  haveI := smooth_geomOrbicurveRing_of_charZero (W := W) hℓ hM
  have h2 : (2 : O) ≠ 0 := fun h => two_ne_zero (congrArg Subtype.val h : ((2 : O) : K) = 0)
  have hΔ : TateNormal.tateDisc π b₄ b₆ ≠ 0 := by
    intro h
    have hW' := TateNormal.Δ_eq_tateDisc (π := π) (b₄ := b₄) (b₆ := b₆) O.subtype W hW.a₁ hW.a₂
      hW.a₃ (by rw [hW.a₄]; simp) (by rw [hW.a₆]; simp)
    rw [h, map_zero] at hW'
    exact W.isUnit_Δ.ne_zero hW'
  exact TateObject.exists_character_ne_one' (data hW hπ hπm ℓ M) V hV p hp hpm
    (ringKrullDim_geomOrbicurveRing_of_charZero hℓ hM) ϖ hϖ
    (TateNormal.squarefree_dpoly π b₄ b₆ h2 hΔ) hb (transcendental_data_x hW hπ hπm ℓ M)

/-- **`Π^tp_X / Π^tp_Y ≅ ℤ` for IUT's Tate orbicurves** with a good Tate presentation. -/
noncomputable def piYQuotEquivInt [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ)
    (hp : p.Prime) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hℓ : 1 ≤ ℓ)
    (hM : (M : Set W.toAffine.Point).Finite) (ϖ : O) (hϖ : Irreducible ϖ) {π b₄ b₆ : O}
    (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0) (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hb : IsUnit b₆ ∨ (b₆ - π ^ 2 * b₄ ^ 2 ≠ 0 ∧ b₆ - π ^ 2 * b₄ ^ 2 ∣ π)) :
    temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸
        (character A ℓ M V hV hW hπ hπm).ker ≃* Multiplicative ℤ :=
  quotKerEquivInt _ (exists_character_ne_one A V hV p hp hpm hℓ hM ϖ hϖ hW hπ hπm hb)

end TateOrbicurve

end Iut.EtaleTheta
