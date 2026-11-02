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
`Π^tp_X / Π^tp_Y ≅ ℤ`. **`TateObject.charN`** is the normalised character `χ/n`
(`normChar`, `charGen`): same kernel `Π^tp_Y` (`charN_eq_one_iff`), and it takes the value `1`
when `χ ≠ 1` (`exists_charN_eq_ofAdd_one`); it is the character used for `Π^tp_X̿` (TFGD run 2).

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

/-- **A generator of the image of a character** `χ : G → ℤ` (the image is `charGen χ · ℤ`). -/
noncomputable def charGen (χ : G →* Multiplicative ℤ) : ℤ :=
  ((IsCyclic.exists_generator (α := χ.range)).choose : Multiplicative ℤ).toAdd

theorem charGen_dvd (χ : G →* Multiplicative ℤ) (x : G) : charGen χ ∣ (χ x).toAdd := by
  obtain ⟨k, hk⟩ := (IsCyclic.exists_generator (α := χ.range)).choose_spec ⟨χ x, x, rfl⟩
  refine ⟨k, ?_⟩
  have h := congrArg (fun y : χ.range => (y : Multiplicative ℤ).toAdd) hk
  simp only [SubgroupClass.coe_zpow, toAdd_zpow, smul_eq_mul] at h
  rw [← h, charGen, mul_comm]

/-- **The normalised character** `χ̂ = χ / m` of `χ : G → ℤ` with image `mℤ`: it has the same
kernel (`normChar_eq_one_iff`) and, if `χ ≠ 1`, takes the value `1`
(`exists_normChar_eq_ofAdd_one`), i.e. it induces the isomorphism `G / ker χ ≅ ℤ`. -/
noncomputable def normChar (χ : G →* Multiplicative ℤ) : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd ((χ x).toAdd / charGen χ)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul]
    rw [Int.add_ediv_of_dvd_left (charGen_dvd χ x)]
    rfl

theorem normChar_apply (χ : G →* Multiplicative ℤ) (x : G) :
    normChar χ x = Multiplicative.ofAdd ((χ x).toAdd / charGen χ) := rfl

theorem normChar_eq_one_iff (χ : G →* Multiplicative ℤ) (x : G) :
    normChar χ x = 1 ↔ χ x = 1 := by
  obtain ⟨k, hk⟩ := charGen_dvd χ x
  rw [normChar_apply, ← ofAdd_zero, ← ofAdd_toAdd (χ x), hk]
  simp only [toAdd_ofAdd, EmbeddingLike.apply_eq_iff_eq]
  rcases eq_or_ne (charGen χ) 0 with h0 | h0
  · simp [h0]
  · rw [Int.mul_ediv_cancel_left _ h0, mul_eq_zero]
    simp [h0]

/-- **A nontrivial character has normalised value `1`** somewhere (at a preimage of a generator
of its image). -/
theorem exists_normChar_eq_ofAdd_one (χ : G →* Multiplicative ℤ) (h : ∃ g, χ g ≠ 1) :
    ∃ g, normChar χ g = Multiplicative.ofAdd (1 : ℤ) := by
  obtain ⟨g₀, hg₀⟩ := ((IsCyclic.exists_generator (α := χ.range)).choose : χ.range).2
  have hm : charGen χ = (χ g₀).toAdd := congrArg Multiplicative.toAdd hg₀.symm
  have hm0 : charGen χ ≠ 0 := by
    intro h0
    obtain ⟨g, hg⟩ := h
    obtain ⟨k, hk⟩ := charGen_dvd χ g
    rw [h0, zero_mul] at hk
    exact hg (by rw [← ofAdd_toAdd (χ g), hk]; rfl)
  refine ⟨g₀, ?_⟩
  rw [normChar_apply, ← hm, Int.ediv_self hm0]

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

/-- **The normalised character `χ̂ : Π^tp_X → ℤ` of `Y → X`** (`normChar` of
`TateObject.character`): `χ / m` for the image `mℤ` of `χ`. Same kernel `Π^tp_Y`
(`charN_eq_one_iff`); `χ̂` induces `Π^tp_X / Π^tp_Y ≅ ℤ` and takes the value `1` as soon as
`χ ≠ 1` (Theorem B; `exists_charN_eq_ofAdd_one`). ([EtTh] uses `Gal(Y/X) ≅ ℤ`; the subgroups
`χ̂⁻¹(lℤ)` are the intrinsic `l`-cyclic quotients of `Gal(Y/X)`.) -/
noncomputable def charN : temperedPi1 O R A V hV →* Multiplicative ℤ :=
  normChar (character (A := A) T V hV)

theorem charN_eq_one_iff (α : temperedPi1 O R A V hV) :
    charN (A := A) T V hV α = 1 ↔ α ∈ piY (A := A) T V hV :=
  normChar_eq_one_iff _ α

lemma continuous_charN : Continuous (charN (A := A) T V hV) :=
  (continuous_of_discreteTopology (f := fun x : Multiplicative ℤ =>
    Multiplicative.ofAdd (x.toAdd / charGen (character (A := A) T V hV)))).comp
    (continuous_character T V hV)

theorem exists_charN_eq_ofAdd_one (h : ∃ α, character (A := A) T V hV α ≠ 1) :
    ∃ α, charN (A := A) T V hV α = Multiplicative.ofAdd (1 : ℤ) :=
  exists_normChar_eq_ofAdd_one _ h

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
