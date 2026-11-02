/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllRad
import TemperedFundamentalGroups.Andre.CompCuspSet
import TemperedFundamentalGroups.Andre.TateObjectDouble

/-!
# The Tate curve of `tempered-fundamental-groups` and the analytic model (MR18 T7c, iut side)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

`tempered-fundamental-groups` (tfg) provides, for Tate data `D : TateObject.Data O R` over a
field `F` (`y² + xy = x³ + π²b₄ x + π²b₆`), the `ℤ`-covering `Y = X₀` of the special fibre of the
model `TateModel.model π b₄ b₆` (a line `C` and a conic `E′` meeting in `p = [1:0:0]` and
`q = [1:-1:0]`), its character `χ = TateObject.character : Π^tp_X → ℤ`, for `Ÿ` the character
`character₂ : Π^tp_X → ℤ × ℤ/2` (`TateObjectDouble`), and the `Π^tp`-sets `TateComp D V = Bool × ℤ`
(the sheets `C × {n}` (`true`) and `E′ × {n}` (`false`)) and `CuspSet` (`Andre/CompCuspSet`).
The B-an side (`EllDiv`, `EllGal`, `EllRad`) works with the analytic model `Ÿ_∞ = 𝔾_m^an`
(coordinate `Ü`, `U = Ü²`) over a complete ultrametric field `K`, a Tate parameter `t`, a square
root `s` of `q`, the prime set `EllPrime t = ℤ ⊕ Cusp t` (component `a` = the circle
`|Ü| = ‖s‖^a`, i.e. `|U| = ‖q‖^a`) and the group `GalDeck t = Deck t ⋊ IsoAut t`.

## The sheet index (checked numerically before formalising)

For `p = 3`, `q = 81`, `π = 9` (so `ord q = 2 ord π`, `b₆ = a₆(q)/π²` a unit and `E′` a smooth
conic), the Tate parametrisation `(x(U), y(U))` (series to `|n| ≤ 8`, equation residual of
valuation `≥ 26`; an exact-rational computation, not committed) gives for `[x : y : π] mod 3`:

| `|U|`          | reduction       | piece        |
|----------------|-----------------|--------------|
| `‖q‖^{-1/2}`   | `[1:1:1]`       | `E′`         |
| `‖q‖^{-1/4}`   | `[2:1:0]`       | node `q`     |
| `1`            | `[2:2:0]`       | `C`          |
| `‖q‖^{1/4}`    | `[2:0:0]`       | node `p`     |
| `‖q‖^{1/2}`    | `[1:1:1]`       | `E′`         |
| `‖q‖^{3/4}`    | `[2:1:0]`       | node `q`     |
| `‖q‖`          | `[2:2:0]`       | `C`          |

With the gluing `Cₙ ∩ Eₙ = Cp`, `Cₙ ∩ Eₙ₊₁ = Cq` of `TateCovering.Decomp`, the sheet `C × {n}` is
the circle `|U| = ‖q‖^{n₀-n}` and `E′ × {n}` the circle `|U| = ‖q‖^{n₀-n+1/2}` (`n₀` = the sheet
of `|U| = 1`, fixed by the base point of the fibre functor). Consequently:

* **`TateComp ≇ ℤ`**: only the `C`-sheets are components of [EtTh]'s special fibre. The analytic
  component `a` (`|Ü| = ‖s‖^a`, `|U| = ‖q‖^a`) is the sheet `(true, n₀ - a)`; the sheets
  `E′ × {n}` lie over `|Ü| = ‖s‖^{a + 1/2}`, are exceptional curves of the blow-up
  (`TateModel`: "the exceptional curve") carrying no cusp, and are contracted in the stable
  model: [EtTh]'s `X^log` is a *stable* log curve of type `(1,1)` (l.392–395), and "the
  special fiber of `Y` is an infinite chain of copies of the projective line" (l.445–458).
  So the comparison is a bijection between `EllPrime t`'s components and the `C`-sheets
  `TateCompC` (`compEquiv`), not with all of `Bool × ℤ`.
* **Orientation**: the tfg deck generator `n ↦ n + 1` moves `|U| = ‖q‖^m` to `‖q‖^{m-1}`, i.e. it
  is `U ↦ q⁻¹U`, `Ü ↦ ±s⁻¹Ü`: the deck part of `g ∈ Π^tp` has index `-χ(g)` (`idx_tateDeck`).
  [EtTh] fixes `Π^tp_X ↠ ℤ` only "up to composition with an element of `Aut(ℤ) = {±1}`"
  (l.445–447); the sign `-χ` is the one matching tfg's sheet orientation with Tate's `U`.
* (For `ord q > 2 ord π`, `b₆` is not a unit and `E′` is two lines, the circles
  `|U| = ‖π‖, ‖q/π‖`; then `TateComp`'s `false`-sheets are not even irreducible.)

## Main definitions and results

* `dataCurve D`, **`IsTateParam φ D t`** (the Weierstrass curve of `D`, transported along
  `φ : F →+* K`, is Tate's `E_t`), `isTateParam_iff` (`φ(π²b₄) = a₄(t)`, `φ(π²b₆) = a₆(t)`) and
  **`IsTateParam.unique`**: the Tate parameter of `D` is unique (`tateJ_injective`).
* `tateDeckOfChar`, **`tateDeck`** : `Π^tp_X →* Deck t`, `(n, ε) ↦ (-1)^ε s^{-n}` on
  `character₂`, with **`idx_tateDeck`** (`idx = -χ`); **`tateGalDeck σ hσ`** :
  `Π^tp_X →* GalDeck t` with an explicit Galois part `σ : Π^tp_X →* IsoAut t` fixing `s`.
* **`gammaChi τ`** : `Π^tp_X →* ExtGalDeck t R` (a genuine `γ`), through `χ` and one extension
  `τ` of `Ü ↦ s⁻¹Ü` (`exists_genLift` for `R` an algebraic closure; `extRes_gammaChi`), and
  `gammaChiRadData`, the radical-layer Frobenioid data on `Π^tp_X`.
* `IsTateLift γ σ hσ` (a property of an input `γ : Π^tp_X →* ExtGalDeck t R`: it lifts
  `tateGalDeck σ hσ`).
* Components: `TateCompC` (the `C`-sheets, a sub-`Π^tp`-set), **`compEquiv n₀ : ℤ ≃ TateCompC`**,
  **`compEquiv_smul`** (equivariance for every `ρ : Π^tp_X →* GalDeck t` with deck index `-χ`).
* Cusps: **`CuspDecompFix ρ α`** (explicit hypothesis: the decomposition group `N(I^tp_{W i})` of
  the base cusp `i` fixes the chosen analytic cusp `α i`), `cuspMap`, **`cuspMap_smul`**,
  `cuspMap_baseCusp`, `cuspMap_isCusp`.
* **`tatePrimeMap`** : `TateCompC ⊕ CuspSet → EllPrime t`, `Π^tp`-equivariant
  (`tatePrimeMap_smul`), a bijection from the `C`-sheets onto the components
  (`tatePrimeMap_inl_bijective`); `tatePrimeMap_smul_tateGalDeck` for the Tate action,
  `tatePrimeMap_smul_lift` for `ρ = extRes ∘ γ` (e.g. `γ` a Tate lift or `gammaChi`).

## Explicit inputs and debts (T7c)

* `tateDeck` is *defined* by the deck formula found above (consumers may use only what is proved
  about it). Its comparison with the analytic `Ü`-model is proved on the function field of `X'`
  (`EllTateAn`: `K(E_t) ⊆ Mero K`, `√(x - e) ∈ Mero K`); the comparison of all tempered
  coverings (`Π^tp` acting on `Ÿ_∞ = 𝔾_m^an`) is not formalised. `σ` (the image of
  `Π^tp_X → G_F` in `IsoAut t`) is a parameter here; `TateGalSigma.sigmaTemp` constructs it from
  tfg's `piToGk ∘ tempToPi` for `K` the completion of `k̄` (`tateGalDeckK`). `hσ` (σ fixes `s`)
  holds when `s ∈ φ(F)`, which tfg's `DoubleData` (the `2`-torsion point `√q` is `F`-rational)
  forces.
* A lift `γ` of `tateGalDeck σ hσ` with nontrivial `ℤ/2`-part does not factor through
  `ℤ × ℤ/2` when `K` is algebraically closed (an involution of `R` fixing `K ∋ √-1` would have a
  real closed fixed field), so no such `γ` is constructed; `gammaChi` covers the `χ`-part.
* **`CuspDecompFix`** is the T7c debt "CuspSet = geometric cusps" in the form consumed here.
  Nonemptiness of `CompSys` is not used.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta TemperedFundamentalGroups TemperedFundamentalGroups.CompCusp
open TemperedFundamentalGroups.TateObject

universe u

/-! ### The Tate parameter of `TateObject.Data` -/

section Param

variable {F : Type u} [Field F] {O : ValuationSubring F} {R : Type u} [CommRing R] [Algebra F R]
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The Weierstrass curve of the Tate data** `y² + xy = x³ + π²b₄ x + π²b₆` over `F`. -/
def dataCurve (D : TateObject.Data O R) : WeierstrassCurve F where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := (D.π : F) ^ 2 * D.b₄
  a₆ := (D.π : F) ^ 2 * D.b₆

/-- **`t` is the Tate parameter of `D`** (along `φ : F →+* K`): the Weierstrass curve of `D`,
transported to `K`, is Tate's curve `E_t`. -/
def IsTateParam (φ : F →+* K) (D : TateObject.Data O R) (t : TateParameter K) : Prop :=
  (dataCurve D).map φ = t.tateCurve

theorem isTateParam_iff (φ : F →+* K) (D : TateObject.Data O R) (t : TateParameter K) :
    IsTateParam φ D t ↔ φ ((D.π : F) ^ 2 * D.b₄) = t.a₄ ∧ φ ((D.π : F) ^ 2 * D.b₆) = t.a₆ := by
  constructor
  · intro h
    exact ⟨congrArg WeierstrassCurve.a₄ h, congrArg WeierstrassCurve.a₆ h⟩
  · rintro ⟨h4, h6⟩
    ext
    · exact map_one φ
    · exact map_zero φ
    · exact map_zero φ
    · exact h4
    · exact h6

/-- **The Tate parameter of `D` is unique** (`q ↦ j(E_q)` is injective). -/
theorem IsTateParam.unique (h12 : (12 : K) ≠ 0) {φ : F →+* K} {D : TateObject.Data O R}
    {t₁ t₂ : TateParameter K} (h₁ : IsTateParam φ D t₁) (h₂ : IsTateParam φ D t₂) : t₁ = t₂ :=
  TateParameter.tateJ_injective t₁ t₂ h12 (by
    rw [TateParameter.tateJ_def, TateParameter.tateJ_def,
      ← show (dataCurve D).map φ = t₁.tateCurve from h₁,
      ← show (dataCurve D).map φ = t₂.tateCurve from h₂])

end Param

/-! ### The deck part `Π^tp_X → Deck t` -/

section Deck

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

variable (t) in
/-- `Ü ↦ -Ü`. -/
def Deck.neg : Deck t := ⟨-1, 0, by simp⟩

lemma Deck.neg_mul_neg : Deck.neg t * Deck.neg t = 1 :=
  Subtype.ext (Units.ext (by simp [Deck.neg]))

lemma Deck.idx_neg : Deck.idx (Deck.neg t) = 0 := Deck.idx_eq (by simp [Deck.neg])

lemma Deck.idx_zpow (c : Deck t) (n : ℤ) : Deck.idx (c ^ n) = n * Deck.idx c := by
  apply Deck.idx_eq
  rw [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, Deck.idx_spec, ← zpow_mul, mul_comm]

lemma Deck.idx_inv (c : Deck t) : Deck.idx c⁻¹ = -Deck.idx c := by
  rw [← zpow_neg_one, Deck.idx_zpow, neg_one_mul]

lemma mult_zmod_two (e : Multiplicative (ZMod 2)) : e = 1 ∨ e = Multiplicative.ofAdd 1 := by
  revert e; decide

variable (t) in
/-- **The sign** `ℤ/2 →* Deck t`, `1 ↦ (Ü ↦ -Ü)`. -/
def signHom : Multiplicative (ZMod 2) →* Deck t where
  toFun e := if e = 1 then 1 else Deck.neg t
  map_one' := if_pos rfl
  map_mul' a b := by
    have h11 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    rcases mult_zmod_two a with rfl | rfl <;> rcases mult_zmod_two b with rfl | rfl <;>
      simp only [h11, hne, mul_one, one_mul, if_true, if_false, Deck.neg_mul_neg]

lemma signHom_ofAdd_one : signHom t (Multiplicative.ofAdd 1) = Deck.neg t :=
  show (if Multiplicative.ofAdd (1 : ZMod 2) = 1 then (1 : Deck t) else Deck.neg t) = Deck.neg t
    from if_neg (by decide)

lemma Deck.idx_signHom (e : Multiplicative (ZMod 2)) : Deck.idx (signHom t e) = 0 := by
  rcases mult_zmod_two e with rfl | rfl
  · rw [map_one, Deck.idx_one]
  · rw [signHom_ofAdd_one, Deck.idx_neg]

/-- **The deck transformation of `(n, ε) ∈ ℤ × ℤ/2`**: `Ü ↦ (-1)^ε s^{-n} Ü` (the tfg sheet
shift `n ↦ n + 1` is `U ↦ q⁻¹U`, see the module docstring). -/
def tateDeckOfChar {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    Multiplicative ℤ × Multiplicative (ZMod 2) →* Deck t :=
  MonoidHom.coprod (zpowersHom (Deck t) (Deck.gen t hs)⁻¹) (signHom t)

lemma idx_tateDeckOfChar {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (x : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    Deck.idx (tateDeckOfChar hs x) = -Multiplicative.toAdd x.1 := by
  rw [tateDeckOfChar, MonoidHom.coprod_apply, Deck.idx_mul, Deck.idx_signHom, add_zero,
    zpowersHom_apply, Deck.idx_zpow, Deck.idx_inv, Deck.idx_gen, mul_neg, mul_one]

/-- `σ` fixing `s` fixes every deck transformation `(-1)^ε s^{-n}`. -/
lemma gal_tateDeckOfChar {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {σ : IsoAut t}
    (hσ : (σ : RingAut K) s = s) (x : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    galOnDeck t σ (tateDeckOfChar hs x) = tateDeckOfChar hs x := by
  have hg : galOnDeck t σ (Deck.gen t hs) = Deck.gen t hs :=
    Subtype.ext (Units.ext (by rw [galOnDeck_apply, Deck.coe_gal, IsoAut.coe_u]; exact hσ))
  have hn : galOnDeck t σ (Deck.neg t) = Deck.neg t :=
    Subtype.ext (Units.ext (by
      rw [galOnDeck_apply, Deck.coe_gal, IsoAut.coe_u]
      simp [Deck.neg]))
  have he : ∀ e, galOnDeck t σ (signHom t e) = signHom t e := fun e => by
    rcases mult_zmod_two e with rfl | rfl
    · rw [map_one, map_one]
    · rw [signHom_ofAdd_one, hn]
  rw [tateDeckOfChar, MonoidHom.coprod_apply, map_mul, he, zpowersHom_apply, map_zpow, map_inv,
    hg]

variable {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  [IsReduced R] (D : TateObject.DoubleData O R) (sΩ : Ω) (hsΩ : sΩ ^ 2 = algebraMap R Ω D.c)

/-- **The deck part `Π^tp_X → Deck t`, defined by a formula**: `character₂` followed by
`(n, ε) ↦ (-1)^ε s^{-n}`.

This is a *definition*, not a theorem that it is the action of `Π^tp_X` on `Ÿ_∞ = 𝔾_m^an`: no
consumer may treat it as "the action on `𝔾_m^an`" beyond what is proved about it (rule 4). The
proved comparison (`EllTateAn`) is on the function field of `X' = E_t(√(x - e))` inside
`Mero K`: `tateDeck g` fixes the image of `K(E_t)` and multiplies the analytic `√(x - e)` by
`(-1)^ε`, where `ε` (the `ℤ/2`-part of `character₂ g`) is the action of `g` on the fibre
`{±√c}` of `X'`; for elements of the decomposition group this is their Galois action on `√c`.
The `ℤ`-part acts trivially on `X'`, and its sign `-χ` is a convention matching tfg's sheet
orientation with Tate's `U` (module docstring): [EtTh] fixes `Π^tp_X ↠ ℤ` only "up to
composition with an element of `Aut(ℤ) = {±1}`" (l.445–447). The identification of all tempered
coverings of the analytic and the schematic Tate curve is not formalised. -/
def tateDeck {s : Kˣ} (hs : (s : K) ^ 2 = t.q) : temperedPi1 O R A V hV →* Deck t :=
  (tateDeckOfChar hs).comp (character₂ (A := A) D V hV sΩ hsΩ)

/-- **The deck index is `-χ`.** -/
theorem idx_tateDeck {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (g : temperedPi1 O R A V hV) :
    Deck.idx (tateDeck V hV D sΩ hsΩ hs g) =
      -Multiplicative.toAdd (character (A := A) D.toData V hV g) := by
  rw [tateDeck, MonoidHom.comp_apply, idx_tateDeckOfChar, character_eq_fst D V hV sΩ hsΩ]

/-- **The Galois × deck part** `Π^tp_X →* GalDeck t`, `g ↦ ⟨tateDeck g, σ g⟩`, for an explicit
Galois part `σ` fixing `s`. -/
def tateGalDeck {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) :
    temperedPi1 O R A V hV →* GalDeck t where
  toFun g := ⟨tateDeck V hV D sΩ hsΩ hs g, σ g⟩
  map_one' := SemidirectProduct.ext (map_one _) (map_one _)
  map_mul' g h := SemidirectProduct.ext (by
      rw [SemidirectProduct.mul_left, map_mul]
      change _ = _ * galOnDeck t (σ g) (tateDeckOfChar hs _)
      rw [gal_tateDeckOfChar hs (hσ g)]
      rfl) (map_mul σ g h)

lemma tateGalDeck_left {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) (g : temperedPi1 O R A V hV) :
    (tateGalDeck V hV D sΩ hsΩ hs σ hσ g).left = tateDeck V hV D sΩ hsΩ hs g := rfl

lemma tateGalDeck_right {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) (g : temperedPi1 O R A V hV) :
    (tateGalDeck V hV D sΩ hsΩ hs σ hσ g).right = σ g := rfl

variable {RR : Type u} [Field RR] [Algebra (Mero K) RR]

/-- **`γ` is a Tate lift**: an action `γ : Π^tp_X →* ExtGalDeck t RR` on the radical layer
restricting to `tateGalDeck σ hσ` on `Mero K` (a property of the input `γ`). -/
def IsTateLift {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (σ : temperedPi1 O R A V hV →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s)
    (γ : temperedPi1 O R A V hV →* ExtGalDeck t RR) : Prop :=
  (extRes t RR).comp γ = tateGalDeck V hV D sΩ hsΩ hs σ hσ

lemma IsTateLift.idx {s : Kˣ} {hs : (s : K) ^ 2 = t.q} {σ : temperedPi1 O R A V hV →* IsoAut t}
    {hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s}
    {γ : temperedPi1 O R A V hV →* ExtGalDeck t RR}
    (h : IsTateLift V hV D sΩ hsΩ hs σ hσ γ) (g : temperedPi1 O R A V hV) :
    Deck.idx (extRes t RR (γ g)).left =
      -Multiplicative.toAdd (character (A := A) D.toData V hV g) := by
  rw [← MonoidHom.comp_apply, h, tateGalDeck_left, idx_tateDeck]

end Deck

/-! ### A genuine action of `Π^tp_X` on the radical layer through `χ` -/

section GammaChi

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  [IsReduced R] (D : TateObject.Data O R)
  {RR : Type u} [Field RR] [Algebra (Mero K) RR]

set_option synthInstance.maxHeartbeats 400000 in
-- `Module.IsTorsionFree (Mero K) RR` (needed by `IsAlgClosure`) times out at the default budget
-- (as in `EllRad.exists_ext`).
/-- **`Ü ↦ s⁻¹Ü` extends** to an algebraic closure `RR` of `Mero K` (`extRes_surjective`). -/
theorem exists_genLift [IsAlgClosure (Mero K) RR] {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ∃ τ : ExtGalDeck t RR, extRes t RR τ = SemidirectProduct.inl (Deck.gen t hs)⁻¹ :=
  extRes_surjective (SemidirectProduct.inl (Deck.gen t hs)⁻¹)

/-- **A genuine `γ : Π^tp_X →* ExtGalDeck t RR`**: `g ↦ τ^{χ(g)}` for one extension `τ` of
`Ü ↦ s⁻¹Ü` (`exists_genLift`); `ℤ` being free, nothing else is chosen. -/
def gammaChi (τ : ExtGalDeck t RR) : temperedPi1 O R A V hV →* ExtGalDeck t RR :=
  (zpowersHom _ τ).comp (character (A := A) D V hV)

/-- `gammaChi` restricts to the deck transformation `Ü ↦ s^{-χ(g)}Ü` on `Mero K`. -/
theorem extRes_gammaChi {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {τ : ExtGalDeck t RR}
    (hτ : extRes t RR τ = SemidirectProduct.inl (Deck.gen t hs)⁻¹) (g : temperedPi1 O R A V hV) :
    extRes t RR (gammaChi V hV D τ g) =
      SemidirectProduct.inl
        ((Deck.gen t hs)⁻¹ ^ Multiplicative.toAdd (character (A := A) D V hV g)) := by
  rw [gammaChi, MonoidHom.comp_apply, zpowersHom_apply, map_zpow, hτ, map_zpow]

theorem idx_gammaChi {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {τ : ExtGalDeck t RR}
    (hτ : extRes t RR τ = SemidirectProduct.inl (Deck.gen t hs)⁻¹) (g : temperedPi1 O R A V hV) :
    Deck.idx (extRes t RR (gammaChi V hV D τ g)).left =
      -Multiplicative.toAdd (character (A := A) D V hV g) := by
  rw [extRes_gammaChi V hV D hs hτ, SemidirectProduct.left_inl, Deck.idx_zpow, Deck.idx_inv,
    Deck.idx_gen, mul_neg, mul_one]

/-- **The radical-layer tempered Frobenioid data on `Π^tp_X`** for the action `gammaChi`. -/
abbrev gammaChiRadData (τ : ExtGalDeck t RR) (hval : ValueGroupRat t) {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) : TemperedFrobenioidData (temperedPi1 O R A V hV) :=
  radDataRad (gammaChi V hV D τ) hval hs

end GammaChi

/-! ### Components: the `C`-sheets -/

section Comp

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O) (D : TateObject.Data O R)

/-- **The `C`-sheets** `C × {n}` of `TateComp D V`: the components of the stable model. -/
def TateCompC : Type := {x : TateComp D V // x.1 = true}

instance : MulAction (temperedPi1 O R A V hV) (TateCompC V D) where
  smul g x := ⟨g • x.1, x.2⟩
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

lemma TateCompC.coe_smul (g : temperedPi1 O R A V hV) (x : TateCompC V D) :
    (g • x).1 = g • x.1 := rfl

/-- **The analytic component `a` is the sheet `C × {n₀ - a}`** (`n₀` = the sheet of `|U| = 1`). -/
def compEquiv (n₀ : ℤ) : ℤ ≃ TateCompC V D where
  toFun a := ⟨((true, n₀ - a) : Bool × ℤ), rfl⟩
  invFun x := n₀ - (x.1 : Bool × ℤ).2
  left_inv a := by simp
  right_inv x := by
    obtain ⟨⟨b, n⟩, hb⟩ := x
    change b = true at hb
    subst hb
    apply Subtype.ext
    change ((true, n₀ - (n₀ - n)) : Bool × ℤ) = (true, n)
    rw [sub_sub_cancel]

/-- `GalDeck t` moves the component `a` by the deck index. -/
lemma galDeck_smul_inl (x : GalDeck t) (a : ℤ) :
    x • (Sum.inl a : EllPrime t) = Sum.inl (a + Deck.idx x.left) := rfl

/-- **Equivariance on components**: for any action `ρ : Π^tp_X →* GalDeck t` whose deck index
is `-χ` (`idx_tateDeck`, `idx_gammaChi`, `IsTateLift.idx`). -/
theorem compEquiv_smul (n₀ : ℤ) (ρ : temperedPi1 O R A V hV →* GalDeck t)
    (hρ : ∀ g, Deck.idx (ρ g).left = -Multiplicative.toAdd (character (A := A) D V hV g))
    (g : temperedPi1 O R A V hV) (a : ℤ) :
    compEquiv V D n₀ (a + Deck.idx (ρ g).left) = g • compEquiv V D n₀ a := by
  apply Subtype.ext
  change ((true, n₀ - (a + Deck.idx (ρ g).left)) : Bool × ℤ) =
    (true, n₀ - a + Multiplicative.toAdd (character (A := A) D V hV g))
  rw [hρ]
  congr 1
  ring

end Comp

/-! ### Cusps -/

section Cusp

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap F Ω) = O)
  {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i)
  (ρ : temperedPi1 O R A V hV →* GalDeck t) (α : ι → Cusp t)

/-- **Explicit hypothesis (T7c debt "CuspSet = geometric cusps")**: the decomposition group
`D_i = N(I^tp_{W i})` of the base cusp over `W i` fixes the analytic cusp `α i` of `Ÿ_∞` below
it. -/
def CuspDecompFix : Prop :=
  ∀ i, ∀ g ∈ cuspDecomp O R A hV W hVW i, ρ g • (Sum.inr (α i) : EllPrime t) = Sum.inr (α i)

variable {ρ α}

/-- **The cusp map** `CuspSet → EllPrime t`, `⟨i, g D_i⟩ ↦ ρ(g) • α i`. -/
def cuspMap (hD : CuspDecompFix hV W hVW ρ α) : CuspSet O R A hV W hVW → EllPrime t :=
  fun x => Quotient.liftOn' x.2 (fun g => ρ g • (Sum.inr (α x.1) : EllPrime t)) (by
    intro g g' h
    rw [QuotientGroup.leftRel_apply] at h
    change ρ g • _ = ρ g' • _
    rw [show g' = g * (g⁻¹ * g') by group, map_mul, mul_smul, hD x.1 _ h])

lemma cuspMap_mk (hD : CuspDecompFix hV W hVW ρ α) (i : ι) (g : temperedPi1 O R A V hV) :
    cuspMap hV W hVW hD ⟨i, (g : temperedPi1 O R A V hV ⧸ cuspDecomp O R A hV W hVW i)⟩ =
      ρ g • (Sum.inr (α i) : EllPrime t) := rfl

theorem cuspMap_baseCusp (hD : CuspDecompFix hV W hVW ρ α) (i : ι) :
    cuspMap hV W hVW hD (baseCusp O R A hV W hVW i) = Sum.inr (α i) := by
  rw [baseCusp, cuspMap_mk, map_one, one_smul]

/-- **The cusp map is `Π^tp`-equivariant.** -/
theorem cuspMap_smul (hD : CuspDecompFix hV W hVW ρ α) (g : temperedPi1 O R A V hV)
    (x : CuspSet O R A hV W hVW) :
    cuspMap hV W hVW hD (g • x) = ρ g • cuspMap hV W hVW hD x := by
  obtain ⟨i, y⟩ := x
  induction y using QuotientGroup.induction_on with
  | H h =>
    change ρ (g * h) • (Sum.inr (α i) : EllPrime t) = ρ g • (ρ h • (Sum.inr (α i) : EllPrime t))
    rw [map_mul, mul_smul]

/-- `GalDeck t` maps cusps to cusps. -/
lemma galDeck_smul_inr (x : GalDeck t) (β : Cusp t) :
    ∃ β' : Cusp t, x • (Sum.inr β : EllPrime t) = Sum.inr β' := ⟨_, rfl⟩

theorem cuspMap_isCusp (hD : CuspDecompFix hV W hVW ρ α) (x : CuspSet O R A hV W hVW) :
    ∃ β : Cusp t, cuspMap hV W hVW hD x = Sum.inr β := by
  obtain ⟨i, y⟩ := x
  induction y using QuotientGroup.induction_on with
  | H h => exact galDeck_smul_inr (ρ h) (α i)

end Cusp

/-! ### The prime map `TateCompC ⊕ CuspSet → EllPrime t` -/

section Prime

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O) (D : TateObject.Data O R)
  {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i)
  {ρ : temperedPi1 O R A V hV →* GalDeck t} {α : ι → Cusp t}

/-- **The comparison of prime sets**: the `C`-sheets go to the components
(`(true, n) ↦ n₀ - n`), the cusps through `cuspMap`. -/
def tatePrimeMap (n₀ : ℤ) (hD : CuspDecompFix hV W hVW ρ α) :
    TateCompC V D ⊕ CuspSet O R A hV W hVW → EllPrime t :=
  Sum.elim (fun x => Sum.inl ((compEquiv V D n₀).symm x)) (cuspMap hV W hVW hD)

/-- **The comparison is `Π^tp`-equivariant** for an action `ρ` with deck index `-χ`. -/
theorem tatePrimeMap_smul (n₀ : ℤ) (hD : CuspDecompFix hV W hVW ρ α)
    (hρ : ∀ g, Deck.idx (ρ g).left = -Multiplicative.toAdd (character (A := A) D V hV g))
    (g : temperedPi1 O R A V hV) (x : TateCompC V D ⊕ CuspSet O R A hV W hVW) :
    tatePrimeMap V hV D W hVW n₀ hD (g • x) = ρ g • tatePrimeMap V hV D W hVW n₀ hD x := by
  rcases x with c | c
  · change Sum.inl ((compEquiv V D n₀).symm (g • c)) =
      Sum.inl ((compEquiv V D n₀).symm c + Deck.idx (ρ g).left)
    congr 1
    rw [Equiv.symm_apply_eq, compEquiv_smul V hV D n₀ ρ hρ, Equiv.apply_symm_apply]
  · exact cuspMap_smul hV W hVW hD g c

/-- **On components the comparison is a bijection** `C`-sheets `≃` `ℤ`. -/
theorem tatePrimeMap_inl_bijective (n₀ : ℤ) (hD : CuspDecompFix hV W hVW ρ α) :
    Function.Bijective (fun c : TateCompC V D => (compEquiv V D n₀).symm c) ∧
      ∀ c, tatePrimeMap V hV D W hVW n₀ hD (Sum.inl c) = Sum.inl ((compEquiv V D n₀).symm c) :=
  ⟨(compEquiv V D n₀).symm.bijective, fun _ => rfl⟩

/-- **The comparison with the radical-layer action**: for a Tate lift `γ` (or any `γ` whose deck
index is `-χ`), `tatePrimeMap` is equivariant into `PrimeAct (galDeckRadPerm t γ)`. -/
theorem tatePrimeMap_smul_lift {RR : Type u} [Field RR] [Algebra (Mero K) RR]
    (γ : temperedPi1 O R A V hV →* ExtGalDeck t RR) (n₀ : ℤ)
    (hD : CuspDecompFix hV W hVW ((extRes t RR).comp γ) α)
    (hγ : ∀ g, Deck.idx (extRes t RR (γ g)).left =
      -Multiplicative.toAdd (character (A := A) D V hV g))
    (g : temperedPi1 O R A V hV) (x : TateCompC V D ⊕ CuspSet O R A hV W hVW) :
    (show PrimeAct (galDeckRadPerm t γ) from tatePrimeMap V hV D W hVW n₀ hD (g • x)) =
      g • (show PrimeAct (galDeckRadPerm t γ) from tatePrimeMap V hV D W hVW n₀ hD x) :=
  tatePrimeMap_smul V hV D W hVW n₀ hD hγ g x

end Prime

/-! ### The Tate action `tateGalDeck` -/

section TateAction

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}
  {F : Type u} [Field F] {O : ValuationSubring F}
  {R : Type u} [CommRing R] [Algebra F R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower F R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)
  (D : TateObject.DoubleData O R) (sΩ : Ω) (hsΩ : sΩ ^ 2 = algebraMap R Ω D.c)
  {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i)

/-- **The comparison is equivariant for the Tate action** `tateGalDeck σ hσ` (given the cusp
hypothesis `CuspDecompFix`). -/
theorem tatePrimeMap_smul_tateGalDeck {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (σ : temperedPi1 O R A V hV →* IsoAut t) (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s)
    (n₀ : ℤ) {α : ι → Cusp t}
    (hD : CuspDecompFix hV W hVW (tateGalDeck V hV D sΩ hsΩ hs σ hσ) α)
    (g : temperedPi1 O R A V hV) (x : TateCompC V D.toData ⊕ CuspSet O R A hV W hVW) :
    tatePrimeMap V hV D.toData W hVW n₀ hD (g • x) =
      tateGalDeck V hV D sΩ hsΩ hs σ hσ g • tatePrimeMap V hV D.toData W hVW n₀ hD x :=
  tatePrimeMap_smul V hV D.toData W hVW n₀ hD (fun g => idx_tateDeck V hV D sΩ hsΩ hs g) g x

end TateAction

end Iut.Frobenioid.BAn
