/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.ThetaMonoid
import Iut.Frobenioid.Thm34DivSlim

/-!
# Preservation of base-field-theoretic morphisms ([EtTh], Corollary 3.8(i),(ii))

[EtTh], Corollary 3.8 (l.5911–5994 of `~/iut-scratch/wall/txt/The Etale Theta Function and its
Frobenioid-theoretic Manifestations.txt`): for tempered Frobenioids `C₁`, `C₂` over bases of
FSMFF-type with non-dilating divisor monoids, every equivalence `Ψ : C₁ ≅ C₂` preserves the
base-field-theoretic morphisms (for Frobenius-slim bases, (i); for Div-slim bases, (ii)).

The proof in [EtTh]: `Ψ` preserves pre-steps and primary steps, is compatible with passing to the
perfection ([FrdI], Theorem 3.4(iii)), and preserves the submonoids `O^⊿(−)` ([FrdI],
Theorem 3.4(iv), Corollary 4.11(ii)). By Proposition 3.4(ii) (`O^⊿_L ≅ B₀ ×_{Φ₀^gp} Φ₀`: the
elements of `O^⊿` come from the base field `L`) "a pre-step of `C_i` is base-field-theoretic if
and only if its image `A → B` in `C^pf_i` may be written as a [filtered] projective limit in the
category `(C^pf_i)^{coa-pre}_B` of pre-steps `A' → B` that are abstractly equivalent to an
endomorphism that belongs to `O^⊿(−)`"; finally `Ψ` preserves the factorization of a morphism
into a morphism of Frobenius type, a pre-step and a pull-back morphism.

## Formalisation

For a model Frobenioid `C = Model Φ B divB` ([FrdI], Theorem 5.2) and an object `A` of the base:

* `Model.ratOrhd divB A`: the **zero divisors of the pre-steps of `C^pf` abstractly equivalent to
  endomorphisms in `O^⊿`**: the `e ∈ Φ(A)` with `n·e = Div_B(b)` for some `n ≥ 1`, `b ∈ B(A)`
  (in `C^pf` the object `(X, n)` is an `n`-th root of `X`, [FrdI], Definition 3.1(iii), so a
  pre-step of `C^pf` with zero divisor `e` becomes, after the Frobenius morphism of degree `n`, the
  endomorphism `(1, id, Div_B b, b)` of `O^⊿`);
* `Model.IsBsFldDiv divB d`: `d ∈ Φ(A)` is the **least upper bound of the elements of
  `ratOrhd` below it** — the zero divisor of a projective limit of such pre-steps in the category
  of pre-steps over a fixed target (a pre-step factors through another iff its zero divisor is
  larger, `Model.exists_factor_of_preStep`);
* `Model.BsFldChar ιΦ divB`: the hull `Φ' ⊆ Φ` ([EtTh], Definition 3.6(ii),(iv):
  `Φ^bs-fld = (ℝ·Φ^cnst_0)|_D ×_{(Φ^{ℝ-log})^gp} Φ`) consists exactly of the `IsBsFldDiv`
  elements. This is the content of [EtTh], Proposition 3.4(ii) and Definition 3.6 used in the proof
  quoted above; it is a property of the tempered data `(D, Φ, B, Φ^bs-fld)` (for those data
  `ratOrhd = ℚ_{≥0}·Div(O^⊿_L) ∩ Φ`, and `Φ ∩ ℝ_{≥0}·Div(O^⊿_L)` is the set of least upper bounds of
  its rational multiples), to be verified when the genuine tempered Frobenioid is instantiated.

## Results

For an equivalence `F : C₁ ⥤ C₂` matching the morphism types (`TypeCorresp`, [FrdI],
Theorem 3.4(ii),(iii)) and preserving base-equivalent pairs, with the same properties for `F.inv`:

* `Model.tau_mem_ratOrhd` (**compatibility with the perfection**): the induced order isomorphism
  `τ_X : Φ₁(A_X) → Φ₂(A_{F X})` on zero divisors of pre-steps (`Model.tau`,
  `Iut/Frobenioid/Thm34DivSlim.lean`) maps `ratOrhd` into `ratOrhd`. Proof: the Frobenius square
  `(X → X + d) ≫ φ_n = φ_n ≫ (X^n → X^n + n·d)` and the endomorphism `(1, id, Div_B b, b)` of `X^n`
  (`n·d = Div_B b`) are mapped by `F` to a square with Frobenius degree `m = deg F(φ_n)` and a
  base-identity linear endomorphism, giving `m·τ_X(d) = Div_B(g^* u)`;
* `Model.isBsFldDiv_tau_iff`: `τ_X` preserves and reflects `IsBsFldDiv` (the projective limits);
* `Model.isBsFldDiv_map_iff`: for every morphism `φ`, `Div(F φ)` is `IsBsFldDiv` iff `Div(φ)` is
  (factorization into Frobenius type, pre-step and pull-back, [FrdI], Definition 1.3(iv)(a));
* **[EtTh], Corollary 3.8(i),(ii)** (`Model.isBsFld_map_iff`, and over bases of FSM-type,
  `Model.isBsFld_map_iff_fsm` for slim bases and `Model.isBsFld_map_iff_divSlim` for Div-slim
  bases, [FrdI], Corollary 4.11(ii)): `F` preserves and reflects base-field-theoretic morphisms.
  Slim categories are Frobenius-slim ([FrdI], Definition 3.1(i)); the base `D₀` of [EtTh] is slim
  ([EtTh], Remark 3.7.2).
* `Model.mem_bsFld_mapUnit_iff_fsm`, `Model.map_psiHull_fsm`: the hypothesis `hbs` of
  `Model.mem_bsFld_mapUnit_iff` discharged; `F^birat` maps `Ψ_{C_v}` ([IUTchII], Example 3.2(ii))
  onto `Ψ_{C'_v}`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u u₁ u₂

namespace Model

/-! ### Rational `O^⊿`-divisors and their least upper bounds -/

section Single

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

variable (divB) in
/-- **Zero divisors of the pre-steps of `C^pf` equivalent to endomorphisms in `O^⊿`**: the
`e ∈ Φ(A)` with `n·e = Div_B(b)` for some `n ≥ 1` and `b ∈ B(A)` (then `b ∈ O^⊿`). -/
def ratOrhd (A : D) : Set (Φ.obj A) :=
  {e | e ∈ Φ.pos A ∧ ∃ n : ℕ+, ∃ b : B.obj A, (n : ℕ) • e = divB.app A b}

variable (divB) in
/-- **Zero divisors of projective limits of such pre-steps** ([EtTh], proof of Corollary 3.8):
`d ∈ Φ(A)` is the least upper bound of the elements of `ratOrhd` below it. -/
def IsBsFldDiv {A : D} (d : Φ.obj A) : Prop :=
  d ∈ Φ.pos A ∧ ∀ u ∈ Φ.pos A, (∀ e ∈ ratOrhd divB A, Φ.le e d → Φ.le e u) → Φ.le d u

lemma pb_mem_ratOrhd {A A' : D} (h : A ⟶ A') {e : Φ.obj A'} (he : e ∈ ratOrhd divB A') :
    Φ.pb h e ∈ ratOrhd divB A := by
  obtain ⟨he, n, b, hb⟩ := he
  exact ⟨Φ.pb_mem h he, n, B.pb h b, by rw [divB.natural, ← hb, map_nsmul]⟩

lemma isBsFldDiv_pb {A A' : D} (h : A ⟶ A') [IsIso h] {d : Φ.obj A'}
    (hd : IsBsFldDiv divB d) : IsBsFldDiv divB (Φ.pb h d) := by
  refine ⟨Φ.pb_mem h hd.1, fun u hu hub => ?_⟩
  obtain ⟨u', rfl⟩ := DivMonoid.pb_surj (Φ := Φ) h u
  have hu' : u' ∈ Φ.pos A' := (DivMonoid.pb_mem_iff h).1 hu
  refine (DivMonoid.pb_le_iff h).2 (hd.2 u' hu' fun e he hed => ?_)
  exact (DivMonoid.pb_le_iff h).1
    (hub _ (pb_mem_ratOrhd h he) ((DivMonoid.pb_le_iff h).2 hed))

/-- `IsBsFldDiv` is invariant under pull-back along isomorphisms of the base. -/
lemma isBsFldDiv_pb_iff {A A' : D} (h : A ⟶ A') [IsIso h] {d : Φ.obj A'} :
    IsBsFldDiv divB (Φ.pb h d) ↔ IsBsFldDiv divB d := by
  refine ⟨fun hd => ?_, isBsFldDiv_pb h⟩
  have := isBsFldDiv_pb (inv h) hd
  rwa [GrpOn.pb_inv_pb] at this

variable {Φ' : DivMonoid.{w} D}

variable (divB) in
/-- **The hull `Φ' ⊆ Φ` is the monoid of `IsBsFldDiv` elements** ([EtTh], Definition 3.6(ii),(iv),
Proposition 3.4(ii); see the module docstring): the property of the tempered data used in the
proof of [EtTh], Corollary 3.8(i),(ii). -/
def BsFldChar (ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn) : Prop :=
  ∀ (A : D) (d : Φ.obj A), (∃ y ∈ Φ'.pos A, ιΦ.app A y = d) ↔ IsBsFldDiv divB d

lemma isBsFld_iff_isBsFldDiv {ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn} (h : BsFldChar divB ιΦ)
    {X Y : Model Φ B divB} (φ : X ⟶ Y) : IsBsFld ιΦ φ ↔ IsBsFldDiv divB φ.div :=
  h _ _

end Single

/-! ### Transport by equivalences -/

section Transport

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

section Forward

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) (c : TypeCorresp F)
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
    (F.map φ).base = (F.map φ').base)

include c hbe in
/-- **Compatibility with the perfection** ([FrdI], Theorem 3.4(iii); [EtTh], proof of Corollary
3.8): `τ_X` maps the zero divisors of pre-steps of `C₁^pf` equivalent to `O^⊿`-endomorphisms to
those of `C₂^pf`. -/
theorem tau_mem_ratOrhd (X : Model Φ₁ B₁ divB₁) {d : Φ₁.obj X.base}
    (hd : d ∈ ratOrhd divB₁ X.base) : tau F X d ∈ ratOrhd divB₂ (F.obj X).base := by
  obtain ⟨hd0, n, b, hb⟩ := hd
  let Xn : Model Φ₁ B₁ divB₁ := ⟨X.base, (n : ℕ) • X.α⟩
  have hbpos : divB₁.app X.base b ∈ Φ₁.pos X.base := hb ▸ (Φ₁.pos _).nsmul_mem hd0 _
  -- the endomorphism `(1, id, Div_B b, b)` of `X^n`
  let eb : Xn ⟶ Xn := mk1 (𝟙 _) (divB₁.app _ b) hbpos b (by simp [Xn])
  -- the pre-step `X^n → X^n + n·d`
  let t : Xn ⟶ ⟨X.base, (n : ℕ) • (X.α + d)⟩ :=
    mk1 (𝟙 _) ((n : ℕ) • d) ((Φ₁.pos _).nsmul_mem hd0 _) 0 (by simp [Xn, smul_add])
  let Xd : Model Φ₁ B₁ divB₁ := ⟨X.base, X.α + d⟩
  have hsq : stepOf X d hd0 ≫ frob Xd n = frob X n ≫ t := by
    ext <;> simp [stepOf, frob, t, Xn, Xd]
  have hsq' := congrArg Hom.div (congrArg F.map hsq)
  simp only [F.map_comp, comp_div] at hsq'
  obtain ⟨h0', -⟩ := (isFrobeniusType_iff _).1 ((c.frobType _).1 (frob_isFrobeniusType Xd n))
  obtain ⟨h0, -⟩ := (isFrobeniusType_iff _).1 ((c.frobType _).1 (frob_isFrobeniusType X n))
  have hte : (F.map t).div = (F.map eb).div := by
    rw [div_map_preStep_tau F t (isPreStep_mk1 _ _ _ _ _),
      div_map_preStep_tau F eb (isPreStep_mk1 _ _ _ _ _)]
    change tau F Xn ((n : ℕ) • d) = tau F Xn (divB₁.app _ b)
    rw [hb]
  have hbase : (F.map eb).base = 𝟙 _ := by
    have := hbe eb (𝟙 Xn) rfl
    rwa [F.map_id] at this
  have hdeg : (F.map eb).deg = 1 := ((c.preStep eb).1 (isPreStep_mk1 _ _ _ _ _)).1
  rw [h0', map_zero, zero_add, h0, smul_zero, add_zero, hte,
    div_eq_divB_u (F.map eb) hbase hdeg, ← divB₂.natural,
    ← tau_of_mem F X hd0] at hsq'
  exact ⟨tau_mem F X hd0, (F.map (frob Xd n)).deg, _, hsq'⟩

variable [F.IsEquivalence]

include c hbe in
/-- `τ_X` maps `IsBsFldDiv` elements to `IsBsFldDiv` elements. -/
theorem isBsFldDiv_tau (X : Model Φ₁ B₁ divB₁) {d : Φ₁.obj X.base} (hd : IsBsFldDiv divB₁ d) :
    IsBsFldDiv divB₂ (tau F X d) := by
  have hpre := c.preStep
  refine ⟨tau_mem F X hd.1, fun u₂ hu₂ hub => ?_⟩
  obtain ⟨u, hu, rfl⟩ := tau_surj F hpre X hu₂
  rw [tau_le_iff F hpre X hd.1 hu]
  refine hd.2 u hu fun e he hed => ?_
  rw [← tau_le_iff F hpre X he.1 hu]
  exact hub _ (tau_mem_ratOrhd F c hbe X he) ((tau_le_iff F hpre X he.1 hd.1).2 hed)

include c in
/-- `d = (Base η_X)^* τ^{F⁻¹}_{F X}(τ_X d)` for the unit `η_X : X ≅ F⁻¹(F X)`. -/
lemma pb_unit_tau_inv_tau (X : Model Φ₁ B₁ divB₁) {d : Φ₁.obj X.base}
    (hd : d ∈ Φ₁.pos X.base) :
    Φ₁.pb (F.asEquivalence.unit.app X).base (tau F.inv (F.obj X) (tau F X d)) = d := by
  let s := stepOf X d hd
  have hn := congrArg Hom.div (F.asEquivalence.unit.naturality s)
  have hs : IsPreStep 𝐏₂ (F.map s) := (c.preStep s).1 (stepOf_isPreStep X d hd)
  obtain ⟨hη1, -, hη0⟩ := (isIso_iff (F.asEquivalence.unit.app X)).1 inferInstance
  obtain ⟨hη1', -, hη0'⟩ := (isIso_iff (F.asEquivalence.unit.app ⟨X.base, X.α + d⟩)).1
    inferInstance
  simp only [Functor.id_map, Functor.comp_map, comp_div] at hn
  rw [hη0', map_zero, zero_add, hη1', PNat.one_coe, one_smul, hη0, smul_zero, add_zero] at hn
  have hn' : d = Φ₁.pb (F.asEquivalence.unit.app X).base (F.inv.map (F.map s)).div := hn
  rw [div_map_preStep_tau F.inv (F.map s) hs, ← tau_of_mem F X hd] at hn'
  exact hn'.symm

end Forward

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] (c : TypeCorresp F)
  (c' : TypeCorresp F.inv)
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
    (F.map φ).base = (F.map φ').base)
  (hbe' : ∀ ⦃X Y : Model Φ₂ B₂ divB₂⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
    (F.inv.map φ).base = (F.inv.map φ').base)

include c c' hbe hbe' in
/-- **`τ_X` preserves and reflects the zero divisors of base-field-theoretic pre-steps**. -/
theorem isBsFldDiv_tau_iff (X : Model Φ₁ B₁ divB₁) {d : Φ₁.obj X.base}
    (hd : d ∈ Φ₁.pos X.base) : IsBsFldDiv divB₂ (tau F X d) ↔ IsBsFldDiv divB₁ d := by
  refine ⟨fun h => ?_, isBsFldDiv_tau F c hbe X⟩
  have h' := isBsFldDiv_tau F.inv c' hbe' (F.obj X) h
  have hiso : IsIso (F.asEquivalence.unit.app X).base :=
    ((isIso_iff _).1 (inferInstance : IsIso (F.asEquivalence.unit.app X))).2.1
  have := isBsFldDiv_pb (F.asEquivalence.unit.app X).base h'
  rwa [pb_unit_tau_inv_tau F c X hd] at this

include c c' hbe hbe' in
/-- **`F` preserves and reflects the zero divisors of base-field-theoretic morphisms**: by the
factorization `φ = γ ≫ β ≫ α` (Frobenius type, pre-step, pull-back; [FrdI], Definition
1.3(iv)(a)), `Div(F φ) = (Base F γ)^* τ(Div φ)`. -/
theorem isBsFldDiv_map_iff {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) :
    IsBsFldDiv divB₂ (F.map φ).div ↔ IsBsFldDiv divB₁ φ.div := by
  let X' : Model Φ₁ B₁ divB₁ := ⟨X.base, (φ.deg : ℕ) • X.α⟩
  let Y' : Model Φ₁ B₁ divB₁ := ⟨X.base, Φ₁.pb φ.base Y.α⟩
  let β : X' ⟶ Y' := mk1 (𝟙 _) φ.div φ.div_mem φ.u (by simpa [X', Y'] using φ.rel)
  let α : Y' ⟶ Y := mk1 φ.base 0 (Φ₁.pos _).zero_mem 0 (by simp [Y'])
  have hfac : frob X φ.deg ≫ β ≫ α = φ := by
    ext <;> simp [frob, β, α, X', Y']
  have hβ : IsPreStep 𝐏₁ β := isPreStep_mk1 _ _ _ _ _
  obtain ⟨hγ0, hγi⟩ := (isFrobeniusType_iff _).1 ((c.frobType _).1 (frob_isFrobeniusType X φ.deg))
  obtain ⟨hα1, hα0⟩ := (isPullback_iff _).1 ((c.pullback α).1 ((isPullback_iff _).2 ⟨rfl, rfl⟩))
  have hdiv : (F.map φ).div = Φ₂.pb (F.map (frob X φ.deg)).base (tau F X' φ.div) := by
    have h := congrArg (fun ψ => (F.map ψ).div) hfac
    simp only [F.map_comp, comp_div, hγ0, hα0, hα1, map_zero, zero_add, smul_zero, add_zero,
      PNat.one_coe, one_smul] at h
    rw [div_map_preStep_tau F β hβ] at h
    exact h.symm
  haveI := hγi
  rw [hdiv, isBsFldDiv_pb_iff]
  exact isBsFldDiv_tau_iff F c c' hbe hbe' X' φ.div_mem

variable {Φ₁' : DivMonoid.{w} D₁} {Φ₂' : DivMonoid.{w} D₂} {ιΦ₁ : DivHom Φ₁'.toGrpOn Φ₁.toGrpOn}
  {ιΦ₂ : DivHom Φ₂'.toGrpOn Φ₂.toGrpOn}

include c c' hbe hbe' in
/-- **[EtTh], Corollary 3.8(i),(ii)** (base-field-theoretic morphisms) for model Frobenioids:
an equivalence matching the morphism types and base-equivalent pairs (in both directions)
preserves and reflects the base-field-theoretic morphisms. -/
theorem isBsFld_map_iff (hchar₁ : BsFldChar divB₁ ιΦ₁) (hchar₂ : BsFldChar divB₂ ιΦ₂)
    {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) : IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ) := by
  rw [isBsFld_iff_isBsFldDiv hchar₁, isBsFld_iff_isBsFldDiv hchar₂,
    isBsFldDiv_map_iff F c c' hbe hbe' φ]

end Transport

/-! ### Corollary 3.8(i),(ii) over bases of FSM-type -/

section FSM

variable {D₁ : Type u₁} [Category.{v} D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}
variable {Φ₁' : DivMonoid.{w} D₁} {Φ₂' : DivMonoid.{w} D₂} {ιΦ₁ : DivHom Φ₁'.toGrpOn Φ₁.toGrpOn}
  {ιΦ₂ : DivHom Φ₂'.toGrpOn Φ₂.toGrpOn}

/-- **[EtTh], Corollary 3.8(i)** over slim bases of FSM-type (slim categories are
Frobenius-slim, [FrdI], Definition 3.1(i); the base `D₀` of [EtTh] is slim, Remark 3.7.2):
every equivalence preserves and reflects the base-field-theoretic morphisms. -/
theorem isBsFld_map_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (hchar₁ : BsFldChar divB₁ ιΦ₁)
    (hchar₂ : BsFldChar divB₂ ιΦ₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
    [F.IsEquivalence] {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) :
    IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ) :=
  isBsFld_map_iff F (typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F)
    (typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv)
    (fun _ _ φ φ' => (base_eq_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ F φ φ').1)
    (fun _ _ φ φ' => (base_eq_iff_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ hS₂ hS₁ F.inv φ φ').1)
    hchar₁ hchar₂ φ

/-- **[EtTh], Corollary 3.8(ii)** (base-field-theoretic morphisms) over Div-slim bases of FSM-type
([FrdI], Corollary 4.11(ii), `Model.base_map_eq_of_base_eq_divSlim`). -/
theorem isBsFld_map_iff_divSlim (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hgd₁ : Φ₁.GoodDiv) (hgd₂ : Φ₂.GoodDiv) (hA₁ : Φ₁.AutFaithful) (hA₂ : Φ₂.AutFaithful)
    (hchar₁ : BsFldChar divB₁ ιΦ₁) (hchar₂ : BsFldChar divB₂ ιΦ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] {X Y : Model Φ₁ B₁ divB₁}
    (φ : X ⟶ Y) : IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ) :=
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have c' := typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv
  isBsFld_map_iff F c c' (fun _ _ φ φ' => base_map_eq_of_base_eq_divSlim F c hgd₁ hgd₂ hA₂ φ φ')
    (fun _ _ φ φ' => base_map_eq_of_base_eq_divSlim F.inv c' hgd₂ hgd₁ hA₁ φ φ') hchar₁ hchar₂ φ

/-- **The hypothesis `hbs` of `Model.mem_bsFld_mapUnit_iff` discharged** ([EtTh], Corollary 3.8(i)):
over slim bases of FSM-type, `F^birat` maps `{b : Div(b) ∈ Φ^bs-fld}` onto the same set. -/
theorem mem_bsFld_mapUnit_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (hchar₁ : BsFldChar divB₁ ιΦ₁)
    (hchar₂ : BsFldChar divB₂ ιΦ₂)
    (hpos₁ : ∀ A x, x ∈ Φ₁'.pos A → ιΦ₁.app A x ∈ Φ₁.pos A)
    (hpos₂ : ∀ A x, x ∈ Φ₂'.pos A → ιΦ₂.app A x ∈ Φ₂.pos A)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] {Y : Model Φ₁ B₁ divB₁}
    (b : B₁.obj Y.base) :
    (∃ y ∈ Φ₁'.pos Y.base, divB₁.app _ b = ιΦ₁.app _ y) ↔
      ∃ y ∈ Φ₂'.pos (F.obj Y).base, divB₂.app _
        (mapUnit F (preStep_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F) b) = ιΦ₂.app _ y :=
  mem_bsFld_mapUnit_iff F (preStep_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F)
    (base_eq_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ F) hpos₁ hpos₂
    (fun _ _ φ => isBsFld_map_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ hchar₁ hchar₂ F φ) b

variable {B₁' : GrpOn.{w} D₁} {B₂' : GrpOn.{w} D₂} {divB₁' : DivHom B₁' Φ₁'.toGrpOn}
  {divB₂' : DivHom B₂' Φ₂'.toGrpOn} {ιB₁ : DivHom B₁' B₁} {ιB₂ : DivHom B₂' B₂}

/-- **Category-theoreticity of `Ψ_{C_v}`** ([IUTchII], Example 3.2(ii); [EtTh], Corollary
3.8(i)): over slim bases of FSM-type, `F^birat` maps `Ψ_{C_v}(Y) = O^⊿_{C^bs-fld}` (realised in
`O^×(T^÷)`) onto `Ψ_{C'_v}(F Y)`. -/
theorem map_psiHull_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (hchar₁ : BsFldChar divB₁ ιΦ₁)
    (hchar₂ : BsFldChar divB₂ ιΦ₂)
    (hpos₁ : ∀ A x, x ∈ Φ₁'.pos A → ιΦ₁.app A x ∈ Φ₁.pos A)
    (hpos₂ : ∀ A x, x ∈ Φ₂'.pos A → ιΦ₂.app A x ∈ Φ₂.pos A)
    (hdiv₁ : ∀ A x, divB₁.app A (ιB₁.app A x) = ιΦ₁.app A (divB₁'.app A x))
    (hdiv₂ : ∀ A x, divB₂.app A (ιB₂.app A x) = ιΦ₂.app A (divB₂'.app A x))
    (hιΦ₁ : ∀ A, Function.Injective (ιΦ₁.app A)) (hιΦ₂ : ∀ A, Function.Injective (ιΦ₂.app A))
    (hfib₁ : ∀ A (b : B₁.obj A) (y : Φ₁'.obj A), divB₁.app A b = ιΦ₁.app A y →
      ∃ b' : B₁'.obj A, ιB₁.app A b' = b)
    (hfib₂ : ∀ A (b : B₂.obj A) (y : Φ₂'.obj A), divB₂.app A b = ιΦ₂.app A y →
      ∃ b' : B₂'.obj A, ιB₂.app A b' = b)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] {Y : Model Φ₁ B₁ divB₁}
    (b : B₁.obj Y.base) :
    b ∈ psiHull (divB' := divB₁') ιB₁ Y.base ↔
      mapUnit F (preStep_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F) b ∈
        psiHull (divB' := divB₂') ιB₂ (F.obj Y).base := by
  rw [mem_psiHull_iff hdiv₁ hιΦ₁ hfib₁, mem_psiHull_iff hdiv₂ hιΦ₂ hfib₂]
  exact mem_bsFld_mapUnit_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ hchar₁ hchar₂ hpos₁
    hpos₂ F b

end FSM

end Model

end Frobenioid

end Iut
