/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EnvTransport

/-!
# Self-equivalences over the identity of the base ([IUTchI], Corollary 5.3(iv), injectivity)

[IUTchI], Corollary 5.3(iv) (l.8251–8254 of `~/iut-scratch/wall/txt/Inter-universal Teichmuller
Theory I.txt`): for `v ∈ V^bad` the natural homomorphism `Aut(F_v) → Aut(D_v)` is bijective. The
proof of injectivity (l.8278–8310): let `α ∈ Ker(Aut(F_v) → Aut(D_v))`, without loss of generality
lying over the identity self-equivalence of `D_v`; "to show that `α` is [isomorphic to] the identity
self-equivalence of `F_v`, it suffices to verify that `α` induces the identity on the rational
function and divisor monoids of `F_v`. Indeed, [...] since `F_v` is a Frobenioid of model type
[...] `α` preserves base-Frobenius pairs. Thus, once one shows that `α` induces the identity on the
rational function and divisor monoids of `F_v`, it follows, by arguing as in the construction of the
equivalence of categories given in the proof of [FrdI], Theorem 5.2(iv), that the various units
obtained in [FrdI], Proposition 5.6, determine an isomorphism between `α` and the identity
self-equivalence of `F_v`". The two remaining steps of the proof (identity on rational functions by
the naturality and injectivity of the Kummer map, [EtTh], Theorem 5.6, Proposition 5.5,
Proposition 3.2(iii); identity on the divisor monoid via the divisors of the theta function and of
functions supported on torsion points) are geometric inputs about the genuine `F_v`.

This file proves the claim for an arbitrary model Frobenioid `C = Model Φ B divB` ([FrdI],
Theorem 5.2):

* **`Model.nonempty_iso_id_of_over_id`**: let `F : C ⥤ C` lie over the identity of `D` (natural
  isomorphisms `ε_X : X_D ≅ F(X)_D` with `Base(F φ) = ε_X^{-1} ∘ Base(φ) ∘ ε_Y`), preserve Frobenius
  degrees, induce the identity on zero divisors (`Div(F φ) = ε^* Div(φ)`) and on rational functions
  (`F^birat = ε^*` on `O^×(X^birat) = B(X_D)`). Then `F ≅ 𝟭 C`.

The proof follows the structure indicated in the text. Writing `F` (after the transport along `ε`,
`Model.twistIsoOf`) as a **twist** `X ↦ (X_D, α_X + δ_X)`, `φ ↦ (deg φ, Base φ, Div φ, u_φ + c_φ)`
(`Model.twist`), one has to find `w_X ∈ B(X_D)` with `Div_B(w_X) = −δ_X` and
`c_φ = Base(φ)^* w_Y − deg(φ)·w_X` (then `(1, id, 0, w_X) : X → F X` is a natural isomorphism,
`Model.twistIso`):

* on the base-Frobenius pair `{(A, 0)}` with the morphisms `(n, f, 0, 0)` (the Frobenius-trivial
  objects of [FrdI], Theorem 5.2 proof), `w_{(A,0)} = −c(φ_2)` for the Frobenius endomorphism
  `φ_2 = (2, id, 0, 0)` works
  because `F(φ_n)` commutes with `F(φ_2)` and `F(1, f, 0, 0)` intertwines
  them: this is the uniqueness of base-Frobenius pairs up to units ([FrdI], Proposition 5.6, the
  argument of `Model.baseFrobPair_unique`), i.e. "the units obtained in Proposition 5.6";
* for an arbitrary object `X = (A, p − q)` one uses the pre-steps `(A, −q) → X`, `(A, −q) → (A, 0)`
  ("`FP`-paths" of the proof of [FrdI], Theorem 5.2(iv)), on which `c` only depends on the base
  (this is "identity on rational functions": `F^birat(u_s − u_t) = u_{F s} − u_{F t}`,
  `Model.mapUnit_u_sub`);
* every morphism factors as a base-identity morphism followed by a pull-back morphism
  `(1, f, 0, 0)`, and both are compared with the base-Frobenius pair through commutative squares
  of pre-steps.

* `Model.addHom_eq_id_of_fix`: the divisor step of the proof (identity on principal divisors and
  compatibility with the cuspidal / non-cuspidal decomposition give the identity on `Φ^gp` when
  every divisor has a positive multiple that is a sum of such components).

The hypotheses `hdiv` (identity on divisor monoids) and `hunit` (identity on rational functions)
are the inputs supplied in [IUTchI] by [EtTh] for the genuine tempered Frobenioid; the surjectivity
half of Corollary 5.3(iv) uses [AbsTopIII], Theorem 1.9.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### Twists of the identity functor -/

section Twist

variable (δ : ∀ X : Model Φ B divB, Φ.obj X.base)
  (c : ∀ {X Y : Model Φ B divB}, (X ⟶ Y) → B.obj X.base)
  (hrel : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y),
    (φ.deg : ℕ) • δ X = Φ.pb φ.base (δ Y) + divB.app _ (c φ))
  (hid : ∀ X : Model Φ B divB, c (𝟙 X) = 0)
  (hcomp : ∀ {X Y Z : Model Φ B divB} (φ : X ⟶ Y) (ψ : Y ⟶ Z),
    c (φ ≫ ψ) = B.pb φ.base (c ψ) + (ψ.deg : ℕ) • c φ)

/-- **The twist** of the identity functor by `(δ, c)`: `X ↦ (X_D, α_X + δ_X)`,
`φ ↦ (deg φ, Base φ, Div φ, u_φ + c_φ)`. -/
def twist : Model Φ B divB ⥤ Model Φ B divB where
  obj X := ⟨X.base, X.α + δ X⟩
  map {X Y} φ := ⟨φ.deg, φ.base, φ.div, φ.div_mem, φ.u + c φ, by
    have h₁ := φ.rel
    have h₂ := hrel φ
    rw [smul_add, map_add, map_add]
    linear_combination (norm := abel) h₁ + h₂⟩
  map_id X := hom_ext rfl rfl rfl (by
    change (0 : B.obj X.base) + c (𝟙 X) = 0
    rw [hid, add_zero])
  map_comp {X Y Z} φ ψ := hom_ext rfl rfl rfl (by
    change B.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u + c (φ ≫ ψ) =
      B.pb φ.base (ψ.u + c ψ) + (ψ.deg : ℕ) • (φ.u + c φ)
    rw [hcomp, map_add, smul_add]
    abel)

@[simp] lemma twist_obj (X : Model Φ B divB) :
    (twist δ c hrel hid hcomp).obj X = ⟨X.base, X.α + δ X⟩ := rfl

@[simp] lemma twist_map_u {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((twist δ c hrel hid hcomp).map φ).u = φ.u + c φ := rfl

@[simp] lemma twist_map_base {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((twist δ c hrel hid hcomp).map φ).base = φ.base := rfl

@[simp] lemma twist_map_deg {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((twist δ c hrel hid hcomp).map φ).deg = φ.deg := rfl

@[simp] lemma twist_map_div {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((twist δ c hrel hid hcomp).map φ).div = φ.div := rfl

/-! #### The base-Frobenius pair and `FP`-paths -/

/-- The Frobenius endomorphism `(n, id, 0, 0)` of `(A, 0)`. -/
def frZ (A : D) (n : ℕ+) : (⟨A, 0⟩ : Model Φ B divB) ⟶ ⟨A, 0⟩ :=
  mk' n (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp)

@[simp] lemma frZ_base (A : D) (n : ℕ+) :
    (frZ (Φ := Φ) (B := B) (divB := divB) A n).base = 𝟙 A := rfl

@[simp] lemma frZ_deg (A : D) (n : ℕ+) : (frZ (Φ := Φ) (B := B) (divB := divB) A n).deg = n := rfl

@[simp] lemma frZ_div (A : D) (n : ℕ+) : (frZ (Φ := Φ) (B := B) (divB := divB) A n).div = 0 := rfl

@[simp] lemma frZ_u (A : D) (n : ℕ+) : (frZ (Φ := Φ) (B := B) (divB := divB) A n).u = 0 := rfl

/-- The pull-back morphism `(1, f, 0, 0) : (A, 0) → (A', 0)`. -/
def pfZ {A A' : D} (f : A ⟶ A') : (⟨A, 0⟩ : Model Φ B divB) ⟶ ⟨A', 0⟩ :=
  mk1 f 0 (Φ.pos _).zero_mem 0 (by simp)

@[simp] lemma pfZ_base {A A' : D} (f : A ⟶ A') :
    (pfZ (Φ := Φ) (B := B) (divB := divB) f).base = f := rfl

@[simp] lemma pfZ_deg {A A' : D} (f : A ⟶ A') :
    (pfZ (Φ := Φ) (B := B) (divB := divB) f).deg = 1 := rfl

@[simp] lemma pfZ_div {A A' : D} (f : A ⟶ A') :
    (pfZ (Φ := Φ) (B := B) (divB := divB) f).div = 0 := rfl

@[simp] lemma pfZ_u {A A' : D} (f : A ⟶ A') :
    (pfZ (Φ := Φ) (B := B) (divB := divB) f).u = 0 := rfl

/-- A decomposition `α_X = p − q`, `p, q ∈ Φ(X_D)`. -/
lemma exists_decomp (X : Model Φ B divB) : ∃ p ∈ Φ.pos X.base, ∃ q ∈ Φ.pos X.base, X.α = p - q :=
  Φ.generating X.α

/-- `p` of the chosen decomposition. -/
noncomputable def decP (X : Model Φ B divB) : Φ.obj X.base := (exists_decomp X).choose

lemma decP_mem (X : Model Φ B divB) : decP X ∈ Φ.pos X.base := (exists_decomp X).choose_spec.1

/-- `q` of the chosen decomposition. -/
noncomputable def decQ (X : Model Φ B divB) : Φ.obj X.base :=
  (exists_decomp X).choose_spec.2.choose

lemma decQ_mem (X : Model Φ B divB) : decQ X ∈ Φ.pos X.base :=
  (exists_decomp X).choose_spec.2.choose_spec.1

lemma decomp_eq (X : Model Φ B divB) : X.α = decP X - decQ X :=
  (exists_decomp X).choose_spec.2.choose_spec.2

/-- The source `(X_D, −q)` of the `FP`-path of `X`. -/
noncomputable abbrev fpObj (X : Model Φ B divB) : Model Φ B divB := ⟨X.base, -decQ X⟩

/-- The pre-step `(X_D, −q) → X` (zero divisor `p`). -/
noncomputable def fpS (X : Model Φ B divB) : fpObj X ⟶ X :=
  mk1 (𝟙 _) (decP X) (decP_mem X) 0 (by
    rw [GrpOn.pb_id', map_zero, add_zero, decomp_eq X]; abel)

/-- The pre-step `(X_D, −q) → (X_D, 0)` (zero divisor `q`). -/
noncomputable def fpT (X : Model Φ B divB) : fpObj X ⟶ (⟨X.base, 0⟩ : Model Φ B divB) :=
  mk1 (𝟙 _) (decQ X) (decQ_mem X) 0 (by simp)

@[simp] lemma fpS_base (X : Model Φ B divB) : (fpS X).base = 𝟙 _ := rfl
@[simp] lemma fpS_deg (X : Model Φ B divB) : (fpS X).deg = 1 := rfl
@[simp] lemma fpT_base (X : Model Φ B divB) : (fpT X).base = 𝟙 _ := rfl
@[simp] lemma fpT_deg (X : Model Φ B divB) : (fpT X).deg = 1 := rfl

variable {δ c}

/-- The correction `w_X = c(s_X) − c(t_X) − c(φ_2)`. -/
noncomputable def corr (X : Model Φ B divB) : B.obj X.base :=
  c (fpS X) - c (fpT X) - c (frZ (Φ := Φ) (B := B) (divB := divB) X.base 2)

/-- The naturality defect `Δ(φ) = c_φ − (Base(φ)^* w_Y − deg(φ)·w_X)`. -/
noncomputable def defect {X Y : Model Φ B divB} (φ : X ⟶ Y) : B.obj X.base :=
  c φ - (B.pb φ.base (corr (c := c) Y) - (φ.deg : ℕ) • corr (c := c) X)

include hcomp in
/-- **The defect is a cocycle**. -/
lemma defect_comp {X Y Z : Model Φ B divB} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    defect (c := c) (φ ≫ ψ) =
      B.pb φ.base (defect (c := c) ψ) + (ψ.deg : ℕ) • defect (c := c) φ := by
  simp only [defect, hcomp, comp_base, comp_deg, GrpOn.pb_comp', map_sub, map_nsmul, PNat.mul_coe,
    mul_smul, smul_sub]
  abel

variable (hc : ∀ {X Y : Model Φ B divB} (s t : X ⟶ Y), IsPreStep (toElem Φ B divB) s →
  IsPreStep (toElem Φ B divB) t →
  s.base = t.base → c s = c t)

lemma isPreStep_of_base_id {A : D} {α β : Φ.obj A}
    (φ : (⟨A, α⟩ : Model Φ B divB) ⟶ ⟨A, β⟩) (h₁ : φ.deg = 1) (h₂ : φ.base = 𝟙 A) :
    IsPreStep 𝐏 φ := by
  refine ⟨h₁, ?_⟩
  change IsIso φ.base
  rw [h₂]
  infer_instance

include hcomp in
/-- Commutation of the Frobenius endomorphisms: `c(φ_n) + c(φ_2) = n·c(φ_2)`. -/
lemma c_frZ (A : D) (n : ℕ+) :
    c (frZ (Φ := Φ) (B := B) (divB := divB) A n) + c (frZ (Φ := Φ) (B := B) (divB := divB) A 2) =
      (n : ℕ) • c (frZ (Φ := Φ) (B := B) (divB := divB) A 2) := by
  have e : frZ (Φ := Φ) (B := B) (divB := divB) A 2 ≫ frZ A n = frZ A n ≫ frZ A 2 := by
    ext <;> simp [frZ, mul_comm]
  have h := congrArg c e
  rw [hcomp, hcomp] at h
  simp only [frZ, mk'_base, GrpOn.pb_id', mk'_deg] at h
  change c (frZ A n) + (n : ℕ) • c (frZ A 2) = c (frZ A 2) + ((2 : ℕ+) : ℕ) • c (frZ A n) at h
  rw [show ((2 : ℕ+) : ℕ) = 2 from rfl, two_nsmul] at h
  linear_combination (norm := module) (-1 : ℤ) • h

lemma defect_congr {X Y : Model Φ B divB} {φ φ' : X ⟶ Y} (h : c φ = c φ') (hb : φ.base = φ'.base)
    (hd : φ.deg = φ'.deg) : defect (c := c) φ = defect (c := c) φ' := by
  simp only [defect, h, hb, hd]

lemma isPreStep_fpS (X : Model Φ B divB) : IsPreStep 𝐏 (fpS X) := isPreStep_mk1 _ _ _ _ _

lemma isPreStep_fpT (X : Model Φ B divB) : IsPreStep 𝐏 (fpT X) := isPreStep_mk1 _ _ _ _ _

include hc in
/-- On `(A, 0)` the correction is `w = −c(φ_2)`. -/
lemma corr_zero (A : D) :
    corr (c := c) (⟨A, 0⟩ : Model Φ B divB) = -c (frZ (Φ := Φ) (B := B) (divB := divB) A 2) := by
  have h := hc (fpS (⟨A, 0⟩ : Model Φ B divB)) (fpT _) (isPreStep_fpS _) (isPreStep_fpT _) rfl
  simp only [corr, h, sub_self, zero_sub]

include hcomp hc in
/-- **Pre-steps over the identity into `(A, 0)` have no defect.** -/
lemma defect_preT {A : D} {α : Φ.obj A} (ρ : (⟨A, α⟩ : Model Φ B divB) ⟶ ⟨A, 0⟩)
    (h₁ : ρ.deg = 1) (h₂ : ρ.base = 𝟙 A) : defect (c := c) ρ = 0 := by
  have hρ : IsPreStep 𝐏 ρ := isPreStep_of_base_id ρ h₁ h₂
  have e := hc (fpS (⟨A, α⟩ : Model Φ B divB) ≫ ρ) (fpT _)
    (isPreStep_comp₀ (isPreStep_fpS _) hρ) (isPreStep_fpT _) (by simp [fpS, fpT, h₂])
  rw [hcomp] at e
  change B.pb (𝟙 _) (c ρ) + (ρ.deg : ℕ) • c (fpS _) = c (fpT _) at e
  have hz := corr_zero (c := c) hc A
  simp only [defect, corr, h₂, h₁, GrpOn.pb_id', PNat.one_coe, one_smul] at e hz ⊢
  rw [hz]
  linear_combination (norm := abel) e

include hcomp hc in
lemma defect_fpT (X : Model Φ B divB) : defect (c := c) (fpT X) = 0 :=
  defect_preT hcomp hc (fpT X) rfl rfl

include hcomp hc in
lemma defect_fpS (X : Model Φ B divB) : defect (c := c) (fpS X) = 0 := by
  have h1 := defect_fpT hcomp hc X
  have hz := corr_zero (c := c) hc X.base
  simp only [defect, corr, fpS, fpT, mk1_base, mk1_deg, GrpOn.pb_id', PNat.one_coe, one_smul]
    at h1 hz ⊢
  rw [hz] at h1
  linear_combination (norm := abel) h1

include hcomp hc in
/-- **Pre-steps over the identity have no defect** (`c` only depends on the base for pre-steps:
"identity on rational functions"). -/
lemma defect_pre {A : D} {α β : Φ.obj A} (s : (⟨A, α⟩ : Model Φ B divB) ⟶ ⟨A, β⟩)
    (h₁ : s.deg = 1) (h₂ : s.base = 𝟙 A) : defect (c := c) s = 0 := by
  let P : Model Φ B divB := ⟨A, α⟩
  let Q : Model Φ B divB := ⟨A, β⟩
  let W : Model Φ B divB := ⟨A, -decQ P - decQ Q⟩
  let a : W ⟶ fpObj P := mk1 (𝟙 _) (decQ Q) (decQ_mem Q) 0 (by simp [W])
  let b : W ⟶ fpObj Q := mk1 (𝟙 _) (decQ P) (decQ_mem P) 0 (by simp [W]; try abel)
  have hs : IsPreStep 𝐏 s := isPreStep_of_base_id s h₁ h₂
  have ha : IsPreStep 𝐏 a := isPreStep_mk1 _ _ _ _ _
  have hb : IsPreStep 𝐏 b := isPreStep_mk1 _ _ _ _ _
  have e := hc (a ≫ fpS P ≫ s) (b ≫ fpS Q)
    (isPreStep_comp₀ ha (isPreStep_comp₀ (isPreStep_fpS _) hs))
    (isPreStep_comp₀ hb (isPreStep_fpS _)) (by simp [a, b, fpS, h₂, W, P, Q])
  have e' := defect_congr (c := c) e (by simp [a, b, fpS, h₂, W, P, Q]) (by simp [a, b, fpS, h₁])
  -- `Δ a = 0`, `Δ b = 0` through the pre-steps into `(A, 0)`.
  have haT := defect_preT hcomp hc (a ≫ fpT P) (by simp [a, fpT]) (by simp [a, fpT, W, P])
  have hbT := defect_preT hcomp hc (b ≫ fpT Q) (by simp [b, fpT]) (by simp [b, fpT, W, Q])
  rw [defect_comp hcomp, defect_fpT hcomp hc] at haT hbT
  simp only [map_zero, zero_add, fpT_deg, PNat.one_coe, one_smul] at haT hbT
  rw [defect_comp hcomp, defect_comp hcomp, defect_comp hcomp, defect_fpS hcomp hc,
    defect_fpS hcomp hc, haT, hbT] at e'
  have hab : a.base = 𝟙 _ := rfl
  have hbb : b.base = 𝟙 _ := rfl
  simp only [hab, hbb, fpS_base, GrpOn.pb_id', h₁, PNat.one_coe, smul_zero, add_zero,
    map_zero] at e'
  exact e'

include hcomp in
/-- **The Frobenius endomorphisms have no defect.** -/
lemma defect_frZ {A : D} (hc' : corr (c := c) (⟨A, 0⟩ : Model Φ B divB) =
      -c (frZ (Φ := Φ) (B := B) (divB := divB) A 2)) (n : ℕ+) :
    defect (c := c) (frZ (Φ := Φ) (B := B) (divB := divB) A n) = 0 := by
  have h := c_frZ hcomp A n
  simp only [defect, hc', frZ_base, frZ_deg, GrpOn.pb_id', smul_neg]
  linear_combination (norm := module) h

include hcomp hc in
/-- **The pull-back morphisms `(1, f, 0, 0)` have no defect**: `F(1, f, 0, 0)` intertwines the
Frobenius endomorphisms. -/
lemma defect_pfZ {A A' : D} (f : A ⟶ A') :
    defect (c := c) (pfZ (Φ := Φ) (B := B) (divB := divB) f) = 0 := by
  have e : pfZ (Φ := Φ) (B := B) (divB := divB) f ≫ frZ A' 2 = frZ A 2 ≫ pfZ f := by
    ext <;> simp [pfZ, frZ]
  have h := congrArg c e
  rw [hcomp, hcomp] at h
  simp only [pfZ_base, frZ_base, pfZ_deg, frZ_deg, GrpOn.pb_id', PNat.one_coe, one_smul] at h
  have hA := corr_zero (c := c) hc A
  have hA' := corr_zero (c := c) hc A'
  simp only [defect, hA, hA', pfZ_base, pfZ_deg, PNat.one_coe, one_smul, map_neg]
  rw [show ((2 : ℕ+) : ℕ) = 2 from rfl, two_nsmul] at h
  linear_combination (norm := abel) h

include hcomp hc in
/-- **Pull-back morphisms `(1, f, 0, 0) : (A, f^* α_Y) → Y` have no defect.** -/
lemma defect_pb {A : D} (Y : Model Φ B divB) (f : A ⟶ Y.base) :
    defect (c := c)
      (mk1 (X := ⟨A, Φ.pb f Y.α⟩) (Y := Y) f 0 (Φ.pos _).zero_mem 0 (by simp)) = 0 := by
  let W' : Model Φ B divB := ⟨A, Φ.pb f (-decQ Y)⟩
  let pfW : W' ⟶ fpObj Y := mk1 f 0 (Φ.pos _).zero_mem 0 (by simp [W'])
  let s' : W' ⟶ ⟨A, Φ.pb f Y.α⟩ := mk1 (𝟙 _) (Φ.pb f (decP Y)) (Φ.pb_mem _ (decP_mem Y)) 0 (by
    rw [decomp_eq Y]; simp [W']; try abel)
  let t' : W' ⟶ ⟨A, 0⟩ := mk1 (𝟙 _) (Φ.pb f (decQ Y)) (Φ.pb_mem _ (decQ_mem Y)) 0 (by simp [W'])
  have e₁ : s' ≫ mk1 (X := ⟨A, Φ.pb f Y.α⟩) (Y := Y) f 0 (Φ.pos _).zero_mem 0 (by simp) =
      pfW ≫ fpS Y := by
    ext <;> simp [s', pfW, fpS]
  have e₂ : t' ≫ pfZ f = pfW ≫ fpT Y := by
    ext <;> simp [t', pfW, fpT, pfZ]
  have d₁ := congrArg (defect (c := c)) e₁
  have d₂ := congrArg (defect (c := c)) e₂
  rw [defect_comp hcomp, defect_comp hcomp, defect_fpS hcomp hc] at d₁
  rw [defect_comp hcomp, defect_comp hcomp, defect_fpT hcomp hc, defect_pfZ hcomp hc,
    defect_pre hcomp hc t' rfl rfl] at d₂
  rw [defect_pre hcomp hc s' rfl rfl] at d₁
  have hs' : s'.base = 𝟙 _ := rfl
  simp only [map_zero, smul_zero, add_zero, zero_add, fpS_deg, fpT_deg, PNat.one_coe,
    one_smul] at d₁ d₂
  rw [hs', GrpOn.pb_id'] at d₁
  rw [d₁]
  exact d₂.symm

include hcomp hc in
/-- **Base-identity morphisms have no defect.** -/
lemma defect_baseId (X : Model Φ B divB) {β : Φ.obj X.base}
    (φ : X ⟶ (⟨X.base, β⟩ : Model Φ B divB)) (hb : φ.base = 𝟙 _) : defect (c := c) φ = 0 := by
  have hrelφ := φ.rel
  rw [hb, GrpOn.pb_id'] at hrelφ
  let R : Model Φ B divB := ⟨X.base, β + (φ.deg : ℕ) • decQ X⟩
  let r₁ : (⟨X.base, β⟩ : Model Φ B divB) ⟶ R :=
    mk1 (𝟙 _) ((φ.deg : ℕ) • decQ X) ((Φ.pos _).nsmul_mem (decQ_mem X) _) 0 (by simp [R])
  let r₂ : (⟨X.base, 0⟩ : Model Φ B divB) ⟶ R :=
    mk1 (𝟙 _) (φ.div + (φ.deg : ℕ) • decP X)
      ((Φ.pos _).add_mem φ.div_mem ((Φ.pos _).nsmul_mem (decP_mem X) _)) φ.u (by
      rw [decomp_eq X] at hrelφ
      simp only [GrpOn.pb_id', zero_add]
      linear_combination (norm := module) hrelφ)
  have e : (fpS X ≫ φ) ≫ r₁ = (fpT X ≫ frZ X.base φ.deg) ≫ r₂ := by
    ext
    · simp [r₁, r₂, fpS, fpT, frZ]
    · simp [r₁, r₂, fpS, fpT, frZ, hb]
    · simp [r₁, r₂, fpS, fpT, frZ, hb]; abel
    · simp [r₁, r₂, fpS, fpT, frZ, hb]
  have d := congrArg (defect (c := c)) e
  have hz := corr_zero (c := c) hc X.base
  rw [defect_comp hcomp, defect_comp hcomp, defect_comp hcomp, defect_comp hcomp,
    defect_pre hcomp hc r₁ rfl rfl, defect_pre hcomp hc r₂ rfl rfl, defect_fpS hcomp hc,
    defect_fpT hcomp hc, defect_frZ hcomp hz] at d
  simpa [r₁, r₂, fpS, fpT, hb] using d

include hcomp hc in
/-- **No morphism has a defect.** -/
theorem defect_eq_zero {X Y : Model Φ B divB} (φ : X ⟶ Y) : defect (c := c) φ = 0 := by
  let φ₁ : X ⟶ (⟨X.base, Φ.pb φ.base Y.α⟩ : Model Φ B divB) :=
    mk' φ.deg (𝟙 _) φ.div φ.div_mem φ.u (by rw [GrpOn.pb_id']; exact φ.rel)
  let φ₂ := mk1 (X := ⟨X.base, Φ.pb φ.base Y.α⟩) (Y := Y) φ.base 0 (Φ.pos _).zero_mem 0
    (by simp)
  have e : φ₁ ≫ φ₂ = φ := by
    ext <;> simp [φ₁, φ₂]
  rw [← e, defect_comp hcomp, defect_pb hcomp hc, defect_baseId hcomp hc X φ₁ rfl]
  simp

include hrel in
/-- `Div_B(w_X) = −δ_X`. -/
lemma divB_corr (X : Model Φ B divB) : divB.app _ (corr (c := c) X) = -δ X := by
  have h₁ := hrel (fpS X)
  have h₂ := hrel (fpT X)
  have h₃ := hrel (frZ (Φ := Φ) (B := B) (divB := divB) X.base 2)
  simp only [fpS_deg, fpS_base, fpT_deg, fpT_base, frZ_deg, frZ_base, GrpOn.pb_id', PNat.one_coe,
    one_smul] at h₁ h₂ h₃
  rw [show ((2 : ℕ+) : ℕ) = 2 from rfl, two_nsmul] at h₃
  simp only [corr, map_sub]
  linear_combination (norm := abel) h₂ - h₁ + h₃

include hrel in
/-- The component `(1, id, 0, w_X) : X → twist X`. -/
noncomputable def twistHom (X : Model Φ B divB) : X ⟶ (twist δ c hrel hid hcomp).obj X :=
  mk1 (𝟙 _) (0 : Φ.obj X.base) (Φ.pos _).zero_mem (corr (c := c) X) (by
    rw [divB_corr hrel X]
    change X.α + 0 = Φ.pb (𝟙 X.base) (X.α + δ X) + -δ X
    rw [GrpOn.pb_id']
    abel)

lemma isIso_twistHom (X : Model Φ B divB) : IsIso (twistHom hrel hid hcomp X) :=
  isIso_of _ rfl (inferInstanceAs (IsIso (𝟙 X.base))) rfl

include hc in
/-- **The twist is isomorphic to the identity** ([FrdI], Theorem 5.2(iv), Proposition 5.6;
[IUTchI], Corollary 5.3(iv)): `(1, id, 0, w_X) : X ≅ twist X`. -/
noncomputable def twistIso : 𝟭 (Model Φ B divB) ≅ twist δ c hrel hid hcomp :=
  NatIso.ofComponents
    (fun X =>
      @asIso _ _ X _ (twistHom hrel hid hcomp X) (isIso_twistHom hrel hid hcomp X))
    (fun {X Y} φ => by
      have h := defect_eq_zero hcomp hc φ
      simp only [defect, sub_eq_zero] at h
      ext
      · simp [twistHom, mul_comm]
      · simp [twistHom]
      · simp [twistHom]
      · simp only [Functor.id_map, asIso_hom, comp_u, twistHom, mk1_u, mk1_base, mk1_deg,
          PNat.one_coe, one_smul, twist_map_u, twist_map_deg]
        erw [GrpOn.pb_id']
        have key : B.pb φ.base (corr (c := c) Y) + φ.u =
            φ.u + c φ + (φ.deg : ℕ) • corr (c := c) X := by
          rw [h]; abel
        exact key)

end Twist

/-! ### Functors over the identity of the base -/

section OverId

variable (F : Model Φ B divB ⥤ Model Φ B divB) (ε : ∀ X : Model Φ B divB, X.base ≅ (F.obj X).base)
  (hε : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y), (F.map φ).base = (ε X).inv ≫ φ.base ≫ (ε Y).hom)
  (hdeg : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y), (F.map φ).deg = φ.deg)
  (hdiv : ∀ {X Y : Model Φ B divB} (φ : X ⟶ Y), (F.map φ).div = Φ.pb (ε X).inv φ.div)

/-- `δ_X = ε^* α_{F X} − α_X`. -/
noncomputable def deltaOf (X : Model Φ B divB) : Φ.obj X.base := Φ.pb (ε X).hom (F.obj X).α - X.α

/-- `c_φ = ε^* u_{F φ} − u_φ`. -/
noncomputable def cOf {X Y : Model Φ B divB} (φ : X ⟶ Y) : B.obj X.base :=
  B.pb (ε X).hom (F.map φ).u - φ.u

include hε in
lemma pb_ε_pb {X Y : Model Φ B divB} (φ : X ⟶ Y) {G : GrpOn.{w} D} (z : G.obj (F.obj Y).base) :
    G.pb (ε X).hom (G.pb (F.map φ).base z) = G.pb φ.base (G.pb (ε Y).hom z) := by
  rw [← GrpOn.pb_comp', ← GrpOn.pb_comp', hε]
  simp

include hε hdeg hdiv in
lemma relOf {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    (φ.deg : ℕ) • deltaOf F ε X = Φ.pb φ.base (deltaOf F ε Y) + divB.app _ (cOf F ε φ) := by
  have h₁ := congrArg (Φ.pb (ε X).hom) (F.map φ).rel
  rw [map_add, map_add, map_nsmul, pb_ε_pb F ε hε φ, hdiv, ← GrpOn.pb_comp', Iso.hom_inv_id,
    GrpOn.pb_id', ← divB.natural, hdeg] at h₁
  have h₂ := φ.rel
  simp only [deltaOf, cOf, smul_sub, map_sub]
  linear_combination (norm := abel) h₁ - h₂

lemma idOf (X : Model Φ B divB) : cOf F ε (𝟙 X) = 0 := by
  simp [cOf]

include hε hdeg in
lemma compOf {X Y Z : Model Φ B divB} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    cOf F ε (φ ≫ ψ) = B.pb φ.base (cOf F ε ψ) + (ψ.deg : ℕ) • cOf F ε φ := by
  simp only [cOf, F.map_comp, comp_u, map_add, map_nsmul, pb_ε_pb F ε hε φ, hdeg, map_sub,
    smul_sub]
  abel

/-- The component `(1, ε_X, 0, 0) : twist X → F X`. -/
noncomputable def twistOfHom (X : Model Φ B divB) :
    (twist (deltaOf F ε) (cOf F ε) (relOf F ε hε hdeg hdiv) (idOf F ε)
      (compOf F ε hε hdeg)).obj X ⟶ F.obj X :=
  mk1 (ε X).hom (0 : Φ.obj X.base) (Φ.pos _).zero_mem (0 : B.obj X.base) (by
    change X.α + deltaOf F ε X + (0 : Φ.obj X.base) =
      Φ.pb (ε X).hom (F.obj X).α + divB.app X.base 0
    rw [map_zero, add_zero, add_zero, deltaOf]
    abel)

lemma isIso_twistOfHom (X : Model Φ B divB) : IsIso (twistOfHom F ε hε hdeg hdiv X) :=
  isIso_of _ rfl (inferInstanceAs (IsIso (ε X).hom)) rfl

/-- **`F` is the twist by `(δ, c)`** (after transport along `ε`). -/
noncomputable def twistIsoOf :
    twist (deltaOf F ε) (cOf F ε) (relOf F ε hε hdeg hdiv) (idOf F ε) (compOf F ε hε hdeg) ≅ F :=
  NatIso.ofComponents
    (fun X =>
      haveI := isIso_twistOfHom F ε hε hdeg hdiv X
      asIso (twistOfHom F ε hε hdeg hdiv X))
    (fun {X Y} φ => by
      ext
      · simp [twistOfHom, hdeg]
      · simp [twistOfHom, hε]
      · simp [twistOfHom, hdiv, ← GrpOn.pb_comp']
      · simp [twistOfHom, cOf])

include hε in
lemma baseEq_iff_of_over ⦃X Y : Model Φ B divB⦄ (φ φ' : X ⟶ Y) :
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base := by
  rw [hε, hε]
  constructor
  · intro h; rw [h]
  · intro h
    simpa using h

include hε hdeg in
lemma preStep_iff_of_over ⦃X Y : Model Φ B divB⦄ (φ : X ⟶ Y) :
    IsPreStep 𝐏 φ ↔ IsPreStep 𝐏 (F.map φ) := by
  change φ.deg = 1 ∧ IsIso φ.base ↔ (F.map φ).deg = 1 ∧ IsIso (F.map φ).base
  rw [hdeg, hε, isIso_comp_left_iff, isIso_comp_right_iff]

include hε hdeg in
/-- **"Identity on rational functions" implies that `c` only depends on the base for pre-steps.** -/
lemma cOf_preStep (hunit : ∀ (X : Model Φ B divB) (x : B.obj X.base),
      mapUnit F (preStep_iff_of_over F ε hε hdeg) x = B.pb (ε X).inv x)
    {X Y : Model Φ B divB} (s t : X ⟶ Y) (hs : IsPreStep 𝐏 s) (ht : IsPreStep 𝐏 t)
    (hb : s.base = t.base) : cOf F ε s = cOf F ε t := by
  have h := mapUnit_u_sub F (preStep_iff_of_over F ε hε hdeg) (baseEq_iff_of_over F ε hε) hs ht hb
  rw [hunit] at h
  have h' := congrArg (B.pb (ε X).hom) h
  rw [← GrpOn.pb_comp', Iso.hom_inv_id, GrpOn.pb_id', map_sub] at h'
  simp only [cOf]
  linear_combination (norm := module) (-1 : ℤ) • h'

include hdiv in
/-- **[IUTchI], Corollary 5.3(iv), injectivity (formal core)**: a self-equivalence (or any
endofunctor) `F` of a model Frobenioid lying over the identity of the base (`ε`, `hε`), preserving
Frobenius degrees, and inducing the identity on the divisor monoid (`hdiv`) and on the rational
function monoid `O^×((−)^birat) = B` (`hunit`), is isomorphic to the identity functor. -/
theorem nonempty_iso_id_of_over_id
    (hunit : ∀ (X : Model Φ B divB) (x : B.obj X.base),
      mapUnit F (preStep_iff_of_over F ε hε hdeg) x = B.pb (ε X).inv x) :
    Nonempty (F ≅ 𝟭 (Model Φ B divB)) :=
  ⟨(twistIsoOf F ε hε hdeg hdiv).symm ≪≫
    (twistIso (relOf F ε hε hdeg hdiv) (idOf F ε) (compOf F ε hε hdeg)
      (cOf_preStep F ε hε hdeg hunit)).symm⟩

end OverId

/-! ### The divisor monoid ([IUTchI], Corollary 5.3(iv), proof, divisor step) -/

/-- **Identity on divisors from identity on principal divisors** ([IUTchI], Corollary 5.3(iv),
proof: "by considering the non-cuspidal portion of the divisor of the Frobenioid-theoretic theta
function and its conjugates [...] In a similar vein, since any divisor of degree zero on an elliptic
curve that is supported on the torsion points of the elliptic curve admits a positive multiple which
is principal, [...] `α` also induces the identity on the cuspidal elements"): let `ρ` be an additive
endomorphism of a torsion-free group `G` (`Φ^gp`) commuting with the cuspidal and non-cuspidal
projections `π_c`, `π_n`, and fixing a subgroup `H` (the principal divisors). If every `x` has a
positive multiple of the form `π_c(h₁) + π_n(h₂)` with `h₁, h₂ ∈ H`, then `ρ = id`. -/
theorem addHom_eq_id_of_fix {G : Type*} [AddCommGroup G]
    (htf : ∀ (n : ℕ) (x : G), 0 < n → n • x = 0 → x = 0) (ρ πc πn : G →+ G)
    (hc : ∀ x, ρ (πc x) = πc (ρ x)) (hn : ∀ x, ρ (πn x) = πn (ρ x)) (H : AddSubgroup G)
    (hH : ∀ h ∈ H, ρ h = h)
    (hgen : ∀ x, ∃ n : ℕ, 0 < n ∧ ∃ h₁ ∈ H, ∃ h₂ ∈ H, n • x = πc h₁ + πn h₂) (x : G) :
    ρ x = x := by
  obtain ⟨n, hn0, h₁, hh₁, h₂, hh₂, e⟩ := hgen x
  have hρ : ρ (n • x) = n • x := by rw [e, map_add, hc, hn, hH _ hh₁, hH _ hh₂]
  rw [map_nsmul] at hρ
  have := htf n (ρ x - x) hn0 (by rw [smul_sub, hρ, sub_self])
  exact sub_eq_zero.1 this

end Model

end Frobenioid

end Iut
