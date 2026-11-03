/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Strip
import Iut.Frobenioid.Angular.Kummer
import Iut.Frobenioid.Angular.Frobenioid

/-!
# The archimedean constituents of prime-strips (MR20 T3-arc)

IUT I, Example 3.4 (i), (ii) (l.5190–5300), Definition 4.1 (i)(b), (iii)(b) (l.6363–6450),
Definition 5.2 (i)(b), (ii)(b) (l.9153–9183) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`. At `v ∈ V^arc`:

* `D_v = X→_v` is an Aut-holomorphic orbispace, `A_{D_v}` its field (a CAF), `C_v` the archimedean
  Frobenioid of [FrdII], Example 3.3 (ii) over the one-morphism category, and
  `κ_v : O^▷(C_v) ↪ A_{D_v}` the **Kummer structure**; `F_v = (C_v, D_v, κ_v)`;
* **`TM^⊢`** ([AbsTopIII], Definition 5.6 (i)): split topological monoids `(C, C→)` with
  `C ≅ O^▷_ℂ` and `C^× × C→ ≅ C`; morphisms are isomorphisms of topological monoids inducing
  `C→₁ ≅ C→₂`; `D^⊢_v` is the object of `TM^⊢` determined by `A_{D_v}`;
* `F^⊢_v = (C^⊢_v = C_v, D^⊢_v, τ^⊢_v)`, `τ^⊢_v` the splitting of `C_v` for which
  `(O^▷(C^⊢_v), τ^⊢_v)` is the object of `TM^⊢` determined by `K_v`.

## Formalisation

* `TMVdash` (objects of `TM^⊢`, with the defining conditions as `Prop` fields; the splitting
  condition is recorded algebraically, as the bijectivity of `C^× × C→ → C`), `TMVdash.Iso`, the
  model `tmModel = (O^▷_ℂ, (0, 1])`.
* `EllSp`: an Aut-holomorphic space `(X, A)` isomorphic to a once-punctured complex torus `E_Λ`
  (MR10's `Ell.IsEllModel`, the output of [AbsTopIII], Corollary 2.7 (a)), with `EllSp.Iso`
  (homeomorphisms that are isomorphisms of Aut-holomorphic spaces).
* **Deviation (H5 of the MR20 plan, accepted temporarily by the lead).** `D_v = X→_v` should be
  the Aut-holomorphic orbispace of `X→_K` at `v`, i.e. determined by the period lattice of `E_v`;
  iut has no complex uniformisation of `E_v`. The model `ellModel` is the once-punctured torus
  `E_{Λ₀}` of the fixed lattice `Λ₀ = ℤ + ℤi` (`lam0`), the same at every `v ∈ V^arc`
  (an abstract once-punctured torus, not tied to `E_v`; and a once-punctured elliptic curve rather
  than the orbispace quotient by `±1`). Follow-up: the period lattice of `E_v` (MR10 side).
* `FArcComp`: a Frobenioid `‡C_v` (`FrobCat`), an `EllSp` `‡D_v` and a Kummer structure
  `κ : O^▷(A) → A_{‡D_v}` at the isotropic objects `A` (for `A_{‡D_v}` the field
  `Ell.EllField` at a point `p`, [AbsTopIII] Corollary 2.7 (e)); `FArcIso`: isomorphisms of
  Frobenioids and of Aut-holomorphic spaces preserving isotropy and `O^▷` and **compatible with the
  Kummer structures**, read through every isomorphism `ψ : ‡D_v ≅ E_Λ` (`Ell.ellEquiv`); the model
  `fArcModel = (C_v, E_{Λ₀}, κ_v)` with `C_v` the Frobenioid of angular regions (`Angular.Obj`,
  `Angular.isFrobenioid`) and `κ_v = Angular.kummerEll` (MR10).
* `FVdashArcComp`: a split Frobenioid and an object of `TM^⊢`; the model
  `fVdashArcModel = ((C_v, τ^⊢_v), tmModel)`, `τ^⊢_v(A) = {e ∈ O^▷(A) : rot(e) = 1}` (the
  endomorphisms with positive real `μ`, i.e. `O^▷(C_v) ∩ ℝ_{>0}`).
* The archimedean constituents of `D`-, `D^⊢`-prime-strips (`DArcComp`, `DVdashArcComp`) are
  `EllSp`, resp. `TM^⊢`-objects isomorphic to the models.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid Iut.AutHol

/-! ### `TM^⊢` -/

/-- **An object of `TM^⊢`** ([AbsTopIII], Definition 5.6 (i); IUT I, Example 3.4 (ii)): a
topological monoid `C ≅ O^▷_ℂ` with a submonoid `C→` such that `C^× × C→ → C` is an
isomorphism. -/
structure TMVdash : Type 1 where
  /-- The topological monoid `C`. -/
  M : Type
  [mon : CommMonoid M]
  [top : TopologicalSpace M]
  /-- The submonoid `C→ ⊆ C`. -/
  ray : Submonoid M
  /-- `C ≅ O^▷_ℂ` as topological monoids. -/
  iso_orhd : Nonempty (M ≃ₜ* Angular.orhdC)
  /-- `C^× × C→ ≅ C`. -/
  split : Function.Bijective (fun x : Mˣ × ray => (x.1 : M) * x.2)

attribute [instance] TMVdash.mon TMVdash.top

/-- **A morphism of `TM^⊢`**: an isomorphism of topological monoids inducing `C→₁ ≅ C→₂`. -/
structure TMVdash.Iso (X Y : TMVdash) where
  /-- The isomorphism of topological monoids. -/
  e : X.M ≃ₜ* Y.M
  /-- It induces `C→₁ ≅ C→₂`. -/
  ray : ∀ x : X.M, x ∈ X.ray ↔ e x ∈ Y.ray

namespace TMVdash.Iso

/-- The identity. -/
def refl (X : TMVdash) : X.Iso X := ⟨ContinuousMulEquiv.refl _, fun _ => Iff.rfl⟩

/-- The inverse. -/
def symm {X Y : TMVdash} (f : X.Iso Y) : Y.Iso X :=
  ⟨f.e.symm, fun y => by rw [f.ray, ContinuousMulEquiv.apply_symm_apply]⟩

/-- The composite. -/
def trans {X Y Z : TMVdash} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z :=
  ⟨f.e.trans g.e, fun x => (f.ray x).trans (g.ray _)⟩

end TMVdash.Iso

section TMModel

open Angular

lemma mem_orhdC {z : ℂ} : z ∈ orhdC ↔ z ≠ 0 ∧ ‖z‖ ≤ 1 := Iff.rfl

/-- `C→ = (0, 1] ⊆ O^▷_ℂ`. -/
def rayC : Submonoid orhdC where
  carrier := {z | 0 < (z : ℂ).re ∧ (z : ℂ).im = 0}
  mul_mem' {a b} ha hb := by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · change 0 < ((a : ℂ) * b).re
      rw [Complex.mul_re, ha2, hb2, mul_zero, sub_zero]
      exact mul_pos ha1 hb1
    · change ((a : ℂ) * b).im = 0
      rw [Complex.mul_im, ha2, hb2, mul_zero, zero_mul, add_zero]
  one_mem' := ⟨by simp, by simp⟩

lemma norm_units_orhdC (u : (orhdC)ˣ) : ‖((u : orhdC) : ℂ)‖ = 1 := by
  have h1 : ‖((u : orhdC) : ℂ)‖ ≤ 1 := (mem_orhdC.mp (u : orhdC).2).2
  have h2 : ‖(((u⁻¹ : (orhdC)ˣ) : orhdC) : ℂ)‖ ≤ 1 :=
    (mem_orhdC.mp ((u⁻¹ : (orhdC)ˣ) : orhdC).2).2
  have h3 : ((u : orhdC) : ℂ) * (((u⁻¹ : (orhdC)ˣ) : orhdC) : ℂ) = 1 :=
    congrArg Subtype.val u.mul_inv
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : orhdC) : ℂ), norm_nonneg (((u⁻¹ : (orhdC)ˣ) : orhdC) : ℂ)]

lemma ray_eq_norm {r : orhdC} (hr : r ∈ rayC) : ((r : ℂ)) = (‖(r : ℂ)‖ : ℂ) := by
  obtain ⟨h1, h2⟩ := hr
  apply Complex.ext
  · rw [Complex.ofReal_re, Complex.norm_eq_sqrt_sq_add_sq, h2]
    simp [Real.sqrt_sq h1.le]
  · rw [Complex.ofReal_im, h2]

/-- The unit `z/|z|` of `O^▷_ℂ`. -/
def unitOf (z : ℂ) (hz : z ≠ 0) : (orhdC)ˣ where
  val := ⟨z / ‖z‖, mem_orhdC.mpr ⟨div_ne_zero hz (by exact_mod_cast (norm_pos_iff.mpr hz).ne'),
    by rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.mpr hz).ne']⟩⟩
  inv := ⟨‖z‖ / z, mem_orhdC.mpr ⟨div_ne_zero (by exact_mod_cast (norm_pos_iff.mpr hz).ne') hz,
    by rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.mpr hz).ne']⟩⟩
  val_inv := Subtype.ext (by
    change z / ‖z‖ * (‖z‖ / z) = 1
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
    field_simp)
  inv_val := Subtype.ext (by
    change ‖z‖ / z * (z / ‖z‖) = 1
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
    field_simp)

/-- `O^▷_ℂ^× × (0, 1] ≅ O^▷_ℂ`. -/
theorem split_orhdC : Function.Bijective (fun x : (orhdC)ˣ × rayC => (x.1 : orhdC) * x.2) := by
  refine ⟨fun ⟨u, r⟩ ⟨u', r'⟩ h => ?_, fun z => ?_⟩
  · have hv : ((u : orhdC) : ℂ) * ((r : orhdC) : ℂ) = ((u' : orhdC) : ℂ) * ((r' : orhdC) : ℂ) :=
      congrArg Subtype.val h
    have hn := congrArg norm hv
    rw [norm_mul, norm_mul, norm_units_orhdC, norm_units_orhdC, one_mul, one_mul] at hn
    have hrr : ((r : orhdC) : ℂ) = ((r' : orhdC) : ℂ) := by
      rw [ray_eq_norm r.2, ray_eq_norm r'.2, hn]
    have hr0 : ((r : orhdC) : ℂ) ≠ 0 := (mem_orhdC.mp (r : orhdC).2).1
    have huu : ((u : orhdC) : ℂ) = ((u' : orhdC) : ℂ) := by
      rw [hrr] at hv hr0
      exact mul_right_cancel₀ hr0 hv
    exact Prod.ext (Units.ext (Subtype.ext huu)) (Subtype.ext (Subtype.ext hrr))
  · obtain ⟨hz0, hz1⟩ := mem_orhdC.mp z.2
    have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz0
    refine ⟨⟨unitOf z hz0, ⟨⟨(‖(z : ℂ)‖ : ℂ), mem_orhdC.mpr ⟨by exact_mod_cast hn.ne',
      by rw [Complex.norm_real, norm_norm]; exact hz1⟩⟩, ⟨by simpa using hn, by simp⟩⟩⟩, ?_⟩
    apply Subtype.ext
    change (z : ℂ) / ‖(z : ℂ)‖ * ‖(z : ℂ)‖ = z
    have : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

end TMModel

/-- **The model object of `TM^⊢`**: `(O^▷_ℂ, (0, 1])`, the object determined by `K_v ≅ ℂ`
(IUT I, Example 3.4 (ii)). -/
def tmModel : TMVdash where
  M := Angular.orhdC
  ray := rayC
  iso_orhd := ⟨ContinuousMulEquiv.refl _⟩
  split := split_orhdC

/-! ### Aut-holomorphic once-punctured tori -/

/-- **An Aut-holomorphic space isomorphic to a once-punctured complex torus** (the `D_v`,
`v ∈ V^arc`, of IUT I, Example 3.4 (i); [AbsTopIII], Corollary 2.7 (a)). -/
structure EllSp : Type 1 where
  /-- The space. -/
  X : Type
  [top : TopologicalSpace X]
  /-- The Aut-holomorphic structure. -/
  A : AutHolStr X
  /-- It is isomorphic to some `E_Λ`. -/
  [ell : Fact (Ell.IsEllModel A)]

attribute [instance] EllSp.top EllSp.ell

/-- **An isomorphism of Aut-holomorphic spaces** ([AbsTopIII], Definition 2.1). -/
structure EllSp.Iso (S T : EllSp) where
  /-- The homeomorphism. -/
  e : S.X ≃ₜ T.X
  /-- It is an isomorphism of Aut-holomorphic spaces. -/
  hol : AutHol.IsIso S.A T.A e

namespace EllSp.Iso

/-- The identity. -/
def refl (S : EllSp) : S.Iso S := ⟨Homeomorph.refl _, AutHol.IsIso.refl _⟩

/-- The inverse. -/
def symm {S T : EllSp} (f : S.Iso T) : T.Iso S := ⟨f.e.symm, f.hol.symm⟩

/-- The composite. -/
def trans {S T U : EllSp} (f : S.Iso T) (g : T.Iso U) : S.Iso U :=
  ⟨f.e.trans g.e, f.hol.trans g.hol⟩

end EllSp.Iso

/-- **The fixed lattice `Λ₀ = ℤ + ℤi`** (deviation H5: the period lattice of `E_v` is not
available in iut). -/
def lam0 : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by rw [← Complex.coe_basisOneI]; exact Complex.basisOneI.linearIndependent

instance : Fact (Ell.IsEllModel (Ell.ellStr lam0)) :=
  ⟨⟨lam0, Homeomorph.refl _, AutHol.IsIso.refl _⟩⟩

/-- **The model `D_v = E_{Λ₀}`** at `v ∈ V^arc` (deviation H5). -/
def ellModel : EllSp := ⟨Ell.punct lam0, Ell.ellStr lam0⟩

/-! ### `F_v` at `v ∈ V^arc` -/

/-- **A constituent `(‡C_v, ‡D_v, ‡κ_v)` of an `F`-prime-strip** at `v ∈ V^arc`, before the
condition "isomorphic to `F_v`" (IUT I, Definition 5.2 (i)(b)): a Frobenioid, an Aut-holomorphic
space and a Kummer structure `κ : O^▷(A) → A_{‡D_v}` at the isotropic objects `A`. -/
structure FArcData : Type 1 where
  /-- The Frobenioid `‡C_v`. -/
  F : FrobCat
  /-- The Aut-holomorphic space `‡D_v`. -/
  S : EllSp
  /-- The Kummer structure (`A_{‡D_v} = Ell.EllField` at `p`). -/
  kappa : ∀ (p : S.X) (A : F.C), IsIsotropic F.P A → Orhd F.P A → Ell.EllField S.A p

/-- **An isomorphism of the collections of data `(C, D, κ)`**: isomorphisms of Frobenioids and of
Aut-holomorphic spaces, preserving isotropic objects and `O^▷` (both directions), compatible with
the Kummer structures read through every isomorphism `ψ : ‡D_v ≅ E_Λ` (both directions). -/
structure FArcData.Iso (X Y : FArcData) where
  /-- The isomorphism of Frobenioids. -/
  F : X.F.Iso Y.F
  /-- The isomorphism of Aut-holomorphic spaces. -/
  S : X.S.Iso Y.S
  map_iso : ∀ A, IsIsotropic X.F.P A → IsIsotropic Y.F.P (F.C.functor.obj A)
  map_orhd : ∀ A (e : A ⟶ A), e ∈ Orhd X.F.P A →
    F.C.functor.map e ∈ Orhd Y.F.P (F.C.functor.obj A)
  inv_iso : ∀ B, IsIsotropic Y.F.P B → IsIsotropic X.F.P (F.C.inverse.obj B)
  inv_orhd : ∀ B (e : B ⟶ B), e ∈ Orhd Y.F.P B →
    F.C.inverse.map e ∈ Orhd X.F.P (F.C.inverse.obj B)
  /-- Compatibility with the Kummer structures. -/
  kappa : ∀ (p : X.S.X) (A : X.F.C) (hA : IsIsotropic X.F.P A) (e : Orhd X.F.P A)
    (L : PeriodPair) (ψ : Y.S.X ≃ₜ Ell.punct L) (hψ : AutHol.IsIso Y.S.A (Ell.ellStr L) ψ),
    Ell.ellEquiv (S.hol.trans hψ) p (X.kappa p A hA e) =
      Ell.ellEquiv hψ (S.e p) (Y.kappa (S.e p) _ (map_iso A hA) ⟨_, map_orhd A e.1 e.2⟩)
  /-- Compatibility of the inverse with the Kummer structures. -/
  kappaInv : ∀ (p : Y.S.X) (B : Y.F.C) (hB : IsIsotropic Y.F.P B) (e : Orhd Y.F.P B)
    (L : PeriodPair) (ψ : X.S.X ≃ₜ Ell.punct L) (hψ : AutHol.IsIso X.S.A (Ell.ellStr L) ψ),
    Ell.ellEquiv (S.hol.symm.trans hψ) p (Y.kappa p B hB e) =
      Ell.ellEquiv hψ (S.e.symm p)
        (X.kappa (S.e.symm p) _ (inv_iso B hB) ⟨_, inv_orhd B e.1 e.2⟩)

namespace FArcData.Iso

/-- The identity. -/
def refl (X : FArcData) : X.Iso X where
  F := FrobCat.Iso.refl _
  S := EllSp.Iso.refl _
  map_iso _ h := h
  map_orhd _ _ h := h
  inv_iso _ h := h
  inv_orhd _ _ h := h
  kappa _ _ _ _ _ _ _ := rfl
  kappaInv _ _ _ _ _ _ _ := rfl

/-- The inverse. -/
def symm {X Y : FArcData} (f : X.Iso Y) : Y.Iso X where
  F := f.F.symm
  S := f.S.symm
  map_iso := f.inv_iso
  map_orhd := f.inv_orhd
  inv_iso := f.map_iso
  inv_orhd := f.map_orhd
  kappa := f.kappaInv
  kappaInv := f.kappa

/-- The composite. -/
def trans {X Y Z : FArcData} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z where
  F := f.F.trans g.F
  S := f.S.trans g.S
  map_iso A h := g.map_iso _ (f.map_iso A h)
  map_orhd A e h := g.map_orhd _ _ (f.map_orhd A e h)
  inv_iso B h := f.inv_iso _ (g.inv_iso B h)
  inv_orhd B e h := f.inv_orhd _ _ (g.inv_orhd B e h)
  kappa p A hA e L ψ hψ :=
    (f.kappa p A hA e L _ (g.S.hol.trans hψ)).trans
      (g.kappa (f.S.e p) _ (f.map_iso A hA) ⟨_, f.map_orhd A e.1 e.2⟩ L ψ hψ)
  kappaInv p B hB e L ψ hψ :=
    (g.kappaInv p B hB e L _ (f.S.hol.symm.trans hψ)).trans
      (f.kappaInv (g.S.e.symm p) _ (g.inv_iso B hB) ⟨_, g.inv_orhd B e.1 e.2⟩ L ψ hψ)

end FArcData.Iso

/-- **The model `F_v = (C_v, D_v, κ_v)`** at `v ∈ V^arc` (IUT I, Example 3.4 (i)): the
Frobenioid of angular regions, `E_{Λ₀}` (deviation H5) and `κ_v = Angular.kummerEll`. -/
def fArcModel : FArcData where
  F := FrobCat.ofModel Angular.Obj Angular.P
  S := ellModel
  kappa p _ hA e := Angular.kummerEll (AutHol.IsIso.refl (Ell.ellStr lam0)) p hA e

/-- **The archimedean `F^⊢_v = (C^⊢_v, D^⊢_v, τ^⊢_v)`** splitting: `τ^⊢_v(A)`, the linear
endomorphisms with `μ ∈ ℝ_{>0}` (`rot = 1`), i.e. `O^▷(C_v) ∩ (0, 1]` (IUT I, Example 3.4 (ii)). -/
def tauArc (A : Angular.Obj) : Set (A ⟶ A) := {e | e.deg = 1 ∧ e.rot = 1}

/-- **The archimedean split Frobenioid `(C^⊢_v, τ^⊢_v)`**. -/
def cArcSplit : SplitFrobCat where
  F := FrobCat.ofModel Angular.Obj Angular.P
  tau := tauArc

/-! ### The constituents at `v ∈ V^arc` -/

/-- **A constituent `†D_v` of a `D`-prime-strip** at `v ∈ V^arc` (IUT I, Definition 4.1 (i)(b)):
an Aut-holomorphic space isomorphic to `D_v` (deviation H5: `D_v = E_{Λ₀}`). -/
structure DArcComp : Type 1 where
  /-- The Aut-holomorphic space. -/
  S : EllSp
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (S.Iso ellModel)

/-- **A constituent `†D^⊢_v` of a `D^⊢`-prime-strip** at `v ∈ V^arc` (IUT I, Definition 4.1
(iii)(b)): an object of `TM^⊢` isomorphic to `D^⊢_v`. -/
structure DVdashArcComp : Type 1 where
  /-- The object of `TM^⊢`. -/
  T : TMVdash
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (T.Iso tmModel)

/-- **A constituent `‡F_v` of an `F`-prime-strip** at `v ∈ V^arc` (IUT I, Definition 5.2
(i)(b)). -/
structure FArcComp : Type 1 where
  /-- The data `(‡C_v, ‡D_v, ‡κ_v)`. -/
  X : FArcData
  /-- They are isomorphic to `F_v`. -/
  equiv_model : Nonempty (X.Iso fArcModel)

/-- **The data `(‡C^⊢_v, ‡D^⊢_v, ‡τ^⊢_v)`** of an `F^⊢`-prime-strip at `v ∈ V^arc`. -/
structure FVdashArcData : Type 1 where
  /-- The split Frobenioid `(‡C^⊢_v, ‡τ^⊢_v)`. -/
  F : SplitFrobCat
  /-- The object `‡D^⊢_v` of `TM^⊢`. -/
  T : TMVdash

/-- Isomorphisms of the data `(C^⊢, D^⊢, τ^⊢)`. -/
structure FVdashArcData.Iso (X Y : FVdashArcData) where
  /-- The isomorphism of split Frobenioids. -/
  F : X.F.Iso Y.F
  /-- The isomorphism in `TM^⊢`. -/
  T : X.T.Iso Y.T

namespace FVdashArcData.Iso

/-- The identity. -/
def refl (X : FVdashArcData) : X.Iso X := ⟨SplitFrobCat.Iso.refl _, TMVdash.Iso.refl _⟩

/-- The inverse. -/
def symm {X Y : FVdashArcData} (f : X.Iso Y) : Y.Iso X := ⟨f.F.symm, f.T.symm⟩

/-- The composite. -/
def trans {X Y Z : FVdashArcData} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z :=
  ⟨f.F.trans g.F, f.T.trans g.T⟩

end FVdashArcData.Iso

/-- **The model `F^⊢_v = (C^⊢_v, D^⊢_v, τ^⊢_v)`** at `v ∈ V^arc` (IUT I, Example 3.4 (ii)). -/
def fVdashArcModel : FVdashArcData := ⟨cArcSplit, tmModel⟩

/-- **A constituent `‡F^⊢_v` of an `F^⊢`-prime-strip** at `v ∈ V^arc` (IUT I, Definition 5.2
(ii)(b)). -/
structure FVdashArcComp : Type 1 where
  /-- The data. -/
  X : FVdashArcData
  /-- They are isomorphic to `F^⊢_v`. -/
  equiv_model : Nonempty (X.Iso fVdashArcModel)

/-- **`F ↦ D`** at `v ∈ V^arc` (IUT I, Remark 5.2.1 (i)): the Aut-holomorphic space. -/
def FArcComp.toD (X : FArcComp) : DArcComp := ⟨X.X.S, X.equiv_model.map fun f => f.S⟩

/-- **`F^⊢ ↦ D^⊢`** at `v ∈ V^arc` (IUT I, Remark 5.2.1 (i)): the object of `TM^⊢`. -/
def FVdashArcComp.toD (X : FVdashArcComp) : DVdashArcComp := ⟨X.X.T, X.equiv_model.map fun f => f.T⟩

end PrimeStrip

end Multiradial

end Iut
