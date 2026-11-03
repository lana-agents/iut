/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Strip

/-!
# `O^{×μ}` with its Galois action and `F^{⊢×μ}`-prime-strips (MR20 T7, non-archimedean part)

IUT II, Definition 4.9 (i), (vi), (vii) (l.11580–11945 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory II.txt`): for `v ∈ V^non`, a
universal covering pro-object `A` of `D^⊢_v` with `G = Aut(A) ≅ G_v` gives the `G`-modules
`O^×(A) ⊇ O^μ(A)` and `O^{×μ}(A) = O^×(A)/O^μ(A)` "equipped with natural `G`-actions"; the
`F^{⊢×μ}`-constituent at `v` is the split-`×μ`-Kummer Frobenioid of the isometries, and an
`F^{⊢×μ}`-prime-strip is a collection of data isomorphic to it at every `v`.

For the model (`\bar{ℚ}_p` with `G_v = Gal(\bar{ℚ}_p / ι K_v)`) the units at the universal covering
pro-object are `O^×_{\bar{ℚ}_p} = {x : ‖x‖ = 1}` with the Galois action. This file builds

* `unitsOneBar p = O^×_{\bar{ℚ}_p}`, `OxMuBar p = O^{×μ}_{\bar{ℚ}_p}` (units of norm one modulo
  torsion), with the **genuine `Gal(\bar{ℚ}_p / K)`-action** (`MulDistribMulAction`, `actQ`; this
  replaces the trivial action `trivialMulDistribMulAction` of `HodgeTheater/PrimeStrip.lean`,
  shell #8);
* `GMObj` (a topological group acting on a commutative monoid, IUT II, Definition 4.9 (i):
  `G ↷ O^{×μ}(A)`), its isomorphisms `GMObj.Iso` (topological isomorphism of groups and an
  equivariant isomorphism of monoids);
* the model `fmuModel D v = (G_v ↷ O^{×μ}_{\bar{ℚ}_p})` at `v ∈ V^non`, the constituents
  `FMuComp D v` and the non-archimedean part `FMuStripNon D` of `F^{⊢×μ}`-prime-strips, with the
  tautological strip `FMuStripNon.ofThetaData`.

**Not done here** (recorded in `MR20-plan.md`): the `×μ`-Kummer structures (`Ism`-orbits, Def 4.9
(i): their construction is MR21), the passage `F^⊢ ↦ F^{⊢×μ}` on abstract split Frobenioids
(evaluation of `O^×(−)` at a universal covering pro-object), `O^⊥`, `O^▶` (Def 4.9 (ii)), the
archimedean constituents (Def 4.9 (v)) and `F^{⊩▶×μ}` (Def 4.9 (viii)).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid

/-! ### `O^×` and `O^{×μ}` of `\bar{ℚ}_p` with the Galois action -/

section Units

variable (p : ℕ) [Fact p.Prime]

/-- **`O^×_{\bar{ℚ}_p}`**: the units of norm one. -/
def unitsOneBar : Subgroup (PadicAlgCl p)ˣ where
  carrier := {x | ‖(x : PadicAlgCl p)‖ = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, norm_mul] at ha hb ⊢
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, norm_inv] at ha ⊢
    rw [ha, inv_one]

/-- **`O^{×μ}_{\bar{ℚ}_p} = O^× / O^μ`** (IUT II, Definition 4.9 (i)). -/
abbrev OxMuBar : Type := unitsOneBar p ⧸ CommGroup.torsion (unitsOneBar p)

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The action of `σ ∈ Gal(\bar{ℚ}_p / K)` on `O^×`. -/
def actU (σ : PAdicGalois.GK p K) : unitsOneBar p →* unitsOneBar p where
  toFun x := ⟨Units.map σ.toRingEquiv.toRingHom.toMonoidHom x, by
    change ‖σ ((x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1
    rw [PAdicGalois.norm_smul]; exact x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

lemma actU_val (σ : PAdicGalois.GK p K) (x : unitsOneBar p) :
    ((actU p K σ x : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      σ ((x : (PadicAlgCl p)ˣ) : PadicAlgCl p) := rfl

lemma actU_one (x : unitsOneBar p) : actU p K 1 x = x := Subtype.ext (Units.ext rfl)

lemma actU_mul (σ τ : PAdicGalois.GK p K) (x : unitsOneBar p) :
    actU p K (σ * τ) x = actU p K σ (actU p K τ x) := Subtype.ext (Units.ext rfl)

/-- The action of `σ` on `O^{×μ}`. -/
def actQ (σ : PAdicGalois.GK p K) : OxMuBar p →* OxMuBar p :=
  QuotientGroup.map _ _ (actU p K σ) fun x hx => by
    rw [Subgroup.mem_comap, CommGroup.mem_torsion] at *
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← map_pow, hxn, map_one]⟩

lemma actQ_mk (σ : PAdicGalois.GK p K) (x : unitsOneBar p) :
    actQ p K σ (QuotientGroup.mk x) = QuotientGroup.mk (actU p K σ x) := rfl

/-- **The Galois action on `O^{×μ}_{\bar{ℚ}_p}`** (IUT II, Definition 4.9 (i): "equipped with
natural `G`-actions"). -/
instance : MulDistribMulAction (PAdicGalois.GK p K) (OxMuBar p) where
  smul σ x := actQ p K σ x
  one_smul x := by
    induction x using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (actU_one p K y)
  mul_smul σ τ x := by
    induction x using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (actU_mul p K σ τ y)
  smul_mul σ x y := map_mul (actQ p K σ) x y
  smul_one σ := map_one (actQ p K σ)

lemma smul_mk (σ : PAdicGalois.GK p K) (x : unitsOneBar p) :
    σ • (QuotientGroup.mk x : OxMuBar p) = QuotientGroup.mk (actU p K σ x) := rfl

end Units

/-! ### `G ↷ M` data and their isomorphisms -/

/-- **`G ↷ M`** (IUT II, Definition 4.9 (i)): a topological group acting on a commutative
monoid. -/
structure GMObj : Type 1 where
  /-- The topological group. -/
  G : Type
  /-- The monoid. -/
  M : Type
  [instGroup : Group G]
  [instTop : TopologicalSpace G]
  [instMonoid : CommMonoid M]
  [instAction : MulDistribMulAction G M]

attribute [instance] GMObj.instGroup GMObj.instTop GMObj.instMonoid GMObj.instAction

/-- **An isomorphism of `G ↷ M` data**: a topological isomorphism of groups and an equivariant
isomorphism of monoids. -/
structure GMObj.Iso (X Y : GMObj) where
  /-- The isomorphism of topological groups. -/
  G : X.G ≃ₜ* Y.G
  /-- The isomorphism of monoids. -/
  M : X.M ≃* Y.M
  /-- Equivariance. -/
  equivariant : ∀ (g : X.G) (m : X.M), M (g • m) = G g • M m

namespace GMObj.Iso

/-- The identity. -/
def refl (X : GMObj) : X.Iso X := ⟨ContinuousMulEquiv.refl _, MulEquiv.refl _, fun _ _ => rfl⟩

/-- The inverse. -/
def symm {X Y : GMObj} (e : X.Iso Y) : Y.Iso X :=
  ⟨e.G.symm, e.M.symm, fun g m => by
    apply e.M.injective
    rw [MulEquiv.apply_symm_apply, e.equivariant, ContinuousMulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]⟩

/-- The composite. -/
def trans {X Y Z : GMObj} (e : X.Iso Y) (f : Y.Iso Z) : X.Iso Z :=
  ⟨e.G.trans f.G, e.M.trans f.M, fun g m => by
    change f.M (e.M (g • m)) = f.G (e.G g) • f.M (e.M m)
    rw [e.equivariant, f.equivariant]⟩

end GMObj.Iso

/-! ### `F^{⊢×μ}`-prime-strips (non-archimedean part) -/

section Strips

variable (D : InitialThetaData.{0})

/-- **The model `G_v ↷ O^{×μ}_{\bar{ℚ}_p}`** at `v ∈ V^non` (IUT II, Definition 4.9 (vi), (vii);
`\bar{ℚ}_p` with `G_v = Gal(\bar{ℚ}_p / ι K_v)` the universal covering pro-object of `D^⊢_v`). -/
def fmuModel (v : Vnon D) : GMObj := ⟨Gv D v, OxMuBar (pv D v)⟩

/-- **A constituent of an `F^{⊢×μ}`-prime-strip** at `v ∈ V^non` (IUT II, Definition 4.9 (vii)),
recorded by its `G ↷ O^{×μ}` data. -/
structure FMuComp (v : Vnon D) : Type 1 where
  /-- The `G ↷ O^{×μ}` data. -/
  X : GMObj
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (X.Iso (fmuModel D v))

/-- **The non-archimedean part of an `F^{⊢×μ}`-prime-strip** (IUT II, Definition 4.9 (vii)). -/
structure FMuStripNon : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, FMuComp D v

variable {D}

/-- **Isomorphisms of `F^{⊢×μ}`-prime-strips** (constituentwise). -/
def FMuStripNon.Iso (P Q : FMuStripNon D) : Type := ∀ v, (P.comp v).X.Iso (Q.comp v).X

variable (D)

/-- **The tautological `F^{⊢×μ}`-prime-strip**. -/
def FMuStripNon.ofThetaData : FMuStripNon D := ⟨fun v => ⟨fmuModel D v, ⟨GMObj.Iso.refl _⟩⟩⟩

/-- **Any two `F^{⊢×μ}`-prime-strips are isomorphic** (through the models). -/
theorem FMuStripNon.nonempty_iso (P Q : FMuStripNon D) : Nonempty (P.Iso Q) :=
  ⟨fun v => ((P.comp v).equiv_model.some).trans ((Q.comp v).equiv_model.some.symm)⟩

end Strips

end PrimeStrip

end Multiradial

end Iut
