/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Full

/-!
# `O^⊥`, `O^▶` and `F^{⊢▶×μ}`-prime-strips (MR20 T7; IUT II, Definition 4.9 (ii)–(vii))

IUT II, Definition 4.9 (ii) (l.11665–11700 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory II.txt`): for `w ∈ V^bad` and a
universal covering pro-object `A` of `D^⊢_w` with `G = Aut(A) ≅ G_w`, "the `2l`-torsion subgroup
`μ_{2l}(A) ⊆ O^×(A)` … together with the images of the splittings … generate a submonoid
`O^⊥(A) ⊆ O^▷(A)`, whose quotient by `μ_{2l}(A)` we denote by `O^▶(A) = O^⊥(A)/μ_{2l}(A)`",
`O^{▶×μ}(A) = O^▶(A) × O^{×μ}(A)`, "all equipped with natural `G`-actions"; (iv) the same at
`V^good ∩ V^non` (splitting by `p_w`), (v) at `V^arc`, (vi), (vii) the `F^{⊢▶×μ}`-prime-strips.

For the models (`\bar{ℚ}_p`, `G_v = Gal(\bar{ℚ}_p / ι K_v)`, the splitting `τ^ℕ` of `C^⊢_v`,
`τ = q̲_v` at `V^bad`, `p` at `V^good`):

* `tauElt_fixed`: `τ` is `G_v`-invariant; `ord_pMul`: `ord(p) = 1`;
  **`tauVdash_isCharSplitting_good`**: `τ^⊢_v = p^ℕ` is a characteristic splitting of `C^⊢_v` at
  `V^good ∩ V^non` (IUT I, Example 3.3 (i));
* `oPerp N τ = ⟨μ_N, τ⟩ ⊆ \bar{ℚ}_p^×`, `oBlack N τ = O^⊥/μ_N` (its image in `\bar{ℚ}_p^×/μ_N`),
  **`oBlack_eq_powers`** (`O^▶ = τ^ℕ`), the Galois action `actBlack` on `\bar{ℚ}_p^×/μ_N` and
  **`actBlack_oBlack`**: the natural `G_v`-action on `O^▶` is trivial;
* the model `fBlackModel D v = (G_v ↷ O^▶ × O^{×μ})` (`N = 2l`), the archimedean model
  `{1} ↷ (0, 1] × S¹/μ_∞` (the splitting monoid of `TM^⊢` and the units modulo torsion), the
  constituents and **`F^{⊢▶×μ}`-prime-strips** (`FBlackStrip`) with isomorphisms and the
  tautological strip.

Not done (MR20 plan): `F^{⊩▶×μ}`-prime-strips (Definition 4.9 (viii), the `F^⊩` data with an
`F^{⊢▶×μ}`-strip), the passages `F^⊢ ↦ F^{⊢▶×μ}`, `F^⊢ ↦ F^{⊢×μ}` on abstract split Frobenioids,
and the `×μ`-Kummer structures (`Ism`-orbits, MR21).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid

/-! ### `τ` is Galois-invariant; the splitting at `V^good` -/

section Tau

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

lemma pMul_fixed (σ : Gv D v) : σ • pMul D v = pMul D v := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change σ (algebraMap ℚ_[pv D v] (PadicAlgCl (pv D v)) (pv D v)) =
    algebraMap ℚ_[pv D v] (PadicAlgCl (pv D v)) (pv D v)
  have h := σ.commutes (algebraMap ℚ_[pv D v] (Lv D v) (pv D v))
  rwa [← IsScalarTower.algebraMap_apply] at h

/-- **`τ` is `G_v`-invariant.** -/
lemma tauElt_fixed (σ : Gv D v) : σ • tauElt D v = tauElt D v := by
  unfold tauElt
  split_ifs with hv
  · exact toMul_fixed D v σ _
  · exact pMul_fixed D v σ

/-- **`ord(p) = 1`.** -/
lemma ord_pMul : PAdicGalois.ord (pv D v) (pMul D v) = 1 := by
  have hp : (1 : ℝ) < pv D v := by exact_mod_cast (Fact.out : (pv D v).Prime).one_lt
  change -Real.logb (pv D v) ‖algebraMap ℚ_[pv D v] (PadicAlgCl (pv D v)) (pv D v)‖ = 1
  rw [PadicAlgCl.norm_extends, Padic.norm_p, Real.logb_inv, Real.logb_self_eq_one hp, neg_neg]

/-- **`τ^⊢_v = p^ℕ` is a characteristic splitting of `C^⊢_v`** at `v ∈ V^good ∩ V^non` (IUT I,
Example 3.3 (i): "the splitting determined by `p_v`"). -/
theorem tauVdash_isCharSplitting_good (hv : v ∉ D.VBad) :
    Model.IsCharSplitting
      (divB := divGal (Gv D v) (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
        (gammaVdash D v)) (tauVdash D v) := by
  have hτ : tauElt D v = pMul D v := by simp only [tauElt, dif_neg hv]
  have hΓ : gammaVdash D v = AddSubgroup.zmultiples (PAdicGalois.ord (pv D v) (tauElt D v)) := by
    rw [hτ, ord_pMul]; simp [gammaVdash, ordTau, hv]
  refine GaloisModel.isCharSplitting_piSplit _ (fun σ => tauElt_fixed D v σ) ?_ hΓ
  rw [hτ, ord_pMul]; exact one_pos

end Tau

/-! ### `O^⊥` and `O^▶` -/

section Black

variable (p : ℕ) [Fact p.Prime] (N : ℕ)

/-- **`O^⊥ = ⟨μ_N, τ⟩ ⊆ \bar{ℚ}_p^×`** (IUT II, Definition 4.9 (ii)). -/
def oPerp (τ : (PadicAlgCl p)ˣ) : Submonoid (PadicAlgCl p)ˣ :=
  Submonoid.closure ((rootsOfUnity N (PadicAlgCl p) : Set (PadicAlgCl p)ˣ) ∪ {τ})

/-- `\bar{ℚ}_p^× / μ_N`. -/
abbrev UnitsModMu : Type := (PadicAlgCl p)ˣ ⧸ rootsOfUnity N (PadicAlgCl p)

/-- **`O^▶ = O^⊥/μ_N`** (IUT II, Definition 4.9 (ii)), as the image of `O^⊥` in
`\bar{ℚ}_p^×/μ_N` (`μ_N ⊆ O^⊥`). -/
def oBlack (τ : (PadicAlgCl p)ˣ) : Submonoid (UnitsModMu p N) :=
  (oPerp p N τ).map (QuotientGroup.mk' (rootsOfUnity N (PadicAlgCl p)))

/-- **`O^▶ = τ^ℕ`**. -/
theorem oBlack_eq_powers (τ : (PadicAlgCl p)ˣ) :
    oBlack p N τ = Submonoid.powers (QuotientGroup.mk τ : UnitsModMu p N) := by
  refine le_antisymm (Submonoid.map_le_iff_le_comap.mpr (Submonoid.closure_le.mpr ?_))
    ((Submonoid.powers_le).mpr ⟨τ, Submonoid.subset_closure (Or.inr rfl), rfl⟩)
  rintro x (hx | hx)
  · refine ⟨0, ?_⟩
    change (QuotientGroup.mk τ : UnitsModMu p N) ^ 0 = QuotientGroup.mk x
    rw [pow_zero]
    exact ((QuotientGroup.eq_one_iff x).mpr hx).symm
  · rw [Set.mem_singleton_iff.mp hx]
    exact ⟨1, pow_one _⟩

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The action of `σ ∈ Gal(\bar{ℚ}_p / K)` on `\bar{ℚ}_p^×/μ_N`. -/
def actBlack (σ : PAdicGalois.GK p K) : UnitsModMu p N →* UnitsModMu p N :=
  QuotientGroup.map _ _ (Units.map σ.toRingEquiv.toRingHom.toMonoidHom) fun ζ hζ => by
    rw [Subgroup.mem_comap, mem_rootsOfUnity] at *
    rw [← map_pow, hζ, map_one]

/-- **The natural Galois action on `O^▶` is trivial** when `τ` is `Gal(\bar{ℚ}_p / K)`-invariant
(`τ ∈ K`). -/
theorem actBlack_oBlack (τ : (PadicAlgCl p)ˣ) (σ : PAdicGalois.GK p K)
    (hτ : Units.map σ.toRingEquiv.toRingHom.toMonoidHom τ = τ) {x : UnitsModMu p N}
    (hx : x ∈ oBlack p N τ) : actBlack p N K σ x = x := by
  rw [oBlack_eq_powers] at hx
  obtain ⟨n, rfl⟩ := hx
  rw [map_pow]
  congr 1
  change QuotientGroup.mk (Units.map σ.toRingEquiv.toRingHom.toMonoidHom τ) = _
  rw [hτ]

end Black

/-! ### `F^{⊢▶×μ}`-prime-strips -/

section Strips

variable (D : InitialThetaData.{0})

/-- `τ ∈ \bar{ℚ}_p^×` at `v ∈ V^non`. -/
def tauUnit (v : Vnon D) : (PadicAlgCl (pv D v))ˣ := Additive.toMul (tauElt D v)

lemma tauUnit_fixed (v : Vnon D) (σ : Gv D v) :
    Units.map σ.toRingEquiv.toRingHom.toMonoidHom (tauUnit D v) = tauUnit D v := by
  apply Units.ext
  change σ ((Additive.toMul (tauElt D v) : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v)) =
    ((Additive.toMul (tauElt D v) : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v))
  rw [← PAdicGalois.smul_toMul (pv D v) (Lv D v) σ (tauElt D v), tauElt_fixed D v σ]

/-- **`O^▶` at `v ∈ V^non`**: `O^⊥/μ_{2l}` for the splitting `τ^ℕ` of `F^⊢_v`. -/
abbrev OBlackV (v : Vnon D) : Type := ↥(oBlack (pv D v) (2 * D.ℓ) (tauUnit D v))

/-- The natural `G_v`-action on `O^▶` (trivial: `actBlack_oBlack`). -/
instance (v : Vnon D) : MulDistribMulAction (Gv D v) (OBlackV D v) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

/-- The `G_v`-action on `O^▶` is the restriction of the Galois action on `\bar{ℚ}_p^×/μ_{2l}`. -/
theorem smul_oBlackV (v : Vnon D) (σ : Gv D v) (x : OBlackV D v) :
    ((σ • x : OBlackV D v) : UnitsModMu (pv D v) (2 * D.ℓ)) =
      actBlack (pv D v) (2 * D.ℓ) (Lv D v) σ x :=
  (actBlack_oBlack _ _ _ _ σ (tauUnit_fixed D v σ) x.2).symm

/-- **The model `G_v ↷ O^{▶×μ} = O^▶ × O^{×μ}`** at `v ∈ V^non` (IUT II, Definition 4.9 (ii),
(iv), (vi)). -/
def fBlackModel (v : Vnon D) : GMObj := ⟨Gv D v, OBlackV D v × OxMuBar (pv D v)⟩

/-- The trivial action of the trivial group. -/
instance : MulDistribMulAction PUnit (rayC × OxMuArc) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

/-- **The archimedean model `{1} ↷ (0, 1] × S¹/μ_∞`** (IUT II, Definition 4.9 (v): the splitting
monoid of the `TM^⊢`-object and the units modulo torsion). -/
def fBlackArcModel : GMObj := ⟨PUnit, rayC × OxMuArc⟩

/-- **A constituent of an `F^{⊢▶×μ}`-prime-strip** at `v ∈ V^non` (IUT II, Definition 4.9
(vii)). -/
structure FBlackComp (v : Vnon D) : Type 1 where
  /-- The `G ↷ O^{▶×μ}` data. -/
  X : GMObj
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (X.Iso (fBlackModel D v))

/-- **A constituent of an `F^{⊢▶×μ}`-prime-strip** at `v ∈ V^arc`. -/
structure FBlackArcComp : Type 1 where
  /-- The data. -/
  X : GMObj
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (X.Iso fBlackArcModel)

/-- **An `F^{⊢▶×μ}`-prime-strip** (IUT II, Definition 4.9 (vii)). -/
structure FBlackStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : ∀ v : Vnon D, FBlackComp D v
  /-- The constituents at `V^arc`. -/
  arc : Varc D → FBlackArcComp

variable {D}

/-- **Isomorphisms of `F^{⊢▶×μ}`-prime-strips** (constituentwise). -/
def FBlackStrip.Iso (P Q : FBlackStrip D) : Type :=
  (∀ v, (P.non v).X.Iso (Q.non v).X) × ∀ v, (P.arc v).X.Iso (Q.arc v).X

namespace FBlackStrip

/-- The identity. -/
def Iso.refl (P : FBlackStrip D) : P.Iso P :=
  ⟨fun _ => GMObj.Iso.refl _, fun _ => GMObj.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : FBlackStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨fun v => (f.1 v).symm, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : FBlackStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨fun v => (f.1 v).trans (g.1 v), fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `F^{⊢▶×μ}`-prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : FBlackStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non v).equiv_model.some).trans (Q.non v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

variable (D)

/-- **The tautological `F^{⊢▶×μ}`-prime-strip**. -/
def ofThetaData : FBlackStrip D :=
  ⟨fun v => ⟨fBlackModel D v, ⟨GMObj.Iso.refl _⟩⟩, fun _ => ⟨fBlackArcModel, ⟨GMObj.Iso.refl _⟩⟩⟩

end FBlackStrip

end Strips

end PrimeStrip

end Multiradial

end Iut
