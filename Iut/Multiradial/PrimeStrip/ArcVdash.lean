/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Arc
import Iut.Multiradial.PrimeStrip.IsoClass
import Iut.Frobenioid.Props

/-!
# `F ↦ F^⊢` at `v ∈ V^arc` (MR21 R6)

IUT I, Example 3.4 (i), (ii) (l.5190–5302 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): `C^⊢_v = C_v`, `τ^⊢_v` is
the splitting of `C_v` for which `(O^▷(C^⊢_v), τ^⊢_v)` is the object of `TM^⊢` determined by
`K_v`, `D^⊢_v` is the object of `TM^⊢` determined by `A_{D_v}`, and "`F^⊢_v` may be
algorithmically reconstructed from `F_v`" (l.5300–5302); Remark 5.2.1 (ii) (l.9827). As at
`V^non` (`VdashRes.lean`), "reconstructed" means preserved by isomorphisms (Remark 3.2.1 (i)): the
content is the action of `Aut(F_v)` on `F^⊢_v`.

* **Kummer compatibility in coordinates** (`FArcData.Iso.val_map`): for an automorphism `f` of
  the model `F_v = (C_v, E_{Λ₀}, κ_v)` (`fArcModel`), an isotropic object `A` and
  `e ∈ O^▷(A)`, the element `μ` of `f(e)` is `c_p(μ(e))`, where `c_p = ellConj f.S p` is the
  automorphism of `ℂ` induced by `f.S` on the field `A_{D_v}` at any point `p`; `c_p` is the
  identity or complex conjugation (MR10's `Ell.ellEquiv_trans_eq`, from
  `Complex.ringHom_eq_id_or_conj_of_continuous`) and does not depend on `p`
  (`FArcData.Iso.ellConj_eq_conjC`).
* **`τ^⊢_v` is preserved** (`FArcData.Iso.mapsSplit_tauArc`): on isotropic objects since
  `c_p` fixes `ℝ_{>0}`; on non-isotropic objects every endomorphism has trivial angular part
  (`Angular.rot_eq_one_of_not_isotropic`), and `f` preserves non-isotropy.
* **Rigidity of the divisor monoid** (`FArcData.Iso.phi_apply`): `f` acts as the identity on
  `Φ_{C_v} = ℝ_{≥0}` (IUT I, Remark 5.2.1 (ii): "the rigidity of the divisor monoids …
  [cf., especially, the topological field structure of the field `A_{D_v}`]"): `Div(f(e)) = Div(e)`
  for `e ∈ O^▷(A)`, since `|c_p(z)| = |z|`.
* **`TM^⊢`**: `tmIsoOfConj c` (the automorphism of `(O^▷_ℂ, (0, 1])` given by `c ∈ {id, conj}`);
  `FArcData.Iso.vdashTM f` is the automorphism of `D^⊢_v` induced by `f`, equal to the one
  induced by `f.S` on `A_{D_v}` at every point (`vdashTM_apply`), and it is **the identity or
  complex conjugation** (`vdashTM_id_or_conj`).
* **`vdashArc : Aut(F_v) → Aut(F^⊢_v)`**, `f ↦ ((C_v, τ^⊢_v) ↦ f.F, vdashTM f)`, a functor:
  `vdashArc_trans`, `vdashArc_refl`.
* **Isomorphism classes** (IUT I, §0): `FArcData.IsoClass` (2-isomorphism of the Frobenioid
  part, `FrobCat.Iso.Rel`, and equality of the maps of Aut-holomorphic spaces),
  `FVdashArcData.IsoClass` (2-isomorphism of the Frobenioid part and equality in `TM^⊢`), the
  groupoid laws, `vdashArcClass` with its functoriality, and `F ↦ F^⊢` on isomorphism classes of
  constituents `‡F_v ≅ ‡F'_v` (`FArcComp.vdashClass`, via chosen isomorphisms with the model, as
  `FComp.vdashClass` at `V^non`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid Iut.AutHol

/-! ### Points and the automorphisms of `A_{D_v}` -/

/-- `E_{Λ₀}` is nonempty (the complement of a point of a torus is connected). -/
lemma nonempty_ellModel : Nonempty ellModel.X :=
  (Ell.isConnected_compl_countable (L := lam0) (Set.countable_singleton 0)).nonempty.to_subtype

/-- A point of `E_{Λ₀}`. -/
def ptE : ellModel.X := Classical.choice nonempty_ellModel

/-- The identity of `E_{Λ₀}`, as an isomorphism with the once-punctured torus `E_{Λ₀}`. -/
lemma isIso_refl_model : AutHol.IsIso ellModel.A (Ell.ellStr lam0) (Homeomorph.refl ellModel.X) :=
  AutHol.IsIso.refl _

/-- **The automorphism of `ℂ` induced by an automorphism `S` of `E_{Λ₀}` on `A_{D_v}` at `p`**:
`ℂ ≅ A_{D_v, p} ≅ ℂ`, the first through the identity, the second through `S`. -/
def ellConj (S : ellModel.Iso ellModel) (p : ellModel.X) : ℂ →+* ℂ :=
  (((Ell.ellEquiv isIso_refl_model p).symm.trans
    (Ell.ellEquiv (S.hol.trans isIso_refl_model) p)) : ℂ →+* ℂ)

/-- `c_p` is the identity or complex conjugation. -/
lemma ellConj_eq (S : ellModel.Iso ellModel) (p : ellModel.X) :
    ellConj S p = RingHom.id ℂ ∨ ellConj S p = starRingEnd ℂ :=
  Ell.ellEquiv_trans_eq _ p _

/-- Two elements of `{id, conj}` agreeing at `i/2` are equal. -/
lemma eq_of_id_or_conj {c c' : ℂ →+* ℂ} (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ)
    (hc' : c' = RingHom.id ℂ ∨ c' = starRingEnd ℂ) (h : c (Complex.I / 2) = c' (Complex.I / 2)) :
    c = c' := by
  have hne : Complex.I / 2 ≠ starRingEnd ℂ (Complex.I / 2) := by
    intro h'
    have := congrArg Complex.im h'
    rw [Complex.conj_im, Complex.div_ofNat_im, Complex.I_im] at this
    norm_num at this
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · rfl
  · exact absurd h hne
  · exact absurd h.symm hne
  · rfl

lemma norm_id_or_conj {c : ℂ →+* ℂ} (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) (z : ℂ) :
    ‖c z‖ = ‖z‖ := by
  rcases hc with rfl | rfl
  · rfl
  · exact Complex.norm_conj z

lemma ofReal_id_or_conj {c : ℂ →+* ℂ} (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) (r : ℝ) :
    c (r : ℂ) = r := by
  rcases hc with rfl | rfl
  · rfl
  · exact Complex.conj_ofReal r

lemma invol_id_or_conj {c : ℂ →+* ℂ} (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) (z : ℂ) :
    c (c z) = z := by
  rcases hc with rfl | rfl
  · rfl
  · exact Complex.conj_conj z

lemma continuous_id_or_conj {c : ℂ →+* ℂ} (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) :
    Continuous c := by
  rcases hc with rfl | rfl
  · exact continuous_id
  · exact Complex.continuous_conj

/-! ### Kummer compatibility in coordinates -/

namespace FArcData.Iso

open Angular

variable (f : FArcData.Iso fArcModel fArcModel)

/-- **Kummer compatibility in coordinates**: `μ(f(e)) = c_p(μ(e))` for `e ∈ O^▷(A)`, `A`
isotropic, at every point `p` (IUT I, Example 3.4 (i): `κ_v : O^▷(C_v) ↪ A_{D_v}`). -/
theorem val_map (p : ellModel.X) (A : Obj) (hA : IsIsotropic P A) (e : Orhd P A) :
    val (f.F.C.functor.map e.1) = ellConj f.S p (val e.1) := by
  have h := f.kappa p A hA e lam0 (Homeomorph.refl _) isIso_refl_model
  exact ((h.trans (ellEquiv_kummerEll (AutHol.IsIso.refl (Ell.ellStr lam0)) (f.S.e p)
    (f.map_iso A hA) ⟨_, f.map_orhd A e.1 e.2⟩)).symm)

/-- The isotropic object `iso 0` (the angular region `S¹ × (0, 1]`). -/
lemma isIsotropic_iso0 : IsIsotropic P (iso 0) := (isIsotropic_iff _).mpr rfl

/-- The endomorphism of `iso 0` with element `z ∈ O^▷_ℂ`. -/
def endOf (z : orhdC) : Orhd P (iso 0) := (orhdEquiv isIsotropic_iso0).symm z

lemma val_endOf (z : orhdC) : val (endOf z).1 = z :=
  congrArg Subtype.val ((orhdEquiv isIsotropic_iso0).apply_symm_apply z)

/-- `i/2 ∈ O^▷_ℂ`. -/
def halfI : orhdC := ⟨Complex.I / 2, by
  refine ⟨by simp, ?_⟩
  rw [norm_div, Complex.norm_I, Complex.norm_two]
  norm_num⟩

/-- **The automorphism `c ∈ {id, conj}` of `ℂ` attached to `f`** (at the point `ptE`). -/
def conjC : ℂ →+* ℂ := ellConj f.S ptE

lemma conjC_eq : f.conjC = RingHom.id ℂ ∨ f.conjC = starRingEnd ℂ := ellConj_eq _ _

/-- **`c_p` does not depend on `p`.** -/
theorem ellConj_eq_conjC (p : ellModel.X) : ellConj f.S p = f.conjC := by
  apply eq_of_id_or_conj (ellConj_eq _ _) f.conjC_eq
  have h1 := f.val_map p _ isIsotropic_iso0 (endOf halfI)
  have h2 := f.val_map ptE _ isIsotropic_iso0 (endOf halfI)
  rw [val_endOf] at h1 h2
  exact h1.symm.trans h2

theorem val_map_conjC (A : Obj) (hA : IsIsotropic P A) (e : Orhd P A) :
    val (f.F.C.functor.map e.1) = f.conjC (val e.1) :=
  f.val_map ptE A hA e

/-- **`f` preserves `τ^⊢_v`** (`deg = 1`, `rot = 1`; IUT I, Example 3.4 (ii)). -/
theorem mapsSplit_tauArc : SplitFrobCat.MapsSplit f.F.C.functor tauArc tauArc := by
  intro A e he
  obtain ⟨hd, hr⟩ := he
  have hdeg : (f.F.C.functor.map e).deg = 1 :=
    (mem_orhd _).mp (f.map_orhd A e ((mem_orhd e).mpr hd))
  refine ⟨hdeg, ?_⟩
  by_cases hA : IsIsotropic P A
  · have h := f.val_map_conjC A hA ⟨e, (mem_orhd e).mpr hd⟩
    have hv : val e = ((Real.exp e.rad : ℝ) : ℂ) := by simp [val, hr]
    rw [hv, ofReal_id_or_conj f.conjC_eq] at h
    have h' : ((Real.exp (f.F.C.functor.map e).rad : ℝ) : ℂ) * ((f.F.C.functor.map e).rot : ℂ) =
        ((Real.exp e.rad : ℝ) : ℂ) * ((1 : Circle) : ℂ) := by
      rw [Circle.coe_one, mul_one]
      exact h
    exact (polar_unique h').2
  · by_cases hFA : IsIsotropic P (f.F.C.functor.obj A)
    · exact absurd (isIsotropic_of_iso (f.F.C.unitIso.app A) (f.inv_iso _ hFA)) hA
    · exact rot_eq_one_of_not_isotropic hFA _

/-- In `F_{ℝ_{≥0}}` over the one-morphism category: endomorphisms conjugate by a morphism of
degree one have the same divisor. -/
lemma div_eq_of_comm {a b : Elem phiReal.{0}} (η : a ⟶ b) (hη : η.deg = 1) (x : a ⟶ a)
    (y : b ⟶ b) (hy : y.deg = 1) (h : x ≫ η = η ≫ y) : x.div = y.div := by
  have h' := congrArg (fun φ : a ⟶ b => (Elem.Hom.div φ).down) h
  simp only [Elem.comp_div, hη, hy, PNat.one_coe, one_smul, ULift.add_down] at h'
  apply ULift.ext
  change η.div.down + x.div.down = y.div.down + η.div.down at h'
  linarith

/-- `f` acts on `Div` of the linear endomorphisms of `iso 0` through `Φ`: `Div(f(e)) = φ(Div(e))`
(compatibility with the structure functors, `commP`). -/
theorem phi_divVal (e : (iso 0 : Obj) ⟶ iso 0) (he : e.deg = 1) :
    f.F.phi (P.obj (iso 0)).base ⟨divVal e⟩ = ⟨divVal (f.F.C.functor.map e)⟩ := by
  set η := (FrobCat.sqIso f.F.commP).hom.app (iso 0) with hη
  have hdeg : η.deg = 1 := by
    have h := congrArg Elem.Hom.deg ((FrobCat.sqIso f.F.commP).hom_inv_id_app (iso 0))
    exact PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val h))
  exact (div_eq_of_comm η hdeg _ _ he ((FrobCat.sqIso f.F.commP).hom.naturality e)).symm

/-- `f` preserves `ρ = log|μ|` of the linear endomorphisms of isotropic objects. -/
theorem rad_map (A : Obj) (hA : IsIsotropic P A) (e : Orhd P A) :
    (f.F.C.functor.map e.1).rad = e.1.rad := by
  have h := congrArg norm (f.val_map_conjC A hA e)
  rw [norm_id_or_conj f.conjC_eq, norm_val, norm_val] at h
  exact Real.exp_injective h

/-- **Rigidity of the divisor monoid** (IUT I, Remark 5.2.1 (ii), l.9839–9843): `f` acts as the
identity on `Φ_{C_v} = ℝ_{≥0}`. -/
theorem phi_apply (A : fArcModel.F.D) (x : fArcModel.F.Φ.obj A) : f.F.phi A x = x := by
  obtain ⟨⟨⟩⟩ := A
  have key : ∀ r : ℝ, 0 ≤ r → (f.F.phi pt ⟨r⟩).down = r := by
    intro r hr
    let e : (iso 0 : Obj) ⟶ iso 0 := mkHom 1 (-r) 1 (Set.subset_univ _) (by simp [iso]; linarith)
    have he : e.deg = 1 := rfl
    have h1 := congrArg ULift.down (f.phi_divVal e he)
    have h2 := f.rad_map (iso 0) isIsotropic_iso0 ⟨e, (mem_orhd e).mpr he⟩
    have hdF : (f.F.C.functor.map e).deg = 1 :=
      (mem_orhd _).mp (f.map_orhd _ e ((mem_orhd e).mpr he))
    have hde : divVal e = r := by simp [divVal, e, iso]
    rw [hde] at h1
    refine h1.trans ?_
    simp only [divVal, hdF, PNat.one_coe, Nat.cast_one, one_mul]
    rw [h2]
    simp [e]
  obtain ⟨r⟩ := x
  apply ULift.ext
  rcases le_total 0 r with hx | hx
  · exact key r hx
  · have h := key (-r) (by linarith)
    have hn := map_neg (f.F.phi pt) (⟨-r⟩ : ULift ℝ)
    have hx' : -(⟨-r⟩ : ULift ℝ) = ⟨r⟩ := ULift.ext _ _ (by simp)
    rw [hx'] at hn
    exact (congrArg ULift.down hn).trans
      (show -(f.F.phi pt ⟨-r⟩).down = r by rw [h, neg_neg])

/-- **`F^⊢_v`: the automorphism of the split Frobenioid `(C^⊢_v, τ^⊢_v) = (C_v, τ^⊢_v)`**
induced by `f`. -/
def vdashSplit : cArcSplit.Iso cArcSplit where
  iso := f.F
  map_tau s hs := ⟨tauArc, rfl, by rw [Set.mem_singleton_iff.mp hs]; exact f.mapsSplit_tauArc⟩
  inv_tau s hs := ⟨tauArc, rfl, by
    rw [Set.mem_singleton_iff.mp hs]; exact (FArcData.Iso.symm f).mapsSplit_tauArc⟩

end FArcData.Iso

/-! ### `TM^⊢` -/

/-- **The automorphism `z ↦ c(z)` of `O^▷_ℂ` for `c ∈ {id, conj}`.** -/
def orhdConj (c : ℂ →+* ℂ) (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) :
    Angular.orhdC ≃ₜ* Angular.orhdC where
  toFun z := ⟨c (z : ℂ), mem_orhdC.mpr ⟨fun h => (mem_orhdC.mp z.2).1 (by
      rw [← invol_id_or_conj hc (z : ℂ), h, map_zero]),
    by rw [norm_id_or_conj hc]; exact (mem_orhdC.mp z.2).2⟩⟩
  invFun z := ⟨c (z : ℂ), mem_orhdC.mpr ⟨fun h => (mem_orhdC.mp z.2).1 (by
      rw [← invol_id_or_conj hc (z : ℂ), h, map_zero]),
    by rw [norm_id_or_conj hc]; exact (mem_orhdC.mp z.2).2⟩⟩
  left_inv z := Subtype.ext (invol_id_or_conj hc (z : ℂ))
  right_inv z := Subtype.ext (invol_id_or_conj hc (z : ℂ))
  map_mul' a b := Subtype.ext (map_mul c (a : ℂ) (b : ℂ))
  continuous_toFun := ((continuous_id_or_conj hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_id_or_conj hc).comp continuous_subtype_val).subtype_mk _

/-- `z ↦ c(z)` preserves `(0, 1]`. -/
lemma orhdConj_ray (c : ℂ →+* ℂ) (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ)
    (x : Angular.orhdC) : x ∈ rayC ↔ orhdConj c hc x ∈ rayC := by
  change (0 < (x : ℂ).re ∧ (x : ℂ).im = 0) ↔ (0 < (c x).re ∧ (c x).im = 0)
  rcases hc with rfl | rfl
  · exact Iff.rfl
  · simp

/-- **The automorphism of `(O^▷_ℂ, (0, 1])` given by `c ∈ {id, conj}`.** -/
def tmIsoOfConj (c : ℂ →+* ℂ) (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ) :
    tmModel.Iso tmModel where
  e := orhdConj c hc
  ray x := orhdConj_ray c hc x

/-- The coordinate `O^▷(D^⊢_v) = O^▷_ℂ ⊆ ℂ` of the model object of `TM^⊢`. -/
def tmCoord (x : tmModel.M) : ℂ := Subtype.val x

@[simp] lemma tmCoord_tmIsoOfConj (c : ℂ →+* ℂ) (hc : c = RingHom.id ℂ ∨ c = starRingEnd ℂ)
    (z : Angular.orhdC) : tmCoord ((tmIsoOfConj c hc).e z) = c z := rfl

/-- Isomorphisms of `TM^⊢` are determined by their maps. -/
lemma TMVdash.Iso.ext' {X Y : TMVdash} {a b : X.Iso Y} (h : ∀ x, a.e x = b.e x) : a = b := by
  obtain ⟨ea, ra⟩ := a
  obtain ⟨eb, rb⟩ := b
  have : ea = eb := ContinuousMulEquiv.ext h
  subst this
  rfl

/-- Isomorphisms of Aut-holomorphic spaces are determined by their homeomorphisms. -/
lemma EllSp.Iso.ext' {S T : EllSp} {a b : S.Iso T} (h : a.e = b.e) : a = b := by
  obtain ⟨ea, ha⟩ := a
  obtain ⟨eb, hb⟩ := b
  cases h
  rfl

/-- Isomorphisms of `F^⊢`-data at `V^arc` are determined by their isomorphisms of Frobenioids and
in `TM^⊢`. -/
lemma FVdashArcData.Iso.ext' {X Y : FVdashArcData} {a b : X.Iso Y} (h₁ : a.F.iso = b.F.iso)
    (h₂ : a.T = b.T) : a = b := by
  obtain ⟨⟨fa, ma, ia⟩, ta⟩ := a
  obtain ⟨⟨fb, mb, ib⟩, tb⟩ := b
  cases h₁
  cases h₂
  rfl

namespace FArcData.Iso

open Angular

variable (f g : FArcData.Iso fArcModel fArcModel)

/-- **`F^⊢_v`: the automorphism of `D^⊢_v` induced by `f`** (the automorphism `c ∈ {id, conj}`
of `(O^▷_ℂ, (0, 1])`). -/
def vdashTM : tmModel.Iso tmModel := tmIsoOfConj f.conjC f.conjC_eq

/-- **`vdashTM f` is the automorphism induced by `f.S` on `A_{D_v}`** at every point `p`
(`D^⊢_v` is the object of `TM^⊢` determined by `A_{D_v}`). -/
theorem vdashTM_apply (p : ellModel.X) (z : Angular.orhdC) :
    tmCoord (f.vdashTM.e z) = ellConj f.S p z := by
  rw [f.ellConj_eq_conjC p]
  rfl

/-- **The automorphism of `D^⊢_v` induced by an automorphism of `F_v` is the identity or complex
conjugation.** -/
theorem vdashTM_id_or_conj :
    (∀ z : Angular.orhdC, tmCoord (f.vdashTM.e z) = z) ∨
      ∀ z : Angular.orhdC, tmCoord (f.vdashTM.e z) = starRingEnd ℂ z := by
  rcases f.conjC_eq with h | h
  · left
    intro z
    change f.conjC z = z
    rw [h]
    rfl
  · right
    intro z
    change f.conjC z = _
    rw [h]

/-- **`F ↦ F^⊢` on automorphisms at `v ∈ V^arc`** (IUT I, Example 3.4 (ii); Remark 5.2.1 (ii)). -/
def vdashArc : fVdashArcModel.Iso fVdashArcModel := ⟨f.vdashSplit, f.vdashTM⟩

/-- `c` of a composite. -/
theorem conjC_trans (z : Angular.orhdC) :
    (FArcData.Iso.trans f g).conjC z = g.conjC (f.conjC z) := by
  have h := (FArcData.Iso.trans f g).val_map_conjC _ isIsotropic_iso0 (endOf z)
  have hf := f.val_map_conjC _ isIsotropic_iso0 (endOf z)
  have hg := g.val_map_conjC _ (f.map_iso _ isIsotropic_iso0)
    ⟨f.F.C.functor.map (endOf z).1, f.map_orhd _ _ (endOf z).2⟩
  rw [val_endOf] at h hf
  rw [← h, ← hf]
  exact hg

/-- `c` of the identity. -/
theorem conjC_refl (z : Angular.orhdC) : (FArcData.Iso.refl fArcModel).conjC z = z := by
  have h := ((FArcData.Iso.refl fArcModel).val_map_conjC _ isIsotropic_iso0 (endOf z)).symm.trans
    (val_endOf z)
  rwa [val_endOf] at h

theorem vdashTM_trans : (FArcData.Iso.trans f g).vdashTM = f.vdashTM.trans g.vdashTM :=
  TMVdash.Iso.ext' fun z => Subtype.ext (f.conjC_trans g z)

theorem vdashTM_refl : (FArcData.Iso.refl fArcModel).vdashTM = TMVdash.Iso.refl _ :=
  TMVdash.Iso.ext' fun z => Subtype.ext (conjC_refl z)

/-- **Functoriality of `F ↦ F^⊢` at `V^arc`**: composites. -/
theorem vdashArc_trans :
    (FArcData.Iso.trans f g).vdashArc = FVdashArcData.Iso.trans f.vdashArc g.vdashArc :=
  FVdashArcData.Iso.ext' rfl (f.vdashTM_trans g)

/-- **Functoriality of `F ↦ F^⊢` at `V^arc`**: identities. -/
theorem vdashArc_refl :
    (FArcData.Iso.refl fArcModel).vdashArc = FVdashArcData.Iso.refl fVdashArcModel :=
  FVdashArcData.Iso.ext' rfl vdashTM_refl

/-- `vdashTM f` depends only on the map of Aut-holomorphic spaces. -/
theorem vdashTM_eq_of_S {f g : FArcData.Iso fArcModel fArcModel} (h : f.S.e = g.S.e) :
    f.vdashTM = g.vdashTM := by
  have hS : f.S = g.S := EllSp.Iso.ext' h
  apply TMVdash.Iso.ext'
  intro z
  apply Subtype.ext
  exact (f.vdashTM_apply ptE z).trans ((congrArg (fun S => ellConj S ptE (tmCoord z)) hS).trans
    (g.vdashTM_apply ptE z).symm)

end FArcData.Iso

/-! ### Isomorphism classes -/

namespace FArcData.Iso

variable {X Y Z W : FArcData}

/-- **2-isomorphism of isomorphisms of `F_v`-data at `v ∈ V^arc`**: the isomorphisms of
Frobenioids are 2-isomorphic (`FrobCat.Iso.Rel`) and the maps of Aut-holomorphic spaces agree. -/
def Rel (f g : X.Iso Y) : Prop := FrobCat.Iso.Rel f.F g.F ∧ f.S.e = g.S.e

/-- The setoid of 2-isomorphism. -/
def setoid (X Y : FArcData) : Setoid (X.Iso Y) where
  r := Rel
  iseqv := ⟨fun _ => ⟨FrobCat.Iso.Rel.refl _, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

end FArcData.Iso

/-- **Isomorphisms of `F_v`-data at `v ∈ V^arc` in the sense of IUT I, §0** (classes of
isomorphisms modulo 2-isomorphism). -/
def FArcData.IsoClass (X Y : FArcData) : Type := Quotient (FArcData.Iso.setoid X Y)

namespace FArcData.IsoClass

variable {X Y Z W : FArcData}

/-- The class of an isomorphism. -/
def mk (f : X.Iso Y) : IsoClass X Y := Quotient.mk (FArcData.Iso.setoid X Y) f

lemma mk_eq_mk {f g : X.Iso Y} : mk f = mk g ↔ FArcData.Iso.Rel f g :=
  Quotient.eq (r := FArcData.Iso.setoid X Y)

lemma mk_surjective : Function.Surjective (mk : X.Iso Y → IsoClass X Y) :=
  Quotient.mk_surjective

/-- The identity class. -/
def refl (X : FArcData) : IsoClass X X := mk (FArcData.Iso.refl X)

/-- The inverse. -/
def symm : IsoClass X Y → IsoClass Y X :=
  Quotient.map (sa := FArcData.Iso.setoid X Y) (sb := FArcData.Iso.setoid Y X)
    FArcData.Iso.symm fun _ _ h => ⟨FrobCat.Iso.Rel.symm_iso h.1, by
      change Homeomorph.symm _ = Homeomorph.symm _
      rw [h.2]⟩

/-- The composite. -/
def trans : IsoClass X Y → IsoClass Y Z → IsoClass X Z :=
  Quotient.map₂ (sa := FArcData.Iso.setoid X Y) (sb := FArcData.Iso.setoid Y Z)
    (sc := FArcData.Iso.setoid X Z) FArcData.Iso.trans fun _ _ a _ _ b =>
      ⟨FrobCat.Iso.Rel.hcomp a.1 b.1, by
        change Homeomorph.trans _ _ = Homeomorph.trans _ _
        rw [a.2, b.2]⟩

@[simp] lemma symm_mk (f : X.Iso Y) : (mk f).symm = mk (FArcData.Iso.symm f) := rfl

@[simp] lemma trans_mk (f : X.Iso Y) (g : Y.Iso Z) :
    (mk f).trans (mk g) = mk (FArcData.Iso.trans f g) := rfl

lemma trans_assoc (a : IsoClass X Y) (b : IsoClass Y Z) (c : IsoClass Z W) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  obtain ⟨h, rfl⟩ := mk_surjective c
  exact mk_eq_mk.2 ⟨FrobCat.Iso.Rel.assoc f.F g.F h.F, rfl⟩

lemma refl_trans (a : IsoClass X Y) : (refl X).trans a = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 ⟨FrobCat.Iso.Rel.reflTrans f.F, rfl⟩

lemma trans_refl (a : IsoClass X Y) : a.trans (refl Y) = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 ⟨FrobCat.Iso.Rel.transRefl f.F, rfl⟩

lemma trans_symm (a : IsoClass X Y) : a.trans a.symm = refl X := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 ⟨FrobCat.Iso.Rel.transSymm f.F, f.S.e.self_trans_symm⟩

lemma symm_trans (a : IsoClass X Y) : a.symm.trans a = refl Y := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 ⟨FrobCat.Iso.Rel.symmTrans f.F, f.S.e.symm_trans_self⟩

lemma trans_symm_trans (a : IsoClass X Y) (b : IsoClass X Z) : a.trans (a.symm.trans b) = b := by
  rw [← trans_assoc, trans_symm, refl_trans]

/-- **`F ↦ D` on classes at `v ∈ V^arc`** (IUT I, Remark 5.2.1 (i)): the isomorphism of
Aut-holomorphic spaces. -/
def toD : IsoClass X Y → X.S.Iso Y.S :=
  Quotient.lift (s := FArcData.Iso.setoid X Y) (fun f => f.S) fun _ _ h => EllSp.Iso.ext' h.2

@[simp] lemma toD_mk (f : X.Iso Y) : (mk f).toD = f.S := rfl

end FArcData.IsoClass

namespace FVdashArcData.Iso

variable {X Y Z : FVdashArcData}

/-- **2-isomorphism of isomorphisms of `F^⊢_v`-data at `v ∈ V^arc`**: the isomorphisms of
Frobenioids are 2-isomorphic and the isomorphisms in `TM^⊢` agree. -/
def Rel (f g : X.Iso Y) : Prop := FrobCat.Iso.Rel f.F.iso g.F.iso ∧ f.T = g.T

/-- The setoid of 2-isomorphism. -/
def setoid (X Y : FVdashArcData) : Setoid (X.Iso Y) where
  r := Rel
  iseqv := ⟨fun _ => ⟨FrobCat.Iso.Rel.refl _, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

end FVdashArcData.Iso

/-- **Isomorphisms of `F^⊢_v`-data at `v ∈ V^arc` in the sense of IUT I, §0.** -/
def FVdashArcData.IsoClass (X Y : FVdashArcData) : Type := Quotient (FVdashArcData.Iso.setoid X Y)

namespace FVdashArcData.IsoClass

variable {X Y Z : FVdashArcData}

/-- The class of an isomorphism. -/
def mk (f : X.Iso Y) : IsoClass X Y := Quotient.mk (FVdashArcData.Iso.setoid X Y) f

lemma mk_eq_mk {f g : X.Iso Y} : mk f = mk g ↔ FVdashArcData.Iso.Rel f g :=
  Quotient.eq (r := FVdashArcData.Iso.setoid X Y)

lemma mk_surjective : Function.Surjective (mk : X.Iso Y → IsoClass X Y) :=
  Quotient.mk_surjective

/-- The identity class. -/
def refl (X : FVdashArcData) : IsoClass X X := mk (FVdashArcData.Iso.refl X)

/-- The composite. -/
def trans : IsoClass X Y → IsoClass Y Z → IsoClass X Z :=
  Quotient.map₂ (sa := FVdashArcData.Iso.setoid X Y) (sb := FVdashArcData.Iso.setoid Y Z)
    (sc := FVdashArcData.Iso.setoid X Z) FVdashArcData.Iso.trans fun _ _ a _ _ b =>
      ⟨FrobCat.Iso.Rel.hcomp a.1 b.1, by
        change TMVdash.Iso.trans _ _ = TMVdash.Iso.trans _ _
        rw [a.2, b.2]⟩

@[simp] lemma trans_mk (f : X.Iso Y) (g : Y.Iso Z) :
    (mk f).trans (mk g) = mk (FVdashArcData.Iso.trans f g) := rfl

/-- **`F^⊢ ↦ D^⊢` on classes at `v ∈ V^arc`**: the isomorphism in `TM^⊢`. -/
def toD : IsoClass X Y → X.T.Iso Y.T :=
  Quotient.lift (s := FVdashArcData.Iso.setoid X Y) (fun f => f.T) fun _ _ h => h.2

@[simp] lemma toD_mk (f : X.Iso Y) : (mk f).toD = f.T := rfl

end FVdashArcData.IsoClass

/-- **`F ↦ F^⊢` on automorphism classes of `F_v`, `v ∈ V^arc`** (IUT I, Example 3.4 (ii);
Remark 5.2.1 (ii)). -/
def vdashArcClass (a : FArcData.IsoClass fArcModel fArcModel) :
    FVdashArcData.IsoClass fVdashArcModel fVdashArcModel :=
  Quotient.map (sa := FArcData.Iso.setoid _ _) (sb := FVdashArcData.Iso.setoid _ _)
    FArcData.Iso.vdashArc (fun _ _ h => ⟨h.1, FArcData.Iso.vdashTM_eq_of_S h.2⟩) a

@[simp] lemma vdashArcClass_mk (f : FArcData.Iso fArcModel fArcModel) :
    vdashArcClass (FArcData.IsoClass.mk f) = FVdashArcData.IsoClass.mk f.vdashArc := rfl

/-- **Functoriality**: composites. -/
theorem vdashArcClass_trans (a b : FArcData.IsoClass fArcModel fArcModel) :
    vdashArcClass (a.trans b) = (vdashArcClass a).trans (vdashArcClass b) := by
  obtain ⟨f, rfl⟩ := FArcData.IsoClass.mk_surjective a
  obtain ⟨g, rfl⟩ := FArcData.IsoClass.mk_surjective b
  rw [FArcData.IsoClass.trans_mk, vdashArcClass_mk, vdashArcClass_mk, vdashArcClass_mk,
    FVdashArcData.IsoClass.trans_mk, FArcData.Iso.vdashArc_trans]

/-- **Functoriality**: identities. -/
theorem vdashArcClass_refl :
    vdashArcClass (FArcData.IsoClass.refl fArcModel) = FVdashArcData.IsoClass.refl _ := by
  rw [FArcData.IsoClass.refl, vdashArcClass_mk, FArcData.Iso.vdashArc_refl]
  rfl

/-- **Compatibility with `D ↦ D^⊢`**: on `D^⊢_v` the class `vdashArcClass a` is the automorphism
of `TM^⊢` induced on `A_{D_v}` (at every point `p`) by the automorphism `a.toD` of `D_v`; it is
the identity or complex conjugation. -/
theorem vdashArcClass_toD (a : FArcData.IsoClass fArcModel fArcModel) (p : ellModel.X)
    (z : Angular.orhdC) :
    tmCoord ((vdashArcClass a).toD.e z) = ellConj a.toD p z := by
  obtain ⟨f, rfl⟩ := FArcData.IsoClass.mk_surjective a
  exact f.vdashTM_apply p z

theorem vdashArcClass_toD_id_or_conj (a : FArcData.IsoClass fArcModel fArcModel) :
    (∀ z : Angular.orhdC, tmCoord ((vdashArcClass a).toD.e z) = z) ∨
      ∀ z : Angular.orhdC, tmCoord ((vdashArcClass a).toD.e z) = starRingEnd ℂ z := by
  obtain ⟨f, rfl⟩ := FArcData.IsoClass.mk_surjective a
  exact f.vdashTM_id_or_conj

/-! ### Constituents -/

/-- A chosen isomorphism of a constituent `‡F_v` (`v ∈ V^arc`) with the model `F_v`. -/
def FArcComp.model (X : FArcComp) : X.X.Iso fArcModel := Classical.choice X.equiv_model

/-- **`F ↦ F^⊢` on isomorphism classes of constituents at `v ∈ V^arc`** (IUT I, Example 3.4 (ii);
Remark 5.2.1 (ii)): the class of an isomorphism `‡F_v ≅ ‡F'_v`, transported to an automorphism
class of the model `F_v` and mapped to `F^⊢_v` (`vdashArcClass`). -/
def FArcComp.vdashClass {X Y : FArcComp} (a : FArcData.IsoClass X.X Y.X) :
    FVdashArcData.IsoClass fVdashArcModel fVdashArcModel :=
  vdashArcClass (((FArcData.IsoClass.mk X.model).symm.trans a).trans
    (FArcData.IsoClass.mk Y.model))

/-- **Functoriality of `F ↦ F^⊢`**: composites. -/
theorem FArcComp.vdashClass_trans {X Y Z : FArcComp} (a : FArcData.IsoClass X.X Y.X)
    (b : FArcData.IsoClass Y.X Z.X) :
    FArcComp.vdashClass (a.trans b) = (FArcComp.vdashClass a).trans (FArcComp.vdashClass b) := by
  simp only [FArcComp.vdashClass]
  rw [← vdashArcClass_trans]
  congr 1
  simp only [FArcData.IsoClass.trans_assoc, FArcData.IsoClass.trans_symm_trans]

/-- **Functoriality of `F ↦ F^⊢`**: identities. -/
theorem FArcComp.vdashClass_refl (X : FArcComp) :
    FArcComp.vdashClass (FArcData.IsoClass.refl X.X) = FVdashArcData.IsoClass.refl _ := by
  simp only [FArcComp.vdashClass]
  rw [FArcData.IsoClass.trans_refl, FArcData.IsoClass.symm_trans, vdashArcClass_refl]

end PrimeStrip

end Multiradial

end Iut
