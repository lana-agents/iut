/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.HemiCuspidal
import CurvesJacobian.Cusp.ArithDecompPi

/-!
# [AbsTopII] Cor. 3.3 (iii) (c) for the hemi-elliptic orbicurve, over `V = X_M` (MR8)

[AbsTopII] Corollary 3.3 (iii) (c) (`Topics in Absolute Anabelian Geometry II.txt` l.4510–4513):
"The decomposition groups of the closed points of `X` lying in the complement of `U_X` may be
obtained as the images via `Π_{U_X} ↠ Π` of the cuspidal decomposition groups of `Π_{U_X}`
[cf. [Mzk15], Lemma 4.5, (v)]." The cuspidal decomposition groups are the commensurators of the
cuspidal inertia groups ([AbsTopI] Lemma 4.5 (vi), `Topics in Absolute Anabelian Geometry
I.txt` l.3340: "Let `I ⊆ Π` be a decomposition group of a cusp. Then `I = C_Π(I ∩ Δ)`";
curves-jacobian's `commensurator_arithInertia`).

For `X = C = [(E ∖ {O}) / ±1]`, `U_X = [(E ∖ E[N]) / ±1]`, `π = hemiFillN : Π_{U_X} ↠ Π_C` and
`Π_V ⊴ Π_C` the image of `Π_{X_M}` (`HemiCuspidal.lean`), this file proves step (c) on the open
subgroup `π⁻¹(Π_V) ≅ Π_{U_V}` (`U_V = (E ∖ E[N])_M`, a hyperbolic curve over `M`), from
curves-jacobian's [AbsTopII] Cor. 3.7 (c) along `fillPiHom`
(`exists_map_fillPiHom_commensurator_cusps`) and the fact that commensurators commute with
injective homomorphisms (`map_commensurator_of_injective`):

* `hemiUVToUX : Π_{U_V} ↪ Π_{U_X}` (onto `π⁻¹(Π_V)`), `hemiXMToC : Π_{X_M} → Π_C` (onto `Π_V`);
  `hemiXMFill` is `X_M` written as the filling `fillCurve` of `U_V` (the curve in which
  curves-jacobian states the decomposition groups of the places of `U_V`), `hemiFillPi` the
  filling `Π_{U_V} → Π_{X_M}`, and `exists_hemiFill_comp_eq` says `π ∘ hemiUVToUX` factors through
  it up to one conjugation;
* **`hemi_cor33iii_c`**: up to one conjugation (independent of the cusp), for every cuspidal
  inertia group `I` of `Π_{U_V}` (placed in `Π_{U_X}` by `hemiUVToUX`), the image under `π` of its
  commensurator in `Π_{U_X}`, intersected with `π⁻¹(Π_V)`, is the image in `Π_C` of the
  decomposition group in `Π_{X_M}` of the place `W` defining `I` — a decomposition group of the
  closed point of `X_M ∖ U_V` under `W` when `W` is centred on `X_M`.

Not covered: the decomposition groups in all of `Π_C` (the stabilisers of the points of
`C ∖ U_X` beyond their intersection with `Π_V`).
-/

open CategoryTheory AlgebraicGeometry CurvesJacobian CurvesJacobian.Cusp Belyi Belyi.Anabelian
  Pi1.Orbifold AffOrbicurve Topology PreGaloisCategory AlgebraicGeometry.FiniteEtale

open scoped Pointwise

noncomputable section

namespace Iut.Reconstruction.HemiCusp

universe u

section Hemi

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] [NumberField K] (E : WeierstrassCurve K) [E.IsElliptic]
  (N : ℕ) [NeZero N] (M : IntermediateField K (ConstField₂ K (FFClosure (curveE E))))
  [FiniteDimensional K M] [IsGalois K M]
  (Ω' : Type u) [Field Ω'] [Algebra M Ω'] [IsAlgClosed Ω'] [Algebra.IsAlgebraic M Ω']
  [CharZero Ω']

/-- `Π_{U_V} ↪ Π_{U_X}` (onto `π⁻¹(Π_V)`, `hemiFibreArithEquiv`). -/
def hemiUVToUX : (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N)).Pi →* hemiPiUX E N :=
  (fibreSubgroup (hemiFillHom E N) (hemiPiV E M)).subtype.comp
    (hemiFibreArithEquiv E N M Ω').toMonoidHom

lemma hemiUVToUX_injective : Function.Injective (hemiUVToUX E N M Ω') :=
  Subtype.val_injective.comp (hemiFibreArithEquiv E N M Ω').injective

lemma range_hemiUVToUX :
    (hemiUVToUX E N M Ω').range = fibreSubgroup (hemiFillHom E N) (hemiPiV E M) := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩
    exact (hemiFibreArithEquiv E N M Ω' γ).2
  · intro hg
    obtain ⟨γ, hγ⟩ := (hemiFibreArithEquiv E N M Ω').surjective ⟨g, hg⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩

/-- `Π_{X_M} → Π_C` (onto `Π_V`). -/
def hemiXMToC : (arithmeticExt Ω' (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M))).Pi →* hemiPiC E :=
  (infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)).toMonoidHom.comp
    (hemiMPiXGal E M Ω').toMonoidHom

/-- `X_M = (E ∖ {O})_M`, written as the filling of `U_V = (E ∖ E[N])_M` (`fillCurve`; equal to
`hypCurveX (E.baseChange M)` up to the proof fields). -/
abbrev hemiXMFill : HypCurve M :=
  fillCurve (hypCurveVN (E.baseChange M) N) (VNE_le_XE (E.baseChange M) N)
    (hyperbolic_of_le (E.baseChange M) (VE_le_XE (E.baseChange M)) le_rfl)

/-- `Π_{X_M}` of `hemiXMFill` is `Π_{X_M}` (the identity). -/
def hemiXMFillEquiv : (arithmeticExt Ω' (hemiXMFill E N M)
    (compl_XE_nonempty (E.baseChange M))).Pi ≃* (arithmeticExt Ω' (hypCurveX (E.baseChange M))
    (compl_XE_nonempty (E.baseChange M))).Pi :=
  MulEquiv.refl _

/-- `Π_{X_M} → Π_C` on `hemiXMFill`. -/
def hemiXMFillToC : (arithmeticExt Ω' (hemiXMFill E N M)
    (compl_XE_nonempty (E.baseChange M))).Pi →* hemiPiC E :=
  (hemiXMToC E M Ω').comp (hemiXMFillEquiv E N M Ω').toMonoidHom

/-- `Π_{U_V} → Π_{X_M}`: curves-jacobian's `fillPiHom` of `U_V ⊆ X_M` (into `hemiXMFill`). -/
def hemiFillPi : (arithmeticExt Ω' (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N)).Pi →ₜ*
    (arithmeticExt Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M))).Pi :=
  fillPiHom Ω' (hypCurveVN (E.baseChange M) N)
    (compl_VNE_nonempty (E.baseChange M) N) (VNE_le_XE (E.baseChange M) N)
    (compl_XE_nonempty (E.baseChange M))
    (hyperbolic_of_le (E.baseChange M) (VE_le_XE (E.baseChange M)) le_rfl)

omit [IsGalois K M] in
lemma hemiXMFillEquiv_hemiFillPi (γ) :
    hemiXMFillEquiv E N M Ω' (hemiFillPi E N M Ω' γ) = hemiFillPiNM₃ E N M Ω' γ :=
  rfl

set_option maxHeartbeats 2000000 in
-- the rewrites inside `Π_{X_M}` / `Π_C` (`hemi_fibre_fill_arith`) exceed the default limit
/-- `π ∘ (Π_{U_V} ↪ Π_{U_X})` is `Π_{U_V} → Π_{X_M} → Π_C` (`hemiFillPi`, then
`hemiXMFillToC`) up to one conjugation in `Π_{X_M}` (`hemi_fibre_fill_arith`). -/
theorem exists_hemiFill_comp_eq :
    ∃ u, (hemiFillHom E N).comp (hemiUVToUX E N M Ω') = (hemiXMFillToC E N M Ω').comp
      ((MulAut.conj u).toMonoidHom.comp (hemiFillPi E N M Ω').toMonoidHom) := by
  -- (`obtain` directly on the application is slow; going through `have` is not)
  have hfib := hemi_fibre_fill_arith E N M Ω'
  obtain ⟨x, hx⟩ := hfib
  refine ⟨(hemiXMFillEquiv E N M Ω').symm ((hemiMPiXGal E M Ω').symm x⁻¹), ?_⟩
  ext γ
  change hemiFillN E N (hemiFibreArithEquiv E N M Ω' γ : hemiPiUX E N) =
    infInclC₃ (hemiData E) _ (isOpen_constFixer₃ M) (constFixer₃_normal M)
      (hemiMPiXGal E M Ω' (hemiXMFillEquiv E N M Ω'
        ((hemiXMFillEquiv E N M Ω').symm ((hemiMPiXGal E M Ω').symm x⁻¹) * hemiFillPi E N M Ω' γ *
          ((hemiXMFillEquiv E N M Ω').symm ((hemiMPiXGal E M Ω').symm x⁻¹))⁻¹)))
  rw [hx γ]
  congr 1
  rw [map_mul (hemiXMFillEquiv E N M Ω'), map_mul (hemiXMFillEquiv E N M Ω'),
    map_inv (hemiXMFillEquiv E N M Ω'), MulEquiv.apply_symm_apply, hemiXMFillEquiv_hemiFillPi,
    map_mul (hemiMPiXGal E M Ω'), map_mul (hemiMPiXGal E M Ω'), map_inv (hemiMPiXGal E M Ω'),
    ContinuousMulEquiv.apply_symm_apply, inv_inv]

set_option maxHeartbeats 2000000 in
-- the instantiation of `exists_map_fillPiHom_commensurator_cusps` at `U_V ⊆ X_M` exceeds the default
/-- **[AbsTopII] Cor. 3.3 (iii) (c) over `V = X_M`**: there is `s ∈ Π_{X_M}` such that for every
cuspidal inertia group `I` of `Π_{U_V}` (`U_V = (E ∖ E[N])_M`), with `I = I_W` for a place `W`
over a cusp, the image under `π : Π_{U_X} ↠ Π_C` of the cuspidal decomposition group
`Comm_{Π_{U_X}}(I) ∩ π⁻¹(Π_V)` is the image in `Π_C` of the `s`-conjugate of the decomposition
group of `W` in `Π_{X_M}` (a decomposition group of the closed point of `X_M ∖ U_V` under `W` when
`W` is centred on `X_M`). -/
theorem hemi_cor33iii_c :
    ∃ s, ∀ I ∈ arithCusps Ω' (hypCurveVN (E.baseChange M) N)
        (compl_VNE_nonempty (E.baseChange M) N),
      ∃ W, IsCuspPlace Ω' (hypCurveVN (E.baseChange M) N)
          (compl_VNE_nonempty (E.baseChange M) N) W ∧
        I = arithInertia Ω' (hypCurveVN (E.baseChange M) N)
          (compl_VNE_nonempty (E.baseChange M) N) W ∧
        (Subgroup.Commensurable.commensurator (I.map (hemiUVToUX E N M Ω')) ⊓
            fibreSubgroup (hemiFillHom E N) (hemiPiV E M)).map (hemiFillHom E N) =
          ((arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
            (MulAut.conj s).toMonoidHom).map (hemiXMFillToC E N M Ω') := by
  -- (`obtain` directly on these applications is slow; going through `have` is not)
  have hc := exists_hemiFill_comp_eq E N M Ω'
  obtain ⟨u, hcomp⟩ := hc
  have key : ∃ t : (arithmeticExt Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M))).Pi,
      ∀ I ∈ arithCusps Ω' (hypCurveVN (E.baseChange M) N) (compl_VNE_nonempty (E.baseChange M) N),
      ∃ W, IsCuspPlace Ω' (hypCurveVN (E.baseChange M) N)
          (compl_VNE_nonempty (E.baseChange M) N) W ∧
        I = arithInertia Ω' (hypCurveVN (E.baseChange M) N)
          (compl_VNE_nonempty (E.baseChange M) N) W ∧
        (Subgroup.Commensurable.commensurator I).map (hemiFillPi E N M Ω').toMonoidHom =
          (arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
            (MulAut.conj t).toMonoidHom :=
    exists_map_fillPiHom_commensurator_cusps Ω' (hypCurveVN (E.baseChange M) N)
      (compl_VNE_nonempty (E.baseChange M) N) (VNE_le_XE (E.baseChange M) N)
      (compl_XE_nonempty (E.baseChange M))
      (hyperbolic_of_le (E.baseChange M) (VE_le_XE (E.baseChange M)) le_rfl)
  obtain ⟨t, ht⟩ := key
  refine ⟨u * t, fun I hI => ?_⟩
  have hI' := ht I hI
  obtain ⟨W, hW, hIW, hmap⟩ := hI'
  refine ⟨W, hW, hIW, ?_⟩
  have hD : (arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
      (MulAut.conj (u * t)).toMonoidHom =
      ((arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
        (MulAut.conj t).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_map]
    exact congrArg (fun f => Subgroup.map f
      (arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W))
      (MonoidHom.ext fun y => by simp [mul_assoc])
  -- (explicit `calc`: `rw` on the whole goal compares subgroups of different groups and times out)
  have e1 : Subgroup.Commensurable.commensurator (I.map (hemiUVToUX E N M Ω')) ⊓
      fibreSubgroup (hemiFillHom E N) (hemiPiV E M) =
        (Subgroup.Commensurable.commensurator I).map (hemiUVToUX E N M Ω') := by
    rw [← range_hemiUVToUX E N M Ω']
    exact (map_commensurator_of_injective _ (hemiUVToUX_injective E N M Ω') I).symm
  calc (Subgroup.Commensurable.commensurator (I.map (hemiUVToUX E N M Ω')) ⊓
        fibreSubgroup (hemiFillHom E N) (hemiPiV E M)).map (hemiFillHom E N)
      = ((Subgroup.Commensurable.commensurator I).map (hemiUVToUX E N M Ω')).map
          (hemiFillHom E N) := congrArg (Subgroup.map (hemiFillHom E N)) e1
    _ = (Subgroup.Commensurable.commensurator I).map
          ((hemiFillHom E N).comp (hemiUVToUX E N M Ω')) := Subgroup.map_map _ _ _
    _ = (Subgroup.Commensurable.commensurator I).map ((hemiXMFillToC E N M Ω').comp
          ((MulAut.conj u).toMonoidHom.comp (hemiFillPi E N M Ω').toMonoidHom)) :=
        congrArg (Subgroup.map · (Subgroup.Commensurable.commensurator I)) hcomp
    _ = ((Subgroup.Commensurable.commensurator I).map
          ((MulAut.conj u).toMonoidHom.comp (hemiFillPi E N M Ω').toMonoidHom)).map
            (hemiXMFillToC E N M Ω') := (Subgroup.map_map _ _ _).symm
    _ = (((Subgroup.Commensurable.commensurator I).map (hemiFillPi E N M Ω').toMonoidHom).map
          (MulAut.conj u).toMonoidHom).map (hemiXMFillToC E N M Ω') :=
        congrArg (Subgroup.map (hemiXMFillToC E N M Ω')) (Subgroup.map_map _ _ _).symm
    _ = (((arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
          (MulAut.conj t).toMonoidHom).map (MulAut.conj u).toMonoidHom).map
            (hemiXMFillToC E N M Ω') :=
        congrArg (fun S => (S.map (MulAut.conj u).toMonoidHom).map (hemiXMFillToC E N M Ω')) hmap
    _ = ((arithDecomp Ω' (hemiXMFill E N M) (compl_XE_nonempty (E.baseChange M)) W).map
          (MulAut.conj (u * t)).toMonoidHom).map (hemiXMFillToC E N M Ω') :=
        congrArg (Subgroup.map (hemiXMFillToC E N M Ω')) hD.symm

end Hemi

end Iut.Reconstruction.HemiCusp
