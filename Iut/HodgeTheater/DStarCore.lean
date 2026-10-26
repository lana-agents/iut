/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.DStar
import Pi1.Orbicurve.EllipticArith
import Iut.Reconstruction.Cusp.HemiCoreBaseChange

/-!
# `π₁(†D^⊛)` group-theoretically ([AbsTopII] Cor. 3.3 (i) for `C_{F_mod}`; IUT I, Example 5.1 (i))

IUT I, Example 5.1 (i) (l.8246–8257 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory I.txt`): "one may construct group-theoretically from `π₁(†D^⊚)`, in a functorial fashion,
a profinite group corresponding to "`C_{F_mod}`" [cf. the algorithms of [AbsTopII], Corollary
3.3, (i), which are applicable in light of [AbsTopI], Example 4.8], which contains `π₁(†D^⊚)` as
an open subgroup; write `†D^⊛` for `B(−)⁰` of this profinite group, so we obtain a natural
morphism `†D^⊚ → †D^⊛`". [AbsTopII] Cor. 3.3 (i) (`Topics in Absolute Anabelian Geometry
II.txt` l.4402–4447) characterises the chain `Π ⇝ Π_C` of the core `C` as the unique length-one
chain of type `⋎` that is terminal in `ÉtLoc(Π)`.

For initial Θ-data `D` (with `π₁(C_{F_mod}) = piCmod D`, iut's genuine `π₁`, and
`π₁(†D^⊚) = π₁(C̲_K)`), this file proves, with the relative isomorphism version of the
Grothendieck conjecture (`RelIsomDGC.Exists`, MR7) as the named input `hDGC` and the
`j`-invariant condition `hj` of [CanLift], Proposition 2.7 (`j(E_F)` not exceptional, under which
`C_F = X_F/{±1}` is the core of `X_F`, `Iut.Anabelian.hasCoreUniversally_of_j`):

* `piCmodCoreEquiv D : π₁(C_{F_mod}) ≃ₜ* Π_C` (curves-jacobian's `hemiCoreGrp₄` of `E_mod`, the last
  group of the core chain `hemiCoreChain`), `galCoreEquiv D` (its Galois group `≃* Gal(F̄/F_mod)`),
  and `piCmodPr_eq` (the projections correspond);
* **`dStar_cor33i`**: the chain `Π_{X_{F_mod}} ⇝ Π_{C_{F_mod}}` is terminal in
  `ÉtLoc(Π_{X_{F_mod}})`, its last group being `π₁(C_{F_mod})` over `Gal(F̄/F_mod)`;
* **`dStar_reconstruct`**: every length-one chain of type `⋎` from `Π_{X_{F_mod}}` that is terminal
  in `ÉtLoc` has last group `≃ₜ* π₁(C_{F_mod})` over `Gal(F̄/F_mod)` — the group-theoretic
  characterisation of `π₁(†D^⊛)`;
* **`piCmod_selfComm`**: `π₁(C_{F_mod})` is self-commensurating over `Gal(F̄/F_mod)` (two open
  injections of a compact group lying over `Gal(F̄/F_mod)` up to conjugation differ by an inner
  automorphism);
* **`piCKuToCmod_unique`**, **`dCircToStar_unique`**: the open embedding
  `π₁(†D^⊚) = π₁(C̲_K) ↪ π₁(C_{F_mod})` (`piCKuToCmod`) is unique up to `Inn(π₁(C_{F_mod}))`
  among open embeddings with the same composite to `Gal(F̄/F_mod)` up to conjugation, and the
  natural morphism `†D^⊚ → †D^⊛` (`dCircToStar`) is unique up to natural isomorphism.

* `j_notMem_excJ`: the condition `hj` from IUT I, Definition 3.1, for `j ∈ {0, 1728}` outright and
  for the two other exceptional values modulo the converse of [CanLift], Proposition 2.7 (named
  debt `h27a`).

The descent from `K` to `F_mod` (`π₁(C_{F_mod}) ≅ Aut(π₁(C_K))`, modulo an absolute anabelian
input) is in `DStarDescent.lean`; the `K`-step is `hemi_cor33i_terminal_baseChange`. Not formalised
here: the "Θ-approach" subgroup `Π_{X_K} ⊆ Π_{C_K}` of IUT I, Remark 3.1.2 (i).
-/

noncomputable section

namespace Iut

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid CurvesJacobian CurvesJacobian.Cusp
  Iut.Reconstruction.HemiGenuine Iut.Reconstruction.HemiCore Iut.Anabelian AlgebraicGeometry Belyi
  Belyi.Anabelian Topology

attribute [local instance low] Classical.propDecidable

variable (D : InitialThetaData.{0})

instance : IsAlgClosed D.Fbar := IsAlgClosure.isAlgClosed D.F

instance : CharZero D.Fbar := charZero_of_injective_algebraMap (algebraMap D.F D.Fbar).injective

/-- **`π₁(C_{F_mod}) ≃ₜ* Π_C`**: iut's genuine `π₁` of `C_{F_mod}` is curves-jacobian's group of
the core `[Spec R / A]` of `E_mod ∖ {O}` (`genuinePi1HemiEtaleEquiv`, `hemiCoreEquiv₄`). -/
def piCmodCoreEquiv : piCmod D ≃ₜ* hemiCoreGrp₄ (curveMod D.E) :=
  (genuinePi1HemiEtaleEquiv (curveMod D.E)).trans (hemiCoreEquiv₄ (curveMod D.E))

/-- The Galois group of curves-jacobian's arithmetic `π₁` of `X_{F_mod}` (with `F̄` as algebraic
closure) is `Gal(F̄/F_mod)`. -/
def galCoreEquiv :
    (arithmeticExt D.Fbar (hypCurveX (curveMod D.E)) (compl_XE_nonempty (curveMod D.E))).G ≃*
      GalG (Fmod D) D.Fbar :=
  (hemiGkEquiv (curveMod D.E) D.Fbar).toMulEquiv.trans (galConstEquiv D).toMulEquiv

lemma hemiCorePr₄_piCmodCoreEquiv (x : piCmod D) :
    hemiCorePr₄ (curveMod D.E) D.Fbar (piCmodCoreEquiv D x) =
      hemiPrC (curveMod D.E) D.Fbar (genuinePi1HemiEtaleEquiv (curveMod D.E) x) :=
  congrArg (hemiPrC (curveMod D.E) D.Fbar)
    ((hemiCoreEquiv₄ (curveMod D.E)).symm_apply_apply (genuinePi1HemiEtaleEquiv (curveMod D.E) x))

lemma equivPi1_genuinePi1HemiEtaleEquiv (x : piCmod D) :
    (hemiData (curveMod D.E)).equivPi1 (genuinePi1HemiEtaleEquiv (curveMod D.E) x) =
      genuinePi1HemiEquiv (curveMod D.E) x :=
  (hemiData (curveMod D.E)).equivPi1.apply_symm_apply (genuinePi1HemiEquiv (curveMod D.E) x)

/-- **The projections correspond**: `piCmodPr = galCoreEquiv ∘ hemiCorePr₄ ∘ piCmodCoreEquiv`. -/
lemma piCmodPr_eq (x : piCmod D) :
    piCmodPr D x = galCoreEquiv D (hemiCorePr₄ (curveMod D.E) D.Fbar (piCmodCoreEquiv D x)) :=
  (congrArg (fun y => galConstEquiv D (piConstC (hemiData (curveMod D.E)) y))
    (equivPi1_genuinePi1HemiEtaleEquiv D x).symm).trans
    ((congrArg (galConstEquiv D) (hemiGkEquiv_hemiPrC (curveMod D.E) D.Fbar
      (genuinePi1HemiEtaleEquiv (curveMod D.E) x)).symm).trans
      (congrArg (galCoreEquiv D) (hemiCorePr₄_piCmodCoreEquiv D x).symm))

/-- The `j`-invariant condition for `E_mod`. -/
lemma curveMod_j_notMem (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) :
    ∀ c ∈ AffOrbicurve.excJ, (curveMod D.E).j ≠ (c : Fmod D) := fun c hc h => by
  refine hj c hc ?_
  have h' := congrArg (algebraMap (fieldOfModuli D.F D.E) D.F) h
  rw [map_ratCast, show (curveMod D.E).j = jMod D.E from WeierstrassCurve.ofJ_j _] at h'
  exact h'

/-- **The `j`-invariant condition `hj` from IUT I, Definition 3.1** (`Inter-universal Teichmuller
Theory I.txt` l.3990–4000), modulo the converse of [CanLift], Proposition 2.7 for the two
exceptional values without complex multiplication. `j(E_F) ∉ {0, 1728}` is proved: `E_F` has
multiplicative reduction at the places of `V_mod^bad ≠ ∅` (Def. 3.1 (b)), so `j(E_F)` is not
integral there (`jMod_ne`). For `j ∈ {2¹⁴·31³/5³, 2²·73³/3⁴}` the argument needs the named debt
`h27a`, the converse of [CanLift], Proposition 2.7 for these two values (the named `pi1` statement
`AffOrbicurve.CanLift27ArithNonCM`, the non-CM half of `AffOrbicurve.CanLift27Arith`,
`AffOrbicurve.canLift27Arith_iff`: such `E ∖ {0}` are `k`-arithmetic; not proved, see MR8-plan,
rounds 40–41): `C_K` is the `K`-core of `C̲_K` (`CKu_core`, Def. 3.1 (d)), hence, by the
covers `X̲_K → C̲_K` and `X̲_K → X_K`, of `X_K = (E_F)_K ∖ {0}`; so `X_K` is not `K`-arithmetic. -/
theorem j_notMem_excJ (h27a : AffOrbicurve.CanLift27ArithNonCM.{0}) :
    ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F) := by
  intro c hc hjc
  obtain ⟨h0, h1728⟩ := jMod_ne D
  simp only [AffOrbicurve.excJ, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | hc'
  · exact h0 (Subtype.ext (by change D.E.j = _; simp [hjc]))
  · refine h1728 ((algebraMap (fieldOfModuli D.F D.E) D.F).injective ?_)
    rw [map_ofNat]
    change D.E.j = _
    simp [hjc]
  have h1 := (genuineHasCore_iff_of_cover D.orb.XKu_to_XK).mp
    ((genuineHasCore_iff_of_cover D.orb.XKu_to_CKu).mpr D.orb.CKu_core)
  have hXK : OrbicurveDataSection.XK D.F D.E D.Fbar D.VBad D.prime =
      Orbicurve.oncePunctured (D.E.map (algebraMap D.F D.Kt)) := by
    rw [OrbicurveDataSection.XK, Orbicurve.baseChange_oncePunctured]
  rw [hXK] at h1
  obtain ⟨_, hcore⟩ := h1
  refine h27a D.Kt (D.E.map (algebraMap D.F D.Kt)) ?_
    ⟨_, hcore.congr_left (Genuine.isoPunctured (D.E.map (algebraMap D.F D.Kt)))⟩
  refine ⟨c, ?_, ?_⟩
  · rcases hc' with rfl | rfl <;> simp [AffOrbicurve.excJNonCM]
  · rw [WeierstrassCurve.map_j, hjc, map_ratCast]

/-- **[AbsTopII] Cor. 3.3 (i) for `C_{F_mod}`**: the chain `Π_{X_{F_mod}} ⇝ Π_{C_{F_mod}}` is
terminal in `ÉtLoc(Π_{X_{F_mod}})`, and its last group is `π₁(C_{F_mod})` (`piCmodCoreEquiv`)
over `Gal(F̄/F_mod)`. -/
theorem dStar_cor33i (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F)) :
    (hemiCoreChain (curveMod D.E) D.Fbar).IsTerminalEtLoc ∧
      ∀ x : piCmod D, galCoreEquiv D ((hemiCoreChain (curveMod D.E) D.Fbar).last.toG
        (piCmodCoreEquiv D x)) = piCmodPr D x :=
  ⟨hemi_cor33i_terminal (curveMod D.E) D.Fbar hDGC (curveMod_j_notMem D hj),
    fun x => (piCmodPr_eq D x).symm⟩

/-- **The group-theoretic characterisation of `π₁(†D^⊛)`** ([AbsTopII] Cor. 3.3 (i); IUT I,
Example 5.1 (i)): every length-one chain of type `⋎` from `Π_{X_{F_mod}}` that is terminal in
`ÉtLoc(Π_{X_{F_mod}})` has last group isomorphic to `π₁(C_{F_mod})`, compatibly with the
projections to `Gal(F̄/F_mod)`. -/
theorem dStar_reconstruct (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (c : PiChain (arithmeticExt D.Fbar (hypCurveX (curveMod D.E))
      (compl_XE_nonempty (curveMod D.E))))
    (hq : c.typeChain = [OpKind.quot]) (hc : c.IsTerminalEtLoc) :
    ∃ e : c.last.grp ≃ₜ* piCmod D, ∀ x, piCmodPr D (e x) = galCoreEquiv D (c.last.toG x) := by
  obtain ⟨θ, hθ⟩ := Iut.Reconstruction.EtLocChain.exists_compat_last_iso
    (hemiCoreChain_typeChain (curveMod D.E) D.Fbar) hq (dStar_cor33i D hDGC hj).1 hc
  refine ⟨θ.trans (piCmodCoreEquiv D).symm, fun x => ?_⟩
  rw [piCmodPr_eq]
  change galCoreEquiv D (hemiCorePr₄ (curveMod D.E) D.Fbar
    ((piCmodCoreEquiv D) ((piCmodCoreEquiv D).symm (θ x)))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact congrArg (galCoreEquiv D) (ChainObj.toG_apply_of_compat₄ hθ x)

/-- **`π₁(C_{F_mod})` is self-commensurating over `Gal(F̄/F_mod)`** ([AbsTopII] Cor. 3.3 (i), the
core property of `C_{F_mod}`, `hemi_selfComm`): two open injections `P ↪ π₁(C_{F_mod})` of a
compact group whose composites with `π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)` agree up to conjugation differ
by an inner automorphism of `π₁(C_{F_mod})`. -/
theorem piCmod_selfComm (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (P : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (f₁ f₂ : P →ₜ* piCmod D) (hi₁ : Function.Injective f₁) (ho₁ : IsOpen (Set.range f₁))
    (hi₂ : Function.Injective f₂) (ho₂ : IsOpen (Set.range f₂)) (g : GalG (Fmod D) D.Fbar)
    (hg : ∀ x, piCmodPr D (f₂ x) = g * piCmodPr D (f₁ x) * g⁻¹) :
    ∃ γ : piCmod D, ∀ x, f₂ x = γ * f₁ x * γ⁻¹ := by
  let e := piCmodCoreEquiv D
  let u : ULift.{1} P →ₜ* P := ⟨MulEquiv.ulift.toMonoidHom, continuous_uliftDown⟩
  let F : (P →ₜ* piCmod D) → (ULift.{1} P →ₜ* hemiCoreGrp₄ (curveMod D.E)) := fun f =>
    (ContinuousMonoidHom.toContinuousMonoidHom e).comp (f.comp u)
  have hF : ∀ f : P →ₜ* piCmod D, ∀ x, F f x = e (f x.down) := fun _ _ => rfl
  have hinj : ∀ f : P →ₜ* piCmod D, Function.Injective f → Function.Injective (F f) :=
    fun f hf x y h => ULift.ext _ _ (hf (e.injective h))
  have hopen : ∀ f : P →ₜ* piCmod D, IsOpen (Set.range f) → IsOpen (Set.range (F f)) := by
    intro f hf
    have hr : Set.range (F f) = e '' Set.range f := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨f x.down, ⟨x.down, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨ULift.up x, rfl⟩
    rw [hr]
    exact e.toHomeomorph.isOpenMap _ hf
  have hsc := hemi_selfComm (curveMod D.E) D.Fbar hDGC (curveMod_j_notMem D hj)
  obtain ⟨γ, hγ⟩ := hsc (ULift.{1} P) (F f₁) (F f₂) (hinj f₁ hi₁) (hopen f₁ ho₁)
    (hinj f₂ hi₂) (hopen f₂ ho₂) ((galCoreEquiv D).symm g) (fun x => by
      apply (galCoreEquiv D).injective
      change galCoreEquiv D (hemiCorePr₄ (curveMod D.E) D.Fbar (e (f₂ x.down))) =
        galCoreEquiv D ((galCoreEquiv D).symm g * hemiCorePr₄ (curveMod D.E) D.Fbar
          (e (f₁ x.down)) * ((galCoreEquiv D).symm g)⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← piCmodPr_eq, ← piCmodPr_eq]
      exact hg x.down)
  let γ' : hemiCoreGrp₄ (curveMod D.E) := γ
  refine ⟨e.symm γ', fun x => e.injective ?_⟩
  have h : e (f₂ x) = γ' * e (f₁ x) * γ'⁻¹ := hγ (ULift.up x)
  rw [h, map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]

/-- **The embedding `π₁(†D^⊚) ↪ π₁(†D^⊛)` is unique up to `Inn(π₁(C_{F_mod}))`**: every open
embedding `π₁(C̲_K) ↪ π₁(C_{F_mod})` whose composite with `π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)` agrees
with that of `piCKuToCmod` up to conjugation is a conjugate of `piCKuToCmod`. -/
theorem piCKuToCmod_unique (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (f : D.orb.CKu.genuinePi1 →* piCmod D) (hf : IsOpenEmbedding f) (g : GalG (Fmod D) D.Fbar)
    (hg : ∀ x, piCmodPr D (f x) = g * piCmodPr D (piCKuToCmod D x) * g⁻¹) :
    ∃ γ : piCmod D, ∀ x, f x = γ * piCKuToCmod D x * γ⁻¹ := by
  have h₀ := (exists_piCKu_emb D).choose_spec
  exact piCmod_selfComm D hDGC hj D.orb.CKu.genuinePi1 ⟨piCKuToCmod D, h₀.continuous⟩
    ⟨f, hf.continuous⟩ h₀.injective h₀.isOpen_range hf.injective hf.isOpen_range g hg

/-- **The natural morphism `†D^⊚ → †D^⊛` is unique up to natural isomorphism** (IUT I,
Example 5.1 (i)): the functor `B(π₁(C̲_K))⁰ ⥤ †D^⊛` of any open embedding as in
`piCKuToCmod_unique` is isomorphic to `dCircToStar D`. -/
theorem dCircToStar_unique (hDGC : ∀ (k : Type) [Field k] [NumberField k], RelIsomDGC.Exists k)
    (hj : ∀ c ∈ AffOrbicurve.excJ, D.E.j ≠ (c : D.F))
    (f : D.orb.CKu.genuinePi1 →* piCmod D) (hf : IsOpenEmbedding f) (g : GalG (Fmod D) D.Fbar)
    (hg : ∀ x, piCmodPr D (f x) = g * piCmodPr D (piCKuToCmod D x) * g⁻¹) :
    Nonempty (OrbitObj.mapFunctor f (fun U hU => by
      rw [Subgroup.coe_map]
      exact hf.isOpenMap _ hU) ≅ dCircToStar D) := by
  obtain ⟨γ, hγ⟩ := piCKuToCmod_unique D hDGC hj f hf g hg
  exact ⟨OrbitObj.mapFunctorConjIso (piCKuToCmod D) f _ _ γ hγ⟩

end HodgeTheater

end Iut
