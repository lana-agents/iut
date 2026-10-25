/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Deck
import Iut.AutHolomorphic.Elliptic.Affine

/-!
# Elliptic cuspidalisation for the model `E_Λ` ([AbsTopIII] Corollary 2.7 (b), (c))

For the once-punctured curve `E_Λ = T_Λ ∖ {0}` with its Aut-holomorphic structure `ellStr L`:

* `isEllCusp_mulN`: for `N ≥ 1`, multiplication by `N` gives an elliptic cuspidalisation diagram
  `E ⊇ U_N → E`, `U_N = E ∖ T_Λ[N]` ([AbsTopII] Example 3.2 (i));
* **`exists_hom_of_isEllCusp`** (classification): every elliptic cuspidalisation diagram
  `E ⊇ U → E` comes from a continuous group endomorphism `f` of `T_Λ` (`x ↦ a x` or `x ↦ a x̄`),
  with `U = {f ≠ 0}` and `q = f|_U`. The inputs are Corollary 2.3 (i) on `T_Λ`
  (`exists_rcLift_of_isMorphism`) and `exists_rc_of_rcLift` (lifting, removable singularities,
  Liouville);
* **`isCoveringMap_cuspExt`**: the extension of every diagram to the one-point compactification
  is a covering map ("which necessarily extends to a covering of the one-point compactification";
  the extension is continuous because a finite covering is proper, and it is then the map induced
  by `z ↦ a z` or `z ↦ a z̄`, hence unramified);
* **`mem_cuspTors_iff`**: the torsion points of Corollary 2.7 (b) are the torsion points of
  `T_Λ` (under `OnePoint E_Λ ≃ₜ T_Λ`, `∞ ↦ 0`);
* **`cuspSum_iff`**: their group law induced by `Gal(U/E)` is the group law of `T_Λ`;
* **`isRecAdd_iff`, `recAdd_ellStr`** (Corollary 2.7 (c)): the group law of `T_Λ` is the unique
  continuous operation on `OnePoint E_Λ` extending the torsion law, so the model-implicit
  `recAdd (ellStr L)` is the group law of `T_Λ`.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus OnePoint

variable {L : PeriodPair}

local notation "σ" => onePointEquiv L

/-! ### Multiplication by `N` -/

/-- Multiplication by `N` on `T_Λ`. -/
def mulN (L : PeriodPair) (N : ℕ) : Torus L →+ Torus L where
  toFun x := N • x
  map_zero' := nsmul_zero N
  map_add' a b := nsmul_add a b N

theorem mulN_mk (N : ℕ) (z : ℂ) : mulN L N (mk L z) = mk L ((N : ℂ) * z) := (mk_nsmul N z).symm

theorem isMorphism_mulN {N : ℕ} (hN : 0 < N) :
    IsMorphism (torusStr L) (torusStr L) (mulN L N) ∧ IsLocalHomeomorph (mulN L N) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  let Φ : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (N : ℂ) hN'
  have hΦ : ∀ z, Φ z = (N : ℂ) * z := fun _ => rfl
  have hΦs : ∀ z, Φ.symm z = (N : ℂ)⁻¹ * z := by
    intro z
    rw [Homeomorph.symm_apply_eq, hΦ]
    field_simp
  have hG : ∀ z, mulN L N (mk L z) = mk L (Φ z) := fun z => by rw [mulN_mk, hΦ]
  refine ⟨isMorphism_of_lift Φ false (fun w => ?_) (fun w => ?_) hG, isLocalHomeomorph_of_lift Φ hG⟩
  · rw [rcDiffAt_false]
    have : (Φ : ℂ → ℂ) = fun z => (N : ℂ) * z := funext hΦ
    rw [this]
    fun_prop
  · rw [rcDiffAt_false]
    have : (Φ.symm : ℂ → ℂ) = fun z => (N : ℂ)⁻¹ * z := funext hΦs
    rw [this]
    fun_prop

/-- `U_N = E ∖ T_Λ[N]`. -/
def cuspU (L : PeriodPair) (N : ℕ) : Opens (punct L) :=
  ⟨{x | mulN L N (x : Torus L) ≠ 0},
    (isClosed_singleton.preimage ((continuous_nsmul N).comp continuous_subtype_val)).isOpen_compl⟩

theorem mem_cuspU {N : ℕ} (x : punct L) : x ∈ cuspU L N ↔ mulN L N x ≠ 0 := Iff.rfl

/-- `[N] : U_N → E`. -/
def cuspQ (L : PeriodPair) (N : ℕ) (x : cuspU L N) : punct L := ⟨mulN L N (jU _ x), x.2⟩

/-- **The diagrams `E ⊇ U_N → E` given by multiplication by `N`** ([AbsTopII] Example 3.2 (i)). -/
theorem isEllCusp_mulN {N : ℕ} (hN : 0 < N) : IsEllCusp (ellStr L) (cuspU L N) (cuspQ L N) := by
  obtain ⟨hmor, hlh⟩ := isMorphism_mulN (L := L) hN
  have hU : ∀ x : punct L, x ∈ cuspU L N ↔ mulN L N x ≠ 0 := fun _ => Iff.rfl
  have hq : ∀ x, (cuspQ L N x : Torus L) = mulN L N (jU _ x) := fun _ => rfl
  have hfin : ((cuspU L N : Set (punct L)))ᶜ.Finite := by
    refine ((finite_fiber hlh 0).preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    simp only [mem_compl_iff, SetLike.mem_coe, mem_cuspU, not_not] at hx
    exact hx
  have hqmor : IsMorphism ((ellStr L).restrict (cuspU L N)) (ellStr L) (cuspQ L N) :=
    ((hmor.comp (AutHolStr.isMorphism_val (torusStr L) (punct L))).comp
      (AutHolStr.isMorphism_val (ellStr L) (cuspU L N))).codRestrict (punct L) fun x => x.2
  have hcov : IsCoveringMap (cuspExt (cuspU L N) (cuspQ L N)) := by
    rw [cuspExt_eq (mulN L N) (map_zero _) hU hq, ← isLocalHomeomorph_iff_isCoveringMap]
    exact (σ).symm.isLocalHomeomorph.comp (hlh.comp (σ).isLocalHomeomorph)
  obtain ⟨hqcov, hqfin⟩ := isCoveringMap_of_cuspExt hcov
  refine ⟨hfin, hqmor, hqcov, hqfin, ?_, ?_⟩
  · intro x y hxy
    have ht : mulN L N (jU _ y - jU _ x) = 0 := by
      have := congrArg Subtype.val hxy
      rw [hq, hq] at this
      rw [map_sub, this, sub_self]
    refine ⟨translU (mulN L N) hU ht, translU_mem_deck (mulN L N) hU hq ht,
      Subtype.ext (Subtype.ext ?_)⟩
    change jU _ x + (jU _ y - jU _ x) = jU _ y
    abel
  · intro g hg h hh
    obtain ⟨t, ht, rfl⟩ := exists_eq_translU (mulN L N) hU hq hfin hqmor.1.isLocallyInjective hg
    obtain ⟨s, hs, rfl⟩ := exists_eq_translU (mulN L N) hU hq hfin hqmor.1.isLocallyInjective hh
    ext x
    change jU _ x + s + t = jU _ x + t + s
    abel

/-! ### Classification of the diagrams -/

/-- **Classification of the elliptic cuspidalisation diagrams of `E_Λ`**: every diagram comes from
a continuous group endomorphism `f` of `T_Λ` (a local homeomorphism), `U = {f ≠ 0}`, `q = f|_U`. -/
theorem exists_hom_of_isEllCusp {U : Opens (punct L)} {q : U → punct L}
    (hc : IsEllCusp (ellStr L) U q) :
    ∃ f : Torus L →+ Torus L, (∀ x : punct L, x ∈ U ↔ f x ≠ 0) ∧
      (∀ x, (q x : Torus L) = f (jU U x)) ∧ IsLocalHomeomorph f := by
  obtain ⟨hfin, hqmor, hqcov, hqfin, -, -⟩ := hc
  set F : Torus L → Torus L := σ ∘ cuspExt U q ∘ (σ).symm with hFdef
  have hFc : Continuous F :=
    (σ).continuous.comp ((continuous_cuspExt hqcov hqfin).comp (σ).symm.continuous)
  have hF0 : F 0 = 0 := by simp [F, onePointEquiv_symm_zero]
  have hFmem : ∀ (x : punct L) (hx : x ∈ U), F x = q ⟨x, hx⟩ := by
    intro x hx
    simp only [F, Function.comp_apply, onePointEquiv_symm_coe]
    rw [cuspExt_of_mem U q ⟨x, hx⟩, onePointEquiv_coe]
  have hFnot : ∀ x : punct L, x ∉ U → F x = 0 := by
    intro x hx
    simp only [F, Function.comp_apply, onePointEquiv_symm_coe]
    rw [cuspExt_of_notMem U q hx, onePointEquiv_infty]
  have hU : ∀ x : punct L, x ∈ U ↔ F x ≠ 0 := by
    intro x
    constructor
    · intro hx
      rw [hFmem x hx]
      exact (q _).2
    · intro hx
      by_contra hn
      exact hx (hFnot x hn)
  have hq : ∀ x, (q x : Torus L) = F (jU U x) := fun x => (hFmem x x.2).symm
  -- local RC-holomorphy outside a finite set
  set K : Set (Torus L) := insert 0 (Subtype.val '' (U : Set (punct L))ᶜ)
  have hK : K.Finite := (hfin.image _).insert 0
  set U' : Opens (Torus L) := AutHolStr.openImage (punct L) U
  have hiso := isIso_openImageHomeo (torusStr L) (punct L) U
  let q' : U' → Torus L := fun y => ((q ((AutHolStr.openImageHomeo (punct L) U).symm y) :
    punct L) : Torus L)
  have hq' : IsMorphism ((torusStr L).restrict U') (torusStr L) q' :=
    (AutHolStr.isMorphism_val (torusStr L) (punct L)).comp (hqmor.comp (IsIso.symm hiso))
  have hloc : ∀ z, mk L z ∉ K → ∃ (δ : Bool) (Φ : ℂ → ℂ), (∀ᶠ w in 𝓝 z, RCDiffAt δ Φ w) ∧
      ∀ᶠ w in 𝓝 z, F (mk L w) = mk L (Φ w) := by
    intro z hz
    simp only [K, mem_insert_iff, mem_image, not_or] at hz
    have hzU : (⟨mk L z, hz.1⟩ : punct L) ∈ U := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    have hzU' : mk L z ∈ U' := AutHolStr.mem_openImage.2 ⟨hz.1, hzU⟩
    obtain ⟨δ, Φ, r, hr, hΦ, hΦe⟩ := exists_rcLift_of_isMorphism hq' hzU'
    refine ⟨δ, Φ, Filter.eventually_of_mem (ball_mem_nhds z hr) hΦ,
      Filter.eventually_of_mem (ball_mem_nhds z hr) fun w hw => ?_⟩
    obtain ⟨h, hwe⟩ := hΦe w hw
    obtain ⟨hw0, hwU⟩ := AutHolStr.mem_openImage.1 h
    rw [← hwe, hFmem ⟨mk L w, hw0⟩ hwU]
    have : (AutHolStr.openImageHomeo (punct L) U).symm ⟨mk L w, h⟩ = ⟨⟨mk L w, hw0⟩, hwU⟩ := by
      rw [Homeomorph.symm_apply_eq]
      rfl
    simp only [q', this]
  -- `F` is locally injective outside `K` (there it is `q`, a covering map)
  have hinj : ∀ x ∉ K, ∃ N ∈ 𝓝 x, InjOn F N := by
    intro x hx
    simp only [K, mem_insert_iff, mem_image, not_or] at hx
    have hxU : (⟨x, hx.1⟩ : punct L) ∈ U := by
      by_contra hn
      exact hx.2 ⟨_, hn, rfl⟩
    obtain ⟨N, hNo, hxN, hNinj⟩ := hqcov.isLocalHomeomorph.isLocallyInjective ⟨⟨x, hx.1⟩, hxU⟩
    have hj : IsOpenEmbedding (jU U) :=
      (punct L).isOpenEmbedding'.comp U.isOpenEmbedding'
    refine ⟨jU U '' N, hj.isOpenMap _ hNo |>.mem_nhds ⟨_, hxN, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hyy
    rw [← hq, ← hq] at hyy
    rw [hNinj hy hy' (Subtype.ext hyy)]
  obtain ⟨a, ha, δ, hFa⟩ := exists_rc_of_rcLift hFc hF0 hK hinj hloc
  -- hence `F` is a local homeomorphism
  let R : ℂ ≃ₜ ℂ :=
    { toFun := rc a δ
      invFun := rc (if δ then (starRingEnd ℂ a)⁻¹ else a⁻¹) δ
      left_inv := rc_inv_left ha δ
      right_inv := rc_inv_right ha δ
      continuous_toFun := continuous_rc a δ
      continuous_invFun := continuous_rc _ δ }
  have hFlh : IsLocalHomeomorph F := by
    have h1 : IsLocalHomeomorphOn (F ∘ mk L) univ := by
      have : F ∘ mk L = mk L ∘ R := funext hFa
      rw [this]
      exact (isCoveringMap_mk.isLocalHomeomorph.comp R.isLocalHomeomorph).isLocalHomeomorphOn
    have h2 := IsLocalHomeomorphOn.of_comp_right h1
      isCoveringMap_mk.isLocalHomeomorph.isLocalHomeomorphOn
    rwa [image_univ, mk_surjective.range_eq, ← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
      at h2
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    obtain ⟨z, rfl⟩ := mk_surjective (L := L) x
    obtain ⟨w, rfl⟩ := mk_surjective (L := L) y
    rw [← mk_add, hFa, hFa, hFa, ← mk_add]
    congr 1
    cases δ <;> simp [rc, mul_add, map_add]
  exact ⟨AddMonoidHom.mk' F hadd, hU, hq, hFlh⟩

/-- **The extension to the one-point compactification is a covering** ([AbsTopIII] Corollary 2.7
(b): "which necessarily extends to a covering of the one-point compactification"): for every
elliptic cuspidalisation diagram of `E_Λ`, `cuspExt U q` is a covering map. -/
theorem isCoveringMap_cuspExt {U : Opens (punct L)} {q : U → punct L}
    (hc : IsEllCusp (ellStr L) U q) : IsCoveringMap (cuspExt U q) := by
  obtain ⟨f, hU, hq, hf⟩ := exists_hom_of_isEllCusp hc
  rw [cuspExt_eq f (map_zero f) hU hq, ← isLocalHomeomorph_iff_isCoveringMap]
  exact (σ).symm.isLocalHomeomorph.comp (hf.comp (σ).isLocalHomeomorph)

/-! ### Torsion points and their group law -/

theorem mem_torsion_of_ker {f : Torus L →+ Torus L} (hf : IsLocalHomeomorph f) {x : Torus L}
    (hx : f x = 0) : x ∈ torsion L := by
  have hfin : (f.ker : Set (Torus L)).Finite := finite_fiber hf 0
  haveI : Finite f.ker := hfin.to_subtype
  exact (Function.Injective.isOfFinAddOrder_iff (f := f.ker.subtype)
    Subtype.coe_injective).2 (isOfFinAddOrder_of_finite (⟨x, hx⟩ : f.ker))

/-- **The torsion points of [AbsTopIII] Corollary 2.7 (b) for `E_Λ` are the torsion points of
`T_Λ`.** -/
theorem mem_cuspTors_iff (y : OnePoint (punct L)) : y ∈ cuspTors (ellStr L) ↔ σ y ∈ torsion L := by
  constructor
  · rintro (rfl | ⟨U, q, hc, x, hx, rfl⟩)
    · rw [onePointEquiv_infty]
      exact zero_mem_torsion
    · obtain ⟨f, hU, -, hf⟩ := exists_hom_of_isEllCusp hc
      rw [onePointEquiv_coe]
      refine mem_torsion_of_ker hf ?_
      by_contra hn
      exact hx ((hU x).2 hn)
  · intro hy
    induction y using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe x =>
      right
      rw [onePointEquiv_coe] at hy
      obtain ⟨N, hN, hNx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hy
      refine ⟨cuspU L N, cuspQ L N, isEllCusp_mulN hN, x, ?_, rfl⟩
      simp only [mem_cuspU, not_not]
      exact hNx

/-- **The group law on the torsion points induced by `Gal(U/E)` is the group law of `T_Λ`.** -/
theorem cuspSum_iff {x y : OnePoint (punct L)} (hx : σ x ∈ torsion L) (hy : σ y ∈ torsion L)
    (z : OnePoint (punct L)) : CuspSum (ellStr L) x y z ↔ σ z = σ x + σ y := by
  constructor
  · rintro ⟨U, q, hc, g, hg, h, hh, hgx, hhy, hghz⟩
    obtain ⟨f, hU, hq, -⟩ := exists_hom_of_isEllCusp hc
    have hql := hc.2.1.1.isLocallyInjective
    obtain ⟨t, ht, rfl⟩ := exists_eq_translU f hU hq hc.1 hql hg
    obtain ⟨s, hs, rfl⟩ := exists_eq_translU f hU hq hc.1 hql hh
    rw [cuspLim_iff hc.1 (jU_translU f hU ht)] at hgx
    rw [cuspLim_iff hc.1 (jU_translU f hU hs)] at hhy
    rw [cuspLim_iff hc.1 (t := s + t) (fun x => by
      change jU U x + s + t = jU U x + (s + t)
      abel)] at hghz
    rw [hgx, hhy, hghz]
    simp only [Homeomorph.apply_symm_apply]
    abel
  · intro hz
    obtain ⟨m, hm, hmx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
    obtain ⟨n, hn, hny⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hy
    have hN : 0 < m * n := Nat.mul_pos hm hn
    have hU : ∀ x : punct L, x ∈ cuspU L (m * n) ↔ mulN L (m * n) x ≠ 0 := fun _ => Iff.rfl
    have hq : ∀ x, (cuspQ L (m * n) x : Torus L) = mulN L (m * n) (jU _ x) := fun _ => rfl
    have ht : mulN L (m * n) (σ x) = 0 := by
      change (m * n) • σ x = 0
      rw [mul_comm, ← smul_smul, hmx, smul_zero]
    have hs : mulN L (m * n) (σ y) = 0 := by
      change (m * n) • σ y = 0
      rw [← smul_smul, hny, smul_zero]
    have hfin := (isEllCusp_mulN (L := L) hN).1
    refine ⟨cuspU L (m * n), cuspQ L (m * n), isEllCusp_mulN hN,
      translU _ hU ht, translU_mem_deck _ hU hq ht, translU _ hU hs, translU_mem_deck _ hU hq hs,
      ?_, ?_, ?_⟩
    · rw [cuspLim_iff hfin (jU_translU _ hU ht), Homeomorph.symm_apply_apply]
    · rw [cuspLim_iff hfin (jU_translU _ hU hs), Homeomorph.symm_apply_apply]
    · rw [cuspLim_iff hfin (t := σ y + σ x) (fun w => by
        change jU _ w + σ y + σ x = jU _ w + (σ y + σ x)
        abel), add_comm, ← hz, Homeomorph.symm_apply_apply]

/-- The group law of `T_Λ`, transported to the one-point compactification of `E_Λ`. -/
noncomputable def torusAdd (L : PeriodPair) (x y : OnePoint (punct L)) : OnePoint (punct L) :=
  (onePointEquiv L).symm (onePointEquiv L x + onePointEquiv L y)

/-- **[AbsTopIII] Corollary 2.7 (c) for `E_Λ`**: the group law of `T_Λ` is the unique continuous
operation on the one-point compactification of `E_Λ` that extends the group law of the torsion
points of Corollary 2.7 (b). -/
theorem isRecAdd_iff (μ : OnePoint (punct L) → OnePoint (punct L) → OnePoint (punct L)) :
    IsRecAdd (ellStr L) μ ↔ μ = torusAdd L := by
  constructor
  · rintro ⟨hμc, hμs⟩
    set ν : Torus L → Torus L → Torus L := fun a b => σ (μ ((σ).symm a) ((σ).symm b))
    have hνc : Continuous fun p : Torus L × Torus L => ν p.1 p.2 :=
      (σ).continuous.comp (hμc.comp (((σ).symm.continuous.comp continuous_fst).prodMk
        ((σ).symm.continuous.comp continuous_snd)))
    have hν : ν = (· + ·) := by
      refine eq_add_of_continuous hνc fun a ha b hb => ?_
      have ha' : (σ).symm a ∈ cuspTors (ellStr L) := by
        rw [mem_cuspTors_iff, Homeomorph.apply_symm_apply]; exact ha
      have hb' : (σ).symm b ∈ cuspTors (ellStr L) := by
        rw [mem_cuspTors_iff, Homeomorph.apply_symm_apply]; exact hb
      have := (cuspSum_iff (by rwa [Homeomorph.apply_symm_apply])
        (by rwa [Homeomorph.apply_symm_apply]) _).1 (hμs _ ha' _ hb')
      simpa only [Homeomorph.apply_symm_apply] using this
    funext x y
    have := congrFun (congrFun hν (σ x)) (σ y)
    simp only [ν, Homeomorph.symm_apply_apply] at this
    rw [torusAdd, ← this, Homeomorph.symm_apply_apply]
  · rintro rfl
    refine ⟨?_, fun x hx y hy => ?_⟩
    · exact (σ).symm.continuous.comp (((σ).continuous.comp continuous_fst).add
        ((σ).continuous.comp continuous_snd))
    · rw [mem_cuspTors_iff] at hx hy
      rw [cuspSum_iff hx hy, torusAdd, Homeomorph.apply_symm_apply]

/-- **The model-implicit group law of [AbsTopIII] Corollary 2.7 (c) on `E_Λ ∪ {∞}` is the group law
of `T_Λ`.** -/
theorem recAdd_ellStr : recAdd (ellStr L) = torusAdd L :=
  recAdd_eq ((isRecAdd_iff _).2 rfl) fun _ h => (isRecAdd_iff _).1 h

theorem onePointEquiv_recAdd (x y : OnePoint (punct L)) :
    onePointEquiv L (recAdd (ellStr L) x y) = onePointEquiv L x + onePointEquiv L y := by
  rw [recAdd_ellStr, torusAdd, Homeomorph.apply_symm_apply]

end Ell

end AutHol

end Iut
