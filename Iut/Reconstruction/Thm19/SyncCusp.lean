/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.SyncTame
import Iut.Reconstruction.Thm19.PUStage

/-!
# Cusp bookkeeping for `cycloCongr_tameGen` (MR9 item 4 (b-i))

`cycloCongr_tameGen` (`Thm19/SyncTame.lean`) carries tame generators along an isomorphism
`Φ : Π_U ≃ₜ* Π_{U'}` of Galois models of curves, given the matching of the cusps on `H_{k̄}`
(hypotheses `hK`, `h₁`, `h₂`, `hp`). Here these hypotheses are derived from the matching of the
cuspidal inertia groups of `Π_U` by `Φ` ([AbsTopIII] Thm 1.9 (b), `Topics in Absolute Anabelian
Geometry III.txt` l.2144–2152: the cusps of `U` are group-theoretic, [AbsTopI] Lemma 4.5):

* generic: `bcToDeltaU_mem_inertiaPi`, `exists_bcToDeltaU_eq_of_mem` (inertia of `Π_U` comes from
  `H_{k̄}`), **`exists_deltaU_conj_of_comap_eq`** (places over the same point of `X_{k̄}` have
  `Δ_U`-conjugate inertia groups), the separation property `CuspSep` (the converse; proved for
  curves over number fields in `Thm19/SyncStage.lean`), `exists_deltaU_conj_iff_of_map`;
* on `X_{k̄}`: `deltaBarUCongr_rhoBarU_of` (hypothesis `hp`), `exists_rhoBarU_of_map` (`h₁`, `h₂`),
  `isCentredOn_chartBar_iff`, **`isCentredOn_iff_comap_ne`** (for `V = X_{k̄} ∖ {x̄}`: a place is
  centred on `V` iff it does not lie over `x̄`), **`hK_of_cusps`** (hypothesis `hK`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Generic Galois models -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

lemma bcToDeltaTilde_mem_inertiaH {W : ValuationSubring Ω} {s : (baseChange D).H}
    (hs : s ∈ inertiaH (baseChange D) W) :
    ((bcToDeltaTilde D s : deltaTilde D) : D.H) ∈ inertiaH D W :=
  fun a ha => hs a ha

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- The image in `Π_U` of an inertia element of `H_{k̄}` is in the inertia group. -/
lemma bcToDeltaU_mem_inertiaPi {W : ValuationSubring Ω} {s : (baseChange D).H}
    (hs : s ∈ inertiaH (baseChange D) W) :
    (bcToDeltaU D s : Pi D) ∈ inertiaPi D W :=
  ⟨_, bcToDeltaTilde_mem_inertiaH hs, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Every element of the inertia group of `W ⊇ k` in `Π_U` comes from `I_W ∩ H_{k̄}`.** -/
lemma exists_bcToDeltaU_eq_of_mem {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    {x : Pi D} (hx : x ∈ inertiaPi D W) :
    ∃ s ∈ inertiaH (baseChange D) W, (bcToDeltaU D s : Pi D) = x := by
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨s, hs, hsI⟩ := exists_inertiaBar (D := D) ⟨(W, h), hk, hh⟩
  refine ⟨s, hsI, ?_⟩
  rw [coe_bcToDeltaU]
  exact congrArg _ (Subtype.ext hs)

lemma transPlace_resK₀ (ρ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) (W : ValuationSubring Ω) :
    transPlace (resK₀ k t ρ) W = transPlace ρ W := by
  ext x
  rw [mem_transPlace, mem_transPlace]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Places over the same point of `X_{k̄}` have `Δ_U`-conjugate inertia groups.** -/
theorem exists_deltaU_conj_of_comap_eq (W₁ W₂ : ValuationSubring Ω)
    (h : W₁.comap (algebraMap (F (baseChange D)) Ω) = W₂.comap (algebraMap (F (baseChange D)) Ω)) :
    ∃ δ ∈ DeltaU D, (inertiaPi D W₁).map (MulAut.conj δ).toMonoidHom = inertiaPi D W₂ := by
  obtain ⟨ρ, rfl⟩ := exists_transPlace_eq_of_comap_eq (D := baseChange D) W₁ W₂ h
  refine ⟨((bcToDeltaTilde D ρ : deltaTilde D) : Pi D), (bcToDeltaU D ρ).2, ?_⟩
  refine (map_conj_inertiaH ((bcToDeltaTilde D ρ : deltaTilde D) : D.H) W₁).trans ?_
  exact congrArg (fun W => inertiaPi D W) (transPlace_resK₀ (ρ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) W₁)

variable (D) in
/-- **Separation of the points of `X_{k̄}` by inertia**: cusps whose inertia groups are
`Δ_U`-conjugate lie over the same point of `X_{k̄}` (a property of the Galois model, proved for
curves over number fields from [GalSect] Thm 1.3 (i) and `Comm(I_W) = D_W`, see
`Thm19/SyncStage.lean`; used only as an explicit argument). -/
def CuspSep : Prop :=
  ∀ W₁ ∈ CuspW (k := k) (t := t), ∀ W₂ ∈ CuspW (k := k) (t := t), ∀ δ ∈ DeltaU D,
    (inertiaPi D W₁).map (MulAut.conj δ).toMonoidHom = inertiaPi D W₂ →
      W₁.comap (algebraMap (F (baseChange D)) Ω) = W₂.comap (algebraMap (F (baseChange D)) Ω)

variable {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (Φ : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (hψ : ∀ x, piToGk D' (Φ x) = ψ (piToGk D x))

include hψ in
/-- **`Φ` preserves `Δ_U`-conjugacy of matched inertia groups.** -/
theorem exists_deltaU_conj_of_map {W₁ W₂ : ValuationSubring Ω} {W₁' W₂' : ValuationSubring Ω'}
    (h₁ : (inertiaPi D W₁).map Φ.toMulEquiv.toMonoidHom = inertiaPi D' W₁')
    (h₂ : (inertiaPi D W₂).map Φ.toMulEquiv.toMonoidHom = inertiaPi D' W₂')
    (h : ∃ δ ∈ DeltaU D, (inertiaPi D W₁).map (MulAut.conj δ).toMonoidHom = inertiaPi D W₂) :
    ∃ δ' ∈ DeltaU D', (inertiaPi D' W₁').map (MulAut.conj δ').toMonoidHom = inertiaPi D' W₂' := by
  obtain ⟨δ, hδ, hc⟩ := h
  exact ⟨Φ δ, (mem_deltaU_iff Φ ψ hψ δ).2 hδ, map_conj_of_map_eq Φ.toMulEquiv h₁ h₂ hc⟩

end Generic

/-! ### On `X_{k̄}` -/

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]
  (Φ : Pi (curveGaloisData k hτ) ≃ₜ* Pi (curveGaloisData k' hτ'))
  (ψ : Gk k (FFClosure X) ≃* Gk k' (FFClosure X'))
  (hψ : ∀ x, piToGk (curveGaloisData k' hτ') (Φ x) = ψ (piToGk (curveGaloisData k hτ) x))

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` are found slowly
/-- **Matching on `H_{k̄}` is matching in `Π_U`** (the hypothesis `hp` of `cycloCongr_tameGen`). -/
lemma deltaBarUCongr_rhoBarU_iff (σ : (barData k hτ).H) (σ' : (barData k' hτ').H) :
    deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' ↔
      Φ (bcToDeltaU (curveGaloisData k hτ) σ : Pi (curveGaloisData k hτ)) =
        (bcToDeltaU (curveGaloisData k' hτ') σ' : Pi (curveGaloisData k' hτ')) := by
  have e1 := deltaUEquivBar_symm_deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ)
  rw [deltaUEquivBar_symm_rhoBarU] at e1
  constructor
  · intro h
    rw [← e1, h, deltaUEquivBar_symm_rhoBarU]
  · intro h
    apply (deltaUEquivBar k' hτ').symm.injective
    apply Subtype.ext
    rw [e1, h, deltaUEquivBar_symm_rhoBarU]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` are found slowly
/-- **Inertia of `H_{k̄}` along `Φ`** (the hypothesis `h₁` of `cycloCongr_tameGen`). -/
lemma exists_rhoBarU_of_map {W : ValuationSubring (FFClosure X)}
    {W' : ValuationSubring (FFClosure X')}
    (hk' : ∀ c : k', algebraMap k' (FFClosure X') c ∈ W')
    (hW : (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') W')
    (σ : (barData k hτ).H) (hσ : σ ∈ inertiaH (barData k hτ) W) :
    ∃ σ' ∈ inertiaH (barData k' hτ') W',
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' := by
  have hx : Φ (bcToDeltaU (curveGaloisData k hτ) σ : Pi (curveGaloisData k hτ)) ∈
      inertiaPi (curveGaloisData k' hτ') W' := hW ▸ ⟨_, bcToDeltaU_mem_inertiaPi hσ, rfl⟩
  obtain ⟨σ', hσ', he⟩ := exists_bcToDeltaU_eq_of_mem hk' hx
  exact ⟨σ', hσ', (deltaBarUCongr_rhoBarU_iff Φ ψ hψ σ σ').2 he.symm⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` are found slowly
/-- **Inertia of `H_{k̄}` along `Φ⁻¹`** (the hypothesis `h₂` of `cycloCongr_tameGen`). -/
lemma exists_rhoBarU_of_map_symm {W : ValuationSubring (FFClosure X)}
    {W' : ValuationSubring (FFClosure X')}
    (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W)
    (hW : (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') W')
    (σ' : (barData k' hτ').H) (hσ' : σ' ∈ inertiaH (barData k' hτ') W') :
    ∃ σ ∈ inertiaH (barData k hτ) W,
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' := by
  have hx : (bcToDeltaU (curveGaloisData k' hτ') σ' : Pi (curveGaloisData k' hτ')) ∈
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom :=
    hW ▸ bcToDeltaU_mem_inertiaPi hσ'
  obtain ⟨y, hy, hye⟩ := hx
  obtain ⟨σ, hσ, rfl⟩ := exists_bcToDeltaU_eq_of_mem hk hy
  exact ⟨σ, hσ, (deltaBarUCongr_rhoBarU_iff Φ ψ hψ σ σ').2 hye⟩

/-- **The places centred on `U_{k̄}`** are those containing the coordinate. -/
lemma isCentredOn_chartBar_iff {W : ValuationSubring (FFClosure X)}
    (hk : ∀ c : kbar k (FFClosure X), algebraMap (kbar k (FFClosure X)) (FFClosure X) c ∈ W) :
    IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (chartBar k τ) W ↔
      coordT τ ∈ W := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (mem_range_germ_chartOne_iff (transcendental_ffMap k hτ) (ffMap k X τ)).2
      (isIntegral_algebraMap (x := (⟨ffMap k X τ, Algebra.self_mem_adjoin_singleton _ _⟩ :
        Algebra.adjoin (kbar k (FFClosure X)) {ffMap k X τ})))
    have := h.2 a
    rwa [ha, barEquivL_tau] at this
  · intro ht
    exact ⟨hk, fun a => mem_of_isIntegral (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
      (barEquivL_algebraMap k hτ) hk (s := ffMap k X τ) (by rw [barEquivL_tau]; exact ht)
      ((mem_range_germ_chartOne_iff (transcendental_ffMap k hτ) _).1 ⟨a, rfl⟩)⟩

/-- `comapK` for `X_{k̄}` is the place of `F k̄` below `W`, read through `ffEquiv`. -/
lemma comapK_eq_iff (W₁ W₂ : ValuationSubring (FFClosure X)) :
    comapK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ) W₁ =
        comapK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ)
          W₂ ↔
      W₁.comap (algebraMap (F (barData k hτ)) (FFClosure X)) =
        W₂.comap (algebraMap (F (barData k hτ)) (FFClosure X)) := by
  constructor
  · intro h
    ext f
    have := SetLike.ext_iff.1 h (CurvesJacobian.Kummer.ffEquiv k hτ f)
    simp only [ValuationSubring.mem_comap] at this ⊢
    change ((barEquivL k hτ (CurvesJacobian.Kummer.ffEquiv k hτ f) : (barData k hτ).L) :
        FFClosure X) ∈ W₁ ↔
      ((barEquivL k hτ (CurvesJacobian.Kummer.ffEquiv k hτ f) : (barData k hτ).L) :
        FFClosure X) ∈ W₂ at this
    rwa [coe_barEquivL, AlgEquiv.symm_apply_apply] at this
  · intro h
    ext z
    have := SetLike.ext_iff.1 h ((CurvesJacobian.Kummer.ffEquiv k hτ).symm z)
    simp only [ValuationSubring.mem_comap] at this ⊢
    change ((barEquivL k hτ z : (barData k hτ).L) : FFClosure X) ∈ W₁ ↔
      ((barEquivL k hτ z : (barData k hτ).L) : FFClosure X) ∈ W₂
    rw [coe_barEquivL]
    exact this

/-- **A place is centred on `V = X_{k̄} ∖ {x̄}` iff it does not lie over `x̄`** (the point under
the place `W₀`, which is not centred on `V`). -/
lemma isCentredOn_iff_comapK_ne {V : (baseChangeKbar k X).Opens} [Nonempty V]
    {xb : baseChangeKbar k X} (hUx : (V : Set (baseChangeKbar k X))ᶜ = {xb})
    {W₀ : ValuationSubring (FFClosure X)}
    (hk₀ : ∀ c : kbar k (FFClosure X), algebraMap (kbar k (FFClosure X)) (FFClosure X) c ∈ W₀)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V W₀)
    {W : ValuationSubring (FFClosure X)}
    (hk : ∀ c : kbar k (FFClosure X), algebraMap (kbar k (FFClosure X)) (FFClosure X) c ∈ W) :
    IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V W ↔
      comapK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ) W ≠
        comapK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ)
          W₀ := by
  constructor
  · intro h he
    refine hW₀U ⟨hk₀, fun a => ?_⟩
    have h1 : (baseChangeKbar k X).germToFunctionField V a ∈
        comapK (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ)
          W := h.2 a
    rw [he] at h1
    exact h1
  · intro hne
    by_contra hc
    obtain ⟨y, hyV, hy⟩ := exists_notMem_of_not_isCentredOn (barData k hτ) (baseChangeKbar k X)
      (barEquivL k hτ) (barEquivL_algebraMap k hτ) V hk hc
    obtain ⟨y₀, hy₀V, hy₀⟩ := exists_notMem_of_not_isCentredOn (barData k hτ)
      (baseChangeKbar k X) (barEquivL k hτ) (barEquivL_algebraMap k hτ) V hk₀ hW₀U
    have e1 : y = xb := by
      have : y ∈ (V : Set (baseChangeKbar k X))ᶜ := hyV
      rw [hUx] at this
      exact this
    have e2 : y₀ = xb := by
      have : y₀ ∈ (V : Set (baseChangeKbar k X))ᶜ := hy₀V
      rw [hUx] at this
      exact this
    exact hne (hy.symm.trans (by rw [e1, ← e2, hy₀]))

include hψ in
lemma piToGk_symm (x : Pi (curveGaloisData k' hτ')) :
    piToGk (curveGaloisData k hτ) (Φ.symm x) = ψ.symm (piToGk (curveGaloisData k' hτ') x) := by
  rw [MulEquiv.eq_symm_apply, ← hψ, ContinuousMulEquiv.apply_symm_apply]

/-- `K ⊆ W` gives `k̄ ⊆ W`. -/
lemma kbar_mem_of {W : ValuationSubring (FFClosure X)}
    (hk : ∀ c : k, algebraMap k (FFClosure X) c ∈ W) (c : kbar k (FFClosure X)) :
    algebraMap (kbar k (FFClosure X)) (FFClosure X) c ∈ W :=
  kbar_mem W hk c

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` and the étale fundamental groups are found slowly
set_option maxHeartbeats 1600000 in
-- the étale fundamental groups and the kernels unify slowly
include hψ in
/-- **Kernels of the fillings to `U_x` along `Φ`** (one inclusion): if `Φ` carries cuspidal
inertia groups to cuspidal inertia groups, `W₀ ↦ W₀'`, and the cusps of `U` are separated by
inertia (`CuspSep`), then `Φ` maps the kernel of `H_{k̄} ↠ π₁ᵉᵗ(U_x)` into that of
`H'_{k̄} ↠ π₁ᵉᵗ(U'_{x'})`: the kernel is generated by `S` and the inertia at the cusps `≠ x`, and
a cusp `≠ x` goes to a cusp `≠ x'` (`isCentredOn_iff_comapK_ne`, `exists_deltaU_conj_of_comap_eq`,
`CuspSep`). -/
theorem mem_kernel_of_cusps
    (hcusp : ∀ W ∈ CuspW (k := k) (t := coordT τ), ∃ W' ∈ CuspW (k := k') (t := coordT τ'),
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
        inertiaPi (curveGaloisData k' hτ') W')
    (hsep : CuspSep (curveGaloisData k hτ))
    {W₀ : ValuationSubring (FFClosure X)} {W₀' : ValuationSubring (FFClosure X')}
    (hW₀ : W₀ ∈ CuspW (k := k) (t := coordT τ))
    (hk₀' : ∀ c : k', algebraMap k' (FFClosure X') c ∈ W₀')
    (h₀ : (inertiaPi (curveGaloisData k hτ) W₀).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') W₀')
    {V : (baseChangeKbar k X).Opens} [Nonempty V] {xb : baseChangeKbar k X}
    (hUx : (V : Set (baseChangeKbar k X))ᶜ = {xb})
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V W₀)
    {V' : (baseChangeKbar k' X').Opens} [Nonempty V'] {xb' : baseChangeKbar k' X'}
    (hUx' : (V' : Set (baseChangeKbar k' X'))ᶜ = {xb'})
    (hW₀U' : ¬ IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V' W₀')
    (hle' : chartBar k' τ' ≤ V')
    (σ : (barData k hτ).H)
    (hσ : σ ∈ GaloisPi1.kernel (barData k hτ).H
      (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V))
    (σ' : (barData k' hτ').H)
    (he : Φ (bcToDeltaU (curveGaloisData k hτ) σ : Pi (curveGaloisData k hτ)) =
      (bcToDeltaU (curveGaloisData k' hτ') σ' : Pi (curveGaloisData k' hτ'))) :
    σ' ∈ GaloisPi1.kernel (barData k' hτ').H
      (SU (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V') := by
  have hV' : (V' : Set (baseChangeKbar k' X'))ᶜ.Finite := hUx' ▸ Set.finite_singleton _
  set f' := fillUx k' hτ' hle'
  set T : Subgroup (barData k hτ).H :=
    ((f'.toMonoidHom.ker).comap (deltaBarUCongr Φ ψ hψ).toMulEquiv.toMonoidHom).comap
      (rhoBarU k hτ) with hT
  have hk1 : IsClosed ((f'.toMonoidHom.ker : Subgroup (DeltaBar k' hτ' (chartBar k' τ'))) :
      Set (DeltaBar k' hτ' (chartBar k' τ'))) := by
    have e : ((f'.toMonoidHom.ker : Subgroup (DeltaBar k' hτ' (chartBar k' τ'))) :
        Set (DeltaBar k' hτ' (chartBar k' τ'))) = f' ⁻¹' {1} := by
      ext y
      simp [MonoidHom.mem_ker]
    rw [e]
    exact isClosed_singleton.preimage f'.continuous
  have hTc : IsClosed (T : Set (barData k hτ).H) :=
    (hk1.preimage (deltaBarUCongr Φ ψ hψ).continuous).preimage
      ((barData k hτ).continuous_chartHom _ _)
  have hS : (Subtype.val ⁻¹' SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V :
      Set (barData k hτ).H) ⊆ T := by
    intro s hs
    obtain ⟨-, W, hW, hsW⟩ := (mem_SU_iff _ _ _ V _).1 hs
    change f' (deltaBarUCongr Φ ψ hψ (rhoBarU k hτ s)) = 1
    have hkW : ∀ c : k, algebraMap k (FFClosure X) c ∈ W := fun c => by
      have := hW.1 (algebraMap k (kbar k (FFClosure X)) c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    by_cases ht : coordT τ ∈ W
    · have h1 : rhoBarU k hτ s = 1 := by
        rw [← MonoidHom.mem_ker, (rhoBarU_spec k hτ).1, ← SU_chartBar k hτ,
          GaloisPi1.kernel_eq_topologicalClosure _ (barData k hτ).isClosed_H _
            (SU_subset_H _ _ _ _)]
        exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
          ((mem_SU_iff _ _ _ _ _).2 ⟨s.2, W, (isCentredOn_chartBar_iff hW.1).2 ht, hsW⟩))
      rw [h1, map_one, map_one]
    · obtain ⟨W', hW', hWW'⟩ := hcusp W ⟨hkW, ht⟩
      obtain ⟨s', hs', hss'⟩ := exists_rhoBarU_of_map Φ ψ hψ hW'.1 hWW' s hsW
      rw [hss', fillUx_rhoBarU_eq_one_iff k' hτ' hV' hle']
      have hcent : IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V'
          W' := by
        rw [isCentredOn_iff_comapK_ne hUx' (kbar_mem_of hk₀') hW₀U' (kbar_mem_of hW'.1)]
        intro hc
        rw [comapK_eq_iff] at hc
        obtain ⟨δ, hδ, hc'⟩ := exists_deltaU_conj_of_map Φ.symm ψ.symm (piToGk_symm Φ ψ hψ)
          (map_symm_eq_of_map_eq Φ.toMulEquiv hWW') (map_symm_eq_of_map_eq Φ.toMulEquiv h₀)
          (exists_deltaU_conj_of_comap_eq W' W₀' hc)
        have h4 := hsep W ⟨hkW, ht⟩ W₀ hW₀ δ hδ hc'
        rw [← comapK_eq_iff] at h4
        exact (isCentredOn_iff_comapK_ne hUx (kbar_mem_of hW₀.1) hW₀U (kbar_mem_of hkW)).1 hW h4
      rw [GaloisPi1.kernel_eq_topologicalClosure _ (barData k' hτ').isClosed_H _
        (SU_subset_H _ _ _ _)]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
        ((mem_SU_iff _ _ _ _ _).2 ⟨s'.2, W', hcent, hs'⟩))
  have hle : GaloisPi1.kernel (barData k hτ).H
      (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V) ≤ T := by
    rw [GaloisPi1.kernel_eq_topologicalClosure _ (barData k hτ).isClosed_H _
      (SU_subset_H _ _ _ V)]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hS) hTc
  have h5 : f' (deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ)) = 1 := hle hσ
  rw [(deltaBarUCongr_rhoBarU_iff Φ ψ hψ σ σ').2 he, fillUx_rhoBarU_eq_one_iff k' hτ' hV' hle']
    at h5
  exact h5

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` and the étale fundamental groups are found slowly
set_option maxHeartbeats 1600000 in
-- the étale fundamental groups and the kernels unify slowly
/-- **The hypothesis `hK` of `cycloCongr_tameGen` from the matching of the cusps** (both ways)
and the separation of the cusps on both sides. -/
theorem hK_of_cusps
    (hcusp : ∀ W ∈ CuspW (k := k) (t := coordT τ), ∃ W' ∈ CuspW (k := k') (t := coordT τ'),
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
        inertiaPi (curveGaloisData k' hτ') W')
    (hcusp' : ∀ W' ∈ CuspW (k := k') (t := coordT τ'), ∃ W ∈ CuspW (k := k) (t := coordT τ),
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
        inertiaPi (curveGaloisData k' hτ') W')
    (hsep : CuspSep (curveGaloisData k hτ)) (hsep' : CuspSep (curveGaloisData k' hτ'))
    {W₀ : ValuationSubring (FFClosure X)} {W₀' : ValuationSubring (FFClosure X')}
    (hW₀ : W₀ ∈ CuspW (k := k) (t := coordT τ)) (hW₀' : W₀' ∈ CuspW (k := k') (t := coordT τ'))
    (h₀ : (inertiaPi (curveGaloisData k hτ) W₀).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') W₀')
    {V : (baseChangeKbar k X).Opens} [Nonempty V] {xb : baseChangeKbar k X}
    (hUx : (V : Set (baseChangeKbar k X))ᶜ = {xb})
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V W₀)
    (hle : chartBar k τ ≤ V)
    {V' : (baseChangeKbar k' X').Opens} [Nonempty V'] {xb' : baseChangeKbar k' X'}
    (hUx' : (V' : Set (baseChangeKbar k' X'))ᶜ = {xb'})
    (hW₀U' : ¬ IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V' W₀')
    (hle' : chartBar k' τ' ≤ V') :
    ∀ (σ : (barData k hτ).H) (σ' : (barData k' hτ').H),
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' →
        (σ' ∈ GaloisPi1.kernel (barData k' hτ').H
            (SU (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V') ↔
          σ ∈ GaloisPi1.kernel (barData k hτ).H
            (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V)) := by
  intro σ σ' h
  have he := (deltaBarUCongr_rhoBarU_iff Φ ψ hψ σ σ').1 h
  constructor
  · intro hσ'
    refine mem_kernel_of_cusps Φ.symm ψ.symm (piToGk_symm Φ ψ hψ) (fun W' hW' => ?_) hsep' hW₀'
      hW₀.1 (map_symm_eq_of_map_eq Φ.toMulEquiv h₀) hUx' hW₀U' hUx hW₀U hle σ' hσ' σ ?_
    · obtain ⟨W, hW, hWW'⟩ := hcusp' W' hW'
      exact ⟨W, hW, map_symm_eq_of_map_eq Φ.toMulEquiv hWW'⟩
    · rw [← he]
      exact ContinuousMulEquiv.symm_apply_apply _ _
  · intro hσ
    exact mem_kernel_of_cusps Φ ψ hψ hcusp hsep hW₀ hW₀'.1 h₀ hUx hW₀U hUx' hW₀U' hle' σ hσ σ' he

end Curve

end Iut.Reconstruction.Thm19
