/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm24iiPf
import Iut.Frobenioid.SaturationExists

/-!
# [FrdII], Theorem 2.4(ii) for `C_v`: the Kummer class of a uniformiser and the final statement

Continuation of `Thm24iiPf.lean`:

* `smul_galPairEquiv`: `galPairEquiv σ` acts on `K̄` as `α(σ)`;
* **`h1PairMap_kummer_unif`**: if `B(e_π) = π'` (`RelB`), then `Φ₁(κ(π)) = κ(π')` for
  `Φ₁ = (galPairEquiv, β_Ψ)_*`: an `n`-th root `g` of `π` lies in `K̄^N` (`root_fixed`), so
  `e_g ∈ O^▷(X)`, `B(e_g)^n = π'`, and `B(σ e_g) = B(e_g · e_{σg/g})` gives
  `β_Ψ(σg/g) = α(σ)B(e_g)/B(e_g)`;
* **`thm24Pf_ii`**: [FrdII], Theorem 2.4(ii) for `C_v` (unconditional).
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']

local notation "K̄" => PadicAlgCl p

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaQ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaQ) (divGal (GK p E) (ord p) (ord_smul p E) gammaQ)

variable (α : GK p E ≃ₜ* GK p E') (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))
  (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) : Set (GK p E')))

/-- `galPairEquiv σ` acts on `K̄` as `α(σ)`. -/
lemma galPairEquiv_apply (σ : K̄ ≃ₐ[fixL H] K̄) (y : K̄) :
    galPairEquiv α H hH hH' σ y = α (galFixMulEquiv H hH σ : GK p E) y := by
  have h := congrArg (fun s : H.map (α : GK p E →* GK p E') => (s : GK p E'))
    (galFixEquiv_galPairEquiv α H hH hH' σ)
  exact congrArg (fun f : GK p E' => f y) h

/-- `σ ∈ Gal(K̄/L)` and its image in `H ⊆ G_E` act in the same way on `K̄`. -/
lemma smul_galFixMulEquiv (σ : K̄ ≃ₐ[fixL H] K̄) (y : K̄ˣ) :
    (galFixMulEquiv H hH σ : GK p E) • y = σ • y := Units.ext rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
/-- A root of unity equal to `σ g'/g'` is the Kummer cocycle value (value-level criterion). -/
lemma mu_eq_kummerFun {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {n : ℕ} (g' : Ωˣ)
    (hG : ∀ σ : Ω ≃ₐ[K] Ω, σ • g' ^ n = g' ^ n) (σ : Ω ≃ₐ[K] Ω) (z : KummerTheory.Mu n Ω)
    (h : ((KummerTheory.Mu.val z : Ωˣ) : Ω) * g' = σ (g' : Ω)) :
    z = KummerTheory.kummerFun g' hG σ := by
  apply KummerTheory.Mu.ext
  apply Units.ext
  rw [KummerTheory.val_kummerFun, Units.val_div_eq_div_val, eq_div_iff g'.ne_zero]
  exact h

variable {F : FrobPf p E ⥤ FrobPf p E'} [F.IsEquivalence] {α} {τ : GK p E'}
  {N : OpenNormalSubgroup (GK p E)} {a : gammaQ}

/-- Powers of `e_g` in `O^▷(X)`. -/
lemma exists_pow_orhd {e : XN N a ⟶ XN N a} (he : e ∈ Orhd 𝐏E (XN N a)) (k : ℕ) :
    ∃ e' : XN N a ⟶ XN N a, e' ∈ Orhd 𝐏E (XN N a) ∧ rfE e' = rfE e ^ k ∧
      Bmap F τ N a e' = Bmap F τ N a e ^ k := by
  induction k with
  | zero => exact ⟨𝟙 _, Model.id_mem_orhd _, by rw [rfE_id, pow_zero],
      by rw [Bmap_id, pow_zero]⟩
  | succ k ih =>
    obtain ⟨e', he', h1, h2⟩ := ih
    exact ⟨e' ≫ e, Model.comp_mem_orhd he' he, by rw [rfE_comp he' he, h1, pow_succ],
      by rw [Bmap_comp F τ N a he' he, h2, pow_succ]⟩

variable (hNH : N.toSubgroup ≤ H)

set_option maxHeartbeats 800000 in
-- one long proof unfolding the concrete Frobenioid `X` and Galois groups `Gal(K̄/L)`, `Gal(K̄/L')`
include hNH in
/-- The Frobenioid data for `Φ₁(κ(π)) = κ(π')`: an `n`-th root `g` of `π`, an `n`-th root `G'` of
`π'`, and `β_Ψ(σg/g) = (galPairEquiv σ) G'/G'`. -/
theorem exists_kummer_data (hτ : OrhdCompat F α τ N a) (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) (π : (fixL H)ˣ)
    (π' : (fixL (H.map (α : GK p E →* GK p E')))ˣ)
    (hR : RelB (F := F) (α := α) (τ := τ) (N := N) (a := a) H π π') :
    ∃ (g : K̄ˣ) (hg : g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) π) (G' : K̄ˣ)
      (hG' : G' ^ n = Units.map (algebraMap (fixL (H.map (α : GK p E →* GK p E'))) K̄ :
        fixL (H.map (α : GK p E →* GK p E')) →* K̄) π'),
      ∀ σ : K̄ ≃ₐ[fixL H] K̄,
        betaPsi F τ N a H n hs (KummerTheory.kummerFun g (KummerTheory.smul_pow_of_pow_eq hg) σ) =
          KummerTheory.kummerFun G' (KummerTheory.smul_pow_of_pow_eq hG')
            (galPairEquiv α H hH hH' σ) := by
  obtain ⟨eπ, heπ, h1, h2⟩ := hR
  obtain ⟨g, hg⟩ : ∃ g : K̄ˣ, g ^ n = Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) π := by
    haveI := finiteDimensional_fixL_padic H hH
    haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
    exact ⟨_, KummerTheory.kummerRoot_pow n (fixL H) K̄ π⟩
  have hgN : ∀ ν ∈ (XN N a).base.H, ν • g = g := fun ν hν =>
    root_fixed N a H hH n hs hNH π g hg hν
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hg0 : 0 ≤ ord p (Additive.ofMul g) := by
    have h := ord_rfE_nonneg heπ
    rw [h1] at h
    change 0 ≤ ord p (Additive.ofMul (Units.map (algebraMap (fixL H) K̄ : fixL H →* K̄) π)) at h
    rw [← hg, ofMul_pow, map_nsmul, nsmul_eq_mul] at h
    exact nonneg_of_mul_nonneg_right h hn0
  obtain ⟨eg, heg, hrg⟩ : ∃ e : XN N a ⟶ XN N a, e ∈ Orhd 𝐏E (XN N a) ∧ rfE e = g :=
    ⟨endY (XN N a) g hgN (ord_mem_gammaQ g) hg0,
      endY_mem_orhd (XN N a) g hgN (ord_mem_gammaQ g) hg0,
      rfE_endY (XN N a) g hgN (ord_mem_gammaQ g) hg0⟩
  obtain ⟨G', hG'def⟩ : ∃ G', Bmap F τ N a eg = G' := ⟨_, rfl⟩
  -- `G'^n = π'`
  have hG' : G' ^ n = Units.map (algebraMap (fixL (H.map (α : GK p E →* GK p E'))) K̄ :
      fixL (H.map (α : GK p E →* GK p E')) →* K̄) π' := by
    obtain ⟨en, hen, hn1, hn2⟩ := exists_pow_orhd (F := F) (τ := τ) (N := N) (a := a) heg n
    have : en = eπ := rfE_injective_orhd hen heπ (by rw [hn1, h1, hrg]; exact hg)
    have e1 : Bmap F τ N a en = Bmap F τ N a eπ := congrArg _ this
    rw [← hG'def]
    exact hn2.symm.trans (e1.trans h2)
  refine ⟨g, hg, G', hG', fun σ => ?_⟩
  -- the cocycle identity
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, KummerTheory.kummerFun g (KummerTheory.smul_pow_of_pow_eq hg) σ = ζ :=
    ⟨_, rfl⟩
  rw [hζdef]
  have hζN : ∀ ν ∈ (XN N a).base.H, ν • KummerTheory.Mu.val ζ = KummerTheory.Mu.val ζ :=
    fun ν hν => mu_fixed N a n hs.muSat ζ hν
  have hζ0 : 0 ≤ ord p (Additive.ofMul (KummerTheory.Mu.val ζ)) := (ord_mu n ζ).ge
  obtain ⟨eζ, heζ, hrζ⟩ : ∃ e : XN N a ⟶ XN N a, e ∈ Orhd 𝐏E (XN N a) ∧
      rfE e = KummerTheory.Mu.val ζ :=
    ⟨endY (XN N a) _ hζN (ord_mem_gammaQ _) hζ0,
      endY_mem_orhd (XN N a) _ hζN (ord_mem_gammaQ _) hζ0,
      rfE_endY (XN N a) _ hζN (ord_mem_gammaQ _) hζ0⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : GK p E, (galFixMulEquiv H hH σ : GK p E) = σ₀ := ⟨_, rfl⟩
  have hconj : Model.conj (galIso N a σ₀) eg = eg ≫ eζ := by
    refine rfE_injective_orhd (Model.conj_mem_orhd _ heg) (Model.comp_mem_orhd heg heζ) ?_
    rw [rfE_conj_galHom N a σ₀ heg, rfE_comp heg heζ, hrg, hrζ,
      ← hζdef, KummerTheory.val_kummerFun, ← hσ₀, smul_galFixMulEquiv H hH σ, mul_div_cancel]
  have hB : α σ₀ • G' = G' * Bmap F τ N a eζ := by
    rw [← hG'def, ← Bmap_conj hτ σ₀ heg, hconj, Bmap_comp F τ N a heg heζ]
  refine mu_eq_kummerFun G' _ _ _ ?_
  rw [val_betaPsi F τ N a H n hs ζ heζ hrζ, galPairEquiv_apply, hσ₀]
  change _ = ((α σ₀ • G' : K̄ˣ) : K̄)
  rw [hB, Units.val_mul, mul_comm]

include hNH in
/-- **`Φ₁(κ(π)) = κ(π')`** when `B(e_π) = π'`. -/
theorem h1PairMap_kummer_unif (hτ : OrhdCompat F α τ N a) (n : ℕ) [NeZero n]
    (hs : IsSaturated N a H n) (π : (fixL H)ˣ)
    (π' : (fixL (H.map (α : GK p E →* GK p E')))ˣ)
    (hR : RelB (F := F) (α := α) (τ := τ) (N := N) (a := a) H π π') :
    haveI := finiteDimensional_fixL_padic H hH
    haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
    haveI := finiteDimensional_fixL_padic _ hH'
    haveI := hasKummerRoots (K := fixL (H.map (α : GK p E →* GK p E'))) (Ω := K̄) n
    PairCompat.h1PairMap n (galPairEquiv α H hH hH') (betaPsi F τ N a H n hs)
        (betaPsi_smul F α τ N a (ratFunTw_of_orhdCompat hτ) H hH hH' n hs)
        (KummerTheory.kummer n (fixL H) K̄ π) =
      KummerTheory.kummer n (fixL (H.map (α : GK p E →* GK p E'))) K̄ π' := by
  refine (exists_kummer_data H hH hH' hNH hτ n hs π π' hR).elim fun g h => ?_
  refine h.elim fun hg h => h.elim fun G' h => h.elim fun hG' hc => ?_
  haveI := finiteDimensional_fixL_padic H hH
  haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
  haveI := finiteDimensional_fixL_padic _ hH'
  haveI := hasKummerRoots (K := fixL (H.map (α : GK p E →* GK p E'))) (Ω := K̄) n
  exact PairCompat.h1PairMap_kummer n _ _ _ g hg G' hG' hc

/-- **[FrdII], Theorem 2.4(ii), for `C_v`**: for every equivalence `Ψ : C_v(E) ≌ C_v(E')` of
perfected `p`-adic Frobenioids there is `α : G_E ≃ₜ* G_{E'}` (induced by `Ψ_Base`) such that for
every `X = (G_E/N, a)` there are `τ ∈ G_{E'}` and the `Ψ`-twisted rational functions `ρ` of
`Ψ X` (`hρ`, as in `Thm24ii.lean`) for which: for every `(n, H)`-saturated `X` with `N ⊆ H`
(`H`, `α(H)` open), the isomorphism `F_N(X) ≅ F_N(Ψ X)` of Theorem 2.4(i) (`fngEquiv`), followed
by `F_N(Ψ X) → H²(K̄^{α(H)}, μ_n) ≅ ℤ/n` (`fnPsi`, `h2MuEquiv`), is the natural isomorphism
`F_N(X) ≅ ℤ/n` (`fnEquiv`). -/
theorem thm24Pf_ii (F : FrobPf p E ⥤ FrobPf p E') [F.IsEquivalence] :
    ∃ α : GK p E ≃ₜ* GK p E', ∀ (N : OpenNormalSubgroup (GK p E)) (a : gammaQ),
      ∃ (τ : GK p E') (hρ : ∀ (σ' : GK p E') (v : Model.ouAut (F.obj (XN N a))),
          ratFunTw τ (KummerClass.conjU (Model.ouAut (F.obj (XN N a))) (jPsi F N a α σ') v) =
            σ' • ratFunTw τ v),
        ∀ (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))
          (hH' : IsOpen ((H.map (α : GK p E →* GK p E')) : Set (GK p E'))),
          N.toSubgroup ≤ H → ∀ (n : ℕ) [NeZero n] (hs : IsSaturated N a H n) (x : FN N a H n),
          haveI := finiteDimensional_fixL_padic _ hH'
          PadicField.h2MuEquiv p (fixL (H.map (α : GK p E →* GK p E'))) K̄
              (Nat.pos_of_ne_zero (NeZero.ne n))
              (fnPsi F α τ N a hρ H hH' n (fngEquiv (continuous_galHom N a) H n
                (continuous_jPsi F N a α) (Model.autEquiv F (XN N a)) (mem_ouAut_iff F (XN N a))
                α (jPsi_apply F N a α) x)) =
            fnEquiv N a H hH n hs x := by
  refine (exists_galHom_compat_orhd F).elim fun α hα => ⟨α, fun N a => ?_⟩
  refine (hα N a).elim fun hstab hτex => ?_
  refine hτex.elim fun τ hτ => ⟨τ, ratFunTw_of_orhdCompat hτ, fun H hH hH' hNH n _ hs x => ?_⟩
  refine (exists_unif_rel H hH hNH hτ hstab hH').elim fun π h => h.elim fun π' h => ?_
  refine h.elim fun hπ h => h.elim fun hπ' hR => ?_
  have hk := h1PairMap_kummer_unif H hH hH' hNH hτ n hs π π' hR
  haveI := finiteDimensional_fixL_padic H hH
  haveI := finiteDimensional_fixL_padic _ hH'
  haveI := hasKummerRoots (K := fixL H) (Ω := K̄) n
  refine (PairCompat.pairing_unrChar_kummer n (galPairEquiv α H hH hH')
    (betaPsi F τ N a H n hs) (betaPsi_smul F α τ N a (ratFunTw_of_orhdCompat hτ) H hH hH' n hs)
    hπ hπ' hk).elim fun hpair hunit => ?_
  exact thm24ii_of_pairing F α τ N a (ratFunTw_of_orhdCompat hτ) H hH hH' n hs _ _ hpair hunit x

end PAdicGalois

end Frobenioid

end Iut
