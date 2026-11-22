/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.PivTate
import Iut.Frobenioid.Tempered.TateFrobK

/-!
# Tempered Frobenioid data on the genuine `Π_v` at `v ∈ V^bad` (MR18 run 17, T10)

MR18's B-an tempered Frobenioid data `radDataL` (`EllDescent.lean`) only need an action
`γ : G →* GalDeck t` of the group `G` on `Ÿ_∞ = 𝔾_m^an` that is defined over the base field
(`IsLRat`). `TateFrobK.lean` builds it on tfg's Tate objects from `character₂`, which does not
exist for `X̲_v` (tfg's `DoubleData` needs `x − e ∈ R^×`). This file builds it on the genuine
`Π_v` from the characters of `PivTate.lean`:

* `galDeckOfChar ψ σ`: `g ↦ ((−1)^{ε(g)} s^{−χ(g)}, σ(g))` for any `ψ = (χ, ε) : G →* ℤ × ℤ/2`
  and Galois part `σ` fixing `s` (the formula of `tateGalDeck`, with `ψ` in place of
  `character₂`), `isLRat_galDeckOfChar`;
* `tateParamK`: the Tate parameter `q_v` of `X̲_v` in an analytic field `𝕂 ⊇ K_v`;
* **`tempFrobV`**: the tempered Frobenioid data on `Π_v` (`G = (Piv D v).carrier`) with
  `ψ = psiV` (graph character and `√(x − e)`-character of `X̲_v`) and `σ = sigmaTemp ∘ (Π_v ≃ Π^tp)`
  (the Galois action of `Π_v → G_{K_v}` extended isometrically to `𝕂`), `tempFrobV_isFrobenioid`.

**Analytic setup (explicit parameters, not debts).** As in `TateGalSigma`/`TateFrobK` (setup
accepted by the lead after phase-2 run 15): a complete nonarchimedean field `𝕂` with an isometric
`K_v`-algebra structure, a dense `K_v`-embedding `ι : k̄ → 𝕂` of the algebraic closure of `K_v` in
`Ω`, and `ValueGroupRat` (values of `𝕂` in `‖q_v‖^ℚ`). `PadicEmbed`'s `ℂ_p` does not fit directly:
the norm of `adicCompletion` is `|·|_p^{[K_v : ℚ_p]}`, so `K_v → ℂ_p` is not isometric; the
completion of `k̄` with the spectral norm (Mathlib `spectralNorm.normedField`) is the intended
instance (not built here).
-/

namespace Iut.Multiradial.PrimeStrip

open NumberField TemperedFundamentalGroups Pi1.Orbifold Iut.Anabelian TateCurvesTheta
  Iut.Frobenioid Iut.Frobenioid.BAn KummerTheory.Curve
open scoped Valued

noncomputable section

universe u

/-! ### The Galois × deck action from a character `ψ = (χ, ε)` -/

section Generic

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} {G : Type u} [Group G]

/-- **The Galois × deck action of `G` from `ψ = (χ, ε)`**: `g ↦ ((−1)^ε s^{−χ}, σ g)`. -/
def galDeckOfChar {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (ψ : G →* Multiplicative ℤ × Multiplicative (ZMod 2)) (σ : G →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) : G →* GalDeck t where
  toFun g := ⟨(tateDeckOfChar hs).comp ψ g, σ g⟩
  map_one' := SemidirectProduct.ext (map_one _) (map_one _)
  map_mul' g h := SemidirectProduct.ext (by
      rw [SemidirectProduct.mul_left, map_mul]
      change _ = _ * galOnDeck t (σ g) (tateDeckOfChar hs _)
      rw [gal_tateDeckOfChar hs (hσ g)]
      rfl) (map_mul σ g h)

lemma galDeckOfChar_left {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (ψ : G →* Multiplicative ℤ × Multiplicative (ZMod 2)) (σ : G →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) (g : G) :
    (galDeckOfChar hs ψ σ hσ g).left = tateDeckOfChar hs (ψ g) := rfl

lemma galDeckOfChar_right {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    (ψ : G →* Multiplicative ℤ × Multiplicative (ZMod 2)) (σ : G →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s) (g : G) :
    (galDeckOfChar hs ψ σ hσ g).right = σ g := rfl

variable {k : Type u} [NontriviallyNormedField k] [NormedAlgebra k K]

/-- **The action is defined over `k`** when `s ∈ k` and `σ` fixes `k`. -/
theorem isLRat_galDeckOfChar [TopologicalSpace G] [IsTopologicalGroup G] {s : Kˣ}
    (hs : (s : K) ^ 2 = t.q) {s₀ : k} (hs₀ : algebraMap k K s₀ = s)
    (ψ : G →* Multiplicative ℤ × Multiplicative (ZMod 2)) (σ : G →* IsoAut t)
    (hσ : ∀ g, ((σ g : IsoAut t) : RingAut K) s = s)
    (hσk : ∀ g, ((σ g : IsoAut t) : RingAut K) ∈ galL (algebraMap k K)) :
    IsLRat (algebraMap k K) (galDeckOfChar hs ψ σ hσ) := fun g =>
  ⟨hσk g, tateDeckOfChar_mem_range hs hs₀ _⟩

end Generic

/-! ### The genuine data at `v ∈ V^bad` -/

variable {D : InitialThetaData.{0}} {v : FinitePlace ↥(fieldOfModuli D.F D.E)} (hv : v ∈ D.VBad)
  (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedAlgebra (Kv D v) K]

/-- **The Tate parameter `q_v` of `X̲_v` in `𝕂`.** -/
def tateParamK : TateParameter K where
  q := Units.map (algebraMap (Kv D v) K).toMonoidHom (qv D v hv)
  norm_lt_one := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, norm_algebraMap']
    exact (tateS hv).t.norm_lt_one

/-- `s_v ∈ 𝕂^×`. -/
def svK : Kˣ := Units.map (algebraMap (Kv D v) K).toMonoidHom (sv hv)

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma svK_sq : ((svK hv K : Kˣ) : K) ^ 2 = (tateParamK hv K).q := by
  change algebraMap (Kv D v) K (sv hv) ^ 2 = algebraMap (Kv D v) K (qv D v hv)
  rw [← map_pow, sv_sq_val]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma exists_q₀ : ∃ q₀ : Kv D v, algebraMap (Kv D v) K q₀ = (tateParamK hv K).q :=
  ⟨qv D v hv, rfl⟩

variable {K} {ι : KummerTheory.Curve.kbar (Kv D v) (Genuine.Ω (Xv D v).E) →ₐ[Kv D v] K}
  (hι : DenseRange ι)

/-- **The Galois part `Π_v → IsoAut`**: `Π_v ≃ Π^tp → G_{K_v}` extended isometrically to `𝕂`. -/
def sigmaV : (Piv D v).carrier →* IsoAut (tateParamK hv K) :=
  (sigmaTemp (DGv D v) _ (Vv D v) (Vv_comap D v) hι (exists_q₀ hv K)).comp
    (pivEquivTemp D v hv).toMulEquiv.toMonoidHom

lemma sigmaV_algebraMap (g : (Piv D v).carrier) (a : Kv D v) :
    ((sigmaV hv hι g : IsoAut (tateParamK hv K)) : RingAut K) (algebraMap (Kv D v) K a) =
      algebraMap (Kv D v) K a :=
  sigmaTemp_algebraMap hι (exists_q₀ hv K) _ a

lemma sigmaV_s (g : (Piv D v).carrier) :
    ((sigmaV hv hι g : IsoAut (tateParamK hv K)) : RingAut K) (svK hv K) = svK hv K :=
  sigmaV_algebraMap hv hι g _

/-- **The Galois × deck action of `Π_v` on `Ÿ_∞`** from `ψ_v = (χ_v, ε_v)`. -/
def galDeckV : (Piv D v).carrier →* GalDeck (tateParamK hv K) :=
  galDeckOfChar (svK_sq hv K) (psiV hv) (sigmaV hv hι) (sigmaV_s hv hι)

theorem isLRat_galDeckV : IsLRat (algebraMap (Kv D v) K) (galDeckV hv hι) :=
  isLRat_galDeckOfChar (svK_sq hv K) (s₀ := (sv hv : Kv D v)) rfl _ _ _ fun g =>
    ⟨((sigmaV hv hι g : IsoAut (tateParamK hv K))).2.1, sigmaV_algebraMap hv hι g⟩

/-- **The tempered Frobenioid data on the genuine `Π_v`** at `v ∈ V^bad` (unramified layer,
`B₀` = log-meromorphic functions on `Ÿ_∞` defined over `K_v`), from the characters of `X̲_v`. -/
abbrev tempFrobV (hval : ValueGroupRat (tateParamK hv K)) :
    TemperedFrobenioidData (Piv D v).carrier :=
  radDataL (algebraMap (Kv D v) K) norm_algebraMap_k (galDeckV hv hι) (svK hv K) hval
    (svK_sq hv K) (isLRat_galDeckV hv hι)

theorem tempFrobV_isFrobenioid (hval : ValueGroupRat (tateParamK hv K)) :
    IsFrobenioid (Model.toElem (tempFrobV hv hι hval).Φ₀ (tempFrobV hv hι hval).B₀
      (tempFrobV hv hι hval).div₀) :=
  radDataL_isFrobenioid _ hval _ _

end

end Iut.Multiradial.PrimeStrip
