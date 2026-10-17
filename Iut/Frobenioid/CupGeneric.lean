/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.DualityH1

/-!
# A generic cup product `H¹(G, ℤ/n) × H¹(G, M) → H²(G, M)`

For a topological group `G`, a discrete `G`-module `M` killed by `n` (on which `g ↦ g • m` is
continuous) and a continuous character `χ : G → ℤ/n`, the cup product of `χ` with a continuous
1-cocycle `ζ` is the 2-cocycle

`(χ ∪ ζ)(g, h) = (g • ζ(h))^{χ̃(g)}`, `χ̃(g) ∈ [0, n)` lifting `χ(g)`

(the formula of local class field theory's `Brauer.cupKummerFun`). This gives
**`CupAux.cupH1G`** `: H¹(G, M) → H²(G, M)`, `κ ↦ χ ∪ κ`, which is

* **natural** (`CupAux.map_cupH1G`): for continuous `φ : G' →* G` and a compatible `f : M →* M'`,
  `φ^*(χ ∪ κ) = (χ ∘ φ) ∪ φ^*κ`;
* **local class field theory's cup product** for `G = Gal(Ω/K)`, `M = μ_n(Ω)`
  (`CupAux.cupH1_eq_cupH1G`: `Brauer.cupH1 n χ = cupH1G … χ`).
-/

open groupCohomology

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

namespace CupAux

section Gen

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
variable (n : ℕ)

/-- The exponent `χ̃(g) ∈ [0, n)` of a character `χ : G → ℤ/n`. -/
def chiExpG (χ : G →* Multiplicative (ZMod n)) (g : G) : ℕ :=
  (Multiplicative.toAdd (χ g)).val

lemma chiExpG_mul [NeZero n] (χ : G →* Multiplicative (ZMod n)) (g h : G) :
    chiExpG n χ (g * h) = (chiExpG n χ g + chiExpG n χ h) % n := by
  simp only [chiExpG, map_mul, toAdd_mul, ZMod.val_add]

lemma pow_mod_of_pow_eq_one {n : ℕ} (hM : ∀ m : M, m ^ n = 1) (m : M) (k : ℕ) :
    m ^ (k % n) = m ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hM, one_pow, one_mul]

/-- The cup product cochain `(χ ∪ ζ)(g, h) = (g • ζ(h))^{χ̃(g)}`. -/
def cupFun (χ : G →* Multiplicative (ZMod n)) (ζ : G → M) : G × G → M :=
  fun gh => (gh.1 • ζ gh.2) ^ chiExpG n χ gh.1

lemma isMulCocycle₂_cupFun [NeZero n] (hM : ∀ m : M, m ^ n = 1)
    (χ : G →* Multiplicative (ZMod n)) {ζ : G → M} (hζ : IsMulCocycle₁ ζ) :
    IsMulCocycle₂ (cupFun n χ ζ) := by
  intro g h k
  simp only [cupFun]
  rw [chiExpG_mul, pow_mod_of_pow_eq_one hM, hζ h k, smul_mul', smul_pow', mul_smul, mul_pow,
    pow_add]
  ac_rfl

lemma cupFun_mul (χ : G →* Multiplicative (ZMod n)) (ζ ζ' : G → M) :
    cupFun n χ (ζ * ζ') = cupFun n χ ζ * cupFun n χ ζ' := by
  funext gh
  simp only [cupFun, Pi.mul_apply, smul_mul', mul_pow]

lemma cupFun_coboundary [NeZero n] (hM : ∀ m : M, m ^ n = 1) (χ : G →* Multiplicative (ZMod n))
    (ξ : M) :
    cupFun n χ (fun g => g • ξ / ξ) = ContH2.dx _ _ (fun g => ((g • ξ) ^ chiExpG n χ g)⁻¹) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [cupFun, ContH2.dx_apply, smul_div', smul_inv', smul_pow', smul_smul]
  rw [chiExpG_mul, pow_mod_of_pow_eq_one hM, pow_add, div_pow]
  mul_abel

variable [TopologicalSpace M] [DiscreteTopology M]

lemma isLocallyConstant_chiExpG {χ : G →* Multiplicative (ZMod n)} (hχ : Continuous χ) :
    IsLocallyConstant (chiExpG n χ) :=
  (IsLocallyConstant.of_discrete
    (fun x : Multiplicative (ZMod n) => (Multiplicative.toAdd x).val)).comp_continuous hχ

lemma isLocallyConstant_cupFun (hact : ∀ m : M, Continuous fun g : G => g • m)
    {χ : G →* Multiplicative (ZMod n)} (hχ : Continuous χ) {ζ : G → M} (hζ : Continuous ζ) :
    IsLocallyConstant (cupFun n χ ζ) := by
  have hζl : IsLocallyConstant ζ := (IsLocallyConstant.iff_continuous ζ).2 hζ
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have e1 : ∀ᶠ q : G × G in nhds (g, h), ζ q.2 = ζ h :=
    (continuous_snd.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq ζ).1 hζl h)
  have e2 : ∀ᶠ q : G × G in nhds (g, h), chiExpG n χ q.1 = chiExpG n χ g :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (isLocallyConstant_chiExpG n hχ) g)
  have e3 : ∀ᶠ q : G × G in nhds (g, h), q.1 • ζ h = g • ζ h :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1
        ((IsLocallyConstant.iff_continuous _).2 (hact (ζ h))) g)
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  simp only [cupFun, h1, h2, h3]

variable [IsTopologicalGroup M] [NeZero n]

/-- The cup product with `χ` on continuous 1-cocycles. -/
noncomputable def cupCocycles (hM : ∀ m : M, m ^ n = 1)
    (hact : ∀ m : M, Continuous fun g : G => g • m) (χ : G →* Multiplicative (ZMod n))
    (hχ : Continuous χ) : ContH1.cocycles G M →* ContH2 G M where
  toFun ζ := ContH2.mk (ContH2.mkCocycle (cupFun n χ ζ)
    (isLocallyConstant_cupFun n hact hχ (ContH1.continuous ζ))
    (isMulCocycle₂_cupFun n hM χ (ContH1.isMulCocycle₁ ζ)))
  map_one' := by
    rw [← map_one (ContH2.mk (G := G) (M := M))]
    congr 1
    refine ContH2.cocycles_ext fun g h => ?_
    simp [cupFun]
  map_mul' ζ ζ' := by
    rw [← map_mul]
    congr 1
    refine ContH2.cocycles_ext fun g h => ?_
    simp only [ContH2.coe_mkCocycle, ContH2.coe_mul_apply, Subgroup.coe_mul,
      cupFun_mul n χ ζ ζ', Pi.mul_apply]

/-- **The cup product** `H¹(G, M) → H²(G, M)`, `κ ↦ χ ∪ κ`, for a character `χ : G → ℤ/n` and an
`n`-torsion discrete `G`-module `M`. -/
noncomputable def cupH1G (hM : ∀ m : M, m ^ n = 1)
    (hact : ∀ m : M, Continuous fun g : G => g • m) (χ : G →* Multiplicative (ZMod n))
    (hχ : Continuous χ) : ContH1 G M →* ContH2 G M :=
  QuotientGroup.lift (ContH1.coboundaries _ _) (cupCocycles n hM hact χ hχ) (by
    rintro ζ ⟨ξ, hξ⟩
    rw [MonoidHom.mem_ker]
    change ContH2.mk _ = 1
    rw [ContH2.mk_eq_one_iff]
    refine ⟨fun g => ((g • ξ) ^ chiExpG n χ g)⁻¹, ?_, ?_⟩
    · have h1 := (IsLocallyConstant.iff_continuous _).2 (hact ξ)
      exact ((h1.prodMk (isLocallyConstant_chiExpG n hχ)).comp fun c => c.1 ^ c.2).inv
    · rw [← cupFun_coboundary n hM]
      simp only [ContH2.coe_mkCocycle]
      congr 1
      funext g
      exact hξ g)

lemma cupH1G_mk (hM : ∀ m : M, m ^ n = 1) (hact : ∀ m : M, Continuous fun g : G => g • m)
    (χ : G →* Multiplicative (ZMod n)) (hχ : Continuous χ) (ζ : ContH1.cocycles G M) :
    cupH1G n hM hact χ hχ (ContH1.mk ζ) = ContH2.mk (ContH2.mkCocycle (cupFun n χ ζ)
      (isLocallyConstant_cupFun n hact hχ (ContH1.continuous ζ))
      (isMulCocycle₂_cupFun n hM χ (ContH1.isMulCocycle₁ ζ))) := rfl

end Gen

section Nat

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
variable {G' M' : Type*} [Group G'] [TopologicalSpace G'] [CommGroup M']
  [MulDistribMulAction G' M'] [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalGroup M']
variable (n : ℕ) [NeZero n]

/-- **Naturality of the cup product**: `φ^*(χ ∪ κ) = (χ ∘ φ) ∪ φ^*κ`. -/
theorem map_cupH1G (hM : ∀ m : M, m ^ n = 1) (hact : ∀ m : M, Continuous fun g : G => g • m)
    (hM' : ∀ m : M', m ^ n = 1) (hact' : ∀ m : M', Continuous fun g : G' => g • m)
    (χ : G →* Multiplicative (ZMod n)) (hχ : Continuous χ) (φ : G' →* G) (hφ : Continuous φ)
    (f : M →* M') (hf : Continuous f) (hcomp : ∀ (g : G') (m : M), f (φ g • m) = g • f m)
    (κ : ContH1 G M) :
    ContH2.map φ hφ f hcomp (cupH1G n hM hact χ hχ κ) =
      cupH1G n hM' hact' (χ.comp φ) (hχ.comp hφ) (ContH1.map φ hφ f hf hcomp κ) := by
  induction κ using ContH1.induction_on with | h ζ => ?_
  rw [cupH1G_mk, ContH1.map_mk, cupH1G_mk, ContH2.map_mk]
  congr 1
  refine ContH2.cocycles_ext fun g h => ?_
  change f ((φ g • ζ (φ h)) ^ chiExpG n χ (φ g)) = (g • f (ζ (φ h))) ^ chiExpG n (χ.comp φ) g
  rw [map_pow, hcomp]
  rfl

end Nat

section LCFT

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
variable (n : ℕ) [NeZero n]

lemma mu_pow_n (m : KummerTheory.Mu n Ω) : m ^ n = 1 := by
  have := Brauer.mu_pow_mod n m n
  rwa [Nat.mod_self, pow_zero, eq_comm] at this

lemma continuous_smul_mu (m : KummerTheory.Mu n Ω) :
    Continuous fun g : Ω ≃ₐ[K] Ω => g • m :=
  (Brauer.isLocallyConstant_smul_mu n m).continuous

/-- **The generic cup product is local class field theory's `Brauer.cupH1`.** -/
theorem cupH1_eq_cupH1G (χ : Brauer.LocChar K Ω n)
    (κ : ContH1 (Ω ≃ₐ[K] Ω) (KummerTheory.Mu n Ω)) :
    Brauer.cupH1 n χ κ =
      cupH1G n (mu_pow_n n) (continuous_smul_mu n) χ.1 (χ.2.continuous) κ := by
  induction κ using ContH1.induction_on with | h ζ => ?_
  rfl

end LCFT

end CupAux

end Frobenioid

end Iut
