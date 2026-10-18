/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110H1
import Iut.Reconstruction.Local.Cor110WeilBar
import LocalClassFieldTheory.Brauer.DualityH1

/-!
# Naturality of `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` ([AbsTopIII], Cor. 1.10 (a); [AbsAnab], Prop. 1.2.1 (vii))

[AbsTopIII], Corollary 1.10 (i) (a) (`Topics in Absolute Anabelian Geometry III.txt`,
l.2395–2398):

> "Then one constructs the natural isomorphism `H²(G_k, μ_Ẑ(G_k)) ∼→ Ẑ` "group-theoretically"
> from `G_k` via the algorithm described in the proof of [Mzk9], Proposition 1.2.1, (vii)."

[Mzk9] = [AbsAnab], Proposition 1.2.1 (vii) (`Absolute Anabelian Geometry.txt`, l.467–474):

> "(vii) The morphism `H²(K_1, μ_{Q/Z}(K_1)) ∼→ H²(K_2, μ_{Q/Z}(K_2))` induced by `α` (cf. (vi))
> preserves the "residue map" `H²(K_i, μ_{Q/Z}(K_i)) ∼→ Q/Z` of local class field theory"

Mochizuki's proof (l.517–555) goes through the Brauer group `H²(G_K, K̄^×)` and the unramified
part. Here we argue with cup products instead, which is the "group-theoretic algorithm" of (b)
(l.2401–2406: "By applying the isomorphism of (a) [and the cup-product in group cohomology]"):

* **group-theoretic Kummer classes**: for `y ∈ lim→_U U^ab` with `G`-invariant `y^n`, the cocycle
  `kumFun y : g ↦ g(y)/y ∈ μ_n(G)` (`kumCocycle`); it is transported by `ψ : G ≃ₜ* G'`
  (`kumFun_barMap`);
* **group-theoretic cup products** `cupG χ c ∈ H²(G, μ_n(G))` of a character `χ : G → ℤ/n` and a
  cocycle `c` with values in `μ_n(G)`, `(g, h) ↦ (g · c(h))^{χ(g)}`, transported by `ψ`
  (`h2MuGEquivOf_cupG`);
* the **unramified character** `chiUnr : G_k → Ẑ → ℤ/n` (`frobAb`), which is group-theoretic
  (`chiUnr_map`);
* for `y` in the Weil part `k̄^×(G_k)` (`Cor110WeilBar.lean`) with `y^n = artin(a)` at the top
  level, the class `chiUnr ∪ κ(y)` corresponds to `χ ∪ κ(a)` and has **invariant `v(a)`**
  (`toAdd_h2MuEquiv_cupG`, from LCFT's `PadicField.pairingH1_kummer`, `⟨χ, κ(a)⟩ = χ(artin a)`);
* choosing `a` a uniformiser (`v(a) = 1`), the class `u = chiUnr ∪ κ(y)` is a generator with
  invariant `1`, and `ψ` maps `u` to a class of the same kind for `k'`
  (frobenius-preservation `frobAb_abEquiv`, `map_abWeil`, `barMap_topBar`), whence
  **`h2MuEquiv_h2MuGEquivOf`**: `ψ_*` preserves the invariant `H²(G_k, μ_n(G_k)) ≅ ℤ/n` for every
  `n`, and **`h2ZHatGEquiv_H2ZHatGEquivOf`** ([AbsAnab], Proposition 1.2.1 (vii)):
  `h2ZHatGEquiv k' (H2ZHatGEquivOf ψ x) = h2ZHatGEquiv k x` for every isomorphism of topological
  groups `ψ : G_k ≃ₜ* G_{k'}`.
-/

namespace Iut.Reconstruction

open PadicField IntermediateField MonoidHom KummerTheory Brauer ContH2 groupCohomology

set_option linter.unusedSectionVars false

noncomputable section

universe u

/-! ### Group-theoretic Kummer cocycles and cup products -/

section GroupTheoretic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {n : ℕ}

theorem barConj_mul_apply (g h : G) (z : AbBar G) :
    barConj G (g * h) z = barConj G g (barConj G h z) := by
  rw [barConj_mul]
  rfl

/-- The elements of `G` near `g` move an element of `lim→ U^ab` as `g` does. -/
theorem eventually_barConj_eq (z : AbBar G) (g : G) :
    ∀ᶠ g' in nhds g, barConj G g' z = barConj G g z := by
  obtain ⟨i, x, hx⟩ := exists_toBar G z
  have hopen : IsOpen ((fun u => g * u) '' (sg i : Set G)) :=
    isOpenMap_mul_left g _ (isOpen_sg i)
  filter_upwards [hopen.mem_nhds ⟨1, one_mem _, mul_one g⟩] with g' hg'
  obtain ⟨u, hu, rfl⟩ := hg'
  rw [barConj_mul_apply, hx, barConj_toBar_of_mem hu]

theorem isLocallyConstant_smul_muN (m : muN G n) : IsLocallyConstant fun g : G => g • m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [eventually_barConj_eq (m : AbBar G) g] with g' hg'
  exact Subtype.ext hg'

/-- **The group-theoretic Kummer cocycle** `g ↦ g(y)/y ∈ μ_n(G)`, for `y ∈ lim→ U^ab` with
`G`-invariant `y^n`. -/
def kumFun (y : AbBar G) (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) : G → muN G n :=
  fun g => ⟨barConj G g y / y, by rw [mem_muN, div_pow, ← map_pow, hy, div_self']⟩

theorem coe_kumFun (y : AbBar G) (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) (g : G) :
    (kumFun y hy g : AbBar G) = barConj G g y / y := rfl

theorem isMulCocycle₁_kumFun (y : AbBar G) (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) :
    IsMulCocycle₁ (kumFun y hy) := by
  intro g h
  apply Subtype.ext
  change barConj G (g * h) y / y = barConj G g (barConj G h y / y) * (barConj G g y / y)
  rw [barConj_mul_apply, map_div, div_mul_div_cancel]

theorem isLocallyConstant_kumFun (y : AbBar G) (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) :
    IsLocallyConstant (kumFun y hy) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [eventually_barConj_eq y g] with g' hg'
  apply Subtype.ext
  change barConj G g' y / y = barConj G g y / y
  rw [hg']

/-- The Kummer cocycle as a continuous cocycle. -/
def kumCocycle (y : AbBar G) (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) :
    ContH1.cocycles G (muN G n) :=
  ContH1.mkCocycle (kumFun y hy) (isLocallyConstant_kumFun y hy).continuous
    (isMulCocycle₁_kumFun y hy)

/-- The exponent `χ̃(g) ∈ [0, n)` of a character `χ : G → ℤ/n`. -/
def chiExpG (χ : G →* Multiplicative (ZMod n)) (g : G) : ℕ := (Multiplicative.toAdd (χ g)).val

theorem chiExpG_mul [NeZero n] (χ : G →* Multiplicative (ZMod n)) (g h : G) :
    chiExpG χ (g * h) = (chiExpG χ g + chiExpG χ h) % n := by
  simp only [chiExpG, map_mul, toAdd_mul, ZMod.val_add]

theorem muN_pow_mod (z : muN G n) (m : ℕ) : z ^ (m % n) = z ^ m := by
  have hz : z ^ n = 1 := Subtype.ext (mem_muN.1 z.2)
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hz, one_pow, one_mul]

/-- **The group-theoretic cup product** `(χ ∪ c)(g, h) = (g · c(h))^{χ(g)}`. -/
def cupFunG (χ : G →* Multiplicative (ZMod n)) (c : G → muN G n) : G × G → muN G n :=
  fun gh => (gh.1 • c gh.2) ^ chiExpG χ gh.1

theorem isMulCocycle₂_cupFunG [NeZero n] (χ : G →* Multiplicative (ZMod n)) {c : G → muN G n}
    (hc : IsMulCocycle₁ c) : IsMulCocycle₂ (cupFunG χ c) := by
  intro g h k
  simp only [cupFunG]
  rw [chiExpG_mul, muN_pow_mod, hc h k, smul_mul', smul_pow', mul_smul, mul_pow, pow_add]
  rw [mul_comm ((g • h • c k) ^ chiExpG χ g) ((g • h • c k) ^ chiExpG χ h), mul_assoc]

theorem isLocallyConstant_cupFunG {χ : G →* Multiplicative (ZMod n)} (hχ : IsLocallyConstant χ)
    {c : G → muN G n} (hc : IsLocallyConstant c) : IsLocallyConstant (cupFunG χ c) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have e1 : ∀ᶠ q : G × G in nhds (g, h), c q.2 = c h :=
    (continuous_snd.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq c).1 hc h)
  have e2 : ∀ᶠ q : G × G in nhds (g, h), chiExpG χ q.1 = chiExpG χ g :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (hχ.comp _) g)
  have e3 : ∀ᶠ q : G × G in nhds (g, h), q.1 • c h = g • c h :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (isLocallyConstant_smul_muN (c h)) g)
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  simp only [cupFunG, h1, h2, h3]

/-- **The cup product** `χ ∪ c ∈ H²(G, μ_n(G))` of a continuous character `χ : G → ℤ/n`
and a continuous cocycle `c : G → μ_n(G)`. -/
def cupG [NeZero n] (χ : G →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ)
    (c : ContH1.cocycles G (muN G n)) : H2MuG G n :=
  ContH2.mk (mkCocycle (cupFunG χ c) (isLocallyConstant_cupFunG hχ
    ((IsLocallyConstant.iff_continuous _).2 c.2.1)) (isMulCocycle₂_cupFunG χ c.2.2))

variable {G' : Type*} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']

theorem barMap_pow_invariant (ψ : G ≃ₜ* G') {y : AbBar G}
    (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n) (g' : G') :
    barConj G' g' (barMap ψ y ^ n) = barMap ψ y ^ n := by
  rw [← map_pow, ← ψ.apply_symm_apply g', ← barMap_barConj, hy]

/-- **The Kummer cocycle is transported by `ψ`.** -/
theorem kumFun_barMap (ψ : G ≃ₜ* G') {y : AbBar G} (hy : ∀ g : G, barConj G g (y ^ n) = y ^ n)
    (g : G) :
    kumFun (barMap ψ y) (barMap_pow_invariant ψ hy) (ψ g) = muNEquivOf ψ n (kumFun y hy g) :=
  Subtype.ext (by
    change barConj G' (ψ g) (barMap ψ y) / barMap ψ y = barMap ψ (barConj G g y / y)
    rw [map_div, barMap_barConj])

/-- **The cup product is transported by `ψ`.** -/
theorem h2MuGEquivOf_cupG [NeZero n] (ψ : G ≃ₜ* G') (χ : G →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) (χ' : G' →* Multiplicative (ZMod n)) (hχ' : IsLocallyConstant χ')
    (hχψ : ∀ g, χ' (ψ g) = χ g) (c : ContH1.cocycles G (muN G n))
    (c' : ContH1.cocycles G' (muN G' n)) (hc : ∀ g, c' (ψ g) = muNEquivOf ψ n (c g)) :
    h2MuGEquivOf ψ n (cupG χ hχ c) = cupG χ' hχ' c' := by
  change ContH2.mk _ = ContH2.mk _
  congr 1
  refine cocycles_ext fun a b => ?_
  change muNEquivOf ψ n ((ψ.symm a • c (ψ.symm b)) ^ chiExpG χ (ψ.symm a)) =
    (a • c' b) ^ chiExpG χ' a
  have h1 : chiExpG χ (ψ.symm a) = chiExpG χ' a := by
    rw [chiExpG, chiExpG, ← hχψ, ContinuousMulEquiv.apply_symm_apply]
  rw [map_pow, muNEquivOf_smul, ContinuousMulEquiv.apply_symm_apply, ← hc,
    ContinuousMulEquiv.apply_symm_apply, h1]

end GroupTheoretic

/-! ### `G = G_k`: the unramified character and the invariant of `χ ∪ κ` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- The projection `Ẑ → ℤ/n`. -/
def zhatProj (n : ℕ+) : Multiplicative ZHat →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicative ((Pi.evalAddMonoidHom (fun m : ℕ+ => ZMod m) n).comp
    (AddSubgroup.subtype ZHat))

theorem zhatProj_apply (n : ℕ+) (z : Multiplicative ZHat) :
    zhatProj n z = Multiplicative.ofAdd
      (((Multiplicative.toAdd z : ZHat) : ∀ m : ℕ+, ZMod m) n) := rfl

theorem zhatProj_intToZHat (n : ℕ+) (m : ℤ) :
    zhatProj n (Multiplicative.ofAdd (intToZHat m)) = Multiplicative.ofAdd (m : ZMod n) := rfl

variable (p k Ω) in
/-- **The unramified character** `G_k → G^unr ≅ Ẑ → ℤ/n`, `Frob ↦ 1`. -/
def chiUnr (n : ℕ+) : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod n) :=
  (zhatProj n).comp ((frobAb p k Ω).comp (abMk (Ω ≃ₐ[k] Ω)))

theorem chiUnr_apply (n : ℕ+) (σ : Ω ≃ₐ[k] Ω) :
    chiUnr p k Ω n σ = zhatProj n (unrZHatHom p k Ω σ) := by
  change zhatProj n (frobAb p k Ω (QuotientGroup.mk σ)) = _
  rw [frobAb_mk]
  rfl

theorem isLocallyConstant_chiUnr (n : ℕ+) : IsLocallyConstant (chiUnr p k Ω n) := by
  have hc : Continuous fun σ : Ω ≃ₐ[k] Ω =>
      ((Multiplicative.toAdd (unrZHatHom p k Ω σ) : ZHat) : ∀ m : ℕ+, ZMod m) n :=
    (continuous_apply n).comp (continuous_subtype_val.comp
      (continuous_toAdd.comp (continuous_unrZHatHom (p := p))))
  have h := ((IsLocallyConstant.iff_continuous _).2 hc).comp
    (fun z : ZMod n => Multiplicative.ofAdd z)
  have e : ⇑(chiUnr p k Ω n) = (fun z : ZMod n => Multiplicative.ofAdd z) ∘
      (fun σ : Ω ≃ₐ[k] Ω => ((Multiplicative.toAdd (unrZHatHom p k Ω σ) : ZHat) :
        ∀ m : ℕ+, ZMod m) n) :=
    funext fun σ => chiUnr_apply n σ
  rw [e]
  exact h

/-- `chiUnr` as a local character. -/
def chiUnrLoc (n : ℕ+) : LocChar k Ω n :=
  ⟨chiUnr p k Ω n, isLocallyConstant_chiUnr (p := p) (k := k) (Ω := Ω) n⟩

/-- **`χ(artin a) = v(a)`** for the unramified character. -/
theorem artinChar_chiUnr (n : ℕ+) (a : kˣ) :
    artinChar (p := p) (n : ℕ) (chiUnrLoc (p := p) (Ω := Ω) n) a =
      ((v p (a : k) : ℤ) : ZMod n) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((multAbEquiv p k Ω a : abWeil _) : TopologicalAbelianization (Ω ≃ₐ[k] Ω))
  have hlift : AlgEquiv.restrictNormalHom (maxAbelian k Ω) g = artin p k Ω a := by
    have h := galAbEquiv_mk (p := p) (K := k) (Ω := Ω) g
    rw [hg, galAbEquiv_multAbEquiv] at h
    exact h.symm
  rw [artinChar_eq (n : ℕ) _ a g hlift]
  change Multiplicative.toAdd (zhatProj n (frobAb p k Ω (QuotientGroup.mk g))) = _
  rw [hg, frobAb_multAbEquiv, zhatProj_intToZHat, toAdd_ofAdd]

section Functorial

variable {p' : ℕ} [Fact p'.Prime]
variable {k' : Type u} [Field k'] [Algebra ℚ_[p'] k'] [FiniteDimensional ℚ_[p'] k']
variable {Ω' : Type u} [Field Ω'] [Algebra k' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] k' Ω']
  [IsAlgClosed Ω'] [IsGalois k' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- **The unramified character is group-theoretic.** -/
theorem chiUnr_map (ψ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω' ≃ₐ[k'] Ω')) (n : ℕ+) (σ : Ω ≃ₐ[k] Ω) :
    chiUnr p' k' Ω' n (ψ σ) = chiUnr p k Ω n σ := by
  change zhatProj n (frobAb p' k' Ω' (abEquiv ψ (QuotientGroup.mk σ))) =
    zhatProj n (frobAb p k Ω (QuotientGroup.mk σ))
  rw [frobAb_abEquiv (p := p)]

end Functorial

/-! ### The invariant of `χ_unr ∪ κ(y)` -/

theorem pow_invariant_of_eq_topBar {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {x : TopologicalAbelianization G} {y : AbBar G}
    (hyn : y ^ n = topBar G x) (g : G) : barConj G g (y ^ n) = y ^ n := by
  rw [hyn, barConj_topBar]

theorem val_smul_units (σ : Ω ≃ₐ[k] Ω) (α : Ωˣ) : ((σ • α : Ωˣ) : Ω) = σ (α : Ω) := rfl

/-- **The group-theoretic Kummer cocycle is the Kummer cocycle**: under `μ_n(G_k) ≅ μ_n(Ω)`,
`kumFun y` is `σ ↦ σ(α)/α` for the image `α ∈ Ωˣ` of `y ∈ k̄^×(G_k)`. -/
theorem muNEquiv_kumFun (n : ℕ) [NeZero n] {y : AbBar (Ω ≃ₐ[k] Ω)}
    (hyW : y ∈ weilBar (Ω ≃ₐ[k] Ω)) (hy : ∀ g, barConj _ g (y ^ n) = y ^ n)
    (hα : ∀ σ : Ω ≃ₐ[k] Ω, σ • weilBarHom p ⟨y, hyW⟩ ^ n = weilBarHom p ⟨y, hyW⟩ ^ n)
    (σ : Ω ≃ₐ[k] Ω) :
    muNEquiv p k Ω n (kumFun y hy σ) = kummerFun (weilBarHom p ⟨y, hyW⟩) hα σ := by
  apply Mu.ext
  rw [val_muNEquiv, val_kummerFun, muQZHom_apply]
  set z : unitsBar (Ω ≃ₐ[k] Ω) := ⟨barConj _ σ y / y, muQZ_le_unitsBar (p := p)
    (muN_le_muQZ _ n (kumFun y hy σ).2)⟩
  have h1 := weilBarHom_eq_unitsBarEquiv (p := p) z
  have h2 : (⟨(z : AbBar (Ω ≃ₐ[k] Ω)), unitsBar_le_weilBar (Ω ≃ₐ[k] Ω) z.2⟩ :
      weilBar (Ω ≃ₐ[k] Ω)) =
      ⟨barConj _ σ y, barConj_mem_weilBar σ hyW⟩ / ⟨y, hyW⟩ := rfl
  rw [h2, map_div] at h1
  change (unitsBarEquiv p k Ω z : Ωˣ) = _
  rw [← h1]
  apply Units.ext
  rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, val_smul_units]
  congr 1
  exact weilBarHom_barConj (p := p) σ ⟨y, hyW⟩

/-- **The invariant of `χ_unr ∪ κ(y)` is `v(a)`**, for `y ∈ k̄^×(G_k)` with `y^n = artin(a)` at
the top level: the group-theoretic cup product corresponds to `χ_unr ∪ κ(a)`, whose invariant is
`χ_unr(artin a) = v(a)` (`PadicField.pairingH1_kummer`). -/
theorem toAdd_h2MuEquiv_cupG (n : ℕ+) (a : kˣ) {y : AbBar (Ω ≃ₐ[k] Ω)}
    (hyW : y ∈ weilBar (Ω ≃ₐ[k] Ω)) (hyn : y ^ (n : ℕ) = topBar _ (multAbEquiv p k Ω a)) :
    Multiplicative.toAdd (h2MuEquiv p k Ω n.pos (h2MuGEquiv p k Ω n
      (cupG (chiUnr p k Ω n) (isLocallyConstant_chiUnr n)
        (kumCocycle y (pow_invariant_of_eq_topBar hyn))))) = ((v p (a : k) : ℤ) : ZMod n) := by
  set α := weilBarHom p ⟨y, hyW⟩
  have hαa : α ^ (n : ℕ) = Units.map (algebraMap k Ω : k →* Ω) a := by
    have e : (⟨y, hyW⟩ : weilBar (Ω ≃ₐ[k] Ω)) ^ (n : ℕ) = ⟨topBar _ (multAbEquiv p k Ω a),
        topBar_mem_weilBar (G := Ω ≃ₐ[k] Ω) (multAbEquiv p k Ω a).2⟩ := Subtype.ext hyn
    calc α ^ (n : ℕ) = weilBarHom p ((⟨y, hyW⟩ : weilBar (Ω ≃ₐ[k] Ω)) ^ (n : ℕ)) :=
          (map_pow _ _ _).symm
      _ = weilBarHom p ⟨topBar _ (multAbEquiv p k Ω a),
          topBar_mem_weilBar (G := Ω ≃ₐ[k] Ω) (multAbEquiv p k Ω a).2⟩ := by rw [e]
      _ = _ := weilBarHom_topBar a
  have hα := smul_pow_of_pow_eq hαa
  have hcoc : h2MuGEquiv p k Ω n (cupG (chiUnr p k Ω n) (isLocallyConstant_chiUnr n)
      (kumCocycle y (pow_invariant_of_eq_topBar hyn))) =
      cupH1 (n : ℕ) (chiUnrLoc (p := p) (Ω := Ω) n) (ContH1.mk (kummerCocycle α hα)) := by
    rw [cupH1_mk]
    change ContH2.mk _ = ContH2.mk _
    congr 1
    refine cocycles_ext fun g h => ?_
    change muNEquiv p k Ω n ((g • kumFun y (pow_invariant_of_eq_topBar hyn) h) ^
      chiExpG (chiUnr p k Ω n) g) =
      (g • kummerFun α hα h) ^ chiExp (n : ℕ) (chiUnr p k Ω n) g
    rw [map_pow, muNEquiv_smul,
      muNEquiv_kumFun (p := p) (n : ℕ) hyW (pow_invariant_of_eq_topBar hyn) hα h]
    rfl
  haveI := hasKummerRoots (K := k) (Ω := Ω) (n : ℕ)
  have hpair : pairingH1 (p := p) (n : ℕ) (chiUnrLoc (p := p) (Ω := Ω) n) (kummer (n : ℕ) k Ω a) =
      artinChar (p := p) (n : ℕ) (chiUnrLoc (p := p) (Ω := Ω) n) a :=
    pairingH1_kummer (p := p) (n : ℕ) (chiUnrLoc (p := p) (Ω := Ω) n) a
  rw [kummer_eq a α hαa, artinChar_chiUnr] at hpair
  rw [hcoc]
  exact hpair

variable (p k Ω) in
/-- The invariant `H²(G_k, μ_n(G_k)) ≅ ℤ/n`. -/
def invG (n : ℕ+) : H2MuG (Ω ≃ₐ[k] Ω) n ≃* Multiplicative (ZMod n) :=
  (h2MuGEquiv p k Ω n).trans (h2MuEquiv p k Ω n.pos)

/-! ### Existence of a generator -/

theorem exists_weilBar_root (n : ℕ+) (a : kˣ) :
    ∃ y ∈ weilBar (Ω ≃ₐ[k] Ω), y ^ (n : ℕ) = topBar _ (multAbEquiv p k Ω a) := by
  obtain ⟨α, hα⟩ := Brauer.exists_root (n : ℕ) n.pos (Units.map (algebraMap k Ω : k →* Ω) a)
  obtain ⟨⟨y, hyW⟩, hy⟩ := weilBarHom_surjective (p := p) (k := k) (Ω := Ω) α
  refine ⟨y, hyW, ?_⟩
  have e := weilBarHom_topBar (p := p) (k := k) (Ω := Ω) a
  have h1 : weilBarHom p (⟨y, hyW⟩ ^ (n : ℕ)) = weilBarHom p
      ⟨topBar _ (multAbEquiv p k Ω a), topBar_mem_weilBar (G := Ω ≃ₐ[k] Ω)
        (multAbEquiv p k Ω a).2⟩ :=
    calc weilBarHom p (⟨y, hyW⟩ ^ (n : ℕ)) = α ^ (n : ℕ) := by rw [map_pow, hy]
      _ = Units.map (algebraMap k Ω : k →* Ω) a := hα
      _ = _ := e.symm
  exact congrArg Subtype.val (weilBarHom_injective h1)

end Galois

/-! ### Naturality -/

section Natural

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable {p' : ℕ} [hp' : Fact p'.Prime]
variable {k' : Type u} [Field k'] [Algebra ℚ_[p'] k'] [FiniteDimensional ℚ_[p'] k']
variable {Ω' : Type u} [Field Ω'] [Algebra k' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] k' Ω']
  [IsAlgClosed Ω'] [IsGalois k' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- A class whose invariant is `1`, built from a uniformiser `a` (`v(a) = 1`). -/
theorem invG_cupG_of_v_eq_one (n : ℕ+) (a : kˣ) (ha : v p (a : k) = 1) {y : AbBar (Ω ≃ₐ[k] Ω)}
    (hyW : y ∈ weilBar (Ω ≃ₐ[k] Ω)) (hyn : y ^ (n : ℕ) = topBar _ (multAbEquiv p k Ω a)) :
    invG p k Ω n (cupG (chiUnr p k Ω n) (isLocallyConstant_chiUnr n)
      (kumCocycle y (pow_invariant_of_eq_topBar hyn))) = Multiplicative.ofAdd 1 := by
  have h := toAdd_h2MuEquiv_cupG n a hyW hyn
  rw [ha, Int.cast_one] at h
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  exact h

/-- In a group `A ≃ ℤ/n`, an element with invariant `1` generates. -/
theorem eq_pow_of_invG_eq_one {A : Type*} [CommGroup A] {n : ℕ+}
    (e : A ≃* Multiplicative (ZMod n)) {u : A} (hu : e u = Multiplicative.ofAdd 1) (z : A) :
    z = u ^ (Multiplicative.toAdd (e z)).val := by
  apply e.injective
  rw [map_pow, hu, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

/-- **[AbsAnab], Proposition 1.2.1 (vii), at level `n`**: every isomorphism of topological groups
`ψ : G_k ≃ₜ* G_{k'}` preserves the invariant `H²(G_k, μ_n(G_k)) ≅ ℤ/n`, for the group-theoretic
`μ_n(G_k)`. -/
theorem invG_h2MuGEquivOf (ψ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω' ≃ₐ[k'] Ω')) (n : ℕ+)
    (z : H2MuG (Ω ≃ₐ[k] Ω) n) :
    invG p' k' Ω' n (h2MuGEquivOf ψ n z) = invG p k Ω n z := by
  -- a uniformiser of `k` and an `n`-th root of its image at the top level
  obtain ⟨y, hyW, hyn⟩ := exists_weilBar_root (p := p) (Ω := Ω) n (unif p k)
  set u := cupG (chiUnr p k Ω n) (isLocallyConstant_chiUnr n)
    (kumCocycle y (pow_invariant_of_eq_topBar hyn))
  have hu : invG p k Ω n u = Multiplicative.ofAdd 1 :=
    invG_cupG_of_v_eq_one n (unif p k) v_unif hyW hyn
  -- its transport is a class of the same kind for `k'`
  have hx' : abEquiv ψ ((multAbEquiv p k Ω (unif p k) : abWeil _) :
      TopologicalAbelianization _) ∈ abWeil (Ω' ≃ₐ[k'] Ω') :=
    (abEquiv_mem_abWeil_iff _ _).2 (multAbEquiv p k Ω (unif p k)).2
  set a' : k'ˣ := (multAbEquiv p' k' Ω').symm ⟨_, hx'⟩
  have ha'x : ((multAbEquiv p' k' Ω' a' : abWeil _) : TopologicalAbelianization _) =
      abEquiv ψ ((multAbEquiv p k Ω (unif p k) : abWeil _) : TopologicalAbelianization _) := by
    rw [MulEquiv.apply_symm_apply]
  have ha' : v p' (a' : k') = 1 := by
    have h1 := frobAb_multAbEquiv (p := p') (Ω := Ω') a'
    rw [ha'x, frobAb_abEquiv (p := p) ψ, frobAb_multAbEquiv, v_unif] at h1
    exact (intToZHat_injective (Multiplicative.ofAdd.injective h1)).symm
  have hy'W := barMap_mem_weilBar ψ hyW
  have hy'n : barMap ψ y ^ (n : ℕ) = topBar _ (multAbEquiv p' k' Ω' a') := by
    rw [← map_pow, hyn, barMap_topBar, ha'x]
  have hu' : h2MuGEquivOf ψ n u = cupG (chiUnr p' k' Ω' n) (isLocallyConstant_chiUnr n)
      (kumCocycle (barMap ψ y) (pow_invariant_of_eq_topBar hy'n)) :=
    h2MuGEquivOf_cupG ψ _ _ _ _ (chiUnr_map ψ n) _ _
      (fun g => kumFun_barMap ψ (pow_invariant_of_eq_topBar hyn) g)
  have hinv' : invG p' k' Ω' n (h2MuGEquivOf ψ n u) = Multiplicative.ofAdd 1 := by
    rw [hu']
    exact invG_cupG_of_v_eq_one n a' ha' hy'W hy'n
  rw [eq_pow_of_invG_eq_one (invG p k Ω n) hu z, map_pow, map_pow, map_pow, hinv', hu]

/-- **[AbsAnab], Proposition 1.2.1 (vii); [AbsTopIII], Corollary 1.10 (a)**: the isomorphism
`H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` is **group-theoretic**: for every isomorphism of topological groups
`ψ : G_k ≃ₜ* G_{k'}` (no relation between `k` and `k'` assumed),
`h2ZHatGEquiv k' (ψ_* x) = h2ZHatGEquiv k x`. -/
theorem h2ZHatGEquiv_H2ZHatGEquivOf (ψ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω' ≃ₐ[k'] Ω'))
    (x : H2ZHatG (Ω ≃ₐ[k] Ω)) :
    h2ZHatGEquiv p' k' Ω' (H2ZHatGEquivOf ψ x) = h2ZHatGEquiv p k Ω x := by
  apply Multiplicative.toAdd.injective
  refine Subtype.ext (funext fun n => ?_)
  rw [h2ZHatGEquiv_apply, h2ZHatGEquiv_apply]
  exact congrArg Multiplicative.toAdd (invG_h2MuGEquivOf ψ n (x.1 n))

end Natural

end

end Iut.Reconstruction
