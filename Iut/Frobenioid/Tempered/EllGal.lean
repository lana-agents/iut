/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllB

/-!
# The Galois × deck action on `Mero K` and `ActCompat` (MR18, route B-an)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

In [EtTh] Def 3.3 and Ex 3.9 the group acting on the universal combinatorial covering `Ÿ_∞` is
an extension of the Galois group of the base field by the deck group; on the analytic model
`Ÿ_∞ = 𝔾_m^an` over a complete algebraically closed `K = Ω` it acts by
`f(Ü) ↦ σ(f)(c⁻¹·Ü)` (`σ` an isometric automorphism of `Ω` fixing `q`, acting on coefficients;
`c ∈ Deck t` a deck transformation). This file constructs that action and proves the
compatibility `ActCompat` of `EllB.lean` for it, so that `radB`/`radData` apply to the genuine
analytic action of any group `G` mapping to it (the map `Π^tp → GalDeck t` is MR18 T7c):

* `IsoAut t`: the isometric ring automorphisms of `K` fixing `q` (for `K = Ω ⊇ L ∋ q`, the group
  `Gal(Ω/L)` of isometric automorphisms fixing `L`, `galL φ`, lies in it: `galL_le_isoAut`);
  `σ(s) = ±s` for `s² = q` (`gal_s_eq`), so `σ` maps `Deck t` to itself (`Deck.gal`);
* `GalDeck t = Deck t ⋊ IsoAut t`, acting on `Mero K` (`galDeckHom`; `Mero.gal` = `Mero.map σ`)
  and on the elliptic prime set (`EllPrime t`: components fixed by `σ` and shifted by `c`,
  cusps `α ↦ c·σ(α)`);
* **`ellDiv_galDeck`**: `div(x • f) = div(f) ∘ x⁻¹`, and log-meromorphic functions are preserved;
* **`actCompat_galDeck`**: `ActCompat` for `G` acting on `GalDeckMero γ` through any
  `γ : G →* GalDeck t`. The pure deck action (`actCompat_deck`) is the case `γ = inl ∘ ρ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K)

/-! ### `Mero.map` and the scalings -/

section MapScale

variable {L Ω : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [NontriviallyNormedField Ω] [CompleteSpace Ω] [IsUltrametricDist Ω]
  (φ : L →+* Ω) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

lemma Entire.map_scale (c : Lˣ) (f : Entire L) :
    Entire.map φ hφ (Entire.scale c f) =
      Entire.scale (Units.map φ.toMonoidHom c) (Entire.map φ hφ f) :=
  Entire.ext_coeff (funext fun n => by
    simp only [Entire.coeff_map, Entire.coeff_scale, map_mul, map_zpow₀, Units.coe_map]
    rfl)

/-- **`φ(f(c·Ü)) = φ(f)(φ(c)·Ü)`.** -/
lemma Mero.map_scale (c : Lˣ) (x : Mero L) :
    Mero.map φ hφ (Mero.scale c x) = Mero.scale (Units.map φ.toMonoidHom c) (Mero.map φ hφ x) := by
  have : (Mero.map φ hφ).comp (Mero.scale c) =
      (Mero.scale (Units.map φ.toMonoidHom c)).comp (Mero.map φ hφ) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire L)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← Mero.ofE, Mero.scale_ofE, Mero.map_ofE, Mero.map_ofE, Mero.scale_ofE,
        Entire.map_scale])
  exact RingHom.congr_fun this x

lemma Mero.map_map {Ω' : Type*} [NontriviallyNormedField Ω'] [CompleteSpace Ω']
    [IsUltrametricDist Ω'] (ψ : Ω →+* Ω') (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : Mero L) :
    Mero.map ψ hψ (Mero.map φ hφ x) = Mero.map (ψ.comp φ) (fun x => by simp [hψ, hφ]) x := by
  have : (Mero.map ψ hψ).comp (Mero.map φ hφ) =
      Mero.map (ψ.comp φ) (fun x => by simp [hψ, hφ]) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire L)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← Mero.ofE, Mero.map_ofE, Mero.map_ofE, Mero.map_ofE, Entire.map_map])
  exact RingHom.congr_fun this x

lemma Mero.map_congr {φ' : L →+* Ω} (hφ' : ∀ x, ‖φ' x‖ = ‖x‖) (h : φ = φ') (x : Mero L) :
    Mero.map φ hφ x = Mero.map φ' hφ' x := by
  subst h; rfl

end MapScale

/-! ### Isometric automorphisms fixing `q` -/

/-- **The isometric ring automorphisms of `K` fixing the Tate parameter `q`.** -/
def IsoAut : Subgroup (RingAut K) where
  carrier := {σ | (∀ x, ‖σ x‖ = ‖x‖) ∧ σ t.q = t.q}
  one_mem' := ⟨fun _ => rfl, rfl⟩
  mul_mem' {σ τ} hσ hτ := ⟨fun x => by rw [RingAut.mul_apply, hσ.1, hτ.1],
    by rw [RingAut.mul_apply, hτ.2, hσ.2]⟩
  inv_mem' {σ} hσ := ⟨fun x => by
      rw [← hσ.1 (σ⁻¹ x)]; congr 1; exact RingEquiv.apply_symm_apply σ x,
    by conv_lhs => rw [← hσ.2]
       exact RingEquiv.symm_apply_apply σ t.q⟩

variable {t}

lemma IsoAut.norm (σ : IsoAut t) (x : K) : ‖(σ : RingAut K) x‖ = ‖x‖ := σ.2.1 x

lemma IsoAut.q (σ : IsoAut t) : (σ : RingAut K) t.q = t.q := σ.2.2

lemma IsoAut.inv_apply_apply (σ : IsoAut t) (x : K) :
    ((σ⁻¹ : IsoAut t) : RingAut K) ((σ : RingAut K) x) = x :=
  RingEquiv.symm_apply_apply (σ : RingAut K) x

lemma IsoAut.apply_inv_apply (σ : IsoAut t) (x : K) :
    (σ : RingAut K) (((σ⁻¹ : IsoAut t) : RingAut K) x) = x :=
  RingEquiv.apply_symm_apply (σ : RingAut K) x

section GalL

variable {L : Type*} [Field L] (φ : L →+* K)

/-- **`Gal(Ω/L)`**: the isometric automorphisms of `K = Ω` fixing `φ(L)`. -/
def galL : Subgroup (RingAut K) where
  carrier := {σ | (∀ x, ‖σ x‖ = ‖x‖) ∧ ∀ a, σ (φ a) = φ a}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' {σ τ} hσ hτ := ⟨fun x => by rw [RingAut.mul_apply, hσ.1, hτ.1],
    fun a => by rw [RingAut.mul_apply, hτ.2, hσ.2]⟩
  inv_mem' {σ} hσ := ⟨fun x => by
      rw [← hσ.1 (σ⁻¹ x)]; congr 1; exact RingEquiv.apply_symm_apply σ x,
    fun a => by
      conv_lhs => rw [← hσ.2 a]
      exact RingEquiv.symm_apply_apply σ (φ a)⟩

/-- If `q ∈ φ(L)`, then `Gal(Ω/L) ≤ IsoAut t`. -/
lemma galL_le_isoAut {qL : L} (hq : φ qL = t.q) : galL φ ≤ IsoAut t :=
  fun _ hσ => ⟨hσ.1, by rw [← hq]; exact hσ.2 qL⟩

end GalL

/-- **`σ(s) = ±s`** for `s² = q` and `σ` fixing `q`. -/
lemma gal_s_eq (σ : IsoAut t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    (σ : RingAut K) s = s ∨ (σ : RingAut K) s = -s := by
  have h : ((σ : RingAut K) s) ^ 2 = (s : K) ^ 2 := by rw [← map_pow, hs, (IsoAut.q σ)]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

/-- `σ` as a unit map. -/
abbrev IsoAut.u (σ : IsoAut t) : Kˣ →* Kˣ := Units.map (σ : RingAut K).toRingHom.toMonoidHom

lemma IsoAut.coe_u (σ : IsoAut t) (c : Kˣ) : (((IsoAut.u σ) c : Kˣ) : K) = (σ : RingAut K) c := rfl

lemma IsoAut.u_sq (σ : IsoAut t) {c : Kˣ} {k : ℤ} (hc : ((c : Kˣ) : K) ^ 2 = (t.q : K) ^ k) :
    (((IsoAut.u σ) c : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
  rw [IsoAut.coe_u, ← map_pow, hc, map_zpow₀, (IsoAut.q σ)]

lemma IsoAut.u_mul_inv (σ : IsoAut t) (c : Kˣ) : (IsoAut.u σ) ((IsoAut.u (σ⁻¹ : IsoAut t)) c) = c :=
  Units.ext ((IsoAut.apply_inv_apply σ) c)

lemma IsoAut.inv_u_mul (σ : IsoAut t) (c : Kˣ) : (IsoAut.u (σ⁻¹ : IsoAut t)) ((IsoAut.u σ) c) = c :=
  Units.ext ((IsoAut.inv_apply_apply σ) c)

lemma IsoAut.u_mul (σ τ : IsoAut t) (c : Kˣ) :
    (IsoAut.u (σ * τ)) c = (IsoAut.u σ) ((IsoAut.u τ) c) := rfl

/-- `σ` maps deck transformations to deck transformations. -/
def Deck.gal (σ : IsoAut t) (c : Deck t) : Deck t :=
  ⟨(IsoAut.u σ) (c : Kˣ), Deck.idx c, (IsoAut.u_sq σ) (Deck.idx_spec c)⟩

lemma Deck.coe_gal (σ : IsoAut t) (c : Deck t) :
    ((Deck.gal σ c : Deck t) : Kˣ) = (IsoAut.u σ) (c : Kˣ) := rfl

lemma Deck.idx_gal (σ : IsoAut t) (c : Deck t) : Deck.idx (Deck.gal σ c) = Deck.idx c :=
  Deck.idx_eq ((IsoAut.u_sq σ) (Deck.idx_spec c))

variable (t) in
/-- **The action of `IsoAut t` on the deck group.** -/
def galOnDeck : IsoAut t →* MulAut (Deck t) where
  toFun σ :=
    { toFun := Deck.gal σ
      invFun := Deck.gal σ⁻¹
      left_inv := fun c => Subtype.ext ((IsoAut.inv_u_mul σ) c)
      right_inv := fun c => Subtype.ext ((IsoAut.u_mul_inv σ) c)
      map_mul' := fun c d => Subtype.ext (map_mul (IsoAut.u σ) (c : Kˣ) d) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext (Units.ext rfl)
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext (Units.ext rfl)

lemma galOnDeck_apply (σ : IsoAut t) (c : Deck t) : galOnDeck t σ c = Deck.gal σ c := rfl

variable (t) in
/-- **The Galois × deck group** `Deck t ⋊ IsoAut t`. -/
abbrev GalDeck : Type u := Deck t ⋊[galOnDeck t] IsoAut t

/-! ### The Galois action on `Mero K` -/

namespace Mero

/-- `σ` acting on coefficients (`Mero.map σ`). -/
abbrev gal (σ : IsoAut t) : Mero K →+* Mero K := map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ)

lemma gal_ofE (σ : IsoAut t) (f : Entire K) :
    gal σ (ofE f) = ofE (Entire.map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) f) := map_ofE _ _ f

lemma gal_mul_apply (σ τ : IsoAut t) (x : Mero K) : gal σ (gal τ x) = gal (σ * τ) x := by
  rw [gal, gal, Mero.map_map]
  exact Mero.map_congr _ _ _ rfl x

lemma gal_one_apply (x : Mero K) : gal (1 : IsoAut t) x = x := by
  have : gal (1 : IsoAut t) = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Entire K)) (RingHom.ext fun f => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [← ofE, gal_ofE]
      congr 1
      exact Entire.ext_coeff (by rw [Entire.coeff_map]; rfl))
  exact RingHom.congr_fun this x

/-- **`σ(f(c·Ü)) = σ(f)(σ(c)·Ü)`.** -/
lemma gal_scale (σ : IsoAut t) (c : Kˣ) (x : Mero K) :
    gal σ (scale c x) = scale ((IsoAut.u σ) c) (gal σ x) :=
  Mero.map_scale _ _ c x

lemma gal_ne_zero (σ : IsoAut t) {x : Mero K} (hx : x ≠ 0) : gal σ x ≠ 0 :=
  (map_ne_zero _).mpr hx

/-- `ord_α(σ f) = ord_{σ⁻¹ α}(f)`. -/
lemma ord_gal (σ : IsoAut t) {x : Mero K} (hx : x ≠ 0) (α : Kˣ) :
    ord (gal σ x) α = ord x ((IsoAut.u (σ⁻¹ : IsoAut t)) α) := by
  have h := ord_map ((σ : RingAut K) : K →+* K) (IsoAut.norm σ) hx ((IsoAut.u (σ⁻¹ : IsoAut t)) α)
  rwa [show Units.map ((σ : RingAut K) : K →+* K).toMonoidHom
      ((IsoAut.u (σ⁻¹ : IsoAut t)) α) = α from
    (IsoAut.u_mul_inv σ) α] at h

lemma gn_gal (σ : IsoAut t) (x : Mero K) {r : ℝ} (hr : 0 < r) : gn (gal σ x) r = gn x r :=
  gn_map _ (IsoAut.norm σ) x hr

end Mero

/-- `f ↦ σ(f)` as a ring automorphism of `Mero K`. -/
def galEquiv (σ : IsoAut t) : RingAut (Mero K) :=
  RingEquiv.ofRingHom (Mero.gal σ) (Mero.gal σ⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, Mero.gal_mul_apply, mul_inv_cancel, Mero.gal_one_apply]; rfl)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, Mero.gal_mul_apply, inv_mul_cancel, Mero.gal_one_apply]; rfl)

lemma galEquiv_apply (σ : IsoAut t) (x : Mero K) : galEquiv σ x = Mero.gal σ x := rfl

variable (t) in
/-- **The Galois × deck action on `Mero K`**: `⟨c, σ⟩ • f = σ(f)(c⁻¹·Ü)`. -/
def galDeckHom : GalDeck t →* RingAut (Mero K) where
  toFun x := scaleEquiv (((x.left)⁻¹ : Deck t) : Kˣ) * galEquiv x.right
  map_one' := RingEquiv.ext fun f => by
    rw [RingAut.mul_apply, scaleEquiv_apply, galEquiv_apply, SemidirectProduct.one_left,
      SemidirectProduct.one_right, Mero.gal_one_apply, inv_one, Subgroup.coe_one, Mero.scale_one]
    rfl
  map_mul' x y := RingEquiv.ext fun f => by
    simp only [RingAut.mul_apply, scaleEquiv_apply, galEquiv_apply, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right]
    rw [Mero.gal_scale, Mero.scale_scale, Mero.gal_mul_apply, galOnDeck_apply, mul_inv_rev,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_inv, Deck.coe_gal,
      map_inv]

lemma galDeckHom_apply (x : GalDeck t) (f : Mero K) :
    galDeckHom t x f = Mero.scale (((x.left)⁻¹ : Deck t) : Kˣ) (Mero.gal x.right f) := rfl

/-! ### The action on the elliptic prime set -/

/-- `σ` on cusps. -/
def Cusp.gal (σ : IsoAut t) (α : Cusp t) : Cusp t :=
  ⟨(IsoAut.u σ) α.1, α.2.choose, (IsoAut.u_sq σ) α.2.choose_spec⟩

/-- `σ` on the elliptic prime set: components fixed (`σ` is isometric), cusps `α ↦ σ(α)`. -/
def galP (σ : IsoAut t) : EllPrime t → EllPrime t :=
  Sum.elim (fun a => .inl a) fun α => .inr (Cusp.gal σ α)

lemma galP_one (p : EllPrime t) : galP (1 : IsoAut t) p = p := by
  rcases p with a | α
  · rfl
  · exact congrArg Sum.inr (Subtype.ext (Units.ext rfl))

lemma galP_mul (σ τ : IsoAut t) (p : EllPrime t) : galP (σ * τ) p = galP σ (galP τ p) := by
  rcases p with a | α
  · rfl
  · exact congrArg Sum.inr (Subtype.ext (Units.ext rfl))

lemma galP_smul (σ : IsoAut t) (c : Deck t) (p : EllPrime t) :
    galP σ (c • p) = Deck.gal σ c • galP σ p := by
  rcases p with a | α
  · change Sum.inl (a + Deck.idx c) = Sum.inl (a + Deck.idx (Deck.gal σ c))
    rw [Deck.idx_gal]
  · exact congrArg Sum.inr (Subtype.ext (map_mul (IsoAut.u σ) _ _))

instance : MulAction (GalDeck t) (EllPrime t) where
  smul x p := x.left • galP x.right p
  one_smul p := by
    change (1 : GalDeck t).left • galP (1 : GalDeck t).right p = p
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, galP_one, one_smul]
  mul_smul x y p := by
    change (x * y).left • galP (x * y).right p = x.left • galP x.right (y.left • galP y.right p)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, galP_mul, galP_smul, mul_smul,
      galOnDeck_apply]

lemma galDeck_smul_def (x : GalDeck t) (p : EllPrime t) : x • p = x.left • galP x.right p := rfl

/-! ### Compatibility of the divisor map -/

lemma not_cusp_gal (σ : IsoAut t) {α : Kˣ} (hα : ¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) :
    ¬ ∃ k : ℤ, (((IsoAut.u σ) α : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
  rintro ⟨k, hk⟩
  refine hα ⟨k, ?_⟩
  have := (IsoAut.u_sq (σ⁻¹)) hk
  rwa [IsoAut.inv_u_mul] at this

lemma not_cusp_deck (c : Deck t) {α : Kˣ} (hα : ¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) :
    ¬ ∃ k : ℤ, (((c : Kˣ) * α : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
  rintro ⟨k, hk⟩
  refine hα ⟨k - Deck.idx c, ?_⟩
  rw [Units.val_mul, mul_pow, Deck.idx_spec] at hk
  rw [zpow_sub₀ t.q.ne_zero, ← hk, mul_div_cancel_left₀ _ (zpow_ne_zero _ t.q.ne_zero)]

lemma IsLogMero.gal (σ : IsoAut t) {f : Mero K} (hf : IsLogMero t f) :
    IsLogMero t (Mero.gal σ f) :=
  ⟨Mero.gal_ne_zero σ hf.1, fun α hα => by
    rw [Mero.ord_gal σ hf.1]; exact hf.2 _ (not_cusp_gal σ⁻¹ hα)⟩

lemma IsLogMero.scale (c : Deck t) {f : Mero K} (hf : IsLogMero t f) :
    IsLogMero t (Mero.scale (c : Kˣ) f) :=
  ⟨Mero.scale_ne_zero _ hf.1, fun α hα => by
    rw [Mero.ord_scale hf.1]; exact hf.2 _ (not_cusp_deck c hα)⟩

/-- **The Galois action on divisors**: `div(σ f) = div(f) ∘ σ⁻¹`. -/
theorem ellDiv_gal {s : Kˣ} (σ : IsoAut t) {f : Mero K} (hf : f ≠ 0) (p : EllPrime t) :
    ellDiv t s (Mero.gal σ f) p = ellDiv t s f (galP σ⁻¹ p) := by
  rcases p with a | α
  · change compOrd t s (Mero.gal σ f) a = compOrd t s f a
    rw [compOrd, compOrd, compOrdR, compOrdR, Mero.gn_gal σ f (zpow_pos (norm_s_pos s) a)]
  · change (Mero.ord (Mero.gal σ f) α.1 : ℚ) = Mero.ord f (IsoAut.u σ⁻¹ α.1)
    rw [Mero.ord_gal σ hf]

/-- **The divisor map is `GalDeck t`-equivariant**: `div(x • f) = div(f) ∘ x⁻¹`, and `x`
preserves log-meromorphic functions. -/
theorem ellDiv_galDeck {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (x : GalDeck t) {f : Mero K}
    (hf : IsLogMero t f) :
    IsLogMero t (galDeckHom t x f) ∧
      ∀ p : EllPrime t, ellDiv t s (galDeckHom t x f) p = ellDiv t s f (x⁻¹ • p) := by
  refine ⟨(hf.gal x.right).scale (x.left)⁻¹, fun p => ?_⟩
  rw [galDeckHom_apply, ellDiv_scale hs _ (Mero.gal_ne_zero _ hf.1), ellDiv_gal _ hf.1,
    galP_smul, galDeck_smul_def, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
    galOnDeck_apply]

/-! ### `ActCompat` for the Galois × deck action -/

variable {G : Type u} [Group G] (γ : G →* GalDeck t)

/-- `Mero K` with the action of `G` through `γ : G →* GalDeck t`. -/
def GalDeckMero (_γ : G →* GalDeck t) : Type u := Mero K

instance : Field (GalDeckMero γ) := inferInstanceAs (Field (Mero K))

instance : Algebra (Mero K) (GalDeckMero γ) := inferInstanceAs (Algebra (Mero K) (Mero K))

instance : MulSemiringAction G (GalDeckMero γ) :=
  MulSemiringAction.compHom (Mero K) ((galDeckHom t).comp γ)

variable (t) in
/-- `G` acting on the elliptic prime set through `γ`. -/
abbrev galDeckPerm : GalDeck t →* Equiv.Perm (EllPrime t) := MulAction.toPermHom _ _

/-- **`ActCompat` for the genuine analytic action**: for any `γ : G →* Deck t ⋊ IsoAut t`, the
action of `G` on `Mero K` by `f ↦ σ(f)(c⁻¹·Ü)` and on `ℤ ⊕ Cusps` by `(a, α) ↦ (a + idx c, c·σ(α))`
are compatible. -/
theorem actCompat_galDeck (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ActCompat t s ((galDeckPerm t).comp γ) (GalDeckMero γ) := by
  intro g y hy0 _ hl
  have hι : ∀ z : Mero K, Mero.ι (GalDeckMero γ) z = z := fun _ => rfl
  have hlm : IsLogMero t (show Mero K from y) := ⟨hy0, fun α hα => by
    have h := hl α hα
    rw [← hι y, Mero.rord_ι hy0] at h
    exact_mod_cast h⟩
  obtain ⟨h1, h2⟩ := ellDiv_galDeck hs (γ g) hlm
  have hgy : (g • y : GalDeckMero γ) = galDeckHom t (γ g) y := rfl
  refine ⟨⟨1, one_pos, g • y, (pow_one _).symm⟩, fun α hα => ?_, fun p => ?_⟩
  · rw [hgy, ← hι (galDeckHom t (γ g) y), Mero.rord_ι h1.1, h1.2 α hα, Int.cast_zero]
  · rw [show rEllDiv t s (g • y) = ellDiv t s (galDeckHom t (γ g) y) by
        rw [hgy]; exact rEllDiv_ι (R := GalDeckMero γ) hval hs h1.1,
      show rEllDiv t s y = ellDiv t s y from rEllDiv_ι (R := GalDeckMero γ) hval hs hy0, h2,
      ← map_inv]
    rfl

end Iut.Frobenioid.BAn
