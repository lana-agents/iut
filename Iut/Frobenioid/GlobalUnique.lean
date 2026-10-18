/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalTorsor
import Iut.Frobenioid.Thm64iv

/-!
# Uniqueness of `F^⊛_mod ≅ F^⊛_MOD` after realification (IUT III, Example 3.6(iii))

IUT III, Example 3.6(iii) (l.7203–7220 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller
Theory III.txt`): "By composing the isomorphisms of Frobenioids of (i) and (ii), one thus obtains a
natural isomorphism of Frobenioids `F^⊛_mod ≅ F^⊛_MOD` that induces the identity morphism
`F^×_mod → F^×_mod` on the associated rational function monoids […]. One verifies immediately that
although the above isomorphism of Frobenioids is not necessarily determined by the condition that
it induce the identity morphism on `F^×_mod`, the induced isomorphism between the respective
perfections [hence also on realifications] of `F^⊛_mod`, `F^⊛_MOD` is completely determined by this
condition."

## "Inducing the identity on the rational functions"

For a model Frobenioid with rational function monoid `B` (here `B = K^×`, resp. `B = ℝ·Φ^birat`
for the realification), two morphisms `φ, ψ : X → Y` of the same Frobenius degree differ in the
birationalization by the unique element `u_φ − u_ψ ∈ B = O^×(Y^birat)`. A functor `G` induces
the identity on `B` ([FrdI], Corollary 4.10) iff `u_{Gφ} − u_{Gψ} = u_φ − u_ψ` for all such pairs:

* `GlobalFrobenioid.InducesIdUnits` (`C → C`), `TorsorFrob.InducesIdUnits` (`C → F^⊛_MOD`: the
  `n`-equivariant maps `Gφ`, `Gψ` differ by the factor `u_φ/u_ψ ∈ K^×`);
* `GlobalRealified.InducesIdRatFun` (`C^⊩ → C^⊩`).

`TorsorFrob.ofModel` satisfies `InducesIdUnits` (`TorsorFrob.inducesIdUnits_ofModel`).

## (a) Non-uniqueness on `F^⊛_mod`

`GlobalFrobenioid.twist c` (for any `c : Ob(C) → K^×`) sends `α ↦ α + div(c_α)` and
`(n, Z, u) : α → β` to `(n, Z, u·c_α^n/c_β)`. It preserves Frobenius degrees and zero divisors,
induces the identity on `K^×` (`inducesIdUnits_twist`) and is naturally isomorphic to the identity
(`twistIso`), so `twist c ⋙ ofModel` is another equivalence `F^⊛_mod ≌ F^⊛_MOD` with all the
properties of `ofModel` (`TorsorFrob.isEquivalence_twist_ofModel`,
`TorsorFrob.inducesIdUnits_twist_ofModel`), but **`twist c ⋙ ofModel ≠ ofModel`** for `c ≡ 2`
(`TorsorFrob.twist_ofModel_ne`).

## (b) Uniqueness on the realification

**`GlobalRealified.unique_of_inducesIdRatFun`**: every autoequivalence `G` of `C^⊩(K)` that induces
the identity on `ℝ·Φ^birat` is isomorphic to the identity functor by a **unique** natural
isomorphism (`Unique (G ≅ 𝟭 _)`). Along the way: `Ψ_Φ(G) = id` (`psiPhi_eq_self`) and
`deg(G) = 1` (`degOf_eq_one`). The proof: `Ψ_Φ(z) − z` only depends on `z` modulo `ℝ·Φ^birat`,
i.e. on `deg^arith(z)` (`ker deg^arith = ℝ·Φ^birat`, `ker_degArith_le`); comparing with divisors
supported at a single finite place `p ≠ q` shows that its `q`-coordinate is both `≥ 0` and `≤ 0`.
Uniqueness of the natural isomorphism holds because an isomorphism `X ≅ Y` in `C^⊩` is unique
(`GlobalRealified.hom_eq_of_isIso`).

**Deviation from the text.** (1) Up to natural isomorphism, the functor `F^⊛_mod ≅ F^⊛_MOD` is
already determined before realification in the examples above (`twistIso`); what (a) shows is that
the condition does not pin down the functor itself, while (b) shows that on the realification it
pins it down up to a *unique* natural isomorphism. (2) We state (b) for the realification
`C^⊩(K)` (with `ℝ·Φ^birat`, where `μ(K)` dies) rather than for the perfection: `C^⊩(K)` is the
realification of both `F^⊛_mod` and (via `TorsorFrob.equivModel`) `F^⊛_MOD`, so the induced
isomorphism of realifications is an autoequivalence of `C^⊩(K)` to which (b) applies.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### (a) Twisting by rational functions -/

namespace GlobalFrobenioid

/-- **Inducing the identity on `K^×`** for a functor `C → C`: two morphisms of the same degree
differ by the same rational function before and after. -/
def InducesIdUnits (Ψ : GlobalFrobenioid K ⥤ GlobalFrobenioid K) : Prop :=
  ∀ ⦃X Y : GlobalFrobenioid K⦄ (φ ψ : X ⟶ Y), φ.deg = ψ.deg →
    (Ψ.map φ).u - (Ψ.map ψ).u = φ.u - ψ.u

lemma rel_eq {X Y : GlobalFrobenioid K} (φ : X ⟶ Y) :
    (φ.deg : ℕ) • X.α + φ.div = Y.α + divZ K φ.u := φ.rel

/-- **The twist by `c : Ob(C) → K^×`**: `α ↦ α + div(c_α)`, `(n, Z, u) ↦ (n, Z, u·c_α^n/c_β)`. -/
noncomputable def twist (c : GlobalFrobenioid K → Kˣ) :
    GlobalFrobenioid K ⥤ GlobalFrobenioid K where
  obj X := ⟨X.base, X.α + divZ K (Additive.ofMul (c X))⟩
  map {X Y} φ := Model.mk' φ.deg φ.base φ.div φ.div_mem
      (φ.u + (φ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y)) (by
        have hd := TorsorFrob.div_eq_of_rel φ
        change (φ.deg : ℕ) • (X.α + divZ K (Additive.ofMul (c X))) + φ.div =
          (Y.α + divZ K (Additive.ofMul (c Y))) +
            divZ K (φ.u + (φ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y))
        rw [hd, map_sub, map_add, map_nsmul, smul_add]
        abel)
  map_id X := Model.hom_ext rfl rfl rfl (by
    change (0 : Additive Kˣ) + ((1 : ℕ+) : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c X) = 0
    rw [PNat.one_coe, one_smul, zero_add, sub_self])
  map_comp {X Y Z} φ ψ := Model.hom_ext rfl rfl rfl (by
    change ψ.u + (ψ.deg : ℕ) • φ.u + ((ψ.deg * φ.deg : ℕ+) : ℕ) • Additive.ofMul (c X) -
        Additive.ofMul (c Z) =
      (ψ.u + (ψ.deg : ℕ) • Additive.ofMul (c Y) - Additive.ofMul (c Z)) +
        (ψ.deg : ℕ) • (φ.u + (φ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y))
    rw [PNat.mul_coe, mul_smul, smul_sub, smul_add]
    abel)

@[simp] lemma twist_map_deg (c : GlobalFrobenioid K → Kˣ) {X Y : GlobalFrobenioid K}
    (φ : X ⟶ Y) : ((twist c).map φ).deg = φ.deg := rfl

@[simp] lemma twist_map_div (c : GlobalFrobenioid K → Kˣ) {X Y : GlobalFrobenioid K}
    (φ : X ⟶ Y) : ((twist c).map φ).div = φ.div := rfl

/-- **The twist induces the identity on `K^×`.** -/
theorem inducesIdUnits_twist (c : GlobalFrobenioid K → Kˣ) : InducesIdUnits (twist c) :=
  fun X Y φ ψ h => by
    change (φ.u + (φ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y)) -
      (ψ.u + (ψ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y)) = φ.u - ψ.u
    rw [h]
    abel

/-- The isomorphism `X ≅ twist c X`, `(1, 0, c_X^{-1})`. -/
noncomputable def twistHom (c : GlobalFrobenioid K → Kˣ) (X : GlobalFrobenioid K) :
    X ⟶ (twist c).obj X :=
  Model.mk1 (𝟙 _) 0 (effConeZ K).zero_mem (-Additive.ofMul (c X)) (by
    change X.α + 0 = X.α + divZ K (Additive.ofMul (c X)) + divZ K (-Additive.ofMul (c X))
    rw [map_neg]
    abel)

lemma isIso_twistHom (c : GlobalFrobenioid K → Kˣ) (X : GlobalFrobenioid K) :
    IsIso (twistHom c X) :=
  Model.isIso_of _ rfl (isIso_pt _) rfl

/-- **The twist is naturally isomorphic to the identity.** -/
noncomputable def twistIso (c : GlobalFrobenioid K → Kˣ) : 𝟭 (GlobalFrobenioid K) ≅ twist c :=
  NatIso.ofComponents (fun X => @asIso _ _ _ _ (twistHom c X) (isIso_twistHom c X))
    fun {X Y} φ => by
    refine Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ ?_
    · change (1 : ℕ+) * φ.deg = φ.deg * 1
      rw [one_mul, mul_one]
    · change (0 : ArithDivZ K) + ((1 : ℕ+) : ℕ) • φ.div = φ.div + (φ.deg : ℕ) • 0
      rw [PNat.one_coe, one_smul, zero_add, smul_zero, add_zero]
    · change -Additive.ofMul (c Y) + ((1 : ℕ+) : ℕ) • φ.u =
        (φ.u + (φ.deg : ℕ) • Additive.ofMul (c X) - Additive.ofMul (c Y)) +
          (φ.deg : ℕ) • -Additive.ofMul (c X)
      rw [PNat.one_coe, one_smul, smul_neg]
      abel

instance (c : GlobalFrobenioid K → Kˣ) : (twist c).IsEquivalence :=
  Functor.isEquivalence_of_iso (twistIso c)

/-- `2 ∈ K^×` is not a root of unity. -/
lemma not_isOfFinOrder_two : ¬ IsOfFinOrder (Units.mk0 (2 : K) two_ne_zero) := by
  intro h
  obtain ⟨n, hn, h2⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  have h3 : ((2 ^ n : ℕ) : K) = 1 := by
    have := congrArg Units.val h2
    simpa using this
  have h4 : 2 ^ n = 1 := by exact_mod_cast h3
  have := Nat.one_lt_two_pow hn.ne'
  omega

/-- `div(2) ≠ 0`. -/
lemma divZ_two_ne : divZ K (Additive.ofMul (Units.mk0 (2 : K) two_ne_zero)) ≠ 0 := by
  intro h1
  refine not_isOfFinOrder_two (K := K) ((divZ_mem_effConeZ_iff _).mp ?_)
  rw [h1]
  exact (effConeZ K).zero_mem

end GlobalFrobenioid

namespace TorsorFrob

open GlobalFrobenioid

/-- **Inducing the identity on `K^×`** for a functor `C → F^⊛_MOD`: for `φ, ψ : X → Y` of the
same degree, the elementary morphisms `Gφ`, `Gψ` differ by the factor `u_φ/u_ψ ∈ K^×`. -/
def InducesIdUnits (G : GlobalFrobenioid K ⥤ TorsorFrob K) : Prop :=
  ∀ ⦃X Y : GlobalFrobenioid K⦄ (φ ψ : X ⟶ Y), φ.deg = ψ.deg → ∀ t : (G.obj X).T,
    (G.map φ).ψ t = Additive.toMul (α := Kˣ) (φ.u - ψ.u) • (G.map ψ).ψ t

/-- **`Ψ ⋙ ofModel` induces the identity on `K^×` if `Ψ` does** (and preserves Frobenius
degrees). -/
theorem inducesIdUnits_comp_ofModel {Ψ : GlobalFrobenioid K ⥤ GlobalFrobenioid K}
    (hdeg : ∀ ⦃X Y : GlobalFrobenioid K⦄ (φ : X ⟶ Y), (Ψ.map φ).deg = φ.deg)
    (hΨ : GlobalFrobenioid.InducesIdUnits Ψ) : InducesIdUnits (Ψ ⋙ ofModel K) :=
  fun X Y φ ψ h t => by
    have hu : (Ψ.map φ).u = (φ.u - ψ.u) + (Ψ.map ψ).u := by
      rw [← hΨ φ ψ h]; abel
    change Additive.toMul (α := Kˣ) (Ψ.map φ).u * (show Kˣ from t) ^ ((Ψ.map φ).deg : ℕ) =
      Additive.toMul (α := Kˣ) (φ.u - ψ.u) * (Additive.toMul (α := Kˣ) (Ψ.map ψ).u *
        (show Kˣ from t) ^ ((Ψ.map ψ).deg : ℕ))
    rw [hdeg, hdeg, h, hu, toMul_add, mul_assoc]

/-- **`ofModel` induces the identity on `K^×`.** -/
theorem inducesIdUnits_ofModel : InducesIdUnits (ofModel K) :=
  inducesIdUnits_comp_ofModel (Ψ := 𝟭 _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

/-- **(a)** The twisted comparison functor `twist c ⋙ ofModel` induces the identity on `K^×`. -/
theorem inducesIdUnits_twist_ofModel (c : GlobalFrobenioid K → Kˣ) :
    InducesIdUnits (twist c ⋙ ofModel K) :=
  inducesIdUnits_comp_ofModel (fun _ _ _ => rfl) (inducesIdUnits_twist c)

/-- It preserves Frobenius degrees. -/
lemma twist_ofModel_map_deg (c : GlobalFrobenioid K → Kˣ) {X Y : GlobalFrobenioid K}
    (φ : X ⟶ Y) : ((twist c ⋙ ofModel K).map φ).deg = φ.deg := rfl

/-- It is an equivalence `F^⊛_mod ≌ F^⊛_MOD`. -/
instance isEquivalence_twist_ofModel (c : GlobalFrobenioid K → Kˣ) :
    (twist c ⋙ ofModel K).IsEquivalence := inferInstance

lemma triv_injective {α β : ArithDivZ K} (h : (triv α : TorsorFrob K) = triv β) : α = β := by
  obtain ⟨-, -, h3⟩ := TorsorObj.mk.inj h
  have h4 := congrFun (eq_of_heq h3) (1 : Kˣ)
  simpa using h4

/-- **IUT III, Example 3.6(iii), non-uniqueness**: the equivalence `F^⊛_mod ≌ F^⊛_MOD` is not
determined by preserving Frobenius degrees and inducing the identity on `K^×`: the twist by
`c ≡ 2` is another one. -/
theorem twist_ofModel_ne :
    twist (fun _ => Units.mk0 (2 : K) two_ne_zero) ⋙ ofModel K ≠ ofModel K := by
  intro h
  have h1 := Functor.congr_obj h (⟨pt, 0⟩ : GlobalFrobenioid K)
  have h2 : (0 : ArithDivZ K) + divZ K (Additive.ofMul (Units.mk0 (2 : K) two_ne_zero)) = 0 :=
    triv_injective h1
  rw [zero_add] at h2
  exact divZ_two_ne h2

end TorsorFrob

/-! ### (b) Uniqueness on the realification -/

namespace GlobalRealified

/-- **Inducing the identity on `ℝ·Φ^birat`** for a functor `C^⊩ → C^⊩`. -/
def InducesIdRatFun (G : GlobalRealified K ⥤ GlobalRealified K) : Prop :=
  ∀ ⦃X Y : GlobalRealified K⦄ (φ ψ : X ⟶ Y), φ.deg = ψ.deg →
    ((G.map φ).u : ArithDiv K) - (G.map ψ).u = (φ.u : ArithDiv K) - ψ.u

lemma rel_eq {X Y : GlobalRealified K} (φ : X ⟶ Y) :
    (φ.deg : ℕ) • X.α + φ.div = Y.α + (φ.u : ArithDiv K) := φ.rel

/-- **Isomorphisms of `C^⊩` are unique**: an isomorphism `X → Y` is `(1, 0, α_X − α_Y)`. -/
theorem hom_eq_of_isIso {X Y : GlobalRealified K} (i j : X ⟶ Y) [IsIso i] [IsIso j] : i = j := by
  obtain ⟨hi0, hi1⟩ := iso_div_deg i
  obtain ⟨hj0, hj1⟩ := iso_div_deg j
  refine Model.hom_ext (hi1.trans hj1.symm) (Subsingleton.elim _ _) (hi0.trans hj0.symm)
    (Subtype.ext ?_)
  have ri := rel_eq i
  have rj := rel_eq j
  rw [hi0, hi1] at ri
  rw [hj0, hj1] at rj
  have : Y.α + (i.u : ArithDiv K) = Y.α + (j.u : ArithDiv K) := ri.symm.trans rj
  exact add_left_cancel this

instance {C : Type*} [Category C] (G H : C ⥤ GlobalRealified K) : Subsingleton (G ≅ H) :=
  ⟨fun _ _ => Iso.ext (NatTrans.ext (funext fun _ => hom_eq_of_isIso _ _))⟩

theorem inducesIdRatFun_id : InducesIdRatFun (𝟭 (GlobalRealified K)) := fun _ _ _ _ _ => rfl

variable (G : GlobalRealified K ⥤ GlobalRealified K) [G.IsEquivalence]

/-- `Ψ_Φ(z) − z` only depends on `z` modulo `ℝ·Φ^birat`. -/
theorem psiPhi_sub_eq (hG : InducesIdRatFun G) {z z' : ArithDiv K} (hz : z ∈ effCone K)
    (hz' : z' ∈ effCone K) (hr : z' - z ∈ ratFun K) :
    psiPhi G z' hz' - z' = psiPhi G z hz - z := by
  let X : GlobalRealified K := objOfDeg 0
  let φ₀ := step X z hz
  let φ : X ⟶ stepTgt X z := Model.mk1 (𝟙 _) z' hz' ⟨z' - z, hr⟩ (by
    change X.α + z' = X.α + z + (z' - z)
    abel)
  have h1 := hG φ φ₀ rfl
  have r1 := rel_eq (G.map φ)
  have r0 := rel_eq (G.map φ₀)
  rw [deg_map G φ, div_map G φ] at r1
  rw [deg_map G φ₀, div_map G φ₀] at r0
  change ((G.map φ).u : ArithDiv K) - (G.map φ₀).u = (z' - z) - 0 at h1
  change _ + psiPhi G z' hz' = _ at r1
  change _ + psiPhi G z hz = _ at r0
  have hdeg : φ.deg = φ₀.deg := rfl
  have e1 : psiPhi G z' hz' = (G.obj (stepTgt X z)).α + ((G.map φ).u : ArithDiv K) -
      (φ.deg : ℕ) • (G.obj X).α := by rw [← r1]; abel
  have e0 : psiPhi G z hz = (G.obj (stepTgt X z)).α + ((G.map φ₀).u : ArithDiv K) -
      (φ₀.deg : ℕ) • (G.obj X).α := by rw [← r0]; abel
  rw [e1, e0, hdeg]
  rw [sub_zero] at h1
  rw [show ((G.map φ).u : ArithDiv K) = (G.map φ₀).u + (z' - z) by rw [← h1]; abel]
  abel

lemma exists_finitePlace_ne (q : Place K) : ∃ p : FinitePlace K, (Sum.inl p : Place K) ≠ q := by
  haveI := infinite_finitePlace K
  rcases q with w | v
  · obtain ⟨p, hp⟩ := exists_ne w
    exact ⟨p, fun h => hp (Sum.inl_injective h)⟩
  · exact ⟨Classical.arbitrary _, Sum.inl_ne_inr⟩

lemma degArith_single_inl_div (p : FinitePlace K) (t : ℝ) :
    degArith K (single (Sum.inl p) (t / Real.log (primeNorm p))) = t := by
  rw [degArith_single_inl]
  have := Real.log_pos (one_lt_primeNorm p)
  field_simp

/-- **`Ψ_Φ(G) = id`** for an autoequivalence of `C^⊩` inducing the identity on `ℝ·Φ^birat`. -/
theorem psiPhi_eq_self (hG : InducesIdRatFun G) (z : ArithDiv K) (hz : z ∈ effCone K) :
    psiPhi G z hz = z := by
  rw [eq_iff_coord]
  intro q
  obtain ⟨p, hp⟩ := exists_finitePlace_ne q
  have hl : 0 < Real.log (primeNorm p) := Real.log_pos (one_lt_primeNorm p)
  have hq0 : ∀ t, coord (single (Sum.inl p) t) q = 0 := fun t => by
    rw [coord_single, if_neg hp.symm]
  -- `≥`: compare with a divisor of the same degree supported at `p`
  have ht : 0 ≤ degArith K z := degArith_nonneg hz
  have hz1 : single (Sum.inl p) (degArith K z / Real.log (primeNorm p)) ∈ effCone K :=
    single_mem (div_nonneg ht hl.le)
  have e1 := psiPhi_sub_eq G hG hz hz1 (ker_degArith_le (by
    rw [LinearMap.mem_ker, map_sub, degArith_single_inl_div, sub_self]))
  have c1 := congrArg (fun x => coord x q) e1
  simp only [coord_sub, hq0, sub_zero] at c1
  have c1' := (mem_effCone_iff_coord.mp (psiPhi_mem G _ hz1)) q
  -- `≤`: compare with the preimage of a divisor supported at `p`
  have hs : 0 ≤ degArith K (psiPhi G z hz) := degArith_nonneg (psiPhi_mem G z hz)
  obtain ⟨z2, hz2, hy⟩ := psiPhi_surjective G
    (single_mem (p := Sum.inl p) (div_nonneg hs hl.le))
  have hd2 : degArith K z2 = degArith K z := by
    have a1 := degArith_psiPhi G z2 hz2
    have a2 := degArith_psiPhi G z hz
    rw [hy, degArith_single_inl_div, a2] at a1
    exact (mul_left_cancel₀ (degOf_pos G).ne' a1).symm
  have e2 := psiPhi_sub_eq G hG hz hz2 (ker_degArith_le (by
    rw [LinearMap.mem_ker, map_sub, hd2, sub_self]))
  have c2 := congrArg (fun x => coord x q) e2
  rw [hy] at c2
  simp only [coord_sub, hq0, zero_sub] at c2
  have c2' := (mem_effCone_iff_coord.mp hz2) q
  linarith

/-- **`deg(G) = 1`.** -/
theorem degOf_eq_one (hG : InducesIdRatFun G) : degOf G = 1 := by
  obtain ⟨p, -⟩ := exists_finitePlace_ne (K := K) (Sum.inr (Classical.arbitrary _))
  have hl : 0 < Real.log (primeNorm p) := Real.log_pos (one_lt_primeNorm p)
  have hz := single_mem (p := Sum.inl p) (div_nonneg zero_le_one hl.le)
  have := degArith_psiPhi G _ hz
  rw [psiPhi_eq_self G hG, degArith_single_inl_div, mul_one] at this
  exact this.symm

/-- The component `G X → X`: `(1, 0, α_{G X} − α_X)`. -/
noncomputable def toIdHom (hG : InducesIdRatFun G) (X : GlobalRealified K) : G.obj X ⟶ X :=
  Model.mk1 (Discrete.eqToHom (Subsingleton.elim _ _)) 0 (effCone K).zero_mem
    ⟨(G.obj X).α - X.α, ker_degArith_le (by
      rw [LinearMap.mem_ker, map_sub]
      have := degree_map_eq G X
      rw [degOf_eq_one G hG, one_mul] at this
      change (G.obj X).degree - X.degree = 0
      rw [this, sub_self])⟩ (by
    change (G.obj X).α + 0 = X.α + ((G.obj X).α - X.α)
    abel)

lemma isIso_toIdHom (hG : InducesIdRatFun G) (X : GlobalRealified K) :
    IsIso (toIdHom G hG X) :=
  Model.isIso_of _ rfl (isIso_pt _) rfl

/-- **The natural isomorphism `G ≅ 𝟭`.** -/
noncomputable def isoId (hG : InducesIdRatFun G) : G ≅ 𝟭 (GlobalRealified K) :=
  NatIso.ofComponents (fun X => @asIso _ _ _ _ (toIdHom G hG X) (isIso_toIdHom G hG X))
    fun {X Y} φ => by
    have r := rel_eq φ
    have r' := rel_eq (G.map φ)
    rw [deg_map G φ, div_map G φ, psiPhi_eq_self G hG] at r'
    refine Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ (Subtype.ext ?_)
    · change (1 : ℕ+) * (G.map φ).deg = φ.deg * 1
      rw [deg_map G φ, one_mul, mul_one]
    · change (0 : ArithDiv K) + ((1 : ℕ+) : ℕ) • (G.map φ).div = φ.div + (φ.deg : ℕ) • 0
      rw [div_map G φ, psiPhi_eq_self G hG, PNat.one_coe, one_smul, zero_add, smul_zero,
        add_zero]
    · change ((G.obj Y).α - Y.α) + ((1 : ℕ+) : ℕ) • ((G.map φ).u : ArithDiv K) =
        (φ.u : ArithDiv K) + (φ.deg : ℕ) • ((G.obj X).α - X.α)
      have eu : ((G.map φ).u : ArithDiv K) = (φ.deg : ℕ) • (G.obj X).α + φ.div - (G.obj Y).α := by
        rw [r']; abel
      have eu' : (φ.u : ArithDiv K) = (φ.deg : ℕ) • X.α + φ.div - Y.α := by
        rw [r]; abel
      rw [eu, eu', PNat.one_coe, one_smul, smul_sub]
      abel

/-- **IUT III, Example 3.6(iii), uniqueness on the realification**: an autoequivalence of `C^⊩`
inducing the identity on `ℝ·Φ^birat` is isomorphic to the identity by a unique natural
isomorphism. -/
noncomputable abbrev unique_of_inducesIdRatFun (hG : InducesIdRatFun G) :
    Unique (G ≅ 𝟭 (GlobalRealified K)) :=
  uniqueOfSubsingleton (isoId G hG)

/-- Two such autoequivalences are uniquely isomorphic. -/
noncomputable abbrev uniqueIso (hG : InducesIdRatFun G) (G' : GlobalRealified K ⥤ GlobalRealified K)
    [G'.IsEquivalence] (hG' : InducesIdRatFun G') : Unique (G ≅ G') :=
  uniqueOfSubsingleton ((isoId G hG).trans (isoId G' hG').symm)

end GlobalRealified

end Frobenioid

end Iut
