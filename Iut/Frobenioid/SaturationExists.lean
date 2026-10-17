/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ReciprocityIso
import Iut.Frobenioid.SaturationGen
import LocalClassFieldTheory.Duality.MuN
import LocalClassFieldTheory.Brauer.Absolute

/-!
# Existence of `(N, H)`-saturated objects ([FrdII], Remark 2.2.1)

[FrdII], Remark 2.2.1: "it follows immediately from the definitions, together with the finiteness
of the cohomology modules `H¹(H, μ_N(A))`, `H²(H, μ_N(A))` [cf., e.g., [NSW], Chapter 7,
Theorem 7.2.6], that given an `A' ∈ Ob(C)`, it follows that, for any `N`, `H` as in Definition
2.2, there exists a pull-back morphism `A'' → A'` in `C` such that `A''` is `(N, H)`-saturated."

For the `p`-adic Frobenioid `C^⊢(E)` (`E/ℚ_p` finite), an open subgroup `H ⊆ G_E` and `n ≥ 1`:
**`exists_isSaturated`**: there is an open normal `N₀ ⊆ G_E` such that every `X = (G_E/N, a)`
with `N ⊆ N₀` is `(n, H)`-saturated (`X` admits the pull-back morphism `X → (G_E/N', a)` for every
`N ⊆ N'`). The inputs are the finiteness of `H¹(H, μ_n)`, `H¹(H, ℤ/n)` (local class field theory,
`PadicField.finite_h1_mu`, `finite_h1_trivZMod`) and of `H²(H, μ_n) ≅ ℤ/n` (`h2MuEquiv`), the
openness of the stabilizer of `μ_n(K̄)`, uniform local constancy of 2-cocycles on the compact
group `H` (`exists_openSubgroup_prod_invariant`), and `μ_n`-saturation (`muSat_of_fix`: units of
`X` are the `N`-invariant elements of norm `1`, `GaloisModel.ounitsEquiv`).
-/

namespace Iut

namespace Frobenioid

namespace ContH2Aux

variable {G M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  [CommGroup M'] [MulDistribMulAction G M']

/-- A representative of a class of `H²(G, M)` obtained from a chosen representative of its image
in `H²(G, M')` under an equivariant isomorphism `M ≅ M'`. -/
theorem exists_cocycle_of_reps (e : M ≃* M') (hes : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (r : ContH2 G M' → ContH2.cocycles G M') (hr : ∀ y, ContH2.mk (r y) = y) (x : ContH2 G M) :
    ∃ c : ContH2.cocycles G M, ContH2.mk c = x ∧ ∃ y : ContH2 G M',
      ∀ ab : G × G, e ((c : G × G → M) ab) = (r y : G × G → M') ab := by
  let E := mapCoeff e hes
  have hes' : ∀ (g : G) (m : M'), e.symm (g • m) = g • e.symm m := fun g m => by
    apply e.injective
    rw [hes, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  let c := ContH2.cocyclesMap (MonoidHom.id G) continuous_id e.symm.toMonoidHom hes' (r (E x))
  refine ⟨c, ?_, E x, fun ab => ?_⟩
  · have hc : E.symm (ContH2.mk (r (E x))) = ContH2.mk c := rfl
    rw [← hc, hr, MulEquiv.symm_apply_apply]
  · change e (e.symm ((r (E x) : G × G → M') (ab.1, ab.2))) = _
    rw [MulEquiv.apply_symm_apply]

end ContH2Aux

namespace PAdicGalois

open Saturation CategoryTheory IntermediateField

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K̄" => PadicAlgCl p

lemma mem_of_galHom_eq_one (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) {k : GK p E}
    (h : galHom N a k = 1) : k ∈ N := by
  have h1 := congrArg (fun α : WithDisc (Aut (XN N a)) => (show Aut (XN N a) from α).hom.base) h
  change OrbitObj.rmul N k⁻¹ = 𝟙 _ at h1
  exact inv_mem_iff.mp ((OrbitObj.rmul_eq_id_iff N k⁻¹).mp h1)

lemma isOpen_stab_mu (n : ℕ) (ζ : KummerTheory.Mu n K̄) :
    IsOpen {σ : GK p E | σ • ζ = ζ} := by
  have e : {σ : GK p E | σ • ζ = ζ} =
      MulAction.stabilizer (GK p E) ((KummerTheory.Mu.val ζ : K̄ˣ) : K̄) := by
    ext σ
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact (KummerTheory.Mu.val_smul_coe σ ζ).symm.trans
        (congrArg (fun z => ((KummerTheory.Mu.val z : K̄ˣ) : K̄)) h)
    · intro h
      exact KummerTheory.Mu.ext (Units.ext h)
  rw [e]
  exact stabilizer_isOpen_of_isIntegral _

lemma ord_mu (n : ℕ) [NeZero n] (ζ : KummerTheory.Mu n K̄) :
    ord p (Additive.ofMul (KummerTheory.Mu.val ζ)) = 0 := by
  change -Real.logb p ‖((KummerTheory.Mu.val ζ : K̄ˣ) : K̄)‖ = 0
  have h1 : ‖((KummerTheory.Mu.val ζ : K̄ˣ) : K̄)‖ ^ n = 1 := by
    have hz : (KummerTheory.Mu.val ζ : K̄ˣ) ^ n = 1 := (mem_rootsOfUnity n _).1 ζ.2
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, norm_one]
  have h2 : ‖((KummerTheory.Mu.val ζ : K̄ˣ) : K̄)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)).mp h1
  rw [h2, Real.logb_one, neg_zero]

/-- **`μ_n`-saturation**: if `N` fixes `μ_n(K̄)`, then `μ_n(X) ≅ ℤ/n` for `X = (G_E/N, a)`. -/
theorem muSat_of_fix (N : OpenNormalSubgroup (GK p E)) (a : gammaZ) (n : ℕ) [NeZero n]
    (hN : ∀ σ ∈ N, ∀ ζ : KummerTheory.Mu n K̄, σ • ζ = ζ) :
    Nonempty (muX N a n ≃* Multiplicative (ZMod n)) := by
  have hsurj : Function.Surjective (uMu N a n) := by
    intro ζ
    let w : Mul p := Additive.ofMul (KummerTheory.Mu.val ζ)
    have hw : w ∈ fixedSub (preSub (GK p E) (ord p) (ord_smul p E) gammaZ)
        (OrbitObj.ofONS N) := by
      refine ⟨?_, fun h hh => ?_⟩
      · change ord p w ∈ gammaZ
        rw [ord_mu]
        exact zero_mem _
      · change Additive.ofMul (h • KummerTheory.Mu.val ζ) = Additive.ofMul (KummerTheory.Mu.val ζ)
        rw [← KummerTheory.Mu.val_smul, hN h hh]
    let e := (GaloisModel.ounitsEquiv (XN N a)).symm ⟨⟨w, hw⟩, ord_mu n ζ⟩
    haveI := e.2.1
    let α : WithDisc (Aut (XN N a)) := asIso e.1
    let u : Model.ouAut (XN N a) := ⟨α, e.2⟩
    have hr : ratFun N a u = KummerTheory.Mu.val ζ := rfl
    have hu : u ∈ muX N a n := by
      rw [KummerClass.mem_mu]
      apply ratFun_injective N a
      have : ratFunHom N a (u ^ n) = 1 := by
        rw [map_pow]
        change ratFun N a u ^ n = 1
        rw [hr]
        exact (mem_rootsOfUnity n _).1 ζ.2
      exact this.trans (ratFun_one N a).symm
    exact ⟨⟨u, hu⟩, KummerTheory.Mu.ext hr⟩
  haveI : IsCyclic (KummerTheory.Mu n K̄) := inferInstanceAs (IsCyclic (rootsOfUnity n K̄))
  haveI : NeZero (n : K̄) := ⟨by exact_mod_cast NeZero.ne n⟩
  have hc : Nat.card (KummerTheory.Mu n K̄) = Nat.card (Multiplicative (ZMod n)) := by
    have h1 : Nat.card (KummerTheory.Mu n K̄) = n :=
      HasEnoughRootsOfUnity.natCard_rootsOfUnity K̄ n
    rw [h1, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  exact ⟨(MulEquiv.ofBijective (uMu N a n) ⟨uMu_injective N a n, hsurj⟩).trans
    (mulEquivOfCyclicCardEq hc)⟩

section Finite

variable (H : Subgroup (GK p E)) (hH : IsOpen (H : Set (GK p E)))

include hH in
lemma finite_h1Mu_H [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n] :
    Finite (ContH1 H (KummerTheory.Mu n K̄)) := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI := PadicField.finite_h1_mu (p := p) (K := fixL H) (Ω := K̄) n
  exact Finite.of_equiv _ (ContH1Aux.mapEquiv (galFixEquiv H hH)
    (MulEquiv.refl (KummerTheory.Mu n K̄)) continuous_id continuous_id
    (fun _ _ => rfl)).symm.toEquiv

/-- `ℤ/n` (`Saturation.ZTriv`) and LCFT's `Brauer.TrivZMod`. -/
def zTrivEquiv (n : ℕ) : ZTriv n ≃* Brauer.TrivZMod n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

include hH in
lemma finite_h1Z_H [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n] :
    Finite (ContH1 H (ZTriv n)) := by
  haveI := finiteDimensional_fixL_padic H hH
  haveI := PadicField.finite_h1_trivZMod (p := p) (K := fixL H) (Ω := K̄) n
  exact Finite.of_equiv _ (ContH1Aux.mapEquiv (galFixEquiv H hH) (zTrivEquiv n)
    continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl)).symm.toEquiv

include hH in
lemma finite_h2Mu_H [FiniteDimensional ℚ_[p] E] (n : ℕ) [NeZero n] :
    Finite (ContH2 H (KummerTheory.Mu n K̄)) := by
  haveI := finiteDimensional_fixL_padic H hH
  exact Finite.of_equiv _ ((h2HEquiv H hH n).trans
    (PadicField.h2MuEquiv p (fixL H) K̄ (Nat.pos_of_ne_zero (NeZero.ne n)))).symm.toEquiv

include hH in
lemma compactSpace_H : CompactSpace H :=
  isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen H hH).isCompact

open scoped Topology in
lemma basis_H (V : Set H) (hV : V ∈ 𝓝 (1 : H)) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ (U : Set H) ⊆ V := by
  obtain ⟨u, hu, huV⟩ := (mem_nhds_subtype (H : Set (GK p E)) (1 : H) V).mp hV
  obtain ⟨W, hWu, hW, h1⟩ := mem_nhds_iff.mp hu
  obtain ⟨N', hN'⟩ := OrbitObj.exists_ons_le hW h1
  refine ⟨N'.toSubgroup.comap H.subtype, N'.isOpen.preimage continuous_subtype_val, ?_⟩
  intro x hx
  exact huV (hWu (hN' hx))

end Finite

/-- **Existence of `(n, H)`-saturated objects** ([FrdII], Remark 2.2.1): for `E/ℚ_p` finite,
`H ⊆ G_E` open and `n ≥ 1`, there is an open normal `N₀ ⊆ G_E` such that every `X = (G_E/N, a)` with
`N ⊆ N₀` is `(n, H)`-saturated. -/
theorem exists_isSaturated [FiniteDimensional ℚ_[p] E] (H : Subgroup (GK p E))
    (hH : IsOpen (H : Set (GK p E))) (n : ℕ) [NeZero n] :
    ∃ N₀ : OpenNormalSubgroup (GK p E), ∀ N : OpenNormalSubgroup (GK p E), N ≤ N₀ →
      ∀ a : gammaZ, IsSaturated N a H n := by
  classical
  haveI := finite_h1Mu_H H hH n
  haveI := finite_h1Z_H H hH n
  haveI := finite_h2Mu_H H hH n
  haveI := compactSpace_H H hH
  -- representatives
  let r1 : ContH1 H (KummerTheory.Mu n K̄) → ContH1.cocycles H (KummerTheory.Mu n K̄) :=
    fun c => (ContH1.mk_surjective c).choose
  have hr1 : ∀ c, ContH1.mk (r1 c) = c := fun c => (ContH1.mk_surjective c).choose_spec
  let r2 : ContH1 H (ZTriv n) → ContH1.cocycles H (ZTriv n) :=
    fun c => (ContH1.mk_surjective c).choose
  have hr2 : ∀ c, ContH1.mk (r2 c) = c := fun c => (ContH1.mk_surjective c).choose_spec
  let r3 : ContH2 H (KummerTheory.Mu n K̄) → ContH2.cocycles H (KummerTheory.Mu n K̄) :=
    fun c => (ContH2.mk_surjective c).choose
  have hr3 : ∀ c, ContH2.mk (r3 c) = c := fun c => (ContH2.mk_surjective c).choose_spec
  have hU : ∀ y : ContH2 H (KummerTheory.Mu n K̄), ∃ U : Subgroup H, IsOpen (U : Set H) ∧
      ∀ g h : H, ∀ u ∈ U, ∀ u' ∈ U, (r3 y : H × H → KummerTheory.Mu n K̄) (g * u, h * u') =
        (r3 y : H × H → KummerTheory.Mu n K̄) (g, h) := fun y =>
    exists_openSubgroup_prod_invariant (basis_H H) _ (ContH2.isLocallyConstant (r3 y))
  choose U hUo hUi using hU
  let T : Set H := (⋂ c, {h | (r1 c : H → KummerTheory.Mu n K̄) h = 1}) ∩
    (⋂ c, {h | (r2 c : H → ZTriv n) h = 1}) ∩ (⋂ y, (U y : Set H))
  have hT : IsOpen T := by
    refine ((isOpen_iInter_of_finite fun c => ?_).inter (isOpen_iInter_of_finite fun c => ?_)).inter
      (isOpen_iInter_of_finite hUo)
    · exact (ContH1.continuous (r1 c)).isOpen_preimage {1} (isOpen_discrete _)
    · exact (ContH1.continuous (r2 c)).isOpen_preimage {1} (isOpen_discrete _)
  have h1T : (1 : H) ∈ T := by
    refine ⟨⟨Set.mem_iInter.mpr fun c => ContH1.map_one_eq _,
      Set.mem_iInter.mpr fun c => ContH1.map_one_eq _⟩, Set.mem_iInter.mpr fun y => (U y).one_mem⟩
  let Fix : Set (GK p E) := ⋂ ζ : KummerTheory.Mu n K̄, {σ | σ • ζ = ζ}
  have hFix : IsOpen Fix := isOpen_iInter_of_finite fun ζ => isOpen_stab_mu n ζ
  let S : Set (GK p E) := Fix ∩ Subtype.val '' T
  have hS : IsOpen S := hFix.inter (hH.isOpenMap_subtype_val T hT)
  have h1S : (1 : GK p E) ∈ S :=
    ⟨Set.mem_iInter.mpr fun ζ => one_smul _ ζ, ⟨1, h1T, rfl⟩⟩
  obtain ⟨N₀, hN₀⟩ := OrbitObj.exists_ons_le hS h1S
  refine ⟨N₀, fun N hN a => ?_⟩
  -- the kernel of `H → H_A` lies in `N`, hence in `S`
  have hker : ∀ k ∈ (subHom N a H).ker, (k : GK p E) ∈ N := fun k hk =>
    mem_of_galHom_eq_one N a (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
  have hkS : ∀ k ∈ (subHom N a H).ker, (∀ ζ : KummerTheory.Mu n K̄, (k : GK p E) • ζ = ζ) ∧
      k ∈ T := fun k hk => by
    obtain ⟨hf, ⟨k', hk'T, hk'⟩⟩ := hN₀ (hN (hker k hk))
    refine ⟨fun ζ => Set.mem_iInter.mp hf ζ, ?_⟩
    rwa [← Subtype.ext hk']
  have hNfix : ∀ σ ∈ N, ∀ ζ : KummerTheory.Mu n K̄, σ • ζ = ζ := fun σ hσ ζ =>
    Set.mem_iInter.mp (hN₀ (hN hσ)).1 ζ
  have hms := muSat_of_fix N a n hNfix
  have hc1 : Function.Bijective
      (infl₁ (subHom N a H) (continuous_subHom N a H) (muX N a n)) := by
    refine ⟨infl₁_injective (subHom N a H) (continuous_subHom N a H) (subHom_surjective N a H)
      (muX N a n), infl₁_surjective (subHom N a H) (continuous_subHom N a H)
      (subHom_surjective N a H) (muX N a n) fun d k hk => ?_⟩
    exact cocycle_eq_one_of_reps (uMuEquiv N a H n hms) continuous_of_discreteTopology
      (uMuEquiv_smul N a H n hms) r1 hr1 (fun m' => (hkS k hk).1 m')
      (fun c => Set.mem_iInter.mp (hkS k hk).2.1.1 c) d
  have hc2 : Function.Bijective (infl₁Z (subHom N a H) (continuous_subHom N a H) n) := by
    refine ⟨infl₁Z_injective (subHom N a H) (continuous_subHom N a H) (subHom_surjective N a H)
      n, infl₁Z_surjective (subHom N a H) (continuous_subHom N a H)
      (subHom_surjective N a H) n fun d k hk => ?_⟩
    have hkT := (hkS k hk).2
    obtain ⟨m, hm⟩ := (ContH1.mk_eq_mk_iff _ _).mp (hr2 (ContH1.mk d))
    have h1 : k • m / m = (r2 (ContH1.mk d) : H → ZTriv n) k / (d : H → ZTriv n) k := hm k
    have hr : (r2 (ContH1.mk d) : H → ZTriv n) k = 1 := Set.mem_iInter.mp hkT.1.2 (ContH1.mk d)
    rw [ZTriv.smul_eq, div_self', hr, one_div, eq_comm, inv_eq_one] at h1
    exact h1
  have hc3 : Function.Surjective
      (infl₂ (subHom N a H) (continuous_subHom N a H) (muX N a n)) := by
    refine infl₂_surjective (subHom N a H) (continuous_subHom N a H) (subHom_surjective N a H)
      (muX N a n) fun x => ?_
    have hex := ContH2Aux.exists_cocycle_of_reps (G := H)
      (M := Pull (subHom N a H) (muX N a n)) (M' := KummerTheory.Mu n K̄)
      (uMuEquiv N a H n hms) (uMuEquiv_smul N a H n hms) r3 hr3 x
    obtain ⟨c, hcx, y, hce⟩ := hex
    refine ⟨c, hcx, fun h h' k k' hk hk' => (uMuEquiv N a H n hms).injective ?_⟩
    have hk1 : k ∈ U y := Set.mem_iInter.mp (hkS k hk).2.2 y
    have hk2 : k' ∈ U y := Set.mem_iInter.mp (hkS k' hk').2.2 y
    have e1 := hce (h * k, h' * k')
    have e2 := hce (h, h')
    exact (e1.trans (hUi y h h' k hk1 k' hk2)).trans e2.symm
  exact ⟨hms, hc1, hc2, hc3⟩

end PAdicGalois

end Frobenioid

end Iut
