/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.MultiContainer

/-!
# The constraints of Milestone 2 in the multi-container model (the wall, Milestone 3, part 3)

The candidate constraints (C1)–(C10) of `Iut/Wall/Constraints.lean` are re-stated for the
multi-container model `MultiContainer D` (`Iut/Wall/MultiContainer.lean`), where each Hodge
theater has its own container, log-volume and Kummer isomorphism, and the output is transported
along `κ_{h₂} ∘ κ_{h₁}⁻¹`. Constraints that only concern the algorithm (C1, C7, C8) are unchanged;
the others now refer to the transport. A further constraint is added:

* **(C11) volume compatibility** (`MultiContainer.VolCompat`; IUT III, Proposition 3.9(ii):
  mono-analytic log-volumes "compatible with the log-volumes obtained in (i), relative to the
  natural poly-isomorphisms", constructed "via a functorial algorithm from the `D⊢`-prime-strips";
  Proposition 3.9(iv) and Corollary 3.12, Step (x): the log-volumes are invariant under (Ind1),
  (Ind2) and compatible with the Kummer isomorphisms and log-links of the log-Kummer
  correspondence).

## Results

* **(C2) transported SHE** (`SHE3`: the transported output is a function of the target Hodge
  theater and `S`) and **(C6) transported multiradiality** (`Multiradial3`: outputs through any
  two Hodge theaters, transported to the same target, agree up to (Ind3)) each **imply (C11)**
  for identified-copies log-volumes (`volCompat_of_she3`, `volCompat_of_multiradial3`), hence the
  Scholze–Stix wall (`wall3_iff_ss_of_she3`, `wall3_iff_ss_of_multiradial3`).
* **(C4) distinct Kummer identifications** (`DistinctKummer`) and **(C10) alien transports**
  (`Alien3`: no transport between distinct Hodge theaters is a ring isomorphism) are now
  non-vacuous and **exclude the identified-copies collapse** (`not_distinctKummer_idModel`,
  `not_alien3_idModel`); but `negModel D` (two Hodge theaters, Kummer isomorphisms `1` and
  `x ↦ −x`) satisfies both, together with (C11), and its wall is still the Scholze–Stix
  inequality (`wall3_negModel_iff`).
* **(C5) the wall across distinct Hodge theaters** (`WallDistinct3 := WallOn (· ≠ ·)`) implies
  the Scholze–Stix inequality as soon as there are two Hodge theaters (`ss_of_wallDistinct3`):
  the distortions of the two directions cancel.
* **A model where the wall is not the Scholze–Stix inequality**: `chainModel D k`, Hodge
  theaters `ℤ` (one row of the log-theta-lattice, Θ-links `n → n + 1`, IUT III, Definition
  3.8), Kummer isomorphisms `q^{−k·n}` (multiplication by a power of `q_v` in the factor of the
  label `1`). The transport `n → n + 1` distorts volume by `k·|log(q)|`
  (`distortion_chain`), and along the Θ-links the wall is
  **`(s − 1 − k)·|log(q)| ≤ log-vol(hull(VC(I)))`** (`wallOn_chain_iff`). For `k ≠ 0` this model
  violates (C11), (C2) and (C6) (`not_volCompat_chain`, `not_she3_chain`,
  `not_multiradial3_chain`), satisfies (C4) and (C10) (`alien3_chain`), and its wall for all
  pairs is false (`not_wall3_chain`). For suitable `k` the wall along the Θ-links holds, for
  every `D` (`exists_wallOn_chain`); it then says nothing about Corollary 3.12 by itself.
-/

namespace Iut

namespace Wall

namespace MultiContainer

variable {D : InitialThetaData.{0}} (M : MultiContainer D)

/-! ### (C2) transported simultaneous holomorphic expressibility -/

/-- **(C2) SHE, transported form** (IUT III, Remark 3.11.1(iii), Corollary 3.12, Step (xi-c):
the construction "may be expressed entirely relative to the arithmetic holomorphic structure in
the 1-column"): the transported output in `VC_{h₂}` is a function of `h₂` and `S` only. -/
def SHE3 : Prop :=
  ∃ G : M.HT → Ind3 D → Region D, ∀ (h₁ h₂ : M.HT) (ι : M.alg.Choice (M.alg.qBPS h₂) h₁)
    (S : Ind3 D), M.transport h₁ h₂ (M.alg.out ι S) = G h₂ S

/-- **Transported SHE forces volume compatibility** (for identified-copies log-volumes). -/
theorem volCompat_of_she3 (hS : M.alg.ThetaShift) (hE : M.SHE3) : M.VolCompat := by
  obtain ⟨G, hG⟩ := hE
  intro h₁ h₁'
  obtain ⟨h₂⟩ := M.alg.side_nonempty
  obtain ⟨ι⟩ := M.alg.nonempty_choice h₁ h₂
  obtain ⟨ι'⟩ := M.alg.nonempty_choice h₁' h₂
  have e := congrArg (logVol D) ((hG h₁ h₂ ι (Ind3.top D)).trans (hG h₁' h₂ ι' _).symm)
  have a := M.logVol_transport h₁ h₂ (M.alg.realisation ι (Ind3.top D)).1
  have b := M.logVol_transport h₁' h₂ (M.alg.realisation ι' (Ind3.top D)).1
  unfold vol at a b
  rw [a, b, hS, hS] at e
  unfold distortion at e
  linarith

/-- **Under transported SHE the wall is the Scholze–Stix inequality.** -/
theorem wall3_iff_ss_of_she3 (hS : M.alg.ThetaShift) (hE : M.SHE3) : M.Wall3 ↔ SSIneq D := by
  obtain ⟨h⟩ := M.alg.side_nonempty
  exact M.wallOn_iff_ss_of_volCompat hS (M.volCompat_of_she3 hS hE) ⟨h, h, trivial⟩

/-! ### (C6) transported multiradiality -/

/-- **(C6) Multiradiality, transported form** (IUT III, Theorem 3.11(i), the permutation
symmetries of the étale-picture; Corollary 3.12, Step (xi-b): `0,◦U ≅ 1,◦U`): the outputs through
any two Hodge theaters, transported to the same target, agree up to (Ind3). -/
def Multiradial3 : Prop :=
  ∀ (h₁ h₁' h₂ : M.HT) (ι : M.alg.Choice (M.alg.qBPS h₂) h₁)
    (ι' : M.alg.Choice (M.alg.qBPS h₂) h₁'), ∃ τ : Ind3 D ≃ Ind3 D, ∀ S,
      M.transport h₁ h₂ (M.alg.out ι S) = M.transport h₁' h₂ (M.alg.out ι' (τ S))

/-- **Transported multiradiality forces volume compatibility** (for identified-copies
log-volumes): compare the largest outputs. -/
theorem volCompat_of_multiradial3 (hS : M.alg.ThetaShift) (hM : M.Multiradial3) :
    M.VolCompat := by
  have key : ∀ h₁ h₁' : M.HT, shift D (M.kum h₁') ≤ shift D (M.kum h₁) := by
    intro h₁ h₁'
    obtain ⟨h₂⟩ := M.alg.side_nonempty
    obtain ⟨ι⟩ := M.alg.nonempty_choice h₁ h₂
    obtain ⟨ι'⟩ := M.alg.nonempty_choice h₁' h₂
    obtain ⟨τ, hτ⟩ := hM h₁ h₁' h₂ ι ι'
    have e := congrArg (logVol D) (hτ (Ind3.top D))
    have a := M.logVol_transport h₁ h₂ (M.alg.realisation ι (Ind3.top D)).1
    have b := M.logVol_transport h₁' h₂ (M.alg.realisation ι' (τ (Ind3.top D))).1
    unfold vol at a b
    rw [a, b, hS, hS] at e
    unfold distortion at e
    have := logVol_le_vcI D (τ (Ind3.top D))
    change _ + logVol D (hullOf D (vcI D)) + _ = _ at e
    linarith
  exact fun h₁ h₁' => le_antisymm (key h₁' h₁) (key h₁ h₁')

/-- **Under transported multiradiality the wall is the Scholze–Stix inequality.** -/
theorem wall3_iff_ss_of_multiradial3 (hS : M.alg.ThetaShift) (hM : M.Multiradial3) :
    M.Wall3 ↔ SSIneq D := by
  obtain ⟨h⟩ := M.alg.side_nonempty
  exact M.wallOn_iff_ss_of_volCompat hS (M.volCompat_of_multiradial3 hS hM) ⟨h, h, trivial⟩

/-! ### (C4), (C5), (C10) -/

/-- **(C4) Distinct Hodge theaters, with distinct identifications** of the coric log-shells
(IUT III, Theorem 3.11: "distinct" Hodge theaters; [LANA], §7.1(b)). -/
def DistinctKummer : Prop := ∃ h₁ h₂ : M.HT, M.kum h₁ ≠ M.kum h₂

/-- **(C10) Alien transports** ([LANA], §7.1(b)(c): "the ring/scheme structures are not
identified"; IUT III, Corollary 3.12, Step (xi-a)): no transport between distinct Hodge theaters
is a ring isomorphism. -/
def Alien3 : Prop := ∀ h₁ h₂ : M.HT, h₁ ≠ h₂ → ¬ M.IsRingTransport h₁ h₂

/-- (C10) in terms of the Kummer isomorphisms: they are pairwise distinct. -/
theorem alien3_iff : M.Alien3 ↔ ∀ h₁ h₂ : M.HT, h₁ ≠ h₂ → M.kum h₁ ≠ M.kum h₂ :=
  forall₂_congr fun h₁ h₂ => forall_congr' fun _ => not_congr (M.isRingTransport_iff h₁ h₂)

/-- **(C5) The wall across distinct Hodge theaters** ([LANA], §7.1(b)). -/
def WallDistinct3 : Prop := M.WallOn fun h₁ h₂ => h₁ ≠ h₂

/-- **(C5) with two Hodge theaters gives the Scholze–Stix inequality** (both directions are
required, and the distortions cancel). -/
theorem ss_of_wallDistinct3 [Nontrivial M.HT] (hS : M.alg.ThetaShift) (hW : M.WallDistinct3) :
    SSIneq D := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne M.HT
  exact M.ss_of_wallOn_pair hS hW hab hab.symm

end MultiContainer

/-! ### The identified-copies model against the constraints -/

variable (D : InitialThetaData.{0}) (σ : Type) [Nonempty σ]

theorem idModel_she3 : (idModel D σ).SHE3 :=
  ⟨fun _ S => lgp D S.1, fun h₁ h₂ _ _ => MultiContainer.transport_ofAlg (idAlgOn D σ) h₁ h₂ _⟩

theorem idModel_multiradial3 : (idModel D σ).Multiradial3 := fun h₁ h₁' h₂ _ _ =>
  ⟨Equiv.refl _, fun _ => by
    rw [transport_idModel, transport_idModel]
    rfl⟩

theorem idModel_volCompat : (idModel D σ).VolCompat := MultiContainer.ofAlg_volCompat _

/-- **The collapse violates (C4).** -/
theorem not_distinctKummer_idModel : ¬ (idModel D σ).DistinctKummer := by
  rintro ⟨_, _, h⟩
  exact h rfl

/-- **The collapse violates (C10)** when there are two Hodge theaters. -/
theorem not_alien3_idModel [Nontrivial σ] : ¬ (idModel D σ).Alien3 := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne σ
  exact fun h => h a b hab (MultiContainer.ofAlg_isRingTransport (idAlgOn D σ) a b)

/-! ### Alien, volume-compatible transports: `negModel` -/

/-- **Two Hodge theaters with alien, volume-compatible Kummer isomorphisms**: `1` and `x ↦ −x`
(at the bad primes), running the identified-copies algorithm. -/
noncomputable def negModel : MultiContainer D :=
  ⟨idAlgOn D Bool, fun b : Bool => if b then negScale D else 1⟩

theorem negModel_kum (b : Bool) : (negModel D).kum b = if b then negScale D else 1 := rfl

theorem negModel_volCompat : (negModel D).VolCompat := by
  have h : ∀ b : Bool, shift D ((negModel D).kum b) = 0 := by
    intro b
    rw [negModel_kum]
    cases b
    · exact shift_one D
    · exact shift_negScale D
  intro b₁ b₂
  exact (h b₁).trans (h b₂).symm

theorem negModel_alien3 : (negModel D).Alien3 := by
  rw [MultiContainer.alien3_iff]
  intro (b₁ : Bool) (b₂ : Bool) hb
  rw [negModel_kum, negModel_kum]
  cases b₁ <;> cases b₂
  · exact absurd rfl hb
  · exact fun h => negScale_ne_one D (by simpa using h.symm)
  · exact fun h => negScale_ne_one D (by simpa using h)
  · exact absurd rfl hb

theorem negModel_distinctKummer : (negModel D).DistinctKummer :=
  ⟨(false : Bool), (true : Bool),
    (MultiContainer.alien3_iff _).mp (negModel_alien3 D) false true Bool.false_ne_true⟩

/-- The two Hodge theaters of `negModel` induce different ring structures on the coric data. -/
theorem negModel_ringAt_ne :
    (negModel D).ringAt (false : Bool) ≠ (negModel D).ringAt (true : Bool) := fun h =>
  (MultiContainer.alien3_iff _).mp (negModel_alien3 D) false true Bool.false_ne_true
    (((negModel D).ringAt_eq_iff false true).mp h)

/-- **(C4), (C10), (C11) together: the wall is still the Scholze–Stix inequality.** -/
theorem wall3_negModel_iff : (negModel D).Wall3 ↔ SSIneq D :=
  (negModel D).wallOn_iff_ss_of_volCompat (idAlgOn_thetaShift D Bool) (negModel_volCompat D)
    ⟨(false : Bool), (false : Bool), trivial⟩

/-! ### Volume-distorting transports: `chainModel` -/

/-- **A row of the log-theta-lattice with drifting Kummer identifications**: Hodge theaters `ℤ`,
the identified-copies algorithm, Kummer isomorphism `q^{−k·n}` for the Hodge theater `n`. -/
noncomputable def chainModel (k : ℤ) : MultiContainer D :=
  ⟨idAlgOn D ℤ, fun n : ℤ => qScale D ^ (-(k * n))⟩

theorem chainModel_kum (k n : ℤ) : (chainModel D k).kum n = qScale D ^ (-(k * n)) := rfl

/-- The Θ-links of the row: `n → n + 1`. -/
def thetaRow (n m : ℤ) : Prop := m = n + 1

variable (k : ℤ)

/-- **The distortion of the transport `n → m` is `k·(m − n)·|log(q)|`.** -/
theorem distortion_chain (n m : ℤ) :
    (chainModel D k).distortion n m = k * (m - n) * D.qPilot.absLogQ := by
  rw [MultiContainer.distortion, chainModel_kum, chainModel_kum, shift_zpow, shift_zpow,
    shift_qScale]
  push_cast
  ring

/-- **The wall along the Θ-links of the row**: `(s − 1 − k)·|log(q)| ≤ log-vol(hull(VC(I)))`. -/
theorem wallOn_chain_iff :
    (chainModel D k).WallOn thetaRow ↔
      (sFactor (nC D) - 1 - k) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := by
  rw [(chainModel D k).wallOn_iff_of_thetaShift (idAlgOn_thetaShift D ℤ)]
  constructor
  · intro h
    have := h (0 : ℤ) (1 : ℤ) rfl
    rw [distortion_chain] at this
    push_cast at this
    linarith
  · intro h n m hnm
    rw [distortion_chain, hnm]
    push_cast
    linarith

/-- For `k = 0` the row is the identified-copies model and its wall is the Scholze–Stix
inequality. -/
theorem wallOn_chain_zero_iff : (chainModel D 0).WallOn thetaRow ↔ SSIneq D := by
  rw [wallOn_chain_iff]
  unfold SSIneq
  push_cast
  rw [sub_zero]

/-- **The directed wall can always be met by drift**: for every `D` some row satisfies the wall
along its Θ-links (take `k ≥ s − 1 − log-vol(hull(VC(I)))/|log(q)|`). Such a wall alone carries no
information on the Corollary 3.12 variant; with distortion, `variant_of_wallOn` needs the
realisation of the transported outputs in the target container. -/
theorem exists_wallOn_chain : ∃ k : ℤ, (chainModel D k).WallOn thetaRow := by
  have ha := absLogQ_pos D
  refine ⟨⌈sFactor (nC D) - 1 - logVol D (hullOf D (vcI D)) / D.qPilot.absLogQ⌉, ?_⟩
  rw [wallOn_chain_iff]
  have h1 := Int.le_ceil (sFactor (nC D) - 1 - logVol D (hullOf D (vcI D)) / D.qPilot.absLogQ)
  have h2 : sFactor (nC D) - 1 - (⌈sFactor (nC D) - 1 - logVol D (hullOf D (vcI D)) /
      D.qPilot.absLogQ⌉ : ℝ) ≤ logVol D (hullOf D (vcI D)) / D.qPilot.absLogQ := by linarith
  have h3 := mul_le_mul_of_nonneg_right h2 ha.le
  rwa [div_mul_cancel₀ _ ha.ne'] at h3

variable {k}

theorem not_volCompat_chain (hk : k ≠ 0) : ¬ (chainModel D k).VolCompat := fun h => by
  have := (chainModel D k).distortion_eq_zero_of_volCompat h (0 : ℤ) (1 : ℤ)
  rw [distortion_chain] at this
  have ha := (absLogQ_pos D).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  push_cast at this
  simp only [sub_zero, mul_one, mul_eq_zero] at this
  tauto

theorem not_she3_chain (hk : k ≠ 0) : ¬ (chainModel D k).SHE3 := fun h =>
  not_volCompat_chain D hk ((chainModel D k).volCompat_of_she3 (idAlgOn_thetaShift D ℤ) h)

theorem not_multiradial3_chain (hk : k ≠ 0) : ¬ (chainModel D k).Multiradial3 := fun h =>
  not_volCompat_chain D hk
    ((chainModel D k).volCompat_of_multiradial3 (idAlgOn_thetaShift D ℤ) h)

theorem alien3_chain (hk : k ≠ 0) : (chainModel D k).Alien3 := by
  intro (n : ℤ) (m : ℤ) hnm hR
  have := (chainModel D k).distortion_eq_zero_of_isRingTransport hR
  rw [distortion_chain] at this
  have ha := (absLogQ_pos D).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hnm' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm.symm)
  simp only [mul_eq_zero] at this
  tauto

/-- **For `k ≠ 0` the wall for all pairs fails in the row**: the distortion is unbounded. -/
theorem not_wall3_chain (hk : k ≠ 0) : ¬ (chainModel D k).Wall3 := by
  intro hW
  have hw := ((chainModel D k).wall3_iff_of_thetaShift (idAlgOn_thetaShift D ℤ)).mp hW
  have ha := absLogQ_pos D
  have hs : 0 ≤ sFactor (nC D) := (sFactor_pos (nC_pos D)).le
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((logVol D (hullOf D (vcI D)) + D.qPilot.absLogQ) / D.qPilot.absLogQ)
  have hN' : logVol D (hullOf D (vcI D)) + D.qPilot.absLogQ < N * D.qPilot.absLogQ :=
    (div_lt_iff₀ ha).mp hN
  have h := hw (0 : ℤ) (N : ℤ)
  rw [distortion_chain] at h
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have habs : |(k : ℝ) * (((N : ℤ) : ℝ) - ((0 : ℤ) : ℝ)) * D.qPilot.absLogQ| =
      |(k : ℝ)| * (N * D.qPilot.absLogQ) := by
    have hN0 : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
    rw [Int.cast_zero, sub_zero, Int.cast_natCast, abs_mul, abs_mul, hN0, abs_of_pos ha]
    ring
  rw [habs] at h
  have hNa : 0 ≤ (N : ℝ) * D.qPilot.absLogQ := mul_nonneg (Nat.cast_nonneg N) ha.le
  nlinarith

end Wall

end Iut
