/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.AutKernel
import Iut.EtaleTheta.RigidSystems

/-!
# The projective system of model environments and discrete rigidity ([EtTh], Cor. 2.19(ii))

[EtTh], Cor. 2.19(ii) (Discrete Rigidity): letting `N` vary in a cofinal totally ordered
`E ⊆ ℕ_{≥1}`, every projective system `⋯ → M•_{M'} → M•_M → ⋯` of mod `M` mono-theta environments
is isomorphic to the natural projective system of model environments; it "follows immediately
from Cor. 2.18(iv)" (the kernels `Hom(Π_Y̲/Π_Ÿ̲, μ_N)` are finite, so the relevant `R¹ lim`
vanishes).

Here the levels are indexed by `n : ℕ` (`N = e_n` in [EtTh]) and the data of the abstract theta
setting (`Env/Model.lean`) are given levelwise, compatibly:

* cyclotomes `μ n` (finite, discrete) with actions `ψ n` and **reduction maps**
  `red n : μ (n+1) ↠ μ n`, equivariant (`hred`), with kernel the `k n`-th powers (`hker`; for
  `μ_N ↠ μ_{N'}`, `k n = N'`);
* cocycles `η n` (the reductions of `η̈^Θ̲`) with `η n = red n ∘ η (n+1)` (`hηred`), and Kummer
  cocycles `Kum n = red n ∘ Kum (n+1)` (`hKumRed`).

Results:

* `fiPow_envY`: in `Π_Y[μ]` (`Π_Y` `FISlim`, `μ` finite) the subgroup `fiPow` of `k`-th powers of
  the intrinsic cyclotome is `inl(μ^k)`;
* `redX`, `redY`: the reduction `Π_Y[μ_{n+1}] ↠ Π_Y[μ_n]`, with kernel `inl(Ker red)`
  (`ker_redY`);
* **`betaIso`**: the reduction (`MonoThetaEnv.reduce`, `Env/Reduction.lean`) of the model of
  level `n+1` is isomorphic to the model of level `n` — the natural projective system of model
  environments of [EtTh], Cor. 2.19(ii);
* `envTower`: the tower of categories of mono-theta environments with the reduction functors and
  the model system (`RigidSystems.Tower`);
* `autPY_comp_autRes`: the actions `autPY` of `Aut(model n)` on `Π_Y` (`Env/AutKernel.lean`) are
  compatible with the restriction maps;
* **`discreteRigidity_env`** ([EtTh], Cor. 2.19(ii)): every projective system of environments
  that is levelwise isomorphic to the models is isomorphic to the model system. The finiteness
  of the kernels (the half of Cor. 2.18(iv) computed in `AutKernel.lean`) is proved; the
  surjectivity half of Cor. 2.18(iv) enters as the hypothesis `hlift` (every automorphism of
  `Π_Y` induced by an automorphism of the model of level `0` is induced at every level; in
  [EtTh] it comes from the functorial algorithm of Cor. 2.18(ii) applied to automorphisms of
  `Π_X̲` — a Layer-B obligation, MR15 plan).
-/

namespace Iut.EtaleTheta.Env

open SemidirectProduct
open scoped Envelope

universe u

/-! ### `fiPow` in the model -/

section FiPow

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ) {PY : Subgroup PX}

/-- **The `k`-th powers of the intrinsic cyclotome of `Π_Y[μ]`** are `inl(μ^k)`. -/
theorem fiPow_envY [Finite μ] (hPY : Envelope.FISlim PY) (k : ℕ) :
    fiPow (envY aug ψ PY) k = ((powMonoidHom k : μ →* μ).range).map (inlY aug ψ PY) := by
  apply le_antisymm
  · rw [fiPow, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := (mem_fiCentralizers_envY aug ψ hPY x).1 hx
    exact ⟨m ^ k, ⟨m, rfl⟩, by simp [map_pow]⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨inlY aug ψ PY m, (mem_fiCentralizers_envY aug ψ hPY _).2 ⟨m, rfl⟩, by simp [map_pow]⟩

end FiPow

/-! ### Reduction maps between the levels -/

section Levels

variable {PX G : Type u} [Group PX] [Group G] (aug : PX →* G)
  {μ : ℕ → Type u} [∀ n, CommGroup (μ n)] (ψ : ∀ n, G →* MulAut (μ n))
  (red : ∀ n, μ (n + 1) →* μ n)
  (hred : ∀ n σ m, red n (ψ (n + 1) σ m) = ψ n σ (red n m))

/-- The reduction `Π_X[μ_{n+1}] → Π_X[μ_n]`. -/
def redX (n : ℕ) : EnvX aug (ψ (n + 1)) →* EnvX aug (ψ n) :=
  SemidirectProduct.map (red n) (MonoidHom.id PX) fun g => MonoidHom.ext fun m => hred n (aug g) m

@[simp] lemma redX_left (n : ℕ) (x : EnvX aug (ψ (n + 1))) :
    (redX aug ψ red hred n x).left = red n x.left := rfl

@[simp] lemma redX_right (n : ℕ) (x : EnvX aug (ψ (n + 1))) :
    (redX aug ψ red hred n x).right = x.right := rfl

variable (PY : Subgroup PX)

/-- **The reduction `Π_Y[μ_{n+1}] ↠ Π_Y[μ_n]`.** -/
def redY (n : ℕ) : envY aug (ψ (n + 1)) PY →* envY aug (ψ n) PY :=
  ((redX aug ψ red hred n).comp (envY aug (ψ (n + 1)) PY).subtype).codRestrict _ fun z => z.2

@[simp] lemma coe_redY (n : ℕ) (z : envY aug (ψ (n + 1)) PY) :
    (redY aug ψ red hred PY n z : EnvX aug (ψ n)) = redX aug ψ red hred n z := rfl

@[simp] lemma redY_inlY (n : ℕ) (m : μ (n + 1)) :
    redY aug ψ red hred PY n (inlY aug (ψ (n + 1)) PY m) = inlY aug (ψ n) PY (red n m) :=
  Subtype.ext (SemidirectProduct.ext rfl rfl)

@[simp] lemma redY_salg (n : ℕ) (h : PY) :
    redY aug ψ red hred PY n (salg aug (ψ (n + 1)) PY h) = salg aug (ψ n) PY h :=
  Subtype.ext (SemidirectProduct.ext (map_one _) rfl)

@[simp] lemma rightPY_redY (n : ℕ) (z : envY aug (ψ (n + 1)) PY) :
    rightPY aug (ψ n) PY (redY aug ψ red hred PY n z) = rightPY aug (ψ (n + 1)) PY z := rfl

variable (hs : ∀ n, Function.Surjective (red n))

include hs in
lemma redX_surjective (n : ℕ) : Function.Surjective (redX aug ψ red hred n) := fun w =>
  ⟨⟨(hs n w.left).choose, w.right⟩, SemidirectProduct.ext (hs n w.left).choose_spec rfl⟩

include hs in
lemma redY_surjective (n : ℕ) : Function.Surjective (redY aug ψ red hred PY n) := fun w =>
  ⟨⟨⟨(hs n (w : EnvX aug (ψ n)).left).choose, (w : EnvX aug (ψ n)).right⟩, w.2⟩,
    Subtype.ext (SemidirectProduct.ext (hs n _).choose_spec rfl)⟩

/-- The kernel of `Π_Y[μ_{n+1}] ↠ Π_Y[μ_n]` is `inl(Ker red)`. -/
theorem ker_redY (n : ℕ) :
    (redY aug ψ red hred PY n).ker = (red n).ker.map (inlY aug (ψ (n + 1)) PY) := by
  ext z
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz
    have h1 : red n (z : EnvX aug (ψ (n + 1))).left = 1 :=
      congrArg (fun w : envY aug (ψ n) PY => (w : EnvX aug (ψ n)).left) hz
    have h2 : (z : EnvX aug (ψ (n + 1))).right = 1 :=
      congrArg (fun w : envY aug (ψ n) PY => (w : EnvX aug (ψ n)).right) hz
    refine ⟨(z : EnvX aug (ψ (n + 1))).left, h1, Subtype.ext (SemidirectProduct.ext rfl ?_)⟩
    exact h2.symm
  · rintro ⟨m, hm, rfl⟩
    rw [redY_inlY, MonoidHom.mem_ker.1 hm, map_one]

end Levels

/-! ### The natural projective system of model environments -/

section Tower

variable {PX G : Type u} [Group PX] [Group G] [TopologicalSpace PX] [IsTopologicalGroup PX]
  (aug : PX →* G)
  {μ : ℕ → Type u} [∀ n, CommGroup (μ n)] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [∀ n, Finite (μ n)] (ψ : ∀ n, G →* MulAut (μ n))
  (red : ∀ n, μ (n + 1) →* μ n)
  (hred : ∀ n σ m, red n (ψ (n + 1) σ m) = ψ n σ (red n m))
  (hs : ∀ n, Function.Surjective (red n)) (k : ℕ → ℕ)
  (hker : ∀ n, (red n).ker = (powMonoidHom (k n) : μ (n + 1) →* μ (n + 1)).range)
  (Kum : ∀ n, Subgroup (G → μ n))
  (hKumRed : ∀ n, Kum n = (Kum (n + 1)).map (MonoidHom.compLeft (red n) G))
  {PY PYdd : Subgroup PX} [PY.Normal] (hle : PYdd ≤ PY)
  (hψ : ∀ n, IsOpen ((act aug (ψ n)).ker : Set PX)) (hKum : ∀ n, ∀ κ ∈ Kum n, IsCocycle (ψ n) κ)
  {η : ∀ n, PYdd → μ n} (hη : ∀ n, IsCocycle (actDD aug (ψ n) PYdd) (η n))
  (hηred : ∀ n g, η n g = red n (η (n + 1) g))
  (hPY : Envelope.FISlim PY)

/-- The model environment of level `n`. -/
abbrev modelN (n : ℕ) : MonoThetaEnv.{u} :=
  modelEnv aug (ψ n) (Kum n) hle (hψ n) (hKum n) (hη n)

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [PY.Normal] in
include hker hPY in
lemma fiPow_eq_ker_redY (n : ℕ) :
    fiPow (envY aug (ψ (n + 1)) PY) (k n) = (redY aug ψ red hred PY n).ker := by
  rw [fiPow_envY aug (ψ (n + 1)) hPY, ker_redY, hker]

/-- The group isomorphism `Π_Y[μ_{n+1}] / inl(μ_{n+1}^{k_n}) ≅ Π_Y[μ_n]`. -/
noncomputable def betaE (n : ℕ) :
    envY aug (ψ (n + 1)) PY ⧸ fiPow (envY aug (ψ (n + 1)) PY) (k n) ≃* envY aug (ψ n) PY :=
  (QuotientGroup.quotientMulEquivOfEq
    (fiPow_eq_ker_redY aug ψ red hred k hker hPY n)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (redY_surjective aug ψ red hred PY hs n))

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [PY.Normal] in
lemma betaE_mk (n : ℕ) (z : envY aug (ψ (n + 1)) PY) :
    betaE aug ψ red hred hs k hker hPY n (z : envY aug (ψ (n + 1)) PY ⧸ _) =
      redY aug ψ red hred PY n z := rfl

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [PY.Normal] in
lemma betaE_symm_redY (n : ℕ) (z : envY aug (ψ (n + 1)) PY) :
    (betaE aug ψ red hred hs k hker hPY n).symm (redY aug ψ red hred PY n z) =
      (z : envY aug (ψ (n + 1)) PY ⧸ fiPow (envY aug (ψ (n + 1)) PY) (k n)) := by
  rw [MulEquiv.symm_apply_eq, betaE_mk]

omit [IsTopologicalGroup PX] [∀ n, Finite (μ n)] [PY.Normal] in
lemma continuous_redY (n : ℕ) : Continuous (redY aug ψ red hred PY n) := by
  refine Continuous.subtype_mk ?_ _
  refine Envelope.continuous_mk ?_ (Envelope.continuous_right.comp continuous_subtype_val)
  exact (continuous_of_discreteTopology (f := red n)).comp
    (Envelope.continuous_left.comp continuous_subtype_val)

/-- **The reduction of the model of level `n+1` is the model of level `n`**, as topological
groups. -/
noncomputable def betaT (n : ℕ) :
    (envY aug (ψ (n + 1)) PY ⧸ fiPow (envY aug (ψ (n + 1)) PY) (k n)) ≃ₜ* envY aug (ψ n) PY where
  toMulEquiv := betaE aug ψ red hred hs k hker hPY n
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact continuous_redY aug ψ red hred n (PY := PY)
  continuous_invFun := by
    -- a set-theoretic section of `red n` gives a continuous formula for the inverse
    let s : μ n → μ (n + 1) := fun m => (hs n m).choose
    let lift : envY aug (ψ n) PY → envY aug (ψ (n + 1)) PY := fun w =>
      ⟨⟨s (w : EnvX aug (ψ n)).left, (w : EnvX aug (ψ n)).right⟩, w.2⟩
    have hlift : ∀ w, redY aug ψ red hred PY n (lift w) = w := fun w =>
      Subtype.ext (SemidirectProduct.ext (hs n _).choose_spec rfl)
    have hc : Continuous lift := by
      refine Continuous.subtype_mk ?_ _
      refine Envelope.continuous_mk ?_ (Envelope.continuous_right.comp continuous_subtype_val)
      exact (continuous_of_discreteTopology (f := s)).comp
        (Envelope.continuous_left.comp continuous_subtype_val)
    have heq : ⇑(betaE aug ψ red hred hs k hker hPY n).symm =
        fun w => ((lift w : envY aug (ψ (n + 1)) PY) :
          envY aug (ψ (n + 1)) PY ⧸ fiPow (envY aug (ψ (n + 1)) PY) (k n)) := by
      funext w
      conv_lhs => rw [← hlift w]
      exact betaE_symm_redY aug ψ red hred hs k hker hPY n (lift w)
    change Continuous ⇑(betaE aug ψ red hred hs k hker hPY n).symm
    rw [heq]
    exact QuotientGroup.continuous_mk.comp hc

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [∀ n, Finite (μ n)] [PY.Normal] in
lemma redX_twist (n : ℕ) (κ : G → μ (n + 1)) (hκ : IsCocycle (ψ (n + 1)) κ)
    (hκ' : IsCocycle (ψ n) (fun σ => red n (κ σ))) (x : EnvX aug (ψ (n + 1))) :
    redX aug ψ red hred n (twist κ hκ x) =
      twist (fun σ => red n (κ σ)) hκ' (redX aug ψ red hred n x) :=
  SemidirectProduct.ext (by simp [map_mul]) rfl

omit [Group G] [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [∀ n, Finite (μ n)] [PY.Normal] in
include hKumRed in
lemma red_mem_Kum (n : ℕ) {κ : G → μ (n + 1)} (hκ : κ ∈ Kum (n + 1)) :
    (fun σ => red n (κ σ)) ∈ Kum n := by
  rw [hKumRed n]
  exact ⟨κ, hκ, rfl⟩

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [PY.Normal] in
/-- The transport of the automorphism induced by `γ` on the reduction, along `betaT`, applied to
`redY z`. -/
lemma conjAut_betaE_quotAut_redY (n : ℕ) (γ : MulAut (envY aug (ψ (n + 1)) PY))
    (z : envY aug (ψ (n + 1)) PY) :
    MonoThetaEnv.conjAut (betaE aug ψ red hred hs k hker hPY n)
        (quotAut (envY aug (ψ (n + 1)) PY) (k n) γ) (redY aug ψ red hred PY n z) =
      redY aug ψ red hred PY n (γ z) := by
  rw [MonoThetaEnv.conjAut_apply, betaE_symm_redY, quotAut_mk, betaE_mk]

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] in
include hKumRed in
/-- `D` of the reduction is mapped onto `D` of the lower model. -/
theorem map_D_betaE (n : ℕ) :
    ((DY aug (ψ (n + 1)) (Kum (n + 1)) PY (hKum (n + 1))).map
        (quotAut (envY aug (ψ (n + 1)) PY) (k n))).map
      (MonoThetaEnv.conjAut (betaE aug ψ red hred hs k hker hPY n)) =
      DY aug (ψ n) (Kum n) PY (hKum n) := by
  rw [Subgroup.map_map]
  ext γ'
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨γ, ⟨β, ⟨κ, hκ, x, rfl⟩, hγβ⟩, rfl⟩
    have hκn := red_mem_Kum red Kum hKumRed n hκ
    refine ⟨twist _ (hKum n _ hκn) * MulAut.conj (redX aug ψ red hred n x),
      ⟨_, hκn, _, rfl⟩, fun w => ?_⟩
    obtain ⟨z, rfl⟩ := redY_surjective aug ψ red hred PY hs n w
    rw [conjAut_betaE_quotAut_redY, coe_redY, hγβ, MulAut.mul_apply, MulAut.conj_apply,
      redX_twist aug ψ red hred n κ _ (hKum n _ hκn)]
    simp only [map_mul, map_inv, coe_redY, MulAut.mul_apply, MulAut.conj_apply]
  · rintro ⟨β', ⟨κ', hκ', x', rfl⟩, hγβ'⟩
    rw [hKumRed n] at hκ'
    obtain ⟨κ, hκ, rfl⟩ := hκ'
    obtain ⟨x, rfl⟩ := redX_surjective aug ψ red hred hs n x'
    let β := twist κ (hKum (n + 1) κ hκ) * MulAut.conj x
    have hβ : ∀ y, β y ∈ envY aug (ψ (n + 1)) PY ↔ y ∈ envY aug (ψ (n + 1)) PY := by
      intro y
      simp only [β, MulAut.mul_apply]
      rw [twist_mem_envY_iff, conj_mem_envY_iff]
    refine ⟨restrictAut aug (ψ (n + 1)) PY β hβ,
      restrictAut_mem_DY aug (ψ (n + 1)) (Kum (n + 1)) PY (hKum (n + 1)) β hβ
        ⟨κ, hκ, x, rfl⟩, MulEquiv.ext fun w => ?_⟩
    obtain ⟨z, rfl⟩ := redY_surjective aug ψ red hred PY hs n w
    apply Subtype.ext
    rw [conjAut_betaE_quotAut_redY, hγβ', coe_redY, coe_redY, coe_restrictAut]
    simp only [β, MulAut.mul_apply, MulAut.conj_apply]
    rw [redX_twist aug ψ red hred n κ _ (hKum n _ (red_mem_Kum red Kum hKumRed n hκ))]
    simp only [map_mul, map_inv]
    rfl

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [∀ n, Finite (μ n)] [PY.Normal] in
include hηred in
lemma redY_comp_thetaSection (n : ℕ) :
    (redY aug ψ red hred PY n).comp (thetaSection aug (ψ (n + 1)) hle (hη (n + 1))) =
      thetaSection aug (ψ n) hle (hη n) := by
  ext g
  · simp [hηred n g]
  · rfl

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [∀ n, TopologicalSpace (μ n)]
  [∀ n, DiscreteTopology (μ n)] [PY.Normal] in
include hηred in
/-- The theta subgroups of the reduction are mapped onto those of the lower model. -/
theorem map_theta_betaE (n : ℕ) :
    Subgroup.map (betaE aug ψ red hred hs k hker hPY n).toMonoidHom ''
        (Subgroup.map (QuotientGroup.mk' (fiPow (envY aug (ψ (n + 1)) PY) (k n))) ''
          thetaSubgroups aug (ψ (n + 1)) hle (hη (n + 1))) =
      thetaSubgroups aug (ψ n) hle (hη n) := by
  rw [Set.image_image]
  have hcomp : ∀ H : Subgroup (envY aug (ψ (n + 1)) PY),
      Subgroup.map (betaE aug ψ red hred hs k hker hPY n).toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (fiPow (envY aug (ψ (n + 1)) PY) (k n))) H) =
      H.map (redY aug ψ red hred PY n) := by
    intro H
    rw [Subgroup.map_map]
    rfl
  simp only [hcomp]
  have hconj : ∀ ζ : μ (n + 1),
      ((thetaSection aug (ψ (n + 1)) hle (hη (n + 1))).range.map
        (MulAut.conj (inlY aug (ψ (n + 1)) PY ζ)).toMonoidHom).map (redY aug ψ red hred PY n) =
      (thetaSection aug (ψ n) hle (hη n)).range.map
        (MulAut.conj (inlY aug (ψ n) PY (red n ζ))).toMonoidHom := by
    intro ζ
    rw [← redY_comp_thetaSection aug ψ red hred hle hη hηred n, Subgroup.map_map,
      MonoidHom.range_comp, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun z => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv, redY_inlY]
  ext H
  simp only [Set.mem_image, mem_thetaSubgroups_iff]
  constructor
  · rintro ⟨_, ⟨ζ, rfl⟩, rfl⟩
    exact ⟨red n ζ, hconj ζ⟩
  · rintro ⟨ζ', rfl⟩
    obtain ⟨ζ, rfl⟩ := hs n ζ'
    exact ⟨_, ⟨ζ, rfl⟩, hconj ζ⟩

/-- **The natural projective system of model environments** ([EtTh], Cor. 2.19(ii)): the
reduction of the model environment of level `n+1` is isomorphic to the model environment of
level `n`, via `Π_Y[μ_{n+1}]/inl(μ_{n+1}^{k_n}) ≅ Π_Y[μ_n]`. -/
noncomputable def betaIso (n : ℕ) :
    MonoThetaEnv.Iso ((modelN aug ψ Kum hle hψ hKum hη (n + 1)).reduce (k n))
      (modelN aug ψ Kum hle hψ hKum hη n) where
  e := betaT aug ψ red hred hs k hker hPY n
  map_D := map_D_betaE aug ψ red hred hs k hker Kum hKumRed hKum hPY n
  map_theta := map_theta_betaE aug ψ red hred hs k hker hle hη hηred hPY n

lemma betaIso_e_mk (n : ℕ) (z : envY aug (ψ (n + 1)) PY) :
    (betaIso aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).e
      (z : envY aug (ψ (n + 1)) PY ⧸ fiPow (envY aug (ψ (n + 1)) PY) (k n)) =
      redY aug ψ red hred PY n z := rfl

/-- **The tower of mono-theta environments**: at each level the groupoid of environments, the
reduction functors `M ↦ M_{k_n}`, and the natural projective system of model environments. -/
noncomputable def envTower : RigidSystems.Tower.{u + 1, u} where
  C _ := MonoThetaEnv.{u}
  res n := MonoThetaEnv.reduceFunctor (k n)
  model n := modelN aug ψ Kum hle hψ hKum hη n
  β n := (betaIso aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).toCatIso

/-- The action on `Π_Y` of the automorphisms of the model of level `n`. -/
noncomputable abbrev autPYN (n : ℕ) :
    CategoryTheory.Aut ((envTower aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred
      hPY).model n) →* MulAut PY :=
  autPY aug (ψ n) (Kum n) hle (hψ n) (hKum n) (hη n) hPY

/-- **The actions on `Π_Y` are compatible with the restriction maps** `Aut(M_{n+1}) → Aut(M_n)`. -/
theorem autPY_comp_autRes (n : ℕ) :
    (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).comp
        ((envTower aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY).autRes n) =
      autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY (n + 1) := by
  refine MonoidHom.ext fun a => MulEquiv.ext fun h => ?_
  change rightPY aug (ψ n) PY ((betaIso aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη
      hηred hPY n).e ((MonoThetaEnv.reduceIso (k n) (MonoThetaEnv.homIso a.hom)).e
        ((betaIso aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).e.symm
          (salg aug (ψ n) PY h)))) = _
  have h1 : (betaIso aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).e.symm
      (salg aug (ψ n) PY h) = (QuotientGroup.mk (salg aug (ψ (n + 1)) PY h) :
        ((modelN aug ψ Kum hle hψ hKum hη (n + 1)).reduce (k n)).G) := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact (redY_salg aug ψ red hred PY n h).symm
  rw [h1]
  rfl

/-- The image of `Aut(M_{n+1})` in `Aut(Π_Y)` is contained in the image of `Aut(M_n)`. -/
theorem range_autPYN_succ_le (n : ℕ) :
    (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY (n + 1)).range ≤
      (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).range := by
  rw [← autPY_comp_autRes, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

theorem range_autPYN_le_zero (n : ℕ) :
    (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).range ≤
      (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY 0).range := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (range_autPYN_succ_le aug ψ red hred hs k hker Kum hKumRed hle hψ hKum
      hη hηred hPY n).trans ih

/-- **Discrete rigidity** ([EtTh], Cor. 2.19(ii)): every projective system of mono-theta
environments (with respect to the reduction functors) that is levelwise isomorphic to the model
environments is isomorphic to the natural projective system of model environments.

Inputs: the finiteness of `Ker(Aut(M_n) → Aut(Π_Y))` (`finite_ker_autPY`, from
`[Π_Y̲ : Π_Ÿ̲] < ∞`) is proved; `hlift` is the surjectivity half of [EtTh], Cor. 2.18(iv) (every
automorphism of `Π_Y` coming from the level-`0` model comes from every level; Layer-B
obligation). -/
theorem discreteRigidity_env [(PYdd.subgroupOf PY).FiniteIndex]
    (hlift : ∀ n, (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY 0).range ≤
      (autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY n).range)
    (S : (envTower aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY).System)
    (hS : ∀ n, Nonempty (S.X n ≅
      (envTower aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY).model n)) :
    S.IsoModel := by
  let p := autPYN aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη hηred hPY
  let H := (p 0).range
  let q : ∀ n, CategoryTheory.Aut ((envTower aug ψ red hred hs k hker Kum hKumRed hle hψ hKum hη
      hηred hPY).model n) →* H := fun n =>
    (p n).codRestrict H fun a => range_autPYN_le_zero aug ψ red hred hs k hker Kum hKumRed hle
      hψ hKum hη hηred hPY n ⟨a, rfl⟩
  refine RigidSystems.Tower.discreteRigidity _ q (fun n => ?_) (fun n => ?_) (fun n => ?_) S hS
  · rintro ⟨φ, hφ⟩
    obtain ⟨a, ha⟩ := hlift n hφ
    exact ⟨a, Subtype.ext ha⟩
  · refine MonoidHom.ext fun a => Subtype.ext ?_
    exact congrArg (fun f => f a) (autPY_comp_autRes aug ψ red hred hs k hker Kum hKumRed hle hψ
      hKum hη hηred hPY n)
  · haveI : Finite (p n).ker := finite_ker_autPY aug (ψ n) (Kum n) hle (hψ n) (hKum n) (hη n) hPY
    refine Finite.of_injective (fun a : (q n).ker => (⟨a.1, ?_⟩ : (p n).ker)) fun a b hab => ?_
    · have := congrArg Subtype.val (MonoidHom.mem_ker.1 a.2)
      exact MonoidHom.mem_ker.2 this
    · exact Subtype.ext (by have := congrArg Subtype.val hab; exact this)

end Tower

end Iut.EtaleTheta.Env
