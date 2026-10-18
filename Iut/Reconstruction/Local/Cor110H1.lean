/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110H2
import Iut.Reconstruction.Local.Cor110Kummer

/-!
# `H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab ↠ Ẑ` with group-theoretic coefficients ([AbsTopIII], Cor. 1.10 (b))

[AbsTopIII], Corollary 1.10 (i) (a), (b) (`Topics in Absolute Anabelian Geometry III.txt`,
l.2375–2377 and l.2401–2406):

> "`μ_{Q/Z}(G_k) := lim→_H (H^ab)_tors`; `μ_Ẑ(G_k) := Hom(Q/Z, μ_{Q/Z}(G_k))`"
> "(b) By applying the isomorphism of (a) [and the cup-product in group cohomology], one
> constructs the surjection `H¹(G_k, μ_Ẑ(G_k)) ∼→ G_k^ab ↠ G^unr ∼→ Ẑ` determined by the
> Frobenius element in the maximal unramified quotient `G^unr` of `G_k` […]."

`Cor110Kummer.lean` proves (b) with the field-theoretic coefficients `Ẑ(1) = lim_n μ_n(Ω)`.
Here the coefficients are the **group-theoretic cyclotome** of `Cor110.lean`:

* `MuZHatG G = μ_Ẑ(G) = lim_n μ_n(G)` (`μ_n(G)` the `n`-torsion of `lim→_U U^ab`, discrete),
  with the inverse-limit topology and the `G`-action through `barConj`; this is
  `Hom(ℚ/ℤ, μ_{ℚ/ℤ}(G))` written as an inverse limit (the convention of `H2ZHatG`);
* functoriality: `ψ : G ≃ₜ* G'` induces `H1ZHatGEquivOf ψ : H¹(G, μ_Ẑ(G)) ≃* H¹(G', μ_Ẑ(G'))`;
* for `G = G_k`: `muZHatEquiv p k Ω : μ_Ẑ(G_k) ≃* Ẑ(1)`, a `G_k`-equivariant homeomorphism
  (levelwise `muNEquiv`), hence
  **`h1ZHatGAbEquiv p k Ω : H¹(G_k, μ_Ẑ(G_k)) ≃* G_k^ab`** and the **Frobenius surjection**
  `h1FrobG p k Ω : H¹(G_k, μ_Ẑ(G_k)) ↠ Ẑ` (`h1FrobG_surjective`), sending the Kummer class of
  `a ∈ k^×` to `v(a)` (`h1FrobG_kummerZHatG`);
* (d) with group-theoretic coefficients: `range_kummerZHatG`, the Kummer image is the inverse
  image of `ℤ = ⟨Frob⟩`.

Not formalised here: that `h1ZHatGAbEquiv` commutes with `H1ZHatGEquivOf ψ` for an arbitrary
`ψ : G_k ≃ₜ* G_{k'}` (this is equivalent to the naturality of `h2ZHatGEquiv`, see
`Cor110Natural.lean`). The Frobenius surjection `frobAb` itself is group-theoretic
(`frobAb_abEquiv`).
-/

namespace Iut.Reconstruction

open PadicField IntermediateField MonoidHom KummerTheory Brauer

set_option linter.unusedSectionVars false

noncomputable section

universe u

/-! ### Transport of `H¹` -/

section Congr

variable {G G' M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M] [Group G'] [TopologicalSpace G'] [CommGroup M']
  [TopologicalSpace M'] [IsTopologicalGroup M'] [MulDistribMulAction G' M']

/-- **Transport of `H¹`** along an isomorphism `e : G ≃ₜ* G'` of topological groups and an
`e`-equivariant isomorphism `ψ : M ≃* M'` of coefficients which is a homeomorphism. -/
def h1Congr (e : G ≃ₜ* G') (ψ : M ≃* M') (hψ : Continuous ψ) (hψ' : Continuous ψ.symm)
    (h : ∀ (g : G) (m : M), ψ (g • m) = e g • ψ m) : ContH1 G M ≃* ContH1 G' M' where
  toFun := ContH1.map e.symm.toMulEquiv.toMonoidHom e.symm.continuous ψ.toMonoidHom hψ
    (fun g m => by
      change ψ (e.symm g • m) = g • ψ m
      rw [h, ContinuousMulEquiv.apply_symm_apply])
  invFun := ContH1.map e.toMulEquiv.toMonoidHom e.continuous ψ.symm.toMonoidHom hψ'
    (fun g m => by
      change ψ.symm (e g • m) = g • ψ.symm m
      apply ψ.injective
      rw [MulEquiv.apply_symm_apply, h, MulEquiv.apply_symm_apply])
  left_inv x := by
    induction x using ContH1.induction_on with | h c => ?_
    simp only [ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun a => by
      simp only [ContH1.cocyclesMap_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact congrArg c (e.symm_apply_apply a))
  right_inv x := by
    induction x using ContH1.induction_on with | h c => ?_
    simp only [ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun a => by
      simp only [ContH1.cocyclesMap_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact congrArg c (e.apply_symm_apply a))
  map_mul' := map_mul _

theorem h1Congr_mk (e : G ≃ₜ* G') (ψ : M ≃* M') (hψ : Continuous ψ) (hψ' : Continuous ψ.symm)
    (h : ∀ (g : G) (m : M), ψ (g • m) = e g • ψ m) (c : ContH1.cocycles G M) :
    ∃ c' : ContH1.cocycles G' M', h1Congr e ψ hψ hψ' h (ContH1.mk c) = ContH1.mk c' ∧
      ∀ a, c' a = ψ (c (e.symm a)) :=
  ⟨_, rfl, fun _ => rfl⟩

end Congr

/-! ### The group-theoretic `μ_Ẑ(G)` -/

section GroupTheoretic

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `μ_n(G)` is discrete. -/
instance (n : ℕ) : TopologicalSpace (muN G n) := ⊥

instance (n : ℕ) : DiscreteTopology (muN G n) := ⟨rfl⟩

instance (n : ℕ) : IsTopologicalGroup (muN G n) where

/-- The subgroup `lim_n μ_n(G) ⊆ ∏_n μ_n(G)`. -/
def muZHatSub : Subgroup (∀ n : ℕ+, muN G n) :=
  limSub (A := fun n : ℕ+ => muN G n) fun h => muNPow G h

/-- **`μ_Ẑ(G) = lim_n μ_n(G)`**, along `z ↦ z^{m/n}`, with the inverse-limit topology. -/
def MuZHatG : Type _ := muZHatSub G

instance : CommGroup (MuZHatG G) := inferInstanceAs (CommGroup (muZHatSub G))

instance : TopologicalSpace (MuZHatG G) := inferInstanceAs (TopologicalSpace (muZHatSub G))

instance : IsTopologicalGroup (MuZHatG G) := inferInstanceAs (IsTopologicalGroup (muZHatSub G))

variable {G}

/-- The `n`-th component of `x ∈ μ_Ẑ(G)`. -/
def MuZHatG.val (x : MuZHatG G) (n : ℕ+) : muN G n := (show muZHatSub G from x).1 n

theorem MuZHatG.compat (x : MuZHatG G) (n m : ℕ+) (h : (n : ℕ) ∣ m) :
    muNPow G h (x.val m) = x.val n :=
  (show muZHatSub G from x).2 n m h

/-- An element of `μ_Ẑ(G)` from a compatible family. -/
def MuZHatG.mk (f : ∀ n : ℕ+, muN G n)
    (hf : ∀ n m : ℕ+, ∀ h : (n : ℕ) ∣ m, muNPow G h (f m) = f n) : MuZHatG G :=
  (⟨f, hf⟩ : muZHatSub G)

@[simp]
theorem MuZHatG.val_mk (f : ∀ n : ℕ+, muN G n)
    (hf : ∀ n m : ℕ+, ∀ h : (n : ℕ) ∣ m, muNPow G h (f m) = f n) (n : ℕ+) :
    (MuZHatG.mk f hf).val n = f n := rfl

theorem MuZHatG.ext {x y : MuZHatG G} (h : ∀ n, x.val n = y.val n) : x = y :=
  Subtype.ext (funext h)

@[simp]
theorem MuZHatG.one_val (n : ℕ+) : (1 : MuZHatG G).val n = 1 := rfl

@[simp]
theorem MuZHatG.mul_val (x y : MuZHatG G) (n : ℕ+) : (x * y).val n = x.val n * y.val n := rfl

theorem MuZHatG.continuous_val (n : ℕ+) : Continuous fun x : MuZHatG G => x.val n :=
  (continuous_apply n).comp continuous_subtype_val

theorem MuZHatG.continuous_to {X : Type*} [TopologicalSpace X] {f : X → MuZHatG G}
    (h : ∀ n, Continuous fun x => (f x).val n) : Continuous f :=
  (continuous_pi h).subtype_mk (fun x => (show muZHatSub G from f x).2)

variable (G) in
/-- **The `G`-module `μ_Ẑ(G)`**, componentwise. -/
instance : MulDistribMulAction G (MuZHatG G) where
  smul g x := MuZHatG.mk (fun n => g • x.val n) fun n m h => by
    rw [muNPow_smul, x.compat n m h]
  one_smul x := MuZHatG.ext fun n => one_smul G (x.val n)
  mul_smul g h x := MuZHatG.ext fun n => mul_smul g h (x.val n)
  smul_mul g x y := MuZHatG.ext fun n => smul_mul' g (x.val n) (y.val n)
  smul_one g := MuZHatG.ext fun n => smul_one g

@[simp]
theorem MuZHatG.smul_val (g : G) (x : MuZHatG G) (n : ℕ+) : (g • x).val n = g • x.val n := rfl

end GroupTheoretic

/-! ### Functoriality -/

section Functorial

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']

theorem muNPow_muNEquivOf (ψ : G ≃ₜ* G') {n m : ℕ} (h : n ∣ m) (z : muN G m) :
    muNPow G' h (muNEquivOf ψ m z) = muNEquivOf ψ n (muNPow G h z) :=
  Subtype.ext (map_pow (barMap ψ) _ _).symm

/-- The map `μ_Ẑ(G) → μ_Ẑ(G')` induced by `ψ : G ≃ₜ* G'`. -/
def muZHatGHomOf (ψ : G ≃ₜ* G') : MuZHatG G →* MuZHatG G' where
  toFun x := MuZHatG.mk (fun n => muNEquivOf ψ n (x.val n)) fun n m h => by
    rw [muNPow_muNEquivOf, x.compat n m h]
  map_one' := MuZHatG.ext fun n => map_one (muNEquivOf ψ n)
  map_mul' x y := MuZHatG.ext fun n => map_mul (muNEquivOf ψ n) (x.val n) (y.val n)

/-- `μ_Ẑ(G) ≃* μ_Ẑ(G')` induced by `ψ : G ≃ₜ* G'`. -/
def muZHatGEquivOf (ψ : G ≃ₜ* G') : MuZHatG G ≃* MuZHatG G' where
  toFun := muZHatGHomOf ψ
  invFun := muZHatGHomOf ψ.symm
  left_inv x := MuZHatG.ext fun n => (muNEquivOf ψ n).symm_apply_apply (x.val n)
  right_inv x := MuZHatG.ext fun n => (muNEquivOf ψ n).apply_symm_apply (x.val n)
  map_mul' := map_mul _

theorem muZHatGEquivOf_val (ψ : G ≃ₜ* G') (x : MuZHatG G) (n : ℕ+) :
    (muZHatGEquivOf ψ x).val n = muNEquivOf ψ n (x.val n) := rfl

theorem continuous_muZHatGEquivOf (ψ : G ≃ₜ* G') : Continuous (muZHatGEquivOf ψ) :=
  MuZHatG.continuous_to fun n =>
    (continuous_of_discreteTopology (f := fun z : muN G n => muNEquivOf ψ n z)).comp
      (MuZHatG.continuous_val n)

theorem muZHatGEquivOf_symm_apply (ψ : G ≃ₜ* G') (x : MuZHatG G') :
    (muZHatGEquivOf ψ).symm x = muZHatGEquivOf ψ.symm x := rfl

theorem muZHatGEquivOf_smul (ψ : G ≃ₜ* G') (g : G) (x : MuZHatG G) :
    muZHatGEquivOf ψ (g • x) = ψ g • muZHatGEquivOf ψ x :=
  MuZHatG.ext fun n => muNEquivOf_smul ψ g (x.val n)

/-- **`H¹(G, μ_Ẑ(G))` is group-theoretic**: `ψ : G ≃ₜ* G'` induces
`H¹(G, μ_Ẑ(G)) ≃* H¹(G', μ_Ẑ(G'))`. -/
def H1ZHatGEquivOf (ψ : G ≃ₜ* G') : ContH1 G (MuZHatG G) ≃* ContH1 G' (MuZHatG G') :=
  h1Congr ψ (muZHatGEquivOf ψ) (continuous_muZHatGEquivOf ψ)
    (continuous_muZHatGEquivOf ψ.symm) (muZHatGEquivOf_smul ψ)

end Functorial

/-! ### `G = G_k`: `μ_Ẑ(G_k) ≅ Ẑ(1)` and `H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem muPow_eq_transition {n m : ℕ} (h : n ∣ m) (ζ : Mu m Ω) :
    muPow h ζ = Mu.transition h ζ :=
  Mu.ext (by rw [val_muPow, Mu.val_transition])

theorem kIdx_pos (i : KummerIndex k) : 0 < i.n := Nat.pos_of_ne_zero i.n_ne_zero

variable (p) in
include p in
theorem natCast_ne_zero_padic (n : ℕ+) : ((n : ℕ) : k) ≠ 0 :=
  haveI := charZero_padic p k
  Nat.cast_ne_zero.2 n.ne_zero

/-- The level-`i` component of `μ_Ẑ(G_k) → Ẑ(1)`. -/
def muZHatLevel (x : MuZHatG (Ω ≃ₐ[k] Ω)) (i : KummerIndex k) : Mu i.n Ω :=
  muNEquiv p k Ω i.n (x.val ⟨i.n, kIdx_pos i⟩)

theorem muZHatLevel_compat (x : MuZHatG (Ω ≃ₐ[k] Ω)) (i j : KummerIndex k) (h : i ≤ j) :
    Mu.transition h (muZHatLevel (p := p) x j) = muZHatLevel (p := p) x i := by
  have h' : i.n ∣ j.n := h
  rw [muZHatLevel, muZHatLevel, ← muPow_eq_transition h', muNEquiv_muNPow]
  exact congrArg (muNEquiv p k Ω i.n) (x.compat ⟨i.n, kIdx_pos i⟩ ⟨j.n, kIdx_pos j⟩ h')

variable (p k Ω) in
/-- The map `μ_Ẑ(G_k) → Ẑ(1)`, levelwise `muNEquiv`. -/
def muZHatHom : MuZHatG (Ω ≃ₐ[k] Ω) →* ZHatOne k Ω where
  toFun x := ⟨fun i => muZHatLevel (p := p) x i, fun i j h => muZHatLevel_compat x i j h⟩
  map_one' := Subtype.ext (funext fun i => map_one (muNEquiv p k Ω i.n))
  map_mul' _ _ := Subtype.ext (funext fun i => map_mul (muNEquiv p k Ω i.n) _ _)

/-- The level-`n` component of `Ẑ(1) → μ_Ẑ(G_k)`. -/
def muZHatInvLevel (y : ZHatOne k Ω) (n : ℕ+) : muN (Ω ≃ₐ[k] Ω) n :=
  (muNEquiv p k Ω n).symm (ZHatOne.proj ⟨n, natCast_ne_zero_padic p n⟩ y)

theorem muZHatInvLevel_compat (y : ZHatOne k Ω) (n m : ℕ+) (h : (n : ℕ) ∣ m) :
    muNPow _ h (muZHatInvLevel (p := p) y m) = muZHatInvLevel (p := p) y n := by
  apply (muNEquiv p k Ω n).injective
  rw [muZHatInvLevel, muZHatInvLevel, ← muNEquiv_muNPow, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, muPow_eq_transition]
  exact ZHatOne.transition_proj (i := ⟨n, natCast_ne_zero_padic p n⟩)
    (j := ⟨m, natCast_ne_zero_padic p m⟩) h y

variable (p k Ω) in
/-- The map `Ẑ(1) → μ_Ẑ(G_k)`, levelwise `muNEquiv⁻¹`. -/
def muZHatInv : ZHatOne k Ω →* MuZHatG (Ω ≃ₐ[k] Ω) where
  toFun y := MuZHatG.mk (fun n => muZHatInvLevel (p := p) y n) fun n m h =>
    muZHatInvLevel_compat y n m h
  map_one' := MuZHatG.ext fun n => map_one (muNEquiv p k Ω n).symm
  map_mul' _ _ := MuZHatG.ext fun n => map_mul (muNEquiv p k Ω n).symm _ _

variable (p k Ω) in
/-- **`μ_Ẑ(G_k) ≅ Ẑ(1)`**: the group-theoretic cyclotome is the field-theoretic one. -/
def muZHatEquiv : MuZHatG (Ω ≃ₐ[k] Ω) ≃* ZHatOne k Ω where
  toFun := muZHatHom p k Ω
  invFun := muZHatInv p k Ω
  left_inv x := MuZHatG.ext fun n => (muNEquiv p k Ω n).symm_apply_apply (x.val n)
  right_inv y := Subtype.ext (funext fun i =>
    (muNEquiv p k Ω i.n).apply_symm_apply (ZHatOne.proj i y))
  map_mul' := map_mul _

theorem continuous_muZHatEquiv : Continuous (muZHatEquiv p k Ω) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact (continuous_of_discreteTopology
    (f := fun z : muN (Ω ≃ₐ[k] Ω) i.n => muNEquiv p k Ω i.n z)).comp
    (MuZHatG.continuous_val ⟨i.n, kIdx_pos i⟩)

theorem continuous_muZHatEquiv_symm : Continuous (muZHatEquiv p k Ω).symm :=
  MuZHatG.continuous_to fun n =>
    (continuous_of_discreteTopology
      (f := fun ζ : Mu (n : ℕ) Ω => (muNEquiv p k Ω n).symm ζ)).comp
      (ZHatOne.continuous_proj ⟨n, natCast_ne_zero_padic p n⟩)

/-- **`μ_Ẑ(G_k) ≅ Ẑ(1)` is `G_k`-equivariant.** -/
theorem muZHatEquiv_smul (σ : Ω ≃ₐ[k] Ω) (x : MuZHatG (Ω ≃ₐ[k] Ω)) :
    muZHatEquiv p k Ω (σ • x) = σ • muZHatEquiv p k Ω x :=
  Subtype.ext (funext fun i => muNEquiv_smul i.n σ (x.val ⟨i.n, kIdx_pos i⟩))

variable (p k Ω) in
/-- `H¹(G_k, μ_Ẑ(G_k)) ≅ H¹(G_k, Ẑ(1))`. -/
def h1MuZHatEquiv :
    ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω)) ≃* ContH1 (Ω ≃ₐ[k] Ω) (ZHatOne k Ω) :=
  h1Congr (ContinuousMulEquiv.refl _) (muZHatEquiv p k Ω) continuous_muZHatEquiv
    continuous_muZHatEquiv_symm muZHatEquiv_smul

variable (p k Ω) in
/-- **[AbsTopIII], Corollary 1.10 (b)**: `H¹(G_k, μ_Ẑ(G_k)) ≃* G_k^ab`, for the group-theoretic
cyclotome `μ_Ẑ(G_k) = lim_n μ_n(G_k)` (Kummer theory and local class field theory). -/
def h1ZHatGAbEquiv :
    ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω)) ≃* TopologicalAbelianization (Ω ≃ₐ[k] Ω) :=
  (h1MuZHatEquiv p k Ω).trans (h1AbEquiv p k Ω)

variable (p k Ω) in
/-- The Kummer map `k^× → H¹(G_k, μ_Ẑ(G_k))`. -/
def kummerZHatG : kˣ →* ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω)) :=
  (h1MuZHatEquiv p k Ω).symm.toMonoidHom.comp (kummerZHat k Ω)

/-- **The Kummer class of `a ∈ k^×` corresponds to the Artin symbol of `a`.** -/
theorem h1ZHatGAbEquiv_kummerZHatG (a : kˣ) :
    h1ZHatGAbEquiv p k Ω (kummerZHatG p k Ω a) = multAbEquiv p k Ω a := by
  change h1AbEquiv p k Ω ((h1MuZHatEquiv p k Ω) ((h1MuZHatEquiv p k Ω).symm _)) = _
  rw [MulEquiv.apply_symm_apply, h1AbEquiv_kummerZHat]

theorem kummerZHatG_injective : Function.Injective (kummerZHatG p k Ω) :=
  (h1MuZHatEquiv p k Ω).symm.injective.comp (kummerZHat_injective p)

variable (p k Ω) in
/-- **The surjection `H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab ↠ Ẑ`** of [AbsTopIII], Corollary 1.10 (b),
determined by the Frobenius (`frobAb_of_isFrobLift`). -/
def h1FrobG : ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω)) →* Multiplicative ZHat :=
  (frobAb p k Ω).comp (h1ZHatGAbEquiv p k Ω).toMonoidHom

theorem h1FrobG_apply (c : ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω))) :
    h1FrobG p k Ω c = frobAb p k Ω (h1ZHatGAbEquiv p k Ω c) := rfl

theorem h1FrobG_surjective : Function.Surjective (h1FrobG p k Ω) :=
  (frobAb_surjective (p := p) (k := k) (Ω := Ω)).comp (h1ZHatGAbEquiv p k Ω).surjective

/-- On Kummer classes, `h1FrobG` is the valuation. -/
theorem h1FrobG_kummerZHatG (a : kˣ) :
    h1FrobG p k Ω (kummerZHatG p k Ω a) = Multiplicative.ofAdd (intToZHat (v p (a : k))) := by
  rw [h1FrobG_apply, h1ZHatGAbEquiv_kummerZHatG, frobAb_multAbEquiv]

/-- **[AbsTopIII], Corollary 1.10 (d)**, with the group-theoretic cyclotome `μ_Ẑ(G_k)`: the image
of the Kummer map `k^× → H¹(G_k, μ_Ẑ(G_k))` is the inverse image of `ℤ = ⟨Frob⟩ ⊆ Ẑ` under
`H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab ↠ Ẑ`. -/
theorem range_kummerZHatG :
    (kummerZHatG p k Ω).range =
      (Subgroup.zpowers (Multiplicative.ofAdd (intToZHat 1))).comap (h1FrobG p k Ω) := by
  have h1 : (kummerZHatG p k Ω).range =
      (kummerZHat k Ω).range.comap (h1MuZHatEquiv p k Ω).toMonoidHom := by
    ext c
    simp only [MonoidHom.mem_range, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, ((h1MuZHatEquiv p k Ω).apply_symm_apply _).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by
        change (h1MuZHatEquiv p k Ω).symm _ = c
        rw [ha, MulEquiv.symm_apply_apply]⟩
  rw [h1, range_kummerZHat (p := p), Subgroup.comap_comap]
  rfl

end Galois

end

end Iut.Reconstruction
