/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110
import LocalClassFieldTheory.Brauer.H2ZHat

/-!
# `H²(G, μ_Ẑ(G))` and `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` ([AbsTopIII], Corollary 1.10 (a), MR9 L1)

[AbsTopIII], Corollary 1.10 (i) (`Topics in Absolute Anabelian Geometry III.txt`, l.2369–2372 and
l.2392–2395):

> "(i) There exists a functorial "group-theoretic" algorithm for reconstructing the natural
> isomorphism `H²(G_k, μ_Ẑ(G_k)) ∼→ Ẑ` [cf. (a) below] […]"
> "Then one constructs the natural isomorphism `H²(G_k, μ_Ẑ(G_k)) ∼→ Ẑ` "group-theoretically"
> from `G_k` via the algorithm described in the proof of [Mzk9], Proposition 1.2.1, (vii)."

For a compact topological group `G`, with `μ_n(G) ⊆ μ_{ℚ/ℤ}(G)` the `G`-module of `Cor110.lean`:

* `H2MuG G n = H²(G, μ_n(G))` (`ContH2`, continuous cochains), `h2PowG` the maps induced by
  `μ_m(G) → μ_n(G)`, `z ↦ z^{m/n}`, and **`H2ZHatG G = H²(G, μ_Ẑ(G)) = lim_n H²(G, μ_n(G))`**
  (the inverse-limit convention of `Brauer.H2ZHatOne`, i.e. `μ_Ẑ(G) = lim_n μ_n(G)`, which is
  `Hom(ℚ/ℤ, μ_{ℚ/ℤ}(G))`);
* **functoriality**: every `ψ : G ≃ₜ* G'` induces
  `H2ZHatGEquivOf ψ : H²(G, μ_Ẑ(G)) ≃* H²(G', μ_Ẑ(G'))` (`h2Congr`, transport of `ContH2`
  along an isomorphism of groups and an equivariant isomorphism of coefficients);
* for `G = G_k`, `k/ℚ_p` finite: the `G_k`-equivariant `μ_n(G_k) ≅ μ_n(Ω)` (`muNEquiv`) gives
  `H²(G_k, μ_n(G_k)) ≅ H²(G_k, μ_n(Ω))` compatibly with the transition maps, hence
  **`h2ZHatGEquiv p k Ω : H²(G_k, μ_Ẑ(G_k)) ≃* Ẑ`** (the inverse limit of the cyclotomic rigidity
  isomorphisms `PadicField.h2MuEquiv`, `PadicField.h2ZHatOneEquiv`), with `h2ZHatGEquiv_apply`
  computing it levelwise.

Not formalised here: that `h2ZHatGEquiv` commutes with `H2ZHatGEquivOf ψ` for an arbitrary
`ψ : G_k ≃ₜ* G_{k'}` (the "group-theoretic" characterisation of the invariant map of [Mzk9],
Proposition 1.2.1 (vii), which uses the cup product with the Kummer classes of (b)), and the
index normalisation of Remark 1.10.1 (iii) (l.2558–2561) on the group side (on the field side it
is `PadicField.h2ZHatOneEquiv_res`).
-/

namespace Iut.Reconstruction

open PadicField IntermediateField MonoidHom KummerTheory Brauer ContH2

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Transport of `H²` -/

section Congr

variable {G G' M M' : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
  [MulDistribMulAction G M] [Group G'] [TopologicalSpace G'] [CommGroup M']
  [MulDistribMulAction G' M']

/-- **Transport of `H²`** along an isomorphism `e : G ≃ₜ* G'` of topological groups and an
`e`-equivariant isomorphism `ψ : M ≃* M'` of coefficients. -/
def h2Congr (e : G ≃ₜ* G') (ψ : M ≃* M') (h : ∀ (g : G) (m : M), ψ (g • m) = e g • ψ m) :
    ContH2 G M ≃* ContH2 G' M' where
  toFun := ContH2.map e.symm.toMulEquiv.toMonoidHom e.symm.continuous ψ.toMonoidHom
    (fun g m => by
      change ψ (e.symm g • m) = g • ψ m
      rw [h, ContinuousMulEquiv.apply_symm_apply])
  invFun := ContH2.map e.toMulEquiv.toMonoidHom e.continuous ψ.symm.toMonoidHom
    (fun g m => by
      change ψ.symm (e g • m) = g • ψ.symm m
      apply ψ.injective
      rw [MulEquiv.apply_symm_apply, h, MulEquiv.apply_symm_apply])
  left_inv x := by
    induction x using ContH2.induction_on with | h f => ?_
    simp only [map_mk]
    congr 1
    exact cocycles_ext fun a b => by
      simp only [cocyclesMap_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact congrArg f (Prod.ext (e.symm_apply_apply a) (e.symm_apply_apply b))
  right_inv x := by
    induction x using ContH2.induction_on with | h f => ?_
    simp only [map_mk]
    congr 1
    exact cocycles_ext fun a b => by
      simp only [cocyclesMap_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact congrArg f (Prod.ext (e.apply_symm_apply a) (e.apply_symm_apply b))
  map_mul' := map_mul _

theorem h2Congr_mk (e : G ≃ₜ* G') (ψ : M ≃* M') (h : ∀ (g : G) (m : M), ψ (g • m) = e g • ψ m)
    (f : cocycles G M) (a b : G') :
    ∃ f' : cocycles G' M', h2Congr e ψ h (mk f) = mk f' ∧ f' (a, b) = ψ (f (e.symm a, e.symm b)) :=
  ⟨_, rfl, rfl⟩

end Congr

/-! ### Inverse limits over `ℕ+` -/

section Limit

variable {A B : ℕ+ → Type*} [∀ n, Group (A n)] [∀ n, Group (B n)]

/-- The inverse limit `lim_n A n ⊆ ∏_n A n` along transition maps `A m → A n` (`n ∣ m`). -/
def limSub (t : ∀ {n m : ℕ+}, (n : ℕ) ∣ m → A m →* A n) : Subgroup (∀ n, A n) where
  carrier := {x | ∀ n m : ℕ+, ∀ h : (n : ℕ) ∣ m, t h (x m) = x n}
  mul_mem' hx hy n m h := by simp [hx n m h, hy n m h]
  one_mem' n m h := by simp
  inv_mem' hx n m h := by simp [hx n m h]

/-- Compatible isomorphisms induce an isomorphism of inverse limits. -/
def limSubEquiv {tA : ∀ {n m : ℕ+}, (n : ℕ) ∣ m → A m →* A n}
    {tB : ∀ {n m : ℕ+}, (n : ℕ) ∣ m → B m →* B n} (e : ∀ n, A n ≃* B n)
    (he : ∀ (n m : ℕ+) (h : (n : ℕ) ∣ m) (x : A m), tB h (e m x) = e n (tA h x)) :
    limSub tA ≃* limSub tB where
  toFun x := ⟨fun n => e n (x.1 n), fun n m h => by rw [he, x.2 n m h]⟩
  invFun y := ⟨fun n => (e n).symm (y.1 n), fun n m h => by
    apply (e n).injective
    rw [← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, y.2 n m h]⟩
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply _)
  right_inv y := Subtype.ext (funext fun n => (e n).apply_symm_apply _)
  map_mul' x y := Subtype.ext (funext fun n => map_mul (e n) _ _)

theorem limSubEquiv_apply {tA : ∀ {n m : ℕ+}, (n : ℕ) ∣ m → A m →* A n}
    {tB : ∀ {n m : ℕ+}, (n : ℕ) ∣ m → B m →* B n} (e : ∀ n, A n ≃* B n)
    (he : ∀ (n m : ℕ+) (h : (n : ℕ) ∣ m) (x : A m), tB h (e m x) = e n (tA h x))
    (x : limSub tA) (n : ℕ+) : (limSubEquiv e he x).1 n = e n (x.1 n) := rfl

end Limit

/-! ### The group-theoretic `H²(G, μ_Ẑ(G))` -/

section GroupTheoretic

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `H²(G, μ_n(G))`. -/
abbrev H2MuG (n : ℕ) : Type _ := ContH2 G (muN G n)

/-- The map `μ_m(G) → μ_n(G)`, `z ↦ z^{m/n}`, for `n ∣ m`. -/
def muNPow {n m : ℕ} (h : n ∣ m) : muN G m →* muN G n where
  toFun z := ⟨(z : AbBar G) ^ (m / n), by
    rw [mem_muN, ← pow_mul, Nat.div_mul_cancel h, mem_muN.1 z.2]⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' z w := Subtype.ext (mul_pow (z : AbBar G) w _)

theorem coe_muNPow {n m : ℕ} (h : n ∣ m) (z : muN G m) :
    (muNPow G h z : AbBar G) = (z : AbBar G) ^ (m / n) := rfl

theorem muNPow_smul {n m : ℕ} (h : n ∣ m) (g : G) (z : muN G m) :
    muNPow G h (g • z) = g • muNPow G h z :=
  Subtype.ext (map_pow (barConj G g) (z : AbBar G) _).symm

/-- `H²(G, μ_m(G)) → H²(G, μ_n(G))` induced by `z ↦ z^{m/n}`. -/
def h2PowG {n m : ℕ} (h : n ∣ m) : H2MuG G m →* H2MuG G n :=
  ContH2.map (MonoidHom.id G) continuous_id (muNPow G h) (fun g z => muNPow_smul G h g z)

/-- **`H²(G, μ_Ẑ(G)) = lim_n H²(G, μ_n(G))`.** -/
def H2ZHatG : Subgroup (∀ n : ℕ+, H2MuG G n) :=
  limSub (A := fun n : ℕ+ => H2MuG G n) fun h => h2PowG G h

end GroupTheoretic

section Functorial

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']

/-- `H²(G, μ_n(G)) ≃* H²(G', μ_n(G'))` induced by `ψ : G ≃ₜ* G'`. -/
def h2MuGEquivOf (ψ : G ≃ₜ* G') (n : ℕ) : H2MuG G n ≃* H2MuG G' n :=
  h2Congr ψ (muNEquivOf ψ n) (fun g z => muNEquivOf_smul ψ g z)

theorem h2PowG_h2MuGEquivOf (ψ : G ≃ₜ* G') {n m : ℕ} (h : n ∣ m) (x : H2MuG G m) :
    h2PowG G' h (h2MuGEquivOf ψ m x) = h2MuGEquivOf ψ n (h2PowG G h x) := by
  induction x using ContH2.induction_on with | h f => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  exact cocycles_ext fun a b => Subtype.ext (map_pow (barMap ψ) _ _).symm

/-- **`H²(G, μ_Ẑ(G))` is group-theoretic**: `ψ : G ≃ₜ* G'` induces
`H²(G, μ_Ẑ(G)) ≃* H²(G', μ_Ẑ(G'))`. -/
def H2ZHatGEquivOf (ψ : G ≃ₜ* G') : H2ZHatG G ≃* H2ZHatG G' :=
  limSubEquiv (fun n => h2MuGEquivOf ψ n) fun _ _ h x => h2PowG_h2MuGEquivOf ψ h x

end Functorial

/-! ### `G = G_k`: `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p k Ω) in
/-- **`H²(G_k, μ_n(G_k)) ≅ H²(G_k, μ_n(Ω))`** via the equivariant `μ_n(G_k) ≅ μ_n(Ω)`. -/
def h2MuGEquiv (n : ℕ) [NeZero n] : H2MuG (Ω ≃ₐ[k] Ω) n ≃* H2Mu k Ω n :=
  h2Congr (ContinuousMulEquiv.refl _) (muNEquiv p k Ω n) (fun g z => muNEquiv_smul n g z)

theorem muNEquiv_muNPow {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m)
    (z : muN (Ω ≃ₐ[k] Ω) m) :
    muPow h (muNEquiv p k Ω m z) = muNEquiv p k Ω n (muNPow _ h z) := by
  apply Mu.ext
  rw [val_muPow, val_muNEquiv, val_muNEquiv]
  have hz : (⟨(muNPow _ h z : AbBar (Ω ≃ₐ[k] Ω)), muN_le_muQZ _ n (muNPow _ h z).2⟩ :
      muQZ (Ω ≃ₐ[k] Ω)) = ⟨z, muN_le_muQZ _ m z.2⟩ ^ (m / n) := rfl
  rw [hz, map_pow]

theorem h2MuPow_h2MuGEquiv {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m)
    (x : H2MuG (Ω ≃ₐ[k] Ω) m) :
    h2MuPow h (h2MuGEquiv p k Ω m x) = h2MuGEquiv p k Ω n (h2PowG _ h x) := by
  induction x using ContH2.induction_on with | h f => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  exact cocycles_ext fun a b => muNEquiv_muNPow h _

variable (p k Ω) in
/-- `H²(G_k, μ_Ẑ(G_k)) ≅ H²(k, Ẑ(1))`. -/
def h2ZHatGEquivOne : H2ZHatG (Ω ≃ₐ[k] Ω) ≃* H2ZHatOne k Ω :=
  limSubEquiv (B := fun n : ℕ+ => H2Mu k Ω n) (tB := fun h => h2MuPow h)
    (fun n => h2MuGEquiv p k Ω n) fun _ _ h x => h2MuPow_h2MuGEquiv h x

variable (p k Ω) in
/-- **[AbsTopIII], Corollary 1.10 (a)**: `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ`, for the group-theoretic
cyclotome `μ_Ẑ(G_k)` built from the transfer, via the cyclotomic rigidity isomorphisms
`H²(G_k, μ_n) ≅ ℤ/n` of local class field theory. -/
def h2ZHatGEquiv : H2ZHatG (Ω ≃ₐ[k] Ω) ≃* Multiplicative ZHat :=
  (h2ZHatGEquivOne p k Ω).trans (h2ZHatOneEquiv p k Ω)

/-- `h2ZHatGEquiv` levelwise: the `n`-th component is the invariant of the class in
`H²(G_k, μ_n(G_k)) ≅ H²(G_k, μ_n(Ω))`. -/
theorem h2ZHatGEquiv_apply (x : H2ZHatG (Ω ≃ₐ[k] Ω)) (n : ℕ+) :
    ((Multiplicative.toAdd (h2ZHatGEquiv p k Ω x) : ZHat) : ∀ n : ℕ+, ZMod n) n =
      Multiplicative.toAdd (h2MuEquiv p k Ω n.pos (h2MuGEquiv p k Ω n (x.1 n))) :=
  h2ZHatOneEquiv_apply _ n

end Galois

end

end Iut.Reconstruction
