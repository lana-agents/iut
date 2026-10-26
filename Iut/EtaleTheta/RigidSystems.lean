/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.DiscreteRigidity
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

/-!
# Discrete rigidity of projective systems ([EtTh], Cor. 2.19(ii), Cor. 2.18(iv))

[EtTh], Cor. 2.19(ii): every projective system `⋯ → M•_{M'} → M•_M → ⋯` (`M ∈ E`) of mod `M`
mono-theta environments is isomorphic to the natural projective system of model environments.
Mochizuki deduces it from Cor. 2.18(iv): the homomorphisms `Aut^μ(M_N) → Aut(Π_X)` are
surjective with kernel `Hom(Π_Y/Π_Ÿ, μ_N) ≅ Hom(ℤ/2, ℤ/N)` (finite), compatibly in `N` — "the
`R¹ lim`'s of `{Hom(ℤ/2, ℤ/N)}` and `{μ_N}` vanish".

This file proves the formal part of this deduction:

* `exists_compatible_seq`: König's lemma for sequences of finite nonempty sets.
* `exists_untwist` (**`lim¹` vanishes**): for a tower of groups `G_n` with transition maps
  `r_n : G_{n+1} → G_n` and compatible surjections `p_n : G_n ↠ H` onto a fixed group, with
  finite kernels, every twisted system is trivial: for every `(g_n)` there is `(α_n)` with
  `α_n g_n = r_n(α_{n+1})`.
* `Tower`, `Tower.System`, **`Tower.discreteRigidity`**: in a tower of categories `C_n` (mod `e_n`
  environments) with restriction functors and model objects `M_n`, if the induced maps on
  automorphism groups have such compatible surjections `Aut(M_n) ↠ H` with finite kernels
  (the content of [EtTh], Cor. 2.18(iv), with `H = Aut(Π_X)`), then every projective system
  levelwise isomorphic to the models is isomorphic to the model system.
* `Tower.discreteRigidity_of_surjective`: the case of surjective restriction maps (e.g. `N/M`
  odd in Cor. 2.18(iv); [EtTh], Prop. 2.15(ii) is the case `Aut = ℤ` with identity transitions,
  `DiscreteRigidity.iso_of_level_one`).

The finiteness of the kernels is essential: for the bi-theta environments the kernels are
infinite (`N·l·ℤ`, Prop. 2.14(iii)) and rigidity fails (`DiscreteRigidity.exists_not_iso`).
Cor. 2.18(iv) itself — the computation of `Aut^μ` of the environments built from `Π^tp_Y[μ_N]`
— is not formalized (see `README.md`).
-/

namespace Iut.EtaleTheta.RigidSystems

open CategoryTheory

universe u v w

/-- **König's lemma for sequences**: a sequence of maps `X_{n+1} → X_n` between finite nonempty
sets has a compatible family of elements. -/
theorem exists_compatible_seq {X : ℕ → Type v} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (f : ∀ n, X (n + 1) → X n) : ∃ x : ∀ n, X n, ∀ n, f n (x (n + 1)) = x n := by
  let F : ℕᵒᵖ ⥤ Type v := Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (X j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (X j.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => s (Opposite.op n), fun n => ?_⟩
  have := hs (homOfLE (Nat.le_add_right n 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at this
  exact this

/-- **Vanishing of `lim¹`** for a tower of groups `G_n` with compatible surjections onto a fixed
group `H` and finite kernels: every twisted system `(g_n)` is trivialized by some `(α_n)`,
`α_n g_n = r_n(α_{n+1})`. -/
theorem exists_untwist {G : ℕ → Type w} [∀ n, Group (G n)] {H : Type*} [Group H]
    (r : ∀ n, G (n + 1) →* G n) (p : ∀ n, G n →* H) (hp : ∀ n, Function.Surjective (p n))
    (hpr : ∀ n, (p n).comp (r n) = p (n + 1)) (hK : ∀ n, Finite (p n).ker) (g : ∀ n, G n) :
    ∃ α : ∀ n, G n, ∀ n, α n * g n = r n (α (n + 1)) := by
  have hpr' : ∀ n x, p n (r n x) = p (n + 1) x := fun n x => DFunLike.congr_fun (hpr n) x
  -- Step 1: solve the problem in `H`.
  let h : ℕ → H := fun n => Nat.rec 1 (fun k hk => hk * p k (g k)) n
  have hh : ∀ n, h (n + 1) = h n * p n (g n) := fun _ => rfl
  -- Step 2: lift.
  let α' : ∀ n, G n := fun n => (hp n (h n)).choose
  have hα' : ∀ n, p n (α' n) = h n := fun n => (hp n (h n)).choose_spec
  -- Step 3: the defect lies in the kernels.
  let c : ∀ n, G n := fun n => r n (α' (n + 1))
  let δ : ∀ n, G n := fun n => (c n)⁻¹ * α' n * g n
  have hδ : ∀ n, δ n ∈ (p n).ker := by
    intro n
    simp only [δ, c, MonoidHom.mem_ker, map_mul, map_inv, hpr', hα', hh]
    group
  have hcδ : ∀ n, α' n * g n = c n * δ n := by
    intro n
    simp only [δ]
    group
  -- Step 4: correct by a compatible family in the finite kernels (König).
  let f : ∀ n, (p (n + 1)).ker → (p n).ker := fun n κ =>
    ⟨r n κ * (c n * (δ n)⁻¹ * (c n)⁻¹), by
      refine (p n).ker.mul_mem ?_ ((p n).normal_ker.conj_mem _ ((p n).ker.inv_mem (hδ n)) _)
      rw [MonoidHom.mem_ker, hpr']
      exact κ.2⟩
  haveI : ∀ n, Nonempty (p n).ker := fun _ => ⟨1⟩
  obtain ⟨κ, hκ⟩ := exists_compatible_seq (X := fun n => (p n).ker) f
  refine ⟨fun n => (κ n : G n) * α' n, fun n => ?_⟩
  rw [mul_assoc, hcδ, ← hκ n, map_mul]
  simp only [f]
  change r n (κ (n + 1)) * (c n * (δ n)⁻¹ * (c n)⁻¹) * (c n * δ n) = r n (κ (n + 1)) * c n
  group

/-! ### Towers of categories and their projective systems -/

set_option linter.checkUnivs false in
/-- **A tower of categories with model objects**: categories `C_n` (e.g. mod `e_n` mono-theta
environments), restriction functors `res_n : C_{n+1} ⥤ C_n` (e.g. `M ↦ M_{e_n}`) and model objects
`M_n` with isomorphisms `β_n : res_n(M_{n+1}) ≅ M_n` (the natural projective system). -/
structure Tower where
  /-- The categories. -/
  C : ℕ → Type u
  [cat : ∀ n, Category.{v} (C n)]
  /-- The restriction functors. -/
  res : ∀ n, C (n + 1) ⥤ C n
  /-- The model objects. -/
  model : ∀ n, C n
  /-- The transition isomorphisms of the model system. -/
  β : ∀ n, (res n).obj (model (n + 1)) ≅ model n

attribute [instance] Tower.cat

namespace Tower

variable (T : Tower.{u, v})

/-- **A projective system** in the tower: objects `X_n` with `γ_n : res_n(X_{n+1}) ≅ X_n`. -/
structure System where
  /-- The objects. -/
  X : ∀ n, T.C n
  /-- The transition isomorphisms. -/
  γ : ∀ n, (T.res n).obj (X (n + 1)) ≅ X n

/-- A projective system is **isomorphic to the model system** if there are isomorphisms
`α_n : X_n ≅ M_n` compatible with the transition isomorphisms. -/
def System.IsoModel {T : Tower.{u, v}} (S : T.System) : Prop :=
  ∃ α : ∀ n, S.X n ≅ T.model n,
    ∀ n, (T.res n).map (α (n + 1)).hom ≫ (T.β n).hom = (S.γ n).hom ≫ (α n).hom

/-- The restriction `Aut(M_{n+1}) → Aut(M_n)`, `a ↦ β_n⁻¹ ∘ res_n(a) ∘ β_n`. -/
def autRes (n : ℕ) : Aut (T.model (n + 1)) →* Aut (T.model n) where
  toFun a := (T.β n).symm ≪≫ (T.res n).mapIso a ≪≫ T.β n
  map_one' := by
    ext
    change (T.β n).inv ≫ (T.res n).map (𝟙 _) ≫ (T.β n).hom = 𝟙 _
    simp
  map_mul' a b := by
    ext
    simp [Aut.Aut_mul_def]

lemma autRes_hom (n : ℕ) (a : Aut (T.model (n + 1))) :
    (T.res n).map a.hom ≫ (T.β n).hom = (T.β n).hom ≫ (T.autRes n a).hom := by
  simp [autRes]

/-- **Discrete rigidity** ([EtTh], Cor. 2.19(ii) from Cor. 2.18(iv)): if the automorphism
groups of the models have compatible surjections onto a fixed group `H` with finite kernels,
every projective system that is levelwise isomorphic to the models is isomorphic to the model
system. -/
theorem discreteRigidity {H : Type*} [Group H] (p : ∀ n, Aut (T.model n) →* H)
    (hp : ∀ n, Function.Surjective (p n)) (hpr : ∀ n, (p n).comp (T.autRes n) = p (n + 1))
    (hK : ∀ n, Finite (p n).ker) (S : T.System) (hS : ∀ n, Nonempty (S.X n ≅ T.model n)) :
    S.IsoModel := by
  let θ : ∀ n, S.X n ≅ T.model n := fun n => (hS n).some
  -- the defect `t_n = β⁻¹ ∘ res(θ_{n+1})⁻¹ ∘ γ_n ∘ θ_n ∈ Aut(M_n)`
  let t : ∀ n, Aut (T.model n) := fun n =>
    (T.β n).symm ≪≫ (T.res n).mapIso (θ (n + 1)).symm ≪≫ S.γ n ≪≫ θ n
  obtain ⟨a, ha⟩ := exists_untwist T.autRes p hp hpr hK t
  refine ⟨fun n => θ n ≪≫ a n, fun n => ?_⟩
  have h : (T.autRes n (a (n + 1))).hom = (t n).hom ≫ (a n).hom := by
    rw [← ha n, Aut.Aut_mul_def, Iso.trans_hom]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, autRes_hom, h]
  simp [t]

/-- **Discrete rigidity for surjective restriction maps** (e.g. `N/M` odd in [EtTh],
Cor. 2.18(iv)). -/
theorem discreteRigidity_of_surjective (hsurj : ∀ n, Function.Surjective (T.autRes n))
    (S : T.System) (hS : ∀ n, Nonempty (S.X n ≅ T.model n)) : S.IsoModel := by
  let θ : ∀ n, S.X n ≅ T.model n := fun n => (hS n).some
  let t : ∀ n, Aut (T.model n) := fun n =>
    (T.β n).symm ≪≫ (T.res n).mapIso (θ (n + 1)).symm ≪≫ S.γ n ≪≫ θ n
  let a : ∀ n, Aut (T.model n) := fun n =>
    Nat.rec 1 (fun k ak => (hsurj k (ak * t k)).choose) n
  have ha : ∀ n, a n * t n = T.autRes n (a (n + 1)) := fun n =>
    ((hsurj n (a n * t n)).choose_spec).symm
  refine ⟨fun n => θ n ≪≫ a n, fun n => ?_⟩
  have h : (T.autRes n (a (n + 1))).hom = (t n).hom ≫ (a n).hom := by
    rw [← ha n, Aut.Aut_mul_def, Iso.trans_hom]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, autRes_hom, h]
  simp [t]

end Tower

end Iut.EtaleTheta.RigidSystems
