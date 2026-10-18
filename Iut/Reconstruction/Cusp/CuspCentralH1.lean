/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.CuspCentral
import LocalClassFieldTheory.Cohomology.FiveTerm

/-!
# `H¹` of the maximal cuspidally central and abelian quotients ([Cusp], Proposition 2.1(i))

[Cusp] = "Absolute Anabelian Cuspidalizations of Proper Hyperbolic Curves", Proposition 2.1(i)
(l.1834–1860 of `~/iut-scratch/papers/txt/Absolute Anabelian Cuspidalizations.txt`):
"The natural surjections induce isomorphisms as follows:
`H¹(Π^{c-cn}_{U_S}, M_X) ≅ H¹(Π^{c-ab}_{U_S}, M_X) ≅ H¹(Π_{U_S}, M_X)`", with the proof "follows
immediately from the definitions". This is the step of [AbsTopIII], Proposition 1.6 / Theorem
1.9(c) that lets one compute Kummer classes of functions on the cuspidally central (or abelian)
quotient.

Group-theoretically: let `Π` be a topological group, `Δ ⊆ Π` a subgroup acting trivially on a
discrete `Π`-module `A` (for `Δ = Δ_{U_S}` and `A = M_X`, the geometric fundamental group acts
trivially on the cyclotome), and `N ⊴ Π` contained in the closure of `⁅Δ, Δ⁆`. Then a continuous
`1`-cocycle of `Π` is a homomorphism on `Δ`, hence vanishes on `cl⁅Δ, Δ⁆ ⊇ N`, so

* `res₁_eq_one_of_le_closure_commutator`: `H¹(Π, A) → H¹(N, A)` is trivial, and
* **`inf₁_bijective_of_le_closure_commutator`**: inflation `H¹(Π/N, A^N) → H¹(Π, A)` is bijective
  (LCFT `FiveTerm.inf₁_injective`, `exists_inf₁_eq_of_res₁_eq_one`).

For a normal `K ≤ Δ` (the kernel of `Δ_{U_S} ↠ Δ_X`), both `N = cl⁅K, Δ⁆` (the kernel of the
maximal cuspidally central quotient) and `N = cl⁅K, K⁆` (the maximal cuspidally abelian one)
qualify: `inf₁_bijective_cuspCentral`, `inf₁_bijective_cuspAbelian`.
-/

namespace Iut.Reconstruction

open FiveTerm

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [MulDistribMulAction P A]

/-- A continuous `1`-cocycle on `Π`, restricted to a subgroup `Δ` acting trivially, is a
homomorphism; it kills `cl⁅Δ, Δ⁆`. -/
theorem cocycle_eq_one_of_mem_closure_commutator (Δ : Subgroup P)
    (htriv : ∀ δ ∈ Δ, ∀ a : A, δ • a = a) (c : ContH1.cocycles P A) {p : P}
    (hp : p ∈ (⁅Δ, Δ⁆ : Subgroup P).topologicalClosure) : c p = 1 := by
  have hc : ∀ a b : P, c (a * b) = a • c b * c a := c.2.2
  have hone : c 1 = 1 := by
    have h := hc 1 1
    rw [one_mul, one_smul] at h
    exact mul_left_cancel (a := c 1) (by rw [mul_one]; exact h.symm)
  have hmul : ∀ a ∈ Δ, ∀ b, c (a * b) = c b * c a := fun a ha b => by rw [hc, htriv a ha]
  have hinv : ∀ a ∈ Δ, c a⁻¹ = (c a)⁻¹ := fun a ha => by
    have h := hmul a ha a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let H : Subgroup P :=
    { carrier := {p | p ∈ Δ ∧ c p = 1}
      mul_mem' := fun {a b} ha hb => ⟨Δ.mul_mem ha.1 hb.1, by rw [hmul a ha.1, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Δ.one_mem, hone⟩
      inv_mem' := fun {a} ha => ⟨Δ.inv_mem ha.1, by rw [hinv a ha.1, ha.2, inv_one]⟩ }
  have hle : (⁅Δ, Δ⁆ : Subgroup P) ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨by
      rw [commutatorElement_def]
      exact Δ.mul_mem (Δ.mul_mem (Δ.mul_mem ha hb) (Δ.inv_mem ha)) (Δ.inv_mem hb), ?_⟩
    rw [commutatorElement_def, hmul _ (Δ.mul_mem (Δ.mul_mem ha hb) (Δ.inv_mem ha)),
      hmul _ (Δ.mul_mem ha hb), hmul a ha, hinv a ha, hinv b hb]
    mul_abel
  have hZ : IsClosed {p : P | c p = 1} :=
    isClosed_singleton.preimage c.2.1
  have hcl : ((⁅Δ, Δ⁆ : Subgroup P).topologicalClosure : Set P) ⊆ {p : P | c p = 1} :=
    closure_minimal (fun x hx => (hle hx).2) hZ
  exact hcl hp

variable (Δ N : Subgroup P) [N.Normal]

omit [N.Normal] in
/-- **The restriction `H¹(Π, A) → H¹(N, A)` is trivial** for `N ⊆ cl⁅Δ, Δ⁆`. -/
theorem res₁_eq_one_of_le_closure_commutator (htriv : ∀ δ ∈ Δ, ∀ a : A, δ • a = a)
    (hN : N ≤ (⁅Δ, Δ⁆ : Subgroup P).topologicalClosure) (x : ContH1 P A) :
    res₁ N A x = 1 := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [res₁, ContH1.map_mk, ContH1.mk_eq_one_iff]
    refine ⟨1, fun n => ?_⟩
    change (n : P) • (1 : A) / 1 = c n
    rw [smul_one, div_one, cocycle_eq_one_of_mem_closure_commutator Δ htriv c (hN n.2)]

/-- **[Cusp], Proposition 2.1(i)**, group-theoretically: inflation
`H¹(Π/N, A^N) → H¹(Π, A)` is bijective for `N ⊆ cl⁅Δ, Δ⁆`, `Δ` acting trivially on `A`. -/
theorem inf₁_bijective_of_le_closure_commutator [ContinuousSMul P A]
    (htriv : ∀ δ ∈ Δ, ∀ a : A, δ • a = a)
    (hN : N ≤ (⁅Δ, Δ⁆ : Subgroup P).topologicalClosure) :
    Function.Bijective (inf₁ N A) :=
  ⟨inf₁_injective, fun x =>
    exists_inf₁_eq_of_res₁_eq_one (res₁_eq_one_of_le_closure_commutator Δ N htriv hN x)⟩

variable {Δ} (K : Subgroup P)

/-- The cuspidally central case `N = cl⁅K, Δ⁆` (`K ≤ Δ`). -/
theorem inf₁_bijective_cuspCentral [ContinuousSMul P A]
    [(⁅K, Δ⁆ : Subgroup P).topologicalClosure.Normal]
    (htriv : ∀ δ ∈ Δ, ∀ a : A, δ • a = a) (hK : K ≤ Δ) :
    Function.Bijective (inf₁ (⁅K, Δ⁆ : Subgroup P).topologicalClosure A) :=
  inf₁_bijective_of_le_closure_commutator Δ _ htriv
    (Subgroup.topologicalClosure_mono (Subgroup.commutator_mono hK le_rfl))

/-- The cuspidally abelian case `N = cl⁅K, K⁆` (`K ≤ Δ`). -/
theorem inf₁_bijective_cuspAbelian [ContinuousSMul P A]
    [(⁅K, K⁆ : Subgroup P).topologicalClosure.Normal]
    (htriv : ∀ δ ∈ Δ, ∀ a : A, δ • a = a) (hK : K ≤ Δ) :
    Function.Bijective (inf₁ (⁅K, K⁆ : Subgroup P).topologicalClosure A) :=
  inf₁_bijective_of_le_closure_commutator Δ _ htriv
    (Subgroup.topologicalClosure_mono (Subgroup.commutator_mono hK hK))

end Iut.Reconstruction
