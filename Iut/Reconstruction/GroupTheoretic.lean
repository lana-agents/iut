/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Group-theoretic invariants of topological groups (roadmap P17, M0)

A field invariant is *reconstructed group-theoretically* ([AbsTopIII], Remark 1.9.8; IUT I,
Remark 1.9.2) if it is a function of the absolute Galois group regarded as an abstract
topological group. Formally: a function of topological groups that is invariant under
isomorphisms of topological groups (`≃ₜ*`).

The basic invariant used for `p`-adic fields is the number of continuous characters of
order dividing `n`,

`charCount G n = #{χ : G →* ℤ/n | IsLocallyConstant χ}`

(`IsLocallyConstant` = continuity for the discrete topology on `ℤ/n`). By local Tate duality it
equals `[Kˣ : (Kˣ)ⁿ]` for `G = Gal(K̄/K)` (`Iut.Reconstruction.charCount_gal`).

## Main definitions and results

* `Iut.Reconstruction.ContChar G n`, `Iut.Reconstruction.charCount G n`;
* `Iut.Reconstruction.charEquiv`, `Iut.Reconstruction.charCount_congr`: invariance under
  isomorphisms of topological groups.
-/

namespace Iut.Reconstruction

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Continuous (`IsLocallyConstant`) characters `G → ℤ/n`, written multiplicatively. -/
def ContChar (n : ℕ) : Type u :=
  {χ : G →* Multiplicative (ZMod n) // IsLocallyConstant χ}

/-- **The character count** `#Hom_cont(G, ℤ/n)` of a topological group (`0` if infinite). -/
noncomputable def charCount (n : ℕ) : ℕ := Nat.card (ContChar G n)

variable {G} {H : Type v} [Group H] [TopologicalSpace H]

/-- Transport of characters along an isomorphism of topological groups. -/
def charEquiv (φ : G ≃ₜ* H) (n : ℕ) : ContChar G n ≃ ContChar H n where
  toFun χ := ⟨χ.1.comp φ.symm.toMulEquiv.toMonoidHom, χ.2.comp_continuous φ.symm.continuous⟩
  invFun χ := ⟨χ.1.comp φ.toMulEquiv.toMonoidHom, χ.2.comp_continuous φ.continuous⟩
  left_inv χ := by
    apply Subtype.ext
    ext g
    change χ.1 (φ.symm (φ g)) = χ.1 g
    rw [φ.symm_apply_apply]
  right_inv χ := by
    apply Subtype.ext
    ext g
    change χ.1 (φ (φ.symm g)) = χ.1 g
    rw [φ.apply_symm_apply]

/-- **Invariance**: the character count is a group-theoretic invariant. -/
theorem charCount_congr (φ : G ≃ₜ* H) (n : ℕ) : charCount G n = charCount H n :=
  Nat.card_congr (charEquiv φ n)

/-- A function of topological groups (in a fixed universe) is **group-theoretic** if it is
invariant under isomorphisms of topological groups. -/
def IsGroupTheoretic {α : Sort*}
    (F : ∀ (G : Type u) [Group G] [TopologicalSpace G], α) : Prop :=
  ∀ (G H : Type u) [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H],
    (G ≃ₜ* H) → F G = F H

theorem isGroupTheoretic_charCount (n : ℕ) :
    IsGroupTheoretic.{u} fun G _ _ => charCount G n :=
  fun _ _ _ _ _ _ φ => charCount_congr φ n

/-- Functions of group-theoretic data are group-theoretic. -/
theorem IsGroupTheoretic.comp {α β : Sort*}
    {F : ∀ (G : Type u) [Group G] [TopologicalSpace G], α}
    (hF : IsGroupTheoretic F) (g : α → β) :
    IsGroupTheoretic fun G _ _ => g (F G) :=
  fun G H _ _ _ _ φ => by
    simp only
    rw [hF G H φ]

/-- The whole character-count function `n ↦ charCount G n` is group-theoretic. -/
theorem isGroupTheoretic_charCountFun :
    IsGroupTheoretic.{u} fun G _ _ => fun n => charCount G n :=
  fun _ _ _ _ _ _ φ => funext fun n => charCount_congr φ n

end Iut.Reconstruction
