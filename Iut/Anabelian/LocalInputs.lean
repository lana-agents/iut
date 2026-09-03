/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.TateTorsion
import Iut.Anabelian.Torsion
import Iut.Cor312.ThetaData.TateFamily

/-!
# The reduction-theoretic inputs at the bad places (taxis #1529)

For admissible prime data `P` with torsion field `K` and a Tate family `TF` (the Tate
uniformizations of `E` over the completions `K_w` at the places over `V_mod^bad`), the
facts about the ℓ-torsion of `E` over `K_w` needed by the existence of local theta data
follow from the rationality of the ℓ-torsion over `K` (`E(K)[ℓ]` has `ℓ²` elements,
`Iut.AdmissiblePrimeData.card_TK`) and the computation of the ℓ-torsion of a Tate curve
(`Iut.Anabelian.TateTorsion`):

* `TateFamily.torsion_surj`: every ℓ-torsion point of `E(K_w)` is rational over `K`;
* `TateFamily.map_graphLineAt`, `card_graphLineAt`, `graphLineAt_le_TK`: the graph line at
  `w`, pulled back to `E(K)`, is a subgroup of `E(K)[ℓ]` of order `ℓ` mapping onto the
  graph line of the Tate structure;
* `TateFamily.exists_canonical`: the canonical generators at `w` are the two cosets
  `±g + L_w` of a torsion point `g ∉ L_w`.
-/

namespace Iut.TateFamily

open WeierstrassCurve NumberField Iut Iut.Anabelian
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable (P : Iut.AdmissiblePrimeData F E Fbar VBad) [NumberField ↥P.torsionField]

attribute [local instance 1100] Iut.AdmissiblePrimeData.instDecidableEqK

/-- `ℓ` is prime. -/
local instance instFactPrime : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩

local instance instNeZero : NeZero P.ℓ := ⟨P.ℓ_prime.ne_zero⟩

local instance instFactOneLt : Fact (1 < P.ℓ) := ⟨P.ℓ_prime.one_lt⟩

variable (TF : TateFamily E P.torsionField P.ℓ VBad)

/-- The map `E(K) → E(K_w)`. -/
abbrev toLocal (w : FinitePlace ↥P.torsionField) :
    P.EK.toAffine.Point →+ (curveKw E P.torsionField w).toAffine.Point :=
  pointMap P.EK (emb P.torsionField w)

variable {w : FinitePlace ↥P.torsionField} (hw : IsBadPlace E P.torsionField VBad w)

/-- `K`-rational ℓ-torsion maps to local ℓ-torsion. -/
lemma toLocal_mem_torsion {R : P.EK.toAffine.Point} (hR : R ∈ P.TK) :
    toLocal P w R ∈ TateStructure.torsion P.ℓ (curveKw E P.torsionField w) := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

lemma mem_TK_of_toLocal {R : P.EK.toAffine.Point}
    (hR : toLocal P w R ∈ TateStructure.torsion P.ℓ (curveKw E P.torsionField w)) : R ∈ P.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul] at hR
  exact pointMap_injective _ _ (hR.trans (map_zero _).symm)

/-- The image of `E(K)[ℓ]` in `E(K_w)`. -/
abbrev imageTK (w : FinitePlace ↥P.torsionField) :
    AddSubgroup (curveKw E P.torsionField w).toAffine.Point :=
  P.TK.map (toLocal P w)

lemma imageTK_le_torsion :
    imageTK P w ≤ TateStructure.torsion P.ℓ (curveKw E P.torsionField w) := by
  rintro _ ⟨R, hR, rfl⟩
  exact toLocal_mem_torsion P hR

lemma card_imageTK : Nat.card (imageTK P w) = P.ℓ * P.ℓ := by
  rw [← pow_two, ← P.card_TK]
  exact (Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ (pointMap_injective _ _)).toEquiv).symm

include TF hw

/-- `ℓ² ≤ |E(K_w)[ℓ]|`. -/
lemma sq_le_card_torsion :
    P.ℓ * P.ℓ ≤ Nat.card (TateStructure.torsion P.ℓ (curveKw E P.torsionField w)) := by
  haveI := (TF.S w hw).finite_torsion P.ℓ
  rw [← card_imageTK P]
  exact AddSubgroup.card_le_of_le (imageTK_le_torsion P)

/-- **The local ℓ-torsion is rational over `K`.** -/
theorem torsion_surj :
    imageTK P w = TateStructure.torsion P.ℓ (curveKw E P.torsionField w) := by
  haveI := (TF.S w hw).finite_torsion P.ℓ
  apply AddSubgroup.eq_of_le_of_card_ge (imageTK_le_torsion P)
  rw [card_imageTK]
  exact (TF.S w hw).card_torsion_le P.ℓ

lemma exists_toLocal_eq {Q : (curveKw E P.torsionField w).toAffine.Point}
    (hQ : Q ∈ TateStructure.torsion P.ℓ (curveKw E P.torsionField w)) :
    ∃ R ∈ P.TK, toLocal P w R = Q := by
  rw [← TF.torsion_surj P hw] at hQ
  exact hQ

/-- The graph line at `w` maps onto the graph line of the Tate structure. -/
theorem map_graphLineAt :
    (TF.graphLineAt w hw).map (toLocal P w) = (TF.S w hw).graphLine P.ℓ := by
  ext Q
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact hR
  · intro hQ
    obtain ⟨R, -, rfl⟩ := TF.exists_toLocal_eq P hw
      ((TF.S w hw).graphLine_le_torsion P.ℓ hQ)
    exact ⟨R, hQ, rfl⟩

/-- The graph line at `w` has `ℓ` elements. -/
theorem card_graphLineAt : Nat.card (TF.graphLineAt w hw) = P.ℓ := by
  have h1 : Nat.card (TF.graphLineAt w hw) =
      Nat.card ((TF.graphLineAt w hw).map (toLocal P w)) :=
    Nat.card_congr (AddSubgroup.equivMapOfInjective _ _ (pointMap_injective _ _)).toEquiv
  rw [h1, TF.map_graphLineAt P hw]
  exact (TF.S w hw).card_graphLine_eq P.ℓ (TF.sq_le_card_torsion P hw)

/-- The graph line at `w` consists of ℓ-torsion points. -/
theorem graphLineAt_le_TK : TF.graphLineAt w hw ≤ P.TK := fun R hR =>
  mem_TK_of_toLocal P ((TF.S w hw).graphLine_le_torsion P.ℓ hR)

/-- **The canonical generators at `w`** are the two cosets `±g + L_w` of an ℓ-torsion point
`g ∉ L_w`. -/
theorem exists_canonical :
    ∃ g ∈ P.TK, g ∉ TF.graphLineAt w hw ∧
      ∀ R, TF.IsCanonicalAt w hw R ↔
        (R - g ∈ TF.graphLineAt w hw ∨ R + g ∈ TF.graphLineAt w hw) := by
  obtain ⟨u₁, m₁, hu₁⟩ := (TF.S w hw).exists_root_class P.ℓ (TF.sq_le_card_torsion P hw)
  obtain ⟨g, hgT, hg⟩ := TF.exists_toLocal_eq P hw ((TF.S w hw).ofUnit_mem_torsion P.ℓ hu₁)
  refine ⟨g, hgT, ?_, fun R => ?_⟩
  · intro h
    apply (TF.S w hw).ofUnit_not_mem_graphLine P.ℓ hu₁
    rw [← hg]
    exact h
  · unfold IsCanonicalAt
    rw [(TF.S w hw).isCanonical_iff P.ℓ hu₁, ← hg]
    unfold graphLineAt
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, map_sub, map_add]

end

end Iut.TateFamily
