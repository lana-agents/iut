/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tower.RamIdx
import Iut.Tower.LogDK
import Iut.Tower.StepIII

/-!
# The tower arithmetic from the local facts

`Iut.towerArithmetic_of_localFacts`: the tower arithmetic `Iut.TowerArithmetic D LT TL`
of IUT IV, Theorem 1.10 ((R4), Steps (ii), (iii)) for initial Θ-data `D`, from

* the residual local facts `Iut.TowerLocalFacts` (IUT IV, Propositions 1.3 and 1.8:
  the different bound, Néron–Ogg–Shafarevich, the ramification bound away from `2·3·5·ℓ`)
  and the ramification bound `e(u/u₀) ≤ 2` of `F_tpd/F_mod` at the bad places
  (`Iut.RelRamIdxModLeTwo`; a theorem for the curves of the tripod,
  `Iut.Tripod.relRamIdx_tpd_le_two`);
* the Galois property of `F_tpd/F_mod` and the degree bounds `[F_tpd : F_mod] ≤ 6`,
  `[F : ℚ] ≤ 552960·[F_tpd : ℚ]` (for the curves of the tripod: `F_tpd = ℚ(λ)`,
  `F_mod = ℚ(j)`, `[ℚ(λ) : ℚ(j)] ≤ 6` by the sextic relation between `λ` and `j`,
  `[F_λ : ℚ(λ)] ≤ 2³·48·480`);
* the finiteness of the bad places of `F` and the description of the bad residue
  characteristics of the theta local data.

The three fields are `Iut.ramIdx_bound_of_facts`, `Iut.logDifferentDeg_torsionField_le`
(with `Iut.ThetaLocalData.sum_dst_logDK_eq`) and `Iut.sum_log_distinguished_le`.
-/

namespace Iut

open NumberField

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)

/-- **The tower arithmetic from the local facts** (IUT IV, (R4), Steps (ii), (iii)). -/
theorem towerArithmetic_of_localFacts (H : TowerLocalFacts D.E D.VBad D.prime)
    (he2 : RelRamIdxModLeTwo D.E D.VBad)
    [IsGalois ↥(fieldOfModuli D.F D.E) ↥(tripodalFieldOf D.F D.E)]
    (h6 : Module.finrank ↥(fieldOfModuli D.F D.E) ↥(tripodalFieldOf D.F D.E) ≤ 6)
    (hF : Module.finrank ℚ D.F ≤ 552960 * Module.finrank ℚ ↥(tripodalFieldOf D.F D.E))
    (hfin : (badPlacesOver D.F D.E D.VBad).Finite)
    (hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p) :
    TowerArithmetic D LT TL where
  ramIdx_bound v hv := ramIdx_bound_of_facts H h6 hF v hv
  step_ii := by
    rw [TL.sum_dst_logDK_eq]
    exact logDifferentDeg_torsionField_le D.prime H hfin
  step_iii := by
    refine sum_log_distinguished_le H he2 hfin TL.dst fun p hp => ?_
    simp only [ThetaLocalData.dst, Finset.mem_union] at hp
    rcases hp with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hbad p h))
    · refine Or.inr (Or.inr ?_)
      simp only [LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨v, rfl, hv⟩

end Iut
