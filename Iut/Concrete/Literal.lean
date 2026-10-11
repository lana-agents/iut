/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalEstimate

/-!
# The literal reading of IUT III, Corollary 3.12, and IUT IV's reading

IUT III, Corollary 3.12 defines `−|log(Θ)|` as the procession-normalized log-volume of the
holomorphic hull of the union of the possible images of a Θ-pilot object under the
indeterminacies (Ind1), (Ind2), (Ind3) of Theorem 3.11. The indeterminacy (Ind1) contains the
permutation automorphisms of the label sets `S_{j+1}` of the procession (IUT III,
Introduction): the theta value `q^{j²}` of the capsule `S_{j+1}` may sit at any label. IUT IV,
proof of Theorem 1.10, Steps (iv)–(v), computes with the theta value at the label `j` only.

* `Cor312LiteralHolds` (`Iut/Concrete/ThetaRegion.lean`) is the variant with the union over all
  label positions (`InitialThetaData.litLabels`), the literal reading of Corollary 3.12;
* `Cor312VariantHolds` is the variant with the label `j` (`InitialThetaData.ivLabels`),
  IUT IV's reading, from which the implication to ABC is proved.

The literal region contains IUT IV's region, so its hull has larger log-volume, and the IV
reading implies the literal one (`cor312Literal_of_variant`). The converse is exactly the
step from the literal Corollary 3.12 to IUT IV, Steps (iv)–(v): it holds when every place
of `F_mod` above each bad prime is bad (then the theta values at all labels of a tuple have the
same order), but not in general.
-/

namespace Iut

universe u

open NumberField

namespace InitialThetaData

variable (D : InitialThetaData.{u}) (n : ℕ)

lemma thetaFiniteOn_mono (i : Fin n) {S T : Set (Lab n i)} (hST : S ⊆ T) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Kt (.finite p)) :
    D.thetaFiniteOn n i S p c ⊆ D.thetaFiniteOn n i T p c :=
  Set.iUnion₂_mono fun _ _ => Set.image_mono (Set.biUnion_subset_biUnion_left hST)

lemma thetaComponentOn_mono (i : Fin n) {S T : Set (Lab n i)} (hST : S ⊆ T)
    (vQ : RationalPlace) (c : Lab n i → LocalTheory.Fiber D.Kt vQ) :
    D.thetaComponentOn n i S vQ c ⊆ D.thetaComponentOn n i T vQ c := by
  rcases vQ with p | _
  · exact D.thetaFiniteOn_mono n i hST p c
  · exact le_rfl

lemma thetaPilotOn_mono {S T : ∀ i : Fin n, Set (Lab n i)} (hS : ∀ i, (S i).Nonempty)
    (hT : ∀ i, (T i).Nonempty) (hST : ∀ i, S i ⊆ T i)
    (i : Fin (LocalTheory.container D.Kt n).proc.length) :
    D.thetaPilotOn n S hS i ≤ D.thetaPilotOn n T hT i :=
  fun vQ _ hx c => D.thetaComponentOn_mono n i (hST i) vQ c (hx c)

/-- **The literal right-hand side dominates IUT IV's**: `−|log(Θ)|` in IUT IV's reading is at
most `−|log(Θ)|` in the literal reading of IUT III, Corollary 3.12. -/
theorem rhs_le_rhsLit : D.rhsData.rhs ≤ D.rhsDataLit.rhs := by
  set n := (D.ℓ - 1) / 2
  set H := LocalTheory.hull D.Kt n
  have hadm : ∀ (S : ∀ i : Fin n, Set (Lab n i)) (hS : ∀ i, (S i).Nonempty) i,
      H.IsAdmissible (D.thetaPilotOn n S hS i) := fun S hS i vQ =>
    ⟨fun c => D.thetaComponentOn n i (S i) vQ c,
      fun c => D.thetaComponentOn_admissible n i (S i) (hS i) vQ c, rfl⟩
  have hle : ∀ i, H.hullAdmissible (D.thetaPilotOn n (ivLabels n) (ivLabels_nonempty n) i) ≤
      H.hullAdmissible (D.thetaPilotOn n (litLabels n) (litLabels_nonempty n) i) := fun i =>
    H.hullAdmissible_mono (hadm _ _ i) (hadm _ _ i)
      (D.thetaPilotOn_mono n _ _ (ivLabels_subset_litLabels n) i)
  have hhull : ∀ (S : ∀ i : Fin n, Set (Lab n i)) (hS : ∀ i, (S i).Nonempty) i vQ,
      (LocalTheory.packet D.Kt (Lab n i) vQ).IsHullRegion
        ((H.hullAdmissible (D.thetaPilotOn n S hS i)).region vQ) := fun S hS i vQ =>
    LocalTheory.isHullRegion_of_mem_hullRegions D.Kt _ vQ _
      ((H.system i vQ).hull_mem_hullRegions (hadm S hS i vQ))
  change (LocalTheory.vol D.Kt n).processionVol
      (H.hullFamily (D.thetaPilotOn n (ivLabels n) (ivLabels_nonempty n))) ≤
    (LocalTheory.vol D.Kt n).processionVol
      (H.hullFamily (D.thetaPilotOn n (litLabels n) (litLabels_nonempty n)))
  unfold LogVolumeData.processionVol
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
  unfold LogVolumeData.globalVol
  refine finsum_le_finsum' ((LocalTheory.vol D.Kt n).finite_support_packetVol _)
    ((LocalTheory.vol D.Kt n).finite_support_packetVol _) fun vQ => ?_
  exact TowerArithmetic.packetVol_mono (D := D) i vQ _ _ (hhull _ _ i vQ) (hhull _ _ i vQ)
    (hle i vQ)

end InitialThetaData

/-- **IUT IV's reading implies the literal reading of IUT III, Corollary 3.12.** -/
theorem cor312Literal_of_variant (h : Cor312VariantHolds) : Cor312LiteralHolds :=
  fun D => (h D).trans D.rhs_le_rhsLit

end Iut
