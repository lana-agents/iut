/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.Labels
import Iut.Cor312.Procession

/-!
# Processions of labels (IUT I, Definition 4.10, Propositions 4.11, 6.9)

The label sets of the processions of IUT I:

* `sStar ℓ j = S^*_j = {1, …, j} ⊆ F_ℓ^*` (`j = 1, …, ℓ*`; Proposition 4.11(i)), of cardinality
  `j` (`card_sStar`);
* `sPm ℓ t = S^±_t = {0, …, t − 1} ⊆ |F_ℓ|` (`t = 1, …, ℓ±`; Proposition 6.9(i)), of cardinality
  `t` (`card_sPm`);

the `ℓ*`-procession `prcStar ℓ` and the `ℓ±`-procession `prcPm ℓ` (as `Iut.Procession`s of
`Iut/Cor312/Procession.lean`, whose capsule `i` is the label set of index `i + 1`), and the
**morphisms of processions** (Definition 4.10: an order-preserving injection of the index sets
together with compatible maps of capsules; here between processions of labels, so a map of labels
carrying each capsule into the image capsule, `LabelHom`).

Results:

* **Proposition 6.9(iii)**: the inclusions `S^*_j ↪ S^±_{j+1}` (`sStar_image_eq`: the image of
  `S^*_j` in `|F_ℓ|` is `S^±_{j+1} \ {0}`) form a morphism of processions
  `prcStar ℓ → prcPm ℓ` (`starToPm`).
* **The label indeterminacies of Propositions 4.11(i), 6.9(i)**: an index of the `n`-capsule of a
  procession has `n` possible labels, so a choice of one label for each capsule of an
  `n`-procession of capsules `S_1 ⊆ ⋯ ⊆ S_n` with `|S_k| = k` has `n!` possibilities
  (`card_choices_prcStar = ℓ*!`, `card_choices_prcPm = ℓ±!`), against `n^n` for `n` unordered
  `n`-capsules (Proposition 4.9(ii), 6.8(ii)); `n! < n^n` for `n ≥ 2` (`factorial_lt_pow_self`).
* **The container procession is a procession of `±`-labels**: the standard procession
  `S_2 ⊆ ⋯ ⊆ S_{ℓ*+1}` of `Iut/Cor312/Procession.lean` (the procession of the container of
  `Iut/Concrete/Container.lean`, hence of the wall) is carried isomorphically, by the natural map
  `ℕ → |F_ℓ|`, onto the capsules `S^±_2 ⊆ ⋯ ⊆ S^±_{ℓ±}` of `prcPm ℓ`
  (`standard_image_eq`, `standardToPm`, `natAbs_injOn_standard`).
-/

namespace Iut

namespace HodgeTheater

open Finset Nat

variable (ℓ : ℕ) [OddPrime ℓ]

open scoped Classical in
/-- **`S^±_t = {0, 1, …, t − 1} ⊆ |F_ℓ|`** (IUT I, Proposition 6.9(i)). -/
noncomputable def sPm (t : ℕ) : Finset (AbsFl ℓ) := (range t).image (natAbs ℓ)

open scoped Classical in
/-- **`S^*_j = {1, …, j} ⊆ F_ℓ^*`** (IUT I, Proposition 4.11(i)): the elements of `F_ℓ^*` whose
class in `|F_ℓ|` is one of `1, …, j`. -/
noncomputable def sStar (j : ℕ) : Finset (FlStar ℓ) :=
  (Finset.univ : Finset (FlStar ℓ)).filter fun x => starToAbs ℓ x ∈ (Icc 1 j).image (natAbs ℓ)

noncomputable instance : Fintype (FlStar ℓ) := Fintype.ofFinite _

lemma card_image_natAbs {s : Finset ℕ} (hs : ∀ k ∈ s, k ≤ ellStar ℓ) :
    (s.image (natAbs ℓ)).card = s.card := by
  classical
  exact card_image_of_injOn fun j hj k hk h => natAbs_injOn ℓ (hs j hj) (hs k hk) h

/-- **`|S^±_t| = t`** for `t ≤ ℓ±`. -/
theorem card_sPm {t : ℕ} (ht : t ≤ ellPm ℓ) : (sPm ℓ t).card = t := by
  classical
  simp only [ellPm] at ht
  unfold sPm
  rw [card_image_natAbs ℓ fun k hk => by rw [mem_range] at hk; omega, card_range]

lemma sStar_image_eq (j : ℕ) :
    (sStar ℓ j).image (starToAbs ℓ) = (sPm ℓ (j + 1)).filter (· ≠ 0) := by
  classical
  ext a
  simp only [sStar, sPm, mem_image, mem_filter, mem_univ, true_and, mem_Icc, mem_range]
  constructor
  · rintro ⟨x, ⟨k, ⟨hk1, hkj⟩, hk⟩, rfl⟩
    exact ⟨⟨k, by omega, hk⟩, starToAbs_ne_zero ℓ x⟩
  · rintro ⟨⟨k, hk, rfl⟩, h0⟩
    have hk0 : k ≠ 0 := fun h => h0 (by rw [h]; simp [natAbs, AbsFl.zero_def])
    refine ⟨nonzeroAbsEquiv ℓ ⟨natAbs ℓ k, h0⟩, ⟨k, ⟨by omega, by omega⟩, ?_⟩, ?_⟩ <;>
      rw [starToAbs_nonzeroAbsEquiv]

/-- **`|S^*_j| = j`** for `j ≤ ℓ*`. -/
theorem card_sStar {j : ℕ} (hj : j ≤ ellStar ℓ) : (sStar ℓ j).card = j := by
  classical
  have h := sStar_image_eq ℓ j
  rw [← card_image_of_injective _ (starToAbs_injective ℓ), h]
  have h0 : (0 : AbsFl ℓ) ∈ sPm ℓ (j + 1) :=
    mem_image.mpr ⟨0, mem_range.mpr (Nat.succ_pos j), by simp [natAbs, AbsFl.zero_def]⟩
  have := card_filter_add_card_filter_not (s := sPm ℓ (j + 1)) (p := (· ≠ 0))
  rw [card_sPm ℓ (by simp only [ellPm]; omega)] at this
  have h1 : ((sPm ℓ (j + 1)).filter fun a => ¬a ≠ 0) = {0} := by
    ext a
    simp only [mem_filter, not_not, mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ h0, h⟩⟩
  rw [h1, card_singleton] at this
  omega

lemma sPm_mono {s t : ℕ} (h : s ≤ t) : sPm ℓ s ⊆ sPm ℓ t := by
  classical
  exact image_subset_image (range_subset_range.mpr h)

lemma sStar_mono {i j : ℕ} (h : i ≤ j) : sStar ℓ i ⊆ sStar ℓ j := by
  classical
  intro x hx
  simp only [sStar, mem_filter, mem_univ, true_and, mem_image, mem_Icc] at hx ⊢
  obtain ⟨k, ⟨hk1, hki⟩, hk⟩ := hx
  exact ⟨k, ⟨hk1, hki.trans h⟩, hk⟩

/-! ### The processions -/

/-- **The `ℓ±`-procession of `±`-labels** `S^±_1 ⊆ S^±_2 ⊆ ⋯ ⊆ S^±_{ℓ±} = |F_ℓ|` (IUT I,
Proposition 6.9(i), Fig. 6.2). -/
noncomputable def prcPm : Procession (AbsFl ℓ) where
  length := ellPm ℓ
  capsule i := ⟨sPm ℓ (i + 1)⟩
  labels_mono _ _ h := sPm_mono ℓ (Nat.add_le_add_right h 1)

/-- **The `ℓ*`-procession of labels** `S^*_1 ⊆ S^*_2 ⊆ ⋯ ⊆ S^*_{ℓ*} = F_ℓ^*` (IUT I,
Proposition 4.11(i), Fig. 4.6). -/
noncomputable def prcStar : Procession (FlStar ℓ) where
  length := ellStar ℓ
  capsule i := ⟨sStar ℓ (i + 1)⟩
  labels_mono _ _ h := sStar_mono ℓ (Nat.add_le_add_right h 1)

/-- The `i`-th capsule of `prcPm` is an `(i + 1)`-capsule. -/
theorem prcPm_capsule_card (i : Fin (prcPm ℓ).length) : ((prcPm ℓ).capsule i).card = i + 1 :=
  card_sPm ℓ (by have := i.2; change (i : ℕ) < ellPm ℓ at this; omega)

/-- The `i`-th capsule of `prcStar` is an `(i + 1)`-capsule. -/
theorem prcStar_capsule_card (i : Fin (prcStar ℓ).length) :
    ((prcStar ℓ).capsule i).card = i + 1 :=
  card_sStar ℓ (by have := i.2; change (i : ℕ) < ellStar ℓ at this; omega)

/-- The last capsule of `prcPm` is `|F_ℓ|`. -/
theorem prcPm_last : ((prcPm ℓ).capsule ⟨ellStar ℓ, Nat.lt_succ_self _⟩).labels =
    Finset.univ := by
  classical
  apply eq_univ_of_card
  rw [← Nat.card_eq_fintype_card, card_absFl]
  exact card_sPm ℓ le_rfl

/-- The last capsule of `prcStar` is `F_ℓ^*`. -/
theorem prcStar_last (h : 0 < ellStar ℓ) :
    ((prcStar ℓ).capsule ⟨ellStar ℓ - 1, Nat.sub_lt h one_pos⟩).labels = Finset.univ := by
  classical
  apply eq_univ_of_card
  rw [← Nat.card_eq_fintype_card, card_flStar]
  change (sStar ℓ (ellStar ℓ - 1 + 1)).card = _
  rw [card_sStar ℓ (by omega)]
  omega

/-! ### Morphisms of processions of labels -/

/-- **A morphism of processions of labels** (IUT I, Definition 4.10): an order-preserving
injection `ι` of the index sets and a map of labels carrying the `j`-th capsule into the
`ι(j)`-th capsule. -/
structure LabelHom {α β : Type*} (P : Procession α) (Q : Procession β) where
  /-- The order-preserving injection of index sets. -/
  ι : Fin P.length ↪o Fin Q.length
  /-- The map of labels. -/
  f : α → β
  /-- Each capsule goes into the corresponding capsule. -/
  maps_to : ∀ j, ∀ a ∈ (P.capsule j).labels, f a ∈ (Q.capsule (ι j)).labels

/-- The shift `j ↦ j + 1` of index sets. -/
def succEmb (n : ℕ) : Fin n ↪o Fin (n + 1) := Fin.succOrderEmb n

open scoped Classical in
/-- **IUT I, Proposition 6.9(iii)**: the natural inclusions `S^*_j ↪ S^±_{j+1}` form a morphism
of processions `Prc^* → Prc^±`. -/
noncomputable def starToPm : LabelHom (prcStar ℓ) (prcPm ℓ) where
  ι := succEmb (ellStar ℓ)
  f := starToAbs ℓ
  maps_to j x hx := by
    have h := sStar_image_eq ℓ (j + 1)
    have hm : starToAbs ℓ x ∈ (sStar ℓ (j + 1)).image (starToAbs ℓ) := mem_image_of_mem _ hx
    rw [h, mem_filter] at hm
    exact hm.1

/-! ### The label indeterminacy -/

lemma prod_card_capsules {α : Type*} (P : Procession α) (hP : ∀ i, (P.capsule i).card = i + 1) :
    Nat.card (∀ i : Fin P.length, (P.capsule i).LabelType) = P.length ! := by
  classical
  rw [Nat.card_pi]
  simp only [Nat.card_eq_fintype_card]
  have : ∀ i : Fin P.length, Fintype.card (P.capsule i).LabelType = i + 1 := fun i => by
    rw [← hP i]
    exact Fintype.card_coe _
  simp only [this]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), Finset.prod_range_add_one_eq_factorial]

/-- **IUT I, Proposition 4.11(i)**: with processions, the label indeterminacy is `ℓ*!`. -/
theorem card_choices_prcStar :
    Nat.card (∀ i : Fin (prcStar ℓ).length, ((prcStar ℓ).capsule i).LabelType) = (ellStar ℓ)! :=
  prod_card_capsules _ (prcStar_capsule_card ℓ)

/-- **IUT I, Proposition 6.9(i)**: with processions, the label indeterminacy is `ℓ±!`. -/
theorem card_choices_prcPm :
    Nat.card (∀ i : Fin (prcPm ℓ).length, ((prcPm ℓ).capsule i).LabelType) = (ellPm ℓ)! :=
  prod_card_capsules _ (prcPm_capsule_card ℓ)

/-- Without processions (Propositions 4.9(ii), 6.8(ii)): each of the `n` indices of an
`n`-capsule has `n` possible labels, `n^n` in all. -/
theorem card_choices_capsule (n : ℕ) : Nat.card (Fin n → Fin n) = n ^ n := by
  simp

/-- `n! < n^n` for `n ≥ 2`: processions reduce the label indeterminacy. -/
theorem factorial_lt_pow_self {n : ℕ} (hn : 2 ≤ n) : n ! < n ^ n := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  calc ∏ i ∈ range n, (i + 1) < ∏ _i ∈ range n, n :=
        Finset.prod_lt_prod (fun i _ => Nat.succ_pos i)
          (fun i hi => by rw [mem_range] at hi; omega) ⟨0, by rw [mem_range]; omega, by omega⟩
    _ = n ^ n := by simp

/-! ### The container procession -/

lemma natAbs_injOn_standard (i : Fin (ellStar ℓ)) {a b : ℕ}
    (ha : a ∈ ((Procession.standard (ellStar ℓ)).capsule i).labels)
    (hb : b ∈ ((Procession.standard (ellStar ℓ)).capsule i).labels)
    (h : natAbs ℓ a = natAbs ℓ b) : a = b := by
  rw [Procession.standard_capsule_labels, mem_procLabels] at ha hb
  exact natAbs_injOn ℓ (by omega) (by omega) h

open scoped Classical in
/-- **The capsules of the container procession are `±`-label capsules**: the `i`-th capsule
`S_{i+2} = {0, …, i+1}` of the standard procession is carried onto `S^±_{i+2}`. -/
theorem standard_image_eq (i : Fin (ellStar ℓ)) :
    ((Procession.standard (ellStar ℓ)).capsule i).labels.image (natAbs ℓ) =
      ((prcPm ℓ).capsule ((succEmb (ellStar ℓ)) i)).labels := by
  rw [Procession.standard_capsule_labels]
  change (procLabels (i + 1)).image (natAbs ℓ) = sPm ℓ ((i : ℕ) + 1 + 1)
  unfold sPm procLabels
  congr 1
  ext k
  simp only [mem_Iic, mem_range]
  omega

/-- **The standard procession of the container maps to the `±`-label procession**
`S^±_2 ⊆ ⋯ ⊆ S^±_{ℓ±}`, injectively on every capsule. -/
noncomputable def standardToPm : LabelHom (Procession.standard (ellStar ℓ)) (prcPm ℓ) where
  ι := succEmb (ellStar ℓ)
  f := natAbs ℓ
  maps_to j a ha := by
    classical
    exact (standard_image_eq ℓ j).subset (mem_image_of_mem (natAbs ℓ) ha)

/-- The standard procession has the same number of capsules as the `±`-label procession minus
the first one (`S^±_1 = {0}`). -/
theorem standard_length : (Procession.standard (ellStar ℓ)).length + 1 = (prcPm ℓ).length := rfl

end HodgeTheater

end Iut
