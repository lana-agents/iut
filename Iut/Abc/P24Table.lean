/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.DeriveFintype

/-!
# The incidence table behind Theorem P2.4, as a decidable certificate

Theorem P2.4 of the research note `P2P9.md` (§2.4, "what every proof of Szpiro over `ℚ` must
use") is a statement about a finite incidence table: ten recorded structures `C1`–`C10`
(§2.1) against fourteen candidate proof ingredients `PF, RAD, BASE, α, ε, FIN, RIG, ISO, PAS,
HT, CHAR0, MOD, NEW, VA` (§2.2), with entries "holds", "fails", "inexpressible" and
"unknown/split" (§2.3). This file encodes that table and checks its combinatorics by
`decide`.

**Scope.** Only the *combinatorics* of P2.4 relative to the recorded table is certified. The
mathematical content of each entry (for instance that Frobenius twists over `𝔽̄_p(t)` violate
Szpiro, or that `Π₇₈` satisfies every proven profile inequality) is cited in `P2P9.md` and is
not formalised here. The ingredients and structures are plain labels.

## Semantics

An ingredient *separates* a structure when its entry is "fails": a proof that uses the
ingredient is not refuted by that structure. "Holds" and "inexpressible" (`—`) never separate.
The eight entries marked unknown, split, heuristic or from memory are left open, and a
`Reading` decides each of them (`true` = fails). The *baseline* reading takes the primary
entry of the table: `FIN` fails in `C1` (`𝔽̄_p(t)`), and every other open entry holds.

A set `S` of ingredients *hits* a family of structures when every structure of the family is
separated by some member of `S`. The general family is `C1`–`C5`, `C7`–`C9`; the package
family adds `C6` (proofs through the IUT package). `C10` is not a countermodel (Szpiro does not
fail there) and is not a row of the incidence table, so its row is inexpressible throughout
and it belongs to neither family.

## Main results

* `minimalHittingSets_general_baseline`: in the baseline reading the minimal hitting sets of the
  general family are exactly the nine sets of `generalMinimal`. They all contain `BASE` and
  `NEW`, but neither `PF` nor `RAD` is in all of them: `{BASE, NEW, RIG, α}` and
  `{BASE, NEW, PF, α}` hit every structure (`hits_without_pf`, `hits_without_rad`, in every
  reading).
* `minimalHittingSets_package_baseline`: with `C6`, each of them acquires `VA`.
* `clauses_hits_iff`: the five clauses of P2.4 (`PF`, `RAD`, `BASE`, one of
  `α, ε, FIN, RIG, ISO, PAS, HT`, `NEW`) form a *sufficient* hitting condition exactly in the
  readings where `FIN` fails in `C1`; `clause_irredundant` shows that each clause is needed for
  that sufficiency, witnessed by `C7, C9, C3, C2, C5`, in every reading.
* Robustness: `new_mem_of_hits` (`NEW` is necessary in every reading), `base_mem_iff`
  (`BASE` is necessary iff `PAS` and `HT` hold in `C3`), `clause4_mem_of_hits` and
  `hits_mod_char0` (clause 4 is necessary iff `MOD` holds in `C2`), and
  `minimalHittingSets_general_eq_iff`: the family of minimal hitting sets is unchanged iff
  `FIN` fails in `C1` and the open entries `C2 × MOD`, `C3 × PAS`, `C3 × HT`, `C7 × CHAR0`
  hold; the entries `C1 × MOD`, `C4 × PAS`, `C4 × HT` do not matter.

So, relative to the table, P2.4's "any proof must use each of (1)–(5)" holds literally for
clauses 3 and 5 (clause 3 only if `PAS`, `HT` hold in `C3`) and for clause 4 (only if `MOD`
holds in `C2`). Clauses 1 and 2 are not forced by the table: `PF` can be replaced by `RIG`
(for `C7`) together with `α` or `FIN` (for `C8`), and `RAD` by any of `α, ε, FIN, RIG` (for
`C9`). P2.4's irredundancy claim does hold, read as irredundancy of the five clauses as a
sufficient condition (`clause_irredundant`).

The enumeration over `Finset.powerset` (`minimalHittingSets_general_baseline`, inside the
twelve-element support, `minimalHittingSets_eq_support`) uses `decide +kernel`: the kernel
evaluates the `Decidable` instance and no compiled code is trusted. Every other check is a
plain `decide`; the package family is reduced to the general one by hand.
-/

namespace Iut.Abc.P24Table

/-- The ten recorded structures `C1`–`C10` of `P2P9.md` §2.1. -/
inductive Model
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype, Repr

/-- The fourteen candidate proof ingredients of `P2P9.md` §2.2. -/
inductive Ingredient
  /-- `PF`: a global product formula. -/
  | pf
  /-- `RAD`: radicals (conductors) are in the language. -/
  | rad
  /-- `BASE`: the base field is `ℚ`, or a base-discriminant term is carried. -/
  | base
  /-- `α`: places of pairwise distinct finite residue characteristics. -/
  | alpha
  /-- `ε`: an archimedean place. -/
  | eps
  /-- `FIN`: finite residue fields. -/
  | fin
  /-- `RIG`: no height-scaling endomorphism fixing the radical degree. -/
  | rig
  /-- `ISO`: bounded isogeny classes, Shafarevich finiteness. -/
  | iso
  /-- `PAS`: Pasten's product cut. -/
  | pas
  /-- `HT`: height bounds (Pasten 2026, Stewart–Yu, Baker). -/
  | ht
  /-- `CHAR0`: characteristic zero. -/
  | char0
  /-- `MOD`: modularity, Galois representations. -/
  | mod
  /-- `NEW`: a profile inequality violated by `Π₇₈` (not yet proven). -/
  | new
  /-- `VA`: the IUT coupling `V ≥ (s - 1) a`. -/
  | va
  deriving DecidableEq, Fintype, Repr

/-- The entries of the incidence table. -/
inductive Entry
  /-- `✓`: the ingredient holds in the structure. -/
  | holds
  /-- `✗`: the ingredient fails in the structure; only this entry separates. -/
  | fails
  /-- `—`: inexpressible or vacuous in the structure. -/
  | blank
  /-- Unknown, split, heuristic or from memory: decided by a `Reading`. -/
  | undetermined
  deriving DecidableEq, Fintype, Repr

open Model Ingredient Entry

/-- The incidence table of `P2P9.md` §2.3 (rows `C1`–`C9`; `VA` is recorded only for `C6`).
The row of `C10`, which is not a countermodel, is inexpressible throughout. -/
def table : Model → Ingredient → Entry
  | c1, pf => holds | c1, rad => holds | c1, base => holds | c1, alpha => fails
  | c1, eps => fails | c1, fin => undetermined | c1, rig => fails | c1, iso => fails
  | c1, pas => fails | c1, ht => fails | c1, char0 => fails | c1, mod => undetermined
  | c2, pf => holds | c2, rad => holds | c2, base => holds | c2, alpha => fails
  | c2, eps => fails | c2, fin => fails | c2, rig => fails | c2, iso => fails
  | c2, pas => fails | c2, ht => fails | c2, char0 => holds | c2, mod => undetermined
  | c3, base => fails | c3, pas => undetermined | c3, ht => undetermined
  | c3, va => blank | c3, _ => holds
  | c4, pf => holds | c4, rad => holds | c4, base => holds | c4, alpha => holds
  | c4, eps => holds | c4, fin => holds | c4, pas => undetermined
  | c4, ht => undetermined | c4, new => fails
  | c5, pf => holds | c5, rad => holds | c5, base => holds | c5, alpha => holds
  | c5, eps => holds | c5, fin => holds | c5, pas => holds | c5, ht => holds
  | c5, new => fails
  | c6, base => holds | c6, va => fails
  | c7, pf => fails | c7, rad => holds | c7, alpha => holds | c7, fin => holds
  | c7, rig => fails | c7, char0 => undetermined
  | c8, pf => fails | c8, rad => holds | c8, alpha => fails | c8, fin => fails
  | c8, char0 => holds
  | c9, pf => holds | c9, rad => fails | c9, base => holds | c9, alpha => fails
  | c9, eps => fails | c9, fin => fails | c9, rig => fails | c9, iso => holds
  | c9, char0 => holds
  | _, _ => blank

/-- A reading of the eight open entries of the table (`true` = the ingredient fails there):
`C1 × FIN` (`✗` for `𝔽̄_p`, `✓` for `𝔽_q`), `C1 × MOD` and `C2 × MOD` (from memory, heuristic),
`C3 × PAS` and `C3 × HT` (unknown), `C4 × PAS` and `C4 × HT` (split between fixed and moving
support), `C7 × CHAR0` (split). -/
structure Reading where
  c1Fin : Bool
  c1Mod : Bool
  c2Mod : Bool
  c3Pas : Bool
  c3Ht : Bool
  c4Pas : Bool
  c4Ht : Bool
  c7Char0 : Bool
  deriving DecidableEq, Repr

/-- A statement about all readings is a statement about eight Booleans. -/
lemma Reading.forall_iff {P : Reading → Prop} :
    (∀ r, P r) ↔ ∀ a b c d e f g h : Bool, P ⟨a, b, c, d, e, f, g, h⟩ :=
  ⟨fun H _ _ _ _ _ _ _ _ ↦ H _, fun H ⟨a, b, c, d, e, f, g, h⟩ ↦ H a b c d e f g h⟩

/-- All `2 ^ 8` readings can be checked by `decide`. -/
instance Reading.decidableForall {P : Reading → Prop} [DecidablePred P] :
    Decidable (∀ r, P r) :=
  decidable_of_iff _ Reading.forall_iff.symm

/-- The baseline reading: the primary entry of the table. -/
def baseline : Reading := ⟨true, false, false, false, false, false, false, false⟩

/-- The value that a reading assigns to an open entry (`false` off the open entries). -/
def Reading.read (r : Reading) : Model → Ingredient → Bool
  | c1, fin => r.c1Fin | c1, mod => r.c1Mod | c2, mod => r.c2Mod
  | c3, pas => r.c3Pas | c3, ht => r.c3Ht | c4, pas => r.c4Pas | c4, ht => r.c4Ht
  | c7, char0 => r.c7Char0
  | _, _ => false

/-- Whether ingredient `i` separates structure `m` in reading `r`. -/
def fails (r : Reading) (m : Model) (i : Ingredient) : Bool :=
  match table m i with
  | .fails => true
  | .undetermined => r.read m i
  | _ => false

/-- The reading touches only the open entries: these are exactly the eight listed cells. -/
theorem undetermined_iff (m : Model) (i : Ingredient) :
    table m i = undetermined ↔
      (m, i) ∈ ({(c1, fin), (c1, mod), (c2, mod), (c3, pas), (c3, ht), (c4, pas), (c4, ht),
        (c7, char0)} : Finset (Model × Ingredient)) := by
  revert m i; decide

/-- `S` hits the family `M`: every structure in `M` is separated by a member of `S`. -/
def Hits (r : Reading) (M : Finset Model) (S : Finset Ingredient) : Prop :=
  ∀ m ∈ M, ∃ i ∈ S, fails r m i = true

instance (r : Reading) (M : Finset Model) (S : Finset Ingredient) : Decidable (Hits r M S) := by
  unfold Hits; infer_instance

/-- A minimal hitting set: it hits `M`, and no proper subset obtained by erasing one element
does. -/
def IsMinimalHitting (r : Reading) (M : Finset Model) (S : Finset Ingredient) : Prop :=
  Hits r M S ∧ ∀ i ∈ S, ¬ Hits r M (S.erase i)

instance (r : Reading) (M : Finset Model) (S : Finset Ingredient) :
    Decidable (IsMinimalHitting r M S) := by
  unfold IsMinimalHitting; infer_instance

/-- The minimal hitting sets of `M`, computed through `Finset.powerset`. -/
def minimalHittingSets (r : Reading) (M : Finset Model) : Finset (Finset Ingredient) :=
  (Finset.univ : Finset Ingredient).powerset.filter (IsMinimalHitting r M)

/-- The general family: the countermodels `C1`–`C5`, `C7`–`C9`. -/
def general : Finset Model := {c1, c2, c3, c4, c5, c7, c8, c9}

/-- The package family: the general family and `C6` (proofs through the IUT package). -/
def package : Finset Model := insert c6 general

/-- The nine minimal hitting sets of the general family in the baseline reading. -/
def generalMinimal : Finset (Finset Ingredient) :=
  {{base, new, pf, alpha}, {base, new, rig, alpha}, {base, new, pf, rig},
   {base, new, pf, fin}, {base, new, pf, eps}, {base, new, rig, fin},
   {base, new, pf, rad, pas}, {base, new, pf, rad, iso}, {base, new, pf, rad, ht}}

lemma Hits.mono {r : Reading} {M : Finset Model} {S T : Finset Ingredient}
    (h : Hits r M S) (hST : S ⊆ T) : Hits r M T := fun m hm ↦
  let ⟨i, hi, hf⟩ := h m hm
  ⟨i, hST hi, hf⟩

/-- Every hitting set contains a minimal one. -/
lemma exists_isMinimalHitting {r : Reading} {M : Finset Model} {S : Finset Ingredient}
    (h : Hits r M S) : ∃ T ⊆ S, IsMinimalHitting r M T := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hm : ∀ i ∈ S, ¬ Hits r M (S.erase i)
    · exact ⟨S, subset_rfl, h, hm⟩
    · obtain ⟨i, hi, h'⟩ := not_forall₂.1 hm
      rw [not_not] at h'
      obtain ⟨T, hT, hTm⟩ := ih _ (Finset.erase_ssubset hi) h'
      exact ⟨T, hT.trans (Finset.erase_subset _ _), hTm⟩

lemma mem_minimalHittingSets {r : Reading} {M : Finset Model} {S : Finset Ingredient} :
    S ∈ minimalHittingSets r M ↔ IsMinimalHitting r M S := by
  simp [minimalHittingSets]

/-- The ingredients that separate some structure of `M`. -/
def support (r : Reading) (M : Finset Model) : Finset Ingredient :=
  Finset.univ.filter fun i ↦ ∃ m ∈ M, fails r m i = true

/-- A minimal hitting set consists of separating ingredients. -/
lemma IsMinimalHitting.subset_support {r : Reading} {M : Finset Model}
    {S : Finset Ingredient} (h : IsMinimalHitting r M S) : S ⊆ support r M := by
  intro i hi
  by_contra hs
  refine h.2 i hi fun m hm ↦ ?_
  obtain ⟨j, hj, hf⟩ := h.1 m hm
  have hji : j ≠ i := by
    rintro rfl
    exact hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, m, hm, hf⟩)
  exact ⟨j, Finset.mem_erase.2 ⟨hji, hj⟩, hf⟩

/-- The minimal hitting sets can be enumerated inside the powerset of the support only. -/
lemma minimalHittingSets_eq_support (r : Reading) (M : Finset Model) :
    minimalHittingSets r M = (support r M).powerset.filter (IsMinimalHitting r M) := by
  ext S
  simp only [minimalHittingSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  exact ⟨fun h ↦ ⟨h.subset_support, h⟩, fun h ↦ h.2⟩

/-! ### The package family -/

lemma va_not_fails_general (r : Reading) : ∀ m ∈ general, fails r m va = false := by
  revert r; decide

lemma fails_c6 (r : Reading) (i : Ingredient) : fails r c6 i = true ↔ i = va := by
  revert r i; decide

lemma hits_general_erase_va {r : Reading} {S : Finset Ingredient} :
    Hits r general (S.erase va) ↔ Hits r general S := by
  refine ⟨fun h ↦ h.mono (Finset.erase_subset _ _), fun h m hm ↦ ?_⟩
  obtain ⟨i, hi, hf⟩ := h m hm
  refine ⟨i, Finset.mem_erase.2 ⟨?_, hi⟩, hf⟩
  rintro rfl
  simp [va_not_fails_general r m hm] at hf

lemma hits_package_iff {r : Reading} {S : Finset Ingredient} :
    Hits r package S ↔ va ∈ S ∧ Hits r general S := by
  simp only [Hits, package, Finset.forall_mem_insert, fails_c6, exists_eq_right]

/-- The minimal hitting sets of the package family are those of the general family with `VA`
added. -/
lemma isMinimalHitting_package_iff {r : Reading} {S : Finset Ingredient} :
    IsMinimalHitting r package S ↔ va ∈ S ∧ IsMinimalHitting r general (S.erase va) := by
  simp only [IsMinimalHitting, hits_package_iff, hits_general_erase_va]
  constructor
  · rintro ⟨⟨hva, hS⟩, hmin⟩
    refine ⟨hva, hS, fun i hi h ↦ ?_⟩
    have hiv : i ≠ va := (Finset.mem_erase.1 hi).1
    refine hmin i (Finset.mem_of_mem_erase hi) ⟨Finset.mem_erase.2 ⟨hiv.symm, hva⟩, ?_⟩
    rw [← hits_general_erase_va, Finset.erase_right_comm]
    exact h
  · rintro ⟨hva, hS, hmin⟩
    refine ⟨⟨hva, hS⟩, fun i hi ⟨hva', h⟩ ↦ ?_⟩
    have hiv : i ≠ va := fun e ↦ by simp [e] at hva'
    refine hmin i (Finset.mem_erase.2 ⟨hiv, hi⟩) ?_
    rw [Finset.erase_right_comm, hits_general_erase_va]
    exact h

/-! ### The baseline families -/

/-- **P2.4, literal combinatorics.** In the baseline reading the minimal hitting sets of the
general family are exactly the nine sets of `generalMinimal`. -/
theorem minimalHittingSets_general_baseline :
    minimalHittingSets baseline general = generalMinimal := by
  rw [minimalHittingSets_eq_support]
  decide +kernel

/-- With `C6` (proofs through the IUT package), `VA` is added to each minimal hitting set. -/
theorem minimalHittingSets_package_baseline :
    minimalHittingSets baseline package = generalMinimal.image (insert va) := by
  ext S
  rw [mem_minimalHittingSets, isMinimalHitting_package_iff,
    ← minimalHittingSets_general_baseline]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨hva, hT⟩
    exact ⟨S.erase va, (mem_minimalHittingSets.2 hT), Finset.insert_erase hva⟩
  · rintro ⟨T, hT, rfl⟩
    have hT' := mem_minimalHittingSets.1 hT
    have hvT : va ∉ T := fun hv ↦ by
      obtain ⟨-, m, hm, hf⟩ := Finset.mem_filter.1 (hT'.subset_support hv)
      simp [va_not_fails_general baseline m hm] at hf
    exact ⟨Finset.mem_insert_self _ _, by rw [Finset.erase_insert hvT]; exact hT'⟩

/-! ### The five clauses of P2.4 -/

/-- The ingredients of clause 4 of P2.4. -/
def clause4 : Finset Ingredient := {alpha, eps, fin, rig, iso, pas, ht}

/-- The five clauses (1)–(5) of P2.4. -/
inductive ClauseIdx
  | one | two | three | four | five
  deriving DecidableEq, Fintype, Repr

open ClauseIdx

/-- Clause `k` of P2.4 holds for the ingredient set `S`. -/
def Clause (S : Finset Ingredient) : ClauseIdx → Prop
  | one => pf ∈ S
  | two => rad ∈ S
  | three => base ∈ S
  | four => ∃ i ∈ clause4, i ∈ S
  | five => new ∈ S

instance (S : Finset Ingredient) : (k : ClauseIdx) → Decidable (Clause S k)
  | one => inferInstanceAs (Decidable (pf ∈ S))
  | two => inferInstanceAs (Decidable (rad ∈ S))
  | three => inferInstanceAs (Decidable (base ∈ S))
  | four => inferInstanceAs (Decidable (∃ i ∈ clause4, i ∈ S))
  | five => inferInstanceAs (Decidable (new ∈ S))

/-- All five clauses of P2.4 hold. -/
def Clauses (S : Finset Ingredient) : Prop := ∀ k, Clause S k

/-- The clauses of P2.4 are a sufficient hitting condition exactly in the readings where `FIN`
fails in `C1`: in the others the choice `FIN` in clause 4 misses `C1`. -/
theorem clauses_hits_iff (r : Reading) :
    (∀ S, Clauses S → Hits r general S) ↔ r.c1Fin = true := by
  have key : ∀ r : Reading, (∀ i ∈ clause4, Hits r general {pf, rad, base, i, new}) ↔
      r.c1Fin = true := by decide
  rw [← key]
  constructor
  · intro h i hi
    refine h _ fun k ↦ ?_
    cases k
    · simp [Clause]
    · simp [Clause]
    · simp [Clause]
    · exact ⟨i, hi, by simp⟩
    · simp [Clause]
  · intro h S hS
    obtain ⟨i, hi, hiS⟩ := hS four
    refine (h i hi).mono ?_
    have := hS one; have := hS two; have := hS three; have := hS five
    simp only [Clause] at *
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- The witness of irredundancy for clause `k`: P2P9's `C7, C9, C3, C2, C5`. -/
def witness : ClauseIdx → Model
  | one => c7 | two => c9 | three => c3 | four => c2 | five => c5

/-- A set satisfying every clause except clause `k`. -/
def dropClause : ClauseIdx → Finset Ingredient
  | one => {rad, base, iso, new}
  | two => {pf, base, iso, new}
  | three => {pf, rad, iso, new}
  | four => {pf, rad, base, new}
  | five => {pf, rad, base, iso}

/-- **Irredundancy of P2.4**, in every reading: `dropClause k` satisfies every clause except
clause `k`, and the witness structure `witness k` is not separated by it. -/
theorem clause_irredundant (r : Reading) (k : ClauseIdx) :
    (∀ j, j ≠ k → Clause (dropClause k) j) ∧ ¬ Clause (dropClause k) k ∧
      ∀ i ∈ dropClause k, fails r (witness k) i = false := by
  revert r k; decide

/-! ### Robustness under the readings of the open entries -/

/-- `NEW` is necessary in every reading, because of `C5`. -/
theorem new_mem_of_hits {r : Reading} {S : Finset Ingredient} (h : Hits r general S) :
    new ∈ S := by
  obtain ⟨i, hi, hf⟩ := h c5 (by decide)
  have : ∀ r : Reading, ∀ i, fails r c5 i = true → i = new := by decide
  exact this r i hf ▸ hi

/-- `BASE` is necessary iff `PAS` and `HT` hold in `C3`; otherwise `{PF, RAD, PAS, HT, NEW}`
hits without it. -/
theorem base_mem_iff (r : Reading) :
    (∀ S, Hits r general S → base ∈ S) ↔ r.c3Pas = false ∧ r.c3Ht = false := by
  constructor
  · intro h
    have key : ∀ r : Reading, Hits r general {pf, rad, pas, ht, new} ↔
        (r.c3Pas = true ∨ r.c3Ht = true) := by decide
    by_contra hc
    have hc' : r.c3Pas = true ∨ r.c3Ht = true := by
      revert hc; cases r.c3Pas <;> cases r.c3Ht <;> simp
    have := h _ ((key r).2 hc')
    simp at this
  · rintro ⟨hp, hh⟩ S hS
    obtain ⟨i, hi, hf⟩ := hS c3 (by decide)
    have : ∀ r : Reading, r.c3Pas = false → r.c3Ht = false → ∀ i, fails r c3 i = true →
        i = base := by decide
    exact this r hp hh i hf ▸ hi

/-- Clause 4 is necessary when `MOD` holds in `C2`, because of `C2`. -/
theorem clause4_mem_of_hits {r : Reading} (hr : r.c2Mod = false) {S : Finset Ingredient}
    (h : Hits r general S) : ∃ i ∈ clause4, i ∈ S := by
  obtain ⟨i, hi, hf⟩ := h c2 (by decide)
  have : ∀ r : Reading, r.c2Mod = false → ∀ i, fails r c2 i = true → i ∈ clause4 := by
    decide
  exact ⟨i, this r hr i hf, hi⟩

/-- If `MOD` fails in `C2` (it holds there only heuristically), clause 4 can be replaced by
`MOD` together with `CHAR0`. -/
theorem hits_mod_char0 {r : Reading} (hr : r.c2Mod = true) :
    Hits r general {pf, rad, base, mod, char0, new} := by
  revert r; decide

/-- `PF` is not necessary, in any reading: `RIG` separates `C7` and `α` separates `C8`. -/
theorem hits_without_pf (r : Reading) : Hits r general {base, new, rig, alpha} := by
  revert r; decide

/-- `RAD` is not necessary, in any reading: `α` separates `C9`. -/
theorem hits_without_rad (r : Reading) : Hits r general {pf, base, new, alpha} := by
  revert r; decide

/-- The open entries `C1 × MOD`, `C4 × PAS`, `C4 × HT` do not affect hitting, once the
others are as in the baseline. -/
lemma hits_iff_baseline {r : Reading} (h1 : r.c1Fin = true) (h2 : r.c2Mod = false)
    (h3 : r.c3Pas = false) (h4 : r.c3Ht = false) (h7 : r.c7Char0 = false)
    (S : Finset Ingredient) : Hits r general S ↔ Hits baseline general S := by
  obtain ⟨a, b, c, d, e, f, g, k⟩ := r
  simp only at h1 h2 h3 h4 h7
  subst h1 h2 h3 h4 h7
  -- `C1` is implied by `C2`, and `C4` by `C5`, in every such reading.
  have h12 : ∀ b f g : Bool, ∀ i, fails ⟨true, b, false, false, false, f, g, false⟩ c2 i = true →
      fails ⟨true, b, false, false, false, f, g, false⟩ c1 i = true := by decide
  have h54 : ∀ b f g : Bool, ∀ i, fails ⟨true, b, false, false, false, f, g, false⟩ c5 i = true →
      fails ⟨true, b, false, false, false, f, g, false⟩ c4 i = true := by decide
  have heq : ∀ b f g : Bool, ∀ m ∈ ({c2, c3, c5, c7, c8, c9} : Finset Model), ∀ i,
      fails ⟨true, b, false, false, false, f, g, false⟩ m i = fails baseline m i := by decide
  have core : ∀ r : Reading, (∀ i, fails r c2 i = true → fails r c1 i = true) →
      (∀ i, fails r c5 i = true → fails r c4 i = true) →
      (Hits r general S ↔ Hits r {c2, c3, c5, c7, c8, c9} S) := by
    intro r hc1 hc4
    simp only [Hits, general, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq]
    constructor
    · rintro ⟨-, h2, h3, -, h5, h7, h8, h9⟩; exact ⟨h2, h3, h5, h7, h8, h9⟩
    · rintro ⟨h2, h3, h5, h7, h8, h9⟩
      obtain ⟨i, hi, hf⟩ := h2
      obtain ⟨j, hj, hg⟩ := h5
      exact ⟨⟨i, hi, hc1 i hf⟩, ⟨i, hi, hf⟩, h3, ⟨j, hj, hc4 j hg⟩, ⟨j, hj, hg⟩, h7, h8, h9⟩
  rw [core _ (h12 b f g) (h54 b f g), core baseline (h12 false false false)
    (h54 false false false)]
  simp only [Hits]
  refine forall₂_congr fun m hm ↦ ?_
  simp only [heq b f g m hm]

/-- **Sensitivity of P2.4.** The family of minimal hitting sets of the general family equals
the baseline family iff `FIN` fails in `C1` and `MOD` (in `C2`), `PAS`, `HT` (in `C3`) and
`CHAR0` (in `C7`) hold. The other three open entries never matter. -/
theorem minimalHittingSets_general_eq_iff (r : Reading) :
    minimalHittingSets r general = generalMinimal ↔
      r.c1Fin = true ∧ r.c2Mod = false ∧ r.c3Pas = false ∧ r.c3Ht = false ∧
        r.c7Char0 = false := by
  constructor
  · intro h
    have hmem : ∀ S, Hits r general S → ∃ T ∈ generalMinimal, T ⊆ S := fun S hS ↦ by
      obtain ⟨T, hT, hTm⟩ := exists_isMinimalHitting hS
      exact ⟨T, h ▸ mem_minimalHittingSets.2 hTm, hT⟩
    have hfin : Hits r general {base, new, pf, fin} := by
      have : ({base, new, pf, fin} : Finset Ingredient) ∈ minimalHittingSets r general := by
        rw [h]; decide
      exact (mem_minimalHittingSets.1 this).1
    -- For each open entry that matters, a hitting set containing no member of the family.
    have w2 : ∀ r : Reading, r.c2Mod = true → Hits r general {pf, rad, base, mod, char0, new} :=
      by decide
    have w3 : ∀ r : Reading, r.c3Pas = true ∨ r.c3Ht = true →
        Hits r general {pf, rad, pas, ht, new} := by decide
    have w7 : ∀ r : Reading, r.c7Char0 = true → Hits r general {base, new, char0, alpha} := by
      decide
    have w1 : ∀ r : Reading, Hits r general {base, new, pf, fin} → r.c1Fin = true := by decide
    have n2 : ¬ ∃ T ∈ generalMinimal, T ⊆ {pf, rad, base, mod, char0, new} := by decide
    have n3 : ¬ ∃ T ∈ generalMinimal, T ⊆ {pf, rad, pas, ht, new} := by decide
    have n7 : ¬ ∃ T ∈ generalMinimal, T ⊆ {base, new, char0, alpha} := by decide
    refine ⟨w1 r hfin, ?_, ?_, ?_, ?_⟩
    · cases h2 : r.c2Mod
      · rfl
      · exact (n2 (hmem _ (w2 r h2))).elim
    · cases h3 : r.c3Pas
      · rfl
      · exact (n3 (hmem _ (w3 r (Or.inl h3)))).elim
    · cases h4 : r.c3Ht
      · rfl
      · exact (n3 (hmem _ (w3 r (Or.inr h4)))).elim
    · cases h7 : r.c7Char0
      · rfl
      · exact (n7 (hmem _ (w7 r h7))).elim
  · rintro ⟨h1, h2, h3, h4, h7⟩
    rw [← minimalHittingSets_general_baseline]
    ext S
    simp only [mem_minimalHittingSets, IsMinimalHitting, hits_iff_baseline h1 h2 h3 h4 h7]

end Iut.Abc.P24Table
