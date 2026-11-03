/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFTransition

/-!
# Conjugation by automorphisms of `Ω` and the Kummer map (MR9, `CKSemiAbsConj` item 3)

For the Galois equivariance of the functoriality of [AbsTopIII] Thm 1.9
(`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) the Kummer classes must be moved
along the conjugation action of `Π_U` on the stages. Generically, for a ring automorphism `a` of
`Ω`:

* `muConj`, **`zConj`**: `a` on `μ_n(Ω)` and on `Ẑ(1) = lim μ_n(Ω)`;
* `restrictE`: `a` restricted to a subfield `E` with `a(E) ⊆ E`;
* **`galConjInv`**: `σ ↦ a⁻¹ σ a` on `Gal(Ω/E)` (for `a(E) ⊆ E`), continuous;
* `zConj_galConjInv_smul`: `a (a⁻¹ σ a · m) = σ · a(m)` (the compatibility of `ContH1.map`);
* **`conjH1`**: the induced map `H¹(Gal(Ω/E), Ẑ(1)) → H¹(Gal(Ω/E), Ẑ(1))`, cocycles
  `c ↦ a ∘ c ∘ (σ ↦ a⁻¹ σ a)`;
* **`conjH1_kummerZHat`**: `a_*(κ_E(u)) = κ_E(a(u))` (Kummer classes are natural in field
  automorphisms; at level `n` the Kummer cocycle of the root `a(α)`).
-/

open KummerTheory Curve

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-! ### Roots of unity -/

section Mu

variable {Ω : Type*} [Field Ω] (a : Ω ≃+* Ω)

/-- `μ_n(Ω) → μ_n(Ω)` along a ring automorphism `a`. -/
def muConj (n : ℕ) : Mu n Ω →* Mu n Ω where
  toFun ζ := Mu.mk (Units.map (a : Ω →* Ω) (Mu.val ζ)) (by rw [← map_pow, Mu.val_pow_n, map_one])
  map_one' := Mu.ext (by simp)
  map_mul' ζ η := Mu.ext (by simp)

@[simp]
lemma val_muConj (n : ℕ) (ζ : Mu n Ω) :
    ((Mu.val (muConj a n ζ) : Ωˣ) : Ω) = a ((Mu.val ζ : Ωˣ) : Ω) := rfl

lemma muConj_transition {m n : ℕ} (h : m ∣ n) (ζ : Mu n Ω) :
    muConj a m (Mu.transition h ζ) = Mu.transition h (muConj a n ζ) := by
  apply Mu.ext
  apply Units.ext
  simp

variable (K : Type*) [Field K]

/-- **`Ẑ(1) → Ẑ(1)` along a ring automorphism `a` of `Ω`.** -/
def zConj : ZHatOne K Ω →* ZHatOne K Ω where
  toFun x := ⟨fun i => muConj a i.n ((x : ∀ j, Mu j.n Ω) i), fun i j h => by
    rw [← muConj_transition, x.2 i j h]⟩
  map_one' := Subtype.ext (funext fun i => map_one (muConj a i.n))
  map_mul' x y := Subtype.ext (funext fun i => map_mul (muConj a i.n) _ _)

lemma zConj_apply (x : ZHatOne K Ω) (i : KummerIndex K) :
    ((zConj a K x : ZHatOne K Ω) : ∀ i, Mu i.n Ω) i = muConj a i.n ((x : ∀ j, Mu j.n Ω) i) :=
  rfl

lemma continuous_zConj : Continuous (zConj a K) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact continuous_of_discreteTopology.comp ((continuous_apply i).comp continuous_subtype_val)

lemma proj_zConj (i : KummerIndex K) (x : ZHatOne K Ω) :
    ZHatOne.proj i (zConj a K x) = muConj a i.n (ZHatOne.proj i x) := rfl

/-- `a` intertwines the actions of `σ` and `σ'` on `Ẑ(1)` if `σ' ∘ a = a ∘ σ` on `Ω`. -/
lemma zConj_smul {P P' : Type*} [Field P] [Field P'] [Algebra P Ω] [Algebra P' Ω]
    (σ : Ω ≃ₐ[P] Ω) (σ' : Ω ≃ₐ[P'] Ω) (h : ∀ x, σ' (a x) = a (σ x)) (m : ZHatOne K Ω) :
    zConj a K (σ • m) = σ' • zConj a K m := by
  apply Subtype.ext
  funext i
  apply Mu.ext
  apply Units.ext
  change a (σ _) = σ' (a _)
  rw [h]

end Mu

/-! ### Conjugation on `Gal(Ω/E)` -/

section Gal

variable {P Ω : Type*} [Field P] [Field Ω] [Algebra P Ω] (E : IntermediateField P Ω)
  (a : Ω ≃+* Ω) (ha : ∀ x ∈ E, a x ∈ E)

/-- `a` restricted to a subfield `E` with `a(E) ⊆ E`. -/
def restrictE : E →+* E where
  toFun x := ⟨a x, ha x x.2⟩
  map_one' := Subtype.ext (map_one a)
  map_mul' x y := Subtype.ext (map_mul a (x : Ω) y)
  map_zero' := Subtype.ext (map_zero a)
  map_add' x y := Subtype.ext (map_add a (x : Ω) y)

@[simp]
lemma coe_restrictE (x : E) : ((restrictE E a ha x : E) : Ω) = a x := rfl

/-- **`σ ↦ a⁻¹ σ a` on `Gal(Ω/E)`**, for `a(E) ⊆ E`. -/
def galConjInv : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[E] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := a.trans (σ.toRingEquiv.trans a.symm)) fun c => by
    change a.symm (σ (a (c : Ω))) = c
    have h := σ.commutes ⟨a c, ha c c.2⟩
    change σ (a (c : Ω)) = a (c : Ω) at h
    rw [h, RingEquiv.symm_apply_apply]
  map_one' := AlgEquiv.ext fun x => by
    change a.symm (a x) = x
    rw [RingEquiv.symm_apply_apply]
  map_mul' σ τ := AlgEquiv.ext fun x => by
    change a.symm ((σ * τ) (a x)) = a.symm (σ (a (a.symm (τ (a x)))))
    rw [RingEquiv.apply_symm_apply]
    rfl

@[simp]
lemma galConjInv_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : galConjInv E a ha σ x = a.symm (σ (a x)) := rfl

lemma continuous_galConjInv [Algebra.IsIntegral E Ω] : Continuous (galConjInv E a ha) := by
  refine continuous_of_isOpen_setOf_apply_eq _ fun x => ?_
  have e : {σ : Ω ≃ₐ[E] Ω | galConjInv E a ha σ x = x} =
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (a x) : Set (Ω ≃ₐ[E] Ω)) := by
    ext σ
    simp only [Set.mem_setOf_eq, galConjInv_apply, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    constructor
    · intro h
      have h' := congrArg a h
      rwa [RingEquiv.apply_symm_apply] at h'
    · intro h
      rw [h, RingEquiv.symm_apply_apply]
  rw [e]
  exact stabilizer_isOpen_of_isIntegral (a x)

lemma zConj_galConjInv_smul (K : Type*) [Field K] (σ : Ω ≃ₐ[E] Ω) (m : ZHatOne K Ω) :
    zConj a K (galConjInv E a ha σ • m) = σ • zConj a K m :=
  zConj_smul a K _ σ (fun x => by rw [galConjInv_apply, RingEquiv.apply_symm_apply]) m

lemma muConj_galConjInv_smul (n : ℕ) (σ : Ω ≃ₐ[E] Ω) (ζ : Mu n Ω) :
    muConj a n (galConjInv E a ha σ • ζ) = σ • muConj a n ζ := by
  apply Mu.ext
  apply Units.ext
  change a (a.symm (σ (a _))) = σ (a _)
  rw [RingEquiv.apply_symm_apply]

variable [Algebra.IsIntegral E Ω]

/-- **`a_* : H¹(Gal(Ω/E), Ẑ(1)) → H¹(Gal(Ω/E), Ẑ(1))`**, cocycles `c ↦ a ∘ c ∘ (σ ↦ a⁻¹ σ a)`. -/
def conjH1 : ContH1 (Ω ≃ₐ[E] Ω) (ZHatOne E Ω) →* ContH1 (Ω ≃ₐ[E] Ω) (ZHatOne E Ω) :=
  ContH1.map (galConjInv E a ha) (continuous_galConjInv E a ha) (zConj a E)
    (continuous_zConj a E) (zConj_galConjInv_smul E a ha E)

/-- The same at level `n`. -/
def conjH1Mu (n : ℕ) : ContH1 (Ω ≃ₐ[E] Ω) (Mu n Ω) →* ContH1 (Ω ≃ₐ[E] Ω) (Mu n Ω) :=
  ContH1.map (galConjInv E a ha) (continuous_galConjInv E a ha) (muConj a n)
    continuous_of_discreteTopology (muConj_galConjInv_smul E a ha n)

lemma h1Proj_conjH1 (i : KummerIndex E) (X : ContH1 (Ω ≃ₐ[E] Ω) (ZHatOne E Ω)) :
    h1Proj E Ω i (conjH1 E a ha X) = conjH1Mu E a ha i.n (h1Proj E Ω i X) := by
  induction X using ContH1.induction_on with
  | h c => rfl

lemma conjH1Mu_kummer [IsSepClosed Ω] (n : ℕ) [NeZero (n : E)] (u : Eˣ) :
    conjH1Mu E a ha n (kummer n E Ω u) =
      kummer n E Ω (Units.map (restrictE E a ha : E →* E) u) := by
  obtain ⟨α, hα⟩ := HasKummerRoots.exists_pow_eq (n := n) (K := E) (Ω := Ω) u
  have hα' : Units.map (a : Ω →* Ω) α ^ n =
      Units.map (algebraMap E Ω : E →* Ω) (Units.map (restrictE E a ha : E →* E) u) := by
    rw [← map_pow, hα]
    ext
    rfl
  rw [kummer_eq u α hα, kummer_eq _ _ hα', conjH1Mu, ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext σ
  apply Mu.ext
  apply Units.ext
  simp only [ContH1.cocyclesMap_apply, kummerCocycle_apply, val_muConj, val_kummerFun,
    Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe,
    map_div₀, galConjInv_apply, RingEquiv.apply_symm_apply]

/-- **Kummer classes are natural in field automorphisms**: `a_*(κ_E(u)) = κ_E(a(u))`. -/
theorem conjH1_kummerZHat [IsGalois E Ω] [IsSepClosed Ω] [CharZero E] (u : Eˣ) :
    conjH1 E a ha (kummerZHat E Ω u) =
      kummerZHat E Ω (Units.map (restrictE E a ha : E →* E) u) := by
  refine h1ToLimit_injective E Ω (Subtype.ext (funext fun i => ?_))
  change h1Proj E Ω i _ = h1Proj E Ω i _
  rw [h1Proj_conjH1, h1Proj_kummerZHat, h1Proj_kummerZHat, conjH1Mu_kummer]

end Gal

end Iut.Reconstruction.Thm19
