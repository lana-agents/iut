/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalGalois
import Iut.Frobenioid.GlobalFracIdeal
import Iut.Frobenioid.GlobalPrimeZ
import Iut.Arakelov.ArchScaling

/-!
# The Galois-base global Frobenioid: primes and the fibre over `G/G` ([FrdI], Example 6.3)

[FrdI], Example 6.3 (l.6278–6285 of `~/iut-scratch/frd/FrdI.txt`): "if `F̃` is a [not
necessarily finite] Galois extension of `F`, `G = Gal(F̃/F)`, `D = B(G)⁰`, then `Φ`, `B` determine
monoids on `D` […] for each finite extension `L ⊆ F̃` of `F`, one verifies immediately that
`Φ(L) ≠ 0` is perf-factorial, that there is a natural bijection `Prime(Φ(L)) ∼→ V(L)`, and that
the supports of elements of `Φ(L)` are precisely the finite subsets of `V(L)`".

`GlobalGalois.lean` encodes `Φ^gp(L)` with invertible fractional ideals at the finite places
(`ArithDivG L`, so that the pull-back is the extension of ideals); `GlobalNonRlf.lean` encodes it
with coordinates `FinitePlace L →₀ ℤ` (`ArithDivZ L`, used for `GlobalFrobenioid L` over the
one-morphism base). This file compares the two and deduces:

* **`toZ L : ArithDivG L ≃+ ArithDivZ L`** (`I ↦ (count_w I)_w`), with `Φ(L)` corresponding to
  `Φ(L)` (`toZ_mem_iff`) and `div` to `div` (`toZ_divG`);
* `DivMonoid.Prime Φ A` (the primes of `Φ(A)`, [FrdI] §0, for any divisorial monoid on any base),
  its invariance under order isomorphisms (`DivMonoid.primeCongr`) and the identification with
  `PrimeZ` (`primeZEquiv`);
* **`primeGalEquiv A : Prime(Φ(G/H)) ≃ V(E^H)`** ([FrdI], Example 6.3, over the Galois base);
* **`degG_pbDiv`: `deg^arith_L(σ^*D) = [L:K]·deg^arith_K(D)`** for `K ⊆ L`, from
  `N(I·O_L) = N(I)^{[L:K]}` (`absNorm_extIdeal`, via Mathlib's `Ideal.absNorm_algebraMap` and the
  norm of principal ideals) and `∑_{w|v} m_w = [L:K]·m_v` (`sum_mult_comap`);
* the object `topObj = G/G` (`Fix topObj = F`, `fixTopEquiv`), and **the fibre over `G/G`**: a
  functor `fibreTop : GlobalFrobenioid F ⥤ GlobalGaloisFrob F E`, `Full` and `Faithful`, whose
  objects are exactly the objects of `C_{F̃/F}` lying over `G/G` (`fibreTop_obj_mk`,
  `fibreTop_base`); every morphism between objects over `G/G` lies over the identity, so
  `GlobalFrobenioid F` is isomorphic to the fibre of `C_{F̃/F}` over `G/G`.
-/

set_option linter.unusedSectionVars false

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField FractionalIdeal

open scoped nonZeroDivisors

universe w u v

/-! ### Primes of a divisorial monoid ([FrdI] §0) and their invariance -/

namespace DivMonoid

variable {D : Type u} [Category.{v} D] (Φ : DivMonoid.{w} D)

lemma le_nsmul {A : D} {a b : Φ.obj A} (h : Φ.le a b) (n : ℕ) : Φ.le (n • a) (n • b) := by
  change n • b - n • a ∈ Φ.pos A
  rw [← smul_sub]
  exact (Φ.pos A).nsmul_mem h n

lemma le_trans {A : D} {a b c : Φ.obj A} (h₁ : Φ.le a b) (h₂ : Φ.le b c) : Φ.le a c := by
  change c - a ∈ Φ.pos A
  rw [show c - a = (c - b) + (b - a) by abel]
  exact (Φ.pos A).add_mem h₂ h₁

lemma preceq_refl {A : D} (a : Φ.obj A) : Φ.preceq a a := ⟨1, one_pos, by simpa using Φ.le_refl a⟩

lemma preceq_trans {A : D} {a b c : Φ.obj A} (h₁ : Φ.preceq a b) (h₂ : Φ.preceq b c) :
    Φ.preceq a c := by
  obtain ⟨n, hn, h₁⟩ := h₁
  obtain ⟨m, hm, h₂⟩ := h₂
  refine ⟨n * m, Nat.mul_pos hn hm, Φ.le_trans h₁ ?_⟩
  rw [mul_smul]
  exact Φ.le_nsmul h₂ n

/-- The primary elements of `Φ(A)`. -/
def Primary (A : D) : Type w := {a : Φ.obj A // Φ.IsPrimary a}

/-- `a ∼ b` iff `a ≼ b ≼ a`. -/
def primarySetoid (A : D) : Setoid (Φ.Primary A) where
  r a b := Φ.preceq a.1 b.1 ∧ Φ.preceq b.1 a.1
  iseqv := ⟨fun a => ⟨Φ.preceq_refl a.1, Φ.preceq_refl a.1⟩, fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨Φ.preceq_trans h₁.1 h₂.1, Φ.preceq_trans h₂.2 h₁.2⟩⟩

/-- **`Prime(Φ(A))`** ([FrdI] §0): primary elements of `Φ(A)` up to `≼`-equivalence. -/
def Prime (A : D) : Type w := Quotient (Φ.primarySetoid A)

variable {Φ} {D' : Type*} [Category D'] {Ψ : DivMonoid.{w} D'} {A : D} {B : D'}

section Congr

variable (e : Φ.obj A ≃+ Ψ.obj B) (he : ∀ x, e x ∈ Ψ.pos B ↔ x ∈ Φ.pos A)
include he

lemma le_congr (a b : Φ.obj A) : Ψ.le (e a) (e b) ↔ Φ.le a b := by
  change e b - e a ∈ Ψ.pos B ↔ b - a ∈ Φ.pos A
  rw [← map_sub, he]

lemma preceq_congr (a b : Φ.obj A) : Ψ.preceq (e a) (e b) ↔ Φ.preceq a b := by
  refine exists_congr fun n => and_congr Iff.rfl ?_
  rw [← map_nsmul, le_congr e he]

lemma isPrimary_congr (a : Φ.obj A) : Ψ.IsPrimary (e a) ↔ Φ.IsPrimary a := by
  refine and_congr (he a) (and_congr (by simp) ⟨fun h b hb hb0 hba => ?_, fun h b hb hb0 hba => ?_⟩)
  · rw [← preceq_congr e he]
    exact h (e b) ((he b).2 hb) (by simpa using hb0) ((preceq_congr e he b a).2 hba)
  · obtain ⟨b, rfl⟩ := e.surjective b
    rw [preceq_congr e he]
    exact h b ((he b).1 hb) (by simpa using hb0) ((preceq_congr e he b a).1 hba)

/-- **Primes are invariant under isomorphisms of ordered monoids** `Φ(A) ≅ Ψ(B)`. -/
def primeCongr : Φ.Prime A ≃ Ψ.Prime B :=
  Quotient.congr
    { toFun := fun a => ⟨e a.1, (isPrimary_congr e he a.1).2 a.2⟩
      invFun := fun b => ⟨e.symm b.1, (isPrimary_congr e he _).1 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
      right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    fun a b => (and_congr (preceq_congr e he a.1 b.1) (preceq_congr e he b.1 a.1)).symm

lemma primeCongr_mk (a : Φ.Primary A) :
    primeCongr e he (Quotient.mk _ a) = Quotient.mk _ ⟨e a.1, (isPrimary_congr e he a.1).2 a.2⟩ :=
  rfl

end Congr

end DivMonoid

/-! ### Fractional ideals versus coordinates -/

section ToZ

variable {K : Type u} [Field K] [NumberField K]

lemma unit_ne_zero (I : (FI K)ˣ) : (I : FI K) ≠ 0 := I.ne_zero

variable (K) in
/-- The finite part of `toZ`: `I ↦ (count_w I)_w`. -/
noncomputable def toZFin : Additive (FI K)ˣ →+ (FinitePlace K →₀ ℤ) where
  toFun x := Finsupp.ofSupportFinite (fun w => FracIdealFrob.cnt ((Additive.toMul x : (FI K)ˣ) : FI K) w)
    (FracIdealFrob.finite_support_cnt _)
  map_zero' := by
    ext w
    simp [Finsupp.ofSupportFinite_coe, FracIdealFrob.cnt, count_one]
  map_add' x y := by
    ext w
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_add, Pi.add_apply, toMul_add,
      Units.val_mul, FracIdealFrob.cnt]
    exact count_mul K _ (unit_ne_zero _) (unit_ne_zero _)

lemma toZFin_apply (x : Additive (FI K)ˣ) (w : FinitePlace K) :
    toZFin K x w = FracIdealFrob.cnt ((Additive.toMul x : (FI K)ˣ) : FI K) w := rfl

/-- The fractional ideal with prescribed counts, as a unit. -/
noncomputable def ofZFin (c : FinitePlace K →₀ ℤ) : Additive (FI K)ˣ :=
  Additive.ofMul (Units.mk0 (Arakelov.FracIdeal.ofCounts K
    (c.equivMapDomain FinitePlace.equivHeightOneSpectrum))
    (Arakelov.FracIdeal.ofCounts_ne_zero _))

lemma toZFin_ofZFin (c : FinitePlace K →₀ ℤ) : toZFin K (ofZFin c) = c := by
  ext w
  rw [toZFin_apply, FracIdealFrob.cnt, ofZFin]
  change count K (FinitePlace.equivHeightOneSpectrum w) (Arakelov.FracIdeal.ofCounts K _) = _
  rw [Arakelov.FracIdeal.count_ofCounts]
  simpa using congrArg c (FinitePlace.equivHeightOneSpectrum.symm_apply_apply w)

lemma ofZFin_toZFin (x : Additive (FI K)ˣ) : ofZFin (toZFin K x) = x := by
  apply Additive.toMul.injective
  refine Units.ext (Arakelov.FracIdeal.eq_of_count_eq (Units.ne_zero _) (unit_ne_zero _)
    fun v => ?_)
  obtain ⟨w, rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective v
  have h := congrArg (fun c => c w) (toZFin_ofZFin (K := K) (toZFin K x))
  simpa [toZFin_apply, FracIdealFrob.cnt] using h

variable (K) in
/-- **`Φ^gp(L)` in the two encodings**: `(I, D_∞) ↦ ((count_w I)_w, D_∞)`. -/
noncomputable def toZ : ArithDivG K ≃+ ArithDivZ K where
  toFun x := (toZFin K x.1, x.2)
  invFun y := (ofZFin y.1, y.2)
  left_inv x := Prod.ext (ofZFin_toZFin x.1) rfl
  right_inv y := Prod.ext (toZFin_ofZFin y.1) rfl
  map_add' x y := Prod.ext (map_add (toZFin K) x.1 y.1) rfl

@[simp] lemma toZ_fst (x : ArithDivG K) : (toZ K x).1 = toZFin K x.1 := rfl
@[simp] lemma toZ_snd (x : ArithDivG K) : (toZ K x).2 = x.2 := rfl

/-- **`Φ(L)` corresponds to `Φ(L)`**: an ideal is integral iff all its counts are `≥ 0`. -/
theorem toZ_mem_iff (x : ArithDivG K) : toZ K x ∈ effConeZ K ↔ x ∈ effG K := by
  rw [mem_effConeZ, mem_effG]
  refine and_congr ?_ Iff.rfl
  have h := Arakelov.FracIdeal.le_iff_count_le (K := K)
    (unit_ne_zero (Additive.toMul x.1 : (FI K)ˣ)) (one_ne_zero (α := FI K))
  rw [h]
  simp only [count_one, toZ_fst, toZFin_apply, FracIdealFrob.cnt]
  exact ⟨fun h v => by
    obtain ⟨w, rfl⟩ := FinitePlace.equivHeightOneSpectrum.surjective v
    exact h w, fun h w => h _⟩

/-- **`div` corresponds to `div`**. -/
theorem toZ_divG (x : Additive Kˣ) : toZ K (divG K x) = divZ K x := by
  obtain ⟨y, rfl⟩ : ∃ y : Kˣ, Additive.ofMul y = x := ⟨x.toMul, rfl⟩
  refine Prod.ext (Finsupp.ext fun w => ?_) rfl
  rw [toZ_fst, toZFin_apply, divG_fst]
  exact FracIdealFrob.cnt_spanSingleton y w

end ToZ

/-! ### `deg(σ^*D) = [L:K]·deg D` -/

section Degree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra in
/-- `N(J·O_L) = N(J)^{[L:K]}` for an integral ideal `J`. -/
lemma absNorm_extIdeal_coeIdeal (J : Ideal (𝓞 K)) :
    absNorm (extIdeal (algebraMap K L) (J : FI K)) =
      absNorm (J : FI K) ^ Module.finrank K L := by
  have hmap : RingOfIntegers.mapRingHom (algebraMap K L) = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  rw [extIdeal, extendedHom'_apply, extended_coeIdeal_eq_map, coeIdeal_absNorm, coeIdeal_absNorm,
    hmap, Ideal.absNorm_algebraMap, Algebra.finrank_eq_of_equiv_equiv
      (FractionRing.algEquiv (𝓞 K) K).toRingEquiv (FractionRing.algEquiv (𝓞 L) L).toRingEquiv]
  · push_cast; rfl
  · ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 K) K)
      (FractionRing.algEquiv (𝓞 L) L) _

/-- `N(x·O_L) = N(x)^{[L:K]}`. -/
lemma absNorm_extIdeal_spanSingleton (x : K) :
    absNorm (extIdeal (algebraMap K L) (spanSingleton (𝓞 K)⁰ x)) =
      absNorm (spanSingleton (𝓞 K)⁰ x) ^ Module.finrank K L := by
  rw [extIdeal_spanSingleton, absNorm_span_singleton, absNorm_span_singleton,
    ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow, abs_pow]

/-- **`N(I·O_L) = N(I)^{[L:K]}`** for a fractional ideal `I`. -/
theorem absNorm_extIdeal (I : FI K) :
    absNorm (extIdeal (algebraMap K L) I) = absNorm I ^ Module.finrank K L := by
  obtain ⟨a, J, -, rfl⟩ := exists_eq_spanSingleton_mul I
  rw [map_mul, map_mul, map_mul, absNorm_extIdeal_spanSingleton, absNorm_extIdeal_coeIdeal,
    mul_pow]

/-- `∑_w m_w D(w|_K) = [L:K] ∑_v m_v D(v)`. -/
theorem sum_mult_comap (D : InfinitePlace K → ℝ) :
    ∑ w : InfinitePlace L, (w.mult : ℝ) * D (w.comap (algebraMap K L)) =
      Module.finrank K L * ∑ v : InfinitePlace K, (v.mult : ℝ) * D v := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun w : InfinitePlace L => w.comap (algebraMap K L)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : ∀ w ∈ Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v),
      (w.mult : ℝ) * D (w.comap (algebraMap K L)) = (w.mult : ℝ) * D v := fun w hw => by
    rw [(Finset.mem_filter.mp hw).2]
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul]
  have := Arakelov.sum_mult_comap_eq (k := K) (K := L) v
  rw [← Nat.cast_sum, this]
  push_cast
  ring

/-- **`deg(σ^*D) = [L:K]·deg D`** ([FrdI], Example 6.3: the arithmetic degrees of the
divisor monoids on `B(G)⁰` are compatible with pull-back up to the degree of the extension). -/
theorem degG_pbDiv (x : ArithDivG K) :
    degG L (pbDiv (algebraMap K L) x) = Module.finrank K L * degG K x := by
  change Real.log (absNorm ((Additive.toMul (pbDiv (algebraMap K L) x).1 : (FI L)ˣ) : FI L) : ℝ) +
    ∑ w, (w.mult : ℝ) * (pbDiv (algebraMap K L) x).2 w = _ * (Real.log
      (absNorm ((Additive.toMul x.1 : (FI K)ˣ) : FI K) : ℝ) + ∑ v, (v.mult : ℝ) * x.2 v)
  rw [pbDiv_fst, absNorm_extIdeal, Rat.cast_pow, Real.log_pow]
  simp only [pbDiv_snd]
  rw [sum_mult_comap, mul_add]

end Degree

/-! ### Pull-back along isomorphisms of number fields -/

section PbEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- `pbDiv` along a ring isomorphism, as an additive equivalence. -/
noncomputable def pbDivEquiv (τ : K ≃+* L) : ArithDivG K ≃+ ArithDivG L where
  toFun := pbDiv (τ : K →+* L)
  invFun := pbDiv (τ.symm : L →+* K)
  left_inv x := by
    rw [pbDiv_comp]
    convert pbDiv_id x
    ext; simp
  right_inv y := by
    rw [pbDiv_comp]
    convert pbDiv_id y
    ext; simp
  map_add' := map_add _

lemma pbDivEquiv_apply (τ : K ≃+* L) (x : ArithDivG K) :
    pbDivEquiv τ x = pbDiv (τ : K →+* L) x := rfl

lemma pbDivEquiv_mem_iff (τ : K ≃+* L) (x : ArithDivG K) :
    pbDivEquiv τ x ∈ effG L ↔ x ∈ effG K :=
  pbDiv_mem_iff _ x

end PbEquiv

/-! ### `Prime(Φ(L)) ≅ V(L)` over the Galois base -/

section Prime

variable {K : Type u} [Field K] [NumberField K]

/-- `PrimeZ` is the `Prime` of the divisorial monoid `Φ(F)` on `Pt`. -/
def primeZEquiv : (phiZ K).Prime pt ≃ GlobalFrobenioid.PrimeZ K :=
  Equiv.refl _

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

/-- **`Prime(Φ(G/H)) ≅ V(E^H)`** ([FrdI], Example 6.3: "a natural bijection
`Prime(Φ(L)) ∼→ V(L)`", over the Galois base `B(Gal(E/F))⁰`). -/
noncomputable def primeGalEquiv (A : OrbitObj (GalG F E)) :
    (phiGal F E).Prime A ≃ GlobalRealified.Place (Fix A) :=
  (DivMonoid.primeCongr (Ψ := phiZ (Fix A)) (B := pt) (toZ (Fix A))
    toZ_mem_iff).trans (primeZEquiv.trans GlobalFrobenioid.primeEquivZ)

end Prime

/-! ### The fibre over `G/G` -/

section Fibre

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [IsGalois F E]

variable (F E) in
/-- The terminal object `G/G` of `B(G)⁰`. -/
def topObj : OrbitObj (GalG F E) := ⟨⊤, isOpen_univ⟩

instance : Subsingleton (topObj F E ⟶ topObj F E) :=
  ⟨fun _ _ => OrbitHom.hom_ext (funext fun _ =>
    haveI : Subsingleton (GalG F E ⧸ (⊤ : Subgroup (GalG F E))) :=
      QuotientGroup.subsingleton_quotient_top
    Subsingleton.elim (α := GalG F E ⧸ (⊤ : Subgroup (GalG F E))) _ _)⟩

lemma mem_fix_top (x : E) (hx : x ∈ Fix (topObj F E)) : x ∈ (⊥ : IntermediateField F E) := by
  have h : Fix (topObj F E) = ⊥ := by
    have h1 := InfiniteGalois.fixedField_fixingSubgroup (k := F) (K := E) ⊥
    rw [IntermediateField.fixingSubgroup_bot] at h1
    exact h1
  rwa [h] at hx

variable (F E) in
/-- **`E^G = F`**. -/
noncomputable def fixTopEquiv : F ≃+* Fix (topObj F E) :=
  RingEquiv.ofBijective (algebraMap F (Fix (topObj F E)))
    ⟨(algebraMap F (Fix (topObj F E))).injective, fun x => by
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp (mem_fix_top (x : E) x.2)
      exact ⟨c, Subtype.ext hc⟩⟩

variable (F E) in
/-- `Φ^gp(G/G) ≅ Φ^gp(F)` in coordinates. -/
noncomputable def eTop : (phiGal F E).obj (topObj F E) ≃+ ArithDivZ F :=
  (pbDivEquiv (fixTopEquiv F E).symm).trans (toZ F)

lemma eTop_mem_iff (x : (phiGal F E).obj (topObj F E)) :
    eTop F E x ∈ effConeZ F ↔ x ∈ (phiGal F E).pos (topObj F E) := by
  change toZ F (pbDivEquiv _ x) ∈ _ ↔ _
  rw [toZ_mem_iff, pbDivEquiv_mem_iff]
  rfl

lemma eTop_symm_mem (x : ArithDivZ F) (hx : x ∈ effConeZ F) :
    (eTop F E).symm x ∈ (phiGal F E).pos (topObj F E) := by
  rw [← eTop_mem_iff, AddEquiv.apply_symm_apply]
  exact hx

variable (F E) in
/-- `B(G/G) ≅ F^×`. -/
noncomputable def uTop : Additive Fˣ →+ (bGalNF F E).obj (topObj F E) :=
  pbU (fixTopEquiv F E : F →+* Fix (topObj F E))

lemma uTop_injective : Function.Injective (uTop F E) := pbU_injective _

lemma eTop_divG_uTop (u : Additive Fˣ) :
    eTop F E ((divGalNF F E).app (topObj F E) (uTop F E u)) = divZ F u := by
  change toZ F (pbDiv ((fixTopEquiv F E).symm : Fix (topObj F E) →+* F)
    (divG (Fix (topObj F E)) (pbU (fixTopEquiv F E : F →+* Fix (topObj F E)) u))) = _
  rw [pbDiv_divG]
  convert toZ_divG u
  apply Additive.toMul.injective
  ext
  simp [pbU_apply]

lemma uTop_surjective : Function.Surjective (uTop F E) := fun y =>
  ⟨pbU ((fixTopEquiv F E).symm : Fix (topObj F E) →+* F) y, by
    refine Additive.toMul.injective (Units.ext ?_)
    exact RingEquiv.apply_symm_apply (fixTopEquiv F E) _⟩

lemma eTop_symm_divZ (u : Additive Fˣ) :
    (eTop F E).symm (divZ F u) = (divGalNF F E).app (topObj F E) (uTop F E u) := by
  rw [AddEquiv.symm_apply_eq, eTop_divG_uTop]

variable (F E) in
/-- **The fibre of `C_{F̃/F}` over `G/G`**: `GlobalFrobenioid F → GlobalGaloisFrob F E`,
`(pt, α) ↦ (G/G, α)`, `(n, Z, u) ↦ (n, id, Z, u)`. -/
noncomputable def fibreTop : GlobalFrobenioid F ⥤ GlobalGaloisFrob F E where
  obj X := ⟨topObj F E, (eTop F E).symm X.α⟩
  map {X Y} φ := Model.mk' φ.deg (𝟙 _) ((eTop F E).symm φ.div) (eTop_symm_mem _ φ.div_mem)
    (uTop F E φ.u) (by
      rw [(phiGal F E).pb_id, ← eTop_symm_divZ, ← map_nsmul, ← map_add, ← map_add]
      congr 1
      exact φ.rel)
  map_id X := Model.hom_ext rfl rfl (by simp) (by simp [uTop])
  map_comp φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · simp only [Model.mk', Model.comp_div, (phiGal F E).pb_id', map_add, map_nsmul]
      rfl
    · simp only [Model.mk', Model.comp_u, (bGalNF F E).pb_id', map_add, map_nsmul]
      rfl

@[simp] lemma fibreTop_base (X : GlobalFrobenioid F) : ((fibreTop F E).obj X).base = topObj F E :=
  rfl

/-- Every object of `C_{F̃/F}` over `G/G` is in the image of `fibreTop`. -/
theorem fibreTop_obj_mk (α : (phiGal F E).obj (topObj F E)) :
    (fibreTop F E).obj ⟨pt, eTop F E α⟩ = ⟨topObj F E, α⟩ := by
  change (⟨topObj F E, (eTop F E).symm (eTop F E α)⟩ : GlobalGaloisFrob F E) = _
  rw [AddEquiv.symm_apply_apply]

lemma fibreTop_obj_injective : Function.Injective (fibreTop F E).obj := by
  rintro ⟨⟨⟨⟩⟩, α⟩ ⟨⟨⟨⟩⟩, β⟩ h
  have h' : (eTop F E).symm α = (eTop F E).symm β := by
    have := congrArg (fun X : GlobalGaloisFrob F E => X) h
    simp only [fibreTop] at this
    exact (Model.mk.inj this).2 |> eq_of_heq
  rw [(eTop F E).symm.injective h']

instance : (fibreTop F E).Faithful where
  map_injective {X Y} φ ψ h := by
    have h1 : ((fibreTop F E).map φ).deg = ((fibreTop F E).map ψ).deg := by rw [h]
    have h3 : ((fibreTop F E).map φ).div = ((fibreTop F E).map ψ).div := by rw [h]
    have h4 : ((fibreTop F E).map φ).u = ((fibreTop F E).map ψ).u := by rw [h]
    change (eTop F E).symm φ.div = (eTop F E).symm ψ.div at h3
    change uTop F E φ.u = uTop F E ψ.u at h4
    exact Model.hom_ext h1 (Subsingleton.elim _ _) ((eTop F E).symm.injective h3)
      (uTop_injective h4)

/-- The relation of a morphism between objects over `G/G`, in coordinates. -/
lemma rel_top {a b : (phiGal F E).obj (topObj F E)}
    (ψ : (⟨topObj F E, a⟩ : GlobalGaloisFrob F E) ⟶ ⟨topObj F E, b⟩) :
    (ψ.deg : ℕ) • eTop F E a + eTop F E ψ.div =
      eTop F E b + eTop F E ((divGalNF F E).app _ ψ.u) := by
  have r := ψ.rel
  have hb : ψ.base = 𝟙 _ := Subsingleton.elim _ _
  rw [hb, GrpOn.pb_id'] at r
  have := congrArg (eTop F E) r
  simpa only [map_add, map_nsmul] using this

instance : (fibreTop F E).Full where
  map_surjective {X Y} ψ := by
    obtain ⟨u, hu⟩ := uTop_surjective (F := F) (E := E) ψ.u
    have hb : ψ.base = 𝟙 _ := Subsingleton.elim (α := topObj F E ⟶ topObj F E) _ _
    refine ⟨Model.mk' ψ.deg (eqToHom (Subsingleton.elim X.base Y.base)) (eTop F E ψ.div)
      ((eTop_mem_iff _).2 ψ.div_mem) u ?_, ?_⟩
    · have r := rel_top (a := (eTop F E).symm X.α) (b := (eTop F E).symm Y.α) ψ
      rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← hu, eTop_divG_uTop] at r
      exact r
    · exact Model.hom_ext rfl hb.symm (AddEquiv.symm_apply_apply _ _) hu

end Fibre

end Frobenioid

end Iut
