/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Kummer.NFDescent
import CurvesJacobian.Galois.FunctionFieldF
import Iut.Reconstruction.Uchida.FunctionField

/-!
# [AbsTopIII] Thm 1.9 (e): the additive structure of the NF-portion `K_{Z_NF}`

[AbsTopIII] Thm 1.9 (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2179–2185): "One
constructs the additive structure on `k̄_NF^× ⋃ {0}`, `K^×_{Z_NF} ⋃ {0}` [notation as in (d)] by
applying the functorial algorithm of Proposition 1.3 to the data of the form described in
Proposition 1.3, (a), (b), (c), arising from the construction of (d) [cf. also the decomposition
groups of (a), the isomorphisms of (b)]." Here `K_{Z_NF}` is the function field of the descent
`Z_NF` of `Z ×_{k_Z} k̄` to `k̄_NF` (l.2172–2174), a function field of one variable over the
algebraically closed field `k̄_NF`, so Prop 1.3 (Uchida's lemma, `Uchida.ofFunctionField`)
applies to it.

In curves-jacobian's Galois model of an NF-curve (`NFModel D`: `F_NF ⊆ F k̄ ⊆ Ω` with
`F_NF · k̄ = F k̄`, linearly disjoint from `k̄` over `k̄_NF = algebraicClosure ℚ Ω`):

* `fnf N`: `F_NF` as an intermediate field of `Ω / k̄_NF`;
  **`isFunctionField_fnf`**: `F_NF` is a function field of one variable over `k̄_NF`
  (from curves-jacobian `NFModel.exists_transcendental`, `NFModel.exists_basis`);
* `nfTriple N`: the triple `(K^×_{Z_NF}, {ord_x}, {U_x})` of Prop 1.3 (a)–(c) for `F_NF`;
  **`nf_addRel_iso_iff`** (Thm 1.9 (e)): for **any** triple isomorphic to it, Uchida's
  algorithm `AddRel` returns the addition of `F_NF`; **`nf_mem_consts_iso_iff`**: its constants
  are `k̄_NF^×` (the first half of (e));
* the points of `Z_NF` from NF-points of `X_{k̄}` (Def 1.7 (ii)): `nfPlace hk hW`, the place of
  `F_NF / k̄_NF` below an NF-point `W ⊇ k`, and `barPlace hk hW`, the place of `F k̄ / k̄` below
  `W`; **`exists_valuation_eq_fnf`** (every value of `W` on `F k̄` is a value on `F_NF`, from the
  Gauss lemma `NFModel.valuation_le_valuation_sum`) and **`ord_nfPlace`**: `ord` at the NF-point
  computed in `F_NF` agrees with `ord` computed in `F k̄` (`Z_NF ×_{k̄_NF} k̄ → Z_NF` is
  unramified at NF-points). This is how the divisors of (c) (`res_p ∘ κ_U`, computed in the
  function field over `k̄`) give the `ord_x` of the triple of `F_NF`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  (N : NFModel D)

/-- `F_NF = k̄_NF(Z_NF)` as an intermediate field of `Ω / k̄_NF`. -/
def fnf : IntermediateField (algebraicClosure ℚ Ω) Ω :=
  N.FNF.toIntermediateField fun x => N.algebraic_mem _ (mem_algebraicClosure_iff.1 x.2)

lemma mem_fnf {x : Ω} : x ∈ fnf N ↔ x ∈ N.FNF := Iff.rfl

/-- An element transcendental over `k̄` is transcendental over `k̄_NF ⊆ k̄`. -/
theorem transcendental_algebraicClosure {y : Ω} (hyt : Transcendental (kbar k Ω) y) :
    Transcendental (algebraicClosure ℚ Ω) y := fun h => hyt <| by
  have hy' : y ∈ kbar k Ω :=
    mem_kbar_of_isAlgebraic (@IsAlgebraic.restrictScalars ℚ (algebraicClosure ℚ Ω) Ω
      _ _ _ _ _ _ _ _ (algebraicClosure.isAlgebraic ℚ Ω) y h)
  exact isAlgebraic_algebraMap (R := kbar k Ω) (⟨y, hy'⟩ : kbar k Ω)

/-- **`F_NF` is a function field of one variable over `k̄_NF`** (`Z_NF` is a curve over
`k̄_NF`). -/
theorem isFunctionField_fnf : IsFunctionField (algebraicClosure ℚ Ω) (fnf N) := by
  classical
  obtain ⟨y, hy, hyt⟩ := N.exists_transcendental
  obtain ⟨n, b, hbF, -, hspan, -⟩ := N.exists_basis hy hyt
  set Q := algebraicClosure ℚ Ω
  let y' : fnf N := ⟨y, hy⟩
  refine ⟨⟨y', fun h => transcendental_algebraicClosure hyt (h.algHom (fnf N).val), ?_⟩⟩
  let b' : Fin n → fnf N := fun i => ⟨b i, hbF i⟩
  have hmap : (IntermediateField.adjoin Q {y'}).map (fnf N).val =
      IntermediateField.adjoin Q {y} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have htop : Submodule.span (IntermediateField.adjoin Q {y'}) (Set.range b') = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan z z.2)
    have hex : ∀ i, ∃ a : IntermediateField.adjoin Q {y'}, ((a : fnf N) : Ω) = c i := fun i => by
      have : (c i : Ω) ∈ (IntermediateField.adjoin Q {y'}).map (fnf N).val := by
        rw [hmap]; exact (c i).2
      obtain ⟨a, ha, he⟩ := this
      exact ⟨⟨a, ha⟩, he⟩
    choose a ha using hex
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨a, Subtype.ext ?_⟩
    rw [← hc, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ((a i : fnf N) : Ω) * b i = (c i : Ω) * b i
    rw [ha i]
  exact ⟨htop ▸ Submodule.fg_span (Set.finite_range b')⟩

attribute [local instance] isFunctionField_fnf

variable [IsAlgClosed Ω]

/-- `k̄_NF` is algebraically closed. -/
theorem isAlgClosed_algebraicClosure : IsAlgClosed (algebraicClosure ℚ Ω) :=
  (algebraicClosure.isAlgClosure (F := ℚ) (E := Ω)).isAlgClosed

attribute [local instance] isAlgClosed_algebraicClosure

/-- **The triple of [AbsTopIII] Prop 1.3 (a)–(c) for the NF-portion** `K_{Z_NF} = F_NF`:
`(F_NF^×, {ord_x}_{x ∈ Z_NF(k̄_NF)}, {U_x})`. -/
noncomputable abbrev nfTriple : Uchida.ValEvalData.{u} :=
  Uchida.ofFunctionField (algebraicClosure ℚ Ω) (fnf N)

open Classical in
/-- **[AbsTopIII] Thm 1.9 (e), `K^×_{Z_NF} ⋃ {0}`**: for any triple `𝒟'` isomorphic to the triple
`(K^×_{Z_NF}, {ord_x}, {U_x})` of the NF-portion, Uchida's algorithm `AddRel` on `𝒟'` (transported
back along the isomorphism) is the addition of `K_{Z_NF} = F_NF`. -/
theorem nf_addRel_iso_iff {D' : Uchida.ValEvalData.{u}} (e : Uchida.ValEvalData.Iso (nfTriple N) D')
    (x y z : fnf N) :
    D'.AddRel (e.mapZ (WithZero.withZeroUnitsEquiv.symm x))
        (e.mapZ (WithZero.withZeroUnitsEquiv.symm y))
        (e.mapZ (WithZero.withZeroUnitsEquiv.symm z)) ↔ x + y = z :=
  by convert Uchida.ofFunctionField.addRel_iso_iff e x y z

/-- **[AbsTopIII] Thm 1.9 (e), `k̄_NF^× ⋃ {0}`**: the constants of any triple isomorphic to the
triple of the NF-portion are the images of `k̄_NF^×`, the NF-constants (algebraic numbers);
`AddRel` restricted to them is the addition of `k̄_NF` (`nf_addRel_iso_iff`). -/
theorem nf_mem_consts_iso_iff {D' : Uchida.ValEvalData.{u}}
    (e : Uchida.ValEvalData.Iso (nfTriple N) D') (c : (fnf N)ˣ) :
    e.φ c ∈ D'.consts ↔ IsAlgebraic ℚ (((c : fnf N) : Ω)) := by
  rw [e.mem_consts_iff, Uchida.ofFunctionField.mem_consts_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact mem_algebraicClosure_iff.1 a.2
  · intro h
    exact ⟨⟨_, mem_algebraicClosure_iff.2 h⟩, Subtype.ext rfl⟩

/-! ### Points of `Z_NF` from NF-points, and `ord` -/

variable {N} {W : ValuationSubring Ω}

omit [CharZero k] [CharZero Ω] [IsAlgClosed Ω] in
lemma mem_of_mem_kbar' (hk : ∀ c : k, algebraMap k Ω c ∈ W) {x : Ω} (hx : x ∈ kbar k Ω) :
    x ∈ W :=
  Curve.mem_of_isIntegral hk (mem_algebraicClosure_iff.1 hx).isIntegral

omit [IsAlgClosed Ω] in
lemma mem_of_mem_algebraicClosure (hk : ∀ c : k, algebraMap k Ω c ∈ W) {x : Ω}
    (hx : x ∈ algebraicClosure ℚ Ω) : x ∈ W :=
  mem_of_mem_kbar' hk (mem_kbar_of_isAlgebraic (mem_algebraicClosure_iff.1 hx))

/-- **The point of `Z_NF` below an NF-point** `W ⊇ k`: the place `W ∩ F_NF` of `F_NF / k̄_NF`. -/
def nfPlace (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) :
    Place (algebraicClosure ℚ Ω) (fnf N) :=
  ⟨W.comap (algebraMap (fnf N) Ω), by
    obtain ⟨g, hg, hgW⟩ := hW
    intro h
    have : (⟨g, hg⟩ : fnf N) ∈ W.comap (algebraMap (fnf N) Ω) := h ▸ ValuationSubring.mem_top _
    exact hgW this, fun c => mem_of_mem_algebraicClosure hk c.2⟩

/-- **The point of `X_{k̄}` below** `W ⊇ k` (if `W ∩ F k̄ ≠ F k̄`, e.g. for an NF-point): the
place `W ∩ F k̄` of `F k̄ / k̄`. -/
def barPlace (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) :
    Place (kbar k Ω) (F (baseChange D)) :=
  ⟨W.comap (algebraMap (F (baseChange D)) Ω), by
    obtain ⟨g, hg, hgW⟩ := hW
    intro h
    have : (⟨g, N.mem_F g hg⟩ : F (baseChange D)) ∈ W.comap (algebraMap (F (baseChange D)) Ω) :=
      h ▸ ValuationSubring.mem_top _
    exact hgW this, fun c => mem_of_mem_kbar' hk c.2⟩

omit [CharZero Ω] [IsAlgClosed Ω] in
/-- For a place `P` cut out by `W` along `φ`, `ord_P` is read off from the valuation of `W`. -/
lemma Place.ord_le_ord_iff {κ K : Type*} [Field κ] [Field K] [Algebra κ K] [IsFunctionField κ K]
    [PerfectField κ] (P : Place κ K) (φ : K →+* Ω) (hP : P.1 = W.comap φ) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : P.ord x ≤ P.ord y ↔ W.valuation (φ y) ≤ W.valuation (φ x) := by
  have hφx : φ x ≠ 0 := (map_ne_zero_iff φ φ.injective).2 hx
  have h1 : P.ord x ≤ P.ord y ↔ y / x ∈ P.1 := by
    rw [← sub_nonneg, ← P.ord_div hy hx]
    constructor
    · intro h
      by_contra hn
      exact absurd ((P.ord_neg_iff).2 hn) (not_lt.2 h)
    · exact P.ord_nonneg_of_mem
  rw [h1, hP, ValuationSubring.mem_comap, map_div₀, ← W.valuation_le_one_iff, map_div₀,
    div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hφx))]

/-- **Gauss lemma, values**: at an NF-point `W ⊇ k`, every nonzero element of
`Subring.closure (F_NF ∪ k̄)` has the `W`-value of a nonzero NF-rational function. -/
theorem exists_valuation_eq_of_mem_closure (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) {r : Ω}
    (hr : r ∈ Subring.closure ((N.FNF : Set Ω) ∪ kbar k Ω)) (hr0 : r ≠ 0) :
    ∃ a ∈ N.FNF, a ≠ 0 ∧ W.valuation r = W.valuation a := by
  classical
  have hle : Subring.closure ((N.FNF : Set Ω) ∪ kbar k Ω) ≤
      (Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (hx | hx)
    · exact Algebra.subset_adjoin hx
    · exact (Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω)).algebraMap_mem ⟨x, hx⟩
  have hspan : r ∈ Submodule.span (kbar k Ω) (N.FNF : Set Ω) := by
    have h2 : r ∈ Subalgebra.toSubmodule (Algebra.adjoin (kbar k Ω) (N.FNF : Set Ω)) := hle hr
    rw [Algebra.adjoin_eq_span] at h2
    have h3 : Submonoid.closure (N.FNF : Set Ω) = N.FNF.toSubmonoid :=
      Submonoid.closure_eq N.FNF.toSubmonoid
    rw [h3] at h2
    exact h2
  obtain ⟨T, hTF, hT⟩ := Submodule.mem_span_finite_of_mem_span hspan
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hT
  set C : Finset Ω := T.image fun a => (f a : Ω)
  have hrC : r ∈ Submodule.span N.FNF (C : Set Ω) := by
    rw [← hf]
    refine Submodule.sum_mem _ fun a ha => ?_
    have e : f a • a = (⟨a, hTF ha⟩ : N.FNF) • (f a : Ω) := by
      rw [Algebra.smul_def, Subfield.smul_def, mul_comm]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ ha))
  obtain ⟨B, hBC, hBsp, hBli⟩ := exists_linearIndependent N.FNF (C : Set Ω)
  have hrB : r ∈ Submodule.span N.FNF B := hBsp ▸ hrC
  haveI : Fintype B := (C.finite_toSet.subset hBC).fintype
  obtain ⟨g, hg⟩ := Submodule.mem_span_iff_of_fintype.1 hrB
  set c : B → Ω := Subtype.val
  set a : B → Ω := fun b => (g b : Ω)
  have hc : ∀ b, c b ∈ kbar k Ω := by
    intro b
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (hBC b.2)
    change (b : Ω) ∈ kbar k Ω
    rw [← hx]
    exact (f x).2
  have ha : ∀ b, a b ∈ N.FNF := fun b => (g b).2
  have hli : LinearIndependent (algebraicClosure ℚ Ω) c := by
    rw [linearIndependent_iff'] at hBli ⊢
    intro s μ hμ i hi
    have := hBli s (fun j => ⟨μ j, N.algebraic_mem _ (mem_algebraicClosure_iff.1 (μ j).2)⟩)
      (by
        rw [← hμ]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Subfield.smul_def, Algebra.smul_def]
        rfl) i hi
    have h1 : ((μ i : algebraicClosure ℚ Ω) : Ω) = 0 := congrArg Subtype.val this
    exact Subtype.ext h1
  have hsum : r = ∑ b, c b * a b := by
    rw [← hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  have hne : Nonempty B := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hr0 (by rw [hsum]; exact Finset.sum_of_isEmpty _)
  obtain ⟨b₀, hb₀⟩ := Finite.exists_max fun b => W.valuation (a b)
  have hge := N.valuation_le_valuation_sum hk hW c hc hli a ha b₀
  rw [← hsum] at hge
  have hle' : W.valuation r ≤ W.valuation (a b₀) := by
    rw [hsum]
    refine Valuation.map_sum_le _ fun b _ => ?_
    rw [map_mul]
    exact le_trans (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).2
      (mem_of_mem_kbar' hk (hc b)))) (hb₀ b)
  refine ⟨a b₀, ha b₀, fun h0 => hr0 ?_, le_antisymm hle' hge⟩
  have : W.valuation r = 0 := by
    rw [h0, map_zero] at hle'
    exact le_antisymm hle' zero_le
  exact (Valuation.zero_iff _).1 this

/-- **Every value of `W` on `F k̄` is a value on `F_NF`** (NF-point `W ⊇ k`): for `b ∈ F k̄`,
`b ≠ 0`, there is a nonzero NF-rational function with the same `W`-value. -/
theorem exists_valuation_eq_fnf (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {b : Ω}
    (hb : b ∈ F (baseChange D))
    (hb0 : b ≠ 0) : ∃ a ∈ N.FNF, a ≠ 0 ∧ W.valuation b = W.valuation a := by
  obtain ⟨r, hr, s, hs, rfl⟩ := Subfield.mem_closure_iff.1 (N.mem_closure b hb)
  have hs0 : s ≠ 0 := fun h => hb0 (by rw [h, div_zero])
  have hr0 : r ≠ 0 := fun h => hb0 (by rw [h, zero_div])
  obtain ⟨a₁, ha₁, ha₁0, h₁⟩ := exists_valuation_eq_of_mem_closure hk hW hr hr0
  obtain ⟨a₂, ha₂, ha₂0, h₂⟩ := exists_valuation_eq_of_mem_closure hk hW hs hs0
  exact ⟨a₁ / a₂, N.FNF.div_mem ha₁ ha₂, div_ne_zero ha₁0 ha₂0, by
    rw [map_div₀, map_div₀, h₁, h₂]⟩

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- The inclusion `F_NF ⊆ F k̄`. -/
def fnfToBar (f : fnf N) : F (baseChange D) := ⟨f, N.mem_F f f.2⟩

omit [IsAlgClosed Ω] in
lemma fnfToBar_ne_zero {f : fnf N} (hf : f ≠ 0) : fnfToBar f ≠ 0 := fun h =>
  hf (Subtype.ext (congrArg Subtype.val h :))

omit [IsAlgClosed Ω] in
/-- `ord` at an NF-point is monotone-compatible between `F_NF` and `F k̄`. -/
lemma ord_le_ord_iff_bar (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {x y : fnf N}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (nfPlace hk hW).ord x ≤ (nfPlace hk hW).ord y ↔
      (barPlace hk hW).ord (fnfToBar x) ≤ (barPlace hk hW).ord (fnfToBar y) := by
  rw [Place.ord_le_ord_iff (nfPlace hk hW) (algebraMap (fnf N) Ω) rfl hx hy,
    Place.ord_le_ord_iff (barPlace hk hW) (algebraMap (F (baseChange D)) Ω) rfl
      (fnfToBar_ne_zero hx) (fnfToBar_ne_zero hy)]
  rfl

omit [IsAlgClosed Ω] in
lemma ord_eq_ord_iff_bar (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) {x y : fnf N}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (nfPlace hk hW).ord x = (nfPlace hk hW).ord y ↔
      (barPlace hk hW).ord (fnfToBar x) = (barPlace hk hW).ord (fnfToBar y) := by
  rw [le_antisymm_iff, le_antisymm_iff, ord_le_ord_iff_bar hk hW hx hy,
    ord_le_ord_iff_bar hk hW hy hx]

/-- **`ord` at an NF-point computed in `F_NF` equals `ord` computed in `F k̄`**: the extension of
constants `Z_NF ×_{k̄_NF} k̄ → Z_NF` is unramified at NF-points (the value groups agree by
`exists_valuation_eq_fnf`). -/
theorem ord_nfPlace (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W) (f : fnf N) :
    (barPlace hk hW).ord (fnfToBar f) = (nfPlace hk hW).ord f := by
  set P := nfPlace hk hW
  set Q := barPlace hk hW
  by_cases hf : f = 0
  · subst hf
    rw [P.ord_zero, show fnfToBar (0 : fnf N) = 0 from rfl, Q.ord_zero]
  -- a uniformiser of `P` and the index `e = ord_Q(π)`
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := fun h => by rw [h, P.ord_zero] at hπ; exact zero_ne_one hπ
  have hpow : ∀ m : ℤ, π ^ m ≠ 0 := fun m => zpow_ne_zero m hπ0
  have hQpow : ∀ m : ℤ, Q.ord (fnfToBar (π ^ m)) = m * Q.ord (fnfToBar π) := fun m => by
    rw [show fnfToBar (π ^ m) = fnfToBar π ^ m from rfl, Q.ord_zpow]
  have hgen : ∀ x : fnf N, x ≠ 0 → Q.ord (fnfToBar x) = P.ord x * Q.ord (fnfToBar π) := by
    intro x hx
    have h := (ord_eq_ord_iff_bar hk hW hx (hpow (P.ord x))).1 (by
      rw [P.ord_zpow, hπ, mul_one])
    rw [h, hQpow]
  -- `e = 1`
  obtain ⟨ϖ, hϖ⟩ := Q.exists_ord_eq_one
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, Q.ord_zero] at hϖ; exact zero_ne_one hϖ
  have hϖ0' : (ϖ : Ω) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  obtain ⟨a, haF, ha0, hva⟩ := exists_valuation_eq_fnf hk hW ϖ.2 hϖ0'
  set a' : fnf N := ⟨a, haF⟩
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg Subtype.val h :)
  have hQa : Q.ord (fnfToBar a') = 1 := by
    rw [← hϖ]
    refine le_antisymm ?_ ?_
    · rw [Place.ord_le_ord_iff Q (algebraMap (F (baseChange D)) Ω) rfl
        (fnfToBar_ne_zero ha'0) hϖ0]
      exact le_of_eq hva
    · rw [Place.ord_le_ord_iff Q (algebraMap (F (baseChange D)) Ω) rfl hϖ0
        (fnfToBar_ne_zero ha'0)]
      exact le_of_eq hva.symm
  have he1 : P.ord a' * Q.ord (fnfToBar π) = 1 := by rw [← hgen a' ha'0, hQa]
  have hepos : 0 < Q.ord (fnfToBar π) := by
    have h1 : P.ord 1 < P.ord π := by rw [P.ord_one, hπ]; exact one_pos
    have h2 := (ord_le_ord_iff_bar hk hW hπ0 one_ne_zero).not.1 (not_le.2 h1)
    rw [not_le, show fnfToBar (1 : fnf N) = 1 from rfl, Q.ord_one] at h2
    exact h2
  have he : Q.ord (fnfToBar π) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one ((mul_comm _ _).trans he1) with h | h
    · exact h
    · omega
  rw [hgen f hf, he, mul_one]

end Iut.Reconstruction.Thm19

end
