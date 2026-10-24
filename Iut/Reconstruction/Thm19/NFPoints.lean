/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFAdditive

/-!
# [AbsTopIII] Thm 1.9 (e): the points and the evaluation data of `Z_NF`

[AbsTopIII] Thm 1.9 (e) (`Topics in Absolute Anabelian Geometry III.txt` l.2179–2185) feeds the
triple of Prop 1.3 (a)–(c) for `K_{Z_NF}` into Uchida's algorithm. Its points (b) are the points
of `Z_NF` over `k̄_NF`, and its subgroups (c) are `U_x = {f | f(x) = 1}`. In the Galois model
(`NFModel D`, `F_NF ⊆ F k̄ ⊆ Ω`):

* `IsNFPlaceBar N Q`: the place `Q` of `F k̄ / k̄` is **an NF-point of `X_{k̄}`** (Def 1.7 (ii)),
  i.e. nontrivial on `F_NF` (the points of `X_{k̄}` with transcendental coordinates restrict to
  the trivial valuation of `F_NF`); `nfPlaceOfBar`: the point `Q ∩ F_NF` of `Z_NF`;
* **`nfPointEquiv N : {NF-points of X_{k̄}} ≃ {points of Z_NF}`** (`Place k̄_NF F_NF`), from
  `exists_nfPlace_eq` (surjectivity) and `barPlace_eq_of_nfPlace_eq` (injectivity);
* **`mem_U_nfTriple_iff`**: for an NF-point `W ⊇ k` of `Ω` and `f ∈ F_NF^×`, `f` lies in the
  subgroup `U_x` of the triple at `x = W ∩ F_NF` iff `v_W(f − 1) < 1`, i.e. iff `f(x) = 1` at the
  point of `X_{k̄}` (or of `Ω`) under `W` (`mem_U_nfTriple_iff_bar`): the evaluation data of
  (c) are read off at NF-points of `X_{k̄}`, where [AbsTopIII] Prop 1.8 (ii) computes them by
  restriction to the decomposition groups (`s_x^* κ_U(f) = κ(f(x))`);
* `ord_nfPointEquiv`: the valuations `ord_x` of the triple are those of `X_{k̄}` at the
  corresponding NF-points (`ord_nfPlace`).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

/-- `v(y) < 1` iff `y = 0` or `y⁻¹ ∉ A`. -/
lemma ValuationSubring.valuation_lt_one_iff_inv {K : Type*} [Field K] (A : ValuationSubring K)
    (y : K) : A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [← A.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2
    ((Valuation.ne_zero_iff _).2 hy))]
  simp [hy]

/-- `v_{W ∩ E}(y) < 1` iff `v_W(y) < 1`. -/
lemma ValuationSubring.valuation_comap_lt_one_iff {E K : Type*} [Field E] [Field K]
    (W : ValuationSubring K) (φ : E →+* K) (y : E) :
    (W.comap φ).valuation y < 1 ↔ W.valuation (φ y) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff_inv, ValuationSubring.valuation_lt_one_iff_inv,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff φ φ.injective]

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [IsAlgClosed Ω] (N : NFModel D)

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

/-- `F_NF ⊆ F k̄` as a ring homomorphism. -/
def fnfToBarHom : fnf N →+* F (baseChange D) where
  toFun := fnfToBar
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **An NF-point of `X_{k̄}`** ([AbsTopIII] Def 1.7 (ii)): a place of `F k̄ / k̄` nontrivial on
`F_NF`. -/
def IsNFPlaceBar (Q : Place (kbar k Ω) (F (baseChange D))) : Prop :=
  ∃ g : fnf N, fnfToBar g ∉ Q.1

variable {N}

/-- **The point of `Z_NF` under an NF-point `Q` of `X_{k̄}`**: `Q ∩ F_NF`. -/
def nfPlaceOfBar (Q : Place (kbar k Ω) (F (baseChange D))) (hQ : IsNFPlaceBar N Q) :
    Place (algebraicClosure ℚ Ω) (fnf N) :=
  ⟨Q.1.comap (fnfToBarHom N), fun h => by
    obtain ⟨g, hg⟩ := hQ
    have : g ∈ Q.1.comap (fnfToBarHom N) := h ▸ ValuationSubring.mem_top _
    exact hg this, fun c => by
    change fnfToBar (algebraMap (algebraicClosure ℚ Ω) (fnf N) c) ∈ Q.1
    have : fnfToBar (algebraMap (algebraicClosure ℚ Ω) (fnf N) c) =
        algebraMap (kbar k Ω) (F (baseChange D))
          ⟨(c : Ω), mem_kbar_of_isAlgebraic (mem_algebraicClosure_iff.1 c.2)⟩ := rfl
    rw [this]
    exact Q.algebraMap_mem _⟩

omit [IsAlgClosed Ω] in
/-- `barPlace` is an NF-point of `X_{k̄}`. -/
lemma isNFPlaceBar_barPlace {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) : IsNFPlaceBar N (barPlace hk hW) := by
  obtain ⟨g, hg, hgW⟩ := hW
  exact ⟨⟨g, hg⟩, hgW⟩

omit [IsAlgClosed Ω] in
lemma nfPlaceOfBar_barPlace {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) :
    nfPlaceOfBar (barPlace hk hW) (isNFPlaceBar_barPlace hk hW) = nfPlace hk hW :=
  Place.ext (by ext; rfl)

omit [IsAlgClosed Ω] in
/-- **Every NF-point of `X_{k̄}` is `barPlace` of an NF-point of `Ω`.** -/
lemma exists_barPlace_eq (Q : Place (kbar k Ω) (F (baseChange D))) (hQ : IsNFPlaceBar N Q) :
    ∃ (W : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W),
      barPlace hk hW = Q := by
  obtain ⟨W, hW⟩ := CurvesJacobian.exists_valuationSubring_liesOver (baseChange D) Q
  have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c => by
    have h := (hW (algebraMap (kbar k Ω) (F (baseChange D)) (algebraMap k (kbar k Ω) c))).2
      (Q.algebraMap_mem _)
    exact h
  obtain ⟨g, hg⟩ := hQ
  refine ⟨W, hk, ⟨g, g.2, fun h => hg ((hW (fnfToBar g)).1 h)⟩, Place.ext ?_⟩
  ext y
  exact hW y

variable (N) in
/-- **[AbsTopIII] Thm 1.9 (e), the points: the NF-points of `X_{k̄}` are the points of `Z_NF`**,
`Q ↦ Q ∩ F_NF` (surjective by `exists_nfPlace_eq`, injective by `barPlace_eq_of_nfPlace_eq`). -/
def nfPointEquiv :
    {Q : Place (kbar k Ω) (F (baseChange D)) // IsNFPlaceBar N Q} ≃
      Place (algebraicClosure ℚ Ω) (fnf N) where
  toFun Q := nfPlaceOfBar Q.1 Q.2
  invFun P := ⟨barPlace (exists_nfPlace_eq (N := N) P).choose_spec.choose
      (exists_nfPlace_eq (N := N) P).choose_spec.choose_spec.choose,
    isNFPlaceBar_barPlace _ _⟩
  left_inv Q := by
    obtain ⟨W, hk, hW, hQ⟩ := exists_barPlace_eq Q.1 Q.2
    obtain ⟨Q, hQ'⟩ := Q
    subst hQ
    apply Subtype.ext
    have h := (exists_nfPlace_eq (N := N)
      (nfPlaceOfBar (barPlace hk hW) hQ')).choose_spec.choose_spec.choose_spec
    exact barPlace_eq_of_nfPlace_eq _ _ _ _ (h.trans (nfPlaceOfBar_barPlace hk hW))
  right_inv P :=
    (nfPlaceOfBar_barPlace _ _).trans
      (exists_nfPlace_eq (N := N) P).choose_spec.choose_spec.choose_spec

lemma nfPointEquiv_barPlace {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) :
    nfPointEquiv N ⟨barPlace hk hW, isNFPlaceBar_barPlace hk hW⟩ = nfPlace hk hW := by
  change nfPlaceOfBar (barPlace hk hW) (isNFPlaceBar_barPlace hk hW) = _
  exact nfPlaceOfBar_barPlace hk hW

/-- **The valuations of the triple are those of `X_{k̄}`**: for an NF-point `Q` of `X_{k̄}` and
`f ∈ F_NF`, `ord` at the point `Q ∩ F_NF` of `Z_NF` is `ord_Q(f)` (`ord_nfPlace`). -/
theorem ord_nfPointEquiv (Q : {Q : Place (kbar k Ω) (F (baseChange D)) // IsNFPlaceBar N Q})
    (f : fnf N) : (nfPointEquiv N Q).ord f = Q.1.ord (fnfToBar f) := by
  obtain ⟨W, hk, hW, hQ⟩ := exists_barPlace_eq Q.1 Q.2
  obtain ⟨Q, hQ'⟩ := Q
  subst hQ
  rw [nfPointEquiv_barPlace, ord_nfPlace]

/-- **The subgroups `U_x` of the triple at NF-points**: `f ∈ U_x` (`f(x) = 1` on `Z_NF`) iff
`v_W(f − 1) < 1` for the NF-point `W` of `Ω` over `x`. -/
theorem mem_U_nfTriple_iff {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) (f : (fnf N)ˣ) :
    f ∈ (nfTriple N).U (nfPlace hk hW) ↔ W.valuation (((f : fnf N) : Ω) - 1) < 1 := by
  change f ∈ (nfPlace hk hW).1.principalUnitGroup ↔ _
  rw [ValuationSubring.mem_principalUnitGroup_iff]
  exact ValuationSubring.valuation_comap_lt_one_iff W (algebraMap (fnf N) Ω) _

/-- **The same at the NF-point of `X_{k̄}`**: `f ∈ U_x` iff `f(Q) = 1` at the point `Q` of
`X_{k̄}` over `x` (`f − 1` vanishes at `Q`). -/
theorem mem_U_nfTriple_iff_bar
    (Q : {Q : Place (kbar k Ω) (F (baseChange D)) // IsNFPlaceBar N Q}) (f : (fnf N)ˣ) :
    f ∈ (nfTriple N).U (nfPointEquiv N Q) ↔ Q.1.1.valuation (fnfToBar (f : fnf N) - 1) < 1 := by
  obtain ⟨W, hk, hW, hQ⟩ := exists_barPlace_eq Q.1 Q.2
  obtain ⟨Q, hQ'⟩ := Q
  subst hQ
  rw [nfPointEquiv_barPlace, mem_U_nfTriple_iff]
  exact (ValuationSubring.valuation_comap_lt_one_iff W (algebraMap (F (baseChange D)) Ω)
    (fnfToBar (f : fnf N) - 1)).symm

end Iut.Reconstruction.Thm19

end
