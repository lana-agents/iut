/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFDirectLimit
import Iut.Reconstruction.Thm19.NFEval
import Iut.Reconstruction.Thm19.CuspPrincipal

/-!
# [AbsTopIII] Thm 1.9 (d), (e) assembled: the reconstructed NF-portion `recFunctionField`

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) reconstructs
"the NF-portion of the function field" of `X`: step (d) (l.2158–2178) embeds `K^×_{Z_NF}` into
`lim→_V H¹(Π_V, μ_Ẑ(Π_U))` by the Kummer map, and step (e) (l.2179–2185) applies "the functorial
algorithm of Proposition 1.3 to the data of the form described in Proposition 1.3, (a), (b), (c),
arising from the construction of (d) [cf. also the decomposition groups of (a), the isomorphisms
of (b)]". Here, for the Galois model `D` of a curve over a number field `k` with NF-model `N`:

* `kummerNFRange N hkF ⊆ H1Lim D`: the image of `K^×_{Z_NF}` in `lim→_V H¹(Π_V, Ẑ(1))`
  (`Thm19/NFDirectLimit.lean`), and `kummerNFEquiv : K^×_{Z_NF} ≃* kummerNFRange`;
* **`recTriple N hkF`**: the triple of Prop 1.3 (a)–(c) on the Kummer classes (the group
  `kummerNFRange`, the points of `Z_NF`, `ord_x` and `U_x` carried over by the Kummer map), and
  **`recIso : nfTriple N ≅ recTriple N hkF`**;
* **`recFunctionField N hkF`**: `kummerNFRange ∪ {0}` with the multiplication of the classes and
  the addition computed by Uchida's algorithm (`Uchida.ValEvalData.AddRel`):
  **`recFunctionField_add_eq_iff`** (`a + b = c ↔ AddRel a b c`, Thm 1.9 (e)) and
  **`recFunctionFieldEquiv : K_{Z_NF} ≃+* recFunctionField`** (the Kummer map, extended by `0`);
* **`ringEquivOfIso`**: every isomorphism of triples `recTriple N ≅ recTriple N'` (e.g. one induced
  by an isomorphism of the fundamental groups that respects the data of (a)–(d)) is additive, so
  it induces a field isomorphism `K_{Z_NF} ≃+* K_{Z'_NF}` (the functoriality of Thm 1.9);
* **`kummerNF_eq_mk`**: the class of `f` in the colimit is `[V, κ_V(v)]` at every stage `V` on
  which `f` is a unit `v`;
* **`mem_U_recTriple_iff`** (Thm 1.9 (e) with (a)): at an NF-point `x` which is a closed point of
  a stage `V`, the class of `f` lies in `U_x` iff its restriction `s_x^* κ_V(f)` to the
  decomposition group of `x` is trivial (`Thm19/NFEval.lean`), so the subgroups `U_x` of the
  triple are read off from the Kummer classes and the decomposition groups.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

section Rec

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

/-- **`K^×_{Z_NF}` inside `lim→_V H¹(Π_V, Ẑ(1))`**: the image of the Kummer map. -/
abbrev kummerNFRange : Subgroup (H1Lim D) := (kummerNF N hkF).range

/-- The Kummer map onto its image ([AbsTopIII] Thm 1.9 (d)). -/
def kummerNFEquiv : (fnf N)ˣ ≃* kummerNFRange N hkF :=
  MonoidHom.ofInjective (kummerNF_injective N hkF)

@[simp] lemma coe_kummerNFEquiv (f : (fnf N)ˣ) :
    ((kummerNFEquiv N hkF f : kummerNFRange N hkF) : H1Lim D) = kummerNF N hkF f :=
  MonoidHom.ofInjective_apply _

/-- **The reconstructed triple of [AbsTopIII] Prop 1.3 (a)–(c)** on the Kummer classes of the
NF-rational functions: the group `kummerNFRange ⊆ lim→_V H¹(Π_V, Ẑ(1))`, the points of `Z_NF`,
and `ord_x`, `U_x` carried over by the Kummer map. -/
def recTriple : Uchida.ValEvalData.{u} where
  G := kummerNFRange N hkF
  P := Place (algebraicClosure ℚ Ω) (fnf N)
  ord x := ((nfTriple N).ord x).comp (kummerNFEquiv N hkF).symm.toMonoidHom
  U x := ((nfTriple N).U x).map (kummerNFEquiv N hkF).toMonoidHom

/-- **The reconstructed triple is the triple of the NF-portion** (via the Kummer map). -/
def recIso : (nfTriple N).Iso (recTriple N hkF) where
  φ := kummerNFEquiv N hkF
  σ := Equiv.refl _
  ord_eq x f := by
    change ((nfTriple N).ord x) ((kummerNFEquiv N hkF).symm (kummerNFEquiv N hkF f)) = _
    rw [MulEquiv.symm_apply_apply]
  mem_U_iff x f := by
    change kummerNFEquiv N hkF f ∈ ((nfTriple N).U x).map (kummerNFEquiv N hkF).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

lemma recIso_φ (f : (fnf N)ˣ) : (recIso N hkF).φ f = kummerNFEquiv N hkF f := rfl

/-- **The reconstructed NF-portion** `kummerNFRange ∪ {0}` ([AbsTopIII] Thm 1.9 (e)), with the
field structure for which multiplication is that of the Kummer classes
(`recFunctionField_mul`) and addition is the one computed by Uchida's algorithm
(`recFunctionField_add_eq_iff`). -/
def recFunctionField : Type u := WithZero (recTriple N hkF).G

open Classical in
/-- The NF-portion `K_{Z_NF} = F_NF` onto `kummerNFRange ∪ {0}`: the Kummer map extended by `0`. -/
def recEquiv : fnf N ≃ recFunctionField N hkF :=
  WithZero.withZeroUnitsEquiv.symm.toEquiv.trans (recIso N hkF).mapZ.toEquiv

open Classical in
lemma recEquiv_apply (x : fnf N) :
    recEquiv N hkF x = (recIso N hkF).mapZ (WithZero.withZeroUnitsEquiv.symm x) := rfl

instance : Field (recFunctionField N hkF) := (recEquiv N hkF).symm.field

/-- `K_{Z_NF} ≃+* recFunctionField`: the Kummer map extended by `0`. -/
def recFunctionFieldEquiv : fnf N ≃+* recFunctionField N hkF where
  toEquiv := recEquiv N hkF
  map_mul' x y := by
    change _ = recEquiv N hkF ((recEquiv N hkF).symm (recEquiv N hkF x) *
      (recEquiv N hkF).symm (recEquiv N hkF y))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  map_add' x y := by
    change _ = recEquiv N hkF ((recEquiv N hkF).symm (recEquiv N hkF x) +
      (recEquiv N hkF).symm (recEquiv N hkF y))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl

lemma recFunctionFieldEquiv_apply (x : fnf N) :
    recFunctionFieldEquiv N hkF x = recEquiv N hkF x := rfl

/-- An element of `recFunctionField` as an element of `kummerNFRange ∪ {0}`. -/
def toWZ : recFunctionField N hkF ≃ WithZero (recTriple N hkF).G := Equiv.refl _

/-- **The multiplication of `recFunctionField` is that of the Kummer classes** (of `WithZero`). -/
lemma recFunctionField_mul (a b : recFunctionField N hkF) :
    toWZ N hkF (a * b) = toWZ N hkF a * toWZ N hkF b := by
  obtain ⟨x, rfl⟩ := (recEquiv N hkF).surjective a
  obtain ⟨y, rfl⟩ := (recEquiv N hkF).surjective b
  change toWZ N hkF (recEquiv N hkF ((recEquiv N hkF).symm (recEquiv N hkF x) *
    (recEquiv N hkF).symm (recEquiv N hkF y))) = toWZ N hkF (recEquiv N hkF x) *
      toWZ N hkF (recEquiv N hkF y)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, recEquiv_apply, recEquiv_apply,
    recEquiv_apply, map_mul, map_mul]
  rfl

/-- **[AbsTopIII] Thm 1.9 (e): the addition of `recFunctionField` is computed by Uchida's
algorithm** on the reconstructed triple. -/
theorem recFunctionField_add_eq_iff (a b c : recFunctionField N hkF) :
    a + b = c ↔ (recTriple N hkF).AddRel a b c := by
  obtain ⟨x, rfl⟩ := (recEquiv N hkF).surjective a
  obtain ⟨y, rfl⟩ := (recEquiv N hkF).surjective b
  obtain ⟨z, rfl⟩ := (recEquiv N hkF).surjective c
  have hx := recEquiv_apply N hkF x
  have hy := recEquiv_apply N hkF y
  have hz := recEquiv_apply N hkF z
  have e := nf_addRel_iso_iff N (recIso N hkF) x y z
  rw [← hx, ← hy, ← hz] at e
  rw [e]
  constructor
  · intro h
    apply (recEquiv N hkF).injective
    rw [← h]
    exact (recFunctionFieldEquiv N hkF).map_add x y
  · rintro rfl
    exact ((recFunctionFieldEquiv N hkF).map_add x y).symm

/-! ### The Kummer classes at the stages, and `U_x` from the decomposition groups -/

/-- The class of `f` in `lim→_V Γ(V, 𝒪^×)` is `[V, v]` at every stage `V` on which `f` is a unit
`v`. -/
lemma nfToLim_eq_mk (f : (fnf N)ˣ) (s : StageIdx D) (v : US D s)
    (hv : (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω)) :
    nfToLim N hkF f = UnitsLim.mk s v :=
  coeLim_injective D (by
    rw [coeLim_nfToLim, coeLim_mk]
    exact Units.ext hv.symm)

/-- **The Kummer class of an NF-rational function in the colimit** is `[V, κ_V(v)]` at every
stage `V` on which `f` is a unit `v`. -/
lemma kummerNF_eq_mk (f : (fnf N)ˣ) (s : StageIdx D) (v : US D s)
    (hv : (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω)) :
    kummerNF N hkF f = H1Lim.mk s (kummerMapZHat s.data v) := by
  change kummerLim D (nfToLim N hkF f) = _
  rw [nfToLim_eq_mk N hkF f s v hv]
  exact kummerLim_mk D s v

set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(W)/k_x)` on `Ẑ(1)_{k_x}` is found slowly (coercion of `k_x` to a type)
/-- **[AbsTopIII] Thm 1.9 (e), the subgroups `U_x` of the reconstructed triple from the
decomposition groups of (a)**: let `W` be an NF-point which is a closed point of a stage `V`
(`K ⊆ W`, `t′ ∈ W`, residue field `k_x` finite over `K`) on which the NF-rational function `f`
is a unit `v`. Then the class of `f` lies in `U_x` iff the restriction `s_x^* κ_V(v)` of its
Kummer class to the decomposition group of `x` is trivial. (`hu`, `hu'`: `v` is a unit at `x`, as
every unit of `V` at a point of `V`, `units_mem`.) -/
theorem mem_U_recTriple_iff (f : (fnf N)ˣ) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W)
    (s : StageIdx D) (v : US D s)
    (hv : (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω))
    (hkW : ∀ c : s.K, algebraMap s.K Ω c ∈ W) [Algebra s.K (ResidueField W)]
    (hkres : ∀ c : s.K,
      residue W ⟨algebraMap s.K Ω c, hkW c⟩ = algebraMap s.K (ResidueField W) c)
    [Algebra.IsIntegral s.K (ResidueField W)] (ht : s.t' ∈ W)
    [FiniteDimensional s.K (Decomposition.pointField (F s.data) W hkW hkres)]
    (hu : (((v : (F s.data)ˣ) : F s.data) : Ω) ∈ W)
    (hu' : ((((v : (F s.data)ˣ)⁻¹ : (F s.data)ˣ) : F s.data) : Ω) ∈ W) :
    kummerNFEquiv N hkF f ∈ (recTriple N hkF).U (nfPlace hk hW) ↔
      restrictClosed s.data W hkW hkres rfl ht (kummerMapZHat s.data v) = 1 := by
  haveI : NumberField s.K := NumberField.of_module_finite k s.K
  have h3 := restrictClosed_kummerMapZHat_eq_one_iff_valuation s.data W hkW hkres rfl ht
    (NumberField.isTorallyKummerFaithful s.K) v hu hu'
  have h4 : W.valuation (((f : fnf N) : Ω) - 1) < 1 ↔
      W.valuation ((((v : (F s.data)ˣ) : F s.data) : Ω) - 1) < 1 := by
    rw [hv]
  exact ((recIso N hkF).mem_U_iff (nfPlace hk hW) f).trans
    ((mem_U_nfTriple_iff hk hW f).trans (h4.trans h3.symm))

/-! ### `ord_x` from the residues at the inertia groups -/

/-- **The function field of a stage lies in `F k̄`** (`V ⊆ U_K`, `K ⊆ k̄`). -/
lemma mem_F_baseChange_of_stage (s : StageIdx D) {x : Ω} (hx : x ∈ F s.data) :
    x ∈ F (baseChange D) := by
  have hxL := (mem_F_stage_iff D s.K s.ht' s.htr').1 hx
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact (mem_L_constExt_iff D s.K).1 hxL (resK₀ k t σ)
    ((Fact.out : D.H ≤ D.HL) ((mem_baseChange_H D).1 hσ))
    (fun c => σ.commutes ⟨_, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, algebraMap_mem_kbar c⟩⟩)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [Fact (D.H ≤ D.HL)]
  [NumberField k] in
/-- For a place cut out by `W`, two nonzero elements have the same `ord` iff the same value. -/
lemma ord_eq_ord_iff_val {κ L : Type*} [Field κ] [Field L] [Algebra κ L] [IsFunctionField κ L]
    [PerfectField κ] {W : ValuationSubring Ω} (P : Place κ L) (φ : L →+* Ω)
    (hP : P.1 = W.comap φ) {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    P.ord x = P.ord y ↔ W.valuation (φ x) = W.valuation (φ y) := by
  rw [le_antisymm_iff, le_antisymm_iff, Place.ord_le_ord_iff P φ hP hx hy,
    Place.ord_le_ord_iff P φ hP hy hx, and_comm]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] [CharZero Ω] [Fact (D.H ≤ D.HL)]
  [NumberField k] in
/-- `v(x) = v(π)^n` for `ord x = n`, `ord π = 1`. -/
lemma val_eq_zpow_of_ord {κ L : Type*} [Field κ] [Field L] [Algebra κ L] [IsFunctionField κ L]
    [PerfectField κ] {W : ValuationSubring Ω} (P : Place κ L) (φ : L →+* Ω)
    (hP : P.1 = W.comap φ) {x π : L} (hx : x ≠ 0) (hπ : P.ord π = 1) :
    W.valuation (φ x) = W.valuation (φ π) ^ P.ord x := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, P.ord_zero] at hπ; exact zero_ne_one hπ
  have h := (ord_eq_ord_iff_val P φ hP hx (zpow_ne_zero (P.ord x) hπ0)).1
    (by rw [P.ord_zpow, hπ, mul_one])
  rw [h, map_zpow₀, map_zpow₀]

/-- **A uniformiser at an NF-point is a uniformiser on every stage containing it**: the
extensions of constants `Z_NF ×_{k̄_NF} k̄ ⊇ Z_NF` and `V_{k̄} ⊇ V` are unramified at the point
(every value of `W` on `F k̄` is a value on `F_NF`, `exists_valuation_eq_fnf`). -/
theorem ord_stage_eq_one {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) (s : StageIdx D) (P : Place s.K (F s.data))
    (hP : P.1 = W.comap (algebraMap (F s.data) Ω)) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F s.data) :
    P.ord (⟨π, hπs⟩ : F s.data) = 1 := by
  set Q := nfPlace hk hW
  have hQ : Q.1 = W.comap (algebraMap (fnf N) Ω) := rfl
  set π' : F s.data := ⟨π, hπs⟩
  have hπ0 : π ≠ 0 := fun h => by rw [h, Q.ord_zero] at hπ; exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := fun h => hπ0 (Subtype.ext (congrArg Subtype.val h :))
  obtain ⟨ϖ, hϖ⟩ := P.exists_ord_eq_one
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, P.ord_zero] at hϖ; exact zero_ne_one hϖ
  have hϖ0' : (ϖ : Ω) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  obtain ⟨a, haF, ha0, hva⟩ :=
    exists_valuation_eq_fnf hk hW (mem_F_baseChange_of_stage s ϖ.2) hϖ0'
  set a' : fnf N := ⟨a, haF⟩
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg Subtype.val h :)
  have h1 : W.valuation a = W.valuation (π : Ω) ^ Q.ord a' :=
    val_eq_zpow_of_ord Q (algebraMap (fnf N) Ω) hQ ha'0 hπ
  have h2 : W.valuation (π : Ω) = W.valuation (ϖ : Ω) ^ P.ord π' :=
    val_eq_zpow_of_ord P (algebraMap (F s.data) Ω) hP hπ'0 hϖ
  have h3 : P.ord ϖ = P.ord (ϖ ^ (P.ord π' * Q.ord a')) := by
    refine (ord_eq_ord_iff_val P (algebraMap (F s.data) Ω) hP hϖ0 (zpow_ne_zero _ hϖ0)).2 ?_
    rw [map_zpow₀, map_zpow₀, zpow_mul]
    change W.valuation (ϖ : Ω) = (W.valuation (ϖ : Ω) ^ P.ord π') ^ Q.ord a'
    rw [← h2, ← h1]
    exact hva
  rw [P.ord_zpow, hϖ, mul_one] at h3
  have hm : 0 ≤ P.ord π' := by
    refine P.ord_nonneg_of_mem ?_
    rw [hP]
    have : π ∈ Q.1 := Q.mem_of_ord_nonneg (by rw [hπ]; exact zero_le_one)
    exact this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h3.symm with h | h
  · exact h
  · omega

/-- **`ord` at an NF-point computed on a stage is `ord_x` of `Z_NF`**, for every stage whose
function field contains a uniformiser of `Z_NF` at `x`. -/
theorem ord_stage_eq_ord_nf {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (hW : N.IsNFPoint W) (s : StageIdx D) (P : Place s.K (F s.data))
    (hP : P.1 = W.comap (algebraMap (F s.data) Ω)) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F s.data) {y : F s.data} {g : fnf N}
    (hyg : (y : Ω) = (g : Ω)) (hg : g ≠ 0) :
    P.ord y = (nfPlace hk hW).ord g := by
  set Q := nfPlace hk hW
  have hQ : Q.1 = W.comap (algebraMap (fnf N) Ω) := rfl
  have hy0 : y ≠ 0 := fun h => hg (Subtype.ext (by rw [← hyg, h]; rfl))
  have hπ0 : π ≠ 0 := fun h => by rw [h, Q.ord_zero] at hπ; exact zero_ne_one hπ
  have hπ'0 : (⟨π, hπs⟩ : F s.data) ≠ 0 := fun h => hπ0 (Subtype.ext (congrArg Subtype.val h :))
  have h1 := val_eq_zpow_of_ord Q (algebraMap (fnf N) Ω) hQ hg hπ
  have h2 : P.ord y = P.ord ((⟨π, hπs⟩ : F s.data) ^ Q.ord g) := by
    refine (ord_eq_ord_iff_val P (algebraMap (F s.data) Ω) hP hy0 (zpow_ne_zero _ hπ'0)).2 ?_
    rw [map_zpow₀, map_zpow₀]
    change W.valuation (y : Ω) = W.valuation (π : Ω) ^ Q.ord g
    rw [hyg]
    exact h1
  rw [h2, P.ord_zpow, ord_stage_eq_one N hk hW s P hP π hπ hπs, mul_one]

/-- **[AbsTopIII] Thm 1.9 (b), (c), (e): `ord_x` of the reconstructed triple from the residues**:
let `f` be an NF-rational function which is a unit `v` on a stage `V`, `W` an NF-point (e.g. a
cusp of `V`, where `x` has been removed) with `K ⊆ W`, and `p = (W, σ)` an inertia index of `V`
at `W` (`σ ∈ I_W ∩ H`). If the function field of `V` contains a uniformiser of `Z_NF` at `x`,
then the residue of the Kummer class `κ_V(v)` at `p` is `θ_p^{ord_x(f)}`, `θ_p` the tame
generator at `p`, with `ord_x` the valuation of the reconstructed triple. -/
theorem res_kummerMapZHat_eq_tameGen_zpow (f : (fnf N)ˣ) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (hW : N.IsNFPoint W)
    (s : StageIdx D) (v : US D s)
    (hv : (((v : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω))
    (p : InertiaIndex s.data) (hpW : p.1.1 = W) (π : fnf N)
    (hπ : (nfPlace hk hW).ord π = 1) (hπs : (π : Ω) ∈ F s.data) :
    res s.data (kummerMapZHat s.data v) p =
      tameGen p ^ (recTriple N hkF).val (nfPlace hk hW) (kummerNFEquiv N hkF f) := by
  have hπ0 : π ≠ 0 := fun h => by
    rw [h, (nfPlace hk hW).ord_zero] at hπ; exact zero_ne_one hπ
  have hne : idxVal p ≠ ⊤ := by
    intro h
    have hmem : (⟨π, hπs⟩ : F s.data)⁻¹ ∈ idxVal p := h ▸ ValuationSubring.mem_top _
    have hmem' : π⁻¹ ∈ (nfPlace hk hW).1 := by
      change ((π⁻¹ : fnf N) : Ω) ∈ W
      rw [← hpW]
      exact hmem
    have := (nfPlace hk hW).ord_nonneg_of_mem hmem'
    rw [(nfPlace hk hW).ord_inv, hπ] at this
    omega
  rw [res_kummerMapZHat]
  congr 1
  rw [divAt, dif_pos hne, Divisor.div_apply]
  have hP : (idxPlace p hne).1 = W.comap (algebraMap (F s.data) Ω) := by
    rw [← hpW]
    rfl
  rw [ord_stage_eq_ord_nf N hk hW s (idxPlace p hne) hP π hπ hπs hv f.ne_zero]
  change _ = Multiplicative.toAdd ((nfTriple N).ord (nfPlace hk hW)
    ((kummerNFEquiv N hkF).symm (kummerNFEquiv N hkF f)))
  rw [MulEquiv.symm_apply_apply]
  rfl

end Rec

/-! ### Functoriality -/

section Functorial

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] [Fact (D'.H ≤ D'.HL)] [NumberField k'] (N' : NFModel D')
  (hkF' : ∀ x : F D', IsAlgebraic k' x → x ∈ Set.range (algebraMap k' (F D')))

/-- **[AbsTopIII] Thm 1.9, functoriality**: every isomorphism of reconstructed triples (the
Kummer classes in `lim→_V H¹(Π_V, Ẑ(1))` with their points, `ord_x` and `U_x`) is additive for
the field structures of `recFunctionField`, by the functoriality of Uchida's algorithm
(`Uchida.ValEvalData.Iso.addRel_iff`). -/
def recFunctionFieldIso (e : (recTriple N hkF).Iso (recTriple N' hkF')) :
    recFunctionField N hkF ≃+* recFunctionField N' hkF' where
  toEquiv := e.mapZ.toEquiv
  map_mul' a b := by
    apply (toWZ N' hkF').injective
    rw [recFunctionField_mul N' hkF']
    change e.mapZ (toWZ N hkF (a * b)) = e.mapZ (toWZ N hkF a) * e.mapZ (toWZ N hkF b)
    rw [recFunctionField_mul N hkF]
    exact e.mapZ.map_mul _ _
  map_add' a b := by
    have h := (recFunctionField_add_eq_iff N hkF a b (a + b)).1 rfl
    rw [← e.addRel_iff] at h
    exact ((recFunctionField_add_eq_iff N' hkF' _ _ _).2 h).symm

/-- **[AbsTopIII] Thm 1.9, functoriality, on the NF-portions**: an isomorphism of the reconstructed
triples induces a field isomorphism `K_{Z_NF} ≃+* K_{Z'_NF}` which is the given isomorphism on
the Kummer classes. -/
def ringEquivOfIso (e : (recTriple N hkF).Iso (recTriple N' hkF')) : fnf N ≃+* fnf N' :=
  (recFunctionFieldEquiv N hkF).trans
    ((recFunctionFieldIso N hkF N' hkF' e).trans (recFunctionFieldEquiv N' hkF').symm)

end Functorial

end Iut.Reconstruction.Thm19
