/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Uchida's lemma: the algorithm ([AbsTopIII], Propositions 1.1–1.3)

[AbsTopIII], Proposition 1.3 (l.1691–1721 of `~/iut-scratch/papers/txt/Topics in Absolute Anabelian
Geometry III.txt`; "implicit in the argument of [Uchi], §3, Lemmas 8-11"): "there exists a
functorial algorithm for constructing the additive structure on `K_X^× ∪ {0}` […] from the
following data:
(a) the [abstract!] group `K_X^×`; (b) the set of [surjective] homomorphisms
`V_X = {ord_x : K_X^× ↠ ℤ}_{x∈X(k)}` […]; (c) for each homomorphism `v = ord_x ∈ V_X`, the
subgroup `U_v ⊆ K_X^×` given by the `f ∈ K_X^×` such that `f(x) = 1`. Here, the term "functorial"
is with respect to isomorphisms [in the evident sense] of such triples".

This file is the **algorithm side** (MR9 step U1, `Plans/MR9Plan.md`): everything is defined from
the abstract triple `(G, {ord_x}, {U_x})` (`ValEvalData`), following the proof (l.1722–1743):

* `consts`: `k^× = ⋂_v Ker(v)`;
* `EvalAt x f c` ("`f(x) = c`"): `ord_x(f) = 0`, `c ∈ k^×` and `f·c⁻¹ ∈ U_x` (from
  `Ker(v) = U_v × k^×`);
* divisors `P →₀ ℤ`, `Gamma E = Γ^×(E) = {f | div(f) + E ≥ 0}`, and `ell E = l(E)` defined by
  the characterisation of Proposition 1.1(ii) (l.1655): "the smallest nonnegative integer `d` such
  that there exists an effective divisor `E` of degree `d` on `X` for which `Γ^×(D − E) = ∅`";
* `IsConfig` (Proposition 1.2(i), l.1660–1663), `IsBasisFn` (`f_{λ,i}`, 1.2(ii)) and `IsConstSum`
  (1.2(iii), l.1667–1673: `λ + μ = g(x)` for the unique `g ∈ Γ^×(D)` with `g(y_i) = f(y_i)`);
* `IsNegOne` (`−1 ∈ k^×`, multiplicatively: the element of order `2` if there is one);
* **`AddRel a b c`** on `G ∪ {0}` ("`a + b = c`"): `0` is neutral; `f + g = 0` iff `g/f = −1`;
  otherwise `f + g = h` iff at every point where `f, g, h` are units the values satisfy
  `IsConstSum` (a rational function is determined by its values at infinitely many points).

**Functoriality** (`ValEvalData.Iso`, an isomorphism of triples in the sense of l.1716–1720):
**`Iso.addRel_iff`**: `AddRel` is transported by every isomorphism of triples (as are all the
intermediate constructions: `Iso.mem_consts_iff`, `Iso.evalAt_iff`, `Iso.ell_eq`, …). So the
additive structure is a "group-theoretic" invariant of the triple.

The *correctness* theorem (MR9 step U2) — for the triple of the function field of a proper curve
over an algebraically closed field, `AddRel a b c ↔ a + b = c` — is
`Iut/Reconstruction/Uchida/FunctionField.lean` (`ofFunctionField.addRel_iff`), from the
Riemann–Roch-level input of Propositions 1.1 and 1.2 proved in `weil-curves`
(`WeilCurves.FunctionField.LinearSystem`).
-/

namespace Iut.Reconstruction.Uchida

universe u

/-- **Valuation–evaluation data** ([AbsTopIII], Proposition 1.3(a)–(c)): an abstract abelian group
`G` (`K_X^×`), points `P` with homomorphisms `ord x : G → ℤ` and subgroups `U x` (`f(x) = 1`). -/
structure ValEvalData where
  /-- The abstract group `K_X^×`. -/
  G : Type u
  [grp : CommGroup G]
  /-- The points `x ∈ X(k)`. -/
  P : Type u
  /-- The valuations `ord_x`. -/
  ord : P → G →* Multiplicative ℤ
  /-- The subgroups `U_x = {f | f(x) = 1}`. -/
  U : P → Subgroup G

attribute [instance] ValEvalData.grp

namespace ValEvalData

variable (D : ValEvalData.{u})

/-- `ord_x(f) ∈ ℤ`. -/
def val (x : D.P) (f : D.G) : ℤ := Multiplicative.toAdd (D.ord x f)

/-- **The constants** `k^× = ⋂_x Ker(ord_x)`. -/
def consts : Subgroup D.G := ⨅ x, (D.ord x).ker

lemma mem_consts_iff {c : D.G} : c ∈ D.consts ↔ ∀ x, D.val x c = 0 := by
  simp only [consts, Subgroup.mem_iInf, MonoidHom.mem_ker, val]
  exact forall_congr' fun x => by rw [← toAdd_one, Multiplicative.toAdd.apply_eq_iff_eq]

/-- **Evaluation** `f(x) = c` (`Ker(ord_x) = U_x × k^×`). -/
def EvalAt (x : D.P) (f c : D.G) : Prop :=
  D.val x f = 0 ∧ c ∈ D.consts ∧ f * c⁻¹ ∈ D.U x

/-- `Γ^×(E) = {f | div(f) + E ≥ 0}`. -/
def Gamma (E : D.P →₀ ℤ) : Set D.G := {f | ∀ x, 0 ≤ D.val x f + E x}

/-- The degree of a divisor. -/
def deg (E : D.P →₀ ℤ) : ℤ := E.sum fun _ n => n

/-- The admissible degrees of Proposition 1.1(ii): `d` such that `Γ^×(E − E') = ∅` for an effective
`E'` of degree `d`. -/
def ellSet (E : D.P →₀ ℤ) : Set ℕ :=
  {d | ∃ E' : D.P →₀ ℤ, 0 ≤ E' ∧ D.deg E' = d ∧ D.Gamma (E - E') = ∅}

/-- **`l(E)`** via Proposition 1.1(ii): the least admissible degree. -/
noncomputable def ell (E : D.P →₀ ℤ) : ℕ := sInf (D.ellSet E)

/-- **The configuration of Proposition 1.2(i)**: distinct points `x, y₁, y₂ ∉ Supp(E)` with
`l(E) = 2` and `l(E − e₁ − e₂) = 0` for distinct `e₁, e₂ ∈ {x, y₁, y₂}`. -/
def IsConfig (E : D.P →₀ ℤ) (x y₁ y₂ : D.P) : Prop :=
  x ≠ y₁ ∧ x ≠ y₂ ∧ y₁ ≠ y₂ ∧ E x = 0 ∧ E y₁ = 0 ∧ E y₂ = 0 ∧ D.ell E = 2 ∧
    D.ell (E - Finsupp.single x 1 - Finsupp.single y₁ 1) = 0 ∧
    D.ell (E - Finsupp.single x 1 - Finsupp.single y₂ 1) = 0 ∧
    D.ell (E - Finsupp.single y₁ 1 - Finsupp.single y₂ 1) = 0

/-- **`f = f_{λ,i}`** (Proposition 1.2(ii)), `y = y_i`, `y' = y_{3−i}`: `f ∈ Γ^×(E)`, `f(x) = λ`,
`f(y) ≠ 0`, `f(y') = 0`. -/
def IsBasisFn (E : D.P →₀ ℤ) (x y y' : D.P) (c f : D.G) : Prop :=
  f ∈ D.Gamma E ∧ D.EvalAt x f c ∧ D.val y f = 0 ∧ 0 < D.val y' f

/-- **`ν = λ + μ`** for constants (Proposition 1.2(iii)): for a configuration `(E, x, y₁, y₂)`,
`ν = g(x)` where `g ∈ Γ^×(E)` has the values of `f_{λ,1}` at `y₁` and of `f_{μ,2}` at `y₂`. -/
def IsConstSum (c₁ c₂ c : D.G) : Prop :=
  ∃ (E : D.P →₀ ℤ) (x y₁ y₂ : D.P), D.IsConfig E x y₁ y₂ ∧ ∃ f₁ f₂ g a₁ a₂ : D.G,
    D.IsBasisFn E x y₁ y₂ c₁ f₁ ∧ D.IsBasisFn E x y₂ y₁ c₂ f₂ ∧ g ∈ D.Gamma E ∧
    D.EvalAt y₁ f₁ a₁ ∧ D.EvalAt y₁ g a₁ ∧ D.EvalAt y₂ f₂ a₂ ∧ D.EvalAt y₂ g a₂ ∧ D.EvalAt x g c

/-- **`c = −1`**: `c² = 1`, and `c ≠ 1` unless `1` is the only square root of `1` in `k^×`. -/
def IsNegOne (c : D.G) : Prop :=
  c ∈ D.consts ∧ c * c = 1 ∧ (c = 1 → ∀ c' ∈ D.consts, c' * c' = 1 → c' = 1)

/-- **The additive structure on `G ∪ {0}`** ("`a + b = c`") of Proposition 1.3. -/
def AddRel (a b c : WithZero D.G) : Prop :=
  (a = 0 ∧ c = b) ∨ (b = 0 ∧ a ≠ 0 ∧ c = a) ∨
    (∃ f g : D.G, a = f ∧ b = g ∧ c = 0 ∧ D.IsNegOne (g * f⁻¹)) ∨
    (∃ f g h : D.G, a = f ∧ b = g ∧ c = h ∧
      ∀ (x : D.P) (u v w : D.G), D.EvalAt x f u → D.EvalAt x g v → D.EvalAt x h w →
        D.IsConstSum u v w)

/-! ### Isomorphisms of triples -/

/-- **An isomorphism of triples** `(G, {ord_x}, {U_x}) ≅ (G', {ord'_x}, {U'_x})` (in the evident
sense of [AbsTopIII], Proposition 1.3): a group isomorphism and a bijection of points compatible
with the valuations and the evaluation subgroups. -/
structure Iso (D D' : ValEvalData.{u}) where
  /-- The group isomorphism. -/
  φ : D.G ≃* D'.G
  /-- The bijection of points. -/
  σ : D.P ≃ D'.P
  ord_eq : ∀ x f, D'.ord (σ x) (φ f) = D.ord x f
  mem_U_iff : ∀ x f, φ f ∈ D'.U (σ x) ↔ f ∈ D.U x

namespace Iso

variable {D} {D' : ValEvalData.{u}} (e : Iso D D')

lemma val_eq (x : D.P) (f : D.G) : D'.val (e.σ x) (e.φ f) = D.val x f := by
  simp only [val, e.ord_eq]

lemma mem_consts_iff (c : D.G) : e.φ c ∈ D'.consts ↔ c ∈ D.consts := by
  rw [ValEvalData.mem_consts_iff, ValEvalData.mem_consts_iff, ← e.σ.forall_congr_right]
  simp only [e.val_eq]

lemma evalAt_iff (x : D.P) (f c : D.G) :
    D'.EvalAt (e.σ x) (e.φ f) (e.φ c) ↔ D.EvalAt x f c := by
  rw [EvalAt, EvalAt, e.val_eq, e.mem_consts_iff, ← map_inv, ← map_mul, e.mem_U_iff]

/-- The transport of divisors. -/
def mapDiv : (D.P →₀ ℤ) ≃+ (D'.P →₀ ℤ) := Finsupp.domCongr e.σ

@[simp] lemma mapDiv_apply (E : D.P →₀ ℤ) (x : D.P) : e.mapDiv E (e.σ x) = E x := by
  simp [mapDiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]

lemma mapDiv_single (x : D.P) (n : ℤ) :
    e.mapDiv (Finsupp.single x n) = Finsupp.single (e.σ x) n := by
  simp [mapDiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]

lemma mem_gamma_iff (E : D.P →₀ ℤ) (f : D.G) :
    e.φ f ∈ D'.Gamma (e.mapDiv E) ↔ f ∈ D.Gamma E := by
  simp only [Gamma, Set.mem_setOf_eq]
  rw [← e.σ.forall_congr_right]
  simp only [e.val_eq, e.mapDiv_apply]

lemma gamma_eq_empty_iff (E : D.P →₀ ℤ) :
    D'.Gamma (e.mapDiv E) = ∅ ↔ D.Gamma E = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem]
  rw [← e.φ.toEquiv.forall_congr_right]
  exact forall_congr' fun f => not_congr (e.mem_gamma_iff E f)

lemma deg_mapDiv (E : D.P →₀ ℤ) : D'.deg (e.mapDiv E) = D.deg E := by
  simp only [deg, mapDiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

lemma mapDiv_nonneg_iff (E : D.P →₀ ℤ) : 0 ≤ e.mapDiv E ↔ 0 ≤ E := by
  rw [Finsupp.le_def, Finsupp.le_def, ← e.σ.forall_congr_right]
  simp only [Finsupp.coe_zero, Pi.zero_apply, e.mapDiv_apply]

lemma ellSet_eq (E : D.P →₀ ℤ) : D'.ellSet (e.mapDiv E) = D.ellSet E := by
  ext d
  simp only [ellSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨E', h0, hd, hg⟩
    obtain ⟨E'', rfl⟩ := e.mapDiv.surjective E'
    refine ⟨E'', (e.mapDiv_nonneg_iff E'').mp h0, (e.deg_mapDiv E'').symm.trans hd, ?_⟩
    rw [← map_sub] at hg
    exact (e.gamma_eq_empty_iff _).mp hg
  · rintro ⟨E', h0, hd, hg⟩
    refine ⟨e.mapDiv E', (e.mapDiv_nonneg_iff E').mpr h0, (e.deg_mapDiv E').trans hd, ?_⟩
    rw [← map_sub]
    exact (e.gamma_eq_empty_iff _).mpr hg

lemma ell_eq (E : D.P →₀ ℤ) : D'.ell (e.mapDiv E) = D.ell E := by
  rw [ell, ell, e.ellSet_eq]

lemma isConfig_iff (E : D.P →₀ ℤ) (x y₁ y₂ : D.P) :
    D'.IsConfig (e.mapDiv E) (e.σ x) (e.σ y₁) (e.σ y₂) ↔ D.IsConfig E x y₁ y₂ := by
  simp only [IsConfig, ← e.mapDiv_single, ← map_sub, e.ell_eq, e.mapDiv_apply,
    e.σ.injective.ne_iff]

lemma isBasisFn_iff (E : D.P →₀ ℤ) (x y y' : D.P) (c f : D.G) :
    D'.IsBasisFn (e.mapDiv E) (e.σ x) (e.σ y) (e.σ y') (e.φ c) (e.φ f) ↔
      D.IsBasisFn E x y y' c f := by
  simp only [IsBasisFn, e.mem_gamma_iff, e.evalAt_iff, e.val_eq]

lemma isConstSum_iff (c₁ c₂ c : D.G) :
    D'.IsConstSum (e.φ c₁) (e.φ c₂) (e.φ c) ↔ D.IsConstSum c₁ c₂ c := by
  constructor
  · rintro ⟨E, x, y₁, y₂, hC, f₁, f₂, g, a₁, a₂, h1, h2, hg, h3, h4, h5, h6, h7⟩
    obtain ⟨E, rfl⟩ := e.mapDiv.surjective E
    obtain ⟨x, rfl⟩ := e.σ.surjective x
    obtain ⟨y₁, rfl⟩ := e.σ.surjective y₁
    obtain ⟨y₂, rfl⟩ := e.σ.surjective y₂
    obtain ⟨f₁, rfl⟩ := e.φ.surjective f₁
    obtain ⟨f₂, rfl⟩ := e.φ.surjective f₂
    obtain ⟨g, rfl⟩ := e.φ.surjective g
    obtain ⟨a₁, rfl⟩ := e.φ.surjective a₁
    obtain ⟨a₂, rfl⟩ := e.φ.surjective a₂
    exact ⟨E, x, y₁, y₂, (e.isConfig_iff _ _ _ _).mp hC, f₁, f₂, g, a₁, a₂,
      (e.isBasisFn_iff _ _ _ _ _ _).mp h1, (e.isBasisFn_iff _ _ _ _ _ _).mp h2,
      (e.mem_gamma_iff _ _).mp hg, (e.evalAt_iff _ _ _).mp h3, (e.evalAt_iff _ _ _).mp h4,
      (e.evalAt_iff _ _ _).mp h5, (e.evalAt_iff _ _ _).mp h6, (e.evalAt_iff _ _ _).mp h7⟩
  · rintro ⟨E, x, y₁, y₂, hC, f₁, f₂, g, a₁, a₂, h1, h2, hg, h3, h4, h5, h6, h7⟩
    exact ⟨e.mapDiv E, e.σ x, e.σ y₁, e.σ y₂, (e.isConfig_iff _ _ _ _).mpr hC, e.φ f₁, e.φ f₂,
      e.φ g, e.φ a₁, e.φ a₂, (e.isBasisFn_iff _ _ _ _ _ _).mpr h1,
      (e.isBasisFn_iff _ _ _ _ _ _).mpr h2, (e.mem_gamma_iff _ _).mpr hg,
      (e.evalAt_iff _ _ _).mpr h3, (e.evalAt_iff _ _ _).mpr h4, (e.evalAt_iff _ _ _).mpr h5,
      (e.evalAt_iff _ _ _).mpr h6, (e.evalAt_iff _ _ _).mpr h7⟩

lemma isNegOne_iff (c : D.G) : D'.IsNegOne (e.φ c) ↔ D.IsNegOne c := by
  simp only [IsNegOne, e.mem_consts_iff, ← map_mul, e.φ.map_eq_one_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl (imp_congr Iff.rfl ?_))
  rw [← e.φ.toEquiv.forall_congr_right]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, e.mem_consts_iff, ← map_mul,
    e.φ.map_eq_one_iff]

/-- The transport of `G ∪ {0}`. -/
def mapZ : WithZero D.G ≃* WithZero D'.G := MulEquiv.withZero e.φ

@[simp] lemma mapZ_coe (f : D.G) : e.mapZ (f : WithZero D.G) = (e.φ f : WithZero D'.G) := by
  simp [mapZ]

@[simp] lemma mapZ_zero : e.mapZ 0 = 0 := by simp [mapZ]

/-- **Functoriality of the algorithm of Proposition 1.3**: the reconstructed additive structure is
transported by every isomorphism of triples. -/
theorem addRel_iff (a b c : WithZero D.G) :
    D'.AddRel (e.mapZ a) (e.mapZ b) (e.mapZ c) ↔ D.AddRel a b c := by
  have hz : ∀ a : WithZero D.G, e.mapZ a = 0 ↔ a = 0 := fun a => by
    induction a <;> simp
  have hinj : ∀ a b : WithZero D.G, e.mapZ a = e.mapZ b ↔ a = b := fun a b =>
    e.mapZ.injective.eq_iff
  have hcoe : ∀ (a : WithZero D.G) (f' : D'.G), e.mapZ a = f' ↔ a = e.φ.symm f' := fun a f' => by
    rw [← hinj, mapZ_coe, MulEquiv.apply_symm_apply]
  unfold AddRel
  refine or_congr (and_congr (hz a) (hinj c b)) (or_congr
    (and_congr (hz b) (and_congr (not_congr (hz a)) (hinj c a))) (or_congr ?_ ?_))
  · constructor
    · rintro ⟨f, g, hf, hg, hc, hn⟩
      refine ⟨e.φ.symm f, e.φ.symm g, (hcoe a f).mp hf, (hcoe b g).mp hg, (hz c).mp hc, ?_⟩
      rw [← e.isNegOne_iff]
      simpa using hn
    · rintro ⟨f, g, rfl, rfl, rfl, hn⟩
      exact ⟨e.φ f, e.φ g, rfl, rfl, rfl, by rw [← map_inv, ← map_mul, e.isNegOne_iff]; exact hn⟩
  · constructor
    · rintro ⟨f, g, h, hf, hg, hc, hall⟩
      refine ⟨e.φ.symm f, e.φ.symm g, e.φ.symm h, (hcoe a f).mp hf, (hcoe b g).mp hg,
        (hcoe c h).mp hc, fun x u v w hu hv hw => ?_⟩
      rw [← e.isConstSum_iff]
      refine hall (e.σ x) (e.φ u) (e.φ v) (e.φ w) ?_ ?_ ?_
      · simpa using (e.evalAt_iff x _ u).mpr hu
      · simpa using (e.evalAt_iff x _ v).mpr hv
      · simpa using (e.evalAt_iff x _ w).mpr hw
    · rintro ⟨f, g, h, rfl, rfl, rfl, hall⟩
      refine ⟨e.φ f, e.φ g, e.φ h, rfl, rfl, rfl, fun x u v w hu hv hw => ?_⟩
      obtain ⟨x, rfl⟩ := e.σ.surjective x
      obtain ⟨u, rfl⟩ := e.φ.surjective u
      obtain ⟨v, rfl⟩ := e.φ.surjective v
      obtain ⟨w, rfl⟩ := e.φ.surjective w
      exact (e.isConstSum_iff u v w).mpr (hall x u v w ((e.evalAt_iff _ _ _).mp hu)
        ((e.evalAt_iff _ _ _).mp hv) ((e.evalAt_iff _ _ _).mp hw))

end Iso

end ValEvalData

end Iut.Reconstruction.Uchida
