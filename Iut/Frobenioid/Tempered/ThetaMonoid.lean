/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.Hull
import Iut.Frobenioid.Tempered.SplitFrob

/-!
# Theta monoids constructed from tempered Frobenioids ([IUTchII], Example 3.2)

[IUTchII], Example 3.2(i) (l.5422–5500 of `~/iut-scratch/wall/txt/Inter-universal Teichmuller
Theory II.txt`): the choice of a Frobenioid-theoretic theta function `Θ_v ∈ O^×(T^÷_Ÿ)` determines
the monoid `O^⊿_{C^Θ_v}(−)` on `D^Θ_v`; evaluating it on a universal covering pro-object `A^Θ_∞`
gives submonoids

  `Ψ_{F^Θ_v, id} = O^×_{C^Θ_v}(A^Θ_∞) · Θ_v^ℕ ⊆ ∞Ψ_{F^Θ_v, id} = O^×_{C^Θ_v}(A^Θ_∞) · Θ_v^{ℚ≥0}
    ⊆ O^×(T^÷_{A^Θ_∞})`,

"where the superscript `ℚ≥0` denotes the set of elements for which some [positive integer] power
is equal to a [positive integer] power of `Θ_v`"; the conjugates `Θ^α_v` give `Ψ_{F^Θ_v, α} ⊆
∞Ψ_{F^Θ_v, α}`, with the natural conjugation action of `Π_v` on the collections
`Ψ_{F^Θ_v} = {Ψ_{F^Θ_v, α}}_α`, `∞Ψ_{F^Θ_v} = {∞Ψ_{F^Θ_v, α}}_α`; `Θ^{ℚ≥0}_v` determines
characteristic splittings, up to torsion, compatible with the action of `Π_v`; and the data are
reconstructed category-theoretically from `F_v` up to inner automorphisms. Example 3.2(ii):
`Ψ_{C_v} = O^⊿_{C_v}(A^Θ_∞)` with its natural `Π_v`-action. [IUTchII], Proposition 3.3 consumes
these data (`Π_X(M^Θ_*) ↷ Ψ_{†F^Θ_v}, ∞Ψ_{†F^Θ_v}`, the splittings up to torsion, and
`Π_X(M^Θ_*) ↷ Ψ_{†C_v}`).

## Formalisation

**Abstract layer** (an abelian group `M` written additively — `O^×(T^÷_{A})` — with a group `Π`
acting through `act : Π →* AddMonoid.End M`, a `Π`-stable subgroup `U` — the units — and `θ ∈ M`):

* `psi U θ act α = U · (α θ)^ℕ` and `psiInf U θ act α = U · (α θ)^{ℚ≥0}`, with
  `rootMon θ = θ^{ℚ≥0} = {y | n·y = m·θ for some n ≥ 1, m ∈ ℕ}`; `psi_le_psiInf`;
* **the conjugation action** (`act_mem_psi_iff`, `act_mem_psiInf_iff`): `g` maps `Ψ_α` onto
  `Ψ_{gα}` and `∞Ψ_α` onto `∞Ψ_{gα}`; `psi_congr`: `Ψ_α` only depends on `α θ` (so on the image of
  `α` in the automorphisms of `Ÿ`, `psi_eq_of_fix`);
* **splittings** (`psiEquiv`): `U × ℕ ≅ Ψ_α`, `(u, n) ↦ u + n·αθ`, equivariant
  (`act_psiEquiv`); **splittings up to torsion** of `∞Ψ_α`: `∞Ψ_α = U + (αθ)^{ℚ≥0}` with
  `U ∩ (αθ)^{ℚ≥0}` torsion (`inter_rootMon_torsion`), and the exponent `thetaExp : ∞Ψ_α → ℚ`
  (`x = u + y`, `n·y = m·αθ ↦ m/n`), additive (`thetaExp_add`), nonnegative, equal to `n` on
  `u + n·αθ` (`thetaExp_psi`), vanishing exactly on `U + torsion` (`thetaExp_eq_zero_iff`);
* **transport** (`map_psi`, `map_psiInf`): an additive isomorphism `M ≅ M'` matching units,
  intertwining `act` and `act' ∘ ρ`, maps `Ψ_α(θ)` onto `Ψ_{ρ α}(f θ)` and `∞Ψ_α(θ)` onto
  `∞Ψ_{ρ α}(f θ)`.

**Frobenioid layer** (a model Frobenioid `C = Model Φ B divB`, [FrdI], Theorem 5.2):

* `Model.baseAct Y : Aut_C(Y) →* End(B(Y_D))`, the action of the automorphisms of the
  Frobenius-trivial object `T_A = (A, 0)` on `O^×(T^÷_A) = B(A)` through their bases (`g ↦
  (Base g^{-1})^*`), which preserves `O^×(T_A)` and `O^⊿(T_A)`;
* `Model.thetaPsi`, `Model.thetaPsiInf`: `Ψ_{F^Θ, α}`, `∞Ψ_{F^Θ, α}` at `T_A` for `Θ ∈ B(A)`;
  `Model.psiCns`: `Ψ_C = O^⊿(T_A)`, `Aut`-stable (`Model.baseAct_mem_orhdSub_iff`); for a hull the
  monoid `Ψ_{C_v}` is the image of `psiCns` of `C^bs-fld` (`Iut/Frobenioid/Tempered/Hull.lean`);
* **`Ψ_{C_v}`** (`Model.psiHull`): `O^⊿` of the hull `C_v = C^bs-fld` realised in `B`;
  `Model.mem_psiHull_iff`: `Ψ_{C_v}(A) = {b : Div(b) ∈ Φ^bs-fld(A)}`; stable under pull-back;
  `Model.mem_bsFld_mapUnit_iff`: transported by every equivalence preserving base-field-theoretic
  morphisms ([EtTh], Corollary 3.8(i),(ii), an explicit hypothesis `hbs`);
* **category-theoreticity** ([IUTchII], Example 3.2(i), "reconstructed category-theoretically from
  `F_v`"; [IUTchI], Example 3.2(vi)(e)): for an equivalence `F : C₁ ⥤ C₂` matching pre-steps and
  base-equivalent pairs (e.g. any equivalence over slim bases of FSM-type, `Model.preStep_iff_fsm`,
  `Model.base_eq_iff_fsm`), `F^birat` on `B(A) = O^×(T^÷_A)` (`Model.mapUnitEquiv`) matches units
  (`Model.mem_unitSub_mapUnit_iff`) and `O^⊿` (`Model.mem_orhdSub_mapUnit_iff`), intertwines the
  actions of `Aut(T_A)` and `Aut(F T_A)` (`Model.mapUnit_baseAct`), and maps
  `Ψ_{F^Θ,α}`, `∞Ψ_{F^Θ,α}`, `Ψ_C` onto the monoids of the image data
  (`Model.map_thetaPsi`, `Model.map_thetaPsiInf`, `Model.map_psiCns`).

The pro-object `A^Θ_∞` of Example 3.2 is represented level-wise: the monoids at a Galois object `A`
of `D^Θ` with the action of `Aut(T_A)`, natural for pull-backs (`Model.pb_mem_thetaPsi`); the
evaluation on `A^Θ_∞` is the inductive limit of these levels.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v v₁ v₂ u u₁ u₂

/-! ### `θ^{ℚ≥0}` -/

section Abstract

variable {M : Type*} [AddCommGroup M]

/-- **`θ^{ℚ≥0}`**: the elements `y` with `n·y = m·θ` for some `n ≥ 1`, `m ∈ ℕ`. -/
def rootMon (θ : M) : AddSubmonoid M where
  carrier := {y | ∃ n : ℕ, 0 < n ∧ ∃ m : ℕ, n • y = m • θ}
  add_mem' := by
    rintro y z ⟨n, hn, m, e⟩ ⟨n', hn', m', e'⟩
    refine ⟨n * n', Nat.mul_pos hn hn', m * n' + m' * n, ?_⟩
    rw [smul_add, mul_comm n n', mul_smul, e, mul_comm n' n, mul_smul, e', add_nsmul,
      ← mul_smul, ← mul_smul, mul_comm n' m, mul_comm n m']
  zero_mem' := ⟨1, Nat.one_pos, 0, by simp⟩

lemma theta_mem_rootMon (θ : M) : θ ∈ rootMon θ := ⟨1, Nat.one_pos, 1, by simp⟩

lemma nsmul_mem_rootMon (θ : M) (k : ℕ) : k • θ ∈ rootMon θ := ⟨1, Nat.one_pos, k, by simp⟩

/-- **`U · θ^{ℚ≥0}`**. -/
def thetaMonInf (U : AddSubgroup M) (θ : M) : AddSubmonoid M where
  carrier := {x | ∃ u ∈ U, ∃ y ∈ rootMon θ, x = u + y}
  add_mem' := by
    rintro _ _ ⟨u, hu, y, hy, rfl⟩ ⟨u', hu', y', hy', rfl⟩
    exact ⟨u + u', U.add_mem hu hu', y + y', (rootMon θ).add_mem hy hy', by abel⟩
  zero_mem' := ⟨0, U.zero_mem, 0, (rootMon θ).zero_mem, by simp⟩

lemma thetaMon_le_thetaMonInf (U : AddSubgroup M) (θ : M) : thetaMon U θ ≤ thetaMonInf U θ := by
  rintro _ ⟨u, hu, n, rfl⟩
  exact ⟨u, hu, n • θ, nsmul_mem_rootMon θ n, rfl⟩

/-- **Splitting up to torsion**: `U ∩ θ^{ℚ≥0}` consists of torsion elements. -/
theorem inter_rootMon_torsion {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) {y : M}
    (hyU : y ∈ U) (hy : y ∈ rootMon θ) : ∃ n : ℕ, 0 < n ∧ n • y = 0 := by
  obtain ⟨n, hn, m, e⟩ := hy
  have hm : (m : ℤ) = 0 := h m (by rw [natCast_zsmul, ← e]; exact U.nsmul_mem hyU n)
  refine ⟨n, hn, ?_⟩
  rw [e, show m = 0 by exact_mod_cast hm, zero_smul]

/-- The exponent of an element of `θ^{ℚ≥0}` is well defined. -/
lemma rootMon_exp_unique {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) {u u' y y' : M}
    (hu : u ∈ U) (hu' : u' ∈ U) {n n' m m' : ℕ} (e : n • y = m • θ) (e' : n' • y' = m' • θ)
    (hn : 0 < n) (hn' : 0 < n') (hx : u + y = u' + y') : (m : ℚ) / n = m' / n' := by
  have hy : y = u' - u + y' := by linear_combination (norm := abel) hx
  have e1 : (n * n') • y = (m * n') • θ := by
    rw [mul_comm n n', mul_smul, e, ← mul_smul, mul_comm n' m]
  have e2 : (n * n') • y' = (m' * n) • θ := by
    rw [mul_smul, e', ← mul_smul, mul_comm n m']
  have key : (((m * n' : ℕ) : ℤ) - ((m' * n : ℕ) : ℤ)) • θ = ((n * n' : ℕ) : ℤ) • (u' - u) := by
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, ← e1, ← e2, hy, smul_add]
    abel
  have hz : (((m * n' : ℕ) : ℤ) - ((m' * n : ℕ) : ℤ)) • θ ∈ U := by
    rw [key]; exact U.zsmul_mem (U.sub_mem hu' hu) _
  have h0 := h _ hz
  have h1 : (m * n' : ℕ) = m' * n := by omega
  rw [div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast hn'.ne')]
  exact_mod_cast h1

end Abstract

/-! ### The theta monoids with a group action -/

section Action

variable {M : Type*} [AddCommGroup M] {G : Type*} [Group G]
variable (U : AddSubgroup M) (θ : M) (act : G →* AddMonoid.End M)

/-- **`Ψ_{F^Θ, α} = U · (α θ)^ℕ`** ([IUTchII], Example 3.2(i)). -/
def psi (α : G) : AddSubmonoid M := thetaMon U (act α θ)

/-- **`∞Ψ_{F^Θ, α} = U · (α θ)^{ℚ≥0}`** ([IUTchII], Example 3.2(i)). -/
def psiInf (α : G) : AddSubmonoid M := thetaMonInf U (act α θ)

lemma psi_le_psiInf (α : G) : psi U θ act α ≤ psiInf U θ act α :=
  thetaMon_le_thetaMonInf _ _

lemma act_mul (g h : G) (x : M) : act (g * h) x = act g (act h x) := by
  rw [map_mul]; rfl

lemma act_one (x : M) : act 1 x = x := by
  rw [map_one]; rfl

/-- `act g` as an additive automorphism. -/
def actEquiv (g : G) : M ≃+ M where
  toFun := act g
  invFun := act g⁻¹
  left_inv x := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv x := by rw [← act_mul, mul_inv_cancel, act_one]
  map_add' := map_add _

@[simp] lemma actEquiv_apply (g : G) (x : M) : actEquiv act g x = act g x := rfl

variable {U θ act}

/-- `U` is `G`-stable. -/
def IsStable (U : AddSubgroup M) (act : G →* AddMonoid.End M) : Prop :=
  ∀ (g : G) (x : M), x ∈ U ↔ act g x ∈ U

/-- `Ψ_α` depends only on `α θ`. -/
lemma psi_congr {α β : G} (h : act α θ = act β θ) : psi U θ act α = psi U θ act β := by
  simp only [psi, h]

lemma psiInf_congr {α β : G} (h : act α θ = act β θ) : psiInf U θ act α = psiInf U θ act β := by
  simp only [psiInf, h]

/-- If `α` fixes `θ` (e.g. `α` acts over the identity of `Ÿ` and `θ` is pulled back from `Ÿ`),
`Ψ_α = Ψ_id`. -/
lemma psi_eq_of_fix {α : G} (h : act α θ = θ) : psi U θ act α = psi U θ act 1 :=
  psi_congr (by rw [h, act_one])

lemma rootMon_map {M' : Type*} [AddCommGroup M'] (f : M ≃+ M') (θ : M) (y : M) :
    y ∈ rootMon θ ↔ f y ∈ rootMon (f θ) := by
  constructor
  · rintro ⟨n, hn, m, e⟩
    exact ⟨n, hn, m, by rw [← map_nsmul, e, map_nsmul]⟩
  · rintro ⟨n, hn, m, e⟩
    exact ⟨n, hn, m, f.injective (by rw [map_nsmul, e, map_nsmul])⟩

/-- **Transport of `U · θ^{ℚ≥0}`** along an additive isomorphism matching `U` and `U'`. -/
theorem thetaMonInf_map {M' : Type*} [AddCommGroup M'] (f : M ≃+ M') {U : AddSubgroup M}
    {U' : AddSubgroup M'} (hU : ∀ x, x ∈ U ↔ f x ∈ U') (θ : M) (x : M) :
    x ∈ thetaMonInf U θ ↔ f x ∈ thetaMonInf U' (f θ) := by
  constructor
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨f u, (hU u).1 hu, f y, (rootMon_map f θ y).1 hy, map_add _ _ _⟩
  · rintro ⟨u', hu', y', hy', e⟩
    refine ⟨f.symm u', (hU _).2 (by simpa using hu'), f.symm y', ?_, f.injective ?_⟩
    · rw [rootMon_map f θ, AddEquiv.apply_symm_apply]; exact hy'
    · rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, e]

lemma thetaMon_map' {M' : Type*} [AddCommGroup M'] (f : M ≃+ M') {U : AddSubgroup M}
    {U' : AddSubgroup M'} (hU : ∀ x, x ∈ U ↔ f x ∈ U') (θ : M) (x : M) :
    x ∈ thetaMon U θ ↔ f x ∈ thetaMon U' (f θ) := by
  rw [← thetaMon_map f hU θ]
  simp only [AddSubmonoid.mem_map, AddEquiv.coe_toAddMonoidHom]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => f.injective e ▸ hy⟩

/-- **The conjugation action on `Ψ_{F^Θ}`**: `g` maps `Ψ_α` onto `Ψ_{gα}`. -/
theorem act_mem_psi_iff (hU : IsStable U act) (g α : G) (x : M) :
    x ∈ psi U θ act α ↔ act g x ∈ psi U θ act (g * α) := by
  rw [psi, psi, act_mul]
  exact thetaMon_map' (actEquiv act g) (hU g) _ x

/-- **The conjugation action on `∞Ψ_{F^Θ}`**: `g` maps `∞Ψ_α` onto `∞Ψ_{gα}`. -/
theorem act_mem_psiInf_iff (hU : IsStable U act) (g α : G) (x : M) :
    x ∈ psiInf U θ act α ↔ act g x ∈ psiInf U θ act (g * α) := by
  rw [psiInf, psiInf, act_mul]
  exact thetaMonInf_map (actEquiv act g) (hU g) _ x

lemma NonTorsionMod.of_act (hU : IsStable U act) (h : NonTorsionMod U θ) (α : G) :
    NonTorsionMod U (act α θ) := fun n hn => h n (by
  rw [hU α, map_zsmul]; exact hn)

/-- **The splitting `U × ℕ ≅ Ψ_α`** determined by `(α θ)^ℕ` ([IUTchII], Example 3.2(i):
"`Θ_v` determines characteristic splittings"; [IUTchI], Example 3.2(v): `τ^Θ_v`). -/
noncomputable def psiEquiv (hU : IsStable U act) (h : NonTorsionMod U θ) (α : G) :
    U × ℕ ≃+ psi U θ act α :=
  thetaMonEquiv (h.of_act hU α)

/-- **The splittings are compatible with the action of `G`**:
`g (u + n·αθ) = g u + n·(gα)θ`. -/
lemma act_psiEquiv (hU : IsStable U act) (h : NonTorsionMod U θ) (g α : G) (p : U × ℕ) :
    act g (psiEquiv hU h α p : M) =
      (psiEquiv hU h (g * α) (⟨act g p.1, (hU g p.1).1 p.1.2⟩, p.2) : M) := by
  change act g ((p.1 : M) + p.2 • act α θ) = act g p.1 + p.2 • act (g * α) θ
  rw [map_add, map_nsmul, act_mul]

/-- **Transport of the theta monoids** along an additive isomorphism `f : M ≅ M'` matching units,
with `f (g x) = (ρ g) (f x)`. -/
theorem map_psi {M' : Type*} [AddCommGroup M'] {G' : Type*} [Group G'] {U' : AddSubgroup M'}
    {act' : G' →* AddMonoid.End M'} (f : M ≃+ M') (ρ : G →* G') (hU : ∀ x, x ∈ U ↔ f x ∈ U')
    (hf : ∀ g x, f (act g x) = act' (ρ g) (f x)) (α : G) (x : M) :
    x ∈ psi U θ act α ↔ f x ∈ psi U' (f θ) act' (ρ α) := by
  rw [psi, psi, ← hf]
  exact thetaMon_map' f hU _ x

theorem map_psiInf {M' : Type*} [AddCommGroup M'] {G' : Type*} [Group G'] {U' : AddSubgroup M'}
    {act' : G' →* AddMonoid.End M'} (f : M ≃+ M') (ρ : G →* G') (hU : ∀ x, x ∈ U ↔ f x ∈ U')
    (hf : ∀ g x, f (act g x) = act' (ρ g) (f x)) (α : G) (x : M) :
    x ∈ psiInf U θ act α ↔ f x ∈ psiInf U' (f θ) act' (ρ α) := by
  rw [psiInf, psiInf, ← hf]
  exact thetaMonInf_map f hU _ x

end Action

/-! ### The exponent: splittings of `∞Ψ` up to torsion -/

section Exp

variable {M : Type*} [AddCommGroup M] {U : AddSubgroup M} {θ : M}

/-- **The exponent** `x = u + y ↦ m/n` (`n·y = m·θ`) on `U · θ^{ℚ≥0}`. -/
noncomputable def thetaExp (x : thetaMonInf U θ) : ℚ :=
  (x.2.choose_spec.2.choose_spec.1.choose_spec.2.choose : ℚ) /
    x.2.choose_spec.2.choose_spec.1.choose

lemma thetaExp_spec (h : NonTorsionMod U θ) (x : thetaMonInf U θ) {u y : M} (hu : u ∈ U)
    {n m : ℕ} (hn : 0 < n) (e : n • y = m • θ) (hx : (x : M) = u + y) :
    thetaExp x = (m : ℚ) / n := by
  have hu₀ := x.2.choose_spec.1
  have hy₀ := x.2.choose_spec.2.choose_spec.1
  have hx₀ := x.2.choose_spec.2.choose_spec.2
  have hn₀ := hy₀.choose_spec.1
  have e₀ := hy₀.choose_spec.2.choose_spec
  exact rootMon_exp_unique h hu₀ hu e₀ e hn₀ hn (hx₀.symm.trans hx)

/-- The exponent is nonnegative. -/
lemma thetaExp_nonneg (x : thetaMonInf U θ) : 0 ≤ thetaExp x :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The exponent is additive** (a homomorphism `∞Ψ → ℚ≥0`). -/
theorem thetaExp_add (h : NonTorsionMod U θ) (x x' : thetaMonInf U θ) :
    thetaExp (x + x') = thetaExp x + thetaExp x' := by
  obtain ⟨u, hu, y, ⟨n, hn, m, e⟩, hx⟩ := x.2
  obtain ⟨u', hu', y', ⟨n', hn', m', e'⟩, hx'⟩ := x'.2
  rw [thetaExp_spec h x hu hn e hx, thetaExp_spec h x' hu' hn' e' hx',
    thetaExp_spec h (x + x') (U.add_mem hu hu') (Nat.mul_pos hn hn')
      (y := y + y') (m := m * n' + m' * n) ?_ ?_]
  · push_cast
    field_simp
  · rw [smul_add, mul_comm n n', mul_smul, e, mul_comm n' n, mul_smul, e', add_nsmul,
      ← mul_smul, ← mul_smul, mul_comm n' m, mul_comm n m']
  · rw [AddSubmonoid.coe_add, hx, hx']; abel

/-- **The exponent on `Ψ = U · θ^ℕ`** is the exponent `n` of the splitting `U × ℕ ≅ Ψ`. -/
theorem thetaExp_psi (h : NonTorsionMod U θ) {u : M} (hu : u ∈ U) (n : ℕ) :
    thetaExp (⟨u + n • θ, thetaMon_le_thetaMonInf U θ (add_mem_thetaMon hu n)⟩ :
      thetaMonInf U θ) = n :=
  (thetaExp_spec h _ hu Nat.one_pos (y := n • θ) (m := n) (by simp) rfl).trans (by simp)

/-- **The kernel of the exponent is `U + torsion`**: `thetaExp x = 0` iff `x = u + t` with `u ∈ U`
and `t` torsion (so `∞Ψ / (U + torsion)` embeds in `ℚ≥0`: the splitting up to torsion). -/
theorem thetaExp_eq_zero_iff (h : NonTorsionMod U θ) (x : thetaMonInf U θ) :
    thetaExp x = 0 ↔ ∃ u ∈ U, ∃ t : M, (∃ n : ℕ, 0 < n ∧ n • t = 0) ∧ (x : M) = u + t := by
  constructor
  · intro h0
    obtain ⟨u, hu, y, ⟨n, hn, m, e⟩, hx⟩ := x.2
    rw [thetaExp_spec h x hu hn e hx, div_eq_zero_iff] at h0
    have hm : m = 0 := by
      rcases h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd (by exact_mod_cast h0) hn.ne'
    exact ⟨u, hu, y, ⟨n, hn, by rw [e, hm, zero_smul]⟩, hx⟩
  · rintro ⟨u, hu, t, ⟨n, hn, e⟩, hx⟩
    rw [thetaExp_spec h x hu hn (m := 0) (by rw [e, zero_smul]) hx]
    simp

end Exp

/-! ### The Frobenioid layer -/

namespace Model

section Act

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

/-- **The action of `Aut_C(Y)` on `O^×(Y^birat) = B(Y_D)`** through the base:
`g ↦ (Base g^{-1})^*`. -/
def baseAct (Y : Model Φ B divB) : Aut Y →* AddMonoid.End (B.obj Y.base) where
  toFun g := B.pb g.inv.base
  map_one' := by
    ext x
    change B.pb (𝟙 Y : Y ⟶ Y).base x = x
    rw [id_base, GrpOn.pb_id']
  map_mul' g h := by
    ext x
    change B.pb (g.inv ≫ h.inv).base x = B.pb g.inv.base (B.pb h.inv.base x)
    rw [comp_base, GrpOn.pb_comp']

@[simp] lemma baseAct_apply (Y : Model Φ B divB) (g : Aut Y) (x : B.obj Y.base) :
    baseAct Y g x = B.pb g.inv.base x := rfl

/-- `O^×(T_Y)` is stable under `Aut_C(Y)`. -/
lemma isStable_unitSub (Y : Model Φ B divB) :
    IsStable (Model.unitSub divB Y.base) (baseAct Y) := by
  intro g x
  change divB.app _ x = 0 ↔ divB.app _ (B.pb g.inv.base x) = 0
  rw [divB.natural]
  exact ⟨fun h => by rw [h, map_zero], fun h => Φ.pb_injective _ (by rw [h, map_zero])⟩

/-- `O^⊿(T_Y)` is stable under `Aut_C(Y)`. -/
lemma baseAct_mem_orhdSub_iff (Y : Model Φ B divB) (g : Aut Y) (x : B.obj Y.base) :
    x ∈ Model.orhdSub divB Y.base ↔ baseAct Y g x ∈ Model.orhdSub divB Y.base := by
  refine ⟨fun h => Model.pb_mem_orhdSub _ h, fun h => ?_⟩
  have := Model.pb_mem_orhdSub g.hom.base h
  rwa [baseAct_apply, ← GrpOn.pb_comp', ← comp_base, g.hom_inv_id, id_base, GrpOn.pb_id'] at this

/-- **`Ψ_{F^Θ, α}`** at an object `Y` (the level `Y = T_A` of `A^Θ_∞`), for `Θ ∈ O^×(Y^birat)`. -/
abbrev thetaPsi (Y : Model Φ B divB) (Θ : B.obj Y.base) (α : Aut Y) : AddSubmonoid (B.obj Y.base) :=
  psi (Model.unitSub divB Y.base) Θ (baseAct Y) α

/-- **`∞Ψ_{F^Θ, α}`** at an object `Y`. -/
abbrev thetaPsiInf (Y : Model Φ B divB) (Θ : B.obj Y.base) (α : Aut Y) :
    AddSubmonoid (B.obj Y.base) :=
  psiInf (Model.unitSub divB Y.base) Θ (baseAct Y) α

/-- **`Ψ_C = O^⊿(T_Y)`** ([IUTchII], Example 3.2(ii) for the Frobenioid `C`). -/
abbrev psiCns (Y : Model Φ B divB) : AddSubmonoid (B.obj Y.base) := Model.orhdSub divB Y.base

/-- **The levels are compatible**: pull-back along `f : Y'_D → Y_D` maps `Ψ_{F^Θ, id}` at `Y`
into `Ψ_{F^Θ, id}` at `Y'` for the pulled-back theta function. -/
lemma pb_mem_thetaPsi {Y Y' : Model Φ B divB} (f : Y'.base ⟶ Y.base) (Θ : B.obj Y.base)
    {x : B.obj Y.base} (hx : x ∈ thetaPsi Y Θ 1) : B.pb f x ∈ thetaPsi Y' (B.pb f Θ) 1 := by
  simp only [thetaPsi, psi, act_one] at hx ⊢
  obtain ⟨u, hu, n, rfl⟩ := hx
  exact ⟨B.pb f u, Model.pb_mem_unitSub _ hu, n, by rw [map_add, map_nsmul]⟩

end Act

/-! ### `Ψ_{C_v}` for a base-field-theoretic hull ([IUTchII], Example 3.2(ii)) -/

section Hull

variable {D : Type u} [Category.{v} D]
variable {Φ Φ' : DivMonoid.{w} D} {B B' : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {divB' : DivHom B' Φ'.toGrpOn}
variable (ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn) (ιB : DivHom B' B)

/-- **`Ψ_{C_v} = O^⊿_{C_v}(−)`** realised in `O^×((−)^birat) = B(−)` of `C` through `ι_B`
(`C_v = C^bs-fld` the hull of `Iut/Frobenioid/Tempered/Hull.lean`). -/
def psiHull (A : D) : AddSubmonoid (B.obj A) := (Model.orhdSub divB' A).map (ιB.app A)

variable {ιΦ ιB}

/-- **`Ψ_{C_v}(A) = {b ∈ O^×(T^÷_A) : Div(b) ∈ Φ^bs-fld(A)}`** for `F = B ×_{Φ^gp} Φ'^gp`
([EtTh], Definition 3.6(ii)(b),(iv)). -/
theorem mem_psiHull_iff
    (hdiv : ∀ A x, divB.app A (ιB.app A x) = ιΦ.app A (divB'.app A x))
    (hιΦ : ∀ A, Function.Injective (ιΦ.app A))
    (hfib : ∀ A (b : B.obj A) (y : Φ'.obj A), divB.app A b = ιΦ.app A y →
      ∃ b' : B'.obj A, ιB.app A b' = b) {A : D} (b : B.obj A) :
    b ∈ psiHull (divB' := divB') ιB A ↔ ∃ y ∈ Φ'.pos A, divB.app A b = ιΦ.app A y := by
  constructor
  · rintro ⟨b', hb', rfl⟩
    exact ⟨divB'.app A b', hb', hdiv A b'⟩
  · rintro ⟨y, hy, e⟩
    obtain ⟨b', rfl⟩ := hfib A b y e
    refine ⟨b', ?_, rfl⟩
    change divB'.app A b' ∈ Φ'.pos A
    rw [hιΦ A ((hdiv A b').symm.trans e)]
    exact hy

/-- `Ψ_{C_v}` is stable under pull-back (hence under the action of `Aut`). -/
lemma pb_mem_psiHull {A A' : D} (f : A ⟶ A') {b : B.obj A'}
    (hb : b ∈ psiHull (divB' := divB') ιB A') : B.pb f b ∈ psiHull (divB' := divB') ιB A := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨B'.pb f b', Model.pb_mem_orhdSub f hb', ιB.natural f b'⟩

end Hull

/-! ### Category-theoreticity -/

section Transport

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ : DivMonoid.{w} D₁} {B₁ : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ : DivMonoid.{w} D₂} {B₂ : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
  (hpre : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y),
    IsPreStep (toElem Φ₁ B₁ divB₁) φ ↔ IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)

include hbe in
/-- For a base-identity linear endomorphism `e`, `u_{F e} = F^birat(u_e)`. -/
lemma map_u_of_baseId {Y : Model Φ₁ B₁ divB₁} (e : Y ⟶ Y) (h₁ : e.deg = 1) (h₂ : e.base = 𝟙 _) :
    (F.map e).u = mapUnit F hpre e.u := by
  have hb : (toBirat Φ₁ B₁ divB₁).map e = birUnit Y e.u := by
    ext
    · exact h₁
    · exact h₂
    · rfl
  have := biratFunctor_map_toBirat F (fun _ _ φ h => (hpre φ).1 h) e
  rw [hb, map_birUnit' F hpre hbe] at this
  exact (congrArg BHom.u this).symm

include hbe in
lemma map_base_of_baseId {Y : Model Φ₁ B₁ divB₁} (e : Y ⟶ Y) (h₂ : e.base = 𝟙 _) :
    (F.map e).base = 𝟙 _ := by
  have := (hbe e (𝟙 Y)).1 h₂
  rwa [F.map_id] at this

include hbe in
/-- **`F^birat` preserves `O^⊿`** (forward direction). -/
lemma mapUnit_mem_orhdSub {Y : Model Φ₁ B₁ divB₁} {x : B₁.obj Y.base}
    (hx : x ∈ Model.orhdSub divB₁ Y.base) :
    mapUnit F hpre x ∈ Model.orhdSub divB₂ (F.obj Y).base := by
  let e : Y ⟶ Y := mk1 (𝟙 _) (divB₁.app _ x) hx x (by simp)
  have hu : (F.map e).u = mapUnit F hpre x := map_u_of_baseId F hpre hbe e rfl rfl
  have hb := map_base_of_baseId F hbe e rfl
  have h1 : (F.map e).deg = 1 := ((hpre e).1 (isPreStep_mk1 _ _ _ _ _)).1
  have hd := div_eq_divB_u (F.map e) hb h1
  change divB₂.app _ (mapUnit F hpre x) ∈ Φ₂.pos _
  rw [← hu, ← hd]
  exact (F.map e).div_mem

variable [F.IsEquivalence]

include hbe in
/-- **`F^birat` matches `O^⊿`** ([FrdI], Theorem 3.4(iv), Corollary 4.10). -/
theorem mem_orhdSub_mapUnit_iff {Y : Model Φ₁ B₁ divB₁} (x : B₁.obj Y.base) :
    x ∈ Model.orhdSub divB₁ Y.base ↔ mapUnit F hpre x ∈ Model.orhdSub divB₂ (F.obj Y).base := by
  refine ⟨mapUnit_mem_orhdSub F hpre hbe, fun hx => ?_⟩
  let e' : F.obj Y ⟶ F.obj Y := mk1 (𝟙 _) (divB₂.app _ (mapUnit F hpre x)) hx (mapUnit F hpre x)
    (by simp)
  let g : Y ⟶ Y := F.preimage e'
  have hFg : F.map g = e' := F.map_preimage e'
  have hgb : g.base = 𝟙 _ := by
    refine (hbe g (𝟙 Y)).2 ?_
    rw [hFg, F.map_id]; rfl
  have hg1 : g.deg = 1 := ((hpre g).2 (by rw [hFg]; exact isPreStep_mk1 _ _ _ _ _)).1
  have hu := map_u_of_baseId F hpre hbe g hg1 hgb
  rw [hFg] at hu
  have hx' : g.u = x := mapUnit_injective F hpre hbe Y hu.symm
  rw [← hx']
  change divB₁.app _ g.u ∈ Φ₁.pos _
  rw [← div_eq_divB_u g hgb hg1]
  exact g.div_mem

include hbe in
/-- **`F^birat` matches the units `O^×`.** -/
theorem mem_unitSub_mapUnit_iff {Y : Model Φ₁ B₁ divB₁} (x : B₁.obj Y.base) :
    x ∈ Model.unitSub divB₁ Y.base ↔ mapUnit F hpre x ∈ Model.unitSub divB₂ (F.obj Y).base := by
  refine ⟨fun hx => divB_mapUnit F hpre hbe hx, fun hx => ?_⟩
  have hx' : divB₂.app _ (mapUnit F hpre x) = 0 := hx
  let g : Y ⟶ Y := F.preimage (unitHom (F.obj Y) (mapUnit F hpre x) hx')
  have hFg : F.map g = unitHom (F.obj Y) (mapUnit F hpre x) hx' := F.map_preimage _
  have hgb : g.base = 𝟙 _ := by
    refine (hbe g (𝟙 Y)).2 ?_
    rw [hFg, F.map_id]; rfl
  haveI : IsIso (F.map g) := by rw [hFg]; exact (unitIso _ _ hx').isIso_hom
  haveI : IsIso g := isIso_of_fully_faithful F g
  obtain ⟨hg, -⟩ := eq_unitHom_of_base g hgb
  have hg1 : g.deg = 1 := deg_of_iso (asIso g)
  have hu := map_u_of_baseId F hpre hbe g hg1 hgb
  rw [hFg] at hu
  have : g.u = x := mapUnit_injective F hpre hbe Y hu.symm
  rw [← this]
  exact hg

omit [F.IsEquivalence] in
include hbe in
/-- **`F^birat` intertwines the actions** of `Aut_C(Y)` and `Aut_C(F Y)`. -/
theorem mapUnit_baseAct (Y : Model Φ₁ B₁ divB₁) (g : Aut Y) (x : B₁.obj Y.base) :
    mapUnit F hpre (baseAct Y g x) = baseAct (F.obj Y) (F.mapAut Y g) (mapUnit F hpre x) := by
  rw [baseAct_apply, mapUnit_pb F hpre hbe g.inv ((hpre _).2 ?_)]
  · rfl
  · exact isPreStep_of_isIso (F.map g.inv)

include hbe in
/-- **Category-theoreticity of `Ψ_{F^Θ}`** ([IUTchII], Example 3.2(i); [IUTchI], Example
3.2(vi)(e)): `F^birat` maps `Ψ_{F^Θ, α}` at `Y` onto `Ψ_{F^{F(Θ)}, F α}` at `F Y`. -/
theorem map_thetaPsi (Y : Model Φ₁ B₁ divB₁) (Θ : B₁.obj Y.base) (α : Aut Y) (x : B₁.obj Y.base) :
    x ∈ thetaPsi Y Θ α ↔
      mapUnit F hpre x ∈ thetaPsi (F.obj Y) (mapUnit F hpre Θ) (F.mapAut Y α) :=
  map_psi (mapUnitEquiv F hpre hbe Y) (F.mapAut Y) (mem_unitSub_mapUnit_iff F hpre hbe)
    (mapUnit_baseAct F hpre hbe Y) α x

include hbe in
/-- **Category-theoreticity of `∞Ψ_{F^Θ}`.** -/
theorem map_thetaPsiInf (Y : Model Φ₁ B₁ divB₁) (Θ : B₁.obj Y.base) (α : Aut Y)
    (x : B₁.obj Y.base) :
    x ∈ thetaPsiInf Y Θ α ↔
      mapUnit F hpre x ∈ thetaPsiInf (F.obj Y) (mapUnit F hpre Θ) (F.mapAut Y α) :=
  map_psiInf (mapUnitEquiv F hpre hbe Y) (F.mapAut Y) (mem_unitSub_mapUnit_iff F hpre hbe)
    (mapUnit_baseAct F hpre hbe Y) α x

include hbe in
/-- **Category-theoreticity of `Ψ_C = O^⊿`** with its `Aut`-action. -/
theorem map_psiCns (Y : Model Φ₁ B₁ divB₁) (x : B₁.obj Y.base) :
    x ∈ psiCns Y ↔ mapUnit F hpre x ∈ psiCns (F.obj Y) :=
  mem_orhdSub_mapUnit_iff F hpre hbe x

variable {Φ₁' : DivMonoid.{w} D₁} {Φ₂' : DivMonoid.{w} D₂} {ιΦ₁ : DivHom Φ₁'.toGrpOn Φ₁.toGrpOn}
  {ιΦ₂ : DivHom Φ₂'.toGrpOn Φ₂.toGrpOn}

include hbe in
/-- **Category-theoreticity of `Ψ_{C_v}`** ([IUTchII], Example 3.2(ii); [IUTchI], Example 3.2(iii)):
if `F` preserves base-field-theoretic morphisms (in both directions; [EtTh], Corollary 3.8(i),(ii)),
`F^birat` maps `{b : Div(b) ∈ Φ^bs-fld}` at `Y` onto the same set at `F Y`. -/
theorem mem_bsFld_mapUnit_iff
    (hpos₁ : ∀ A x, x ∈ Φ₁'.pos A → ιΦ₁.app A x ∈ Φ₁.pos A)
    (hpos₂ : ∀ A x, x ∈ Φ₂'.pos A → ιΦ₂.app A x ∈ Φ₂.pos A)
    (hbs : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ))
    {Y : Model Φ₁ B₁ divB₁} (b : B₁.obj Y.base) :
    (∃ y ∈ Φ₁'.pos Y.base, divB₁.app _ b = ιΦ₁.app _ y) ↔
      ∃ y ∈ Φ₂'.pos (F.obj Y).base, divB₂.app _ (mapUnit F hpre b) = ιΦ₂.app _ y := by
  constructor
  · rintro ⟨y, hy, e⟩
    let g : Y ⟶ Y := mk1 (𝟙 _) (divB₁.app _ b) (by rw [e]; exact hpos₁ _ _ hy) b (by simp)
    have hg : IsBsFld ιΦ₁ g := ⟨y, hy, e.symm⟩
    obtain ⟨y', hy', e'⟩ := (hbs g).1 hg
    have hu : (F.map g).u = mapUnit F hpre b := map_u_of_baseId F hpre hbe g rfl rfl
    have hb := map_base_of_baseId F hbe g rfl
    have h1 : (F.map g).deg = 1 := ((hpre g).1 (isPreStep_mk1 _ _ _ _ _)).1
    refine ⟨y', hy', ?_⟩
    rw [e', div_eq_divB_u (F.map g) hb h1, hu]
  · rintro ⟨y', hy', e'⟩
    let g' : F.obj Y ⟶ F.obj Y := mk1 (𝟙 _) (divB₂.app _ (mapUnit F hpre b))
      (by rw [e']; exact hpos₂ _ _ hy') (mapUnit F hpre b) (by simp)
    let g : Y ⟶ Y := F.preimage g'
    have hFg : F.map g = g' := F.map_preimage g'
    have hgb : g.base = 𝟙 _ := by
      refine (hbe g (𝟙 Y)).2 ?_
      rw [hFg, F.map_id]; rfl
    have hg1 : g.deg = 1 := ((hpre g).2 (by rw [hFg]; exact isPreStep_mk1 _ _ _ _ _)).1
    have hu := map_u_of_baseId F hpre hbe g hg1 hgb
    rw [hFg] at hu
    have hgu : g.u = b := mapUnit_injective F hpre hbe Y hu.symm
    obtain ⟨y, hy, e⟩ := (hbs g).2 (by rw [hFg]; exact ⟨y', hy', e'.symm⟩)
    refine ⟨y, hy, ?_⟩
    rw [← hgu, ← div_eq_divB_u g hgb hg1, e]

end Transport

end Model

end Frobenioid

end Iut
