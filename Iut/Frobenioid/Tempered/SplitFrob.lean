/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EnvTransport
import Iut.Frobenioid.OrbitMap

/-!
# Split Frobenioids ([IUTchI], Example 3.2(iv),(v); [FrdI], Definition 2.3)

[IUTchI], Example 3.2(v) (l.3837–3934 of `~/iut-scratch/wall/txt/Inter-universal Teichmuller
Theory I.txt`): for `A^Θ ∈ D^Θ_v` the assignment

  `A^Θ ↦ O^×(T_{A^Θ}) · (Θ_v^ℕ|_{T_{A^Θ}}) ⊆ O^×(T^÷_{A^Θ})`

"determines a monoid `O^⊿_{C^Θ_v}(−)` on `D^Θ_v`", hence ([FrdII], Example 1.1(ii)) a `p_v`-adic
Frobenioid `C^Θ_v ⊆ F^÷_v` with base `D^Θ_v`, "equipped with a `μ_{2l}(−)`-orbit of characteristic
splittings `τ^Θ_v` determined by `Θ_v`". Example 3.2(iv) does the same for the `q`-parameter:
`Φ_{C^⊢_v} = ℕ · log_Φ(q̲_v)|_{D^⊢_v}` determines `C^⊢_v ⊆ C_v` with splittings `τ^⊢_v`. Relative to
the natural equivalence `D^⊢_v ≅ D^Θ_v`, `A ↦ A^Θ = Ÿ_v × A`, there are natural isomorphisms
`O^⊿_{C^⊢_v}(−) ≅ O^⊿_{C^Θ_v}(−)`, `O^×_{C^⊢_v}(−) ≅ O^×_{C^Θ_v}(−)` "compatible with the
assignment `q̲_v|_{T_A} ↦ Θ_v|_{T_{A^Θ}}` and the natural isomorphism [induced by the natural
projection `A^Θ = Ÿ_v × A → A`] `O^×(T_A) ≅ O^×(T_{A^Θ})`"; hence a natural equivalence
`C^⊢_v ≅ C^Θ_v` mapping `τ^⊢_v` to `τ^Θ_v`, written `F^⊢_v ≅ F^Θ_v`, where a **split Frobenioid**
is a Frobenioid equipped with a collection of characteristic splittings.

[FrdI], Definition 2.3: a **characteristic splitting** is a subfunctor `τ ⊆ O^⊿(−)` (on isotropic
objects and linear morphisms) such that `τ(A)` maps bijectively onto `O^⊿(A)^char`, i.e.
`O^×(A) × τ(A) ≅ O^⊿(A)`.

## Formalisation

* `thetaMon U θ = U · θ^ℕ ⊆ M` for an abelian group `M` (written additively), a subgroup `U` and
  `θ ∈ M`; if `θ` is non-torsion modulo `U` (`NonTorsionMod U θ`), `U × ℕ ≅ U · θ^ℕ`
  (`thetaMonEquiv`) and the units of `U · θ^ℕ` are `U` (`neg_mem_thetaMon_iff`).
* For a model Frobenioid `Model Φ B divB` ([FrdI], Theorem 5.2):
  `O^⊿(X) ≅ orhdSub X_D =
  {b ∈ B(X_D) : Div_B(b) ∈ Φ(X_D)}` (`Model.orhdEquivSub`), `O^×(X) ≅ unitSub X_D = Ker Div_B`
  (`Model.ounitsEquivSub`); **characteristic splittings** `Model.IsCharSplitting τ`: families
  `τ(A) ⊆ O^⊿` stable under all pull-backs (the linear morphisms of a model Frobenioid have
  arbitrary bases) with `O^× × τ ≅ O^⊿`.
* **The split Frobenioid of a group of units** ([FrdII], Example 1.1(ii) for the monoid
  `U · Θ^ℕ`): `SplitModel U`, the model Frobenioid over `E` with `Φ = ℕ` (fixed value),
  `B = U × ℤ`, `Div_B = pr₂`; a Frobenioid (`SplitModel.isFrobenioid`), with `O^⊿ = U × ℕ`,
  `O^× = U × 0`, and the standard characteristic splitting
  `0 × ℕ` (`SplitModel.isCharSplitting_std`)
  together with its orbit under natural torsion units (`SplitModel.isCharSplitting_twist`: the
  `μ_{2l}(−)`-orbit).
* **Realisation inside `F^÷_v`** (`SplitModel.realize`): for a natural family `θ_A ∈ B(j A)` of
  rational functions of a model Frobenioid along a functor `j : E ⥤ D` and the units
  `U = O^×(T_{j(−)})`, `(u, n) ↦ u + n·θ` is injective when `θ` is non-torsion modulo units and maps
  `O^⊿_{SplitModel}(A)` onto `O^×(T_{jA}) · θ^ℕ` (`SplitModel.realize_orhd`), units onto units:
  this is "the monoid `O^⊿_{C^Θ_v}(−)` determines a `p_v`-adic Frobenioid `C^Θ_v ⊆ F^÷_v`".
* **Functoriality** (`SplitModel.mapFunctor`): an equivalence `e : E₁ ⥤ E₂` with natural additive
  isomorphisms `U₁(A) ≅ U₂(e A)` induces an equivalence `SplitModel U₁ ⥤ SplitModel U₂` over `e`
  mapping the standard splitting to the standard splitting, and compatible with the realisations
  for `θ₁ ↦ θ₂` (`SplitModel.realize_mapFunctor`).
* **[IUTchI], Example 3.2(v)** (`SplitModel.exampleEquiv`, `SplitModel.example_realize`): for a
  model Frobenioid `C` over `D`, the inclusion `j : D^⊢ ⥤ D`, the functor `jΘ : D^⊢ ⥤ D`
  (`A ↦ Ÿ × A`) with the natural projection `pr : jΘ ⟶ j`, a natural family `q̲` on `j` and `Θ` on
  `jΘ`, and the hypothesis that `pr^*` is bijective on units (the base field of `Ÿ_v` is `K_v`,
  [IUTchI], Example 3.2(v), Definition 3.1(e)), the equivalence `F^⊢_v ≅ F^Θ_v` over
  `D^⊢_v ≅ D^Θ_v`, compatible with `q̲|_{T_A} ↦ Θ|_{T_{A^Θ}}` and with `pr^*` on units.

Here `D^Θ_v` is represented by `D^⊢_v` itself (the equivalence `D^⊢_v ≅ D^Θ_v` of Example 3.2(v) is
`A ↦ Ÿ × A`, so `jΘ` is the composite `D^⊢_v ≅ D^Θ_v ⊆ (D_v)_Ÿ → D_v`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v v₁ v₂ u u₁ u₂

/-! ### The monoids `U · θ^ℕ` -/

section ThetaMon

variable {M : Type*} [AddCommGroup M]

/-- **`U · θ^ℕ ⊆ M`**: the elements `u + n·θ`, `u ∈ U`, `n ∈ ℕ` (additive notation for
`O^×(−) · Θ^ℕ`). -/
def thetaMon (U : AddSubgroup M) (θ : M) : AddSubmonoid M where
  carrier := {x | ∃ u ∈ U, ∃ n : ℕ, x = u + n • θ}
  add_mem' := by
    rintro _ _ ⟨u, hu, n, rfl⟩ ⟨u', hu', n', rfl⟩
    exact ⟨u + u', U.add_mem hu hu', n + n', by rw [add_nsmul]; abel⟩
  zero_mem' := ⟨0, U.zero_mem, 0, by simp⟩

lemma mem_thetaMon {U : AddSubgroup M} {θ x : M} :
    x ∈ thetaMon U θ ↔ ∃ u ∈ U, ∃ n : ℕ, x = u + n • θ := Iff.rfl

lemma add_mem_thetaMon {U : AddSubgroup M} {θ u : M} (hu : u ∈ U) (n : ℕ) :
    u + n • θ ∈ thetaMon U θ := ⟨u, hu, n, rfl⟩

lemma le_thetaMon (U : AddSubgroup M) (θ : M) : U.toAddSubmonoid ≤ thetaMon U θ :=
  fun u hu => ⟨u, hu, 0, by simp⟩

lemma theta_mem_thetaMon (U : AddSubgroup M) (θ : M) : θ ∈ thetaMon U θ :=
  ⟨0, U.zero_mem, 1, by simp⟩

/-- `θ` is **non-torsion modulo `U`**: `n·θ ∈ U` only for `n = 0` (for `U = O^×`, `θ = Θ`:
`Div(Θ) ≠ 0` in a torsion-free group of divisors). -/
def NonTorsionMod (U : AddSubgroup M) (θ : M) : Prop := ∀ n : ℤ, n • θ ∈ U → n = 0

lemma NonTorsionMod.of_divHom {N : Type*} [AddCommGroup N] {d : M →+ N} {θ : M}
    (h : ∀ n : ℤ, n • d θ = 0 → n = 0) : NonTorsionMod d.ker θ :=
  fun n hn => h n (by rw [← map_zsmul]; exact hn)

lemma NonTorsionMod.unique {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) {u u' : M}
    (hu : u ∈ U) (hu' : u' ∈ U) {n n' : ℕ} (e : u + n • θ = u' + n' • θ) : u = u' ∧ n = n' := by
  have hn : ((n : ℤ) - n') • θ ∈ U := by
    have : ((n : ℤ) - n') • θ = u' - u := by
      rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
      linear_combination (norm := abel) e
    rw [this]
    exact U.sub_mem hu' hu
  have hnn : n = n' := by
    have := h _ hn
    omega
  subst hnn
  exact ⟨add_right_cancel e, rfl⟩

lemma NonTorsionMod.smul {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) {k : ℕ} (hk : 0 < k) :
    NonTorsionMod U (k • θ) := fun n hn => by
  have := h (n * k) (by rw [mul_zsmul, natCast_zsmul]; exact hn)
  rcases mul_eq_zero.1 this with h' | h'
  · exact h'
  · omega

/-- The units of `U · θ^ℕ` are `U` (for `θ` non-torsion modulo `U`). -/
theorem neg_mem_thetaMon_iff {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) {x : M}
    (hx : x ∈ thetaMon U θ) : -x ∈ thetaMon U θ ↔ x ∈ U := by
  refine ⟨fun hx' => ?_, fun hx' => le_thetaMon U θ (U.neg_mem hx')⟩
  obtain ⟨u, hu, n, rfl⟩ := hx
  obtain ⟨u', hu', n', e⟩ := hx'
  have e' : (-u) + 0 • θ = u' + (n + n') • θ := by
    rw [add_nsmul, zero_smul]
    linear_combination (norm := abel) e
  have := (h.unique (U.neg_mem hu) hu' e').2
  have hn : n = 0 := by omega
  subst hn
  simpa using hu

/-- The map `U × ℕ → U · θ^ℕ`, `(u, n) ↦ u + n·θ`. -/
def thetaMonHom (U : AddSubgroup M) (θ : M) : U × ℕ →+ thetaMon U θ where
  toFun p := ⟨p.1 + p.2 • θ, add_mem_thetaMon p.1.2 _⟩
  map_zero' := by ext; simp
  map_add' p q := by
    ext
    simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, AddSubmonoid.coe_add, add_nsmul]
    abel

/-- **The splitting `U × ℕ ≅ U · θ^ℕ`** ([FrdI], Definition 2.3(a) for the splitting `θ^ℕ`). -/
noncomputable def thetaMonEquiv {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ) :
    U × ℕ ≃+ thetaMon U θ :=
  AddEquiv.ofBijective (thetaMonHom U θ) ⟨fun p q e => by
    have e' : (p.1 : M) + p.2 • θ = q.1 + q.2 • θ := congrArg Subtype.val e
    obtain ⟨h₁, h₂⟩ := h.unique p.1.2 q.1.2 e'
    exact Prod.ext (Subtype.ext h₁) h₂, fun x => by
    obtain ⟨u, hu, n, e⟩ := x.2
    exact ⟨(⟨u, hu⟩, n), Subtype.ext e.symm⟩⟩

@[simp] lemma thetaMonEquiv_apply {U : AddSubgroup M} {θ : M} (h : NonTorsionMod U θ)
    (p : U × ℕ) : (thetaMonEquiv h p : M) = p.1 + p.2 • θ := rfl

/-- The image of `U · θ^ℕ` under an additive isomorphism mapping `U` onto `U'` and `θ` to `θ'`
is `U' · θ'^ℕ`. -/
theorem thetaMon_map {M' : Type*} [AddCommGroup M'] (f : M ≃+ M') {U : AddSubgroup M}
    {U' : AddSubgroup M'} (hU : ∀ x, x ∈ U ↔ f x ∈ U') (θ : M) :
    (thetaMon U θ).map f.toAddMonoidHom = thetaMon U' (f θ) := by
  ext y
  simp only [AddSubmonoid.mem_map, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨x, ⟨u, hu, n, rfl⟩, rfl⟩
    exact ⟨f u, (hU u).1 hu, n, by rw [map_add, map_nsmul]⟩
  · rintro ⟨u', hu', n, rfl⟩
    refine ⟨f.symm u' + n • θ, ⟨f.symm u', (hU _).2 (by simpa using hu'), n, rfl⟩, ?_⟩
    rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]

end ThetaMon

/-! ### `O^⊿`, `O^×` and characteristic splittings of a model Frobenioid -/

namespace Model

section CharSplit

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

variable (divB) in
/-- **`O^⊿(T_A) ⊆ B(A)`**: rational functions with effective divisor. -/
def orhdSub (A : D) : AddSubmonoid (B.obj A) where
  carrier := {b | divB.app A b ∈ Φ.pos A}
  add_mem' {a b} ha hb := by
    change divB.app A (a + b) ∈ Φ.pos A
    rw [map_add]; exact (Φ.pos A).add_mem ha hb
  zero_mem' := by
    change divB.app A 0 ∈ Φ.pos A
    rw [map_zero]; exact (Φ.pos A).zero_mem

variable (divB) in
/-- **`O^×(T_A) ⊆ B(A)`**: rational functions with trivial divisor (`Ker Div_B`). -/
abbrev unitSub (A : D) : AddSubgroup (B.obj A) := (divB.app A).ker

lemma mem_orhdSub {A : D} {b : B.obj A} : b ∈ orhdSub divB A ↔ divB.app A b ∈ Φ.pos A := Iff.rfl

lemma unitSub_le_orhdSub (A : D) : (unitSub divB A).toAddSubmonoid ≤ orhdSub divB A := by
  intro b hb
  change divB.app A b = 0 at hb
  change divB.app A b ∈ Φ.pos A
  rw [hb]; exact (Φ.pos A).zero_mem

lemma pb_mem_orhdSub {A A' : D} (f : A ⟶ A') {b : B.obj A'} (hb : b ∈ orhdSub divB A') :
    B.pb f b ∈ orhdSub divB A := by
  change divB.app A (B.pb f b) ∈ Φ.pos A
  rw [divB.natural]; exact Φ.pb_mem f hb

lemma pb_mem_unitSub {A A' : D} (f : A ⟶ A') {b : B.obj A'} (hb : b ∈ unitSub divB A') :
    B.pb f b ∈ unitSub divB A := by
  change divB.app A (B.pb f b) = 0
  rw [divB.natural, show divB.app A' b = 0 from hb, map_zero]

/-- A base-identity linear endomorphism has zero divisor `Div_B(u)`. -/
lemma div_eq_divB_u {X : Model Φ B divB} (e : X ⟶ X) (hb : e.base = 𝟙 _) (h : e.deg = 1) :
    e.div = divB.app _ e.u := by
  have r := e.rel
  rw [h, hb, GrpOn.pb_id', PNat.one_coe, one_smul] at r
  exact add_left_cancel r

/-- **`O^⊿(X) ≅ {b ∈ B(X_D) : Div_B(b) ∈ Φ(X_D)}`** ([FrdI], Theorem 5.2(ii); Proposition 2.2). -/
noncomputable def orhdEquivSub (X : Model Φ B divB) : Orhd 𝐏 X ≃ orhdSub divB X.base where
  toFun a := ⟨a.1.u, by
    change divB.app _ a.1.u ∈ Φ.pos _
    rw [← div_eq_divB_u a.1 a.2.1 a.2.2]; exact a.1.div_mem⟩
  invFun b := ⟨mk1 (𝟙 _) (divB.app _ b.1) b.2 b.1 (by simp), rfl, rfl⟩
  left_inv a := by
    refine Subtype.ext (hom_ext ?_ a.2.1.symm ?_ rfl)
    · exact (show a.1.deg = 1 from a.2.2).symm
    · exact (div_eq_divB_u a.1 a.2.1 a.2.2).symm
  right_inv b := rfl

/-- **`O^×(X) ≅ Ker(Div_B : B(X_D) → Φ^gp(X_D))`**. -/
noncomputable def ounitsEquivSub (X : Model Φ B divB) : Ounits 𝐏 X ≃ unitSub divB X.base where
  toFun a := ⟨a.1.u, by
    obtain ⟨-, -, h₃⟩ := (isIso_iff a.1).mp a.2.1
    change divB.app _ a.1.u = 0
    rw [← div_eq_divB_u a.1 a.2.2.1 a.2.2.2]; exact h₃⟩
  invFun b :=
    let φ : X ⟶ X := mk1 (𝟙 _) 0 (Φ.pos _).zero_mem b.1 (by
      rw [show divB.app _ b.1 = 0 from b.2]; simp)
    ⟨φ, isIso_of φ rfl (inferInstanceAs (IsIso (𝟙 X.base))) rfl, rfl, rfl⟩
  left_inv a := by
    obtain ⟨h₁, -, h₃⟩ := (isIso_iff a.1).mp a.2.1
    exact Subtype.ext (hom_ext h₁.symm a.2.2.1.symm h₃.symm rfl)
  right_inv b := rfl

/-- **Characteristic splittings** of a model Frobenioid ([FrdI], Definition 2.3): submonoids
`τ(A) ⊆ O^⊿(T_A)`, stable under pull-back along every morphism of the base (the linear morphisms
of `C`; all objects of a model Frobenioid are isotropic), such that `O^×(T_A) × τ(A) ≅ O^⊿(T_A)`,
i.e. every element of `O^⊿` is uniquely a unit plus an element of `τ`. -/
structure IsCharSplitting (τ : ∀ A : D, AddSubmonoid (B.obj A)) : Prop where
  le : ∀ A, τ A ≤ orhdSub divB A
  pb_mem : ∀ {A A' : D} (f : A ⟶ A') {b : B.obj A'}, b ∈ τ A' → B.pb f b ∈ τ A
  exists_split : ∀ (A : D) (b : B.obj A), b ∈ orhdSub divB A →
    ∃ u ∈ unitSub divB A, ∃ t ∈ τ A, b = u + t
  split_unique : ∀ (A : D) (u u' t t' : B.obj A), u ∈ unitSub divB A → u' ∈ unitSub divB A →
    t ∈ τ A → t' ∈ τ A → u + t = u' + t' → u = u' ∧ t = t'

end CharSplit

end Model

/-! ### The split Frobenioid of a group of units -/

section SplitModel

variable {E : Type u} [Category.{v} E]

/-- `ℕ ⊆ ℤ`. -/
def intCone : AddSubmonoid (ULift.{w} ℤ) where
  carrier := {n | 0 ≤ n.down}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, ULift.add_down] at ha hb ⊢
    exact add_nonneg ha hb
  zero_mem' := le_refl (0 : ℤ)

lemma mem_intCone {n : ULift.{w} ℤ} : n ∈ intCone ↔ 0 ≤ n.down := Iff.rfl

variable (E) in
/-- **The fixed-value divisor monoid `ℕ`** on `E` (identity pull-backs): `ℕ · log_Φ(Θ)`. -/
abbrev natPhi : DivMonoid.{w} E where
  obj _ := ULift.{w} ℤ
  pb _ := AddMonoidHom.id _
  pb_id _ _ := rfl
  pb_comp _ _ _ := rfl
  pb_injective _ := Function.injective_id
  pb_bijective_of_fsm _ _ := Function.bijective_id
  pos _ := intCone
  pb_mem _ _ h := h
  sharp {_ x} h h' := by
    rw [mem_intCone] at h h'
    ext
    simp only [ULift.neg_down, Left.nonneg_neg_iff] at h'
    exact le_antisymm h' h
  saturated {_ x} n hn h := by
    rw [mem_intCone] at h ⊢
    rw [ULift.smul_down, nsmul_eq_mul] at h
    exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hn)
  generating {_} x := by
    refine ⟨⟨max x.down 0⟩, show (0 : ℤ) ≤ max x.down 0 from le_max_right _ _,
      ⟨max (-x.down) 0⟩, show (0 : ℤ) ≤ max (-x.down) 0 from le_max_right _ _, ?_⟩
    ext
    change x.down = max x.down 0 - max (-x.down) 0
    omega
  pos_surj_of_fsm _ _ y hy := ⟨y, hy, rfl⟩

/-- **`B = U × ℤ`**: the rational functions `u · Θ^n`. -/
abbrev splitB (U : GrpOn.{w} E) : GrpOn.{w} E where
  obj A := U.obj A × ULift.{w} ℤ
  pb f := (U.pb f).prodMap (AddMonoidHom.id _)
  pb_id A x := by ext <;> simp
  pb_comp f g x := by ext <;> simp [U.pb_comp]
  pb_injective f x y h := by
    rw [Prod.ext_iff] at h
    exact Prod.ext (U.pb_injective f h.1) h.2
  pb_bijective_of_fsm f hf := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · rw [Prod.ext_iff] at h
      exact Prod.ext ((U.pb_bijective_of_fsm f hf).1 h.1) h.2
    · obtain ⟨a, ha⟩ := (U.pb_bijective_of_fsm f hf).2 y.1
      exact ⟨(a, y.2), Prod.ext ha rfl⟩

@[simp] lemma splitB_pb {U : GrpOn.{w} E} {A A' : E} (f : A ⟶ A') (x : (splitB U).obj A') :
    (splitB U).pb f x = (U.pb f x.1, x.2) := rfl

/-- `Div_B = pr₂ : U × ℤ → ℤ` (the exponent of `Θ`). -/
def splitDiv (U : GrpOn.{w} E) : DivHom (splitB U) (natPhi E).toGrpOn where
  app _ := AddMonoidHom.snd _ _
  natural _ _ := rfl

/-- **The split Frobenioid `C^Θ` of the monoid `U · Θ^ℕ`** ([FrdII], Example 1.1(ii); [IUTchI],
Example 3.2(iv),(v)): the model Frobenioid over `E` with `Φ = ℕ`, `B = U × ℤ`, `Div_B = pr₂`. -/
abbrev SplitModel (U : GrpOn.{w} E) : Type _ := Model (natPhi E) (splitB U) (splitDiv U)

namespace SplitModel

variable (U : GrpOn.{w} E)

/-- `SplitModel U` is a Frobenioid ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid [IsConnected E] [TotallyEpimorphic E] :
    IsFrobenioid (Model.toElem (natPhi E) (splitB U) (splitDiv U)) :=
  Model.isFrobenioid

lemma mem_orhdSub {A : E} {b : (splitB U).obj A} :
    b ∈ Model.orhdSub (splitDiv U) A ↔ 0 ≤ b.2.down := Iff.rfl

lemma mem_unitSub {A : E} {b : (splitB U).obj A} :
    b ∈ Model.unitSub (splitDiv U) A ↔ b.2 = 0 := Iff.rfl

/-- **The standard characteristic splitting** `τ(A) = 0 × ℕ` (the powers of `Θ`). -/
def stdSplit (A : E) : AddSubmonoid ((splitB U).obj A) where
  carrier := {b | b.1 = 0 ∧ 0 ≤ b.2.down}
  add_mem' {a b} ha hb := ⟨by simp [ha.1, hb.1], by
    simp only [Prod.snd_add, ULift.add_down]; exact add_nonneg ha.2 hb.2⟩
  zero_mem' := ⟨rfl, le_refl (0 : ℤ)⟩

/-- **The twisted characteristic splitting** `τ_ζ(A) = {(n·ζ_A, n)}` for a natural family `ζ` of
torsion units (`N·ζ = 0`): the splittings determined by the `μ_N`-multiples `ζ·Θ` of `Θ`. -/
def twistSplit (ζ : ∀ A, U.obj A) (A : E) : AddSubmonoid ((splitB U).obj A) where
  carrier := {b | 0 ≤ b.2.down ∧ b.1 = b.2.down.toNat • ζ A}
  add_mem' {a b} ha hb := ⟨by
    simp only [Prod.snd_add, ULift.add_down]; exact add_nonneg ha.1 hb.1, by
    simp only [Prod.fst_add, Prod.snd_add, ULift.add_down]
    rw [ha.2, hb.2, ← add_nsmul, Int.toNat_add ha.1 hb.1]⟩
  zero_mem' := ⟨le_refl (0 : ℤ), by simp⟩

lemma twistSplit_zero (A : E) : twistSplit U (fun _ => 0) A = stdSplit U A := by
  ext b
  simp only [twistSplit, stdSplit, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    smul_zero]
  tauto

/-- **The `μ`-orbit of characteristic splittings** ([IUTchI], Example 3.2(iv),(v): "a
`μ_{2l}(−)`-orbit of characteristic splittings"): for every natural family `ζ` of units,
`τ_ζ` is a characteristic splitting of `SplitModel U`. -/
theorem isCharSplitting_twist (ζ : ∀ A, U.obj A)
    (hζ : ∀ {A A' : E} (f : A ⟶ A'), U.pb f (ζ A') = ζ A) :
    Model.IsCharSplitting (divB := splitDiv U) (twistSplit U ζ) where
  le A b hb := hb.1
  pb_mem f b hb := ⟨hb.1, by
    change U.pb f b.1 = _
    rw [hb.2, map_nsmul, hζ]
    rfl⟩
  exists_split A b hb := by
    refine ⟨(b.1 - b.2.down.toNat • ζ A, 0), rfl, (b.2.down.toNat • ζ A, b.2), ⟨hb, rfl⟩, ?_⟩
    ext
    · simp
    · simp
  split_unique A u u' t t' hu hu' ht ht' e := by
    have hu0 : u.2 = 0 := hu
    have hu0' : u'.2 = 0 := hu'
    have e2 := congrArg Prod.snd e
    simp only [Prod.snd_add, hu0, hu0', zero_add] at e2
    have e1 := congrArg Prod.fst e
    simp only [Prod.fst_add] at e1
    rw [ht.2, ht'.2, e2] at e1
    have hu1 : u.1 = u'.1 := add_right_cancel e1
    exact ⟨Prod.ext hu1 (hu0.trans hu0'.symm), Prod.ext (by rw [ht.2, ht'.2, e2]) e2⟩

/-- **The standard characteristic splitting** `0 × ℕ` of `SplitModel U`. -/
theorem isCharSplitting_std :
    Model.IsCharSplitting (divB := splitDiv U) (stdSplit U) := by
  have h := isCharSplitting_twist U (fun _ => 0) (fun f => map_zero _)
  rwa [show twistSplit U (fun _ => 0) = stdSplit U from funext (twistSplit_zero U)] at h

end SplitModel

end SplitModel

/-! ### Realisation inside the birationalization -/

section Realize

variable {E : Type u₁} [Category.{v₁} E] {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} (divB : DivHom B Φ.toGrpOn)
variable (j : E ⥤ D)

/-- `θ` is a **natural family of rational functions** along `j`: `θ_A ∈ B(j A)` with
`(j f)^* θ_{A'} = θ_A`. -/
def IsNatFamily (θ : ∀ A : E, B.obj (j.obj A)) : Prop :=
  ∀ ⦃A A' : E⦄ (f : A ⟶ A'), B.pb (j.map f) (θ A') = θ A

variable (hj : ∀ {A A' : E} (f : A ⟶ A'), IsFSM f → IsFSM (j.map f))

/-- **The units `O^×(T_{j(−)})`** as a group-like monoid on `E`. -/
abbrev unitGrpOn : GrpOn.{w} E where
  obj A := Model.unitSub divB (j.obj A)
  pb f :=
    { toFun := fun x => ⟨B.pb (j.map f) x.1, Model.pb_mem_unitSub _ x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  pb_id A x := Subtype.ext (by simp)
  pb_comp f g x := Subtype.ext (by simp)
  pb_injective f x y h := Subtype.ext (B.pb_injective _ (congrArg Subtype.val h))
  pb_bijective_of_fsm f hf := by
    refine ⟨fun x y h => Subtype.ext (B.pb_injective _ (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (B.pb_bijective_of_fsm _ (hj f hf)).2 y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change divB.app _ x = 0
    have hy : divB.app _ y.1 = 0 := y.2
    rw [← hx, divB.natural] at hy
    exact Φ.pb_injective _ (by rw [hy, map_zero])

@[simp] lemma unitGrpOn_pb_coe {A A' : E} (f : A ⟶ A') (x : (unitGrpOn divB j hj).obj A') :
    (((unitGrpOn divB j hj).pb f x : Model.unitSub divB (j.obj A)) : B.obj (j.obj A)) =
      B.pb (j.map f) x.1 := rfl

variable (θ : ∀ A : E, B.obj (j.obj A))

/-- **The realisation** `(u, n) ↦ u · θ^n` of the rational functions of `SplitModel` in the
birationalization of the model Frobenioid (`O^×(T^÷_{jA}) = B(jA)`). -/
def SplitModel.realize (A : E) (b : (splitB (unitGrpOn divB j hj)).obj A) : B.obj (j.obj A) :=
  (b.1 : B.obj (j.obj A)) + b.2.down • θ A

variable {divB j hj θ}

lemma SplitModel.realize_add (A : E) (a b : (splitB (unitGrpOn divB j hj)).obj A) :
    SplitModel.realize divB j hj θ A (a + b) =
      SplitModel.realize divB j hj θ A a + SplitModel.realize divB j hj θ A b := by
  change ((a.1 + b.1 : Model.unitSub divB (j.obj A)) : B.obj _) + (a.2.down + b.2.down) • θ A = _
  rw [add_zsmul, AddSubgroup.coe_add]
  simp only [SplitModel.realize]
  abel

/-- The realisation is natural for natural families. -/
lemma SplitModel.realize_pb (hθ : IsNatFamily j θ) {A A' : E} (f : A ⟶ A')
    (b : (splitB (unitGrpOn divB j hj)).obj A') :
    SplitModel.realize divB j hj θ A ((splitB (unitGrpOn divB j hj)).pb f b) =
      B.pb (j.map f) (SplitModel.realize divB j hj θ A' b) := by
  change B.pb (j.map f) b.1.1 + b.2.down • θ A = B.pb (j.map f) (b.1.1 + b.2.down • θ A')
  rw [map_add, map_zsmul, hθ f]

/-- The realisation is injective when `θ` is non-torsion modulo units. -/
theorem SplitModel.realize_injective {A : E}
    (h : NonTorsionMod (Model.unitSub divB (j.obj A)) (θ A)) :
    Function.Injective (SplitModel.realize divB j hj θ A) := by
  intro a b hab
  change a.1.1 + a.2.down • θ A = b.1.1 + b.2.down • θ A at hab
  have h1 : (a.2.down - b.2.down) • θ A ∈ Model.unitSub divB (j.obj A) := by
    have : (a.2.down - b.2.down) • θ A = b.1.1 - a.1.1 := by
      rw [sub_zsmul]; linear_combination (norm := abel) hab
    rw [this]; exact (Model.unitSub divB _).sub_mem b.1.2 a.1.2
  have h2 : a.2.down = b.2.down := by have := h _ h1; omega
  rw [h2, add_left_inj] at hab
  exact Prod.ext (Subtype.ext hab) (ULift.ext _ _ h2)

/-- **The monoid `O^⊿_{C^Θ}(A) = O^×(T_{jA}) · θ^ℕ`** ([IUTchI], Example 3.2(v)): the realisation
maps `O^⊿_{SplitModel}(T_A) = U × ℕ` onto `O^×(T_{jA}) · θ_A^ℕ ⊆ O^×(T^÷_{jA})`. -/
theorem SplitModel.realize_orhd (A : E) (x : B.obj (j.obj A)) :
    x ∈ thetaMon (Model.unitSub divB (j.obj A)) (θ A) ↔
      ∃ b ∈ Model.orhdSub (splitDiv (unitGrpOn divB j hj)) A,
        SplitModel.realize divB j hj θ A b = x := by
  constructor
  · rintro ⟨u, hu, n, rfl⟩
    exact ⟨(⟨u, hu⟩, ⟨n⟩), show (0 : ℤ) ≤ n from Int.natCast_nonneg n, by
      simp [SplitModel.realize, natCast_zsmul]⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b.1.1, b.1.2, b.2.down.toNat, ?_⟩
    have hb' : 0 ≤ b.2.down := hb
    simp only [SplitModel.realize]
    rw [← natCast_zsmul, Int.toNat_of_nonneg hb']

/-- **The units**: the realisation maps `O^×_{SplitModel}(T_A) = U × 0` onto `O^×(T_{jA})`. -/
theorem SplitModel.realize_unit (A : E) (x : B.obj (j.obj A)) :
    x ∈ Model.unitSub divB (j.obj A) ↔
      ∃ b ∈ Model.unitSub (splitDiv (unitGrpOn divB j hj)) A,
        SplitModel.realize divB j hj θ A b = x := by
  constructor
  · intro hx
    exact ⟨(⟨x, hx⟩, 0), rfl, by simp [SplitModel.realize]⟩
  · rintro ⟨b, hb, rfl⟩
    have hb' : b.2 = 0 := hb
    simp only [SplitModel.realize, hb', ULift.zero_down, zero_zsmul, add_zero]
    exact b.1.2

/-- **The characteristic splitting `τ^Θ`**: the standard splitting is realised as `θ^ℕ`. -/
theorem SplitModel.realize_std (A : E) (x : B.obj (j.obj A)) :
    x ∈ thetaMon ⊥ (θ A) ↔
      ∃ b ∈ SplitModel.stdSplit (unitGrpOn divB j hj) A,
        SplitModel.realize divB j hj θ A b = x := by
  constructor
  · rintro ⟨u, hu, n, rfl⟩
    rw [AddSubgroup.mem_bot] at hu
    subst hu
    exact ⟨(0, ⟨n⟩), ⟨rfl, show (0 : ℤ) ≤ n from Int.natCast_nonneg n⟩, by
      simp [SplitModel.realize, natCast_zsmul]⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨0, (⊥ : AddSubgroup _).zero_mem, b.2.down.toNat, ?_⟩
    simp only [SplitModel.realize, hb.1, ZeroMemClass.coe_zero, zero_add]
    rw [← natCast_zsmul, Int.toNat_of_nonneg hb.2]

/-- **`O^×(T_{(−)}) · θ^ℕ` is a monoid on `E`** ([IUTchI], Example 3.2(v), "determines a monoid
`O^⊿_{C^Θ_v}(−)` on `D^Θ_v`"): it is stable under pull-back. -/
lemma pb_mem_thetaMon (hθ : IsNatFamily j θ) {A A' : E} (f : A ⟶ A') {x : B.obj (j.obj A')}
    (hx : x ∈ thetaMon (Model.unitSub divB (j.obj A')) (θ A')) :
    B.pb (j.map f) x ∈ thetaMon (Model.unitSub divB (j.obj A)) (θ A) := by
  obtain ⟨u, hu, n, rfl⟩ := hx
  exact ⟨B.pb (j.map f) u, Model.pb_mem_unitSub _ hu, n, by rw [map_add, map_nsmul, hθ f]⟩

end Realize

/-! ### Functoriality of split Frobenioids -/

section MapFunctor

variable {E₁ : Type u₁} [Category.{v₁} E₁] {E₂ : Type u₂} [Category.{v₂} E₂]
variable {U₁ : GrpOn.{w} E₁} {U₂ : GrpOn.{w} E₂}
variable (e : E₁ ⥤ E₂) (ι : ∀ A : E₁, U₁.obj A ≃+ U₂.obj (e.obj A))
  (hι : ∀ ⦃A A' : E₁⦄ (f : A ⟶ A') (x : U₁.obj A'), ι A (U₁.pb f x) = U₂.pb (e.map f) (ι A' x))

namespace SplitModel

/-- **The functor `SplitModel U₁ ⥤ SplitModel U₂`** over `e`, `(A, α) ↦ (e A, α)`,
`(n, f, d, (u, k)) ↦ (n, e f, d, (ι u, k))`. -/
def mapFunctor : SplitModel U₁ ⥤ SplitModel U₂ where
  obj X := ⟨e.obj X.base, X.α⟩
  map φ := ⟨φ.deg, e.map φ.base, φ.div, φ.div_mem, (ι _ φ.u.1, φ.u.2), φ.rel⟩
  map_id X := Model.hom_ext rfl (e.map_id _) rfl (by
    change (ι X.base 0, (0 : ULift ℤ)) = (0 : U₂.obj _ × ULift ℤ)
    rw [map_zero]; rfl)
  map_comp φ ψ := Model.hom_ext rfl (e.map_comp _ _) rfl (Prod.ext (by
    change ι _ (U₁.pb φ.base ψ.u.1 + (ψ.deg : ℕ) • φ.u.1) =
      U₂.pb (e.map φ.base) (ι _ ψ.u.1) + (ψ.deg : ℕ) • ι _ φ.u.1
    rw [map_add, map_nsmul, hι]) rfl)

@[simp] lemma mapFunctor_obj (X : SplitModel U₁) :
    (mapFunctor e ι hι).obj X = ⟨e.obj X.base, X.α⟩ := rfl

@[simp] lemma mapFunctor_map_u {X Y : SplitModel U₁} (φ : X ⟶ Y) :
    ((mapFunctor e ι hι).map φ).u = (ι _ φ.u.1, φ.u.2) := rfl

@[simp] lemma mapFunctor_map_base {X Y : SplitModel U₁} (φ : X ⟶ Y) :
    ((mapFunctor e ι hι).map φ).base = e.map φ.base := rfl

/-- **`mapFunctor` maps the standard characteristic splitting to the standard splitting**: on
`O^⊿ = U × ℕ` it is `(u, n) ↦ (ι u, n)`, which maps `0 × ℕ` onto `0 × ℕ`. -/
lemma map_stdSplit (A : E₁) (b : (splitB U₁).obj A) :
    b ∈ stdSplit U₁ A ↔ ((ι A b.1, b.2) : (splitB U₂).obj (e.obj A)) ∈ stdSplit U₂ (e.obj A) := by
  change (b.1 = 0 ∧ 0 ≤ b.2.down) ↔ (ι A b.1 = 0 ∧ 0 ≤ b.2.down)
  rw [AddEquivClass.map_eq_zero_iff]

variable [e.IsEquivalence]

instance : (mapFunctor e ι hι).Faithful where
  map_injective {X Y} φ ψ h := by
    have h₁' := congrArg Model.Hom.deg h
    have h₃' := congrArg Model.Hom.div h
    have h₁ : φ.deg = ψ.deg := h₁'
    have h₂ : e.map φ.base = e.map ψ.base := congrArg Model.Hom.base h
    have h₃ : φ.div = ψ.div := h₃'
    have h₄ : ((ι _ φ.u.1, φ.u.2) : (splitB U₂).obj _) = (ι _ ψ.u.1, ψ.u.2) :=
      congrArg Model.Hom.u h
    rw [Prod.mk.injEq] at h₄
    exact Model.hom_ext h₁ (e.map_injective h₂) h₃ (Prod.ext ((ι _).injective h₄.1) h₄.2)

instance : (mapFunctor e ι hι).Full where
  map_surjective {X Y} ψ := by
    refine ⟨⟨ψ.deg, e.preimage ψ.base, ψ.div, ψ.div_mem, ((ι _).symm ψ.u.1, ψ.u.2), ψ.rel⟩, ?_⟩
    refine Model.hom_ext rfl (e.map_preimage _) rfl ?_
    change (ι _ ((ι _).symm ψ.u.1), ψ.u.2) = ψ.u
    rw [AddEquiv.apply_symm_apply]
    rfl

instance : (mapFunctor e ι hι).EssSurj where
  mem_essImage Y := by
    let i : e.obj (e.objPreimage Y.base) ≅ Y.base := e.objObjPreimageIso Y.base
    let φ : (mapFunctor e ι hι).obj ⟨e.objPreimage Y.base, Y.α⟩ ⟶ Y :=
      Model.mk1 i.hom 0 (intCone.{w}).zero_mem 0 (by
        change Y.α + 0 = Y.α + 0
        rfl)
    haveI : IsIso φ := Model.isIso_of φ rfl (inferInstanceAs (IsIso i.hom)) rfl
    exact ⟨_, ⟨asIso φ⟩⟩

/-- **`mapFunctor` is an equivalence** (for an equivalence `e` of bases). -/
instance : (mapFunctor e ι hι).IsEquivalence where

end SplitModel

end MapFunctor

/-! ### [IUTchI], Example 3.2(v): `F^⊢_v ≅ F^Θ_v` -/

section Example

variable {E : Type u₁} [Category.{v₁} E] {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
variable (j jΘ : E ⥤ D) (pr : jΘ ⟶ j)
  (hj : ∀ {A A' : E} (f : A ⟶ A'), IsFSM f → IsFSM (j.map f))
  (hjΘ : ∀ {A A' : E} (f : A ⟶ A'), IsFSM f → IsFSM (jΘ.map f))

/-- `pr^* : O^×(T_A) → O^×(T_{A^Θ})`. -/
def prUnit (A : E) : Model.unitSub divB (j.obj A) →+ Model.unitSub divB (jΘ.obj A) where
  toFun x := ⟨B.pb (pr.app A) x.1, Model.pb_mem_unitSub _ x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (hpr : ∀ A, Function.Bijective (prUnit (divB := divB) j jΘ pr A))

/-- The natural isomorphism `O^×(T_A) ≅ O^×(T_{A^Θ})` induced by the projection `A^Θ → A`. -/
noncomputable def prUnitEquiv (A : E) :
    (unitGrpOn divB j hj).obj A ≃+ (unitGrpOn divB jΘ hjΘ).obj ((𝟭 E).obj A) :=
  AddEquiv.ofBijective (prUnit j jΘ pr A) (hpr A)

include pr in
lemma prUnitEquiv_natural ⦃A A' : E⦄ (f : A ⟶ A') (x : (unitGrpOn divB j hj).obj A') :
    prUnitEquiv j jΘ pr hj hjΘ hpr A ((unitGrpOn divB j hj).pb f x) =
      (unitGrpOn divB jΘ hjΘ).pb ((𝟭 E).map f) (prUnitEquiv j jΘ pr hj hjΘ hpr A' x) := by
  apply Subtype.ext
  change B.pb (pr.app A) (B.pb (j.map f) x.1) = B.pb (jΘ.map f) (B.pb (pr.app A') x.1)
  rw [← GrpOn.pb_comp', ← GrpOn.pb_comp', pr.naturality]

/-- **The natural equivalence `C^⊢_v ≅ C^Θ_v`** ([IUTchI], Example 3.2(v)) over
`D^⊢_v ≅ D^Θ_v`, induced by `pr^*` on units; it maps the splitting `τ^⊢_v` (the powers of `q̲`) to
`τ^Θ_v` (the powers of `Θ`), `SplitModel.map_stdSplit`. -/
noncomputable def SplitModel.exampleEquiv :
    SplitModel (unitGrpOn divB j hj) ⥤ SplitModel (unitGrpOn divB jΘ hjΘ) :=
  SplitModel.mapFunctor (𝟭 E) (prUnitEquiv j jΘ pr hj hjΘ hpr)
    (prUnitEquiv_natural j jΘ pr hj hjΘ hpr)

noncomputable instance : (SplitModel.exampleEquiv j jΘ pr hj hjΘ hpr).IsEquivalence := by
  unfold SplitModel.exampleEquiv
  infer_instance

variable {j jΘ pr}

/-- **The monoid isomorphism `O^⊿_{C^⊢_v}(T_A) ≅ O^⊿_{C^Θ_v}(T_{A^Θ})`** ([IUTchI], Example
3.2(v)): `O^×(T_A) · q̲^ℕ ≅ O^×(T_{A^Θ}) · Θ^ℕ`, the realisation of `SplitModel.exampleEquiv` on
`O^⊿ = U × ℕ`. -/
noncomputable def SplitModel.exampleMonEquiv (q : ∀ A, B.obj (j.obj A)) (Θ : ∀ A, B.obj (jΘ.obj A))
    (A : E) (hq : NonTorsionMod (Model.unitSub divB (j.obj A)) (q A))
    (hΘ : NonTorsionMod (Model.unitSub divB (jΘ.obj A)) (Θ A)) :
    thetaMon (Model.unitSub divB (j.obj A)) (q A) ≃+
      thetaMon (Model.unitSub divB (jΘ.obj A)) (Θ A) :=
  (thetaMonEquiv hq).symm.trans
    (((prUnitEquiv j jΘ pr hj hjΘ hpr A).prodCongr (AddEquiv.refl ℕ)).trans (thetaMonEquiv hΘ))

/-- **Compatibility with `q̲|_{T_A} ↦ Θ|_{T_{A^Θ}}`.** -/
theorem SplitModel.exampleMonEquiv_q (q : ∀ A, B.obj (j.obj A)) (Θ : ∀ A, B.obj (jΘ.obj A))
    (A : E) (hq : NonTorsionMod (Model.unitSub divB (j.obj A)) (q A))
    (hΘ : NonTorsionMod (Model.unitSub divB (jΘ.obj A)) (Θ A)) :
    (SplitModel.exampleMonEquiv hj hjΘ hpr q Θ A hq hΘ
      ⟨q A, theta_mem_thetaMon _ _⟩ : B.obj (jΘ.obj A)) = Θ A := by
  have h : (thetaMonEquiv hq).symm ⟨q A, theta_mem_thetaMon _ _⟩ = (0, 1) :=
    (thetaMonEquiv hq).symm_apply_eq.2 (Subtype.ext (by simp))
  simp only [SplitModel.exampleMonEquiv, AddEquiv.trans_apply, h]
  change ((thetaMonEquiv hΘ (prUnitEquiv j jΘ pr hj hjΘ hpr A 0, 1) :
    ↥(thetaMon (Model.unitSub divB (jΘ.obj A)) (Θ A))) : B.obj (jΘ.obj A)) = Θ A
  rw [thetaMonEquiv_apply, map_zero]
  change (0 : B.obj (jΘ.obj A)) + (1 : ℕ) • Θ A = Θ A
  rw [one_smul, zero_add]

/-- **Compatibility with `pr^* : O^×(T_A) ≅ O^×(T_{A^Θ})`.** -/
theorem SplitModel.exampleMonEquiv_unit (q : ∀ A, B.obj (j.obj A)) (Θ : ∀ A, B.obj (jΘ.obj A))
    (A : E) (hq : NonTorsionMod (Model.unitSub divB (j.obj A)) (q A))
    (hΘ : NonTorsionMod (Model.unitSub divB (jΘ.obj A)) (Θ A)) (u : B.obj (j.obj A))
    (hu : u ∈ Model.unitSub divB (j.obj A)) :
    (SplitModel.exampleMonEquiv hj hjΘ hpr q Θ A hq hΘ
      ⟨u, le_thetaMon _ _ hu⟩ : B.obj (jΘ.obj A)) = B.pb (pr.app A) u := by
  have h : (thetaMonEquiv hq).symm ⟨u, le_thetaMon _ _ hu⟩ = (⟨u, hu⟩, 0) :=
    (thetaMonEquiv hq).symm_apply_eq.2 (Subtype.ext (by simp))
  simp only [SplitModel.exampleMonEquiv, AddEquiv.trans_apply, h]
  change ((thetaMonEquiv hΘ (prUnitEquiv j jΘ pr hj hjΘ hpr A ⟨u, hu⟩, 0) :
    ↥(thetaMon (Model.unitSub divB (jΘ.obj A)) (Θ A))) : B.obj (jΘ.obj A)) = _
  rw [thetaMonEquiv_apply, zero_smul, add_zero]
  rfl

end Example

end Frobenioid

end Iut
