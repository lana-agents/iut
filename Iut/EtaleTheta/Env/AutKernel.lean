/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Env.Reduction
import Iut.EtaleTheta.Env.PiX
import Iut.EtaleTheta.Env.Shift

/-!
# Automorphisms of the model environment over the identity of `Π_Y̲` ([EtTh], Cor. 2.18(iv))

[EtTh], Cor. 2.18(iv): the natural map `Isom^μ(M_α, M_β) → Isom(Π_X̲α, Π_X̲β)` is surjective with
fibres of cardinality 1 (resp. 2) for `N` odd (resp. even); in the proof, the kernel
`Ker(Aut^μ(M) → Aut(Π_X̲))` consists of automorphisms acting as the identity on `Π_Y̲`, and by
Cor. 2.19(i) also on `μ_N`, and is identified with `Hom(Π_Y̲/Π_Ÿ̲, μ_N)`.

This file treats the model environment `modelEnv` of the abstract theta setting
(`Env/Model.lean`), for finite `μ` and `Π_Y̲ = PY` with `FISlim PY` (finite-index slimness; the
shell-#29 debt, lead decision 2026-10-26):

* `mem_fiCentralizers_envY`, `apply_mem_range_inlY_iff`: every group automorphism of `Π_Y[μ]`
  preserves `μ` ([EtTh], Prop. 2.11(ii), finite-index form);
* `indPY`: the automorphism of `Π_Y = Π_Y[μ]/μ` induced by an automorphism of `Π_Y[μ]`;
  `autPY : Aut(modelEnv) →* Aut(Π_Y)` (the action on `Π_Y`; `Π_X̲` is recovered from it by
  `PiX.lean`, Cor. 2.18(iii));
* `ker_autPY_apply`: elements of the kernel lie over the identity of `Π_Y`;
* **`finite_ker_autPY`** (the finiteness half of Cor. 2.18(iv)): if `Π_Ÿ̲` has finite index in
  `Π_Y̲`, the kernel of `autPY` is finite; an element of the kernel is determined by its action
  on `μ`, the `μ`-conjugate of the theta section it produces, and its values on coset
  representatives of `Π_Y̲/Π_Ÿ̲`;
* **`ker_autPY_eq_conj_shift`** (the description of the kernel in [EtTh], proof of
  Cor. 2.18(iv)): an element of the kernel acting trivially on `μ` (which is what Cor. 2.19(i),
  `cyclotomicRigidity_envAut`, gives) is `inn(ζ) ∘ α_δ` for some `ζ ∈ μ` and a shifting
  automorphism `α_δ` (`Shift.lean`) by a cocycle `δ` on `Π_Y̲` that is trivial on `Π_Ÿ̲`;
  `cocycle_trivialOn_coset`, `cocycle_trivialOn_sq`, `cocycle_trivialOn_fixed`: such a `δ`
  takes one value on each coset of `Π_Ÿ̲`, so for `[Π_Y̲ : Π_Ÿ̲] = 2` it is determined by its
  value `c` at one `t ∈ Π_Y̲ ∖ Π_Ÿ̲`; `c · t(c) = 1` and `c` is fixed by `Π_Ÿ̲` — i.e.
  `δ ∈ Hom(Π_Y̲/Π_Ÿ̲, μ)` for `t` geometric (`c² = 1`), of order 1 or 2 for `μ = μ_N`.
-/

namespace Iut.EtaleTheta.Env

open SemidirectProduct
open scoped commutatorElement

universe u

variable {PX G μ : Type u} [Group PX] [Group G] [CommGroup μ] (aug : PX →* G)
  (ψ : G →* MulAut μ)

/-! ### Automorphisms of `Π_Y[μ]` preserve `μ` -/

section Induced

variable {PY : Subgroup PX}

/-- **[EtTh], Prop. 2.11(ii), finite-index form, for `Π_Y[μ]`**: `μ` is the union of the
centralizers of the finite-index subgroups. -/
theorem mem_fiCentralizers_envY [Finite μ] (hPY : Envelope.FISlim PY) (x : envY aug ψ PY) :
    x ∈ fiCentralizers (envY aug ψ PY) ↔ x ∈ (inlY aug ψ PY).range := by
  rw [← apply_mem_fiCentralizers_iff (envYEquiv aug ψ PY)]
  change (∃ V : Subgroup (μ ⋊[(act aug ψ).comp PY.subtype] PY), V.FiniteIndex ∧
    envYEquiv aug ψ PY x ∈
      Subgroup.centralizer (V : Set (μ ⋊[(act aug ψ).comp PY.subtype] PY))) ↔ _
  refine (Envelope.mem_range_inl_iff_finiteIndex hPY _).symm.trans ⟨?_, ?_⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (envYEquiv aug ψ PY).injective hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, rfl⟩

/-- **Every automorphism of `Π_Y[μ]` preserves `μ`.** -/
theorem apply_mem_range_inlY_iff [Finite μ] (hPY : Envelope.FISlim PY)
    (α : envY aug ψ PY ≃* envY aug ψ PY) (x : envY aug ψ PY) :
    α x ∈ (inlY aug ψ PY).range ↔ x ∈ (inlY aug ψ PY).range := by
  rw [← mem_fiCentralizers_envY aug ψ hPY, ← mem_fiCentralizers_envY aug ψ hPY]
  exact apply_mem_fiCentralizers_iff α x

lemma eq_inlY_mul_salg (z : envY aug ψ PY) :
    z = inlY aug ψ PY (z : EnvX aug ψ).left * salg aug ψ PY (rightPY aug ψ PY z) := by
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ ?_
  · simp
  · simp

@[simp] lemma rightPY_inlY (m : μ) : rightPY aug ψ PY (inlY aug ψ PY m) = 1 := rfl

@[simp] lemma rightPY_salg (h : PY) : rightPY aug ψ PY (salg aug ψ PY h) = h := rfl

lemma rightPY_apply [Finite μ] (hPY : Envelope.FISlim PY) (α : envY aug ψ PY ≃* envY aug ψ PY)
    (z : envY aug ψ PY) :
    rightPY aug ψ PY (α z) = rightPY aug ψ PY (α (salg aug ψ PY (rightPY aug ψ PY z))) := by
  conv_lhs => rw [eq_inlY_mul_salg aug ψ z]
  rw [map_mul, map_mul]
  obtain ⟨m, hm⟩ := (apply_mem_range_inlY_iff aug ψ hPY α _).2 ⟨(z : EnvX aug ψ).left, rfl⟩
  rw [← hm, rightPY_inlY, one_mul]

/-- **The automorphism of `Π_Y = Π_Y[μ]/μ` induced by an automorphism of `Π_Y[μ]`.** -/
def indPY [Finite μ] (hPY : Envelope.FISlim PY) (α : envY aug ψ PY ≃* envY aug ψ PY) :
    MulAut PY where
  toFun h := rightPY aug ψ PY (α (salg aug ψ PY h))
  invFun h := rightPY aug ψ PY (α.symm (salg aug ψ PY h))
  left_inv h := by
    change rightPY aug ψ PY (α.symm (salg aug ψ PY (rightPY aug ψ PY (α (salg aug ψ PY h))))) = h
    rw [← rightPY_apply aug ψ hPY α.symm, MulEquiv.symm_apply_apply, rightPY_salg]
  right_inv h := by
    change rightPY aug ψ PY (α (salg aug ψ PY (rightPY aug ψ PY (α.symm (salg aug ψ PY h))))) = h
    rw [← rightPY_apply aug ψ hPY α, MulEquiv.apply_symm_apply, rightPY_salg]
  map_mul' h h' := by simp only [map_mul]

lemma indPY_apply [Finite μ] (hPY : Envelope.FISlim PY) (α : envY aug ψ PY ≃* envY aug ψ PY)
    (h : PY) : indPY aug ψ hPY α h = rightPY aug ψ PY (α (salg aug ψ PY h)) := rfl

lemma indPY_mul [Finite μ] (hPY : Envelope.FISlim PY) (α β : envY aug ψ PY ≃* envY aug ψ PY) :
    indPY aug ψ hPY (α * β) = indPY aug ψ hPY α * indPY aug ψ hPY β :=
  MulEquiv.ext fun h => rightPY_apply aug ψ hPY α (β (salg aug ψ PY h))

lemma indPY_one [Finite μ] (hPY : Envelope.FISlim PY) : indPY aug ψ hPY 1 = 1 :=
  MulEquiv.ext fun _ => rfl

/-- `indPY α = 1` iff `α` lies over the identity of `Π_Y`. -/
lemma indPY_eq_one_iff [Finite μ] (hPY : Envelope.FISlim PY)
    (α : envY aug ψ PY ≃* envY aug ψ PY) :
    indPY aug ψ hPY α = 1 ↔ ∀ z, rightPY aug ψ PY (α z) = rightPY aug ψ PY z := by
  constructor
  · intro h z
    rw [rightPY_apply aug ψ hPY α z, ← indPY_apply aug ψ hPY, h]
    rfl
  · intro h
    exact MulEquiv.ext fun x => (h _).trans (rightPY_salg aug ψ x)

end Induced

/-! ### Cocycles on `Π_Y` trivial on `Π_Ÿ` -/

section TrivialOn

variable {PY PYdd : Subgroup PX} {δ : PY → μ} (hδ : IsCocycle (actY aug ψ PY) δ)
  (h1 : ∀ g : PY, (g : PX) ∈ PYdd → δ g = 1)

include hδ h1

/-- A cocycle on `Π_Y` trivial on `Π_Ÿ` takes the value `δ(t)` on all of `t·Π_Ÿ`. -/
theorem cocycle_trivialOn_coset (t h : PY) (ht : ((t⁻¹ * h : PY) : PX) ∈ PYdd) : δ h = δ t := by
  have e := hδ t (t⁻¹ * h)
  rw [mul_inv_cancel_left, h1 _ ht, map_one, mul_one] at e
  exact e

/-- Its value `c = δ(t)` at an element `t` with `t² ∈ Π_Ÿ` satisfies `c · t(c) = 1` (for `t`
geometric: `c² = 1`, i.e. `δ ∈ Hom(Π_Y/Π_Ÿ, μ) = Hom(ℤ/2, μ)`). -/
theorem cocycle_trivialOn_sq (t : PY) (ht : ((t * t : PY) : PX) ∈ PYdd) :
    δ t * actY aug ψ PY t (δ t) = 1 := by
  rw [← hδ t t, h1 _ ht]

/-- Its value at `t` is fixed by every `g ∈ Π_Ÿ` with `t⁻¹gt ∈ Π_Ÿ` (all of `Π_Ÿ` if `Π_Ÿ` is
normal in `Π_Y`). -/
theorem cocycle_trivialOn_fixed (t g : PY) (hg : (g : PX) ∈ PYdd)
    (htg : ((t⁻¹ * g * t : PY) : PX) ∈ PYdd) : actY aug ψ PY g (δ t) = δ t := by
  have e1 := hδ g t
  rw [h1 g hg, one_mul] at e1
  have e2 := hδ t (t⁻¹ * g * t)
  rw [h1 _ htg, map_one, mul_one, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at e2
  rw [← e1, e2]

end TrivialOn

lemma mul_aux {M : Type*} [CommGroup M] (l d ζ X : M) :
    l * d = ζ * (d * (ζ⁻¹ * X) * l) * X⁻¹ := by
  simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [mul_left_comm X ζ⁻¹ X⁻¹, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-! ### The model: `Aut(modelEnv) → Aut(Π_Y)` and its kernel -/

section Model

variable [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  (Kum : Subgroup (G → μ)) {PY PYdd : Subgroup PX} (hle : PYdd ≤ PY)
  (hψ : IsOpen ((act aug ψ).ker : Set PX)) (hKum : ∀ κ ∈ Kum, IsCocycle ψ κ)
  {η : PYdd → μ} (hη : IsCocycle (actDD aug ψ PYdd) η) [Finite μ] (hPY : Envelope.FISlim PY)

/-- The automorphism of `Π_Y[μ]` underlying an automorphism of the model environment. -/
abbrev autE (a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)) :
    envY aug ψ PY ≃* envY aug ψ PY :=
  (MonoThetaEnv.homIso a.hom).e.toMulEquiv

/-- **The action of `Aut(M)` on `Π_Y`** ([EtTh], Cor. 2.18(iii),(iv): the map
`Aut(M) → Aut(Π_X̲)` factors through it, `Π_X̲` being recovered from `Π_Y̲` and `D`). -/
def autPY : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη) →* MulAut PY where
  toFun a := indPY aug ψ hPY (autE aug ψ Kum hle hψ hKum hη a)
  map_one' := indPY_one aug ψ hPY
  map_mul' a b := by
    rw [CategoryTheory.Aut.Aut_mul_def]
    exact indPY_mul aug ψ hPY _ _

lemma autPY_apply (a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)) :
    autPY aug ψ Kum hle hψ hKum hη hPY a = indPY aug ψ hPY (autE aug ψ Kum hle hψ hKum hη a) :=
  rfl

/-- Elements of the kernel lie over the identity of `Π_Y`. -/
theorem ker_autPY_apply {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (z : envY aug ψ PY) :
    rightPY aug ψ PY (autE aug ψ Kum hle hψ hKum hη a z) = rightPY aug ψ PY z :=
  (indPY_eq_one_iff aug ψ hPY _).1 ha z

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  [Finite μ] in
/-- The image of the theta section is a member of datum (c). -/
lemma range_thetaSection_mem :
    (thetaSection aug ψ hle hη).range ∈ thetaSubgroups aug ψ hle hη := by
  refine (mem_thetaSubgroups_iff aug ψ hle hη _).2 ⟨1, ?_⟩
  ext z
  simp

omit [Finite μ] in
/-- An automorphism of the model environment maps the image of the theta section to a
`μ`-conjugate of it. -/
theorem exists_map_range_thetaSection
    (a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)) :
    ∃ ζ : μ, (thetaSection aug ψ hle hη).range.map
        (autE aug ψ Kum hle hψ hKum hη a).toMonoidHom =
      (thetaSection aug ψ hle hη).range.map (MulAut.conj (inlY aug ψ PY ζ)).toMonoidHom := by
  have h := (MonoThetaEnv.homIso a.hom).map_theta
  have hmem : (thetaSection aug ψ hle hη).range.map
      (autE aug ψ Kum hle hψ hKum hη a).toMonoidHom ∈ thetaSubgroups aug ψ hle hη := by
    change _ ∈ (modelEnv aug ψ Kum hle hψ hKum hη).thetaSubgroups
    rw [← h]
    exact ⟨_, range_thetaSection_mem aug ψ hle hη, rfl⟩
  exact (mem_thetaSubgroups_iff aug ψ hle hη _).1 hmem

omit [TopologicalSpace PX] [IsTopologicalGroup PX] [TopologicalSpace μ] [DiscreteTopology μ]
  [Finite μ] in
/-- `s^alg(g) = η(g) · s^Θ(g)` on `Π_Ÿ`. -/
lemma salg_eq_inlY_mul_thetaSection (g : PYdd) :
    salg aug ψ PY ⟨g, hle g.2⟩ = inlY aug ψ PY (η g) * thetaSection aug ψ hle hη g := by
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ ?_
  · simp
  · simp

variable {aug ψ Kum hle hψ hKum hη hPY}

/-- An element of the kernel acts on `μ` by some map `u` and on `s^alg` by a function `δ`. -/
lemma ker_autPY_inlY {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (m : μ) :
    autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) =
      inlY aug ψ PY (autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) : EnvX aug ψ).left := by
  conv_lhs => rw [eq_inlY_mul_salg aug ψ (autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m))]
  rw [ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha, rightPY_inlY, map_one, mul_one]

lemma ker_autPY_salg {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (h : PY) :
    autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY h) =
      inlY aug ψ PY (autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY h) : EnvX aug ψ).left *
        salg aug ψ PY h := by
  conv_lhs => rw [eq_inlY_mul_salg aug ψ (autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY h))]
  rw [ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha, rightPY_salg]

/-- An element of the kernel conjugates the theta section by an element of `μ`, pointwise. -/
lemma ker_autPY_thetaSection {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) {ζ : μ}
    (hζ : (thetaSection aug ψ hle hη).range.map
        (autE aug ψ Kum hle hψ hKum hη a).toMonoidHom =
      (thetaSection aug ψ hle hη).range.map (MulAut.conj (inlY aug ψ PY ζ)).toMonoidHom)
    (g : PYdd) :
    autE aug ψ Kum hle hψ hKum hη a (thetaSection aug ψ hle hη g) =
      MulAut.conj (inlY aug ψ PY ζ) (thetaSection aug ψ hle hη g) := by
  have hmem : autE aug ψ Kum hle hψ hKum hη a (thetaSection aug ψ hle hη g) ∈
      (thetaSection aug ψ hle hη).range.map (MulAut.conj (inlY aug ψ PY ζ)).toMonoidHom := by
    rw [← hζ]
    exact ⟨_, ⟨g, rfl⟩, rfl⟩
  obtain ⟨_, ⟨g', rfl⟩, hg'⟩ := hmem
  have hr := ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha (thetaSection aug ψ hle hη g)
  rw [← hg'] at hr ⊢
  have hgg : (g' : PX) = g := by
    have := congrArg Subtype.val hr
    simpa [MulAut.conj_apply] using this
  have : g' = g := Subtype.ext hgg
  subst this
  rfl

variable (aug ψ Kum hle hψ hKum hη hPY)

/-- **[EtTh], Cor. 2.18(iv), finiteness of the kernel**: if `Π_Ÿ̲` has finite index in `Π_Y̲`,
the automorphisms of the model environment lying over the identity of `Π_Y̲` form a finite
group. -/
theorem finite_ker_autPY [(PYdd.subgroupOf PY).FiniteIndex] :
    Finite (autPY aug ψ Kum hle hψ hKum hη hPY).ker := by
  classical
  let Q := PY ⧸ PYdd.subgroupOf PY
  have hζ := fun a => exists_map_range_thetaSection aug ψ Kum hle hψ hKum hη a
  let f : (autPY aug ψ Kum hle hψ hKum hη hPY).ker → (μ → μ) × μ × (Q → μ) := fun a =>
    (fun m => (autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) : EnvX aug ψ).left,
      (hζ a).choose,
      fun q => (autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY q.out) : EnvX aug ψ).left)
  refine Finite.of_injective f fun a b hab => ?_
  simp only [f, Prod.mk.injEq] at hab
  obtain ⟨hu, hz, hc⟩ := hab
  -- the two automorphisms agree on `μ`
  have hμ : ∀ m, autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) =
      autE aug ψ Kum hle hψ hKum hη b (inlY aug ψ PY m) := by
    intro m
    rw [ker_autPY_inlY a.2, ker_autPY_inlY b.2]
    exact congrArg _ (congrFun hu m)
  -- on `s^alg` of `Π_Ÿ`
  have hdd : ∀ g : PYdd, autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY ⟨g, hle g.2⟩) =
      autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY ⟨g, hle g.2⟩) := by
    intro g
    rw [salg_eq_inlY_mul_thetaSection aug ψ hle hη, map_mul, map_mul, hμ,
      ker_autPY_thetaSection a.2 (hζ a).choose_spec g,
      ker_autPY_thetaSection b.2 (hζ b).choose_spec g, hz]
  -- on coset representatives
  have hrep : ∀ q : Q, autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY q.out) =
      autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY q.out) := by
    intro q
    rw [ker_autPY_salg a.2, ker_autPY_salg b.2]
    exact congrArg (· * _) (congrArg _ (congrFun hc q))
  -- on all of `s^alg`
  have hY : ∀ h : PY, autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY h) =
      autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY h) := by
    intro h
    have hq : ((h : Q).out)⁻¹ * h ∈ PYdd.subgroupOf PY :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (h : Q))
    obtain ⟨g, hg⟩ : ∃ g : PY, g = ((h : Q).out)⁻¹ * h := ⟨_, rfl⟩
    have hgdd : (g : PX) ∈ PYdd := by rw [hg]; exact hq
    have hh : h = (h : Q).out * g := by rw [hg, mul_inv_cancel_left]
    have e1 : autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY g) =
        autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY g) := hdd ⟨g, hgdd⟩
    calc autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY h)
        = autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY ((h : Q).out * g)) :=
          congrArg (fun x => autE aug ψ Kum hle hψ hKum hη a (salg aug ψ PY x)) hh
      _ = autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY ((h : Q).out * g)) := by
          simp only [map_mul, e1, hrep]
      _ = autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY h) :=
          (congrArg (fun x => autE aug ψ Kum hle hψ hKum hη b (salg aug ψ PY x)) hh).symm
  -- hence everywhere
  apply Subtype.ext
  apply CategoryTheory.Iso.ext
  apply MonoThetaEnv.Iso.ext
  intro z
  change autE aug ψ Kum hle hψ hKum hη a z = autE aug ψ Kum hle hψ hKum hη b z
  rw [eq_inlY_mul_salg aug ψ z, map_mul, map_mul, hμ, hY]

variable {aug ψ Kum hle hψ hKum hη hPY}

/-- **[EtTh], proof of Cor. 2.18(iv): the kernel consists of shifts.** An automorphism of the
model environment lying over the identity of `Π_Y` and acting trivially on `μ` (the latter is
supplied by Cor. 2.19(i), `cyclotomicRigidity_envAut`) is `inn(ζ) ∘ α_δ` for some `ζ ∈ μ` and a
shifting automorphism `α_δ` (`Shift.lean`) by a cocycle `δ` on `Π_Y` which is trivial on `Π_Ÿ`. -/
theorem ker_autPY_eq_conj_shift {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker)
    (hu : ∀ m, autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) = inlY aug ψ PY m) :
    ∃ (ζ : μ) (δ : PY → μ) (hδ : IsCocycle (actY aug ψ PY) δ),
      (∀ g : PYdd, δ ⟨g, hle g.2⟩ = 1) ∧
      ∀ z, autE aug ψ Kum hle hψ hKum hη a z =
        MulAut.conj (inlY aug ψ PY ζ) (shift aug ψ δ hδ z) := by
  obtain ⟨ζ, hζ⟩ := exists_map_range_thetaSection aug ψ Kum hle hψ hKum hη a
  let E := autE aug ψ Kum hle hψ hKum hη a
  let δ0 : PY → μ := fun h => (E (salg aug ψ PY h) : EnvX aug ψ).left
  have hEc : ∀ h, (E (salg aug ψ PY h) : EnvX aug ψ) = ⟨δ0 h, h⟩ := by
    intro h
    refine SemidirectProduct.ext rfl ?_
    exact congrArg Subtype.val (ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha (salg aug ψ PY h))
  have hδ0 : IsCocycle (actY aug ψ PY) δ0 := by
    intro h h'
    have e : (E (salg aug ψ PY (h * h')) : EnvX aug ψ) =
        (E (salg aug ψ PY h) : EnvX aug ψ) * E (salg aug ψ PY h') := by
      rw [map_mul, map_mul]
      rfl
    rw [hEc, hEc, hEc] at e
    have := congrArg SemidirectProduct.left e
    simpa [mul_left] using this
  -- on `Π_Ÿ`, `δ0` is the coboundary of `ζ`
  have hdd : ∀ g : PYdd, δ0 ⟨g, hle g.2⟩ = cob (ψ := ψ) ζ (aug g) := by
    intro g
    have e : (E (salg aug ψ PY ⟨g, hle g.2⟩) : EnvX aug ψ) =
        inl (η g) * (inl ζ * ⟨(η g)⁻¹, (g : PX)⟩ * (inl ζ)⁻¹) := by
      rw [salg_eq_inlY_mul_thetaSection aug ψ hle hη, map_mul, hu,
        ker_autPY_thetaSection ha hζ g]
      rfl
    rw [hEc] at e
    have := congrArg SemidirectProduct.left e
    simp only [mul_left, inv_left, left_inl, right_inl, map_one, MulAut.one_apply, inv_one,
      one_mul, mul_right, MonoidHom.coe_comp, Function.comp_apply] at this
    rw [this, cob, map_inv]
    simp only [mul_assoc]
    rw [mul_left_comm, mul_inv_cancel_left]
  let c : PY → μ := fun h => cob (ψ := ψ) ζ (aug h)
  have hc : IsCocycle (actY aug ψ PY) c := fun h h' => by
    simp only [c, Subgroup.coe_mul, map_mul]
    exact isCocycle_cob ζ (aug h) (aug h')
  refine ⟨ζ, δ0 * c⁻¹, isCocycle_mul hδ0 (isCocycle_inv' hc), fun g => ?_, fun z => ?_⟩
  · simp only [Pi.mul_apply, Pi.inv_apply, c, hdd g, mul_inv_cancel]
  · apply Subtype.ext
    have hz : (E z : EnvX aug ψ) = inl (z : EnvX aug ψ).left * ⟨δ0 (rightPY aug ψ PY z),
        (z : EnvX aug ψ).right⟩ := by
      conv_lhs => rw [eq_inlY_mul_salg aug ψ z]
      rw [map_mul, hu]
      change inl _ * (E (salg aug ψ PY (rightPY aug ψ PY z)) : EnvX aug ψ) = _
      rw [hEc]
      rfl
    rw [hz, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_inlY, coe_shift]
    refine SemidirectProduct.ext ?_ ?_
    · simp only [mul_left, inv_left, left_inl, right_inl, map_one, MulAut.one_apply, mul_right,
        one_mul, inv_one, Pi.mul_apply, Pi.inv_apply, c, cob, MonoidHom.coe_comp,
        Function.comp_apply, map_inv, inv_inv, mul_inv]
      exact mul_aux _ _ _ _
    · simp

/-- Elements of the kernel preserve every subgroup of `Π_Y[μ]` defined through `Π_Y[μ] ↠ Π_Y`. -/
theorem map_of_ker_autPY {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (S : Subgroup (envY aug ψ PY))
    (hS : ∀ z z', rightPY aug ψ PY z = rightPY aug ψ PY z' → (z ∈ S ↔ z' ∈ S)) :
    S.map (MonoThetaEnv.homIso a.hom).hom = S := by
  have hr := ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hS _ _ (hr y)).2 hy
  · intro hz
    refine ⟨(autE aug ψ Kum hle hψ hKum hη a).symm z, ?_, MulEquiv.apply_symm_apply _ z⟩
    refine (hS _ _ ?_).1 hz
    have := hr ((autE aug ψ Kum hle hψ hKum hη a).symm z)
    rw [MulEquiv.apply_symm_apply] at this
    exact this

/-- **Cor. 2.19(i) on the kernel**: an automorphism of the model environment lying over the
identity of `Π_Y` acts trivially on `μ`, provided the hypotheses of `cyclotomicRigidity_envAut`
hold and `-η` maps `L ∩ Π_Ÿ` onto `μ` (the isomorphism `(l·Δ_Θ) ⊗ ℤ/N ≅ μ_N`). Together with
`ker_autPY_eq_conj_shift` this is the description of the kernel in [EtTh], proof of
Cor. 2.18(iv). -/
theorem ker_autPY_inlY_eq [PY.Normal] (hG : ∀ τ : G, (∀ σ, τ * σ = σ * τ) → τ = 1)
    (hsurj : ∀ σ : G, ∃ h ∈ PY, aug h = σ)
    (L Kθ : Subgroup PX) (hKL : Kθ ≤ L) (hLdd : L ≤ PYdd) (hLg : ∀ l ∈ L, aug l = 1)
    (hη13 : ∀ k (hk : k ∈ PYdd), k ∈ Kθ → η ⟨k, hk⟩ = 1)
    (hL : Subgroup.closure {c | c ∈ L ∧ ∃ a b, aug a = 1 ∧ b ∈ PY ∧ aug b = 1 ∧ c = ⁅a, b⁆} ⊔
      Kθ = L)
    (hηL : ∀ m : μ, ∃ l : PYdd, (l : PX) ∈ L ∧ (η l)⁻¹ = m)
    {a : CategoryTheory.Aut (modelEnv aug ψ Kum hle hψ hKum hη)}
    (ha : a ∈ (autPY aug ψ Kum hle hψ hKum hη hPY).ker) (m : μ) :
    autE aug ψ Kum hle hψ hKum hη a (inlY aug ψ PY m) = inlY aug ψ PY m := by
  obtain ⟨l, hl, rfl⟩ := hηL m
  have hsub : ∀ T : Subgroup PX, (rightSub aug ψ PY T).map (MonoThetaEnv.homIso a.hom).hom =
      rightSub aug ψ PY T := fun T =>
    map_of_ker_autPY ha _ fun z z' hzz' => by
      rw [mem_rightSub, mem_rightSub]
      rw [show (z : EnvX aug ψ).right = (rightPY aug ψ PY z : PX) from rfl,
        show (z' : EnvX aug ψ).right = (rightPY aug ψ PY z' : PX) from rfl, hzz']
  have hgeom : (geomSub aug ψ PY).map (MonoThetaEnv.homIso a.hom).hom = geomSub aug ψ PY :=
    map_of_ker_autPY ha _ fun z z' hzz' => by
      rw [mem_geomSub, mem_geomSub]
      rw [show (z : EnvX aug ψ).right = (rightPY aug ψ PY z : PX) from rfl,
        show (z' : EnvX aug ψ).right = (rightPY aug ψ PY z' : PX) from rfl, hzz']
  obtain ⟨l', -, h1, h2⟩ := cyclotomicRigidity_envAut aug ψ Kum hle hψ hKum hη hPY hG hsurj L Kθ
    hKL hLdd hLg hη13 hL (MonoThetaEnv.homIso a.hom) (hsub L) (hsub Kθ) hgeom l hl
  have hll : l' = l := by
    have hr := ker_autPY_apply aug ψ Kum hle hψ hKum hη hPY ha (algSection aug ψ hle l)
    change rightPY aug ψ PY ((MonoThetaEnv.homIso a.hom).e (algSection aug ψ hle l)) = _ at hr
    rw [h1] at hr
    exact Subtype.ext (by have := congrArg Subtype.val hr; exact this)
  rw [hll] at h2
  exact h2

end Model

end Iut.EtaleTheta.Env
