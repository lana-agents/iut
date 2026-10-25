/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.CyclotomicEnvelope

/-!
# The cyclotomic envelope as a fibre product ([EtTh], Definition 2.10, Proposition 2.11)

[EtTh], Definition 2.10: for a topological group `Π` with an augmentation `Π ↠ G_K`, the
**cyclotomic envelope** is the fibre product `Π[μ_N] = Π ×_{G_K} (μ_N ⋊ G_K)`, the geometric
part is `Δ[μ_N] = Ker(Π[μ_N] ↠ G_K) = Δ × μ_N` for `Δ = Ker(Π ↠ G_K)`, and the trivial section
of `μ_N ⋊ G_K ↠ G_K` gives the **tautological section** `s^alg_Π : Π → Π[μ_N]`.

`CyclotomicEnvelope.lean` works with the semidirect product `μ ⋊ Π` for the action of `Π` on
`μ` through the augmentation. Here we

* show that `μ ⋊ Π` (product topology) is a topological group when `μ` is discrete and the
  action has open kernel (`Envelope.isTopologicalGroup`);
* define the fibre product of Def. 2.10 literally (`fibreEnvelope`) and identify it with
  `μ ⋊ Π` as topological groups (`fibreEquiv`), compatibly with the projections to `Π` and the
  tautological sections (`fibreEquiv_symm_inr`);
* identify `Δ[μ]` with `Δ × μ` (`geomEquiv`) and prove **Prop. 2.11(i)** for it
  (`mem_center_geom_iff`: the kernel of `Δ[μ] ↠ Δ` is the center, if `Δ` is center-free) and its
  consequence for isomorphisms (`geom_right_eq_one_iff_of_equiv`);
* prove the **finite-index variant of Prop. 2.11(ii)** (`mem_range_inl_iff_finiteIndex`): if `μ`
  is finite and every finite-index subgroup of `Π` has trivial centralizer (`FISlim`, the
  route of MR13 decision D4: a dense embedding of `Π^tp` into a slim profinite group gives it),
  then `μ` is the union of the centralizers of the finite-index subgroups of `Π[μ]`. This is a
  purely group-theoretic characterisation, so *every* group isomorphism `Π_α[μ_α] ≅ Π_β[μ_β]`
  maps `μ_α` onto `μ_β` and induces an isomorphism `Π_α ≅ Π_β` compatible with the
  projections (`rightEquivOfMap`, `rightEquivFI`).
-/

namespace Iut.EtaleTheta

open SemidirectProduct

namespace Envelope

section Topology

variable {μ P : Type*} [CommGroup μ] [Group P] [TopologicalSpace μ] [TopologicalSpace P]
  {φ : P →* MulAut μ}

lemma continuous_left : Continuous fun x : μ ⋊[φ] P => x.left :=
  continuous_fst.comp (homeomorphProd (φ := φ)).continuous

lemma continuous_right : Continuous fun x : μ ⋊[φ] P => x.right :=
  continuous_snd.comp (homeomorphProd (φ := φ)).continuous

lemma continuous_mk {X : Type*} [TopologicalSpace X] {f : X → μ} {g : X → P} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (⟨f x, g x⟩ : μ ⋊[φ] P) :=
  (homeomorphProd (φ := φ)).symm.continuous.comp (hf.prodMk hg)

lemma continuous_inl : Continuous (inl : μ → μ ⋊[φ] P) :=
  continuous_mk (φ := φ) continuous_id continuous_const

lemma continuous_inr : Continuous (inr : P → μ ⋊[φ] P) :=
  continuous_mk (φ := φ) continuous_const continuous_id

/-- The action map `Π × μ → μ` is continuous if `μ` is discrete and the action has open
kernel. -/
lemma continuous_act [DiscreteTopology μ] [IsTopologicalGroup P] (hφ : IsOpen (φ.ker : Set P)) :
    Continuous fun p : P × μ => φ p.1 p.2 := by
  rw [continuous_discrete_rng]
  intro m
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g, n⟩ hgn
  refine ⟨((fun h => g⁻¹ * h) ⁻¹' (φ.ker : Set P)) ×ˢ {n}, ?_,
    (hφ.preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _),
    ⟨by simp, rfl⟩⟩
  rintro ⟨g', n'⟩ ⟨hg', hn'⟩
  simp only [Set.mem_singleton_iff] at hn'
  subst hn'
  have hk' : φ (g⁻¹ * g') = 1 := hg'
  have hg'' : g' = g * (g⁻¹ * g') := (mul_inv_cancel_left g g').symm
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hgn ⊢
  rw [hg'', map_mul, MulAut.mul_apply, hk', MulAut.one_apply, hgn]

/-- **The cyclotomic envelope is a topological group** (product topology), for `μ` discrete and
an action with open kernel. -/
theorem isTopologicalGroup [DiscreteTopology μ] [IsTopologicalGroup P]
    (hφ : IsOpen (φ.ker : Set P)) : IsTopologicalGroup (μ ⋊[φ] P) where
  continuous_mul := by
    have hact := continuous_act hφ
    change Continuous fun p : (μ ⋊[φ] P) × (μ ⋊[φ] P) =>
      (⟨p.1.left * φ p.1.right p.2.left, p.1.right * p.2.right⟩ : μ ⋊[φ] P)
    refine continuous_mk ?_ ?_
    · exact (continuous_of_discreteTopology (f := fun q : μ × μ => q.1 * q.2)).comp
        (((continuous_left (φ := φ)).comp continuous_fst).prodMk
          (hact.comp (((continuous_right (φ := φ)).comp continuous_fst).prodMk
            ((continuous_left (φ := φ)).comp continuous_snd))))
    · exact ((continuous_right (φ := φ)).comp continuous_fst).mul
        ((continuous_right (φ := φ)).comp continuous_snd)
  continuous_inv := by
    have hact := continuous_act hφ
    change Continuous fun x : μ ⋊[φ] P =>
      (⟨φ x.right⁻¹ x.left⁻¹, x.right⁻¹⟩ : μ ⋊[φ] P)
    refine continuous_mk ?_ (continuous_right (φ := φ)).inv
    exact hact.comp ((continuous_right (φ := φ)).inv.prodMk
      ((continuous_of_discreteTopology (f := fun q : μ => q⁻¹)).comp (continuous_left (φ := φ))))

end Topology

/-! ### The fibre product of [EtTh], Definition 2.10 -/

section FibreProduct

variable {P G μ : Type*} [Group P] [Group G] [CommGroup μ] (aug : P →* G)
  (ψ : G →* MulAut μ)

/-- **[EtTh], Definition 2.10**: the cyclotomic envelope `Π[μ] = Π ×_G (μ ⋊ G)`. -/
def fibreEnvelope : Subgroup (P × (μ ⋊[ψ] G)) :=
  (aug.comp (MonoidHom.fst _ _)).eqLocus (rightHom.comp (MonoidHom.snd _ _))

lemma mem_fibreEnvelope (x : P × (μ ⋊[ψ] G)) : x ∈ fibreEnvelope aug ψ ↔ aug x.1 = x.2.right :=
  Iff.rfl

/-- The fibre product is the semidirect product for the action through the augmentation. -/
def fibreMulEquiv : fibreEnvelope aug ψ ≃* μ ⋊[ψ.comp aug] P where
  toFun x := ⟨(x : P × (μ ⋊[ψ] G)).2.left, (x : P × (μ ⋊[ψ] G)).1⟩
  invFun y := ⟨(y.right, ⟨y.left, aug y.right⟩), rfl⟩
  left_inv x := by
    obtain ⟨⟨p, m, σ⟩, hx⟩ := x
    have hx' : aug p = σ := hx
    subst hx'
    rfl
  right_inv y := rfl
  map_mul' x y := by
    obtain ⟨⟨p, m, σ⟩, hx⟩ := x
    obtain ⟨⟨q, n, τ⟩, hy⟩ := y
    have hx' : aug p = σ := hx
    subst hx'
    rfl

@[simp] lemma fibreMulEquiv_left (x : fibreEnvelope aug ψ) :
    (fibreMulEquiv aug ψ x).left = (x : P × (μ ⋊[ψ] G)).2.left := rfl

@[simp] lemma fibreMulEquiv_right (x : fibreEnvelope aug ψ) :
    (fibreMulEquiv aug ψ x).right = (x : P × (μ ⋊[ψ] G)).1 := rfl

/-- The **tautological section** `s^alg_Π : Π → Π[μ]` of Def. 2.10, induced by the trivial
section of `μ ⋊ G ↠ G`. -/
def salgFibre : P →* fibreEnvelope aug ψ :=
  ((MonoidHom.prod (MonoidHom.id P) (inr.comp aug)).codRestrict _ fun _ => rfl)

/-- Under `fibreMulEquiv`, the tautological section is `inr`. -/
@[simp] lemma fibreMulEquiv_salgFibre (p : P) :
    fibreMulEquiv aug ψ (salgFibre aug ψ p) = inr p := rfl

lemma fibreEquiv_symm_inr (p : P) : (fibreMulEquiv aug ψ).symm (inr p) = salgFibre aug ψ p :=
  (fibreMulEquiv aug ψ).symm_apply_eq.2 rfl

variable [TopologicalSpace P] [TopologicalSpace G] [TopologicalSpace μ]

open scoped Envelope in
/-- **[EtTh], Definition 2.10, topologically**: for a continuous augmentation, the fibre product
`Π ×_G (μ ⋊ G)` (subspace of the product topology) is isomorphic as a topological group to
`μ ⋊ Π` with the product topology. -/
def fibreEquiv (haug : Continuous aug) : fibreEnvelope aug ψ ≃ₜ* μ ⋊[ψ.comp aug] P where
  toMulEquiv := fibreMulEquiv aug ψ
  continuous_toFun := continuous_mk (continuous_left.comp (continuous_snd.comp
    continuous_subtype_val)) (continuous_fst.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_right.prodMk (continuous_mk continuous_left (haug.comp continuous_right))

end FibreProduct

/-! ### The geometric part `Δ[μ] = Δ × μ` and [EtTh], Proposition 2.11(i) -/

section Geometric

lemma _root_.MulEquiv.apply_mem_center_iff' {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (a : A) : f a ∈ Subgroup.center B ↔ a ∈ Subgroup.center A := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg f.symm (h (f g))
    simpa using this
  · intro h g
    have := congrArg f (h (f.symm g))
    simpa using this

variable {P G μ : Type*} [Group P] [Group G] [CommGroup μ] (aug : P →* G)
  (ψ : G →* MulAut μ)

/-- `Δ[μ] = Ker(Π[μ] ↠ G)`. -/
def geom : Subgroup (μ ⋊[ψ.comp aug] P) := (aug.comp rightHom).ker

lemma mem_geom (x : μ ⋊[ψ.comp aug] P) : x ∈ geom aug ψ ↔ aug x.right = 1 := Iff.rfl

/-- **`Δ[μ] = Δ × μ`** ([EtTh], Def. 2.10). -/
def geomEquiv : geom aug ψ ≃* aug.ker × μ where
  toFun x := (⟨(x : μ ⋊[ψ.comp aug] P).right, x.2⟩, (x : μ ⋊[ψ.comp aug] P).left)
  invFun y := ⟨⟨y.2, y.1⟩, y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := by
    obtain ⟨⟨m, p⟩, hx⟩ := x
    obtain ⟨⟨n, q⟩, hy⟩ := y
    have hp : aug p = 1 := hx
    ext
    · rfl
    · change m * (ψ (aug p)) n = m * n
      rw [hp, map_one, MulAut.one_apply]

/-- **[EtTh], Proposition 2.11(i)**: if `Δ = Ker(Π ↠ G)` is center-free (e.g. temp-slim,
`TempSlim.center_eq_bot`), the kernel of `Δ[μ] ↠ Δ` is the center of `Δ[μ]`. -/
theorem mem_center_geom_iff (hΔ : Subgroup.center aug.ker = ⊥) (x : geom aug ψ) :
    x ∈ Subgroup.center (geom aug ψ) ↔ (x : μ ⋊[ψ.comp aug] P).right = 1 := by
  rw [← (geomEquiv aug ψ).apply_mem_center_iff' x]
  constructor
  · intro hx
    have h1 : (⟨(x : μ ⋊[ψ.comp aug] P).right, x.2⟩ : aug.ker) ∈ Subgroup.center aug.ker := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      have := congrArg Prod.fst (hx (g, 1))
      exact this
    rw [hΔ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · intro hx
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, n⟩
    ext
    · change (g : P) * (x : μ ⋊[ψ.comp aug] P).right = (x : μ ⋊[ψ.comp aug] P).right * g
      rw [hx, mul_one, one_mul]
    · exact mul_comm _ _

variable {P' G' μ' : Type*} [Group P'] [Group G'] [CommGroup μ'] (aug' : P' →* G')
  (ψ' : G' →* MulAut μ')

/-- **[EtTh], Proposition 2.11(i)**, consequence: any isomorphism `Δ_α[μ] ≅ Δ_β[μ]` (of groups;
a fortiori of topological groups) is compatible with the natural surjections `Δ_□[μ] ↠ Δ_□`:
it maps the kernel onto the kernel. -/
theorem geom_right_eq_one_iff_of_equiv (hΔ : Subgroup.center aug.ker = ⊥)
    (hΔ' : Subgroup.center aug'.ker = ⊥) (e : geom aug ψ ≃* geom aug' ψ') (x : geom aug ψ) :
    ((e x : geom aug' ψ') : μ' ⋊[ψ'.comp aug'] P').right = 1 ↔
      (x : μ ⋊[ψ.comp aug] P).right = 1 := by
  rw [← mem_center_geom_iff aug' ψ' hΔ', ← mem_center_geom_iff aug ψ hΔ,
    MulEquiv.apply_mem_center_iff']

end Geometric

/-! ### The finite-index variant of [EtTh], Proposition 2.11(ii) -/

/-- Every finite-index subgroup has trivial centralizer. For `Π^tp` this follows from a dense
embedding into a slim profinite group (tempered-fundamental-groups,
`TempSlim.centralizer_eq_bot_of_denseRange`; MR13 decision D4); it is what [EtTh], Prop. 2.11
uses when `μ_N` is finite. -/
def FISlim (P : Type*) [Group P] : Prop :=
  ∀ H : Subgroup P, H.FiniteIndex → Subgroup.centralizer (H : Set P) = ⊥

section FiniteIndex

variable {μ P : Type*} [CommGroup μ] [Group P] {φ : P →* MulAut μ}

/-- The subgroup `rightHom⁻¹(Ker φ)` centralizes `inl(μ)`. -/
lemma inl_mem_centralizer_comap_ker (m : μ) :
    inl m ∈ Subgroup.centralizer ((φ.ker.comap (rightHom : μ ⋊[φ] P →* P)) : Set (μ ⋊[φ] P)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : φ y.right = 1 := hy
  ext
  · simp only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply, hy']
    exact mul_comm _ _
  · simp

/-- **[EtTh], Proposition 2.11(ii), finite-index form**: for `μ` finite and `Π` with
`FISlim Π`, the kernel `inl(μ)` of `Π[μ] ↠ Π` is the union of the centralizers of the
finite-index subgroups of `Π[μ]`. -/
theorem mem_range_inl_iff_finiteIndex [Finite μ] (hP : FISlim P) (x : μ ⋊[φ] P) :
    x ∈ (inl : μ →* μ ⋊[φ] P).range ↔
      ∃ V : Subgroup (μ ⋊[φ] P), V.FiniteIndex ∧ x ∈ Subgroup.centralizer (V : Set (μ ⋊[φ] P)) := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨φ.ker.comap rightHom, ?_, inl_mem_centralizer_comap_ker m⟩
    haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ rightHom_surjective]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rintro ⟨V, hV, hx⟩
    have hW : (V.map (rightHom : μ ⋊[φ] P →* P)).FiniteIndex := by
      refine ⟨fun h0 => hV.index_ne_zero ?_⟩
      have := V.index_map_dvd (rightHom_surjective (φ := φ))
      rw [h0] at this
      exact Nat.eq_zero_of_zero_dvd this
    have hxr : x.right ∈ Subgroup.centralizer ((V.map rightHom : Subgroup P) : Set P) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      rintro _ ⟨v, hv, rfl⟩
      have := congrArg rightHom (hx v hv)
      rw [map_mul, map_mul] at this
      exact this
    rw [hP _ hW, Subgroup.mem_bot] at hxr
    rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact hxr

variable {μ' P' : Type*} [CommGroup μ'] [Group P'] {φ' : P' →* MulAut μ'}

/-- Group isomorphisms preserve the union of the centralizers of finite-index subgroups. -/
lemma exists_finiteIndex_centralizer_map {A B : Type*} [Group A] [Group B] (f : A ≃* B) (a : A)
    (h : ∃ V : Subgroup A, V.FiniteIndex ∧ a ∈ Subgroup.centralizer (V : Set A)) :
    ∃ V : Subgroup B, V.FiniteIndex ∧ f a ∈ Subgroup.centralizer (V : Set B) := by
  obtain ⟨V, hV, ha⟩ := h
  refine ⟨V.map (f : A →* B), ⟨?_⟩, ?_⟩
  · rw [Subgroup.index_map_equiv]
    exact hV.index_ne_zero
  · rw [Subgroup.mem_centralizer_iff] at ha ⊢
    rintro _ ⟨v, hv, rfl⟩
    have := congrArg f (ha v hv)
    rw [map_mul, map_mul] at this
    exact this

/-- **Isomorphisms preserve the kernel** (finite-index form of [EtTh], Prop. 2.11(ii)): any group
isomorphism `Π[μ] ≅ Π'[μ']` maps `μ` onto `μ'`. -/
theorem apply_mem_range_inl_iff_finiteIndex [Finite μ] [Finite μ'] (hP : FISlim P)
    (hP' : FISlim P') (e : (μ ⋊[φ] P) ≃* (μ' ⋊[φ'] P')) (x : μ ⋊[φ] P) :
    e x ∈ (inl : μ' →* μ' ⋊[φ'] P').range ↔ x ∈ (inl : μ →* μ ⋊[φ] P).range := by
  rw [mem_range_inl_iff_finiteIndex hP', mem_range_inl_iff_finiteIndex hP]
  refine ⟨fun h => ?_, exists_finiteIndex_centralizer_map e x⟩
  simpa using exists_finiteIndex_centralizer_map e.symm (e x) h

/-- The homomorphism `Π → Π'` induced by an isomorphism of envelopes. -/
def rightHomOfMulEquiv (e : (μ ⋊[φ] P) ≃* (μ' ⋊[φ'] P')) : P →* P' :=
  rightHom.comp (e.toMonoidHom.comp inr)

section OfMap

variable (e : (μ ⋊[φ] P) ≃* (μ' ⋊[φ'] P'))
  (he : ∀ x, e x ∈ (inl : μ' →* μ' ⋊[φ'] P').range ↔ x ∈ (inl : μ →* μ ⋊[φ] P).range)

include he in
theorem rightHomOfMulEquiv_rightHom (x : μ ⋊[φ] P) :
    rightHomOfMulEquiv e (rightHom x) = rightHom (e x) := by
  have hx : x = inl x.left * inr x.right := by ext <;> simp
  have h1 : rightHom (e (inl x.left)) = 1 := by
    have := (he (inl x.left)).2 ⟨x.left, rfl⟩
    rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at this
    exact this
  conv_rhs => rw [hx]
  rw [map_mul, map_mul, h1, one_mul]
  rfl

include he in
lemma symm_mem_iff (y : μ' ⋊[φ'] P') :
    e.symm y ∈ (inl : μ →* μ ⋊[φ] P).range ↔ y ∈ (inl : μ' →* μ' ⋊[φ'] P').range := by
  rw [← he, MulEquiv.apply_symm_apply]

include he in
lemma rightHomOfMulEquiv_symm_comp (p : P) :
    rightHomOfMulEquiv e.symm (rightHomOfMulEquiv e p) = p := by
  have h := rightHomOfMulEquiv_rightHom e.symm (symm_mem_iff e he) (e (inr p))
  rw [MulEquiv.symm_apply_apply, rightHom_inr] at h
  have h2 := rightHomOfMulEquiv_rightHom e he (inr p)
  rw [rightHom_inr] at h2
  rw [h2, h]

/-- An isomorphism of envelopes mapping the kernel `μ` onto `μ'` induces an isomorphism
`Π ≃* Π'`, compatible with the projections (`rightEquivOfMap_rightHom`). -/
def rightEquivOfMap : P ≃* P' where
  toFun := rightHomOfMulEquiv e
  invFun := rightHomOfMulEquiv e.symm
  left_inv := rightHomOfMulEquiv_symm_comp e he
  right_inv p := by
    have := rightHomOfMulEquiv_symm_comp e.symm (symm_mem_iff e he) p
    simpa using this
  map_mul' := map_mul _

theorem rightEquivOfMap_rightHom (x : μ ⋊[φ] P) :
    rightEquivOfMap e he (rightHom x) = rightHom (e x) :=
  rightHomOfMulEquiv_rightHom e he x

end OfMap

/-- **[EtTh], Proposition 2.11(ii), finite-index form**: for finite `μ`, `μ'` and `FISlim`
groups `Π`, `Π'`, every group isomorphism `Π[μ] ≅ Π'[μ']` induces an isomorphism `Π ≅ Π'`
compatible with the natural surjections (`rightEquivOfMap_rightHom`). -/
def rightEquivFI [Finite μ] [Finite μ'] (hP : FISlim P) (hP' : FISlim P')
    (e : (μ ⋊[φ] P) ≃* (μ' ⋊[φ'] P')) : P ≃* P' :=
  rightEquivOfMap e (apply_mem_range_inl_iff_finiteIndex hP hP' e)

theorem rightEquivFI_rightHom [Finite μ] [Finite μ'] (hP : FISlim P) (hP' : FISlim P')
    (e : (μ ⋊[φ] P) ≃* (μ' ⋊[φ'] P')) (x : μ ⋊[φ] P) :
    rightEquivFI hP hP' e (rightHom x) = rightHom (e x) :=
  rightEquivOfMap_rightHom _ _ x

end FiniteIndex

end Envelope

/-- `TempSlim` (all open subgroups) implies the condition on open finite-index subgroups; for a
group in which finite-index subgroups are open (e.g. a topologically finitely generated
profinite group) it gives `FISlim`. -/
lemma TempSlim.fISlim {P : Type*} [Group P] [TopologicalSpace P] (h : TempSlim P)
    (hopen : ∀ H : Subgroup P, H.FiniteIndex → IsOpen (H : Set P)) : Envelope.FISlim P :=
  fun H hH => h H (hopen H hH)

end Iut.EtaleTheta
