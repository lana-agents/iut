/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.Literal

/-!
# The (Ind1)-invariance of the procession-normalized log-volume

Test file.
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped Pointwise TensorProduct

universe u

/-! ### Reindexing a tensor product of algebras -/

section Reindex

variable {R : Type*} [CommSemiring R] {ι ι' : Type*} {A : ι → Type*} [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)]

/-- **Reindexing the factors of a tensor product of algebras** along `e : ι ≃ ι'`, as an
algebra isomorphism `⊗_i A_i ≃ ⊗_{i'} A_{e⁻¹ i'}` (`PiTensorProduct.reindex`). -/
noncomputable def reindexAlgEquiv (e : ι ≃ ι') :
    (⨂[R] i, A i) ≃ₐ[R] ⨂[R] i', A (e.symm i') :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.reindex R A e)
    (by rw [PiTensorProduct.one_def, PiTensorProduct.reindex_tprod]; rfl)
    (fun x y => by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod s g =>
          rw [smul_mul_smul_comm, PiTensorProduct.tprod_mul_tprod, map_smul, map_smul,
            map_smul, PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod,
            PiTensorProduct.reindex_tprod, smul_mul_smul_comm, PiTensorProduct.tprod_mul_tprod]
          rfl
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul])

lemma reindexAlgEquiv_tprod (e : ι ≃ ι') (f : ∀ i, A i) :
    reindexAlgEquiv (R := R) e (PiTensorProduct.tprod R f) =
      PiTensorProduct.tprod R fun i' => f (e.symm i') :=
  PiTensorProduct.reindex_tprod (R := R) e f

lemma reindexAlgEquiv_apply (e : ι ≃ ι') (x : ⨂[R] i, A i) :
    reindexAlgEquiv (R := R) e x = PiTensorProduct.reindex R A e x := rfl

end Reindex

/-! ### Algebra isomorphisms of packets -/

section AlgEquiv

variable {K : Type u} [Field K] [NumberField K] {ι ι' : Type} [Fintype ι] [Fintype ι']
  {vQ : RationalPlace} {c : ι → Place K} {c' : ι' → Place K}

/-- **Algebra homomorphisms of packets map the integral structure into the integral
structure**: at a prime `(R_I)^∼` is the integral closure of `ℤ_p`, at `∞` the elements all of
whose components (`ℝ`-algebra homomorphisms to `ℂ`) have absolute value at most `1`. -/
theorem image_integralAt_subset
    (φ : Tensor K vQ c →ₐ[baseField vQ] Tensor K vQ c') :
    φ '' integralAt vQ c ⊆ integralAt vQ c' := by
  cases vQ with
  | finite p =>
    rintro _ ⟨x, hx, rfl⟩
    let φ' : Tensor K (.finite p) c →ₐ[ℚ_[p]] Tensor K (.finite p) c' := φ
    refine ((mem_integral p c).mp hx).map_of_comp_eq (RingHom.id ℤ_[p]) φ'.toRingHom ?_
    ext r
    change algebraMap ℚ_[p] _ (r : ℚ_[p]) = φ' (algebraMap ℚ_[p] _ (r : ℚ_[p]))
    rw [φ'.commutes]
  | infinite =>
    rintro _ ⟨x, hx, rfl⟩ m
    have h := norm_algHom_eq_archChar ((archChar c' m).comp φ) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact hx _

/-- **Algebra isomorphisms of packets preserve the integral structure.** -/
theorem image_integralAt_algEquiv
    (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c') :
    E '' integralAt vQ c = integralAt vQ c' := by
  refine Set.Subset.antisymm (image_integralAt_subset E.toAlgHom) fun y hy => ?_
  exact ⟨E.symm y, image_integralAt_subset E.symm.toAlgHom ⟨y, hy, rfl⟩, E.apply_symm_apply y⟩

/-- Ring isomorphisms of packets map `a·X` to `E(a)·E(X)`. -/
lemma image_smul_set_algEquiv (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c')
    (a : Tensor K vQ c) (X : Set (Tensor K vQ c)) : E '' (a • X) = E a • E '' X := by
  rw [smul_set_eq_image, smul_set_eq_image, Set.image_image, Set.image_image]
  simp only [map_mul]

/-- Algebra isomorphisms of packets map hull regions `a·O` to hull regions `E(a)·O`. -/
theorem image_smul_integralAt_algEquiv
    (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c') (a : Tensor K vQ c) :
    E '' (a • integralAt vQ c) = E a • integralAt vQ c' := by
  rw [← image_integralAt_algEquiv E, smul_set_eq_image, smul_set_eq_image, Set.image_image,
    Set.image_image]
  simp only [map_mul]

/-- **Linear isomorphisms of packets preserving the integral structure preserve the normalized
log-volume** `μ^log(S) = log(μ(S)/μ(O))/[T : ℚ_{v_ℚ}]`: the image of a Haar measure is a Haar
measure, hence a multiple of the Haar measure. -/
theorem componentVol_image_linearEquiv
    (E : Tensor K vQ c ≃ₗ[baseField vQ] Tensor K vQ c')
    (hE : E '' integralAt vQ c = integralAt vQ c') (S : Set (Tensor K vQ c)) :
    componentVol vQ c' (E '' S) = componentVol vQ c S := by
  have hcont : Continuous E := LinearMap.continuous_of_finiteDimensional E.toLinearMap
  have hcont' : Continuous E.symm :=
    LinearMap.continuous_of_finiteDimensional E.symm.toLinearMap
  let L : Tensor K vQ c ≃L[baseField vQ] Tensor K vQ c' :=
    { E with continuous_toFun := hcont, continuous_invFun := hcont' }
  let ν : Measure (Tensor K vQ c) := (haar vQ c').map L.symm
  have hν : ν = Measure.addHaarScalarFactor ν (haar vQ c) • haar vQ c :=
    Measure.isAddLeftInvariant_eq_smul ν (haar vQ c)
  set k := Measure.addHaarScalarFactor ν (haar vQ c)
  have himg : ∀ T : Set (Tensor K vQ c), haar vQ c' (E '' T) = (k : ENNReal) * haar vQ c T := by
    intro T
    have h1 : ν T = haar vQ c' (E '' T) := by
      change Measure.map L.symm.toHomeomorph.toMeasurableEquiv (haar vQ c') T = _
      rw [MeasurableEquiv.map_apply]
      congr 1
      exact (E.image_eq_preimage_symm T).symm
    rw [← h1, hν]
    rfl
  have hO := himg (integralAt vQ c)
  rw [hE] at hO
  have hk : (k : ℝ) ≠ 0 := by
    intro h0
    have : haar vQ c' (integralAt vQ c') = 0 := by
      rw [hO, show (k : ENNReal) = 0 from by exact_mod_cast h0, zero_mul]
    exact (haar_integralAt_pos (vQ := vQ) (c := c')).ne' this
  unfold componentVol
  rw [himg, hO, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    mul_div_mul_left _ _ hk, E.finrank_eq]

/-- Algebra isomorphisms of packets preserve the normalized log-volume. -/
theorem componentVol_image_algEquiv
    (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c') (S : Set (Tensor K vQ c)) :
    componentVol vQ c' (E '' S) = componentVol vQ c S :=
  componentVol_image_linearEquiv E.toLinearEquiv (image_integralAt_algEquiv E) S

end AlgEquiv


/-! ### Least hull regions of a component -/

section LeastHull

variable {K : Type u} [Field K] [NumberField K] {ι ι' : Type} [Fintype ι] [Fintype ι']
  {vQ : RationalPlace} {c : ι → Place K} {c' : ι' → Place K}

/-- `a·O` is **the least hull region** of the region `U` of a packet: `a` is a unit, `U ⊆ a·O`,
and `a·O ⊆ b·O` for every unit `b` with `U ⊆ b·O` (IUT III, Remark 3.9.5(i)). -/
def IsLeastHull (U : Set (Tensor K vQ c)) (a : Tensor K vQ c) : Prop :=
  IsUnit a ∧ U ⊆ a • integralAt vQ c ∧
    ∀ b : Tensor K vQ c, IsUnit b → U ⊆ b • integralAt vQ c →
      a • integralAt vQ c ⊆ b • integralAt vQ c

/-- Least hull regions are unique. -/
lemma IsLeastHull.smul_eq {U : Set (Tensor K vQ c)} {a b : Tensor K vQ c}
    (ha : IsLeastHull U a) (hb : IsLeastHull U b) :
    a • integralAt vQ c = b • integralAt vQ c :=
  Set.Subset.antisymm (ha.2.2 b hb.1 hb.2.1) (hb.2.2 a ha.1 ha.2.1)

/-- **Algebra isomorphisms of packets map least hull regions to least hull regions**: the
hull of the image is the image of the hull. -/
theorem IsLeastHull.algEquiv (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c')
    {U : Set (Tensor K vQ c)} {a : Tensor K vQ c} (ha : IsLeastHull U a) :
    IsLeastHull (E '' U) (E a) := by
  refine ⟨ha.1.map E, ?_, fun b hb hUb => ?_⟩
  · rw [← image_smul_integralAt_algEquiv E a]
    exact Set.image_mono ha.2.1
  · have hb' : b • integralAt vQ c' = E '' (E.symm b • integralAt vQ c) := by
      rw [image_smul_integralAt_algEquiv E, AlgEquiv.apply_symm_apply]
    have hsub : U ⊆ E.symm b • integralAt vQ c := by
      intro x hx
      have := hUb ⟨x, hx, rfl⟩
      rw [hb'] at this
      exact E.injective.mem_set_image.mp this
    rw [← image_smul_integralAt_algEquiv E a, hb']
    exact Set.image_mono (ha.2.2 _ (hb.map E.symm) hsub)

/-- The normalized log-volume of the least hull region of the image under an algebra
isomorphism is that of the least hull region. -/
theorem IsLeastHull.componentVol_eq (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c')
    {U : Set (Tensor K vQ c)} {a : Tensor K vQ c} (ha : IsLeastHull U a) {b : Tensor K vQ c'}
    (hb : IsLeastHull (E '' U) b) :
    componentVol vQ c' (b • integralAt vQ c') = componentVol vQ c (a • integralAt vQ c) := by
  rw [hb.smul_eq (ha.algEquiv E), ← image_smul_integralAt_algEquiv E a,
    componentVol_image_algEquiv]

end LeastHull

/-! ### Reindexing the packets along a bijection of the labels -/

section PacketReindex

variable {K : Type u} [Field K] [NumberField K] {ι ι' : Type} [Fintype ι] [Fintype ι']

variable (vQ : RationalPlace) (c : ι → Place K) (e : ι ≃ ι')

/-- **The reindexing isomorphism of packets** `⊗_j K_{c j} ≃ ⊗_{j'} K_{c(e⁻¹ j')}` along a
bijection `e` of the labels (for a label permutation `σ`, the action `c ↦ c ∘ σ⁻¹` of (Ind1) on
the tuples of places, together with the permutation of the tensor factors). -/
noncomputable def packetReindex :
    Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ (c ∘ e.symm) :=
  reindexAlgEquiv e

variable {vQ c e}

lemma packetReindex_tprod (f : ∀ j, Factor' K vQ (c j)) :
    packetReindex vQ c e (PiTensorProduct.tprod (baseField vQ) f) =
      PiTensorProduct.tprod (baseField vQ) fun j' => f (e.symm j') :=
  reindexAlgEquiv_tprod e f

variable (vQ c e)

/-- The reindexing isomorphism preserves the integral structure. -/
theorem image_integralAt_packetReindex :
    packetReindex vQ c e '' integralAt vQ c = integralAt vQ (c ∘ e.symm) :=
  image_integralAt_algEquiv _

/-- The reindexing isomorphism maps hull regions `a·O` to hull regions. -/
theorem image_smul_integralAt_packetReindex (a : Tensor K vQ c) :
    packetReindex vQ c e '' (a • integralAt vQ c) =
      packetReindex vQ c e a • integralAt vQ (c ∘ e.symm) :=
  image_smul_integralAt_algEquiv _ a

/-- The reindexing isomorphism maps units to units. -/
lemma isUnit_packetReindex {a : Tensor K vQ c} (ha : IsUnit a) :
    IsUnit (packetReindex vQ c e a) :=
  ha.map _

/-- **The reindexing isomorphism preserves the normalized log-volume.** -/
theorem componentVol_image_packetReindex (S : Set (Tensor K vQ c)) :
    componentVol vQ (c ∘ e.symm) (packetReindex vQ c e '' S) = componentVol vQ c S :=
  componentVol_image_algEquiv _ S

/-! #### The tensor product of the log-shells -/

variable (p : Nat.Primes)

/-- The reindexing isomorphism maps the elementary tensors of log-shell elements onto the
elementary tensors of log-shell elements. -/
lemma image_logShellSet_packetReindex :
    packetReindex (.finite p) c e '' logShellSet p c = logShellSet p (c ∘ e.symm) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨fun j' => a (e.symm j'), ?_⟩
    exact (packetReindex_tprod (vQ := .finite p) (c := c) (e := e)
      (fun j => (a j : Factor K p (c j)))).symm
  · rintro _ ⟨a', rfl⟩
    refine ⟨_, ⟨(Equiv.piCongrLeft' (fun j => factorLogShell p (c j)) e).symm a', rfl⟩, ?_⟩
    rw [packetReindex_tprod (vQ := .finite p)]
    have h := (Equiv.piCongrLeft' (fun j => factorLogShell p (c j)) e).apply_symm_apply a'
    congr 1
    funext j'
    exact congrArg Subtype.val (congrFun h j')

/-- **The reindexing isomorphism preserves the tensor product of the log-shells**
`⊗_j 𝓘_{c j}` (`LocalTheory.shell`). -/
theorem image_tensorLogShell_packetReindex :
    packetReindex (.finite p) c e '' tensorLogShell p c = tensorLogShell p (c ∘ e.symm) := by
  let E : Tensor K (.finite p) c →ₗ[ℤ_[p]] Tensor K (.finite p) (c ∘ e.symm) :=
    { toFun := packetReindex (.finite p) c e
      map_add' := map_add _
      map_smul' := fun r x => by
        change packetReindex (.finite p) c e ((r : ℚ_[p]) • x) =
          (r : ℚ_[p]) • packetReindex (.finite p) c e x
        exact map_smul (packetReindex (.finite p) c e).toLinearEquiv (r : ℚ_[p]) x }
  have h := Submodule.map_span E (logShellSet p c)
  have h' : (E : Tensor K (.finite p) c → _) '' logShellSet p c = logShellSet p (c ∘ e.symm) :=
    image_logShellSet_packetReindex c e p
  rw [h'] at h
  have h2 := congrArg SetLike.coe h
  rw [Submodule.map_coe] at h2
  exact h2

/-! #### The inclusions of the factors -/

/-- The reindexing isomorphism moves the inclusion of the factor at `e⁻¹ j'` to the inclusion
of the factor at `j'`. -/
lemma packetReindex_inclFactor (j' : ι') (x : Factor K p (c (e.symm j'))) :
    packetReindex (.finite p) c e (inclFactor p c (e.symm j') x) =
      inclFactor p (c ∘ e.symm) j' x := by
  classical
  change packetReindex (.finite p) c e (PiTensorProduct.tprod ℚ_[p] _) =
    PiTensorProduct.tprod ℚ_[p] _
  rw [packetReindex_tprod (vQ := .finite p)]
  congr 1
  funext k
  by_cases hk : k = j'
  · subst hk
    rw [MonoidHom.mulSingle_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_same]
  · have hk' : e.symm k ≠ e.symm j' := fun h => hk (e.symm.injective h)
    rw [MonoidHom.mulSingle_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hk,
      Pi.mulSingle_eq_of_ne hk']
    rfl

/-- **The reindexing isomorphism moves the inclusion of the factor at `e⁻¹ j'` to the inclusion
of the factor at `j'`** (`LocalTheory.incl`). -/
theorem packetReindex_incl (j' : ι') (w : FinitePlace K) (h : c (e.symm j') = Place.finite w)
    (x : completionAt K w) :
    packetReindex (.finite p) c e (incl p c (e.symm j') w h x) =
      incl p (c ∘ e.symm) j' w h x :=
  packetReindex_inclFactor c e p j' _

/-! #### The indeterminacy automorphisms at a prime -/

lemma packetReindex_congr (g : ∀ j, Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j))
    (x : Tensor K (.finite p) c) :
    packetReindex (.finite p) c e (PiTensorProduct.congr g x) =
      PiTensorProduct.congr (fun j' => g (e.symm j')) (packetReindex (.finite p) c e x) := by
  exact (PiTensorProduct.map_reindex (R := ℚ_[p])
    (fun j => (g j : Factor K p (c j) →ₗ[ℚ_[p]] Factor K p (c j))) e x).symm

/-- **The reindexing isomorphism conjugates the indeterminacy automorphisms at a prime onto
the indeterminacy automorphisms**: `φ ↦ E ∘ φ ∘ E⁻¹` maps `tensorAut` (the tensor products
`⊗_j g_j` of factor automorphisms) onto `tensorAut` of the reindexed packet. -/
theorem image_iUnion_tensorAut_packetReindex (X : Set (Tensor K (.finite p) c)) :
    packetReindex (.finite p) c e '' (⋃ φ ∈ tensorAut p c, φ '' X) =
      ⋃ φ ∈ tensorAut p (c ∘ e.symm), φ '' (packetReindex (.finite p) c e '' X) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, hy, rfl⟩
    obtain ⟨φ, ⟨g, hg, rfl⟩, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hy
    refine Set.mem_iUnion₂.mpr ⟨_, ⟨fun j' => g (e.symm j'), fun j' => hg (e.symm j'), rfl⟩,
      packetReindex (.finite p) c e x, ⟨x, hx, rfl⟩, ?_⟩
    exact (packetReindex_congr c e p g x).symm
  · intro y hy
    obtain ⟨φ, ⟨g', hg', rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨g, rfl⟩ : ∃ g : ∀ j, Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j),
        (fun j' => g (e.symm j')) = g' :=
      ⟨(Equiv.piCongrLeft' (fun j => Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j)) e).symm g',
        (Equiv.piCongrLeft' (fun j => Factor K p (c j) ≃ₗ[ℚ_[p]] Factor K p (c j))
          e).apply_symm_apply g'⟩
    have hmem : ∀ j, g j ∈ factorAut p (c j) := fun j => by
      have : g (e.symm (e j)) ∈ factorAut p (c (e.symm (e j))) := hg' (e j)
      rwa [e.symm_apply_apply] at this
    refine ⟨PiTensorProduct.congr g x, Set.mem_iUnion₂.mpr ⟨_, ⟨g, hmem, rfl⟩, x, hx, rfl⟩, ?_⟩
    exact packetReindex_congr c e p g x

/-! #### The archimedean log-shell -/

/-- **The reindexing isomorphism is an isometry of the tensor-product Hermitian metrics.** -/
theorem archTensorInner_packetReindex (x y : Tensor K .infinite c) :
    archTensorInner (c ∘ e.symm) (packetReindex .infinite c e x) (packetReindex .infinite c e y) =
      archTensorInner c x y := by
  have key : ∀ f g : ∀ j, Factor' K .infinite (c j),
      archTensorInner (c ∘ e.symm) (packetReindex .infinite c e (PiTensorProduct.tprod ℝ f))
          (packetReindex .infinite c e (PiTensorProduct.tprod ℝ g)) =
        archTensorInner c (PiTensorProduct.tprod ℝ f) (PiTensorProduct.tprod ℝ g) := by
    intro f g
    rw [packetReindex_tprod (vQ := .infinite), packetReindex_tprod (vQ := .infinite)]
    exact (archTensorInner_tprod (c ∘ e.symm) (fun j' => f (e.symm j'))
      (fun j' => g (e.symm j'))).trans ((Equiv.prod_comp e.symm fun j =>
        archInner (c j) (f j) (g j)).trans (archTensorInner_tprod c f g).symm)
  have h : (archTensorInner (c ∘ e.symm)).compl₁₂ (packetReindex .infinite c e).toLinearMap
      (packetReindex .infinite c e).toLinearMap = archTensorInner c := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
    refine PiTensorProduct.ext (MultilinearMap.ext fun g => ?_)
    exact key f g
  exact LinearMap.congr_fun₂ h x y

/-- **The reindexing isomorphism preserves the archimedean log-shell** (the unit ball of the
tensor-product Hermitian metric). -/
theorem image_archLogShell_packetReindex :
    packetReindex .infinite c e '' archLogShell c = archLogShell (c ∘ e.symm) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_archLogShell, archTensorInner_packetReindex c e, ← Fintype.card_congr e]
    exact hx
  · intro hy
    refine ⟨(packetReindex .infinite c e).symm y, ?_, AlgEquiv.apply_symm_apply _ y⟩
    rw [mem_archLogShell, ← archTensorInner_packetReindex c e, AlgEquiv.apply_symm_apply,
      Fintype.card_congr e]
    exact hy

end PacketReindex

end LocalConstruct

/-! ## The container: weights, hulls and volumes -/

namespace LocalTheory

open LocalConstruct NumberField
open scoped Pointwise

variable {K : Type u} [Field K] [NumberField K] {k : Type u} [Field k] [NumberField k]
  (σ : PlaceSection K k)

/-- **The (Ind1)-action on the tuples of places preserves the tuple weights**:
`∏_l w(c(τ⁻¹ l)) = ∏_l w(c l)`. -/
theorem tupleWeight_comp_perm {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (τ : Equiv.Perm ι) (c : ι → LocalTheory.Fiber k vQ) :
    tupleWeight vQ (c ∘ τ.symm) = tupleWeight vQ c :=
  Equiv.prod_comp τ.symm fun j => weight k vQ (c j)

/-- The tuple of places of `c ∘ τ⁻¹` is the tuple of places of `c`, permuted. -/
lemma tuple_comp {ι ι' : Type} (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ)
    (e : ι ≃ ι') : tuple σ vQ (c ∘ e.symm) = tuple σ vQ c ∘ e.symm := rfl

/-- **The (Ind1)-reindexing of a direct summand** `⊗_l K_{v_l}` of the packet at a tuple
`c = (v_l)_l` onto the summand at the tuple `c ∘ τ⁻¹` (`LocalConstruct.packetReindex`). -/
noncomputable def ind1Reindex {ι : Type} [Fintype ι] (vQ : RationalPlace) (τ : Equiv.Perm ι)
    (c : ι → LocalTheory.Fiber k vQ) :
    Tensor K vQ (tuple σ vQ c) ≃ₐ[baseField vQ] Tensor K vQ (tuple σ vQ (c ∘ τ.symm)) :=
  packetReindex vQ (tuple σ vQ c) τ

section Ind1Reindex

variable {ι : Type} [Fintype ι] (τ : Equiv.Perm ι)

/-- The (Ind1)-reindexing preserves the integral structure. -/
theorem image_integral_ind1Reindex (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ) :
    ind1Reindex σ vQ τ c '' integral K vQ (tuple σ vQ c) =
      integral K vQ (tuple σ vQ (c ∘ τ.symm)) :=
  image_integralAt_packetReindex vQ _ τ

/-- The (Ind1)-reindexing preserves the tensor product of the log-shells at a prime. -/
theorem image_shell_ind1Reindex (p : Nat.Primes) (c : ι → LocalTheory.Fiber k (.finite p)) :
    ind1Reindex σ (.finite p) τ c '' shell K p (tuple σ _ c) =
      shell K p (tuple σ _ (c ∘ τ.symm)) :=
  image_tensorLogShell_packetReindex _ τ p

/-- The (Ind1)-reindexing preserves the archimedean log-shell. -/
theorem image_logShell_infinite_ind1Reindex (c : ι → LocalTheory.Fiber k .infinite) :
    ind1Reindex σ .infinite τ c '' logShell K .infinite (tuple σ _ c) =
      logShell K .infinite (tuple σ _ (c ∘ τ.symm)) :=
  image_archLogShell_packetReindex _ τ

/-- The (Ind1)-reindexing maps hull regions `a·O` to hull regions. -/
theorem image_smul_integral_ind1Reindex (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ)
    (a : Tensor K vQ (tuple σ vQ c)) :
    ind1Reindex σ vQ τ c '' (a • integral K vQ (tuple σ vQ c)) =
      ind1Reindex σ vQ τ c a • integral K vQ (tuple σ vQ (c ∘ τ.symm)) :=
  image_smul_integralAt_packetReindex vQ _ τ a

/-- The (Ind1)-reindexing preserves the normalized log-volume of the components. -/
theorem componentVol_image_ind1Reindex (vQ : RationalPlace) (c : ι → LocalTheory.Fiber k vQ)
    (U : Set (Tensor K vQ (tuple σ vQ c))) :
    componentVol K vQ (tuple σ vQ (c ∘ τ.symm)) (ind1Reindex σ vQ τ c '' U) =
      componentVol K vQ (tuple σ vQ c) U :=
  componentVol_image_packetReindex vQ _ τ U

end Ind1Reindex

lemma mem_hullRegions_of_isHullRegion (ι : Type) [Fintype ι] (vQ : RationalPlace)
    {R : Set (packet σ ι vQ).Total} (h : (packet σ ι vQ).IsHullRegion R) :
    R ∈ hullRegions σ ι vQ := by
  cases vQ with
  | finite p => exact h
  | infinite => exact h

variable (n : ℕ)

/-- **The packet log-volume of the holomorphic hull of a product region** is the weighted sum of
the log-volumes of the least hull regions of its components. -/
theorem packetVol_hull_productRegion (i : Fin n) (vQ : RationalPlace)
    (fam : ∀ c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber k vQ,
      Set (Tensor K vQ (tuple σ vQ c)))
    (hfam : ∀ c, fam c ∈ admissible K vQ (tuple σ vQ c))
    (a : ∀ c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber k vQ,
      Tensor K vQ (tuple σ vQ c))
    (ha : ∀ c, IsLeastHull (fam c) (a c)) :
    (vol σ n).packetVol i vQ
        (((hull σ n).system i vQ).hull ((packet σ _ vQ).productRegion fam)) =
      ∑ c : ((Procession.standard n).capsule i).LabelType → LocalTheory.Fiber k vQ,
        tupleWeight vQ c *
          componentVol K vQ (tuple σ vQ c) (a c • integral K vQ (tuple σ vQ c)) := by
  classical
  set U := (packet σ ((Procession.standard n).capsule i).LabelType vQ).productRegion fam
  have hU : U ∈ ((hull σ n).system i vQ).Admissible := ⟨fam, hfam, rfl⟩
  have hl := ((hull σ n).system i vQ).isLeastHullRegion_hull U hU
  obtain ⟨a', ha', hR⟩ := isHullRegion_of_mem_hullRegions σ _ vQ _ hl.1
  have hsub : U ⊆ (packet σ _ vQ).scaledIntegral a' := hR ▸ hl.2.1
  have hne : ∀ c, (fam c).Nonempty := fun c => admissible_nonempty K vQ _ _ (hfam c)
  have hleast : ∀ c, IsLeastHull (fam c) (a' c) := by
    intro c
    refine ⟨ha' c, fun y hy => ?_, fun b hb hfb => ?_⟩
    · have hx : Function.update (fun c' => (hne c').some) c y ∈ U := by
        intro c'
        by_cases h : c' = c
        · subst h; rw [Function.update_self]; exact hy
        · rw [Function.update_of_ne h]; exact (hne c').some_mem
      have := hsub hx c
      rwa [Function.update_self] at this
    · have hmem : (packet σ _ vQ).scaledIntegral (Function.update a' c b) ∈
          hullRegions σ ((Procession.standard n).capsule i).LabelType vQ := by
        refine mem_hullRegions_of_isHullRegion σ _ vQ ⟨Function.update a' c b, fun c' => ?_, rfl⟩
        by_cases h : c' = c
        · subst h; rw [Function.update_self]; exact hb
        · rw [Function.update_of_ne h]; exact ha' c'
      have hUsub : U ⊆ (packet σ _ vQ).scaledIntegral (Function.update a' c b) := by
        intro x hx c'
        by_cases h : c' = c
        · subst h; rw [Function.update_self]; exact hfb (hx c')
        · rw [Function.update_of_ne h]; exact hsub hx c'
      have hle := hl.2.2 _ hmem hUsub
      rw [hR] at hle
      intro y hy
      have hx : Function.update (fun c' => scaledOne σ vQ c' (a' c')) c y ∈
          (packet σ _ vQ).scaledIntegral a' := by
        intro c'
        by_cases h : c' = c
        · subst h; rw [Function.update_self]; exact hy
        · rw [Function.update_of_ne h]
          exact Set.smul_mem_smul_set (one_mem_integral K vQ _)
      have := hle hx c
      rwa [Function.update_self, Function.update_self] at this
  rw [hR]
  refine (packetVol_scaledIntegral K σ n i vQ a').trans ?_
  refine @Fintype.sum_equiv _ _ ℝ ((container σ n).instFintypeComponents i vQ) Pi.instFintype _
    (Equiv.refl _) _ _ fun c => ?_
  exact congrArg (fun S => tupleWeight vQ c * componentVol K vQ (tuple σ vQ c) S)
    ((hleast c).smul_eq (ha c))

/-- **Monotonicity of the packet log-volume between hull regions** (for any section of places;
`TowerArithmetic.packetVol_mono` is the case of the Θ-data). -/
theorem packetVol_mono (i : Fin n) (vQ : RationalPlace)
    (U V : Set (packet σ ((Procession.standard n).capsule i).LabelType vQ).Total)
    (hU : (packet σ _ vQ).IsHullRegion U) (hV : (packet σ _ vQ).IsHullRegion V) (hUV : U ⊆ V) :
    (vol σ n).packetVol i vQ U ≤ (vol σ n).packetVol i vQ V := by
  obtain ⟨a, ha, rfl⟩ := hU
  obtain ⟨b, hb, rfl⟩ := hV
  refine (packetVol_scaledIntegral K σ n i vQ a).trans_le
    (le_of_le_of_eq ?_ (packetVol_scaledIntegral K σ n i vQ b).symm)
  refine Finset.sum_le_sum fun c _ => ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun l _ => (weight_pos k _ _).le)
  apply componentVol_mono K vQ _ _ _ (ha c) (hb c)
  intro y hy
  classical
  have hx : Function.update (fun c' => scaledOne σ vQ c' (a c')) c y ∈
      (packet σ _ vQ).scaledIntegral a := by
    intro c'
    by_cases h : c' = c
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]
      exact Set.smul_mem_smul_set (one_mem_integral K vQ _)
  have := hUV hx c
  rwa [Function.update_self] at this

/-- **Monotonicity of the procession-normalized log-volume** in families of hull regions:
if `R i ⊆ S i` placewise and all packet regions are hull regions `a·O`, then the
procession-normalized log-volume of `R` is at most that of `S`. -/
theorem processionVol_mono (R S : ∀ i : Fin (container σ n).proc.length,
      (container σ n).AdmissibleRegion i)
    (hR : ∀ i vQ, ((container σ n).packet i vQ).IsHullRegion ((R i).region vQ))
    (hS : ∀ i vQ, ((container σ n).packet i vQ).IsHullRegion ((S i).region vQ))
    (hRS : ∀ i, R i ≤ S i) :
    (vol σ n).processionVol R ≤ (vol σ n).processionVol S := by
  unfold LogVolumeData.processionVol
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
  unfold LogVolumeData.globalVol
  exact finsum_le_finsum' ((vol σ n).finite_support_packetVol _)
    ((vol σ n).finite_support_packetVol _) fun vQ =>
      packetVol_mono σ n i vQ _ _ (hR i vQ) (hS i vQ) (hRS i vQ)

end LocalTheory


/-! ## The (Ind1)-invariance of the theta-pilot region and of `−|log(Θ)|` -/

namespace InitialThetaData

open LocalConstruct NumberField
open scoped Pointwise

variable (D : InitialThetaData.{u}) (n : ℕ)

/-- The (Ind1)-reindexing moves the theta value of the capsule at the label `τ⁻¹ j'` of a tuple
`c` to the theta value at the label `j'` of the tuple `c ∘ τ⁻¹`. -/
lemma ind1Reindex_scaleEltAt (i : Fin n) (τ : Equiv.Perm (Lab n i)) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) (j' : Lab n i) :
    LocalTheory.ind1Reindex D.placeSect (.finite p) τ c (D.scaleEltAt n i p c (τ.symm j')) =
      D.scaleEltAt n i p (c ∘ τ.symm) j' :=
  packetReindex_incl (LocalTheory.tuple D.placeSect _ c) τ p j' _ _ _

/-- **(Ind1)-equivariance of the theta-pilot component at a prime**: the reindexing along a
label permutation `τ` (acting on the labels, on the tuples `c ↦ c ∘ τ⁻¹` and on the tensor
factors) maps the theta-pilot component with label positions `S` at the tuple `c` onto the
theta-pilot component with label positions `τ(S)` at the tuple `c ∘ τ⁻¹`. -/
theorem image_thetaFiniteOn_ind1Reindex (i : Fin n) (τ : Equiv.Perm (Lab n i))
    (S : Set (Lab n i)) (p : Nat.Primes) (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.ind1Reindex D.placeSect (.finite p) τ c '' D.thetaFiniteOn n i S p c =
      D.thetaFiniteOn n i (τ '' S) p (c ∘ τ.symm) := by
  unfold thetaFiniteOn
  change packetReindex (.finite p) (LocalTheory.tuple D.placeSect _ c) τ ''
      (⋃ φ ∈ tensorAut p (LocalTheory.tuple D.placeSect _ c), φ '' _) =
    ⋃ φ ∈ tensorAut p (LocalTheory.tuple D.placeSect _ c ∘ τ.symm), φ '' _
  rw [image_iUnion_tensorAut_packetReindex, Set.image_iUnion₂, Set.biUnion_image]
  refine Set.iUnion₂_congr fun φ _ => ?_
  congr 1
  refine Set.iUnion₂_congr fun l _ => ?_
  rw [image_smul_set_algEquiv, image_tensorLogShell_packetReindex]
  congr 1
  have h := D.ind1Reindex_scaleEltAt n i τ p c (τ l)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- **(b) Each single-label theta-pilot component is an (Ind1)-image of IUT IV's**: for every
label `l` of the capsule `S_{j+1}`, the theta-pilot component at a prime with the theta value
at the label `l` (label positions `{l}`) at the tuple `c` is the image under the
(Ind1)-reindexing along the transposition `τ = (l j)` of the component with the theta value at
the label `j` (`ivLabels`, IUT IV's reading) at the tuple `c ∘ τ⁻¹`. -/
theorem thetaFiniteOn_singleton_eq_image (i : Fin n) (l : Lab n i) (p : Nat.Primes)
    (c : Lab n i → LocalTheory.Fiber D.Fmod (.finite p)) :
    D.thetaFiniteOn n i {l} p c =
      (LocalTheory.ind1Reindex D.placeSect (.finite p) (Equiv.swap l (distinguished n i)) c).symm ''
        D.thetaFiniteOn n i (ivLabels n i) p (c ∘ (Equiv.swap l (distinguished n i)).symm) := by
  have h := D.image_thetaFiniteOn_ind1Reindex n i (Equiv.swap l (distinguished n i)) {l} p c
  rw [Set.image_singleton, Equiv.swap_apply_left] at h
  rw [ivLabels, ← h]
  ext x
  constructor
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, AlgEquiv.symm_apply_apply _ x⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rwa [AlgEquiv.symm_apply_apply]

/-- **(Ind1)-invariance of the hull log-volume of the theta-pilot region, packetwise**: for
label permutations `τ_i` of the capsules, the packet log-volume of the holomorphic hull of the
theta-pilot region with label positions `τ_i(S_i)` equals that with label positions `S_i`. At a
prime, the component at the tuple `c ∘ τ⁻¹` is the (Ind1)-image of the component at `c`
(`image_thetaFiniteOn_ind1Reindex`), so its least hull region is the image of the least hull
region, of the same log-volume (`LocalConstruct.IsLeastHull.componentVol_eq`), and the weights
agree (`LocalTheory.tupleWeight_comp_perm`); at `∞` the region does not depend on the labels. -/
theorem packetVol_hull_thetaPilotOn_perm (S : ∀ i : Fin n, Set (Lab n i))
    (hS : ∀ i, (S i).Nonempty) (τ : ∀ i : Fin n, Equiv.Perm (Lab n i))
    (hτS : ∀ i, (τ i '' S i).Nonempty) (i : Fin n) (vQ : RationalPlace) :
    (LocalTheory.vol D.placeSect n).packetVol i vQ
        (((LocalTheory.hull D.placeSect n).hullAdmissible
          (D.thetaPilotOn n (fun i => τ i '' S i) hτS i)).region vQ) =
      (LocalTheory.vol D.placeSect n).packetVol i vQ
        (((LocalTheory.hull D.placeSect n).hullAdmissible
          (D.thetaPilotOn n S hS i)).region vQ) := by
  cases vQ with
  | infinite => rfl
  | finite p =>
    choose a ha using fun c => LocalTheory.exists_leastHull D.Kt p _ _
      (D.thetaComponentOn_admissible n i (S i) (hS i) (.finite p) c)
    choose b hb using fun c => LocalTheory.exists_leastHull D.Kt p _ _
      (D.thetaComponentOn_admissible n i (τ i '' S i) (hτS i) (.finite p) c)
    refine (LocalTheory.packetVol_hull_productRegion D.placeSect n i (.finite p) _
      (fun c => D.thetaComponentOn_admissible n i _ (hτS i) (.finite p) c) b hb).trans
      (Eq.trans ?_ (LocalTheory.packetVol_hull_productRegion D.placeSect n i (.finite p) _
        (fun c => D.thetaComponentOn_admissible n i _ (hS i) (.finite p) c) a ha).symm)
    refine (Fintype.sum_equiv (Equiv.arrowCongr (τ i) (Equiv.refl _)) _ _ fun c => ?_).symm
    change _ = LocalTheory.tupleWeight (.finite p) (c ∘ (τ i).symm) *
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ (c ∘ (τ i).symm))
        (b (c ∘ (τ i).symm) • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.placeSect _ (c ∘ (τ i).symm)))
    rw [LocalTheory.tupleWeight_comp_perm]
    congr 1
    have hb' : IsLeastHull (LocalTheory.ind1Reindex D.placeSect (.finite p) (τ i) c ''
        D.thetaFiniteOn n i (S i) p c) (b (c ∘ (τ i).symm)) := by
      rw [D.image_thetaFiniteOn_ind1Reindex n i (τ i) (S i) p c]
      exact hb (c ∘ (τ i).symm)
    exact (IsLeastHull.componentVol_eq _ (ha c) hb').symm

/-- The right-hand side `−|log(Θ)|` for the label positions `S` depends only on `S`. -/
lemma rhsDataOn_rhs_congr {S S' : ∀ i : Fin ((D.ℓ - 1) / 2), Set (Lab ((D.ℓ - 1) / 2) i)}
    (h : S = S') (hS : ∀ i, (S i).Nonempty) (hS' : ∀ i, (S' i).Nonempty) :
    (D.rhsDataOn S hS).rhs = (D.rhsDataOn S' hS').rhs := by
  subst h; rfl

/-- **(Ind1)-invariance of the procession-normalized log-volume** `−|log(Θ)|`: permuting the
label positions of the theta values by label permutations `τ_i` of the capsules `S_{j+1}`
(the label permutations of (Ind1), IUT III, Theorem 3.11) does not change the
procession-normalized log-volume of the holomorphic hull of the theta-pilot region. -/
theorem rhsDataOn_perm (S : ∀ i : Fin ((D.ℓ - 1) / 2), Set (Lab ((D.ℓ - 1) / 2) i))
    (hS : ∀ i, (S i).Nonempty) (τ : ∀ i : Fin ((D.ℓ - 1) / 2), Equiv.Perm (Lab _ i))
    (hτS : ∀ i, (τ i '' S i).Nonempty) :
    (D.rhsDataOn (fun i => τ i '' S i) hτS).rhs = (D.rhsDataOn S hS).rhs := by
  change (LocalTheory.vol D.placeSect _).processionVol
      ((LocalTheory.hull D.placeSect _).hullFamily (D.thetaPilotOn _ (fun i => τ i '' S i) hτS)) =
    (LocalTheory.vol D.placeSect _).processionVol
      ((LocalTheory.hull D.placeSect _).hullFamily (D.thetaPilotOn _ S hS))
  unfold LogVolumeData.processionVol LogVolumeData.globalVol
  congr 1
  refine Finset.sum_congr rfl fun i _ => finsum_congr fun vQ => ?_
  exact D.packetVol_hull_thetaPilotOn_perm _ S hS τ hτS i vQ

/-- **(c) The variant is the hull taken for each (Ind1)-image separately**: for every choice of
labels `l_i ∈ S_{j+1}` at which the theta values `q^{j²}` of the capsules sit, the
procession-normalized log-volume `−|log(Θ)|` of the holomorphic hull of the theta-pilot region
with label positions `{l_i}` equals that of IUT IV's reading (`rhsData`, label positions
`{j}`): each single-label region is the image of IUT IV's region under the label permutation
`(l_i j)` of (Ind1) (`thetaFiniteOn_singleton_eq_image`), and the procession-normalized
log-volume of the hull is (Ind1)-invariant (`rhsDataOn_perm`). -/
theorem rhsDataOn_singleton (l : ∀ i : Fin ((D.ℓ - 1) / 2), Lab _ i) :
    (D.rhsDataOn (fun i => {l i}) fun _ => Set.singleton_nonempty _).rhs = D.rhsData.rhs := by
  let τ : ∀ i : Fin ((D.ℓ - 1) / 2), Equiv.Perm (Lab _ i) :=
    fun i => Equiv.swap (distinguished _ i) (l i)
  have hτ : (fun i => τ i '' ivLabels _ i) = fun i => {l i} := by
    funext i
    rw [ivLabels, Set.image_singleton, Equiv.swap_apply_left]
  have hne : ∀ i, (τ i '' ivLabels _ i).Nonempty := fun i => (ivLabels_nonempty _ i).image _
  rw [← D.rhsDataOn_rhs_congr hτ hne, D.rhsDataOn_perm _ _ τ hne]

end InitialThetaData

end Iut
