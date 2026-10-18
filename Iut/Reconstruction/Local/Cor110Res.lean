/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110H2

/-!
# Open subgroups and the index normalisation ([AbsTopIII], Remark 1.10.1 (iii), MR9 L1)

[AbsTopIII], Corollary 1.10 (a) (`Topics in Absolute Anabelian Geometry III.txt`, l.2393–2395):

> "[Thus, the underlying module of `μ_{Q/Z}(G_k)`, `μ_Ẑ(G_k)` is unaffected by the operation of
> passing from `G_k` to an open subgroup of `G_k`.]"

and Remark 1.10.1 (iii) (l.2558–2561):

> "In a similar vein, note that the isomorphism `H²(G_k, μ_Ẑ(G_k)) ∼→ Ẑ` of Corollary 1.10, (a),
> is functorial in the sense that it is compatible with the result of dividing the usual
> functorially induced morphism by a factor given by the index of the open subgroups of `G_k`
> under consideration."

Group-theoretic part, for an open embedding `ι : H →* G` of compact topological groups (e.g. the
inclusion of an open subgroup):

* `barEquivEmb hι : lim→_V V^ab ≃* lim→_U U^ab` (`AbBar H ≃* AbBar G`): the open subgroups of
  `G` contained in `ι(H)` are cofinal, and `V ↦ ι(V)` is compatible with the transfer
  (`abFamEmb_abTrans`); it intertwines the conjugation actions (`barEmb_barConj`);
* hence `muNEmb hι n : μ_n(H) ≃* μ_n(G)`, `ι`-equivariant (`muNEmb_smul`): **the module
  `μ_n(G)` is unaffected by passing to an open subgroup**;
* the **restriction** `resZHatG hι : H²(G, μ_Ẑ(G)) → H²(H, μ_Ẑ(H))`, defined group-theoretically
  as `ι^*` on cochains combined with `μ_n(G) ≅ μ_n(H)`.

Galois part, for `K'/k` finite inside `Ω` and `ι = resScalars K' : G_{K'} ↪ G_k`
(`isOpenEmbedding_resScalars`):

* `muNEquiv_muNEmb`: the group-theoretic identification `μ_n(G_{K'}) ≅ μ_n(G_k)` is compatible
  with the comparison isomorphisms `μ_n(G_{K'}) ≅ μ_n(Ω) ≅ μ_n(G_k)` of `Cor110.lean` (from
  the Galois naturality of the Artin map, `PadicField.artin_naturality`);
* **`h2ZHatGEquiv_resZHatG`** (Remark 1.10.1 (iii)): `h2ZHatGEquiv (res x) = [K' : k] •
  h2ZHatGEquiv x`, i.e. `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` is compatible with restriction to the open
  subgroup `G_{K'}` after dividing by the index `[G_k : G_{K'}] = [K' : k]`
  (`PadicField.h2ZHatOneEquiv_res` on the field side).
-/

namespace Iut.Reconstruction

open PadicField IntermediateField MonoidHom KummerTheory Brauer ContH2 Topology

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Open embeddings and `lim→ U^ab` -/

theorem le_of_sg_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {i j : OpenIdx G}
    (h : sg j ≤ sg i) : i ≤ j := h

theorem conjCont_symm_apply {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] (g x : X) : (conjCont g).symm x = g⁻¹ * x * g := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  simp [conjCont_apply, mul_assoc]

section OpenEmb

variable {H G : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : H →* G} (hι : IsOpenEmbedding ι)

include hι

/-- The image `ι(V)` of an open subgroup `V ⊆ H`, an open subgroup of `G`. -/
def idxEmb (i : OpenIdx H) : OpenIdx G :=
  OrderDual.toDual ⟨(sg i).map ι, hι.isOpenMap _ (isOpen_sg i)⟩

theorem sg_idxEmb (i : OpenIdx H) : sg (idxEmb hι i) = (sg i).map ι := rfl

theorem idxEmb_mono {i j : OpenIdx H} (h : i ≤ j) : idxEmb hι i ≤ idxEmb hι j :=
  le_of_sg_le (Subgroup.map_mono (sg_le h))

theorem continuous_equivMapOfInjective_symm (i : OpenIdx H) :
    Continuous ((sg i).equivMapOfInjective ι hι.injective).symm := by
  rw [(hι.isEmbedding.comp IsEmbedding.subtypeVal).continuous_iff]
  have : (ι ∘ Subtype.val) ∘ ((sg i).equivMapOfInjective ι hι.injective).symm = Subtype.val :=
    funext fun y =>
      congrArg Subtype.val (((sg i).equivMapOfInjective ι hι.injective).apply_symm_apply y)
  rw [this]
  exact continuous_subtype_val

/-- `V ≃ₜ* ι(V)`. -/
def sgEmb (i : OpenIdx H) : sg i ≃ₜ* sg (idxEmb hι i) :=
  { toMulEquiv := (sg i).equivMapOfInjective ι hι.injective
    continuous_toFun := (hι.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := continuous_equivMapOfInjective_symm hι i }

theorem coe_sgEmb (i : OpenIdx H) (u : sg i) : ((sgEmb hι i u : sg (idxEmb hι i)) : G) = ι u :=
  rfl

/-- `V^ab ≃ ι(V)^ab`. -/
def abFamEmb (i : OpenIdx H) : AbFam H i ≃* AbFam G (idxEmb hι i) :=
  abEquiv (sgEmb hι i)

theorem abFamEmb_mk (i : OpenIdx H) (u : sg i) :
    abFamEmb hι i (abMk _ u) = abMk _ (sgEmb hι i u) := rfl

/-- **The transfer commutes with `V ↦ ι(V)`.** -/
theorem abFamEmb_abTrans {i j : OpenIdx H} (h : i ≤ j) (x : AbFam H i) :
    abFamEmb hι j (abTrans H i j h x) =
      abTrans G _ _ (idxEmb_mono hι h) (abFamEmb hι i x) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change abFamEmb hι j (verAb _ _ (abMk _ u)) = verAb _ _ (abFamEmb hι i (abMk _ u))
  rw [verAb_mk, abFamEmb_mk, verAb_mk]
  set e : sg i ≃* sg (idxEmb hι i) := (sgEmb hι i).toMulEquiv
  have hmap : ((sg j).subgroupOf (sg i)).map e.toMonoidHom =
      (sg (idxEmb hι j)).subgroupOf (sg (idxEmb hι i)) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(y : H), hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨e.symm x, ?_, by simp⟩
      have : ((e.symm x : sg i) : H) = y :=
        hι.injective ((congrArg Subtype.val (e.apply_symm_apply x)).trans hyx.symm)
      rw [this]
      exact hy
  change abFamEmb hι j ((abMkOf (sg_le h)).transfer u) =
    (abMkOf (sg_le (idxEmb_mono hι h))).transfer (e u)
  rw [MonoidHom.transfer_map_equiv e hmap, ← MulEquiv.coe_toMonoidHom, ← transfer_comp_hom]
  congr 1

/-- **The map `lim→_V V^ab → lim→_U U^ab` induced by the open embedding `ι`.** -/
def barEmb : AbBar H →* AbBar G where
  toFun := DirectLimit.lift (abTrans H)
    (fun i x => toBar G (idxEmb hι i) (abFamEmb hι i x)) fun i j h x => by
      rw [abFamEmb_abTrans, toBar_abTrans]
  map_one' := DirectLimit.lift_one (g := fun i => (toBar G (idxEmb hι i)).comp
    (abFamEmb hι i).toMonoidHom) _
  map_mul' x y := DirectLimit.lift_mul (g := fun i => (toBar G (idxEmb hι i)).comp
    (abFamEmb hι i).toMonoidHom) _ x y

theorem barEmb_toBar (i : OpenIdx H) (x : AbFam H i) :
    barEmb hι (toBar H i x) = toBar G (idxEmb hι i) (abFamEmb hι i x) := rfl

/-- Every open subgroup of `G` contained in `ι(H)` is of the form `ι(V)`. -/
theorem exists_idxEmb_eq (l : OpenIdx G) (hl : sg l ≤ ι.range) : ∃ l', idxEmb hι l' = l := by
  refine ⟨OrderDual.toDual ⟨(sg l).comap ι, (isOpen_sg l).preimage hι.continuous⟩, ?_⟩
  apply OpenSubgroup.toSubgroup_injective
  change ((sg l).comap ι).map ι = sg l
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := hl hx
    exact ⟨y, hx, rfl⟩

theorem barEmb_injective : Function.Injective (barEmb hι) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨i, x, rfl⟩ := exists_toBar H z
  rw [barEmb_toBar, ← map_one (toBar G (idxEmb hι i))] at hz
  obtain ⟨l, hil, hil2, hl⟩ := Quotient.exact hz
  have hlr : sg l ≤ ι.range := (sg_le hil).trans (Subgroup.map_le_range ι (sg i))
  obtain ⟨l', rfl⟩ := exists_idxEmb_eq hι l hlr
  have hil' : i ≤ l' := by
    refine le_of_sg_le fun y hy => ?_
    obtain ⟨y', hy', he⟩ := sg_le hil (⟨y, hy, rfl⟩ : ι y ∈ sg (idxEmb hι l'))
    rw [← hι.injective he]
    exact hy'
  rw [map_one, ← abFamEmb_abTrans hι hil', ← map_one (abFamEmb hι l')] at hl
  have h1 := (abFamEmb hι l').injective hl
  rw [← toBar_abTrans H hil' x, h1, map_one]

theorem barEmb_surjective : Function.Surjective (barEmb hι) := by
  intro z
  obtain ⟨j, x, rfl⟩ := exists_toBar G z
  have key : ∀ l : OpenIdx G, j ≤ l → sg l ≤ ι.range → ∃ w, barEmb hι w = toBar G j x := by
    intro l hjl hl
    obtain ⟨l', rfl⟩ := exists_idxEmb_eq hι l hl
    refine ⟨toBar H l' ((abFamEmb hι l').symm (abTrans G j _ hjl x)), ?_⟩
    rw [barEmb_toBar, MulEquiv.apply_symm_apply, toBar_abTrans]
  have hR : IsOpen ((sg j ⊓ ι.range : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, MonoidHom.coe_range]
    exact (isOpen_sg j).inter hι.isOpen_range
  exact key (OrderDual.toDual ⟨sg j ⊓ ι.range, hR⟩) (le_of_sg_le inf_le_left) inf_le_right

/-- **`lim→_V V^ab ≃* lim→_U U^ab`** for an open embedding `ι : H ↪ G`. -/
def barEquivEmb : AbBar H ≃* AbBar G :=
  MulEquiv.ofBijective (barEmb hι) ⟨barEmb_injective hι, barEmb_surjective hι⟩

theorem barEquivEmb_apply (z : AbBar H) : barEquivEmb hι z = barEmb hι z := rfl

theorem sg_idxEmb_conj (h : H) (i : OpenIdx H) :
    sg (idxEmb hι (idxMap (conjCont h) i)) = sg (idxMap (conjCont (ι h)) (idxEmb hι i)) := by
  ext x
  rw [sg_idxEmb, sg_idxMap, sg_idxMap, sg_idxEmb]
  change (∃ y, (conjCont h).symm y ∈ sg i ∧ ι y = x) ↔
    ∃ y, y ∈ sg i ∧ ι y = (conjCont (ι h)).symm x
  simp only [conjCont_symm_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, by simp [map_mul, map_inv]⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨h * y * h⁻¹, by simpa [mul_assoc] using hy, ?_⟩
    rw [map_mul, map_mul, hyx, map_inv]
    group

/-- **`barEmb` intertwines the conjugation actions**: `ι_*(h · z) = ι(h) · ι_*(z)`. -/
theorem barEmb_barConj (h : H) (z : AbBar H) :
    barEmb hι (barConj H h z) = barConj G (ι h) (barEmb hι z) := by
  have : (barEmb hι).comp (barConj H h) = (barConj G (ι h)).comp (barEmb hι) := by
    refine AbBar.hom_ext fun i u => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, barConj, barConj, barMap_toBar_mk,
      barEmb_toBar, barEmb_toBar, abFamEmb_mk, abFamEmb_mk, barMap_toBar_mk]
    refine toBar_mk_eq (sg_idxEmb_conj hι h i) _ _ ?_
    change ι (h * u * h⁻¹) = ι h * ι u * (ι h)⁻¹
    rw [map_mul, map_mul, map_inv]
  exact DFunLike.congr_fun this z

/-! ### `μ_n(H) ≅ μ_n(G)` and the restriction on `H²` -/

/-- **`μ_n(H) ≃* μ_n(G)`** for an open embedding `ι : H ↪ G`: the module `μ_n` is unaffected
by passing to an open subgroup. -/
def muNEmb (n : ℕ) : muN H n ≃* muN G n where
  toFun z := ⟨barEquivEmb hι z, by rw [mem_muN, ← map_pow, mem_muN.1 z.2, map_one]⟩
  invFun z := ⟨(barEquivEmb hι).symm z, by rw [mem_muN, ← map_pow, mem_muN.1 z.2, map_one]⟩
  left_inv z := Subtype.ext ((barEquivEmb hι).symm_apply_apply (z : AbBar H))
  right_inv z := Subtype.ext ((barEquivEmb hι).apply_symm_apply (z : AbBar G))
  map_mul' z w := Subtype.ext (map_mul (barEquivEmb hι) (z : AbBar H) w)

theorem coe_muNEmb {n : ℕ} (z : muN H n) : (muNEmb hι n z : AbBar G) = barEmb hι z := rfl

theorem coe_muNEmb_symm {n : ℕ} (z : muN G n) :
    ((muNEmb hι n).symm z : AbBar H) = (barEquivEmb hι).symm z := rfl

/-- **`μ_n(H) ≃* μ_n(G)` is `ι`-equivariant.** -/
theorem muNEmb_smul {n : ℕ} (h : H) (z : muN H n) :
    muNEmb hι n (h • z) = ι h • muNEmb hι n z :=
  Subtype.ext (barEmb_barConj hι h z)

theorem muNEmb_symm_smul {n : ℕ} (h : H) (z : muN G n) :
    (muNEmb hι n).symm (ι h • z) = h • (muNEmb hι n).symm z := by
  apply (muNEmb hι n).injective
  rw [MulEquiv.apply_symm_apply, muNEmb_smul, MulEquiv.apply_symm_apply]

/-- **Restriction** `H²(G, μ_n(G)) → H²(H, μ_n(H))`, through `μ_n(G) ≅ μ_n(H)`. -/
def resMuG (n : ℕ) : H2MuG G n →* H2MuG H n :=
  ContH2.map ι hι.continuous (muNEmb hι n).symm.toMonoidHom fun h z => muNEmb_symm_smul hι h z

theorem resMuG_h2PowG {n m : ℕ} (h : n ∣ m) (x : H2MuG G m) :
    resMuG hι n (h2PowG G h x) = h2PowG H h (resMuG hι m x) := by
  induction x using ContH2.induction_on with | h f => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  exact cocycles_ext fun a b => Subtype.ext (map_pow (barEquivEmb hι).symm _ _)

/-- **Restriction** `H²(G, μ_Ẑ(G)) → H²(H, μ_Ẑ(H))`, defined group-theoretically. -/
def resZHatG : H2ZHatG G →* H2ZHatG H :=
  (MonoidHom.pi fun n : ℕ+ => (resMuG hι n).comp
    ((Pi.evalMonoidHom (fun n : ℕ+ => H2MuG G n) n).comp (H2ZHatG G).subtype)).codRestrict _
    fun x n m h => by
      simp only [MonoidHom.pi_apply, MonoidHom.coe_comp, Function.comp_apply,
        Pi.evalMonoidHom_apply, Subgroup.coe_subtype]
      rw [← resMuG_h2PowG, x.2 n m h]

theorem resZHatG_apply (x : H2ZHatG G) (n : ℕ+) :
    (resZHatG hι x).1 n = resMuG hι n (x.1 n) := rfl

end OpenEmb

/-! ### `G_{K'} ⊆ G_k` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable (K' : IntermediateField k Ω) [FiniteDimensional k K']

/-- **`G_{K'} ↪ G_k` is an open embedding.** -/
theorem isOpenEmbedding_resScalars : IsOpenEmbedding (resScalars (K := k) K') := by
  have hf : ⇑(resScalars (K := k) K') =
      Subtype.val ∘ (fixingSubgroupContEquiv K').symm.toHomeomorph := by
    funext σ
    exact AlgEquiv.ext fun x => rfl
  rw [hf]
  exact K'.fixingSubgroup_isOpen.isOpenEmbedding_subtypeVal.comp
    (fixingSubgroupContEquiv K').symm.toHomeomorph.isOpenEmbedding

variable {K'}

theorem mem_fld_idxEmb_iff (i : OpenIdx (Ω ≃ₐ[K'] Ω)) (x : Ω) :
    x ∈ fld (idxEmb (isOpenEmbedding_resScalars K') i) ↔ x ∈ fld i := by
  rw [fld, fld, IntermediateField.mem_fixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx σ hσ
    exact hx _ ⟨σ, hσ, rfl⟩
  · rintro hx _ ⟨σ, hσ, rfl⟩
    exact hx σ hσ

variable (p) in
/-- The fixed fields of `V ⊆ G_{K'}` and of its image in `G_k` coincide. -/
def fldEmb (i : OpenIdx (Ω ≃ₐ[K'] Ω)) :
    fld i ≃ₐ[ℚ_[p]] fld (idxEmb (isOpenEmbedding_resScalars K') i) where
  toFun x := ⟨x, (mem_fld_idxEmb_iff i x).2 x.2⟩
  invFun y := ⟨y, (mem_fld_idxEmb_iff i y).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem fldEmb_compat (i : OpenIdx (Ω ≃ₐ[K'] Ω)) (c : fld i) :
    (RingEquiv.refl Ω) (algebraMap (fld i) Ω c) =
      algebraMap (fld (idxEmb (isOpenEmbedding_resScalars K') i)) Ω (fldEmb p i c) := rfl

set_option maxHeartbeats 2000000 in
-- the instances on fixed fields of subgroups of `Gal(Ω/K')`, `K'` an intermediate field, are slow
/-- **The comparison with `𝒪^×_Ω` is compatible with `G_{K'} ⊆ G_k` on generators**: from the
naturality of the Artin map (`PadicField.artin_naturality`) for the identity of the fixed
field. -/
theorem unitsMap_emb (i : OpenIdx (Ω ≃ₐ[K'] Ω)) (x : abUnits (sg i)) :
    ((unitsMap p (idxEmb (isOpenEmbedding_resScalars K') i)
        ⟨abFamEmb _ i x, (abEquiv_mem_abUnits_iff _ _).2 x.2⟩ : Ωˣ) : Ω) =
      ((unitsMap p i x : Ωˣ) : Ω) := by
  set hι := isOpenEmbedding_resScalars K'
  set j := idxEmb hι i
  set τ := fldEmb p i
  set σ := RingEquiv.refl Ω
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective _ (x : TopologicalAbelianization (sg i))
  set a : unitGroup p (fld i) := (unitsAbEquiv p (fld i) Ω).symm (abUnitsEquiv (galEquiv i) x)
  have hg : AlgEquiv.restrictNormalHom (maxAbelian (fld i) Ω) (galEquiv i g0) =
      artin p (fld i) Ω (a : (fld i)ˣ) := by
    rw [← galAbEquiv_unitsAbEquiv, MulEquiv.apply_symm_apply, coe_abUnitsEquiv, ← hg0]
    rfl
  set b : unitGroup p (fld j) := ⟨Units.map (τ : fld i →* fld j) (a : (fld i)ˣ), by
    rw [mem_unitGroup, Units.coe_map]
    change nrm p (fld j) (τ _) = 1
    rw [nrm_algEquiv']
    exact a.2⟩
  set x' : abUnits (sg j) := ⟨abFamEmb hι i x, (abEquiv_mem_abUnits_iff _ _).2 x.2⟩
  have hx' : abUnitsEquiv (galEquiv j) x' = unitsAbEquiv p (fld j) Ω b := by
    apply Subtype.ext
    apply (galAbEquiv p (fld j) Ω).injective
    rw [galAbEquiv_unitsAbEquiv, coe_abUnitsEquiv]
    change galAbEquiv p (fld j) Ω (abEquiv (galEquiv j) (abFamEmb hι i
      (x : TopologicalAbelianization (sg i)))) = _
    rw [← hg0]
    change galAbEquiv p (fld j) Ω (abEquiv (galEquiv j)
      (QuotientGroup.mk (sgEmb hι i g0))) = _
    rw [abEquiv_mk, galAbEquiv_mk]
    ext y'
    obtain ⟨y, rfl⟩ := (maxAbelianRingEquiv τ σ (fldEmb_compat i)).surjective y'
    have hN := artin_naturality τ σ (fldEmb_compat i) (a : (fld i)ˣ) y
    change _ = (artin p (fld j) Ω (Units.map (τ : fld i →* fld j) (a : (fld i)ˣ))
      (maxAbelianRingEquiv τ σ (fldEmb_compat i) y) : Ω)
    rw [hN, ← hg]
    have hc := AlgEquiv.restrictNormal_commutes (galEquiv i g0) (maxAbelian (fld i) Ω) y
    change _ = σ (algebraMap (maxAbelian (fld i) Ω) Ω ((galEquiv i g0).restrictNormal _ y))
    rw [hc]
    have hc' := AlgEquiv.restrictNormal_commutes (galEquiv j (sgEmb hι i g0))
      (maxAbelian (fld j) Ω) (maxAbelianRingEquiv τ σ (fldEmb_compat i) y)
    change algebraMap (maxAbelian (fld j) Ω) Ω
      ((galEquiv j (sgEmb hι i g0)).restrictNormal _
        (maxAbelianRingEquiv τ σ (fldEmb_compat i) y)) = _
    rw [hc']
    rfl
  change (((((unitsAbEquiv p (fld j) Ω).symm (abUnitsEquiv (galEquiv j) x')) :
    unitGroup p (fld j)) : (fld j)ˣ) : fld j) = ((((a : unitGroup p (fld i)) : (fld i)ˣ) :
      fld i) : Ω)
  rw [hx', MulEquiv.symm_apply_apply]
  rfl

include hp in
theorem barEmb_mem_unitsBar {z : AbBar (Ω ≃ₐ[K'] Ω)} (hz : z ∈ unitsBar (Ω ≃ₐ[K'] Ω)) :
    barEmb (isOpenEmbedding_resScalars K') z ∈ unitsBar (Ω ≃ₐ[k] Ω) := by
  obtain ⟨i, x, hx, rfl⟩ := (mem_unitsBar_iff (p := p) z).1 hz
  rw [barEmb_toBar]
  exact (mem_unitsBar_iff (p := p) _).2
    ⟨_, _, (abEquiv_mem_abUnits_iff _ _).2 hx, rfl⟩

/-- **`𝒪^×_{k̄}(G_{K'}) ≅ 𝒪^×_Ω ≅ 𝒪^×_{k̄}(G_k)` is the group-theoretic `barEmb`.** -/
theorem unitsBarEquiv_barEmb (z : unitsBar (Ω ≃ₐ[K'] Ω)) :
    ((unitsBarEquiv p k Ω ⟨barEmb (isOpenEmbedding_resScalars K') z,
      barEmb_mem_unitsBar (p := p) z.2⟩ : Ωˣ) : Ω) =
      ((unitsBarEquiv p K' Ω z : Ωˣ) : Ω) := by
  obtain ⟨i, x, hx, hz⟩ := (mem_unitsBar_iff (p := p) z.1).1 z.2
  have hz' : z = ⟨toBar _ i x, (mem_unitsBar_iff (p := p) _).2 ⟨i, x, hx, rfl⟩⟩ := Subtype.ext hz
  subst hz'
  have e1 := unitsBarEquiv_toBar (p := p) i ⟨x, hx⟩
  have e2 := unitsBarEquiv_toBar (p := p) (idxEmb (isOpenEmbedding_resScalars K') i)
    ⟨abFamEmb _ i x, (abEquiv_mem_abUnits_iff _ _).2 hx⟩
  simp only [barEmb_toBar]
  rw [e2, e1]
  exact unitsMap_emb i ⟨x, hx⟩

set_option maxHeartbeats 1000000 in
/-- **The identification `μ_n(G_{K'}) ≅ μ_n(G_k)` is compatible with `μ_n(·) ≅ μ_n(Ω)`.** -/
theorem muNEquiv_muNEmb (n : ℕ) [NeZero n] (z : muN (Ω ≃ₐ[K'] Ω) n) :
    muNEquiv p k Ω n (muNEmb (isOpenEmbedding_resScalars K') n z) = muNEquiv p K' Ω n z := by
  apply Mu.ext
  apply Units.ext
  rw [val_muNEquiv, val_muNEquiv, muQZHom_apply, muQZHom_apply]
  have e := unitsBarEquiv_barEmb (p := p) (K' := K')
    ⟨(z : AbBar (Ω ≃ₐ[K'] Ω)), muQZ_le_unitsBar (p := p) (muN_le_muQZ _ n z.2)⟩
  exact Eq.trans (congrArg (fun w => ((unitsBarEquiv p k Ω w : Ωˣ) : Ω))
    (Subtype.ext (coe_muNEmb _ z))) e

theorem h2MuGEquiv_resMuG (n : ℕ) [NeZero n] (x : H2MuG (Ω ≃ₐ[k] Ω) n) :
    h2MuGEquiv p K' Ω n (resMuG (isOpenEmbedding_resScalars K') n x) =
      resMu K' n (h2MuGEquiv p k Ω n x) := by
  induction x using ContH2.induction_on with | h f => ?_
  change ContH2.mk _ = ContH2.mk _
  congr 1
  refine cocycles_ext fun a b => ?_
  change muNEquiv p K' Ω n ((muNEmb _ n).symm _) = muNEquiv p k Ω n _
  rw [← muNEquiv_muNEmb (p := p) n, MulEquiv.apply_symm_apply]
  rfl

theorem h2ZHatGEquivOne_resZHatG (x : H2ZHatG (Ω ≃ₐ[k] Ω)) :
    h2ZHatGEquivOne p K' Ω (resZHatG (isOpenEmbedding_resScalars K') x) =
      resZHatOne K' (h2ZHatGEquivOne p k Ω x) :=
  Subtype.ext (funext fun n => h2MuGEquiv_resMuG (p := p) n (x.1 n))

/-- **[AbsTopIII], Remark 1.10.1 (iii)**: the isomorphism `H²(G_k, μ_Ẑ(G_k)) ≅ Ẑ` of
Corollary 1.10 (a) is compatible with the group-theoretic restriction to the open subgroup
`G_{K'} ⊆ G_k` after dividing by the index `[G_k : G_{K'}] = [K' : k]`. -/
theorem h2ZHatGEquiv_resZHatG (x : H2ZHatG (Ω ≃ₐ[k] Ω)) :
    Multiplicative.toAdd (h2ZHatGEquiv p K' Ω (resZHatG (isOpenEmbedding_resScalars K') x)) =
      Module.finrank k K' • Multiplicative.toAdd (h2ZHatGEquiv p k Ω x) := by
  change Multiplicative.toAdd (h2ZHatOneEquiv p K' Ω (h2ZHatGEquivOne p K' Ω _)) =
    Module.finrank k K' • Multiplicative.toAdd (h2ZHatOneEquiv p k Ω (h2ZHatGEquivOne p k Ω x))
  rw [h2ZHatGEquivOne_resZHatG, h2ZHatOneEquiv_res]

/-- The index `[G_k : G_{K'}]` is `[K' : k]`. -/
theorem index_range_resScalars :
    (resScalars (K := k) K').range.index = Module.finrank k K' := by
  have : (resScalars (K := k) K').range = K'.fixingSubgroup := by
    ext σ
    constructor
    · rintro ⟨τ, rfl⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => τ.commutes ⟨x, hx⟩
    · intro hσ
      exact ⟨fixingSubgroupContEquiv K' ⟨σ, hσ⟩, AlgEquiv.ext fun x => rfl⟩
  rw [this]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index K').symm

end Galois

end

end Iut.Reconstruction
