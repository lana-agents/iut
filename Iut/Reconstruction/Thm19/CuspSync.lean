/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CuspPrincipal
import Iut.Reconstruction.Thm19.NFKummer
import CurvesJacobian.Kummer.SyncEquivariant

/-!
# [AbsTopIII] Thm 1.9 (b), (c): residues with coefficients in `M_X = μ_Ẑ(Π_U)`

[AbsTopIII] Thm 1.9 (b) (`Topics in Absolute Anabelian Geometry III.txt` l.2144–2152): "one
constructs […] the isomorphisms `I_z ≅ μ_Ẑ(Π_U)` of Proposition 1.4, (ii) […] for each cusp `z` of
`U`"; (c) (l.2153–2157): "one constructs the subgroup `P_U ⊆ H¹(Π_U, μ_Ẑ(Π_U))` determined by the
cuspidal principal divisors via the isomorphisms of (b) and the characterization of principal
divisors given in Proposition 1.6, (ii)"; Prop 1.8 (l.2061–2106) then tests classes of `P_U`.
`Thm19/CuspPrincipal.lean` and `Thm19/NFKummer.lean` prove (c) and Prop 1.8 with `Ẑ(1)`
coefficients in the Galois model `D` (`Π_U = Pi D`), with the residues `res_p` at inertia indices
`p = (W, σ)`, `σ ∈ I_W ∩ H`, and the tame generator `θ_p = tameGen p`. Here they are transported
to `M_X = Hom(H²(Δ_X, Ẑ), Ẑ)` (curves-jacobian `MX`, a `Π_U`-module, and the `Π_U`-equivariant
`M_X ≅ Ẑ(1)`, `natIsoHatK`, `h1MXEquiv`), and `θ_p` is identified with the synchronization of (b):

* `exists_inertiaBar`, `inertiaBar`: **`I_W ∩ H ⊆ Gal(Ω/F k̄)`** (inertia fixes `k̄`), i.e.
  `σ` lies in the inertia group of `W` in the Galois model `D_{k̄}` (curves-jacobian `barData`)
  of `X_{k̄}`, where curves-jacobian's synchronization lives;
* `idxPlaceBar_eq`: for `p` over a rational point `x`, `W ∩ F k̄ = x_{k̄}`;
  **`proj_tameChar_inertiaBar`**: the tame character of any uniformiser of `W ∩ F k̄` at `σ` is
  `θ_p` (the constant field extension is unramified at `x`, curves-jacobian `ord_placeOf_ιF`);
* `pointData_of_liesOver`, `exists_syncData`: the data of curves-jacobian's `syncEquivBar`
  (`U_x = X_{k̄} ∖ {x}`, `W` centred on `x`, a uniformiser) exist for the prescribed `W`;
* `mxReindex`: `M_X` with the Kummer indices of `F k̄` or of `F` (both all `n ≥ 1`);
* **`syncEquivBar_inertiaToCusp`** (**Thm 1.9 (b) at a cusp**): the synchronization
  `I_x ≅ M_X` (Prop 1.4 (ii), `syncEquivBar`) sends the image of `σ` in `I_x ⊆ Δ_{U_x}`
  (`inertiaToCusp`) to `θ_p` read in `M_X`. This is the match of the inertia indices
  `(W, σ)` of the Kummer side (`U` with any number of cusps) with curves-jacobian's cusp inertia
  `inertiaToCusp` of `U_x`: the residue of a class of `H¹(Π_U, ·)` at the cusp `x` is computed on
  `I_W ∩ H`, and `I_W ∩ H ≅ I_x ⊆ Δ_{U_x}` (`inertiaCuspEquiv`);
* `resMX`, `tameGenMX`, `HasResiduesMX`, `PUMX`: residues, tame generators and `P_U` in
  `H¹(Π_U, M_X)`; `resMX_h1MXEquiv`, `hasResiduesMX_h1MXEquiv`, `res_kummerMapMX`;
  **`resMX_eq_sync_zpow`**: residues of `η` at a cusp `x` are `sync(σ)^{E(x)}`;
* **`mem_PUMX_iff_eta_curve_numberField`**, **`mem_PUMX_iff_eta_curve_padic`**
  (**Thm 1.9 (c) with `M_X` coefficients**, unconditional over number fields and `p`-adic fields);
* `restrictClosedMX`, `IsNFKummerTestMX`; **`isNFKummerTestMX_iff_curve_numberField`**
  (Prop 1.8 (i)) and **`exists_restrictClosedMX_eq_iff_curve`** (Prop 1.8 (ii)) with `M_X`
  coefficients and the Kummer map `kummerMapMX : Γ(U, 𝒪^×) → H¹(Π_U, M_X)`.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

namespace Iut.Reconstruction.Thm19

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- The constants `k̄` lie in every place `W ⊇ k` of an inertia index. -/
lemma kbar_mem_idx (p : InertiaIndex D) (c : kbar k Ω) :
    algebraMap (kbar k Ω) Ω c ∈ p.1.1 :=
  kbar_mem p.1.1 p.2.1 c

omit [IsAlgClosed Ω] in
/-- **`I_W ∩ H ⊆ Gal(Ω/F k̄)`**: an element of the inertia group of a place `W ⊇ k` fixes `k̄`
(residue characteristic `0`, `inertia_fix_algebraic`), so it lifts to the group `H` of the base
change `D_{k̄}` (the Galois model of `X_{k̄}`), still in the inertia group of `W`. -/
lemma exists_inertiaBar (p : InertiaIndex D) :
    ∃ σ' : (baseChange D).H, resK₀ k t (σ' : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) = p.1.2 ∧
      (σ' : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) ∈ GaloisPi1.inertia p.1.1 := by
  obtain ⟨σ, hσ⟩ := exists_resK₀_eq (k := k) (t := t) (h := (p.1.2 : Ω ≃ₐ[K₀ k t] Ω))
    fun x hx => inertia_fix_algebraic p.2.1 p.2.2 (mem_algebraicClosure_iff.mp hx)
  refine ⟨⟨σ, (mem_baseChange_H D).2 (hσ ▸ p.1.2.2)⟩, hσ, fun a ha => ?_⟩
  have := p.2.2 a ha
  rw [← hσ] at this
  exact this

/-- **The lift of `σ ∈ I_W ∩ H` to `I_W ∩ H_{k̄}`** (`exists_inertiaBar`). -/
noncomputable def inertiaBar (p : InertiaIndex D) : inertiaH (baseChange D) p.1.1 :=
  ⟨(exists_inertiaBar p).choose, (exists_inertiaBar p).choose_spec.2⟩

omit [IsAlgClosed Ω] in
lemma inertiaBar_apply (p : InertiaIndex D) (y : Ω) :
    (((inertiaBar p : (baseChange D).H) : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω)) y =
      ((p.1.2 : D.H) : Ω ≃ₐ[K₀ k t] Ω) y := by
  rw [← (exists_inertiaBar p).choose_spec.1]
  rfl

/-- The place of `F` below an inertia index lying over a rational point `x` is `x`. -/
lemma idxVal_eq (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) :
    idxVal p = (placeOfF x).1 := by
  ext y
  exact hpx y

lemma idxVal_ne_top (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) : idxVal p ≠ ⊤ := by
  rw [idxVal_eq p x hpx]
  exact (placeOfF x).ne_top

lemma idxPlace_eq (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) (h : idxVal p ≠ ⊤) :
    idxPlace p h = placeOfF x :=
  Place.ext (idxVal_eq p x hpx)

/-- The uniformiser `unif p` has order `1` at the rational point `x` below `p`. -/
lemma ord_unif (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) :
    (placeOfF x).ord ((unif p : (F D)ˣ) : F D) = 1 := by
  have h := idxVal_ne_top p x hpx
  rw [unif, dif_pos h, Units.val_mk0, ← idxPlace_eq p x hpx h]
  exact (idxPlace p h).exists_ord_eq_one.choose_spec

/-- The place of `F k̄` below an inertia index lying over a rational point `x`. -/
noncomputable def idxPlaceBar (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) :
    Place (kbar k Ω) (F (baseChange D)) :=
  ⟨p.1.1.comap (algebraMap (F (baseChange D)) Ω), fun htop => by
    apply idxVal_ne_top p x hpx
    refine eq_top_iff.2 fun y _ => ?_
    have : ιF D y ∈ p.1.1.comap (algebraMap (F (baseChange D)) Ω) :=
      htop ▸ ValuationSubring.mem_top _
    change ((ιF D y : F (baseChange D)) : Ω) ∈ p.1.1 at this
    rw [coe_ιF] at this
    exact this, kbar_mem_idx p⟩

/-- **It is the place `x_{k̄}`** (the only place of `F k̄` over `x`, `eq_placeOf_of_liesOver`). -/
lemma idxPlaceBar_eq (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) :
    idxPlaceBar p x hpx = placeOf x :=
  eq_placeOf_of_liesOver x _ fun u => by
    change ((ιF D u : F (baseChange D)) : Ω) ∈ p.1.1 ↔ _
    rw [coe_ιF, mem_placeOfF]
    exact hpx u

set_option maxHeartbeats 1600000 in
-- `ContH1.evalTriv` terms unify slowly
/-- **The tame characters of `D` and of its base change `D_{k̄}` agree on `I_W ∩ H`**, at every
level `n`: for `p = (W, σ)` over a `k`-rational point `x` and any uniformiser `π` of `W ∩ F k̄`,
`θ_π(σ) = θ_p` (`tameGen p`, the tame character of a uniformiser of `W ∩ F`). The constant field
extension is unramified at `x` (`ord_placeOf_ιF`), so the two uniformisers differ by a unit,
whose `n`-th roots are fixed by inertia (`smul_eq_of_ord_eq_zero`). -/
theorem proj_tameChar_inertiaBar (p : InertiaIndex D) (x : RatPoint D)
    (hpx : ∀ y : F D, (y : Ω) ∈ p.1.1 ↔ (y : Ω) ∈ x.A) {π : (F (baseChange D))ˣ}
    (hπW : p.1.1.valuation ((π : F (baseChange D)) : Ω) < 1)
    (hπ : ∀ f ∈ F (baseChange D), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (baseChange D)) : Ω))
    (n : ℕ) [NeZero n] :
    ZHatOne.proj (CurvesJacobian.ChernClass.kIdx (baseChange D) n)
        (tameChar (kbar_mem_idx p) π (inertiaBar p)) =
      ZHatOne.proj (CurvesJacobian.ChernClass.kIdx D n) (tameGen p) := by
  set Q := idxPlaceBar p x hpx
  have hQ : ∀ y : F (baseChange D), ((y : F (baseChange D)) : Ω) ∈ p.1.1 ↔ y ∈ Q.1 :=
    fun _ => Iff.rfl
  have hπ1 : Q.ord (π : F (baseChange D)) = 1 :=
    CurvesJacobian.ChernClass.ord_eq_one_of_valuation hQ hπW hπ
  have hQx : Q = placeOf x := idxPlaceBar_eq p x hpx
  have hu1 : Q.ord (ιF D ((unif p : (F D)ˣ) : F D)) = 1 := by
    rw [hQx, ord_placeOf_ιF, ord_unif p x hpx]
  set u : F (baseChange D) := ιF D ((unif p : (F D)ˣ) : F D) / (π : F (baseChange D))
  have hι0 : ιF D ((unif p : (F D)ˣ) : F D) ≠ 0 := (map_ne_zero _).2 (unif p).ne_zero
  have hu0 : u ≠ 0 := div_ne_zero hι0 π.ne_zero
  have hu : Q.ord u = 0 := by
    rw [Q.ord_div hι0 π.ne_zero, hu1, hπ1, sub_self]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((π : F (baseChange D)) : Ω)
    (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq ((u : F (baseChange D)) : Ω)
    (Nat.pos_of_ne_zero (NeZero.ne n))
  have hπΩ : ((π : F (baseChange D)) : Ω) ≠ 0 := fun h => π.ne_zero (Subtype.ext h)
  have huΩ : ((u : F (baseChange D)) : Ω) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hα0 : α ≠ 0 := fun h => hπΩ (by rw [← hα, h, zero_pow (NeZero.ne n)])
  have hγ0 : γ ≠ 0 := fun h => huΩ (by rw [← hγ, h, zero_pow (NeZero.ne n)])
  have hσγ : (inertiaBar p : (baseChange D).H) • γ = γ :=
    CurvesJacobian.ChernClass.smul_eq_of_ord_eq_zero hQ hu0 hu (inertiaBar p).2 hγ
  have hβ : (γ * α) ^ n = (((unif p : (F D)ˣ) : F D) : Ω) := by
    rw [mul_pow, hγ, hα]
    simp only [u, IntermediateField.coe_div, coe_ιF]
    field_simp
  have hL := val_proj_tameChar (kbar_mem_idx p) π (inertiaBar p)
    (CurvesJacobian.ChernClass.kIdx (baseChange D) n) (Units.mk0 α hα0)
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hα))
  have hR := val_proj_tameChar p.2.1 (unif p) ⟨p.1.2, p.2.2⟩
    (CurvesJacobian.ChernClass.kIdx D n) (Units.mk0 (γ * α) (mul_ne_zero hγ0 hα0))
    (Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      exact hβ))
  have hσγ' : ((p.1.2 : D.H) : Ω ≃ₐ[K₀ k t] Ω) γ = γ := by
    rw [← inertiaBar_apply]
    exact hσγ
  apply Mu.ext
  apply Units.ext
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [Units.val_mk0]
  rw [map_mul, hσγ', inertiaBar_apply]
  field_simp

end Generic

/-! ### Points of `X_{k̄}` over a given place of `Ω` -/

section PointData

open CategoryTheory AlgebraicGeometry Belyi Pi1.Orbifold CurvesJacobian.Cusp
  CurvesJacobian.ChernClass

variable {k Ω : Type u} [Field k] [CharZero k]
  [Field Ω] [Algebra k Ω] [IsSepClosed Ω] {t : Ω} [IsGalois (K₀ k t) Ω] {D : GaloisData k t}
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X]
  {eL : X.functionField ≃+* D.L} [Nonempty (⊤ : X.Opens)]
  (hk : ∀ c : k, ((eL (algebraMap k X.functionField c) : D.L) : Ω) = algebraMap k Ω c)

attribute [local instance] CurvesJacobian.isFunctionField_F

omit [IsSepClosed Ω] in
include hk in
/-- **The data of a point under a given place `W₀` of `Ω`** (curves-jacobian `pointData`, with
`W₀` prescribed): for a place `W₀` of `Ω` over a place `P` of `F` there are the point `x` of `X`
under `W₀`, `U = X ∖ {x}` and a uniformiser `π`, as `syncEquiv` requires. -/
theorem pointData_of_liesOver (P : Place k (F D)) (W₀ : ValuationSubring Ω)
    (hW₀P : ∀ y : F D, ((y : F D) : Ω) ∈ W₀ ↔ y ∈ P.1) {R : Prop}
    (hR : ∀ (x : X) (U : X.Opens) [Nonempty U] (π : (F D)ˣ),
      (U : Set X)ᶜ = {x} → IsCentredOn D X eL ⊤ W₀ → ¬ IsCentredOn D X eL U W₀ →
      W₀.valuation ((π : F D) : Ω) < 1 →
      (∀ f ∈ F D, W₀.valuation f < 1 → W₀.valuation f ≤ W₀.valuation ((π : F D) : Ω)) → R) :
    R := by
  have hkW₀ : ∀ c : k, algebraMap k Ω c ∈ W₀ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (F D) Ω]
    exact (hW₀P _).2 (P.algebraMap_mem c)
  haveI := CurvesJacobian.isSeparated_of_over k X
  have hkO : ∀ c : k, algebraMap k X.functionField c ∈ CurvesJacobian.comapK D X eL hk W₀ :=
      fun c ↦ by
    change ((eL (algebraMap k X.functionField c) : D.L) : Ω) ∈ W₀
    rw [hk]
    exact hkW₀ c
  obtain ⟨y, hy⟩ :
      ∃ y : X, CurvesJacobian.stalkVS k y = CurvesJacobian.comapK D X eL hk W₀ := by
    refine ⟨(CurvesJacobian.pointEquivValuationSubringOver k
      (valuationRing_stalk_of_isCurveOver k X)).symm ⟨_, hkO⟩, ?_⟩
    have := congrArg Subtype.val ((CurvesJacobian.pointEquivValuationSubringOver k
      (valuationRing_stalk_of_isCurveOver k X)).apply_symm_apply ⟨_, hkO⟩)
    rw [CurvesJacobian.pointEquivValuationSubringOver_apply] at this
    exact this
  have hyη : y ≠ genericPoint X := by
    intro hyη
    apply P.ne_top
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h1 : eL.symm ⟨_, mem_L_of_mem_F z⟩ ∈ CurvesJacobian.comapK D X eL hk W₀ := by
      have htop : CurvesJacobian.stalkVS k (genericPoint X) = ⊤ :=
        CurvesJacobian.stalkValuationSubring_genericPoint _
      rw [← hy, hyη, htop]
      trivial
    have h2 : ((z : F D) : Ω) ∈ W₀ := by
      change ((eL (eL.symm ⟨_, mem_L_of_mem_F z⟩) : D.L) : Ω) ∈ W₀ at h1
      simpa using h1
    exact (hW₀P z).1 h2
  let U : X.Opens := ⟨{y}ᶜ, (CurvesJacobian.isClosed_closedPoint k X ⟨y, hyη⟩).isOpen_compl⟩
  have hUx : (U : Set X)ᶜ = {y} := compl_compl _
  haveI : Nonempty U := ⟨⟨genericPoint X, fun h ↦ hyη h.symm⟩⟩
  have hUfin : (U : Set X)ᶜ.Finite := hUx ▸ Set.finite_singleton y
  have hW₀ : IsCentredOn D X eL ⊤ W₀ := isCentredOn_top_of hk hkW₀
  have hW₀U : ¬ IsCentredOn D X eL U W₀ := fun h ↦
    (mem_of_isCentredOn D X eL hk U hUfin h hy) rfl
  obtain ⟨π, -, hπW, hπ⟩ := exists_uniformiser hW₀P
  exact hR y U π hUx hW₀ hW₀U hπW hπ

end PointData

/-! ### `M_X` with reindexed Kummer indices -/

section Reindex

open CurvesJacobian.TopClass

variable {G : Type*} [Group G] [TopologicalSpace G] (K K' : Type*) [Field K] [Field K']
  [CharZero K] [CharZero K']

/-- **`M_X = lim_n M_X/n` does not depend on the field indexing the levels** (characteristic
`0`: all `n ≥ 1`). -/
noncomputable def mxReindex : MXHat G K ≃* MXHat G K' where
  toFun φ := ⟨fun i ↦ (φ : ∀ i : KummerIndex K, MXmod G i.n)
    ⟨i.n, Nat.cast_ne_zero.2 i.n_ne_zero⟩, fun _ _ h ↦ φ.2 _ _ h⟩
  invFun φ := ⟨fun i ↦ (φ : ∀ i : KummerIndex K', MXmod G i.n)
    ⟨i.n, Nat.cast_ne_zero.2 i.n_ne_zero⟩, fun _ _ h ↦ φ.2 _ _ h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {K K'}

@[simp]
lemma proj_mxReindex (φ : MXHat G K) (i : KummerIndex K') :
    MXHat.proj i (mxReindex K K' φ) = MXHat.proj ⟨i.n, Nat.cast_ne_zero.2 i.n_ne_zero⟩ φ := rfl

end Reindex

/-! ### Thm 1.9 (b): the tame generator is the synchronization of the inertia generator -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian CurvesJacobian.Cusp
  CurvesJacobian.TopClass CurvesJacobian.CuspCentral

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

variable {k hτ}

attribute [local instance] CurvesJacobian.isFunctionField_F

set_option maxHeartbeats 800000 in
-- unfolding `syncEquivBar` to `natIsoHatBar` is slow
/-- **[AbsTopIII] Thm 1.9 (b) at a cusp**: for an inertia index `p = (W, σ)` of `U` over a
`k`-rational point `x` (`W ∩ F = x`), and any choice of the data of the synchronization
`I_{x} ≅ M_X` of [AbsTopIII] Prop 1.4 (ii) for `X_{k̄}` at `W` (curves-jacobian `syncEquivBar`:
`U_x = X_{k̄} ∖ {x}`, `W` centred on `x`, a uniformiser `π` of `W ∩ F k̄`), the
synchronization of the image of `σ` in `I_x ⊆ Δ_{U_x}` is the tame generator `θ_p` read in `M_X`
through the natural `M_X ≅ Ẑ(1)` of the `Π_U`-module `M_X` (`natIsoHatK`, which defines
`h1MXEquiv`). -/
theorem syncEquivBar_inertiaToCusp (hg : 0 < (curveGenus k X).toNat)
    (p : InertiaIndex (curveGaloisData k hτ)) (x : RatPoint (curveGaloisData k hτ))
    (hpx : ∀ y : F (curveGaloisData k hτ), (y : FFClosure X) ∈ p.1.1 ↔ (y : FFClosure X) ∈ x.A)
    {U : (baseChangeKbar k X).Opens} [Nonempty U] {x' : baseChangeKbar k X}
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x'})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U p.1.1)
    {π : (F (barData k hτ))ˣ}
    (hπW : p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X)) :
    mxReindex _ _ (syncEquivBar hg hUx hW₀ hW₀U hπW hπ
        (inertiaToCusp (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) U p.1.1
          (inertiaBar p))) =
      MX.equiv hτ _ ((natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm (tameGen p)) := by
  have h1 : syncEquivBar hg hUx hW₀ hW₀U hπW hπ (inertiaToCusp (barData k hτ) (barEquivL k hτ)
      (barData_H_le k hτ) U p.1.1 (inertiaBar p)) =
      (natIsoHatBar hτ hg).symm (tameChar (kbar_mem_idx p) π (inertiaBar p)) := by
    rw [← cuspInertiaZHatEquiv_inertiaToCusp (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
      (genus_bar_pos hg) U hUx hW₀ hW₀U hπW hπ]
    rfl
  apply Subtype.ext
  funext i
  rw [h1]
  exact congrArg (natIsoBar hτ i.n hg).symm (proj_tameChar_inertiaBar p x hpx hπW hπ i.n)

/-- **The data of the synchronization exist at every cusp**: for `p = (W, σ)` over a rational
point `x`, there are `U_x = X_{k̄} ∖ {x}` and a uniformiser at `W`, so that
`syncEquivBar_inertiaToCusp` applies. -/
theorem exists_syncData (p : InertiaIndex (curveGaloisData k hτ))
    (x : RatPoint (curveGaloisData k hτ))
    (hpx : ∀ y : F (curveGaloisData k hτ), (y : FFClosure X) ∈ p.1.1 ↔ (y : FFClosure X) ∈ x.A)
    {R : Prop}
    (hR : ∀ (x' : baseChangeKbar k X) (U : (baseChangeKbar k X).Opens) [Nonempty U]
      (π : (F (barData k hτ))ˣ), (U : Set (baseChangeKbar k X))ᶜ = {x'} →
      IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1 →
      ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U p.1.1 →
      p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1 →
      (∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
        p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X)) → R) : R :=
  pointData_of_liesOver (barEquivL_algebraMap k hτ) (idxPlaceBar p x hpx) p.1.1
    (fun _ ↦ Iff.rfl) hR

/-! ### Thm 1.9 (c) with coefficients in `M_X = μ_Ẑ(Π_U)` -/

variable [Fact (0 < (curveGenus k X).toNat)]

/-- Inertia acts trivially on `M_X`. -/
lemma pi_inertia_smul_mx (p : InertiaIndex (curveGaloisData k hτ))
    (φ : MX hτ (F (curveGaloisData k hτ))) :
    ((p.1.2 : (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) • φ = φ :=
  (natIsoHatK hτ _ Fact.out).injective (by
    rw [natIsoHatK_pi_smul]
    exact pi_inertia_smul_zHatOne p.2.1 p.2.2 _ _)

variable (k hτ) in
/-- **The residues with coefficients in `M_X`**: `η ↦ (η(σ))_{p = (W, σ)}`, restriction to the
inertia groups (the second map of [AbsTopIII] Prop 1.6 (iii) for `H¹(Π_U, M_X)`). -/
noncomputable def resMX :
    ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ))) →*
      (InertiaIndex (curveGaloisData k hτ) → MX hτ (F (curveGaloisData k hτ))) :=
  MonoidHom.pi fun p ↦ ContH1.evalTriv ((p.1.2 : (curveGaloisData k hτ).H) :
    Pi (curveGaloisData k hτ)) (pi_inertia_smul_mx p)

/-- The residues of `h1MXEquiv η` are those of `η`, read in `M_X`. -/
lemma resMX_h1MXEquiv
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (p : InertiaIndex (curveGaloisData k hτ)) :
    resMX k hτ (h1MXEquiv hτ _ η) p =
      (natIsoHatK hτ _ Fact.out).symm (Kummer.res (curveGaloisData k hτ) η p) := by
  induction η using ContH1.induction_on with
  | h c => rfl

/-- **The tame generator in `M_X`**: `θ_p` under `Ẑ(1) ≅ M_X`. By
`syncEquivBar_inertiaToCusp` it is the synchronization of the inertia generator. -/
noncomputable def tameGenMX (p : InertiaIndex (curveGaloisData k hτ)) :
    MX hτ (F (curveGaloisData k hτ)) :=
  (natIsoHatK hτ _ Fact.out).symm (tameGen p)

/-- **The residues of `η ∈ H¹(Π_U, M_X)` are those of the divisor `E`**. -/
def HasResiduesMX (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ))))
    (E : Divisor k (F (curveGaloisData k hτ))) : Prop :=
  ∀ p : InertiaIndex (curveGaloisData k hτ), resMX k hτ η p = tameGenMX p ^ divAt E p

lemma hasResiduesMX_h1MXEquiv
    (η : ContH1 (Pi (curveGaloisData k hτ)) (ZHatOne (F (curveGaloisData k hτ)) (FFClosure X)))
    (E : Divisor k (F (curveGaloisData k hτ))) :
    HasResiduesMX (h1MXEquiv hτ _ η) E ↔ HasResidues η E := by
  refine forall_congr' fun p ↦ ?_
  rw [resMX_h1MXEquiv, tameGenMX, ← map_zpow]
  exact (natIsoHatK hτ _ Fact.out).symm.injective.eq_iff

variable (k hτ) in
/-- **`P_U ⊆ H¹(Π_U, M_X)`**: the image of `P_U` under `h1MXEquiv`. -/
noncomputable def PUMX :
    Subgroup (ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))) :=
  (PU (curveGaloisData k hτ)).map (h1MXEquiv hτ (F (curveGaloisData k hτ))).toMonoidHom

lemma mem_PUMX_iff
    (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))) :
    η ∈ PUMX k hτ ↔ (h1MXEquiv hτ (F (curveGaloisData k hτ))).symm η ∈ PU (curveGaloisData k hτ) :=
  Subgroup.mem_map_equiv

/-- Kummer classes of units lie in `P_U`. -/
lemma kummerMapMX_mem_PUMX (u : units (curveGaloisData k hτ)) : kummerMapMX k hτ u ∈ PUMX k hτ :=
  Subgroup.mem_map_of_mem _ ⟨u, rfl⟩

/-- **Residues of Kummer classes are divisors**, with `M_X`-coefficients. -/
theorem res_kummerMapMX (u : units (curveGaloisData k hτ))
    (p : InertiaIndex (curveGaloisData k hτ)) :
    resMX k hτ (kummerMapMX k hτ u) p =
      tameGenMX p ^ divAt (Divisor.div k ((u : (F (curveGaloisData k hτ))ˣ) :
        F (curveGaloisData k hτ))) p := by
  change resMX k hτ (h1MXEquiv hτ _ (kummerMapZHat (curveGaloisData k hτ) u)) p = _
  rw [resMX_h1MXEquiv, res_kummerMapZHat, tameGenMX, map_zpow]

set_option maxHeartbeats 800000 in
-- unfolding `syncEquivBar` is slow
/-- **The residues at a cusp, in the form of [AbsTopIII] Thm 1.9 (c)**: if `η` has the residues
of `E`, then at an inertia index `p = (W, σ)` over a rational point `x`, `η(σ)` is the
`E(x)`-th power of the synchronization `I_x ≅ M_X` (Prop 1.4 (ii)) of the inertia generator. -/
theorem resMX_eq_sync_zpow
    {η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))}
    {E : Divisor k (F (curveGaloisData k hτ))} (hη : HasResiduesMX η E)
    (p : InertiaIndex (curveGaloisData k hτ)) (x : RatPoint (curveGaloisData k hτ))
    (hpx : ∀ y : F (curveGaloisData k hτ), (y : FFClosure X) ∈ p.1.1 ↔ (y : FFClosure X) ∈ x.A)
    {U : (baseChangeKbar k X).Opens} [Nonempty U] {x' : baseChangeKbar k X}
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x'})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U p.1.1)
    {π : (F (barData k hτ))ˣ}
    (hπW : p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X)) :
    MX.equiv hτ _ (resMX k hτ η p) =
      mxReindex _ _ (syncEquivBar Fact.out hUx hW₀ hW₀U hπW hπ
        (inertiaToCusp (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) U p.1.1
          (inertiaBar p))) ^ E (placeOfF x) := by
  rw [syncEquivBar_inertiaToCusp Fact.out p x hpx hUx hW₀ hW₀U hπW hπ, hη p, map_zpow]
  congr 1
  rw [divAt, dif_pos (idxVal_ne_top p x hpx), idxPlace_eq p x hpx]

section Global

open CategoryTheory AlgebraicGeometry

/-- **[AbsTopIII] Thm 1.9 (c) with coefficients in `M_X`, over a number field**: for a curve with
`X(k) ≠ ∅` and rational cusps, `η ∈ H¹(Π_U, M_X)` lies in `P_U` iff its residues are those of a
divisor `f` on the cusps with `deg f = 0` and `η_f = 1`. -/
theorem mem_PUMX_iff_eta_curve_numberField [NumberField k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hrat : ∀ P : Place k (F (curveGaloisData k hτ)), IsCuspPlaceF P →
      ∃ x : RatPoint (curveGaloisData k hτ), placeOfF x = P)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    η ∈ PUMX k hτ ↔ ∃ f : RatPoint (curveGaloisData k hτ) →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResiduesMX η (ratDivF f) := by
  rw [mem_PUMX_iff, mem_PU_iff_eta_curve_numberField σ hσ hrat]
  simp_rw [← hasResiduesMX_h1MXEquiv, MulEquiv.apply_symm_apply]

/-- **[AbsTopIII] Thm 1.9 (c) with coefficients in `M_X`, over a finite extension of `ℚ_p`**. -/
theorem mem_PUMX_iff_eta_curve_padic (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k]
    [FiniteDimensional ℚ_[p] k] (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (hrat : ∀ P : Place k (F (curveGaloisData k hτ)), IsCuspPlaceF P →
      ∃ x : RatPoint (curveGaloisData k hτ), placeOfF x = P)
    (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))) :
    letI : Fact (Function.Surjective (piJ1ToGk (curveGaloisData k hτ))) :=
      fact_piJ1ToGk_surjective _ (mem_range_of_isAlgebraic_F k hτ)
    η ∈ PUMX k hτ ↔ ∃ f : RatPoint (curveGaloisData k hτ) →₀ ℤ,
      (∀ x ∈ f.support, IsCuspPlaceF (placeOfF x)) ∧ (f.sum fun _ m => m) = 0 ∧ eta f = 1 ∧
        HasResiduesMX η (ratDivF f) := by
  rw [mem_PUMX_iff, mem_PU_iff_eta_curve_padic p σ hσ hrat]
  simp_rw [← hasResiduesMX_h1MXEquiv, MulEquiv.apply_symm_apply]

end Global

/-! ### The tests of Prop 1.8 with coefficients in `M_X` -/

section NFTest

open CategoryTheory AlgebraicGeometry IsLocalRing

variable [CharZero (FFClosure X)]

/-- **The restriction `η|_x = s_x^*(η)` for `η ∈ H¹(Π_U, M_X)`**: `restrictClosed` after
`M_X ≅ Ẑ(1)` (`h1MXEquiv`). -/
noncomputable def restrictClosedMX [IsAlgClosed (FFClosure X)]
    (A : ValuationSubring (FFClosure X))
    (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A) [Algebra k (ResidueField A)]
    (hkres : ∀ c : k, residue A ⟨algebraMap k (FFClosure X) c, hkA c⟩ =
      algebraMap k (ResidueField A) c)
    [Algebra.IsIntegral k (ResidueField A)] (ht : coordT τ ∈ A) :
    ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ))) →*
      ContH1 (ResidueField A ≃ₐ[Decomposition.pointField (F (curveGaloisData k hτ)) A hkA hkres]
          ResidueField A)
        (ZHatOne (Decomposition.pointField (F (curveGaloisData k hτ)) A hkA hkres)
          (ResidueField A)) :=
  (restrictClosed (curveGaloisData k hτ) A hkA hkres rfl ht).comp
    (h1MXEquiv hτ (F (curveGaloisData k hτ))).symm.toMonoidHom

/-- **The test of [AbsTopIII] Prop 1.8 (i) for `η ∈ H¹(Π_U, M_X)`** (read through
`M_X ≅ Ẑ(1)`). -/
def IsNFKummerTestMX [IsAlgClosed (FFClosure X)] (N : NFModel (curveGaloisData k hτ))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ)))) : Prop :=
  IsNFKummerTest N rfl ((h1MXEquiv hτ (F (curveGaloisData k hτ))).symm η)

set_option maxHeartbeats 800000 in
-- the `IsNFKummerTest` statement elaborates slowly
/-- **[AbsTopIII] Prop 1.8 (i) with coefficients in `M_X`, over a number field**: `η ∈ P_U`
passes the test of (i) iff some positive multiple of `η` is the Kummer class `κ_U(w) ∈
H¹(Π_U, M_X)` of a nonconstant NF-rational unit `w` of `U`. -/
theorem isNFKummerTestMX_iff_curve_numberField [IsAlgClosed (FFClosure X)] [NumberField k]
    (N : NFModel (curveGaloisData k hτ)) (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (η : ContH1 (Pi (curveGaloisData k hτ)) (MX hτ (F (curveGaloisData k hτ))))
    (hη : η ∈ PUMX k hτ) :
    IsNFKummerTestMX N η ↔
      ∃ M : ℕ, 0 < M ∧ ∃ w : units (curveGaloisData k hτ),
        η ^ M = kummerMapMX k hτ w ∧
        w ∉ Set.range (constUnit (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((w : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) := by
  rw [IsNFKummerTestMX, isNFKummerTest_iff_curve_numberField N σ hσ _ ((mem_PUMX_iff η).1 hη)]
  refine exists_congr fun M => and_congr Iff.rfl (exists_congr fun w => and_congr ?_ Iff.rfl)
  rw [← map_pow, MulEquiv.symm_apply_eq]
  rfl

set_option maxHeartbeats 1600000 in
-- unification of `ContH1` terms over `Gal(κ(A)/k_x)` is slow
set_option synthInstance.maxHeartbeats 100000 in
-- the action of `Gal(κ(A)/k_x)` on `Ẑ(1)_{k_x}` is found slowly
/-- **[AbsTopIII] Prop 1.8 (ii) with coefficients in `M_X`**: if `U` has a nonconstant
NF-rational unit, the class of `c ∈ (k^×)^∧` in `H¹(Π_U, M_X)` is the Kummer class of an
`IsNFConstant` element of `kˣ` iff `κ_U(f)|_x = c|_x` for a nonconstant NF-rational unit `f` and
an NF-point `x`. -/
theorem exists_restrictClosedMX_eq_iff_curve [IsAlgClosed (FFClosure X)]
    (N : NFModel (curveGaloisData k hτ))
    (htf : IsTorallyKummerFaithful k) (f₀ : units (curveGaloisData k hτ))
    (hf₀ : Transcendental k ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (hNF₀ : N.IsNFFunction ((f₀ : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)))
    (c : KummerCompletion k) :
    (∃ b : kˣ, IsNFConstant (FFClosure X) (b : k) ∧ c = toKummerCompletion k b) ↔
      ∃ f : units (curveGaloisData k hτ),
        Transcendental k ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
        N.IsNFFunction ((f : (F (curveGaloisData k hτ))ˣ) : F (curveGaloisData k hτ)) ∧
        ∃ (A : ValuationSubring (FFClosure X)) (hkA : ∀ c : k, algebraMap k (FFClosure X) c ∈ A)
          (ht : coordT τ ∈ A),
          N.IsNFPoint A ∧
          letI := Decomposition.residueAlgebra A hkA
          ∃ (_ : Algebra.IsIntegral k (ResidueField A))
            (_ : FiniteDimensional k (Decomposition.pointField (F (curveGaloisData k hτ)) A hkA
              (Decomposition.residue_algebraMap_residueAlgebra A hkA))),
            restrictClosedMX A hkA (Decomposition.residue_algebraMap_residueAlgebra A hkA) ht
                (kummerMapMX k hτ f) =
              restrictClosedMX A hkA (Decomposition.residue_algebraMap_residueAlgebra A hkA) ht
                (h1MXEquiv hτ _ (constMapZHat (curveGaloisData k hτ) c)) := by
  rw [exists_restrictClosed_eq_iff_curve N htf f₀ hf₀ hNF₀ c]
  simp only [restrictClosedMX, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, kummerMapMX,
    MulEquiv.symm_apply_apply]

end NFTest

end Curve

end Iut.Reconstruction.Thm19
