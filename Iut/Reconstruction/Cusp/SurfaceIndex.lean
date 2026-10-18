/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Cusp.SurfaceH2
import LocalClassFieldTheory.Brauer.Corestriction

/-!
# Index normalisation of `M_X ≅ I_x` under open subgroups ([AbsTopIII], Remark 1.10.1(i))

[AbsTopIII], Remark 1.10.1(i) (l.2545–2551 of
`~/iut-scratch/papers/txt/Topics in Absolute Anabelian Geometry III.txt`):

> "In general, the functoriality of Theorem 1.9, Corollary 1.10, when applied to the operation of
> passing to open subgroups of `Π_X`, is to be understood in the sense of a "compatibility",
> relative to dividing the usual functorially induced morphism on "`μ_Ẑ(Π_X)`'s" by a factor
> given by the index of the subgroups of `Δ_X` that arise from the open subgroups of `Π_X` under
> consideration [cf., e.g., [Mzk19], Remark 1]."

Here `μ_Ẑ(Π_X) = M_X = Hom(H²(Δ_X, Ẑ), Ẑ)` (Prop 1.4(ii)), in the levelwise form `MX` of
`SurfaceH2.lean`.

## General part (any topological group `P`, open `H ≤ P` of finite index `d`)

* `MXg P`: compatible families `H²(P, ℤ/n) → ℤ/n` (`MX g = MXg (SurfGrp g)` by definition,
  `MX_eq`);
* `resM H : M_H → M_P`, the usual functorially induced morphism (dual of restriction);
* if corestriction `cor : H²(H, ℤ/n) → H²(P, ℤ/n)` is bijective for all `n`, `normM` (dual of
  `cor⁻¹`) is an isomorphism `M_H ≃* M_P` with **`resM f = (normM f)^d`** (`resM_eq_normM_pow`,
  from LCFT `cor_res`), and it is **the unique** homomorphism with this property as soon as `M_P`
  has no `d`-torsion (`normM_unique`): `normM` is "`resM` divided by the index".

## The model `Δ_X = Π̂_{g,0}`

Let `H ≤ Π̂_{g,0}` be open of index `d`, the geometric fundamental group of a finite étale cover
`Y → X` of degree `d`. The two inputs about the cover are taken as explicit arguments (they are
the profinite Schreier/Riemann–Hurwitz theorem for surface groups, not available in iut: `pi1`'s
discrete Schreier results are not in the `pi1` revision iut pins, and their profinite completion is
not formalised):

* `φ : H ≃ₜ* Π̂_{g',0}` (geometrically `g' = 1 + d(g − 1)`, which is not used below);
* `hres`: the restriction to `H` of the cusp class of `X` (the transgression of `1 ∈ Hom(I_x, I_x)`,
  `gen`) is `d` times the cusp class of `Y` at a point `y` over `x` — the degree of the pull-back
  of the divisor `x` is `d`. Here the canonical generators `r̄` of `I_y` and `I_x` (the cusp
  loops) correspond under the isomorphism `I_y ≅ I_x` of the unramified cover.

From these: `cor_gen` (the cusp class of `Y` corestricts to that of `X`, by passing to level
`d·n`), `cor_bijective`, and **`normM_syncEquiv`**: the index-normalised map `M_Y → M_X` carries
`syncEquiv_Y(i_y)` to `syncEquiv_X(i_x)` for corresponding `i_y ↔ i_x` (both `= a ∈ Ẑ` under
`inertiaEquiv`), while the usual induced morphism carries it to `syncEquiv_X(i_x)^d`
(`resM_syncEquiv`). `hres_top` checks the input for `H = ⊤`.
-/

namespace Iut.Reconstruction.SurfaceH2

open ContH2 Brauer

set_option linter.unusedSectionVars false

/-! ### Divisibility in `ℤ/n` and `Ẑ` -/

lemma castHom_eq_zero_of_nsmul_eq_zero {d n m : ℕ} (hd : 0 < d) [NeZero n] (hm : m = d * n)
    (h : n ∣ m) (x : ZMod m) (hx : d • x = 0) : ZMod.castHom h (ZMod n) x = 0 := by
  subst hm
  haveI : NeZero (d * n) := ⟨Nat.mul_ne_zero hd.ne' (NeZero.ne n)⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_left hd hx

/-- `Ẑ` is torsion-free. -/
lemma zhat_eq_zero_of_nsmul {d : ℕ} (hd : 0 < d) {a : ZHat} (ha : d • a = 0) : a = 0 := by
  refine ZHat.ext fun n => ?_
  let N : ℕ+ := ⟨d * n, Nat.mul_pos hd n.pos⟩
  have h := ZHat.castHom_apply a (n := n) (m := N) (Dvd.intro_left d rfl)
  rw [← h]
  have h' := congrArg (fun x : ZHat => (x : ∀ n : ℕ+, ZMod n) N) ha
  simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, AddSubgroup.coe_zero, Pi.zero_apply] at h'
  exact castHom_eq_zero_of_nsmul_eq_zero (n := n) hd rfl _ _ h'

/-! ### `M_P` for any topological group `P` -/

section General

variable (P : Type*) [Group P] [TopologicalSpace P]

/-- `H²(P, ℤ/m) → H²(P, ℤ/n)` for `n ∣ m`. -/
noncomputable def h2RedG {n m : ℕ} (h : n ∣ m) : ContH2 P (Zn m) →* ContH2 P (Zn n) :=
  ContH2.map (MonoidHom.id _) continuous_id (redZn h : Zn m →* Zn n) fun _ _ => rfl

/-- **`M_P = Hom((H²(P, ℤ/n))_n, (ℤ/n)_n)`**, compatible families of homomorphisms. -/
def MXg : Subgroup (∀ n : ℕ+, ContH2 P (Zn n) →* Zn n) where
  carrier := {f | ∀ (n m : ℕ+) (h : (n : ℕ) ∣ m) (z : ContH2 P (Zn m)),
    f n (h2RedG P h z) = redZn h (f m z)}
  mul_mem' hf hf' n m h z := by simp [hf n m h z, hf' n m h z]
  one_mem' n m h z := by simp
  inv_mem' hf n m h z := by simp [hf n m h z]

lemma MX_eq (g : ℕ) : MX g = MXg (SurfGrp g) := rfl

variable {P} (H : Subgroup P)

/-- Restriction `H²(P, ℤ/n) → H²(H, ℤ/n)`. -/
noncomputable def resH (n : ℕ) : ContH2 P (Zn n) →* ContH2 H (Zn n) :=
  ContH2.map H.subtype continuous_subtype_val (MonoidHom.id _) fun _ _ => rfl

lemma resH_h2RedG {n m : ℕ} (h : n ∣ m) (z : ContH2 P (Zn m)) :
    resH H n (h2RedG P h z) = h2RedG H h (resH H m z) := by
  induction z using ContH2.induction_on with
  | h c => rfl

/-- **The usual functorially induced morphism** `M_H → M_P` (the dual of restriction). -/
noncomputable def resM : MXg H →* MXg P where
  toFun f := ⟨fun n => (f.1 n).comp (resH H n), fun n m h z => by
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [resH_h2RedG, f.2 n m h]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma resM_apply (f : MXg H) (n : ℕ+) (z : ContH2 P (Zn n)) :
    (resM H f).1 n z = f.1 n (resH H n z) := rfl

variable [IsTopologicalGroup P] [Fintype (P ⧸ H)] (hH : IsOpen (H : Set P))

/-- Corestriction `H²(H, ℤ/n) → H²(P, ℤ/n)` (LCFT). -/
noncomputable def corH (n : ℕ) : ContH2 H (Zn n) →* ContH2 P (Zn n) := ContH2.cor H hH

lemma corH_h2RedG {n m : ℕ} (h : n ∣ m) (z : ContH2 H (Zn m)) :
    corH H hH n (h2RedG H h z) = h2RedG P h (corH H hH m z) := by
  induction z using ContH2.induction_on with
  | h c =>
    change ContH2.cor H hH (ContH2.map _ _ _ _ (mk c)) =
      ContH2.map _ _ _ _ (ContH2.cor H hH (mk c))
    rw [map_mk, cor_mk, cor_mk, map_mk]
    congr 1
    refine cocycles_ext fun a b => ?_
    simp only [corCocycles, MonoidHom.coe_mk, OneHom.coe_mk, coe_mkCocycle, corFun_apply,
      cocyclesMap_apply, MonoidHom.id_apply, map_prod]
    rfl

/-- **`cor ∘ res = d`** on `H²(P, ℤ/n)`. -/
lemma corH_resH (n : ℕ) (z : ContH2 P (Zn n)) :
    corH H hH n (resH H n z) = z ^ Fintype.card (P ⧸ H) :=
  ContH2.cor_res H hH z

variable (hcor : ∀ n : ℕ+, Function.Bijective (corH H hH n))

/-- `cor` as an isomorphism. -/
noncomputable def corEquiv (n : ℕ+) : ContH2 H (Zn n) ≃* ContH2 P (Zn n) :=
  MulEquiv.ofBijective (corH H hH n) (hcor n)

lemma corEquiv_symm_h2RedG (n m : ℕ+) (h : (n : ℕ) ∣ m) (z : ContH2 P (Zn m)) :
    (corEquiv H hH hcor n).symm (h2RedG P h z) =
      h2RedG H h ((corEquiv H hH hcor m).symm z) := by
  apply (corEquiv H hH hcor n).injective
  rw [MulEquiv.apply_symm_apply]
  change _ = corH H hH n _
  rw [corH_h2RedG]
  change _ = h2RedG P h ((corEquiv H hH hcor m) ((corEquiv H hH hcor m).symm z))
  rw [MulEquiv.apply_symm_apply]

/-- **The index-normalised morphism** `M_H ≃* M_P`, the dual of `cor⁻¹`. -/
noncomputable def normM : MXg H ≃* MXg P where
  toFun f := ⟨fun n => (f.1 n).comp (corEquiv H hH hcor n).symm.toMonoidHom, fun n m h z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [corEquiv_symm_h2RedG, f.2 n m h]⟩
  invFun f := ⟨fun n => (f.1 n).comp (corH H hH n), fun n m h z => by
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [corH_h2RedG, f.2 n m h]⟩
  left_inv f := Subtype.ext (funext fun n => MonoidHom.ext fun z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    exact congrArg (f.1 n) ((corEquiv H hH hcor n).symm_apply_apply z))
  right_inv f := Subtype.ext (funext fun n => MonoidHom.ext fun z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    exact congrArg (f.1 n) ((corEquiv H hH hcor n).apply_symm_apply z))
  map_mul' _ _ := rfl

lemma normM_apply (f : MXg H) (n : ℕ+) (z : ContH2 P (Zn n)) :
    (normM H hH hcor f).1 n z = f.1 n ((corEquiv H hH hcor n).symm z) := rfl

/-- **Remark 1.10.1(i), the compatibility**: the usual functorially induced morphism is the
index-normalised one multiplied by the index, `resM f = (normM f)^d`. -/
theorem resM_eq_normM_pow (f : MXg H) :
    resM H f = normM H hH hcor f ^ Fintype.card (P ⧸ H) := by
  refine Subtype.ext (funext fun n => MonoidHom.ext fun z => ?_)
  change f.1 n (resH H n z) = ((normM H hH hcor f).1 ^ Fintype.card (P ⧸ H)) n z
  rw [Pi.pow_apply, MonoidHom.pow_apply, normM_apply, ← map_pow, ← map_pow]
  congr 1
  apply (corEquiv H hH hcor n).injective
  rw [MulEquiv.apply_symm_apply]
  exact corH_resH H hH n z

/-- **Uniqueness of the normalisation**: if `M_P` has no `d`-torsion, `normM` is the only
homomorphism `ψ` with `ψ(f)^d = resM f`, i.e. "`resM` divided by the index". -/
theorem normM_unique
    (htf : ∀ x : MXg P, x ^ Fintype.card (P ⧸ H) = 1 → x = 1) (ψ : MXg H →* MXg P)
    (hψ : ∀ f, ψ f ^ Fintype.card (P ⧸ H) = resM H f) (f : MXg H) :
    ψ f = normM H hH hcor f := by
  have := htf (ψ f / normM H hH hcor f) (by
    rw [div_pow, hψ, resM_eq_normM_pow H hH hcor, div_self'])
  exact div_eq_one.mp this

end General

/-! ### The model: open subgroups of `Π̂_{g,0}` -/

section Model

variable {g : ℕ} (i₀ : Fin g)

include i₀ in
/-- `M_X` (`g ≥ 1`) is torsion-free: `M_X ≅ I ≅ Ẑ`. -/
lemma MX_torsionFree {d : ℕ} (hd : 0 < d) (x : MXg (SurfGrp g)) (hx : x ^ d = 1) : x = 1 := by
  obtain ⟨i, rfl⟩ := (syncEquiv i₀).surjective x
  obtain ⟨a, rfl⟩ := (inertiaEquiv i₀).surjective i
  have h1 : (inertiaEquiv i₀ a) ^ d = 1 :=
    (syncEquiv i₀).injective (by rw [map_pow, map_one]; exact hx)
  have h2 : a ^ d = 1 := (inertiaEquiv i₀).injective (by rw [map_pow, map_one]; exact h1)
  have h3 : Multiplicative.toAdd a = 0 :=
    zhat_eq_zero_of_nsmul hd (by simpa [toAdd_pow] using congrArg Multiplicative.toAdd h2)
  have h4 : a = 1 := Multiplicative.toAdd.injective h3
  rw [h4, map_one, map_one]
  rfl

lemma inertiaEquiv_apply (a : Multiplicative ZHat) :
    inertiaEquiv i₀ a = zhatPow (relBar g) a := rfl

variable {H : Subgroup (SurfGrp g)} (hH : IsOpen (H : Set (SurfGrp g)))
  {g' : ℕ} (i₀' : Fin g') (φ : H ≃ₜ* SurfGrp g')

/-- Transport `H²(Π̂_{g',0}, ℤ/n) ≃* H²(H, ℤ/n)` along `φ`. -/
noncomputable def phiH2 (n : ℕ) : ContH2 (SurfGrp g') (Zn n) ≃* ContH2 H (Zn n) :=
  ContH2.mapEquiv φ.toMulEquiv φ.continuous φ.symm.continuous fun _ _ => rfl

lemma phiH2_h2Red {n m : ℕ} (h : n ∣ m) (z : ContH2 (SurfGrp g') (Zn m)) :
    phiH2 φ n (h2Red g' h z) = h2RedG H h (phiH2 φ m z) := by
  induction z using ContH2.induction_on with
  | h c => rfl

/-- `M_Y ≃* M_H` along `φ`. -/
noncomputable def transM : MX g' ≃* MXg H where
  toFun f := ⟨fun n => (f.1 n).comp (phiH2 φ n).symm.toMonoidHom, fun n m h z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    obtain ⟨w, rfl⟩ := (phiH2 φ m).surjective z
    rw [← phiH2_h2Red, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, f.2 n m h]⟩
  invFun f := ⟨fun n => (f.1 n).comp (phiH2 φ n).toMonoidHom, fun n m h z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [phiH2_h2Red, f.2 n m h]⟩
  left_inv f := Subtype.ext (funext fun n => MonoidHom.ext fun z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    exact congrArg (f.1 n) ((phiH2 φ n).symm_apply_apply z))
  right_inv f := Subtype.ext (funext fun n => MonoidHom.ext fun z => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    exact congrArg (f.1 n) ((phiH2 φ n).apply_symm_apply z))
  map_mul' _ _ := rfl

lemma transM_apply (f : MX g') (n : ℕ+) (z : ContH2 H (Zn n)) :
    (transM φ f).1 n z = f.1 n ((phiH2 φ n).symm z) := rfl

variable [Fintype (SurfGrp g ⧸ H)]

/-- The Riemann–Hurwitz input: the restriction of the cusp class of `X` is `d` times the cusp
class of the cover at a point over the cusp. -/
def ResCuspInput : Prop :=
  ∀ n : ℕ+, resH H n (gen i₀ n) = phiH2 φ n (gen i₀' n) ^ Fintype.card (SurfGrp g ⧸ H)

include i₀ in
lemma h2Red_eq_one_of_pow {n N : ℕ+} {d : ℕ} (hd : 0 < d) (hN : (N : ℕ) = d * n)
    (h : (n : ℕ) ∣ N) (w : ContH2 (SurfGrp g) (Zn N)) (hw : w ^ d = 1) : h2Red g h w = 1 := by
  apply (h2SurfEquiv n i₀).injective
  rw [h2SurfEquiv_h2Red, map_one]
  obtain ⟨t, ht⟩ : ∃ t : ZMod N, h2SurfEquiv N i₀ w = Multiplicative.ofAdd t :=
    ⟨Multiplicative.toAdd (h2SurfEquiv N i₀ w : Multiplicative (ZMod N)), rfl⟩
  have hw' : (h2SurfEquiv N i₀ w) ^ d = 1 := by rw [← map_pow, hw, map_one]
  rw [ht] at hw'
  change (Multiplicative.ofAdd t : Multiplicative (ZMod N)) ^ d = 1 at hw'
  have ht0 : d • t = 0 := by
    have := congrArg Multiplicative.toAdd hw'
    rwa [toAdd_pow, toAdd_ofAdd, toAdd_one] at this
  rw [ht, redZn_ofAdd, castHom_eq_zero_of_nsmul_eq_zero hd hN h t ht0]
  rfl

variable {i₀ i₀' φ}

/-- **The cusp class of the cover corestricts to the cusp class of `X`** (from `hres`, at level
`d·n`). -/
theorem cor_gen (hres : ResCuspInput i₀ i₀' φ) (n : ℕ+) :
    corH H hH n (phiH2 φ n (gen i₀' n)) = gen i₀ n := by
  set d := Fintype.card (SurfGrp g ⧸ H)
  have hd : 0 < d := Fintype.card_pos
  let N : ℕ+ := ⟨d * n, Nat.mul_pos hd n.pos⟩
  have hnN : (n : ℕ) ∣ (N : ℕ) := Dvd.intro_left d rfl
  have key : (corH H hH N (phiH2 φ N (gen i₀' N)) / gen i₀ N) ^ d = 1 := by
    rw [div_pow, ← map_pow, ← hres N, corH_resH, div_self']
  have h1 := h2Red_eq_one_of_pow i₀ hd rfl hnN _ key
  change h2RedG (SurfGrp g) hnN _ = 1 at h1
  have h2 : h2RedG (SurfGrp g) hnN (gen i₀ N) = gen i₀ n := h2Red_gen i₀ n N hnN
  rw [map_div, div_eq_one, ← corH_h2RedG, ← phiH2_h2Red, h2Red_gen] at h1
  exact h1.trans h2

/-- `cor ∘ φ^*` agrees with `h2SurfEquiv_X⁻¹ ∘ h2SurfEquiv_Y`. -/
lemma cor_phiH2_eq (hres : ResCuspInput i₀ i₀' φ) (n : ℕ+) (z : ContH2 (SurfGrp g') (Zn n)) :
    corH H hH n (phiH2 φ n z) = (h2SurfEquiv n i₀).symm (h2SurfEquiv n i₀' z) := by
  rw [eq_gen_pow i₀' n z, map_pow, map_pow, cor_gen hH hres, map_pow, map_pow,
    h2SurfEquiv_gen, ← h2SurfEquiv_gen i₀ n, MulEquiv.symm_apply_apply]

/-- **Corestriction is bijective** on `H²(−, ℤ/n)`. -/
theorem cor_bijective (hres : ResCuspInput i₀ i₀' φ) (n : ℕ+) :
    Function.Bijective (corH H hH n) := by
  have : (corH H hH n : ContH2 H (Zn n) → ContH2 (SurfGrp g) (Zn n)) =
      ((phiH2 φ n).symm.trans ((h2SurfEquiv n i₀').trans (h2SurfEquiv n i₀).symm) :
        ContH2 H (Zn n) → ContH2 (SurfGrp g) (Zn n)) := by
    funext z
    obtain ⟨w, rfl⟩ := (phiH2 φ n).surjective z
    rw [cor_phiH2_eq hH hres]
    simp
  rw [this]
  exact MulEquiv.bijective _

/-- **Remark 1.10.1(i) for `M_X ≅ I_x`**: the index-normalised morphism `M_Y → M_X` carries
`syncEquiv_Y(i_y)` to `syncEquiv_X(i_x)` for `i_y ↔ i_x` (both the image of `a ∈ Ẑ`, i.e.
corresponding under `I_y ≅ I_x`, cusp loop to cusp loop). -/
theorem normM_syncEquiv (hres : ResCuspInput i₀ i₀' φ) (a : Multiplicative ZHat) :
    normM H hH (cor_bijective hH hres) (transM φ (syncEquiv i₀' (inertiaEquiv i₀' a))) =
      syncEquiv i₀ (inertiaEquiv i₀ a) := by
  refine Subtype.ext (funext fun n => MonoidHom.ext fun z => ?_)
  rw [normM_apply, transM_apply]
  have hz : (corEquiv H hH (cor_bijective hH hres) n).symm z =
      phiH2 φ n ((h2SurfEquiv n i₀').symm (h2SurfEquiv n i₀ z)) := by
    rw [MulEquiv.symm_apply_eq]
    have := cor_phiH2_eq hH hres n ((h2SurfEquiv n i₀').symm (h2SurfEquiv n i₀ z))
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at this
    exact this.symm
  rw [hz, MulEquiv.symm_apply_apply, eq_gen_pow i₀ n z, map_pow, h2SurfEquiv_gen,
    ← h2SurfEquiv_gen i₀' n, ← map_pow (h2SurfEquiv n i₀'), MulEquiv.symm_apply_apply]
  change pair g' n _ (gen i₀' n ^ _) = pair g n _ (gen i₀ n ^ _)
  rw [map_pow, map_pow, pair_gen, pair_gen, inertiaEquiv_apply, inertiaEquiv_apply, charN_zhatPow,
    charN_zhatPow]

include hH in
/-- The usual functorially induced morphism carries `syncEquiv_Y(i_y)` to `syncEquiv_X(i_x)^d`. -/
theorem resM_syncEquiv (hres : ResCuspInput i₀ i₀' φ) (a : Multiplicative ZHat) :
    resM H (transM φ (syncEquiv i₀' (inertiaEquiv i₀' a))) =
      syncEquiv i₀ (inertiaEquiv i₀ a) ^ Fintype.card (SurfGrp g ⧸ H) := by
  rw [resM_eq_normM_pow H hH (cor_bijective hH hres), normM_syncEquiv hH hres]
  rfl

/-- `normM` is "the usual induced morphism divided by the index" on `M_X ≅ Ẑ`. -/
theorem normM_unique_model (hres : ResCuspInput i₀ i₀' φ) (ψ : MXg H →* MXg (SurfGrp g))
    (hψ : ∀ f, ψ f ^ Fintype.card (SurfGrp g ⧸ H) = resM H f) (f : MXg H) :
    ψ f = normM H hH (cor_bijective hH hres) f :=
  normM_unique H hH _ (fun x hx => MX_torsionFree i₀ Fintype.card_pos x hx) ψ hψ f

end Model

/-! ### The input for `H = ⊤` -/

/-- `⊤ ≃ₜ* Π̂_{g,0}`. -/
noncomputable def topEquiv (g : ℕ) : (⊤ : Subgroup (SurfGrp g)) ≃ₜ* SurfGrp g where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- The Riemann–Hurwitz input holds for the trivial cover (`d = 1`). -/
theorem hres_top {g : ℕ} (i₀ : Fin g) [Fintype (SurfGrp g ⧸ (⊤ : Subgroup (SurfGrp g)))] :
    ResCuspInput (H := ⊤) i₀ i₀ (topEquiv g) := by
  intro n
  have h1 : Fintype.card (SurfGrp g ⧸ (⊤ : Subgroup (SurfGrp g))) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_top x)
  rw [h1, pow_one]
  induction gen i₀ n using ContH2.induction_on with
  | h c => rfl

end Iut.Reconstruction.SurfaceH2
