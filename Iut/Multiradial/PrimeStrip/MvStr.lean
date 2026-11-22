/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.KummerLiftPf
import Iut.Multiradial.PrimeStrip.KummerRigid
import Iut.Multiradial.PrimeStrip.Black

/-!
# `π₁(‡D_v) ↷ ‡M_v`-structures at `v ∈ V^non` (IUT I, Definition 5.2 (v), (vi); MR21 R8a)

IUT I, Definition 5.2 (v) (`Inter-universal Teichmuller Theory I.txt`, l.9228–9268) constructs
from `π₁(‡D_v)`, functorially, an ind-topological monoid `M_v(‡D_v)`, "naturally isomorphic to
`O^▷_{F̄_v}`", with its natural `π₁(‡D_v)`-action ([AbsTopIII], Corollary 1.10 (b), (c), (d),
(d′)). Definition 5.2 (vi) (l.9269–9420) considers pairs `π₁(‡D_v) ↷ ‡M_v` isomorphic to
`π₁(‡D_v) ↷ M_v(‡D_v)` and observes (l.9388–9402) that there is a unique isomorphism
`M_v(‡D_v) ≅ ‡M_v` of monoids with `π₁(‡D_v)`-action. Here, for the model `Π_v ↷ O^▷` with
`O^▷ = {m ∈ \bar{ℚ}_p^× : ord m ≥ 0}` (`Mv D v`, `Π_v` acting through `Π_v → G_v`):

* generic part (any abelian group `M` with `ord : M →+ ℝ` and an element of `ord = 1`):
  `posPart ord = {ord ≥ 0}`; an additive automorphism `φ` of `posPart ord` extends uniquely to
  `M` (`PosPart.ext`, since `M = posPart − posPart`) and scales `ord` by some `λ > 0`
  (`PosPart.exists_ord_scale`: `φ` preserves the units `{ord = 0}` and the divisibility order;
  `λ = ord φ(c)`, then a squeeze by rationals);
* **`mvAut_eq_refl`**: every `Π_v`-equivariant additive automorphism of `O^▷` is the identity,
  from MR21's `KummerRigid` ([AbsTopIII], Proposition 3.2 (iv), injectivity; holds if
  `Π_v → G_v` is surjective, `kummerRigid`);
* **`MvStr D v`**: a monoid `‡M_v` with `Π_v`-action and an equivariant isomorphism from
  `O^▷` (unique, so a property up to unique choice); **`MvStr.uniqueIso`**: between two such
  structures there is exactly one equivariant isomorphism ("unique up to a uniquely determined
  isomorphism", l.9404–9407 for the `∞κ`-variant; l.9388–9402 for `M_v`);
* **functoriality in `Aut(π₁(‡D_v))`**: `mvLift`, the unique `σ`-equivariant automorphism of
  `O^▷` (existence from MR21's `kummerLift`, i.e. [AbsTopIII], Proposition 3.2 (iv),
  surjectivity, with the inputs `DeltaCharacteristic D v` and H3), `mvLift_trans`, `mvLift_refl`.

The topology of `‡M_v` is not recorded; uniqueness is proved for all (not necessarily continuous)
equivariant isomorphisms, which is the stronger statement. The `κ`-, `∞κ`-, `∞κ×`-coric
pseudo-monoids of (v), (vi) need a local version of MR9's `recFunctionField` (R8b, MR9).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Frobenioid

/-! ### Generic part: automorphisms of `{ord ≥ 0}` -/

section PosPart

variable {M : Type*} [AddCommGroup M] (ord : M →+ ℝ)

/-- **`{m : ord m ≥ 0}`** (`O^▷` for `M = \bar{ℚ}_p^×`). -/
def posPart : AddSubmonoid M where
  carrier := {m | 0 ≤ ord m}
  add_mem' {a b} ha hb := by
    change 0 ≤ ord (a + b)
    rw [map_add]
    exact add_nonneg ha hb
  zero_mem' := by
    change 0 ≤ ord 0
    rw [map_zero]

namespace PosPart

variable {ord}

theorem mem_iff {m : M} : m ∈ posPart ord ↔ 0 ≤ ord m := Iff.rfl

/-- Every element is a difference of two elements of `{ord ≥ 0}`. -/
theorem exists_sub (x : M) : ∃ a ∈ posPart ord, ∃ b ∈ posPart ord, x = a - b := by
  by_cases hx : 0 ≤ ord x
  · exact ⟨x, hx, 0, (posPart ord).zero_mem, (sub_zero x).symm⟩
  · refine ⟨0, (posPart ord).zero_mem, -x, ?_, by rw [zero_sub, neg_neg]⟩
    change 0 ≤ ord (-x)
    rw [map_neg]
    linarith

/-- The value of the extension on a chosen difference. -/
def extFun (f : posPart ord →+ posPart ord) (x : M) : M :=
  ((f ⟨_, (exists_sub x).choose_spec.1⟩ : posPart ord) : M) -
    f ⟨_, (exists_sub x).choose_spec.2.choose_spec.1⟩

theorem sub_wd (f : posPart ord →+ posPart ord) {a b a' b' : M} (ha : a ∈ posPart ord)
    (hb : b ∈ posPart ord) (ha' : a' ∈ posPart ord) (hb' : b' ∈ posPart ord)
    (h : a - b = a' - b') :
    ((f ⟨a, ha⟩ : posPart ord) : M) - f ⟨b, hb⟩ = f ⟨a', ha'⟩ - f ⟨b', hb'⟩ := by
  rw [sub_eq_sub_iff_add_eq_add] at h ⊢
  have h1 : (⟨a, ha⟩ : posPart ord) + ⟨b', hb'⟩ = ⟨a', ha'⟩ + ⟨b, hb⟩ := Subtype.ext h
  have h2 := congrArg (fun s => ((f s : posPart ord) : M)) h1
  simpa only [map_add, AddSubmonoid.coe_add] using h2

theorem extFun_eq (f : posPart ord →+ posPart ord) {x a b : M} (ha : a ∈ posPart ord)
    (hb : b ∈ posPart ord) (h : x = a - b) :
    extFun f x = ((f ⟨a, ha⟩ : posPart ord) : M) - f ⟨b, hb⟩ :=
  sub_wd f _ _ ha hb ((exists_sub x).choose_spec.2.choose_spec.2.symm.trans h)

/-- **The extension of `f` to `M`** (`M = posPart − posPart`). -/
def extHom (f : posPart ord →+ posPart ord) : M →+ M where
  toFun := extFun f
  map_zero' := by
    rw [extFun_eq f (posPart ord).zero_mem (posPart ord).zero_mem (sub_zero 0).symm, sub_self]
  map_add' x y := by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub (ord := ord) x
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_sub (ord := ord) y
    rw [extFun_eq f ha hb rfl, extFun_eq f ha' hb' rfl,
      extFun_eq f ((posPart ord).add_mem ha ha') ((posPart ord).add_mem hb hb') (by abel)]
    have e1 : (⟨a + a', (posPart ord).add_mem ha ha'⟩ : posPart ord) = ⟨a, ha⟩ + ⟨a', ha'⟩ := rfl
    have e2 : (⟨b + b', (posPart ord).add_mem hb hb'⟩ : posPart ord) = ⟨b, hb⟩ + ⟨b', hb'⟩ := rfl
    rw [e1, e2, map_add, map_add, AddSubmonoid.coe_add, AddSubmonoid.coe_add]
    abel

theorem extHom_coe (f : posPart ord →+ posPart ord) (s : posPart ord) :
    extHom f (s : M) = f s := by
  change extFun f (s : M) = _
  rw [extFun_eq f s.2 (posPart ord).zero_mem (sub_zero _).symm]
  have : (⟨0, (posPart ord).zero_mem⟩ : posPart ord) = 0 := rfl
  rw [this, map_zero, AddSubmonoid.coe_zero, sub_zero]

/-- **The extension of an automorphism of `posPart ord` to an automorphism of `M`.** -/
def ext (φ : posPart ord ≃+ posPart ord) : M ≃+ M where
  toFun := extHom φ.toAddMonoidHom
  invFun := extHom φ.symm.toAddMonoidHom
  left_inv x := by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub (ord := ord) x
    change extFun _ (extFun _ (a - b)) = a - b
    rw [extFun_eq _ ha hb rfl,
      extFun_eq _ (φ.toAddMonoidHom ⟨a, ha⟩).2 (φ.toAddMonoidHom ⟨b, hb⟩).2 rfl]
    simp
  right_inv x := by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub (ord := ord) x
    change extFun _ (extFun _ (a - b)) = a - b
    rw [extFun_eq _ ha hb rfl,
      extFun_eq _ (φ.symm.toAddMonoidHom ⟨a, ha⟩).2 (φ.symm.toAddMonoidHom ⟨b, hb⟩).2 rfl]
    simp
  map_add' := (extHom φ.toAddMonoidHom).map_add

theorem ext_coe (φ : posPart ord ≃+ posPart ord) (s : posPart ord) : ext φ (s : M) = φ s :=
  extHom_coe φ.toAddMonoidHom s

theorem ext_sub (φ : posPart ord ≃+ posPart ord) {a b : M} (ha : a ∈ posPart ord)
    (hb : b ∈ posPart ord) :
    ext φ (a - b) = ((φ ⟨a, ha⟩ : posPart ord) : M) - φ ⟨b, hb⟩ := by
  rw [map_sub]
  exact congrArg₂ (· - ·) (ext_coe φ ⟨a, ha⟩) (ext_coe φ ⟨b, hb⟩)

/-- **Units are preserved**: `ord s = 0` implies `ord φ(s) = 0`. -/
theorem ord_eq_zero (φ : posPart ord ≃+ posPart ord) (s : posPart ord) (hs : ord s = 0) :
    ord (φ s : M) = 0 := by
  have hn : -(s : M) ∈ posPart ord := by
    change 0 ≤ ord (-(s : M))
    rw [map_neg, hs, neg_zero]
  have hsum : s + ⟨-(s : M), hn⟩ = 0 := Subtype.ext (add_neg_cancel (s : M))
  have h2 := congrArg (fun t => ((φ t : posPart ord) : M)) hsum
  simp only [map_add, AddSubmonoid.coe_add, map_zero, AddSubmonoid.coe_zero] at h2
  have h3 := congrArg ord h2
  rw [map_add, map_zero] at h3
  have h4 := (φ s).2
  have h5 := (φ ⟨-(s : M), hn⟩).2
  rw [mem_iff] at h4 h5
  linarith

/-- **The divisibility order is preserved**: `ord s ≤ ord t` implies `ord φ(s) ≤ ord φ(t)`. -/
theorem ord_mono (φ : posPart ord ≃+ posPart ord) (s t : posPart ord) (h : ord s ≤ ord t) :
    ord (φ s : M) ≤ ord (φ t : M) := by
  have hd : (t : M) - s ∈ posPart ord := by
    change 0 ≤ ord ((t : M) - s)
    rw [map_sub]
    linarith
  have hsum : t = s + ⟨(t : M) - s, hd⟩ := Subtype.ext (by simp)
  rw [hsum, map_add, AddSubmonoid.coe_add, map_add]
  have h5 := (φ ⟨(t : M) - s, hd⟩).2
  rw [mem_iff] at h5
  linarith

theorem ord_nsmul (φ : posPart ord ≃+ posPart ord) (n : ℕ) (s : posPart ord) :
    ord (φ (n • s) : M) = n * ord (φ s : M) := by
  rw [map_nsmul, AddSubmonoidClass.coe_nsmul, map_nsmul, nsmul_eq_mul]

/-- A rational bound `q ≤ ord s` (resp. `≥`) transfers to `q · ord φ(c) ≤ ord φ(s)` (resp. `≥`). -/
theorem rat_le (φ : posPart ord ≃+ posPart ord) (c s : posPart ord) (hc : ord c = 1) (q : ℚ)
    (hq : 0 ≤ q) :
    ((q : ℝ) ≤ ord s → q * ord (φ c : M) ≤ ord (φ s : M)) ∧
      (ord s ≤ q → ord (φ s : M) ≤ q * ord (φ c : M)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = q.num := ⟨q.num.toNat, Int.toNat_of_nonneg
    (Rat.num_nonneg.mpr hq)⟩
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hqab : (q : ℝ) = a / q.den := by
    rw [Rat.cast_def, ← ha, Int.cast_natCast]
  have hca : ord ((a • c : posPart ord) : M) = a := by
    rw [AddSubmonoidClass.coe_nsmul, map_nsmul, hc, nsmul_eq_mul, mul_one]
  have hsb : ord ((q.den • s : posPart ord) : M) = q.den * ord s := by
    rw [AddSubmonoidClass.coe_nsmul, map_nsmul, nsmul_eq_mul]
  rw [hqab]
  constructor
  · intro h
    have h1 : ord ((a • c : posPart ord) : M) ≤ ord ((q.den • s : posPart ord) : M) := by
      rw [hca, hsb]
      rwa [div_le_iff₀ hb, mul_comm] at h
    have h2 := ord_mono φ _ _ h1
    rw [ord_nsmul, ord_nsmul] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hb, mul_comm (ord _)]
    exact h2
  · intro h
    have h1 : ord ((q.den • s : posPart ord) : M) ≤ ord ((a • c : posPart ord) : M) := by
      rw [hca, hsb]
      rwa [le_div_iff₀ hb, mul_comm] at h
    have h2 := ord_mono φ _ _ h1
    rw [ord_nsmul, ord_nsmul] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hb, mul_comm (ord _)]
    exact h2

/-- **`φ` scales `ord` by `λ = ord φ(c) > 0`** on `posPart ord`, if `ord c = 1`. -/
theorem exists_ord_scale (φ : posPart ord ≃+ posPart ord) (c : M) (hc : ord c = 1) :
    ∃ l : ℝ, 0 < l ∧ ∀ s : posPart ord, ord (φ s : M) = l * ord s := by
  have hc0 : c ∈ posPart ord := by rw [mem_iff, hc]; exact zero_le_one
  set c' : posPart ord := ⟨c, hc0⟩
  set l := ord (φ c' : M)
  have hl0 : 0 ≤ l := (φ c').2
  have hl : 0 < l := by
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := ord_eq_zero φ.symm (φ c') h.symm
      rw [AddEquiv.symm_apply_apply] at h1
      change ord c = 0 at h1
      rw [hc] at h1
      exact one_ne_zero h1
  refine ⟨l, hl, fun s => ?_⟩
  have hs0 : 0 ≤ ord s := s.2
  have ht0 : 0 ≤ ord (φ s : M) := (φ s).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : ord (φ s : M) / l < ord s := by rwa [div_lt_iff₀ hl, mul_comm]
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    have hq0 : (0 : ℝ) ≤ q := (div_nonneg ht0 hl0).trans hq1.le
    have := (rat_le φ c' s hc q (by exact_mod_cast hq0)).1 hq2.le
    rw [div_lt_iff₀ hl] at hq1
    linarith
  · have h1 : ord s < ord (φ s : M) / l := by rwa [lt_div_iff₀ hl, mul_comm]
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    have hq0 : (0 : ℝ) ≤ q := hs0.trans hq1.le
    have := (rat_le φ c' s hc q (by exact_mod_cast hq0)).2 hq1.le
    rw [lt_div_iff₀ hl] at hq2
    linarith

/-- **The extension scales `ord` on all of `M`.** -/
theorem ord_ext (φ : posPart ord ≃+ posPart ord) {l : ℝ}
    (hφ : ∀ s : posPart ord, ord (φ s : M) = l * ord s) (x : M) :
    ord (ext φ x) = l * ord x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub (ord := ord) x
  rw [ext_sub φ ha hb, map_sub, map_sub, hφ, hφ, mul_sub]

/-- **The extension is equivariant** for an action preserving `ord`, if `φ` is. -/
theorem ext_smul {G : Type*} [Monoid G] [DistribMulAction G M]
    (hord : ∀ (g : G) m, ord (g • m) = ord m)
    (φ : posPart ord ≃+ posPart ord)
    (hφ : ∀ (g : G) (s : posPart ord), ((φ ⟨g • (s : M), by rw [mem_iff, hord]; exact s.2⟩ :
      posPart ord) : M) = g • (φ s : M)) (g : G) (x : M) :
    ext φ (g • x) = g • ext φ x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_sub (ord := ord) x
  have ha' : g • a ∈ posPart ord := by rw [mem_iff, hord]; exact ha
  have hb' : g • b ∈ posPart ord := by rw [mem_iff, hord]; exact hb
  rw [smul_sub, ext_sub φ ha' hb', ext_sub φ ha hb, smul_sub]
  exact congrArg₂ (· - ·) (hφ g ⟨a, ha⟩) (hφ g ⟨b, hb⟩)

end PosPart

end PosPart

/-! ### The model `Π_v ↷ O^▷` -/

section Model

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`M_v = O^▷_{F̄_v}`** `= {m ∈ \bar{ℚ}_p^× : ord m ≥ 0}` (IUT I, Definition 5.2 (v),
l.9250–9256), as a type. -/
abbrev Mv : Type := ↥(posPart (ordPi D v))

theorem ordPi_smul_mem (g : (Piv D v).carrier) (s : Mv D v) :
    g • (s : PiMul D v) ∈ posPart (ordPi D v) := by
  rw [PosPart.mem_iff, ordPi_smul]
  exact s.2

/-- **The natural action `π₁(‡D_v) = Π_v ↷ M_v`** (through `Π_v → G_v`). -/
instance : DistribMulAction (Piv D v).carrier (Mv D v) where
  smul g s := ⟨g • (s : PiMul D v), ordPi_smul_mem D v g s⟩
  one_smul s := Subtype.ext (one_smul _ (s : PiMul D v))
  mul_smul g h s := Subtype.ext (mul_smul g h (s : PiMul D v))
  smul_zero g := Subtype.ext (smul_zero (A := PiMul D v) g)
  smul_add g s t := Subtype.ext (smul_add g (s : PiMul D v) (t : PiMul D v))

theorem mv_smul_coe (g : (Piv D v).carrier) (s : Mv D v) :
    ((g • s : Mv D v) : PiMul D v) = g • (s : PiMul D v) := rfl

/-- **`M_v`-uniqueness** (IUT I, Definition 5.2 (vi), l.9388–9402; from [AbsTopIII],
Proposition 3.2 (iv), injectivity = `KummerRigid`): every `Π_v`-equivariant additive automorphism
of `O^▷` is the identity. -/
theorem mvAut_eq_refl (hk : KummerRigid D v) (φ : Mv D v ≃+ Mv D v)
    (hφ : ∀ (g : (Piv D v).carrier) (s : Mv D v), φ (g • s) = g • φ s) :
    φ = AddEquiv.refl _ := by
  obtain ⟨l, hl, hscale⟩ := PosPart.exists_ord_scale φ (pMul D v) (ord_pMul D v)
  have hext := hk (PosPart.ext φ)
    (PosPart.ext_smul (fun g m => ordPi_smul D v g m) φ (fun g s => congrArg Subtype.val (hφ g s)))
    l hl (PosPart.ord_ext φ hscale)
  ext s
  have := DFunLike.congr_fun hext (s : PiMul D v)
  rw [PosPart.ext_coe] at this
  exact this

/-- **Equivariant isomorphisms** `M ≅ N` of monoids with `Π_v`-action. -/
def EqvIso (M N : Type) [AddCommMonoid M] [AddCommMonoid N] [DistribMulAction (Piv D v).carrier M]
    [DistribMulAction (Piv D v).carrier N] : Type :=
  {e : M ≃+ N // ∀ (g : (Piv D v).carrier) (m : M), e (g • m) = g • e m}

/-- **A `π₁(‡D_v) ↷ ‡M_v`-structure** (IUT I, Definition 5.2 (vi), l.9279–9284): a monoid with
`Π_v`-action, isomorphic (as such) to `Π_v ↷ M_v`. -/
structure MvStr where
  /-- The monoid `‡M_v`. -/
  M : Type
  [inst : AddCommMonoid M]
  [act : DistribMulAction (Piv D v).carrier M]
  /-- An equivariant isomorphism `M_v ≅ ‡M_v` (data; by `eqvIso_model_unique` it is the only
  one, so the choice is no extra structure). -/
  iso : EqvIso D v (Mv D v) M

attribute [instance] MvStr.inst MvStr.act

namespace EqvIso

variable {D v}
variable {M N P : Type} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [DistribMulAction (Piv D v).carrier M] [DistribMulAction (Piv D v).carrier N]
  [DistribMulAction (Piv D v).carrier P]

/-- Composition. -/
def trans (e : EqvIso D v M N) (f : EqvIso D v N P) : EqvIso D v M P :=
  ⟨e.1.trans f.1, fun g m => by
    change f.1 (e.1 (g • m)) = g • f.1 (e.1 m)
    rw [e.2, f.2]⟩

/-- Inverse. -/
def symm (e : EqvIso D v M N) : EqvIso D v N M :=
  ⟨e.1.symm, fun g n => by
    apply e.1.injective
    rw [e.2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]⟩

end EqvIso

/-- **Uniqueness of the isomorphism from the model**: two equivariant isomorphisms
`M_v ≅ ‡M_v` coincide (`KummerRigid`). -/
theorem eqvIso_model_unique (hk : KummerRigid D v) (T : MvStr D v)
    (e f : EqvIso D v (Mv D v) T.M) : e = f := by
  have h := mvAut_eq_refl D v hk (e.trans f.symm).1 (e.trans f.symm).2
  apply Subtype.ext
  ext s
  have h1 := DFunLike.congr_fun h s
  change f.1.symm (e.1 s) = s at h1
  calc e.1 s = f.1 (f.1.symm (e.1 s)) := (f.1.apply_symm_apply _).symm
    _ = f.1 s := by rw [h1]

/-- **`‡M_v` is unique up to a uniquely determined isomorphism** (IUT I, Definition 5.2 (vi),
l.9388–9407): between two `π₁(‡D_v) ↷ ‡M_v`-structures there is exactly one equivariant
isomorphism. -/
@[reducible] def MvStr.uniqueIso (hk : KummerRigid D v) (T T' : MvStr D v) :
    Unique (EqvIso D v T.M T'.M) where
  default := T.iso.symm.trans T'.iso
  uniq e := by
    let i := T.iso
    have h := eqvIso_model_unique D v hk T' (i.trans e)
      (i.trans (T.iso.symm.trans T'.iso))
    apply Subtype.ext
    ext m
    have h1 := DFunLike.congr_fun (congrArg Subtype.val h) (i.1.symm m)
    change e.1 (i.1 (i.1.symm m)) = _ at h1
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1]
    change (T.iso.symm.trans T'.iso).1 (i.1 (i.1.symm m)) = _
    rw [AddEquiv.apply_symm_apply]

/-- **The model structure** `Π_v ↷ M_v`. -/
def MvStr.model : MvStr D v where
  M := Mv D v
  iso := ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-! ### Functoriality in `Aut(π₁(‡D_v))` -/

/-- **`σ`-equivariant automorphisms of `M_v`** for `σ ∈ Aut(Π_v)`. -/
def IsMvLift (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) (φ : Mv D v ≃+ Mv D v) : Prop :=
  ∀ (g : (Piv D v).carrier) (s : Mv D v), φ (g • s) = σ g • φ s

/-- **Uniqueness of `σ`-lifts** (`KummerRigid`). -/
theorem isMvLift_unique (hk : KummerRigid D v) {σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier}
    {φ ψ : Mv D v ≃+ Mv D v} (hφ : IsMvLift D v σ φ) (hψ : IsMvLift D v σ ψ) : φ = ψ := by
  have h := mvAut_eq_refl D v hk (φ.trans ψ.symm) (fun g s => by
    change ψ.symm (φ (g • s)) = g • ψ.symm (φ s)
    apply ψ.injective
    rw [AddEquiv.apply_symm_apply, hψ, AddEquiv.apply_symm_apply, hφ])
  ext s
  have h1 := DFunLike.congr_fun h s
  change ψ.symm (φ s) = s at h1
  refine congrArg Subtype.val ?_
  calc φ s = ψ (ψ.symm (φ s)) := (ψ.apply_symm_apply _).symm
    _ = ψ s := by rw [h1]

/-- **Existence of `σ`-lifts** ([AbsTopIII], Proposition 3.2 (iv), surjectivity = MR21's
`KummerLift`): an `ord`-preserving `σ`-equivariant automorphism of `\bar{ℚ}_p^×` restricts to
`O^▷`. -/
theorem exists_isMvLift (hk : KummerLift D v) (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) :
    ∃ φ : Mv D v ≃+ Mv D v, IsMvLift D v σ φ := by
  obtain ⟨ψ, hψ, hord⟩ := hk σ
  have hm : ∀ s : Mv D v, ψ s ∈ posPart (ordPi D v) := fun s => by
    rw [PosPart.mem_iff, hord]; exact s.2
  have hm' : ∀ s : Mv D v, ψ.symm s ∈ posPart (ordPi D v) := fun s => by
    rw [PosPart.mem_iff, ← hord, AddEquiv.apply_symm_apply]; exact s.2
  let e : Mv D v ≃+ Mv D v :=
    { toFun := fun s => ⟨ψ s, hm s⟩
      invFun := fun s => ⟨ψ.symm s, hm' s⟩
      left_inv := fun s => Subtype.ext (ψ.symm_apply_apply (s : PiMul D v))
      right_inv := fun s => Subtype.ext (ψ.apply_symm_apply (s : PiMul D v))
      map_add' := fun s t => Subtype.ext (map_add ψ (s : PiMul D v) t) }
  exact ⟨e, fun g s => Subtype.ext (hψ g s)⟩

/-- **The functorial action of `Aut(π₁(‡D_v))` on `M_v`** (IUT I, Definition 5.2 (v):
"in a functorial fashion"): the unique `σ`-equivariant automorphism of `O^▷`, given MR20's
named input `DeltaCharacteristic D v` and H3. -/
def mvLift (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) : Mv D v ≃+ Mv D v :=
  (exists_isMvLift D v (kummerLift D v hΔ h3) σ).choose

theorem mvLift_spec (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) : IsMvLift D v σ (mvLift D v hΔ h3 σ) :=
  (exists_isMvLift D v (kummerLift D v hΔ h3) σ).choose_spec

/-- `mvLift` is the only `σ`-lift. -/
theorem mvLift_eq (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (σ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) {φ : Mv D v ≃+ Mv D v}
    (hφ : IsMvLift D v σ φ) : mvLift D v hΔ h3 σ = φ :=
  isMvLift_unique D v (kummerRigid D v h3.1) (mvLift_spec D v hΔ h3 σ) hφ

/-- **Functoriality**: `mvLift (σ ≫ τ) = mvLift σ ≫ mvLift τ`. -/
theorem mvLift_trans (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v)
    (σ τ : (Piv D v).carrier ≃ₜ* (Piv D v).carrier) :
    mvLift D v hΔ h3 (σ.trans τ) = (mvLift D v hΔ h3 σ).trans (mvLift D v hΔ h3 τ) :=
  mvLift_eq D v hΔ h3 _ fun g s => by
    change mvLift D v hΔ h3 τ (mvLift D v hΔ h3 σ (g • s)) = τ (σ g) • _
    rw [mvLift_spec, mvLift_spec]
    rfl

/-- **Functoriality**: `mvLift id = id`. -/
theorem mvLift_refl (hΔ : DeltaCharacteristic D v) (h3 : PiToGQuotient D v) :
    mvLift D v hΔ h3 (ContinuousMulEquiv.refl _) = AddEquiv.refl _ :=
  mvLift_eq D v hΔ h3 _ fun _ _ => rfl

end Model

end PrimeStrip

end Multiradial

end Iut

end
