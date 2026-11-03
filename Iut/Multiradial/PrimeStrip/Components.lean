/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Local
import Iut.Frobenioid.OrbitMap
import Iut.Frobenioid.Tempered.SplitFrob
import Iut.Concrete.ThetaLocalConstruct.Roots
import Iut.Cor312.ThetaData.TwoTorsion

/-!
# The non-archimedean constituents `D_v`, `D^⊢_v`, `C_v`, `F^⊢_v` (MR20 T2, T3)

IUT I, Examples 3.2 (i), (iii), (iv) (`v ∈ V^bad`) and 3.3 (i) (`v ∈ V^good ∩ V^non`), l.4483–5189
of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`:

* **`Dv D v = B^{(temp)}(Π_v)⁰`** (`OrbitObj (Piv D v)`, the connected objects of `B^temp(Π_v)`
  at `V^bad`, of `B(Π_v)` at `V^good`);
* **`DVdash D v = D^⊢_v = B(G_v)⁰`** (`OrbitObj (Gv D v)`), and, given the quotient property
  `PiToGQuotient D v` (debt H3), the functor **`toVdash D v h : D_v ⥤ D^⊢_v`**, `Π_v/U ↦ G_v/φ(U)`
  (the passage to `B(K_v)⁰` of [AbsAnab], Lemma 1.3.8, used for the mono-analyticisation of IUT I,
  Definition 4.1 (iv));
* **`Cv D v`**, the `p_v`-adic Frobenioid over `D_v` with `Φ = ord(O^▷)^{pf} ≅ ℚ_{≥0}`
  ([FrdII], Example 1.1 (ii)): the model Frobenioid of the `Π_v`-module `\bar{ℚ}_p^×` (`Π_v` acting
  through `Π_v → G_v`), `B(Π_v/U) = (\bar{ℚ}_p^×)^U ×_{ord} ℚ`, `Div_B = ord`. At `V^good` this is
  `C_v` of Example 3.3 (i) (the pull-back of `ord(O^▷_{K̄})^{pf}` to `D_v`); at `V^bad` it is the
  base-field-theoretic hull `C_v = C^{bs-fld} ⊆ F_v` of Example 3.2 (iii) ([EtTh], Definition 3.6
  (iv): its rational functions are those of the base field). That this model is the hull *of the
  tempered Frobenioid `F_v` of `X̲_v`* needs MR18's tempered Frobenioid instantiated at `X̲_v` (debt
  H4 of the MR20 plan; not used by the objects here). A Frobenioid (`Cv_isFrobenioid`) with
  roots of unity with open stabilizers (`Cv_torsion`, the input of [FrdI], Theorem 3.4 for models;
  `GaloisModel.thm34` itself assumes a compact group, which the tempered `Π_v` is not);
* **`CVdash D v = C^⊢_v`** over `D^⊢_v`: the `p_v`-adic Frobenioid of `G_v` with
  `Φ = ord(ℤ_p^▷) = ℕ · ord(p)` at `V^good` (Example 3.3 (i), `PAdicGalois.Frob`) and
  `Φ = ℕ · log_Φ(q̲_v)` at `V^bad` (Example 3.2 (iv), `q̲_v = q_v^{1/2l}`,
  `ord(q̲_v) = ord(q_v)/2l`);
* **the splittings `τ^⊢_v`** (`tauVdash`): `p^ℕ` at `V^good` (Example 3.3 (i): "the splitting
  determined by `p_v`"), `q̲_v^ℕ` at `V^bad` (Example 3.2 (iv)); generic statement
  `GaloisModel.isCharSplitting_piSplit` ([FrdI], Definition 2.3, `Model.IsCharSplitting`). At
  `V^bad` the root `q̲_v ∈ K_v` of `q_v` exists by Definition 3.1 (b), (c) ("our assumption
  concerning 2-torsion … together with the definition of K", Example 3.2 (iv)): `qRootExists`
  (`E(K_v)[l]` has `l²` points by the type `(1, l-tors)` of `X̲_K`, `E(K_v)[2]` four by the
  rationality of `E_F[2]`; `TateStructure.exists_pow_eq_q`). Both
  `tauVdash_isCharSplitting_good` (in `Black.lean`) and `tauVdash_isCharSplitting_bad` are
  unconditional (the latter uses `‖ι q̲_v‖ < 1`, from the continuity of `ι`:
  `norm_iota_lt_one`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Anabelian Iut.Frobenioid

/-! ### Characteristic splittings `π^ℕ` of a Galois model Frobenioid -/

namespace GaloisModel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
variable (ℓ : M →+ ℝ) (hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m) (Γ : AddSubgroup ℝ)

/-- The element of `M` underlying a rational function `b ∈ B(A) = (ℓ⁻¹Γ)^H`. -/
def bval {A : OrbitObj G} (b : (bGal G ℓ hℓ Γ).obj A) : M :=
  (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from b).1

lemma bval_mem {A : OrbitObj G} (b : (bGal G ℓ hℓ Γ).obj A) :
    bval ℓ hℓ Γ b ∈ fixedSub (preSub G ℓ hℓ Γ) A :=
  (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from b).2

/-- The rational function given by an element of `(ℓ⁻¹Γ)^H`. -/
def bmk {A : OrbitObj G} (m : M) (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    (bGal G ℓ hℓ Γ).obj A :=
  (⟨m, hm⟩ : ↥(fixedSub (preSub G ℓ hℓ Γ) A))

lemma bval_bmk {A : OrbitObj G} (m : M) (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    bval ℓ hℓ Γ (bmk ℓ hℓ Γ m hm) = m := rfl

lemma bval_injective {A : OrbitObj G} : Function.Injective (bval ℓ hℓ Γ (A := A)) :=
  fun _ _ h => Subtype.ext h

lemma bval_add {A : OrbitObj G} (a b : (bGal G ℓ hℓ Γ).obj A) :
    bval ℓ hℓ Γ (a + b) = bval ℓ hℓ Γ a + bval ℓ hℓ Γ b := rfl

lemma bval_zero {A : OrbitObj G} : bval ℓ hℓ Γ (0 : (bGal G ℓ hℓ Γ).obj A) = 0 := rfl

lemma bval_pb {A A' : OrbitObj G} (f : A ⟶ A') (b : (bGal G ℓ hℓ Γ).obj A') :
    bval ℓ hℓ Γ ((bGal G ℓ hℓ Γ).pb f b) = OrbitHom.rep f • bval ℓ hℓ Γ b := rfl

lemma divGal_app {A : OrbitObj G} (b : (bGal G ℓ hℓ Γ).obj A) :
    (((divGal G ℓ hℓ Γ).app A b : Γ) : ℝ) = ℓ (bval ℓ hℓ Γ b) := rfl

/-- `τ(A) = π^ℕ ⊆ B(A)`, for a `G`-invariant element `π`. -/
def piSplit (π : M) (A : OrbitObj G) : AddSubmonoid ((bGal G ℓ hℓ Γ).obj A) where
  carrier := {b | ∃ n : ℕ, bval ℓ hℓ Γ b = n • π}
  add_mem' {a b} := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by change bval ℓ hℓ Γ (a + b) = _; rw [bval_add, hm, hn, add_nsmul]⟩
  zero_mem' := ⟨0, by rw [bval_zero, zero_nsmul]⟩

variable {ℓ hℓ Γ}

lemma mem_piSplit {π : M} {A : OrbitObj G} {b : (bGal G ℓ hℓ Γ).obj A} :
    b ∈ piSplit ℓ hℓ Γ π A ↔ ∃ n : ℕ, bval ℓ hℓ Γ b = n • π := Iff.rfl

/-- **`π^ℕ` is a characteristic splitting** ([FrdI], Definition 2.3) of the Galois model
Frobenioid with `Γ = ℤ · ℓ(π)`, for `π` fixed by `G` with `ℓ(π) > 0`. -/
theorem isCharSplitting_piSplit (π : M) (hπ : ∀ g : G, g • π = π) (hpos : 0 < ℓ π)
    (hΓ : Γ = AddSubgroup.zmultiples (ℓ π)) :
    Model.IsCharSplitting (divB := divGal G ℓ hℓ Γ) (piSplit ℓ hℓ Γ π) := by
  have hnπ : ∀ (n : ℕ) (g : G), g • (n • π) = n • π := fun n g => by rw [smul_comm, hπ]
  have hmemΓ : ∀ n : ℕ, ℓ (n • π) ∈ Γ := fun n => by
    rw [hΓ, map_nsmul]; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) n
  have hdiv : ∀ {A : OrbitObj G} (b : (bGal G ℓ hℓ Γ).obj A),
      b ∈ Model.orhdSub (divGal G ℓ hℓ Γ) A ↔ 0 ≤ ℓ (bval ℓ hℓ Γ b) := fun _ => Iff.rfl
  have hunit : ∀ {A : OrbitObj G} (b : (bGal G ℓ hℓ Γ).obj A),
      b ∈ Model.unitSub (divGal G ℓ hℓ Γ) A ↔ ℓ (bval ℓ hℓ Γ b) = 0 := fun b => by
    rw [Model.unitSub, AddMonoidHom.mem_ker, ← divGal_app, Subtype.ext_iff]
    rfl
  refine ⟨fun A b hb => ?_, fun {A A'} f b hb => ?_, fun A b hb => ?_, fun A u u' t t' hu hu' ht
    ht' h => ?_⟩
  · obtain ⟨n, hn⟩ := hb
    rw [hdiv, hn, map_nsmul]
    exact nsmul_nonneg hpos.le n
  · obtain ⟨n, hn⟩ := hb
    exact ⟨n, by rw [bval_pb, hn, hnπ]⟩
  · have hb0 : 0 ≤ ℓ (bval ℓ hℓ Γ b) := (hdiv b).mp hb
    have hbΓ₀ : ℓ (bval ℓ hℓ Γ b) ∈ Γ := (bval_mem ℓ hℓ Γ b).1
    have hbΓ : ℓ (bval ℓ hℓ Γ b) ∈ AddSubgroup.zmultiples (ℓ π) := hΓ ▸ hbΓ₀
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hbΓ
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have hneg' : (k : ℝ) * ℓ π < 0 :=
        mul_neg_of_neg_of_pos (by exact_mod_cast (not_le.mp hneg)) hpos
      rw [← hk, zsmul_eq_mul] at hb0
      linarith
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hℓu : ℓ (bval ℓ hℓ Γ b - n • π) = 0 := by
      rw [map_sub, map_nsmul, ← hk, natCast_zsmul, sub_self]
    have hbH := (bval_mem ℓ hℓ Γ b).2
    refine ⟨bmk ℓ hℓ Γ (bval ℓ hℓ Γ b - n • π) ⟨by
      change ℓ (bval ℓ hℓ Γ b - n • π) ∈ Γ; rw [hℓu]; exact Γ.zero_mem, fun h hh => by
      rw [smul_sub, hbH h hh, hnπ]⟩, (hunit _).mpr hℓu,
      bmk ℓ hℓ Γ (n • π) ⟨hmemΓ n, fun h _ => hnπ n h⟩, ⟨n, rfl⟩,
      bval_injective ℓ hℓ Γ ?_⟩
    rw [bval_add, bval_bmk, bval_bmk, sub_add_cancel]
  · obtain ⟨m, hm⟩ := ht
    obtain ⟨m', hm'⟩ := ht'
    have hu0 := (hunit u).mp hu
    have hu0' := (hunit u').mp hu'
    have hval := congrArg (fun x : (bGal G ℓ hℓ Γ).obj A => ℓ (bval ℓ hℓ Γ x)) h
    simp only [bval_add, map_add, hu0, hu0', hm, hm', map_nsmul, zero_add] at hval
    have hmm : m = m' := by
      rw [nsmul_eq_mul, nsmul_eq_mul] at hval
      exact_mod_cast mul_right_cancel₀ hpos.ne' hval
    have htt : t = t' := bval_injective ℓ hℓ Γ (by rw [hm, hm', hmm])
    refine ⟨?_, htt⟩
    rw [htt] at h
    exact add_right_cancel h

end GaloisModel

section Theta

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-! ### `D_v` and `D^⊢_v` -/

/-- **`D_v = B^{(temp)}(Π_v)⁰`** (IUT I, Examples 3.2 (i), 3.3 (i)). -/
abbrev Dv : Type := OrbitObj (Piv D v).carrier

/-- **`D^⊢_v = B(G_v)⁰`** (IUT I, Examples 3.2 (i), 3.3 (i): `B(K_v)⁰`). -/
abbrev DVdash : Type := OrbitObj (Gv D v)

/-- **`D_v ⥤ D^⊢_v`**, `Π_v/U ↦ G_v/φ(U)` (given the quotient property, debt H3). -/
def toVdash (h : PiToGQuotient D v) : Dv D v ⥤ DVdash D v :=
  OrbitObj.mapFunctor (piToG D v) h.2

/-! ### `C_v` -/

/-- `\bar{ℚ}_p^×` (additively) as a `Π_v`-module, through `Π_v → G_v`. -/
def PiMul : Type := PAdicGalois.Mul (pv D v)

instance : AddCommGroup (PiMul D v) := inferInstanceAs (AddCommGroup (PAdicGalois.Mul (pv D v)))

instance : DistribMulAction (Piv D v).carrier (PiMul D v) :=
  letI : DistribMulAction (Gv D v) (PiMul D v) :=
    inferInstanceAs (DistribMulAction (Gv D v) (PAdicGalois.Mul (pv D v)))
  DistribMulAction.compHom _ (piToG D v)

lemma piMul_smul (g : (Piv D v).carrier) (x : PiMul D v) :
    g • x = (show PAdicGalois.Mul (pv D v) from (piToG D v g • (show PAdicGalois.Mul (pv D v)
      from x))) := rfl

/-- `ord : \bar{ℚ}_p^× → ℝ` on the `Π_v`-module. -/
def ordPi : PiMul D v →+ ℝ := PAdicGalois.ord (pv D v)

lemma ordPi_smul (g : (Piv D v).carrier) (x : PiMul D v) : ordPi D v (g • x) = ordPi D v x :=
  PAdicGalois.ord_smul (pv D v) (Lv D v) (piToG D v g) x

/-- **The `p_v`-adic Frobenioid `C_v` over `D_v`** (IUT I, Examples 3.2 (iii), 3.3 (i);
[FrdII], Example 1.1 (ii) with `Φ = ord(O^▷)^{pf} ≅ ℚ_{≥0}`). -/
abbrev Cv : Type := GaloisModel (Piv D v).carrier (ordPi D v) (ordPi_smul D v) PAdicGalois.gammaQ

/-- The Frobenioid structure functor `C_v → F_Φ` of `C_v`. -/
abbrev cvElem :=
  Model.toElem (constPhi (Dv D v) PAdicGalois.gammaQ)
    (bGal (Piv D v).carrier (ordPi D v) (ordPi_smul D v) PAdicGalois.gammaQ)
    (divGal (Piv D v).carrier (ordPi D v) (ordPi_smul D v) PAdicGalois.gammaQ)

/-- **`C_v` is a Frobenioid** ([FrdI], Theorem 5.2 (ii)). -/
theorem Cv_isFrobenioid : IsFrobenioid (cvElem D v) := GaloisModel.isFrobenioid _ _ _ _

/-- The base functor `C_v ⥤ D_v`. -/
abbrev cvBase : Cv D v ⥤ Dv D v := cvElem D v ⋙ Elem.proj

/-- Roots of unity of `\bar{ℚ}_p` have open stabilizers in `Π_v`. -/
theorem Cv_torsion (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : PiMul D v, m ≠ 0 ∧ n • m = 0 ∧ ordPi D v m = 0 ∧
      IsOpen (MulAction.stabilizer (Piv D v).carrier m : Set (Piv D v).carrier) := by
  obtain ⟨m, h0, hn', ho, hopen⟩ := PAdicGalois.torsion (pv D v) (Lv D v) n hn
  refine ⟨m, h0, hn', ho, ?_⟩
  have : (MulAction.stabilizer (Piv D v).carrier (show PiMul D v from m) :
      Set (Piv D v).carrier) = piToG D v ⁻¹' (MulAction.stabilizer (Gv D v) m : Set (Gv D v)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rfl
  rw [this]
  exact hopen.preimage (continuous_piToG D v)

/-! ### `C^⊢_v` and `τ^⊢_v` -/

/-- **The Tate parameter `q_v ∈ K_v`** at `v ∈ V^bad` (of the Tate structure of `X̲_v`). -/
def qv (hv : v ∈ D.VBad) : (Kv D v)ˣ := (D.localData.tateX v hv).t.q

/-- `\bar{ℚ}_p^×` image of a unit of `K_v`. -/
def toMul (x : (Kv D v)ˣ) : PAdicGalois.Mul (pv D v) :=
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  Additive.ofMul (Units.map (iota (pv D v) (Kv D v)).toRingHom.toMonoidHom x)

open scoped Classical in
/-- **`ord(q̲_v) = ord(q_v)/2l`** at `v ∈ V^bad`; `ord(p) = 1` otherwise. -/
def ordTau : ℝ :=
  if hv : v ∈ D.VBad then PAdicGalois.ord (pv D v) (toMul D v (qv D v hv)) / (2 * D.ℓ) else 1

/-- **`Φ^gp_{C^⊢_v} = ℤ · ord(τ)`** (`τ = q̲_v` at `V^bad`, `p` at `V^good`). -/
def gammaVdash : AddSubgroup ℝ := AddSubgroup.zmultiples (ordTau D v)

/-- **`C^⊢_v` over `D^⊢_v`** (IUT I, Example 3.2 (iv): `Φ_{C^⊢_v} = ℕ · log_Φ(q̲_v)`; Example 3.3
(i): `Φ_{C^⊢_v} = ord(ℤ_p^▷)`). -/
abbrev CVdash : Type := PAdicGalois.GFrob (pv D v) (Lv D v) (gammaVdash D v)

/-- The Frobenioid structure functor of `C^⊢_v`. -/
abbrev cvdElem :=
  Model.toElem (constPhi (DVdash D v) (gammaVdash D v))
    (bGal (Gv D v) (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
      (gammaVdash D v))
    (divGal (Gv D v) (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
      (gammaVdash D v))

/-- **`C^⊢_v` is a Frobenioid**. -/
theorem CVdash_isFrobenioid : IsFrobenioid (cvdElem D v) := GaloisModel.isFrobenioid _ _ _ _

/-- The base functor `C^⊢_v ⥤ D^⊢_v`. -/
abbrev cvdBase : CVdash D v ⥤ DVdash D v := cvdElem D v ⋙ Elem.proj

/-- `q_v` has a `2l`-th root in `K_v` (IUT I, Example 3.2 (iv), from Definition 3.1 (b), (c));
proved as `qRootExists`. -/
def QRootExists (hv : v ∈ D.VBad) : Prop := ∃ x : (Kv D v)ˣ, x ^ (2 * D.ℓ) = qv D v hv

open scoped Classical in
/-- An injective homomorphism of abelian groups does not decrease the size of the `n`-torsion. -/
lemma card_torsionBy_le_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (hφ : Function.Injective φ) (n : ℕ)
    [Finite ↥(AddSubgroup.torsionBy B (n : ℤ))] :
    Nat.card ↥(AddSubgroup.torsionBy A (n : ℤ)) ≤ Nat.card ↥(AddSubgroup.torsionBy B (n : ℤ)) := by
  refine Nat.card_le_card_of_injective (fun P => ⟨φ P.1, ?_⟩) fun P Q h => ?_
  · have := P.2
    rw [AddSubgroup.torsionBy.nsmul_iff] at this ⊢
    rw [← map_nsmul, this, map_zero]
  · exact Subtype.ext (hφ (congrArg Subtype.val h))

open scoped Classical in
/-- Four rational `2`-torsion points of `E_F` stay `2`-torsion points of any curve `W` over `K`
equal to `E_F ×_F K`, after a further base change `g : K → L`. -/
lemma four_le_card_torsion_two_map {F K L : Type*} [Field F] [Field K] [Field L]
    (E : WeierstrassCurve F) (f : F →+* K) (g : K →+* L) (W : WeierstrassCurve K)
    (hW : W = E.map f)
    [Finite ↥(AddSubgroup.torsionBy (W.map g).toAffine.Point ((2 : ℕ) : ℤ))]
    (htwo : 2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy E.toAffine.Point ((2 : ℕ) : ℤ))) :
    2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (W.map g).toAffine.Point ((2 : ℕ) : ℤ)) := by
  subst hW
  exact htwo.trans (card_torsionBy_le_of_injective ((pointMap (E.map f) g).comp (pointMap E f))
    ((pointMap_injective _ g).comp (pointMap_injective E f)) 2)

open scoped Classical in
/-- For `X` of type `(1, l-tors)` over `K` (`E(K)[l]` of order `l²`), `E(L)[l]` has at least `l²`
elements after any base change `K → L`. -/
lemma sq_le_card_torsion_baseChange {K L : Type*} [Field K] [Field L] (X : Orbicurve K)
    (f : K →+* L) (ℓ : ℕ) (hX : X.IsTypeOneEllTors ℓ)
    (hfin : Finite ↥(AddSubgroup.torsionBy (X.E.map f).toAffine.Point (ℓ : ℤ))) :
    ℓ * ℓ ≤ Nat.card ↥(AddSubgroup.torsionBy (X.E.map f).toAffine.Point (ℓ : ℤ)) := by
  obtain ⟨-, hlev, -, -, -, hcard⟩ := hX
  rw [← pow_two, ← hcard, Orbicurve.torsion, hlev]
  exact card_torsionBy_le_of_injective (pointMap X.E f) (pointMap_injective _ _) ℓ

open scoped Classical in
/-- **`q_v` has a `2l`-th root in `K_v`** (IUT I, Example 3.2 (iv): "our assumption concerning
2-torsion … together with the definition of `K`"): `E(K_v)[l]` has `l²` elements since `X̲_K` is of
type `(1, l-tors)` (Definition 3.1 (d)), `E(K_v)[2]` has four since `E_F[2]` is rational over `F`
(Definition 3.1 (b)); `TateStructure.exists_pow_eq_q`. -/
theorem qRootExists (hv : v ∈ D.VBad) : QRootExists D v hv := by
  have hℓ := D.prime.ℓ_prime
  haveI : NeZero D.prime.ℓ := ⟨hℓ.ne_zero⟩
  have hodd : Odd D.prime.ℓ := hℓ.odd_of_ne_two (by have := D.prime.five_le; omega)
  let S := D.localData.tateX v hv
  haveI := S.finite_torsion D.prime.ℓ
  haveI := S.finite_torsion 2
  have hl : D.prime.ℓ * D.prime.ℓ ≤ Nat.card ↥(TateStructure.torsion D.prime.ℓ (Xv D v).E) :=
    sq_le_card_torsion_baseChange D.orb.XKu (FinitePlace.embedding (D.V.sectFin v).maximalIdeal)
      D.prime.ℓ D.orb.XKu_type (S.finite_torsion D.prime.ℓ)
  have h2 : 2 * 2 ≤ Nat.card ↥(TateStructure.torsion 2 (Xv D v).E) :=
    @four_le_card_torsion_two_map _ _ _ _ _ _ D.E (algebraMap D.F D.Kt)
      (FinitePlace.embedding (D.V.sectFin v).maximalIdeal) D.orb.XKu.E D.orb.XKu_to_XK.E_eq
      (S.finite_torsion 2) (four_le_card_torsionBy_two D.E D.global.six_torsion_rational)
  obtain ⟨x, hx⟩ := S.exists_pow_eq_q D.prime.ℓ hodd hl h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (mul_ne_zero two_ne_zero hℓ.ne_zero)] at hx
    exact (qv D v hv).ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hx)⟩

/-- `p ∈ \bar{ℚ}_p^×`. -/
def pMul : PAdicGalois.Mul (pv D v) :=
  Additive.ofMul (Units.mk0 (algebraMap ℚ_[pv D v] (PadicAlgCl (pv D v)) (pv D v))
    (by simpa using (Fact.out : (pv D v).Prime).ne_zero))

open scoped Classical in
/-- **The element `τ` generating the splitting**: a chosen root `q̲_v` at `V^bad`, `p` at
`V^good`. -/
def tauElt : PAdicGalois.Mul (pv D v) :=
  if hv : v ∈ D.VBad then toMul D v (qRootExists D v hv).choose else pMul D v

/-- **The characteristic splitting `τ^⊢_v`** of `C^⊢_v` (IUT I, Examples 3.2 (iv), 3.3 (i)). -/
def tauVdash (A : DVdash D v) :=
  GaloisModel.piSplit (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
    (gammaVdash D v) (tauElt D v) A

/-! ### `τ^⊢_v` at `V^bad` -/

/-- `ι : K_v → \bar{ℚ}_p` is continuous (a `ℚ_p`-linear map out of a finite-dimensional
space). -/
theorem continuous_iota :
    letI := padicAlg D v
    haveI := isAlgebraic_padicAlg D v
    Continuous (iota (pv D v) (Kv D v)) := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  haveI : FiniteDimensional ℚ_[pv D v] (Kv D v) :=
    LocalConstruct.finite_padicAlgebra (p := pv D v) rfl
  haveI : ContinuousSMul ℚ_[pv D v] (Kv D v) :=
    continuousSMul_of_algebraMap ℚ_[pv D v] _
      (LocalConstruct.continuous_padicEmb (p := pv D v) rfl)
  exact (iota (pv D v) (Kv D v)).toLinearMap.continuous_of_finiteDimensional

/-- **`‖ι x‖ < 1` for `‖x‖ < 1`**. -/
theorem norm_iota_lt_one (x : Kv D v) (hx : ‖x‖ < 1) :
    letI := padicAlg D v
    haveI := isAlgebraic_padicAlg D v
    ‖iota (pv D v) (Kv D v) x‖ < 1 := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  have h0 : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  have h1 : Filter.Tendsto (fun n : ℕ => iota (pv D v) (Kv D v) x ^ n) Filter.atTop
      (nhds 0) := by
    have := ((continuous_iota D v).tendsto 0).comp h0
    simpa [Function.comp_def, map_pow] using this
  by_contra hge
  push Not at hge
  have h2 := (h1.norm).eventually (gt_mem_nhds (show ‖(0 : PadicAlgCl (pv D v))‖ < 1 by simp))
  obtain ⟨n, hn⟩ := h2.exists
  rw [norm_pow] at hn
  exact absurd (one_le_pow₀ hge : (1 : ℝ) ≤ _) (not_le.mpr hn)

lemma toMul_val (x : (Kv D v)ˣ) :
    letI := padicAlg D v
    haveI := isAlgebraic_padicAlg D v
    ((Additive.toMul (toMul D v x) : (PadicAlgCl (pv D v))ˣ) : PadicAlgCl (pv D v)) =
      iota (pv D v) (Kv D v) x := rfl

lemma toMul_pow (x : (Kv D v)ˣ) (n : ℕ) : toMul D v (x ^ n) = n • toMul D v x := by
  unfold toMul
  rw [map_pow]
  rfl

/-- The image of `K_v^×` is fixed by `G_v`. -/
lemma toMul_fixed (σ : Gv D v) (x : (Kv D v)ˣ) : σ • toMul D v x = toMul D v x := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  apply congrArg Additive.ofMul
  apply Units.ext
  change σ (iota (pv D v) (Kv D v) x) = iota (pv D v) (Kv D v) x
  rw [← eL_apply]
  exact σ.commutes (eL (pv D v) (Kv D v) x)

lemma ord_toMul_pos (x : (Kv D v)ˣ) (hx : ‖(x : Kv D v)‖ < 1) :
    0 < PAdicGalois.ord (pv D v) (toMul D v x) := by
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  have hp : (1 : ℝ) < pv D v := by exact_mod_cast (Fact.out : (pv D v).Prime).one_lt
  have hlt := norm_iota_lt_one D v x hx
  have hpos : 0 < ‖iota (pv D v) (Kv D v) x‖ :=
    norm_pos_iff.mpr ((map_ne_zero _).mpr x.ne_zero)
  change 0 < -Real.logb (pv D v) ‖iota (pv D v) (Kv D v) x‖
  rw [neg_pos]
  exact Real.logb_neg hp hpos hlt

/-- **`τ^⊢_v = q̲_v^ℕ` is a characteristic splitting of `C^⊢_v`** at `v ∈ V^bad` (IUT I,
Example 3.2 (iv)) (the root `q̲_v ∈ K_v`: `qRootExists`). -/
theorem tauVdash_isCharSplitting_bad (hv : v ∈ D.VBad) :
    Model.IsCharSplitting
      (divB := divGal (Gv D v) (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
        (gammaVdash D v)) (tauVdash D v) := by
  have hq := qRootExists D v hv
  have hτ : tauElt D v = toMul D v hq.choose := by simp only [tauElt, dif_pos hv]
  have hℓ : (0 : ℝ) < 2 * D.ℓ := by
    have := D.prime.ℓ_prime.pos
    have : (0 : ℝ) < D.ℓ := by exact_mod_cast this
    linarith
  have hord : PAdicGalois.ord (pv D v) (toMul D v hq.choose) =
      PAdicGalois.ord (pv D v) (toMul D v (qv D v hv)) / (2 * D.ℓ) := by
    have hqx : toMul D v (qv D v hv) = (2 * D.ℓ) • toMul D v hq.choose := by
      rw [← toMul_pow]; exact congrArg _ hq.choose_spec.symm
    rw [hqx, map_nsmul, nsmul_eq_mul, eq_div_iff hℓ.ne']
    push_cast
    ring
  have hqlt : ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ < 1 := (D.localData.tateX v hv).t.norm_lt_one
  have hxlt : ‖((hq.choose : (Kv D v)ˣ) : Kv D v)‖ < 1 := by
    have h := hq.choose_spec
    have h' : ‖((hq.choose : (Kv D v)ˣ) : Kv D v)‖ ^ (2 * D.ℓ) < 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h]; exact hqlt
    by_contra hge
    push Not at hge
    exact absurd (one_le_pow₀ hge) (not_le.mpr h')
  have hΓ : gammaVdash D v = AddSubgroup.zmultiples (PAdicGalois.ord (pv D v) (tauElt D v)) := by
    rw [hτ, hord]; simp [gammaVdash, ordTau, hv]
  refine GaloisModel.isCharSplitting_piSplit _ (fun σ => ?_) ?_ hΓ
  · rw [hτ]; exact toMul_fixed D v σ _
  · rw [hτ]; exact ord_toMul_pos D v _ hxlt

end Theta

end PrimeStrip

end Multiradial

end Iut
