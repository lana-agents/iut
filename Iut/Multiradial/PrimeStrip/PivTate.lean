/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Anabelian.Genuine.TateChar
import Iut.Anabelian.AdicCompletion
import Iut.Cor312.ThetaData.ReductionNorm
import Iut.Cor312.ThetaData.TateStructureUnique
import Iut.Multiradial.PrimeStrip.Components

/-!
# The Tate characters of `Π_v` at `v ∈ V^bad` (MR18 run 17, T10)

IUT I, Definition 3.1 (e), (f): at `v ∈ V^bad`, `Π_v` is the tempered fundamental group of the
local model `X̲_v` (`Piv D v`), a curve of type `(1, ℓ-tors)` (`± = false`) whose elliptic curve
`E_v` carries the Tate structure `D.localData.tateX v hv` (a change of variables `C` with
`C • E_v = E_{q_v}`). [EtTh] §1 (`The Etale Theta Function …txt`, l.443–452): the dual graph of
the special fibre gives `Π^tp_X ↠ ℤ` with kernel `Π^tp_Y`; [EtTh] l.976–980: `Ÿ = Y_2 → Y`, the
double covering.

This file attaches to the genuine `Π_v` (no hypotheses beyond the Θ-data):

* `pivEquivTemp`: `Π_v ≃ₜ* Kummer.TempPi DG …`, `DG` the Galois data of `X̲_v`
  (`Orbicurve.temperedPi1EquivGalois`, `Genuine.subsingleton_A_false`);
* `tateDataV`: tfg's `TateObject.Data` of `X̲_v` in the coordinates of the Tate model
  `C • E_v = E_{q_v}` with `π = q_v^{1/2}` (`qRootExists`, IUT I, Example 3.2 (iv),
  l.4578–4583), `b₄ = a₄(q)/q`, `b₆ = a₆(q)/q`;
* **`chiV : Π_v →* ℤ`**, the graph character of the Tate model (`TateObject.character`),
  continuous;
* **`epsV : Π_v →* ℤ/2`**, the character of the étale double cover `√(x − e)` of `X̲_v`,
  `e = X(q_v^{1/2})` the `x`-coordinate of the rational `2`-torsion point `q_v^{1/2}`
  (`Genuine.TateChar.tempSign`), with open kernel;
* **`psiV = (chiV, epsV) : Π_v →* ℤ × ℤ/2`**, whose kernel is `Π_Ÿ = Π_Y ∩ Π_{X'}` (open).
-/

namespace Iut.Multiradial.PrimeStrip

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  TemperedFundamentalGroups Pi1.Orbifold WeierstrassCurve
  Iut.Anabelian TateCurvesTheta
open scoped Valued

noncomputable section

attribute [local instance low] Classical.propDecidable

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- `X̲_v` is a curve (`± = false`; IUT I, Definition 3.1 (d), `IsTypeOneEllTors`). -/
lemma Xv_pm : (Xv D v).pm = false := D.orb.XKu_type.2.2.1

/-- **The Galois data of `X̲_v`.** -/
abbrev DGv : GaloisData (Kv D v) (Genuine.xG (Xv D v).E) :=
  Genuine.galoisData (Xv D v).E (Xv D v).level (Xv D v).M false

/-- The valuation subring of `Ω` used by `Π_v`. -/
abbrev Vv : ValuationSubring (Genuine.Ω (Xv D v).E) :=
  Genuine.tempV (Xv D v).E (Xv D v).level (Xv D v).M false

lemma Vv_comap : (Vv D v).comap (algebraMap (Kv D v) (Genuine.Ω (Xv D v).E)) =
    canonicalValuationSubring (Kv D v) :=
  Genuine.tempV_comap _ _ _ _

/-- `Π_v` in its Galois presentation: `Kummer.TempPi` of the Galois data of `X̲_v`. -/
abbrev TempPiv : Type := Kummer.TempPi (DGv D v) (canonicalValuationSubring (Kv D v)) (Vv D v)
  (Vv_comap D v)

/-- Equal topological groups (as `TopGrp`) are isomorphic. -/
def TopGrp.equivOfEq {G G' : TopGrp} (h : G = G') : G.carrier ≃ₜ* G'.carrier := by
  subst h
  exact ContinuousMulEquiv.refl _

lemma piData_fst_of_bad (hv : v ∈ D.VBad) : (piData D v).1 = ⟨(Xv D v).temperedPi1⟩ := by
  unfold piData
  simp only [if_pos hv]

/-- **`Π_v ≃ₜ* Kummer.TempPi DG …` at `v ∈ V^bad`.** -/
def pivEquivTemp (hv : v ∈ D.VBad) : (Piv D v).carrier ≃ₜ* TempPiv D v :=
  (TopGrp.equivOfEq (piData_fst_of_bad D v hv)).trans
    ((Xv D v).temperedPi1EquivGalois (Xv_pm D v))

/-! ### The Tate model of `X̲_v` -/

variable {D v} (hv : v ∈ D.VBad)

/-- The Tate structure of `X̲_v`. -/
abbrev tateS : TateStructure (Xv D v).E := D.localData.tateX v hv

/-- `s_v = q_v^{1/2} = (q_v^{1/2ℓ})^ℓ`. -/
def sv : (Kv D v)ˣ := (qRootExists D v hv).choose ^ D.ℓ

lemma sv_sq : sv hv ^ 2 = qv D v hv := by
  rw [sv, ← pow_mul]
  exact (congrArg ((qRootExists D v hv).choose ^ ·) (Nat.mul_comm D.ℓ 2)).trans
    (qRootExists D v hv).choose_spec

lemma val_sv_lt_one : Valued.v ((sv hv : Kv D v)) < 1 := by
  have hq : ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ < 1 := (tateS hv).t.norm_lt_one
  have h2 : ‖((sv hv : (Kv D v)ˣ) : Kv D v)‖ ^ 2 < 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, sv_sq]; exact hq
  rw [← norm_lt_one_iff_valued]
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

lemma mem_canonical_iff (x : Kv D v) :
    x ∈ canonicalValuationSubring (Kv D v) ↔ ‖x‖ ≤ 1 := by
  rw [AdicCompletion.canonicalValuationSubring_eq, norm_le_one_iff_valued]
  exact mem_adicCompletionIntegers _ _ _

/-- `π = s_v ∈ O_v`. -/
def piV : canonicalValuationSubring (Kv D v) :=
  ⟨sv hv, (mem_canonical_iff _).2 ((norm_le_one_iff_valued _ _).2 (val_sv_lt_one hv).le)⟩

/-- `π = s_v` is not a unit of `O_v`. -/
lemma piV_mem_maximalIdeal :
    piV hv ∈ IsLocalRing.maximalIdeal (canonicalValuationSubring (Kv D v)) := by
  refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_
  obtain ⟨u, hu⟩ := hu
  have h1 : ‖(((u⁻¹ : (canonicalValuationSubring (Kv D v))ˣ) :
      canonicalValuationSubring (Kv D v)) : Kv D v)‖ ≤ 1 :=
    (mem_canonical_iff _).1 ((u⁻¹ : (canonicalValuationSubring (Kv D v))ˣ) :
      canonicalValuationSubring (Kv D v)).2
  have h2 : ‖((sv hv : (Kv D v)ˣ) : Kv D v)‖ < 1 :=
    (norm_lt_one_iff_valued _ _).2 (val_sv_lt_one hv)
  have h3 : ((sv hv : (Kv D v)ˣ) : Kv D v) * (((u⁻¹ : (canonicalValuationSubring (Kv D v))ˣ) :
      canonicalValuationSubring (Kv D v)) : Kv D v) = 1 := by
    have := congrArg Subtype.val u.mul_inv
    rw [hu] at this
    exact this
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((sv hv : (Kv D v)ˣ) : Kv D v)]

lemma norm_div_q_le {a : Kv D v} (ha : ‖a‖ ≤ ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖) :
    ‖a / ((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ≤ 1 := by
  rw [norm_div]
  exact div_le_one_of_le₀ ha (norm_nonneg _)

/-- `b₄ = a₄(q)/q ∈ O_v`. -/
def b₄V : canonicalValuationSubring (Kv D v) :=
  ⟨(tateS hv).t.a₄ / (qv D v hv : Kv D v), (mem_canonical_iff _).2
    (norm_div_q_le hv (tateS hv).t.norm_a₄_le)⟩

/-- `b₆ = a₆(q)/q ∈ O_v`. -/
def b₆V : canonicalValuationSubring (Kv D v) :=
  ⟨(tateS hv).t.a₆ / (qv D v hv : Kv D v), (mem_canonical_iff _).2
    (norm_div_q_le hv ((tateS hv).t.norm_a₆_le (twelve_ne_zero _)))⟩

lemma sv_sq_val : ((sv hv : Kv D v)) ^ 2 = (qv D v hv : Kv D v) := by
  rw [← Units.val_pow_eq_pow_val, sv_sq]

lemma q_ne_zero : (qv D v hv : Kv D v) ≠ 0 := (qv D v hv).ne_zero

/-- **The Tate data of `X̲_v`** in the coordinates of its Tate model. -/
def tateDataV : TateObject.Data (canonicalValuationSubring (Kv D v)) (DGv D v).R :=
  Genuine.tateData (Xv D v).level (Xv D v).M false (tateS hv).C (piV hv) (b₄V hv) (b₆V hv)
    (fun h => (sv hv).ne_zero (congrArg Subtype.val h))
    (piV_mem_maximalIdeal hv)
    (by rw [(tateS hv).hC]; rfl) (by rw [(tateS hv).hC]; rfl) (by rw [(tateS hv).hC]; rfl)
    (by
      rw [(tateS hv).hC]
      change (tateS hv).t.a₄ = ((sv hv : Kv D v)) ^ 2 * ((tateS hv).t.a₄ / (qv D v hv : Kv D v))
      rw [sv_sq_val]
      field_simp [q_ne_zero hv])
    (by
      rw [(tateS hv).hC]
      change (tateS hv).t.a₆ = ((sv hv : Kv D v)) ^ 2 * ((tateS hv).t.a₆ / (qv D v hv : Kv D v))
      rw [sv_sq_val]
      field_simp [q_ne_zero hv])

/-! ### The rational `2`-torsion point `s_v` and the Kummer data of `√(x − e)` -/

lemma sv_notMem : sv hv ∉ Subgroup.zpowers (tateS hv).t.q := by
  rintro ⟨n, hn⟩
  have hn' : (qv D v hv) ^ n = sv hv := hn
  have hpos : 0 < ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ := norm_pos_iff.2 (q_ne_zero hv)
  have hlt : ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ < 1 := (tateS hv).t.norm_lt_one
  have e1 : ‖((sv hv : (Kv D v)ˣ) : Kv D v)‖ = ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ^ n := by
    rw [← hn', Units.val_zpow_eq_zpow_val, norm_zpow]
  have e2 : ‖((sv hv : (Kv D v)ˣ) : Kv D v)‖ ^ 2 = ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ := by
    rw [← norm_pow, sv_sq_val]
  have h3 : ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ^ (2 * n) =
      ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ^ (1 : ℤ) := by
    calc ‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ^ (2 * n)
        = (‖((qv D v hv : (Kv D v)ˣ) : Kv D v)‖ ^ n) ^ ((2 : ℕ) : ℤ) := by
          rw [← zpow_mul, mul_comm]; rfl
      _ = ‖((sv hv : (Kv D v)ˣ) : Kv D v)‖ ^ 2 := by rw [e1, zpow_natCast]
      _ = _ := by rw [e2, zpow_one]
  have := zpow_right_injective₀ hpos hlt.ne h3
  omega

/-- The `2`-torsion point `s_v ∈ K_v^×/q^ℤ ≅ E_v(K_v)`. -/
abbrev Pv : (Xv D v).E.toAffine.Point := (tateS hv).ofUnit (sv hv)

lemma Pv_ne_zero : Pv hv ≠ 0 := (tateS hv).ofUnit_ne_zero (sv_notMem hv)

lemma neg_Pv : -Pv hv = Pv hv := by
  rw [← TateStructure.ofUnit_inv, TateStructure.ofUnit_eq_iff]
  refine ⟨1, ?_⟩
  have hq : (tateS hv).t.q = qv D v hv := rfl
  rw [hq, zpow_one, ← sv_sq]
  group

/-- `e = X(s_v)`, the `x`-coordinate of `P_v` in the Tate model. -/
abbrev eV : Kv D v := xCoord (tateS hv).C (Pv hv)

/-- `f = Y(s_v)`. -/
abbrev fV : Kv D v := yCoord (tateS hv).C (Pv hv)

lemma hC₁ : ((tateS hv).C • (Xv D v).E).a₁ = 1 := by rw [(tateS hv).hC]; rfl
lemma hC₂ : ((tateS hv).C • (Xv D v).E).a₂ = 0 := by rw [(tateS hv).hC]; rfl
lemma hC₃ : ((tateS hv).C • (Xv D v).E).a₃ = 0 := by rw [(tateS hv).hC]; rfl

lemma two_fV_add_eV : 2 * fV hv + eV hv = 0 := by
  have h := yCoord_neg (tateS hv).C (Pv_ne_zero hv)
  rw [neg_Pv] at h
  have h' : fV hv = -fV hv - ((tateS hv).C • (Xv D v).E).a₁ * eV hv -
      ((tateS hv).C • (Xv D v).E).a₃ := h
  rw [hC₁, hC₃] at h'
  linear_combination h'

lemma equation_eV_fV : ((tateS hv).C • (Xv D v).E).toAffine.Equation (eV hv) (fV hv) := by
  have hP := Pv_ne_zero hv
  change ((tateS hv).C • (Xv D v).E).toAffine.Equation (xCoord (tateS hv).C (Pv hv))
    (yCoord (tateS hv).C (Pv hv))
  generalize Pv hv = Q at hP ⊢
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rw [Affine.equation_iff]
    have h1 := h.1
    rw [Affine.equation_iff] at h1
    have := (Genuine.equation_variableChange (E := (Xv D v).E) (RingHom.id _) (tateS hv).C
      (x := x) (y := y) (by simpa using h1))
    simp only [RingHom.id_apply] at this
    simp only [xCoord, yCoord]
    linear_combination this

lemma kummer_dV :
    fV hv ^ 2 + eV hv * fV hv = eV hv ^ 3 + ((tateS hv).C • (Xv D v).E).a₄ * eV hv +
        ((tateS hv).C • (Xv D v).E).a₆ ∧
      3 * eV hv ^ 2 + eV hv / 2 + ((tateS hv).C • (Xv D v).E).a₄ ≠ 0 :=
  Genuine.two_torsion_data (hC₁ hv) (hC₂ hv) (hC₃ hv) (equation_eV_fV hv) (two_fV_add_eV hv)

/-- `c = x − e ∈ R`. -/
abbrev cV : (DGv D v).R := Genuine.cR (Xv D v).level (Xv D v).M false (tateS hv).C (eV hv)

/-- A square root `√c ∈ Ω`. -/
def gammaV : Genuine.Ω (Xv D v).E :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap (DGv D v).R (Genuine.Ω (Xv D v).E) (cV hv))
    two_pos).choose

lemma gammaV_sq : gammaV hv ^ 2 = algebraMap (DGv D v).R _ (cV hv) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap (DGv D v).R (Genuine.Ω (Xv D v).E) (cV hv))
    two_pos).choose_spec

lemma gammaV_ne_zero : gammaV hv ≠ 0 := by
  intro h
  have h' := gammaV_sq hv
  rw [h, zero_pow two_ne_zero, eq_comm] at h'
  exact Genuine.cR_ne_zero _ _ (CoordRing.algebraMap_injective (h'.trans (map_zero _).symm))

lemma gammaV_sq_fix : ∀ σ ∈ (DGv D v).H, (σ : _ ≃ₐ[_] _) (gammaV hv ^ 2) = gammaV hv ^ 2 :=
  fun σ hσ => by rw [gammaV_sq]; exact TateChar.fix_R_of_mem_HL (DGv D v) hσ _

lemma gammaV_fix_S : ∀ σ ∈ (DGv D v).S, σ (gammaV hv) = gammaV hv := fun _ hσ =>
  TateChar.fix_sqrt_of_mem_S (DGv D v) (Genuine.aR_mul_add (kummer_dV hv).2)
    (Genuine.hR_sq (hC₁ hv) (hC₂ hv) (hC₃ hv) (kummer_dV hv).1 (two_fV_add_eV hv))
    (Genuine.cR_ne_zero _ _) (gammaV_sq hv) hσ

/-! ### The characters -/

/-- **The graph character `χ_v : Π_v → ℤ`** (in the Galois presentation) of the Tate model. -/
def chiTemp : TempPiv D v →* Multiplicative ℤ :=
  TateObject.character (A := (DGv D v).A) (tateDataV hv) (Vv D v) (Vv_comap D v)

/-- **The character `ε_v : Π_v → ℤ/2` of the étale double cover `√(x − e)`.** -/
def epsTemp : TempPiv D v →* Multiplicative (ZMod 2) :=
  TateChar.tempSign (DGv D v) (gammaV_ne_zero hv) (gammaV_sq_fix hv) _ (Vv D v) (Vv_comap D v)
    (gammaV_fix_S hv)

/-- **`ψ_v = (χ_v, ε_v) : Π_v → ℤ × ℤ/2`** on the genuine `Π_v`. -/
def psiV : (Piv D v).carrier →* Multiplicative ℤ × Multiplicative (ZMod 2) :=
  ((chiTemp hv).prod (epsTemp hv)).comp (pivEquivTemp D v hv).toMulEquiv.toMonoidHom

theorem continuous_chiTemp : Continuous (chiTemp hv) := TateObject.continuous_character _ _ _

theorem isOpen_ker_epsTemp : IsOpen ((epsTemp hv).ker : Set (TempPiv D v)) :=
  TateChar.isOpen_ker_tempSign _ _ _ _ _ _ _

/-- The kernel of `(χ, ε) ∘ e` is open if those of `χ` and `ε` are. -/
lemma isOpen_ker_prod_comp {G H A B : Type*} [Group G] [Group H] [Group A] [Group B]
    [TopologicalSpace G] [TopologicalSpace H] (e : G ≃ₜ* H) (χ : H →* A) (ε : H →* B)
    (hχ : IsOpen (χ.ker : Set H)) (hε : IsOpen (ε.ker : Set H)) :
    IsOpen (((χ.prod ε).comp e.toMulEquiv.toMonoidHom).ker : Set G) := by
  have h : (((χ.prod ε).comp e.toMulEquiv.toMonoidHom).ker : Set G) =
      e ⁻¹' ((χ.ker : Set H) ∩ ε.ker) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.prod_apply,
      Prod.mk_eq_one, Set.mem_preimage, Set.mem_inter_iff]
    rfl
  rw [h]
  exact (hχ.inter hε).preimage e.continuous

theorem isOpen_ker_chiTemp : IsOpen ((chiTemp hv).ker : Set (TempPiv D v)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage (continuous_chiTemp hv)

/-- **`Π_Ÿ = ker ψ_v` is open in `Π_v`.** -/
theorem isOpen_ker_psiV : IsOpen ((psiV hv).ker : Set (Piv D v).carrier) :=
  isOpen_ker_prod_comp (pivEquivTemp D v hv) (chiTemp hv) (epsTemp hv) (isOpen_ker_chiTemp hv)
    (isOpen_ker_epsTemp hv)

end

end Iut.Multiradial.PrimeStrip
