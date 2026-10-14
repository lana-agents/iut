/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.WallEquiv.Forms
import Iut.LogLink.Thm311Rest
import Iut.Concrete.Literal

/-!
# Non-derivability of Step (xi) from Theorem 3.11

**Theorem 3.11 of IUT III, as formalised here, does not imply Step (xi) of the proof of
Corollary 3.12.** We isolate everything the repository proves about genuine initial Θ-data at
the level of Theorem 3.11 into an abstract structure `Thm311Package`, in which the arithmetic
(the numbers `|log q|` and `log-vol(hull(VC(I)))`) is decoupled from the data, and show the
following.
Since Theorem 3.11 is a theorem of the model for every genuine `D` (`thm311_full_model`),
"Theorem 3.11 implies Step (xi)" for one fixed `D` is just `SSIneq D`; non-derivability is a
statement relative to such an abstraction. **Lean-checked**: no argument that uses only the
fields of `Thm311Package` proves Step (xi). **Audited, not a theorem**: that these fields exhaust
what the repository proves at the level of Theorem 3.11 (see below).

* **faithfulness** (`Thm311Package.ofThetaData`): every log-theta-lattice with unit-induced
  Kummer data over genuine initial Θ-data `D` gives a package, every field proved from the
  theorems of `main`; and Step (xi) of that package is Step (xi) of the lattice
  (`xi_ofThetaData_iff`);
* **the sharp form** (`xi_iff`): for every package, Step (xi) holds iff `(s − 1)·a ≤ V`, i.e.
  Step (xi) adds exactly the Scholze–Stix inequality to the package;
* **non-derivability** (`not_xi_family`, `exists_package_not_xi`, `not_forall_xi`): for all
  numbers compatible with what is proved (`family`), and explicitly for `ℓ = 7`, `a = 1`,
  `V = 1` (`(s − 1)·a = 11/3 > V`), there is a package in which every field holds and Step (xi)
  fails. Hence no argument that uses only the package's fields proves
  Step (xi); a proof of Step (xi) for all genuine `D` must use facts about `D` beyond them, and
  such a proof would give the ABC conjecture (`classicalABC_of_forall_xi`).

## The package

The numbers: the prime `ℓ` (prime, `ℓ ≥ 5`), `ℓ* = (ℓ − 1)/2`, `s = sFactor ℓ*`, the `q`-parameter
`log q > 0`, `a = |log q| = log q / (2ℓ)`, `V = log-vol(hull(VC(I)))` (IUT's container volume,
`Iut/Wall/Ind3.lean`), `R = −|log Θ|` (the log-volume of the hull of the Θ-pilot region). The
structure: an abstract region type with log-volume, adelic regions, the container `hull(VC(I))`
(field `cont`), the (Ind3)-choices (adelic subregions of `hull(VC(I))`; their log-volumes are
exactly `(−∞, V]`), the LGP-action of the identified-copies output law
(`vol(LGP·S) = −s·a + vol(S)`, outputs in the hull of the Θ-pilot region: `vol(LGP·S) ≤ R`), the
`q`-pilot region (`vol = −a`), the mono-analytic scalings with their volume shift, and the
log-theta-lattice `ℤ × ℤ` with Kummer identifications that are log-shell compatible and
volume-preserving (unit-inducedness, Theorem 3.11(ii), Proposition 3.9(iv)), Θ-links and
choices of Step 1 (nonempty: Lemma 4.1.7 of [LANA]); the multiradiality of Theorem 3.11(i) is a
field. The remaining conclusions of Theorem 3.11 and Theorem 1.5(v) proved in the model
(`LogLink.thm311_full_model`: Theorem 3.11(i), (ii)(a)–(c), (iii)(a)–(d), Theorem 1.5(v)) do
not involve the log-volumes or degrees of a package: they hold for every initial Θ-data and
every choice of Kummer data. They are recorded as the field `structural`: a closed
proposition, provable outright, which places no constraint on the other fields. Its numeric parts
(`Thm15v.horizScale`/`frobScale`: the factor `1/s`; `Thm311LGP.splitDeg`) refer to the quantified
`D`, not to the package's numbers; their package-level counterparts are `vol_lgp`,
`vol_qRegion`, `one_lt_s`, `hexagon`, `pilots_ne`. The value-group facts (the pilots `s·a` and
`a`, the hexagon `deg_Θ = s·(Θ-link)` with `s ≠ 1`, the non-isomorphism of the pilot objects of
the realified Frobenioid) are functions of `s` and `a` and are derived (`hexagon`, `pilots_ne`).

## Every relation between `a`, `V` and `R` is a field

The facts the repository proves about `ℓ`, `log q`, `|log q|`, `log-vol(hull(VC(I)))` and
`−|log Θ|` for all genuine `D` (audited over `Iut/`): `ℓ` prime, `ℓ ≥ 5`; `a = log q/(2ℓ) > 0`
(`absLogQ_pos`); the log-volume calculus (`logVol_integralRegion`, `logVol_archScale`,
`logVol_act`, `shift_mul`, `shift_qScale`); the (Ind3) volumes `(−∞, V]`
(`exists_ind3_logVol_iff`); the output law (`logVol_lgp`, `logVol_lgp_integral`); the hull
volumes `(−∞, R]` (`exists_adelic_iff`) and the realisation of the outputs in the hull
(`inHullOfImage_lgp`), which give `V − s·a ≤ R` (`V_sub_le_R`); the preservation of the
container by log-shell compatible scalings (`ThetaLink.act_hull_vcI`, field `logShell`);
`R ≤ R_lit` (`rhs_le_rhsLit`);
`vol(q-pilot region) = −a` (`logVol_qRegion`). All are fields or consequences of fields.
**Relations proved for the hull only through other numbers, argued harmless**:
`log-vol(VC(I)) ≤ V` (`logVol_vcI_le_logVol_hullOf`; `log-vol(VC(I))` is not a package number,
and the bound is an upper bound on it); the local formulas of `Iut/WallEquiv/VcI.lean` (the exact
prime packet terms `∑_c w_c·∑_j ρ_{c j}·log p` of `hull(VC(I))`, their tame values
`∑_c w_c·d_{I,c}·log p ≥ 0`, the lattice-sandwich bounds at the wild primes, the upper bound
`|I|·log(√2π)` at `∞`). These are bounds on `V` in terms of the ramification of `K` at the primes
of the container; none of them involves `ord_v(q)`, so none grows with `a`. The repository proves
no other relation coupling `V` with `a`. Every other
statement about these numbers is an equivalence with a hypothesis (the forms of the wall,
`Iut/WallEquiv`), the Corollary 3.12 variant `−a ≤ R` (a hypothesis, `Cor312VariantHolds`), a
computation of `a` and of the pilot degrees from the arithmetic of `D`
(`Iut/Arakelov/QPilot.lean`, consequence for the package: `a > 0`), or the IUT IV estimate
`R ≤ C'(D) − s'·a` with `s' < s` (`Theorem110Invariants.LocalEstimate.rhs_le`), which holds only
under the hypothesis `LocalEstimate` (from `TowerArithmetic D`) and gives an upper bound
`V ≤ (s − s')·a + C'(D)`. Upper bounds on `V` cannot force Step (xi): `family` realises **every**
`ℓ`, `log q > 0`, `V` and `R` with `V − s·a ≤ R`, and `not_xi_family` shows Step (xi) fails in it
whenever `V < (s − 1)·a`. Lower bounds on `V` that do not grow with `a` do not change this either:
`0 ≤ V` (mathematically from `O ⊆ I`, IUT III Proposition 1.2; not formalised globally) is
compatible with the failure of Step (xi) for every `ℓ` and `log q`
(`exists_package_not_xi_nonneg`), and so is every lower bound `L ≤ V` with `L` independent of
`a` (`exists_package_not_xi_ge`: the package with `V = L` and `a > L/(s − 1)`).

## What is and is not shown

Shown: the formalised content of Theorem 3.11 (with unit-induced Kummer identifications) is
consistent with the failure of Step (xi) and with Step (xi) itself (`exists_package_not_xi`,
`exists_package_xi`): Step (xi) is independent of it, and equivalent to the Scholze–Stix
inequality over it. **Not shown**: that Step (xi) fails for some genuine `D`, or
that ABC fails; the package is a model, and the modelling inputs of the repository apply
(local fields in place of Frobenioids, Hodge theaters with data strips, the identified-copies
output law, see `Iut/WallEquiv/README.md`).
-/

namespace Iut

namespace WallEquiv

namespace NonDerivable

open Wall LogLink

noncomputable section

/-- **The formalised content of IUT III, Theorem 3.11, with the arithmetic decoupled** (see the
module docstring). -/
structure Thm311Package where
  /-- The prime `ℓ` of the Θ-data. -/
  ell : ℕ
  ell_prime : ell.Prime
  five_le_ell : 5 ≤ ell
  /-- `log q > 0` (the `q`-parameter). -/
  logQ : ℝ
  /-- `a = |log q| = log q / (2ℓ)`, the `q`-pilot degree. -/
  a : ℝ
  a_eq : a = logQ / (2 * ell)
  a_pos : 0 < a
  /-- `V = log-vol(hull(VC(I)))`, the log-volume of IUT's container. -/
  V : ℝ
  /-- `R = −|log Θ|`, the log-volume of the hull of the Θ-pilot region. -/
  R : ℝ
  /-- The regions of the procession, with log-volume and adelicity. -/
  Reg : Type
  vol : Reg → ℝ
  Adelic : Reg → Prop
  /-- Inclusion of regions. -/
  Sub : Reg → Reg → Prop
  /-- The container `hull(VC(I))` (the holomorphic hull of the log-shell container). -/
  cont : Reg
  adelic_cont : Adelic cont
  vol_cont : vol cont = V
  /-- The (Ind3)-choices are the adelic subregions of `hull(VC(I))`; their log-volumes are
  exactly `(−∞, V]`. -/
  ind3_le : ∀ S, Adelic S → Sub S cont → vol S ≤ V
  ind3_exists : ∀ x ≤ V, ∃ S, Adelic S ∧ Sub S cont ∧ vol S = x
  /-- The identified-copies output law `LGP·S`. -/
  lgp : Reg → Reg
  adelic_lgp : ∀ S, Adelic S → Adelic (lgp S)
  vol_lgp : ∀ S, Adelic S → vol (lgp S) = -(sFactor ((ell - 1) / 2) * a) + vol S
  /-- The integral region (log-volume `0`) and the archimedean scalings (adding `log t`). -/
  integral : Reg
  adelic_integral : Adelic integral
  vol_integral : vol integral = 0
  archScale : ℝ → Reg → Reg
  adelic_archScale : ∀ t, 0 < t → ∀ U, Adelic U → Adelic (archScale t U)
  vol_archScale : ∀ t, 0 < t → ∀ U, Adelic U → vol (archScale t U) = vol U + Real.log t
  /-- The regions in the hull of a single (Ind1)-image of the Θ-pilot region; their log-volumes
  are exactly `(−∞, R]`. -/
  InHull : Reg → Prop
  hull_le : ∀ U, Adelic U → InHull U → vol U ≤ R
  hull_exists : ∀ x ≤ R, ∃ U, Adelic U ∧ InHull U ∧ vol U = x
  /-- (T3) realisation: the outputs `LGP·S` lie in such a hull. -/
  lgp_inHull : ∀ S, Adelic S → Sub S cont → InHull (lgp S)
  /-- The right-hand side in the literal reading of Corollary 3.12 dominates `R`. -/
  Rlit : ℝ
  R_le_Rlit : R ≤ Rlit
  /-- The `q`-pilot region. -/
  qRegion : Reg
  adelic_qRegion : Adelic qRegion
  vol_qRegion : vol qRegion = -a
  /-- The mono-analytic scalings, acting on regions with a volume shift. -/
  Scal : Type
  [group : Group Scal]
  act : Scal → Reg → Reg
  act_one : ∀ S, act 1 S = S
  act_mul : ∀ g h S, act (g * h) S = act g (act h S)
  adelic_act : ∀ g S, Adelic S → Adelic (act g S)
  shift : Scal → ℝ
  shift_mul : ∀ g h, shift (g * h) = shift g + shift h
  vol_act : ∀ g S, Adelic S → vol (act g S) = vol S + shift g
  act_lgp : ∀ g S, act g (lgp S) = lgp (act g S)
  /-- The scaling by `q` (shift `−a`). -/
  qScale : Scal
  shift_qScale : shift qScale = -a
  /-- The Kummer identifications of the vertices of the log-theta-lattice. -/
  kum : ℤ × ℤ → Scal
  /-- They are log-shell compatible (Theorem 3.11(ii)), hence preserve the container
  (`ThetaLink.act_hull_vcI`). -/
  logShell : ∀ v, act (kum v) cont = cont
  /-- They preserve log-volume (unit-induced: Proposition 3.9(iv), Theorem 3.11(ii)). -/
  volCompat : ∀ v, shift (kum v) = 0
  /-- The Θ-links (from the Θ-pilot of `v` to the `q`-pilot of `w`) and the choices of Step 1;
  both exist ([LANA], Lemma 4.1.7). -/
  ThetaLink : ℤ × ℤ → ℤ × ℤ → Type
  thetaLink_nonempty : ∀ v w, Nonempty (ThetaLink v w)
  Choice : ℤ × ℤ → ℤ × ℤ → Type
  choice_nonempty : ∀ v w, Nonempty (Choice v w)
  /-- Theorem 3.11(i), multiradiality: outputs through any two vertices, transported to a third,
  agree up to a bijection of the (Ind3)-choices (as regions). -/
  multiradial : ∀ v v' w S, Adelic S → Sub S cont → ∃ S', Adelic S' ∧ Sub S' cont ∧
    act (kum w * (kum v')⁻¹) (lgp S') = act (kum w * (kum v)⁻¹) (lgp S)
  /-- **The remaining conclusions of Theorem 3.11 and Theorem 1.5(v) in the model**: a closed
  proposition, provable outright (`thm311_full_model`), constraining nothing else in the package;
  its numeric parts concern the quantified `D` (see the module docstring). -/
  structural : ∀ (D : InitialThetaData.{0}) (L : LGPLattice D)
    (K : LatticeKummer L.toLogThetaLattice) (B : BiCoricKummer L.toLogThetaLattice)
    (M : MonoThetaKummer D),
      Thm311LGP L K ∧ Thm311iii L.toLogThetaLattice B M ∧ Thm15v L.toLogThetaLattice

namespace Thm311Package

variable (P : Thm311Package)

attribute [instance] Thm311Package.group

/-- `ℓ* = (ℓ − 1)/2`. -/
def ellStar : ℕ := (P.ell - 1) / 2

/-- The scale factor `s = (1² + ⋯ + ℓ*²)/ℓ*`. -/
def s : ℝ := sFactor P.ellStar

/-- The transport from the container of `v` to the container of `w`. -/
def transport (v w : ℤ × ℤ) : P.Reg → P.Reg := P.act (P.kum w * (P.kum v)⁻¹)

/-- **Step (xi) for a package**: along every horizontal arrow `v → w` of the lattice and every
Θ-link, some choice and some (Ind3)-choice `S` give an output `LGP·S` whose transport to `w`
has the log-volume of the `q`-pilot region (as `XiPrinciple`, i.e. `WallOn horizRel`). The output
`LGP·S` does not depend on the choice `ι`, as in the model (`LatticeKummer.model_out`): the
identified-copies output law. -/
def Xi : Prop :=
  ∀ v w : ℤ × ℤ, horizRel v w → ∀ _gl : P.ThetaLink v w, ∃ (_ι : P.Choice w v) (S : P.Reg),
    P.Adelic S ∧ P.Sub S P.cont ∧ P.vol (P.transport v w (P.lgp S)) = P.vol P.qRegion

/-- **The Scholze–Stix inequality for a package**: `(s − 1)·a ≤ V`. -/
def SS : Prop := (P.s - 1) * P.a ≤ P.V

lemma two_le_ellStar : 2 ≤ P.ellStar := by
  have := P.five_le_ell
  unfold ellStar
  omega

lemma one_lt_s : 1 < P.s := one_lt_sFactor P.two_le_ellStar

/-- Outputs have log-volume at most `R`; with `S = hull(VC(I))`: `V − s·a ≤ R`. -/
theorem vol_lgp_le (S : P.Reg) (hS : P.Adelic S) (hsub : P.Sub S P.cont) :
    P.vol (P.lgp S) ≤ P.R :=
  P.hull_le _ (P.adelic_lgp S hS) (P.lgp_inHull S hS hsub)

theorem V_sub_le_R : P.V - P.s * P.a ≤ P.R := by
  obtain ⟨S, hS, hsub, hv⟩ := P.ind3_exists P.V le_rfl
  have := P.vol_lgp_le S hS hsub
  rw [P.vol_lgp S hS, hv] at this
  unfold s ellStar
  linarith

lemma shift_inv (g : P.Scal) : P.shift g⁻¹ = -P.shift g := by
  have h := P.shift_mul g⁻¹ g
  have h1 : P.shift 1 = 0 := by
    have := P.shift_mul 1 1
    rw [mul_one] at this
    linarith
  rw [inv_mul_cancel, h1] at h
  linarith

/-- Transports preserve log-volume (unit-inducedness). -/
theorem vol_transport (v w : ℤ × ℤ) {S : P.Reg} (hS : P.Adelic S) :
    P.vol (P.transport v w S) = P.vol S := by
  rw [transport, P.vol_act _ _ hS, P.shift_mul, P.shift_inv, P.volCompat, P.volCompat]
  ring

/-- **The sharp form**: in every package, Step (xi) is the Scholze–Stix inequality. -/
theorem xi_iff : P.Xi ↔ P.SS := by
  constructor
  · intro h
    obtain ⟨gl⟩ := P.thetaLink_nonempty (0, 0) (1, 0)
    obtain ⟨_, S, hS, hsub, hv⟩ := h (0, 0) (1, 0) rfl gl
    rw [P.vol_transport _ _ (P.adelic_lgp S hS), P.vol_lgp S hS, P.vol_qRegion] at hv
    have hle := P.ind3_le S hS hsub
    unfold SS s ellStar
    linarith
  · intro h v w _ _
    obtain ⟨S, hS, hsub, hv⟩ := P.ind3_exists ((P.s - 1) * P.a) h
    refine ⟨(P.choice_nonempty w v).some, S, hS, hsub, ?_⟩
    rw [P.vol_transport _ _ (P.adelic_lgp S hS), P.vol_lgp S hS, P.vol_qRegion, hv]
    unfold s ellStar
    ring

/-- The pilot degrees `s·a ≠ a` (the hexagon does not commute; the Θ-pilot and `q`-pilot objects
of the realified Frobenioid are not isomorphic). -/
theorem pilots_ne : P.s * P.a ≠ P.a := by
  intro h
  have := P.one_lt_s
  have ha := P.a_pos
  nlinarith

/-- **The hexagon** (`Wall.degTheta_eq_smul_thetaLink`): the output of the integral region has
`s` times the log-volume of the `q`-pilot region; it commutes (`s = 1`) for no package. -/
theorem hexagon : P.vol (P.lgp P.integral) = P.s * P.vol P.qRegion ∧ P.s ≠ 1 := by
  refine ⟨?_, P.one_lt_s.ne'⟩
  rw [P.vol_lgp _ P.adelic_integral, P.vol_integral, P.vol_qRegion]
  unfold s ellStar
  ring

/-- The Corollary 3.12 variant `−a ≤ R` follows from Step (xi) (as `variant_of_thm311`). -/
theorem variant_of_xi (h : P.Xi) : -P.a ≤ P.R := by
  have hss := P.xi_iff.mp h
  obtain ⟨S, hS, hsub, hv⟩ := P.ind3_exists ((P.s - 1) * P.a) hss
  have := P.vol_lgp_le S hS hsub
  rw [P.vol_lgp S hS, hv] at this
  unfold s ellStar at this
  linarith

end Thm311Package

/-! ### Faithfulness -/

open Thm311Package

/-- The (Ind3)-choice given by an adelic subregion of the container `hull(VC(I))`. -/
def toInd3 (D : InitialThetaData.{0}) (S : Region D) (hS : IsAdelic D S)
    (hsub : ∀ i, S i ≤ hullOf D (vcI D) i) : Ind3 D :=
  ⟨S, hS, hsub⟩

/-- **The package of a log-theta-lattice with unit-induced Kummer data over genuine initial
Θ-data**: every field is a theorem of the repository. -/
def ofThetaData (D : InitialThetaData.{0}) {L : LogThetaLattice D} (K : LatticeKummer L) :
    Thm311Package where
  ell := D.ℓ
  ell_prime := D.prime.ℓ_prime
  five_le_ell := D.prime.five_le
  logQ := D.qPilot.logQ
  a := D.qPilot.absLogQ
  a_eq := rfl
  a_pos := absLogQ_pos D
  V := logVol D (hullOf D (vcI D))
  R := (concreteVariantData D).rhsData.rhs
  Reg := Region D
  vol := logVol D
  Adelic := IsAdelic D
  Sub S T := ∀ i, S i ≤ T i
  cont := hullOf D (vcI D)
  adelic_cont := isAdelic_hullOf_vcI D
  vol_cont := rfl
  ind3_le S hS hsub := logVol_le_vcI D ⟨S, hS, hsub⟩
  ind3_exists x hx := by
    obtain ⟨S, hS⟩ := (exists_ind3_logVol_iff D x).mpr hx
    exact ⟨S.1, S.2.1, S.2.2, hS⟩
  lgp := lgp D
  adelic_lgp _ hS := isAdelic_lgp D hS
  vol_lgp S hS := by rw [logVol_lgp D hS, logVol_lgp_integral]
  integral := integralRegion D
  adelic_integral := isAdelic_integralRegion D
  vol_integral := logVol_integralRegion D
  archScale := archScale D
  adelic_archScale _ ht _ hU := isAdelic_archScale D ht hU
  vol_archScale _ ht _ hU := logVol_archScale D ht hU
  InHull := InHullOfImage D
  hull_le _ hU hI := logVol_le_rhs D hU hI
  hull_exists x hx := (exists_adelic_iff D x).mpr hx
  lgp_inHull S hS hsub := inHullOfImage_lgp D ⟨S, hS, hsub⟩
  Rlit := D.rhsDataLit.rhs
  R_le_Rlit := D.rhs_le_rhsLit
  qRegion := qRegion D
  adelic_qRegion := isAdelic_qRegion D
  vol_qRegion := logVol_qRegion D
  Scal := Scaling D
  act := act D
  act_one := act_one D
  act_mul := act_mul D
  adelic_act g _ hS := isAdelic_act D g hS
  shift := shift D
  shift_mul := shift_mul D
  vol_act g _ hS := by rw [logVol_act D g hS, add_comm]
  act_lgp := act_lgp
  qScale := qScale D
  shift_qScale := shift_qScale D
  kum := K.kum
  logShell v := ThetaLink.act_hull_vcI D (K.logShellCompat v)
  volCompat := K.model_kummerVolCompat
  ThetaLink v w := BPS.Iso (K.model.alg.thetaBPS v) (K.model.alg.qBPS w)
  thetaLink_nonempty := K.model.alg.nonempty_thetaLink
  Choice w v := K.model.alg.Choice (K.model.alg.qBPS w) v
  choice_nonempty w v := K.model.alg.nonempty_choice v w
  multiradial v v' w S hS hsub := by
    obtain ⟨τ, hτ⟩ := K.model_multiradial3 v v' w
      (K.model.alg.nonempty_choice v w).some (K.model.alg.nonempty_choice v' w).some
    have := hτ ⟨S, hS, hsub⟩
    exact ⟨(τ ⟨S, hS, hsub⟩).1, (τ ⟨S, hS, hsub⟩).2.1, (τ ⟨S, hS, hsub⟩).2.2, this.symm⟩
  structural _ L K B M :=
    have h := thm311_full_model L K B M
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem ss_ofThetaData_iff (D : InitialThetaData.{0}) {L : LogThetaLattice D}
    (K : LatticeKummer L) : (ofThetaData D K).SS ↔ SSIneq D := Iff.rfl

/-- **Step (xi) of the package of a lattice is Step (xi) of the lattice.** -/
theorem xi_ofThetaData_iff (D : InitialThetaData.{0}) {L : LogThetaLattice D}
    (K : LatticeKummer L) : (ofThetaData D K).Xi ↔ XiPrinciple K := by
  rw [xi_iff, ss_ofThetaData_iff, xi_iff_ss (thm311_model L K)]

/-! ### Non-derivability -/

/-- **The packages with prescribed numbers**: for every prime `ℓ ≥ 5`, every `log q > 0` and
every `V`, `R` with `V − s·a ≤ R` (the only proved relation coupling `V` with `a` and `R`), a
package with exactly these numbers: regions are their log-volumes, `LGP` is the shift by `−s·a`,
the Kummer identifications are trivial. -/
def family (ell : ℕ) (hp : ell.Prime) (h5 : 5 ≤ ell) (logQ : ℝ) (hq : 0 < logQ) (V R : ℝ)
    (hVR : V - sFactor ((ell - 1) / 2) * (logQ / (2 * ell)) ≤ R) : Thm311Package where
  ell := ell
  ell_prime := hp
  five_le_ell := h5
  logQ := logQ
  a := logQ / (2 * ell)
  a_eq := rfl
  a_pos := div_pos hq (by have : (0 : ℝ) < ell := by exact_mod_cast hp.pos
                          linarith)
  V := V
  R := R
  Reg := ℝ
  vol := id
  Adelic _ := True
  Sub x y := x ≤ y
  cont := V
  adelic_cont := trivial
  vol_cont := rfl
  ind3_le _ _ h := h
  ind3_exists x hx := ⟨x, trivial, hx, rfl⟩
  lgp x := -(sFactor ((ell - 1) / 2) * (logQ / (2 * ell))) + x
  adelic_lgp _ _ := trivial
  vol_lgp _ _ := rfl
  integral := 0
  adelic_integral := trivial
  vol_integral := rfl
  archScale t x := x + Real.log t
  adelic_archScale _ _ _ _ := trivial
  vol_archScale _ _ _ _ := rfl
  InHull x := x ≤ R
  hull_le _ _ h := h
  hull_exists x hx := ⟨x, trivial, hx, rfl⟩
  lgp_inHull x _ hx := by linarith
  Rlit := R
  R_le_Rlit := le_rfl
  qRegion := -(logQ / (2 * ell))
  adelic_qRegion := trivial
  vol_qRegion := rfl
  Scal := Multiplicative ℝ
  act g x := x + Multiplicative.toAdd g
  act_one _ := by simp
  act_mul g h x := by simp only [toAdd_mul]; ring
  adelic_act _ _ _ := trivial
  shift := Multiplicative.toAdd
  shift_mul _ _ := toAdd_mul _ _
  vol_act _ _ _ := rfl
  act_lgp g x := by ring
  qScale := Multiplicative.ofAdd (-(logQ / (2 * ell)))
  shift_qScale := rfl
  kum _ := 1
  logShell _ := by simp
  volCompat _ := rfl
  ThetaLink _ _ := Unit
  thetaLink_nonempty _ _ := ⟨()⟩
  Choice _ _ := Unit
  choice_nonempty _ _ := ⟨()⟩
  multiradial _ _ _ S _ hsub := ⟨S, trivial, hsub, rfl⟩
  structural _ L K B M :=
    have h := thm311_full_model L K B M
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Step (xi) fails in the family exactly when the Scholze–Stix inequality fails**: for every
prime `ℓ ≥ 5`, `log q > 0` and `V < (s − 1)·a` (any `R ≥ V − s·a`), the package with these numbers
satisfies every field and not Step (xi). In particular every upper bound on `V` or `R` (such as
the conditional IUT IV estimate `LocalEstimate.rhs_le`) is compatible with the failure of
Step (xi). -/
theorem not_xi_family (ell : ℕ) (hp : ell.Prime) (h5 : 5 ≤ ell) (logQ : ℝ) (hq : 0 < logQ)
    (V R : ℝ) (hVR : V - sFactor ((ell - 1) / 2) * (logQ / (2 * ell)) ≤ R)
    (hV : V < (sFactor ((ell - 1) / 2) - 1) * (logQ / (2 * ell))) :
    ¬ (family ell hp h5 logQ hq V R hVR).Xi := fun h => by
  have h' := (family ell hp h5 logQ hq V R hVR).xi_iff.mp h
  exact absurd h' (not_le.mpr hV)

/-- **An explicit package in which Step (xi) fails**: `ℓ = 7`, `log q = 14` (`a = 1`, `s = 14/3`),
`V = R = 1`; here `(s − 1)·a = 11/3 > 1 = V`. -/
def counterexample : Thm311Package :=
  family 7 (by norm_num) (by norm_num) 14 (by norm_num) 1 1 (by
    have := one_lt_sFactor (n := (7 - 1) / 2) (by norm_num)
    norm_num
    linarith)

/-- **There is a package in which Step (xi) fails.** -/
theorem exists_package_not_xi : ∃ P : Thm311Package, ¬ P.Xi := by
  refine ⟨counterexample, not_xi_family 7 (by norm_num) (by norm_num) 14 (by norm_num) 1 1 _ ?_⟩
  rw [sFactor_eq (by norm_num)]
  norm_num

/-- **There is a package in which Step (xi) holds** (`ℓ = 7`, `a = 1`, `V = R = 4`): Step (xi)
is independent of the package, not refutable from it. -/
theorem exists_package_xi : ∃ P : Thm311Package, P.Xi := by
  have hs : sFactor ((7 - 1) / 2) = 14 / 3 := by rw [sFactor_eq (by norm_num)]; norm_num
  refine ⟨family 7 (by norm_num) (by norm_num) 14 (by norm_num) 4 4 (by rw [hs]; norm_num), ?_⟩
  refine (Thm311Package.xi_iff _).mpr ?_
  change (sFactor ((7 - 1) / 2) - 1) * (14 / (2 * ((7 : ℕ) : ℝ))) ≤ 4
  rw [hs]
  norm_num

/-- **Step (xi) fails with `0 ≤ V`, for every `ℓ` and `log q`**: the package of `family` with
`V = R = 0`. -/
theorem exists_package_not_xi_nonneg (ell : ℕ) (hp : ell.Prime) (h5 : 5 ≤ ell) (logQ : ℝ)
    (hq : 0 < logQ) :
    ∃ P : Thm311Package, P.ell = ell ∧ P.logQ = logQ ∧ 0 ≤ P.V ∧ ¬ P.Xi := by
  have hs : 1 < sFactor ((ell - 1) / 2) := one_lt_sFactor (by omega)
  have hl : (0 : ℝ) < ell := by exact_mod_cast hp.pos
  have ha : 0 < logQ / (2 * ell) := div_pos hq (by linarith)
  have hVR : (0 : ℝ) - sFactor ((ell - 1) / 2) * (logQ / (2 * ell)) ≤ 0 := by nlinarith
  refine ⟨family ell hp h5 logQ hq 0 0 hVR, rfl, rfl, le_rfl,
    not_xi_family ell hp h5 logQ hq 0 0 hVR (by nlinarith)⟩

/-- **Step (xi) fails above every lower bound on `V`**: for every `ℓ` and every `L` there is a
package with `V = L` (and `log q` large) in which Step (xi) fails. So a lower bound on
`V = log-vol(hull(VC(I)))` that does not grow with `a = |log q|` cannot force Step (xi). -/
theorem exists_package_not_xi_ge (ell : ℕ) (hp : ell.Prime) (h5 : 5 ≤ ell) (L : ℝ) :
    ∃ P : Thm311Package, P.ell = ell ∧ L ≤ P.V ∧ ¬ P.Xi := by
  have hs : 1 < sFactor ((ell - 1) / 2) := one_lt_sFactor (by omega)
  have hl : (0 : ℝ) < ell := by exact_mod_cast hp.pos
  set a : ℝ := (|L| + 1) / (sFactor ((ell - 1) / 2) - 1) with ha_def
  have ha : 0 < a := div_pos (by positivity) (by linarith)
  have hq : 0 < 2 * ell * a := by positivity
  have hqa : 2 * ell * a / (2 * ell) = a := by field_simp
  have hsa : (sFactor ((ell - 1) / 2) - 1) * a = |L| + 1 := by
    rw [ha_def]
    have : sFactor ((ell - 1) / 2) - 1 ≠ 0 := by linarith
    field_simp
  have hVR : L - sFactor ((ell - 1) / 2) * (2 * ell * a / (2 * ell)) ≤ L := by
    rw [hqa]
    nlinarith
  refine ⟨family ell hp h5 (2 * ell * a) hq L L hVR, rfl, le_rfl,
    not_xi_family ell hp h5 _ hq L L hVR ?_⟩
  rw [hqa, hsa]
  linarith [le_abs_self L]

/-- **Non-derivability**: Step (xi) does not follow from the formalised content of Theorem 3.11
(the fields of `Thm311Package`). -/
theorem not_forall_xi : ¬ ∀ P : Thm311Package, P.Xi := fun h =>
  exists_package_not_xi.elim fun P hP => hP (h P)

/-- **Step (xi) for all genuine data gives the ABC conjecture** (`classicalABC_of_thm311`), so
the input beyond the package that a proof of Step (xi) needs is of ABC strength. -/
theorem classicalABC_of_forall_xi (L : ∀ D : InitialThetaData.{0}, LogThetaLattice D)
    (K : ∀ D, LatticeKummer (L D)) (hx : ∀ D, (ofThetaData D (K D)).Xi) : ClassicalABC :=
  classicalABC_of_thm311 L K (fun D => thm311_model (L D) (K D))
    fun D => (xi_ofThetaData_iff D (K D)).mp (hx D)

/-- **Summary**: the package is faithful (for genuine data its Step (xi) is the lattice's), Step
(xi) is equivalent to `(s − 1)·a ≤ V` over the package, and it is independent of the package
(neither it nor its negation is a consequence). -/
theorem nonDerivability :
    (∀ (D : InitialThetaData.{0}) (L : LogThetaLattice D) (K : LatticeKummer L),
      (ofThetaData D K).Xi ↔ XiPrinciple K) ∧
    (∀ P : Thm311Package, P.Xi ↔ (P.s - 1) * P.a ≤ P.V) ∧
    (¬ ∀ P : Thm311Package, P.Xi) ∧ (¬ ∀ P : Thm311Package, ¬ P.Xi) :=
  ⟨fun D _ K => xi_ofThetaData_iff D K, fun P => P.xi_iff, not_forall_xi,
    fun h => exists_package_xi.elim fun P hP => h P hP⟩

end

end NonDerivable

end WallEquiv

end Iut
