/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.PAdicGalois
import Iut.Concrete.LocalConstruct.LogShell
import Iut.Reconstruction.Cusp.GaloisConj
import Iut.Anabelian.Tempered
import Iut.Cor312.ThetaData.Basic
import CurvesJacobian.Cusp.OrbiQuotientPi1

/-!
# Local Galois data of the prime-strips (MR20 T1; IUT I, Definition 3.1 (e), Examples 3.2, 3.3)

For `v ∈ V^non` IUT I works with the local field `K_v`, the local model `X̲_v = X̲_K ×_K K_v`, its
(tempered at `V^bad`, profinite étale at `V^good`) fundamental group `Π_v`, and the absolute
Galois group `G_v = Gal(K̄_v / K_v)` (IUT I, Definition 3.1 (e): `Π_v ↠ G_v`, the quotient by the
geometric fundamental group `Δ_v`). The `p_v`-adic Frobenioids of IUT I, Examples 3.2 (iii), 3.3
(i), are built from the `G_v`-module `K̄_v^×` ([FrdII], Example 1.1 (ii)); iut's construction
(`Iut.Frobenioid.PAdicGalois`) uses `K̄ = \bar{ℚ}_p = PadicAlgCl p` and `K ⊆ \bar{ℚ}_p`.

This file supplies these local data for initial Θ-data `D`:

* **generic part** (any field `k` of characteristic `0` with a `ℚ_p`-algebra structure, algebraic
  over `ℚ_p`): the embedding `ι : k → \bar{ℚ}_p` (`PrimeStrip.iota`), its image `L = ι(k)`
  (`PrimeStrip.Lfield`) with `k ≃ L` (`PrimeStrip.eL`); for a model orbicurve `X` over `k`, the
  algebraic closure `k̄ = kbar X` of `k` in iut's field `Ω` of the genuine fundamental group, the
  restriction to the constants `resConst X : Gal(Ω / k(X)) →* Gal(k̄ / k)` (curves-jacobian's
  `galResConst`), trivial on inertia, hence **`piConstX X : π₁(X) →* Gal(k̄ / k)`**; the
  isomorphism `k̄ ≃ \bar{ℚ}_p` extending `ι` (`kbarEquiv`) and the induced
  `Gal(k̄ / k) ≃ₜ* Gal(\bar{ℚ}_p / L)` (`galK`); **`piToGX X : π₁(X) →* Gal(\bar{ℚ}_p / ι k)`**,
  continuous;
* **for `D` and `v ∈ V^non`** (`v` a finite place of `F_mod`, `v̲ = sectFin v` the place of `K`
  of the section): `Kv D v = K_{v̲}`, `pv D v` its residue characteristic, the `ℚ_p`-structure
  `LocalConstruct.padicAlgebra`, **`Lv D v = ι(K_v) ⊆ \bar{ℚ}_p`**,
  **`Gv D v = Gal(\bar{ℚ}_p / ι K_v)`**
  (lead decision 1 of the MR20 plan: `G_v` is the local Galois group, transported into
  `\bar{ℚ}_p`; the comparison with the decomposition group `decompGroup ⊆ Gal(F̄/K)` is MR22's),
  `Xv D v = X̲_v`, **`Piv D v`** (`Π_v`: the tempered fundamental group of `X̲_v` if
  `v ∈ V^bad`, the étale one otherwise; IUT I, Definition 3.1 (e)) and
  **`piToG D v : Π_v →* G_v`** (through the tempered-to-étale comparison at `V^bad`), continuous.

## Debt (H3 of the MR20 plan)

That `Π_v → G_v` is a quotient map — surjective, with open images of open subgroups — is the
exactness of `1 → Δ_v → Π_v → G_v → 1` on the right (geometric connectedness of `X̲_v` over `K_v`;
for the tempered group, at iut's canonical base point). It is **not proved** here: tfg's
`Kummer.tempQuotGk` (`Tempered/GaloisQuotient.lean`) proves it for tfg's tempered group at a base
point over a `k`-rational point, which is not yet identified with iut's `Orbicurve.temperedPi1`;
for the étale group the analogue of curves-jacobian's `galResConst_surjective_hemi` for the
orbicurves of type `(1, ℓ-tors)^±` is missing. It enters as the named `Prop`
**`PiToGQuotient D v`**, an explicit argument of the constructions that need it (recorded in
`MR20-plan.md`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open NumberField Iut.Anabelian Iut.Anabelian.Genuine Iut.Frobenioid

/-! ### `ι : k → \bar{ℚ}_p` -/

section Embed

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Algebra ℚ_[p] k]
  [Algebra.IsAlgebraic ℚ_[p] k]

/-- **A `ℚ_p`-embedding `ι : k → \bar{ℚ}_p`** (for `k` finite over `ℚ_p`, isometric:
`BAn.PadicEmbed.norm_algHom_padicAlgCl`). -/
def iota : k →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift

/-- **`L = ι(k) ⊆ \bar{ℚ}_p`**. -/
def Lfield : IntermediateField ℚ_[p] (PadicAlgCl p) := (iota p k).fieldRange

/-- `k ≃ ι(k)`. -/
def eL : k ≃ₐ[ℚ_[p]] Lfield p k := AlgEquiv.ofInjectiveField (iota p k)

lemma eL_apply (x : k) : ((eL p k x : Lfield p k) : PadicAlgCl p) = iota p k x := rfl

instance (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : Algebra.IsAlgebraic L (PadicAlgCl p) :=
  Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) L

instance (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : IsAlgClosure L (PadicAlgCl p) :=
  ⟨inferInstance, inferInstance⟩

end Embed

/-! ### `π₁(X) → Gal(k̄ / k)` -/

section ConstGal

variable {k : Type} [Field k] [CharZero k] (X : Orbicurve k)

/-- **`k̄`**: the algebraic closure of `k` in the field `Ω` of the genuine fundamental group of
`X`. -/
abbrev kbar : IntermediateField k (Ω X.E) := algebraicClosure k (Ω X.E)

instance : Algebra.IsAlgebraic k (kbar X) := IsAlgClosure.isAlgebraic

instance : T2Space (kbar X ≃ₐ[k] kbar X) := krullTopology_t2

/-- **Restriction to the constants** `Gal(Ω / k(X_M)) → Gal(k̄ / k)` (curves-jacobian's
`galResConst` along `Gal E ≃ Aut(Ω / k(x))`). -/
def resConst : Gal X.E →* (kbar X ≃ₐ[k] kbar X) :=
  (CurvesJacobian.Cusp.galResConst (xG X.E)).comp (galEquiv X.E).toMulEquiv.toMonoidHom

lemma continuous_resConst : Continuous (resConst X) :=
  (CurvesJacobian.Cusp.continuous_galResConst (xG X.E)).comp (galEquiv X.E).continuous

/-- **Inertia restricts trivially to the constants.** -/
lemma resConst_eq_one_of_mem {s : Gal X.E} (hs : s ∈ SgenC X.E X.level X.M) :
    resConst X s = 1 := by
  rw [SgenC_of_charZero] at hs
  obtain ⟨-, W, hk, -, hI⟩ := hs
  refine CurvesJacobian.Cusp.galResConst_eq_one_of_mem_inertia W hk ?_
  intro a ha
  change W.valuation ((galEquiv X.E s) a - a) < 1
  rw [galEquiv_apply]
  exact hI a ha

set_option synthInstance.maxHeartbeats 200000 in
-- `T1Space` of the Krull topology on `Gal(k̄ / k)`
/-- **`π₁(X) = H ⧸ ⟨⟨S⟩⟩ → Gal(k̄ / k)`**. -/
def piConstX : X.genuinePi1 →* (kbar X ≃ₐ[k] kbar X) :=
  QuotientGroup.lift (GaloisPi1.kernel (Hgp X.E X.level X.M X.pm) (SgenC X.E X.level X.M))
    ((resConst X).comp (Hgp X.E X.level X.M X.pm).subtype) (by
    intro x hx
    rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker]
    have hcl : IsClosed (((resConst X).ker : Subgroup _) : Set (Gal X.E)) := by
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (continuous_resConst X)
    refine Subgroup.topologicalClosure_minimal _ ?_ hcl hx
    rw [Subgroup.closure_le]
    rintro _ ⟨h, -, s, hs, rfl⟩
    change resConst X (h * s * h⁻¹) = 1
    rw [map_mul, map_mul, resConst_eq_one_of_mem X hs, mul_one, map_inv, mul_inv_cancel])

lemma continuous_piConstX : Continuous (piConstX X) := by
  change Continuous (QuotientGroup.lift (GaloisPi1.kernel (Hgp X.E X.level X.M X.pm)
    (SgenC X.E X.level X.M)) ((resConst X).comp (Hgp X.E X.level X.M X.pm).subtype) _)
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact (continuous_resConst X).comp continuous_subtype_val

variable (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] k] [Algebra.IsAlgebraic ℚ_[p] k]

set_option synthInstance.maxHeartbeats 200000 in
-- the instance search goes through the intermediate-field algebra instances of `k̄ ⊆ Ω`
/-- **`k̄ ≃ \bar{ℚ}_p`** extending `ι : k ≃ ι(k)`. -/
def kbarEquiv : kbar X ≃+* PadicAlgCl p :=
  IsAlgClosure.equivOfEquiv (kbar X) (PadicAlgCl p) (eL p k).toRingEquiv

set_option synthInstance.maxHeartbeats 200000 in
-- as for `kbarEquiv`
omit [CharZero k] in
lemma kbarEquiv_algebraMap (c : k) :
    kbarEquiv X p (algebraMap k (kbar X) c) = algebraMap (Lfield p k) (PadicAlgCl p) (eL p k c) :=
  IsAlgClosure.equivOfEquiv_algebraMap (kbar X) (PadicAlgCl p) (eL p k).toRingEquiv c

omit [CharZero k] in
lemma kbarEquiv_mem_range (x : kbar X) :
    x ∈ (algebraMap k (kbar X)).range ↔
      kbarEquiv X p x ∈ (algebraMap (Lfield p k) (PadicAlgCl p)).range := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨eL p k c, (kbarEquiv_algebraMap X p c).symm⟩
  · rintro ⟨l, hl⟩
    refine ⟨(eL p k).symm l, (kbarEquiv X p).injective ?_⟩
    rw [kbarEquiv_algebraMap, AlgEquiv.apply_symm_apply, hl]

/-- **`Gal(k̄ / k) ≃ₜ* Gal(\bar{ℚ}_p / ι k)`** (conjugation by `kbarEquiv`). -/
def galK : (kbar X ≃ₐ[k] kbar X) ≃ₜ* PAdicGalois.GK p (Lfield p k) :=
  Reconstruction.HemiGenuine.galConj (kbarEquiv X p) (kbarEquiv_mem_range X p)

/-- **`π₁(X) → Gal(\bar{ℚ}_p / ι k)`**. -/
def piToGX : X.genuinePi1 →* PAdicGalois.GK p (Lfield p k) :=
  (galK X p).toMulEquiv.toMonoidHom.comp (piConstX X)

lemma continuous_piToGX : Continuous (piToGX X p) :=
  (galK X p).continuous.comp (continuous_piConstX X)

/-- `π₁^temp(X) → π₁(X) → Gal(\bar{ℚ}_p / ι k)`. -/
def piTempToGX : X.temperedPi1 →* PAdicGalois.GK p (Lfield p k) :=
  (piToGX X p).comp X.tempToEtale

lemma continuous_piTempToGX : Continuous (piTempToGX X p) :=
  (continuous_piToGX X p).comp X.continuous_tempToEtale

end ConstGal

/-! ### Bundled topological groups -/

/-- A topological group (bundled). -/
structure TopGrp : Type 1 where
  /-- The underlying type. -/
  carrier : Type
  [grp : Group carrier]
  [top : TopologicalSpace carrier]
  [isTop : IsTopologicalGroup carrier]

attribute [instance] TopGrp.grp TopGrp.top TopGrp.isTop

/-! ### The local data of initial Θ-data -/

section Theta

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`K_v`** (the completion of `K` at the place `v̲ = sectFin v` of the section over `v`). -/
abbrev Kv : Type := completionAt D.Kt (D.V.sectFin v)

/-- **The residue characteristic `p_v`**. -/
abbrev pv : ℕ := residueChar (D.V.sectFin v)

instance factPrime_pv : Fact (pv D v).Prime := ⟨residueChar_prime _⟩

/-- The `ℚ_{p_v}`-algebra structure of `K_v` (`LocalConstruct.padicAlgebra`; not an instance). -/
abbrev padicAlg : Algebra ℚ_[pv D v] (Kv D v) := LocalConstruct.padicAlgebra (p := pv D v) rfl

lemma isAlgebraic_padicAlg :
    letI := padicAlg D v
    Algebra.IsAlgebraic ℚ_[pv D v] (Kv D v) :=
  letI := padicAlg D v
  haveI : FiniteDimensional ℚ_[pv D v] (Kv D v) :=
    LocalConstruct.finite_padicAlgebra (p := pv D v) rfl
  Algebra.IsAlgebraic.of_finite _ _

/-- **`L_v = ι(K_v) ⊆ \bar{ℚ}_{p_v}`**. -/
def Lv : IntermediateField ℚ_[pv D v] (PadicAlgCl (pv D v)) :=
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  Lfield (pv D v) (Kv D v)

/-- **`G_v = Gal(\bar{ℚ}_p / ι K_v)`**, the local Galois group (IUT I, Examples 3.2 (i), 3.3 (i):
`D^⊢_v = B(G_v)⁰`). -/
abbrev Gv : Type := PAdicGalois.GK (pv D v) (Lv D v)

/-- **The local model `X̲_v = X̲_K ×_K K_v`** (IUT I, Definition 3.1 (e)). -/
abbrev Xv : Orbicurve (Kv D v) := localize (D.V.sectFin v) D.orb.XKu

/-- `Π_v` together with `Π_v → G_v` (tempered at `V^bad`, étale otherwise). -/
def piData : Σ G : TopGrp, {f : G.carrier →* Gv D v // Continuous f} := by
  classical
  letI := padicAlg D v
  haveI := isAlgebraic_padicAlg D v
  exact if v ∈ D.VBad then
    ⟨⟨(Xv D v).temperedPi1⟩, piTempToGX (Xv D v) (pv D v),
      continuous_piTempToGX (Xv D v) (pv D v)⟩
  else
    ⟨⟨(Xv D v).genuinePi1⟩, piToGX (Xv D v) (pv D v), continuous_piToGX (Xv D v) (pv D v)⟩

/-- **`Π_v`** (IUT I, Definition 3.1 (e)): the tempered fundamental group of `X̲_v` at
`v ∈ V^bad`, the profinite étale fundamental group at `v ∈ V^good ∩ V^non`. -/
abbrev Piv : TopGrp := (piData D v).1

/-- **`Π_v → G_v`** (restriction to the constants, through the tempered-to-étale comparison at
`V^bad`). -/
def piToG : (Piv D v).carrier →* Gv D v := (piData D v).2.1

lemma continuous_piToG : Continuous (piToG D v) := (piData D v).2.2

/-- **Debt H3** (MR20 plan): `Π_v → G_v` is a quotient map of topological groups — surjective,
with open images of open subgroups (IUT I, Definition 3.1 (e), `1 → Δ_v → Π_v → G_v → 1`). -/
def PiToGQuotient : Prop :=
  Function.Surjective (piToG D v) ∧
    ∀ U : Subgroup (Piv D v).carrier, IsOpen (U : Set (Piv D v).carrier) →
      IsOpen (U.map (piToG D v) : Set (Gv D v))

end Theta

end PrimeStrip

end Multiradial

end Iut
