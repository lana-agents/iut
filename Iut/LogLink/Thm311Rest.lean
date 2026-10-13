/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.LogLink.Thm311LGP
import Iut.EtaleTheta.CyclotomicRigidity

/-!
# Theorem 3.11(iii) of IUT III (Θ-link compatibility) in the log-theta-lattice model

IUT III, Theorem 3.11(iii) states that the Kummer isomorphisms of Theorem 3.11(ii) are compatible
with the horizontal arrows (the `Θ^{×μ}_LGP`-links) of the lattice:

* **(a)** the Kummer isomorphisms `n,mF^{⊢×μ}_△ ≅ F^{⊢×μ}_△(n,◦D^⊢_△)` (Theorem 1.5(iii))
  carry the full poly-isomorphism `n,mF^{⊢×μ}_△ ≅ n+1,mF^{⊢×μ}_△` induced by the horizontal
  arrows (Theorem 1.5(ii)) to the full poly-isomorphism of the coric strips
  `F^{⊢×μ}_△(n,◦D^⊢_△) ≅ F^{⊢×μ}_△(n+1,◦D^⊢_△)`;
* **(b)** the same holds for the `F^{⊢×μ}`-prime-strips `F^{⊢×μ}_env(n,◦D_>)` of the
  mono-theta environments, relative to the natural isomorphisms `F^{⊢×μ}_△ ≅ F^{⊢×μ}_env`
  (Proposition 2.1(vi));
* **(c)** the data `n,◦R` built from the projective systems of mono-theta environments (the
  splitting monoids of the LGP-monoids, through cyclotomic rigidity and the theta values) are
  related to the corresponding Frobenius-like data of `n,mHT` by Kummer isomorphisms of
  mono-theta environments, and these constructions are compatible with the horizontal arrows "in
  the sense that they are stabilized/equivariant/functorial with respect to arbitrary
  automorphisms of the domain and codomain of these horizontal arrows";
* **(d)** the same for the `κ`-coric data of the number field `F_mod` (the Kummer theory of
  `F_mod^×` with its cyclotomic rigidity, IUT I, Example 5.1(v)).

Theorem 1.5(v) (**bi-coric mono-analytic global realified Frobenioids**): the poly-isomorphisms
of `D^⊢`-prime-strips induce **an** isomorphism (not a poly-isomorphism) of the collections of
data `(D^⊩(n,mD^⊢_△), Prime(D^⊩) ≅ V, {ρ_v}_v)`, compatible, relative to the horizontal arrows,
with the `ℝ_{>0}`-orbits of the isomorphisms `n,mC^⊩_△ ≅ D^⊩(n,mD^⊢_△)`.

## What is formalised here

* **Conjugation** (`fmuConj`): isomorphisms `κ : P ≅ Q`, `κ' : P' ≅ Q'` of
  `F^{⊢×μ}`-prime-strips give a bijection `Iso(P, P') ≃ Iso(Q, Q')`, functorial (`fmuConj_trans`,
  `fmuConj_comp`). This is the precise form of "relative to the Kummer isomorphisms, the full
  poly-isomorphism is compatible with the full poly-isomorphism".
* **(a), (b), Theorem 1.5(iii)** (`BiCoricKummer`: coric strips `cor n`, Kummer isomorphisms
  `kum n m`, environment strips `env n` with natural isomorphisms `envIso n`):
  `horizCor` (a bijection from the Θ-links `(n, m) → (n + 1, m)` onto the full poly-isomorphism
  of the coric strips, **`horizCor_bijective`**), `kum_comm` (the Kummer square commutes),
  `horizEnv`, **`horizEnv_eq`** (compatibility relative to the natural isomorphisms);
  `vertCor` (the vertical poly-isomorphisms of Theorem 1.5(iii), first line) and
  **`biCoric_square`** (Θ-links of different rows inducing the same coric isomorphism commute
  with the vertical isomorphisms); `BiCoricKummer.ofLattice` (every lattice carries such data).
* **(c)** (`MonoThetaKummer`: Frobenius-like mono-theta environments `envF (n, m) w` at the bad
  places, étale-like ones `envD n w`, Kummer isomorphisms of environments and the
  isomorphisms `perm n w` of the étale-picture, using P16's abelian environments
  `EtaleTheta.Env`): the transport `horizMap` along a horizontal arrow carries the cyclotomic
  rigidity isomorphism of `n,mHT` to that of `n+1,mHT` (**`isCyc_horizMap`**), also after
  composing with *arbitrary* automorphisms of the domain and codomain
  (**`isCyc_horizMap_aut`**), and likewise along the vertical arrows (`isCyc_vertMap`); if the
  étale-like environment is the model one (a rigidification `r`), the output at every vertex of
  the column is the natural isomorphism `l·c ↦ −red(l·c)`, **independent of the Kummer class `ρ`
  of the coordinate** (`isCyc_of_rigid`). The theta values themselves (the generators
  `{q_v^{j²}}_j` of the splitting monoids) are fixed by the Kummer isomorphisms of an
  LGP-lattice (`LGPLattice.kum_gen`, used in `Thm311LGP.splitCoric`).
* **(c), (d), stabilization**: Θ-links are permuted by arbitrary automorphisms of the domain and
  codomain theaters (`thetaLink_congr_bijective`), and every automorphism of the
  `D-Θ^{±ell}NF`-Hodge theater (the étale-like side on which `n,◦R` and the `κ`-coric data are
  constructed) is the label part of such an automorphism (`labels_realized`).
* **(d)** for `F_mod` (`fmodOxMu`: the image of `x ∈ F_mod` with `|x|_v = 1` in
  `O^{×μ}(K_v)`): **an element of `F_mod^×` integral at every place of `V` maps to `1` in
  `O^{×μ}(K_v)` at every `v ∈ V^non`** (`fmodOxMu_eq_one`, from Proposition 3.10(ii),
  `nonInterference_sect`). So the global units of `F_mod` are invisible to the
  `F^{⊢×μ}`-prime-strips, the only data the horizontal arrows transport (`unitEquiv`); `F_mod`
  enters the horizontal compatibility only through the étale-like side, where it is stabilized
  by all automorphisms (previous item).
* **Theorem 1.5(v)** (`Thm15v`): for families of value-group BPSs (the model of the collections
  `(D^⊩, Prime(D^⊩) ≅ V, {ρ_v})`: a realified line with local pilots indexed by the places) with
  equal product formulas, **the isomorphism between any two members exists and is unique**
  (`rlf_unique`), hence induced independently of the chosen member of a poly-isomorphism of
  `D^⊢`-strips, and the isomorphisms form a cocycle (`rlf_cocycle`); the `ℝ_{>0}`-orbits
  (`RposOrbit`: linear isomorphisms sending each local pilot to the same positive multiple of the
  corresponding one) are exactly the positive multiples of the unique isomorphism
  (`mem_rposOrbit_iff`), and the unique isomorphisms are compatible with them up to `ℝ_{>0}`
  (**`rposOrbit_compat`**). For a lattice, `rlfData L a` is the value-group portion of
  `n,mF^{⊩▶×μ}_△`; the Θ-links act on value groups by the positive scaling `1/s` in degree
  coordinates (`ThetaLinkIso.val_apply`) and, on the global realified Frobenioid, exactly the
  `ℝ_{>0}`-scaling `1/s` carries the Θ-pilot object to the `q`-pilot object
  (`ThetaLink.scaling_iff`). **`thm15v_model`**.
* **`thm311iii_model`**: `Thm311iii` (all of the above for (iii)(a)–(d)) holds for every lattice,
  every bi-coric Kummer data and every mono-theta Kummer data.

## What is not formalised (precisely)

* The coric strips `F^{⊢×μ}_△(n,◦D^⊢_△)`, the environment strips and the mono-theta
  environments are **data** of `BiCoricKummer` / `MonoThetaKummer`, not constructed from the
  `D^⊢`-prime-strips or from the tempered Frobenioids of the theaters (P18's theaters do not
  carry tempered Frobenioids, and the `D^⊢`-strip reconstruction is only in `StripKummer.lean`).
  The natural isomorphisms `F^{⊢×μ}_△ ≅ F^{⊢×μ}_env` are arbitrary isomorphisms (identities in
  P19's model).
* The environments are P16's **abelian** environments (the geometric theta quotient); the
  projective systems, discrete rigidity along them and the evaluation maps (the Kummer classes of
  the theta values as functions on the environments) are not recorded here.
* (d): the `κ`-coric functions, `π_1^{κ-sol}(D^⊛)` and the cyclotomic rigidity of IUT I,
  Example 5.1(v) are not formalised; only the interaction of `F_mod^×` with the unit portions.
* Theorem 1.5(v): `D^⊩(D^⊢)` is not constructed from a `D^⊢`-strip; the collections are modelled
  by value-group BPSs (indexed by the places of `F`, the wall's indexing), and `ρ_v` by the local
  pilots.
* These parts do not touch the multi-container model: `XiPrinciple` and `xi_iff_ss` are
  unchanged.
-/

namespace Iut

namespace LogLink

open Wall ThetaLink HodgeTheater NumberField
open scoped Valued

noncomputable section

variable {D : InitialThetaData.{0}}

/-! ### Conjugation of isomorphisms of `F^{⊢×μ}`-prime-strips -/

/-- **Conjugation by Kummer isomorphisms** `κ : P ≅ Q`, `κ' : P' ≅ Q'`: `u ↦ κ⁻¹ ∘ u ∘ κ'` (in
the diagrammatic order of `PrimeStrip.Iso.trans`). -/
def fmuConj {P P' Q Q' : FMuStrip D} (κ : P.Iso Q) (κ' : P'.Iso Q') : P.Iso P' ≃ Q.Iso Q' where
  toFun u := PrimeStrip.Iso.trans κ.symm (PrimeStrip.Iso.trans u κ')
  invFun v := PrimeStrip.Iso.trans κ (PrimeStrip.Iso.trans v κ'.symm)
  left_inv u := FMuIso.ext fun x => ⟨fun a => by
      simp [PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind],
    fun m => by simp [PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]⟩
  right_inv v := FMuIso.ext fun x => ⟨fun a => by
      simp [PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind],
    fun m => by simp [PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]⟩

theorem fmuConj_apply {P P' Q Q' : FMuStrip D} (κ : P.Iso Q) (κ' : P'.Iso Q') (u : P.Iso P') :
    fmuConj κ κ' u = PrimeStrip.Iso.trans κ.symm (PrimeStrip.Iso.trans u κ') := rfl

/-- Conjugation is functorial: `conj(u ∘ u') = conj(u) ∘ conj(u')`. -/
theorem fmuConj_trans {P P' P'' Q Q' Q'' : FMuStrip D} (κ : P.Iso Q) (κ' : P'.Iso Q')
    (κ'' : P''.Iso Q'') (u : P.Iso P') (u' : P'.Iso P'') :
    fmuConj κ κ'' (PrimeStrip.Iso.trans u u') =
      PrimeStrip.Iso.trans (fmuConj κ κ' u) (fmuConj κ' κ'' u') :=
  FMuIso.ext fun x => ⟨fun a => by
      simp [fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind],
    fun m => by simp [fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]⟩

/-- Conjugating by composites is composing conjugations. -/
theorem fmuConj_comp {P P' Q Q' R R' : FMuStrip D} (κ : P.Iso Q) (κ' : P'.Iso Q')
    (ν : Q.Iso R) (ν' : Q'.Iso R') (u : P.Iso P') :
    fmuConj (PrimeStrip.Iso.trans κ ν) (PrimeStrip.Iso.trans κ' ν') u =
      fmuConj ν ν' (fmuConj κ κ' u) :=
  FMuIso.ext fun x => ⟨fun a => by
      simp [fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]
      rfl,
    fun m => by
      simp [fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]
      rfl⟩

/-! ### (a), (b): bi-coric Kummer data (Theorem 1.5(iii)) -/

/-- **Bi-coric Kummer data** of a log-theta-lattice (IUT III, Theorem 1.5(iii); Theorem
3.11(iii)(a), (b)): coric `F^{⊢×μ}`-prime-strips of the columns, Kummer isomorphisms from the
`F^{⊢×μ}`-prime-strips of the vertices, and the environment strips with their natural
isomorphisms. -/
structure BiCoricKummer (L : LogThetaLattice D) where
  /-- `F^{⊢×μ}_△(n,◦D^⊢_△)`: the coric `F^{⊢×μ}`-prime-strip of the `n`-th column. -/
  cor : ℤ → FMuStrip D
  /-- The Kummer isomorphisms `n,mF^{⊢×μ}_△ ≅ F^{⊢×μ}_△(n,◦D^⊢_△)`. -/
  kum : ∀ n m : ℤ, (L.H (n, m)).Fmu.Iso (cor n)
  /-- `F^{⊢×μ}_env(n,◦D_>)`: the `F^{⊢×μ}`-prime-strip of the mono-theta environments. -/
  env : ℤ → FMuStrip D
  /-- The natural isomorphisms `F^{⊢×μ}_△(n,◦D^⊢_△) ≅ F^{⊢×μ}_env(n,◦D_>)` (Proposition
  2.1(vi)). -/
  envIso : ∀ n : ℤ, (cor n).Iso (env n)

namespace BiCoricKummer

variable {L : LogThetaLattice D} (B : BiCoricKummer L)

/-- **Every lattice carries bi-coric Kummer data** (all `F^{⊢×μ}`-prime-strips are
isomorphic): the coric strips are the tautological ones. -/
def ofLattice (L : LogThetaLattice D) : BiCoricKummer L where
  cor _ := PrimeStrip.tautological _ _
  kum _ _ := (PrimeStrip.nonempty_iso _ _).some
  env _ := PrimeStrip.tautological _ _
  envIso _ := PrimeStrip.Iso.refl _

/-- **The coric isomorphism induced by a horizontal arrow** (Theorem 3.11(iii)(a)): a Θ-link
`(n, m) → (n + 1, m)` induces, through the Kummer isomorphisms, an isomorphism
`F^{⊢×μ}_△(n,◦D^⊢_△) ≅ F^{⊢×μ}_△(n+1,◦D^⊢_△)`. -/
def horizCor (n m : ℤ) :
    ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)) ≃ (B.cor n).Iso (B.cor (n + 1)) :=
  (ThetaLinkIso.unitEquiv _ _).trans (fmuConj (B.kum n m) (B.kum (n + 1) m))

/-- **Theorem 3.11(iii)(a)**: relative to the Kummer isomorphisms, the full poly-isomorphism of
the coric strips is exactly the full poly-isomorphism induced by the horizontal arrows. -/
theorem horizCor_bijective (n m : ℤ) : Function.Bijective (B.horizCor n m) :=
  (B.horizCor n m).bijective

/-- **The Kummer square commutes**: `θ ∘ κ_{n+1,m} = κ_{n,m} ∘ horizCor θ`. -/
theorem kum_comm (n m : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m))) :
    PrimeStrip.Iso.trans (ThetaLinkIso.unitEquiv _ _ θ) (B.kum (n + 1) m) =
      PrimeStrip.Iso.trans (B.kum n m) (B.horizCor n m θ) :=
  FMuIso.ext fun x => ⟨fun a => by
      simp [horizCor, fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind],
    fun m => by
      simp [horizCor, fmuConj_apply, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]⟩

/-- The isomorphism of environment strips induced by a horizontal arrow. -/
def horizEnv (n m : ℤ) :
    ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)) ≃ (B.env n).Iso (B.env (n + 1)) :=
  (B.horizCor n m).trans (fmuConj (B.envIso n) (B.envIso (n + 1)))

/-- **Theorem 3.11(iii)(b)**: relative to the natural isomorphisms `F^{⊢×μ}_△ ≅ F^{⊢×μ}_env` and
the Kummer isomorphisms, the full poly-isomorphism of the environment strips is the full
poly-isomorphism induced by the horizontal arrows. -/
theorem horizEnv_eq (n m : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m))) :
    B.horizEnv n m θ = fmuConj (PrimeStrip.Iso.trans (B.kum n m) (B.envIso n))
      (PrimeStrip.Iso.trans (B.kum (n + 1) m) (B.envIso (n + 1)))
      (ThetaLinkIso.unitEquiv _ _ θ) :=
  (fmuConj_comp _ _ _ _ _).symm

theorem horizEnv_bijective (n m : ℤ) : Function.Bijective (B.horizEnv n m) :=
  (B.horizEnv n m).bijective

/-- **The vertical isomorphisms of Theorem 1.5(iii)** (first line of the fifth display): the
`F^{⊢×μ}`-prime-strips of two vertices of a column are identified through the coric strip. -/
def vertCor (n m m' : ℤ) : (L.H (n, m)).Fmu.Iso (L.H (n, m')).Fmu :=
  PrimeStrip.Iso.trans (B.kum n m) (B.kum n m').symm

/-- **Bi-coricity** (Theorem 1.5(iii)): Θ-links of the rows `m` and `m'` that induce the same
coric isomorphism commute with the vertical isomorphisms. -/
theorem biCoric_square (n m m' : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)))
    (θ' : ThetaLinkIso D (L.H (n, m')) (L.H (n + 1, m')))
    (h : B.horizCor n m θ = B.horizCor n m' θ') :
    PrimeStrip.Iso.trans (B.vertCor n m m') (ThetaLinkIso.unitEquiv _ _ θ') =
      PrimeStrip.Iso.trans (ThetaLinkIso.unitEquiv _ _ θ) (B.vertCor (n + 1) m m') := by
  have h' : ThetaLinkIso.unitEquiv _ _ θ' =
      (fmuConj (B.kum n m') (B.kum (n + 1) m')).symm
        (fmuConj (B.kum n m) (B.kum (n + 1) m) (ThetaLinkIso.unitEquiv _ _ θ)) := by
    rw [Equiv.eq_symm_apply]
    exact h.symm
  rw [h']
  exact FMuIso.ext fun x => ⟨fun a => by
      simp [vertCor, fmuConj, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind],
    fun m => by simp [vertCor, fmuConj, PrimeStrip.Iso.trans, PrimeStrip.Iso.symm, fmuKind]⟩

end BiCoricKummer

/-! ### (c): mono-theta environments and cyclotomic rigidity -/

open EtaleTheta in
/-- The identity isomorphism of an abelian mono-theta environment. -/
def envIsoRefl (E : Env.{0}) : Env.Iso E E where
  e := AddEquiv.refl _
  map_D γ := by
    have : (AddEquiv.refl E.carrier).trans (γ.trans (AddEquiv.refl E.carrier).symm) = γ := by
      ext; rfl
    rw [this]
  map_S := by
    ext x
    simp

open EtaleTheta in
variable (D) in
/-- **Kummer data of mono-theta environments** along a log-theta-lattice (IUT III,
Proposition 2.1(ii), (iii); Theorem 3.11(iii)(c)): at each bad place, Frobenius-like
environments of the vertices (from the tempered Frobenioids of `n,mHT`), étale-like ones of the
columns (from `n,◦HT^{D-Θ^{±ell}NF}`), Kummer isomorphisms of environments, and the isomorphisms
`n,◦R ≅ n+1,◦R` induced by the permutation symmetries of the étale-picture. -/
structure MonoThetaKummer where
  /-- The Frobenius-like mono-theta environments of `n,mHT` at `w ∈ V^bad`. -/
  envF : ℤ × ℤ → ∀ w : FinitePlace D.Fmod, w ∈ D.VBad → Env.{0}
  /-- The étale-like mono-theta environments of `n,◦HT^{D-Θ^{±ell}NF}`. -/
  envD : ℤ → ∀ w : FinitePlace D.Fmod, w ∈ D.VBad → Env.{0}
  /-- The Kummer isomorphisms of mono-theta environments. -/
  kum : ∀ (n m : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad),
    Env.Iso (envF (n, m) w hw) (envD n w hw)
  /-- The isomorphisms induced by the permutation symmetries of the étale-picture. -/
  perm : ∀ (n : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad),
    Env.Iso (envD n w hw) (envD (n + 1) w hw)

namespace MonoThetaKummer

open EtaleTheta

variable (M : MonoThetaKummer D)

/-- **The trivial mono-theta Kummer data** of one environment (identity isomorphisms): the data
are not vacuous. -/
def const (D : InitialThetaData.{0}) (E : Env.{0}) : MonoThetaKummer D where
  envF _ _ _ := E
  envD _ _ _ := E
  kum _ _ _ _ := envIsoRefl E
  perm _ _ _ := envIsoRefl E

/-- **The transport along a horizontal arrow** `(n, m) → (n + 1, m)`: Kummer isomorphism,
permutation symmetry of the étale-picture, inverse Kummer isomorphism. -/
def horizMap (n m : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad) :
    (M.envF (n, m) w hw).carrier → (M.envF (n + 1, m) w hw).carrier :=
  fun t => (M.kum (n + 1) m w hw).e.symm ((M.perm n w hw).e ((M.kum n m w hw).e t))

/-- **The transport along the vertical arrows** of a column, through the étale-like
environment. -/
def vertMap (n m m' : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad) :
    (M.envF (n, m) w hw).carrier → (M.envF (n, m') w hw).carrier :=
  fun t => (M.kum n m' w hw).e.symm ((M.kum n m w hw).e t)

/-- Transport of the cyclotomic rigidity relation through the inverse of an isomorphism. -/
theorem isCyc_symm {E E' : Env.{0}} (f : Env.Iso E E') (t x : E'.carrier) :
    E.IsCyc (f.e.symm t) (f.e.symm x) ↔ E'.IsCyc t x := by
  rw [← f.isCyc_iff, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **Theorem 3.11(iii)(c), cyclotomic rigidity along the horizontal arrows**: the transport
along a horizontal arrow carries the cyclotomic rigidity isomorphism of the environment of
`n,mHT` exactly onto that of `n+1,mHT`. -/
theorem isCyc_horizMap (n m : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad)
    (t x : (M.envF (n, m) w hw).carrier) :
    (M.envF (n + 1, m) w hw).IsCyc (M.horizMap n m w hw t) (M.horizMap n m w hw x) ↔
      (M.envF (n, m) w hw).IsCyc t x := by
  rw [horizMap, horizMap, isCyc_symm, (M.perm n w hw).isCyc_iff, (M.kum n m w hw).isCyc_iff]

/-- **Stabilization by arbitrary automorphisms** (Theorem 3.11(iii)(c)): the compatibility holds
after composing with arbitrary automorphisms `α` of the domain and `β` of the codomain of the
horizontal arrow. -/
theorem isCyc_horizMap_aut (n m : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad)
    (α : Env.Iso (M.envF (n, m) w hw) (M.envF (n, m) w hw))
    (β : Env.Iso (M.envF (n + 1, m) w hw) (M.envF (n + 1, m) w hw))
    (t x : (M.envF (n, m) w hw).carrier) :
    (M.envF (n + 1, m) w hw).IsCyc (β.e (M.horizMap n m w hw (α.e t)))
        (β.e (M.horizMap n m w hw (α.e x))) ↔
      (M.envF (n, m) w hw).IsCyc t x := by
  rw [β.isCyc_iff, isCyc_horizMap, α.isCyc_iff]

/-- Cyclotomic rigidity along the vertical arrows of a column. -/
theorem isCyc_vertMap (n m m' : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad)
    (t x : (M.envF (n, m) w hw).carrier) :
    (M.envF (n, m') w hw).IsCyc (M.vertMap n m m' w hw t) (M.vertMap n m m' w hw x) ↔
      (M.envF (n, m) w hw).IsCyc t x := by
  rw [vertMap, vertMap, isCyc_symm, (M.kum n m w hw).isCyc_iff]

/-- **The output at every vertex is the natural isomorphism of cyclotomes**, if the étale-like
environment of the column is rigidified by an isomorphism `r` with P16's model environment:
`t ↔ x` iff `t`, `x` correspond to `(0, l·y, 0)`, `(−red(l·y), 0, 0)`. The right-hand side does
not involve the Kummer class `ρ` of the coordinate. -/
theorem isCyc_of_rigid {Mg : Type} [AddCommGroup Mg] [IsAddTorsionFree Mg] {l : ℤ} {μ : Type}
    [AddCommGroup μ] (hμ : AddMonoid.IsTorsion μ) {red ρ : Mg →+ μ} (n m : ℤ)
    (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad) (r : Env.Iso (M.envD n w hw) (model Mg l μ red ρ))
    (t x : (M.envF (n, m) w hw).carrier) :
    (M.envF (n, m) w hw).IsCyc t x ↔ ∃ y : Mg, r.e ((M.kum n m w hw).e t) = (0, l • y, 0) ∧
      r.e ((M.kum n m w hw).e x) = (-red (l • y), 0, 0) := by
  rw [← (M.kum n m w hw).isCyc_iff, ← r.isCyc_iff, model_isCyc hμ]

end MonoThetaKummer

/-! ### (c), (d): stabilization by automorphisms of the domain and codomain -/

/-- **The Θ-links are permuted by arbitrary automorphisms of the domain and codomain** (Theorem
3.11(iii)(c), (d): "stabilized/equivariant/functorial with respect to arbitrary automorphisms of
the domain and codomain of these horizontal arrows"). -/
theorem thetaLink_congr_bijective {A B : ThetaPmEllNFHT D} (f : A.Iso A) (g : B.Iso B) :
    Function.Bijective (ThetaLinkIso.congr f g) :=
  (ThetaLinkIso.congr f g).bijective

/-- **Every automorphism of the étale-like side is realized**: every automorphism of the
associated `D-Θ^{±ell}NF`-Hodge theater (on which `n,◦R` and the `κ`-coric data are
constructed) is the label part of an automorphism of the `Θ^{±ell}NF`-Hodge theater. -/
theorem labels_realized (A : ThetaPmEllNFHT D) (σ : A.labels.Iso A.labels) :
    ∃ f : A.Iso A, f.labels = σ :=
  ThetaPmEllNFHT.toLabels_surjective A A σ

/-! ### (d): `F_mod^×` and the unit portions -/

theorem embFin_ne_zero_of_norm {w : FinitePlace D.Fmod} {x : D.Fmod}
    (hx : ‖embFin D w x‖ = 1) : embFin D w x ≠ 0 := by
  intro h
  rw [h, norm_zero] at hx
  exact zero_ne_one hx

/-- The unit of norm one of `K_v` defined by `x ∈ F_mod` with `|x|_v = 1`. -/
def fmodUnit (w : FinitePlace D.Fmod) (x : D.Fmod) (hx : ‖embFin D w x‖ = 1) :
    unitsOne (Kfin D w) :=
  ⟨Units.mk0 (embFin D w x) (embFin_ne_zero_of_norm hx), by
    change ‖((Units.mk0 (embFin D w x) _ : (Kfin D w)ˣ) : Kfin D w)‖ = 1
    rw [Units.val_mk0]
    exact hx⟩

/-- **The image of `x ∈ F_mod` with `|x|_v = 1` in `O^{×μ}(K_v)`**, the monoid of the
tautological `F^{⊢×μ}`-prime-strip at `v ∈ V^non`. -/
def fmodOxMu (w : FinitePlace D.Fmod) (x : D.Fmod) (hx : ‖embFin D w x‖ = 1) :
    OxMu (Kfin D w) :=
  QuotientGroup.mk (fmodUnit w x hx)

theorem embFin_pow (w : FinitePlace D.Fmod) (x : D.Fmod) (k : ℕ) :
    embFin D w x ^ k = embFin D w (x ^ k) := by
  rw [embFin, embFin, map_pow, map_pow]

/-- **Theorem 3.11(iii)(d), the unit portions do not see `F_mod`**: an element of `F_mod^×`
integral at every place of `V` has absolute value `1` at every `v ∈ V^non`, and its image in
`O^{×μ}(K_v)` is trivial (Proposition 3.10(ii): it is a root of unity). -/
theorem fmodOxMu_eq_one {x : D.Fmod} (hx : x ≠ 0)
    (hfin : ∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1)
    (hinf : ∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1)
    (w : FinitePlace D.Fmod) : ∃ h : ‖embFin D w x‖ = 1, fmodOxMu w x h = 1 := by
  obtain ⟨k, hk, h⟩ := (nonInterference_sect D hx).1 ⟨hfin, hinf⟩
  have hroot : embFin D w x ^ k = 1 := by
    rw [embFin_pow, h, embFin, map_one, map_one]
  have hnorm : ‖embFin D w x‖ = 1 := by
    have e := congrArg norm hroot
    rw [norm_pow, norm_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 e
  refine ⟨hnorm, ?_⟩
  rw [fmodOxMu, QuotientGroup.eq_one_iff, CommGroup.mem_torsion,
    isOfFinOrder_iff_pow_eq_one]
  refine ⟨k, hk, Subtype.ext (Units.ext ?_)⟩
  change embFin D w x ^ k = 1
  exact hroot

/-! ### Theorem 1.5(v): bi-coric mono-analytic global realified Frobenioids -/

section Rlf

variable {V : Type} {bad : Finset V}

/-- **Any two value-group BPSs with the same product formula have exactly one isomorphism**
(Theorem 1.5(v): the poly-isomorphisms of `D^⊢`-prime-strips induce *an* isomorphism of the
collections `(D^⊩, Prime(D^⊩) ≅ V, {ρ_v})`). -/
theorem rlf_unique (B B' : ValBPS V bad) (h : B.PF = B'.PF) : Nonempty (Unique (B.Iso B')) := by
  obtain ⟨e⟩ := (ValBPS.nonempty_iso_iff B B').mpr h
  haveI := ValBPS.valIso_subsingleton B B'
  exact ⟨uniqueOfSubsingleton e⟩

/-- The unique isomorphisms form a cocycle. -/
theorem rlf_cocycle {B₁ B₂ B₃ : ValBPS V bad} (e₁₂ : B₁.Iso B₂) (e₂₃ : B₂.Iso B₃)
    (e₁₃ : B₁.Iso B₃) : e₁₂.trans e₂₃ = e₁₃ :=
  (ValBPS.valIso_subsingleton B₁ B₃).elim _ _

/-- **The `ℝ_{>0}`-orbit of identifications** of the realified lines of `B` and `B'`: the linear
isomorphisms sending every local pilot to the same positive multiple of the corresponding local
pilot (IUT II, Corollary 4.6(ii): the identifications `C^⊩ ≅ D^⊩` are only determined up to
`ℝ_{>0}`). -/
def RposOrbit (B B' : ValBPS V bad) : Set (B.C ≃ₗ[ℝ] B'.C) :=
  {φ | ∃ c : ℝ, 0 < c ∧ ∀ v, φ (B.localPilot v) = c • B'.localPilot v}

/-- **The `ℝ_{>0}`-orbit is the set of positive multiples of the unique isomorphism.** -/
theorem mem_rposOrbit_iff {B B' : ValBPS V bad} (e : B.Iso B') (φ : B.C ≃ₗ[ℝ] B'.C) :
    φ ∈ RposOrbit B B' ↔ ∃ c : ℝ, 0 < c ∧ ∀ x, φ x = c • e.toLinearEquiv x := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x => ?_⟩
    have : (φ : B.C →ₗ[ℝ] B'.C) = c • (e.toLinearEquiv : B.C →ₗ[ℝ] B'.C) :=
      LinearMap.ext_on_range B.span_localPilot fun v => by
        simp [h, e.map_localPilot]
    exact LinearMap.congr_fun this x
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun v => by rw [h, e.map_localPilot]⟩

/-- **Compatibility up to `ℝ_{>0}`** (Theorem 1.5(v)): for identifications `φ`, `ψ` in the
`ℝ_{>0}`-orbits `C_a ≅ D_a`, `C_b ≅ D_b` and the unique isomorphisms `e : D_a ≅ D_b`,
`c : C_a ≅ C_b`, the two routes `C_a → D_b` differ by a positive scalar. -/
theorem rposOrbit_compat {Ca Cb Da Db : ValBPS V bad} (hCD : Ca.PF = Da.PF)
    {φ : Ca.C ≃ₗ[ℝ] Da.C} {ψ : Cb.C ≃ₗ[ℝ] Db.C} (hφ : φ ∈ RposOrbit Ca Da)
    (hψ : ψ ∈ RposOrbit Cb Db) (e : Da.Iso Db) (c : Ca.Iso Cb) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, e.toLinearEquiv (φ x) = r • ψ (c.toLinearEquiv x) := by
  obtain ⟨ea⟩ := (ValBPS.nonempty_iso_iff Ca Da).mpr hCD
  obtain ⟨a, ha, hφ'⟩ := (mem_rposOrbit_iff ea φ).1 hφ
  obtain ⟨b, hb, hψ'⟩ := (mem_rposOrbit_iff (c.symm.trans (ea.trans e)) ψ).1 hψ
  refine ⟨a / b, div_pos ha hb, fun x => ?_⟩
  rw [hφ', hψ', map_smul, smul_smul, div_mul_cancel₀ _ hb.ne']
  congr 1
  change _ = e.toLinearEquiv (ea.toLinearEquiv (c.toLinearEquiv.symm (c.toLinearEquiv x)))
  rw [LinearEquiv.symm_apply_apply]

end Rlf

/-- **The collection `(D^⊩(n,mD^⊢_△), Prime ≅ V, {ρ_v})` of a vertex**, in the model: the
value-group portion of `n,mF^{⊩▶×μ}_△`. -/
def rlfData (L : LogThetaLattice D) (a : ℤ × ℤ) : ValBPS (Pl D) D.bpsDegrees.bad :=
  (qStrip D (L.H a)).val

/-- **IUT III, Theorem 1.5(v), as a statement about a log-theta-lattice.** -/
structure Thm15v (L : LogThetaLattice D) : Prop where
  /-- An isomorphism of the collections between any two vertices, and only one. -/
  unique : ∀ a b : ℤ × ℤ, Nonempty (Unique ((rlfData L a).Iso (rlfData L b)))
  /-- The isomorphisms are compatible with composition. -/
  cocycle : ∀ (a b c : ℤ × ℤ) (e₁ : (rlfData L a).Iso (rlfData L b))
    (e₂ : (rlfData L b).Iso (rlfData L c)) (e₃ : (rlfData L a).Iso (rlfData L c)),
      e₁.trans e₂ = e₃
  /-- Compatibility with the `ℝ_{>0}`-orbits of identifications `C^⊩_△ ≅ D^⊩` (for
  Frobenius-like collections `C` with the product formula of `D^⊩`). -/
  rpos : ∀ (a b : ℤ × ℤ) (Ca Cb : ValBPS (Pl D) D.bpsDegrees.bad),
    Ca.PF = (rlfData L a).PF → ∀ {φ : Ca.C ≃ₗ[ℝ] (rlfData L a).C}
      {ψ : Cb.C ≃ₗ[ℝ] (rlfData L b).C}, φ ∈ RposOrbit Ca (rlfData L a) →
      ψ ∈ RposOrbit Cb (rlfData L b) → ∀ (e : (rlfData L a).Iso (rlfData L b))
      (c : Ca.Iso Cb), ∃ r : ℝ, 0 < r ∧ ∀ x, e.toLinearEquiv (φ x) = r • ψ (c.toLinearEquiv x)
  /-- Relative to the horizontal arrows, the value groups are identified by the positive scaling
  `1/s` in degree coordinates. -/
  horizScale : ∀ (n m : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)))
    (x : (gauStrip D (L.H (n, m))).val.C),
      ThetaLinkIso.qCoord (θ.val.toLinearEquiv x) =
        D.wallS⁻¹ * degTheta D.bpsDegrees D.wallS_ne_zero x ∧ 0 < D.wallS⁻¹
  /-- On the global realified Frobenioid, exactly the `ℝ_{>0}`-scaling `1/s` carries the
  Θ-pilot object to the `q`-pilot object. -/
  frobScale : ∀ (c : ℝ) (hc : 0 < c),
    Nonempty ((Frobenioid.GlobalRealified.scale c hc).obj (Frobenioid.thetaPilotObj D) ≅
      Frobenioid.qPilotObj D) ↔ c = D.wallS⁻¹

/-- **Theorem 1.5(v) holds in the model.** -/
theorem thm15v_model (L : LogThetaLattice D) : Thm15v L where
  unique _ _ := rlf_unique _ _ rfl
  cocycle _ _ _ e₁ e₂ e₃ := rlf_cocycle e₁ e₂ e₃
  rpos _ _ _ _ hCD _ _ hφ hψ e c := rposOrbit_compat hCD hφ hψ e c
  horizScale _ _ θ x := ⟨ThetaLinkIso.val_apply θ x, inv_pos.mpr (D.one_lt_wallS.trans' one_pos)⟩
  frobScale c hc := scaling_iff D c hc

/-! ### Theorem 3.11(iii) -/

/-- **IUT III, Theorem 3.11(iii)(a)–(d), as a statement** about a log-theta-lattice `L` with
bi-coric Kummer data `B` and mono-theta Kummer data `M` (see the module docstring). -/
structure Thm311iii (L : LogThetaLattice D) (B : BiCoricKummer L) (M : MonoThetaKummer D) :
    Prop where
  /-- (a) The horizontal arrows induce exactly the full poly-isomorphism of the coric strips. -/
  a_full : ∀ n m : ℤ, Function.Bijective (B.horizCor n m)
  /-- (a) The Kummer isomorphisms commute with the horizontal arrows. -/
  a_kummer : ∀ (n m : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m))),
    PrimeStrip.Iso.trans (ThetaLinkIso.unitEquiv _ _ θ) (B.kum (n + 1) m) =
      PrimeStrip.Iso.trans (B.kum n m) (B.horizCor n m θ)
  /-- (a), Theorem 1.5(iii): bi-coricity. -/
  a_biCoric : ∀ (n m m' : ℤ) (θ : ThetaLinkIso D (L.H (n, m)) (L.H (n + 1, m)))
    (θ' : ThetaLinkIso D (L.H (n, m')) (L.H (n + 1, m'))),
    B.horizCor n m θ = B.horizCor n m' θ' →
      PrimeStrip.Iso.trans (B.vertCor n m m') (ThetaLinkIso.unitEquiv _ _ θ') =
        PrimeStrip.Iso.trans (ThetaLinkIso.unitEquiv _ _ θ) (B.vertCor (n + 1) m m')
  /-- (b) The full poly-isomorphism of the environment strips, relative to the natural and the
  Kummer isomorphisms. -/
  b_env : ∀ n m : ℤ, Function.Bijective (B.horizEnv n m) ∧
    ∀ θ, B.horizEnv n m θ = fmuConj (PrimeStrip.Iso.trans (B.kum n m) (B.envIso n))
      (PrimeStrip.Iso.trans (B.kum (n + 1) m) (B.envIso (n + 1)))
      (ThetaLinkIso.unitEquiv _ _ θ)
  /-- (c) Cyclotomic rigidity of the mono-theta environments is compatible with the horizontal
  arrows, after arbitrary automorphisms of domain and codomain. -/
  c_cyc : ∀ (n m : ℤ) (w : FinitePlace D.Fmod) (hw : w ∈ D.VBad)
    (α : EtaleTheta.Env.Iso (M.envF (n, m) w hw) (M.envF (n, m) w hw))
    (β : EtaleTheta.Env.Iso (M.envF (n + 1, m) w hw) (M.envF (n + 1, m) w hw))
    (t x : (M.envF (n, m) w hw).carrier),
      (M.envF (n + 1, m) w hw).IsCyc (β.e (M.horizMap n m w hw (α.e t)))
          (β.e (M.horizMap n m w hw (α.e x))) ↔ (M.envF (n, m) w hw).IsCyc t x
  /-- (c), (d) The Θ-links are stabilized by arbitrary automorphisms of domain and codomain. -/
  cd_stable : ∀ (n m : ℤ) (f : (L.H (n, m)).Iso (L.H (n, m)))
    (g : (L.H (n + 1, m)).Iso (L.H (n + 1, m))), Function.Bijective (ThetaLinkIso.congr f g)
  /-- (c), (d) Every automorphism of the étale-like `D-Θ^{±ell}NF`-Hodge theater is realized. -/
  cd_labels : ∀ (a : ℤ × ℤ) (σ : (L.H a).labels.Iso (L.H a).labels),
    ∃ f : (L.H a).Iso (L.H a), f.labels = σ
  /-- (d) The global units of `F_mod` are trivial in the unit portions. -/
  d_fmod : ∀ {x : D.Fmod}, x ≠ 0 → (∀ w : FinitePlace D.Fmod, ‖embFin D w x‖ ≤ 1) →
    (∀ w : InfinitePlace D.Fmod, D.V.sectInf w (algebraMap D.Fmod D.Kt x) ≤ 1) →
      ∀ w : FinitePlace D.Fmod, ∃ h : ‖embFin D w x‖ = 1, fmodOxMu w x h = 1

/-- **Theorem 3.11(iii) holds in the model**, for every lattice, every bi-coric Kummer data and
every mono-theta Kummer data. -/
theorem thm311iii_model (L : LogThetaLattice D) (B : BiCoricKummer L) (M : MonoThetaKummer D) :
    Thm311iii L B M where
  a_full := B.horizCor_bijective
  a_kummer := B.kum_comm
  a_biCoric := B.biCoric_square
  b_env n m := ⟨B.horizEnv_bijective n m, B.horizEnv_eq n m⟩
  c_cyc := M.isCyc_horizMap_aut
  cd_stable _ _ f g := thetaLink_congr_bijective f g
  cd_labels a σ := labels_realized (L.H a) σ
  d_fmod hx hfin hinf w := fmodOxMu_eq_one hx hfin hinf w

/-- **Theorem 3.11 in full in the model**: parts (i), (ii)(a)–(c) (`Thm311LGP`), (iii)(a)–(d)
(`Thm311iii`) and Theorem 1.5(v) (`Thm15v`) hold for every LGP-Gaussian log-theta-lattice with
unit-induced, bi-coric and mono-theta Kummer data; Step (xi) is still the Scholze–Stix
inequality. -/
theorem thm311_full_model (L : LGPLattice D) (K : LatticeKummer L.toLogThetaLattice)
    (B : BiCoricKummer L.toLogThetaLattice) (M : MonoThetaKummer D) :
    Thm311LGP L K ∧ Thm311iii L.toLogThetaLattice B M ∧ Thm15v L.toLogThetaLattice ∧
      (XiPrinciple K ↔ SSIneq D) :=
  ⟨thm311LGP_model L K, thm311iii_model _ B M, thm15v_model _, xi_iff_ss_lgp (thm311LGP_model L K)⟩

end

end LogLink

end Iut
