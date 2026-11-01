/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllGal

/-!
# `L`-descent of `B₀` (MR18, route B-an)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

In [EtTh] §3 the tempered coverings and their functions are defined over a finite extension `L`
of `ℚ_p`, while divisors are computed geometrically. In route B-an the geometric model is
`Mero Ω` (`Ω` complete, algebraically closed, with an isometric `φ : L → Ω`, e.g. `ℂ_p`,
`PadicEmbed.lean`), on which `G` acts through `γ : G →* GalDeck t` (`EllGal.lean`). This file
cuts out the functions **defined over `L`**:

* `GrpOn.sub`: a sub-functor of a group-like monoid closed under pull-backs and their inverses
  along FSM-morphisms is again a group-like monoid; `DivHom.restrict`.
* `IsLRat φ hφ γ` (explicit input): the action of `G` is defined over `L` — its Galois part lies
  in `Gal(Ω/L)` (`galL φ`) and its deck part in `φ(L)^×`.
* `Mero.map_scale`, `Mero.gal_map_of_fix`: the image `Mero.map φ (Mero L)` is stable under the
  action (`smul_map_mem`).
* `radBL`: `B_L(G/H)` = the `H`-fixed log-meromorphic functions of `B(G/H)` that come from
  `Mero L` (the unramified layer `n = 1` of `RatFunRadL.lean`, with `ψ = Mero.map φ`), and the
  divisor map `radDivL` (divisors over `Ω`); `radDataL`, `radDataL_isFrobenioid`;
* **`radDivL_eq_zero_iff`**: the kernel of `B_L(G/H) → Φ^gp(G/H)` is `O_L^×` ([EtTh] Def 3.3,
  Prop 3.4(ii) over `L`; via `Mero.exists_eq_const_of_map_eq`);
* `gal_rv_radBL`: elements of `B_L` are fixed by `Gal(Ω/L)`. (The converse, that
  `Gal(Ω/L)`-invariant elements come from `L`, is Ax–Sen–Tate for the coefficients; it is not
  used and not claimed here.)
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid

open CategoryTheory

universe u v w

/-! ### Sub-functors of group-like monoids -/

section Sub

variable {D : Type u} [Category.{v} D] (B : GrpOn.{w} D) (S : ∀ A, AddSubgroup (B.obj A))
  (hpb : ∀ {A A' : D} (f : A ⟶ A') (x : B.obj A'), x ∈ S A' → B.pb f x ∈ S A)
  (hfsm : ∀ {A A' : D} (f : A ⟶ A'), IsFSM f → ∀ y ∈ S A, ∃ x ∈ S A', B.pb f x = y)

/-- **A sub-functor of a group-like monoid**, stable under pull-backs and under their inverses
along FSM-morphisms. -/
def GrpOn.sub : GrpOn.{w} D where
  obj A := S A
  pb f :=
    { toFun := fun x => ⟨B.pb f x.1, hpb f x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  pb_id A x := Subtype.ext (B.pb_id A x.1)
  pb_comp f g x := Subtype.ext (B.pb_comp f g x.1)
  pb_injective f x y h := Subtype.ext (B.pb_injective f (congrArg Subtype.val h))
  pb_bijective_of_fsm f hf := ⟨fun x y h => Subtype.ext (B.pb_injective f (congrArg Subtype.val h)),
    fun y => by
      obtain ⟨x, hx, hxy⟩ := hfsm f hf y.1 y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

variable {B S} in
/-- The restriction of a divisor map to a sub-functor. -/
def DivHom.restrict {Φ : GrpOn.{w} D} (d : DivHom B Φ) : DivHom (B.sub S hpb hfsm) Φ where
  app A := (d.app A).comp (S A).subtype
  natural f x := d.natural f x.1

end Sub

namespace BAn

open TateCurvesTheta

/-! ### `L`-rational actions -/

variable {L : Type u} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K} (φ : L →+* K) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

/-- Galois elements fixing `φ(L)` fix the functions defined over `L`. -/
lemma Mero.gal_map_of_fix (σ : IsoAut t) (hσ : (σ : RingAut K) ∈ galL φ) (z : Mero L) :
    Mero.gal σ (Mero.map φ hφ z) = Mero.map φ hφ z := by
  rw [Mero.gal, Mero.map_map]
  exact Mero.map_congr _ _ hφ (RingHom.ext fun a => hσ.2 a) z

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (γ : G →* GalDeck t)

/-- **The action of `G` is defined over `L`** (explicit input): its Galois part fixes `φ(L)`
and its deck part lies in `φ(L)^×`. -/
def IsLRat : Prop :=
  ∀ g : G, (((γ g).right : IsoAut t) : RingAut K) ∈ galL φ ∧
    ∃ c : Lˣ, Units.map φ.toMonoidHom c = (((γ g).left : Deck t) : Kˣ)

variable {φ hφ γ}

/-- The functions defined over `L` are stable under `G`. -/
lemma smul_map_mem (hγ : IsLRat φ γ) (g : G) (z : Mero L) :
    ∃ z' : Mero L, g • (show GalDeckMero γ from Mero.map φ hφ z) = Mero.map φ hφ z' := by
  obtain ⟨hgal, c, hc⟩ := hγ g
  refine ⟨Mero.scale c⁻¹ z, ?_⟩
  change galDeckHom t (γ g) (Mero.map φ hφ z) = _
  rw [galDeckHom_apply, Mero.gal_map_of_fix φ hφ _ hgal, Mero.map_scale, map_inv, hc,
    Subgroup.coe_inv]

variable (s : Kˣ) (hval : ValueGroupRat t) (hs : (s : K) ^ 2 = t.q)

variable (φ hφ γ) in
/-- `B_L(G/H)`: the elements of `B(G/H)` defined over `L`. -/
def subL (A : OrbitObj G) :
    AddSubgroup ((radB s ((galDeckPerm t).comp γ) (GalDeckMero γ)
      (actCompat_galDeck γ hval hs)).obj A) where
  carrier := {x | ∃ z : Mero L, rv x = Mero.map φ hφ z}
  zero_mem' := ⟨1, by rw [map_one]; rfl⟩
  add_mem' {x y} hx hy := by
    obtain ⟨z, hz⟩ := hx
    obtain ⟨z', hz'⟩ := hy
    exact ⟨z * z', by rw [map_mul, ← hz, ← hz']; rfl⟩
  neg_mem' {x} hx := by
    obtain ⟨z, hz⟩ := hx
    refine ⟨z⁻¹, ?_⟩
    rw [map_inv₀, ← hz]
    change ((((Additive.toMul x)⁻¹ : radSub t (R := GalDeckMero γ) A.H) : (GalDeckMero γ)ˣ) :
      GalDeckMero γ) = _
    rw [InvMemClass.coe_inv, Units.val_inv_eq_inv_val]
    rfl

lemma mem_subL_pb (hγ : IsLRat φ γ) {A A' : OrbitObj G} (f : A ⟶ A')
    (x : (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)).obj A')
    (hx : x ∈ subL φ hφ γ s hval hs A') :
    (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)).pb f x ∈
      subL φ hφ γ s hval hs A := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨z', hz'⟩ := smul_map_mem (hφ := hφ) hγ (rep f) z
  refine ⟨z', ?_⟩
  change rep f • rv x = _
  rw [hz]
  exact hz'

lemma exists_mem_subL_pb (hγ : IsLRat φ γ) {A A' : OrbitObj G} (f : A ⟶ A') (hf : IsFSM f)
    (y : (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)).obj A)
    (hy : y ∈ subL φ hφ γ s hval hs A) :
    ∃ x ∈ subL φ hφ γ s hval hs A',
      (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)).pb f x =
        y := by
  obtain ⟨x, hxy⟩ :=
    (GrpOn.pb_bijective_of_fsm
      (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)) f hf).2 y
  refine ⟨x, ?_, hxy⟩
  obtain ⟨z, hz⟩ := hy
  obtain ⟨z', hz'⟩ := smul_map_mem (hφ := hφ) hγ (rep f)⁻¹ z
  refine ⟨z', ?_⟩
  have h1 : rep f • rv x = rv y := congrArg rv hxy
  rw [← hz', ← hz, ← h1, inv_smul_smul]

variable (φ hφ γ) in
/-- **`B_L`**: the group-like monoid of log-meromorphic functions defined over `L`. -/
def radBL (hγ : IsLRat φ γ) : GrpOn.{u} (OrbitObj G) :=
  (radB s ((galDeckPerm t).comp γ) (GalDeckMero γ) (actCompat_galDeck γ hval hs)).sub
    (subL φ hφ γ s hval hs) (fun f x hx => mem_subL_pb s hval hs hγ f x hx)
    (fun f hf y hy => exists_mem_subL_pb s hval hs hγ f hf y hy)

variable (φ hφ γ) in
/-- **The tempered Frobenioid over `L`** (B-an): `Φ₀` the `ℚ`-divisors on the elliptic prime
set (computed over `Ω`), `B₀ = B_L`. -/
def radDataL (hγ : IsLRat φ γ) : TemperedFrobenioidData G where
  Φ₀ := PrimeDiv.divMonoid G (PrimeAct ((galDeckPerm t).comp γ)) ℚ
  B₀ := radBL φ hφ γ s hval hs hγ
  div₀ := DivHom.restrict (fun f x hx => mem_subL_pb s hval hs hγ f x hx)
    (fun f hf y hy => exists_mem_subL_pb s hval hs hγ f hf y hy)
    (radDiv s ((galDeckPerm t).comp γ) (GalDeckMero γ) hval hs (actCompat_galDeck γ hval hs))

theorem radDataL_isFrobenioid (hγ : IsLRat φ γ) :
    IsFrobenioid (Model.toElem (radDataL φ hφ γ s hval hs hγ).Φ₀ (radDataL φ hφ γ s hval hs hγ).B₀
      (radDataL φ hφ γ s hval hs hγ).div₀) :=
  (radDataL φ hφ γ s hval hs hγ).isFrobenioid

/-- **The kernel of the divisor map of `B_L` is `O_L^×`** ([EtTh] Def 3.3, Prop 3.4(ii) over
`L`): an element of `B_L(G/H)` has divisor `0` iff it is a scalar `c ∈ L` with `‖c‖ = 1`. -/
theorem radDivL_eq_zero_iff [IsAlgClosed K] (hγ : IsLRat φ γ) {A : OrbitObj G}
    (x : (radBL φ hφ γ s hval hs hγ).obj A) :
    (radDataL φ hφ γ s hval hs hγ).div₀.app A x = 0 ↔
      ∃ c : L, ‖c‖ = 1 ∧ rv x.1 = Mero.const (φ c) := by
  change (radDiv s ((galDeckPerm t).comp γ) (GalDeckMero γ) hval hs
    (actCompat_galDeck γ hval hs)).app A x.1 = 0 ↔ _
  rw [radDiv_eq_zero_iff]
  obtain ⟨z, hz⟩ := x.2
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨c', hc', rfl⟩ := Mero.exists_eq_const_of_map_eq φ hφ (hz.symm.trans h)
    exact ⟨c', by rw [← hφ, hc', hc], by rw [hz, Mero.map_const]⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨φ c, by rw [hφ, hc], h⟩

/-- **Elements of `B_L` are fixed by `Gal(Ω/L)`.** -/
theorem gal_rv_radBL (hγ : IsLRat φ γ) {A : OrbitObj G} (x : (radBL φ hφ γ s hval hs hγ).obj A)
    (σ : IsoAut t) (hσ : (σ : RingAut K) ∈ galL φ) :
    Mero.gal σ (rv (R := GalDeckMero γ) x.1) = rv x.1 := by
  obtain ⟨z, hz⟩ := x.2
  rw [hz]
  exact Mero.gal_map_of_fix φ hφ σ hσ z

end BAn

end Iut.Frobenioid
