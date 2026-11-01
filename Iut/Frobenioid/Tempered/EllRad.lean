/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllDescent
import Iut.Frobenioid.Tempered.EllTheta

/-!
# The radical layer (`n > 1`) under the Galois × deck action (MR18, route B-an)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

[EtTh] Ex 3.9(i)–(iii) (l.6074–6111) works with *all* tempered coverings of `Y^log`, including
those ramified at the cusps (only `D^ell_Y` is "unramified over the cusps", l.6085), and `Φ_W`
is a perfection. On such coverings live the radicals of meromorphic functions on
`Ÿ_∞ = 𝔾_m^an`, e.g. the `l`-th roots of `Θ̈` consumed by the mono-theta environments and
[EtTh] Prop 5.2(iii) (l.6946–6977). `EllGal.lean` gives the action of
`GalDeck t = Deck t ⋊ IsoAut t` on `Mero K` (the unramified layer `n = 1`); this
file extends it to a radical field `R ⊇ Mero K`.

## Non-canonicity (recorded honestly)

An automorphism `x • ·` of `Mero K` extends to an algebraic closure `R` of `Mero K`
(`exists_ext`, via `IsAlgClosure.equivOfEquiv`), but **not canonically**: two extensions differ
by an element of `Gal(R/Mero K)` (`ext_one_iff`), and there is in general no choice of extensions
forming a group action of `GalDeck t`. We therefore do not choose a section. The canonical object
is the group

  `ExtGalDeck t R = {(x, τ) ∈ GalDeck t × Aut(R) | τ ∘ ι = ι ∘ (x • ·)}`

of all extensions; it maps **onto** `GalDeck t` (`extRes_surjective`, `R` an algebraic
closure) with kernel `Gal(R/Mero K)` (the geometric ramified part: the automorphisms of the
coverings ramified at the cusps over `𝔾_m^an`). A group `G` (eventually `Π^tp`, MR18 T7c) acts on
the radical layer through a homomorphism `γ : G →* ExtGalDeck t R` — *this* is the choice, and
it is an explicit input, as is `γ` in `EllGal.lean`. For `G = ExtGalDeck t R` itself (`γ = id`)
nothing is chosen.

## Main results

* `ExtGalDeck t R`, `extRes`, `exists_ext`, `extRes_surjective`, `ext_one_iff`;
* `GalDeckRad γ` (`R` with the action of `G` through `γ`) and **`actCompat_galDeckRad`**:
  `ActCompat` on the radical layer for the Galois × deck action, so `radB`/`radData` apply
  (`radDataRad`); `isRad_isLogRad_of_pow` (a root of a log-meromorphic function is a
  log-meromorphic radical);
* **`l`-th roots of `Θ̈`**: `thetaRoot_pow_smul` (`(g • y)^l = x • Θ̈` for `γ g` over `x`),
  `rEllDiv_thetaRoot` (`div y = div Θ̈ / l`), and **`deck_thetaRoot`**: along the deck
  generator power `s^a` (Galois part trivial), `(g • y / y)^l = (-1)^{-a} Ü^{2a} s^{-a²}`, the
  radical form of [EtTh] Prop 1.4(ii) (l.1324–1328);
* **`L`-descent of radicals**: `IsLRad φ hφ y` (`yⁿ` comes from `Mero L` for some `n ≥ 1`),
  stable under `G` when `γ` is `L`-rational (`isLRad_smul`); `radBRadL`, `radDataRadL`,
  `radDataRadL_isFrobenioid`, and **`radDivRadL_eq_zero_iff`**: the kernel of the divisor map on
  `L`-radicals is `{y | yⁿ ∈ O_L^× for some n ≥ 1}` ([EtTh] Prop 3.4(ii) over `L` on the
  radical layer, cf. `radL_ker_iff`); `IsLRad` contains the unramified layer `B_L`
  (`isLRad_map`).

No converse descent (Ax–Sen–Tate) is claimed (lead decision after run 11).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open CategoryTheory TateCurvesTheta

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {t : TateParameter K}

/-! ### The group of extensions -/

section Ext

variable (t) (R : Type u) [Field R] [Algebra (Mero K) R]

/-- **The extensions of the Galois × deck action to `R`**: pairs `(x, τ)` with `τ ∈ Aut(R)`
restricting to `f ↦ x • f` on `Mero K`. -/
def ExtGalDeck : Subgroup (GalDeck t × RingAut R) where
  carrier := {x | ∀ f : Mero K, x.2 (Mero.ι R f) = Mero.ι R (galDeckHom t x.1 f)}
  one_mem' f := by
    change Mero.ι R f = Mero.ι R (galDeckHom t 1 f)
    rw [map_one]; rfl
  mul_mem' {x y} hx hy f := by
    change x.2 (y.2 (Mero.ι R f)) = Mero.ι R (galDeckHom t (x.1 * y.1) f)
    rw [hy, hx, map_mul, RingAut.mul_apply]
  inv_mem' {x} hx f := by
    change x.2.symm (Mero.ι R f) = Mero.ι R (galDeckHom t x.1⁻¹ f)
    apply x.2.injective
    rw [RingEquiv.apply_symm_apply, hx, ← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

variable {t R}

lemma ExtGalDeck.spec (x : ExtGalDeck t R) (f : Mero K) :
    (x : GalDeck t × RingAut R).2 (Mero.ι R f) =
      Mero.ι R (galDeckHom t (x : GalDeck t × RingAut R).1 f) := x.2 f

variable (t R) in
/-- **The restriction** `ExtGalDeck t R →* GalDeck t`. -/
def extRes : ExtGalDeck t R →* GalDeck t :=
  (MonoidHom.fst _ _).comp (ExtGalDeck t R).subtype

lemma extRes_apply (x : ExtGalDeck t R) : extRes t R x = (x : GalDeck t × RingAut R).1 := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- `Module.IsTorsionFree (Mero K) R` (needed by `IsAlgClosure`) times out at the default budget.
/-- **Every element of `GalDeck t` extends** to an algebraic closure `R` of `Mero K`
(non-canonically: `IsAlgClosure.equivOfEquiv` makes a choice). -/
theorem exists_ext [IsAlgClosure (Mero K) R] (x : GalDeck t) :
    ∃ τ : RingAut R, (x, τ) ∈ ExtGalDeck t R :=
  ⟨IsAlgClosure.equivOfEquiv R R (galDeckHom t x), fun f =>
    IsAlgClosure.equivOfEquiv_algebraMap R R (galDeckHom t x) f⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `Module.IsTorsionFree (Mero K) R` (needed by `IsAlgClosure`) times out at the default budget.
theorem extRes_surjective [IsAlgClosure (Mero K) R] : Function.Surjective (extRes t R) :=
  fun x => by
    obtain ⟨τ, hτ⟩ := exists_ext (R := R) x
    exact ⟨⟨(x, τ), hτ⟩, rfl⟩

/-- **The kernel of the restriction is `Gal(R/Mero K)`**: the extensions of the identity are
exactly the automorphisms of `R` fixing `Mero K` (the source of the non-canonicity). -/
theorem ext_one_iff (τ : RingAut R) :
    ((1 : GalDeck t), τ) ∈ ExtGalDeck t R ↔ ∀ f : Mero K, τ (Mero.ι R f) = Mero.ι R f := by
  change (∀ f : Mero K, τ (Mero.ι R f) = Mero.ι R (galDeckHom t 1 f)) ↔ _
  rw [map_one]
  rfl

/-- Two extensions of the same element differ by an element of `Gal(R/Mero K)`. -/
theorem ext_unique_up_to (x y : ExtGalDeck t R) (h : extRes t R x = extRes t R y) :
    ∀ f : Mero K, ((x : GalDeck t × RingAut R).2⁻¹ * (y : GalDeck t × RingAut R).2)
      (Mero.ι R f) = Mero.ι R f := by
  have hm : x⁻¹ * y ∈ (extRes t R).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := ExtGalDeck.spec (x⁻¹ * y)
  intro f
  rw [MonoidHom.mem_ker, extRes_apply] at hm
  have := h1 f
  rw [hm, map_one] at this
  exact this

end Ext

/-! ### The action of `G` on the radical layer and `ActCompat` -/

section Act

variable {R : Type u} [Field R] [Algebra (Mero K) R]
  {G : Type u} [Group G] (γ : G →* ExtGalDeck t R)

/-- `R` with the action of `G` through `γ : G →* ExtGalDeck t R`. -/
def GalDeckRad (_γ : G →* ExtGalDeck t R) : Type u := R

instance : Field (GalDeckRad γ) := inferInstanceAs (Field R)

instance : Algebra (Mero K) (GalDeckRad γ) := inferInstanceAs (Algebra (Mero K) R)

instance : MulSemiringAction G (GalDeckRad γ) :=
  MulSemiringAction.compHom R ((MonoidHom.snd _ _).comp ((ExtGalDeck t R).subtype.comp γ))

variable (t) in
/-- The action of `G` on the elliptic prime set through `extRes ∘ γ`. -/
abbrev galDeckRadPerm : G →* Equiv.Perm (EllPrime t) := (galDeckPerm t).comp ((extRes t R).comp γ)

lemma smul_ι (g : G) (f : Mero K) :
    g • Mero.ι (GalDeckRad γ) f = Mero.ι (GalDeckRad γ) (galDeckHom t (extRes t R (γ g)) f) :=
  ExtGalDeck.spec (γ g) f

/-- **A root of a log-meromorphic function is a log-meromorphic radical.** -/
lemma isRad_isLogRad_of_pow {R' : Type u} [Field R'] [Algebra (Mero K) R'] {y : R'} (hy0 : y ≠ 0)
    {n : ℕ} (hn : 0 < n) {x : Mero K} (hx : Mero.ι R' x = y ^ n) (hl : IsLogMero t x) :
    Mero.IsRad K y ∧ IsLogRad t y :=
  ⟨⟨n, hn, x, hx⟩, fun α hα => by rw [Mero.rord_eq hy0 hn hx, hl.2 α hα, Int.cast_zero, zero_div]⟩

/-- A log-meromorphic radical has a log-meromorphic power in `Mero K`. -/
lemma isLogMero_of_isLogRad {R' : Type u} [Field R'] [Algebra (Mero K) R'] {y : R'} (hy0 : y ≠ 0)
    {n : ℕ} (hn : 0 < n) {x : Mero K} (hx : Mero.ι R' x = y ^ n) (hl : IsLogRad t y) :
    IsLogMero t x :=
  ⟨Mero.ne_zero_of_ι_eq hy0 hx, fun α hα => by
    have h := hl α hα
    rw [Mero.rord_eq hy0 hn hx, div_eq_zero_iff] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h (by exact_mod_cast hn.ne')⟩

/-- **`ActCompat` on the radical layer for the Galois × deck action**: for any
`γ : G →* ExtGalDeck t R`, `G` maps log-meromorphic radicals to log-meromorphic radicals and
`div(g • y) = div(y) ∘ g⁻¹` on `ℤ ⊕ Cusps`. -/
theorem actCompat_galDeckRad (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    ActCompat t s (galDeckRadPerm t γ) (GalDeckRad γ) := by
  intro g y hy0 hrad hl
  obtain ⟨n, hn, x, hx⟩ := hrad
  have hlx := isLogMero_of_isLogRad hy0 hn hx hl
  obtain ⟨h1, h2⟩ := ellDiv_galDeck hs (extRes t R (γ g)) hlx
  have hgy0 : g • y ≠ 0 := (smul_ne_zero_iff_ne _).mpr hy0
  have hx' : Mero.ι (GalDeckRad γ) (galDeckHom t (extRes t R (γ g)) x) = (g • y) ^ n := by
    rw [← smul_ι, hx, smul_pow']
  obtain ⟨hr', hl'⟩ := isRad_isLogRad_of_pow hgy0 hn hx' h1
  refine ⟨hr', hl', fun p => ?_⟩
  rw [rEllDiv_eq hval hs hgy0 hn hx', rEllDiv_eq hval hs hy0 hn hx]
  change ellDiv t s _ p / n = ellDiv t s x (galDeckRadPerm t γ g⁻¹ p) / n
  rw [h2, map_inv]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The tempered Frobenioid of the radical layer under the Galois × deck action**. -/
abbrev radDataRad (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    TemperedFrobenioidData G :=
  radData s (galDeckRadPerm t γ) (GalDeckRad γ) hval hs (actCompat_galDeckRad γ hval hs)

theorem radDataRad_isFrobenioid (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) :
    IsFrobenioid (Model.toElem (radDataRad γ hval hs).Φ₀ (radDataRad γ hval hs).B₀
      (radDataRad γ hval hs).div₀) :=
  (radDataRad γ hval hs).isFrobenioid

end Act

/-! ### The `l`-th roots of `Θ̈` under the action -/

section ThetaRoot

variable {R : Type u} [Field R] [Algebra (Mero K) R]
  {G : Type u} [Group G] (γ : G →* ExtGalDeck t R)

/-- **`G` permutes the `l`-th roots of the transforms of `Θ̈`**: `(g • y)^l = x • Θ̈` where `x`
is the image of `γ g` in `GalDeck t`. -/
theorem thetaRoot_pow_smul {y : GalDeckRad γ} {l : ℕ}
    (hy : y ^ l = Mero.ι (GalDeckRad γ) (Mero.ofE (thetaDd t))) (g : G) :
    (g • y) ^ l =
      Mero.ι (GalDeckRad γ) (galDeckHom t (extRes t R (γ g)) (Mero.ofE (thetaDd t))) := by
  rw [← smul_pow', hy, smul_ι]

/-- **An `l`-th root of `Θ̈` is a log-meromorphic radical with divisor `div(Θ̈)/l`**
(order `1/l` at the cusps, `-a²/(2l)` on the component `a`). -/
theorem rEllDiv_thetaRoot {R' : Type u} [Field R'] [Algebra (Mero K) R'] (h2 : (2 : K) ≠ 0)
    (hval : ValueGroupRat t) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {y : R'} (hy0 : y ≠ 0) {l : ℕ}
    (hl : 0 < l) (hy : y ^ l = Mero.ι R' (Mero.ofE (thetaDd t))) :
    Mero.IsRad K y ∧ IsLogRad t y ∧
      rEllDiv t s y =
        (Sum.elim (fun a : ℤ => -((a : ℚ) ^ 2) / (2 * l)) fun _ => 1 / l : EllPrime t → ℚ) := by
  obtain ⟨hr, hlr⟩ := isRad_isLogRad_of_pow hy0 hl hy.symm (isLogMero_thetaDd (t := t))
  refine ⟨hr, hlr, ?_⟩
  rw [rEllDiv_eq hval hs hy0 hl hy.symm, ellDiv_thetaDd h2 hs]
  funext p
  rcases p with a | α
  · simp only [Sum.elim_inl]
    field_simp
  · simp

/-- **[EtTh] Prop 1.4(ii) on the `l`-th roots of `Θ̈`** (l.1324–1328): if `γ g` lies over the
deck transformation `s^a` with trivial Galois part, then `g` moves an `l`-th root `y` of `Θ̈` by an
`l`-th root of `(-1)^{-a} · Ü^{2a} · s^{-a²}`. -/
theorem deck_thetaRoot {s : Kˣ} (hs : (s : K) ^ 2 = t.q) {y : GalDeckRad γ} (hy0 : y ≠ 0)
    {l : ℕ} (hy : y ^ l = Mero.ι (GalDeckRad γ) (Mero.ofE (thetaDd t))) (g : G) (a : ℤ)
    (hleft : (extRes t R (γ g)).left = Deck.gen t hs ^ a)
    (hright : (extRes t R (γ g)).right = 1) :
    (g • y / y) ^ l = Mero.ι (GalDeckRad γ) (Mero.const ((-1 : K) ^ (-a)) *
      Mero.ofE (Entire.mono 1) ^ (2 * a) * Mero.const (s : K) ^ (-(a ^ 2))) := by
  have hθ : Mero.ι (GalDeckRad γ) (Mero.ofE (thetaDd t)) ≠ 0 := by
    rw [← hy]; exact pow_ne_zero _ hy0
  have e : galDeckHom t (extRes t R (γ g)) (Mero.ofE (thetaDd t)) =
      Mero.scale (s ^ (-a)) (Mero.ofE (thetaDd t)) := by
    rw [galDeckHom_apply, hleft, hright, Mero.gal_one_apply, ← zpow_neg, Subgroup.coe_zpow]
    rfl
  rw [div_pow, thetaRoot_pow_smul γ hy, hy, e, Iut.Frobenioid.scale_thetaDd_mero hs, div_eq_iff hθ]
  simp only [Mero.ι, map_mul]
  ring

end ThetaRoot

/-! ### `L`-descent of radicals -/

section Descent

variable {L : Type u} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (φ : L →+* K) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
  {R : Type u} [Field R] [Algebra (Mero K) R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (γ : G →* ExtGalDeck t R)

variable {R' : Type u} [Field R'] [Algebra (Mero K) R'] in
/-- **`y` is a radical over `L`**: some power `yⁿ`, `n ≥ 1`, is (the image of) a meromorphic
function defined over `L`. -/
def IsLRad (y : R') : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ z : Mero L, Mero.ι R' (Mero.map φ hφ z) = y ^ n

variable {φ hφ γ}

/-- `L`-radicals are stable under an `L`-rational action. -/
lemma isLRad_smul (hγ : IsLRat φ ((extRes t R).comp γ)) (g : G) {y : GalDeckRad γ}
    (hy : IsLRad φ hφ y) : IsLRad φ hφ (g • y) := by
  obtain ⟨n, hn, z, hz⟩ := hy
  obtain ⟨z', hz'⟩ := smul_map_mem (hφ := hφ) hγ g z
  refine ⟨n, hn, z', ?_⟩
  rw [← smul_pow', ← hz, smul_ι]
  exact congrArg (Mero.ι (GalDeckRad γ)) hz'.symm

variable (s : Kˣ) (hval : ValueGroupRat t) (hs : (s : K) ^ 2 = t.q)

variable (φ hφ γ) in
/-- `B_L^rad(G/H)`: the elements of `B(G/H)` that are radicals over `L`. -/
def subRadL (A : OrbitObj G) :
    AddSubgroup ((radB s (galDeckRadPerm t γ) (GalDeckRad γ)
      (actCompat_galDeckRad γ hval hs)).obj A) where
  carrier := {x | IsLRad φ hφ (rv x)}
  zero_mem' := ⟨1, one_pos, 1, by rw [map_one, pow_one]; exact map_one _⟩
  add_mem' {x y} hx hy := by
    obtain ⟨n, hn, z, hz⟩ := hx
    obtain ⟨m, hm, z', hz'⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, z ^ m * z' ^ n, ?_⟩
    change _ = (rv x * rv y) ^ (n * m)
    rw [map_mul, map_pow, map_pow, Mero.ι_mul, Mero.ι_pow, Mero.ι_pow, hz, hz', mul_pow,
      ← pow_mul, ← pow_mul, mul_comm m n]
  neg_mem' {x} hx := by
    obtain ⟨n, hn, z, hz⟩ := hx
    refine ⟨n, hn, z⁻¹, ?_⟩
    change _ = ((((Additive.toMul x)⁻¹ : radSub t (R := GalDeckRad γ) A.H) :
      (GalDeckRad γ)ˣ) : GalDeckRad γ) ^ n
    rw [InvMemClass.coe_inv, Units.val_inv_eq_inv_val, map_inv₀, Mero.ι, map_inv₀, ← Mero.ι, hz,
      inv_pow]

lemma mem_subRadL_pb (hγ : IsLRat φ ((extRes t R).comp γ)) {A A' : OrbitObj G} (f : A ⟶ A')
    (x : (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)).obj A')
    (hx : x ∈ subRadL φ hφ γ s hval hs A') :
    (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)).pb f x ∈
      subRadL φ hφ γ s hval hs A :=
  isLRad_smul hγ (rep f) hx

lemma exists_mem_subRadL_pb (hγ : IsLRat φ ((extRes t R).comp γ)) {A A' : OrbitObj G}
    (f : A ⟶ A') (hf : IsFSM f)
    (y : (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)).obj A)
    (hy : y ∈ subRadL φ hφ γ s hval hs A) :
    ∃ x ∈ subRadL φ hφ γ s hval hs A',
      (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)).pb f x =
        y := by
  obtain ⟨x, hxy⟩ :=
    (GrpOn.pb_bijective_of_fsm
      (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)) f hf).2 y
  refine ⟨x, ?_, hxy⟩
  have h1 : rep f • rv x = rv y := congrArg rv hxy
  have h2 : rv x = (rep f)⁻¹ • rv y := by rw [← h1, inv_smul_smul]
  change IsLRad φ hφ (rv x)
  rw [h2]
  exact isLRad_smul hγ _ hy

variable (φ hφ γ) in
/-- **`B_L^rad`**: the group-like monoid of log-meromorphic radicals over `L`. -/
def radBRadL (hγ : IsLRat φ ((extRes t R).comp γ)) : GrpOn.{u} (OrbitObj G) :=
  (radB s (galDeckRadPerm t γ) (GalDeckRad γ) (actCompat_galDeckRad γ hval hs)).sub
    (subRadL φ hφ γ s hval hs) (fun f x hx => mem_subRadL_pb s hval hs hγ f x hx)
    (fun f hf y hy => exists_mem_subRadL_pb s hval hs hγ f hf y hy)

variable (φ hφ γ) in
/-- **The tempered Frobenioid of `L`-radicals** (B-an, coverings ramified at the cusps):
`Φ₀` the `ℚ`-divisors on the elliptic prime set (over `Ω`), `B₀ = B_L^rad`. -/
def radDataRadL (hγ : IsLRat φ ((extRes t R).comp γ)) : TemperedFrobenioidData G where
  Φ₀ := PrimeDiv.divMonoid G (PrimeAct (galDeckRadPerm t γ)) ℚ
  B₀ := radBRadL φ hφ γ s hval hs hγ
  div₀ := DivHom.restrict (fun f x hx => mem_subRadL_pb s hval hs hγ f x hx)
    (fun f hf y hy => exists_mem_subRadL_pb s hval hs hγ f hf y hy)
    (radDiv s (galDeckRadPerm t γ) (GalDeckRad γ) hval hs (actCompat_galDeckRad γ hval hs))

theorem radDataRadL_isFrobenioid (hγ : IsLRat φ ((extRes t R).comp γ)) :
    IsFrobenioid (Model.toElem (radDataRadL φ hφ γ s hval hs hγ).Φ₀
      (radDataRadL φ hφ γ s hval hs hγ).B₀ (radDataRadL φ hφ γ s hval hs hγ).div₀) :=
  (radDataRadL φ hφ γ s hval hs hγ).isFrobenioid

/-- **The kernel of the divisor map on `L`-radicals** ([EtTh] Def 3.3, Prop 3.4(ii) over `L`,
radical layer): an element of `B_L^rad(G/H)` has divisor `0` iff some power `yⁿ`, `n ≥ 1`, is a
scalar `c ∈ L` with `‖c‖ = 1`. (Only up to `n`-th powers: the root `y` itself is a scalar of
`O_Ω^×` that need not lie in `L`.) -/
theorem radDivRadL_eq_zero_iff [IsAlgClosed K] (hγ : IsLRat φ ((extRes t R).comp γ))
    {A : OrbitObj G} (x : (radBRadL φ hφ γ s hval hs hγ).obj A) :
    (radDataRadL φ hφ γ s hval hs hγ).div₀.app A x = 0 ↔
      ∃ n : ℕ, 0 < n ∧ ∃ c : L, ‖c‖ = 1 ∧
        Mero.ι (GalDeckRad γ) (Mero.const (φ c)) = rv x.1 ^ n := by
  change (radDiv s (galDeckRadPerm t γ) (GalDeckRad γ) hval hs
    (actCompat_galDeckRad γ hval hs)).app A x.1 = 0 ↔ _
  rw [radDiv_eq_zero_iff]
  obtain ⟨n, hn, z, hz⟩ := x.2
  constructor
  · rintro ⟨c, hc, h⟩
    have e : Mero.map φ hφ z = Mero.const (c ^ n) := by
      apply Mero.ι_injective (R := GalDeckRad γ)
      rw [hz, h, ← Mero.ι_pow, ← Mero.const_pow]
    obtain ⟨c', hc', -⟩ := Mero.exists_eq_const_of_map_eq φ hφ e
    refine ⟨n, hn, c', ?_, ?_⟩
    · rw [← hφ, hc', norm_pow, hc, one_pow]
    · rw [hc', Mero.const_pow, Mero.ι_pow, h]
  · rintro ⟨m, hm, c, hc, h⟩
    have hc0 : φ c ≠ 0 := fun h0 => by
      have h1 := hφ c
      rw [h0, norm_zero, hc] at h1
      exact zero_ne_one h1
    obtain ⟨e, he, he'⟩ := Mero.eq_const_of_pow_eq_const hm h hc0
    refine ⟨e, ?_, he'⟩
    have : ‖e‖ ^ m = 1 := by rw [← norm_pow, he, hφ, hc]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) hm.ne').mp this

/-- The unramified layer: a radical whose first power comes from `Mero L` is an `L`-radical
(so `B_L^rad` contains the image of `B_L` of `EllDescent.lean`). -/
lemma isLRad_map {R' : Type u} [Field R'] [Algebra (Mero K) R'] (z : Mero L) :
    IsLRad φ hφ (Mero.ι R' (Mero.map φ hφ z)) :=
  ⟨1, one_pos, z, (pow_one _).symm⟩

end Descent

end Iut.Frobenioid.BAn
