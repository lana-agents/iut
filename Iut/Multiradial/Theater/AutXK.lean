/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.AutCK

/-!
# `Aut(X̲_K)`, `Aut_±`, `Aut_+`, `Aut_csp` (MR22 T6, IUT I Definition 6.1 (v))

IUT I, Definition 6.1 (v) (l.10845–10910 of `~/iut-scratch/papers/txt/Inter-universal
Teichmuller Theory I.txt`): `D^⊚± = B(X̲_K)⁰`; the rank-one quotient gives a surjection
`Aut(D^⊚±) ↠ F_ℓ^⋇` with kernel `Aut_±(D^⊚±)`; `Aut_csp(D^⊚±) ⊆ Aut_±(D^⊚±)` fixes the cusps of
`X̲_K`; `Aut_K(X̲_K) ≅ Aut_±/Aut_csp ≅ F_ℓ^{⋊±}`; `Aut_+` the index-two subgroup containing
`Aut_csp`.

As for `C̲_K` (`AutCK.lean`): **`AutXK D = N(π₁(X̲_K))/π₁(X̲_K)`** inside `π₁(C_{F_mod})`. The image
of `π₁(X̲_K)` in `π₁(C_K)` is the kernel of the dihedral action `rhoCK` on the cusps
`Q ≅ F_ℓ` of `X̲_K` (`X̲_K → C_K` is Galois with group `F_ℓ ⋊ {±1}`), so `γ ∈ N(π₁(X̲_K))`
acts on the cusps by an affine map `z ↦ a z + b` (`psiHom`, `AutScalar.lean`):

* **`psiXK : Aut(X̲_K) → Sym(F_ℓ)`**, the action on the cusps of `X̲_K`; **`chiXK`**:
  `a mod ±1 ∈ F_ℓ^⋇`;
* **`AutPm D = ker chiXK`** (`Aut_±`), **`AutCsp D = ker psiXK`** (`Aut_csp`), **`AutPlus D`**
  (`a = 1`, `Aut_+`), `AutCsp ≤ AutPlus ≤ AutPm`;
* **`psiXK_map_autPm`**: `psiXK(Aut_±) = F_ℓ ⋊ {±1}` (`Aut_±/Aut_csp ≅ F_ℓ^{⋊±}`), the
  `K`-linear automorphisms `π₁(C_K)/π₁(X̲_K)` already giving everything;
* `autCspPoly`, **`phiEllCsp`**: `Aut_csp(D^⊚±)` as a poly-automorphism and the instance of
  `Capsule.phiEll`.
-/

noncomputable section

namespace Iut.Multiradial.Theater

open CategoryTheory Topology Iut.HodgeTheater Iut.Anabelian Pi1.Profinite CurvesJacobian.Cusp
  Iut.Frobenioid Belyi.Anabelian PrimeStrip

variable (D : InitialThetaData.{0})

/-- The prime `ℓ` of initial Θ-data is an odd prime. -/
local instance oddPrimeEllAutXK : HodgeTheater.OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

/-- `π₁(X̲_K) → π₁(C_K)`. -/
def piXKToCKdown : PiXK D →ₜ* piCK D := (piCKuToCK D).comp (piXKToCK D)

/-- **`π₁(X̲_K) ↪ π₁(C_{F_mod})`.** -/
def iotaXK : PiXK D →ₜ* piCmod D := (piCKToCmod D).comp (piXKToCKdown D)

lemma isOpenEmbedding_iotaXK : IsOpenEmbedding (iotaXK D) := by
  have e : ⇑(iotaXK D) = piCKToCmod D ∘ piCKuToCK D ∘ piXKToCK D := rfl
  rw [e]
  exact (isOpenEmbedding_piCKToCmod D).comp
    (D.orb.pi1CKu_to_CK_isOpenEmbedding.comp D.orb.pi1XKu_to_CKu_isOpenEmbedding)

/-- The normaliser `N(π₁(X̲_K))` in `π₁(C_{F_mod})`. -/
abbrev normXK : Subgroup (piCmod D) := normRange (iotaXK D)

/-- **`Aut(X̲_K) = N(π₁(X̲_K)) / π₁(X̲_K)`** (IUT I, Definition 6.1 (v)). -/
abbrev AutXK : Type := normXK D ⧸ rangeIn (iotaXK D)

/-- **`Aut(X̲_K) ↪ Out(π₁(X̲_K))`.** -/
def outXK : AutXK D → OuterHom (PiXK D) (PiXK D) :=
  outOf (isOpenEmbedding_iotaXK D).injective (isOpenEmbedding_iotaXK D).isEmbedding
    (isSlim_piCmod D) (isOpenEmbedding_iotaXK D).isOpen_range

theorem outXK_injective : Function.Injective (outXK D) :=
  outOf_injective _ _ _ _

lemma range_XK_eq_ker : (piXKToCKdown D).toMonoidHom.range = (rhoCK D).ker := by
  ext y
  rw [MonoidHom.mem_ker]
  exact mem_range_XK_iff D y

/-- `γ ∈ N(π₁(X̲_K))` acts on `π₁(C_K)` preserving `π₁(X̲_K) = ker ρ`. -/
lemma normXK_mem_stabAut (γ : normXK D) :
    ((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) ∈ stabAut (rhoCK D).ker := by
  rw [← range_XK_eq_ker]
  exact mem_stabAut_of_norm D (piXKToCKdown D).toMonoidHom γ γ.2

/-- `N(π₁(X̲_K)) → Aut(π₁(C_K), π₁(X̲_K))`. -/
def normToStabXK : normXK D →* stabAut (rhoCK D).ker :=
  (((contAut (piCK D)).subtype.comp ((piCmodToAut D).comp (normXK D).subtype))).codRestrict _
    (normXK_mem_stabAut D)

/-- `π₁(X̲_K)` acts on `π₁(C_K)` by conjugation by elements of `ker ρ`. -/
lemma normToStabXK_of_mem (γ : normXK D) (hγ : γ ∈ rangeIn (iotaXK D)) :
    ∃ g : piCK D, rhoCK D g = 1 ∧
      normToStabXK D γ = ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩ := by
  rw [Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, hu⟩ := hγ
  have hu' : piCKToCmod D (piXKToCKdown D u) = (γ : piCmod D) := hu
  refine ⟨piXKToCKdown D u, (mem_range_XK_iff D _).1 ⟨u, rfl⟩, ?_⟩
  refine Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective ?_)
  change piCKToCmod D (((piCmodToAut D γ : contAut (piCK D)) : MulAut (piCK D)) x) =
    piCKToCmod D (piXKToCKdown D u * x * (piXKToCKdown D u)⁻¹)
  rw [piCKToCmod_piCmodToAut, map_mul, map_mul, map_inv, hu']

/-- The affine action of `N(π₁(X̲_K))` on the cusps `F_ℓ` of `X̲_K`. -/
def psiN : normXK D →* Equiv.Perm (ZMod D.ℓ) := (psiHom (isDihedralFull_rhoCK D)).comp
  (normToStabXK D)

lemma psiN_eq_one (γ : normXK D) (hγ : γ ∈ rangeIn (iotaXK D)) : psiN D γ = 1 := by
  obtain ⟨g, hg, he⟩ := normToStabXK_of_mem D γ hγ
  change psiHom (isDihedralFull_rhoCK D) (normToStabXK D γ) = 1
  obtain ⟨-, -, hψ⟩ := affOf_conj (isDihedralFull_rhoCK D) g
  rw [he, hψ, hg]

/-- **`ψ : Aut(X̲_K) → Sym(F_ℓ)`, the action on the cusps of `X̲_K`.** -/
def psiXK : AutXK D →* Equiv.Perm (ZMod D.ℓ) :=
  QuotientGroup.lift _ (psiN D) fun γ hγ => (MonoidHom.mem_ker).2 (psiN_eq_one D γ hγ)

/-- The linear part `N(π₁(X̲_K)) → F_ℓ^×`. -/
def linN : normXK D →* (ZMod D.ℓ)ˣ := (linHom (isDihedralFull_rhoCK D)).comp (normToStabXK D)

lemma linN_mem_pmSub (γ : normXK D) (hγ : γ ∈ rangeIn (iotaXK D)) : linN D γ ∈ pmSub D.ℓ := by
  obtain ⟨g, -, he⟩ := normToStabXK_of_mem D γ hγ
  obtain ⟨ε, hε, -⟩ := affOf_conj (isDihedralFull_rhoCK D) g
  change linHom (isDihedralFull_rhoCK D) (normToStabXK D γ) ∈ pmSub D.ℓ
  rw [he]
  change (affOf (isDihedralFull_rhoCK D) ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩).1 ∈ pmSub D.ℓ
  rw [hε]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · left; simp
  · right; ext; simp

/-- **`Aut(X̲_K) ↠ F_ℓ^⋇`** (the action on the rank-one quotient, up to `±1`). -/
def chiXK : AutXK D →* FlStar D.ℓ :=
  QuotientGroup.map _ _ (linN D) fun γ hγ => linN_mem_pmSub D γ hγ

/-- **`Aut_±(D^⊚±) = ker(Aut ↠ F_ℓ^⋇)`.** -/
def AutPm : Subgroup (AutXK D) := (chiXK D).ker

/-- **`Aut_csp(D^⊚±)`**: the automorphisms fixing the cusps of `X̲_K`. -/
def AutCsp : Subgroup (AutXK D) := (psiXK D).ker

/-- The translations `z ↦ z + b`. -/
def transSub : Subgroup (Equiv.Perm (ZMod D.ℓ)) where
  carrier := {f | ∃ b, f = affPerm D.ℓ 1 b}
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨_, by rw [affPerm_mul, one_mul]⟩
  one_mem' := ⟨0, affPerm_one.symm⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨_, affPerm_inv 1 b⟩

/-- **`Aut_+(D^⊚±)`**: the automorphisms acting on the cusps by translations. -/
def AutPlus : Subgroup (AutXK D) := (transSub D).comap (psiXK D)

lemma psiXK_mk (γ : normXK D) : psiXK D (QuotientGroup.mk γ) = psiN D γ := rfl

lemma psiN_eq (γ : normXK D) :
    psiN D γ = affU D.ℓ (linN D γ) (affOf (isDihedralFull_rhoCK D) (normToStabXK D γ)).2 := rfl

theorem autCsp_le_autPlus : AutCsp D ≤ AutPlus D := fun a ha => by
  change psiXK D a ∈ transSub D
  rw [MonoidHom.mem_ker.1 ha]
  exact one_mem _

theorem autPlus_le_autPm : AutPlus D ≤ AutPm D := by
  intro a ha
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, hb⟩ : psiN D γ ∈ transSub D := ha
  rw [psiN_eq] at hb
  have h1 := congrArg (· 1) hb
  have h0 := congrArg (· 0) hb
  simp only [affU_apply, affPerm_apply, sgn_one, mul_one, mul_zero, zero_add] at h1 h0
  have hl : linN D γ = 1 := Units.ext (by rw [Units.val_one]; linear_combination h1 - h0)
  change (linN D γ : FlStar D.ℓ) = 1
  rw [hl]
  rfl

/-- **`ψ(Aut_±) = F_ℓ ⋊ {±1}`**, i.e. `Aut_±(D^⊚±)/Aut_csp(D^⊚±) ≅ F_ℓ^{⋊±}` (IUT I,
Definition 6.1 (v)); already the `K`-linear automorphisms (`π₁(C_K)`) give all of
`F_ℓ ⋊ {±1}`. -/
theorem psiXK_map_autPm : (AutPm D).map (psiXK D) = FlSemi D.ℓ := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
    have ha' : (linN D γ : FlStar D.ℓ) = 1 := ha
    rw [QuotientGroup.eq_one_iff] at ha'
    rw [psiXK_mk, psiN_eq]
    rcases ha' with h | h
    · exact ⟨1, (affOf (isDihedralFull_rhoCK D) (normToStabXK D γ)).2, by
        rw [h, affPerm_eq_affU, map_one]⟩
    · exact ⟨-1, (affOf (isDihedralFull_rhoCK D) (normToStabXK D γ)).2, by
        rw [h, affPerm_eq_affU]; congr 1; ext; simp⟩
  · intro f hf
    -- every element of `F_ℓ ⋊ {±1}` is `ρ(g)` for some `g ∈ π₁(C_K)`
    obtain ⟨n, m, -, hg⟩ : ∃ n m : ℕ, m < 2 ∧ f = rhoCK D
        ((isDihedralFull_rhoCK D).2.1.choose ^ n * (isDihedralFull_rhoCK D).2.2.choose ^ m) := by
      obtain ⟨ε, c, rfl⟩ := hf
      refine ⟨c.val, ?_⟩
      have h1 := (isDihedralFull_rhoCK D).2.1.choose_spec
      have h0 := (isDihedralFull_rhoCK D).2.2.choose_spec
      rcases Int.units_eq_one_or ε with rfl | rfl
      · refine ⟨0, by norm_num, ?_⟩
        rw [pow_zero, mul_one, map_pow, h1, affPerm_one_pow, ZMod.natCast_zmod_val]
      · refine ⟨1, by norm_num, ?_⟩
        rw [pow_one, map_mul, map_pow, h1, h0, affPerm_one_pow, ZMod.natCast_zmod_val,
          affPerm_mul, sgn_one, one_mul, mul_zero, zero_add]
    obtain ⟨g, hg⟩ : ∃ g : piCK D, f = rhoCK D g := ⟨_, hg⟩
    -- `g ∈ π₁(C_K)` normalises `π₁(X̲_K) = ker ρ`
    have hN : piCKToCmod D g ∈ normXK D := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨u, rfl⟩
        have hk : g * piXKToCKdown D u * g⁻¹ ∈ (rhoCK D).ker :=
          (rhoCK D).normal_ker.conj_mem _ (by rw [← range_XK_eq_ker]; exact ⟨u, rfl⟩) g
        rw [← range_XK_eq_ker] at hk
        obtain ⟨u', hu'⟩ := hk
        refine ⟨u', ?_⟩
        change piCKToCmod D (piXKToCKdown D u') = _
        change piXKToCKdown D u' = _ at hu'
        rw [hu', map_mul, map_mul, map_inv]
        rfl
      · rintro ⟨u', hu'⟩
        change piCKToCmod D (piXKToCKdown D u') = _ at hu'
        have hk : g⁻¹ * piXKToCKdown D u' * g ∈ (rhoCK D).ker := by
          have := (rhoCK D).normal_ker.conj_mem _
            (by rw [← range_XK_eq_ker]; exact ⟨u', rfl⟩) g⁻¹
          simpa using this
        rw [← range_XK_eq_ker] at hk
        obtain ⟨u, hu⟩ := hk
        refine ⟨u, ?_⟩
        change piCKToCmod D (piXKToCKdown D u) = h
        change piXKToCKdown D u = _ at hu
        rw [hu, map_mul, map_mul, map_inv, hu']
        group
    let γ : normXK D := ⟨piCKToCmod D g, hN⟩
    have hst : normToStabXK D γ = ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩ := by
      refine Subtype.ext (MulEquiv.ext fun x => (isOpenEmbedding_piCKToCmod D).injective ?_)
      change piCKToCmod D (((piCmodToAut D (piCKToCmod D g) : contAut (piCK D)) :
        MulAut (piCK D)) x) = piCKToCmod D (g * x * g⁻¹)
      rw [piCKToCmod_piCmodToAut, map_mul, map_mul, map_inv]
    obtain ⟨ε, hε, hψ⟩ := affOf_conj (isDihedralFull_rhoCK D) g
    refine ⟨QuotientGroup.mk γ, ?_, ?_⟩
    · change (linN D γ : FlStar D.ℓ) = 1
      rw [QuotientGroup.eq_one_iff]
      change linHom (isDihedralFull_rhoCK D) (normToStabXK D γ) ∈ pmSub D.ℓ
      rw [hst]
      change (affOf (isDihedralFull_rhoCK D) ⟨MulAut.conj g, conj_mem_stabAut_ker g⟩).1 ∈ pmSub D.ℓ
      rw [hε]
      rcases Int.units_eq_one_or ε with rfl | rfl
      · left; simp
      · right; ext; simp
    · change psiHom (isDihedralFull_rhoCK D) (normToStabXK D γ) = f
      rw [hst, hψ, hg]

/-- **`Aut_csp(D^⊚±)`** as a poly-automorphism of `D^⊚± = B(X̲_K)⁰`. -/
def autCspPoly : PolyMor (dCircPmModel D) (dCircPmModel D) (PiXK D) (PiXK D) :=
  autPolyN (isOpenEmbedding_iotaXK D).injective (isOpenEmbedding_iotaXK D).isEmbedding (AutCsp D)

theorem autCspPoly_comp_subset : (autCspPoly D).comp (autCspPoly D) ⊆ autCspPoly D :=
  autPolyN_comp_subset _ _ (hasONSBasis_profinite D.orb.XKu.genuinePi1)
    (isONSComplete_profinite D.orb.XKu.genuinePi1) (AutCsp D)

/-- **`φ^Θell_v` for `A = Aut_csp(D^⊚±)`** (IUT I, Example 6.3 (i)). -/
def phiEllCsp (v : NumberField.FinitePlace ↥(fieldOfModuli D.F D.E)) :
    PolyMor (Dv D v) (dCircPmModel D) (Piv D v).carrier (PiXK D) :=
  phiEll D (autCspPoly D) v

/-- `φ^Θell_v` is stabilised by `Aut_csp(D^⊚±)`. -/
theorem phiEllCsp_comp_subset (v : NumberField.FinitePlace ↥(fieldOfModuli D.F D.E)) :
    (phiEllCsp D v).comp (autCspPoly D) ⊆ phiEllCsp D v :=
  phiEll_comp_subset D (autCspPoly_comp_subset D) v

end Iut.Multiradial.Theater
