/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.HodgeTheater.FRlfMod
import Iut.Frobenioid.GlobalUnique

/-!
# Isomorphisms of the global data of `F^⊩`-prime-strips (IUT I, Definition 5.2(iv))

IUT I, Definition 5.2(iv) (l.9197–9227): an `F^⊩`-prime-strip is a collection
`(C^⊩, Prime(C^⊩) ≅ V, F^⊢, {ρ_v})` isomorphic to `F^⊩_mod`, and "a morphism of
`F^⊩`-prime-strips is defined to be an isomorphism between collections of data". The global
data are encoded by `FRlfGlobal D` (`C^⊩` with `equiv : C^⊩ ≌ C^⊩_mod`); `Prime(C^⊩) ≅ V` and
the `ρ_v` are those of `F^⊩_mod` transported along `equiv` (`FRlfGlobal.prime`,
`FRlfGlobal.rho`), not inputs. An equivalence `e : C^⊩₁ ≌ C^⊩₂` acts on them through the
conjugated autoequivalence `σ_e = equiv₁⁻¹ ⋙ e ⋙ equiv₂` of `C^⊩_mod` (`FRlfGlobal.conj`), by
its `Ψ_Prime` (`GlobalRealified.placeEquiv`) and its `Ψ_Φ` (`GlobalRealified.psiPhi`).

Results:

* **`FRlfGlobal.Iso.placeEquiv_conj`**, **`FRlfGlobal.Iso.prime_primeMap`**: an isomorphism
  `FRlfGlobal.Iso` is compatible with `Prime(−) ≅ V`;
* **`FRlfGlobal.Iso.psiPhi_conj`**, **`FRlfGlobal.Iso.rho_psiPhi_conj`**: it is compatible with the
  `ρ_v` (and `Ψ_Φ(σ_e) = id`);
* **`FRlfGlobal.Iso.ofCompat`**: conversely, every equivalence `e` whose `σ_e` is compatible with
  `Prime(−) ≅ V` and with the `ρ_v` underlies an `FRlfGlobal.Iso` (so `FRlfGlobal.Iso` is exactly
  the notion of Definition 5.2(iv), global part), and the compatibility datum is unique
  (`FRlfGlobal.Iso.subsingleton_comm`).

General facts about `Ψ_Φ` used here: `psiPhi_eq_of_iso` (`Ψ_Φ(G) = id` for `G ≅ 𝟭`),
`placeEquiv_eq_of_psiPhi` and `inducesIdRatFun_of_psiPhi`.
-/

namespace Iut

namespace Frobenioid

namespace GlobalRealified

open CategoryTheory

universe u

variable {K : Type u} [Field K] [NumberField K]
variable (G : GlobalRealified K ⥤ GlobalRealified K) [G.IsEquivalence]

/-- **`Ψ_Φ(G) = id` for `G ≅ 𝟭`.** -/
theorem psiPhi_eq_of_iso (η : G ≅ 𝟭 (GlobalRealified K)) (z : ArithDiv K) (hz : z ∈ effCone K) :
    psiPhi G z hz = z := by
  let φ := step (objOfDeg (K := K) 0) z hz
  have h1 := div_map G φ
  have hn : G.map φ ≫ η.hom.app _ = η.hom.app _ ≫ φ := η.hom.naturality φ
  have h2 : (G.map φ ≫ η.hom.app _).div = (η.hom.app _ ≫ φ).div := by rw [hn]
  rw [div_comp_iso, div_iso_comp] at h2
  rw [h2] at h1
  exact h1.symm

/-- `Ψ_Prime(G) = id` if `Ψ_Φ(G) = id`. -/
theorem placeEquiv_eq_of_psiPhi (h : ∀ z (hz : z ∈ effCone K), psiPhi G z hz = z) (p : Place K) :
    placeEquiv G p = p := by
  have := supp_psiPhi G (single_mem (p := p) zero_le_one)
  rw [h, supp_single one_ne_zero, Set.image_singleton] at this
  exact (Set.singleton_eq_singleton_iff.mp this).symm

/-- `G` induces the identity on `ℝ·Φ^birat` if `Ψ_Φ(G) = id`. -/
theorem inducesIdRatFun_of_psiPhi (h : ∀ z (hz : z ∈ effCone K), psiPhi G z hz = z) :
    InducesIdRatFun G := by
  intro X Y φ ψ hd
  have r1 := rel_eq φ
  have r2 := rel_eq ψ
  have r1' := rel_eq (G.map φ)
  have r2' := rel_eq (G.map ψ)
  rw [deg_map G φ, div_map G φ, h] at r1'
  rw [deg_map G ψ, div_map G ψ, h] at r2'
  rw [hd] at r1 r1'
  have e1 : ((G.map φ).u : ArithDiv K) = (ψ.deg : ℕ) • (G.obj X).α + φ.div - (G.obj Y).α := by
    rw [r1']; abel
  have e2 : ((G.map ψ).u : ArithDiv K) = (ψ.deg : ℕ) • (G.obj X).α + ψ.div - (G.obj Y).α := by
    rw [r2']; abel
  have e3 : (φ.u : ArithDiv K) = (ψ.deg : ℕ) • X.α + φ.div - Y.α := by rw [r1]; abel
  have e4 : (ψ.u : ArithDiv K) = (ψ.deg : ℕ) • X.α + ψ.div - Y.α := by rw [r2]; abel
  rw [e1, e2, e3, e4]
  abel

/-- **`Ψ_Φ(G) = id` from `Ψ_Prime(G) = id` and `Ψ_Φ(G) = id` on each `Φ_v`.** -/
theorem psiPhi_eq_of_phiAt (hP : ∀ p, placeEquiv G p = p)
    (hv : ∀ v z (hz : z ∈ phiAt v), psiPhi G z hz.1 = z) (z : ArithDiv K) (hz : z ∈ effCone K) :
    psiPhi G z hz = z := by
  refine eq_iff_coord.mpr fun q => ?_
  have hq : 0 ≤ coord z q := mem_effCone_iff_coord.mp hz q
  set a := single q (coord z q)
  have ha : a ∈ phiAt q := single_mem_phiAt q hq
  have hr : z - a ∈ effCone K := by
    refine mem_effCone_iff_coord.mpr fun p => ?_
    rw [coord_sub, coord_single]
    split_ifs with hp
    · subst hp; simp
    · simpa using mem_effCone_iff_coord.mp hz p
  have hrq : q ∉ supp (z - a) := by
    simp [supp, a, coord_sub, coord_single]
  have hsum := psiPhi_add G ha.1 hr
  simp only [add_sub_cancel] at hsum
  rw [hsum, coord_add, hv q a ha]
  have : q ∉ supp (psiPhi G (z - a) hr) := by
    rw [supp_psiPhi]
    rintro ⟨p, hp, hpq⟩
    rw [hP] at hpq
    exact hrq (hpq ▸ hp)
  rw [coord_eq_zero_of_not_mem this, add_zero, coord_single, if_pos rfl]

end GlobalRealified

end Frobenioid

namespace HodgeTheater

open CategoryTheory NumberField Frobenioid Frobenioid.GlobalRealified

universe u

variable {D : InitialThetaData.{u}}

namespace FRlfMod

/-- `ρ_v` is injective on `Φ_v`. -/
theorem rhoMod_injOn (v : Vp D) {z z' : ArithDiv ↥(fieldOfModuli D.F D.E)} (hz : z ∈ phiAt v)
    (hz' : z' ∈ phiAt v) (h : rhoMod D v z = rhoMod D v z') : z = z' := by
  rcases v with v | v
  · have := (rhoEquivFin (D.V.sectFin_liesOver v)).injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨z', hz'⟩)
      (NNReal.eq (by rw [coe_rhoEquivFin, coe_rhoEquivFin]; exact h))
    exact congrArg Subtype.val this
  · have := (rhoEquivInf (D.V.sectInf v) v).injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨z', hz'⟩)
      (NNReal.eq (by rw [coe_rhoEquivInf, coe_rhoEquivInf]; exact h))
    exact congrArg Subtype.val this

end FRlfMod

namespace FRlfGlobal

/-- **The conjugated autoequivalence `σ_e = equiv₁⁻¹ ⋙ e ⋙ equiv₂` of `C^⊩_mod`.** -/
noncomputable def conj {A B : FRlfGlobal D} (e : A.C ≌ B.C) :
    GlobalRealified ↥(fieldOfModuli D.F D.E) ⥤ GlobalRealified ↥(fieldOfModuli D.F D.E) :=
  A.equiv.inverse ⋙ e.functor ⋙ B.equiv.functor

instance {A B : FRlfGlobal D} (e : A.C ≌ B.C) : (conj e).IsEquivalence := by
  unfold conj; infer_instance

/-- **The bijection `Prime(C^⊩₁) ≅ Prime(C^⊩₂)` induced by `e`** (`Ψ_Prime(σ_e)`). -/
noncomputable def primeMap {A B : FRlfGlobal D} (e : A.C ≌ B.C) :
    GlobalRealified.Prime ↥(fieldOfModuli D.F D.E) ≃
      GlobalRealified.Prime ↥(fieldOfModuli D.F D.E) :=
  primeEquiv.trans ((placeEquiv (conj e)).trans primeEquiv.symm)

namespace Iso

variable {A B : FRlfGlobal D} (f : A.Iso B)

/-- `σ_e ≅ 𝟭` for an isomorphism. -/
noncomputable def conjIso : conj f.equiv ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft A.equiv.inverse f.comm ≪≫ A.equiv.counitIso

/-- **`Ψ_Φ(σ_e) = id`.** -/
theorem psiPhi_conj (z : ArithDiv ↥(fieldOfModuli D.F D.E)) (hz : z ∈ effCone _) :
    psiPhi (conj f.equiv) z hz = z :=
  psiPhi_eq_of_iso _ f.conjIso z hz

/-- **Compatibility with `Prime(−) ≅ V`**: `Ψ_Prime(σ_e) = id`. -/
theorem placeEquiv_conj (p : Vp D) : placeEquiv (conj f.equiv) p = p :=
  placeEquiv_eq_of_psiPhi _ (psiPhi_conj f) p

/-- **Compatibility with `Prime(−) ≅ V`**: `prime₂ ∘ Ψ_Prime(e) = prime₁`. -/
theorem prime_primeMap (p : GlobalRealified.Prime ↥(fieldOfModuli D.F D.E)) :
    B.prime (primeMap f.equiv p) = A.prime p := by
  simp [prime, primeMap, placeEquiv_conj f]

/-- **Compatibility with the `ρ_v`**: `ρ_{2,v} ∘ Ψ_Φ(σ_e) = ρ_{1,v}`. -/
theorem rho_psiPhi_conj (v : Vp D) (z : ArithDiv ↥(fieldOfModuli D.F D.E)) (hz : z ∈ effCone _) :
    B.rho v (psiPhi (conj f.equiv) z hz) = A.rho v z := by
  rw [psiPhi_conj f]; rfl

/-- **Converse**: an equivalence `e : C^⊩₁ ≌ C^⊩₂` compatible with `Prime(−) ≅ V` and with the `ρ_v`
(IUT I, Definition 5.2(iv)) underlies an isomorphism of the global data. -/
noncomputable def ofCompat (e : A.C ≌ B.C)
    (hP : ∀ p, B.prime (primeMap e p) = A.prime p)
    (hρ : ∀ v z (hz : z ∈ phiAt v), B.rho v (psiPhi (conj e) z hz.1) = A.rho v z) :
    A.Iso B where
  equiv := e
  comm := by
    have hP' : ∀ p, placeEquiv (conj e) p = p := fun p => by
      have := hP (primeEquiv.symm p)
      simpa [prime, primeMap] using this
    have hv : ∀ v z (hz : z ∈ phiAt v), psiPhi (conj e) z hz.1 = z := by
      intro v z hz
      have hm : psiPhi (conj e) z hz.1 ∈ phiAt v := by
        refine ⟨psiPhi_mem _ z hz.1, ?_⟩
        rw [supp_psiPhi]
        rintro _ ⟨p, hp, rfl⟩
        rw [hP']
        exact hz.2 hp
      exact FRlfMod.rhoMod_injOn v hm hz (hρ v z hz)
    let η : conj e ≅ 𝟭 _ := isoId (conj e)
      (inducesIdRatFun_of_psiPhi _ (psiPhi_eq_of_phiAt _ hP' hv))
    exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight A.equiv.unitIso _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft A.equiv.functor η ≪≫
      Functor.rightUnitor _

/-- **The compatibility datum is unique.** -/
theorem subsingleton_comm (e : A.C ≌ B.C) :
    Subsingleton (e.functor ⋙ B.equiv.functor ≅ A.equiv.functor) := by
  constructor
  intro a b
  ext X
  -- all isomorphisms in `C^⊩` are unique
  exact hom_eq_of_isIso _ _

end Iso

end FRlfGlobal

end HodgeTheater

end Iut
