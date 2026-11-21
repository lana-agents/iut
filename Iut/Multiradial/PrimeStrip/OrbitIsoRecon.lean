/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Cor53
import Iut.Multiradial.PrimeStrip.MonoAn

/-!
# Self-equivalences of `B(Π_v)⁰` are induced by automorphisms of `Π_v` (MR21 R4a)

[Mzk2], Proposition 3.2 (profinite) and [SemiAnbd], Proposition 3.2 (tempered), as formalised in
`Iut.Frobenioid.OrbitObj.exists_continuousMulEquiv` and `exists_continuousMulEquiv_temp`, give,
for an equivalence `F : B(G₁)⁰ ⥤ B(G₂)⁰`, an isomorphism of topological groups `σ : G₁ ≅ G₂`
and base points `x_N ∈ F(G₁/N)` (`N` open normal) compatible with the projections and with
`F(rmul g)(x_N) = σ(g)·x_N`. This file turns these data into a **natural isomorphism
`F ≅ (G₁/H ↦ G₂/σ(H))`** (`OrbitObj.natIsoOfBasePoints`): the component at `G₁/H` is
`G₂/σ(H) ≅ F(G₁/H)`, `y σ(H) ↦ y · y_H`, where `y_H = F(G₁/N → G₁/H)(x_N)` for any open normal
`N ⊆ H`; its stabilizer is `σ(H)`, by the faithfulness of `F`.

Consequences:

* `orbitIsoRecon_of_profinite`, `orbitIsoRecon_of_temp`: the functorial reconstruction
  `OrbitIsoRecon` (`Cor53.lean`) for profinite groups and for tempered groups (Hausdorff, with a
  basis of open normal subgroups, complete for them, with a countable cofinal chain);
* `orbitIsoRecon_piv`: `OrbitIsoRecon Π_v` at `v ∉ V^bad` unconditionally, at `v ∈ V^bad` from
  MR18's countability debt `PivCountable D v` (`PivTemp.lean`);
* **`FStripNon.isoClassToD_surjective_of_kummerLift`: IUT I, Corollary 5.3 (ii), surjectivity at
  `V^non`**, from `KummerLift` ([AbsTopIII], Proposition 3.2 (iv), debt R4b) and `PivCountable` at
  `V^bad` only (debt R4a discharged).
-/

noncomputable section

namespace Iut

namespace Frobenioid

namespace OrbitObj

open CategoryTheory

universe u u'

section BasePoints

variable {G₁ : Type u} [Group G₁] [TopologicalSpace G₁]
  {G₂ : Type u'} [Group G₂] [TopologicalSpace G₂]
  (F : OrbitObj G₁ ⥤ OrbitObj G₂) (hb : HasONSBasis G₁) (σ : G₁ ≃ₜ* G₂)
  (x : ∀ N : OpenNormalSubgroup G₁, G₂ ⧸ (F.obj (ofONS N)).H)
  (hpt : ∀ {N M : OpenNormalSubgroup G₁} (h : N ≤ M),
    (F.map (proj (ofONS M) (fun _ hx => h hx))).toFun (x N) = x M)
  (hrmul : ∀ N g, (F.map (rmul N g)).toFun (x N) = σ g • x N)

/-- Equivariant maps out of a transitive set agreeing at one point are equal. -/
lemma OrbitHom.ext_of_apply_eq {G : Type*} [Group G] [TopologicalSpace G] {A B : OrbitObj G}
    {f g : A ⟶ B} {z : G ⧸ A.H} (h : f.toFun z = g.toFun z) : f = g := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  refine OrbitHom.ext_of_mk_one ?_
  have e : (QuotientGroup.mk 1 : G ⧸ A.H) = c⁻¹ • (QuotientGroup.mk c : G ⧸ A.H) := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  rw [e, f.map_smul, g.map_smul, h]

lemma toFun_map_comp {A B C : OrbitObj G₁} (a : A ⟶ B) (b : B ⟶ C) (z : G₂ ⧸ (F.obj A).H) :
    (F.map (a ≫ b)).toFun z = (F.map b).toFun ((F.map a).toFun z) := by
  rw [F.map_comp]; rfl

/-- An open normal subgroup inside the open subgroup `H` (chosen). -/
def onsLe (A : OrbitObj G₁) : OpenNormalSubgroup G₁ :=
  (hb A.isOpen A.H.one_mem).choose

lemma onsLe_le (A : OrbitObj G₁) : ((onsLe hb A).toSubgroup : Subgroup G₁) ≤ A.H :=
  fun _ hx => (hb A.isOpen A.H.one_mem).choose_spec hx

/-- The base point `y_A = F(G₁/N → A)(x_N)` of `F(A)`. -/
def basePt (A : OrbitObj G₁) : G₂ ⧸ (F.obj A).H :=
  (F.map (proj A (onsLe_le hb A))).toFun (x (onsLe hb A))

include hpt in
/-- `y_A` does not depend on the open normal subgroup `N ⊆ H`. -/
lemma basePt_eq (A : OrbitObj G₁) {N : OpenNormalSubgroup G₁}
    (hN : (N.toSubgroup : Subgroup G₁) ≤ A.H) :
    basePt F hb x A = (F.map (proj A hN)).toFun (x N) := by
  let L : OpenNormalSubgroup G₁ := N ⊓ onsLe hb A
  have h1 : L ≤ N := inf_le_left
  have h2 : L ≤ onsLe hb A := inf_le_right
  have e1 : proj (ofONS N) (fun _ hx => h1 hx) ≫ proj A hN =
      proj A (fun _ hx => hN (h1 hx)) := OrbitHom.ext_of_mk_one (by
    rw [OrbitHom.comp_toFun, Function.comp_apply, proj_mk, proj_mk, proj_mk])
  have e2 : proj (ofONS (onsLe hb A)) (fun _ hx => h2 hx) ≫ proj A (onsLe_le hb A) =
      proj A (fun _ hx => hN (h1 hx)) := OrbitHom.ext_of_mk_one (by
    rw [OrbitHom.comp_toFun, Function.comp_apply, proj_mk, proj_mk, proj_mk])
  rw [basePt, ← hpt h2, ← toFun_map_comp, e2, ← e1, toFun_map_comp, hpt h1]

include hrmul in
/-- `σ(g)·y_A = F(rmul g ≫ (G₁/N → A))(x_N)`. -/
lemma smul_basePt (A : OrbitObj G₁) (g : G₁) :
    σ g • basePt F hb x A =
      (F.map (rmul (onsLe hb A) g ≫ proj A (onsLe_le hb A))).toFun (x (onsLe hb A)) := by
  rw [basePt, ← (F.map _).map_smul, ← hrmul, toFun_map_comp]

variable [F.Faithful]

include hrmul in
/-- **The stabilizer of `y_A` is `σ(H)`.** -/
lemma smul_basePt_eq_iff (A : OrbitObj G₁) (g : G₁) :
    σ g • basePt F hb x A = basePt F hb x A ↔ g ∈ A.H := by
  rw [smul_basePt F hb σ x hrmul]
  constructor
  · intro h
    have e := F.map_injective (OrbitHom.ext_of_apply_eq h)
    have := congrFun (congrArg OrbitHom.toFun e) (QuotientGroup.mk 1)
    rw [OrbitHom.comp_toFun, Function.comp_apply, rmul_mk, proj_mk, proj_mk, one_mul] at this
    exact mk_eq_one_iff.mp this
  · intro hg
    congr 2
    refine OrbitHom.ext_of_mk_one ?_
    rw [OrbitHom.comp_toFun, Function.comp_apply, rmul_mk, proj_mk, proj_mk, one_mul]
    exact mk_eq_one_iff.mpr hg

/-- A representative of `y_A`. -/
def baseRep (A : OrbitObj G₁) : G₂ := (basePt F hb x A).out

omit [F.Faithful] in
lemma mk_baseRep (A : OrbitObj G₁) :
    (QuotientGroup.mk (baseRep F hb x A) : G₂ ⧸ (F.obj A).H) = basePt F hb x A :=
  QuotientGroup.out_eq' _

include hrmul in
lemma mem_iff_conj (A : OrbitObj G₁) (k : G₂) :
    k ∈ A.H.map (σ : G₁ →* G₂) ↔ (baseRep F hb x A)⁻¹ * k * baseRep F hb x A ∈ (F.obj A).H := by
  obtain ⟨g, rfl⟩ := σ.surjective k
  have e : (σ g • basePt F hb x A = basePt F hb x A) ↔
      (baseRep F hb x A)⁻¹ * σ g * baseRep F hb x A ∈ (F.obj A).H := by
    rw [← mk_baseRep F hb x A, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
      ← Subgroup.inv_mem_iff]
    rw [show ((σ g * baseRep F hb x A)⁻¹ * baseRep F hb x A)⁻¹ =
      (baseRep F hb x A)⁻¹ * σ g * baseRep F hb x A by group]
  rw [← e, smul_basePt_eq_iff F hb σ x hrmul]
  constructor
  · rintro ⟨g', hg', he⟩
    rw [show g = g' from σ.injective he.symm]
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- The component `G₂/σ(H) ≅ F(G₁/H)`, `y σ(H) ↦ y · y_H`. -/
def baseIsoApp (A : OrbitObj G₁) : (OrbitObj.isoFunctor σ).obj A ≅ F.obj A :=
  OrbitObj.isoOfConj _ _ (baseRep F hb x A)
    (fun a ha => (mem_iff_conj F hb σ x hrmul A a).1 ha)
    (fun b hb' => (mem_iff_conj F hb σ x hrmul A _).2 (by
      simpa [mul_assoc] using hb'))

lemma baseIsoApp_mk (A : OrbitObj G₁) (y : G₂) :
    (baseIsoApp F hb σ x hrmul A).hom.toFun (QuotientGroup.mk y) =
      QuotientGroup.mk (y * baseRep F hb x A) := rfl

lemma isoFunctor_map_mk {A B : OrbitObj G₁} (f : A ⟶ B) (y : G₂) :
    ((OrbitObj.isoFunctor σ).map f).toFun (QuotientGroup.mk y) =
      QuotientGroup.mk (y * σ (OrbitHom.rep f)) := rfl

lemma baseIsoApp_mk_one (A : OrbitObj G₁) :
    (baseIsoApp F hb σ x hrmul A).hom.toFun (QuotientGroup.mk 1) = basePt F hb x A := by
  change (QuotientGroup.mk (1 * baseRep F hb x A) : G₂ ⧸ (F.obj A).H) = _
  rw [one_mul, mk_baseRep]

include hpt in
/-- **The natural isomorphism `(G₁/H ↦ G₂/σ(H)) ≅ F`** from base points. -/
def natIsoOfBasePoints : OrbitObj.isoFunctor σ ≅ F :=
  NatIso.ofComponents (baseIsoApp F hb σ x hrmul) fun {A B} f => by
    refine OrbitHom.ext_of_mk_one ?_
    let N : OpenNormalSubgroup G₁ := onsLe hb A ⊓ onsLe hb B
    have hNA : (N.toSubgroup : Subgroup G₁) ≤ A.H := fun _ hx => onsLe_le hb A hx.1
    have hNB : (N.toSubgroup : Subgroup G₁) ≤ B.H := fun _ hx => onsLe_le hb B hx.2
    have key : proj A hNA ≫ f = rmul N (OrbitHom.rep f) ≫ proj B hNB :=
      OrbitHom.ext_of_mk_one (by
        rw [OrbitHom.comp_toFun, OrbitHom.comp_toFun, Function.comp_apply, Function.comp_apply,
          proj_mk, rmul_mk, proj_mk, one_mul, ← OrbitHom.mk_rep f])
    have hL : ((OrbitObj.isoFunctor σ).map f ≫ (baseIsoApp F hb σ x hrmul B).hom).toFun
        (QuotientGroup.mk 1) = σ (OrbitHom.rep f) • basePt F hb x B := by
      rw [OrbitHom.comp_toFun, Function.comp_apply, isoFunctor_map_mk, baseIsoApp_mk, one_mul,
        ← mk_baseRep F hb x B, MulAction.Quotient.smul_mk, smul_eq_mul]
    have hR : ((baseIsoApp F hb σ x hrmul A).hom ≫ F.map f).toFun (QuotientGroup.mk 1) =
        σ (OrbitHom.rep f) • basePt F hb x B := by
      rw [OrbitHom.comp_toFun, Function.comp_apply, baseIsoApp_mk_one,
        basePt_eq F hb x hpt A hNA, ← toFun_map_comp, key, toFun_map_comp, hrmul,
        (F.map _).map_smul, ← basePt_eq F hb x hpt B hNB]
    exact hL.trans hR.symm

end BasePoints

end OrbitObj

end Frobenioid

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-- **[Mzk2], Proposition 3.2 in functorial form** (profinite groups). -/
theorem orbitIsoRecon_of_profinite {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ] :
    OrbitIsoRecon Γ := fun e => by
  have hb : HasONSBasis Γ := fun _ hU h1 =>
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  obtain ⟨σ, x, -, hpt, hrmul⟩ := OrbitObj.exists_continuousMulEquiv e.functor
  exact ⟨σ, ⟨(OrbitObj.natIsoOfBasePoints e.functor hb σ x hpt hrmul).symm⟩⟩

/-- **[SemiAnbd], Proposition 3.2 in functorial form** (tempered groups). -/
theorem orbitIsoRecon_of_temp {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [T2Space Γ] (hb : HasONSBasis Γ) (hs : HasONSChain Γ) (hc : IsONSComplete Γ) :
    OrbitIsoRecon Γ := fun e => by
  obtain ⟨σ, x, -, hpt, hrmul⟩ :=
    OrbitObj.exists_continuousMulEquiv_temp hb hs hc hb hc e.functor
  exact ⟨σ, ⟨(OrbitObj.natIsoOfBasePoints e.functor hb σ x hpt hrmul).symm⟩⟩

/-- **`OrbitIsoRecon Π_v`**: unconditional at `v ∉ V^bad` (`Π_v` profinite), from the
countability debt `PivCountable` (MR18's `hctbl`) at `v ∈ V^bad`. -/
theorem orbitIsoRecon_piv (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))
    (hc : v ∈ D.VBad → PivCountable D v) : OrbitIsoRecon (Piv D v).carrier := by
  by_cases hv : v ∈ D.VBad
  · obtain ⟨h1, hb, hs, hcc⟩ := tempRecon_of_countable D v hv (hc hv)
    haveI := h1
    exact orbitIsoRecon_of_temp hb hs hcc
  · obtain ⟨h1, h2, h3⟩ := piv_profinite D v hv
    haveI := h1
    haveI := h2
    haveI := h3
    exact orbitIsoRecon_of_profinite

/-- **IUT I, Corollary 5.3 (ii), surjectivity at `V^non`**: `Isom(¹F, ²F) → Isom(¹D, ²D)` is
surjective, from the named input `KummerLift` ([AbsTopIII], Proposition 3.2 (iv), debt R4b) at
every `v ∈ V^non` and MR18's countability debt `PivCountable` at `v ∈ V^bad`. -/
theorem FStripNon.isoClassToD_surjective_of_kummerLift {D : InitialThetaData.{0}}
    (hc : ∀ v : Vnon D, v ∈ D.VBad → PivCountable D v) (hk : ∀ v : Vnon D, KummerLift D v)
    (P Q : FStripNon D) :
    Function.Surjective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) :=
  FStripNon.isoClassToD_surjective_of (fun v => orbitIsoRecon_piv D v (hc v)) hk P Q

end PrimeStrip

end Multiradial

end Iut
