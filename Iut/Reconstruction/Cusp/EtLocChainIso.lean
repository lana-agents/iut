/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import CurvesJacobian.Cusp.EtLocTerminal

/-!
# Uniqueness of the terminal `⋎`-chain in `Chain(Π)` ([AbsTopII] Cor. 3.3 (i)) (MR8)

[AbsTopII] Cor. 3.3 (i) (`Topics in Absolute Anabelian Geometry II.txt`, l.4440–4447)
characterises the chain `Π' ⇝ Π_C` "up to isomorphism in `Chain(Π')`" as the unique chain of
length `1` with type-chain `⋎` whose object of `ÉtLoc(Π')` is terminal. Isomorphisms in `Chain(Π)`
([AbsTopI] Def. 4.2 (iv), `Topics in Absolute Anabelian Geometry I.txt` l.3022–3035) are
collections of isomorphisms `Π_j ≅ Ψ_j` compatible with the rigidifying homomorphisms (belyi's
`PiChain.Iso`); curves-jacobian's `PiChain.nonempty_terminalIso_of_isTerminalEtLoc` only gives a
terminal isomorphism of the last groups (compatible with the maps to `G` up to conjugation).

Here we upgrade it: **`PiChain.nonempty_iso_of_isTerminalEtLoc`** — two length-one chains of type
`[⋎]` that are terminal in `ÉtLoc(Π)` are isomorphic in `Chain(Π)`. Proof: both last groups
receive `Π` by a compatible open injection (the composite `Π ≅ Π₀ ↪ Π₁`); the terminal
isomorphism `T : Π₁ ≅ Π'₁` carries one into the other up to an inner automorphism `c_γ` of `Π'₁`
(uniqueness half of terminality, applied to the trivial chain); then `c_γ⁻¹ ∘ T` is compatible with
the rigidifying homomorphisms.

Generic lemmas: `ChainObj.compat_trans`, `ChainObj.grpEquivOfEq`, `ChainObj.compat_grpEquivOfEq`.
-/

open Topology Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

namespace Iut.Reconstruction.EtLocChain

universe u

variable {E : CuspidalExt.{u}}

/-- `Compat` is transitive. -/
theorem compat_trans {A B C : ChainObj E} {φ : A.grp →ₜ* B.grp} {ψ : B.grp →ₜ* C.grp}
    (h₁ : ChainObj.Compat A B φ) (h₂ : ChainObj.Compat B C ψ) :
    ChainObj.Compat A C (ψ.comp φ) := by
  obtain ⟨H₁, hA, hB, e₁⟩ := h₁
  obtain ⟨H₂, hB', hC, e₂⟩ := h₂
  refine ⟨H₁ ⊓ H₂, fun x hx => hA (OpenSubgroup.mem_inf.1 hx).1,
    fun x hx => hC (OpenSubgroup.mem_inf.1 hx).2, fun h hh => ?_⟩
  have hh₁ := (OpenSubgroup.mem_inf.1 hh).1
  have hh₂ := (OpenSubgroup.mem_inf.1 hh).2
  change ψ (φ (A.rho ⟨h, hA hh₁⟩)) = C.rho ⟨h, hC hh₂⟩
  rw [e₁ h hh₁]
  exact e₂ h hh₂

/-- The identification of the groups of equal chain objects. -/
def grpEquivOfEq {A B : ChainObj E} (h : A = B) : A.grp ≃ₜ* B.grp :=
  h ▸ ContinuousMulEquiv.refl _

theorem compat_grpEquivOfEq {A B : ChainObj E} (h : A = B) :
    ChainObj.Compat A B (ContinuousMonoidHom.toContinuousMonoidHom (grpEquivOfEq h)) := by
  subst h
  exact ⟨A.dom, le_rfl, le_rfl, fun _ _ => rfl⟩

lemma len_eq_one_of_typeChain {c : PiChain E} (hq : c.typeChain = [OpKind.quot]) : c.len = 1 := by
  have h := congrArg List.length hq
  rwa [PiChain.typeChain, List.length_ofFn] at h

/-- For a chain of type `[⋎]`: the operation homomorphism `Π₀ ↪ Π₁` as a compatible open
injection from the base, `Π ≅ Π₀ ↪ Π₁ = Π_last`. -/
theorem exists_baseInj_of_typeChain {c : PiChain E} (hq : c.typeChain = [OpKind.quot]) :
    ∃ ψ : (ChainObj.base E).grp →ₜ* c.last.grp, Function.Injective ψ ∧ IsOpen (Set.range ψ) ∧
      ChainObj.Compat (ChainObj.base E) c.last ψ := by
  have hl := len_eq_one_of_typeChain hq
  let j₀ : Fin c.len := ⟨0, by omega⟩
  have hk : (c.op j₀).kind = OpKind.quot := by
    have h := congrArg (fun l => l[0]?) hq
    simp only [PiChain.typeChain, List.getElem?_ofFn] at h
    simpa [j₀, hl] using h
  have h0 : c.obj 0 = c.obj j₀.castSucc := congrArg c.obj (Fin.ext rfl)
  have h1 : c.obj j₀.succ = c.last := congrArg c.obj (Fin.ext (by simp [j₀, hl]))
  obtain ⟨φ, hinj, hopen, hc⟩ : ∃ φ : (c.obj j₀.castSucc).grp →ₜ* (c.obj j₀.succ).grp,
      Function.Injective φ ∧ IsOpen (Set.range φ) ∧ ChainObj.Compat _ _ φ := by
    revert hk
    cases c.op j₀ with
    | quot φ inj op compat => exact fun _ => ⟨φ, inj, op, compat⟩
    | cover => intro h; cases h
    | decusp => intro h; cases h
    | deorb => intro h; cases h
  let i₁ := OpenInjOver.ofCompat _ c.obj_zero.choose.symm.injective
    (by
      change IsOpen (Set.range c.obj_zero.choose.symm)
      rw [c.obj_zero.choose.symm.surjective.range_eq]
      exact isOpen_univ)
    (ChainObj.compat_symm₄ c.obj_zero.choose_spec)
  let i₂ := OpenInjOver.ofCompat _ (grpEquivOfEq h0).injective
    (by
      change IsOpen (Set.range (grpEquivOfEq h0))
      rw [(grpEquivOfEq h0).surjective.range_eq]
      exact isOpen_univ) (compat_grpEquivOfEq h0)
  let i₃ := OpenInjOver.ofCompat φ hinj hopen hc
  let i₄ := OpenInjOver.ofCompat _ (grpEquivOfEq h1).injective
    (by
      change IsOpen (Set.range (grpEquivOfEq h1))
      rw [(grpEquivOfEq h1).surjective.range_eq]
      exact isOpen_univ) (compat_grpEquivOfEq h1)
  let i := i₁.trans (i₂.trans (i₃.trans i₄))
  exact ⟨i.hom, i.inj, i.isOpen_range,
    compat_trans (ChainObj.compat_symm₄ c.obj_zero.choose_spec) (compat_trans
      (compat_grpEquivOfEq h0) (compat_trans hc (compat_grpEquivOfEq h1)))⟩

/-- A terminal isomorphism is an open injection over `G`. -/
def openInjOverOfTerminalIso {c c' : PiChain E} (T : c.TerminalIso c') :
    OpenInjOver c.last c'.last where
  hom := ContinuousMonoidHom.toContinuousMonoidHom T.iso
  inj := T.iso.injective
  isOpen_range := by
    change IsOpen (Set.range T.iso)
    rw [T.iso.surjective.range_eq]
    exact isOpen_univ
  g := T.over.choose
  toG_hom := T.over.choose_spec

/-- The conjugation `x ↦ γ⁻¹ x γ` after an isomorphism. -/
def conjEquiv {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] (T : P ≃ₜ* Q) (γ : Q) : P ≃ₜ* Q where
  toFun x := γ⁻¹ * T x * γ
  invFun y := T.symm (γ * y * γ⁻¹)
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_mul' x y := by simp only [map_mul]; group
  continuous_toFun := by
    have := T.continuous
    fun_prop
  continuous_invFun := by
    have := T.symm.continuous
    fun_prop

/-- **The last isomorphism.** For two chains of type `[⋎]` terminal in `ÉtLoc(Π)`, the last groups
are isomorphic compatibly with the rigidifying homomorphisms. -/
theorem exists_compat_last_iso {c₀ c₁ : PiChain E} (hq₀ : c₀.typeChain = [OpKind.quot])
    (hq₁ : c₁.typeChain = [OpKind.quot]) (h₀ : c₀.IsTerminalEtLoc) (h₁ : c₁.IsTerminalEtLoc) :
    ∃ θ : c₁.last.grp ≃ₜ* c₀.last.grp,
      ChainObj.Compat c₁.last c₀.last (ContinuousMonoidHom.toContinuousMonoidHom θ) := by
  obtain ⟨T⟩ := PiChain.nonempty_terminalIso_of_isTerminalEtLoc h₀ h₁
  obtain ⟨ψ₀, hi₀, ho₀, hc₀⟩ := exists_baseInj_of_typeChain hq₀
  obtain ⟨ψ₁, hi₁, ho₁, hc₁⟩ := exists_baseInj_of_typeChain hq₁
  let a := openInjOverOfTerminalIso T
  let j₀ : OpenInjOver (ChainObj.base E) c₀.last := OpenInjOver.ofCompat ψ₀ hi₀ ho₀ hc₀
  let j₁ : OpenInjOver (ChainObj.base E) c₀.last :=
    (OpenInjOver.ofCompat ψ₁ hi₁ ho₁ hc₁).trans a
  have htriv : (PiChain.trivial E).IsEtLoc := fun t ht => by
    simp [PiChain.typeChain, PiChain.trivial] at ht
  obtain ⟨γ, hγ⟩ := (h₀.2 (PiChain.trivial E) htriv).2 j₀ j₁
  refine ⟨conjEquiv T.iso γ, ?_⟩
  obtain ⟨H₀, hb₀, hl₀, e₀⟩ := hc₀
  obtain ⟨H₁, hb₁, hl₁, e₁⟩ := hc₁
  refine ⟨H₀ ⊓ H₁, fun x hx => hl₁ (OpenSubgroup.mem_inf.1 hx).2,
    fun x hx => hl₀ (OpenSubgroup.mem_inf.1 hx).1, fun h hh => ?_⟩
  have hh₀ := (OpenSubgroup.mem_inf.1 hh).1
  have hh₁ := (OpenSubgroup.mem_inf.1 hh).2
  let x : (ChainObj.base E).grp := (ChainObj.base E).rho ⟨h, hb₀ hh₀⟩
  have k₀ : ψ₀ x = c₀.last.rho ⟨h, hl₀ hh₀⟩ := e₀ h hh₀
  have k₁ : ψ₁ x = c₁.last.rho ⟨h, hl₁ hh₁⟩ := e₁ h hh₁
  have k := hγ x
  change T.iso (ψ₁ x) = γ * ψ₀ x * γ⁻¹ at k
  change γ⁻¹ * T.iso (c₁.last.rho ⟨h, hl₁ hh₁⟩) * γ = c₀.last.rho ⟨h, hl₀ hh₀⟩
  rw [← k₁, k, ← k₀]
  group

/-- **[AbsTopII] Cor. 3.3 (i), uniqueness in `Chain(Π)`**: two chains of length one and type `[⋎]`
that are terminal objects of `ÉtLoc(Π)` are isomorphic in `Chain(Π)` (belyi's `PiChain.Iso`:
isomorphisms of all objects compatible with the rigidifying homomorphisms). -/
theorem nonempty_iso_of_isTerminalEtLoc {c₀ c₁ : PiChain E}
    (hq₀ : c₀.typeChain = [OpKind.quot]) (hq₁ : c₁.typeChain = [OpKind.quot])
    (h₀ : c₀.IsTerminalEtLoc) (h₁ : c₁.IsTerminalEtLoc) : Nonempty (c₁.Iso c₀) := by
  obtain ⟨θ, hθ⟩ := exists_compat_last_iso hq₀ hq₁ h₀ h₁
  have hl₀ := len_eq_one_of_typeChain hq₀
  have hl₁ := len_eq_one_of_typeChain hq₁
  have hlen : c₁.len = c₀.len := hl₁.trans hl₀.symm
  let cst : Fin (c₁.len + 1) → Fin (c₀.len + 1) := Fin.cast (congrArg (· + 1) hlen)
  -- index `0`
  have e0₁ : ∀ j : Fin (c₁.len + 1), (j : ℕ) = 0 → c₁.obj j = c₁.obj 0 :=
    fun j hj => congrArg c₁.obj (Fin.ext hj)
  have e0₀ : ∀ j : Fin (c₁.len + 1), (j : ℕ) = 0 → c₀.obj 0 = c₀.obj (cst j) :=
    fun j hj => congrArg c₀.obj (Fin.ext (by simp [cst, hj]))
  -- index `1 = last`
  have e1₁ : ∀ j : Fin (c₁.len + 1), (j : ℕ) ≠ 0 → c₁.obj j = c₁.last :=
    fun j hj => congrArg c₁.obj (Fin.ext (by simp only [Fin.val_last]; omega))
  have e1₀ : ∀ j : Fin (c₁.len + 1), (j : ℕ) ≠ 0 → c₀.last = c₀.obj (cst j) :=
    fun j hj => congrArg c₀.obj (Fin.ext (by simp only [Fin.val_last, cst, Fin.val_cast]; omega))
  let z₁ := c₁.obj_zero.choose
  let z₀ := c₀.obj_zero.choose
  let iso : ∀ j : Fin (c₁.len + 1), (c₁.obj j).grp ≃ₜ* (c₀.obj (cst j)).grp := fun j =>
    if hj : (j : ℕ) = 0 then
      (grpEquivOfEq (e0₁ j hj)).trans (z₁.trans (z₀.symm.trans (grpEquivOfEq (e0₀ j hj))))
    else (grpEquivOfEq (e1₁ j hj)).trans (θ.trans (grpEquivOfEq (e1₀ j hj)))
  refine ⟨⟨hlen, hq₁.trans hq₀.symm, iso, fun j => ?_⟩⟩
  by_cases hj : (j : ℕ) = 0
  · have : iso j = (grpEquivOfEq (e0₁ j hj)).trans
        (z₁.trans (z₀.symm.trans (grpEquivOfEq (e0₀ j hj)))) := dif_pos hj
    rw [this]
    exact compat_trans (compat_grpEquivOfEq _) (compat_trans c₁.obj_zero.choose_spec
      (compat_trans (ChainObj.compat_symm₄ c₀.obj_zero.choose_spec) (compat_grpEquivOfEq _)))
  · have : iso j = (grpEquivOfEq (e1₁ j hj)).trans (θ.trans (grpEquivOfEq (e1₀ j hj))) :=
      dif_neg hj
    rw [this]
    exact compat_trans (compat_grpEquivOfEq _) (compat_trans hθ (compat_grpEquivOfEq _))

end Iut.Reconstruction.EtLocChain
