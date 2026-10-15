/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34
import Iut.Frobenioid.PAdic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Data.ZMod.Basic

/-!
# [FrdI], Proposition 1.14(iii) fails for Frobenioids whose units contain all roots of unity

[FrdI], Proposition 1.14 (p. 41) concerns a Frobenioid `C` of isotropic type over a base category
`D` of FSMFF-type. Assertion (iii) reads:

> Suppose that `φ` is irreducible. Then `φ` is a non-pre-step if and only if the following
> condition holds: there exists an `N ∈ ℕ_{≥1}` such that for every equality of composites in
> `C`, `αₙ ∘ … ∘ α₁ = ψ ∘ φ`, where `α₁, …, αₙ, ψ` are FSMI-morphisms, it holds that `n ≤ N`.

The proof of "irreducible pre-step ⇒ the condition fails" takes `ψ` to be a prime-Frobenius
morphism of large degree and uses that such morphisms are FSMI-morphisms. A morphism of Frobenius
type of degree `n` in a model Frobenioid is, however, *not* a monomorphism as soon as the group
`B(A)` of rational functions contains an element of order `n` (`Model.deg_eq_one_of_mono`). This
is the case for the Frobenioids of IUT (`B(A) ⊇ μ(K̄)`).

**Counterexample** (`not_prop114iii`). `D = Pt` (one object, one morphism; of FSM-type, hence of
FSMFF-type), `Φ = ℤ_{≥0}`, `B = ∏_{n} ℤ/n` (torsion of every order), `Div_B = 0`. The model
Frobenioid `CE` is a Frobenioid of isotropic type ([FrdI], Theorem 5.2(ii)). Its FSMI-morphisms are
exactly the steps with zero divisor `1`, so every composite of FSMI-morphisms equal to `ψ ∘ φ` for
the step `φ : (pt, 0) → (pt, 1)` and an FSMI-morphism `ψ` has length `2` (the zero divisors add up
to `2`). Hence `φ` satisfies the condition of (iii) with `N = 2`, although `φ` is an irreducible
pre-step.

The statement of [FrdI], Theorem 3.4(ii) is not affected for such Frobenioids: it is proved
for model Frobenioids with all torsion by a different route in `Iut/Frobenioid/Thm34.lean`
(pre-steps are exactly the FSM-morphisms, `Model.isPreStep_iff_isFSM`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe v u

section Chains

variable {C : Type u} [Category.{v} C]

/-- **FSMI-morphisms** ([FrdI] §0, p. 17): irreducible FSM-morphisms. -/
def IsFSMI {X Y : C} (φ : X ⟶ Y) : Prop := IsFSM φ ∧ IsIrreducible φ

/-- All arrows of a path of composable morphisms satisfy `S`. -/
def AllOf (S : MorClass C) {X : C} : ∀ {Y : C}, Quiver.Path X Y → Prop
  | _, .nil => True
  | _, .cons p f => AllOf S p ∧ S f

/-- **The condition of [FrdI], Proposition 1.14(iii)** on `φ : X → Y`: the lengths of the
factorizations of `ψ ∘ φ` (`ψ` an FSMI-morphism) into FSMI-morphisms are bounded. -/
def BoundedFSMIChains {X Y : C} (φ : X ⟶ Y) : Prop :=
  ∃ N : ℕ, ∀ ⦃Z : C⦄ (ψ : Y ⟶ Z) (p : Quiver.Path X Z), IsFSMI ψ →
    AllOf (fun _ _ f => IsFSMI f) p → composePath p = φ ≫ ψ → p.length ≤ N

/-- **Categories of FSMFF-type** ([FrdI] §0, p. 17): (a) every non-isomorphic FSM-morphism is a
composite of finitely many FSMI-morphisms; (b) for every object `A` the lengths of composable
chains of FSMI-morphisms starting at `A` are bounded. -/
def IsFSMFF (C : Type u) [Category.{v} C] : Prop :=
  (∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsFSM f → ¬ IsIso f →
    ∃ p : Quiver.Path X Y, AllOf (fun _ _ g => IsFSMI g) p ∧ composePath p = f) ∧
  ∀ X : C, ∃ N : ℕ, ∀ ⦃Y : C⦄ (p : Quiver.Path X Y), AllOf (fun _ _ g => IsFSMI g) p →
    p.length ≤ N

/-- A category of FSM-type is of FSMFF-type ([FrdI] §0, p. 18). -/
lemma isFSMFF_of_fsm (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsFSM f → IsIso f) : IsFSMFF C := by
  refine ⟨fun X Y f hf hn => absurd (h f hf) hn, fun X => ⟨0, fun Y p hp => ?_⟩⟩
  cases p with
  | nil => exact le_refl _
  | cons p f => exact absurd (h f hp.2.1) hp.2.2.1

/-- **The assertion of [FrdI], Proposition 1.14(iii)** for a pre-Frobenioid `P : C ⥤ F_Φ`. -/
def Prop114iii {D : Type*} [Category D] {Φ : DivMonoid D} (P : C ⥤ Elem Φ) : Prop :=
  ∀ ⦃X Y : C⦄ (φ : X ⟶ Y), IsIrreducible φ → (¬ IsPreStep P φ ↔ BoundedFSMIChains φ)

end Chains

/-! ### The counterexample -/

namespace Counterexample

/-- The rational functions `B = ∏_{n ∈ ℕ} ℤ/n`: torsion of every order. -/
abbrev Tors : Type := ∀ n : ℕ, ZMod n

/-- `B` on `Pt`. -/
abbrev bTors : GrpOn.{0} Pt := constGrpOn Tors

/-- `Φ = ℤ_{≥0}` on `Pt`. -/
abbrev PhiN : DivMonoid.{0} Pt := phiNat.{0}

/-- `Div_B = 0`. -/
abbrev divTors : DivHom bTors PhiN.toGrpOn := constDivHom 0

/-- **The model Frobenioid of the counterexample**. -/
abbrev CE : Type := Model PhiN bTors divTors

local notation "𝐏" => Model.toElem PhiN bTors divTors

lemma tors_spec (n : ℕ) (hn : 2 ≤ n) :
    (Pi.single n 1 : Tors) ≠ 0 ∧ n • (Pi.single n 1 : Tors) = 0 := by
  refine ⟨fun h => ?_, funext fun m => ?_⟩
  · have h1 := congrFun h n
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    haveI : Fact (1 < n) := ⟨hn⟩
    exact one_ne_zero h1
  · rw [Pi.smul_apply, Pi.zero_apply]
    by_cases hm : m = n
    · subst hm
      rw [Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_self]
    · rw [Pi.single_eq_of_ne hm, smul_zero]

lemma hasAllTorsion : HasAllTorsion bTors := fun _ n hn => ⟨Pi.single n 1, tors_spec n hn⟩

lemma baseHyp : BaseHyp Pt := ⟨fun _ _ f _ => isIso_pt f, fun _ f => isIso_pt f⟩

/-- `CE` is a Frobenioid ([FrdI], Theorem 5.2(ii)). -/
theorem isFrobenioid : IsFrobenioid 𝐏 := Model.isFrobenioid

/-- `CE` is of isotropic type. -/
theorem isIsotropic (X : CE) : IsIsotropic 𝐏 X := Model.isIsotropic X

/-- The base category `Pt` is of FSMFF-type. -/
theorem pt_isFSMFF : IsFSMFF Pt := isFSMFF_of_fsm fun _ _ f _ => isIso_pt f

/-- The objects `(pt, k)`. -/
abbrev obj (k : ℤ) : CE := ⟨pt, ⟨k⟩⟩

lemma down_div_nonneg {X Y : CE} (f : X ⟶ Y) : 0 ≤ f.div.down := f.div_mem

/-- A pre-step of `CE` with zero divisor `0` is an isomorphism. -/
lemma isIso_of_preStep_div {X Y : CE} (f : X ⟶ Y) (hf : IsPreStep 𝐏 f) (h : f.div.down = 0) :
    IsIso f :=
  Model.isIso_of f hf.1 hf.2 (ULift.ext _ _ h)

@[simp] lemma pb_eq {A A' : Pt} (g : A ⟶ A') (x : ULift.{0} ℤ) :
    PhiN.pb g x = x := rfl

@[simp] lemma divTors_eq (A : Pt) (u : Tors) : divTors.app A u = 0 := rfl

/-- The relation of a morphism of `CE`: `deg·α_X + Div = α_Y`. -/
lemma rel_down {X Y : CE} (f : X ⟶ Y) :
    (f.deg : ℤ) * X.α.down + f.div.down = Y.α.down := by
  have r := congrArg ULift.down f.rel
  simpa [ULift.add_down, ULift.smul_down] using r

lemma div_comp_down {X Y Z : CE} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).div.down = g.div.down + (g.deg : ℤ) * f.div.down := by
  simp [Model.comp_div, ULift.add_down]

/-- The unique morphism of `Pt`. -/
def ptHom (a b : Pt) : a ⟶ b := eqToHom (Subsingleton.elim a b)

/-- A step `(1, id, k, u)` of `CE` from a relation `α_X + k = α_Y`. -/
def stepHom (X Y : CE) (k : ℤ) (hk : 0 ≤ k) (u : Tors) (h : X.α.down + k = Y.α.down) :
    X ⟶ Y :=
  Model.mk1 (ptHom X.base Y.base) ⟨k⟩ hk u (by
    apply ULift.ext
    simp only [ULift.add_down, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, add_zero]
    exact h)

lemma isPreStep_stepHom (X Y : CE) (k : ℤ) (hk : 0 ≤ k) (u : Tors)
    (h : X.α.down + k = Y.α.down) : IsPreStep 𝐏 (stepHom X Y k hk u h) :=
  ⟨show degFr 𝐏 _ = 1 from rfl, isIso_pt _⟩

/-- An irreducible pre-step of `CE` has zero divisor `1`. -/
lemma div_eq_one_of_irreducible {X Y : CE} (f : X ⟶ Y) (hf : IsPreStep 𝐏 f)
    (hi : IsIrreducible f) : f.div.down = 1 := by
  have h1 : f.deg = 1 := hf.1
  have hpos := down_div_nonneg f
  have r := rel_down f
  rw [h1, PNat.one_coe, Nat.cast_one, one_mul] at r
  rcases lt_trichotomy f.div.down 1 with h | h | h
  · exact absurd (isIso_of_preStep_div f hf (by omega)) hi.1
  · exact h
  · exfalso
    let W : CE := obj (X.α.down + 1)
    let a : X ⟶ W := stepHom X W 1 (by norm_num) 0 rfl
    let b : W ⟶ Y := Model.mk1 f.base ⟨f.div.down - 1⟩
      (show (0 : ℤ) ≤ f.div.down - 1 by omega) f.u (by
      apply ULift.ext
      simp only [W, ULift.add_down, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, add_zero]
      change X.α.down + 1 + (f.div.down - 1) = Y.α.down
      omega)
    have hab : a ≫ b = f := by
      refine Model.hom_ext (by simp [a, b, stepHom, h1]) (Subsingleton.elim _ _) ?_ ?_
      · ext
        simp [a, b, stepHom, ULift.add_down]
      · simp [a, b, stepHom]
    rcases hi.2 a b hab with ha | hb
    · have := congrArg ULift.down (Div_of_isIso (P := 𝐏) a)
      simp [a, stepHom] at this
    · have := congrArg ULift.down (Div_of_isIso (P := 𝐏) b)
      simp only [Model.Div_eq, b, Model.mk1_div, ULift.zero_down] at this
      omega

/-- The FSMI-morphisms of `CE` are the pre-steps with zero divisor `1`. -/
lemma fsmi_spec {X Y : CE} {f : X ⟶ Y} (hf : IsFSMI f) : f.deg = 1 ∧ f.div.down = 1 := by
  have hp := (Model.isPreStep_iff_isFSM baseHyp hasAllTorsion f).mpr hf.1
  exact ⟨hp.1, div_eq_one_of_irreducible f hp hf.2⟩

/-- The zero divisor of a composite of FSMI-morphisms is the length of the chain. -/
lemma path_spec {X : CE} : ∀ {Y : CE} (p : Quiver.Path X Y),
    AllOf (fun _ _ f => IsFSMI f) p →
      (composePath p).div.down = p.length ∧ (composePath p).deg = 1
  | _, .nil, _ => ⟨rfl, rfl⟩
  | _, .cons p f, h => by
    obtain ⟨ih₁, ih₂⟩ := path_spec p h.1
    obtain ⟨hf₁, hf₂⟩ := fsmi_spec h.2
    refine ⟨?_, ?_⟩
    · rw [composePath_cons, div_comp_down, ih₁, hf₁, hf₂, Quiver.Path.length_cons]
      push_cast
      ring
    · rw [composePath_cons, Model.comp_deg, ih₂, hf₁]
      rfl

/-- The step `φ = (1, id, 1, 0) : (pt, 0) → (pt, 1)`. -/
def φ₀ : obj 0 ⟶ obj 1 := stepHom (obj 0) (obj 1) 1 (by norm_num) 0 rfl

lemma φ₀_isPreStep : IsPreStep 𝐏 φ₀ := isPreStep_stepHom _ _ _ _ _ _

lemma φ₀_irreducible : IsIrreducible φ₀ := by
  refine ⟨fun h => ?_, fun W a b hab => ?_⟩
  · have := congrArg ULift.down (Div_of_isIso (P := 𝐏) φ₀)
    simp [φ₀, stepHom] at this
  · have hdeg := congrArg Model.Hom.deg hab
    have hdiv := congrArg (fun f => f.div.down) hab
    simp only [Model.comp_deg, φ₀, stepHom, Model.mk1_deg] at hdeg
    have ha1 : a.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hdeg))
    have hb1 : b.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val hdeg))
    simp only [div_comp_down, hb1, PNat.one_coe, Nat.cast_one, one_mul] at hdiv
    have e : (φ₀.div).down = 1 := rfl
    rw [e] at hdiv
    have ha := down_div_nonneg a
    have hb := down_div_nonneg b
    rcases (show a.div.down = 0 ∨ b.div.down = 0 by omega) with h | h
    · exact Or.inl (Model.isIso_of a ha1 (isIso_pt _) (ULift.ext _ _ h))
    · exact Or.inr (Model.isIso_of b hb1 (isIso_pt _) (ULift.ext _ _ h))

/-- `φ₀` satisfies the condition of [FrdI], Proposition 1.14(iii) with `N = 2`. -/
lemma φ₀_bounded : BoundedFSMIChains φ₀ := by
  refine ⟨2, fun Z ψ p hψ hp hc => ?_⟩
  obtain ⟨hl, -⟩ := path_spec p hp
  obtain ⟨hψ₁, hψ₂⟩ := fsmi_spec hψ
  rw [hc, div_comp_down, hψ₁, hψ₂] at hl
  have e : (φ₀.div).down = 1 := rfl
  rw [e] at hl
  push_cast at hl
  omega

/-- **[FrdI], Proposition 1.14(iii) fails** for the Frobenioid `CE` of isotropic type over the
base category `Pt` of FSMFF-type: the irreducible pre-step `φ₀` satisfies the condition that
(iii) attributes to the non-pre-steps. -/
theorem not_prop114iii : ¬ Prop114iii 𝐏 :=
  fun h => (h φ₀ φ₀_irreducible).2 φ₀_bounded φ₀_isPreStep

/-- The prime-Frobenius morphisms of `CE` are not monomorphisms (hence not FSMI-morphisms), which
is where the argument of [FrdI] for Proposition 1.14(iii) breaks down. -/
theorem frob_not_mono (X : CE) (n : ℕ+) (hn : n ≠ 1) : ¬ Mono (Model.frob X n) := fun _ =>
  hn (Model.deg_eq_one_of_mono hasAllTorsion (Model.frob X n))

end Counterexample

end Frobenioid

end Iut
