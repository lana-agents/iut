/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Cor53
import Iut.Frobenioid.Tempered.AutBase
import Iut.Frobenioid.Tempered.SplitTransport

/-!
# Rigidity of automorphisms of Galois model Frobenioids over the identity (MR21 R3)

IUT I, Corollary 5.3 (ii) (l.9891–9894 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): the natural map
`Isom(¹F, ²F) → Isom(¹D, ²D)` is bijective. By `FStripNon.isoClassToD_injective` (`IsoClass.lean`)
the injectivity at `V^non` reduces to `FrobCat.AutRigid` of the models `C_v`: every automorphism
of `C_v` whose base functor is isomorphic to the identity is 2-isomorphic to the identity. This
file proves it for Galois model Frobenioids `GaloisModel G ℓ Γ` (`galFrob`) from a rigidity
property of the `G`-module `M` (`ψ = id` for `G`-equivariant `ψ` with `ℓ ∘ ψ = λ ℓ`, the shape of
[AbsTopIII], Proposition 3.2 (iv), injectivity, `KummerRigid`), and hence for `C_v`.

The argument (an automorphism `h` with `β : h.D ≅ id`):

* the square `commP` and `β` give base isomorphisms `ε_X : X_D ≅ F(X)_D` over which
  `F = h.C.functor` lies, and `F` preserves Frobenius degrees (`autF_map_base`, `autF_map_deg`;
  isomorphisms of elementary Frobenioids have degree `1` and divisor `0`, `elem_isIso_deg`,
  `elem_isIso_div`); on divisors `F` is `h.phi`, which is the same order automorphism of `Γ` at
  every object (`phi_eq_top`), a scaling by `λ > 0` when `Γ` has that property (`Γ = ℚ`:
  `gammaQ_scaling`);
* the images `F^birat` of rational functions ([FrdI], Corollary 4.10; `Model.mapUnit`) transported
  by `ε` are compatible with all linear morphisms (`psi_nat`), hence glue to a `G`-equivariant
  additive automorphism `ψ` of `M` (`autPsi`) with `ℓ ∘ ψ = λ ℓ` (`ell_autPsi`);
* rigidity gives `ψ = id`, so `λ = 1`: `F` is the identity on divisors and on rational functions,
  and [IUTchI], Corollary 5.3 (iv), formal core (`Model.nonempty_iso_id_of_over_id`, with the
  explicit isomorphism) gives `F ≅ id` compatible with `commP` and `β`: a 2-isomorphism
  `h ⟹ id` (`galFrob_autRigid`).

For `C_v` (`cvFrob_autRigid`) the inputs are: `Γ = ℚ`, `ord(\bar{ℚ}_p^×) ⊆ ℚ`, open stabilizers,
`p` with `ord(p) = 1`, and `KummerRigid D v` (proved in `KummerRigid.lean` from the surjectivity of
`Π_v → G_v`, debt H3). **IUT I, Corollary 5.3 (ii), bijectivity at `V^non`**:
`FStripNon.isoClassToD_bijective`.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

/-! ### Isomorphisms of elementary Frobenioids -/

namespace FrobCat

/-- An isomorphism of `F_Φ` has Frobenius degree `1`. -/
lemma elem_isIso_deg {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {a b : Elem Φ}
    (f : a ⟶ b) [IsIso f] : f.deg = 1 := by
  have h : (inv f).deg * f.deg = 1 := congrArg Elem.Hom.deg (IsIso.hom_inv_id f)
  have h2 : ((inv f).deg : ℕ) * (f.deg : ℕ) = 1 := by
    rw [← PNat.mul_coe, h]; rfl
  have h3 : (f.deg : ℕ) = 1 := Nat.eq_one_of_mul_eq_one_left h2
  exact PNat.eq (h3.trans PNat.one_coe.symm)

/-- An isomorphism of `F_Φ` has zero divisor (`Φ` is sharp). -/
lemma elem_isIso_div {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {a b : Elem Φ}
    (f : a ⟶ b) [IsIso f] : f.div = 0 := by
  have h : (f ≫ inv f).div = (𝟙 a : a ⟶ a).div := congrArg Elem.Hom.div (IsIso.hom_inv_id f)
  rw [Elem.comp_div, Elem.id_div, elem_isIso_deg (inv f), PNat.one_coe, one_smul] at h
  have h1 : Φ.pb f.base (inv f).div ∈ Φ.pos a.base := Φ.pb_mem _ (inv f).div_mem
  have h2 : -f.div ∈ Φ.pos a.base := by rw [neg_eq_of_add_eq_zero_left h]; exact h1
  exact Φ.sharp f.div_mem h2

/-- Isomorphisms of `F_Φ` with the same base morphism are equal. -/
lemma elem_hom_ext_of_isIso {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {a b : Elem Φ}
    {f g : a ⟶ b} (hf : IsIso f) (hg : IsIso g) (h : f.base = g.base) : f = g :=
  Elem.hom_ext h ((elem_isIso_div f).trans (elem_isIso_div g).symm)
    ((elem_isIso_deg f).trans (elem_isIso_deg g).symm)

/-- Degrees in a square of `F_Φ` with isomorphisms as vertical sides. -/
lemma elem_deg_conj {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {a b c d : Elem Φ}
    {u : a ⟶ b} {i : b ⟶ d} {j : a ⟶ c} {v : c ⟶ d} [IsIso i] [IsIso j]
    (h : u ≫ i = j ≫ v) : u.deg = v.deg := by
  have h1 := congrArg Elem.Hom.deg h
  rw [Elem.comp_deg, Elem.comp_deg, elem_isIso_deg i, elem_isIso_deg j, one_mul, mul_one] at h1
  exact h1

/-- Divisors in a square of `F_Φ` with isomorphisms as vertical sides. -/
lemma elem_div_conj {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {a b c d : Elem Φ}
    {u : a ⟶ b} {i : b ⟶ d} {j : a ⟶ c} {v : c ⟶ d} [IsIso i] [IsIso j]
    (h : u ≫ i = j ≫ v) : u.div = Φ.pb j.base v.div := by
  have h1 := congrArg Elem.Hom.div h
  rw [Elem.comp_div, Elem.comp_div, elem_isIso_div i, elem_isIso_div j, elem_isIso_deg i,
    map_zero, zero_add, PNat.one_coe, one_smul, smul_zero, add_zero] at h1
  exact h1

/-- A morphism conjugated through two squares of isomorphisms, in an arbitrary category. -/
lemma conj_of_sq {C₀ : Type*} [Category* C₀] {x1 x2 y1 y2 z1 z2 : C₀} {u : x1 ⟶ x2}
    {φ : z1 ⟶ z2} {I1 : x1 ≅ y1} {I2 : x2 ≅ y2} {D : y1 ⟶ y2} {J1 : y1 ≅ z1} {J2 : y2 ≅ z2}
    (h1 : u ≫ I2.hom = I1.hom ≫ D) (h2 : D ≫ J2.hom = J1.hom ≫ φ) :
    u = (I1 ≪≫ J1).hom ≫ φ ≫ (I2 ≪≫ J2).inv := by
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.trans_inv, Category.assoc]
  rw [← reassoc_of% h2, ← reassoc_of% h1]
  simp

end FrobCat

/-! ### Galois model Frobenioids -/

section Galois

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M]
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m} {Γ : AddSubgroup ℝ}

variable (G ℓ hℓ Γ) in
/-- **The Galois model Frobenioid `GaloisModel G ℓ Γ` with its base `B(G)⁰`.** -/
abbrev galFrob : FrobCat :=
  FrobCat.ofModel (GaloisModel G ℓ hℓ Γ)
    (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))

/-- The underlying element of `M` of a rational function. -/
def bval {A : OrbitObj G} (u : (bGal G ℓ hℓ Γ).obj A) : M :=
  (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from u).1

/-- A rational function from an element of `M`. -/
def bmk {A : OrbitObj G} (m : M) (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    (bGal G ℓ hℓ Γ).obj A :=
  (⟨m, hm⟩ : ↥(fixedSub (preSub G ℓ hℓ Γ) A))

lemma bval_mem {A : OrbitObj G} (u : (bGal G ℓ hℓ Γ).obj A) :
    bval u ∈ fixedSub (preSub G ℓ hℓ Γ) A :=
  (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from u).2

@[simp] lemma bval_bmk {A : OrbitObj G} (m : M) (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    bval (bmk (hℓ := hℓ) m hm) = m := rfl

lemma bval_injective {A : OrbitObj G} :
    Function.Injective (bval : (bGal G ℓ hℓ Γ).obj A → M) := fun _ _ h => Subtype.ext h

@[simp] lemma bval_add {A : OrbitObj G} (u v : (bGal G ℓ hℓ Γ).obj A) :
    bval (u + v) = bval u + bval v := rfl

@[simp] lemma bval_zero {A : OrbitObj G} : bval (0 : (bGal G ℓ hℓ Γ).obj A) = 0 := rfl

@[simp] lemma bval_nsmul {A : OrbitObj G} (n : ℕ) (u : (bGal G ℓ hℓ Γ).obj A) :
    bval (n • u) = n • bval u := rfl

@[simp] lemma bval_sub {A : OrbitObj G} (u v : (bGal G ℓ hℓ Γ).obj A) :
    bval (u - v) = bval u - bval v := rfl

lemma bval_pb {A A' : OrbitObj G} (f : A ⟶ A') (u : (bGal G ℓ hℓ Γ).obj A') :
    bval ((bGal G ℓ hℓ Γ).pb f u) = OrbitHom.rep f • bval u := rfl

lemma bval_pb_of_mk_one {A A' : OrbitObj G} (f : A ⟶ A')
    (hf : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1) (u : (bGal G ℓ hℓ Γ).obj A') :
    bval ((bGal G ℓ hℓ Γ).pb f u) = bval u :=
  (bval_mem u).2 _ (OrbitHom.rep_mem_of_mk_one hf)

lemma divGal_val {A : OrbitObj G} (u : (bGal G ℓ hℓ Γ).obj A) :
    (((divGal G ℓ hℓ Γ).app A u : Γ) : ℝ) = ℓ (bval u) := rfl

/-- The terminal object `G/G` of `B(G)⁰`. -/
def topObj : OrbitObj G := ⟨⊤, isOpen_univ⟩

/-- The morphism `A ⟶ G/G`. -/
def toTop (A : OrbitObj G) : A ⟶ topObj :=
  pointHom A topObj (QuotientGroup.mk 1) fun g _ => by
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact (mk_eq_one_iff.mpr (Subgroup.mem_top g))

/-- The object `G/H` with `α = 0`. -/
abbrev obj0 (A : OrbitObj G) : GaloisModel G ℓ hℓ Γ := ⟨A, 0⟩

/-- The linear morphism `(1, f, 0, 0) : (A, 0) ⟶ (A', 0)` over `f`. -/
def hom0 {A A' : OrbitObj G} (f : A ⟶ A') :
    (obj0 (hℓ := hℓ) (Γ := Γ) A : GaloisModel G ℓ hℓ Γ) ⟶ obj0 A' :=
  Model.mk1 f 0 ((constPhi (OrbitObj G) Γ).pos _).zero_mem 0 (by rw [map_zero]; simp [obj0])

/-- The intersection of two objects. -/
def interObj (A A' : OrbitObj G) : OrbitObj G := ⟨A.H ⊓ A'.H, A.isOpen.inter A'.isOpen⟩

/-- The projection `A ∩ A' ⟶ A`. -/
def interFst (A A' : OrbitObj G) : interObj A A' ⟶ A :=
  pointHom _ A (QuotientGroup.mk 1) fun _ hg => by
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact mk_eq_one_iff.mpr hg.1

/-- The projection `A ∩ A' ⟶ A'`. -/
def interSnd (A A' : OrbitObj G) : interObj A A' ⟶ A' :=
  pointHom _ A' (QuotientGroup.mk 1) fun _ hg => by
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact mk_eq_one_iff.mpr hg.2

omit [IsTopologicalGroup G] in
lemma interFst_mk {A A' : OrbitObj G} :
    (interFst A A').toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
  rw [interFst, pointHom_mk, one_smul]

omit [IsTopologicalGroup G] in
lemma interSnd_mk {A A' : OrbitObj G} :
    (interSnd A A').toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
  rw [interSnd, pointHom_mk, one_smul]

omit [IsTopologicalGroup G] in
lemma mem_fixedSub_inter {A A' : OrbitObj G} {m : M}
    (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    m ∈ fixedSub (preSub G ℓ hℓ Γ) (interObj A A') :=
  ⟨hm.1, fun g hg => hm.2 g hg.1⟩

omit [IsTopologicalGroup G] in
lemma mem_fixedSub_inter' {A A' : OrbitObj G} {m : M}
    (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A') :
    m ∈ fixedSub (preSub G ℓ hℓ Γ) (interObj A A') :=
  ⟨hm.1, fun g hg => hm.2 g hg.2⟩

/-! ### An automorphism lying over the identity of the base -/

variable (h : (galFrob G ℓ hℓ Γ).Iso (galFrob G ℓ hℓ Γ))
  (β : h.D.functor ≅ 𝟭 (galFrob G ℓ hℓ Γ).D)

/-- The functor of model Frobenioids of `h`. -/
abbrev autF : GaloisModel G ℓ hℓ Γ ⥤ GaloisModel G ℓ hℓ Γ := h.C.functor

instance : (autF h).IsEquivalence := inferInstanceAs h.C.functor.IsEquivalence

/-- The component of `commP` at `X`, `P(F X) ≅ (h.D(X_D), …)`. -/
abbrev cP (X : GaloisModel G ℓ hℓ Γ) :
    (galFrob G ℓ hℓ Γ).P.obj ((autF h).obj X) ⟶
      (FrobCat.elemMap h.D.functor h.phi h.phi_pos h.phi_pb).obj ((galFrob G ℓ hℓ Γ).P.obj X) :=
  (FrobCat.sqIso h.commP).hom.app X

instance cP_isIso (X : GaloisModel G ℓ hℓ Γ) : IsIso (cP h X) :=
  ⟨⟨(FrobCat.sqIso h.commP).inv.app X, (FrobCat.sqIso h.commP).hom_inv_id_app X,
    (FrobCat.sqIso h.commP).inv_hom_id_app X⟩⟩

lemma cP_deg (X : GaloisModel G ℓ hℓ Γ) : (cP h X).deg = 1 := FrobCat.elem_isIso_deg _

lemma cP_div (X : GaloisModel G ℓ hℓ Γ) : (cP h X).div = 0 := FrobCat.elem_isIso_div _

/-- **`ε_X : X_D ≅ F(X)_D`**, from `commP` and `β`. -/
def eps (X : GaloisModel G ℓ hℓ Γ) : X.base ≅ ((autF h).obj X).base :=
  (Elem.proj.mapIso ((FrobCat.sqIso h.commP).app X) ≪≫ β.app X.base).symm

lemma eps_inv (X : GaloisModel G ℓ hℓ Γ) :
    (eps h β X).inv = (cP h X).base ≫ β.hom.app X.base := rfl

lemma cP_naturality {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y) :
    (galFrob G ℓ hℓ Γ).P.map ((autF h).map φ) ≫ cP h Y =
      cP h X ≫ (FrobCat.elemMap h.D.functor h.phi h.phi_pos h.phi_pb).map
        ((galFrob G ℓ hℓ Γ).P.map φ) :=
  (FrobCat.sqIso h.commP).hom.naturality φ

/-- **`F` lies over the identity through `ε`.** -/
lemma autF_map_base {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y) :
    ((autF h).map φ).base = (eps h β X).inv ≫ φ.base ≫ (eps h β Y).hom :=
  FrobCat.conj_of_sq (I1 := Elem.proj.mapIso ((FrobCat.sqIso h.commP).app X))
    (I2 := Elem.proj.mapIso ((FrobCat.sqIso h.commP).app Y)) (J1 := β.app X.base)
    (J2 := β.app Y.base) (congrArg Elem.Hom.base (cP_naturality h φ)) (β.hom.naturality φ.base)

/-- **`F` preserves Frobenius degrees.** -/
lemma autF_map_deg {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y) :
    ((autF h).map φ).deg = φ.deg :=
  FrobCat.elem_deg_conj (cP_naturality h φ)

/-- **`F` is `h.phi` on divisors.** -/
lemma autF_map_div {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y) :
    ((autF h).map φ).div = h.phi X.base φ.div :=
  FrobCat.elem_div_conj (cP_naturality h φ)

/-- `h.phi` is the same at every object (pull-backs of `Γ_{≥0}` are identities and every object
maps to `G/G`). -/
lemma phi_eq_top (A : OrbitObj G) (x : Γ) : h.phi A x = h.phi topObj x :=
  h.phi_pb (toTop A) x

include β in
/-- The hypotheses `hpre` of `Model.mapUnit`. -/
lemma autF_hpre : ∀ ⦃X Y : GaloisModel G ℓ hℓ Γ⦄ (φ : X ⟶ Y),
    IsPreStep (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ)) φ ↔
      IsPreStep (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))
        ((autF h).map φ) :=
  Model.preStep_iff_of_over (autF h) (eps h β) (fun φ => autF_map_base h β φ)
    (fun φ => autF_map_deg h φ)

include β in
lemma autF_hbe : ∀ ⦃X Y : GaloisModel G ℓ hℓ Γ⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ ((autF h).map φ).base = ((autF h).map φ').base :=
  Model.baseEq_iff_of_over (autF h) (eps h β) (fun φ => autF_map_base h β φ)

/-- `F^birat` on rational functions, transported along `ε`: `B(X_D) → B(X_D)`. -/
def psiX (X : GaloisModel G ℓ hℓ Γ) (c : (bGal G ℓ hℓ Γ).obj X.base) :
    (bGal G ℓ hℓ Γ).obj X.base :=
  (bGal G ℓ hℓ Γ).pb (eps h β X).hom (Model.mapUnit (autF h) (autF_hpre h β) (X := X) c)

lemma psiX_add (X : GaloisModel G ℓ hℓ Γ) (c d : (bGal G ℓ hℓ Γ).obj X.base) :
    psiX h β X (c + d) = psiX h β X c + psiX h β X d := by
  rw [psiX, psiX, psiX, Model.mapUnit_add (autF h) (autF_hpre h β) (autF_hbe h β), map_add]

/-- **Compatibility of `psiX` with linear morphisms.** -/
lemma psi_nat {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y) (hφ : φ.deg = 1)
    (c : (bGal G ℓ hℓ Γ).obj Y.base) :
    psiX h β X ((bGal G ℓ hℓ Γ).pb φ.base c) = (bGal G ℓ hℓ Γ).pb φ.base (psiX h β Y c) := by
  rw [psiX, psiX, Model.mapUnit_pb_linear (autF h) (autF_hpre h β) (autF_hbe h β) φ hφ
    ((autF_map_deg h φ).trans hφ), autF_map_base h β φ, ← GrpOn.pb_comp', ← GrpOn.pb_comp']
  congr 1
  simp

/-- `psiX` does not depend on `α_X`: it agrees with its value at `(X_D, 0)`. -/
lemma psiX_eq_obj0 (X : GaloisModel G ℓ hℓ Γ) (c : (bGal G ℓ hℓ Γ).obj X.base) :
    psiX h β X c = psiX h β (obj0 X.base) c := by
  rcases le_total (0 : ℝ) (X.α : ℝ) with hα | hα
  · -- `(1, id, α, 0) : (A, 0) ⟶ X`
    let φ : (obj0 X.base : GaloisModel G ℓ hℓ Γ) ⟶ X :=
      Model.mk1 (𝟙 X.base) X.α hα 0 (by rw [map_zero]; simp [obj0])
    have e := psi_nat h β φ rfl c
    simp only [φ, Model.mk1_base] at e
    exact ((bGal G ℓ hℓ Γ).pb_id _ _).symm.trans
      (e.symm.trans (congrArg (psiX h β (obj0 X.base)) ((bGal G ℓ hℓ Γ).pb_id _ _)))
  · -- `(1, id, -α, 0) : X ⟶ (A, 0)`
    let φ : X ⟶ (obj0 X.base : GaloisModel G ℓ hℓ Γ) :=
      Model.mk1 (𝟙 X.base) (-X.α) (by
        change (0 : ℝ) ≤ ((-X.α : Γ) : ℝ)
        rw [AddSubgroup.coe_neg]; linarith) 0 (by rw [map_zero]; simp)
    have e := psi_nat h β φ rfl c
    simp only [φ, Model.mk1_base] at e
    exact (congrArg (psiX h β X) ((bGal G ℓ hℓ Γ).pb_id _ _)).symm.trans
      (e.trans ((bGal G ℓ hℓ Γ).pb_id _ _))

/-- `psi` on `B(G/H)`. -/
abbrev psiA (A : OrbitObj G) (c : (bGal G ℓ hℓ Γ).obj A) : (bGal G ℓ hℓ Γ).obj A :=
  psiX h β (obj0 A) c

lemma psiA_add (A : OrbitObj G) (c d : (bGal G ℓ hℓ Γ).obj A) :
    psiA h β A (c + d) = psiA h β A c + psiA h β A d :=
  psiX_add h β (obj0 A) c d

lemma psiA_pb {A A' : OrbitObj G} (f : A ⟶ A') (c : (bGal G ℓ hℓ Γ).obj A') :
    psiA h β A ((bGal G ℓ hℓ Γ).pb f c) = (bGal G ℓ hℓ Γ).pb f (psiA h β A' c) :=
  psi_nat h β (hom0 f) rfl c

/-- The values of `psiA` do not depend on the open subgroup. -/
lemma bval_psiA_indep {A A' : OrbitObj G} {m : M} (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A)
    (hm' : m ∈ fixedSub (preSub G ℓ hℓ Γ) A') :
    bval (psiA h β A (bmk m hm)) = bval (psiA h β A' (bmk m hm')) := by
  have e1 := psiA_pb h β (interFst A A') (bmk m hm)
  have e2 := psiA_pb h β (interSnd A A') (bmk m hm')
  have c1 : (bGal G ℓ hℓ Γ).pb (interFst A A') (bmk m hm) = bmk m (mem_fixedSub_inter hm) :=
    bval_injective (bval_pb_of_mk_one _ interFst_mk _)
  have c2 : (bGal G ℓ hℓ Γ).pb (interSnd A A') (bmk m hm') = bmk m (mem_fixedSub_inter' hm') :=
    bval_injective (bval_pb_of_mk_one _ interSnd_mk _)
  rw [c1] at e1
  rw [c2] at e2
  have e3 := congrArg bval e1
  have e4 := congrArg bval e2
  rw [bval_pb_of_mk_one _ interFst_mk] at e3
  rw [bval_pb_of_mk_one _ interSnd_mk] at e4
  rw [← e3, ← e4]

variable {h β}

section Glue

variable (hmem : ∀ m, ℓ m ∈ Γ) (hopen : ∀ m : M, IsOpen (MulAction.stabilizer G m : Set G))

/-- The stabilizer of `m` as an object of `B(G)⁰`. -/
def stabObj (hopen : ∀ m : M, IsOpen (MulAction.stabilizer G m : Set G)) (m : M) : OrbitObj G :=
  ⟨MulAction.stabilizer G m, hopen m⟩

omit [IsTopologicalGroup G] in
include hmem in
lemma mem_stabObj (m : M) : m ∈ fixedSub (preSub G ℓ hℓ Γ) (stabObj hopen m) :=
  ⟨hmem m, fun _ hg => hg⟩

variable (h β) in
/-- **The glued map `ψ : M → M`.** -/
def psiFun (m : M) : M := bval (psiA h β (stabObj hopen m) (bmk m (mem_stabObj hmem hopen m)))

lemma psiFun_eq {A : OrbitObj G} {m : M} (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    psiFun h β hmem hopen m = bval (psiA h β A (bmk m hm)) :=
  bval_psiA_indep h β _ _

lemma psiFun_add (m m' : M) :
    psiFun h β hmem hopen (m + m') = psiFun h β hmem hopen m + psiFun h β hmem hopen m' := by
  let A := interObj (interObj (stabObj hopen m) (stabObj hopen m')) (stabObj hopen (m + m'))
  have hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A :=
    mem_fixedSub_inter (mem_fixedSub_inter (mem_stabObj hmem hopen m))
  have hm' : m' ∈ fixedSub (preSub G ℓ hℓ Γ) A :=
    mem_fixedSub_inter (mem_fixedSub_inter' (mem_stabObj hmem hopen m'))
  have hmm : m + m' ∈ fixedSub (preSub G ℓ hℓ Γ) A :=
    (fixedSub (preSub G ℓ hℓ Γ) A).add_mem hm hm'
  rw [psiFun_eq hmem hopen hm, psiFun_eq hmem hopen hm', psiFun_eq hmem hopen hmm,
    ← bval_add, ← psiA_add]
  rfl

/-- **`ψ` is `G`-equivariant.** -/
lemma psiFun_smul (g : G) (m : M) :
    psiFun h β hmem hopen (g • m) = g • psiFun h β hmem hopen m := by
  let A := stabObj hopen m
  let A' := stabObj hopen (g • m)
  have hle : A'.H ≤ MulAction.stabilizer G (QuotientGroup.mk g : G ⧸ A.H) := fun k hk => by
    rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul]
    refine QuotientGroup.eq.mpr ?_
    change (k * g)⁻¹ * g ∈ MulAction.stabilizer G m
    rw [MulAction.mem_stabilizer_iff]
    have hk' : k • g • m = g • m := hk
    have hk'' : k⁻¹ • g • m = g • m := inv_smul_eq_iff.mpr hk'.symm
    calc ((k * g)⁻¹ * g) • m = g⁻¹ • k⁻¹ • g • m := by
          simp only [mul_inv_rev, mul_smul]
      _ = m := by rw [hk'', inv_smul_smul]
  let f : A' ⟶ A := pointHom A' A (QuotientGroup.mk g) hle
  have hrep : (QuotientGroup.mk (OrbitHom.rep f) : G ⧸ A.H) = QuotientGroup.mk g := by
    rw [OrbitHom.mk_rep, pointHom_mk, MulAction.Quotient.smul_mk, smul_eq_mul, one_mul]
  have hrep' : g⁻¹ * OrbitHom.rep f ∈ A.H := QuotientGroup.eq.mp hrep.symm
  have hm := mem_stabObj (hℓ := hℓ) hmem hopen m
  have hgm := mem_stabObj (hℓ := hℓ) hmem hopen (g • m)
  have e := psiA_pb h β f (bmk m hm)
  have c : (bGal G ℓ hℓ Γ).pb f (bmk m hm) = bmk (g • m) hgm :=
    bval_injective (by
      rw [bval_pb, bval_bmk, bval_bmk]
      exact fixed_smul_eq_of_mem _ hm hrep')
  rw [c] at e
  have e' := congrArg bval e
  rw [bval_pb] at e'
  change psiFun h β hmem hopen (g • m) = _ at e'
  rw [e']
  exact fixed_smul_eq_of_mem _ (bval_mem _) hrep'

include hmem hopen in
lemma bval_psiA (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) :
    bval (psiA h β A u) = psiFun h β hmem hopen (bval u) :=
  (psiFun_eq hmem hopen (bval_mem u)).symm

lemma psiFun_injective : Function.Injective (psiFun h β hmem hopen) := by
  intro m m' e
  have hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) (interObj (stabObj hopen m) (stabObj hopen m')) :=
    mem_fixedSub_inter (mem_stabObj hmem hopen m)
  have hm' : m' ∈ fixedSub (preSub G ℓ hℓ Γ) (interObj (stabObj hopen m) (stabObj hopen m')) :=
    mem_fixedSub_inter' (mem_stabObj hmem hopen m')
  rw [psiFun_eq hmem hopen hm, psiFun_eq hmem hopen hm'] at e
  have e2 := congrArg ((bGal G ℓ hℓ Γ).pb
    (eps h β (obj0 (interObj (stabObj hopen m) (stabObj hopen m')))).inv) (bval_injective e)
  simp only [psiX, ← GrpOn.pb_comp', CategoryTheory.Iso.inv_hom_id, GrpOn.pb_id'] at e2
  exact congrArg bval (Model.mapUnit_injective (autF h) (autF_hpre h β) (autF_hbe h β) _ e2)

lemma psiFun_surjective : Function.Surjective (psiFun h β hmem hopen) := by
  intro n
  obtain ⟨x, hx⟩ := Model.mapUnit_surjective (autF h) (autF_hpre h β) (autF_hbe h β)
    (obj0 (stabObj hopen n)) ((bGal G ℓ hℓ Γ).pb (eps h β (obj0 (stabObj hopen n))).inv
      (bmk n (mem_stabObj hmem hopen n)))
  refine ⟨bval x, (bval_psiA (h := h) (β := β) hmem hopen _ x).symm.trans ?_⟩
  change bval ((bGal G ℓ hℓ Γ).pb (eps h β (obj0 (stabObj hopen n))).hom
    (Model.mapUnit (autF h) (autF_hpre h β) x)) = n
  rw [hx, ← GrpOn.pb_comp', CategoryTheory.Iso.hom_inv_id, GrpOn.pb_id']
  rfl

variable (h β) in
/-- **The automorphism `ψ` of `M` induced by `h`** (glued from `F^birat` on all `M^H`). -/
def autPsi : M ≃+ M :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (psiFun h β hmem hopen) (psiFun_add hmem hopen))
    ⟨psiFun_injective hmem hopen, psiFun_surjective hmem hopen⟩

lemma autPsi_apply (m : M) : autPsi h β hmem hopen m = psiFun h β hmem hopen m := rfl

lemma autPsi_smul (g : G) (m : M) :
    autPsi h β hmem hopen (g • m) = g • autPsi h β hmem hopen m :=
  psiFun_smul hmem hopen g m

/-- **On effective rational functions `ψ` is `h.phi` on divisors.** -/
lemma ell_psiA_of_nonneg (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) (hu : 0 ≤ ℓ (bval u)) :
    ℓ (bval (psiA h β A u)) =
      ((@id ↥Γ (h.phi topObj ((divGal G ℓ hℓ Γ).app A u))) : ℝ) := by
  let e : (obj0 A : GaloisModel G ℓ hℓ Γ) ⟶ obj0 A :=
    Model.mk1 (𝟙 A) ((divGal G ℓ hℓ Γ).app A u) hu u rfl
  have hs : IsPreStep (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ)
      (divGal G ℓ hℓ Γ)) e := ⟨rfl, inferInstanceAs (IsIso (𝟙 A))⟩
  have ht : IsPreStep (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ)
      (divGal G ℓ hℓ Γ)) (𝟙 (obj0 A : GaloisModel G ℓ hℓ Γ)) :=
    ⟨rfl, inferInstanceAs (IsIso (𝟙 A))⟩
  have hu1 := Model.mapUnit_u_sub (autF h) (autF_hpre h β) (autF_hbe h β) hs ht rfl
  rw [CategoryTheory.Functor.map_id] at hu1
  change Model.mapUnit (autF h) (autF_hpre h β) (u - 0) = ((autF h).map e).u - 0 at hu1
  rw [sub_zero, sub_zero] at hu1
  have hr := ((autF h).map e).rel
  rw [autF_map_deg, autF_map_div] at hr
  change ((1 : ℕ+) : ℕ) • (@id ↥Γ (((autF h).obj (obj0 A)).α)) +
      (@id ↥Γ (h.phi A ((divGal G ℓ hℓ Γ).app A u))) =
    (@id ↥Γ (((autF h).obj (obj0 A)).α)) +
      (@id ↥Γ ((divGal G ℓ hℓ Γ).app _ ((autF h).map e).u)) at hr
  rw [PNat.one_coe, one_smul] at hr
  have hr' := add_left_cancel hr
  calc ℓ (bval (psiA h β A u))
      = ℓ (bval (Model.mapUnit (autF h) (autF_hpre h β) (X := obj0 A) u)) := by
        simp only [psiX, bval_pb, hℓ]
    _ = (((divGal G ℓ hℓ Γ).app _ ((autF h).map e).u : Γ) : ℝ) := by rw [hu1]; rfl
    _ = ((@id ↥Γ (h.phi A ((divGal G ℓ hℓ Γ).app A u))) : ℝ) :=
        congrArg Subtype.val hr'.symm
    _ = ((@id ↥Γ (h.phi topObj ((divGal G ℓ hℓ Γ).app A u))) : ℝ) :=
        congrArg Subtype.val (phi_eq_top h A _)

end Glue

/-! ### From `F ≅ id` on divisors and rational functions to a 2-isomorphism -/

section Hom2

variable (hdiv : ∀ {X Y : GaloisModel G ℓ hℓ Γ} (φ : X ⟶ Y),
    ((autF h).map φ).div = (constPhi (OrbitObj G) Γ).pb (eps h β X).inv φ.div)
  (hunit : ∀ (X : GaloisModel G ℓ hℓ Γ) (x : (bGal G ℓ hℓ Γ).obj X.base),
    Model.mapUnit (autF h) (autF_hpre h β) x = (bGal G ℓ hℓ Γ).pb (eps h β X).inv x)

variable (h β) in
/-- **The isomorphism `F ≅ id`** of [IUTchI], Corollary 5.3 (iv), formal core
(`Model.nonempty_iso_id_of_over_id`), made explicit. -/
def autIso : autF h ≅ 𝟭 (GaloisModel G ℓ hℓ Γ) :=
  (Model.twistIsoOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) hdiv).symm ≪≫
    (Model.twistIso (Model.relOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) hdiv) (Model.idOf (autF h) (eps h β))
      (Model.compOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ))
      (Model.cOf_preStep (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ) hunit)).symm

/-- The base of `F(X) ≅ X` is `ε_X⁻¹`. -/
lemma autIso_base (X : GaloisModel G ℓ hℓ Γ) :
    ((autIso h β hdiv hunit).hom.app X).base = (eps h β X).inv := by
  have h1 := FrobCat.map_inv_of_map_hom (Model.forget (constPhi (OrbitObj G) Γ)
      (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))
    ((Model.twistIsoOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) hdiv).app X) (eps h β X) rfl
  have h2 := FrobCat.map_inv_of_map_hom (Model.forget (constPhi (OrbitObj G) Γ)
      (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))
    ((Model.twistIso (Model.relOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) hdiv) (Model.idOf (autF h) (eps h β))
      (Model.compOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ))
      (Model.cOf_preStep (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ) hunit)).app X) (CategoryTheory.Iso.refl _) rfl
  exact (congrArg₂ (· ≫ ·) h1 h2).trans (Category.comp_id _)

include hdiv hunit in
/-- **An automorphism inducing the identity on divisors and rational functions is 2-isomorphic to
the identity.** -/
theorem rel_refl_of_id (hphi : ∀ (A : OrbitObj G) (x : Γ), h.phi A x = x) :
    FrobCat.Iso.Rel h (FrobCat.Iso.refl (galFrob G ℓ hℓ Γ)) := by
  refine ⟨⟨autIso h β hdiv hunit, β, fun A x => (hphi A x).symm, fun A => ?_⟩⟩
  have hb : ((galFrob G ℓ hℓ Γ).P.map ((autIso h β hdiv hunit).hom.app A) ≫
      (FrobCat.sqIso (FrobCat.Iso.refl (galFrob G ℓ hℓ Γ)).commP).hom.app A).base =
      (eps h β A).inv ≫ 𝟙 _ :=
    congrArg (· ≫ 𝟙 _) (autIso_base hdiv hunit A)
  exact FrobCat.elem_hom_ext_of_isIso
    (IsIso.comp_isIso' (CategoryTheory.Functor.map_isIso _ _) (inferInstanceAs (IsIso (𝟙 _))))
    (IsIso.comp_isIso' (cP_isIso h A) inferInstance) (hb.trans (Category.comp_id _))

end Hom2

/-! ### Rigidity -/

section Rigid

variable (hmem : ∀ m, ℓ m ∈ Γ) (hopen : ∀ m : M, IsOpen (MulAction.stabilizer G m : Set G))
  {m0 : M} (hm0 : 0 < ℓ m0) (hfix0 : ∀ g : G, g • m0 = m0)

include hm0 hfix0 in
/-- **`ℓ ∘ ψ = λ ℓ`** when `h.phi` is the scaling by `λ`. -/
lemma ell_autPsi {l : ℝ} (hl : ∀ x : Γ, ((@id ↥Γ (h.phi topObj x)) : ℝ) = l * x)
    (m : M) :
    ℓ (autPsi h β hmem hopen m) = l * ℓ m := by
  have key : ∀ m', 0 ≤ ℓ m' → ℓ (autPsi h β hmem hopen m') = l * ℓ m' := fun m' hm' => by
    rw [autPsi_apply, psiFun]
    exact (ell_psiA_of_nonneg (stabObj hopen m') (bmk m' (mem_stabObj hmem hopen m')) hm').trans
      (hl _)
  have hfixm0 : ∀ n : ℕ, ∀ g : G, g • (n • m0) = n • m0 := fun n g => by
    rw [smul_comm, hfix0]
  obtain ⟨n, hn⟩ := exists_nat_ge (-(ℓ m) / ℓ m0)
  have hn' : 0 ≤ ℓ m + n * ℓ m0 := by
    have := (div_le_iff₀ hm0).1 hn
    linarith
  have h1 := key (m + n • m0) (by rw [map_add, map_nsmul, nsmul_eq_mul]; exact hn')
  have h2 := key (n • m0) (by rw [map_nsmul, nsmul_eq_mul]; positivity)
  have e : m = (m + n • m0) - n • m0 := by abel
  rw [e]
  simp only [map_sub]
  rw [h1, h2]
  ring

include hmem hopen hm0 hfix0 in
/-- **Rigidity of automorphisms of Galois model Frobenioids over the identity**: if every
`G`-equivariant additive automorphism `ψ` of `M` with `ℓ ∘ ψ = λ ℓ` (`λ > 0`) is the identity
(`hrig`) and every order automorphism of `Γ` is a scaling (`hΓ`), then every automorphism of
`GaloisModel G ℓ Γ` whose base functor is isomorphic to the identity is 2-isomorphic to the
identity. -/
theorem galFrob_autRigid
    (hΓ : ∀ e : Γ ≃+ Γ, (∀ x : Γ, 0 ≤ (x : ℝ) ↔ 0 ≤ (e x : ℝ)) →
      ∃ l : ℝ, 0 < l ∧ ∀ x : Γ, (e x : ℝ) = l * x)
    (hrig : ∀ ψ : M ≃+ M, (∀ (g : G) (m : M), ψ (g • m) = g • ψ m) → ∀ l : ℝ, 0 < l →
      (∀ m, ℓ (ψ m) = l * ℓ m) → ψ = AddEquiv.refl M) :
    (galFrob G ℓ hℓ Γ).AutRigid := by
  intro h ⟨β⟩
  obtain ⟨l, hl0, hl⟩ := hΓ (h.phi topObj) (fun x => h.phi_pos topObj x)
  have hψ := hrig (autPsi h β hmem hopen) (autPsi_smul hmem hopen) l hl0
    (ell_autPsi hmem hopen hm0 hfix0 hl)
  have hl1 : l = 1 := by
    have e := ell_autPsi (h := h) (β := β) hmem hopen hm0 hfix0 hl m0
    rw [hψ, AddEquiv.refl_apply] at e
    have e' : (l - 1) * ℓ m0 = 0 := by linarith
    rcases mul_eq_zero.1 e' with h1 | h1
    · linarith
    · linarith
  have hphi : ∀ (A : OrbitObj G) (x : Γ), h.phi A x = x := fun A x => by
    rw [phi_eq_top]
    exact Subtype.ext ((hl x).trans (by rw [hl1, one_mul]))
  have hpsi : ∀ m, psiFun h β hmem hopen m = m := fun m => by
    rw [← autPsi_apply, hψ]; rfl
  refine rel_refl_of_id (h := h) (β := β) (fun {X Y} φ => ?_) (fun X x => ?_) hphi
  · rw [autF_map_div, hphi]; rfl
  · have e : psiX h β X x = x := by
      rw [psiX_eq_obj0]
      exact bval_injective ((bval_psiA hmem hopen X.base x).trans (hpsi _))
    calc Model.mapUnit (autF h) (autF_hpre h β) x
        = (bGal G ℓ hℓ Γ).pb (eps h β X).inv ((bGal G ℓ hℓ Γ).pb (eps h β X).hom
            (Model.mapUnit (autF h) (autF_hpre h β) x)) := by
          rw [← GrpOn.pb_comp', CategoryTheory.Iso.inv_hom_id, GrpOn.pb_id']
      _ = (bGal G ℓ hℓ Γ).pb (eps h β X).inv x := congrArg _ e

end Rigid

/-! ### `Γ = ℚ` -/

/-- **Order automorphisms of `ℚ ⊆ ℝ` are scalings by a positive real.** -/
theorem gammaQ_scaling (e : PAdicGalois.gammaQ ≃+ PAdicGalois.gammaQ)
    (he : ∀ x : PAdicGalois.gammaQ, 0 ≤ (x : ℝ) ↔ 0 ≤ (e x : ℝ)) :
    ∃ l : ℝ, 0 < l ∧ ∀ x : PAdicGalois.gammaQ, (e x : ℝ) = l * x := by
  have h1mem : (1 : ℝ) ∈ PAdicGalois.gammaQ := ⟨1, by simp⟩
  refine ⟨(e ⟨1, h1mem⟩ : ℝ), ?_, fun x => ?_⟩
  · have h0 : 0 ≤ (e ⟨1, h1mem⟩ : ℝ) := (he ⟨1, h1mem⟩).1 zero_le_one
    have hne : (e ⟨1, h1mem⟩ : ℝ) ≠ 0 := fun h => by
      have h2 : e ⟨1, h1mem⟩ = e 0 := by rw [map_zero]; exact Subtype.ext h
      have h3 := congrArg Subtype.val (e.injective h2)
      norm_num at h3
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  · obtain ⟨q, hq⟩ := x.2
    have hx : (x : ℝ) = (q : ℝ) := by rw [← hq]; simp
    have hden : (q.den : ℝ) ≠ 0 := by positivity
    have hqd : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have key : (q.den : ℤ) • x = q.num • (⟨1, h1mem⟩ : PAdicGalois.gammaQ) := Subtype.ext (by
      simp only [AddSubgroup.coe_zsmul, zsmul_eq_mul, Int.cast_natCast, mul_one]
      rw [hx, mul_comm]
      exact hqd)
    have key' : (q.den : ℝ) * (e x : ℝ) = q.num * (e ⟨1, h1mem⟩ : ℝ) := by
      have := congrArg (fun y : PAdicGalois.gammaQ => (y : ℝ)) (congrArg e key)
      simpa only [map_zsmul, AddSubgroup.coe_zsmul, zsmul_eq_mul, Int.cast_natCast] using this
    rw [hx]
    apply mul_left_cancel₀ hden
    rw [key', ← hqd]
    ring

end Galois

end PrimeStrip

end Multiradial

end Iut
