/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.KummerClassFrob
import Iut.Frobenioid.GaloisRecon

/-!
# Frobenioid-theoretic and Galois-theoretic Kummer classes ([FrdII], Definition 2.2, Remark 2.2.1)

For the `p`-adic Frobenioid `C^⊢(E)` over `B(G_E)⁰` and an object `X` over `G_E/N` (`N` open
normal), the automorphisms `galAut σ⁻¹` (base `gN ↦ gσ⁻¹N`) give a continuous homomorphism
`galHom : G_E → Aut_C(X)` (`G_E/N ≅ G_X ⊆ Aut_D(X_D)`, [FrdII], Definition 2.2(i)), and the
rational function of a unit gives `μ_n(O^×(X)) → μ_n(K̄)` (`uMu`), compatibly with the actions
(`uMu_smul`). Pulling back along these maps:

* **`kummerClass_eq_galois`**: the Frobenioid-theoretic Kummer class of `g ∈ O^×(X)` (on the image
  `H = galHom(G_E)`) is the Galois-theoretic Kummer class of its rational function `γ`,
  `[σ ↦ σγ/γ] ∈ H¹(G_E, μ_n(K̄))` (`KummerTheory.kummerCocycle`);
* **`kummerClass_eq_kummer`**: if `γ^n = a ∈ E^×`, it is `KummerTheory.kummer n E K̄ a`, the Kummer
  class used by local class field theory (`PadicField.pairingH1_kummer`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime] {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝐏E" => Model.toElem (constPhi (OrbitObj (GK p E)) gammaZ)
  (bGal (GK p E) (ord p) (ord_smul p E) gammaZ) (divGal (GK p E) (ord p) (ord_smul p E) gammaZ)

variable (N : OpenNormalSubgroup (GK p E)) (a : gammaZ)

/-- The object `X = (G_E/N, a)`. -/
noncomputable abbrev XN : Frob p E := ⟨OrbitObj.ofONS N, a⟩

local notation "W" => WithDisc (Aut (XN N a))

lemma galAut_hom_eq_id {x : GK p E} (hx : x ∈ N) :
    (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E) N a x).hom = 𝟙 (XN N a) := by
  refine Model.hom_ext rfl ?_ ?_ ?_
  · exact (OrbitObj.rmul_eq_id_iff N x).mpr hx
  · rfl
  · rfl

/-- **`σ ↦ galAut σ⁻¹`**, the homomorphism `G_E → Aut_C(X)` through `G_E/N`. -/
noncomputable def galHom : GK p E →* W where
  toFun σ := GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹
  map_one' := Iso.ext (by rw [inv_one]; exact galAut_hom_eq_id N a N.toSubgroup.one_mem)
  map_mul' σ τ := by
    change GaloisModel.galAut N a (σ * τ)⁻¹ =
      (GaloisModel.galAut N a τ⁻¹).trans (GaloisModel.galAut N a σ⁻¹)
    refine Iso.ext (Model.hom_ext rfl ?_ ?_ ?_)
    · change OrbitObj.rmul N (σ * τ)⁻¹ = OrbitObj.rmul N τ⁻¹ ≫ OrbitObj.rmul N σ⁻¹
      rw [OrbitObj.rmul_mul, mul_inv_rev]
    · simp [GaloisModel.galAut]
    · simp [GaloisModel.galAut]

lemma galHom_hom (σ : GK p E) :
    (show Aut (XN N a) from galHom N a σ).hom =
      (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹).hom := rfl

lemma continuous_galHom : Continuous (galHom N a) :=
  continuous_of_mul_right_invariant N.toSubgroup N.isOpen _ fun σ ν hν => by
    rw [map_mul]
    have : galHom N a ν = 1 :=
      Iso.ext (galAut_hom_eq_id N a (N.toSubgroup.inv_mem hν))
    rw [this, mul_one]

/-- The image `H = galHom(G_E) ⊆ Aut_C(X)`. -/
noncomputable abbrev galRange : Subgroup W := (galHom N a).range

/-- `G_E → H`. -/
noncomputable def galSub : GK p E →* galRange N a := (galHom N a).rangeRestrict

lemma continuous_galSub : Continuous (galSub N a) :=
  Continuous.subtype_mk (continuous_galHom N a) _

/-- The rational function of a unit, as an element of `K̄^×`. -/
noncomputable def ratFun (u : Model.ouAut (XN N a)) : (PadicAlgCl p)ˣ :=
  ((show Aut (XN N a) from (u : W)).hom.u.1).toMul

lemma ratFun_mul (u v : Model.ouAut (XN N a)) :
    ratFun N a (u * v) = ratFun N a u * ratFun N a v := by
  have h := Model.ounits_comp_u v.2 u.2
  unfold ratFun
  change Additive.toMul (((show Aut (XN N a) from (v : W)).hom ≫
    (show Aut (XN N a) from (u : W)).hom).u.1) = _
  rw [h]
  change Additive.toMul (_ + _) = _
  rw [toMul_add, mul_comm]

lemma ratFun_one : ratFun N a 1 = 1 := rfl

/-- `μ_n(O^×(X)) → μ_n(K̄)`, `u ↦ γ_u`. -/
noncomputable def uMu (n : ℕ) : KummerClass.mu (Model.ouAut (XN N a)) n →*
    KummerTheory.Mu n (PadicAlgCl p) where
  toFun u := KummerTheory.Mu.mk (ratFun N a u) (by
    have hpow : ∀ m : ℕ, ratFun N a ((u : Model.ouAut (XN N a)) ^ m) =
        ratFun N a (u : Model.ouAut (XN N a)) ^ m := fun m => by
      induction m with
      | zero => simp [ratFun_one]
      | succ m ih => rw [pow_succ, ratFun_mul, ih, pow_succ]
    rw [← hpow, KummerClass.mem_mu.mp u.2, ratFun_one])
  map_one' := KummerTheory.Mu.ext rfl
  map_mul' u v := KummerTheory.Mu.ext (ratFun_mul N a u v)

/-- `galAut σ⁻¹` acts on rational functions of units by `σ`. -/
lemma ratFun_conj (σ : GK p E) (u : Model.ouAut (XN N a)) :
    ((ratFun N a (KummerClass.conjU (Model.ouAut (XN N a)) (galHom N a σ) u) :
      (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ ((ratFun N a u : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
  have h := GaloisModel.pb_galAut_inv (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹
    ((show Aut (XN N a) from (u : W)).hom.u)
  rw [inv_inv] at h
  unfold ratFun
  rw [KummerClass.coe_conjU, Model.conj_hom, Model.conj_u _ u.2]
  change (((((bGal (GK p E) (ord p) (ord_smul p E) gammaZ).pb
    (GaloisModel.galAut (ℓ := ord p) (hℓ := ord_smul p E) N a σ⁻¹).inv.base
      (show Aut (XN N a) from (u : W)).hom.u).1).toMul : (PadicAlgCl p)ˣ) : PadicAlgCl p) = _
  rw [h]
  exact smul_toMul p E σ _

/-- Compatibility of `uMu` with the actions: `galAut σ⁻¹` acts on rational functions by `σ`. -/
lemma uMu_smul (n : ℕ) (σ : GK p E) (m : KummerClass.mu (Model.ouAut (XN N a)) n) :
    uMu N a n (galSub N a σ • m) = σ • uMu N a n m := by
  apply KummerTheory.Mu.ext
  rw [KummerTheory.Mu.val_smul]
  apply Units.ext
  exact ratFun_conj N a σ m

/-- `ratFun` as a homomorphism. -/
noncomputable def ratFunHom : Model.ouAut (XN N a) →* (PadicAlgCl p)ˣ where
  toFun := ratFun N a
  map_one' := ratFun_one N a
  map_mul' := ratFun_mul N a

lemma ratFun_kfun (n : ℕ) (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ galRange N a, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (σ : GK p E) :
    ratFun N a (KummerClass.kfun (Model.ouAut (XN N a)) (galRange N a) n g hg (galSub N a σ)) =
      σ • ratFun N a g / ratFun N a g := by
  have e : (KummerClass.kfun (Model.ouAut (XN N a)) (galRange N a) n g hg (galSub N a σ) :
      Model.ouAut (XN N a)) = KummerClass.conjU (Model.ouAut (XN N a)) (galHom N a σ) g / g :=
    rfl
  apply Units.ext
  rw [e]
  change ((ratFunHom N a (KummerClass.conjU (Model.ouAut (XN N a)) (galHom N a σ) g / g) :
    (PadicAlgCl p)ˣ) : PadicAlgCl p) = _
  rw [map_div, Units.val_div_eq_div_val, Units.val_div_eq_div_val]
  congr 1
  exact ratFun_conj N a σ g

/-- **The Frobenioid-theoretic Kummer class is the Galois-theoretic one**: pulled back along
`G_E → Aut_C(X)` and `μ_n(O^×(X)) → μ_n(K̄)`, the Kummer class of `g ∈ O^×(X)` is the class of
`σ ↦ σγ/γ`, `γ` the rational function of `g`. -/
theorem kummerClass_eq_galois (n : ℕ) (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ galRange N a, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (hγ : ∀ σ : GK p E, σ • ratFun N a g ^ n = ratFun N a g ^ n) :
    ContH1.map (galSub N a) (continuous_galSub N a) (uMu N a n) continuous_of_discreteTopology
      (uMu_smul N a n) (Model.frobKummerClass (XN N a) (galRange N a) n g hg) =
    ContH1.mk (KummerTheory.kummerCocycle (ratFun N a g) hγ) :=
  KummerClass.map_kummerClass_eq_mk (g := g) (hg := hg)
    (c := KummerTheory.kummerCocycle (ratFun N a g) hγ)
    (hc := fun σ => KummerTheory.Mu.ext (ratFun_kfun N a n g hg σ)) ..

/-- **The Frobenioid-theoretic Kummer class is LCFT's Kummer class**: if the rational function
`γ` of `g` satisfies `γ^n = x ∈ E^×`, the pulled-back Kummer class of `g` is
`KummerTheory.kummer n E K̄ x` (the class paired with characters by `PadicField.pairingH1`). -/
theorem kummerClass_eq_kummer (n : ℕ) [NeZero (n : E)] (g : Model.ouAut (XN N a))
    (hg : ∀ h ∈ galRange N a, KummerClass.conjU (Model.ouAut (XN N a)) h (g ^ n) = g ^ n)
    (x : Eˣ)
    (hx : ratFun N a g ^ n = Units.map (algebraMap E (PadicAlgCl p) : E →* PadicAlgCl p) x) :
    ContH1.map (galSub N a) (continuous_galSub N a) (uMu N a n) continuous_of_discreteTopology
      (uMu_smul N a n) (Model.frobKummerClass (XN N a) (galRange N a) n g hg) =
    KummerTheory.kummer n E (PadicAlgCl p) x :=
  (kummerClass_eq_galois N a n g hg _).trans (KummerTheory.kummer_eq x _ hx).symm

end PAdicGalois

end Frobenioid

end Iut
