/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFLimit
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# [AbsTopIII] Thm 1.9 (d): the direct limit `lim→_V H¹(Π_V, Ẑ(1))` and `K^×_{Z_NF} ↪ lim→`

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178): "one
constructs the subgroups `k̄_NF^× ⊆ K^×_{Z_NF} ↪ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` — where `V` ranges over
the open subschemes obtained by removing finite collections of NF-points from `Z ×_{k_Z} k′`, for
`k′` a finite extension of `k_Z`; […] the "`↪`" arises from the Kummer map". The stages and their
transition maps are in `Thm19/NFTransition.lean`, directedness and injectivity stage by stage in
`Thm19/NFLimit.lean`. Here the colimit itself is built, as Mathlib's `DirectLimit` of the
directed system of stages:

* `StageIdx D`: the stages `V ⊆ U_K` (`K / k` finite, `V` the open of a coordinate `t′` of `U_K`
  on which `t` is regular), ordered by `K ⊆ K′` and "`t′` regular on the open of `t″`";
  directed (`exists_stage_ge_sup`) and nonempty (`U` itself);
* `H1Lim D = lim→_V H¹(Π_V, Ẑ(1))` along `resT`, and `UnitsLim D = lim→_V Γ(V, 𝒪^×)` along
  `unitsT`, both commutative groups;
* **`kummerLim : UnitsLim D →* H1Lim D`**, the Kummer map in the colimit (`resT_kummerMapZHat`),
  and **`kummerLim_injective`** (`k` a number field: Prop 1.6 (i) at every stage);
* `coeLim : UnitsLim D →* Ωˣ` (a unit of a stage is a nonzero function), injective;
* **`nfToLim N : K^×_{Z_NF} →* UnitsLim D`** (every NF-rational function is a unit on some
  stage, `exists_stage_units_fnf`) and **`kummerNF N := kummerLim ∘ nfToLim N`**, injective:
  the "`↪`" of Thm 1.9 (d) as a monomorphism of groups.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **A stage of the colimit of [AbsTopIII] Thm 1.9 (d)**: a finite extension `K / k` inside `Ω`
and a coordinate `t′` of the base change `U_K` on whose open `V` the coordinate `t` of `U` is
regular (`stage D K ht' htr'`). -/
structure StageIdx where
  /-- The finite extension `k′ = K` of `k`. -/
  K : IntermediateField k Ω
  [fin : FiniteDimensional k K]
  /-- The coordinate of the open `V ⊆ U_K`. -/
  t' : Ω
  ht' : t' ∈ (constExt K D).L
  htr' : Transcendental K t'
  htV : t ∈ chartRing K t'

namespace StageIdx

attribute [instance] StageIdx.fin

variable {D}

/-- The Galois model of the stage. -/
abbrev data (s : StageIdx D) : Pi1.Orbifold.GaloisData s.K s.t' := stage D s.K s.ht' s.htr'

instance isGalois (s : StageIdx D) : IsGalois (K₀ s.K s.t') Ω := isGalois_stage D s.K s.ht' s.htr'

/-- `s ≤ s'`: `K ⊆ K′` and `t′` is regular on the open of `t″`. -/
instance : LE (StageIdx D) := ⟨fun s s' => s.K ≤ s'.K ∧ s.t' ∈ chartRing s'.K s'.t'⟩

lemma le_def {s s' : StageIdx D} : s ≤ s' ↔ s.K ≤ s'.K ∧ s.t' ∈ chartRing s'.K s'.t' := Iff.rfl

lemma mem_chartRing_trans {K₁ K₂ : IntermediateField k Ω} (h : K₁ ≤ K₂) {x t₁ t₂ : Ω}
    (hx : x ∈ chartRing K₁ t₁) (h₁ : t₁ ∈ chartRing K₂ t₂) : x ∈ chartRing K₂ t₂ :=
  mem_chartRing_of_forall fun W hk hW =>
    mem_of_mem_chartRing W (fun c : K₁ => hk ⟨c, h c.2⟩) (mem_of_mem_chartRing W hk hW h₁) hx

instance : Preorder (StageIdx D) where
  le_refl s := ⟨le_rfl, self_mem_chartRing s.K s.t'⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, mem_chartRing_trans h₂.1 h₁.2 h₂.2⟩

variable (D) in
/-- `U` itself as a stage (`K = k`, `t′ = t`). -/
def base : StageIdx D where
  K := ⊥
  t' := t
  ht' := t_mem_L_constExt D ⊥
  htr' := transcendental_K D
  htV := self_mem_chartRing _ t

instance : Nonempty (StageIdx D) := ⟨base D⟩

/-- **The stages are directed** (`exists_stage_ge_sup`), for `U` without orbifold points. -/
instance [hH : Fact (D.H ≤ D.HL)] : IsDirectedOrder (StageIdx D) where
  directed s₁ s₂ := by
    obtain ⟨t₃, ht₃, htr₃, h₁, h₂⟩ := exists_stage_ge_sup D hH.out s₁.ht' s₁.htr' s₂.ht'
    refine ⟨⟨s₁.K ⊔ s₂.K, t₃, ht₃, htr₃, mem_chartRing_trans le_sup_left s₁.htV h₁⟩,
      ⟨le_sup_left, h₁⟩, ⟨le_sup_right, h₂⟩⟩

end StageIdx

open StageIdx

/-! ### The direct systems -/

/-- `H¹(Π_V, Ẑ(1))` at a stage. -/
abbrev H1S (s : StageIdx D) : Type u := ContH1 (Pi s.data) (ZHatOne (F s.data) Ω)

/-- `Γ(V, 𝒪^×)` at a stage. -/
abbrev US (s : StageIdx D) : Type u := units s.data

instance (s : StageIdx D) : CommGroup (H1S D s) := inferInstance

instance (s : StageIdx D) : CommGroup (US D s) := inferInstance

variable {D}

lemma F_le {s s' : StageIdx D} (h : s ≤ s') : ∀ x ∈ F s.data, x ∈ F s'.data :=
  fun _ hx => F_stage_mono D h.1 s'.ht' s'.htr' hx

lemma hW_le {s s' : StageIdx D} (h : s ≤ s') (W : ValuationSubring Ω)
    (hK : ∀ c : s'.K, algebraMap s'.K Ω c ∈ W) (hW : s'.t' ∈ W) :
    (∀ c : s.K, algebraMap s.K Ω c ∈ W) ∧ s.t' ∈ W :=
  hW_stage_mono h.1 h.2 W hK hW

/-- The transition map `H¹(Π_V, Ẑ(1)) → H¹(Π_{V′}, Ẑ(1))` for `V ≤ V′`. -/
def resS {s s' : StageIdx D} (h : s ≤ s') : H1S D s →* H1S D s' :=
  resT s.data s'.data (F_le h) (hW_le h) (stage_H_le D s.K s.ht' s.htr')

/-- The transition map `Γ(V, 𝒪^×) → Γ(V′, 𝒪^×)` for `V ≤ V′`. -/
def unitsS {s s' : StageIdx D} (h : s ≤ s') : US D s →* US D s' :=
  unitsT s.data s'.data (F_le h) (hW_le h)

lemma resS_self (s : StageIdx D) (x : H1S D s) : resS (le_refl s) x = x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [resS, resT, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply]
    have hσ : piT s.data s.data (F_le (le_refl s)) (hW_le (le_refl s))
        (stage_H_le D s.K s.ht' s.htr') σ = σ := by
      induction σ using QuotientGroup.induction_on with
      | H σ => exact congrArg (fun h : s.data.H => (h : Pi s.data)) (Subtype.ext rfl)
    rw [hσ]
    apply Subtype.ext
    funext i
    apply Mu.ext
    apply Units.ext
    rfl

lemma resS_resS {s₁ s₂ s₃ : StageIdx D} (h₁₂ : s₁ ≤ s₂) (h₂₃ : s₂ ≤ s₃) (x : H1S D s₁) :
    resS h₂₃ (resS h₁₂ x) = resS (h₁₂.trans h₂₃) x :=
  resT_resT x

lemma unitsS_self (s : StageIdx D) (x : US D s) : unitsS (le_refl s) x = x := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact coe_unitsT _ _ _ _ x

lemma unitsS_unitsS {s₁ s₂ s₃ : StageIdx D} (h₁₂ : s₁ ≤ s₂) (h₂₃ : s₂ ≤ s₃) (x : US D s₁) :
    unitsS h₂₃ (unitsS h₁₂ x) = unitsS (h₁₂.trans h₂₃) x :=
  unitsT_unitsT x

instance : DirectedSystem (H1S D) (fun _ _ h => resS (D := D) h) where
  map_self := fun _ x => resS_self _ x
  map_map := fun _ _ _ h₁ h₂ x => resS_resS h₁ h₂ x

instance : DirectedSystem (US D) (fun _ _ h => unitsS (D := D) h) where
  map_self := fun _ x => unitsS_self _ x
  map_map := fun _ _ _ h₁ h₂ x => unitsS_unitsS h₁ h₂ x

lemma resS_kummerMapZHat {s s' : StageIdx D} (h : s ≤ s') (u : US D s) :
    resS h (kummerMapZHat s.data u) = kummerMapZHat s'.data (unitsS h u) :=
  resT_kummerMapZHat s.data s'.data (F_le h) (hW_le h) (stage_H_le D s.K s.ht' s.htr') u

/-! ### The direct limits and the Kummer map -/

section General

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {F₁ F₂ : ι → Type*}
  {T₁ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} (f₁ : ∀ i j (h : i ≤ j), T₁ h)
  [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₁ h) (F₁ i) (F₁ j)] [DirectedSystem F₁ (f₁ · · ·)]
  {T₂ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} (f₂ : ∀ i j (h : i ≤ j), T₂ h)
  [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₂ h) (F₂ i) (F₂ j)] [DirectedSystem F₂ (f₂ · · ·)]

/-- A compatible family of injective maps induces an injective map of direct limits. -/
theorem directLimit_map_injective (ih : ∀ i, F₁ i → F₂ i)
    (compat : ∀ i j h x, f₂ i j h (ih i x) = ih j (f₁ i j h x))
    (hinj : ∀ i, Function.Injective (ih i)) :
    Function.Injective (DirectLimit.map f₁ f₂ ih compat) := by
  intro a b hab
  induction a, b using DirectLimit.induction₂ f₁ with
  | ih i x y =>
    rw [DirectLimit.map_def, DirectLimit.map_def] at hab
    obtain ⟨j, hij, hij', e⟩ := Quotient.exact hab
    have e' : ih j (f₁ i j hij x) = ih j (f₁ i j hij' y) := by
      rw [← compat, ← compat]
      exact e
    exact Quotient.sound ⟨j, hij, hij', hinj j e'⟩

end General

section Lim

variable (D) [Fact (D.H ≤ D.HL)]

/-- **`lim→_V H¹(Π_V, Ẑ(1))`** ([AbsTopIII] Thm 1.9 (d)), along the transition maps `resT`. -/
abbrev H1Lim : Type u := DirectLimit (H1S D) (fun _ _ h => resS (D := D) h)

/-- **`lim→_V Γ(V, 𝒪^×)`**, along `unitsT`. -/
abbrev UnitsLim : Type u := DirectLimit (US D) (fun _ _ h => unitsS (D := D) h)

variable {D} in
/-- The class of `x ∈ H¹(Π_V, Ẑ(1))` in the colimit. -/
abbrev H1Lim.mk (s : StageIdx D) (x : H1S D s) : H1Lim D := ⟦⟨s, x⟩⟧

variable {D} in
/-- The class of a unit of a stage in the colimit. -/
abbrev UnitsLim.mk (s : StageIdx D) (x : US D s) : UnitsLim D := ⟦⟨s, x⟩⟧

lemma H1Lim.one_eq (s : StageIdx D) : (1 : H1Lim D) = H1Lim.mk s 1 :=
  DirectLimit.one_def (G := H1S D) (f := fun _ _ h => resS (D := D) h) s

lemma H1Lim.mk_mul_mk (s : StageIdx D) (x y : H1S D s) :
    H1Lim.mk s x * H1Lim.mk s y = H1Lim.mk s (x * y) :=
  DirectLimit.mul_def (G := H1S D) (f := fun _ _ h => resS (D := D) h) s x y

lemma UnitsLim.one_eq (s : StageIdx D) : (1 : UnitsLim D) = UnitsLim.mk s 1 :=
  DirectLimit.one_def (G := US D) (f := fun _ _ h => unitsS (D := D) h) s

lemma UnitsLim.mk_mul_mk (s : StageIdx D) (x y : US D s) :
    UnitsLim.mk s x * UnitsLim.mk s y = UnitsLim.mk s (x * y) :=
  DirectLimit.mul_def (G := US D) (f := fun _ _ h => unitsS (D := D) h) s x y

lemma UnitsLim.induction₂ {C : UnitsLim D → UnitsLim D → Prop}
    (ih : ∀ s x y, C (UnitsLim.mk s x) (UnitsLim.mk s y)) (a b : UnitsLim D) : C a b :=
  DirectLimit.induction₂ (F := US D) (f := fun _ _ h => unitsS (D := D) h) ih a b

/-- The Kummer map on the colimit, as a function. -/
def kummerLimFun : UnitsLim D → H1Lim D :=
  DirectLimit.map (fun _ _ h => unitsS (D := D) h) (fun _ _ h => resS (D := D) h)
    (fun s => ⇑(kummerMapZHat s.data)) (fun _ _ h x => resS_kummerMapZHat h x)

lemma kummerLimFun_mk (s : StageIdx D) (u : US D s) :
    kummerLimFun D (UnitsLim.mk s u) = H1Lim.mk s (kummerMapZHat s.data u) := rfl

set_option maxHeartbeats 2000000 in
-- the multiplication of `H1Lim` from its `CommGroup` instance and from `DirectLimit.mul_def` are
-- unified through the `CommGroup` instance of `ContH1` (a quotient of cocycle groups)
/-- **The Kummer map in the colimit**, `[V, u] ↦ [V, κ_V(u)]`. -/
def kummerLim : UnitsLim D →* H1Lim D where
  toFun := kummerLimFun D
  map_one' := by
    rw [UnitsLim.one_eq D (base D), kummerLimFun_mk, map_one, ← H1Lim.one_eq]
  map_mul' := UnitsLim.induction₂ D fun s x y => by
    rw [UnitsLim.mk_mul_mk, kummerLimFun_mk, kummerLimFun_mk, kummerLimFun_mk,
      (kummerMapZHat s.data).map_mul]
    exact (H1Lim.mk_mul_mk D s _ _).symm

lemma kummerLim_mk (s : StageIdx D) (u : US D s) :
    kummerLim D (UnitsLim.mk s u) = H1Lim.mk s (kummerMapZHat s.data u) := rfl

/-- **[AbsTopIII] Thm 1.9 (d), the Kummer map into `lim→_V H¹(Π_V, Ẑ(1))` is injective**, `k` a
number field (Prop 1.6 (i) at every stage, `kummerMapZHat_stage_injective_numberField`). -/
theorem kummerLim_injective [NumberField k]
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Injective (kummerLim D) := by
  change Function.Injective (kummerLimFun D)
  exact directLimit_map_injective (fun _ _ h => unitsS (D := D) h)
    (fun _ _ h => resS (D := D) h) (fun s => ⇑(kummerMapZHat s.data))
    (fun _ _ h x => resS_kummerMapZHat h x) fun s =>
      kummerMapZHat_stage_injective_numberField (D := D) (K := s.K) (ht' := s.ht')
        (htr' := s.htr') (Fact.out : D.H ≤ D.HL) hkF

/-- A unit of a stage as a unit of `Ω`. -/
def coeS (s : StageIdx D) : US D s →* Ωˣ :=
  (Units.map (algebraMap (F s.data) Ω : F s.data →* Ω)).comp (units s.data).subtype

@[simp] lemma coe_coeS (s : StageIdx D) (u : US D s) :
    ((coeS D s u : Ωˣ) : Ω) = (((u : (F s.data)ˣ) : F s.data) : Ω) := rfl

lemma coeS_unitsS {s s' : StageIdx D} (h : s ≤ s') (u : US D s) :
    coeS D s' (unitsS h u) = coeS D s u :=
  Units.ext (by rw [coe_coeS, coe_coeS]; exact coe_unitsT s.data s'.data (F_le h) (hW_le h) u)

lemma coeS_injective (s : StageIdx D) : Function.Injective (coeS D s) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val h

/-- A unit of a stage as a nonzero function, on the colimit. -/
def coeLimFun : UnitsLim D → Ωˣ :=
  DirectLimit.lift (fun _ _ h => unitsS (D := D) h) (fun s => ⇑(coeS D s))
    (fun _ _ h x => (coeS_unitsS D h x).symm)

lemma coeLimFun_mk (s : StageIdx D) (u : US D s) : coeLimFun D (UnitsLim.mk s u) = coeS D s u :=
  rfl

/-- **A unit of a stage is a nonzero function**: `lim→_V Γ(V, 𝒪^×) → Ωˣ`. -/
def coeLim : UnitsLim D →* Ωˣ where
  toFun := coeLimFun D
  map_one' := by
    rw [UnitsLim.one_eq D (base D), coeLimFun_mk, map_one]
  map_mul' := UnitsLim.induction₂ D fun s x y => by
    rw [UnitsLim.mk_mul_mk, coeLimFun_mk, coeLimFun_mk, coeLimFun_mk, map_mul]

lemma coeLim_mk (s : StageIdx D) (u : US D s) : coeLim D (UnitsLim.mk s u) = coeS D s u :=
  rfl

lemma coeLim_injective : Function.Injective (coeLim D) :=
  DirectLimit.lift_injective (F := US D) (fun _ _ h => unitsS (D := D) h) (fun s => ⇑(coeS D s))
    (fun _ _ h x => (coeS_unitsS D h x).symm) fun s => coeS_injective D s

variable {D} [CharZero Ω] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

/-- An NF-rational function as a unit of `Ω`. -/
abbrev coeNF : (fnf N)ˣ →* Ωˣ := Units.map (algebraMap (fnf N) Ω : fnf N →* Ω)

include hkF in
/-- **Every NF-rational function is a unit on some stage** (`exists_stage_units_fnf`). -/
lemma exists_coeLim_eq (f : (fnf N)ˣ) : ∃ z : UnitsLim D, coeLim D z = coeNF N f := by
  obtain ⟨K, hK, t', ht', htr', htV, v, hv⟩ := exists_stage_units_fnf D N hkF f
  exact ⟨UnitsLim.mk ⟨K, t', ht', htr', htV⟩ v, Units.ext hv⟩

/-- **`K^×_{Z_NF} → lim→_V Γ(V, 𝒪^×)`**: every NF-rational function, as a unit of a stage. -/
def nfToLim : (fnf N)ˣ →* UnitsLim D where
  toFun f := (exists_coeLim_eq N hkF f).choose
  map_one' := coeLim_injective D (by rw [(exists_coeLim_eq N hkF 1).choose_spec, map_one,
    map_one])
  map_mul' f g := coeLim_injective D (by
    rw [(exists_coeLim_eq N hkF (f * g)).choose_spec, (coeLim D).map_mul,
      (exists_coeLim_eq N hkF f).choose_spec, (exists_coeLim_eq N hkF g).choose_spec, map_mul])

lemma coeLim_nfToLim (f : (fnf N)ˣ) : coeLim D (nfToLim N hkF f) = coeNF N f :=
  (exists_coeLim_eq N hkF f).choose_spec

lemma nfToLim_injective : Function.Injective (nfToLim N hkF) := by
  intro f g h
  have := congrArg (coeLim D) h
  rw [coeLim_nfToLim, coeLim_nfToLim] at this
  exact Units.ext (Subtype.ext (congrArg Units.val this))

/-- **[AbsTopIII] Thm 1.9 (d), `K^×_{Z_NF} ↪ lim→_V H¹(Π_V, Ẑ(1))`**: the Kummer classes of the
NF-rational functions in the colimit. -/
def kummerNF : (fnf N)ˣ →* H1Lim D := (kummerLim D).comp (nfToLim N hkF)

/-- **[AbsTopIII] Thm 1.9 (d), the "`↪`"**: over a number field, the Kummer map of the
NF-portion into `lim→_V H¹(Π_V, Ẑ(1))` is injective. -/
theorem kummerNF_injective [NumberField k] : Function.Injective (kummerNF N hkF) :=
  (kummerLim_injective D hkF).comp (nfToLim_injective N hkF)

end Lim

end Iut.Reconstruction.Thm19
