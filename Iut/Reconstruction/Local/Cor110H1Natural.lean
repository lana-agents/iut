/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Cor110Natural
import LocalClassFieldTheory.Brauer.ArtinTransfer

/-!
# Naturality of `H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab` ([AbsTopIII], Cor. 1.10 (b))

[AbsTopIII], Corollary 1.10 (i) (b) (`Topics in Absolute Anabelian Geometry III.txt`,
l.2401–2406):

> "(b) By applying the isomorphism of (a) [and the cup-product in group cohomology], one
> constructs the surjection `H¹(G_k, μ_Ẑ(G_k)) ∼→ G_k^ab ↠ G^unr ∼→ Ẑ` […]."

`Cor110H1.lean` constructs `h1ZHatGAbEquiv : H¹(G_k, μ_Ẑ(G_k)) ≃* G_k^ab` by Kummer theory and
local class field theory. Here we prove that this isomorphism is **group-theoretic**, i.e. it is
the isomorphism obtained, as in (b), from the invariant of (a) and the cup product:

* `chiAb χ : G^ab → ℤ/n`, the character of `G^ab` induced by a continuous character `χ` of `G`;
  characters separate the points of `G^ab` for compact totally disconnected `G`
  (`eq_of_forall_chiAb`);
* **`chiAb_h1ZHatGAbEquiv`**: for a cocycle `c` with values in `μ_Ẑ(G_k)`,
  `χ(h1ZHatGAbEquiv [c]) = inv(χ ∪ (c mod n))`, where `∪` is the group-theoretic cup product
  `cupG` into `H²(G_k, μ_n(G_k))` and `inv = invG` its invariant. The proof compares both sides on
  the profinite completion `(k^×)^∧ ≅ H¹(G_k, Ẑ(1))`: they are continuous in the completion and
  agree on `k^×` by `⟨χ, κ(a)⟩ = χ(artin a)` (LCFT `pairingH1_kummer`), hence everywhere;
* **`h1ZHatGAbEquiv_H1ZHatGEquivOf`**: for every isomorphism of topological groups
  `ψ : G_k ≃ₜ* G_{k'}` (no relation between `k` and `k'` assumed),
  `h1ZHatGAbEquiv k' (ψ_* x) = ψ^ab (h1ZHatGAbEquiv k x)`: the right-hand side of the formula
  above is transported by `ψ` (`h2MuGEquivOf_cupG`, and the naturality of the invariant
  `invG_h2MuGEquivOf`, [AbsAnab] Proposition 1.2.1 (vii)).
-/

namespace Iut.Reconstruction

open PadicField KummerTheory Brauer ContH2 groupCohomology CategoryTheory ProfiniteGrp

set_option linter.unusedSectionVars false

noncomputable section

universe u

/-! ### Characters of `G^ab` -/

section Char

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The character `G^ab → ℤ/n` induced by a continuous character `χ : G → ℤ/n`. -/
def chiAb {n : ℕ} (χ : G →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ) :
    TopologicalAbelianization G →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ χ (Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker χ) (by
      rw [MonoidHom.coe_ker]
      exact hχ.isClosed_fiber 1))

@[simp] lemma chiAb_mk {n : ℕ} (χ : G →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ)
    (g : G) : chiAb χ hχ (QuotientGroup.mk g : TopologicalAbelianization G) = χ g := rfl

lemma isLocallyConstant_chiAb {n : ℕ} (χ : G →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) : IsLocallyConstant (chiAb χ hχ) := by
  letI : TopologicalSpace (Multiplicative (ZMod n)) := ⊥
  haveI : DiscreteTopology (Multiplicative (ZMod n)) := ⟨rfl⟩
  exact (IsLocallyConstant.iff_continuous _).2
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      ((IsLocallyConstant.iff_continuous _).1 hχ))

lemma chiAb_abEquiv {G' : Type*} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {n : ℕ} (ψ : G ≃ₜ* G') (χ' : G' →* Multiplicative (ZMod n)) (hχ' : IsLocallyConstant χ')
    (x : TopologicalAbelianization G) :
    chiAb χ' hχ' (abEquiv ψ x) =
      chiAb (χ'.comp ψ.toMulEquiv.toMonoidHom) (hχ'.comp_continuous ψ.continuous) x := by
  induction x using QuotientGroup.induction_on with | H g => rfl

/-- **Characters separate the points of `G^ab`** for a compact totally disconnected `G`. -/
theorem eq_of_forall_chiAb [CompactSpace G] [TotallyDisconnectedSpace G]
    {u v : TopologicalAbelianization G}
    (h : ∀ (n : ℕ+) (χ : G →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ),
      chiAb χ hχ u = chiAb χ hχ v) : u = v := by
  by_contra huv
  haveI : TotallyDisconnectedSpace (TopologicalAbelianization G) :=
    QuotientGroup.totallyDisconnectedSpace_of_isClosed _ (Subgroup.isClosed_topologicalClosure _)
  have hw : u / v ≠ 1 := div_ne_one.mpr huv
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := TopologicalAbelianization G) (isOpen_compl_singleton (x := u / v))
    (fun h1 => hw (Set.mem_singleton_iff.mp h1).symm)
  have hnot : u / v ∉ (H : Subgroup (TopologicalAbelianization G)) := fun hm => hH hm rfl
  set Q := TopologicalAbelianization G ⧸ (H : Subgroup (TopologicalAbelianization G))
  haveI : DiscreteTopology Q := QuotientGroup.discreteTopology H.isOpen'
  haveI : Finite Q := finite_of_compact_of_discrete
  let q : TopologicalAbelianization G →* Q := QuotientGroup.mk' _
  have hq : Continuous q := QuotientGroup.continuous_mk
  let r : G →* TopologicalAbelianization G := QuotientGroup.mk' _
  have hr : Continuous r := QuotientGroup.continuous_mk
  have key : q u = q v := by
    refine PadicField.eq_of_forall_char fun m _ φ => ?_
    let χ : G →* Multiplicative (ZMod m) := φ.comp (q.comp r)
    have hχ : IsLocallyConstant χ :=
      (IsLocallyConstant.of_discrete φ).comp_continuous (hq.comp hr)
    have h1 := h ⟨m, Nat.pos_of_ne_zero (NeZero.ne m)⟩ χ hχ
    have e : ∀ w, chiAb χ hχ w = φ (q w) := fun w => by
      induction w using QuotientGroup.induction_on with | H g => rfl
    exact (e u).symm.trans (h1.trans (e v))
  exact hnot ((QuotientGroup.eq_iff_div_mem).mp key)

end Char

/-! ### Reduction of `μ_Ẑ(G)`-valued cocycles modulo `n` -/

section Red

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `μ_Ẑ(G) → μ_n(G)`. -/
def muZHatProj (n : ℕ+) : MuZHatG G →* muN G n where
  toFun x := x.val n
  map_one' := rfl
  map_mul' _ _ := rfl

lemma muZHatProj_apply (n : ℕ+) (x : MuZHatG G) : muZHatProj n x = x.val n := rfl

lemma continuous_muZHatProj (n : ℕ+) : Continuous (muZHatProj (G := G) n) := by
  have : (muZHatProj (G := G) n : MuZHatG G → muN G n) = fun x => x.val n := rfl
  rw [this]
  exact MuZHatG.continuous_val n

/-- The reduction `c mod n` of a cocycle with values in `μ_Ẑ(G)`. -/
def redCoc (n : ℕ+) (c : ContH1.cocycles G (MuZHatG G)) : ContH1.cocycles G (muN G n) :=
  ContH1.mkCocycle (fun g => (c g).val n)
    ((MuZHatG.continuous_val n).comp (ContH1.continuous c)) fun g h => by
      change (c (g * h)).val n = (g • c h).val n * (c g).val n
      rw [ContH1.isMulCocycle₁ c g h]
      rfl

@[simp] lemma redCoc_apply (n : ℕ+) (c : ContH1.cocycles G (MuZHatG G)) (g : G) :
    redCoc n c g = (c g).val n := rfl

end Red

/-! ### `G = G_k`: `χ(h1ZHatGAbEquiv [c]) = inv(χ ∪ (c mod n))` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p k) in
/-- The Kummer index `n` of `k`. -/
def kIdx (n : ℕ+) : KummerIndex k := ⟨n, natCast_ne_zero_padic p n⟩

/-- **`χ(h1AbEquiv y) = ⟨χ, y mod n⟩`**: the Kummer–Artin isomorphism `H¹(G_k, Ẑ(1)) ≅ G_k^ab`
is computed by the local duality pairing. Both sides are continuous on the profinite completion
`(k^×)^∧ ≅ H¹(G_k, Ẑ(1))` and agree on `k^×` (`pairingH1_kummer`). -/
theorem chiAb_h1AbEquiv (n : ℕ+) (χ : LocChar k Ω n) (y : ContH1 (Ω ≃ₐ[k] Ω) (ZHatOne k Ω)) :
    chiAb χ.1 χ.2 (h1AbEquiv p k Ω y) =
      Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ) χ (h1Proj k Ω (kIdx p k n) y)) := by
  haveI := charZero_padic p k
  haveI := finiteKummerQuotients_padic p k
  letI : TopologicalSpace (Multiplicative (ZMod n)) := ⊥
  haveI : DiscreteTopology (Multiplicative (ZMod n)) := ⟨rfl⟩
  set e := kummerZHatEquivProfiniteCompletion k Ω
  obtain ⟨c, rfl⟩ := e.symm.surjective y
  have hproj : h1Proj k Ω (kIdx p k n) (e.symm c) =
      kummerEquiv (kIdx p k n).n k Ω (c.1 (powSubgroup (kIdx p k n))) :=
    congrArg (fun z : H1Limit k Ω => z.1 (kIdx p k n))
      ((h1ZHatOneEquiv k Ω).apply_symm_apply (kummerLimitEquiv k Ω
        ((kummerCompletionEquivProfiniteCompletion k).symm c)))
  have hab : h1AbEquiv p k Ω (e.symm c) =
      (galAbEquiv p k Ω).symm (artinCompletionEquiv p k Ω c) := by
    change (galAbEquiv p k Ω).symm (artinCompletionEquiv p k Ω (e (e.symm c))) = _
    rw [MulEquiv.apply_symm_apply]
  let f1 : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of kˣ) →
      Multiplicative (ZMod n) := fun c =>
    chiAb χ.1 χ.2 ((galAbEquiv p k Ω).symm (artinCompletionEquiv p k Ω c))
  let f2 : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of kˣ) →
      Multiplicative (ZMod n) := fun c =>
    Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ) χ
      (kummerEquiv (kIdx p k n).n k Ω (c.1 (powSubgroup (kIdx p k n)))))
  have hf1 : Continuous f1 := ((isLocallyConstant_chiAb χ.1 χ.2).continuous).comp
    ((galAbEquiv p k Ω).symm.continuous.comp (artinCompletionEquiv p k Ω).continuous)
  have hf2 : Continuous f2 := by
    have hc : Continuous fun c : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of kˣ) =>
        c.1 (powSubgroup (kIdx p k n)) :=
      (continuous_apply (powSubgroup (kIdx p k n))).comp continuous_subtype_val
    haveI : DiscreteTopology ((ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of kˣ)).obj
        (powSubgroup (kIdx p k n))) := ⟨rfl⟩
    exact Continuous.comp (g := fun x : (ProfiniteGrp.ProfiniteCompletion.diagram
      (GrpCat.of kˣ)).obj (powSubgroup (kIdx p k n)) =>
        Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ) χ (kummerEquiv (kIdx p k n).n k Ω x)))
      continuous_of_discreteTopology hc
  have heq : f1 = f2 := (ProfiniteCompletion.denseRange (GrpCat.of kˣ)).equalizer hf1 hf2
    (funext fun a => by
      obtain ⟨g, hg⟩ := exists_lift_artin (p := p) (K := k) (Ω := Ω) a
      have h1 : (galAbEquiv p k Ω).symm (artin p k Ω a) = QuotientGroup.mk g := by
        rw [ContinuousMulEquiv.symm_apply_eq, galAbEquiv_mk, hg]
      haveI := hasKummerRoots (K := k) (Ω := Ω) (n : ℕ)
      simp only [Function.comp_apply]
      change chiAb χ.1 χ.2 ((galAbEquiv p k Ω).symm (artinCompletionEquiv p k Ω
        (ProfiniteCompletion.etaFn _ a))) = Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ) χ
          (kummerEquiv (kIdx p k n).n k Ω (QuotientGroup.mk a)))
      rw [artinCompletionEquiv_eta, h1, chiAb_mk, kummerEquiv_mk]
      change _ = Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ) χ (kummer (n : ℕ) k Ω a))
      rw [pairingH1_kummer, artinChar_eq (n : ℕ) χ a g hg, ofAdd_toAdd])
  rw [hab, hproj]
  exact congrFun heq c

/-- The invariant of `χ ∪ (c mod n)` is the duality pairing of `χ` with the reduction of the
field-theoretic class of `c`. -/
theorem invG_cupG_redCoc (n : ℕ+) (χ : LocChar k Ω n)
    (c : ContH1.cocycles (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω))) :
    invG p k Ω n (cupG χ.1 χ.2 (redCoc n c)) = Multiplicative.ofAdd (pairingH1 (p := p) (n : ℕ)
      χ (h1Proj k Ω (kIdx p k n) (h1MuZHatEquiv p k Ω (ContH1.mk c)))) := by
  rw [pairingH1, ofAdd_toAdd]
  change h2MuEquiv p k Ω n.pos (h2MuGEquiv p k Ω n (cupG χ.1 χ.2 (redCoc n c))) = _
  congr 1
  simp only [h1MuZHatEquiv, h1Congr, h1Proj, MulEquiv.coe_mk, Equiv.coe_fn_mk, ContH1.map_mk]
  change ContH2.mk _ = ContH2.mk _
  congr 1
  refine cocycles_ext fun g h => ?_
  change muNEquiv p k Ω n ((g • (c h).val n) ^ chiExpG χ.1 g) = _
  rw [map_pow, muNEquiv_smul]
  rfl

/-- **[AbsTopIII], Corollary 1.10 (b), group-theoretically**: for a continuous character
`χ : G_k → ℤ/n` and a cocycle `c` with values in `μ_Ẑ(G_k)`,
`χ(h1ZHatGAbEquiv [c]) = inv(χ ∪ (c mod n))` (group-theoretic cup product `cupG` and invariant
`invG`). -/
theorem chiAb_h1ZHatGAbEquiv (n : ℕ+) (χ : LocChar k Ω n)
    (c : ContH1.cocycles (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω))) :
    chiAb χ.1 χ.2 (h1ZHatGAbEquiv p k Ω (ContH1.mk c)) =
      invG p k Ω n (cupG χ.1 χ.2 (redCoc n c)) := by
  rw [invG_cupG_redCoc]
  exact chiAb_h1AbEquiv n χ _

end Galois

/-! ### Naturality -/

section Natural

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
variable {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] k Ω]
  [IsAlgClosed Ω] [IsGalois k Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]
variable {p' : ℕ} [hp' : Fact p'.Prime]
variable {k' : Type u} [Field k'] [Algebra ℚ_[p'] k'] [FiniteDimensional ℚ_[p'] k']
variable {Ω' : Type u} [Field Ω'] [Algebra k' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] k' Ω']
  [IsAlgClosed Ω'] [IsGalois k' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- **[AbsTopIII], Corollary 1.10 (b): `H¹(G_k, μ_Ẑ(G_k)) ≅ G_k^ab` is group-theoretic.** For
every isomorphism of topological groups `ψ : G_k ≃ₜ* G_{k'}` (no relation between `k` and `k'`
assumed), `h1ZHatGAbEquiv k' (ψ_* x) = ψ^ab (h1ZHatGAbEquiv k x)`. -/
theorem h1ZHatGAbEquiv_H1ZHatGEquivOf (ψ : (Ω ≃ₐ[k] Ω) ≃ₜ* (Ω' ≃ₐ[k'] Ω'))
    (x : ContH1 (Ω ≃ₐ[k] Ω) (MuZHatG (Ω ≃ₐ[k] Ω))) :
    h1ZHatGAbEquiv p' k' Ω' (H1ZHatGEquivOf ψ x) = abEquiv ψ (h1ZHatGAbEquiv p k Ω x) := by
  induction x using ContH1.induction_on with | h c => ?_
  refine eq_of_forall_chiAb fun n χ' hχ' => ?_
  rw [chiAb_abEquiv]
  set χ : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod n) := χ'.comp ψ.toMulEquiv.toMonoidHom
  have hχ : IsLocallyConstant χ := hχ'.comp_continuous ψ.continuous
  change chiAb χ' hχ' (h1ZHatGAbEquiv p' k' Ω' (ContH1.map _ _ _ _ _ (ContH1.mk c))) = _
  rw [ContH1.map_mk]
  rw [chiAb_h1ZHatGAbEquiv (p := p') (k := k') (Ω := Ω') n ⟨χ', hχ'⟩,
    chiAb_h1ZHatGAbEquiv (p := p) (k := k) (Ω := Ω) n ⟨χ, hχ⟩ c]
  have hcup := h2MuGEquivOf_cupG ψ χ hχ χ' hχ' (fun _ => rfl) (redCoc n c) (redCoc n
    (ContH1.cocyclesMap ψ.symm.toMulEquiv.toMonoidHom ψ.symm.continuous
      (muZHatGEquivOf ψ).toMonoidHom (continuous_muZHatGEquivOf ψ) (fun g m => by
        change muZHatGEquivOf ψ (ψ.symm g • m) = g • muZHatGEquivOf ψ m
        rw [muZHatGEquivOf_smul, ContinuousMulEquiv.apply_symm_apply]) c)) (fun g => by
      change ((muZHatGEquivOf ψ) (c (ψ.symm (ψ g)))).val n = _
      rw [ContinuousMulEquiv.symm_apply_apply]
      rfl)
  rw [← hcup, invG_h2MuGEquivOf (p := p) (k := k) (Ω := Ω) (p' := p') (k' := k') (Ω' := Ω')]

end Natural

end

end Iut.Reconstruction
