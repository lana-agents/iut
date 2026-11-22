/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.CuspInertiaProcyclic

/-!
# Route B, step 7: the vertex group of `Δ^Σ` is `Π^Σ_{0,3}` (abstract level interface)

MR13 plan, run 18 (2), items D2/D3 (lead decision (i) after run 18: against an abstract interface).
`Δ` is a profinite pro-`Σ` group (later `Δ^Σ`, the maximal pro-`Σ` quotient of the geometric
fundamental group of the Tate curve `E ∖ {O}`, with `Δ ≃ₜ* Π^Σ_{1,1}` from B1). The geometric
input enters through subgroups of `Δ` and one group-theoretic statement per finite level:

* **D2** (generic, `sup_eq_of_transitive`): for a family of open subgroups `S N ⊇ N` of `Δ`
  (`N` open normal; `S N` = the stabiliser of a component `Y_N` over the line `ℓ` of the special
  fibre of the Galois cover `C_N` with group `Δ/N`), decreasing in `N` and **transitive**
  (`S N' ≤ S N ⊔ N'` for `N ≤ N'`: `N'/N` acts transitively on the components of `C_N` over
  `Y_{N'}`), the intersection `D = ⋂ S N` (the vertex group `D_v`, stabiliser of the compatible
  system `(Y_N)`) satisfies `D ⊔ N = S N`, i.e. `D_v/(D_v ∩ N) ≅ S N / N = Γ_v(C_N)`;
  `surjective_restrict`: a homomorphism `S N → Γ_v(C_N)` stays onto on `D`.
* **Procyclic generators** (`exists_topGenerator`): a closed subgroup `I` with cyclic images in
  all finite quotients (the node inertia: the special stabilisers are cyclic, B4′ + C2) is the
  closure of `⟨γ⟩` for some `γ ∈ I`.
* **D3** (`exists_pair`, `exists_vertex_iso`): let `I ≤ D` be closed (the stabiliser of the
  branch-0 point over the node, procyclic) and `τ ∈ Δ` with `τ I τ⁻¹ ≤ D` (the branch-1 point;
  `τ` the loop element), `D ∪ {τ}` generating `Δ`. If at every level `N` there are
  `d₀, d₁ ∈ D`, `y₀, y₁ ∈ I` with `D ≤ N ⊔ ⟨d₀ y₀ d₀⁻¹, (d₁ τ y₁ τ⁻¹ d₁⁻¹)⁻¹⟩` (B4′ at level `N`:
  two cusp generators conjugate into the two branch stabilisers generate `Γ_v(C_N)`), then
  (compactness, `RouteB.exists_mem_iInter_of_saturated`-type choice of `d₀, d₁`) there is a
  continuous `β : Π^Σ_{0,3} → Δ` with `β(c₀) = d₀ γ d₀⁻¹`, `β(c₁)⁻¹ = d₁ τ γ τ⁻¹ d₁⁻¹`, image
  `D`, the HNN relation for `τ' = d₁ τ d₀⁻¹`, and (with `Δ ≃ₜ* Π^Σ_{1,1}`, Hopficity)
  `hnnLift β τ'` bijective and `β` a closed embedding: **`D_v ≅ Π^Σ_{0,3}`**, with `c₀`
  generating a conjugate of the branch inertia `I`.
* **`exists_vertex_iso_of_tower`**: the same for `D = ⋂ S N`, `I = ⋂ T N` given as towers of
  open stabilisers (closedness derived);
* **`eq_map_cuspInertia_of_cyclic`** (C2 at the vertex): for the closed embedding `β`, a closed
  subgroup of `β(Π^Σ_{0,3})` containing `β(cⱼ)` with cyclic finite images is `β` of the cusp
  inertia `cuspInertiaSigma P j (ℤ^Σ)` (tfg `RouteB.eq_range_cuspInertiaSigma_of_cyclic`);
* `le_sup_closure_of_quot`, `isCyclic_map_of_ker_le`: transport of the level statements from a
  finite quotient `ρ : D → Γ_v(C_N)` (`ker ρ ⊆ N`) to `Δ`.

The level statement is supplied by B4′ (`P1ThreeCuspStab.exists_cusp_stabilisers_cyclic`,
see `RouteBLevel.lean`) once the dictionary D1 (vertex datum of a Galois Tate cover) exists.
-/

open Pi1 Pi1.Profinite Pi1.SurfaceGroup Pi1.SurfaceGen Pi1.Profinite.ProSigmaCompletion
  TemperedFundamentalGroups TemperedFundamentalGroups.RouteB TemperedFundamentalGroups.OneOneHNN

namespace Iut.Reconstruction.RouteBVertex

/-! ### Generic profinite lemmas -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The whole group as an open normal subgroup. -/
def topONS : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ ↦ trivial⟩ }

/-- A union of cosets of an open normal subgroup is closed. -/
lemma isClosed_preimage_mk (N : OpenNormalSubgroup G) (T : Set (G ⧸ (N : Subgroup G))) :
    IsClosed (QuotientGroup.mk' (N : Subgroup G) ⁻¹' T) := by
  haveI : DiscreteTopology (G ⧸ (N : Subgroup G)) :=
    QuotientGroup.discreteTopology N.toOpenSubgroup.isOpen
  exact (isClosed_discrete T).preimage continuous_quot_mk

omit [IsTopologicalGroup G] in
/-- `x ∈ N ⊔ C` is invariant under right multiplication of `x` by `N`. -/
lemma mem_sup_mul_iff (N : OpenNormalSubgroup G) (C : Subgroup G) {x n : G}
    (hn : n ∈ (N : Subgroup G)) : x * n ∈ (N : Subgroup G) ⊔ C ↔ x ∈ (N : Subgroup G) ⊔ C := by
  constructor
  · intro h
    simpa using Subgroup.mul_mem _ h (Subgroup.mem_sup_left ((N : Subgroup G).inv_mem hn))
  · exact fun h ↦ Subgroup.mul_mem _ h (Subgroup.mem_sup_left hn)

omit [IsTopologicalGroup G] in
/-- **A decreasing family of nonempty closed sets indexed by the open normal subgroups has a
common point** (compactness). -/
theorem exists_mem_iInter_of_isClosed {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : OpenNormalSubgroup G → Set X)
    (hcl : ∀ N, IsClosed (A N)) (hne : ∀ N, (A N).Nonempty)
    (hmono : ∀ N N', N ≤ N' → A N ⊆ A N') : ∃ x : X, ∀ N, x ∈ A N := by
  haveI : Nonempty (OpenNormalSubgroup G) := ⟨topONS⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A
    (fun N N' ↦ ⟨N ⊓ N', hmono _ _ inf_le_left, hmono _ _ inf_le_right⟩) hne
    (fun N ↦ (hcl N).isCompact) hcl
  exact ⟨p, Set.mem_iInter.mp hp⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **A closed subgroup with cyclic images in all finite quotients is procyclic**: it is the
closure of `⟨γ⟩` for some `γ` in it. -/
theorem exists_topGenerator {I : Subgroup G} (hI : IsClosed (I : Set G))
    (hcyc : ∀ N : OpenNormalSubgroup G, IsCyclic (I.map (QuotientGroup.mk' (N : Subgroup G)))) :
    ∃ γ ∈ I, I = (Subgroup.zpowers γ).topologicalClosure := by
  let S : OpenNormalSubgroup G → Set G := fun N ↦
    {γ | ∀ x ∈ I, x ∈ (N : Subgroup G) ⊔ Subgroup.zpowers γ}
  have hS : ∀ N, S N = QuotientGroup.mk' (N : Subgroup G) ⁻¹'
      {q | ∀ x ∈ I, ∃ k : ℤ, QuotientGroup.mk' (N : Subgroup G) x = q ^ k} := by
    intro N
    ext γ
    simp only [S, Set.mem_setOf_eq, Set.mem_preimage]
    refine forall₂_congr fun x _ ↦ ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
    · haveI := N.isNormal'
      obtain ⟨n, hn, z, ⟨k, rfl⟩, hnz⟩ := Subgroup.mem_sup_of_normal_left.mp h
      refine ⟨k, ?_⟩
      have h1 : QuotientGroup.mk' (N : Subgroup G) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      simp only [← hnz, map_mul, h1, one_mul, map_zpow]
    · rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk
      rw [sup_comm]
      simpa using
        Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers γ k) ((N : Subgroup G).inv_mem hk)
  obtain ⟨γ, hγ⟩ := exists_mem_iInter_of_isClosed (G := G) (fun N ↦ (I : Set G) ∩ S N)
    (fun N ↦ hI.inter (by rw [hS N]; exact isClosed_preimage_mk N _))
    (fun N ↦ by
      obtain ⟨g, hg, hgen⟩ := exists_generator_of_isCyclic_map _ (hcyc N)
      refine ⟨g, hg, fun x hx ↦ ?_⟩
      obtain ⟨k, hk⟩ := hgen x hx
      rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk
      rw [sup_comm]
      simpa using
        Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers g k) ((N : Subgroup G).inv_mem hk))
    (fun N N' h ↦ Set.inter_subset_inter_right _ fun γ hγ x hx ↦
      sup_le_sup_right (show (N : Subgroup G) ≤ (N' : Subgroup G) from fun _ hy ↦ h hy)
        (Subgroup.zpowers γ) (hγ x hx))
  refine ⟨γ, (hγ topONS).1, le_antisymm (fun x hx ↦ ?_) (Subgroup.topologicalClosure_minimal _
    (Subgroup.zpowers_le.mpr (hγ topONS).1) hI)⟩
  exact mem_topologicalClosure_of_forall_sup fun N ↦ (hγ N).2 x hx

end Generic

/-! ### D2: the vertex group and its finite quotients -/

section D2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **D2**: for a decreasing, transitive family of open subgroups `S N ⊇ N` (stabilisers of a
compatible system of components), the intersection `D = ⋂ S N` maps onto every `S N / N`:
`D ⊔ N = S N`. -/
theorem sup_eq_of_transitive (S : OpenNormalSubgroup G → Subgroup G)
    (hSo : ∀ N, IsOpen (S N : Set G)) (hNS : ∀ N : OpenNormalSubgroup G, (N : Subgroup G) ≤ S N)
    (hmono : ∀ N N', N ≤ N' → S N ≤ S N')
    (htrans : ∀ N N', N ≤ N' → S N' ≤ S N ⊔ (N' : Subgroup G))
    {D : Subgroup G} (hD : ∀ x, x ∈ D ↔ ∀ N, x ∈ S N) (N : OpenNormalSubgroup G) :
    D ⊔ (N : Subgroup G) = S N := by
  refine le_antisymm (sup_le (fun x hx ↦ (hD x).mp hx N) (hNS N)) fun x hx ↦ ?_
  -- choose `d ∈ x N` in every `S (M ⊓ N)`
  obtain ⟨d, hd⟩ := exists_mem_iInter_of_isClosed (G := G)
    (fun M ↦ {d | d⁻¹ * x ∈ (N : Subgroup G)} ∩ (S (M ⊓ N) : Set G))
    (fun M ↦ by
      refine IsClosed.inter ?_ (Subgroup.isClosed_of_isOpen _ (hSo _))
      have : {d | d⁻¹ * x ∈ (N : Subgroup G)} = QuotientGroup.mk' (N : Subgroup G) ⁻¹'
          {QuotientGroup.mk' (N : Subgroup G) x} := by
        ext d
        simp [QuotientGroup.eq]
      rw [this]
      exact isClosed_preimage_mk N _)
    (fun M ↦ by
      haveI := N.isNormal'
      obtain ⟨s, hs, n, hn, rfl⟩ :=
        Subgroup.mem_sup_of_normal_right.mp (htrans (M ⊓ N) N inf_le_right hx)
      refine ⟨s, ?_, hs⟩
      simpa using hn)
    (fun M M' h ↦ Set.inter_subset_inter_right _ (hmono _ _ (inf_le_inf_right _ h)))
  have hdD : d ∈ D := (hD d).mpr fun M ↦ hmono _ _ inf_le_left (hd M).2
  have h1 : d⁻¹ * x ∈ (N : Subgroup G) := (hd N).1
  simpa using Subgroup.mul_mem_sup hdD h1

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
/-- A homomorphism `S → Γ` onto, killing `N ≤ S`, stays onto on `D` when `D ⊔ N = S`. -/
theorem surjective_restrict {Γ : Type*} [Group Γ] {S D : Subgroup G} {N : Subgroup G} [N.Normal]
    (hDS : D ≤ S) (hsup : D ⊔ N = S) (ρ : S →* Γ) (hρ : Function.Surjective ρ)
    (hN : ∀ x : S, (x : G) ∈ N → ρ x = 1) :
    Function.Surjective (ρ.comp (Subgroup.inclusion hDS)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := hρ q
  have hx' := hx
  rw [← hsup] at hx'
  obtain ⟨d, hd, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  refine ⟨⟨d, hd⟩, ?_⟩
  have hnS : n ∈ S := hsup ▸ Subgroup.mem_sup_right hn
  have : (⟨d * n, hx⟩ : S) = Subgroup.inclusion hDS ⟨d, hd⟩ * ⟨n, hnS⟩ := rfl
  rw [MonoidHom.comp_apply, this, map_mul, hN ⟨n, hnS⟩ hn, mul_one]

end D2

/-! ### Transport from finite quotients -/

section Quot

variable {G : Type*} [Group G] {D : Subgroup G} {N : Subgroup G} {Γ : Type*} [Group Γ]

/-- **Generation in `Γ_v(C_N)` gives generation of `D` modulo `N`**: if `ρ : D → Γ` has
`ker ρ ⊆ N` and `ρ a, ρ b` generate `Γ`, then `D ≤ N ⊔ ⟨a, b⟩`. -/
theorem le_sup_closure_of_quot (ρ : D →* Γ) (hker : ∀ x : D, ρ x = 1 → (x : G) ∈ N)
    {a b : D} (hab : Subgroup.closure {ρ a, ρ b} = ⊤) :
    D ≤ N ⊔ Subgroup.closure {(a : G), (b : G)} := by
  intro x hx
  have h1 : ρ ⟨x, hx⟩ ∈ (Subgroup.closure {a, b}).map ρ := by
    rw [MonoidHom.map_closure, Set.image_pair, hab]
    trivial
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp h1
  have h2 : ((w⁻¹ * ⟨x, hx⟩ : D) : G) ∈ N := hker _ (by rw [map_mul, map_inv, hwx, inv_mul_cancel])
  have h3 : (w : G) ∈ Subgroup.closure {(a : G), (b : G)} := by
    have : (w : G) ∈ (Subgroup.closure {a, b}).map D.subtype := Subgroup.mem_map_of_mem _ hw
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  have := Subgroup.mul_mem_sup h3 h2
  rw [sup_comm]
  simpa using this

/-- **Cyclicity transfers along kernels**: if `I ≤ D`, `ker ρ ⊆ N` and `ρ(I)` is cyclic, the
image of `I` in `G/N` is cyclic. -/
theorem isCyclic_map_of_ker_le [N.Normal] {I : Subgroup G} (hID : I ≤ D) (ρ : D →* Γ)
    (hker : ∀ x : D, ρ x = 1 → (x : G) ∈ N) (hcyc : IsCyclic ((I.subgroupOf D).map ρ)) :
    IsCyclic (I.map (QuotientGroup.mk' N)) := by
  let f : I →* (I.subgroupOf D).map ρ :=
    { toFun := fun y ↦ ⟨ρ (Subgroup.inclusion hID y), Subgroup.mem_map_of_mem _ y.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ ↦ by ext; simp }
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  let g : I →* I.map (QuotientGroup.mk' N) :=
    (QuotientGroup.mk' N).subgroupMap I
  have hg : Function.Surjective g := (QuotientGroup.mk' N).subgroupMap_surjective I
  have hle : f.ker ≤ g.ker := by
    intro y hy
    have h1 : ρ (Subgroup.inclusion hID y) = 1 := congrArg Subtype.val hy
    have h2 := hker _ h1
    ext
    simpa [g, QuotientGroup.eq_one_iff] using h2
  haveI : IsCyclic (I ⧸ f.ker) := isCyclic_of_surjective
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.surjective
  exact isCyclic_of_surjective (QuotientGroup.lift f.ker g hle)
    (QuotientGroup.lift_surjective_of_surjective _ _ hg _)

end Quot

/-! ### D3: choosing the generators and the vertex isomorphism -/

section D3

variable {P : ℕ → Prop} {Δ : Type} [Group Δ] [TopologicalSpace Δ] [IsTopologicalGroup Δ]
  [CompactSpace Δ] [TotallyDisconnectedSpace Δ]
  (hΔ : ∀ M : Subgroup Δ, IsOpen (M : Set Δ) → M.Normal → IsSigmaNat P M.index)

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
/-- `N ⊔ ⟨a, b⟩` depends only on `a, b` modulo `N`. -/
lemma sup_closure_pair_eq (N : OpenNormalSubgroup Δ) {a b a' b' : Δ}
    (ha : a⁻¹ * a' ∈ (N : Subgroup Δ)) (hb : b⁻¹ * b' ∈ (N : Subgroup Δ)) :
    (N : Subgroup Δ) ⊔ Subgroup.closure {a', b'} ≤ (N : Subgroup Δ) ⊔ Subgroup.closure {a, b} := by
  refine sup_le le_sup_left ((Subgroup.closure_le _).mpr ?_)
  rintro _ (rfl | rfl)
  · rw [sup_comm]
    simpa using Subgroup.mul_mem_sup
      (Subgroup.subset_closure (by simp) : a ∈ Subgroup.closure {a, b}) ha
  · rw [sup_comm]
    simpa using Subgroup.mul_mem_sup
      (Subgroup.subset_closure (by simp) : b ∈ Subgroup.closure {a, b}) hb

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
/-- Conjugation of `γ ^ k n` by `h` lies in `N ⊔ ⟨h γ h⁻¹⟩`. -/
lemma conj_mem_sup (N : OpenNormalSubgroup Δ) {γ y : Δ} (h : Δ)
    (hy : y ∈ (N : Subgroup Δ) ⊔ Subgroup.zpowers γ) :
    h * y * h⁻¹ ∈ (N : Subgroup Δ) ⊔ Subgroup.zpowers (h * γ * h⁻¹) := by
  haveI := N.isNormal'
  obtain ⟨n, hn, z, ⟨k, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  have e : h * (n * γ ^ k) * h⁻¹ = (h * n * h⁻¹) * (h * γ * h⁻¹) ^ k := by
    rw [conj_zpow]; group
  rw [e]
  exact Subgroup.mul_mem_sup (N.isNormal'.conj_mem n hn h) (Subgroup.zpow_mem_zpowers _ k)

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
/-- Changing the conjugating element by `N` changes the conjugate (and its inverse) by `N`. -/
lemma conj_mul_mem (N : OpenNormalSubgroup Δ) {n : Δ} (hn : n ∈ (N : Subgroup Δ)) (h x : Δ) :
    ((h * n) * x * (h * n)⁻¹)⁻¹ * (h * x * h⁻¹) ∈ (N : Subgroup Δ) ∧
      ((h * n) * x * (h * n)⁻¹)⁻¹⁻¹ * (h * x * h⁻¹)⁻¹ ∈ (N : Subgroup Δ) := by
  have h1 : x⁻¹ * n⁻¹ * x⁻¹⁻¹ ∈ (N : Subgroup Δ) :=
    N.isNormal'.conj_mem _ ((N : Subgroup Δ).inv_mem hn) _
  have h2 : x * n⁻¹ * x⁻¹ ∈ (N : Subgroup Δ) :=
    N.isNormal'.conj_mem _ ((N : Subgroup Δ).inv_mem hn) _
  constructor
  · have e : ((h * n) * x * (h * n)⁻¹)⁻¹ * (h * x * h⁻¹) = h * (n * (x⁻¹ * n⁻¹ * x⁻¹⁻¹)) * h⁻¹ := by
      group
    rw [e]
    exact N.isNormal'.conj_mem _ ((N : Subgroup Δ).mul_mem hn h1) h
  · have e : ((h * n) * x * (h * n)⁻¹)⁻¹⁻¹ * (h * x * h⁻¹)⁻¹ = h * (n * (x * n⁻¹ * x⁻¹)) * h⁻¹ := by
      group
    rw [e]
    exact N.isNormal'.conj_mem _ ((N : Subgroup Δ).mul_mem hn h2) h

/-- The pair attached to `d₀, d₁`: `(d₀ γ d₀⁻¹, (d₁ τ γ τ⁻¹ d₁⁻¹)⁻¹)`. -/
def pairOf (γ τ d₀ d₁ : Δ) : Δ × Δ := (d₀ * γ * d₀⁻¹, (d₁ * (τ * γ * τ⁻¹) * d₁⁻¹)⁻¹)

variable {D I : Subgroup Δ} {τ : Δ}

/-- The image of `pairHom g₀ g₁` lies in a closed subgroup containing `g₀, g₁`. -/
lemma range_pairHom_le {g₀ g₁ : Δ} (hD : IsClosed (D : Set Δ)) (h₀ : g₀ ∈ D) (h₁ : g₁ ∈ D) :
    (pairHom hΔ g₀ g₁).range ≤ D := by
  have hdisc : (pairDisc g₀ g₁).range ≤ D := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    rcases s with i | i | i
    · exact i.elim0
    · exact i.elim0
    · fin_cases i
      · change pairDisc g₀ g₁ (cusp 0) ∈ D
        simpa [pairDisc] using h₀
      · change pairDisc g₀ g₁ (cusp 1) ∈ D
        simpa [pairDisc] using h₁
      · change pairDisc g₀ g₁ (cusp 2) ∈ D
        simpa [pairDisc] using D.inv_mem (D.mul_mem h₀ h₁)
  have hcl : IsClosed (pairHom hΔ g₀ g₁ ⁻¹' (D : Set Δ)) :=
    hD.preimage (continuous_pairHom hΔ g₀ g₁)
  have hsub : Set.range (eta P (Γ := SurfaceGroup 0 3)) ⊆ pairHom hΔ g₀ g₁ ⁻¹' (D : Set Δ) := by
    rintro _ ⟨w, rfl⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, pairHom, liftPro_eta]
    exact hdisc ⟨w, rfl⟩
  rintro _ ⟨x, rfl⟩
  exact closure_minimal hsub hcl
    (by rw [(denseRange_eta (P := P) (Γ := SurfaceGroup 0 3)).closure_range]; trivial)

/-- `g₀, g₁` lie in the image of `pairHom g₀ g₁`. -/
lemma closure_pair_le_range (g₀ g₁ : Δ) :
    Subgroup.closure {g₀, g₁} ≤ (pairHom hΔ g₀ g₁).range := by
  rw [Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact ⟨_, pairHom_c₀ hΔ _ g₁⟩
  · rw [Set.mem_singleton_iff.mp hx]
    exact ⟨_, pairHom_c₁ hΔ g₀ _⟩

include hΔ in
/-- **D3, choice of the generators.** If `I ≤ D` are closed, `I` has cyclic images in all
finite quotients, `τ I τ⁻¹ ≤ D`, and at every level `N` some `d₀ y₀ d₀⁻¹` and
`(d₁ τ y₁ τ⁻¹ d₁⁻¹)⁻¹` (`dᵢ ∈ D`, `yᵢ ∈ I`) generate `D` modulo `N`, then for a topological
generator `γ` of `I` and suitable `d₀, d₁ ∈ D` the continuous map `Π^Σ_{0,3} → Δ`,
`c₀ ↦ d₀ γ d₀⁻¹`, `c₁ ↦ (d₁ τ γ τ⁻¹ d₁⁻¹)⁻¹` has image `D`. -/
theorem exists_pair (hD : IsClosed (D : Set Δ)) (hI : IsClosed (I : Set Δ)) (hID : I ≤ D)
    (hτ : ∀ y ∈ I, τ * y * τ⁻¹ ∈ D)
    (hcyc : ∀ N : OpenNormalSubgroup Δ, IsCyclic (I.map (QuotientGroup.mk' (N : Subgroup Δ))))
    (hlev : ∀ N : OpenNormalSubgroup Δ, ∃ d₀ ∈ D, ∃ d₁ ∈ D, ∃ y₀ ∈ I, ∃ y₁ ∈ I,
      D ≤ (N : Subgroup Δ) ⊔
        Subgroup.closure {d₀ * y₀ * d₀⁻¹, (d₁ * (τ * y₁ * τ⁻¹) * d₁⁻¹)⁻¹}) :
    ∃ γ ∈ I, I = (Subgroup.zpowers γ).topologicalClosure ∧ ∃ d₀ ∈ D, ∃ d₁ ∈ D,
      (pairHom hΔ (pairOf γ τ d₀ d₁).1 (pairOf γ τ d₀ d₁).2).range = D := by
  obtain ⟨γ, hγI, hγ⟩ := exists_topGenerator hI hcyc
  -- `I ⊆ N ⊔ ⟨γ⟩`
  have hIN : ∀ N : OpenNormalSubgroup Δ, ∀ y ∈ I, y ∈ (N : Subgroup Δ) ⊔ Subgroup.zpowers γ := by
    intro N y hy
    have hcl : IsClosed (((N : Subgroup Δ) ⊔ Subgroup.zpowers γ : Subgroup Δ) : Set Δ) :=
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_left N.toOpenSubgroup.isOpen)
    rw [hγ] at hy
    exact Subgroup.topologicalClosure_minimal _ le_sup_right hcl hy
  let S : OpenNormalSubgroup Δ → Set (Δ × Δ) := fun N ↦
    {p | D ≤ (N : Subgroup Δ) ⊔ Subgroup.closure {(pairOf γ τ p.1 p.2).1, (pairOf γ τ p.1 p.2).2}}
  -- saturation
  have hsat : ∀ N : OpenNormalSubgroup Δ, ∀ p ∈ S N, ∀ n₀ ∈ N.toOpenSubgroup,
      ∀ n₁ ∈ N.toOpenSubgroup, (p.1 * n₀, p.2 * n₁) ∈ S N := by
    intro N p hp n₀ hn₀ n₁ hn₁
    exact le_trans hp (sup_closure_pair_eq N (conj_mul_mem N hn₀ p.1 γ).1
      (conj_mul_mem N hn₁ p.2 (τ * γ * τ⁻¹)).2)
  obtain ⟨⟨d₀, d₁⟩, hd⟩ := exists_mem_iInter_of_isClosed (G := Δ)
    (fun N ↦ ((D : Set Δ) ×ˢ (D : Set Δ)) ∩ S N)
    (fun N ↦ (hD.prod hD).inter (isClosed_of_saturated N.toOpenSubgroup (hsat N)))
    (fun N ↦ by
      obtain ⟨d₀, hd₀, d₁, hd₁, y₀, hy₀, y₁, hy₁, hle⟩ := hlev N
      refine ⟨(d₀, d₁), ⟨hd₀, hd₁⟩, le_trans hle (sup_le le_sup_left ?_)⟩
      rw [Subgroup.closure_le]
      rintro _ (rfl | hx)
      · refine sup_le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ?_)) _
          (conj_mem_sup N d₀ (hIN N y₀ hy₀))
        simp [pairOf]
      · rw [Set.mem_singleton_iff.mp hx]
        refine Subgroup.inv_mem _ (sup_le_sup_left (Subgroup.zpowers_le.mpr ?_) _
          (conj_mem_sup N d₁ (conj_mem_sup N τ (hIN N y₁ hy₁))))
        have : (pairOf γ τ d₀ d₁).2 ∈ Subgroup.closure
            {(pairOf γ τ d₀ d₁).1, (pairOf γ τ d₀ d₁).2} := Subgroup.subset_closure (by simp)
        simpa [pairOf] using Subgroup.inv_mem _ this)
    (fun N N' h ↦ Set.inter_subset_inter_right _ fun p hp ↦
      show D ≤ _ from le_trans hp (sup_le_sup_right (fun _ hy ↦ h hy) _))
  obtain ⟨⟨hd₀, hd₁⟩, -⟩ := hd topONS
  refine ⟨γ, hγI, hγ, d₀, hd₀, d₁, hd₁, le_antisymm (range_pairHom_le hΔ hD ?_ ?_) fun x hx ↦ ?_⟩
  · exact D.mul_mem (D.mul_mem hd₀ (hID hγI)) (D.inv_mem hd₀)
  · exact D.inv_mem (D.mul_mem (D.mul_mem hd₁ (hτ γ hγI)) (D.inv_mem hd₁))
  · have hcl : IsClosed ((pairHom hΔ (pairOf γ τ d₀ d₁).1 (pairOf γ τ d₀ d₁).2).range :
        Set Δ) := by
      rw [MonoidHom.coe_range]
      exact (isCompact_range (continuous_pairHom hΔ _ _)).isClosed
    exact mem_of_forall_sup hcl fun N ↦
      sup_le_sup_left (closure_pair_le_range hΔ _ _) _ ((hd N).2 hx)

omit [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
/-- Conjugates of a procyclic subgroup: `⟨h γ h⁻¹⟩` is dense in `h I h⁻¹` if `⟨γ⟩` is dense
in `I`. -/
lemma closure_zpowers_conj [T2Space Δ] [CompactSpace Δ] {γ : Δ} (hI : IsClosed (I : Set Δ))
    (hγ : I = (Subgroup.zpowers γ).topologicalClosure) (h : Δ) :
    (Subgroup.zpowers (h * γ * h⁻¹)).topologicalClosure = I.map (MulAut.conj h).toMonoidHom := by
  have hf : Continuous (MulAut.conj h).toMonoidHom := by
    change Continuous fun x ↦ h * x * h⁻¹
    fun_prop
  have hz : Subgroup.zpowers (h * γ * h⁻¹) =
      (Subgroup.zpowers γ).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_zpowers]; rfl
  refine le_antisymm (Subgroup.topologicalClosure_minimal _ ?_ ?_) ?_
  · rw [hz]
    exact Subgroup.map_mono (hγ ▸ Subgroup.le_topologicalClosure _)
  · rw [Subgroup.coe_map]
    exact (hI.isCompact.image hf).isClosed
  · intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_map, hγ, Subgroup.topologicalClosure_coe] at hx
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hz, Subgroup.coe_map]
    exact image_closure_subset_closure_image hf hx

omit [TopologicalSpace Δ] [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
lemma pairDisc_cusp0 (g₀ g₁ : Δ) : pairDisc g₀ g₁ (cusp 0) = g₀ := by simp [pairDisc]

omit [TopologicalSpace Δ] [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
lemma pairDisc_cusp1 (g₀ g₁ : Δ) : pairDisc g₀ g₁ (cusp 1) = g₁ := by simp [pairDisc]

include hΔ in
/-- **D3: the vertex group is `Π^Σ_{0,3}`** (Route B, [SemiAnbd] Cor 3.11's proof). Under the
hypotheses of `exists_pair`, if moreover `D ∪ {τ}` generates `Δ` modulo every open normal
subgroup and `Δ ≃ₜ* Π^Σ_{1,1}` (B1), there are `g₀, g₁, τ' ∈ Δ` such that the continuous map
`β = pairHom g₀ g₁ : Π^Σ_{0,3} → Δ` (`c₀ ↦ g₀`, `c₁ ↦ g₁`) has image `D`, satisfies the HNN
relation of the 1-gon with stable letter `τ'`, the HNN map `Π^Σ_{1,1} → Δ` is bijective, `β` is a
closed embedding (so `D ≅ Π^Σ_{0,3}`), and `⟨g₀⟩`, `⟨g₁⁻¹⟩` are dense in the conjugates
`d₀ I d₀⁻¹`, `(d₁ τ) I (d₁ τ)⁻¹` (`d₀, d₁ ∈ D`) of the branch stabiliser. -/
theorem exists_vertex_iso (hD : IsClosed (D : Set Δ)) (hI : IsClosed (I : Set Δ)) (hID : I ≤ D)
    (hτ : ∀ y ∈ I, τ * y * τ⁻¹ ∈ D)
    (hcyc : ∀ N : OpenNormalSubgroup Δ, IsCyclic (I.map (QuotientGroup.mk' (N : Subgroup Δ))))
    (hlev : ∀ N : OpenNormalSubgroup Δ, ∃ d₀ ∈ D, ∃ d₁ ∈ D, ∃ y₀ ∈ I, ∃ y₁ ∈ I,
      D ≤ (N : Subgroup Δ) ⊔
        Subgroup.closure {d₀ * y₀ * d₀⁻¹, (d₁ * (τ * y₁ * τ⁻¹) * d₁⁻¹)⁻¹})
    (hgen : ∀ N : OpenNormalSubgroup Δ,
      (N : Subgroup Δ) ⊔ Subgroup.closure ((D : Set Δ) ∪ {τ}) = ⊤)
    (e : Δ ≃ₜ* proSigma P 1 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    ∃ g₀ g₁ τ' : Δ, (pairHom hΔ g₀ g₁).range = D ∧
      (∀ x, τ' * pairHom hΔ g₀ g₁ (oneGonB₀ P x) * τ'⁻¹ = pairHom hΔ g₀ g₁ (oneGonB₁ P x)) ∧
      Function.Bijective (hnnLift hΔ (pairHom hΔ g₀ g₁) τ') ∧
      Topology.IsClosedEmbedding (pairHom hΔ g₀ g₁) ∧
      (∃ d₀ ∈ D, (Subgroup.zpowers g₀).topologicalClosure = I.map (MulAut.conj d₀).toMonoidHom) ∧
      (∃ d₁ ∈ D, (Subgroup.zpowers g₁⁻¹).topologicalClosure =
        I.map (MulAut.conj (d₁ * τ)).toMonoidHom) := by
  haveI : T2Space Δ := e.toHomeomorph.isEmbedding.t2Space
  obtain ⟨γ, hγI, hγ, d₀, hd₀, d₁, hd₁, hrange⟩ := exists_pair hΔ hD hI hID hτ hcyc hlev
  set g₀ := (pairOf γ τ d₀ d₁).1 with hg₀
  set g₁ := (pairOf γ τ d₀ d₁).2 with hg₁
  set τ' := d₁ * τ * d₀⁻¹ with hτ'
  set β := pairHom hΔ g₀ g₁ with hβdef
  have hβ : Continuous β := continuous_pairHom hΔ g₀ g₁
  have hrel : τ' * g₀ * τ'⁻¹ = g₁⁻¹ := by
    simp only [hg₀, hg₁, hτ', pairOf, inv_inv]; group
  have key : ∀ k : ℤ, τ' * g₀ ^ k * τ'⁻¹ = g₁⁻¹ ^ k := fun k ↦ by rw [← conj_zpow, hrel]
  have hhnn : ∀ x, τ' * β (oneGonB₀ P x) * τ'⁻¹ = β (oneGonB₁ P x) := by
    let φ : ProSigmaCompletion P (Multiplicative ℤ) →* Δ :=
      (MulAut.conj τ').toMonoidHom.comp (β.comp (oneGonB₀ P))
    have hφ : Continuous φ := by
      change Continuous fun x ↦ τ' * β (oneGonB₀ P x) * τ'⁻¹
      exact (continuous_const.mul (hβ.comp (continuous_map (P := P) _))).mul continuous_const
    have hψ : Continuous (β.comp (oneGonB₁ P)) :=
      hβ.comp (continuous_map (P := P) (zpowersHom _ (oneGonGen false false)))
    have hext : φ = β.comp (oneGonB₁ P) := ProSigmaCompletion.hom_ext' hφ hψ
      (MonoidHom.ext fun n ↦ by
        simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_eta,
          zpowersHom_apply, oneGonGen, hβdef, pairHom, liftPro_eta, map_zpow, map_inv,
          pairDisc_cusp0, pairDisc_cusp1]
        first | exact key _ | rw [hrel])
    intro x
    exact DFunLike.congr_fun hext x
  have hgen' : ∀ N : OpenNormalSubgroup Δ,
      (N : Subgroup Δ) ⊔ Subgroup.closure (Set.range β ∪ {τ'}) = ⊤ := by
    intro N
    have hr : Set.range β = (D : Set Δ) := by rw [← MonoidHom.coe_range, hβdef, hrange]
    rw [hr]
    refine eq_top_iff.mpr (le_trans (hgen N).ge (sup_le_sup_left ?_ _))
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.subset_closure (Or.inl hx)
    · rw [Set.mem_singleton_iff.mp hx]
      have : τ = d₁⁻¹ * τ' * d₀ := by rw [hτ']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inl (D.inv_mem hd₁)))
        (Subgroup.subset_closure (Or.inr rfl))) (Subgroup.subset_closure (Or.inl hd₀))
  refine ⟨g₀, g₁, τ', hrange, hhnn, hnnLift_bijective hΔ β hβ τ' hhnn hgen' e,
    isClosedEmbedding_of_hnn hΔ β hβ τ' hhnn hgen' e hℓ hP, ⟨d₀, hd₀, ?_⟩, ⟨d₁, hd₁, ?_⟩⟩
  · exact closure_zpowers_conj hI hγ d₀
  · have : g₁⁻¹ = (d₁ * τ) * γ * (d₁ * τ)⁻¹ := by
      simp only [hg₁, pairOf, inv_inv]; group
    rw [this]
    exact closure_zpowers_conj hI hγ (d₁ * τ)

/-- **C2 at the vertex**: if `β : Π^Σ_{0,3} → Δ` is a closed embedding (e.g. from
`exists_vertex_iso`), a closed subgroup `C ≤ β(Π^Σ_{0,3})` containing `β(cⱼ)` whose images in all
finite quotients of `Δ` are cyclic (the cusp stabiliser of a compatible system of points over the
cusp, cyclic at every level by B4′ + C2) is `β` of the cusp inertia group `cuspInertiaSigma P j`. -/
theorem eq_map_cuspInertia_of_cyclic {β : proSigma P 0 3 →* Δ} (hβ : Topology.IsClosedEmbedding β)
    (j : Fin 3) {C : Subgroup Δ} (hC : IsClosed (C : Set Δ)) (hCD : C ≤ β.range)
    (hc : β (eta P (cusp j)) ∈ C)
    (hcyc : ∀ N : OpenNormalSubgroup Δ, IsCyclic (C.map (QuotientGroup.mk' (N : Subgroup Δ)))) :
    C = (cuspInertiaSigma P j).range.map β := by
  have hC' : C.comap β = (cuspInertiaSigma P j).range := by
    refine eq_range_cuspInertiaSigma_of_cyclic (by norm_num) j (hC.preimage hβ.continuous) hc
      fun M ↦ ?_
    obtain ⟨U, hU, hUM⟩ := hβ.isInducing.isOpen_iff.mp M.toOpenSubgroup.isOpen
    have h1 : (1 : proSigma P 0 3) ∈ β ⁻¹' U := by
      rw [hUM]; exact (M : Subgroup (proSigma P 0 3)).one_mem
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU
      (by simpa using h1)
    haveI := M.isNormal'
    let ρ : (⊤ : Subgroup (proSigma P 0 3)) →* Δ ⧸ (N : Subgroup Δ) :=
      ((QuotientGroup.mk' (N : Subgroup Δ)).comp β).comp (⊤ : Subgroup (proSigma P 0 3)).subtype
    refine isCyclic_map_of_ker_le (D := ⊤) le_top ρ (fun x hx ↦ ?_) ?_
    · have h2 : β x ∈ (N : Subgroup Δ) := (QuotientGroup.eq_one_iff _).mp hx
      have h3 : (x : proSigma P 0 3) ∈ β ⁻¹' U := hN h2
      rw [hUM] at h3
      exact h3
    · haveI := hcyc N
      refine Subgroup.isCyclic_of_le (H' := C.map (QuotientGroup.mk' (N : Subgroup Δ))) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨β x, hx, rfl⟩
  rw [← hC']
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hCD hx
    exact ⟨y, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

omit [IsTopologicalGroup Δ] [CompactSpace Δ] [TotallyDisconnectedSpace Δ] in
/-- An intersection of open subgroups is closed. -/
lemma isClosed_of_iff_forall {ι : Type*} (S : ι → Subgroup Δ) [IsTopologicalGroup Δ]
    (hSo : ∀ i, IsOpen (S i : Set Δ)) {D : Subgroup Δ} (hD : ∀ x, x ∈ D ↔ ∀ i, x ∈ S i) :
    IsClosed (D : Set Δ) := by
  have : (D : Set Δ) = ⋂ i, (S i : Set Δ) := by
    ext x
    simp [hD]
  rw [this]
  exact isClosed_iInter fun i ↦ Subgroup.isClosed_of_isOpen _ (hSo i)

include hΔ in
/-- **Route B, step 7, for towers of stabilisers.** `S N` (stabiliser of the component over `ℓ`
at level `N`) and `T N ≤ S N` (stabiliser of the branch-0 point over the node) open subgroups,
`D = ⋂ S N` (`D_v`), `I = ⋂ T N`, the loop element `τ` with `τ (T N) τ⁻¹ ≤ S N`; with the level
statements `hcyc`, `hlev` (B4′ + C2 through `RouteBLevel`), the generation `hgen` and B1
(`e : Δ ≃ₜ* Π^Σ_{1,1}`): `exists_vertex_iso` — `D_v ≅ Π^Σ_{0,3}` through a closed embedding
compatible with the HNN structure. -/
theorem exists_vertex_iso_of_tower (S T : OpenNormalSubgroup Δ → Subgroup Δ)
    (hSo : ∀ N, IsOpen (S N : Set Δ)) (hTo : ∀ N, IsOpen (T N : Set Δ)) (hTS : ∀ N, T N ≤ S N)
    (hD : ∀ x, x ∈ D ↔ ∀ N, x ∈ S N) (hI : ∀ x, x ∈ I ↔ ∀ N, x ∈ T N)
    (hτ : ∀ N, ∀ y ∈ T N, τ * y * τ⁻¹ ∈ S N)
    (hcyc : ∀ N : OpenNormalSubgroup Δ, IsCyclic (I.map (QuotientGroup.mk' (N : Subgroup Δ))))
    (hlev : ∀ N : OpenNormalSubgroup Δ, ∃ d₀ ∈ D, ∃ d₁ ∈ D, ∃ y₀ ∈ I, ∃ y₁ ∈ I,
      D ≤ (N : Subgroup Δ) ⊔
        Subgroup.closure {d₀ * y₀ * d₀⁻¹, (d₁ * (τ * y₁ * τ⁻¹) * d₁⁻¹)⁻¹})
    (hgen : ∀ N : OpenNormalSubgroup Δ,
      (N : Subgroup Δ) ⊔ Subgroup.closure ((D : Set Δ) ∪ {τ}) = ⊤)
    (e : Δ ≃ₜ* proSigma P 1 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    ∃ g₀ g₁ τ' : Δ, (pairHom hΔ g₀ g₁).range = D ∧
      (∀ x, τ' * pairHom hΔ g₀ g₁ (oneGonB₀ P x) * τ'⁻¹ = pairHom hΔ g₀ g₁ (oneGonB₁ P x)) ∧
      Function.Bijective (hnnLift hΔ (pairHom hΔ g₀ g₁) τ') ∧
      Topology.IsClosedEmbedding (pairHom hΔ g₀ g₁) ∧
      (∃ d₀ ∈ D, (Subgroup.zpowers g₀).topologicalClosure = I.map (MulAut.conj d₀).toMonoidHom) ∧
      (∃ d₁ ∈ D, (Subgroup.zpowers g₁⁻¹).topologicalClosure =
        I.map (MulAut.conj (d₁ * τ)).toMonoidHom) :=
  exists_vertex_iso hΔ (isClosed_of_iff_forall S hSo hD) (isClosed_of_iff_forall T hTo hI)
    (fun x hx ↦ (hD x).mpr fun N ↦ hTS N ((hI x).mp hx N))
    (fun y hy ↦ (hD _).mpr fun N ↦ hτ N y ((hI y).mp hy N)) hcyc hlev hgen e hℓ hP

end D3

end Iut.Reconstruction.RouteBVertex
