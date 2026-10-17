# MR17 hand-off: angular archimedean Frobenioids and the rest of [FrdII] Thm 2.4

State at iut main `d02df5d` (2026-10-17). Texts: `~/iut-scratch/frd/FrdII.txt` (line numbers below),
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt` (IUT I Ex 3.4). Look up every
statement there; do not cite from memory.

## What exists (all in `Iut/Frobenioid/`)

* `GaloisModel.lean`: `invGrpOn` (`G/H ↦ M^H` on `B(G)⁰ = OrbitObj G`), `constPhi`,
  `GaloisModel G ℓ hℓ Γ`, `GaloisModel.hasAllTorsion`, `thm34`, `thm34_base`, `orhdEquiv`,
  `ounitsEquiv`.
* `PAdicGalois.lean`: `GK p E = Gal(K̄/E)` (`K̄ = PadicAlgCl p`), `Frob p E` (`C^⊢_v`, `Γ = ℤ`),
  `FrobPf p E` (`C_v`, `Γ = ℚ`), `ord`, `torsion`, `thm34`.
* `PAdicSlim.lean`: `PAdicGalois.isSlimGroup` (via LCFT `PadicField.artin_naturality`,
  `artin_injective`), `thm34_base`, `orbitObj_isSlim`.
* `KummerFrob.lean`: `Model.conj`, `conj_u`, `ounits_comm`, `Model.kummerCocycle`,
  `map_kummerCocycle`, `GaloisModel.galAut`, `PAdicGalois.kummerCocycle_galAut`,
  `kummerCocycle_eq_kummerFun`, `thm24_kummer` (Kummer half of Thm 2.4(i) at cocycle level).
* `Arch.lean`: the *model* Frobenioid `(ℝ_{≥0}, K_v^×, −log|·|)` over `Pt` — not IUT's `C_v`.
* `Thm34iv.lean`: `Model.map_mem_orhd`, `map_mem_ounits`, `mem_orhd_iff`, `mem_ounits_iff`.
* LCFT (pin `1e8b809`): `KummerTheory.kummer`, `kummerEquiv` (`Kˣ/(Kˣ)ⁿ ≃ H¹(K, μ_n)`),
  `Brauer.H2Mu`, `PadicField.h2MuEquiv` (`H²(K, μ_n) ≃ ℤ/n`, canonical), `Brauer.cupH1`,
  `PadicField.pairingH1`, `pairingH1_kummer` (`⟨χ, κ(a)⟩ = χ(artin a)`), perfectness
  (`eq_one_of_forall_pairingH1_eq_zero`), `PadicField.artin`, `artin_injective`, `artin_naturality`;
  `Cohomology/FiveTerm.lean`, `CentralTransgression.lean`.

## Task A: [FrdII] Ex 3.3 angular-region archimedean Frobenioids (IUT I Ex 3.4(i))

**Status (2026-10-17): done for `D = Pt`, `K = ℂ`** in `Iut/Frobenioid/Angular/` (`Circle.lean`:
Lemma 3.2(iv),(v); `Category.lean`: `Obj`, `Hom`, `toElem`, iso / co-angular / isotropic
characterisations; `Frobenioid.lean`: `Angular.isFrobenioid`; `Props.lean`: Ex 3.3(ii) object
types, `orhdEquiv : O^▷(A) ≅ O^▷_ℂ`; `Kummer.lean`: `kummer : O^▷(A) → RecField D p`).
Not done: `C^pf`, `C^rlf` of Ex 3.3(ii), the angular Frobenioid / angloids (iii)–(v), Prop 3.4,
3.5, Thm 3.6 (category-theoretic reconstruction of `S¹`); real `K`; switching
`HodgeTheater/PrimeStrip.lean`'s `archModel` (shell #31) to `Angular` (MR20). The plan below is
kept for reference.

IUT I Ex 3.4(i): `C_v` is "the archimedean Frobenioid as in [FrdII], Example 3.3, (ii) [i.e. `C`]",
base category "the one-morphism category determined by Spec(K_v)" (so `Pt`), with
`O^▷(C_v) ≅ O^▷_{K_v}` and Kummer structure `κ_v : O^▷(C_v) → A_{D_v}` (from `K_v ≅ A_{D_v}`).

Definitions ([FrdII] Def 3.1, l.1219–1300; Ex 3.3, l.1439–1575):

* Def 3.1(ii),(iii): for an archimedean local field `K`, `O_K^× = {|z| = 1}`, `ord(K^×) ≅ ℝ_{>0}`,
  `K^× = O_K^× × ord(K^×)`. An **angular region** `A ⊆ K^×` is `B × (0, λ]` with `B ⊆ O_K^×` open,
  meeting each connected component of `O_K^×` in a nonempty connected set (`B = O_K^×` if `K = ℝ`);
  `λ` is the *tip*; `A` is *isotropic* if `B = O_K^×`; `A, A'` are *co-angular* if they have the
  same `B`. `A₁ ⊗ A₂` is an angular region.
* Ex 3.3(i) over `D = Pt` (one `K`): objects `(V, A)` with `V` a 1-dimensional `K`-space and
  `A ⊆ V` an angular region. Since all `V` are isomorphic to `K`, one can take objects = angular
  regions `A ⊆ K^×`; a morphism `A → A'` is `(d ∈ ℕ_{≥1}, μ ∈ K^×)` with `μ·A^{(d)} ⊆ A'`
  (`A^{(d)} = {a^d}`), composition `(d', μ')∘(d, μ) = (dd', μ' μ^{d'})`. `Div(φ) = log λ` for the
  largest `λ` with `λ·μ·A^{(d)} ⊆ A'`, i.e. `log tip(A') − log|μ| − d·log tip(A)`; `degFr = d`;
  this gives `C → F_Φ` with `Φ = ℝ_{≥0}` (`Φ₀(Spec K) = ord(K) ≅ ℝ_{≥0}` via `log`). "Naively
  co-angular": for complex `K`, `Im(μA^{(d)})` co-angular with `A'`; always if `K` is real.
* Ex 3.3(ii) (cites Lemma 3.2, l.1343–1438, which must be read in full): isotropic = naively
  isotropic; co-angular = naively co-angular; every endomorphism of a non-isotropic object is
  linear and co-angular; isotropic ⇔ Frobenius-trivial ⇔ Frobenius-ample; every object is
  metrically trivial; **`C` satisfies [FrdI] Def 1.3** (the clauses of `IsFrobenioid` in
  `Defs.lean`, ~25 fields), Frobenius-isotropic type, `C^Q = C^pf`, `C^R = C^rlf`.
* Ex 3.3(iii)–(v): angular Frobenioid `A` (isometries), angloids `N`, `R`; slit morphisms are
  FSMI. Prop 3.4 (l.1576), Prop 3.5 (l.1798), Thm 3.6 (l.1927: `(C^Λ)^{istr}` is a model with
  rational functions `Φ^{fld}`, characteristic splitting, `(C^Λ)^{un-tr} ≅ C^R`, Aut-/End-ample,
  metrically trivial, rationally standard).

Plan (keep each file small; the 7 GB cap kills large elaborations):

1. `Iut/Frobenioid/Angular/Region.lean`: `AngularRegion K` for `K = ℂ` (and `ℝ`): structure
   `(B : Set Circle) (isOpen, nonempty, preconnected) (tip : ℝ, 0 < tip)` (for `ℝ`: `B ⊆ {±1}`
   nonempty), membership, `pow d` (image under `z ↦ z^d`; for `ℂ` the angular part `B^{(d)}` is the
   image under the `d`-th power map — note it may become all of `S¹`), scaling by `μ`, tip of the
   image, co-angular, isotropic. Lemma 3.2 facts needed for Def 1.3 (largest `λ`, isotropic hull
   `= O_K^× × (0, tip]`).
2. `Angular/Category.lean`: objects, morphisms `(d, μ)` with containment proof, category laws,
   `toElem : C ⥤ Elem (phiReal-on-Pt)` with `Div` as above (prove additivity).
3. `Angular/Frobenioid1.lean`, `Frobenioid2.lean`, …: the `IsFrobenioid` clauses, grouped as in
   `ModelFrobenioid.lean` ((i) base/pull-back, (ii) Frobenius morphisms `z ↦ z^d` with
   uniqueness up to iso, (iii) co-angular/coslice/slice, (iv) factorisation, (v) pre-step
   factorisations, (vi) units, (vii) isotropic hulls). Isomorphisms are `(1, μ)` with
   `μA = A'`; pull-backs are linear isometries.
4. `Angular/Orhd.lean`: `O^▷(A) ≅ O^▷_K = {0 < |z| ≤ 1}` for isotropic `A` with the topological
   monoid structure; `O^×(A) ≅ S¹`.
5. `Angular/Kummer.lean`: Kummer structure `κ_v : O^▷(C_v) → A_{D_v}`: reuse MR10
   (`Iut/AutHolomorphic/`: reconstructed field `RecField`, `A_p ≃* ℂˣ`, CAF isomorphisms,
   `Transport.lean`) — the "natural topological isomorphism `K_v ≅ A_{D_v}`" restricted to
   `O^▷`. Also state the category-theoreticity part relevant to IUT (Thm 3.6(vii), Prop 4.1(i),
   Cor 4.2: `S¹` of an isotropic complex object is recovered category-theoretically).

## Task B: the rest of [FrdII] Thm 2.4 (l.904–1218)

**Status (2026-10-17):** step 1 is done for profinite groups in `Iut/Frobenioid/GaloisRecon.lean`
(`OrbitObj.exists_continuousMulEquiv`: an equivalence `F : B(G₁)⁰ ≌ B(G₂)⁰` gives
`α : G₁ ≃ₜ* G₂` with `F(G₁/N) = G₂/α(N)` and `F(rmul g)(x_N) = α(g)·x_N` for compatible base
points `x_N`). It is applied to the `p`-adic Frobenioids in `PAdicRecon.lean`
(`PAdicGalois.exists_continuousMulEquiv`: `C^⊢(E) ≌ C^⊢(E')` lies over an equivalence
`G : B(G_E)⁰ ≌ B(G_{E'})⁰` — `BaseEquiv.isEquivalence_base` — and gives `α : G_E ≃ₜ* G_{E'}` with
`G(G_E/N) = G_{E'}/α(N)`). Steps 2–3 unchanged; for step 2 note `G_A ≅ Aut(A_E)`: for
`A_D = G/N` Galois, `F(rmul g)(x_N) = α(g)·x_N` (`exists_continuousMulEquiv`) identifies
`Ψ_Base` on `Aut(G/N) ≅ (G/N)^op` with `α mod N` up to conjugation by the base point.

Missing ingredients, in order:

1. **Outer isomorphism from an equivalence of Galois base categories.** Thm 2.4 obtains
   `Π₁ ≅ Π₂` (outer) from `Ψ_Base : D₁ ≅ D₂` ([Mzk2] Prop 3.2, Thm A.4 — not available locally).
   Needed: for compact (profinite, slim) `G₁, G₂`, an equivalence `OrbitObj G₁ ≌ OrbitObj G₂`
   induces `G₁ ≃* G₂` up to inner automorphisms. Route: Galois objects `G/N` (`N` open normal)
   are characterised category-theoretically (e.g. `|Aut(A)| = |Hom(A', A)|` for any `A'`
   dominating `A`, or "`Aut(A)` acts simply transitively on `Hom(T, A)`" with a cofinal system),
   `Aut(G/N) ≅ (G/N)^op` (`GaloisSlim.rmul`), and `G = lim G/N`. Mathlib's
   `CategoryTheory.PreGaloisCategory` (`IsFundamentalGroup`, `toAutMulEquiv`) works with the
   category of *all* finite `G`-sets with a fibre functor; `OrbitObj` is only the connected part.
   Either show `OrbitObj G` determines the Galois category of finite continuous `G`-sets
   (coproduct completion) or do the inverse-limit argument directly.
2. **Kummer classes on `H_A`** ([FrdII] Def 2.2, l.799–895): `(N, H)`-saturated objects, `H_A =
   Im(H → G_A)`, `κ_f ∈ H¹(H_A, μ_N(A))`. With 1., `κ` is compatible with `Ψ` via
   `map_kummerCocycle` (`KummerFrob.lean`) and `kummerCocycle_eq_kummerFun`.
3. **`F_N(A) = H²(H_A, μ_N)/Ker(→ H²(H, μ_N)) ≅ ℤ/N`** and the **reciprocity map**
   `η_f ∈ H_A^ab ⊗ F_N(A)` via the cup-product isomorphism `H¹(H, μ_N) ≅ H^ab ⊗ H²(H, μ_N)`
   (LCFT: `Brauer.cupH1`, `PadicField.pairingH1`, `pairingH1_kummer`, `h2MuEquiv`; five-term
   sequence / central transgression for the comparison `H_A` vs `H`). Thm 2.4(i): `Ψ` induces
   isomorphisms compatible with Kummer and reciprocity maps; (ii): `F_N(A₁) ≅ F_N(A₂)` compatible
   with `F_N ≅ ℤ/N` when `Φ` is fieldwise saturated (here: `FrobPf`).

Practical notes: `~/s2-lean-slot.sh` (7 GB cap; comparator needs `S2_LEAN_MEM=12G`); build with
`~/tools/lean-batchbuild.py` (topological batches); `Iut.Abc.P24Table` needs > 7 GB (copy its
olean from a built worktree; it only imports Mathlib). `~/lead-iut-b` is a fully built worktree.
