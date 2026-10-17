# MR17 hand-off: angular archimedean Frobenioids and the rest of [FrdII] Thm 2.4

State at iut main `d02df5d` (2026-10-17); Task B status updated through the MR17 Thm 2.4(i) reciprocity / `C_v` merges (main `fa4b67f` and the commit adding `InvCompat.lean`). Texts: `~/iut-scratch/frd/FrdII.txt` (line numbers below),
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
`G(G_E/N) = G_{E'}/α(N)`). Step 2 (Kummer classes) is done group-theoretically in `KummerClass.lean` /
`KummerClassFrob.lean`: `frobKummerClass X H n g hg ∈ ContH1 H (μ_n(O^×(X)))` for
`H ⊆ Aut_C(X)` (discrete), natural under fully faithful functors preserving `O^×`
(`Model.thm24_kummerClass`, `PAdicGalois.thm24_kummerClass`), factoring through `H_A`
(`kfun_eq_of_base`). Still open for step 2: identify, for `X` over `G/N` Galois and
`H ⊆ G_E` open normal, the class with the Galois-theoretic one: the hom `σ ↦ galAut N a σ⁻¹`
(`KummerFrob.lean`) from `H` to `Aut_C(X)`, `kummerCocycle_eq_kummerFun`, and LCFT's
`FiveTerm.inf₁` (`ContH1 (G⧸N) (fixedPts N A) → ContH1 G A`); then (N,H)-saturation as
bijectivity/surjectivity of `inf₁`/`inf₂`. **Update (2026-10-17, later):** the Galois identification is done in `KummerGalois.lean`:
`galHom N a : G_E →* Aut_C(X)` (`σ ↦ galAut σ⁻¹`), `uMu : μ_n(O^×(X)) → μ_n(K̄)` and
`kummerClass_eq_galois` / `kummerClass_eq_kummer` (the pulled-back Frobenioid class is
`KummerTheory.kummer n E K̄ x`).

**Status (2026-10-17, evening): steps 1–4 of the previous hand-off are done** (all for `C^⊢ = Frob p E`,
`Γ = ℤ`; `X = XN N a = (G_E/N, a)`, `H ⊆ G_E` open, `L = K̄^H = fixL H`):

* `Saturation.lean`: generic `Pull φ M`, `ZTriv n`, `infl₁`, `infl₁Z`, `infl₂`; `subA` (`H_A = galHom(H)`),
  `subHom`, `muX`, **`IsSaturated`** (Def 2.2(ii)(a),(c); (b) is automatic for `G_E/N`), **`FN`**.
* `FNEquiv.lean`: `galFixEquiv : Gal(K̄/L) ≃ₜ* H`, `h2HEquiv`, `uMu_bijective` (from μ_N-saturation),
  `fnEquivH2L : F_N(X) ≅ H²(L, μ_N)`, **`fnEquiv : F_N(X) ≅ ℤ/N`** (LCFT `h2MuEquiv`).
* `Reciprocity.lean`: `toL : H¹(H_A, μ_N(X)) → H¹(L, μ_N)`, **`toL_kummerClass`** (Frobenioid Kummer class
  = `KummerTheory.kummer N L K̄ x`), `charL`, **`recip`** (`η(κ) ∈ Hom(H¹(H_A, ℤ/N), F_N(X)) ≅
  H_A^ab ⊗ F_N(X)`, `χ ↦ χ ∪ κ` over `L`), **`fnEquiv_recip_kummerClass`** (`η_f(χ) = χ(artin x)`).
* `ReciprocityIso.lean`: **`toL_bijective`**, **`exists_charL`**, **`recip_injective`**.
* `GalHomCompat.lean`: **`exists_galHom_compat`**: `Ψ : C^⊢(E) ≌ C^⊢(E')` gives `α : G_E ≃ₜ* G_{E'}` with
  `Ψ(galHom σ)` acting on rational functions of units of `Ψ X` by `τ α(σ) τ⁻¹`.
* `SaturationGen.lean`, `SaturationExists.lean`: **`exists_isSaturated`** (Rem 2.2.1: all `(G_E/N, a)` with
  `N ⊆ N₀` are `(n, H)`-saturated — `IsSaturated` is non-vacuous).
* `SaturationTransport.lean`, `Thm24Saturated.lean`: generic `IsSat`/`FNG` for `(U, j, H)` and their
  transport (`IsSat.transport`, `fngEquiv`, `h1Equiv`, `subAEquiv`); **`PAdicGalois.thm24`**: `ΨX` with
  Galois structure `jPsi = Ψ ∘ galHom ∘ α⁻¹` is `(n, α(H))`-saturated and `F_N(X) ≅ F_N(ΨX)`.

Practical lessons: `obtain ⟨_, rfl⟩`/`rw [map_div]`/`rw` with `_` subgroup arguments against concrete
`ContH1`/`ContH2` goals over `Gal(K̄/L)`, `Pull …`, `WithDisc (Aut X)` time out (whnf/isDefEq) —
prove a generic lemma over abstract `G M M'` (e.g. `DualityAux.eq_of_forall_cupH1_eq`,
`Saturation.cocycle_eq_one_of_reps`, `ContH2Aux.exists_cocycle_of_reps`) and apply it; use `.elim`
instead of `obtain` on concrete existentials; `Pull φ M` terms need `@id M m` to use the `Q`-action.

**Status (2026-10-17, night): Thm 2.4(i) is done for `C^⊢_v` and `C_v`** (previous next steps 1, 3 and the
`FrobPf` part of 2):

* `CupGeneric.lean`: generic cup product `CupAux.cupH1G n hM hact χ hχ : H¹(G, M) →* H²(G, M)` for an
  `n`-torsion discrete `G`-module (`(χ ∪ ζ)(g, h) = (g • ζ(h))^{χ̃(g)}`), **`map_cupH1G`** (naturality under
  `ContH2.map`/`ContH1.map`), **`cupH1_eq_cupH1G`** (= LCFT `Brauer.cupH1`). Kept in iut (not LCFT) to avoid a
  pin bump racing the KroneckerDensity move; it has no iut dependency and can be moved to
  `LocalClassFieldTheory/Brauer/` verbatim.
* `ReciprocityTransport.lean`: `Saturation.recipG` (`η(κ)(χ) = [χ ∪ κ] ∈ FNG`, cup over `H_A`),
  **`fngEquiv_recipG`**, **`PAdicGalois.recip_eq_recipG`** (`recip` over `L` = `recipG`), **`thm24_recip`**
  (for every `α`, `fngEquiv (recip κ χ) = recipG (h1Equiv κ) (χ ∘ subATEquiv⁻¹)`).
* `KummerTransportGalois.lean`: generic `toLG U j hj H hH ρ hρ n` (`H¹(j(H), μ_N(U)) → H¹(K̄^H, μ_N)` for a
  `j`-equivariant `ρ : U →* K̄ˣ`), **`toLG_kummerClass`**, `Saturation.h1Equiv_kummerClass`, `ratFunTw τ`
  (`τ⁻¹ • ratFunY`), **`thm24_kummer_galois`** (`h1Equiv κ_g` = `KummerTheory.kummer N L' y` with
  `ρ(Ψ g)^N = y`, `L' = K̄^{α(H)}`).
* All p-adic files from `KummerGalois.lean` on take `{Γ : AddSubgroup ℝ}` (`GFrob p E Γ`, new abbrev in
  `PAdicGalois.lean`; `Frob`/`FrobPf` are `Γ = gammaZ/gammaQ`). `Thm24Pf.lean`: `exists_isSaturatedPf`,
  **`thm24Pf`**, `thm24Pf_recip`.
* `InvCompat.lean` (first step of Thm 2.4(ii)): for `α : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` and an `α`-equivariant
  `β : μ_n(Ω) ≃* μ_n(Ω')`: `PairCompat.h1PairMap` (`Φ₁`), `h2PairMap` (`Φ₂`), `h2PairMap_cupH1`
  (`Φ₂(χ ∪ ζ) = (χ ∘ α⁻¹) ∪ Φ₁ ζ`), **`h2MuEquiv_h2PairMap`**: if `⟨χ ∘ α⁻¹, Φ₁ ζ⟩ = ⟨χ, ζ⟩` for one pair with
  `⟨χ, ζ⟩ ∈ (ℤ/n)^×`, then `h2MuEquiv ∘ Φ₂ = h2MuEquiv`. This replaces Mochizuki's Brauer-group /
  unramified-`H²` argument ([Mzk1] Prop 1.2.1(vii)) by reciprocity.

[Mzk1] = "The Absolute Anabelian Geometry of Hyperbolic Curves", local copy
`~/iut-scratch/papers/txt/Absolute Anabelian Geometry.txt` (use `grep -a`: the file contains NUL bytes),
Prop 1.2.1 at l.426–551: for `α : G_{K₁} ≅ G_{K₂}`: (i) `p₁ = p₂`; (ii) `α(I_{K₁}) = I_{K₂}`; (iii) `α^ab`
preserves the images of `O^×`, `k^×`, `K^×`; (iv) it preserves Frobenius elements of `G^ab/Im(O^×)`;
(v) equal degrees and residue degrees; (vi) a Galois-equivariant `μ_{ℚ/ℤ}(K₁) ≅ μ_{ℚ/ℤ}(K₂)` (from the
abelianizations of open subgroups), so `α` preserves the cyclotomic character; (vii) the induced
`H²(K₁, μ_{ℚ/ℤ}) ≅ H²(K₂, μ_{ℚ/ℤ})` preserves the residue map `H² ≅ ℚ/ℤ`. iut already has (ii), (iv), (v),
the unramified part: `Iut/Reconstruction/Local/{Frobenius,UnramifiedZHat,Valuation,Abelianization,
Invariants,Cyclotome}.lean` (`galEquiv_unrZHat`, `galEquiv_restrict_maxUnramified`, `galEquiv_multEquiv`
(`Kˣ ≃* K'ˣ` from `α` via `G^ab`), `multAbEquiv_galEquiv_multEquiv`, `v_galEquiv_multEquiv`,
`Cyclotome.cyclotomic_rigidity`, `h2MuEquiv_coeffMap`). NB (vii) is *not* true for an arbitrary
`α`-equivariant `β` on `μ_n` (`β = ζ ↦ ζ^a` multiplies the invariant by `a`, `h2MuEquiv_coeffMap`); it holds
for the `β` coming from `α` itself (vi), resp. from `Ψ` on `C_v` (Thm 2.4(ii)), and fails for `C^⊢_v`
(Remark 2.4.2: cyclotomic twist).

**Thm 2.4(ii), Galois-side reduction done** (`Thm24ii.lean`, any `Γ`): for `Ψ`, `α`, `τ` with
`hρ` (`ratFunTw τ` is `jΨ`-equivariant — exactly what `exists_galHom_compat` gives), `X = XN N a`
`(n, H)`-saturated, `H`, `α(H)` open: `galPairEquiv : Gal(K̄/L) ≃ₜ* Gal(K̄/L')`, **`betaPsi`**
(`μ_N(K̄) → μ_N(K̄)`, `ζ ↦ ρ(Ψ(γ⁻¹ζ))`), **`betaPsi_smul`** (equivariance), **`fnPsi`**
(`F_N(Ψ X) → H²(L', μ_N)`), **`fnPsi_fngEquiv`** (`fnPsi ∘ fngEquiv = h2PairMap(galPairEquiv, betaPsi) ∘
fnEquivH2L`), **`thm24ii_of_pairing`**: given `hpair`/`hunit` for one `(χ, ζ)` over `L`,
`h2MuEquiv_{L'} (fnPsi (fngEquiv x)) = h2MuEquiv_L (fnEquivH2L x)` (`= fnEquiv x` by definition). The
generic engine is `Saturation.map_h2Equiv_eq`, `pair_smul`, `ker_infl₂_le_map`, `ContH2Aux.map_map_eq`
(concrete `rw`s against the Galois `H²` time out; every step is a generic lemma applied once).

**Next steps (precise), Thm 2.4(ii) for `C_v` (`Γ = gammaQ`, fieldwise saturated):** only the
arithmetic hypothesis `hpair` of `thm24ii_of_pairing` remains (it is false in general for `C^⊢_v`,
Remark 2.4.2, which is why it cannot be proved for arbitrary `Γ`).
1. *The arithmetic input (`hpair` of `thm24ii_of_pairing`).* Take `χ` unramified of order `N` over `L`
   and `ζ = κ(π)`, `π` a uniformiser of `L`; `⟨χ, κ(π)⟩ = χ(artin π) = χ(Frob)` is a unit
   (`pairingH1_kummer`; LCFT: `artin π` restricts to Frobenius on `L^ur`, see `Valuation.lean`
   `exists_restrict_eq_artin`, `hasRecVal_gal_iff`). Need: (a) `Φ₁(κ(π)) = κ(π')` for some `π' ∈ L'ˣ` with
   `v(π') = v(π)`; (b) `χ ∘ α⁻¹` is unramified with `(χ ∘ α⁻¹)(Frob') = χ(Frob)` (from `galEquiv_unrZHat`
   applied to `galFixEquiv`-transported `α|_H`). (a) is the field reconstruction of [FrdII] Thm 2.4(ii):
   for `C_v`, `O^▷(X)` (`GaloisModel.orhdEquiv`: `O^▷(X) ≅ {x ∈ (K̄^N)ˣ : ord x ∈ ℚ_{≥0}}`) is preserved by
   `Ψ` (`Thm34iv.lean`: `Model.map_mem_orhd`, `mem_orhd_iff`), with `Div` preserved up to the Frobenius
   degree (FrdI Thm 3.4 / `thm34Pf`); its groupification gives `β_N : (K̄^N)ˣ ≅ (K̄^{N'})ˣ` extending `betaPsi`,
   `α`-equivariant and `ord`-preserving. Kummer classes of non-units: extend `frobKummerClass` /
   `toL_kummerClass` from `O^×` to `O^▷`-elements with an `N`-th root in a deeper object `XN N'' a`
   (`N'' ⊆ N` with `K̄^{N''} ∋ π^{1/N}`), or use a *unit* `u` and a *ramified* `χ` with
   `⟨χ, κ(u)⟩ = χ(artin u)` a unit, if such a pair exists for the given `N` (not always: e.g. it needs
   an element of order `N` in the image of `O_L^×` in `L^×/(L^×)^N`; check). The unit route stays inside
   `thm24_kummer_galois` (only `O^×`) but needs the inertia part of `artin` to be preserved, i.e. `β` on `O_L^×` vs `α^ab` on `I^ab` (`unitsAbEquiv`,
   `galEquiv_multEquiv_units`).
2. Then `thm24Pf_ii` is `thm24ii_of_pairing` with `hpair` discharged.
3. Optional (unchanged): `O^□(A)^H ≅ O^□(LH)` (Rem 2.2.1); `(G_A/H_A)`-equivariance statements.

Practical: `lake build <targets>` inside the slot is the fastest way to check a chain after editing an
upstream file (rebuilding from `PAdicGalois.lean` down to `Thm24Pf.lean` is a long queue); `lake env lean` on
a single file needs up-to-date upstream oleans.

Older notes (superseded where the status above says so):

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
