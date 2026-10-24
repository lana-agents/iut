# Aut-holomorphic spaces and the archimedean reconstruction (`Iut/AutHolomorphic/`, MR10)

Milestone MR10 of the multiradial roadmap (`~/iut-scratch/multiradial/ROADMAP.md`, §6.1):
[AbsTopIII] §2 (texts in `~/iut-scratch/abstop/`), as used by IUT I, Example 3.4 and
Remark 3.4.2. Everything is proved in Lean (no hypotheses-as-structures); the analytic inputs are
Mathlib (Liouville, removable singularities, Schwarz lemma) and `oka`
(`Uniformization.deriv_ne_zero_of_injOn`, `Uniformization.exists_SL2R_eq_of_holomorphic`).

No module of this directory is imported by the comparator challenge or by the wall.

## Files

| File | Content | Reference |
|---|---|---|
| `Basic.lean` | `AutHolStr` (Aut-holomorphic structure `U ↦ A_X(U) ⊆ Aut(U^top)`), `LocalStructure`, `IsLocalMorphism`, `IsMorphism`, `IsIso` (`refl`, `symm`, `trans`), the global group `A_X(X)` (`IsIso.global_eq`), `ofEmbedding ι` (holomorphy in a coordinate `ι : X → ℂ`) | [AbsTopIII] Def 2.1(i), (ii); Rem 2.3.3 |
| `EntireAut.lean` | `exists_affine_of_proper`, `exists_affine_of_homeomorph`: an injective proper entire function is affine | classical |
| `Plane.lean` | the Aut-holomorphic plane; `mem_global_plane`: `A_ℂ(ℂ) = {z ↦ az + b}` | Def 2.1(i) |
| `Reconstruct.lean` | model-implicit data from `(X, A_X(X), p)`: translations (`IsTransl`), local additive structure `+_p` (`addAt`), `A_p ∪ {0}` (`Kset`) with its operations; functoriality under conjugation | Prop 2.5(e), 2.6(a); Cor 2.7(e); Rem 2.7.1, 2.7.4 |
| `PlaneField.lean` | the plane computations; `IsPlane`; the coefficient maps are additive / multiplicative | Prop 2.6(a) |
| `RecField.lean` | **`RecField A p`**, a field whose operations are the model-implicit ones (`add_val`, `mul_val`, …); **`recEquiv : RecField A p ≃+* ℂ`**, a homeomorphism, for every isomorphism `(X, A) ≅ ℂ`; `stabEquivUnits`: `A_p ≅ (A_p ∪ {0})ˣ ≅ ℂ^×` | Prop 2.6(a), Cor 2.7(e) |
| `Transport.lean` | functoriality `transportEquiv` (continuous, `refl`, `trans`); `induced_eq_id_or_conj`; `recEquiv_trans_eq`: two Kummer structures differ by `Gal(ℂ/ℝ)` | Cor 2.3(i), Def 4.1(iv) |
| `PlaneAut.lean` | **`isIso_plane_iff`**: the automorphisms of the Aut-holomorphic plane are exactly `z ↦ az + b`, `z ↦ a z̄ + b` | Cor 2.3(i), Prop 2.2(ii) for `ℂ` |
| `CAF.lean` | complex archimedean fields: `cafStr κ` (independent of `κ`, `cafStr_eq`), `tautEquiv` (`c ↦ (x ↦ c x)`), `kummer_transition_archPolyIso` (transitions lie in IUT III Prop 1.2(vii)'s poly-isomorphism `ArchPolyIso` and preserve the log-shell) | Def 4.1(i); IUT I Ex 3.4 |
| `HalfPlane.lean` | the Aut-holomorphic disc `ℍ`: `A_ℍ(ℍ)` = Möbius maps, `globalEquivPSL : A_ℍ(ℍ) ≃* SL₂(ℝ)/{±1}` | Prop 2.2(ii) (group part) |
| `Punctured.lean` | `ℂ^×`: `mem_global_punct` (`A_{ℂ^×}(ℂ^×) = {az, a/z}`); `eq_id_of_mul_of_monoid` | IUT I Rem 3.4.2 |
| `OfCover.lean` | `RCDiffAt`, `RCAlong` ((anti)holomorphy along a coordinate map `π : ℂ → X`), `ofCover hπ` (Aut-holomorphic structure of a uniformised Riemann surface), `ofCover_conj` (RC-holomorphic homeomorphisms are isomorphisms), `AutHolStr.restrict`, `isMorphism_val` (open immersions are morphisms) | Def 2.1 (i), (ii); Cor 2.3 (i) (easy half); Cor 2.7 (b) |
| `Disc/Basic.lean` | the unit disc `Dk`; `holAut` (holomorphic automorphisms), `mobH`, `rotH`, `conjH`; `eq_mul_of_mem_holAut` (stabiliser of `0` = rotations, Schwarz lemma); half-turns `half x`, `eq_half` (the unique involution `≠ 1` fixing `x`); midpoints `mid`, `half_mid`, `eq_mid` | Prop 2.2 (input) |
| `Disc/Formulas.lean` | explicit hyperbolic geometry: `mid_tanh`, dyadic subdivision `Icc_subset_of_mid`, rays `OnRay`/`mid_onRay`, `qN = cosh d(0, ·)`, `qN_double`, `qN_mob_I` (hyperbolic Pythagoras), `half_real`, `exists_real_mob_imag` | Prop 2.2 (input) |
| `Disc/Normalizer.lean` | **`rc_of_normalizes`**: a homeomorphism of the disc normalising `holAut` is `g` or `g ∘ conj`, `g ∈ holAut` (elementary proof replacing Cartan's theorem: half-turns, midpoints, the functional equation `fe_eq_id`) | Prop 2.2 (i), (ii) (normaliser part) |
| `Disc/Domain.lean` | `HolOn`, `holAutOn Ω`, biholomorphisms `IsBihol` and transport `IsBihol.conj_mem_iff`; **`rc_of_normalizes_bihol`**: an isomorphism of Aut-holomorphic discs is RC-holomorphic | Prop 2.2 (i) |
| `Disc/RiemannMap.lean` | **`exists_isBihol`**: a bounded simply connected domain is biholomorphic to the disc (oka's Koebe covering + lifting through the covering) | Riemann mapping theorem |
| `LocalRC.lean` | `mem_aut_iff` (`ofEmbedding (↑)` on `W ⊆ ℂ` is `Aut^hol(W)`); **`rcDiff_of_isMorphism`**: a morphism of Aut-holomorphic spaces between open subsets of `ℂ` is holomorphic or antiholomorphic near every point | **Cor 2.3 (i)** |
| `Elliptic/Torus.lean` | the complex torus `T_Λ = ℂ ⧸ Λ` (Mathlib `PeriodPair`), torsion points dense (`dense_torsion`), `eq_add_of_continuous`: the group law is the unique continuous law extending the torsion law | Cor 2.7 (c) |
| `Elliptic/Lie.lean` | one-parameter subgroups `Lie Y = ℝ →ₜ+ Y` (tangent space, compact-open topology, `ℝ`-module), `expAt`; `lieEquiv`/`lieHomeo : ℂ ≃ Lie T_Λ` (every one-parameter subgroup is `t ↦ mk (t c)`) | Cor 2.7 (c); Rem 2.7.2 |
| `Elliptic/RLinear.lean` | `ℝ`-linear self-maps of `ℂ`: differentiable ⇒ `ℂ`-linear; `M i M⁻¹` complex linear ⇒ `M` linear or antilinear; squares in `ℂ^× ⋊ Gal(ℂ/ℝ)` | Cor 2.7 (d), (e) |
| `Elliptic/LinearHol.lean` | model-implicit `IsLinHol A p M` (the germ of `M` at `p` is a local morphism of Aut-holomorphic spaces), `holGroup`, **`apSet A p` = `A_p`**, `fieldSet`; for `T_Λ`: `torusStr`, `isLinHol_iff` (holomorphic ⇔ `c ↦ a c` or `c ↦ a c̄`) | Cor 2.7 (d), (e) |
| `Elliptic/TorusField.lean` | `mem_apSet_iff` (`A_p = {c ↦ b c, b ≠ 0}`, independent of `p`); **`TorusField L q = A_p ∪ {0}`** with addition = sum of endomorphisms, multiplication = composition; `torusEquiv : TorusField L q ≃+* ℂ`, `torusHomeo` | Prop 2.6 (a), Cor 2.7 (e), Def 4.1 (i) |

## Main statements

* `RecField.recEquiv (hψ : IsIso A plane ψ) (p) : RecField A p ≃+* ℂ`, with
  `recEquiv_continuous`, `recEquiv_symm_continuous`: for an Aut-holomorphic space isomorphic to
  the plane, the field `A_p ∪ {0}` built from `A_X(X)` and `p` alone is a topological field
  isomorphic to `ℂ`. This is the "done when" statement `recField_equiv` of MR10 **for the planar
  case** (Aut-holomorphic spaces of CAFs, Definition 4.1(i)), not yet for elliptically admissible
  orbispaces.
* `isIso_plane_iff ψ : IsIso plane plane ψ ↔ ∃ a b, a ≠ 0 ∧ ((∀ z, ψ z = a z + b) ∨
  (∀ z, ψ z = a z̄ + b))`.
* `recEquiv_trans_eq`, `kummer_transition_archPolyIso`: the archimedean Kummer indeterminacy is
  `{id, conj}` and lies in `LogLink.ArchPolyIso`.
* `globalEquivPSL`, `mem_global_punct`, `eq_id_of_mul_of_monoid`.

## What remains of MR10

Plan for [AbsTopIII] Cor 2.7 (holomorphic elliptic cuspidalisation, the part IUT cites): `Plans/MR10Plan.md`.

* Co-orientations and co-holomorphicizations ([AbsTopIII] Def 2.1(iii), (iv)) via
  `Orn(Z, p) = lim π₁(W ∖ {p})^ab`.
* Aut-holomorphic structures of general Riemann surfaces and orbisurfaces (charts; Rem 2.1.1),
  Cor 2.3 (i) for them (done for open subsets of `ℂ`: `LocalRC.lean`) and Cor 2.3(ii); the
  topological and commensurable terminality parts of Prop 2.2(ii) (the normaliser part is
  `Disc/Normalizer.lean`).
* Cor 2.4 (hyperbolic cores via `π₁(X^top) ↪ Aut(U)`), Prop 2.5, 2.6 (parallelograms); Cor 2.8, 2.9.
* Cor 2.7: (d), (e) and the uniqueness half of (c) are done for the complex torus (`Elliptic/`).
  Still open: (a) cores, (b) torsion points from elliptic cuspidalisation diagrams, the
  reconstruction of the group law on `OnePoint E` from (b), and the transport of `A_p` to an abstract
  Aut-holomorphic space isomorphic to `T_Λ ∖ {0}` (steps T2, T3, T5, T6, T7 of `Plans/MR10Plan.md`).
* Archimedean Frobenioids [FrdII] Ex 3.3 over the Aut-holomorphic base, angular / radial
  log-volumes, and wiring `FullKummer.arc` (shells #18, #22) to these constructions (MR17, MR20,
  MR26).
