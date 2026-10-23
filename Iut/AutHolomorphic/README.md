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
  the local (germ) version of Cor 2.3 and Cor 2.3(ii); the topological and commensurable
  terminality parts of Prop 2.2(ii) (Cartan's theorem).
* Cor 2.4 (hyperbolic cores via `π₁(X^top) ↪ Aut(U)`), Prop 2.5, 2.6 (parallelograms), and the
  holomorphic elliptic cuspidalisation Cor 2.7(a)–(d) that constructs `A_p` for an elliptically
  admissible orbispace; Cor 2.8, 2.9.
* Archimedean Frobenioids [FrdII] Ex 3.3 over the Aut-holomorphic base, angular / radial
  log-volumes, and wiring `FullKummer.arc` (shells #18, #22) to these constructions (MR17, MR20,
  MR26).
