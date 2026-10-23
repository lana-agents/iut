# MR10 plan: holomorphic elliptic cuspidalisation ([AbsTopIII] Cor 2.7)

State: iut main `6e9ce43` (2026-10-23). ROADMAP §6.1 (MR10). The planar part of MR10 is done
(`Iut/AutHolomorphic/`, README there). This file covers what IUT actually cites: [AbsTopIII]
Cor 2.7, the construction of `A_X` for an elliptically admissible Aut-holomorphic orbispace.

Texts (look every statement up there; never quote from memory):

* T3 = `~/iut-scratch/papers/txt/Topics in Absolute Anabelian Geometry III.txt`
* T2 = `… Topics in Absolute Anabelian Geometry II.txt`
* I1, I2, I3 = `… Inter-universal Teichmuller Theory I.txt`, `… II.txt`, `… III.txt`

**Line numbers.** The ROADMAP table (§4.4) gives "Prop 2.6 (l.2862), Cor 2.7 (l.2925)". Those
come from another extraction. In T3: Def 2.1 l.2845, Rem 2.1.1 l.2946, Prop 2.2 l.2963,
Cor 2.3 l.3020, Cor 2.4 l.3059, Prop 2.5 l.3124, Prop 2.6 l.3219, **Cor 2.7 l.3288–3378**,
Rem 2.7.1–2.7.4 l.3379–3521, Cor 2.8 l.3522, Def 4.1 l.5918.

## 1. Cor 2.7: the exact statement (T3 l.3288–3378)

*Hypothesis.* `X` is an elliptically admissible Aut-holomorphic orbispace (Rem 2.1.1)
associated to a Riemann orbisurface `X`. "Elliptically admissible" (T3 l.2867–2869) means
that `X` comes from an elliptically admissible hyperbolic curve over `ℂ` in the sense of
[Mzk21] = [AbsTopII] Def 3.1 (T2 l.4302–4316): (a) `X` has a `k`-core `X → C`; (b) `C` is
semi-elliptic, so it has a double cover `D → C` by a once-punctured elliptic curve; (c) a
condition on covers `Y → X` factoring through `D`.

*Claim.* There is a functorial algorithm that builds the "local linear holomorphic structure"
(Prop 2.6) on `X^top` from the Aut-holomorphic space `X` alone:

* **(a)** Apply Cor 2.4 (c) to build the semi-elliptic hyperbolic core `X → H`. Then take the
  unique double cover `E → H` by an Aut-holomorphic space: the one given by the unique
  torsion-free index-2 subgroup of the group `Π` of Cor 2.4 (c). `E` is a once-punctured
  elliptic curve.
* **(b)** Elliptic cuspidalisation diagrams `E ← U → E` ([AbsTopII] Ex 3.2, T2 l.4326). Here
  `U → E` is an abelian finite étale cover (it extends to the one-point compactification of
  `E^top`), `E ← U` is an open immersion with finite complement, and the two maps are
  co-holomorphic. The **torsion points** of `E` are the points outside the image of such
  `U → E`. Their **group structure** is induced by the group `Gal(U/E)`.
* **(c)** The torsion points are dense. So the **group structure** on the one-point
  compactification of `E^top` is the unique topological group structure extending the one on
  torsion points. It gives **local additive structures** (Prop 2.5 (e)). From them one gets line
  segments (one-parameter subgroups), parallel segments, parallelograms, frames and orientations
  (Prop 2.5 (a)–(d)).
* **(d)** For a parallelogram `V`, consider the one-parameter subgroups of
  `A_V(V) ≅ SL₂(ℝ)/{±1}` (Prop 2.2 (ii), Cor 2.3 (i), Riemann mapping). They give
  tangency of segments to orbits. **Orthogonal frames** are pairs of segments at `p` tangent to
  `S₁·p` and `S₂·p`, where `S₂` is `S₁` conjugated by an element of order 4 of a compact
  one-parameter subgroup fixing `p`.
* **(e)** `A_p` is the group of automorphisms of the system of neighbourhoods of `p` that are
  compatible with the local additive structure and preserve orthogonal frames and orientations.
  As in Prop 2.6 (a), `A_p ∪ {0}` is a topological field, with compatible isomorphisms
  `A_p ≅ A_{p'}`.
* **Functoriality:** with respect to finite étale morphisms of Aut-holomorphic orbispaces
  arising from hyperbolic orbicurves over `ℂ`.

The proof (l.3374–3378) is "immediate from the constructions … together with the references
quoted". The real inputs are Cor 2.3 (i) (morphisms of Aut-holomorphic spaces are étale and
RC-holomorphic; via Prop 2.2, i.e. Cartan's theorem on `SL₂(ℝ)/{±1}`), Cor 2.4 (cores) and
classical facts about complex tori.

## 2. What IUT consumes, and in which form

* **I1 Ex 3.4 (i) (l.5190).** For `□ ∈ {X_v, C_v, …}` the CAF `A_□` "may be algorithmically
  constructed from `□`" ([AbsTopIII] Def 4.1 (i), T3 l.5918: `A_{X_ell}` is the `A_p` of
  Cor 2.7 (e), identified across `p`). It is used through the Kummer structure
  `κ_v : O^▷(C_v) → A_{D_v}`.
* **I1 Rem 3.4.2 (l.5390).** The Kummer structure is the same as the Aut-holomorphic structure on
  `O^▷(C_v)^gp` plus the tautological co-holomorphicization. It uses Cor 2.3.
* **I1 Rem 3.4.3 (l.5423).** `A_{X→v} = A_{D_v} ≅ A_{X_v}` "from the construction of `A_□` in
  Cor 2.7". `A^×` acts on punctured neighbourhoods of a point of `E_v` (Cor 2.7 (e)).
  (ii) (l.5466–5480) says that elliptic cuspidalisation has "a straightforward holomorphic
  analogue" (Cor 2.7), and so does Belyi cuspidalisation; "we leave the routine details to the
  reader". This is the source of the NF-points of `D_v`.
* **I1 Def 5.2 (vii) (l.9480–9560).**
  * Cor 2.7 (a) gives the orbispace `D_v → \underline{D}_v` (the core).
  * Cor 2.7 (e) gives `A_{D_v}` with its Aut-holomorphic structure and tautological
    co-holomorphicization.
  * Cor 2.7 (b) represents the κ-coric functions as meromorphic functions on `D^rat_v`. This is
    used again at l.9783.
* **I2 Prop 4.3 (i) (l.9330–9340).** `Ψ_cns(U_v) = A^▷_{U_v}`, citing Cor 2.7 (e).
  Rem 4.3.1 (l.9495) reads cusp decomposition groups as the `A_p` of Cor 2.7 (e).
* **I3 Rem 1.5.3 (l.3663).** This is motivation only.

**Form needed by iut.** The consumer of MR10 today is `Frobenioid/Angular/Kummer.lean`. It needs a
topological field `A_D`, built model-implicitly from an Aut-holomorphic space `D`, together with a
topological field isomorphism `A_D ≃+* ℂ`, unique up to `Gal(ℂ/ℝ)`. Today `D` must be
an Aut-holomorphic plane (`RecField`, `recEquiv`). Cor 2.7 is what lets `D` be the actual
orbispace `X→_v` (a once-punctured elliptic curve, or a cover of a semi-elliptic core).

## 3. What exists in iut

* `AutHolStr`, local morphisms, isomorphisms, `A_X(X)`, and `ofEmbedding` (`Basic.lean`).
  These cover Def 2.1 (i), (ii).
* The planar reconstruction `RecField A p ≃+* ℂ`, which is a homeomorphism (Prop 2.6 (a) and
  Cor 2.7 (e) for the plane). Also its functoriality and the `{id, conj}` indeterminacy
  (`Transport.lean`). Also `isIso_plane_iff` (Cor 2.3 (i) for the global plane) and
  `globalEquivPSL` (Prop 2.2 (ii), group part).
* CAFs and Kummer transitions (`CAF.lean`), and the Kummer structure on the angular Frobenioid
  (`Frobenioid/Angular/Kummer.lean`, [FrdII] Ex 3.3 over `Pt`).
* **Missing:**
  * Aut-holomorphic structures on non-planar Riemann surfaces;
  * the local (germ) Cor 2.3 (i);
  * Cor 2.4;
  * Prop 2.5 and 2.6 as algorithms on parallelograms;
  * all of Cor 2.7 (a)–(d).

Outside iut: Mathlib `PeriodPair` (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: the
lattice `Λ`, `IsZLattice`, `℘`). oka `Uniformization`: once-punctured tori `ℍ/⟨A,B⟩`, lifting
through coverings (`CoveringLift`), `exists_SL2R_eq_of_holomorphic`, plane uniformisation.

## 4. Formalisation design (model: `E = ℂ/Λ ∖ {0}`)

The inputs of Cor 2.7 used by IUT are `X_v`, `X→_v`, `C_v`, … (I1 Ex 3.4 (i)). By I1 Def 3.1 (d)
(l.3924 ff.), `X_K` has type `(1, l-tors)`, so `X_v = E_v ∖ E_v[l]`. `C_K` is its semi-elliptic
`K`-core. So step (a) is not trivial for IUT. Its output `E` is the once-punctured curve
`E_v ∖ {0}`. Step (a) means: find the core `C_v` (Cor 2.4) and its double cover `E`. The local
linear structures on `X^top` are then pulled back along the local homeomorphism `X^top → E^top`.
The formalisation starts at the output `E` of (a), i.e. at (b); (a) is T7 below.

Each step is a `def` on an arbitrary Aut-holomorphic space `(X, A)`. It is model-implicit and
uses only `X^top` and `A`. Each step comes with a theorem that computes it on the model
`(E_Λ, A_{E_Λ})`.

| Step | Lean | Model theorem | Inputs |
|---|---|---|---|
| T0 | `Torus.lean`: `T_Λ = ℂ ⧸ Λ`, `T[N]`, torsion dense, unique continuous group law extending the torsion law | (c) uniqueness | Mathlib |
| T1 | `ofCover π`: the Aut-holomorphic structure of a Riemann surface uniformised by a local homeomorphism `π : ℂ → X` (`g ∈ A(U)` iff `g`, `g⁻¹` lift locally to holomorphic maps); `ellStr Λ` on `E_Λ` | the multiplication maps `[N]` and open immersions are morphisms; `A(U)` in a chart = holomorphic automorphisms | T0 |
| T2 | (b): `IsEllCuspDiagram A U q`, `cuspPts A`, `cuspAdd A` (group law from `Gal(U/E)`) | `cuspPts (ellStr Λ) = T_Λ^tors ∖ {0}` and `cuspAdd = +`; the inclusion `⊇` is unconditional, `⊆` uses Cor 2.3 (i) | T1; `⊆` needs Cor 2.3 (i) |
| T3 | (c): `recAdd A` on `OnePoint X` = the unique continuous extension of `cuspAdd`; `+_p` | `recAdd = +` on `OnePoint E_Λ ≃ₜ T_Λ` | T0, T2 |
| T4 | (d)+(e): `Lie A` = continuous one-parameter subgroups `ℝ → (OnePoint X, recAdd)` (the tangent space at `p`, Rem 2.7.2); `A_p` = `ℝ`-linear automorphisms whose germ at `p` (through `exp_p`) is a local morphism of Aut-holomorphic spaces (Def 2.1 (ii)) and that are squares (orientation); `ellField A p = A_p ∪ {0}` | `A_p ≅ ℂ^×`, `ellField ≃+* ℂ` homeomorphically; indeterminacy `{id, conj}` | T3 |
| T5 | `A_{X_ell}` as the CAF of Def 4.1 (i); hook into `Frobenioid/Angular/Kummer.lean` (`D` = `E_Λ` instead of a plane) | `kummer` for `E_Λ` | T4 |
| T6 | Cor 2.3 (i) locally: a local morphism between opens of `ℂ` is RC-holomorphic (Prop 2.2 (i) for discs) | discharges the debt in T2 | oka (Riemann mapping / `exists_SL2R_eq_of_holomorphic`) |
| T7 | (a): Cor 2.4 cores and `E → H` for general elliptically admissible `X` | — | Fuchsian groups; large |

**Deviation in (d).** The paper gets conformality from one-parameter subgroups of `A_V(V)`
(orthogonal frames). T4 gets it more directly. An `ℝ`-linear germ `L` at `p` is kept iff it is a
local morphism of Aut-holomorphic spaces (Def 2.1 (ii)). In the model this holds iff `L` is
`ℂ`-linear or `ℂ`-antilinear. The proof conjugates the rotation by `i` on a small disc, which lies
in `A`. Orientation is "`L` is a square in this group": the squares of `ℂ^× ⋊ ⟨conj⟩` are exactly
`ℂ^×`. The output `A_p` is the same group as in the paper. This route needs neither the Riemann
mapping theorem nor Prop 2.2. The paper's (d) can be added later as a second characterisation.

**Debt (rule 4).** The statement "a morphism of Aut-holomorphic spaces `U → E_Λ` is
RC-holomorphic" is Cor 2.3 (i), which comes from Prop 2.2 (Cartan). It enters T2 (`⊆`) only, as
an explicit hypothesis `Cor23i Λ`, until T6 proves it. Nothing in T0, T1, T4 or the `⊇` half of
T2 depends on it.

**Size estimate.**
* T0–T5: about 3.5–4.5 k lines (T0 0.3 k, T1 0.6 k, T2 1.2 k, T3 0.3 k, T4 1 k, T5 0.2 k).
* T6: 1.5–2.5 k. Prop 2.2 via hyperbolic geometry: `φ` maps point stabilisers to point
  stabilisers, hence geodesics and midpoints, hence it is an isometry.
* T7: 5 k or more (Fuchsian commensurators).
* All of this fits the ROADMAP's 20–40 k for MR10, most of which is archimedean Frobenioids and
  log-volumes (MR17/MR26 side).

## 5. Progress log

* 2026-10-23: plan written (T0–T7).
* 2026-10-23: T0, T1 (part) and T4 for the torus model are done.
  * T0 is `Elliptic/Torus.lean`.
  * T1 is `OfCover.lean`: `ofCover`, `RCAlong`, the easy half of Cor 2.3 (i) (`ofCover_conj`),
    `restrict`, `isMorphism_val`.
  * T4 is `Elliptic/Lie.lean`, `RLinear.lean`, `LinearHol.lean` and `TorusField.lean`:
    * `isLinHol_iff`: the holomorphic `ℝ`-linear automorphisms of `Lie T_Λ` are exactly
      `c ↦ a c` and `c ↦ a c̄`;
    * `mem_apSet_iff`: `A_p` is the set of maps `c ↦ b c`;
    * `TorusField L q ≃+* ℂ`, which is a homeomorphism.
  * The torus model is `torusStr L` on all of `T_Λ`. It is not yet tied to the abstract input
    `(E, A_E)`. That needs T2, T3 and T5, plus a locality lemma: `IsLinHol` at `p ≠ 0` only sees
    `A` near `p`.
