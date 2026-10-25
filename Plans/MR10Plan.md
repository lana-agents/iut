# MR10 plan: holomorphic elliptic cuspidalisation ([AbsTopIII] Cor 2.7)

State: iut main after the 2026-10-24 second-session hand-off (§7). ROADMAP §6.1 (MR10). The planar part of MR10 is done
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
* 2026-10-24: merged the 2026-10-23 torus work (main `e8dce3b`). **T6 done for open subsets of
  `ℂ`**: `LocalRC.rcDiff_of_isMorphism` ([AbsTopIII] Cor 2.3 (i): a morphism of Aut-holomorphic
  spaces `U → V`, `U, V ⊆ ℂ` open, is holomorphic or antiholomorphic near every point), via
  * `Disc/Normalizer.rc_of_normalizes` (Prop 2.2 (i) for the disc: a homeomorphism normalising
    `Aut^hol(𝔻)` is RC-holomorphic). **Deviation**: the paper uses Cartan's theorem on
    `SL₂(ℝ)/{±1}`; the proof here is elementary hyperbolic geometry (half-turns ↦ half-turns,
    midpoints, rays by dyadic subdivision, and the functional equation
    `φ(st) = φ(s)φ(t)`, `φ(2t²−1) = 2φ(t)²−1` for `φ(cosh d(0,z)) = cosh d(0,αz)`, which forces
    `φ(2) = 2` and then `φ = id`);
  * `Disc/RiemannMap.exists_isBihol` (Riemann mapping for bounded simply connected domains, from
    oka's Koebe covering and lifting through coverings);
  * `Disc/Domain.rc_of_normalizes_bihol` (Prop 2.2 (i) for Aut-holomorphic discs).
  The debt `Cor23i` of §4 is therefore not needed for planar charts; for `E_Λ` it remains to pass
  through the charts of `ofCover` (T6b below).

* 2026-10-24 (second session). **T6b**: `Elliptic/Chart.lean`, `exists_rcLift_of_isMorphism`
  (Cor 2.3 (i) for opens of `T_Λ`, via `isMorphism_mk` and `rcDiff_of_isMorphism`). **Step 2 by
  route (a)** (lead decision): `Cusp.lean` (model-implicit `IsEllCusp`, `cuspTors`, `CuspSum`,
  `IsRecAdd`, `recAdd`), `Elliptic/{Punct,Affine,Lift,Deck,CuspModel}.lean`: the `[N]` diagrams,
  the classification of all diagrams of `E_Λ` (RC-holomorphic self-coverings of `T_Λ` are
  `x ↦ a x`, `x ↦ a x̄`: lifting, removable singularities, Liouville), `mem_cuspTors_iff`,
  `cuspSum_iff`, `recAdd_ellStr`. Deviations (recorded in `Cusp.lean`): co-holomorphy of
  `E ← U → E` not imposed (shown not to matter in the model); the extension to the
  compactification is imposed rather than derived; `IsRecAdd` asks for a continuous operation.

* 2026-10-24 (second session, cont.). **T3 for abstract `(E, A) ≅ E_Λ`**: `CuspTransport.lean`
  (the constructions of `Cusp.lean` are carried along isomorphisms) and `Elliptic/EllModel.lean`
  (`recAdd_of_isIso`, `isRecAdd_iff_of_isIso`, `ellAddCommGroup` on `OnePoint E` with addition
  `recAdd A`).

* 2026-10-25. **T5 done**: `Elliptic/LieTransport.lean` (`lieMap`, `lieConj`, `IsIsoNear`;
  `IsLinHol.transport`, `mem_apSet_transport`, `mem_fieldSet_transport`: `A_p ∪ {0}` depends only
  on the germ of the Aut-holomorphic structure at `p` and is carried along additive homeomorphisms
  that are isomorphisms near `p`; every `ℝ`-linear endomorphism of `Lie T_Λ` is continuous) and
  `Elliptic/EllField.lean` (`onePointStr A` = `A` on the opens of `OnePoint E` not containing `∞`,
  `EllSpace A` with the group law `recAdd A` of Cor 2.7 (c) as a topological group,
  `isIsoNear_compEquiv`, **`EllField A p = A_p ∪ {0}`** for `p ∈ E`, `add_val`/`mul_val`,
  **`ellEquiv hψ p : EllField A p ≃+* ℂ`** homeomorphically for every `ψ : (E, A) ≅ E_Λ`,
  `ellEquiv_trans_eq` (indeterminacy `{id, conj}`), `fieldSet_eq`). Hook:
  `Frobenioid/Angular/Kummer.lean` section `Ell` (`kummerEll` and its injectivity,
  multiplicativity, continuity, range, transport, indeterminacy for `D` with `IsEllModel D`).
  Design note: the opens containing `∞` get the full group in `onePointStr` (an arbitrary choice);
  this is harmless because `A_p` is only formed for `p ∈ E`, and `IsLinHol` only sees opens near
  `p` (`IsLinHol.transport` with `O = E`).

## 6. Hand-off 2026-10-24 (MR10 agent, lead christian-41)

**Merged to iut main.**

* `e8dce3b`: the 2026-10-23 torus work (T0, T1 part, T4 for `T_Λ`): `OfCover.lean`,
  `Elliptic/{Torus,Lie,RLinear,LinearHol,TorusField}.lean`. This is the stopped agent's commit
  `5062270`, rebased. Two comments and one proof contained the audit token `constant` and were
  reworded.
* `10a5ee0`: **T6 for open subsets of `ℂ`**, i.e. [AbsTopIII] Cor 2.3 (i):
  `LocalRC.rcDiff_of_isMorphism`. Its inputs:
  * Prop 2.2 (i): `Disc/Normalizer.rc_of_normalizes` for the disc, and
    `Disc/Domain.rc_of_normalizes_bihol` for Aut-holomorphic discs;
  * Riemann mapping: `Disc/RiemannMap.exists_isBihol`.

  No sorry, no new axioms, no new structures (the shell lint is unchanged).

**WIP.** None. Branch `mr10-cor27` in `~/mr10-iut` equals main.

**MR8.7.** MR8.7 is [AbsTopII] Cor 3.3 in curves-jacobian. It is profinite and group-theoretic,
and it contains nothing holomorphic. For the Aut-holomorphic side MR10 uses nothing from it. The
holomorphic analogue of elliptic cuspidalisation (Cor 2.7 (b)) has to be built here.

**Next steps (proposal).**

1. **T6b: Cor 2.3 (i) for `ofCover`** (about 0.4 k lines). Charts `mk : ball(q, ρ) ≃ mk(ball)`
   identify `(torusStr L).restrict (mk ball)` with `ofEmbedding (↑)` on the ball. Use `chart`,
   `injOn_psi`, `rcAlong_of_lift` and `differentiableAt_of_holAlong` from
   `Elliptic/LinearHol.lean`. Then a morphism between opens of `T_Λ` is RC-holomorphic in charts,
   by `rcDiff_of_isMorphism`. This needs two lemmas:
   * pre- and post-composition of `IsMorphism` with `IsIso`;
   * `IsMorphism` for restrictions.
2. **Group law on `OnePoint E` (T2/T3).** Two options.
   * (a) Follow the paper's (b), (c). For `⊆` one must classify the finite abelian coverings
     `U → E_Λ`, `U ⊆ E_Λ` cofinite, that extend over the cusp. This needs covering theory of
     tori, removable singularities on tori, and "holomorphic maps of tori are affine". Estimate:
     3–5 k lines.
   * (b) A cheaper, still model-implicit **deviation**:
     * `Aut^RC(OnePoint E)` is the set of homeomorphisms whose restriction to
       `E ∩ σ⁻¹ E → E` is a morphism of Aut-holomorphic spaces;
     * the translations are the squares in it that are `1` or have no fixed point;
     * `x + y = τ_x(y)`, where `τ_x` is the translation with `τ_x(∞) = x`.

     For the model this needs: T6b; removable singularities at two points; the fact that an
     RC-holomorphic homeomorphism of `T_Λ` lifts to an affine map of `ℂ` (Liouville); and
     constancy of `δ` on the connected set `T ∖ {2 points}`. Estimate: 1–1.5 k lines.

     Then the torsion points of (b) are the finite-order elements. The diagram characterisation
     can be added later as a second theorem. IUT I Rem 3.4.3 (ii) uses (b) for NF-points.

   *Decision for the lead*: (a) or (b) first.
3. **T5.** Follow the `RecField` pattern:
   * `Fact (IsEllModel A)`: there is an iso `(E, A) ≅ (E_Λ, ellStr Λ)`, where
     `ellStr Λ = (torusStr Λ).restrict {0}ᶜ`;
   * an `AddCommGroup` instance on `OnePoint E`, transported along the chosen iso, with the
     theorem that it equals the model-implicit law of step 2;
   * `A` pushed forward to `OnePoint E` along the open embedding;
   * transport and locality lemmas for `IsLinHol`: invariance under group isos that are
     Aut-holomorphic isos, and dependence only on `A` near `p ≠ ∞`;
   * `ellField A p ≃+* ℂ` from `TorusField`;
   * hook into `Frobenioid/Angular/Kummer.lean`.
4. T7 (cores, Cor 2.4) is unchanged (large).

**Blockers.** None.

## 7. Hand-off 2026-10-24, second session (MR10 agent, lead christian-aa)

**Merged to iut main.**

* `798a62b`: **T6b** and **step 2 by route (a)** (lead decision: the paper's cuspidalisation
  diagrams, no translation shortcut).
  * `Morphism.lean`: `IsMorphism.comp`, `codRestrict`, `restrict`, `isIso_of_isMorphism`,
    `isIso_openImageHomeo`.
  * `Elliptic/Chart.lean`: `isMorphism_mk` (charts are morphisms) and
    **`exists_rcLift_of_isMorphism`** ([AbsTopIII] Cor 2.3 (i) for opens of `T_Λ`).
  * `Cusp.lean` (model-implicit, any `(E, A)`): `IsEllCusp A U q` (diagram `E ⊇ U → E`: cofinite
    open immersion, morphism `q`, covering after extension to `OnePoint E`, Galois, abelian
    `deck q = Gal(U/E)`), `cuspTors A`, `CuspLim`, `CuspSum` (law via `Gal(U/E)`), `IsRecAdd`,
    `recAdd A`.
  * `Elliptic/{Punct,Affine,Lift,Deck,CuspModel}.lean`: `T_Λ` compact, `E_Λ = punct L`,
    `ellStr L`, `onePointEquiv : OnePoint E_Λ ≃ₜ T_Λ`; `exists_rc_of_rcLift` (RC-holomorphic
    self-coverings of `T_Λ` fixing `0` are `x ↦ a x` / `x ↦ a x̄`: lift through `mk`, type
    constant on the connected `ℂ ∖ mk⁻¹K`, removable singularities, Liouville on the periodic
    derivative); `isEllCusp_mulN` (the `[N]` diagrams of [AbsTopII] Ex 3.2 (i));
    **`exists_hom_of_isEllCusp`** (classification of all diagrams of `E_Λ`); **`mem_cuspTors_iff`**,
    **`cuspSum_iff`**, **`isRecAdd_iff`**, **`recAdd_ellStr`**.
* `96fb410`: `CuspTransport.lean` (isomorphisms carry diagrams, torsion points, their law and
  `recAdd`) and `Elliptic/EllModel.lean`: `IsEllModel A`, **`recAdd_of_isIso`** (Cor 2.7 (c) for
  an abstract `(E, A) ≅ E_Λ`), `isRecAdd_iff_of_isIso`, `ellAddCommGroup` with
  `ellAddCommGroup_add : x + y = recAdd A x y`, zero `∞`.

No sorry, no new axioms, no Prop-field structures (all predicates are `def … : Prop`).
Deviations (documented in `Cusp.lean`): co-holomorphy of `E ← U → E` (Def 2.1 (iv), `Orn`) not
imposed — the model classification shows the torsion points and law are unchanged; the extension of
`U → E` over the compactification is imposed (paper: "necessarily"); `IsRecAdd` asks for a
continuous operation rather than a topological group structure.

**WIP.** None (branch `mr10-cor27` = main after the hand-off commit).

**Next steps.**

1. **T5: `A_p` for abstract `(E, A) ≅ E_Λ`** (estimate 0.8–1.2 k lines). Design:
   * `onePointStr A : AutHolStr (OnePoint E)`: `aut V := if ∞ ∈ V then ⊤ else` the transport of
     `A.aut (coe⁻¹ V)` (only germs at `p ≠ ∞` matter);
   * `IsTopologicalAddGroup` for `ellAddCommGroup hA` (transported along `compEquiv ψ`);
   * `lieMap Θ : Lie Y ≃ₗ[ℝ] Lie Y'` for an additive homeomorphism `Θ` (post-composition), with
     continuity for the compact-open topology;
   * transport + locality lemma: if `Θ` is additive and matches `A`, `A'` on all opens inside a
     neighbourhood of `p`, then `IsLinHol A p M ↔ IsLinHol A' (Θ p) (Θ∗ M Θ∗⁻¹)` (shrink `N` using
     continuity of `expAt` and of `M`; `M` is continuous since `Lie T_Λ ≃ₜ ℂ`, `lieHomeo`);
   * apply with `Θ = compEquiv ψ`, `A' = torusStr L`: `fieldSet (onePointStr A) p` corresponds to
     `fieldSet (torusStr L) (Θ p)`, hence `EllField A p ≃+* ℂ` (via `TorusField`, `torusEquiv`),
     homeomorphically; indeterminacy `{id, conj}` as in `Transport.lean`;
   * hook into `Frobenioid/Angular/Kummer.lean` (a `kummer` for `D` with `IsEllModel D`).
2. T7 (cores, Cor 2.4) unchanged (large).
3. Optional: derive the "necessarily extends" condition (Riemann–Hurwitz-free argument: a finite
   covering of `E_Λ` by a cofinite `U ⊆ E_Λ` is unramified over `∞`) and add co-orientations.

**Blockers.** None. Slot contention made single-file checks slow (14 waiting jobs at times).
