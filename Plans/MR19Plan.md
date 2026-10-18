# MR19 plan: global Frobenioids and κ-coric structures

State: iut main after the MR17 leftovers merge (2026-10-18). ROADMAP §6.2 (MR19), §5 shells #8, #31.
Texts (look every statement up there; never cite from memory):

* IUT I = `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`
* IUT II = `… Teichmuller Theory II.txt`, IUT III = `… Teichmuller Theory III.txt`
* [FrdI] = `~/iut-scratch/frd/FrdI.txt`
* [AbsTopIII] = `~/iut-scratch/papers/txt/Topics in Absolute Anabelian Geometry III.txt`

**Line-number corrections for ROADMAP §6.2 (MR19).** In these files, IUT I Ex 5.1 is at l.8234, not 6905.
IUT II Cor 4.7 is at l.10441, not 9045. IUT II Cor 4.8 is at l.11183, not 9641. IUT III Ex 3.6 is at
l.7074. The κ-coric pseudo-monoids are built in IUT I Ex 5.1(i), not (v). Item (v) defines
"∞κ-coric structures" on an abstract `†F^⊛` and proves that they exist and are unique. The
definition of a κ-coric function is IUT I Rem 3.1.7(i), (ii) (l.4316–4402).

## 1. Exact statements needed

### 1.1 [FrdI] Example 6.3 (l.6219–6326) "A Frobenioid of Arithmetic Origin"

> "Let F be a number ﬁeld […] Write V(F) for the set of valuations on F […] ord(O▷_v) def= O▷_v/O×_v
> […] We shall refer to an element of the monoid Φ(F) def= ⊕_{v∈V(F)} ord(O▷_v) as an eﬀective
> arithmetic divisor on F […] there is a natural homomorphism of groups B(F) def= F× → Φ(F)^gp […]
> if F̃ is a [not necessarily ﬁnite] Galois extension of F, G def= Gal(F̃/F), D def= B(G)0, then Φ,
> B determine monoids on D […] for each ﬁnite extension L ⊆ F̃ of F, one veriﬁes immediately that
> Φ(L) ≠ 0 is perf-factorial, that there is a natural bijection Prime(Φ(L)) ∼→ V(L), and that the
> supports of elements of Φ(L) are precisely the ﬁnite subsets of V(L). Thus, by Theorem 5.2, (ii),
> this data determines a [model] Frobenioid C_{F̃/F} […] we have O×(A) = O▷(A) = μ(L) […] a natural
> arithmetic degree homomorphism deg^arith_L : Φ(L)^gp → R […] deg^arith_L vanishes on the image of
> B(L)."

### 1.2 [FrdI] Theorem 6.4 (l.6334–6419) "Arithmetic Frobenioids"

* (i) (l.6348–6362): `C, C^pf, C^rlf, C^un-tr, (C^pf)^un-tr` are "of isotropic and rationally standard
  type, but not of group-like type; D is Frobenius-slim and Div-slim […] D is slim if and only if
  the subgroup of elements of G that commute with some open subgroup of G is trivial. Finally, if
  A ∈ Ob(C^rlf) is a Frobenius-trivial object […] then deg^arith_L determines an isomorphism of
  groups δA : PicΦ(A) ∼→ R".
* (ii) (l.6363–6378): an equivalence `Ψ^rlf` has a `deg(Ψ^rlf) ∈ R>0` with
  `δ_{A2} ∘ (PicΦ(A1) ≅ PicΦ(A2)) = deg(Ψ^rlf) · δ_{A1}`.
* (iii) (l.6379–6405): if `Ψ^rlf` comes from `(Ψ^pf)^un-tr`, then `deg(Ψ^rlf) ∈ Q>0`, and the bijection
  `V(L1) ≅ Prime(Φ1(L1)) ≅ Prime(Φ2(L2)) ≅ V(L2)` preserves the valuation `v0` of Q lying below.
* (iv) (l.6406–6419): if `Ψ^rlf` comes from `Ψ : C1 ≅ C2`, then `deg(Ψ^rlf) = 1`. If moreover some
  `L1 ⊆ F̃1` is Galois over Q, then `L2 ≅ L1` compatibly with `F1 ≅ F2` (proof: Chebotarev).

### 1.3 IUT I Example 3.5 (l.5485–5759) "Global Realiﬁed Frobenioids"

Item (i), l.5487–5543:

> "Write C⊩_mod for the realiﬁcation […] of the Frobenioid of [FrdI], Example 6.3 […] associated to
> the number ﬁeld Fmod and the trivial Galois extension […] the divisor monoid Φ_{C⊩_mod} […] whose
> set of primes […] Prime(C⊩_mod) […] is in natural bijective correspondence with Vmod […] the
> submonoid Φ_{C⊩_mod,v} […] corresponding to v ∈ Vmod is naturally isomorphic to
> ord(O▷_{(Fmod)v})^pf ⊗ R≥0 (∼= R≥0) […] pv determines an element log⊢_mod(pv) ∈ Φ_{C⊩_mod,v}. […]
> Write logΦ(pv) ∈ Φ^rlf_{C⊢_v} for the element deﬁned by pv and Cρv : C⊩_mod → (C⊢_v)^rlf for the
> natural restriction functor […] Cρv is determined, up to isomorphism, by the isomorphism of
> topological monoids […] ρv : Φ_{C⊩_mod,v} ∼→ Φ^rlf_{C⊢_v} induced by Cρv — which, by considering
> the natural "volume interpretations" of the arithmetic divisors involved, is easily computed to be
> given by the assignment log⊢_mod(pv) ↦ (1/[Kv:(Fmod)v]) logΦ(pv)."

Here `p_v` is defined in IUT I §0, l.2109–2112. For `v` nonarchimedean it is the residue
characteristic. For `v` archimedean it is "the unique positive real element of Fv whose natural
logarithm is equal to 1".

Item (ii), l.5544–5673: the Θ-version `C⊩_tht`, `ρΘ_v`. At bad `v`, `ρΘ_v` maps
`log⊢_mod(pv)·log(Θ) ↦ (logΦ(pv)/[Kv:(Fmod)v])·(logΦ(Θv)/logΦ(q_v))`. The item packages the data as
`F⊩_mod def= (C⊩_mod, Prime(C⊩_mod) ∼→ V, {F⊢_v}v∈V, {ρv}v∈V)` (l.5654–5665).

Item (iii), l.5674–5759: the D-version `F⊩_D`. It uses `(R⊢_≥0)v` from [AbsTopIII] Prop 5.8(iii), (vi).
It needs the factor `e_v` in the nonarchimedean case and `1/2π` in the archimedean case.

### 1.4 IUT I Remark 3.1.7 (l.4316–4482), the κ-coric functions

(i), l.4339–4351: "a rational function f ∈ L̄C on CL [is] κ-coric […] if · whenever f ∉ L̄, it holds that,
over L̄, f has precisely one pole [of unrestricted order], but at least two distinct zeroes; · the
divisor of zeroes and poles of f is deﬁned over a number ﬁeld and avoids the critical points; · f
restricts to a root of unity at every strictly critical point of |CL|cpt."

(ii), l.4384–4400: "∞κ-coric if there exists a positive integer n such that f^n is a κ-coric element
[…] ∞κ×-coric if there exists an element c ∈ UL such that c · f […] is ∞κ-coric […] the operation of
multiplication determines a structure of pseudo-monoid […] in the case of ∞κ- and ∞κ×-coric rational
functions, the resulting pseudo-monoid is divisible and cyclotomic."

### 1.5 IUT I Example 5.1 (l.8234–8949) "Global Frobenioids"

* (i) (l.8236–8411): uses [AbsTopIII] Thm 1.9 "via the Θ-approach" applied to `π1(†D⊚)`. It
  constructs `M⊛(†D⊚)` (an isomorph of `F̄×`, with its field structure), `M⊛_mod` (`F×_mod`), and
  `π^rat_1(†D⊛)`. It also constructs the pseudo-monoids `M⊛_κ`, `M⊛_∞κ`, `M⊛_∞κ×`. Then come the κ-sol
  quotient and "κ-sol-conjugate synchronization".
* (ii) (l.8412–8433): `V(†D⊚)`, `Φ⊛(†D⊚)` ("the monoid denoted "Φ(−)" in [FrdI], Example 6.3"), and the
  model Frobenioid `F⊛(†D⊚)` over `†D⊛` ([FrdI] Thm 5.2(ii)).
* (iii) (l.8434–8466): the abstract `†F⊛ ≃ F⊛(†D⊚)`, `†F⊚ = †F⊛|†D⊚`, and `†F⊛_mod = †F⊛|terminal
  objects`. The last "may be thought of as the Frobenioid of arithmetic line bundles on the stack
  "Smod"".
* (iv) (l.8467–8517): `O×(A^birat)` is the multiplicative group of the number field of `A`. It also
  gives `O▷_p`, and `Π_p0` is the decomposition group of some `v ∈ Vmod`.
* (v) (l.8518–8860): defines ∞κ-/∞κ×-coric structures on `†F⊛`. "†F⊛ always admits an ∞κ-coric
  (respectively, ∞κ×-coric) structure, which is, moreover, unique up to a uniquely determined
  isomorphism" (l.8704). This rests on Kummer theory and the unique cyclotome isomorphism
  `μΘ_Ẑ(π1(†D⊚)) ≅ μ_Ẑ(†M⊛_∞κ)` (l.8640, 8673). The ∞κ× → ∞κ cut-out is at l.8768 and the
  Kummer-restriction algorithm at l.8786. Then "a purely category-theoretic construction, from the
  category †F⊛, of the natural bijection Prime(†F⊛_mod) ∼→ Vmod" (l.8816). The MLF-Galois pairs
  `Π_p0 ↷ O▷^_p0` are at l.8859.
* (vii) (l.8864–8949): the labelled copies `†F⊛_j`, `†F⊛_⟨J⟩` and their realifications.

### 1.6 IUT II Corollary 4.7 (l.10441–10678) and 4.8 (l.11183–11447)

* 4.7(i) (l.10457–10535) "Non-realiﬁed Global Structures": a functorial algorithm in `†D⊚` for
  `†D⊚ → †D⊛`, `M⊛`, `M̄⊛`, `M⊛_∞κ`, `M⊛_mod ⊆ M⊛_sol ⊆ M⊛`, `M⊛_κ`, and the Frobenioids
  `F⊛_mod(†D⊚) ⊆ F⊛(†D⊚) ← F⊚(†D⊚)` with `Prime(F⊛_mod(†D⊚)) ≅ V` and the realification
  `F⊛_mod → F⊛R_mod`.
* 4.7(ii): the labels `j` and the F⋇_l-symmetrizing isomorphisms.
* 4.7(iii) (l.10625–10675): localization functors `F⊛_mod(†D⊚)_j → F⊚(†D⊚)|j`, the realified version,
  `{M⊛_∞κ}_j → ∏_v M∞κv(†Dvj)`, and `D⊩(†D⊢_j) ≅ F⊛R_mod(†D⊚)_j`, compatible with Prime and with the
  local `R≥0`.
* 4.8(i) (l.11207–11298): Kummer isomorphisms `(π^{κ-sol}_1 ↷ †M⊛_∞κ) ≅ (π^{κ-sol}_1 ↷ M⊛_∞κ(†D⊚))`
  and `†M⊛_κ ≅ M⊛_κ(†D⊚)`. Restricting Kummer classes then gives `†M⊛ ≅ M⊛(†D⊚)`,
  `†M⊛_mod ≅ M⊛_mod(†D⊚)`, and so on. These are "a compatible collection of isomorphisms of
  Frobenioids †F⊚ ≅ F⊚(†D⊚), †F⊛ ≅ F⊛(†D⊚), †F⊛_mod ≅ F⊛_mod(†D⊚), †F⊛R_mod ≅ F⊛R_mod(†D⊚)".
* 4.8(iii) (l.11393–11444): localization compatible with 4.7(iii), and `†C⊩_j ≅ (†F⊛R_mod)_j`.
* Both proofs: "follow immediately from the deﬁnitions and the references quoted".

### 1.7 IUT III Example 3.6 (l.7074–7220) "Concrete Representations of Global Frobenioids"

* (i) (l.7091–7147): `F⊛_MOD`. Its objects are `F×_mod`-torsors `T` with trivializations `t_v` of
  `β_v`-pushouts, where `βv : F×_mod → K×_v/O×_{Kv}`, and the `t_v` almost all come from one `t ∈ T`.
  Morphisms are `(n, elementary morphism T1^{⊗n} → T2)`. It has a Frobenioid structure with a
  one-arrow base, and `F⊛_mod ≅ F⊛_MOD`, inducing the identity on `F×_mod`.
* (ii) (l.7148–7202): the fractional-ideal version `{J_v}`. `J_v` is a fractional ideal of `K_v` at
  nonarchimedean `v` and a positive real multiple of `O_{K_v}` at archimedean `v`. Morphisms are
  `(n, f ∈ F×_mod)` with `f·J1^{⊗n} ⊆ J2`. This version is also isomorphic to `F⊛_mod`.
* (iii) (l.7203–7220): the composite isomorphism is not determined by "identity on `F×_mod`", but its
  perfection and realification are.

### 1.8 [AbsTopIII] Theorem 1.9 (l.2109–2199)

Statement: "a functorial "group-theoretic" algorithm for reconstructing the "NF-portion of the
function ﬁeld" of X from the extension 1 → ΔX → ΠX → Gk → 1". The steps:

* (a) Belyi cuspidalization `ΠU ↠ ΠY`, together with the decomposition groups of NF-points.
* (b) `Iz ≅ μẐ(ΠU)`.
* (c) the cuspidal principal divisors `PU ⊆ H1(ΠU, μẐ)`.
* (d) `k̄×_NF ⊆ K×_ZNF ↪ lim→ H1(ΠV, μẐ(ΠU))`.
* (e) the additive structure via Prop 1.3.

## 2. What exists (all over the one-morphism base `Pt`, for any `[NumberField K]`)

* [FrdI] Ex 6.3, `F̃ = F` (`GlobalNonRlf.lean`): `GlobalFrobenioid K` (`Φ = ⊕ ord(O^▷_v)`, `B = K^×`),
  `globalFrobenioid_isFrobenioid`, and `orhdEquiv`/`ounitsEquiv` (`O^▷ = O^× = μ(K)`).
  `realify : C → C^⊩` with `realify_essSurj` and `degree_realify`.
* Realification `GlobalRealified K` (`Global.lean`): `ArithDiv`, `effCone`, `ratFun = ℝ·div(K^×)`,
  `degArith`, and `degArith_ratFun` (the product formula). Also `picDeg`, `ofBundle`/`degree_ofBundle`
  (Arakelov degree of `ArithLineBundle`).
* Thm 6.4(i), the `δ_A` part (`GlobalPic.lean`): `picDegEquiv : Pic_Φ ≃ₗ[ℝ] ℝ` (Dirichlet + finite
  class group), and `nonempty_iso_iff_degree_eq`.
* `Prime(C^⊩) ≅ V` (`GlobalPrime.lean`): `primeEquiv`, `placeEquiv F` (`Ψ_Prime`), `supp_psiPhi`.
* Thm 6.4(ii) (`Thm64.lean`): `degOf F`, `thm64ii`. Thm 6.4(iii) (`Thm64iii.lean`): `thm64iii`.
  Cor 4.11(iii), (iv) for `C^⊩`: `Cor411Rlf.lean`. `(C^pf)^{un-tr}`: `GlobalPf.lean`.
* `Arakelov/`: idelic `ArithLineBundle K`, `ArithPic`, `deg`/`degNorm`, fractional ideals;
  `Container.lean`/`ArchScaling.lean`/`QPilot.lean` (on `D.Kt`, used by Cor 3.12).
* Theta data: `fieldOfModuli F E` (`F_mod`, `NumberField` instance). `ValuationSection` gives
  `sectFin`/`sectInf` (`V ≅ V_mod`, with each `sect v` lying over `v`) and `Vnon`, `Varc`, `Vbad`.
  `FinitePlace.LiesOver`, `ramificationIdx'`, `inertiaDeg'` (`Cor312/ThetaData/{LocalConditions,
  PlacesOver, ValuationTransfer}.lean`).
* Shell #8: `HodgeTheater/PrimeStrip.lean` `FRlfStrip` (`C : Cat`, `equiv_model`, `strip`). It has no
  `Prime ≅ V` and no `ρ_v`.

* New (2026-10-18): `GlobalFracIdeal.lean` (IUT III Ex 3.6(ii)), `Thm64iv.lean` ([FrdI] Thm 6.4(iv) over `Pt`).

## 3. What depends on MR9 (mono-anabelian reconstruction; only the local part exists)

* MR9 itself is planned in `Plans/MR9Plan.md` (step U1, Uchida's lemma, started).
* Everything κ: IUT I Ex 5.1(i), (v) (`M⊛`, `M⊛_κ`, `M⊛_∞κ`, `M⊛_∞κ×` as group-theoretic
  constructions from `π1(†D⊚)`; the uniqueness of ∞κ-coric structures), and IUT II Cor 4.7(i)/4.8(i)
  (the Kummer isomorphisms). These need [AbsTopIII] Thm 1.9 (a)–(e) for the once-punctured elliptic
  curve, i.e. `recFunctionField` (MR9 "Done when"), which does not exist. Even the *definition* of
  the group-theoretic `M⊛(†D⊚)` and the base `†D⊛` with `π1(†D⊛)` (orbicurve `C_{F_mod}`) needs MR9
  and MR22 (`D^⊚ = B(C_K)^0`).
* Ex 5.1(ii)/(iii): the model Frobenioid `F⊛(†D⊚)` over `†D⊛ = B(π1(C_{F_mod}))^0` needs the base
  category from MR22. Its field-theoretic counterpart over `B(Gal(F̄/F_mod))^0` (the Galois base of
  [FrdI] Ex 6.3) does not.
* The category-theoretic `Prime(†F⊛_mod) ≅ V_mod` of Ex 5.1(v) (l.8816) goes through the
  ∞κ-structure. The field-theoretic `Prime ≅ V` does not.

## 4. What can be done now (no MR9)

1. **`Prime(Φ(F)) ≅ V(F)` for the non-realified Ex 6.3 Frobenioid**, compatible with
   realification (`Prime(M) ≅ Prime(M^pf)`, [FrdI] §0 l.579–581). *Done in this session:*
   `GlobalPrimeZ.lean`.
2. **`ρ_v` (IUT I Ex 3.5(i))**: for `k = F_mod ⊆ K`, `v ∈ V_mod` and `w = sect v` over `v`, define:
   * `Φ_{C⊩,v}` (the effective divisors supported at `v`);
   * `log⊢_mod(p_v)` (the `v`-part of `div(p_v)`; `[v]` at archimedean `v`);
   * the local realified monoid `Φ^rlf_{C⊢_v} = ℝ≥0` (coordinate `ord_{K_w}`), with
     `logΦ(p_v) = ord_{K_w}(p_v)` (`1` at archimedean `w`);
   * `ρ_v : Φ_{C⊩,v} ≅ ℝ≥0` with `ρ_v(log⊢_mod(p_v)) = logΦ(p_v)/[K_w : k_v]`.

   Then prove the "volume interpretation" `deg^arith_k(z) = vol_{K_w}(ρ_v z)`, where
   `vol_{K_w}(y) = y·log N(w)` (finite) or `[K_w:ℝ]·y` (archimedean). This needs
   `ord_w(x) = e(w|v)·ord_v(x)` (`valuation_algebraMap_eq_pow`) and `N(w) = N(v)^{f(w|v)}`
   (Mathlib `absNorm_eq_pow_inertiaDeg'_of_liesOver`). *Done:* `GlobalRho.lean` (`rho`, `rho_logMod_fin/inf`,
   `degArith_eq_vol_rho_fin/inf`, `ord_algebraMap`, `primeNorm_liesOver`).
3. **`F⊩_mod` as data** (IUT I Ex 3.5(ii) l.5654): the structure `(C⊩_mod, Prime ≅ V, {ρ_v})` built from
   theta data, replacing `FRlfStrip`'s bare `C : Cat` (shell #8, global half). The local `F⊢_v`
   components wait for MR20 (genuine prime-strips). *Done (global part):* `HodgeTheater/FRlfMod.lean`
   (`FRlfGlobal`, data-only structure; `FRlfGlobal.ofThetaData`, `FRlfMod.rho_logMod`,
   `FRlfMod.degArith_eq_vol_rho`). Next: make `FRlfStrip` carry an `FRlfGlobal` and the `ρ_v` land in the
   realified divisor monoids of the `F^⊢`-strip components (needs MR20's genuine `C^⊢_v`).
4. [FrdI] Ex 6.3 over a Galois base `B(Gal(F̃/F))^0` (needed for Ex 5.1(ii) field-theoretically, and
   for Thm 6.4(iv)): divisor monoid `L ↦ Φ(L)` with pull-back maps along `L ⊆ L'` (`ord_{w'} = e·ord_w`,
   the same input as 2). Model Frobenioid via `Model` over `OrbitObj G` as in `GaloisModel.lean`, which
   currently supports only constant monoids.
5. *Done over `Pt`* (`Thm64iv.lean`): Thm 6.4(iv), both halves. "Arises from `Ψ`" is the natural iso
   `realify ⋙ F ≅ Ψ ⋙ realify`, so Thm 3.4 for `GlobalFrobenioid` is not needed; Chebotarev is replaced by
   LCFT's `infinite_setOf_splitsCompletely` and Bauer's theorem. Over a Galois base: after item 4.
6. *Done* (`GlobalFracIdeal.lean`; (i), (iii) open): IUT III Ex 3.6(ii): the fractional-ideal Frobenioid. Objects `{J_v}`: `J_v = π_v^{n_v} O_{K_v}` at
   finite `v` (a theorem about f.g. `O_v`-submodules of `K_v`, Mathlib's DVR API), `r_v·O` at
   archimedean `v`. Morphisms `(n, f)` with `f·J1^n ⊆ J2`. Then an isomorphism of categories with
   `GlobalFrobenioid F_mod` inducing the identity on `F_mod^×`. (i), the torsor version, follows via
   `ArithLineBundle` ↔ torsors. (iii): uniqueness on realifications (`Thm64ii`-style rigidity).
7. The field-theoretic κ-coric pseudo-monoids (Rem 3.1.7(i), (ii)) as subsets of the function field of
   `C_{F_mod}` (needs the curve `C_{F_mod}` and its critical points from the theta data; the Kummer
   compatibility of Ex 5.1(v) then needs MR9).

## 5. Order of work

1 (done) → 2 → 3 → 6 → 4 → 5; everything κ after MR9. The "Done when" of ROADMAP MR19 should be
split. `primeEquiv` (done), `ρ_v` and `F⊩_mod` (items 2, 3) can be done now. `kappaCoric_kummer` waits
for `recFunctionField` (MR9).

## 6. Status log

* 2026-10-18 (MR9 lead session): IUT III Ex 3.6(i) and the first half of (iii) (`GlobalTorsor.lean`):
  `TorsorFrob K` (`F^⊛_MOD`: `K^×`-torsors with equivariant `τ : T → ArithDivZ K` encoding the
  trivializations of the `β_v`-pushouts; morphisms = integral `n`-equivariant maps),
  `TorsorFrob.ofModel : GlobalFrobenioid K ⥤ TorsorFrob K` fully faithful + essentially surjective
  (`equivModel`), preserving Frobenius degrees and inducing the identity on `K^×` (`ofModel_map_one`);
  `fracIdealEquivTorsor : FracIdealFrob K ≌ TorsorFrob K` (the composite of (iii)). Left of (iii): the
  uniqueness statement on perfections/realifications.
* 2026-10-18 (later): IUT III Ex 3.6(ii) (`GlobalFracIdeal.lean`, iut c785b58): `FracIdeal.le_iff_count_le`
  (not in Mathlib), `FracIdealFrob K`, `toModel` full, faithful, bijective on objects, identity on `K^×`,
  Frobenius degrees preserved. Deviation (documented in the file): the text takes `J_v ⊆ K_v` for `K ⊇ F_mod`;
  for `e(K_v|(F_mod)_v) > 1` that category is *not* isomorphic to the Ex 6.3 Frobenioid of `F_mod` compatibly
  with the identity on `F_mod^×`, so the local fields of `F_mod` are used (cf. IUT III Rem 3.6.1, which reads
  the `β_v` in the perfection). [FrdI] Thm 6.4(iii) restated under `PreservesRatFin` (`thm64iii_pf` is the old
  statement); Thm 6.4(iv) over `Pt` (`Thm64iv.lean`): `thm64iv_deg` (`deg = 1`) and `thm64iv_galois`
  (`K/ℚ` Galois ⇒ `K ≅ L`), with Chebotarev replaced by `NumberField.infinite_setOf_splitsCompletely` and
  Bauer's theorem `NumberField.le_of_splitsCompletely` (LCFT `KroneckerDensity`). MR9 plan: `Plans/MR9Plan.md`.
* 2026-10-18: `GlobalPrimeZ.lean` (`primeEquivZ : Prime(Φ(F)) ≃ V(F)`, `primeRlf`, `primeRlf_bijective`,
  `supp_finite`); `GlobalRho.lean` (`ρ_v`, volume interpretation); `HodgeTheater/FRlfMod.lean` (global part of
  `F^⊩_mod` from Θ-data). Later the same day: `rhoEquivFin`/`rhoEquivInf` (`ρ_v : Φ_v ≃+ ℝ≥0`), and
  `GlobalFrobenioid.exists_supp_eq` (every finite set of places is a support).

* 2026-10-18 (second MR9 lead session, subagent): **IUT III Ex 3.6(iii) both halves**
  (`Frobenioid/GlobalUnique.lean`): "identity on `K^×`" as preservation of unit differences
  `u_φ − u_ψ` for equal degrees (`InducesIdUnits`, `InducesIdRatFun`); non-uniqueness:
  `GlobalFrobenioid.twist c` (`α ↦ α + div c_α`), `twist_ofModel_ne`, `isEquivalence_twist_ofModel`;
  uniqueness on the realification `C^⊩(K)`: `psiPhi_eq_self`, `degOf_eq_one`,
  `unique_of_inducesIdRatFun : Unique (G ≅ 𝟭)`, `uniqueIso`. Deviation: stated on `C^⊩` rather than
  the perfection, and the non-realified condition is not transported to the realified one.
  **[FrdI] Ex 6.3 over `B(Gal(E/F))^0`** (`Frobenioid/GlobalGalois.lean`): finite divisors as
  invertible fractional ideals (pull-back = extension of ideals), `pbDiv`, `divG`, `pbDiv_divG`,
  `GlobalGaloisFrob F E` with `isFrobenioid`, `ounitsEquiv` (`O^× = O^▷ ≅ μ(L)`), `degG_divG`.
  Open: `Prime(Φ(L)) ≅ V(L)` in this encoding, comparison of the fibre over `G/G` with
  `GlobalFrobenioid F` (fractional ideals ≃ `FinitePlace →₀ ℤ`), realification over `B(G)^0`,
  `deg(σ^*D) = [L:K]·deg D`, then Thm 6.4(iv) over the Galois base.

## 7. Next steps (precise)

1. `FRlfStrip` (shell #8): make it carry `FRlfGlobal D` (move `FRlfGlobal` below `PrimeStrip.lean`'s imports
   by stating it with `Place ↥(fieldOfModuli D.F D.E)` and `Cat.of (GlobalRealified _)` directly). Then
   replace `C`/`equiv_model` and update `HodgeTheater.lean` (`Frlf.C`, `Iso.Crlf`). This is a downstream
   rebuild of the HodgeTheater/ThetaLink/LogLink chain; plan a long build queue.
2. *Done:* IUT III Ex 3.6(ii). Left: Ex 3.6(i) (torsor version `F^⊛_MOD`, via `ArithLineBundle` ↔ torsors
   with local trivialisations) and (iii) (the composite is unique on perfections/realifications; non-unique on
   `F^⊛_mod` itself: twist by `Pic`-type automorphisms). Small: 300–600 lines.
3. [FrdI] Ex 6.3 over the Galois base `B(Gal(F̃/F))^0` (item 4). Design: `G = Gal(F̃/F)` with the Krull
   topology; `Φ(G/H) = ArithDivZ (F̃^H)` (needs `NumberField` on `fixedField H`, open `H`); pull-back along
   `f : G/H → G/H'` (representative `g`, `σ_g : F̃^{H'} → F̃^H`) is `w ↦ e(w|w∘σ)·D(w∘σ)` at finite and
   `v ↦ D(v∘σ)` at infinite places; needs `pb_comp` (multiplicativity of `e` in towers), principal-divisor
   compatibility (`ord_algebraMap`), and FSM-morphisms of `OrbitObj G` being isomorphisms (as in
   `GaloisModel.lean`). Estimate 1–2k lines; then Thm 6.4(iv) over this base follows the `Pt` proof
   objectwise. Pull-back of divisors along `L ⊆ L'` is
   `ord_{w'} = e(w'|w)·ord_w`, which is `GlobalRealified.ord_algebraMap` (`GlobalRho.lean`).
4. The Θ-version `ρΘ_v` (Ex 3.5(ii)): at good `v` it is `ρ_v`; at bad `v` it needs `logΦ(Θ_v)/logΦ(q_v)`
   from the tempered Frobenioid (MR18).
* Conventions to keep in mind: the archimedean coordinate of `ArithDiv` is `−log|·|_v` with `|·|_v` Mathlib's
  `InfinitePlace` absolute value (not squared at complex places; the degree weights by `mult`), and
  `log⊢(p_v) = [v]` at archimedean `v` (`log e = 1`). The local coordinate at finite `w` is `ord_{K_w}`
  (normalised valuation of `K_w`), so `ρ_v(c·[v]) = c/f(w|v)`.

* 2026-10-18 (third lead MR9/MR19 session), `Frobenioid/GlobalGaloisCmp.lean` (iut 43b79b8, 7ab458a):
  * `toZ L : ArithDivG L ≃+ ArithDivZ L` (fractional ideals ↔ `FinitePlace →₀ ℤ`), with
    `toZ_mem_iff` (effective ↔ effective) and `toZ_divG` (div ↔ div).
  * Generic primes `DivMonoid.Prime Φ A` and `primeCongr`.
  * **`primeGalEquiv A : Prime(Φ(G/H)) ≃ V(E^H)`** ([FrdI] Ex 6.3, l.6281–6284).
  * **The fibre over `G/G`**: `fixTopEquiv : F ≃+* E^G`, and `fibreTop : GlobalFrobenioid F ⥤
    GlobalGaloisFrob F E` is `Full` and `Faithful`. Every object over `G/G` lies in its image
    (`fibreTop_obj_mk`), and every endomorphism of `G/G` is the identity.
  * **`degG_pbDiv`: `deg_L(σ^*D) = [L:K]·deg_K(D)`**, from `absNorm_extIdeal`
    (`N(I·O_L) = N(I)^{[L:K]}`) and `sum_mult_comap`.
* Next (MR19 §7 item 3, remaining):
  * **Realification over `B(G)⁰`.** Transport `pbDiv` to coordinates (`toZ ∘ pbDiv σ ∘ toZ⁻¹`)
    and extend it ℝ-linearly on the basis `single w 1` (`Finsupp.lift`). Functoriality and
    preservation of effectivity follow from the integral case. Reflection of effectivity needs
    the supports of `σ^*[w]` to be nonempty and pairwise disjoint: each prime of `O_L` lies over
    exactly one prime of `O_K`. `B^rlf(L) = ℝ·div(L^×)` as in `GlobalRealified.ratFun`.
  * **Thm 6.4(iv) over the Galois base.** Honest form: an equivalence
    `Ψ : C_{F̃₁/F₁} ≌ C_{F̃₂/F₂}` induces an equivalence of the bases (Thm 3.4-type base
    reconstruction, `Thm34Base.lean`) matching `G₁/H₁ ↔ G₂/H₂`. Restricted to the fibres over
    `G/H` (`fibreTop`, generalised from `G/G` to any `G/H` with `End(G/H)` acting), the `Pt`
    results `thm64iv_deg`/`thm64iv_galois` apply objectwise to `L_i = E_i^{H_i}`.

* 2026-10-18 (MR9+MR19 track agent): **realification over `B(G)⁰`** (`Frobenioid/GlobalGaloisRlf.lean`):
  `eZ σ w` (counts of `𝔭_w O_L`; effective, nonzero, pairwise disjoint supports via
  `𝔭_{w₁} + 𝔭_{w₂} = O_K`), `pbR σ` (ℝ-linear extension of the integral pull-back, `pbR_castDiv`,
  `span_castDiv`, `pbR_comp`, `pbR_id`, `pbR_mem_iff`, `pbR_injective`, `pbR_divOf`, `pbR_ratFun`),
  `phiRlfGal`, `bRlfGal` (`ℝ·div(L^×)`), **`GlobalGaloisRlf F E`** with `isFrobenioid`, and
  **`GlobalGaloisFrob.realify : C_{F̃/F} ⥤ C_{F̃/F}^rlf`** ([FrdI] Prop 5.3; `castG = castDiv ∘ toZ`).
* 2026-10-18 (MR9+MR19 track agent, cont.):
  * **Fibres over `G/H`** (`Frobenioid/GlobalGaloisFibre.lean`): `fibre A : GlobalFrobenioid (E^H) ⥤
    GlobalGaloisFrob F E` and `fibreRlf A : GlobalRealified (E^H) ⥤ GlobalGaloisRlf F E` (faithful,
    every object over `G/H` in the image, every base-identity morphism between image objects
    comes from the fibre), compatible with both realifications on objects and morphism components.
  * **Shell #8, global half done**: `FRlfStrip` now carries `glob : FRlfGlobal D` (moved to
    `PrimeStrip.lean`, data only) instead of `C` + the Prop field `equiv_model`; `FRlfStrip.C`
    is an abbreviation; allowlist entry removed.
  * **Thm 6.4(iv) over the Galois base: blocked (decision needed).** The statement needs the
    base equivalence `D₁ ≅ D₂` induced by `Ψ : C_{F̃₁/F₁} ≌ C_{F̃₂/F₂}` ([FrdI] Thm 6.4(iv) cites
    (i) and Cor 4.11(ii): `D` Frobenius-slim and Div-slim). iut's base reconstruction
    (`Thm34.lean`/`Thm34Base.lean`) assumes `HasAllTorsion B` (pre-steps = FSM-morphisms), which
    fails here (`B(L) = L^×` has finite torsion), and `IsSlim D` fails for finite nontrivial
    `G`. Needed: [FrdI] Prop 1.14 / Cor 4.11(ii) route for Frobenioids with `B` of finite
    torsion (the counterexample of `Counterexample.lean` needs all torsion), giving
    `PreservesBase` and preservation of base-identity morphisms; then `fibre`/`fibreRlf` reduce
    (iv) objectwise to `thm64iv_deg`/`thm64iv_galois`. Estimate: 1.5–3k lines.
  * `Frobenioid/GlobalGaloisRlfDeg.lean`: `log_absNorm_eq` (`log N(I) = Σ_w ord_w(I)·log N(𝔭_w)`),
    `degArith_castG` (`deg^arith ∘ castG = degG`), **`degArith_pbR`**
    (`deg^arith_L(σ^* x) = [L:K]·deg^arith_K(x)` for ℝ-divisors).
* **Hand-off 2026-10-18 (MR9+MR19 track agent).** Merged: a9408f4 (MR9 SurfaceIndex), 76a32cd
  (realification over `B(G)⁰`), a7f08bf + 9c7fb4f (FRlfStrip/FRlfGlobal; fibres), 55bd45e
  (`degArith_pbR`). No WIP branch. Next, in order:
  1. Decision needed (lead): base reconstruction for global Frobenioids (`B` with finite torsion),
     i.e. [FrdI] Cor 4.11(ii)/Prop 1.14 route, as the prerequisite of Thm 6.4(iv) over the Galois
     base (see the entry above). Alternative stop-gap: state (iv) over the Galois base for
     equivalences that preserve base-identity morphisms (explicit, recorded hypothesis), reducing to
     `thm64iv_deg`/`thm64iv_galois` via `fibre`/`fibreRlf`.
  2. `Iso.Crlf` of `ThetaPmEllNFHT.Iso` (`HodgeTheater.lean`) could be required to respect
     `glob.prime`/`glob.rho`; the `ρ_v` should land in the `F^⊢`-strip components once MR20 has
     genuine `C^⊢_v`.
  3. Θ-version `ρΘ_v` (needs MR18); κ-coric items after MR9 `recFunctionField`.

* 2026-10-18 (MR9+MR19 track agent, next session; lead decision: no base-identity hypothesis):
  **Base reconstruction for `C^rlf` over `B(Gal(F̃/F))⁰` and [FrdI] Thm 6.4(iv) over the Galois base.**
  * `Frobenioid/Thm34Irr.lean`: [FrdI] Thm 3.4(ii),(iii) for model Frobenioids over bases with
    irreducible factorizations (`IrredBase`; `OrbitObj.irredBase` for compact `G`) and divisor
    monoids without irreducibles: `isPreStep_iff_midAdj` (pre-steps = mid-adjoint to the
    irreducibles, cf. Prop 1.14(i),(ii)), `typeCorresp_irr`, `thm34_irr`. No torsion hypothesis.
  * `Frobenioid/Thm34DivSlim.lean`: [FrdI] Cor 4.11(ii) for model Frobenioids over a Div-slim base:
    order isomorphisms `τ_X` on pre-step classes, `Compat` (base-isomorphisms vs `τ`),
    `base_map_eq_of_base_eq_divSlim`, `preservesBase_divSlim`. Hypotheses `GoodDiv` (chain-primes
    stable under `n·`, Riesz, archimedean) and `AutFaithful` (Div-slimness).
    `Thm34Base.preservesBase_of` now generic.
  * `Frobenioid/GlobalGaloisBase.lean`: `GlobalGaloisRlf.preservesBase`, `.thm34`, `.base_map_eq`;
    Div-slimness from `eq_id_of_map_le` (an endomorphism of a number field mapping every prime into
    itself is the identity: degree-one primes, LCFT `infinite_degOnePrimes`) and
    `eq_id_of_sigma_eq` (infinite Galois theory). Merged: iut d0b54ae.
  * `Frobenioid/ModelFib.lean`: fibres `Fib Φ B divB A` of model Frobenioids, restriction
    `resFib Ψ G η` of a base-preserving functor (an equivalence when `Ψ` is and `G` is fully faithful).
  * `Frobenioid/Thm64ivGal.lean`: **`GlobalGaloisRlf.thm64iv`**: for `Ψ^rlf` arising from `Ψ`
    (`e : realify ⋙ Ψ^rlf ≅ Ψ ⋙ realify`), `Ψ^rlf` lies over an equivalence `Ψ_Base`, and for every
    `A = G₁/H` the fibre restriction `G_A : C^rlf(L₁) ≌ C^rlf(L₂)` (`G_A ⋙ fibreRlf ≅ fibreRlf ⋙ Ψ^rlf`)
    has `deg = 1`, `[L₁:ℚ] = [L₂:ℚ]`, and `L₁ ≅ L₂` if `L₁/ℚ` is Galois. The base of `Ψ` is derived
    from that of `Ψ^rlf` through `e` (`baseIsoOfRealify`), so no base reconstruction for the
    non-realified `C` (finite torsion) is needed.
  * Not done: compatibility of `L₁ ≅ L₂` with an isomorphism `F₁ ≅ F₂` (Mochizuki's last clause);
    base reconstruction for the non-realified `C_{F̃/F}` on its own (only via `e`).
