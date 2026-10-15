# The target of the multiradial track: IUT III, Theorem 3.11 (MR0)

This note fixes the target of the multiradial track (roadmap milestones MR0–MR30): what the
final theorem about IUT III, Theorem 3.11 must say, which Lean types carry its output, and how the
"no shells" requirement is checked. The types are in `Iut/Multiradial/Spec.lean`; the lint is
`scripts/shell_lint.sh`.

Sources: IUT III, Theorem 3.11 and Remarks 3.11.1–3.11.4 (pp. 153–173 of the May 2020 version);
IUT I, §0 (capsules, poly-morphisms), Definition 4.10 and Propositions 4.11, 6.9 (processions);
IUT III, Proposition 3.5(ii) ((Ind3)) and Corollary 3.12, Steps (iv), (x) (possible images).

## 1. The reading of Theorem 3.11 that is formalised

| Phrase of the paper | Lean (`Iut.Multiradial`) |
|---|---|
| input: the procession `Prc(n,∘D⊢_T)` "regarded up to isomorphism" (Thm 3.11(i); Rem 3.11.1(ii), (v)) | an object of the groupoid `Procession C n` (IUT I, Def 4.10; capsule index sets are the naked sets `Fin (j+1)`, Rem 3.11.2(ii)) |
| the data (a), (b), (c) "not yet subjected to (Ind1), (Ind2)" (Thm 3.11(ii)) | `RawOutput G A`: a functor `F : G ⥤ Type` with a natural action of the (Ind2)-group `A` |
| (Ind1): automorphisms of the procession | `Aut P` acting through `F` (`autAction`); every relabelling of the capsules is an automorphism (`Procession.exists_aut_labelPerm`) |
| (Ind2): independent copies of `Ism` (resp. of `ℤ/2` at `V^arc`) on each direct summand of each tensor factor | `Ind2Group ℓ* V Ism = ∏_{j ≤ ℓ*} ∏_{i ≤ j} ∏_{v ∈ V} Ism v`, `IsmFamily`, `Ind2Group.single` |
| `n,∘R^LGP`: the data up to (Ind1), (Ind2) | `MRRep R P`, the orbit type of `RawOutput.Ind12Action` (`Aut P × A`) |
| "an algorithm … functorial with respect to isomorphisms of processions" | `IsFunctorialAlg R alg`: `transport f (alg P) = alg Q` for all `f : P ⟶ Q` |
| (Ind1) makes the output independent of the chosen isomorphism | `MRRep.transport_eq_transport` |
| étale-picture permutation symmetries `Prc(n,∘D⊢_T) ⥲ Prc(n',∘D⊢_T)`, `n,∘R^LGP ⥲ n',∘R^LGP` | `Thm311iShape`; automatic from functoriality (`thm311iShape_of_isFunctorial`, `IsFunctorialAlg.polyIso_compat`) |
| (Ind3): upper semi-compatibility, "⊆" at `V^non`, "↠" at `V^arc` (Thm 3.11(ii); Prop 3.5(ii)(a), (b)) | `UpperSemi R S := S ⊆ R`, `UpperSemiCompatible`, `ind3Possible R = Set.Iic R`, `sUnion_ind3Possible` |
| possible images (Cor 3.12, Steps (iv), (x)) | `MRRep.possibleRegion`, `MRRep.subset_possibleRegion` |
| (ii)(b), (c) only up to roots of unity (Rem 3.11.4(i)) | `ModMu M` (orbits of the torsion units), `ModMu.mem_iff_of_stable` |
| mono-analyticization `D ↦ D⊢` of processions (IUT I, Prop 6.9(ii)) | `Procession.map` |

Points of interpretation, stated so that they can be revisited:

1. A capsule-full poly-isomorphism is the set of all families of component isomorphisms over a
   fixed bijection of index sets. `Procession.Hom` records one member; (Ind1) is the action of all
   automorphisms, so the orbit type is the same as for the poly-morphism.
2. The "j+1 possibilities for the element labelled j" of Remark 3.11.2(ii) are part of (Ind1):
   for processions of isomorphic components every relabelling is induced by an automorphism.
3. At `V^arc` the (Ind2)-copies are the group of order 2 of Proposition 1.2(vii); (Ind3) at
   `V^arc` (surjections) is read on the regions they determine, as in `LogLink/Arch.lean`.
4. Remark 3.11.4's "invisible" indeterminacies of (ii)(b), (c) are the passage to `ModMu`; the
   constructions that use only whole sets (number fields) are insensitive to it.

## 2. The target theorem (MR30, `Iut/Multiradial/Main.lean`)

The only free variable is the initial Θ-data `D : InitialThetaData.{0}` (after MR1). With

* `G := Procession (DVdashStrip D) ℓ±`, the processions of the genuine `D⊢`-prime-strips;
* `A := Ind2Group ℓ* V (IsmFamily Ism)`, with `Ism v` the group of IUT III, Proposition 1.2(vi),
  computed from `D`;
* `R : RawOutput G A` the data (a)–(c) of Theorem 3.11(i), built from the input procession
  (tensor packets and their log-volumes, splitting monoids, `M_MOD`/`M_mod` and their
  Frobenioids),

MR30 must provide `alg : ∀ P, MRRep R P` and prove

* `thm311_i : Thm311iShape R alg (fun n => coricProc D n) (etalePicture D)`;
* `thm311_ii`: the Kummer isomorphisms of the lattice relate the Frobenius-like data of each
  `n,m HT` to a representative of `alg (coricProc D n)`, with (a) `UpperSemiCompatible` along the
  column and compatible with log-volumes, (b) splitting monoids in `ModMu`, (c) `M_MOD` compatible,
  `M_mod` not;
* `thm311_iii`: (a)–(d) compatibility with the Θ×μ_LGP-links.

None of `DVdashStrip`, `coricProc`, `etalePicture`, `Ism`, the lattice or the Kummer isomorphisms
exists yet in genuine form; they are the content of MR16–MR29.

## 3. No shells, checked

* **(L1)** `scripts/shell_lint.sh [MODULE]` lists the `Prop`-valued fields of all structures and
  classes in the import closure of `MODULE` (outside Lean core, Mathlib and its third-party
  dependencies) and compares them with `scripts/shell_lint_allowlist.txt`. Tags: `def` (a
  defining condition of a notion, allowed), `shell` (ROADMAP §5, must disappear), `statement`
  (Prop-structures stating theorems about a model), `baseline` (recorded at MR0, not yet
  classified), `new` (added by `--update`, to be reviewed).
* `.orchestra/validation.sh` runs `scripts/shell_lint.sh --ratchet` on the whole library: it prints
  the baseline counts and fails only when a `Prop` field appears that is not in the allowlist. A
  new defining condition is added with the tag `def` in the same change.
* At MR30 the check is `scripts/shell_lint.sh --report Iut.Multiradial.Main` with no `shell`,
  `statement` or `baseline` entry left in that closure, together with the existing dependency
  audit (only `propext`, `Classical.choice`, `Quot.sound`).
* **(L2)**, **(L3)** (no IUT-constructed data as input; no field stand-ins for Frobenioids) are
  checked by review of the signature of `alg` and of the instance of `RawOutput`: the only
  argument is `D`.

Baseline at MR0 (closure of `Iut`, origin/main `cdc9602` plus `Spec.lean`): 917 entries, of which 128 `def`,
35 `shell`, 60 `statement`, 694 `baseline`.

## 4. MR1 (genuine initial Θ-data): done outside the trusted closure, and what is left

The structures `InitialThetaData`, `LocalThetaData` and the predicate `IsThetaRootModel` lie in the
trusted import closure of the comparator challenge (`Comparator/Challenge.lean` imports
`Iut.Concrete.ThetaRegion`). MR1 therefore changes none of them. Done:

* `Iut/Anabelian/CoreOfJ.lean`: the core condition `HasCoreUniversally F E` of IUT I,
  Definition 3.1(d) is derived from [CanLift], Proposition 2.7 (`canLift27`) for non-exceptional
  `j(E)` (`hasCoreUniversally_of_j`); `EllipticCurveData.thetaDataOfJ` is the existence
  construction with this built in (shell #39 reduced to the elementary condition on `j`).
* `Iut/Multiradial/ThetaData.lean`: decomposition groups as stabilizers of primes of the integral
  closure (`IsDecompositionGroup`, closed: `IsDecompositionGroup.isClosed`); genuine Θ-data
  (`HasGenuineDecomp`) and the genuinization `D.withGenuineDecomp` with
  `InitialThetaData.decomp_eq`; the existence construction is genuine
  (`EllipticCurveData.thetaData_hasGenuineDecomp`); the comparator hypothesis is equivalent to its
  restriction to genuine Θ-data (`cor312VariantHolds_iff_genuine`,
  `cor312LiteralHolds_iff_genuine`).

Left (needs a decision, because it changes the trusted closure):

1. Shells #6, #38: replace the field `LocalThetaData.decomp` (and `decomp_isClosed`) by the
   definition `decompGroup`. By `cor312VariantHolds_iff_genuine` the challenge hypothesis keeps
   its meaning, but the text of `Cor312/ThetaData/LocalConditions.lean` (trusted) changes.
2. Shell #37: `IsThetaRootModel` as [EtTh] Definition 2.5 / 2.1 on the genuine objects: a quotient
   `Π^ell_X ↠ Q` of the genuine fundamental group of rank one over `ℤ/ℓ`, surjective on
   `Δ^ell_X`, trivial on the cuspidal decomposition group, factoring through the tempered graph
   quotient `Π^tp_X ↠ ℤ`, with the splitting compatible with the `{±1}`-structure of [EtTh],
   Theorem 1.10(iii). This needs the identification `Δ^ell_X ≅ E[ℓ]` for the genuine π₁ of the
   model orbicurves, the graph quotient of the tempered π₁ of the Tate curve restricted to
   `E[ℓ]` (kernel `μ_ℓ`), and [EtTh] Theorem 1.10(iii) — milestones MR13/MR14 — and it also
   changes `Anabelian/Local.lean` (trusted).
