# VCI-CHECK: the log-volume of `VC(I)` and of `hull(VC(I))` (`VcI.lean`)

Question: what is `log-vol(VC(I))`, the right-hand side of the (former) Scholze–Stix inequality
`(s − 1)·|log q| ≤ logVol D (vcI D)` (now `Wall.SSIneqNoHull D`), in terms of local data? What is
`log-vol(hull(VC(I)))`? Which of the two is the container volume of IUT, and is the Lean
normalization faithful to IUT III, Proposition 3.9 and IUT IV, Proposition 1.2?

Labels: **[Lean]** proved in `Iut/WallEquiv/VcI.lean`;
**[paper]** computed here, not formalized; **[lit]** read in the IUT texts (IUT III:
`review-iut3/iut3.txt`, the RIMS preprint with printed page numbers; IUT IV:
`iut-scratch/proofmap/iut4.txt`, version of April 2020, printed page numbers).

## 0. Verdict

**Switched (Christian's decision).** `Wall.SSIneq D` is now
`(s − 1)·|log q| ≤ logVol D (hullOf D (vcI D))`, and the (Ind3)-choices are the adelic regions
`S ⊆ hull(VC(I))` (`Iut/Wall/Ind3.lean`, a documented deviation from [LANA], §6). The former
wall is `Wall.SSIneqNoHull D` (`(s − 1)·|log q| ≤ logVol D (vcI D)`; numerically false on many
Szpiro-record curves, not IUT's container), with `ssIneq_of_noHull : SSIneqNoHull D → SSIneq D`.
The archimedean container is **not** changed (see §2(e)).

* **IUT's container volume is the hull.** `−|log(Θ)|` in IUT III, Corollary 3.12 is the
  log-volume of the *holomorphic hull* of the union of possible images (proof of Cor. 3.12,
  Step (xi-d)–(xi-f), pp. 183–184), and IUT IV, Theorem 1.10 bounds "the component of the
  log-volume of the holomorphic hull" (Step (v), p. 27–28). The matching Lean quantity is
  `logVol D (hullOf D (vcI D))`, not `logVol D (vcI D)`.
* **The normalization is faithful.** Measuring regions against the maximal order `(R_I)^∼` of
  the packet is IUT III, Prop. 3.9(i) (p. 115) and IUT IV, Prop. 1.4(i) (p. 13). The tensor
  product of the log-shells is IUT's own container: IUT IV, Theorem 1.10, Step (v)
  (p. 27) uses `p^{⌊λ⌋−|I|}·2^{−|I|}·log_p(R_I^×) = p^{⌊λ⌋}·⊗_j (2p)⁻¹log_p(𝓞_j^×)`, and the
  `(2p)⁻¹` agrees with the factor `(p*)⁻¹` of IUT III, Def. 1.1(i) (p. 24) up to a unit. The
  identity `μ^log(⊗𝓘) = ∑_j μ^log(𝓘_j) + μ^log(R_I)` is written out in the proof of IUT IV,
  Prop. 1.4(iii) (p. 14). Its packet term is `μ^log(R_I) = −log[(R_I)^∼ : R_I]/[T:ℚ_p]`, which
  is `≤ 0`. IUT only uses `μ^log(R_I) ≤ 0`, because it only needs upper bounds.
* **So `vcI` itself is faithful, but it is not the quantity IUT bounds.** `log-vol(VC(I))` is
  smaller than `log-vol(hull(VC(I)))` by the average weighted *shell defects*. At a tame prime the
  shell defect is **exactly** the packet index term `−μ^log(R_I)` [Lean]. On paper this is
  `½·(d_I − d_T)·log p`: one half of the log-different for every tensor factor but one (e.g.
  `((m−1)/2)·d_w·log p` for `K_w^{⊗m}`, `K_w/ℚ_p` Galois). At `∞` the defect is
  `log(N!)/(2N)`, with `N` the number of complex components.
* **Consequence for SSIneq.** With `vcI`, the packet index terms enter `SSIneq` with a negative
  sign, of the same order as the main term. This is the `−((ℓ+1)/8)·Σ_p δ_p` term of
  `idea6.md`, §7, Thm G. With `hull(VC(I))` the prime contribution at tame primes is exactly
  `d_I·log p` per packet [Lean, with `d = 1 − 1/e` for tame `e`]. This is the leading term
  `(ℓ+5)/4·log(d^K)` of IUT IV, Thm 1.10.

## 1. What is proved in Lean (`Iut/WallEquiv/VcI.lean`)

Notation: a packet `T = ⊗_j K_{c j}` over `ℚ_p`, all places over `p`, with `n = [T : ℚ_p]`.
`R_I = ⊗_{ℤ_p} 𝓞_{c j}` is `order`, `(R_I)^∼` is `integral`, and `⊗𝓘` is `tensorLogShell`
(= `LocalTheory.shell`). `μ^log = componentVol` is normalized by `(R_I)^∼`, and `hull` is
`LocalTheory.leastHull`.

### Global reduction

| Lean name | statement |
|---|---|
| `logVol_vcI_eq` | `logVol D (vcI D) = (∑_i ∑ᶠ_{v_ℚ} vcIPacket D i v_ℚ)/ℓ*`, `vcIPacket = ∑_c w_c·μ^log(vcIComp)` |
| `ssIneqNoHull_iff_packets` | `SSIneqNoHull D ↔ (s−1)·|log q| ≤ (∑_i ∑ᶠ vcIPacket)/ℓ*` |
| `ssIneq_iff_packets` | `SSIneq D ↔ (s−1)·|log q| ≤ (∑_i ∑ᶠ hullPacket)/ℓ*` (after the switch) |
| `logVol_hull_vcI_eq` | `logVol D (hullOf D (vcI D)) = (∑_i ∑ᶠ hullPacket)/ℓ*`, `hullPacket = ∑_c w_c·μ^log(hull(vcIComp))` |
| `logVol_hull_vcI_sub_eq` | `logVol(hull VC(I)) − logVol(VC(I)) = (∑_i ∑ᶠ defectPacket)/ℓ*`, with `shellDefect` at primes and `archDefect` at `∞` |
| `logVol_vcI_le_hull`, `defectPacket_nonneg` | `logVol(VC(I)) ≤ logVol(hull VC(I))` |
| `vcIPacket_finite` | `vcIPacket D i p = ∑_c w_c·(shellExcess + orderVol)` |
| `hullPacket_finite` | `hullPacket D i p = ∑_c w_c·∑_j ρ_{c j}·log p` (**exact, every prime**) |
| `vcIPacket_tame`, `hullPacket_tame` | at `IsTamePrime D p` (`p` odd, all `e_w ≤ p−2`): `∑_c w_c·(∑_j (1−1/e_{c j})·log p + orderVol)`, resp. `∑_c w_c·∑_j (1−1/e_{c j})·log p` |
| `defectPacket_tame` | at a tame prime: `defectPacket = −∑_c w_c·orderVol(c)` |
| `defectPacket_tame_le` | at a tame prime: `defectPacket ≤ ∑_c w_c·d_{I,c}·log p` |

### Local terms at a prime

| Lean name | statement |
|---|---|
| `orderVol` | `μ^log(R_I)` (the packet index term) |
| `orderVol_nonpos` | `μ^log(R_I) ≤ 0` |
| `neg_sum_differentExponent_mul_log_le_orderVol` | `−d_I·log p ≤ μ^log(R_I)` (IUT IV, Prop. 1.1) |
| `orderVol_eq_zero` | `= 0` at odd primes unramified in every factor |
| `shellExcess` | `log(μ(⊗𝓘)/μ(R_I))/n` (`⊗𝓘` against `⊗𝓞`) |
| `componentVol_tensorLogShell_eq` | **`μ^log(⊗𝓘) = shellExcess + μ^log(R_I)`** |
| `neg_sum_ordp_scalA_mul_log_le_shellExcess`, `shellExcess_le_neg_sum_ordp_scalB_mul_log` | `−ord_p(α)·log p ≤ shellExcess ≤ −ord_p(β)·log p` (sandwich `α·R_I ⊆ ⊗𝓘 ⊆ β·R_I`) |
| `componentVol_leastHull_tensorLogShell_ge`, `_le` | the same bounds for `μ^log(hull(⊗𝓘))` |
| `leastHull_order` | `hull(R_I) = (R_I)^∼` |
| `logShellRadius`, `exists_isGreatest_logShellRadius` | `ρ_w = −min{ord_p z : 0 ≠ z ∈ 𝓘_w}`, attained (so `𝓘_w ⊆ p^{−ρ_w}·𝓞_w`, sharply) |
| `leastHull_tensorLogShell_eq` | `hull(⊗𝓘) = (⊗_j y_j)·(R_I)^∼` for `y_j ∈ 𝓘_j` of maximal norm |
| `componentVol_leastHull_tensorLogShell_eq` | **`μ^log(hull(⊗𝓘)) = ∑_j ρ_{c j}·log p`** |
| `abs_shellDefect_add_orderVol_le` | `|shellDefect + μ^log(R_I)| ≤ ∑_{j: e_j > p−2} (3 + log e_j)` |
| `ordp_scalA_tame`, `ordp_scalB_tame` | tame: `ord_p((2p)⁻¹ϖ_a) = ord_p((2p)⁻¹ϖ_b) = 1/e − 1` |
| `shellExcess_eq_tame` | tame: `shellExcess = ∑_j (1 − 1/e_j)·log p` |
| `componentVol_tensorLogShell_eq_tame` | tame: **`μ^log(⊗𝓘) = ∑_j (1 − 1/e_j)·log p + μ^log(R_I)`** |
| `componentVol_leastHull_tensorLogShell_eq_tame` | tame: **`μ^log(hull(⊗𝓘)) = ∑_j (1 − 1/e_j)·log p`** |
| `shellDefect_eq_neg_orderVol_tame` | tame: **`shellDefect = −μ^log(R_I) = log[(R_I)^∼ : R_I]/n`** |

### At `∞`

`componentVol_archLogShell_le_leastHull_le`: `μ^log(𝓘_∞) ≤ μ^log(hull 𝓘_∞) ≤ |I|·log(√2·π)`.

### Named propositions (stated, not proved)

* `ShellExcessAdditive p c : shellExcess p c = ∑_j factorShellVol (c j)`, where
  `factorShellVol w p = log(μ(𝓘_w)/μ(𝓞_w))/[K_w:ℚ_p]` is the factor log-volume. Proof idea: if
  `𝓘_j = g_j(𝓞_j)` with `g_j ∈ GL(K_j/ℚ_p)`, then `⊗𝓘 = (⊗g_j)(⊗𝓞)` and
  `det(⊗_j g_j) = ∏_j det(g_j)^{n/n_j}`. The repository has
  `factorShellVol = (log p/e)·logShellConst p f e m = log p* − (1/e + m/[K_w:ℚ_p])·log p`
  (`Reconstruction.logVolume_logShell_completionAt`, [AbsTopIII] Prop. 5.8(iii)). IUT IV uses
  the same additivity in the proof of Prop. 1.4(iii), p. 14. In the tame case both sides equal
  `∑_j (1−1/e_j)·log p` (the left side by `shellExcess_eq_tame`; the right side on paper, since
  `𝓘_w = 𝔪^{1−e}` and `m = 0`).
* `PacketIndexFormulaGalois p w hw m`: if `K_w/ℚ_p` is Galois, then
  `μ^log(R_I) = −((m−1)/2)·d_w·log p` for the packet `K_w^{⊗m}`.

## 2. Paper computations

**(a) Packet index term [paper].** The trace form of `A ⊗ B` is the Kronecker product, so
`disc(⊗_j 𝓞_j) = ∏_j disc(𝓞_j)^{n/n_j}`. Since `[(R_I)^∼ : R_I]² = disc(R_I)/disc((R_I)^∼)`,

  `μ^log(R_I) = −½·(∑_j d_j − d_T)·log p`,  `d_T = (1/n)·∑_{L | T} [L:ℚ_p]·d_L`,

where `L` runs over the field factors of `T` and `d` denotes the different exponent with
`ord(p) = 1`. Each `L` contains every `K_j`, so `d_T ≥ max_j d_j` and
`0 ≤ −μ^log(R_I) ≤ ½·(d_I − max_j d_j)·log p`. This bound is sharper than the Lean bound
`−μ^log(R_I) ≤ d_I·log p`. For `K_w^{⊗m}` with `K_w/ℚ_p` Galois, `T ≅ K_w^{n^{m−1}}`, so
`d_T = d_w` and `μ^log(R_I) = −((m−1)/2)·d_w·log p` (checked numerically for ℚ(i), ℚ(ζ₃), ℚ(ζ₅),
ℚ(ζ₇) in `idea6/packet_index_check.out`).

**(b) The prime component of `VC(I)` [Lean + paper].** By `componentVol_tensorLogShell_eq`,
`ShellExcessAdditive` and (a):

  `μ^log(⊗𝓘) = ∑_j λ_j − ½·(d_I − d_T)·log p`, with `λ_w = log p* − (1/e_w + m_w/[K_w:ℚ_p])·log p`.

At a tame prime the formula is `∑_j (1 − 1/e_j)·log p − ½·(d_I − d_T)·log p`. Everything except
the value of `μ^log(R_I)` is in Lean. In the Galois case `K_w^{⊗m}` with tame `e`:
`((m+1)/2)·(1 − 1/e)·log p`.

**(c) The prime component of `hull(VC(I))` [Lean].** It is `∑_j ρ_j·log p` exactly. At a tame
prime, `ρ_j = 1 − 1/e_j = d_j`, so the component is `d_I·log p`. There the hull is IUT IV's
container `p^{−d_I}·(R_I)^∼` exactly (IUT IV, Prop. 1.4(iii) with `λ = 0`, `I* = ∅`; IUT's
bound `(d_I + 1)·log p` adds 1 for the rounding `⌊λ − d_I − a_I⌋`). In general
`ρ_w ≤ 1 + ord_p 2 + b_w` (Prop. 1.2(i)).

**(d) The shell defect [Lean + paper].**

  `shellDefect = (∑_j ρ_j·log p − shellExcess) − μ^log(R_I)`.

The first bracket vanishes at tame primes (`shellDefect_eq_neg_orderVol_tame`) and has absolute
value at most `∑_{e_j > p−2} (3 + log e_j)` in general. So the shell defect is
`½·(d_I − d_T)·log p + O(∑_{I*}(3 + log e_j))`.

**(e) `∞` [paper].** `T = ℂ^{⊗m} ≅ ℂ^N` with `N = 2^{m−1}`, a similarity of ratio `√N` (IUT IV,
Prop. 1.5(i),(iii), p. 15). The log-shell (IUT III, Prop. 3.2(ii), pp. 98–99: the unit ball of the
tensor-product Hermitian metric, the factors' discs of radius `π`) is a Euclidean ball of radius
`√N·π^m` in `ℝ^{2N}`, and `B_I` is the product of `N` unit discs. Hence

  `μ^log(𝓘_∞) = m·log π + ½·log N − log(N!)/(2N)`,  `μ^log(hull 𝓘_∞) = m·log π + ½·log N`,
  `archDefect = log(N!)/(2N)`.

For `m = 2, …, 6`:

| m | `μ^log(𝓘_∞)` | `μ^log(hull 𝓘_∞)` | `archDefect` | IUT IV bound `m·log π` | Lean bound `m·log(√2π)` |
|---|---|---|---|---|---|
| 2 | 2.4627 | 2.6360 | 0.1733 | 2.2895 | 2.9826 |
| 3 | 3.7301 | 4.1273 | 0.3973 | 3.4342 | 4.4739 |
| 4 | 4.9559 | 5.6186 | 0.6628 | 4.5789 | 5.9652 |
| 5 | 6.1514 | 7.1099 | 0.9585 | 5.7236 | 7.4565 |
| 6 | 7.3269 | 8.6012 | 1.2743 | 6.8684 | 8.9478 |

**Deviation at `∞` (within IUT).** IUT IV, Thm. 1.10, Step (vii) (pp. 29–30) uses the container
`π^{j+1}·B_I`. It contains the *elementary* tensors of log-shell elements (Prop. 1.5(iv)), but
not the whole unit ball of IUT III, Prop. 3.2(ii). The repository follows Prop. 3.2(ii). Its
hull exceeds IUT's bound by `½·log N = ((m−1)/2)·log 2` per packet; after procession averaging
this is about `((ℓ+1)/8)·log 2`. The deviation makes the right-hand side larger, i.e. it favours
`SSIneq`. Its size is `O(ℓ)`, against `Θ(ℓ·log q)` for the main terms.

**Decision (kept).** The repository keeps the archimedean log-shell of IUT III, Prop. 3.2(ii)
(the unit ball of the tensor-product metric) and does not switch to IUT IV's `π^{j+1}·B_I`. This
is conservative: the larger container only enlarges the right-hand side of `SSIneq`, so it can
only weaken the inequality (make it easier to satisfy), by `((m−1)/2)·log 2` per packet of `m`
factors, i.e. about `((ℓ+1)/8)·log 2` after procession averaging; a refutation of `SSIneq`
with this container would a fortiori refute it with IUT IV's.

## 3. Faithfulness: the discrepancy as a formula

Write `Δ_hull(D) := log-vol(hull VC(I)) − log-vol(VC(I)) ≥ 0` (`logVol_hull_vcI_sub_eq`). Then

  `Δ_hull(D) = (1/ℓ*)·∑_i [ ∑_p ∑_c w_c·(½·(d_{I,c} − d_{T_c})·log p + ε_{p,c}) + ∑_c w_c·log(N_i!)/(2N_i) ]`

with `ε_{p,c} = 0` at tame primes [Lean], `|ε_{p,c}| ≤ ∑_{j: e > p−2}(3 + log e_j)` [Lean], and
the first summand [paper, (a)]. The `∞` term uses `N_i = 2^{i+1}` (capsule `i` has `i + 2`
labels). For `F_mod = ℚ` and `K/ℚ` Galois, average over `m = 2, …, ℓ*+1` with
`(1/ℓ*)·∑ (m−1)/2 = (ℓ+1)/8`:

  `Δ_hull(D) = ((ℓ+1)/8)·∑_p δ_p + (wild ε-terms) + (1/ℓ*)·∑_m log(N_m!)/(2N_m)`,  `∑_p δ_p = log rd_K` (finite part),

with `δ_p = d_w·log p`. This is the `−((ℓ+1)/8)·Σ_p δ_p` term of `idea6.md`, Thm G.

So measuring the `ℤ_p`-span of `⊗𝓘` against the maximal order **loses exactly the packet index
term**: `½·(d_I − d_T)·log p` per packet, about ½·log-different for every tensor factor but one.
Taking the hull **recovers it exactly** at tame primes, and up to the `ε`-terms in general. The
loss is not an error of normalization: IUT has the same term (IUT IV, Prop. 1.4(iii), proof:
"`μ^log(R_I) ≤ μ^log((R_I)^∼) = 0`"). IUT never uses the volume of `⊗𝓘` itself; it uses the
volume of the hull.

## 4. Relation to `idea6.md` (§7, Thm G, Cor. G3)

* `idea6.md` §7 flags step "(b) my reading of `tensorLogShell`/`integral`/`componentVol`/
  `processionVol`" as a risk. The reading is **confirmed in Lean**: `logVol_vcI_eq`,
  `componentVol_tensorLogShell_eq` (normalization by the maximal order, `⊗𝓘` the `ℤ_p`-span), and
  at tame primes `vcIPacket_tame` gives `m·(1 − 1/e)·log p + μ^log(R_I)` per packet.
* With (a): for a tame prime in the Galois case the packet is `((m+1)/2)·(1 − 1/e)·log p`. The
  procession average is `((ℓ+9)/8)·d_p·log p`, the "tame coefficient `(ℓ+9)/8`" of Thm G. For
  the hull it is `((ℓ+5)/4)·d_p·log p`, IUT IV's coefficient.
* **What a Lean refutation of `SSIneq D` still needs.** Refuting needs an *upper* bound for
  `logVol(VC(I))`. Lean proves only `μ^log(R_I) ≤ 0` (`orderVol_nonpos`), so the Lean-provable
  upper bound at tame primes is the hull value `d_I·log p` per packet, i.e. the
  ABC-strength (Szpiro ≈ 6) normal form. That cannot be violated by known curves. The
  "Szpiro factor 3" form needs the *upper* bound `μ^log(R_I) ≤ −((m−1)/2)·d_w·log p`, i.e. a
  lower bound for `[(R_I)^∼ : R_I]`. That is `PacketIndexFormulaGalois` (or its `≤` half).
  Further inputs: Lean upper bounds at `p = 2` and the wild primes (available: `shellExcess ≤
  −ord_p(β)·log p`, with `μ^log(R_I) ≤ 0`); at `∞` (available: `≤ |I|·log(√2π)`, weaker than the
  exact value by `≈ (m/2)·log 2 − ½` per packet, which `idea6`'s margins `1.13–1.33` should
  absorb for large `ℓ`, but this is not checked here); and the existence of `D` (`orb`,
  `localData`), as `idea6` says.
* **The hull variant.** `logVol_vcI_le_hull` gives `SSIneqNoHull D ⇒ SSIneq D`
  (`ssIneq_of_noHull`). The hull form is the one whose normal form matches IUT IV, Theorem 1.10.
  By `idea6` §0/§8 it is ABC-strength and not refuted by the `idea6` families. **Decided
  (Christian): `Wall.SSIneq` uses `hullOf D (vcI D)`.**
* Relation to `Gap.lean` (now in Lean): `gapTerm = shellDefect + ind2Term` at primes and
  `= archDefect` at `∞`; `gapNoHull_eq_gap_add : gapNoHull D = gap D + Δ_hull(D)`, and
  `gap_eq : gap D = (1/ℓ*)·∑_i ∑_p ∑_c w_c·ind2Term`. The window between (Var) and the no-hull
  wall contains the whole packet-index loss; after the switch only the (Ind2)-terms remain.

## 5. Open points

1. `PacketIndexFormulaGalois` and the general `μ^log(R_I) = −½(d_I − d_T)·log p` (discriminant
   of a tensor product of orders; needs `disc` of the maximal order of the packet via its field
   factors, `ResidueField.lean`).
2. `ShellExcessAdditive` (determinant of a tensor product of `ℚ_p`-linear maps and the Haar
   modulus `|det|_p`). The tame case is done on the left side (`shellExcess_eq_tame`).
3. The value `ρ_w` in the wild case (`ρ_w = 1 + ord_p 2 − min ord_p log(1+𝔪_w)`), and `λ_w`
   (`logShellConst`) linked to `shellExcess` through 2.
4. The exact archimedean values (`μ^log` of a Euclidean ball against a polydisc, with the `√N`
   similarity) in Lean; only the upper bound `|I|·log(√2π)` and `archDefect > 0`
   (`Gap.lean`) are formalized.
5. ~~Whether `Wall.SSIneq` should be restated with `hullOf D (vcI D)`~~: done (switched).
   After the switch the gap between (Var) and `SSIneq` is the average of the (Ind2)-terms at
   the bad primes only (`Gap.lean`, `gap_eq`); their value is open.
