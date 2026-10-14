/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Wall.Checks

/-!
# The wall on the identified-copies model (the wall, Milestone 1d (iii))

The **identified-copies model** (Scholze–Stix, as described in [LANA], §10.2–§10.3, and
roadmap v1, §3, step 3): all Hodge theaters are identified with one, and the η-algorithm is
computed in the single ring structure of `D` — the output `LGP·S` is the image of the
(Ind3)-choice `S ⊆ hull(VC(I))` under multiplication by the theta values `q_{v_j}^{j²}` placed in
the `j`-th tensor factor of the capsule `S_{j+1}` ([LANA], §5.2(f), §6.2(h), (i); IUT IV,
proof of Theorem 1.10, Steps (iv)–(v)).

* `lgp D S`: the region `LGP·S` (theta value at the label `j`, IUT IV's reading);
* `idAlg D`: the η-algorithm of the model, `out ι S = LGP·S` for every choice `ι`. It is an
  admissible `EtaAlg D` — (T1), (T2) trivially, (T3) because `LGP·S` lies in the hull of the
  theta-pilot region with the theta values at the labels `j` (`inHullOfImage_lgp`; for
  `S ⊆ VC(I)` even in the region itself, `inImage_lgp`) — and it satisfies the LGP
  law (T4) (`idAlg_lgpLaw`), so it is **not** the trivial instance (`idAlg_not_isTrivial`).

**What is proved.**

* `logVol_lgp`: `log-vol(LGP·S) = log-vol(LGP·O) + log-vol(S)` (the theta values are units,
  which scale Haar measure by a fixed modulus);
* `logVol_lgp_integral`: **`log-vol(LGP·O) = −s·|log(q)|`**, with the scale factor
  `s = (1² + ⋯ + (ℓ*)²)/ℓ*` of [LANA], §7.1(a) (`sFactor`): the procession-normalized
  log-volume of `q_{v_j}^{j²}·O` is the average over the capsules of `−j²·|log(q)|`. This uses
  the computation of `μ^log` of elementary scalings (IUT IV, Proposition 1.4,
  `componentVol_prod_incl_smul_integral`) and the comparison of the `V`-indexed sum of
  `ord_p(q_v)` with `log(q)` (`InitialThetaData.logQAt_eq_sect`);
* **`wall_idAlg_iff`: `Wall D (idAlg D) ↔ (s − 1)·|log(q)| ≤ log-vol(hull(VC(I)))`.** The wall
  on the identified-copies model is *exactly* the numerical inequality of the Scholze–Stix hexagon
  ([LANA], §10.2: "the composition `R_{⊙,Θ} → R_Θ` scales by a factor of `s`"): the left-hand
  side grows like `(ℓ*²/3)·|log(q)|`, the right-hand side is the log-volume of the hull of the
  log-shell container. That this inequality fails in the situations needed for ABC is the
  Scholze–Stix claim; it is **not** proved here (neither the inequality nor its negation is a
  theorem of this repository). What is proved is that, in this model, the wall *is* that inequality.
* `idAlg_wall_imp`: in this model the wall still implies the variant (as for every
  `EtaAlg`), through `−|log(q)| ≤ log-vol(LGP·hull(VC(I))) ≤ −|log(Θ)|`.

**Which field forbids the collapse?** None. The identified-copies algorithm satisfies every
field of `EtaAlg` and (T4); (T2) (dependence only on the étale-unit portion) is satisfied
because the model's output does not depend on the input at all. So the interface does not
distinguish the identified-copies model from the algorithm IUT intends; what would
distinguish them is a *specification* of `out` as a function of the Θ-side Hodge theater
(the provenance of [LANA], §10.3), which only the construction of the algorithm (roadmap
Milestones 2–3) can supply.
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace LocalConstruct

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] {p : Nat.Primes}
  {c : ι → Place K}

/-- Multiplication by a unit scales the Haar log-volume: `μ^log(a·X) = μ^log(a·O) + μ^log(X)`. -/
theorem componentVol_units_smul {a : Tensor K (.finite p) c} (ha : IsUnit a)
    {X : Set (Tensor K (.finite p) c)} (hX : 0 < haar (.finite p) c X)
    (hX' : haar (.finite p) c X < ⊤) :
    componentVol (.finite p) c (a • X) =
      componentVol (.finite p) c (a • integralAt (.finite p) c) +
        componentVol (.finite p) c X := by
  obtain ⟨u, rfl⟩ := ha
  have hO : integral p c = integralAt (.finite p) c := rfl
  rw [← hO, componentVol_units_smul_integral]
  unfold componentVol
  rw [haar_units_smul, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc,
    Real.log_mul (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
      (div_pos (ENNReal.toReal_pos hX.ne' hX'.ne) toReal_haar_integralAt_pos).ne', add_div]

/-- Multiplication by a unit preserves admissibility. -/
theorem units_smul_mem_admissible {a : Tensor K (.finite p) c} (ha : IsUnit a)
    {X : Set (Tensor K (.finite p) c)} (hX : X ∈ admissible (.finite p) c) :
    a • X ∈ admissible (.finite p) c := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨hne, hcpt, hmeas, hpos, hfin⟩ := hX
  have hcont : Continuous fun x : Tensor K (.finite p) c => (u : Tensor K (.finite p) c) * x :=
    continuous_const.mul continuous_id
  have himg : (u : Tensor K (.finite p) c) • X = (fun x => (u : Tensor K (.finite p) c) * x) '' X :=
    rfl
  have hcl : IsCompact ((fun x => (u : Tensor K (.finite p) c) * x) '' closure X) :=
    hcpt.image hcont
  have hpre : (u : Tensor K (.finite p) c) • X =
      (fun x => ((u⁻¹ : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) * x) ⁻¹' X := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [← mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [← mul_assoc]⟩
  refine ⟨hne.smul_set, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hcl.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.image_mono subset_closure) hcl.isClosed)
  · rw [hpre]
    exact hmeas.preimage (continuous_const.mul continuous_id).measurable
  · rw [haar_units_smul]
    exact ENNReal.mul_pos (by exact_mod_cast distribHaarChar_pos.ne') hpos.ne'
  · rw [haar_units_smul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end LocalConstruct

namespace Wall

variable (D : InitialThetaData.{u})

/-! ### The region `LGP·S` -/

/-- The LGP element of the packet of capsule `i` at `p`: the theta value `q_{v_j}^{j²}` in the
`j`-th tensor factor of every tuple ([LANA], §5.2(f)). -/
noncomputable def lgpElt (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total :=
  fun c => D.scaleElt (nC D) i p c

/-- Multiplication by the LGP element. -/
noncomputable def lgpMap (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total →
      (LocalTheory.packet D.placeSect (InitialThetaData.Lab (nC D) i) (.finite p)).Total :=
  fun x c => @HMul.hMul (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c))
    (LocalTheory.Tensor D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)) instHMul
    (D.scaleElt (nC D) i p c) (x c)

lemma lgpMap_eq_id (i : Fin (nC D)) (p : Nat.Primes) (hbad : (p : ℕ) ∉ D.badChars) :
    lgpMap D i p = id := by
  funext x c
  have h1 : D.scaleElt (nC D) i p c = 1 := by
    unfold InitialThetaData.scaleElt InitialThetaData.scaleEltAt
    rw [D.qroot_eq_one _ (by rw [LocalTheory.residueChar_sectPlace D.placeSect]; exact hbad),
      one_pow, map_one]
  simp only [lgpMap, h1, one_mul, id]

/-- The packet regions of `LGP·R`. -/
noncomputable def lgpRegion (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    ∀ vQ : RationalPlace, Set ((VC D).packet i vQ).Total
  | .finite p => lgpMap D i p '' R.region (.finite p)
  | .infinite => R.region .infinite

/-- **`LGP·R`** at capsule `i`. -/
noncomputable def lgpAt (i : Fin (VC D).proc.length) (R : (VC D).AdmissibleRegion i) :
    (VC D).AdmissibleRegion i where
  region := lgpRegion D i R
  finiteSupport := by
    refine (R.finiteSupport.union ((D.badChars.finite_toSet.image
      fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite))).subset
      fun vQ hvQ => ?_
    rcases vQ with p | _
    · by_cases hbad : (p : ℕ) ∈ D.badChars
      · exact Or.inr ⟨p, hbad, by simp [p.2]⟩
      · refine Or.inl fun h => hvQ ?_
        change lgpMap D i p '' R.region (.finite p) = _
        rw [lgpMap_eq_id D i p hbad, Set.image_id]
        exact h
    · exact Or.inl hvQ

/-- **The region `LGP·S`** ([LANA], §6.2(i), §9.2: `M = 1·S`). -/
noncomputable def lgp (S : Region D) : Region D := fun i => lgpAt D i (S i)

lemma proj_lgp (S : Region D) (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.proj D.placeSect (.finite p) c ((lgp D S i).region (.finite p)) =
      D.scaleElt (nC D) i p c • LocalTheory.proj D.placeSect (.finite p) c
        ((S i).region (.finite p)) := by
  change (fun x => x c) '' (lgpMap D i p '' (S i).region (.finite p)) = _
  rw [Set.image_image]
  unfold LocalTheory.proj
  rw [← Set.image_smul, Set.image_image]
  rfl

/-- `LGP·S` is adelic for adelic `S`. -/
theorem isAdelic_lgp {S : Region D} (hS : IsAdelic D S) : IsAdelic D (lgp D S) := by
  intro i vQ
  rcases vQ with p | _
  · obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    refine ⟨fun c => D.scaleElt (nC D) i p c • fam c, fun c =>
      LocalConstruct.units_smul_mem_admissible (D.isUnit_scaleElt _ i p c) (hfam c), ?_⟩
    change lgpMap D i p '' (S i).region (.finite p) = _
    rw [hR]
    ext x
    simp only [DirectSumPresentation.mem_productRegion, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact ⟨y c, hy c, rfl⟩
    · intro hx
      choose y hy hxy using hx
      exact ⟨y, hy, funext hxy⟩
  · exact hS i .infinite

/-- **`LGP·S` lies in the theta-pilot region with the theta values at the labels `j`** (IUT IV's
(Ind1)-image) when `S ⊆ VC(I)`: at a prime, `q^{j²}·S_c ⊆ q^{j²}·⊗𝓘` (the image under the
identity indeterminacy automorphism); at `∞`, `S_c ⊆ 𝓘_∞`. -/
theorem lgp_le_thetaImage {S : Region D} (hS : ∀ i, S i ≤ vcI D i) (i : Fin (nC D)) :
    lgp D S i ≤ thetaImage D (InitialThetaData.distinguished _) i := by
  intro vQ
  rcases vQ with p | _
  · rintro _ ⟨y, hy, rfl⟩ c
    have hyc : y c ∈ LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c) :=
      hS i (.finite p) hy c
    refine Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, ?_⟩
    rw [Set.image_id]
    exact Set.mem_iUnion₂.mpr ⟨_, rfl, ⟨y c, hyc, rfl⟩⟩
  · intro y hy c
    have hyc : y c ∈ LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.placeSect _ c) :=
      hS i .infinite hy c
    change y c ∈ LocalTheory.thetaInfinite D.placeSect (nC D) i c
    exact Set.mem_iUnion₂.mpr ⟨id, LocalTheory.id_mem_indAut D.Kt _ _, by rwa [Set.image_id]⟩

/-- `LGP·S ⊆` an (Ind1)-image of the theta-pilot region for `S ⊆ VC(I)`
(`lgp_le_thetaImage`). -/
theorem inImage_lgp {S : Region D} (hS : ∀ i, S i ≤ vcI D i) : InImage D (lgp D S) :=
  ⟨_, lgp_le_thetaImage D hS⟩

/-- **`LGP·S` lies in the hull of a single (Ind1)-image of the theta-pilot region** for every
(Ind3)-choice `S ⊆ hull(VC(I))`: the hull commutes with the unit scaling `LGP` at a prime
(`mul_mem_of_mem_hull`; `LGP·VC(I)` lies in the image, `inImage_lgp`), and `LGP` is the
identity at `∞` (monotonicity of the hull). -/
theorem inHullOfImage_lgp (S : Ind3 D) : InHullOfImage D (lgp D S.1) := by
  refine ⟨InitialThetaData.distinguished _, fun i vQ => ?_⟩
  have hθ := thetaImage_isAdmissible D (InitialThetaData.distinguished _) i
  have hl := lgp_le_thetaImage D (S := vcI D) (fun _ _ => subset_rfl) i
  rcases vQ with p | _
  · rintro _ ⟨y, hy, rfl⟩
    set H := (LocalTheory.hull D.placeSect (nC D)).system i (.finite p)
    exact mul_mem_of_mem_hull D i p (isAdelic_vcI D i (.finite p))
      (fun c => D.scaleElt (nC D) i p c) (fun c => D.isUnit_scaleElt _ i p c)
      (H.hull_mem_hullRegions (hθ (.finite p)))
      (fun z hz => H.subset_hull (hθ (.finite p)) (hl (.finite p) ⟨z, hz, rfl⟩))
      (S.2.2 i (.finite p) hy)
  · intro y hy
    exact ((LocalTheory.hull D.placeSect (nC D)).system i .infinite).hull_mono
      (isAdelic_vcI D i .infinite) (hθ .infinite) (hl .infinite) (S.2.2 i .infinite hy)

/-! ### The log-volume of `LGP·S` -/

/-- Packetwise, `LGP` shifts the log-volume by the log-volume of `LGP·O`. -/
theorem packetVol_lgp {S : Region D} (hS : IsAdelic D S) (i : Fin (nC D))
    (vQ : RationalPlace) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((lgp D S i).region vQ) =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
          ((lgp D (integralRegion D) i).region vQ) +
        (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ ((S i).region vQ) := by
  rcases vQ with p | _
  · rw [LocalTheory.packetVol_eq, LocalTheory.packetVol_eq, LocalTheory.packetVol_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨fam, hfam, hR⟩ := hS i (.finite p)
    have hpS : LocalTheory.proj D.placeSect (.finite p) c ((S i).region (.finite p)) = fam c := by
      rw [hR, LocalTheory.proj_productRegion D.placeSect _ fam
        (fun c => LocalTheory.admissible_nonempty D.Kt _ _ _ (hfam c))]
    have hpO : LocalTheory.proj D.placeSect (.finite p) c
        ((integralRegion D i).region (.finite p)) =
        LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) :=
      LocalTheory.proj_productRegion D.placeSect _ _
        (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
    rw [proj_lgp, proj_lgp, hpS, hpO]
    change _ * LocalConstruct.componentVol (.finite p) _ (D.scaleElt (nC D) i p c • fam c) =
      _ * LocalConstruct.componentVol (.finite p) _ (D.scaleElt (nC D) i p c •
          LocalConstruct.integralAt (.finite p) _) +
        _ * LocalConstruct.componentVol (.finite p) _ (fam c)
    rw [LocalConstruct.componentVol_units_smul (D.isUnit_scaleElt _ i p c) (hfam c).2.2.2.1
      (hfam c).2.2.2.2]
    ring
  · change (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite ((S i).region .infinite) =
      (LocalTheory.vol D.placeSect (nC D)).packetVol i .infinite
        ((VC D).packet i .infinite).integralRegion + _
    rw [(LocalTheory.vol D.placeSect (nC D)).packetVol_integral, zero_add]

/-- **The LGP law**: `log-vol(LGP·S) = log-vol(LGP·O) + log-vol(S)` for adelic `S`. -/
theorem logVol_lgp {S : Region D} (hS : IsAdelic D S) :
    logVol D (lgp D S) = logVol D (lgp D (integralRegion D)) + logVol D S := by
  unfold logVol LogVolumeData.processionVol
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold LogVolumeData.globalVol
  rw [← finsum_add_distrib ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)
    ((LocalTheory.vol D.placeSect (nC D)).finite_support_packetVol _)]
  exact finsum_congr fun vQ => packetVol_lgp D hS i vQ

/-! ### The log-volume of `LGP·O` is `−s·|log(q)|` -/

/-- `μ^log(q_{v_j}^{j²}·O) = −j²·ord_p(q_{v_j})·log p`. -/
theorem componentVol_scaleElt (i : Fin (nC D)) (p : Nat.Primes)
    (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) :
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (D.scaleElt (nC D) i p c • LocalTheory.integral D.Kt (.finite p)
          (LocalTheory.tuple D.placeSect _ c)) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2 * ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (InitialThetaData.distinguished _ i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect
          (c (InitialThetaData.distinguished _ i))))) * Real.log p := by
  classical
  set j := InitialThetaData.distinguished (nC D) i
  set W := fun l => LocalTheory.sectPlace D.placeSect (c l)
  set y : ∀ l, completionAt D.Kt (W l) := Function.update (fun _ => 1) j
    (D.qroot (W j) ^ (i.1 + 1) ^ 2)
  have hy : ∀ l, y l ≠ 0 := by
    intro l
    by_cases h : l = j
    · subst h
      simp only [y, Function.update_self]
      exact pow_ne_zero _ (D.qroot_ne_zero _)
    · simp only [y, Function.update_of_ne h]
      exact one_ne_zero
  have hprod : (∏ l, LocalConstruct.incl p (LocalTheory.tuple D.placeSect _ c) l (W l)
      (LocalTheory.tuple_finite D.placeSect c l) (y l)) = D.scaleElt (nC D) i p c := by
    rw [Finset.prod_eq_single j]
    · simp only [y, Function.update_self]
      rfl
    · intro l _ hl
      simp only [y, Function.update_of_ne hl, map_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hsum : ∑ l, ordp D.Kt (W l) (y l) =
      ((i.1 + 1 : ℕ) : ℝ) ^ 2 * ordp D.Kt (W j) (D.qroot (W j)) := by
    rw [Finset.sum_eq_single j]
    · simp only [y, Function.update_self]
      rw [LocalTheory.ordp_pow D.Kt _ _ (D.qroot_ne_zero _)]
      push_cast
      ring
    · intro l _ hl
      simp only [y, Function.update_of_ne hl]
      simp [ordp, norm_one]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have := LocalConstruct.componentVol_prod_incl_smul_integral
    (LocalTheory.tuple_isOver D.placeSect p c) W (LocalTheory.tuple_finite D.placeSect c) y hy
  rw [hprod, hsum] at this
  exact this

/-- The packet log-volume of `LGP·O` at `p` is `−j²·log(q_p)/(2ℓ)`. -/
theorem packetVol_lgp_integral_finite (i : Fin (nC D)) (p : Nat.Primes) :
    (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p)
        ((lgp D (integralRegion D) i).region (.finite p)) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2) * ((concreteVariantData D).logQAt p / (2 * D.ℓ)) := by
  rw [LocalTheory.packetVol_eq]
  have hpO : ∀ c, LocalTheory.proj D.placeSect (.finite p) c
      ((integralRegion D i).region (.finite p)) =
      LocalTheory.integral D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c) := fun c =>
    LocalTheory.proj_productRegion D.placeSect _ _
      (fun c => ⟨1, LocalTheory.one_mem_integral D.Kt _ _⟩) c
  have hc : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.proj D.placeSect (.finite p) c
          ((lgp D (integralRegion D) i).region (.finite p))) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2 * ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (InitialThetaData.distinguished _ i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect
          (c (InitialThetaData.distinguished _ i))))) * Real.log p := by
    intro c
    rw [proj_lgp, hpO]
    exact componentVol_scaleElt D i p c
  simp only [hc]
  have hℓ : (D.ℓ : ℝ) ≠ 0 := by
    have := D.prime.five_le
    change (D.prime.ℓ : ℝ) ≠ 0
    exact_mod_cast (by omega : D.prime.ℓ ≠ 0)
  rw [InitialThetaData.logQAt_eq_sect]
  have key := sum_prod_tuple_mul_coord (LocalTheory.weight D.Fmod (.finite p))
    (LocalTheory.weight_sum_one D.Fmod _)
    (fun v => ordp D.Kt (LocalTheory.sectPlace D.placeSect v)
      (D.qroot (LocalTheory.sectPlace D.placeSect v))) (InitialThetaData.distinguished _ i)
  have hsplit : ∀ c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p),
      LocalTheory.tupleWeight (.finite p) c * (-(((i.1 + 1 : ℕ) : ℝ) ^ 2 * ordp D.Kt
        (LocalTheory.sectPlace D.placeSect (c (InitialThetaData.distinguished _ i)))
        (D.qroot (LocalTheory.sectPlace D.placeSect
          (c (InitialThetaData.distinguished _ i))))) * Real.log p) =
      (-(((i.1 + 1 : ℕ) : ℝ) ^ 2) * Real.log p) *
        ((∏ l, LocalTheory.weight D.Fmod (.finite p) (c l)) *
          ordp D.Kt (LocalTheory.sectPlace D.placeSect (c (InitialThetaData.distinguished _ i)))
            (D.qroot (LocalTheory.sectPlace D.placeSect
              (c (InitialThetaData.distinguished _ i))))) := by
    intro c
    unfold LocalTheory.tupleWeight
    ring
  rw [Finset.sum_congr rfl fun c _ => hsplit c, ← Finset.mul_sum, key]
  field_simp

/-- The rational places of the residue characteristics of the bad places. -/
noncomputable def badPrimePlaces : Finset RationalPlace :=
  (D.qPilot.badFinset.image residueChar).attach.image fun q =>
    RationalPlace.finite ⟨q.1, by
      obtain ⟨w, -, hw⟩ := Finset.mem_image.mp q.2
      rw [← hw]
      exact Iut.residueChar_prime w⟩

lemma logQAt_eq_zero (p : ℕ) (hp : p ∉ D.qPilot.badFinset.image residueChar) :
    (concreteVariantData D).logQAt p = 0 := by
  unfold Corollary312VariantData.logQAt
  refine Finset.sum_eq_zero fun w hw => ?_
  exfalso
  exact hp (Finset.mem_image.mpr ⟨w.1, w.1.2 |> fun _ => w.2, (Finset.mem_filter.mp hw).2⟩)

/-- The global log-volume of `LGP·O` at capsule `i` is `−j²·log(q)/(2ℓ)`. -/
theorem globalVol_lgp_integral (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).globalVol (lgp D (integralRegion D) i) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2) * (D.qPilot.logQ / (2 * D.ℓ)) := by
  classical
  unfold LogVolumeData.globalVol
  set g := fun vQ => (LocalTheory.vol D.placeSect (nC D)).packetVol i vQ
    ((lgp D (integralRegion D) i).region vQ)
  have hinf : g .infinite = 0 :=
    (LocalTheory.vol D.placeSect (nC D)).packetVol_integral i .infinite
  have hsupp : Function.support g ⊆ ↑(badPrimePlaces D) := by
    intro vQ hvQ
    rcases vQ with p | _
    · by_contra h
      apply hvQ
      change (LocalTheory.vol D.placeSect (nC D)).packetVol i (.finite p) _ = 0
      rw [packetVol_lgp_integral_finite, logQAt_eq_zero D p, zero_div, mul_zero]
      intro hp
      apply h
      simp only [badPrimePlaces, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨p, hp, rfl⟩
    · exact absurd hinf hvQ
  rw [finsum_eq_sum_of_support_subset g hsupp, badPrimePlaces, Finset.sum_image]
  · rw [Finset.sum_congr rfl fun q _ => (packetVol_lgp_integral_finite D i _ :
        g (RationalPlace.finite _) = _),
      Finset.sum_attach (D.qPilot.badFinset.image residueChar)
        (fun q => -(((i.1 + 1 : ℕ) : ℝ) ^ 2) * ((concreteVariantData D).logQAt q / (2 * D.ℓ))),
      ← Finset.mul_sum, ← Finset.sum_div, (concreteVariantData D).sum_logQAt
        (s := D.qPilot.badFinset.image residueChar) (fun w hw => Finset.mem_image_of_mem _ hw)]
    rfl
  · intro p _ q _ h
    have := congrArg Subtype.val (RationalPlace.finite.inj h)
    exact Subtype.ext this

/-- **`log-vol(LGP·O) = −s·|log(q)|`**: the theta values `q^{j²}`, averaged over the capsules
`j = 1, …, ℓ*`, shift the procession-normalized log-volume by `−s·|log(q)|` ([LANA], §7.1(a),
§10.2). -/
theorem logVol_lgp_integral :
    logVol D (lgp D (integralRegion D)) = -(sFactor (nC D) * D.qPilot.absLogQ) := by
  unfold logVol LogVolumeData.processionVol
  simp only [globalVol_lgp_integral]
  rw [← Finset.sum_mul, sFactor, QPilotData.absLogQ]
  have h : ∑ i : Fin (nC D), -(((i.1 + 1 : ℕ) : ℝ) ^ 2) =
      -∑ j ∈ Finset.range (nC D), ((j : ℝ) + 1) ^ 2 := by
    rw [Finset.sum_neg_distrib, Fin.sum_univ_eq_sum_range (fun j => ((j + 1 : ℕ) : ℝ) ^ 2)]
    push_cast
    rfl
  change (∑ i : Fin (nC D), -(((i.1 + 1 : ℕ) : ℝ) ^ 2)) * _ / (nC D : ℝ) = _
  rw [h]
  ring

end Wall

namespace Wall

variable (D : InitialThetaData.{0})

/-! ### The identified-copies η-algorithm -/

/-- **The η-algorithm of the identified-copies model**: one Hodge theater; the output is
`LGP·S`, computed in the ring structure of `D`, for every choice `ι`. -/
noncomputable def idAlg : EtaAlg D where
  model _ := trivialGM
  Side := Unit
  side_nonempty := ⟨()⟩
  etUnit _ := trivialEtUnit _
  out _ S := lgp D S.1
  ind12_acts_on_S _ _ := ⟨Equiv.refl _, fun _ => rfl⟩
  etUnitOnly := ⟨fun _ S => lgp D S.1, fun _ _ => rfl⟩
  realisation _ S := ⟨isAdelic_lgp D S.2.1, inHullOfImage_lgp D S⟩

/-- The identified-copies algorithm satisfies the LGP law (T4), with shift `−s·|log(q)|`. -/
theorem idAlg_lgpLaw : (idAlg D).LGPLaw := fun _ =>
  ⟨logVol D (lgp D (integralRegion D)), fun S => logVol_lgp D S.2.1⟩

/-- The identified-copies algorithm is not the trivial instance. -/
theorem idAlg_not_isTrivial : ¬ (idAlg D).IsTrivial :=
  (idAlg D).not_isTrivial_of_lgpLaw (idAlg_lgpLaw D)

/-- **The wall on the identified-copies model is the Scholze–Stix inequality**:
`Wall D (idAlg D) ↔ (s − 1)·|log(q)| ≤ log-vol(hull(VC(I)))`. -/
theorem wall_idAlg_iff :
    Wall D (idAlg D) ↔
      (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := by
  rw [(idAlg D).wall_iff_of_lgpLaw (fun _ => logVol D (lgp D (integralRegion D)))
    (fun _ S => logVol_lgp D S.2.1), logVol_lgp_integral]
  have hlhs : (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ := rfl
  rw [hlhs]
  constructor
  · intro h
    obtain ⟨_, h⟩ := h () ()
    linarith
  · intro h _ _
    exact ⟨((idAlg D).nonempty_choice () ()).some, by linarith⟩

/-- In the identified-copies model the wall implies the variant, through
`−|log(q)| ≤ log-vol(LGP·hull(VC(I))) ≤ −|log(Θ)|`. -/
theorem idAlg_wall_imp (h : Wall D (idAlg D)) :
    (concreteVariantData D).qPilot.lhs ≤ logVol D (lgp D (hullOf D (vcI D))) ∧
      logVol D (lgp D (hullOf D (vcI D))) ≤ (concreteVariantData D).rhsData.rhs := by
  refine ⟨?_, logVol_le_rhs D (isAdelic_lgp D (isAdelic_hullOf_vcI D))
    (inHullOfImage_lgp D (Ind3.top D))⟩
  rw [logVol_lgp D (isAdelic_hullOf_vcI D), logVol_lgp_integral]
  have := (wall_idAlg_iff D).mp h
  change -D.qPilot.absLogQ ≤ _
  linarith

end Wall

end Iut
