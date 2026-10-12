/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.LogVolumeLCFT
import Iut.Concrete.LocalConstruct.LogShell

/-!
# The log-volume of the log-shells of `Iut/Concrete` (roadmap P17, M3e)

For a number field `K` and a finite place `w` of residue characteristic `p`, the completion
`K_w = completionAt K w` of `Iut/Concrete` is a `ℚ_p`-algebra through the continuous embedding
`padicEmb` (`padicAlgebra`, finite-dimensional by `finite_padicAlgebra`), so the unit balls of
its valuation and of the spectral norm of `local-class-field-theory` agree
(`hball_of_continuous`) and the volume computation of `LogVolumeLCFT.lean` applies to the
log-shell `𝓘_{K_w} = Iut.logShell K_w p` of IUT III, Definition 1.1, used by the concrete
`LocalTheory`:

* `measure_logShell_completionAt`: `p^{f+m} μ(𝓘_{K_w}) = (p*)^d μ(𝒪_{K_w})`;
* `logVolume_logShell_completionAt`: the normalised log-volume
  `log(μ(𝓘_{K_w})/μ(𝒪_{K_w})) / [K_w : ℚ_p]` is `(log p / e) · logShellConst p f e m`
  ([AbsTopIII], Proposition 5.8 (iii)), with `f`, `e`, `m` of `K_w`.
-/

namespace Iut.Reconstruction

open Iut.LocalConstruct MeasureTheory PadicField NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] {w : FinitePlace K}
  (hw : residueChar w = p)

/-- **The volume of the log-shell of a completion**: `p^{f+m} μ(𝓘_{K_w}) = (p*)^d μ(𝒪_{K_w})`. -/
theorem measure_logShell_completionAt [MeasurableSpace (completionAt K w)]
    [BorelSpace (completionAt K w)] (μ : Measure (completionAt K w)) [μ.IsAddLeftInvariant] :
    letI := padicAlgebra hw
    haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
    (p : ENNReal) ^ (f p ℚ_[p] (completionAt K w) + mExp p (completionAt K w)) *
        μ (logShell (completionAt K w) p) =
      (pStar p : ENNReal) ^ Module.finrank ℚ_[p] (completionAt K w) *
        μ (Metric.closedBall 0 1) := by
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  exact measure_logShell_eq (hball_of_continuous (continuous_padicEmb hw)) μ

/-- **[AbsTopIII], Proposition 5.8 (iii) for the completions of `Iut/Concrete`**: the normalised
log-volume of `𝓘_{K_w}` is `(log p / e) · logShellConst p f e m`. -/
theorem logVolume_logShell_completionAt [MeasurableSpace (completionAt K w)]
    [BorelSpace (completionAt K w)] (μ : Measure (completionAt K w)) [μ.IsAddLeftInvariant]
    (h0 : μ (Metric.closedBall 0 1) ≠ 0) (hfin : μ (Metric.closedBall 0 1) ≠ ⊤) :
    letI := padicAlgebra hw
    haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
    Real.log ((μ (logShell (completionAt K w) p)).toReal /
        (μ (Metric.closedBall 0 1)).toReal) / Module.finrank ℚ_[p] (completionAt K w) =
      logShellConst p (f p ℚ_[p] (completionAt K w)) (e p ℚ_[p] (completionAt K w))
        (mExp p (completionAt K w)) * Real.log p / e p ℚ_[p] (completionAt K w) := by
  letI := padicAlgebra hw
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  exact logVolume_logShell_eq (hball_of_continuous (continuous_padicEmb hw)) μ h0 hfin

end Iut.Reconstruction
