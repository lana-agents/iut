/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Genl.GeneralPosition.HeightTheory

/-!
# The ABC target statement (taxis #1451)

The target of the implication strand (taxis #1449) is the Diophantine inequality of
IUT IV, Corollary 2.3 — Vojta's conjecture for hyperbolic curves over number fields,
which contains the ABC conjecture and the Szpiro conjecture as special cases:

> for `X` a smooth proper geometrically connected curve over a number field, `D ⊆ X` a
> reduced divisor with `U_X = X ∖ D` hyperbolic, `d ≥ 1` and `ε > 0`,
> `ht_{ω_X(D)} ≲ (1 + ε)·(log-diff_X + log-cond_D)` on `U_X(ℚ̄)^{≤d}`.

As IUT IV observes in the proof of Corollary 2.3, this statement *is* statement (i) of
[GenEll], Theorem 2.1, which `LANA-Project/genl` states as `Genl.HeightTheory.StatementI`
relative to a height formalism `T : Genl.HeightTheory` (taxis #2). We therefore do not
restate the conjecture: `Iut.ABC T` is that statement.

The concrete height formalism of curves over number fields — heights of line bundles,
log-different, log-conductor, compactly bounded subsets of the tripod whose support
contains `2` — is standard arithmetic geometry and is delegated to genl
(taxis #1452, item 1). The implication theorem (`Iut.cor312Variant_implies_abc`) is
proved for every height formalism equipped with the standard inputs it needs, so it
applies to the concrete one as soon as genl provides it.
-/

namespace Iut

/-- **The ABC target**: IUT IV, Corollary 2.3, i.e. [GenEll], Theorem 2.1(i), for the
height formalism `T`. -/
def ABC (T : Genl.HeightTheory) : Prop := T.StatementI

lemma abc_iff (T : Genl.HeightTheory) : ABC T ↔ T.StatementI := Iff.rfl

end Iut
