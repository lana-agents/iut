import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude
import Iut4Sec1.LocalField.Basic
import Iut4Sec1.Real.LogError

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.2. Differents and Logarithms" =>

:::proposition "prop:1.2" (uses := "prop:1.1")
Continue with Proposition 1.1. Let $`e_i` be the ramification index and set

$`a_i=e_i^{-1}\left\lceil e_i/(p-2)\right\rceil` for $`p>2`,
$`a_i=2` for $`p=2`, and
$`b_i=\left\lfloor\log(pe_i/(p-1))/\log p\right\rfloor-e_i^{-1}`.

For nonempty $`E`, put
$`\log_p(R_E^\times)=\bigotimes_{i\in E}\log_p(R_i^\times)`,
$`a_E=\sum_{i\in E}a_i`, and $`b_E=\sum_{i\in E}b_i`. If $`\varphi`
is an automorphism of $`\log_p(R_I^\times)\otimes\Qp` preserving
$`\log_p(R_I^\times)`, then:

1. $`p^{a_i}R_i\subseteq\log_p(R_i^\times)\subseteq p^{-b_i}R_i`, with
   equality throughout when $`p>2` and $`e_i\le p-2`.
2. For $`\lambda\in e_i^{-1}\mathbb Z`, $`i\in I`,
   $`\varphi(p^\lambda(R_I)^\sim)\subseteq
   p^{\lfloor\lambda-d_I-a_I\rfloor}\log_p(R_I^\times)
   \subseteq p^{\lfloor\lambda-d_I-a_I\rfloor-b_I}(R_I)^\sim`.
3. If $`p>2` and every $`e_i\le p-2`, this sharpens to
   $`\varphi(p^\lambda(R_I)^\sim)\subseteq p^{\lambda-d_I-1}(R_I)^\sim`.
4. If $`p>2` and every $`e_i=1`, then
   $`\varphi((R_I)^\sim)\subseteq(R_I)^\sim`.

*Status: partial.* Finite extensions now construct their spectral integer
rings, normalized orders, ramification indices, residue degrees, and
differents. The numerical small-ramification parameter equality is formalized
below; the logarithmic lattice inclusions remain to be proved.
:::

:::definition "def:mixed-char-local-field-data" (lean := "Iut4Sec1.MixedCharLocalFieldData, Iut4Sec1.mixedCharLocalFieldData_of_finiteExtension")
Every finite-dimensional field extension of $`\Qp` has canonical local-field
data obtained from the spectral norm. Completeness, the discrete valuation
ring, finite residue field, normalization $`\operatorname{ord}(p)=1`, and
compatibility with the ideal-theoretic ramification index and different are
constructed rather than assumed.
:::

:::lemma_ "lemma:ramified-quadratic-evaluation" (uses := "def:mixed-char-local-field-data") (lean := "Iut4Sec1.RamifiedQuadraticExample.ramifiedQuadratic_evaluation")
For $`\Q_2(\sqrt 2)` the construction is instantiated on an extension of
finrank two and evaluates its integer ring, normalized order, ramification
index, and different.
:::

:::definition "def:local-parameters" (lean := "Iut4Sec1.aParam, Iut4Sec1.bParam")
The parameters $`a(p,e)` and $`b(p,e)` are the ceiling and floor expressions
in Proposition 1.2.
:::

:::lemma_ "lemma:local-parameters-small" (uses := "def:local-parameters") (lean := "Iut4Sec1.localParameters_eq_of_smallRamification")
If $`p>2` and $`0<e\le p-2`, then $`a(p,e)=1/e` and $`b(p,e)=-1/e`.
:::

:::definition "def:nonarchimedean-log-error" (lean := "Iut4Sec1.nonarchimedeanLogError")
For $`p>2` and positive $`e`, define the nonarchimedean ceiling error

$`\epsilon_p(e)=e^{-1}\lceil e/(p-2)\rceil-e^{-1}`.
:::

:::lemma_ "lemma:nonarchimedean-log-error-zero" (uses := "def:nonarchimedean-log-error") (lean := "Iut4Sec1.nonarchimedeanLogError_eq_zero_of_le")
If $`0<e\le p-2`, then $`\epsilon_p(e)=0`.
:::

:::lemma_ "lemma:nonarchimedean-log-error-pointwise" (uses := "def:nonarchimedean-log-error") (lean := "Iut4Sec1.nonarchimedeanLogError_nonneg, Iut4Sec1.nonarchimedeanLogError_le_four_div")
For $`p>2` prime and $`e>0`, the error $`\epsilon_p(e)` is nonnegative and at
most $`4/p`.
:::
