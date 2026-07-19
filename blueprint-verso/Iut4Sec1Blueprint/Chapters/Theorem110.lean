import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude
import Iut4Sec1.Combinatorics.RangeAverages

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.10. Log-volume Estimates for Theta-pilot Objects" =>

:::theorem "thm:1.10" (uses := "prop:1.1, prop:1.2, prop:1.3, prop:1.4, prop:1.5, prop:1.6, prop:1.7, prop:1.8, def:1.9")
Fix initial Theta-data as in IUT I, Definition 3.1, in the situation of IUT III,
Corollary 3.12, with the stated good-reduction hypothesis. Let
$`d_{\rm mod}=[F_{\rm mod}:\mathbb Q]`, let $`e_{\rm mod}` be the maximal
ramification index, let
$`e^*_{\rm mod}=2^{12}3^3\cdot5e_{\rm mod}`, and take the tripodal tower

$`F_{\rm mod}\subseteq F_{\rm tpd}=F_{\rm mod}(E[2])\subseteq F\subseteq K`

with $`\ell\ge7`, the torsion-rationality, Legendre, Galois, and reduction
conditions in the paper. Let $`\log d_{F_\square}`, $`\log f_{F_\square}`,
and $`\log q` be the normalized degrees of the different, conductor, and
$`q`-divisors, and put $`|\log(q)|=(2\ell)^{-1}\log q`.
The averaging step uses (E1), the average of $`1,\ldots,n`, and (E2), the
average of their squares; both identities are formalized below.

Then the quantity $`C_\Theta` of IUT III, Corollary 3.12 may be taken to be

$`\frac{\ell+1}{4|\log(q)|}\left\{
 (1+12d_{\rm mod}/\ell)(\log d_{F_{\rm tpd}}+\log f_{F_{\rm tpd}})
 +10(e^*_{\rm mod}\ell+\eta_{\rm prm})
 -\frac16(1-12/\ell^2)\log q\right\}-1`.

Using $`C_\Theta\ge-1`, one obtains

$`\frac16\log q\le
 (1+20d_{\rm mod}/\ell)(\log d_{F_{\rm tpd}}+\log f_{F_{\rm tpd}})
 +20(e^*_{\rm mod}\ell+\eta_{\rm prm})`

$`\le (1+20d_{\rm mod}/\ell)(\log d_F+\log f_F)
 +20(e^*_{\rm mod}\ell+\eta_{\rm prm})`.

*Status: conditional on explicit IUT I--III interfaces, an explicit
`PrimeCountingCertificate`, and the explicit `ReductionCertificate` family;
not started.* The five IUT packages, prime-counting certificate, and reduction
certificate family will remain ordinary theorem arguments. Elementary assembly
and numerical tracking will be proved only after those arguments are supplied.
:::

:::lemma_ "lemma:E1-range-average" (lean := "Iut4Sec1.average_range_sum")
For $`n>0`, $`n^{-1}\sum_{m=1}^n m=(n+1)/2`.
:::

:::lemma_ "lemma:E2-range-square-average" (lean := "Iut4Sec1.average_range_sq_sum")
For $`n>0`, $`n^{-1}\sum_{m=1}^n m^2=(2n+1)(n+1)/6`.
:::
