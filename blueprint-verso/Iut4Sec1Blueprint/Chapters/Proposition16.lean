import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.6. The Prime Number Theorem" =>

:::proposition "prop:1.6"
Let $`p_n` be the $`n`-th smallest prime, so $`p_1=2`. There is an integer
$`n_0` such that

$`n\le \frac{4p_n}{3\log p_n}`

for every $`n\ge n_0`. Consequently there is $`\eta_{\rm prm}>0` such that,
for every real $`\eta\ge\eta_{\rm prm}`,

$`\sum_{p\le\eta}1\le\frac{4\eta}{3\log\eta}`,

where the sum ranges over primes.

*Status: conditional on an explicit `PrimeCountingCertificate`; not started.*
Mathlib's available Chebyshev bound has leading coefficient $`\log 4+\varepsilon`
and does not prove the displayed $`4/3` coefficient. A separate weaker
unconditional Chebyshev theorem is planned and will not be labeled Proposition 1.6.
:::
