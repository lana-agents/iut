import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.3. Estimates of Differents" =>

:::proposition "prop:1.3"
Let $`k_0\subseteq k_i` contain $`\Qp`. Write $`d_0,e_0` for the normalized
order of the different of $`k_0/\Qp` and its ramification index, and put
$`e_{i/0}=e_i/e_0`. Let $`n_i\ge0` be determined by requiring
$`[k_i:k_0]/p^{n_i}` to be prime to $`p`.

1. $`d_i\ge d_0+(e_{i/0}-1)/(e_{i/0}e_0)
   =d_0+(e_{i/0}-1)/e_i`; equality holds when $`k_i/k_0` is tamely ramified.
2. If $`k_i` is Galois over a field $`k_1` with $`k_0\subseteq k_1\subseteq k_i`
   and $`k_1/k_0` is tamely ramified, then
   $`d_i\le d_0+n_i+1/e_0`.

*Status: not started.*
:::
