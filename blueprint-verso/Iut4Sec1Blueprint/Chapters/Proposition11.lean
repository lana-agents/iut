import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.1. Multiple Tensor Products and Differents" =>

:::proposition "prop:1.1"
Let $`p` be prime and let $`I` be a finite set with $`|I|\ge 2`. For each
$`i\in I`, let $`k_i\subseteq\overline{\Qp}` be finite over $`\Qp`, let
$`R_i=\mathcal O_{k_i}`, and let $`d_i\in\mathbb Q_{\ge0}` be the normalized
$`p`-adic order of a generator of the different of $`R_i/\Zp`. For nonempty
$`E\subseteq I`, put
$`R_E=\bigotimes_{i\in E,\,\Zp}R_i` and $`d_E=\sum_{i\in E}d_i`.
If $`*\in I` and $`I^*=I\setminus\{*\}`, then

$`p^{d_{I^*}}\,(R_I)^{\sim}\subseteq R_I\subseteq(R_I)^{\sim}`,

where $`(R_I)^{\sim}` is the normalization of the reduced tensor product in
its ring of fractions. The left-hand expression is well-defined for suitable
choices of elements of the indicated orders and the inclusion is independent
of those choices.

*Status: not started.*
:::
