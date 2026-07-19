import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

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

*Status: not started.*
:::
