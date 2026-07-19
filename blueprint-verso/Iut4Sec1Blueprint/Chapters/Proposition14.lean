import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.4. Nonarchimedean Normalized Log-volume Estimates" =>

:::proposition "prop:1.4" (uses := "prop:1.2, prop:1.3")
Continue with Proposition 1.2. Let $`p^{f_i}` be the residue-field cardinality
of $`k_i`; let $`p^{m_i}` be the order of the $`p`-primary part of the torsion
in $`R_i^\times`.

1. Normalized log-volume on compact open subsets satisfies
   $`\logvol(R_i)=0`, $`\logvol(pR_i)=-\log p`, and likewise
   $`\logvol((R_E)^\sim)=0`, $`\logvol(p(R_E)^\sim)=-\log p`.
2. $`\logvol(\log_p(R_i^\times))
   =-(e_i^{-1}+m_i/(e_if_i))\log p`.
3. If $`I^*\subseteq I` and $`e_i\le p-2` for $`i\notin I^*`, then the
   inclusions of Proposition 1.2(2) hold and

   $`\logvol(p^{\lfloor\lambda-d_I-a_I\rfloor}\log_p(R_I^\times))
   \le(-\lambda+d_I+1+4|I^*|/p)\log p`,

   $`\logvol(p^{\lfloor\lambda-d_I-a_I\rfloor-b_I}(R_I)^\sim)
   \le(-\lambda+d_I+1)\log p+\sum_{i\in I^*}(3+\log e_i)`.

   Moreover $`d_I+a_I\ge|I|` for $`p>2` and $`d_I+a_I\ge2|I|` for $`p=2`.
4. If $`p>2` and all $`e_i=1`, then
   $`\varphi((R_I)^\sim)\subseteq(R_I)^\sim` and its log-volume is zero.

*Status: not started.*
:::
