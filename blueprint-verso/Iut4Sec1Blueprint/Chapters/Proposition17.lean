import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude
import Iut4Sec1.Combinatorics.WeightedAverage

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.7. Weighted Averages" =>

:::proposition "prop:1.7"
Let $`E` be a nonempty finite set, $`n>0`, and let
$`\lambda_e\in\mathbb R_{>0}`, $`\beta_e\in\mathbb R` for $`e\in E`. Put

$`\lambda_E=\sum_e\lambda_e`,
$`\beta_E=\sum_e\beta_e\lambda_e`,
$`\beta_{\rm avg}=\beta_E/\lambda_E`,
$`\beta_{\vec e}=\sum_{j=1}^n\beta_{e_j}`, and
$`\lambda^\Pi_{\vec e}=\prod_{j=1}^n\lambda_{e_j}`.

For every $`i=1,\ldots,n`,

$`\frac{\sum_{\vec e\in E^n}\beta_{\vec e}\lambda^\Pi_{\vec e}}
        {\sum_{\vec e\in E^n}\lambda^\Pi_{\vec e}}
 =\frac{\sum_{\vec e\in E^n}n\beta_{e_i}\lambda^\Pi_{\vec e}}
        {\sum_{\vec e\in E^n}\lambda^\Pi_{\vec e}}
 =n\beta_{\rm avg}`.

*Status: formalized.*
:::

:::lemma_ "lemma:weighted-average" (lean := "Iut4Sec1.weighted_average_eq")
The two weighted tuple averages agree and equal $`n\beta_{\rm avg}`.
:::

:::lemma_ "lemma:normalized-packet-weight" (lean := "Iut4Sec1.rawPacketWeight_pos, Iut4Sec1.rawPacketWeight_sum_pos, Iut4Sec1.sum_normalizedPacketWeight_eq_one")
Positive local degrees give positive raw weights, a positive normalizing
denominator, and normalized packet weights summing to one.
:::
