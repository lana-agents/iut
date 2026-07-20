import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.5. Archimedean Metric Estimates" =>

:::proposition "prop:1.5"
Equip $`\mathbb C` with its standard Hermitian metric. Its eight *primitive
automorphisms* are generated on the underlying real metrized vector space by
complex conjugation and multiplication by $`\pm1,\pm\sqrt{-1}`.

1. Under either Chinese-remainder isomorphism
   $`\mathbb C\otimes_{\mathbb R}\mathbb C\simeq\mathbb C\oplus\mathbb C`,
   the direct-sum metric is twice the tensor-product metric.
2. The induced primitive automorphisms preserve the direct-sum decomposition
   and Hermitian metric.
3. For nonempty finite $`I,V`, put $`M=\bigoplus_{v\in V}\mathbb C_v` and
   $`M_I=\bigotimes_{i\in I}M_i`. Then $`M_I` decomposes uniquely as a direct
   sum of $`2^{|I|-1}|V|^{|I|}` copies of $`\mathbb C`; its direct-sum metric is
   $`2^{|I|-1}` times its tensor-product metric. Both metrics, the decomposition,
   and the product $`B_I` of the component unit balls are preserved by the
   induced primitive automorphisms.
4. If every component of every $`m_i\in M_i` has length $`\lambda>0`, then
   $`\bigotimes_i m_i\in\lambda^{|I|}B_I`.

*Status: not started.*
:::
