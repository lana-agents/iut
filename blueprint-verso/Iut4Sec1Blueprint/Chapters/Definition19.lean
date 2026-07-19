import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.9. Arithmetic Divisors" =>

:::definition "def:1.9"
Let $`F` be a number field with nonarchimedean and archimedean places.

1. An $`\mathbb R`-arithmetic divisor is a finite formal sum
   $`a=\sum_{v\in V(F)}c_vv`. Its support consists of the places with
   $`c_v\ne0`, and it is effective when every $`c_v\ge0`. Define
   $`\deg_F(a)` by weighting a finite place $`v` by $`\log q_v` and an
   archimedean place by $`1`; set $`\deg(a)=[F:\mathbb Q]^{-1}\deg_F(a)`.
   For finite $`K/F`, normalized degree is invariant under pullback:
   $`\deg(a|_K)=\deg(a)`.
2. If $`E` is a nonempty set of places of $`F` over one place $`v_{\mathbb Q}`,
   let $`a_E` be the part supported on $`E` and define
   $`\deg_E(a)=\deg(a_E)/(\sum_{v\in E}[F_v:\mathbb Q_{v_{\mathbb Q}}])`.
   If $`E|_K` denotes the places of $`K` above $`E`, then
   $`\deg_{E|_K}(a|_K)=\deg_E(a)`.

*Status: not started.*
:::
