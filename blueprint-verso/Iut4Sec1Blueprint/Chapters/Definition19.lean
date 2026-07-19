import Verso
import VersoManual
import VersoBlueprint
import Iut4Sec1Blueprint.TexPrelude
import Iut4Sec1.Global.Pullback

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

*Status: formalized.* The pullback is constructed separately over finite and
infinite places; its invariance follows from the finite ramification--inertia
sum and the infinite completion-degree sum.
:::

:::definition "def:arithmetic-divisor-model" (lean := "Iut4Sec1.ArithmeticPlace, Iut4Sec1.ArithmeticDivisor, Iut4Sec1.arithmeticDivisorSupport, Iut4Sec1.ArithmeticDivisorEffective, Iut4Sec1.arithmeticDivisorDegree, Iut4Sec1.normalizedArithmeticDivisorDegree")
Arithmetic divisors are finitely supported real-valued functions on the sum of
the finite and infinite place types.
:::

:::lemma_ "lemma:effective-degree-nonnegative" (uses := "def:arithmetic-divisor-model") (lean := "Iut4Sec1.normalizedArithmeticDivisorDegree_nonneg")
The normalized degree of an effective arithmetic divisor is nonnegative.
:::

:::lemma_ "lemma:arithmetic-divisor-pullback" (uses := "def:arithmetic-divisor-model") (lean := "Iut4Sec1.normalizedArithmeticDivisorDegree_pullback")
Normalized global degree is invariant under pullback through a finite extension
of number fields.
:::

:::lemma_ "lemma:normalized-local-degree-pullback" (uses := "def:arithmetic-divisor-model") (lean := "Iut4Sec1.normalizedLocalDegree_pullback")
For a nonempty finite part of the place set, raw part degree and total local
degree scale by the same extension degree, including both place kinds.
:::
