
<div class="hidden">
\begin{code}
module Intro where

import Language.Haskell.Liquid.NewProofCombinators

dummy :: Int
dummy = 7
\end{code}
</div>

<div class="slide">

<br>
<br>
<br>


<p align=center>
<h1 style="border-bottom:none">Reasoning about Functions</h1>

<br>

<h4 style="border-bottom:none"><i>Ranjit Jhala (UCSD)</i></h4>
</p>

</div>

Follow Along at This URL
------------------------

<br>
<br>
<br>

[http://ucsd-progsys.github.io/reasoning-about-functions/](http://ucsd-progsys.github.io/reasoning-about-functions/)


<br>

Zoom in to see nav arrows

Some Math
---------


$$\forall \overline{x}, \overline{y}.\ \overline{x} = \overline{y}\ \Rightarrow\ f(x) = f(y)$$


Some Code
---------

\begin{code}
{-@ assert :: {v:Bool | v} -> () @-}
assert :: Bool -> ()
assert b = ()

goal  = assert (sumTo 0 == 0) &&& assert (sumTo 1 == 1)

goal1 = assert (sumTo 0 == 0 && sumTo 1 == 1 && sumTo 2 == 3)

{-@ reflect sumTo @-}
sumTo :: Int -> Int
sumTo n = if n <= 0 then 0 else n + sumTo (n - 1)

{-@ goal2'' :: () -> { sumTo 2 == 3 } @-}
goal2'' ()
  =   sumTo 2
  === 2 + sumTo 1
  === 2 + 1 + sumTo 0
  === 3

{-@ goal3 :: _ -> { sumTo 2 == 3 } @-}
goal3 _
  =   sumTo 3
  === 3 + sumTo 2
  ==? 6         ? goal2'' ()
\end{code}

I. Motivation
-------------

Motivation: Automated Reasoning
-------------------------------

   SMT awesome
     ... for "shallow" specifications over _decidable_ theories
     ... e.g. _quantifier free_ **arithmetic**, UF, sets, bit-vectors

Shallow Specifications
----------------------

How to verify?

```
sum n =
  if n <= 0 then 0 else n + sum (n-1)

_ = assert (0 <= sum(3))
```

Shallow Specifications
----------------------

How to verify? Use a spec for `sum`

```
sum n =
  @ensures  (0 <= res)
  if n <= 0 then 0 else n + sum (n-1)             ... (*)

goal () =
  @ensures (0 <= sum(3))
  ()
```

Shallow Specifications
----------------------

How to verify? Use a spec for `sum`

```
sum :: Int -> {res | 0 <= res}
sum n =
  if n <= 0 then 0 else n + sum (n-1)             ... (1)

goal :: () -> { _ | 0 <= sum 3}
goal () = ()                                      ... (2)
```

Generate VCs

   ```
   n > 0  => 0 <= sum (n-1) => 0 <= n + sum (n-1)    ... (1)

   0 <= sum(3) => 0 <= sum(3)                        ... (1)
   ```

SMT says Valid!

Motivation: Automated Reasoning about Functions
-----------------------------------------------

   SMT awesome
     ... for "shallow" specifications over _decidable_ theories
     ... e.g. _quantifier free_ **arithmetic**, UF, sets, bit-vectors

   SMT brittle
     ... when spec (contract) _outside decidable_ theories
     ... e.g. containing **user defined functions**

Deep Specifications
-------------------

Whats a good spec for `sum`?

   ```
   sum n =
     if n <= 0 then 0 else n + sum (n-1)

   goal' :: () -> { _ | 0 <= sum 3}
   goal' _ = ()                                      ... (2)
   ```

The implementation **is** the specification!

   forall n. n <= 0 => sum(n) = 0
   forall n. 0 < n  => sum(n) = n + sum(n-1)

Oops. Axioms. SMT goes to die...[Footnote]

Deep Specifications are Everywhere
----------------------------------

* LAWS
      - append_assoc,
      - le_sym, le_trans, [dillig-sousa]

* OPTIMIZATIONS
      - map_fusion
      - opt0

* INVARIANTS
      - filter
      - filter-query [tests/pos/binah-EvalQuery.hs]

* CORRECTNESS
      - range i j

Motivation: Automated Reasoning about Functions
-----------------------------------------------

   SMT awesome
     ... for "shallow" specifications over _decidable_ theories
     ... e.g. _quantifier free_ **arithmetic**, UF, sets, bit-vectors

   SMT brittle
     ... when spec (contract) _outside decidable_ theories
     ... e.g. containing **user defined functions**

   Goal: Make SMT predictable with user defined functions.



## II. Equational Reasoning / Reflection

### Whats a good spec for `sum`?

   ```
   sum n =
     if n <= 0 then 0 else n + sum (n-1)

   _ = assert (sum(3) == 6)
   ```

### Reflection: The implementation is the specification

   ```
   {-@ reflect sum @-}
   sum n =
     if n <= 0 then 0 else n + sum (n-1)
   ```

   Generates a contract for `sum`

   ```
   sum :: n:Int -> {v:Int | v == if n <= 0 then 0 else n + sum(n-1) }
   ```

   where

   `sum` is **uninterpreted** the refinement logic. [Suter et al. 2011]

### Reflection: Calling unfolds definition

   ```
   {-@ reflect sum @-}
   sum n =
     if n <= 0 then 0 else n + sum (n-1)
   ```

   This **lets us** prove

   ```
   _ = assert (sum(0) == 0)
   ```

   Which generates the **valid** VC

   ```
   (sum(0) == if (0 <= 0) then 0 else ...) => sum(0) == 0
   ```

### Reflection: Calling unfolds definition

   ```
   {-@ reflect sum @-}
   sum n =
     if n <= 0 then 0 else n + sum (n-1)
   ```

   This **fails to** prove

   ```
   goal1 = assert (sum(1) == 1)
   ```

   Which generates the VC

   ```
   (sum(1) == if (1 <= 0) then 0 else 1 + sum(0)) => sum(1) == 1
   ```

   which is **invalid** when `sum` is uninterpreted.

## Solution: Unfold/Call `sum` again!

   We can unfold `sum` again, by checking

   ```
   goal1' = assert (sum(0) == 0 && sum(1) == 1)
   ```

   which generates the **valid** VC

   ```
   (  sum(0) == if 0 <= 0 then 0 else ...
   /\ sum(1) == if 1 <= 0 then 0 else 1 + sum(0) )

      =>   sum(0) == 0
        /\ sum(1) == 1
   ```

## Unfold/Call `sum` again ... and again

   ```
   -- FAILS
   goal2  = assert (sum(2) == 3)

   -- OK
   goal2' = assert (sum(0) == 0 && sum(1) == 1 && sum(2) == 3)
   ```

## Operators for Equational Reasoning

   Its silly to keep calling `sum`

   ... but operators make it less so.

   ```
   {-@ goal2'' :: _ -> { sum 2 == 3 } @-}
   goal2'' _ =   sum 2
             === 2 + sum 1
             === 2 + 1 + sum 0
             === 3
  --           *** QED
   ```

   where

   ```
   (===) :: x:a -> {y:a | y = x} ->


## III. Equation Synthesis / PLE

  - Examples
  - Algo
  - Algo by example
  - Completeness & Termination

## IV. Evaluation
  - Tables & run-time
  - Examples (?)
    - OPTIMIZATIONS
    - INVARIANTS
    - CORRECTNESS
  - CHALLENGES
