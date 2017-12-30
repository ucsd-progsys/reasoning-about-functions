
<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}

module Reflection where

\end{code}

</div>

II. Equational Reasoning / Reflection
=====================================


Whats a good spec for `sum`?
----------------------------

   ```
   sum n =
     if n <= 0 then 0 else n + sum (n-1)

   _ = assert (sum(3) == 6)
   ```

Reflection: The implementation is the specification
----------------------------

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

Reflection: Calling unfolds definition
----------------------------

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

Reflection: Calling unfolds definition
----------------------------

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

Solution: Unfold/Call `sum` again!
----------------------------

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

Unfold/Call `sum` again ... and again
----------------------------

   ```
   -- FAILS
   goal2  = assert (sum(2) == 3)

   -- OK
   goal2' = assert (sum(0) == 0 && sum(1) == 1 && sum(2) == 3)
   ```

Operators for Equational Reasoning
----------------------------

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


III. Equation Synthesis / PLE
====

  - Examples
  - Algo
  - Algo by example
  - Completeness & Termination

IV. Evaluation
====

  - Tables & run-time
  - Examples (?)
    - OPTIMIZATIONS
    - INVARIANTS
    - CORRECTNESS
  - CHALLENGES
