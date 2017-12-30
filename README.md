README
======

This repository has the materials for a 50 minute talk on 
Refinement reflection and proof by logical evaluation, which 
are described at length in [this paper](ranjitjhala.github.io/static/refinement_reflection.pdf)

For other talks, you may be interested in:

+ [45mins](http://ucsd-progsys.github.io/live/) 
+ [2 Hr Workshop](http://ucsd-progsys.github.io/lh-workshop/)
+ [Tutorial](http://ucsd-progsys.github.io/liquidhaskell-tutorial/)
+ [Blog](http://ucsd-progsys.github.io/liquidhaskell-blog/)

Build Slides
------------

To build html slides (in dist/_site)

Initialize:

     $ stack exec -- make client 

Rebuild:

     $ stack exec -- make 

Edit Slides
-----------

You can modify the following parameters:

1. **Server URL**: change `liquidserver` in `assets/templates/preamble.lhs`
2. **MathJax URL**: change the relevant link in `assets/templates/pagemeta.template`

Outline [25]
-------

+ 01-intro         [3]
+ 02-refinements   [6]
+ 03-examples      [9]
+ 04-abstracting   [4]
+ 05-concl         [3]


Outline [45]
-------

+ 01-intro         [5]
+ 02-refinements   [8]
+ 03-examples      [10]
+ 04-termination   [7]
+ 05-reflection    [7]
+ 06-concl         [5]


```
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Blank where

import Prelude hiding (sum)
import Language.Haskell.Liquid.ProofCombinators

{-@ assume (*) :: (Num a) => x:a -> y:a -> {v:a | v = x * y} @-}

{-@ reflect sum @-}
{-@ sum :: Nat -> Nat @-}
sum :: Int -> Int
sum n
  | n == 0    = 0
  | otherwise = n + sum (n-1)

{-@ thm :: n:Nat -> { 2 * sum n == n * (n + 1) } @-}
thm :: Int -> ()
thm 0 = ()
thm n = thm (n - 1)

{-@ sumPf :: n:Nat -> { 2 * sum n == n * (n + 1) } @-}
sumPf  :: Int -> ()
sumPf 0 =   2 * (sum 0)
        ==. 0
        *** QED
sumPf n =   2 * (sum n)
        ==. 2 * (n + sum (n-1))
        ==. 2 * (n + ((n - 1) * n)) ? sumPf (n-1)
        ==. n * (n + 1)
        *** QED
```


```
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-cons"                     @-}

module Blank where

import Prelude hiding ((++))

import Language.Haskell.Liquid.ProofCombinators


{-@ reflect ++ @-}
{-@ infix ++ @-}
(++) :: [a] -> [a] -> [a]
[]  ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ inline assoc @-}
assoc op x y z = (x `op` y) `op` z == x `op` (y `op` z)

{-@ thm :: xs:[a] -> ys:[a] -> zs:[a] -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
thm :: [a] -> [a] -> [a] -> ()

thm [] ys zs     = ([] ++ ys) ++ zs
                ==. ys ++ zs
                ==. [] ++ (ys ++ zs)
                *** QED
thm (x:xs) ys zs = ((x:xs) ++ ys) ++ zs
                ==. (x : (xs ++ ys)) ++ zs
                ==.  x : ((xs ++ ys) ++ zs)
                ==.  x : (xs ++ (ys ++ zs)) ? thm xs ys zs
                ==.  (x : xs) ++ (ys ++ zs)
                *** QED
```
