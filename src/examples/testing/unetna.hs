#!/usr/bin/env runhaskell

{-
This script removes Etna mutants for CN.
We make some simplifyinf assumptions, namely:
  * Etna comments are on their own line
  * There's at least one non-enta line between the mutants for one
    block and the following Etna block.
-}

import Data.Char(isSpace)



main = interact (unlines . strip . lines)

strip ls
  | null ls = ls
  | otherwise =
    case break (etnaLine NonMut) ls of
      (as,_:bs) -> as ++ code ++ strip (dropWhile (etnaLine Any) muts)
        where
        (code,muts) = break (etnaLine Mut) bs
      _ -> ls

data EtnaLine = Any | Mut | NonMut

etnaLine ty l =
  case dropWhile isSpace l of
    '/' : '/' : '!' : more ->
      case ty of
        Any -> True
        Mut -> take 1 more == "!"
        NonMut -> take 1 more /= "!"
    _ -> False
