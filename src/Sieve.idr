module Sieve

import Data.List

divides : Nat -> Nat -> Bool
divides n m = (m `modNat` n) == Z

sieve : List Nat -> Nat -> Bool
sieve ps n = not $ any (\p => p `divides` n) $ takeWhile (\p => p*p <= n) ps

-- primes_from : SortedSet Nat -> Nat -> Stream Nat
-- primes_from ps n =  if sieve (SortedSet.toList ps) n
-- then n :: primes_from (insert n ps) (S n)
-- else      primes_from           ps  (S n)

-- primes : Stream Nat
-- primes = primes_from empty 2

-- main : IO ()
-- main = sequence_stream $ map (putStrLn . show) primes



