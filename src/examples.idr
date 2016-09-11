module Examples

import Data.Fin
import Data.List
import Data.Vect

reverse : List a -> List a
reverse xs = revAcc [] xs where
  revAcc : List a -> List a -> List a
  revAcc acc [] = acc
  revAcc acc (x :: xs) = revAcc (x :: acc) xs

data Vect2 : Nat -> Type -> Type where
  Nil  : Vect2 Z a
  (::) : a -> Vect2 k a -> Vect2 (S k) a

(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
-- (++) (x :: xs) ys = x :: xs ++ xs -- BROKEN

intVec : Vect 5 Int
intVec = [1, 2, 3, 4, 5]

double : Int -> Int
double x = x * 2


 
