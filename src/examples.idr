module Examples

import Data.Fin 
import Data.List
import Data.Vect 
import Prelude.Functor.map

reverse : List a -> List a
reverse xs = revAcc [] xs where
  revAcc : List a -> List a -> List a
  revAcc acc [] = acc
  revAcc acc (x :: xs) = revAcc (x :: acc) xs

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
 
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
-- (++) (x :: xs) ys = x :: xs ++ xs -- BROKEN 

intVec : Vect 5 Int
intVec = [1, 2, 3, 4, 5]

double : Int -> Int
double x = x * 2
 

show (map double intVec)
