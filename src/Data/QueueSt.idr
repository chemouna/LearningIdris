module Data.QueueSt

%access export
%default total

data Queue : (ty : Type) -> Type where
  MkQ : List a -> List a -> Queue a

mkQueue : Queue ty
mkQueue = MkQ Nil Nil

setQueue : List a -> List a -> Queue a
setQueue inq outq = MkQ inq outq

isEmpty : Queue a -> Bool
isEmpty (MkQ inq outq) = isNil inq && isNil outq

pushQ : a -> Queue a -> Queue a
pushQ e (MkQ inq outq) = MkQ (e::inq) outq

pushQMany : List a -> Queue a -> Queue a
-- pushQMany [] q = q
-- pushQMany (x::xs) (MkQ inq outq) = pushQMany xs (MkQ (x::inq) outq)
pushQMany xs q = foldl (flip pushQ) q xs
