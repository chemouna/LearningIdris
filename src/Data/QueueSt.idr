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


partial
popQ : (q : Queue ty) -> {auto prf : isQCons q = True} -> (ty, Queue ty)
popQ (MkQ Nil Nil) {prf=Refl} impossible
popQ (MkQ Nil [x]) = (x, MkQ Nil Nil)
popQ (MkQ (x :: xs) Nil) = case (reverse (x::xs)) of (y::ys) => (y, MkQ Nil ys)
popQ (MkQ Nil (y :: ys)) = (y, MkQ Nil ys)
popQ (MkQ (x:xs) [y]) = (y, MkQ Nil (reverse (x:xs))
popQ (MkQ (x :: xs)(y :: ys)) = (y, MkQ (x :: xs) ys)
popQ (MkQ Nil (x :: (y :: ys))) = (x, MkQ Nil (y :: ys))
