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

isQCons : Queue a -> Bool
isQCons (MkQ inq outq) = isCons inq && isCons outq

pushQ : a -> Queue a -> Queue a
pushQ e (MkQ inq outq) = MkQ (e::inq) outq

pushQMany : List a -> Queue a -> Queue a
-- pushQMany [] q = q
-- pushQMany (x::xs) (MkQ inq outq) = pushQMany xs (MkQ (x::inq) outq)
pushQMany xs q = foldl (flip pushQ) q xs

-- partial
-- popQ : (q : Queue ty) -> {auto prf : isQCons q = True} -> (ty, Queue ty)
-- popQ (MkQ Nil Nil) {prf=Refl} impossible
-- popQ (MkQ Nil [x]) = (x, MkQ Nil Nil)
-- popQ (MkQ (x :: xs)(y :: (z :: ys))) = (y, MkQ (x :: xs) ys)
-- popQ (MkQ (x :: xs) Nil) = case (reverse (x::xs)) of 
--   (y::ys) => (y, MkQ Nil ys)
-- --popQ (MkQ Nil (y :: ys)) = (y, MkQ Nil ys)
-- popQ (MkQ (x :: xs) [y]) = (y, MkQ Nil (reverse (x :: xs))
-- popQ (MkQ Nil (x :: (y :: xs))) = (x, MkQ Nil (y::xs))

||| Remove an element from the queue, returning the pair (head, tail)
||| @q The Q
partial
popQ : (q : Queue ty) -> {auto prf : isQCons q = True} ->  (ty, Queue ty)
popQ (MkQ Nil Nil) {prf=Refl} impossible
popQ (MkQ Nil [x])            = (x, MkQ Nil Nil)
popQ (MkQ (x :: xs) (y :: (z :: ys))) = (y, MkQ (x::xs) ys)
popQ (MkQ (x :: xs) Nil) = case (reverse (x::xs)) of
  (y::ys) => (y, MkQ Nil ys)
popQ (MkQ (x :: xs) [y]) = (y, MkQ Nil (reverse (x::xs)))
popQ (MkQ Nil (x :: (y :: xs))) = (x, MkQ Nil (y::xs))
 
-- partial
-- peekQ :: (q : Queue ty) -> {auto prf : isQCons q = True} -> ty
-- peekQ q = fst $ popQ q
