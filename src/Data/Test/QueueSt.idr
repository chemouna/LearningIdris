module Data.Test.Queue

import Data.QueueSt
import Test.Generic

%access export

covering
test2 : IO Bool
test2 = genericTest (Just "Enqueue") (pushQThings [1,2,3] mkQueue) (pushQ 3 $ pushQ 2 $ pushQ 1 mkQueue) (==)

-- partial
-- test3 : IO Bool
-- test3 = genericTest (Just "Dequeue") (popQ' (pushQThings [1,2,3] mkQueue)) (Just (1, setQueue Nil [2,3])) (==)

partial
runTest : IO ()
runTest = do
  putStrLn "Testing Queue"
  putStrLn infoLine
  NonReporting.runTests [
       test2
     --, test3
  ]
