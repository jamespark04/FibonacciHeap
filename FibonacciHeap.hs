
module FibonacciHeap where

import Test.QuickCheck
import Data.Time.Clock
import System.Time
import System.Random
import Control.Monad.ST
import Data.STRef
import Control.Monad
import qualified Data.List as L
-- references for how fibonacci heaps work:
-- https://www.cs.princeton.edu/~wayne/teaching/fibonacci-heap.pdf
-- http://en.wikipedia.org/wiki/Fibonacci_heap
-- http://win.uantwerpen.be/~vanhoudt/graph/fibonacci.pdf
-- http://staff.ustc.edu.cn/~csli/graduate/algorithms/book6/chap21.htm

-- using regular lists
-- creates a Heap tree
data Node a = Node {value :: a, parent :: Maybe(Node a), children :: [Node a], degree :: Int, isMarked :: Bool}
  deriving Show

-- create a FibHeap
data FibHeap a = FibHeap{minElement :: a, roots :: [Node a], size :: Int}
  deriving Show

-- searches the children nodes for a specified value
searchChildrenNodes :: Bounded a => Ord a => a -> [Node a] -> Maybe (Node a)
searchChildrenNodes _ []                         = Nothing
searchChildrenNodes x (n:ns)
   | x == value n                                = Just (n)
   | null (children n)                           = searchChildrenNodes x ns
   | isJust (searchChildrenNodes x (children n)) = searchChildrenNodes x (children n)
   | otherwise                                   = searchChildrenNodes x ns

--finds a node given a value
findNode :: Bounded a => Ord a => a -> FibHeap a -> Maybe (Node a)
findNode x f = searchChildrenNodes x (roots f)

--isJust
isJust :: Maybe a -> Bool
isJust (Just a) = True
isJust Nothing  = False

-- merges two fibonacci heaps into one fibonacci heap1
merge :: Bounded a => Ord a => FibHeap a -> FibHeap a -> FibHeap a
merge f1 f2 
   | minElement f1 <= minElement f2 = f1{roots = (roots f1) ++ (roots f2), size = size f1 + size f2}
   | otherwise                      = f2{roots = (roots f1) ++ (roots f2), size = size f1 + size f2}

-- inserts an element into the fibonacci heap
insertFibHeap :: Bounded a => Ord a => a -> FibHeap a -> FibHeap a
insertFibHeap x f = merge (FibHeap{minElement = x, roots = [(Node{value = x, parent = Nothing, children = [], degree = 0,  isMarked = False})], size = 1}) f

-- returns the minimum element in the heap
findMin :: Bounded a => Ord a => FibHeap a -> a
findMin f = minElement f

-- generates a single element fibonacci heap
singleFibHeap :: Bounded a => Ord a => a -> FibHeap a 
singleFibHeap x = FibHeap{minElement = x, roots = [(Node{value = x, parent = Nothing, children = [], degree = 0, isMarked = False})], size = 1}

-- removes the minimum value from the root list
removeMinFromRoot :: Bounded a => Ord a => a -> Int -> [Node a] -> FibHeap a -> FibHeap a
removeMinFromRoot _ _ [] f = f 
removeMinFromRoot x i (n:ns) f
   | (value n) == x        = f{roots = (take i (roots f)) ++ (drop (i+1) (roots f)) ++ (children n)}
   | otherwise             = removeMinFromRoot x (i+1) ns f



-- combines two roots, smaller value becomes the parent
combineTwoRoots :: Bounded a => Ord a => Node a -> Node a -> Node a
combineTwoRoots n1 n2
   | value n1 <= value n2    = n1{children = (children n1) ++ [n2], degree = (degree n1) + 1}
   | otherwise               = n2{children = (children n2) ++ [n1], degree = (degree n2) + 1}

-- consolidates root nodes with the same degree
consolidateRoots :: Bounded a => Ord a => Int -> Int -> [Node a] -> [Node a] -> FibHeap a -> FibHeap a
consolidateRoots x y [] r f
   | x < (length r)  = consolidateRoots (x+1) (x+2) (drop (x+2) r) r f
   | x >= (length r) = f{roots = r}
consolidateRoots x y (n:ns) r f 
   | x >= (length r) || y >= (length r)     = f{roots = r}
   | degree ((head (drop x r))) /= degree n = consolidateRoots x (y+1) ns r f
   | degree ((head (drop x r))) == degree n = consolidateRoots 0 1 (drop 1 r2) r2 f
                                                        where w1   = (head (drop x r))
                                                              temp = take y r
                                                              r2   = [(combineTwoRoots w1 n)] ++ (take x temp) ++ (drop (x+1) temp) ++ ns

-- find the minimum root in the root list
findMinRoot :: Bounded a => Ord a => a -> [Node a] -> a
findMinRoot x []   = x
findMinRoot x (n:ns)
   | (value n) < x = findMinRoot (value n) ns
   | otherwise     = findMinRoot x ns

-- extracts the minimum element from the fib heap
extractMin :: Bounded a => Ord a => FibHeap a -> FibHeap a
extractMin f = FibHeap{minElement = (findMinRoot (value (head (roots f3))) (roots f3)), roots = roots f3, size = (size f) - 1}
                  where f2        = removeMinFromRoot (minElement f) 0 (roots f) f 
                        f3        = consolidateRoots 0 1 (drop 1 (roots f2)) (roots f2) f2


-- decreases key of Node
decreaseKey :: Bounded a => Ord a => a -> a -> FibHeap a -> FibHeap a
decreaseKey x y f = undefined

-- delete a specific element in the fib heap 
-- search for node, decrease key to large negative, and extract minimum
delete :: Bounded a => Ord a => a -> FibHeap a -> FibHeap a
delete x f
   | isJust (findNode x f) = extractMin (decreaseKey x minBound f)
   | otherwise             = f

-- generates a random list
--http://stackoverflow.com/questions/9139649/how-to-generate-a-list-which-contains-a-given-number-of-random-numbers-within-a
randomList :: (Random a) => (a,a) -> Int -> StdGen -> [a]
randomList bnds n = take n . randomRs bnds

-- generates a random fibheap given a generator and a size
generateRandomFibHeap :: Int -> StdGen -> FibHeap Int 
generateRandomFibHeap i s = buildHeapFromList (randomList (minBound :: Int, maxBound :: Int) i s)

-- given a fibheap, computes the time of insertion
printTimeDifferenceInserts :: FibHeap Int -> IO()
printTimeDifferenceInserts f =
  do 
    seed <- newStdGen
    let i = head (randomList (minBound :: Int, maxBound :: Int) 1 seed)
    t1 <- getCurrentTime
    let result2 = (insertFibHeap i f) `seq` 1
    print result2
    t2 <- getCurrentTime
    print (diffUTCTime t2 t1)

-- given a fibheap, computes the time of extraction of minimum
printTimeDifferenceExtracts :: FibHeap Int -> IO()
printTimeDifferenceExtracts f =
  do 
    t1 <- getCurrentTime
    let result2 = extractMin f `seq` 1
    print result2
    t2 <- getCurrentTime
    print (diffUTCTime t2 t1)

-- prints difference in timestamps for the fibheap sort vs the Data.List sort
printTimeDifferenceHeapSorting :: Int -> IO()
printTimeDifferenceHeapSorting i =
  do 
    seed <- newStdGen
    let l = randomList (minBound :: Int, maxBound :: Int) i seed
    let f = buildHeapFromList l
    let result = f `seq` 1
    print result
    t1 <- getCurrentTime
    let result2 = (buildSortedListFromHeap f) `seq` 1
    print result2
    t2 <- getCurrentTime
    print (diffUTCTime t2 t1)
    t3 <- getCurrentTime 
    let result3 = (L.sort l) `seq` 1
    print result3
    t4 <- getCurrentTime
    print (diffUTCTime t4 t3) 

-- checks that the parent is less than the current node
compareChildren :: Bounded a => Ord a => Node a -> [Node a] -> Bool
compareChildren _ []     = True
compareChildren p (n:ns) = (value p) <= (value n) && (compareChildren p ns)

-- checks all children against the current node
checkChildren :: Bounded a => Ord a => Node a -> Bool
checkChildren n
   | null (children n) = True
   | otherwise         = (compareChildren n (children n)) && and (map checkChildren (children n))

-- helper function for inserting elements into a heap
go :: Bounded a => Ord a => [a] -> FibHeap a -> FibHeap a
go [] f     = f
go (x:xs) f = go xs (insertFibHeap x f)

-- takes in a nonempty list
buildHeapFromList :: Bounded a => Ord a => [a] -> FibHeap a
buildHeapFromList []         = undefined
buildHeapFromList ([x])      = singleFibHeap x
buildHeapFromList (l@(x:xs)) = go xs (singleFibHeap x)

-- property tests that the heap property is true for building a heap
prop_build_heap :: Bounded a => Ord a => [a] -> Bool
prop_build_heap []         = True
prop_build_heap (l@(x:xs)) = and (map checkChildren (roots (buildHeapFromList l)))

-- builds a sorted list from a fibheap
buildSortedListFromHeap :: Bounded a => Ord a => FibHeap a -> [a]
buildSortedListFromHeap f
   | (size f) > 1 = (minElement f) : (buildSortedListFromHeap (extractMin f))
   | otherwise    = [(minElement f)]

-- checks whether sorting works from a heap
prop_sort :: Bounded a => Ord a => [a] -> Bool
prop_sort [] = True
prop_sort (l@(x:xs)) = (L.sort l) == (buildSortedListFromHeap (buildHeapFromList l))

-- heap property check helper function
checkChildrenHeap :: Bounded a => Ord a => FibHeap a -> Bool
checkChildrenHeap f
   | (size f > 1) && (length (roots f)) > 0 = and (map checkChildren (roots f)) && (checkChildrenHeap (extractMin f))
   | otherwise                              = True

-- checks that the heap property is still held valid in every extraction
prop_valid_heap :: Bounded a => Ord a => [a] -> Bool
prop_valid_heap []         = True
prop_valid_heap (l@(x:xs)) = checkChildrenHeap (buildHeapFromList l)


