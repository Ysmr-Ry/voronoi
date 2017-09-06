{-# LANGUAGE PackageImports #-}
{-# LANGUAGE MultiWayIf #-}
module Fortune.Fortune
  ( voronoi
  , Edge' (..)
  , Edge (..)
  , module Fortune.BreakpointTree
  , circleFrom3Points
  )
where

import Fortune.BreakpointTree


import Control.Monad (liftM, join)

import Data.Maybe (maybeToList, catMaybes)
import Data.List (sortOn, sortBy, minimumBy)

--import qualified Data.Vector as V

import qualified Data.Map as Map
import           Data.Map (Map)

--import qualified Data.HashPSQ as PSQ
--import           Data.HashPSQ (HashPSQ)

import qualified Data.Set as Set

import "mtl" Control.Monad.Writer

import Data.Function (on)

type Index = Int
type Coord = Double

--data Point = P !Index !Coord !Coord deriving (Show)

type Point'= (Double, Double)

data Edge  = EmptyEdge | IEdge !Point' | Edge !Point' !Point' deriving Show
data Edge' = Edge' !Index !Index !Point' !Point' deriving (Show)

type NewPointEvent = Point
data CircleEvent   = CircleEvent !Point !Point !Point !Coord !Point'
  deriving (Eq, Ord)

instance Show CircleEvent where
  show (CircleEvent pi pj pk _ _) = show (pindex pi, pindex pj, pindex pk)


data Events = Events
  {
    newPointEvents :: [NewPointEvent]
  , circleEvents   :: Set.Set (Coord, (Index, Index, Index), CircleEvent)
  }

data State = State
  {
    events :: Events
  , breaks :: BTree
  , edges :: Map (Index, Index) Edge
  , prevd  :: Double
  }

type IsCircleEvent = Bool

type Log = Map Double (IsCircleEvent, Map (Index, Index) Edge, BTree, (Index, Index, Index))

-- * Private methods
-- ** Manipulating events


{- |
    > removeCEvent i j k events
    Remove a CircleEvent identified by the 3 indexes /i j k/ from /events/.
-}
removeCEvent :: Point -> Point -> Point -> [CircleEvent]
             -> [CircleEvent]
removeCEvent (P i _ _) (P j _ _) (P k _ _) events =
  let
    predicate x = let CircleEvent (P i' _ _) (P j' _ _) (P k' _ _) _ _ = x in
      i' == i && j' == j && k' == k
    (ls, rs) = break predicate events
  in
    if not (null rs) then ls ++ tail rs else ls

{- |
    > insertEvents newEvents events
    Inserts each Event in /newEvents/ into /events/, keeping the list sorted.
 -}
insertEvents :: [CircleEvent] -> [CircleEvent] -> [CircleEvent]
insertEvents toAdd events =
  let
    insertEvent toAdd' events' = 
      let
        CircleEvent _ _ _ y _ = toAdd'
        (ls, rs) = span (\(CircleEvent _ _ _ y' _) -> y' < y) events'
      in
        if y /= 0 then
          ls ++ toAdd' : rs
        else
          events'
  in
    foldr insertEvent events toAdd

-- ** Helper Functions

pindex (P i _ _) = i
breakNull (Breakpoint (P i _ _) (P j _ _)) = i == 0 && j == 0
pointAtLeftOf (Breakpoint l _) = l
pointAtRightOf (Breakpoint _ r) = r

sortPair a b = if a < b then (a, b) else (b, a)

setVert :: Point' -> Edge -> Edge
setVert p EmptyEdge  = IEdge p
setVert p (IEdge p') = Edge p' p

-- | Returns (Just) the (center, radius) of the circle defined by three given
--   points.
--   If the points are colinear or counter clockwise, it returns Nothing.
circleFrom3Points :: Point -> Point -> Point -> Maybe (Point', Double)
circleFrom3Points (P _ x1 y1) (P _ x2 y2) (P _ x3 y3) =
  let
    (bax, bay) = (x2 - x1, y2 - y1)
    (cax, cay) = (x3 - x1, y3 - y1)
    ba = bax * bax + bay * bay
    ca = cax * cax + cay * cay
    denominator = 2 * (bax * cay - bay * cax)

    x = x1 + (cay * ba - bay * ca) / denominator
    y = y1 + (bax * ca - cax * ba) / denominator
    r = sqrt $ (x-x1) * (x-x1) + (y-y1) * (y-y1)
  in
    if denominator <= 0 then
      Nothing -- colinear points or counter clockwise
    else
      Just ((x, y), r)

circleEvent :: Double -> Point -> Point -> Point -> Maybe CircleEvent
circleEvent h pi pj pk = liftM (\(c@(_, y), r) -> CircleEvent pi pj pk ((y + r)`min`h) c)
  $ circleFrom3Points pi pj pk


-- ** Processing events

processCircleEvent :: Double -> State -> State
processCircleEvent h state = let
  -- state data:
  (_, _, (CircleEvent pi@(P i _ _) pj@(P j _ _) pk@(P k _ _) y p)) = Set.findMin . circleEvents . events $ state
  events' = events $ state
  cevents = circleEvents $ events'
  bTree = breaks state
  d     = y
  d'    = (d + prevd  state) / 2

  -- process breakpoint
  bl = Breakpoint pi pj
  br = Breakpoint pj pk
  newBreak = Breakpoint pi pk
  newBTree = joinPairAt (fst p) bl br d d' bTree

  -- process events
  prevB@(Breakpoint prev@(P previ _ _) (P prevj _ _)) = inOrderPredecessor bl d' bTree
  nextB@(Breakpoint (P nexti _ _) next@(P nextj _ _)) = inOrderSuccessor   br d' bTree

  newCEvents'
    | previ == 0 && prevj == 0 =
      maybeToList $ circleEvent h pi pk next
    | nexti == 0 && nextj == 0 =
      maybeToList $ circleEvent h prev pi pk
    | otherwise =
      catMaybes [circleEvent h pi pk next, circleEvent h prev pi pk]
  
  toRemove
    | previ == 0 && prevj == 0 =
      [(i, j, k), (j, k, nextj)]
    | nexti == 0 && nextj == 0 =
      [(i, j, k), (previ, i, j)]
    | otherwise =
      [(i, j, k), (previ, i, j), (j, k, nextj)]

  insert' ev@(CircleEvent pi pj pk y _) =
    Set.insert (y, (pindex pi, pindex pj, pindex pk), ev)
  removeElem = Set.filter ((`elem`toRemove) . (\(_,a,_) -> a)) cevents
  removed = foldr Set.delete cevents removeElem
  newCEvents = foldr insert' removed newCEvents'

  newEvents = events' { circleEvents = newCEvents }

  -- process edge
  newEdge = IEdge p
  edgesToUpdate = [sortPair (pindex pi) (pindex pj),
                   sortPair (pindex pj) (pindex pk)]
  updatedEdges = foldr (Map.adjust (setVert p)) (edges state) edgesToUpdate
  newEdges = Map.insert (sortPair (pindex pi) (pindex pk)) newEdge updatedEdges

  pretty (a, b, c) = (pindex a, pindex b, pindex c)
  in 
    state { breaks = newBTree, events = newEvents, edges = newEdges, prevd = d }

processNewPointEvent :: Double -> State -> State
processNewPointEvent h state = let
  -- state data:
  newp@(P idx _ d) = head . newPointEvents . events $ state
  newPEvents       = tail . newPointEvents . events $ state
  cEvents = circleEvents . events $ state
  events' = events state
  bTree = breaks state

  (newBTree, fallenOn) = insertPar newp d bTree
  (prev, next) = case fallenOn of
    Left  b -> (inOrderPredecessor b d bTree, b)
    Right b -> (b, inOrderSuccessor b d bTree)
    -- TODO !! inOrderPred.. and inOrderSucc.. shouldn't need d

  pi = if breakNull prev then Nothing else Just $ pointAtLeftOf prev
  pk = if breakNull next then Nothing else Just $ pointAtRightOf next
  pj = case fallenOn of
    Left b -> pointAtLeftOf b
    Right b -> pointAtRightOf b
  
  newCEvents' = catMaybes [ do pi <- pi; circleEvent h pi pj newp
                          , do pk <- pk; circleEvent h newp pj pk]
  
  toRemove = (pi, pj, pk)

  insert' ev@(CircleEvent pi pj pk y _) =
    Set.insert (y, (pindex pi, pindex pj, pindex pk), ev)
  removed = case toRemove of
    (Just i, j, Just k) -> let removeElems = Set.toList $ Set.filter ((==(pindex i,pindex j,pindex k)) . (\(_,a,_) -> a)) cEvents
      in foldr Set.delete cEvents removeElems
    _ -> cEvents
  newCEvents = foldr insert' removed newCEvents'

  newEvents = events' { newPointEvents = newPEvents
                      , circleEvents = newCEvents }

  newEdges = Map.insert (sortPair idx (pindex pj)) EmptyEdge $ 
    edges state

  in
    state { breaks = newBTree, events = newEvents, edges = newEdges, prevd = d }

processEvent :: Double -> Writer Log State -> Writer Log State
processEvent h wri = do
  state <- wri
  let
    (P _ _ nextPointY) = head .  newPointEvents . events $ state
    ((nextCircleY, idxs, _)) = Set.findMin . circleEvents . events $ state
    nextIsCircle
      | (null . newPointEvents .events) state = True
      | (Set.null . circleEvents . events) state = False
      | otherwise = nextCircleY <= nextPointY
  if
    | (null . newPointEvents . events) state && 
      (Set.null . circleEvents . events) state -> return state
    | otherwise -> do 
      if nextIsCircle then do
        tell $ Map.singleton (prevd state) $ (True, edges state, breaks state, idxs)
        return $ processCircleEvent h state
      else do
        tell $ Map.singleton (prevd state) $ (False, edges state, breaks state, (0,0,0))
        return $ processNewPointEvent h state

{- |
    voronoi takes a Vector of pairs of Double(s) and returns a Vector of
    Edge(s) representing the corresponding voronoi diagram.
-}
voronoi :: [Point'] -> Double -> Double -> Writer Log [Edge']
voronoi points w h =
  let
    go :: Writer Log State -> Writer Log [Edge']
    go wri = do
      state <- wri
      if ((null.newPointEvents.events) state) &&
        ((null.circleEvents.events) state) then
        return . mapToList points w h . edges $ state
      else
        go (processEvent h wri)
  in
    go . return . mkState $ points

mkState :: [Point'] -> State
mkState points = let
  ps = sortOn snd points
  newPEvents' = map (\(i, (x, y)) -> P i x y) $ zip [0..] ps
  newPEvents = tail . tail $ newPEvents'
  p0@(P i _ _) = (newPEvents' !! 0)
  p1@(P j _ d) = (newPEvents' !! 1)
  b1 = Breakpoint p0 p1
  b2 = Breakpoint p1 p0
  firstPair = Node Nil b1 $ Node Nil b2 Nil
  firstEdge = Map.singleton (sortPair i j) EmptyEdge
  in
    State (Events newPEvents Set.empty) firstPair firstEdge d

mapToList :: [Point'] -> Double -> Double -> Map (Index, Index) Edge -> [Edge']
mapToList points w h mapD = let
  list' = Map.toList mapD
  iedgeM :: ((Index, Index), Edge) -> ((Index, Index), Edge)
  iedgeM ((i,j), e) = case e of
    Edge p q -> ((i,j), Edge p q)
    IEdge p@(x,y) -> if x >= 0 && x <= w && y >= 0 && y <= h
      then let
          (x1,y1) = points!!i
          (x2,y2) = points!!j
          f x = ((x2**2-x1**2+y2**2-y1**2)/2-(x2-x1)*x)/(y2-y1)
          g y = ((x2**2-x1**2+y2**2-y1**2)/2-(y2-y1)*y)/(x2-x1)
          cands = if
            | y2 /= y1 && x2 /= x1 -> [(0,f 0), (0,f w), (g 0,0), (g h,h)]
            | y2 /= y1             -> [(0,f 0), (0,f w)]
            | x2 /= x1             -> [(g 0,0), (g h,h)]
          dist (a,b) (c,d) = (a-c)**2 + (b-d)**2
          nearestPts pt = sortBy (compare `on` (dist pt)) points
        in if abs (dist p (x1,y1)-dist p (x2,y2)) < 0.01
          then ((i,j), Edge p (minimumBy (compare `on` (dist p)) $ filter ((\x -> (x1,y1)`elem`x && (x2,y2)`elem`x) . take 2 . nearestPts) cands))
          else ((i,j), IEdge p)
      else
        ((i,j), IEdge p)
    EmptyEdge -> ((i,j), EmptyEdge)
      {-
        (x2-x1)*x+(y2-y1)*y = x2^2-x1^2/2+(y2^2-y1^2)/2
      -}
  predicate (_,e) = case e of
    Edge _ _ -> True
    _ -> False
  list = filter predicate $ map iedgeM list'
  edge' ((i, j), Edge l r) = Edge' i j l r
  in
    fmap edge' list
