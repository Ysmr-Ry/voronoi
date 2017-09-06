{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE LambdaCase #-}

module Voronoi.Main where

import Core.Util
import Core.World
import Core.Ease
import Core.Front
import Core.Shape
import Core.Render
import Core.UI
import Core.View

import Haste.DOM

import Fortune.Fortune

import "mtl" Control.Monad.Writer
import Data.Function (on)
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import System.Random

launch :: Canvas -> World ()
launch cvs = do
  view <- consView
  state <- makeMVar view
  onFrame state $ \s -> render cvs $ s^.rendering
  spawn $ emitting $ forever $ do
    s <- withMVar state get
    applyTransform $ s^.rendering
    sleep 1
  return ()

consView :: World (View FocusEvent)
consView = do
  let screenSize' = fmap (_1%~(/2)) screenSize
      (w,h) = v2 $ act screenSize'
  (rw,rh) <- io screenSize'
  pts <- io $ fmap (sortOn snd . take 10 . nubBy (\(a,_) (b,_) -> abs (a-b) < 5) . nubBy (\(_,a) (_,b) -> abs (a-b) < 5)) $ replicateM 100 $ do
    x <- randomRIO (0,rw)
    y <- randomRIO (0,rh)
    return (x,y)
  d <- ease 0 400 linear
  let
    (edges', vor) = runWriter $ voronoi pts rw rh
    gray = (0.15,0.15,0.15,1)
    shape = rect (0,0) (w,h)
    render = do
      fill white $ rect (0,0) (w,h)
      iforM_ pts $ \i (x,y) -> do
        fill gray $ circle (po x,po y) 5
        fill gray $ text "mplus" (po $ show i) LeftAlign TopBase (v2 $ po (x-10,y-10)) 10
      stroke 2 gray $ line (0,morph d) (w,morph d)
      io (valueIO (morph d)) >>= \case
        Just rd -> do
          let convPt i (x,y) = P i x y
          case snd <$> Map.lookupLT rd vor of
              --next = snd $ fromJust $ Map.lookupGE rd vor
            Just prev -> do
              let prevEdges = Map.toList $ prev^._2
                  iedges = flip filter prevEdges $ \(_,e) -> case e of
                    IEdge _ -> True
                    otherwise -> False 
                  edges = flip filter prevEdges $ \(_,e) -> case e of
                    Edge _ _ -> True
                    otherwise -> False
             {--forM_ iedges $ \((i,j), IEdge p@(x,y)) -> when (x >= 0 && x <= rw && y >= 0 && y <= rh) $ do
                let dist (a,b) (c,d) = (a-c)**2+(b-d)**2
                    ps = [pts Prelude.!! i, pts Prelude.!! j]
                    bx = intersection (convPt i $ ps Prelude.!! 0) (convPt j $ ps Prelude.!! 1) rd
                    by = evalParabola (convPt i $ ps Prelude.!! 0) rd bx
                stroke 2 gray $ line ((both%~po) p) $ (both%~po) (bx,by)
              forM_ edges $ \(_, Edge p q) -> do
                stroke 2 gray $ line ((both%~po) p) $ (both%~po) q--}
              let btree = prev^._3
              
              clip (rect (0,0) (w,h)) $ do
                forM_ iedges $ \((i,j), IEdge p@(x,y)) -> do
                  fill (1,0,0,1) $ circle ((both%~po) p) 5
                  fill gray $ text "mplus" (po $ show (i,j)) LeftAlign TopBase (v2 $ po (x-10,y-10)) 10
                --fill (0.2,0.2,0.2,1) $ text "mplus" (po $ show $ filter (\(_, IEdge (x,y)) -> x >= 0 && x <= rw && y >= 0 && y <= rh) iedges) LeftAlign TopBase (20,20) 10
                when (prev^._1) $ do
                  let (i,j,k) = prev^._4
                  case circleFrom3Points (convPt i $ pts Prelude.!! i) (convPt j $ pts Prelude.!! j) (convPt k $ pts Prelude.!! k) of
                    Just (center, r) -> stroke 2 (1,0,0,1) $ circle (v2 $ po center) (po r)
                    Nothing -> return ()
                let leaves = nub $ concatMap (\(Breakpoint p q) -> [p, q]) $ inOrder btree
                iforM_ leaves $ \i p@(P _ _ y) -> do
                  let prvP = if i > 0 then Just (leaves Prelude.!! (i-1)) else Nothing
                      nxtP = if i < length leaves-1 then Just (leaves Prelude.!! (i+1)) else Nothing
                      fi = fromIntegral
                      sx = if i > 0 then intersection (fromJust prvP) p rd else 0
                      ex = if i < length leaves-1 then intersection p (fromJust nxtP) rd else rw
                      step = if (ex-sx)/15 > 20 then (ex-sx)/50 else (ex-sx)/15
                  when (y <= rd) $ forM_ [sx,sx+step..ex] $ \x1 -> do
                    let from = (x1 `min` ex) `max` sx
                        to = ((x1+step) `min` ex) `max` sx
                        y1 = evalParabola p rd from
                        y2 = evalParabola p rd to

                    when (y1 >= 0 && y1 <= rh) $ do
                      stroke 2 (0,0.5,1,1) $ line ((both%~po) (from,y1)) $ (both%~po) (to,y2)
                --fill gray $ text "mplus" (po $ show leaves) LeftAlign TopBase (v2 $ po (20,20)) 10
              let mkTree (ox,oy) flr pad Nil = []
                  mkTree (ox,oy) flr pad n@(Node l (Breakpoint (P i _ _) (P j _ _)) r) = mkTree (ox-pad, oy+1.5*pad`max`15) False (pad/2) l ++ [((ox,oy), (i,j), n, pad, flr)] ++ mkTree (ox+pad, oy+1.5*pad`max`15) True (pad/2) r
                  tree = mkTree (rw/2,rw/5+30) True (rw/5) btree
              forM_ tree $ \(p,(i,j),n,rad,flr) -> do
                let p' = (_1%~(+rw)) p
                stroke 2 gray $ circle ((both%~po) p') (po rad)
                fill gray $ text "mplus" (po $ show (i,j)) CenterAlign MiddleBase (if (rad/2) > 10 then p' & both %~ po else p' & _1 %~ (if flr then (+ (rad+15)) else (subtract (rad+15))) & both %~ po) (po $ (rad/2) `max` 10)
                stroke 2 gray $ do
                  let isLeft (Node Nil _ _) = Nothing
                      isLeft (Node l _ _) = Just l
                      isLeft Nil = Nothing
                      isRight (Node _ _ Nil) = Nothing
                      isRight (Node _ _ r) = Just r
                      isRight Nil = Nothing
                      nl = isLeft n
                      nr = isRight n
                  when (isJust nl) $ do
                    let
                      Node _ (Breakpoint (P i _ _) (P j _ _)) _ = fromJust nl
                      (q,_,_,_,_) = head $ filter ((==(i,j)) . (^._2)) tree
                      q' = (_1%~(+rw)) q
                      (px, py) = p'
                      (qx, qy) = q'
                      norm = sqrt $ (qx-px)**2 + (qy-py)**2
                      (nx, ny) = ((qx-px)/norm, (qy-py)/norm)
                      sp = (px+nx*rad, py+ny*rad)
                      ep = (qx-nx*rad/2, qy-ny*rad/2)
                    line (sp & both %~ po) (ep & both %~ po)
                  when (isJust nr) $ do
                    let
                      Node _ (Breakpoint (P i _ _) (P j _ _)) _ = fromJust nr
                      (q,_,_,_,_) = head $ filter ((==(i,j)) . (^._2)) tree
                      q' = (_1%~(+rw)) q
                      (px, py) = p'
                      (qx, qy) = q'
                      norm = sqrt $ (qx-px)**2 + (qy-py)**2
                      (nx, ny) = ((qx-px)/norm, (qy-py)/norm)
                      sp = (px+nx*rad, py+ny*rad)
                      ep = (qx-nx*rad/2, qy-ny*rad/2)
                    line (sp & both %~ po) (ep & both %~ po)

            Nothing -> return ()
          {-iforM_ pts $ \i (x,y) -> do
            when (y <= rd) $ forM_ [0,10..rw] $ \x1 -> do
              let y1 = evalParabola (convPt i (x,y)) rd x1
                  y2 = evalParabola (convPt i (x,y)) rd (x1+10)

              when (y1 >= 0 && y1 <= rh) $ do
                stroke 2 (0,0.5,1,1) $ line ((both%~po) (x1,y1)) $ (both%~po) (x1+10,y2)-}
        Nothing -> return ()
      clip (rect (0,0) (w,h)) $ forM_ edges' $ \(Edge' i j p q) -> do
        stroke 2 (0,1,0.2,1) $ line ((both%~po) p) $ (both%~po) q
        fill gray $ text "mplus" (po $ show (i,j)) LeftAlign TopBase ((both%~po) p) 10        
    handler = forever $ do
      d ~~> rh+100
      d ~~>! rh+100
      d ==> 0

  makeView Just shape render $ \box -> do
    fork handler