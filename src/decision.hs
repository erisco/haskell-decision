-- Module for representing and investigating possible decisions
-- of higher order recursive functions.
-- (work in progress)
-- by Eric Brisco (eric.brisco@gmail.com)
{-# LANGUAGE TupleSections #-}
module Decision.Bi where

import Prelude hiding (
  foldr,
  foldl,
  foldl1
  )
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Monoid hiding (
  Last
  )
--

data Decision a r =
  Branch {
    branchLeft  :: Decision a r, -- Left branch
    branchRight :: Decision a r, -- Right branch
    branchArg   :: a             -- Next branch argument
  }
  | Return {
    returnValue :: r             -- Function return value
  }
--

data Cont s a r =
  More {
    moreState  :: s,  -- Next state
    moreArg    :: a   -- Next branch argument
  }
  | Last {
    lastReturn :: r   -- Function return value
  }
  deriving Show
--

instance (Show a, Show r) => Show (Decision a r) where
  show = let
    f pad (Return r    ) = pad ++ show r
    f pad (Branch l r a) = let
      pad' = "| " ++ pad
      in pad ++ show a ++ "-+\n" ++ f pad' l ++ "\n" ++ f pad' r
    in f ""
--

instance Functor (Decision a) where
  fmap = desMap id
--

instance Applicative (Decision a) where
  pure    = Return
  x <*> y = follow x (flip desRet' y)
--

instance Monad (Decision a) where
  return  = Return
  (>>=)   = follow
--

instance Foldable (Decision a) where
  foldMap f (Return r)     = f r
  foldMap f (Branch l r _) = foldMap f l <> foldMap f r
--

instance Traversable (Decision a) where
  traverse f (Return r)     = Return <$> f r
  traverse f (Branch l r a) = (\l' r' -> Branch l' r' a) <$> traverse f l <*> traverse f r
--

desMap :: (a1 -> a2) -> (r1 -> r2) -> Decision a1 r1 -> Decision a2 r2
desMap f g (Branch l r a) = Branch (desMap f g l) (desMap f g r) (f a)
desMap _ g (Return r    ) = Return (g r)

desFlip :: Decision a r -> Decision a r
desFlip (Branch l r a) = Branch (desFlip r) (desFlip l) a
desFlip r              = r

desArg' :: (a1 -> a2) -> Decision a1 r -> Decision a2 r
desArg' f = desMap f id

desRet' :: (r1 -> r2) -> Decision a r1 -> Decision a r2
desRet' = desMap id


build ::    (s -> Cont s a r)   -- Left branch function
         -> (s -> Cont s a r)   -- Right branch function
         -> Cont s a r          -- Initial input result
         -> Decision a r
build f g init = let
  branch (More s' a) = Branch (branch $ f s') (branch $ g s') a
  branch (Last r   ) = Return r
  in branch init
--

follow ::    Decision a r1
          -> (r1 -> Decision a r2)
          -> Decision a r2
follow root f = let
  branch (Branch l r a) = Branch (branch l) (branch r) a
  branch (Return r    ) = f r
  in branch root
--

decide :: (Bounded b, Enum b) => (a -> b) -> Decision a r -> r
decide f = let
  which b l r = case [b..minBound] of
                  [] -> r
                  _  -> l
  branch (Branch l r a) = branch $ which (f a) l r
  branch (Return r    ) = r
  in branch
--

range :: Decision a r -> [r]
range = foldr (:) []

down :: (a -> c -> c) -> c -> Decision a r -> Decision c r
down f acc (Branch l r a) = let acc' = f a acc
                             in Branch (down f acc' l) (down f acc' r) acc'
down f _   (Return r    ) = Return r

down2 :: (a -> c -> c) -> c -> Decision a r -> Decision (a, c) r
down2 f c = down (\a (_, c) -> (a, f a c)) (undefined, c)

-- Equiv to but has better performance than:
--   look (const . const $ LookLR) undefined
up :: (r -> c) -> (a -> c -> c -> c) -> Decision a r -> Decision c r
up init f = let
  branch (Branch l r a) = let (l', lv) = branch l
                              (r', rv) = branch r
                              a' = f a lv rv
                           in (Branch l' r' a', a')
  branch (Return r    ) = (Return r, init r)
  in fst . branch
--

up2 :: (r -> c) -> (a -> c -> c -> c) -> Decision a r -> Decision (a, c) r
up2 init f = up (\r -> (undefined, init r)) (\a (_, c1) (_, c2) -> (a, f a c1 c2))


data Look = LookL | LookR | LookLR | LookNA

look :: (a -> a -> Look) -> c -> (r -> c) -> (a -> c -> c -> c) -> Decision a r -> Decision c r
look sel base init f = let
  
  ahead sel' (Branch l r a) =
    case sel' a of
      LookL  -> f a (ahead sel' l) base
      LookR  -> f a base           (ahead sel' r)
      LookLR -> f a (ahead sel' l) (ahead sel' r)
      LookNA -> f a base           base
  ahead _     (Return r    ) = init r
  
  branch b@(Branch l r a) = Branch (branch l) (branch r) (ahead (sel a) b)
  branch   (Return r    ) = Return r
  
  in branch
--

look2 :: (a -> a -> Look) -> c -> (r -> c) -> (a -> c -> c -> c) -> Decision a r -> Decision (a, c) r
look2 sel base init f = look sel (undefined, base) (\r -> (undefined, init r)) (\a (_, c1) (_, c2) -> (a, f a c1 c2))

order :: (Enum a) => (a, a) -> (b, b) -> (b, b)
order (a1, a2) b@(b1, b2) = case [a1..a2] of
                            [] -> (b2, b1)
                            _  -> b
--



--
-- Examples
--

{-
span :: (a -> Bool) -> [a] -> ([a],[a])
span xs@[]              =  (xs, xs)
span p xs@(x:xs')
         | p x          =  let (ys,zs) = span p xs' in (x:ys,zs)
         | otherwise    =  ([],xs)
-}
dspan :: [a] -> Decision a ([a], [a])
dspan = let
  root         [] = Last ([], [])
  root yys@(y:ys) = More (y, [], ys) y
  true  (a, xxs,   []) = Last (xxs ++ [a], [])
  true  (a, xxs, y:ys) = More (y, xxs ++ [a], ys) y
  false (a, xxs, yys ) = Last (xxs, a:yys)
  (left, right) = order (True, False) (true, false)
  in build left right . root
--

{-
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}
dgroupBy :: [a] -> Decision (a, a) [[a]]
dgroupBy = let
  f grps []     = return grps
  f grps (x:xs) = desArg' (x,) (dspan xs) >>= \(ys, zs) -> f (grps ++ [x:ys]) zs
  in f []
--

{-
filter :: (a -> Bool) -> [a] -> [a]
filter _pred []    = []
filter pred (x:xs)
  | pred x         = x : filter pred xs
  | otherwise      = filter pred xs
-}
dfilter :: [a] -> Decision a [a]
dfilter = let
  root []     = Last []
  root (x:xs) = More (x, [], xs) x
  true  (a, yys, []    ) = Last (yys ++ [a])
  true  (a, yys, (x:xs)) = More (x, yys ++ [a], xs) x
  false (_, yys, []    ) = Last yys
  false (_, yys, (x:xs)) = More (x, yys, xs) x
  (left, right) = order (True, False) (true, false)
  in build left right . root
--

{-
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []     = []
nubBy eq (x:xs) = x : nubBy eq (filter (\ y -> not (eq x y)) xs)
-}
dnubBy :: [a] -> Decision (a,a) [a]
dnubBy = let
  f yys []     = return yys
  f yys (x:xs) = desFlip (desArg' (x,) (dfilter xs)) >>= f (yys ++ [x])
  in f []
--



























