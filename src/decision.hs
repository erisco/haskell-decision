-- Module for representing and investigating possible decisions
-- of higher order recursive functions.
-- (work in progress)
-- by Eric Brisco (eric.brisco@gmail.com)
{-# LANGUAGE TupleSections #-}
module Decision where

import Data.Enumerable

data BiDecision a b i r =
  BiDecision {
    biInput :: i,           -- Input to the decision
    biBMap  :: b -> BiLR,   -- Branch mapping function
    biRoot  :: BiTree a r   -- Root node
  }
--


data BiTree a r =
  BiBranch {
    biLeft   :: BiTree a r,  -- Left branch
    biRight  :: BiTree a r,  -- Right branch
    biArg    :: a            -- Next branch argument
  }
  | BiReturn {
    biReturn :: r            -- Function return value
  }
--


data Cont s a r =
  More {
    contState  :: s,  -- Next state
    contArg    :: a   -- Next branch argument
  }
  | Last {
    contReturn :: r   -- Function return value
  }
  deriving Show
--

data BiLR = BiLeft | BiRight
  deriving Show
--

biRoot' :: (BiTree a1 r1 -> BiTree a2 r2) -> BiDecision a1 b i r1 -> BiDecision a2 b i r2
biRoot' f d = d { biRoot = f . biRoot $ d }

biBMap' :: ((b -> BiLR) -> b -> BiLR) -> BiDecision a b i r -> BiDecision a b i r
biBMap' f d = d { biBMap = f . biBMap $ d }

biArg' :: (a1 -> a2) -> BiTree a1 r -> BiTree a2 r
biArg' f (BiBranch l r a) = BiBranch (biArg' f l) (biArg' f r) (f a)
biArg' _ (BiReturn r    ) = BiReturn r

instance (Show i, Show a, Show b, Show r, Enumerable b) => Show (BiDecision a b i r) where
  show (BiDecision i m r) = let
    bmap = fmap (\x -> (x, m x)) enumerate
    tree = unlines . fmap (\x -> replicate 2 ' ' ++ x) . lines . show $ r
    in "BiDecision {\n"
       ++ "  input = " ++ show i ++ "\n"
       ++ "  map   = " ++ show bmap ++ "\n"
       ++ "  tree  =\n"
       ++ tree
       ++ "}"
--

instance (Show a, Show r) => Show (BiTree a r) where
  show = let
    f pad (BiReturn r    ) = pad ++ show r
    f pad (BiBranch l r a) = let
      pad' = "| " ++ pad
      in pad ++ show a ++ "-+\n" ++ f pad' l ++ "\n" ++ f pad' r
    in f ""
--


bi ::    (i -> Cont s a r)   -- Root function
      -> (s -> Cont s a r)   -- Left branch function
      -> (s -> Cont s a r)   -- Right branch function
      -> (b -> BiLR)         -- Branch map
      -> i                   -- Input
      -> BiDecision a b i r
bi init f g m i = let
  branch (More s' a) = BiBranch (branch $ f s') (branch $ g s') a
  branch (Last r   ) = BiReturn r
  in BiDecision i m (branch $ init i)
--

biFollow ::    BiDecision a b i r1
            -> (r1 -> BiDecision a b i r2)
            -> BiDecision a b i r2
biFollow (BiDecision i m1 root) f = let
  branch (BiBranch l r a) = BiBranch (branch l) (branch r) a
  -- todo: check m1, m2 and switch branches if necessary
  branch (BiReturn r    ) = case f r of (BiDecision _ _ root') -> root'
  in BiDecision i m1 (branch root)
--

biDecide :: (Eq b) => (a -> b) -> BiDecision a b i r -> r
biDecide df (BiDecision _ mf root) = let
  branch (BiBranch l r a) = case mf . df $ a of 
                              BiLeft  -> branch l
                              BiRight -> branch r
  branch (BiReturn r    ) = r
  in branch root
--

biRange :: BiDecision a b i r -> [r]
biRange (BiDecision _ _ root) = let
  branch (BiReturn r    ) = [r]
  branch (BiBranch l r _) = branch l ++ branch r
  in branch root
--

biTrivial :: i -> (b -> BiLR) -> r -> BiDecision a b i r
biTrivial i m r = BiDecision i m (BiReturn r)

biArgMap :: (a1 -> a2) -> BiDecision a1 b i r -> BiDecision a2 b i r
biArgMap = biRoot' . biArg'

biBMapMap :: ((b -> BiLR) -> b -> BiLR) -> BiDecision a b i r -> BiDecision a b i r
biBMapMap = biBMap'

revBMap :: (b -> BiLR) -> b -> BiLR
revBMap f b = case f b of
                BiLeft  -> BiRight
                BiRight -> BiLeft                
--


--
-- Examples
--


bmap :: Bool -> BiLR
bmap True  = BiLeft
bmap False = BiRight

bmapr :: Bool -> BiLR
bmapr = revBMap bmap

{-
span :: (a -> Bool) -> [a] -> ([a],[a])
span xs@[]              =  (xs, xs)
span p xs@(x:xs')
         | p x          =  let (ys,zs) = span p xs' in (x:ys,zs)
         | otherwise    =  ([],xs)
-}
dspan :: [a] -> BiDecision a Bool [a] ([a], [a])
dspan = let
  root         [] = Last ([], [])
  root yys@(y:ys) = More (y, [], ys) y
  left  (a, xxs,   []) = Last (xxs ++ [a], [])
  left  (a, xxs, y:ys) = More (y, xxs ++ [a], ys) y
  right (a, xxs, yys ) = Last (xxs, a:yys)
  in bi root left right bmap
--

{-
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}
dgroupBy :: [a] -> BiDecision (a, a) Bool [a] [[a]]
dgroupBy = let
  f grps []     = biTrivial [] bmap grps
  f grps (x:xs) = biArgMap (x,) (dspan xs) `biFollow` \(ys, zs) -> f (grps ++ [x:ys]) zs
  in f []
--

{-
filter :: (a -> Bool) -> [a] -> [a]
filter _pred []    = []
filter pred (x:xs)
  | pred x         = x : filter pred xs
  | otherwise      = filter pred xs
-}
dfilter :: [a] -> BiDecision a Bool [a] [a]
dfilter = let
  root []     = Last []
  root (x:xs) = More (x, [], xs) x
  left  (a, yys, []    ) = Last (yys ++ [a])
  left  (a, yys, (x:xs)) = More (x, yys ++ [a], xs) x
  right (_, yys, []    ) = Last yys
  right (_, yys, (x:xs)) = More (x, yys, xs) x
  in bi root left right bmap
--

{-
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []     = []
nubBy eq (x:xs) = x : nubBy eq (filter (\ y -> not (eq x y)) xs)
-}
dnubBy :: [a] -> BiDecision (a,a) Bool [a] [a]
dnubBy = let
  dfilter_ x = biBMapMap (revBMap) . biArgMap (x,) . dfilter 
  f yys []     = biTrivial [] bmapr yys
  f yys (x:xs) = dfilter_ x xs `biFollow` \xs' -> f (yys ++ [x]) xs'
  in f []
--












