-- Module for representing and investigating possible decisions
-- of higher order recursive functions.
-- (work in progress)
-- by Eric Brisco (eric.brisco@gmail.com)
{-# LANGUAGE TupleSections #-}
module Decision where

data BiDecision a b r =
  BiDecision {
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

biRoot' :: (BiTree a1 r1 -> BiTree a2 r2) -> BiDecision a1 b r1 -> BiDecision a2 b r2
biRoot' f d = d { biRoot = f . biRoot $ d }

biBMap' :: ((b -> BiLR) -> b -> BiLR) -> BiDecision a b r -> BiDecision a b r
biBMap' f d = d { biBMap = f . biBMap $ d }

biArg' :: (a1 -> a2) -> BiTree a1 r -> BiTree a2 r
biArg' f (BiBranch l r a) = BiBranch (biArg' f l) (biArg' f r) (f a)
biArg' _ (BiReturn r    ) = BiReturn r

instance (Show a, Show b, Show r, Enum b, Bounded b) => Show (BiDecision a b r) where
  show (BiDecision m r) = let
    bmap = fmap (\x -> (x, m x)) (enumFromTo minBound maxBound)
    tree = unlines . fmap (\x -> replicate 2 ' ' ++ x) . lines . show $ r
    in "BiDecision {\n"
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


bi ::    (s -> Cont s a r)   -- Left branch function
      -> (s -> Cont s a r)   -- Right branch function
      -> (b -> BiLR)         -- Branch map
      -> Cont s a r          -- Initial input result
      -> BiDecision a b r
bi f g m init = let
  branch (More s' a) = BiBranch (branch $ f s') (branch $ g s') a
  branch (Last r   ) = BiReturn r
  in BiDecision m (branch init)
--

biFollow ::    BiDecision a b r1
            -> (r1 -> BiDecision a b r2)
            -> BiDecision a b r2
biFollow (BiDecision m root) f = let
  branch (BiBranch l r a) = BiBranch (branch l) (branch r) a
  branch (BiReturn r    ) = case f r of (BiDecision _ root') -> root'
  in BiDecision m (branch root)
--

biDecide :: (a -> b) -> BiDecision a b r -> r
biDecide df (BiDecision mf root) = let
  branch (BiBranch l r a) = case mf . df $ a of
                              BiLeft  -> branch l
                              BiRight -> branch r
  branch (BiReturn r    ) = r
  in branch root
--

biRange :: BiDecision a b r -> [r]
biRange (BiDecision _ root) = let
  branch (BiReturn r    ) = [r]
  branch (BiBranch l r _) = branch l ++ branch r
  in branch root
--

biTrivial :: (b -> BiLR) -> r -> BiDecision a b r
biTrivial m r = BiDecision m (BiReturn r)

biArgMap :: (a1 -> a2) -> BiDecision a1 b r -> BiDecision a2 b r
biArgMap = biRoot' . biArg'

biBMapMap :: ((b -> BiLR) -> b -> BiLR) -> BiDecision a b r -> BiDecision a b r
biBMapMap = biBMap'

revBMap :: (b -> BiLR) -> b -> BiLR
revBMap f b = case f b of
                BiLeft  -> BiRight
                BiRight -> BiLeft                
--

biDown :: (a -> c -> c) -> c -> BiDecision a b r -> BiDecision c b r
biDown f c = let
  branch acc (BiBranch l r a) = let acc' = f a acc
                                 in BiBranch (branch acc' l) (branch acc' r) acc'
  branch _   (BiReturn r    ) = BiReturn r
  in biRoot' (branch c)
--

biDown2 :: (a -> c -> c) -> c -> BiDecision a b r -> BiDecision (a, c) b r
biDown2 f c = biDown (\a (_, c) -> (a, f a c)) (undefined, c)

-- Equiv to but has better performance than:
--   biLook (const . const $ BiLookLR) undefined
biUp :: (r -> c) -> (a -> c -> c -> c) -> BiDecision a b r -> BiDecision c b r
biUp init f = let
  branch (BiBranch l r a) = let (l', lv) = branch l
                                (r', rv) = branch r
                                a' = f a lv rv
                            in (BiBranch l' r' a', a')
  branch (BiReturn r    ) = (BiReturn r, init r)
  in biRoot' (fst . branch)
--

biUp2 :: (r -> c) -> (a -> c -> c -> c) -> BiDecision a b r -> BiDecision (a, c) b r
biUp2 init f = biUp (\r -> (undefined, init r)) (\a (_, c1) (_, c2) -> (a, f a c1 c2))

data BiLook = BiLookL | BiLookR | BiLookLR | BiLookNA

biLook :: (a -> a -> BiLook) -> c -> (r -> c) -> (a -> c -> c -> c) -> BiDecision a b r -> BiDecision c b r
biLook look base init f = let
  
  ahead look' (BiBranch l r a) = case look' a of
                                   BiLookL  -> f a (ahead look' l) base
                                   BiLookR  -> f a base            (ahead look' r)
                                   BiLookLR -> f a (ahead look' l) (ahead look' r)
                                   BiLookNA -> f a base            base
  ahead _     (BiReturn r    ) = init r
  
  branch b@(BiBranch l r a) = BiBranch (branch l) (branch r) (ahead (look a) b)
  branch   (BiReturn r    ) = BiReturn r
  
  in biRoot' branch
--

biLook2 :: (a -> a -> BiLook) -> c -> (r -> c) -> (a -> c -> c -> c) -> BiDecision a b r -> BiDecision (a, c) b r
biLook2 look base init f = biLook look (undefined, base) (\r -> (undefined, init r)) (\a (_, c1) (_, c2) -> (a, f a c1 c2))

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
dspan :: [a] -> BiDecision a Bool ([a], [a])
dspan = let
  root         [] = Last ([], [])
  root yys@(y:ys) = More (y, [], ys) y
  left  (a, xxs,   []) = Last (xxs ++ [a], [])
  left  (a, xxs, y:ys) = More (y, xxs ++ [a], ys) y
  right (a, xxs, yys ) = Last (xxs, a:yys)
  in bi left right bmap . root
--

{-
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}
dgroupBy :: [a] -> BiDecision (a, a) Bool [[a]]
dgroupBy = let
  f grps []     = biTrivial bmap grps
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
dfilter :: [a] -> BiDecision a Bool [a]
dfilter = let
  root []     = Last []
  root (x:xs) = More (x, [], xs) x
  left  (a, yys, []    ) = Last (yys ++ [a])
  left  (a, yys, (x:xs)) = More (x, yys ++ [a], xs) x
  right (_, yys, []    ) = Last yys
  right (_, yys, (x:xs)) = More (x, yys, xs) x
  in bi left right bmap . root
--

{-
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []     = []
nubBy eq (x:xs) = x : nubBy eq (filter (\ y -> not (eq x y)) xs)
-}
dnubBy :: [a] -> BiDecision (a,a) Bool [a]
dnubBy = let
  dfilter_ x = biBMapMap (revBMap) . biArgMap (x,) . dfilter 
  f yys []     = biTrivial bmapr yys
  f yys (x:xs) = dfilter_ x xs `biFollow` \xs' -> f (yys ++ [x]) xs'
  in f []
--












