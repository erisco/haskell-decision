{-# LANGUAGE ScopedTypeVariables, TupleSections #-}
module Decision.Nary where

import Prelude hiding (
  foldl,
  foldr,
  maximum
  )
import Data.List hiding (
  foldl,
  foldr,
  maximum
  )
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Monoid

data Decision a b r =
  Branch {
    branchFunc :: b -> Decision a b r,
    branchArg  :: a
  }
  | Return {
    returnValue :: r
  }
--

padRight :: Int -> String -> String
padRight n s = s ++ replicate (n - length s) ' '

padLeft :: Int -> String -> String
padLeft n s = replicate (n - length s) ' ' ++ s

dom :: (Bounded t, Enum t) => [t]
dom = [minBound..maxBound]

instance (Show a, Bounded b, Enum b, Show b, Show r) => Show (Decision a b r) where
  show = let
    brange = dom :: [b]
    bpadr = maximum . fmap (length . show) $ brange
    showb b = padLeft bpadr (show b) ++ ": "
    f pad (Return r   ) = show r
    f pad (Branch bf a) =
      let pad' = "  " ++ pad
       in show a ++ "?\n" ++ (intercalate "\n" . fmap (\x -> pad ++ showb x ++ (f pad' . bf) x)) brange
    in f "  "
--

instance Functor (Decision a b) where
  fmap = desMap id id
--

instance Applicative (Decision a b) where
  pure    = Return
  x <*> y = follow x (flip desRet' y)
--

instance Monad (Decision a b) where
  return  = Return
  (>>=)   = follow
--

instance (Bounded b, Enum b) => Foldable (Decision a b) where
  foldMap f (Return r)    = f r
  foldMap f (Branch bf _) = mconcat . fmap (foldMap f . bf) $ dom
--

--instance (Bounded b, Enum b) => Traversable (Decision a b) where
--  traverse f (Return r)    = Return <$> f r
--  traverse f (Branch bf a) = flip Branch a <$> (traverse f . bf) ??????
--


desMap :: (a1 -> a2) -> (b2 -> b1) -> (r1 -> r2) -> Decision a1 b1 r1 -> Decision a2 b2 r2
desMap f g h (Branch bf a) = Branch (desMap f g h . bf . g) (f a)
desMap _ _ h (Return r   ) = Return (h r)

desArg' :: (a1 -> a2) -> Decision a1 b r -> Decision a2 b r
desArg' f = desMap f id id

desType' :: (b2 -> b1) -> Decision a b1 r -> Decision a b2 r
desType' f = desMap id f id

desRet' :: (r1 -> r2) -> Decision a b r1 -> Decision a b r2
desRet' = desMap id id


decide :: (a -> b) -> Decision a b r -> r
decide df (Branch bf a) = decide df . bf . df $ a
decide _  (Return r   ) = r

follow ::    Decision a b r1
          -> (r1 -> Decision a b r2)
          -> Decision a b r2
follow root f = let
  branch (Branch bf a) = Branch (branch . bf) a
  branch (Return r   ) = f r
  in branch root
--

range :: (Bounded b, Enum b) => Decision a b r -> [r]
range = foldr (:) []

down :: (a -> c -> c) -> c -> Decision a b r -> Decision c b r
down f acc (Branch bf a) = let acc' = f a acc
                            in Branch (down f acc' . bf) acc'
down f _   (Return r    ) = Return r

down2 :: (a -> c -> c) -> c -> Decision a b r -> Decision (a, c) b r
down2 f c = down (\a (_, c) -> (a, f a c)) (undefined, c)


-- todo: variant that saves the computed tree (more ideal in certain situations)
up :: (Bounded b, Enum b) => (r -> c) -> (a -> [c] -> c) -> Decision a b r -> Decision c b r
up init f = let
  ahead (Branch bf a) = f a . fmap (ahead . bf) $ dom
  ahead (Return r   ) = init r
  branch b@(Branch bf a) = Branch (branch . bf) (ahead b)
  branch   (Return r   ) = Return r
  in branch
--

up2 :: (Bounded b, Enum b) => (r -> c) -> (a -> [c] -> c) -> Decision a b r -> Decision (a, c) b r
up2 init f = up (\r -> (undefined, init r)) (\a ccs -> (a, f a $ fmap snd ccs))


look :: (a -> a -> [b]) -> c -> (r -> c) -> (a -> [c] -> c) -> Decision a b r -> Decision c b r
look sel base init f = let
  
  ahead sel' (Branch bf a) = f a $ fmap (ahead sel' . bf) (sel' a)
  ahead _    (Return r   ) = init r
  
  branch b@(Branch bf a) = Branch (branch . bf) (ahead (sel a) b)
  branch   (Return r   ) = Return r
  
  in branch
--

look2 :: (a -> a -> [b]) -> c -> (r -> c) -> (a -> [c] -> c) -> Decision a b r -> Decision (a, c) b r
look2 sel base init f = look sel (undefined, base) (\r -> (undefined, init r)) (\a ccs -> (a, f a $ fmap snd ccs))


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
dspan :: [a] -> Decision a Bool ([a], [a])
dspan = let
  f yys []     = Return (yys, [])
  f yys (x:xs) = let
    g True  = f (yys ++ [x]) xs
    g False = Return (yys, x:xs)
    in Branch g x
  in f []
--

{-
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}
dgroupBy :: [a] -> Decision (a, a) Bool [[a]]
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
dfilter :: [a] -> Decision a Bool [a]
dfilter = let
  f yys []     = Return yys
  f yys (x:xs) = let
    g True  = f (yys ++ [x]) xs
    g False = f yys xs
    in Branch g x
  in f []
--

{-
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []     = []
nubBy eq (x:xs) = x : nubBy eq (filter (\ y -> not (eq x y)) xs)
-}
dnubBy :: [a] -> Decision (a,a) Bool [a]
dnubBy = let
  f yys []     = return yys
  f yys (x:xs) = desMap (x,) not id (dfilter xs) >>= f (yys ++ [x])
  in f []
--






