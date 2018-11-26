{-# language DeriveTraversable #-}
{-# language RankNTypes #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language BangPatterns #-}
{-# language ViewPatterns #-}

-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- Skew binary random access lists with cheaper "missing" entries

module Unaligned.Skew
  ( Skew(..)
  , var, var'
  , lookup
  , Cons_(..)
  , allocate
  , empty
  ) where

import Control.Lens (fusing, Lens', FunctorWithIndex(..), FoldableWithIndex(..), TraversableWithIndex(..))
import Data.Bits
import Data.Functor
import Prelude hiding (lookup)
import Unaligned

shr :: Int -> Int
shr j = unsafeShiftR j 1
{-# inline shr #-}

smear :: Int -> Int
smear i0 = i5 .|. unsafeShiftR i5 32 where
      i5 = i4 .|. unsafeShiftR i4 16
      i4 = i3 .|. unsafeShiftR i3 8
      i3 = i2 .|. unsafeShiftR i2 4
      i2 = i1 .|. unsafeShiftR i1 2
      i1 = i0 .|. unsafeShiftR i0 1

data Tree a
  = Bin a !(Tree a) !(Tree a)
  | Bin_ !(Tree a) !(Tree a)
  | Tip
  deriving (Show, Foldable, Functor, Traversable)

data Spine a = Cons !Int !(Tree a) !(Spine a) | Nil
  deriving (Show, Foldable, Functor, Traversable)

instance FunctorWithIndex Int Spine where imapped = itraversed
instance FoldableWithIndex Int Spine where ifolded = itraversed

instance TraversableWithIndex Int Spine where
  itraverse f = go 0 where
    go !_ Nil = pure Nil
    go i (Cons j t s) = Cons j <$> goTree i j t <*> go (i+j) s
    goTree _ _ Tip = pure Tip
    goTree i (shr -> j) (Bin a l r) = Bin <$> f i a <*> goTree (i-1) j l <*> goTree (i-j-1) j r
    goTree i (shr -> j) (Bin_ l r) = Bin_ <$> goTree (i-1) j l <*> goTree (i-j-1) j r
  {-# inline itraverse #-}

bin :: Maybe a -> Tree a -> Tree a -> Tree a
bin Nothing Tip Tip = Tip
bin Nothing l r = Bin_ l r
bin (Just a) l r = Bin a l r
{-# inline conlike bin #-}

bin_ :: Tree a -> Tree a -> Tree a
bin_ Tip Tip = Tip
bin_ l r = Bin_ l r
{-# inline conlike bin_ #-}

padSpine :: Int -> Spine a -> Spine a
padSpine 0 xs = xs
padSpine i Nil = padSpine' i (smear i) Nil
padSpine i xs@(Cons j x Nil)
  | i >= j+1  = padSpine (i-j+1) $ Cons (j+j+1) (bin_ Tip x) Nil
  | otherwise = padSpine' i (unsafeShiftR j 1) xs
padSpine i xs@(Cons j x ys@(Cons k y zs))
  -- climb up and inflate heads as needed
  | j == k    = padSpine (i-1)   $ Cons (j+k+1) (bin_ x y) zs
  | i >= j+1  = padSpine (i-j+1) $ Cons (j+j+1) (bin_ Tip x) ys
  | otherwise = padSpine' i (unsafeShiftR j 1) xs

padSpine' :: Int -> Int -> Spine a -> Spine a
padSpine' 0 _ ws = ws
padSpine' i j ws
  | i >= j = padSpine' (i-j) j $ Cons j Tip ws
  | otherwise = padSpine' i (unsafeShiftR j 1) ws

instance Nil Spine where
  nil = Nil
  {-# inline conlike nil #-}

instance Cons Spine where
  cons a (Cons i x (Cons j y zs)) | i == j = Cons (i+j+1) (Bin a x y) zs
  cons a xs = Cons 1 (Bin a Tip Tip) xs
  {-# inline conlike cons #-}

class Cons_ t where
  cons_ :: t a -> t a

instance Cons_ Spine where
  cons_ (Cons i x (Cons j y zs)) | i == j = Cons (i+j+1) (bin_ x y) zs
  cons_ xs = Cons 1 Tip xs
  {-# inline conlike cons_ #-}

data Skew a = Skew {-# unpack #-} !Int {-# unpack #-} !Int !(Spine a)
  deriving (Functor, Foldable, Traversable, Show)

empty :: Skew a
empty = Skew 0 0 Nil

instance Nil Skew where
  nil = Skew 0 0 nil
  {-# inline conlike nil #-}

instance Cons Skew where
  cons a (Skew i j xs) = Skew (i+1) (i+1) (cons a (padSpine (i-j) xs))
  {-# inline conlike cons #-}

instance Cons_ Skew where
  cons_ (Skew i j xs) = Skew (i+1) j xs
  {-# inline conlike cons_ #-}

instance FoldableWithIndex Int Skew where ifolded = itraversed
instance FunctorWithIndex Int Skew where imapped = itraversed
instance TraversableWithIndex Int Skew where
  itraverse f (Skew j k s) = Skew j k <$> itraverse (\i -> f (k-1-i)) s

-- the allocate i s -- returns an integer j and you now "own" slots [j..j+i-1]
allocate :: Int -> Skew a -> (Int, Skew a)
allocate i (Skew j k xs) = (j, Skew (j+i) k xs)

lookup :: Int -> Skew a -> Maybe a
lookup i (Skew j k xs)
  | i > j     = error "variable impossibly new"
  | i > k     = Nothing
  | otherwise = lookupSpine (k - i - 1) xs

lookupSpine :: Int -> Spine a -> Maybe a
lookupSpine _ Nil = error "variable impossibly old"
lookupSpine i (Cons j t xs)
  | i < j     = lookupTree i j t
  | otherwise = lookupSpine (i - j) xs

lookupTree :: Int -> Int -> Tree a -> Maybe a
lookupTree _ _ Tip = Nothing
lookupTree i (shr -> j) (Bin a l r)
  | i == 0 = Just a
  | i <= j = lookupTree (i-1) j l
  | otherwise = lookupTree (i-j-1) j r
lookupTree i (shr -> j) (Bin_ l r)
  | i == 0 = Nothing
  | i <= j = lookupTree (i-1) j l
  | otherwise = lookupTree (i-j-1) j r

-- type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

var :: Int -> Lens' (Skew a) (Maybe a)
var = fusing . var'

var' :: Int -> Lens' (Skew a) (Maybe a)
var' i f (Skew j k xs)
  | i > j     = error "variable impossibly new"
  | i > k     = f Nothing <&> \case
    Nothing -> Skew j k xs
    Just a  -> Skew j (i+1) $ cons a $ padSpine (i - k - 1) xs
  | otherwise = Skew j k <$> varSpine (k - i - 1) f xs

varSpine :: Int -> Lens' (Spine a) (Maybe a)
varSpine _ _ Nil = error "variable impossibly old"
varSpine i f (Cons j t xs)
  | i < j     = (\t' -> Cons j t' xs) <$> varTree i j f t
  | otherwise = Cons j t <$> varSpine (i - j) f xs

-- place a fresh leaf down inside a tree appropriately
tweak :: Int -> Int -> Maybe a -> Tree a
tweak _ _ Nothing = Tip
tweak i0 j0 (Just a0) = go i0 j0 a0 where
  go :: Int -> Int -> a -> Tree a
  go i (shr -> j) a
    | i == 0 = Bin a Tip Tip
    | i <= j = Bin_ (go (i-1) j a) Tip
    | otherwise = Bin_ Tip $ go (i-j-1) j a
{-# inline tweak #-}

varTree :: Int -> Int -> Lens' (Tree a) (Maybe a)
varTree i j f Tip = tweak i j <$> f Nothing
varTree i (shr -> j) f (Bin a l r)
  | i == 0    = (\ma -> bin ma l r) <$> f (Just a)
  | i <= j   = (\l' -> Bin a l' r) <$> varTree (i-1) j f l
  | otherwise = Bin a l <$> varTree (i-j-1) j f r
varTree i (shr -> j) f (Bin_ l r)
  | i == 0    = (\ma -> bin ma l r) <$> f Nothing
  | i <= j   = (\l' -> bin_ l' r) <$> varTree (i-1) j f l
  | otherwise = bin_ l <$> varTree (i-j-1) j f r