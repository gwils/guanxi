{-# language PatternSynonyms #-}

module Relative.Base
  ( View(..)
  , Cons(..)
  , Uncons(..)
  , Snoc(..)
  , Unsnoc(..)
  , Nil(..)
  , Singleton(..)
  , Q
  , Cat
  , Rev(..)
  , pattern Nil
  , pattern Cons
  , pattern Snoc
  , Relative(..)
  , RelativeSemigroup
  , RelativeMonoid
  ) where

import Relative.Internal
