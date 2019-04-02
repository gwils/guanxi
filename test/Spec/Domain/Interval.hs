{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}

module Spec.Domain.Interval where

import Control.Applicative
import Data.Foldable (traverse_)
import Data.Ratio
import Domain.Internal
import FD.Monad
import Ref
import Relative.Base (plus)
import Test.Hspec

spec :: Spec
spec = do
  describe "Domain.Interval" $ do
    describe "known" $ do
      it "known bottom = Nothing" $ do
        let
          result = run $
            bottom >>= known
        result `shouldBe` [Nothing]
      it "known [1..5] = Nothing" $ do
        let
          result = run $
            1...5 >>= known
        result `shouldBe` [Nothing]
      it "known . abstract = Just" $ do
        let
          result = run $
            known (abstract 5)
        result `shouldBe` [Just 5]

    describe "negatei" $ do
      it "negates an interval" $ do
        let
          result = run $ do
            input <- 1...5
            r <- bottom
            negatei input r
            input `gtz` 4
            known r
        result `shouldBe` [Just (-5)]
      it "propagates information backwards" $ do
        let
          result = run $ do
            input <- 1...5
            r <- bottom
            negatei input r
            r `ltz` (-4)
            known input
        result `shouldBe` [Just 5]

    describe "absi" $ do
      it "passes through a positive number unchanged" $ do
        let
          result = run $ do
            let input = abstract 20
            output <- bottom
            absi input output
            known output
        result `shouldBe` [Just 20]
      it "negates a negative number" $ do
        let
          result = run $ do
            let input = abstract (-30)
            output <- bottom
            absi input output
            known output
        result `shouldBe` [Just 30]

    describe "comparisons" $ do
      let
        pair :: FD s (Interval (FD s))
        pair = 1...2
        knowns a b = (,) <$> known a <*> known b
        concretes a b = (,) <$> concrete a <*> concrete b
      it "[1..2] eq [1..2]" $ do
        let
          result = run $ do
            x <- pair; y <- pair
            x `eq` y
            concretes x y
        result `shouldBe` [(1,1), (2,2)]
      it "[1] eq [1..2]" $ do
        let
          result = run $ do
            let x = abstract 1
            y <- pair
            x `eq` y
            knowns x y
        result `shouldBe` [(Just 1, Just 1)]
      it "[1..2] eq [2]" $ do
        let
          result = run $ do
            x <- pair
            let y = abstract 2
            x `eq` y
            knowns x y
        result `shouldBe` [(Just 2, Just 2)]
      -- it "[1..2] lt [1..2]" $ do
      --   let
      --     result = run $ do
      --       x <- pair; y <- pair
      --       x `lt` y
      --       knowns x y
      --   result `shouldBe` [(Just 1,Just 2)]
      -- it "[1..2] gt [1..2]" $ do
      --   let
      --     result = run $ do
      --       x <- pair
      --       y <- pair
      --       x `gt` y
      --       knowns x y
      --   result `shouldBe` [(Just 2,Just 1)]
      it "[1] le [1..2]" $ do
        let
          result = run $ do
            let x = abstract 1
            y <- pair
            x `le` y
            knowns x y
        result `shouldBe` [(Just 1, Nothing)]
      it "[1..2] le [1]" $ do
        let
          result = run $ do
            x <- pair
            let y = abstract 1
            x `le` y
            knowns x y
        result `shouldBe` [(Just 1, Just 1)]
      it "1 ne [1..2]" $ do
        let
          result = run $ do
            let x = abstract 1
            y <- 1...2
            x `ne` y
            known y
        result `shouldBe` [Just 2]
      it "2 ne [1..2]" $ do
        let
          result = run $ do
            let x = abstract 2
            y <- 1...2
            x `ne` y
            known y
        result `shouldBe` [Just 1]
      -- it "[1..5] ne [1..5]" $ do
      --   let
      --     result = run $ do
      --       x <- 1...5
      --       y <- 1...5
      --       x `ne` y
      --       concrete x
      --   result `shouldBe` [1,2,3,4,5]
      it "[1..5] ne 5" $ do
        let
          result = run $ do
            x <- 1...5
            x `ne` abstract 5
            concrete x
        result `shouldBe` [1,2,3,4]
      it "3 zle [1..5]" $ do
        let
          result = run $ do
            x <- 1...5
            3 `zle` x
            concrete x
        result `shouldBe` [3,4,5]
      it "1 zle [1..5]" $ do
        let
          result = run $ do
            x <- 1...5
            1 `zle` x
            concrete x
        result `shouldBe` [1,2,3,4,5]
      it "5 zle [1..5]" $ do
        let
          result = run $ do
            x <- 1...5
            5 `zle` x
            known x
        result `shouldBe` [Just 5]
      it "6 zle [1..5]" $ do
        let
          result = run $ do
            x <- 1...5
            6 `zle` x
            concrete x
        result `shouldBe` []
      it "0 zle [1..5]" $ do
        let
          result = run $ do
            x <- 1...5
            0 `zle` x
            concrete x
        result `shouldBe` [1,2,3,4,5]
      it "[1..5] lez 3" $ do
        let
          result = run $ do
            x <- 1...5
            x `lez` 3
            concrete x
        result `shouldBe` [1,2,3]
      it "[1..5] lez 1" $ do
        let
          result = run $ do
            x <- 1...5
            x `lez` 1
            concrete x
        result `shouldBe` [1]
      it "[1..5] lez 5" $ do
        let
          result = run $ do
            x <- 1...5
            x `lez` 5
            concrete x
        result `shouldBe` [1,2,3,4,5]
      it "[1..5] lez 6" $ do
        let
          result = run $ do
            x <- 1...5
            x `lez` 6
            concrete x
        result `shouldBe` [1,2,3,4,5]
      it "[1..5] lez 0" $ do
        let
          result = run $ do
            x <- 1...5
            x `lez` 0
            concrete x
        result `shouldBe` []

    describe "<|>" $ do
      it "right id" $ do
        let
          result = run $
            pure 3 <|> empty
        result `shouldBe` [3 :: Integer]
      it "left id" $ do
        let
          result = run $
            empty <|> pure 4
        result `shouldBe` [4 :: Integer]

    -- Art of the Propagator section 6.3
    describe "baker cooper fletcher miller and smith" $ do
      it "finds a solution" $ do
        let
          result = run $ do
            let
              floors = 1...5
              allDistinct [] = pure ()
              allDistinct (x:xs) = traverse_ (ne x) xs *> allDistinct xs
              notAdjacent a b = a `lt` plus b (-1) <|> a `gt` plus b 1

            -- make all tenants
            b <- floors
            c <- floors
            f <- floors
            m <- floors
            s <- floors

            -- Nobody lives on the same floor
            allDistinct [b,c,f,m,s]

            -- constraints
            b `nez` 5
            c `nez` 1
            f `nez` 5
            f `nez` 1
            m `gt` c

            -- cooper does not live directly above or below fletcher
            -- smith does not live directly above or below fletcher
            notAdjacent c f
            notAdjacent s f

            traverse concrete [b,c,f,m,s]

        result `shouldBe` [[3,2,4,5,1]]

    -- Art of the Propagator section 3
    describe "A barometer, a stopwatch, and a ruler" $ do
      it "finds a solution" $ do
        let
          result = run $ do
            let
              fallDuration t h = do
                g <- pure (abstract 10)
                let half = abstract 5
                t2 <- bottom
                gt2 <- bottom
                square t t2
                mult g t2 gt2
                mult half gt2 h

            buildingHeight <- bottom

            -- drop the barometer off the building and time the fall
            fallTime <- pure (abstract 3)
            fallDuration fallTime buildingHeight

            concrete buildingHeight
        result `shouldBe` [5]

-- -- Fixed point numbers with three decimal places of precision
-- -- Put differently, thousandths
-- newtype Fixed3 = Fixed3 Integer
--   deriving (Eq, Ord, Enum)

-- instance Num Fixed3 where
--   fromInteger i = Fixed3 (i*100)
--   Fixed3 i + Fixed3 j = Fixed3 (i + j)
--   Fixed3 i * Fixed3 j = Fixed3 (i*j `div` 1000)
--   Fixed3 i - Fixed3 j = Fixed3 (i - j)
--   negate (Fixed3 i) = Fixed3 (negate i)
--   abs (Fixed3 i) = Fixed3 (abs i)
--   signum (Fixed3 i) = Fixed3 (signum i)

-- instance Real Fixed3 where
--   toRational (Fixed3 i) = i % 1000

-- instance Integral Fixed3 where
--   toInteger (Fixed3 i) = i `div` 1000
--   div (Fixed3 i) (Fixed3 j) = Fixed3 $ i*1000 `div` j
--   quotRem = undefined

mult :: MonadRef m => Interval m -> Interval m -> Interval m -> m ()
mult i j o = do
  onLo i $ \x -> onLo j $ \y -> o `gez` (x*y `div` 1)
  onLo j $ \y -> onLo i $ \x -> o `gez` (x*y `div` 1)
  onHi i $ \x -> onHi j $ \y -> o `lez` (x*y `div` 1)
  onHi j $ \y -> onHi i $ \x -> o `lez` (x*y `div` 1)

square :: MonadRef m => Interval m -> Interval m -> m ()
square i o = do
  onLo i $ \x -> o `gez` (x*x `div` 1)
  onHi i $ \x -> o `lez` (x*x `div` 1)
