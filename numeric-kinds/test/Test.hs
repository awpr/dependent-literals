-- Copyright 2021 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# OPTIONS_GHC -fplugin=DependentLiterals.Plugin #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Prelude hiding ((!!))

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))

import Kinds.Gamma
import Kinds.Num (FromNat, ToNat)

x1 :: SGamma (FromNat 4)
x1 = 4

f0 :: SGamma n -> String
f0 = show

x2 :: String
x2 = f0 4275

x3 :: SGamma n -> Maybe (n :~: FromNat 6)
x3 = \case
  6 -> Just Refl
  _ -> Nothing

x4 :: SGamma n -> Maybe (ToNat n :~: 984964165)
x4 = \case
  984964165 -> Just Refl
  _ -> Nothing

{-
type family If b f a where
  If True f a = f a
  If False f a = a

type family Nest n f a where
  Nest One f a = f a
  Nest (Bit bs b) f a = Nest bs f (Nest bs f (If b f a))
-}

type family ListType n a where
  ListType NZ a = [a]
  ListType (NP n) a = a -> ListType (PredGamma n) a

list :: forall a n. SGammaNat n -> ListType n a
list = go id
 where
  go :: forall m. ([a] -> [a]) -> SGammaNat m -> ListType m a
  go rest SZ     = rest []
  go rest (SP n) = \x -> go (rest . (x:)) (predGamma n)

listUsage :: IO ()
listUsage = do
  print $ list 5 'a' 'b' 'c' 'd' 'e'
  print $ list 3 'a' 'b' 'c'
  print $ list @Char 0

type family Index xs i where
  Index (x : xs) NZ     = x
  Index (x : xs) (NP i) = Index xs (PredGamma i)

data HList (ts :: [Type]) where
  HNil :: HList '[]
  HCons :: a -> HList as -> HList (a : as)

hlistIndex :: HList ts -> SGammaNat i -> Index ts i
hlistIndex (HCons x _)  SZ = x
hlistIndex (HCons _ xs) (SP i) = hlistIndex xs (predGamma i)
hlistIndex _ _ = error "This should have already type-errored"

class IsTuple1 a where
  type HElems a :: [Type]
  toHList :: a -> HList (HElems a)
  fromHList :: HList (HElems a) -> a

instance IsTuple1 (a, b) where
  type HElems (a, b) = [a, b]
  toHList (a, b) = HCons a (HCons b HNil)
  fromHList (HCons a (HCons b HNil)) = (a, b)

class IsTuple a where
  type TupleIndex a (i :: GammaNat) :: Type
  tupleIndex :: a -> SGammaNat i -> TupleIndex a i
  tupleTabulate :: (forall i. SGammaNat i -> TupleIndex a i) -> a

{-
(!!) :: IsTuple a => a -> SGammaNat i -> TupleIndex a i
(!!) = tupleIndex
-}

instance IsTuple (a, b) where
  type TupleIndex (a, b) i = Index '[a, b] i
  tupleIndex (a, b) = \case
    0 -> a
    1 -> b
    _ -> error "Impossible"
  tupleTabulate f = (f 0, f 1)

instance IsTuple (a, b, c) where
  type TupleIndex (a, b, c) i = Index '[a, b, c] i
  tupleIndex (a, b, c) = \case
    0 -> a
    1 -> b
    2 -> c
    _ -> error "Impossible"
  tupleTabulate f = (f 0, f 1, f 2)

instance IsTuple (a, b, c, d) where
  type TupleIndex (a, b, c, d) i = Index '[a, b, c, d] i
  tupleIndex (a, b, c, d) = \case
    0 -> a
    1 -> b
    2 -> c
    3 -> d
    _ -> error "Impossible"
  tupleTabulate f = (f 0, f 1, f 2, f 3)

{-
tupleUsage :: IO ()
tupleUsage = do
  let t0 = (True, False, "hi")
  print $ t0 !! 2
  print $ t0 !! 1

  let t1 = tupleTabulate @(String, Int, Bool) $ \case
        0 -> "hi"
        1 -> 42
        2 -> True
        _ -> error "Impossible"
  print t1
-}


(!!) :: (a, b, c) -> SGammaNat i -> Index [a, b, c] i
(!!) (a, b, c) = \case
  0 -> a
  1 -> b
  2 -> c
  _ -> error "Impossible: Index would have been irreducible"

main :: IO ()
main = print $ ("aoeu", True, Just [42 :: Int]) !! 2
