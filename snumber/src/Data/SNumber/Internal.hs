-- Copyright 2020-2021 Google LLC
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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.SNumber.Internal
  ( IsLessThanMaxBound
  , OutOfReprRangeErr
  ) where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import GHC.TypeNats (type (-), CmpNat, Nat)
import Kinds.Ord (Compare)

type ShowTypedNum a n = 'ShowType n ':<>: 'Text " :: " ':<>: 'ShowType a

type ShowRange min maxp1 =
  'Text "(" ':<>: 'ShowType min ':<>: 'Text ".." ':<>:
  'ShowType (maxp1 - 1) ':<>: 'Text ")"

type NegativeReprUnsignedMsg repr a n =
  'Text "Negative SNumber with unsigned witness type:" ':$$:
  'Text "  " ':<>: ShowTypedNum (a n) n

class NegativeReprUnsignedErr repr (a :: Nat -> Type) (n :: Nat)
instance TypeError (NegativeReprUnsignedMsg repr a n)
      => NegativeReprUnsignedErr repr a n

type OutOfReprRangeMsg min maxp1 repr a n =
  'Text "SNumber overflows witness type:" ':$$:
  'Text "  " ':<>: ShowTypedNum (a n) n ':$$:
  'Text "The representable range is " ':<>: ShowRange min maxp1

class OutOfReprRangeErr
        (min :: Nat)
        (maxp1 :: Nat)
        repr
        (a :: Nat -> Type)
        (n :: Nat)
instance TypeError (OutOfReprRangeMsg min maxp1 repr a n)
      => OutOfReprRangeErr min maxp1 repr a n

type family AssertLT o msg :: Constraint where
  AssertLT 'LT  c = ()
  AssertLT o    c = c

type family AssertLessThanMaxBound
    u
    (n :: Nat)
    (maxp1 :: Nat)
    (err :: Constraint) where
  AssertLessThanMaxBound '() n maxp1 err = AssertLT (CmpNat n maxp1) err

type family Reduce (x :: k) :: ()
type instance Reduce 'LT = '()
type instance Reduce 'EQ = '()
type instance Reduce 'GT = '()
type instance Reduce 'True = '()
type instance Reduce 'False = '()

class IsLessThanMaxBound
        (maxp1 :: Nat)
        (err :: Nat -> Constraint)
        (n :: Nat)
instance AssertLessThanMaxBound (Reduce (Compare n maxp1)) n maxp1 (err n)
      => IsLessThanMaxBound maxp1 err n
