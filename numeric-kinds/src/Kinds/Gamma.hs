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

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type-level naturals and integers inspired by Elias-Gamma coding.

-- Could equally say it's inspired by the implicit leading 1 bit of IEEE754
-- mantissas, but that's not as cool, so let's leave it out of the module
-- Haddock in favor of the more pretentious information theory reference.

module Kinds.Gamma where

import Data.Bits (shiftL, shiftR, setBit, testBit)
import Data.Type.Equality ((:~:)(..))
import GHC.TypeLits (TypeError, ErrorMessage(Text))
import GHC.TypeNats (Nat, Div, Mod)
import Numeric.Natural (Natural)

import Data.SNumber (SNumber(SN, N#), sameSNumber, snumberVal)
import DependentLiterals.Int
         ( HasIntLiterals, SNum(..), Satisfying(..), SNumLit(..)
         )
import Kinds.Integer (pattern Pos)
import Kinds.Ord (type (==?), type (/=?), Compare)
import Kinds.Num (type (+), type (*), FromNat, ToInteger, ToNat)

import Unsafe.Coerce
         ( unsafeCoerce
#if MIN_VERSION_base(4, 15, 0)
         , unsafeEqualityProof, UnsafeEquality(..)
#endif
         )

data Gamma = One | Bit Gamma Bool
  deriving (Eq, Ord, Read, Show)

-- A quick evaluation of "singletons" showed that its TH support only exists
-- for GHC 9.0, and I don't want to drop support for every compiler that
-- currently has a Stackage snapshot, so... yeah, no singletons.  It's not
-- /that/ bad to write manually anyway.

data SBool (b :: Bool) where
  SFalse :: SBool False
  STrue :: SBool True

instance Show (SBool b) where
  showsPrec _ = \case
    STrue -> showString "STrue"
    SFalse -> showString "SFalse"

class KnownBool b where sbool :: SBool b
instance KnownBool False where sbool = SFalse
instance KnownBool True where sbool = STrue

reifyBool :: SBool b -> (KnownBool b => r) -> r
reifyBool STrue r = r
reifyBool SFalse r = r

data SGamma (n :: Gamma) where
  SOne :: SGamma 'One
  SBit :: SGamma n -> SBool b -> SGamma (Bit n b)
  deriving HasIntLiterals via SNumLit (SGammaCheck n) (SGamma n)

instance Show (SGamma n) where
  showsPrec p = \case
    SOne -> showString "SOne"
    SBit n b -> showParen (p > 10) $
      showString "SBit " .
      showsPrec 11 n .
      showChar ' ' .
      showsPrec 11 b

unsafeCastSGamma :: SGamma m -> SGamma n
unsafeCastSGamma = unsafeCoerce

-- Given a (possibly-expensive) equality proof, return a fake one of the same
-- type that doesn't evaluate the real one.  This is fine iff the proof is
-- total; otherwise, it allows proving nonsense, e.g.
-- @unsafeAssertTotal (let x = x in x :: Int :~: Bool)@
unsafeAssertTotal :: forall a b. a :~: b -> a :~: b
unsafeAssertTotal _ =
#if MIN_VERSION_base(4, 15, 0)
  case unsafeEqualityProof @a @b of UnsafeRefl -> Refl
#else
  unsafeCoerce (Refl :: a :~: a)
#endif

gammaToNatIso :: n :~: NatToGamma (GammaToNat n)
gammaToNatIso = unsafeCoerce (Refl :: n :~: n)

class (ToNat n ~ m, n ~ FromNat m) => SGammaConstraint (n :: Gamma) m
instance (ToNat n ~ m, n ~ FromNat m) => SGammaConstraint n m

class SGammaConstraint n m => SGammaCheck n a m
instance SGammaConstraint n m => SGammaCheck n a m

instance SNum (SGamma n) where
  type SNumRepr (SGamma n) = Natural
  type SNumConstraint (SGamma n) = SGammaConstraint n

  fromSNum (Satisfying (SN x))
    | x == 0    = error "Impossible: SNumber 0 with SGammaConstraint"
    | otherwise = go x unsafeCastSGamma
   where
    go :: Natural -> (forall a. SGamma a -> r) -> r
    go 1 k = k SOne
    go n k
      | n > 1 =
          let !n' = n `shiftR` 1
              !b = testBit n 0
          in  go n' $ \bs -> if b then k (SBit bs STrue) else k (SBit bs SFalse)
      | otherwise = error "Impossible: SNumber < 1 with SGammaConstraint"

  intoSNum sg =
    case gammaToNatIso @n of Refl -> Satisfying (N# (go sg))
   where
    go :: SGamma m -> Natural
    go SOne = 1
    go (SBit bs b) = putBit b (go bs `shiftL` 1)

    putBit :: SBool b -> Natural -> Natural
    putBit STrue  = (`setBit` 0)
    putBit SFalse = id

reifyGamma :: SGamma n -> (KnownGamma n => r) -> r
reifyGamma SOne r = r
reifyGamma (SBit n b) r = reifyBool b $ reifyGamma n r

class KnownGamma (n :: Gamma) where sgamma :: SGamma n
instance KnownGamma One where sgamma = SOne
instance (KnownGamma n, KnownBool b) => KnownGamma (Bit n b) where
  sgamma = SBit sgamma sbool

-- type-level bidirection pattern synonym?
type family Bit' (n :: GammaNat) (b :: Bool) = (r :: Gamma) | r -> n b where
  Bit' (NP x) b    = Bit x b
  Bit' NZ     True = One

type Odd (x :: Nat) = 1 ==? Mod x 2

type family NatToGamma (n :: Nat) :: Gamma where
  NatToGamma 0 = TypeError (Text "Invalid NatToGamma 0: Gamma represents >= 1")
  NatToGamma 1 = One
  NatToGamma n = Bit (NatToGamma (Div n 2)) (Odd n)

type instance FromNat n = NatToGamma n

type family BitToNat (b :: Bool) :: Nat where
  BitToNat False = 0
  BitToNat True  = 1

type family GammaToNat (n :: Gamma) :: Nat where
  GammaToNat One = 1
  GammaToNat (Bit x b) = 2 * GammaToNat x + BitToNat b

type instance ToNat x = GammaToNat x
type instance ToInteger x = Pos (GammaToNat x)

type family (x :: Bool) || (y :: Bool) :: Bool where
  True  || x = True
  False || x = x

type family (x :: Bool) && (y :: Bool) :: Bool where
  True  && x = x
  False && x = False

type family FullAddCarry (c :: Bool) (x :: Bool) (y :: Bool) where
  FullAddCarry True x y  = x || y
  FullAddCarry False x y = x && y

type family FullAddSum (c :: Bool) (x :: Bool) (y :: Bool) where
  FullAddSum True  x y = x ==? y
  FullAddSum False x y = x /=? y

type family SuccGamma (n :: Gamma) :: Gamma where
  -- 1 + 1 = 2
  SuccGamma One = Bit One False
  -- (2n + 1) + 1 = 2(n+1) + 0
  SuccGamma (Bit x True) = Bit (SuccGamma x) False
  -- (2n + 0) + 1 = 2n + 1
  SuccGamma (Bit x False) = Bit x True

type Two = Bit One False

type family SuccCarryGamma (c :: Bool) (n :: Gamma) :: Gamma where
  SuccCarryGamma True n  = AddGamma Two n
  SuccCarryGamma False n = SuccGamma n

type family AddCarryGamma (c :: Bool) (x :: Gamma) (y :: Gamma) where
  AddCarryGamma c One y = SuccCarryGamma c y
  AddCarryGamma c x One = SuccCarryGamma c x
  AddCarryGamma c (Bit xs x) (Bit ys y) =
    Bit (AddCarryGamma (FullAddCarry c x y) xs ys) (FullAddSum c x y)

type AddGamma x y = AddCarryGamma False x y

type instance x + y = AddGamma x y

-- | @TimesExp2 x y@ is @2^x * y@, i.e. @'shiftL' y x@.
type family TimesExp2 (x :: GammaNat) (y :: Gamma) where
  -- 2^0 * y = y
  TimesExp2 NZ y = y
  -- 2^x * y = 2(2^(x-1) * y) + 0  | x > 0
  TimesExp2 (NP x) y = Bit (TimesExp2 (PredGamma x) y) False

type Exp2 x = TimesExp2 x One

type family AddIf (b :: Bool) (x :: Gamma) (y :: Gamma) where
  AddIf True  x y = x + y
  AddIf False x y = y

-- Left-biased, i.e. deconstructs the left to construct a summation of shifted
-- copies of the right.
type family TimesGamma (x :: Gamma) (y :: Gamma) where
  TimesGamma One y = y
  TimesGamma (Bit xs x) y = AddIf x y (TimesGamma xs (Bit y False))

type instance x * y = TimesGamma x y

type family SAppendOrdering (x :: Ordering) (y :: Ordering) :: Ordering where
  SAppendOrdering EQ y = y
  SAppendOrdering x  y = x

type family IfThenElse (b :: Bool) (t :: k) (f :: k) :: k where
  IfThenElse True t f = t
  IfThenElse False t f = f

type family CmpBool (x :: Bool) (y :: Bool) where
  CmpBool False x = IfThenElse x LT EQ
  CmpBool True x  = IfThenElse x EQ GT

type family CmpGamma (x :: Gamma) (y :: Gamma) where
  CmpGamma One One        = EQ
  CmpGamma One (Bit ys y) = LT
  CmpGamma (Bit xs x) One = GT
  CmpGamma (Bit xs x) (Bit ys y) =
    SAppendOrdering (CmpGamma xs ys) (CmpBool x y)

type instance Compare x y = CmpGamma x y

-- | Naturals formed by adjoining a zero onto 'Gamma'.
data GammaNat = NZ | NP Gamma

data SGammaNat (n :: GammaNat) where
  SZ :: SGammaNat NZ
  SP :: SGamma n -> SGammaNat (NP n)
  deriving HasIntLiterals via SNumLit (SGammaNatCheck n) (SGammaNat n)

class (ToNat n ~ m, n ~ FromNat m) => SGammaNatConstraint (n :: GammaNat) m
instance (ToNat n ~ m, n ~ FromNat m) => SGammaNatConstraint n m

class SGammaNatConstraint n m => SGammaNatCheck n a m
instance SGammaNatConstraint n m => SGammaNatCheck n a m

instance SNum (SGammaNat n) where
  type SNumRepr (SGammaNat n) = Natural
  type SNumConstraint (SGammaNat n) = SGammaNatConstraint n

  fromSNum (Satisfying (sn :: SNumber Natural x)) =
    case sameSNumber (snumberVal @0) sn of
      Just Refl -> SZ
      _ -> case unsafeCoerce (Refl :: n :~: n) :: n :~: NP (NatToGamma x) of
        Refl -> SP (fromSNum (Satisfying sn))

  intoSNum SZ = Satisfying snumberVal
  intoSNum (SP n) = case intoSNum n of
    Satisfying (n' :: SNumber Natural x) ->
      case unsafeCoerce (Refl :: n :~: n) :: NatToGNat x :~: n of
        Refl -> Satisfying n'

-- | Heh, @GNat@.
type family NatToGNat (n :: Nat) :: GammaNat where
  NatToGNat 0 = NZ
  NatToGNat n = NP (FromNat n)

type instance FromNat n = NatToGNat n

type family GNatToNat (n :: GammaNat) :: Nat where
  GNatToNat NZ     = 0
  GNatToNat (NP x) = GammaToNat x

type instance ToNat n = GNatToNat n

type instance ToInteger n = Pos (GNatToNat n)

-- | @BitOne n@ is @2n+1@ as a 'Gamma' (since it's always nonzero).
type family BitOne (n :: GammaNat) :: Gamma where
  BitOne NZ = One
  BitOne (NP x) = Bit x True

bitOne :: SGammaNat n -> SGamma (BitOne n)
bitOne SZ = SOne
bitOne (SP n) = SBit n STrue

type family GammaNatBit (n :: GammaNat) (b :: Bool) :: GammaNat where
  GammaNatBit x      True  = NP (BitOne x)
  GammaNatBit NZ     False = NZ
  GammaNatBit (NP x) False = NP (Bit x False)

-- | The predecessor of a 'Gamma' as 'GammaNat'.
--
-- This is total, since 'Gamma' is inherently nonzero, and 'GammaNat' augments
-- it with a zero value.
type family PredGamma (n :: Gamma) :: GammaNat where
  -- 1 - 1 = 0
  PredGamma One = NZ
  -- (2n + 0) - 1 = 2(n-1) + 1  | n > 0      (and it is, because it's 'Gamma')
  PredGamma (Bit x False) = NP (BitOne (PredGamma x))
  -- (2n + 1) - 1 = 2n
  PredGamma (Bit x True) = NP (Bit x False)

predGamma :: SGamma n -> SGammaNat (PredGamma n)
predGamma SOne = SZ
predGamma (SBit bs b) = case b of
  SFalse -> SP (bitOne (predGamma bs))
  STrue  -> SP (SBit bs SFalse)

type family GammaNatPlus (x :: GammaNat) (y :: GammaNat) :: GammaNat where
  GammaNatPlus NZ     y      = y
  GammaNatPlus x      NZ     = x
  GammaNatPlus (NP x) (NP y) = NP (x + y)

type instance x + y = GammaNatPlus x y

type family TimesGammaNat (x :: GammaNat) (y :: GammaNat) :: GammaNat where
  TimesGammaNat NZ y = NZ
  TimesGammaNat x NZ = NZ
  TimesGammaNat (NP x) (NP y) = NP (x * y)

type instance x * y = TimesGammaNat x y

type family CmpGammaNat (x :: GammaNat) (y :: GammaNat) :: Ordering where
  CmpGammaNat NZ     NZ     = EQ
  CmpGammaNat NZ     y      = LT
  CmpGammaNat x      NZ     = GT
  CmpGammaNat (NP x) (NP y) = Compare x y

type instance Compare x y = CmpGammaNat x y