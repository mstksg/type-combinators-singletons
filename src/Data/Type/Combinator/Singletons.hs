{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- |
-- Module      : Data.Type.Combinator.Singletons
-- Description : Conversions between datatypes in /type-combinators/ and
--               singletons from /singletons/.
-- Copyright   : (c) Justin Le 2017
-- License     : BSD-3
-- Maintainer  : justin@jle.im
-- Stability   : unstable
-- Portability : portable
--
-- There's a lot of identical data types between /type-combinators/ and
-- /singetons/, as well as similar typeclasses.  This module provides
-- conversion functions between the two, and also many appropriate
-- instances.
--

module Data.Type.Combinator.Singletons (
    prodSing
  , singProd
  , singLength
  , boolSing
  , singBool
  , Sing(SZ, SS), SN, ZSym0, SSym0, SSym1
  , natSing
  , singNat
  , parSing
  , singPar
  , choiceSing
  , singChoice
  , optionSing
  , singOption
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           Data.Type.Boolean
import           Data.Type.Conjunction
import           Data.Type.Disjunction
import           Data.Type.Length
import           Data.Type.Option
import           Data.Type.Product
import           Type.Class.Higher
import           Type.Class.Known
import           Data.Type.Nat
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Family.Nat

instance SingI a => Known Sing a where
    type KnownC Sing a = SingI a
    known = sing

instance Witness ØC (SingI a) (Sing a) where
    x \\ s = withSingI s x

instance SEq k => Eq1 (Sing :: k -> Type) where
    eq1  x y = fromSing $ x %:== y
    neq1 x y = fromSing $ x %:/= y

instance SOrd k => Ord1 (Sing :: k -> Type) where
    compare1 x y = fromSing $ sCompare x y
    x <# y       = fromSing $ x %:< y
    x ># y       = fromSing $ x %:> y
    x <=# y      = fromSing $ x %:<= y
    x >=# y      = fromSing $ x %:>= y

-- | Convert a 'Prod' of 'Sing's of individual values in @as@ to a 'Sing'
-- for all @as@ together.
prodSing :: Prod Sing as -> Sing as
prodSing = \case
    Ø       -> SNil
    x :< xs -> x `SCons` prodSing xs

-- | Convert a 'Sing' for @as@ to a 'Prod' of 'Sing's of each individual
-- value in @as@.
singProd :: Sing as -> Prod Sing as
singProd = \case
    SNil         -> Ø
    x `SCons` xs -> x :< singProd xs

-- | Convert a 'Sing' for @as@ into a 'Length' representing the length of
-- @as@.
--
-- @'Length' as@ is equivalent to @'Prod' 'Proxy' as@, so this is basically
--
-- @
-- 'singLength' = 'map1' ('const' 'Proxy') . 'singProd'
-- @
singLength :: Sing as -> Length as
singLength = \case
    SNil         -> LZ
    _ `SCons` xs -> LS (singLength xs)

-- | Convert a 'Boolean' singleton for @a@ into the 'Sing' singleton for
-- @a@.
boolSing :: Boolean b -> Sing b
boolSing = \case
    False_ -> SFalse
    True_  -> STrue

-- | Convert a 'Sing' singleton for @b@ to a 'Boolean' singleton for @b@.
singBool :: Sing b -> Boolean b
singBool = \case
    SFalse -> False_
    STrue  -> True_

genSingletons [''N]

-- | Convert a 'Nat' singleton for @n@ to a 'Sing' singleton for @n@.
natSing :: Nat n -> Sing n
natSing = \case
    Z_   -> SZ
    S_ n -> SS (natSing n)

-- | Convert a 'Sing' singleton for @n@ to a 'Nat' singleton for @n@.
singNat :: Sing n -> Nat n
singNat = \case
    SZ   -> Z_
    SS n -> S_ (singNat n)

-- | Convert a ':*:' tupling of @'Sing' a@ and @'Sing' b@ into a single
-- 'Sing' for @'(a, b)@.
parSing :: (Sing :*: Sing) '(a, b) -> Sing '(a, b)
parSing (x :*: y) = STuple2 x y

-- | Convert a 'Sing' of @'(a, b)@ to a ':*:' tupling of @'Sing' a@ and
-- @'Sing' b@.
singPar :: Sing '(a, b) -> (Sing :*: Sing) '(a, b)
singPar (STuple2 x y) = x :*: y

-- | Convert a ':+:' sum between a @'Sing' a@ and @'Sing' b@ into
-- a 'Sing' of a sum ('Either') of @a@ and @b@.
choiceSing :: (Sing :+: Sing) e -> Sing e
choiceSing = \case
    L' x -> SLeft x
    R' x -> SRight x

-- | Convert a 'Sing' of a sum ('Either') of @a@ and @b@ to a ':+:' sum
-- between @'Sing' a@ and @'Sing' b@.
singChoice :: Sing e -> (Sing :+: Sing) e
singChoice = \case
    SLeft x  -> L' x
    SRight x -> R' x

-- | Convert an 'Option' of @'Sing' a@ to a 'Sing' of an optional ('Maybe')
-- @a@.
optionSing :: Option Sing a -> Sing a
optionSing = \case
    Nothing_ -> SNothing
    Just_ x  -> SJust x

-- | Convert a 'Sing' of an optional ('Maybe') @a@ to an 'Option' of
-- @'Sing' a@.
singOption :: Sing a -> Option Sing a
singOption = \case
    SNothing -> Nothing_
    SJust x  -> Just_ x
