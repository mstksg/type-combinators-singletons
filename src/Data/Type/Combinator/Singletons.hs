{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- |
-- Module      : Data.Type.Combinator.Singletons
-- Description : Conversions between datatypes in /type-combinators/ and
--               singletons from /singletons/ and orphan instances.
-- Copyright   : (c) Justin Le 2017
-- License     : BSD-3
-- Maintainer  : justin@jle.im
-- Stability   : unstable
-- Portability : portable
--
-- There's a lot of identical data types between /type-combinators/ and
-- /singetons/, as well as similar typeclasses.  This module provides
-- conversion functions between the two (through the 'TC' typeclass), and
-- also many appropriate orphan instances.
--

module Data.Type.Combinator.Singletons (
  -- * Conversion functions
    TC(..)
  , singLength
  -- * Orphan singleton instance for 'N'
  , Sing(SZ, SS), SN, ZSym0, SSym0, SSym1
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

genSingletons [''N]

-- | Typeclass for /type-combinator/ types that can be converted to and
-- from singletons.
class TC f where
    -- | Convert a /type-combinator/ type that is equivalent to a singleton
    -- into its equivalent 'Sing'.
    fromTC :: f a -> Sing a
    -- | Convert a 'Sing' into its equivalent /type-combinator/ type.
    toTC   :: Sing a -> f a

instance TC (Prod Sing) where
    toTC = \case
        SNil         -> Ø
        x `SCons` xs -> x :< toTC xs
    fromTC = \case
        Ø       -> SNil
        x :< xs -> x `SCons` fromTC xs

instance TC Boolean where
    fromTC = \case
      False_ -> SFalse
      True_  -> STrue
    toTC   = \case
      SFalse -> False_
      STrue  -> True_

instance TC Nat where
    fromTC = \case
      Z_   -> SZ
      S_ n -> SS (fromTC n)
    toTC   = \case
      SZ   -> Z_
      SS n -> S_ (toTC n)

instance TC (Sing :*: Sing) where
    fromTC (x :*: y)     = STuple2 x y
    toTC   (STuple2 x y) = x :*: y

instance TC (Sing :+: Sing) where
    fromTC = \case
      L' x -> SLeft x
      R' x -> SRight x
    toTC = \case
      SLeft  x -> L' x
      SRight x -> R' x

instance TC (Option Sing) where
    fromTC = \case
      Nothing_ -> SNothing
      Just_ x  -> SJust x
    toTC   = \case
      SNothing -> Nothing_
      SJust x  -> Just_ x

-- | Convert a 'Sing' for @as@ into a 'Length' representing the length of
-- @as@.
--
-- @'Length' as@ is equivalent to @'Prod' 'Proxy' as@, so this is basically
--
-- @
-- 'singLength' :: 'Sing' as -> 'Prod' 'Proxy' as
-- 'singLength' = 'map1' ('const' 'Proxy') . 'toTC'
-- @
--
-- This function is one-way, since the actual run-time information on the
-- types in @as@ is lost.
singLength :: Sing as -> Length as
singLength = \case
    SNil         -> LZ
    _ `SCons` xs -> LS (singLength xs)

