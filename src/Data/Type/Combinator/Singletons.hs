{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

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

prodSing :: Prod Sing as -> Sing as
prodSing = \case
    Ø       -> SNil
    x :< xs -> x `SCons` prodSing xs

singProd :: Sing as -> Prod Sing as
singProd = \case
    SNil         -> Ø
    x `SCons` xs -> x :< singProd xs

singLength :: Sing as -> Length as
singLength = \case
    SNil         -> LZ
    _ `SCons` xs -> LS (singLength xs)

boolSing :: Boolean a -> Sing a
boolSing = \case
    False_ -> SFalse
    True_  -> STrue

singBool :: Sing a -> Boolean a
singBool = \case
    SFalse -> False_
    STrue  -> True_

genSingletons [''N]

natSing :: Nat a -> Sing a
natSing = \case
    Z_   -> SZ
    S_ n -> SS (natSing n)

singNat :: Sing a -> Nat a
singNat = \case
    SZ   -> Z_
    SS n -> S_ (singNat n)

parSing :: (Sing :*: Sing) '(a, b) -> Sing '(a, b)
parSing (x :*: y) = STuple2 x y

singPar :: Sing '(a, b) -> (Sing :*: Sing) '(a, b)
singPar (STuple2 x y) = x :*: y

choiceSing :: (Sing :+: Sing) e -> Sing e
choiceSing = \case
    L' x -> SLeft x
    R' x -> SRight x

singChoice :: Sing e -> (Sing :+: Sing) e
singChoice = \case
    SLeft x  -> L' x
    SRight x -> R' x

optionSing :: Option Sing a -> Sing a
optionSing = \case
    Nothing_ -> SNothing
    Just_ x  -> SJust x

singOption :: Sing a -> Option Sing a
singOption = \case
    SNothing -> Nothing_
    SJust x  -> Just_ x
