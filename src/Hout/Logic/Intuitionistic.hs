-- For ex falso
{-# LANGUAGE EmptyCase #-}
-- For nice-looking type aliases
{-# LANGUAGE TypeOperators #-}
-- To allow us to redefine True & False as types instead of constructors
{-# LANGUAGE NoImplicitPrelude #-}

{-|
Module      : Hout.Logic.Intuitionistic
Description : Constructs of intuitionistic logic in Haskell types
Copyright   : (c) Isaac van Bakel, 2020
License     : BSD-3
Maintainer  : ivb@vanbakel.io
Stability   : experimental
Portability : POSIX

This module contains type aliases for intuitionistic logic constructions which are
expressed as Haskell types.

It also gives the natural deduction rules for those aliases, except when they
are aliases of arrow types. For example, implies-introduction and elimination
are both Haskell arrow constructions (function abstraction and application,
respectively) so no rule is given.
-}
module Hout.Logic.Intuitionistic where

import Prelude hiding (True, False)

import Data.Void

-- Types

-- | The trivially-inhabited type. 'True' is defined as '()' to give it a
-- canonical construction, so that all proofs of 'True' are identical.
type True = ()

-- | The uninhabited type.
type False = Void

type (a /\ b) = (a, b)

type (a \/ b) = Either a b

-- | Negation of a type. Because this is an arrow type alias, not-introduction
-- and elimination are not part of this module.
type Not a = a -> False

-- | Iff. Some derived rules are defined for iff for the sake of completeness.
type (a <-> b) = (a -> b) /\ (b -> a)

-- Natural deduction 

andIntro :: a -> b -> a /\ b
andIntro a b = (a, b)

andElimLeft :: a /\ b -> a
andElimLeft ((a, _)) = a

andElimRight :: a /\ b -> b
andElimRight ((_, b)) = b

orIntroLeft :: a -> a \/ b
orIntroLeft a = Left a

orIntroRight :: b -> a \/ b
orIntroRight b = Right b

orElim :: (a -> c) -> (b -> c) -> (a \/ b) -> c
orElim fromA fromB (Left a) = fromA a
orElim fromA fromB (Right b) = fromB b

trueIntro :: True
trueIntro = ()

-- | Ex Falso Quod Libet - it is recommended when writing functions of this
-- form to use the 'EmptyCase' extension, to make the compiler check that
-- the type is uninhabited.
exFalso :: False -> a
exFalso false = case false of

-- Derived rules

iffIntro :: (a -> b) -> (b -> a) -> (a <-> b)
iffIntro verse converse = (verse, converse)

iffElimLeft :: (a <-> b) -> a -> b
iffElimLeft (verse, _) a = verse a

iffElimRight :: (a <-> b) -> b -> a
iffElimRight (_, converse) b = converse b
