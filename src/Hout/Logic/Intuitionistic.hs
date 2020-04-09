-- For ex falso
{-# LANGUAGE EmptyCase #-}
-- For nice-looking type aliases
{-# LANGUAGE TypeOperators #-}
-- To allow us to redefine True & False as types instead of constructors
{-# LANGUAGE NoImplicitPrelude #-}

module Hout.Logic.Intuitionistic where

import Prelude hiding (True, False)

-- Types

data True = True

data False

type (a /\ b) = (a, b)

type (a \/ b) = Either a b

type Not a = a -> False

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
trueIntro = True

exFalso :: False -> a
exFalso false = case false of

-- Notice the lack of impliesIntro and impliesElim
--   as well as notIntro and notElim

-- Derived rules

iffIntro :: (a -> b) -> (b -> a) -> (a <-> b)
iffIntro verse converse = (verse, converse)

iffElimLeft :: (a <-> b) -> a -> b
iffElimLeft (verse, _) a = verse a

iffElimRight :: (a <-> b) -> b -> a
iffElimRight (_, converse) b = converse b
