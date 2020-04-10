{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}

{-|
Module      : Hout.Logic.FirstOrder
Description : Constructs of first-order intuitionistic logic in Haskell types
Copyright   : (c) Isaac van Bakel, 2020
License     : BSD-3
Maintainer  : ivb@vanbakel.io
Stability   : experimental
Portability : POSIX

This module contains type aliases for first-order logic constructions which are
expressed as Haskell types, based on those in "Hout.Logic.Intuitionistic". This
gives definitions for

  * the universal quantifier
  * the existential quantifier
  * first-order equality

It also gives the natural deduction rules for these constructions, though they
are not very useful to the programmer.
-}
module Hout.Logic.FirstOrder where

import Data.Kind

-- Types

-- | A witness of a kind inhabitant. 'Witness'es can be constructed for the
-- 'Type' kind, 'Constraint' kind, or any data kind.
data Witness (a :: k) where
  -- | Because Type is the only kind of habitats, it is the only constructor for
  -- which we can demand an inhabitant
  Witness :: (a :: Type) -> Witness a
  ConstraintWitness :: Witness (a :: Constraint)
  DataKindWitness :: Witness (a :: (k :: Type))

-- | The existential quantifier, parameterised by a kind. The predicate itself
-- is required to return a 'Type', since 'Exists' carries the proof term. If
-- @k@ is 'Type', then 'Exists' also carries the witness term in a 'Witness'.
data Exists k (p :: k -> *) where
  Exists :: Witness (a :: k) -> p a -> Exists k p

-- | The forall quantifier. Note that, as this is also an in-built Haskell type
-- operation, like @->@, no rules are given for it.
type Forall k (p :: k -> *) = (forall (a :: k). p a)

-- | Type level equality, parameterised by a kind.
data Equal (a :: k) (b :: k) where
  -- | The unique equality constructor - pattern matching on 'Refl' allows the
  -- compiler to deduce that @a@ and @b@ must unify.
  Refl :: Equal a a

-- Natural deduction (FO)

existsIntro :: Witness (a :: k) -> p a -> Exists k p
existsIntro witness proof = Exists witness proof

-- | Exists elimination, as a continuation.
--
-- Note that this has to be expressed in this continuation style because
-- existential types are not allowed in the return type
existsElim :: (forall (a :: k). Witness a -> p a -> b) -> Exists k p -> b
existsElim f (Exists witness proof) = f witness proof

eqRefl :: Equal a a
eqRefl = Refl

eqSym :: Equal a b -> Equal b a
eqSym Refl = Refl

eqTrans :: Equal a b -> Equal b c -> Equal a c
eqTrans Refl Refl = Refl

-- | Rewrite by equality.
--
-- This could be expressed as an @<->@, but @->@ is easier to use. The power
-- of the rule is not affected.
eqRewrite :: Equal a b -> p a -> p b
eqRewrite Refl proof = proof
