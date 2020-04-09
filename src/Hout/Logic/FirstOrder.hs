{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}

module Hout.Logic.FirstOrder where

import Data.Kind

-- Types

data Witness (a :: k) where
  -- Because Type is the only kind of habitats, it is the only constructor for
  -- which we can demand an inhabitant
  Witness :: (a :: Type) -> Witness a
  ConstraintWitness :: Witness (a :: Constraint)
  DataKindWitness :: Witness (a :: (k :: Type))

data Exists k (p :: k -> *) where
  Exists :: Witness (a :: k) -> p a -> Exists k p

data Forall k (p :: k -> *) = Forall (forall (a :: k). p a)

data Equal (a :: k) (b :: k) where
  Refl :: Equal a a

-- Natural deduction (FO)

existsIntro :: Witness (a :: k) -> p a -> Exists k p
existsIntro witness proof = Exists witness proof

-- Note that this has to be expressed in this "continuation style" because
-- existential types are not allowed in the return type in this way (directly)
existsElim :: (forall (a :: k). Witness a -> p a -> b) -> Exists k p -> b
existsElim f (Exists witness proof) = f witness proof

forallIntro :: (forall (a :: k). p a) -> Forall k p
forallIntro forall = Forall forall

forallElim :: Forall k p -> p a
forallElim (Forall forall) = forall

eqRefl :: Equal a a
eqRefl = Refl

eqSym :: Equal a b -> Equal b a
eqSym Refl = Refl

eqTrans :: Equal a b -> Equal b c -> Equal a c
eqTrans Refl Refl = Refl

eqRewrite :: Equal a b -> p a -> p b
eqRewrite Refl proof = proof
