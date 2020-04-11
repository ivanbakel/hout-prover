{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures, PolyKinds #-}

module Hout.Examples where

import Prelude hiding (True, False, Monad (..), pure)
import Prelude (fail)

import Control.Monad.Indexed
import Language.Haskell.DoNotation

import Hout.Logic.Intuitionistic
import Hout.Logic.FirstOrder
import Hout.Prover.Proofs
import Hout.Prover.Tactics

orComm :: Lemma ((a \/ b) -> (b \/ a))
orComm = Proof do
  a_or_b <- intro
  case a_or_b of
    Left a -> do
      right
      exact a
    Right b -> do
      left
      exact b
  qed

data Implies1 (p :: k -> *) (q :: k -> *) (a :: k) = I1 (p a -> q a)

composition :: Definition ((a -> b) -> (b -> c) -> (a -> c))
composition = Proof do
  a_impl_b <- intro
  b_impl_c <- intro
  a <- intro
  apply b_impl_c
  apply a_impl_b
  exact a

runComposition :: (a -> b) -> (b -> c) -> (a -> c)
runComposition = runProof composition

exists_and_forall_implies_exists :: Theorem (Exists k p -> Forall k (Implies1 p q) -> Exists k q)
exists_and_forall_implies_exists = Proof do
  (Exists witness p_witness) <- intro
  (Forall (I1 forall_implies)) <- intro
  exists witness
  apply forall_implies
  exact p_witness
