{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RebindableSyntax #-}

{-|
Module      : Hout.Prover.Proofs
Description : Definition of the theorem construction.
Copyright   : (c) Isaac van Bakel, 2020
License     : BSD-3
Maintainer  : ivb@vanbakel.io
Stability   : experimental
Portability : POSIX

This module contains some helpers for declaring proofs, and running them as
code.
-}
module Hout.Prover.Proofs where

import Control.Monad.Indexed
import Language.Haskell.DoNotation
import Prelude hiding (True, False, Monad (..))

import Hout.Prover.Tactics

-- | Run a theorem to its Haskell term. If the proof of the theorem uses only
-- terminating values, then the resulting Haskell term can be run as usual
-- without errors.
runProof :: Theorem a -> a
runProof (Proof (Tactic f)) = f \() -> ()

-- | A proven theorem.
--
-- As described in "Hout.Prover.Tactics", proof of @a@ is equivalent to reducing
-- the proof goal @a@ to the trival proof goal @()@.
data Theorem a = Proof (Tactic a () ())

-- Some possible type synonyms
type Lemma a = Theorem a
type Corollary a = Theorem a
type Example a = Theorem a
type Definition a = Theorem a

-- | An unprovable axiom.
data Axiom a

-- | Admit an axiom, without proof. Note that this is not a terminating term,
-- so using it will not yield computable Haskell.
admitted :: Axiom a
admitted = admitted

-- | Use an axiom, with the understood caveat that the result will not be a
-- computable term. It is impossible to construct an 'Axiom', so using one
-- cannot give runnable Haskell.
noncomputable :: Axiom a -> a
noncomputable axiom = case axiom of
