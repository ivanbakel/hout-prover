{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}

module Hout.Prover.Proofs where

import Control.Monad.Indexed
import Language.Haskell.DoNotation
import Prelude hiding (True, False, Monad (..)

import Hout.Prover.Tactics

runProof :: Theorem a -> a
runProof (Proof (Tactic f)) = f \() -> ()

data Theorem a = Proof (Tactic a () ())

-- Some possible type synonyms
type Lemma a = Theorem a
type Corollary a = Theorem a
type Example a = Theorem a
type Definition a = Theorem a
