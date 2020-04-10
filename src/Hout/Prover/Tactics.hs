{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures, PolyKinds #-}

{-|
Module      : Hout.Prover.Tactics
Description : Definition of the proof-transformation monad 'Tactic'.
Copyright   : (c) Isaac van Bakel, 2020
License     : BSD-3
Maintainer  : ivb@vanbakel.io
Stability   : experimental
Portability : POSIX

The module forms the basis of hout as a non-interactive proof assistant. It
contains the definition of 'Tactic', the monad which allows for proof-goal
manipulations in do-notation, and defines some useful 'Tactic' functions to
mimic the syntax of actual proof assistants.
-}
module Hout.Prover.Tactics where

import Control.Monad.Indexed
import Prelude hiding (True, False)

import Hout.Logic.Intuitionistic
import Hout.Logic.FirstOrder

-- Basics of theorem proving

-- | The proof-transformation monad. 'Tactic' is an indexed monad for which
-- the type state is the current proof goal.
--
-- The aim of most 'Tactic' uses is to produce a term with type
-- @Tactic a () ()@ for the proof goal @a@ - this represents a proof of @a@,
-- since it involves reducing the proof goal @a@ to the trivial proof goal @()@.
--
-- A 'Tactic' term is a valid manipulation which takes a proof of @a -> to@
-- and gives a proof of @from@ - allowing for the proof-goal to be transformed
-- from @from@ into @to@, giving the additional hypothesis @a@.
data Tactic from to a = Tactic ((a -> to) -> from)

-- | Bind a term as a hypothesis name.
name :: a -> Tactic b b a
name a = Tactic \f -> f a

-- | Apply a proof transformation to the hypothesis.
applyH :: (a -> b) -> Tactic m n a -> Tactic m n b
applyH proof (Tactic g) = Tactic \f -> g (f . proof)

-- | Combine two hypotheses together.
combineH :: Tactic m n (a -> b) -> Tactic n o a -> Tactic m o b
combineH (Tactic g) (Tactic h) = Tactic \f -> g (\a_b -> h (f . a_b))

-- | Apply an intermediate proof to the hypothesis.
bindH :: (a -> Tactic n o b) -> Tactic m n a -> Tactic m o b
bindH a_tactic (Tactic g) = Tactic \b_o -> g (\a -> let Tactic h = a_tactic a in h b_o)

instance IxFunctor Tactic where
  imap = applyH

instance IxPointed Tactic where
  ireturn = name

instance IxApplicative Tactic where
  iap = combineH

instance IxMonad Tactic where
  ibind = bindH

-- | Apply a proof transformation to the goal. This simplifies the goal of @b@
-- to a goal of @a@.
apply :: (a -> b) -> Tactic b a ()
apply f = Tactic \unit_a -> f (unit_a ())

-- | Apply a forall to the goal. This solves the goal immediately.
applyF :: Forall k p -> Tactic (p a) () ()
applyF (Forall f) = Tactic (\nil -> f)

-- | Transform a disjunction goal into the goal of the left side.
left :: Tactic (a \/ b) a ()
left = Tactic (\f -> Left (f ()))

-- | Transform a disjunction goal into the goal of the right side.
right :: Tactic (a \/ b) b ()
right = Tactic (\f -> Right (f ()))

-- | Give a name to the hypothesis of an @->@.
intro :: Tactic (a -> b) b a
intro = Tactic (\this -> this)

-- | Solve a goal by giving its exact proof.
exact :: a -> Tactic a () ()
exact a = Tactic (\_ -> a)

-- | Split a conjuction goal into two subgoals.
split :: Tactic a () () -> Tactic b () () -> Tactic (a /\ b) () ()
split (Tactic f) (Tactic g) = Tactic (\nil -> (f nil, g nil))

-- | Assert a statement, giving a proof of it. The statement can then be bound
-- as a hypothesis
assert :: Tactic a () () -> Tactic m m a
assert (Tactic f) = Tactic (\a_m -> a_m (f (\() -> ())))

-- | Assert a statement, giving a proof that it solves the goal. The goal then
-- becomes proving the statement.
enough :: (a -> Tactic b () ()) -> Tactic b a ()
enough transform = Tactic \f -> let Tactic g = transform (f ()) in g \() -> ()

-- | Give the witness for an existential goal. The goal then becomes proving
-- the statement for that witness.
exists :: Witness (a :: k) -> Tactic (Exists k p) (p a) ()
exists a = Tactic (\proof_of_p_a -> Exists a (proof_of_p_a ()))

-- | Transform a goal for a specific value to a general 'Forall' goal
generalize :: Tactic (p a) (Forall k p) ()
generalize = Tactic \f -> let Forall forall = f () in forall

-- | Solve a reflexive goal.
reflexivity :: Tactic (Equal a a) () ()
reflexivity = Tactic (\id -> Refl)

-- | Transform an equality goal by symmetry.
symmetry :: Tactic (Equal a b) (Equal b a) ()
symmetry = Tactic (\f -> eqSym (f ()))

-- | Split an equality goal into two subgoals, by transitivity. 
transitivity :: Tactic (Equal a b) () () -> Tactic (Equal b c) () () -> Tactic (Equal a c) () ()
transitivity (Tactic f) (Tactic g) = Tactic (\nil -> eqTrans (f nil) (g nil))

-- | Rewrite a goal by equality, left-to-right.
rewrite :: Equal a b -> Tactic (p a) (p b) ()
rewrite equality = apply (eqRewrite (eqSym equality))

-- | Rewrite a goal by equality, right-to-left.
rewriteRev :: Equal a b -> Tactic (p b) (p a) ()
rewriteRev equality = apply (eqRewrite equality)

-- | A helper for the end of proofs. Assert to the type system that the proof
-- is complete, and act as an ending statement if the final 'Tactic' otherwise
-- introduces a hypothesis.
qed :: Tactic () () ()
qed = Tactic (\unit -> ())
