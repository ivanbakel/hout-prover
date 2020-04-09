{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures, PolyKinds #-}

module Hout.Prover.Tactics where

import Control.Monad.Indexed
import Prelude hiding (True, False)

import Hout.Logic.Intuitionistic
import Hout.Logic.FirstOrder

-- Basics of theorem proving

data Tactic from to a = Tactic ((a -> to) -> from)

name :: a -> Tactic b b a
name a = Tactic \f -> f a

applyH :: (a -> b) -> Tactic m n a -> Tactic m n b
applyH proof (Tactic g) = Tactic \f -> g (f . proof)

combineH :: Tactic m n (a -> b) -> Tactic n o a -> Tactic m o b
combineH (Tactic g) (Tactic h) = Tactic \f -> g (\a_b -> h (f . a_b))

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

apply :: (a -> b) -> Tactic b a ()
apply f = Tactic \unit_a -> f (unit_a ())

applyF :: Forall k p -> Tactic (p a) () ()
applyF (Forall f) = Tactic (\nil -> f)

left :: Tactic (a \/ b) a ()
left = Tactic (\f -> Left (f ()))
right :: Tactic (a \/ b) b ()
right = Tactic (\f -> Right (f ()))

intro :: Tactic (a -> b) b a
intro = Tactic (\this -> this)

exact :: a -> Tactic a () ()
exact a = Tactic (\_ -> a)

split :: Tactic a () () -> Tactic b () () -> Tactic (a /\ b) () ()
split (Tactic f) (Tactic g) = Tactic (\nil -> (f nil, g nil))

assert :: Tactic a () () -> Tactic m m a
assert (Tactic f) = Tactic (\a_m -> a_m (f (\() -> ())))

enough :: (a -> Tactic b () ()) -> Tactic b a ()
enough transform = Tactic \f -> let Tactic g = transform (f ()) in g \() -> ()

exists :: Witness (a :: k) -> Tactic (Exists k p) (p a) ()
exists a = Tactic (\proof_of_p_a -> Exists a (proof_of_p_a ()))

reflexivity :: Tactic (Equal a a) () ()
reflexivity = Tactic (\id -> Refl)

symmetry :: Tactic (Equal a b) (Equal b a) ()
symmetry = Tactic (\f -> eqSym (f ()))

transitivity :: Tactic (Equal a c) (Equal a b /\ Equal b c) ()
transitivity = Tactic (\f -> (uncurry eqTrans) (f ()))

rewrite :: Equal a b -> Tactic (p a) (p b) ()
rewrite equality = apply (eqRewrite (eqSym equality))

rewriteRev :: Equal a b -> Tactic (p b) (p a) ()
rewriteRev equality = apply (eqRewrite equality)

qed :: Tactic () () ()
qed = Tactic (\unit -> ())
