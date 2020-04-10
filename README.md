# hout - a non-interactive proof assistant for first-order logic, in Haskell

hout is an in-Haskell non-interactive proof assistant for intuitionistic first-order logic.

Alternatively, hout provides a monad that allows you to write functions in the style of proof-assistant proofs, which are then computable Haskell terms.

This is possible thanks to the Curry-Howard isomorphism.

## What?

If you know about the CHI and intuitionistic logic, skip this section.

### The Curry-Howard isomorphism

The Curry-Howard isomorphism (or correspondence) is a pattern between intuitionistic logic and type theory, which says that propositions correspond to types, and proofs correspond to terms.

The basis of this correspondence is that an *inhabitant* of a type is a proof that the type is inhabited. For example, the term `3 :: Int` is a proof that you can construct some terminating value of type `Int`.

What about types with no inhabitant? Taking some type known to have no inhabitants, like `Void`, you can show that a type `a` is uninhabited by producing a terminating term of type `a -> Void`. Why? Because `a -> Void` is inhabited only if `a` is uninhabited, and a term of type `a -> Void` is a *proof that `a -> Void` is inhabited*!

This also has implications for function types - a term with type `a -> b` is a function from terms of type `a` to terms of type `b`. You can equally consider it as a function from proofs of the proposition `a` to proofs of the proposition `b` - in other words, the function itself is a proof that `a` implies `b`, because if you have a proof that `a` is true, you can obtain a proof that `b` is true.

Other logical connectives also have equivalents in Haskell types. `False` is `Void`, because you can't construct a proof for it; `a /\ b` is the tuple (or product) `(a, b)`; `a \/ b` is (the sum) `Either a b`; and `Not a` - the claim that `a` is uninhabited - is precisely `a -> False`. `True` can be any inhabited type, but it's helpful to have a type with a canonical construction, so `True` is normally `()`, the empty tuple, which has the unique constructor `()`.

You can see the correspondence in these types - `(a, b)` is inhabited if and only if both `a` and `b` are inhabited. Similarly, `Either a b` is inhabited if and only if at least one of `a`, `b` is inhabited. Phrasing it in terms of proofs, if you have a proof of `a` and a proof of `b`, you can construct a proof of `a /\ b` (and vice-versa) - and with a proof of `a`, you can construct a proof of `a \/ b`. With a proof of `a \/ b`, you can *destruct* the proof to get either a proof for `a` (`Left a`) or a proof for `b` (`Right b`).

For notation's sake, we write `a <-> b` for the type `(a -> b) /\ (b -> a)`.

### Intuistionistic logic

Intuistionistic (or constructive) logic is a subset of classical logic (the kind of logic you normally learn in a CS or Maths course). It behaves exactly like classical logic, but with one caveat - *you can only _construct_ proofs of a proposition*.

To see what that means, consider the type of the law of the excluded middle - `forall a. a \/ Not a`. For every type `a`, one of these two terms must be constructable - either `a` is inhabited, so you can construct a value of type `a`, or `a` is uninhabited, so you can construct a function of type `a -> Void`.

But you can't write a terminating Haskell function with type `forall a. a \/ Not a` - because it would require you to somehow decide if `a` is inhabited, and then get a value of type `a` if it was. In other words, you have to construct either a `Left a` or a `Right (Not a)`, and you have no way to do either of those things.

There are lots of other consequences of this caveat: the following implications do *not* hold in intuitionistic logic - and similarly, you cannot write a terminating Haskell term for their type.

  * `Not (Not a) -> a`
  * `(a -> b) -> (Not a \/ b)`
  * `Not (Not a /\ Not b) -> a \/ b`

## Proofs and the Tactic monad

The `Tactic` monad is an indexed monad for which the monad state is the current proof goal, and the type argument is an additional hypothesis introduced at that proof step. Looking at its definition
```
data Tactic from to a = Tactic ((a -> to) -> from)
```
A `Tactic` term represents a valid goal transformation - you are allowed to change a proof of `from` into a proof of `to`, and introduce the additional hypothesis `a`, if you can use a proof of `a -> to` to prove `from`.

For example, the `apply` function has the signature
```
apply :: (a -> b) -> Tactic b a ()
```
Given a function `a -> b`, it allows you to transform the goal from proving `b` to proving `a` - because once you prove `a`, it will be possible to use the given function to produce a proof of `b`.

Some tactics introduce additional hypotheses - such as `intro`
```
intro :: Tactic (a -> b) b a
```
`intro` allows you to transform a goal of `a -> b` to a goal of `b`, giving you the hypothesis of type `a` to bind into a variable. If you can use the proof of `a` to construct a proof of `b`, then the resulting function term is indeed a proof of `a -> b`.

### Available tactics

hout provides some tactics based on those used in `Coq` - for example, you can `apply` hypotheses to a goal; you can `split` the proof a conjunction into proofs of its conjuncts; you can `intro` a variable; you can `exists` the witness of an existential goal; you can `rewrite` propositions with equality; you can even `assert` hypothesis and produce subgoals.

The full list of tactics is given in `Hout.Prover.Tactics`, and it is possible to write your own using the type signature of the `Tactic` monad.

### Proofs in do notation

Because `Tactic` is an indexed monad, you can use the `do-notation` package to write proofs in do notation, which end up looking quite similar to proofs in interactive proof assistants. Some advice for doing this is:

  * use pattern-matching in binds, particularly when working with existential types. GHC has some unfortunate behaviour when trying to use `let` in do notation when working with existential type arguments.
  * Enable block arguments, and use do notation for subgoals
  * If your final statement is a tactic that introduces a hypothesis, but the new goal is trivial `()`, use `qed` to end your proof.

## Computations written in the proof style

hout also has the nice property of intuitionistic proof assistants that proofs are themselves terms, and can be run as Haskell code. This gives hout the alternative use of writing functions in a proof-y syntax using the `Tactic` monad. For example, the `identity` function can be written as
```
identity :: a -> a
identity :: runProof $ Proof do
  a <- intro
  exact a
```
