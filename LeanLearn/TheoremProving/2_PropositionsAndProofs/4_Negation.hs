{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
import Data.Void qualified as V (Void, absurd)

type False = V.Void

ex1 :: (p -> q) -> (q -> False) -> (p -> False)
ex1 hpq hnq hp = hnq (hpq hp)

-- The connective False has a single elimination rule,
-- False.elim, which expresses the fact that anything follows
-- from a contradiction. This rule is sometimes called ex
-- falso (short for ex falso sequitur quodlibet),
-- or the principle of explosion.

falseElim :: False -> q
falseElim = V.absurd

ex2 :: p -> (p -> False) -> q
ex2 hp hnp =
    let
        false = hnp hp
        hq = falseElim false
     in
        hq
ex2' hp hnp = falseElim (hnp hp)

-- The arbitrary fact, q, that follows from falsity is an
-- implicit argument in False.elim and is inferred automatically.
-- This pattern, deriving an arbitrary fact from contradictory
-- hypotheses, is quite common, and is represented by `absurd`.

absurd :: p -> (p -> False) -> q
absurd hp hnp = falseElim (hnp hp)

ex3 :: p -> (p -> False) -> q
ex3 hp hnp = absurd hp hnp

-- Here, for example, is a proof of ¬p → q → (q → p) → r:
ex4 :: (p -> False) -> q -> (q -> p) -> r
ex4 hnp hq hqp =
    let
        false = hnp $ hqp hq
     in
        falseElim false
ex4' hnp hq hqp = absurd (hqp hq) hnp