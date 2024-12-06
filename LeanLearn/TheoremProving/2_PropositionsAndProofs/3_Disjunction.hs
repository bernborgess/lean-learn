-- hask3
-- The expression Or.intro_left q hp creates a proof of p ∨ q from a proof hp : p. Similarly, Or.intro_right p hq creates a proof for p ∨ q using a proof hq : q. These are the left and right or-introduction rules.
orIntroLeft :: p -> Either p q
orIntroLeft = Left

orIntroRight :: q -> Either p q
orIntroRight = Right

-- hask4
-- The or-elimination rule is slightly more complicated.
-- The idea is that we can prove r from p ∨ q, by showing
-- that r follows from p and that r follows from q.
-- In other words, it is a proof by cases.
-- In the expression Or.elim hpq hpr hqr, Or.elim takes
-- three arguments, hpq : p ∨ q, hpr : p → r and hqr : q → r,
-- and produces a proof of r.

orElim :: Either p q -> (p -> r) -> (q -> r) -> r
orElim (Left p) hpr _ = hpr p
orElim (Right q) _ hqr = hqr q

-- In the following example, we use Or.elim to prove
-- p ∨ q → q ∨ p.
ex1 :: Either p q -> Either q p
ex1 h = orElim h Right Left
ex1' h = orElim h orIntroRight orIntroLeft
ex1'' h =
    orElim
        h
        (\(hp :: p) -> orIntroRight hp :: Either q p)
        (\(hq :: q) -> orIntroLeft hq :: Either q p)