-- hask1
-- The expression And.intro h1 h2 builds a proof of p ∧ q
-- using proofs h1 : p and h2 : q. It is common to describe
-- And.intro as the and-introduction rule. In the next example
-- we use And.intro to create a proof of p → q → p ∧ q.
andIntro :: p -> q -> (p, q)
andIntro hp hq = (hp, hq)
andIntro' = (,)

-- hask2
-- The expression And.left h creates a proof of p from a proof
-- h : p ∧ q. Similarly, And.right h is a proof of q. They are
-- commonly known as the left and right and-elimination rules.
andLeft :: (p, q) -> p
andLeft (hp, hq) = hp
andLeft' = fst

andRight :: (p, q) -> q
andRight (hp, hq) = hq
andRight' = snd

-- We can now prove p ∧ q → q ∧ p with the following proof term.
ex2 :: (p, q) -> (q, p)
ex2 (hp, hq) = (hq, hp)
ex2' h = (snd h, fst h)
ex2'' h = andIntro (snd h) (fst h)
ex2''' h = andIntro (andRight h) (andLeft h)
