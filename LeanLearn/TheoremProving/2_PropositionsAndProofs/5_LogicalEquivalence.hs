-- The expression Iff.intro h1 h2 produces a proof of p ↔ q from h1 : p → q
-- and h2 : q → p.
iffIntro :: (p -> q) -> (q -> p) -> (p -> q, q -> p)
iffIntro h1 h2 = (h1, h2)

-- The expression Iff.mp h produces a proof of p → q from h : p ↔ q.
iffMp :: (p -> q, q -> p) -> (p -> q)
iffMp = fst

-- Similarly, Iff.mpr h produces a proof of q → p from h : p ↔ q.
iffMpr :: (p -> q, q -> p) -> (q -> p)
iffMpr = snd

-- Here is a proof of p ∧ q ↔ q ∧ p:
andSwap :: ((p, q) -> (q, p), (q, p) -> (p, q))
andSwap = iffIntro (\h -> (snd h, fst h)) (\h -> (snd h, fst h))
