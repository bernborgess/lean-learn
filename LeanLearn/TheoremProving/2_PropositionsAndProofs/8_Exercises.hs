import Data.Void (Void, absurd)

-- Prove ¬(p ↔ ¬p) without using classical logic.
newtype Iff a b = Iff (a -> b, b -> a)

example :: Iff p (p -> Void) -> Void
example (Iff (ida, volta)) = absurd $ hnp hp
  where
    hnp (hp :: p) = ida hp hp
    hp = volta hnp