
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib n + fib (n+1)

#eval fib 10

  -- have : n < n + 2 := sorry

-- | n => fib (n-1) + fib (n-2)
--   have : n - 1 < n + 1 := Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.le_succ_self ..)
--   fib n

def nxt (n : Fin 9) : Fin 10 := n.succ
