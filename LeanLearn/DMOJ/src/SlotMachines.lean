--
--    author:  bernborgess
--    problem: SlotMachines - lean-learn
--    created: 12.February.2024 19:44:39
--
import Lean

open IO

def getLine : IO String := do return (←(←getStdin).getLine).trim
def readLn : IO Nat := do return (←getLine).toNat!

--                  TTL   plays jar   mach 1   mach 2    mach 3   curr
def Score : Type := Nat × Nat × Nat × Fin 35 × Fin 100 × Fin 10 × Fin 3

theorem gtz_10 : 10 > 0 := by exact Nat.succ_pos 9
theorem gtz_35 : 35 > 0 := by exact Nat.succ_pos 34
theorem gtz_100 : 100 > 0 := by exact Nat.succ_pos 99

def mkScore : Nat × Nat × Nat × Nat → Score
| (j,x,y,z) => (1000000,0,j, Fin.ofNat' x gtz_35, Fin.ofNat' y gtz_100, Fin.ofNat' z gtz_10,0)

-- Returns the amount of times played
def play (scr : Score) : Nat := match scr with
| (0,  _,_,_,_,_,_) => 0                                 -- Safe Termination
| (_,  s,0,_,_,_,_) => s                                 -- Out of money
| (n+1,s,j,34,y ,z,0) => play (n,s+1,j+29,0  ,y  ,z  ,1) -- Won at mach 1
| (n+1,s,j,x ,y ,z,0) => play (n,s+1,j-1 ,x+1,y  ,z  ,1) -- Lost at mach 1
| (n+1,s,j,x ,99,z,1) => play (n,s+1,j+59,x  ,0  ,z  ,2) -- Won at mach 2
| (n+1,s,j,x ,y ,z,1) => play (n,s+1,j-1 ,x  ,y+1,z  ,2) -- Lost at mach 2
| (n+1,s,j,x ,y ,9,2) => play (n,s+1,j+8 ,x  ,y  ,0  ,0) -- Won at mach 3
| (n+1,s,j,x ,y ,z,2) => play (n,s+1,j-1 ,x  ,y  ,z+1,0) -- Lost at mach 3
termination_by _ => scr.fst

def main : IO Unit := do
  let init : Score := mkScore (←readLn,←readLn,←readLn,←readLn)
  let final := play init
  println s!"Martha plays {final} times before going broke."
