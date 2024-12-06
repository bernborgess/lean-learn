import Mathlib.Tactic.Use
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic

-- Logica de Primeira Ordem
variable {P Q : Prop}

-- negacao
def np := ¬P

-- conjuncao
def pq := P ∧ Q

-- disjuncao
def porq := P ∨ Q

-- implicacao
def ptoq := P → Q

-- quantificadores
variable {A : α → Prop}

-- para todo
def allp := ∀x, A x

-- existe
def exp := ∃x, A x

example : (∀x,A x) → (α) → ∃x,A x := by
  intro allA
  intro x
  use x
  apply show A x from allA x
  done

example : (∀x,A x) → (α) → ∃x,A x :=
  fun allA =>
  fun x =>
    ⟨x,allA x⟩


-- Teorema da correcao

/-
Logic Thoughts
- Understand what "soundness" proof mean.
- More specifically, understand some 'model' steps
- Undestand what "QCL", "structure", "linguagem diagrama", "linguagem de primeira ordem especifica", "Form(L)", "Sent(L)",


Deducao Natural em QCL :=
  Deducao Natural em Logica Classica Sentencial \union {I\forall,E\forall,E\exists,I\exists}
-/


/-
Estrutura :=
  - D := Dominio do discurso
  - I := Interpretacao que atrivui valores semanticos aos simbolos nao logicos de L, com as condicoes:
    1. Se c ∈ C, i.e. c eh uma constante de L, entao I(c) ∈ D;
    2. Se Pⁿ ∈ P, i.e. se Pⁿ eh uma letra de  predicao n-aria de L, entao I(Pⁿ) ⊆ Dⁿ

  Dada uma estrutura 𝔸 = ⟨D,I⟩, escrevemos cA e PA
-/
example (P : α → Prop) (all : ∀x,P x) (x : α) : ∃x,P x :=
  ⟨x,all x⟩

def k : Set Nat := {1,2}

example : ({} : Set Nat) = {} ∪ {} := by
  exact (Set.union_empty ∅).symm
  done

-- Soundness of Classical Logic
-- Completeness of Classical Logic ¬∧∨→
-- Soundness of First Order Logic ∀∃
