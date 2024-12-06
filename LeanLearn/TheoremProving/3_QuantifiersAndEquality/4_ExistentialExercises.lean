
-- Existential Exercises

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

-- unrelated proof
example : (∃ _ : α, r) → r := 
  λ h => 
  Exists.elim h
  λ _ => λ hr => hr


-- tautology existence
example (a : α) : r → (∃ _ : α, r) :=
  λ hr =>
  ⟨a, hr⟩ 


-- unrelated proof can be factored out
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (λ ⟨x, hpx, hr⟩ => ⟨⟨x, hpx⟩, hr⟩)
  (λ ⟨⟨x, hpx⟩, hr⟩ => ⟨x, hpx, hr⟩)


-- Or over existence
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (λ ⟨x, hpq⟩ =>
    Or.elim hpq
      (λ hpx => Or.inl ⟨x, hpx⟩)
      (λ hqx => Or.inr ⟨x, hqx⟩)
  )
  (λ h =>
    Or.elim h 
    (λ ⟨x, hpx⟩ => ⟨x, Or.inl hpx⟩)
    (λ ⟨x, hqx⟩ => ⟨x, Or.inr hqx⟩)
  )


theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p) (λ hp => hp) (λ hnp => absurd hnp h)


def all_has_no_exception : (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
  λ h =>
  byContradiction
  λ hnnpnx =>
    have ⟨x,hnpx⟩ := dne hnnpnx
    absurd (h x) hnpx
    
def no_exception_means_all_pass : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
  λ h =>
  λ x =>
    byCases
    (λ k : p x => k)
    (λ k => absurd ⟨x, k⟩ h)
  
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (all_has_no_exception α p)
  (no_exception_means_all_pass α p)


def some_example_means_not_all_fail : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
  λ ⟨x, hpx⟩ =>
  λ np =>
    absurd hpx (np x)
 
def not_all_fail_means_some_pass : ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
  λ h =>
  byContradiction
    λ hnex : ¬ ∃ x, p x =>
      have hnp : ∀ x, ¬p x :=
        λ x => λ hpx : p x =>
        absurd ⟨x, hpx⟩ hnex
      absurd hnp h


example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (some_example_means_not_all_fail α p)
  (not_all_fail_means_some_pass α p)


def no_case_means_all_fail: (¬ ∃ x, p x) → (∀ x, ¬ p x) :=
  λ hne =>
  byContradiction
    λ hna =>
      have he : ∃ x, p x := (not_all_fail_means_some_pass α p) hna
      absurd he hne
  
def all_fail_means_no_case_passes: (∀ x, ¬ p x) → (¬ ∃ x, p x) :=
  λ h =>
  byContradiction
    λ hnnepx => 
      have ⟨x, hpx⟩ := dne hnnepx
      absurd hpx (h x)
 
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (no_case_means_all_fail α p)
  (all_fail_means_no_case_passes α p)

def not_all_pass_means_some_not_pass : (¬ ∀ x, p x) → (∃ x, ¬ p x) :=
  λ h =>
  byContradiction
    λ hne : ¬ ∃ x, ¬ p x => 
      have ha : ∀ x, p x := (no_exception_means_all_pass α p) hne
      absurd ha h
  
def some_not_pass_means_not_all_pass : (∃ x, ¬ p x) → (¬ ∀ x, p x) :=
  λ ⟨x, hnp⟩ => 
  byContradiction
  λ hnna =>
    have ha := dne hnna
    absurd (ha x) hnp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (not_all_pass_means_some_not_pass α p)
  (some_not_pass_means_not_all_pass α p)


def rule_and_argument_to_r : (∀ (x : α), p x → r) → (∃ x, p x) → r :=
  λ ha => λ ⟨x, hp⟩ =>
    ha x hp

def argument_and_rule_to_r: ((∃ x, p x) → r) → ∀ (x : α), p x → r :=
  λ he => λ x => λ hp =>
    he ⟨x, hp⟩ 

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (rule_and_argument_to_r α p r)
  (argument_and_rule_to_r α p r)


def fun_and_property_to_r : (∃ x, p x → r) → (∀ (x : α), p x) → r :=
  λ ⟨x, hpr⟩ => λ ha =>
    hpr (ha x)

def property_and_fun_to_r : (a : α) → ((∀ (x : α), p x) → r) → ∃ x, p x → r :=
  λ a =>
  λ ha =>
  show ∃ x, p x → r from
    byCases
    (λ hap : ∀ x, p x => ⟨a, λ _ => ha hap⟩)
    (λ hnap : ¬∀ x, p x =>
      byContradiction
      λ hnex =>
        have hap : ∀ x, p x := 
          λ x =>
          byContradiction
            λ hnp : ¬ p x =>
              have hex := ⟨x, λ hp => absurd hp hnp⟩
              absurd hex hnex 
      absurd hap hnap
    )


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
  (fun_and_property_to_r α p r)
  (property_and_fun_to_r α p r a)



