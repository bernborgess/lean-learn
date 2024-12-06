import Lean

open Lean Elab Tactic Meta Expr List

syntax (name := resolution_1) "R1" ident "," ident "," term (",")? ("[" term,* "]")? : tactic

def getNatLit? : Expr → Option Nat
| app (app _ (lit (Literal.natVal x))) _ => some x
| _ => none

def parseResolution : Syntax → TacticM (Option Nat × Option Nat)
  | `(tactic| R1 $_, $_, $_, [ $[$hs],* ]) => get hs
  | `(tactic| R1 $_, $_, $_)               => pure (none, none)
  | _ => throwError "[Resolution]: wrong usage"
where
  get (hs : Array Term) : TacticM (Option Nat × Option Nat) :=
    match hs.toList with
      | [n₁, n₂] => do
        let e₁ ← elabTerm n₁ none
        let e₂ ← elabTerm n₂ none
        return (getNatLit? e₁, getNatLit? e₂)
      | _ => throwError "[Resolution]: wrong usage"

def collectPropsInOrChain : Expr → MetaM (List Expr)
| app (app (const ``Or ..) e₁) e₂ => (e₁ :: ·) <$> collectPropsInOrChain e₂
| e => pure [e]


def createOrChain : List Expr → MetaM Expr
| []   => throwError "createOrChain with empty list"
| [h]  => pure h
| h::t => app (app (mkConst ``Or) h) <$> createOrChain t

-- fold the l-th suffix into one expr
def collectPropsInOrChain' : Nat → Expr → MetaM (List Expr)
| l, e => do
  let li ← collectPropsInOrChain e
  let pref := List.take l li
  let suff := List.drop l li
  let suffE ← createOrChain suff
  pure $ pref ++ [suffE]

def getLength : Expr → (i : Option Nat := none) → MetaM Nat
| e, some i => do
  let li ← collectPropsInOrChain' i e
  pure $ List.length li
| e, none => do
  let li ← collectPropsInOrChain e
  pure $ List.length li

def findIndex? [BEq α] : List α → α → Option Nat
| [], _ => none
| x::xs, a =>
  if a == x then
    some 0
  else (· + 1) <$> findIndex? xs a
def getGroupOrPrefixGoal : Expr → Nat → MetaM Expr
| e, n => do
  let props ← collectPropsInOrChain e
  let left ← createOrChain (take n props)
  let right ← createOrChain (drop n props)
  pure $ app (app (mkConst ``Or) left) right

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {P Q R : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

def groupPrefixLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| props, i_iter + 1, i,  e => do
  let rc ← groupPrefixLemmas' props i_iter i e
  mkAppOptM ``congOrLeft #[none, none, props.get! (i - i_iter - 1), rc]


def groupPrefixLemmasCore : Name → List Expr → Nat → MetaM (List Expr)
| nm, props, n =>
  let f := fun i: Nat => do
    let a₁ := props.get! i
    let a₂ ← createOrChain $ List.take (n - i) (props.drop (i + 1))
    let a₃ ← createOrChain $ props.drop (n + 1)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst nm) a₁) a₂) a₃
    groupPrefixLemmas' props i i appliedArgs
  List.mapM f (List.reverse (List.range n))

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

def groupPrefixLemmas := groupPrefixLemmasCore ``orAssocDir


def groupPrefixCore (mvar : MVarId) (val type : Expr) (prefLen : Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let l ← getLength type
      if prefLen > 0 && prefLen < l then
        let props ← collectPropsInOrChain type
        let goal ← getGroupOrPrefixGoal type prefLen
        let mut answer := val
        let lemmas ← groupPrefixLemmas props (prefLen - 1)
        for l in lemmas do
          answer := mkApp l answer
        let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name goal answer
        return mvar'
      else throwError
        "[groupPrefix]: prefix length must be > 0 and < size of or-chain"


def mkAppList : Expr → List Expr → Expr :=
  fun e l => List.foldr mkApp e l.reverse

def groupMiddleLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| sufProps, iter + 1, init, e => do
  let rc ← groupMiddleLemmas' sufProps iter init e
  mkAppOptM ``congOrLeft #[none, none, sufProps.get! (init - iter - 1), rc]


-- NOT a generalization of groupPrefixLemmas
-- exclusively used for pullMiddle (step₂)
def groupMiddleLemmas : List Expr → Nat → MetaM (List Expr)
| sufProps, groupSize =>
  let f := fun i: Nat => do
    let middleSize := groupSize + 1
    let a₁ := sufProps.get! i
    let a₂ ← createOrChain $ List.take (groupSize - i - 1) (sufProps.drop (i + 1))
    let a₃ := sufProps.get! (middleSize - 1)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst ``orAssocDir) a₁) a₂) a₃
    groupMiddleLemmas' sufProps i i appliedArgs
  List.mapM f (List.reverse (List.range (groupSize - 1)))

-- 0-based
-- inclusive on both sides
def subList (i j : Nat) (xs : List α) : List α :=
  List.take (j + 1 - i) (xs.drop i)


def congLemmas (lemmas props : List Expr) (i_iter i j : Nat)
   (val : Expr) (mid : Expr) (last : Bool) : MetaM Expr := do
    match i_iter with
    | 0      =>
      if last then pure $ mkAppList val lemmas
      else
        let fname ← mkFreshId
        withLocalDeclD fname mid $ fun bv => do
          let body := mkAppList bv lemmas
          let lambda ← mkLambdaFVars #[bv] body
          mkAppM ``congOrRight #[lambda, val]
    | i_iter' + 1 =>
      let fname ← mkFreshId
      let pref := subList (i - i_iter + 1) (i - 1) props
      let suff := subList (j + 1) props.length props
      let mut t := mid
      if not suff.isEmpty then
        t ← createOrChain [t, ← createOrChain suff]
      if not pref.isEmpty then
        let l' ← collectPropsInOrChain t
        t ← createOrChain (pref ++ l')
      withLocalDeclD fname t $ fun bv => do
        let rc ← congLemmas lemmas props i_iter' i j bv mid last
        let lambda ← mkLambdaFVars #[bv] rc
        mkAppM ``congOrLeft #[lambda, val]

def pull! [Inhabited α] (i j : Nat) (xs : List α) : List α :=
  List.join
    [ xs.take i
    , [xs.get! j]
    , List.drop i (xs.eraseIdx j)
    ]

def ungroupMiddleLemmas' : List Expr → Nat → Nat → Expr → MetaM Expr
| _, 0, _, e => pure e
| props, iter + 1, init, e => do
  let rc ← ungroupMiddleLemmas' props iter init e
  let r := props.get! (init - iter - 1)
  mkAppOptM ``congOrLeft #[none, none, r, rc]


theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

def ungroupMiddleLemmas : List Expr → Nat → Nat → MetaM (List Expr)
| props, groupStart, groupSize =>
  let f := fun i: Nat => do
    let a₁ := props.get! i
    let a₂ ← createOrChain (subList (i + 1) (groupStart + groupSize - 1) props)
    let a₃ ← createOrChain $ props.drop (groupStart + groupSize)
    let appliedArgs :=
      mkApp (mkApp (mkApp (mkConst ``orAssocConv) a₁) a₂) a₃
    ungroupMiddleLemmas' props i i appliedArgs
  -- [groupStart ..= groupStart + groupSize - 1]
  let is := List.drop groupStart (List.range (groupStart + groupSize - 1))
  List.mapM f is

-- pull j-th term in the orchain to i-th position
-- (we start counting indices at 0)
def pullToMiddleCore (mvar: MVarId) (i j : Nat) (val type : Expr) (name : Name)
  : MetaM MVarId := mvar.withContext do
  if i == j then
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type val
    return mvar'
  else
    let last := (← getLength type) == j + 1
    let props ← collectPropsInOrChain type
    let mid := List.take (j - i + 1) (List.drop i props)

    -- step₁: group with parenthesis props in the range [i, j]
    -- example: A ∨ B ∨ C ∨ D ∨ E with (2, 4)
    --       -> A ∨ (B ∨ C ∨ D) ∨ E
    let step₁ ←
      if last then pure val
      else do
        let lemmas := List.take (j - i) $ ← groupPrefixLemmas props j
        pure (mkAppList val lemmas)

    /- -- step₂: group prefix of middle -/
    /- -- example: A ∨ (B ∨ C ∨ D) ∨ E -/
    /- --       -> A ∨ ((B ∨ C) ∨ D) ∨ E -/
    let step₂: Expr ← do
      let lemmas ← groupMiddleLemmas (props.drop i) (j - i)
      let mid ← createOrChain (subList i j props)
      congLemmas lemmas props i i j step₁ mid last

    /- -- step₃: apply commutativity on middle -/
    /- -- example: A ∨ ((B ∨ C) ∨ D) ∨ E -/
    /- --       -> A ∨ (D ∨ B ∨ C) ∨ E -/
    let midPref := List.dropLast mid
    let midSuff := List.getLast! mid
    let comm :=
      mkApp (mkApp (mkConst ``orComm) (← createOrChain midPref)) midSuff
    let mid ← createOrChain [← createOrChain midPref, midSuff]
    let step₃ ← congLemmas [comm] props i i j step₂ mid last

    /- -- step₄: ungroup middle -/
    /- -- example: A ∨ (D ∨ B ∨ C) ∨ E -/
    /- --       -> A ∨ D ∨ B ∨ C ∨ E -/
    let goalList := pull! i j props
    let goal ← createOrChain goalList
    let step₄ ←
      if last then pure step₃
      else do
        let lemmas ← ungroupMiddleLemmas goalList i (j - i + 1)
        pure $ mkAppList step₃ lemmas
    let (_, mvar₄) ← MVarId.intro1P $ ← mvar.assert name goal step₄
    return mvar₄


def pullIndex (mvar: MVarId) (index : Nat) (val type : Expr)
  (name : Name) : MetaM MVarId :=
    pullToMiddleCore mvar 0 index val type name

def pullCore (mvar: MVarId) (pivot val type : Expr) (sufIdx : Option Nat)
  (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let lastSuffix := (← getLength type) - 1
      let sufIdx :=
        match sufIdx with
        | some i => i
        | none   => lastSuffix
      let li ← collectPropsInOrChain' sufIdx type
      match findIndex? li pivot with
      | some i =>
        if i == sufIdx && sufIdx != lastSuffix then
          if i == 0 then
            let (_, mvar') ← MVarId.intro1P $ ← mvar.assert name type val
            return mvar'
          else
            let fname ← mkFreshId
            let mvar' ← groupPrefixCore mvar val type sufIdx fname
            mvar'.withContext do
              let lctx ← getLCtx
              let groupped := (lctx.findFromUserName? fname).get!.toExpr
              let answer: Expr ←
                mkAppM ``orComm #[groupped]
              let requiredType ← inferType answer
              let (_, mvar'') ← MVarId.intro1P $
                ← mvar'.assert name requiredType answer
              return mvar''
        else pullIndex mvar i val type name
      | none   => throwError "[Pull]: couldn't find pivot"


theorem resolution_thm : ∀ {A B C : Prop}, (A ∨ B) → (¬ A ∨ C) → B ∨ C := by
  intros A B C h₁ h₂
  cases h₁ with
  | inl ap => cases h₂ with
              | inl nap => exact (False.elim (nap ap))
              | inr cp  => exact (Or.inr cp)
  | inr bp => exact (Or.inl bp)

theorem flipped_resolution_thm : ∀ {A B C : Prop}, (¬ A ∨ B) → (A ∨ C) → B ∨ C := by
  intros A B C h₁ h₂
  cases h₁ with
  | inl nap => cases h₂ with
               | inl ap => exact False.elim (nap ap)
               | inr cp => exact (Or.inr cp)
  | inr bp => exact (Or.inl bp)

theorem resolution_thm₂ : ∀ {A C: Prop}, A → (¬ A ∨ C) → C := λ a ornac =>
  match ornac with
  | Or.inl na => False.elim (na a)
  | Or.inr c  => c

theorem flipped_resolution_thm₂ : ∀ {A C : Prop}, ¬ A → (A ∨ C) → C := λ na orac =>
  match orac with
  | Or.inl a => False.elim (na a)
  | Or.inr c => c

theorem resolution_thm₃ : ∀ {A B: Prop}, (A ∨ B) → ¬ A → B := λ orab na =>
  match orab with
  | Or.inl a => False.elim (na a)
  | Or.inr b => b

theorem flipped_resolution_thm₃ : ∀ {A B : Prop}, (¬ A ∨ B) → A → B := λ ornab a =>
  match ornab with
  | Or.inl na => False.elim (na a)
  | Or.inr b => b

theorem resolution_thm₄ : ∀ {A : Prop}, A → ¬ A → False := λ a na => na a
theorem flipped_resolution_thm₄ : ∀ {A : Prop}, ¬ A → A → False := flip resolution_thm₄

def ungroupPrefixLemmas := fun props n => do
  pure $ List.reverse $ ← groupPrefixLemmasCore ``orAssocConv props n

def resolutionCoreMeta (mvar : MVarId) (val₁ val₂ pivot : Expr)
  (sufIdx₁' sufIdx₂' : Option Nat) (flipped : Bool) (name : Name) : MetaM MVarId :=
    mvar.withContext do
      let type₁ ← inferType val₁
      let type₂ ← inferType val₂
      let mut pivot := pivot
      let mut notPivot := mkApp (mkConst ``Not) pivot
      let sufIdx₁ ←
        match sufIdx₁' with
        | none   => pure $ (← getLength type₁) - 1
        | some i => pure i
      let sufIdx₂ ←
        match sufIdx₂' with
        | none   => pure $ (← getLength type₂) - 1
        | some i => pure i
      let len₁ := sufIdx₁ + 1
      let len₂ := sufIdx₂ + 1
      let lenGoal := len₁ + len₂ - 2
      let prefixLength := len₁ - 2

      if flipped then
        let tmp := pivot
        pivot := notPivot
        notPivot := tmp

      let fname₁ ← mkFreshId
      let fname₂ ← mkFreshId
      let mvar' ← pullCore mvar pivot val₁ type₁ sufIdx₁' fname₁
      let mvar'' ← pullCore mvar' notPivot val₂ type₂ sufIdx₂' fname₂

      mvar''.withContext do
        let lctx ← getLCtx
        let pulled₁ := (lctx.findFromUserName? fname₁).get!.toExpr
        let pulled₂ := (lctx.findFromUserName? fname₂).get!.toExpr
        let props₁ ← collectPropsInOrChain' sufIdx₁ type₁
        let props₁ := props₁.erase pivot
        let props₂ ← collectPropsInOrChain' sufIdx₂ type₂
        let props₂ := props₂.erase notPivot
        let props := props₁ ++ props₂
        let goal ←
          match props with
          | [] => pure $ mkConst ``False
          | _  => createOrChain props
        let thmName : Name :=
          match Nat.blt 1 len₁, Nat.blt 1 len₂ with
          | true, true   => if flipped then ``flipped_resolution_thm  else ``resolution_thm
          | true, false  => if flipped then ``flipped_resolution_thm₃ else ``resolution_thm₃
          | false, true  => if flipped then ``flipped_resolution_thm₂ else ``resolution_thm₂
          | false, false => if flipped then ``flipped_resolution_thm₄ else ``resolution_thm₄
        let mut answer ← mkAppM thmName #[pulled₁, pulled₂]
        if lenGoal > prefixLength + 1 then
          let lemmas ← ungroupPrefixLemmas props prefixLength
          for l in lemmas do
            answer := mkApp l answer
        let (_, mvar₃) ← MVarId.intro1P $ ← mvar''.assert name goal answer
        return mvar₃


@[tactic resolution_1] def evalResolution_1 : Tactic := fun stx =>
  withMainContext do
    let firstHyp : Ident := ⟨stx[1]⟩
    let secondHyp : Ident := ⟨stx[3]⟩
    let pivotTerm : Term := ⟨stx[5]⟩
    let (sufIdx₁, sufIdx₂) ← parseResolution stx
    let val₁ ← elabTerm firstHyp none
    let val₂ ← elabTerm secondHyp none
    let pivot ← elabTerm pivotTerm none
    let fname ← mkFreshId
    let mvar ← getMainGoal
    let mvar' ← resolutionCoreMeta mvar val₁ val₂ pivot sufIdx₁ sufIdx₂ false fname
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
