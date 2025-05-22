import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw

--make this decidable, solvable

inductive Atom
  | atom₁ : Atom | atom₂ : Atom | atom₃ : Atom
deriving DecidableEq, Repr
open Atom

instance : ToString Atom where
  toString a :=
    match a with
    | atom₁ => "a"
    | atom₂ => "b"
    | atom₃ => "c"

inductive Form
  | bot : Form
  | atoms : Atom → Form
  | neg : Form → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
deriving Repr
open Form

def formToString (form : Form) : String :=
   match form with
    | .bot => "⊥"
    | .atoms a => toString a
    | .neg a => "¬" ++ formToString a
    | .and a b => formToString a ++ " ∧ " ++ formToString b
    | .or a b => formToString a ++ " ∨ " ++ formToString b
    | .imp a b => formToString a ++ " → " ++ formToString b

instance : ToString Form where
  toString form := formToString form

/-
Atomic values get valued as one , not as 0, to help show termination for the atomic case in antecedent.
Bottom is valued as 0, for it is semantically different from all others and does not "add complexity" to our sequent
 -/
@[simp]
def sizeOf_Form : Form → Nat
  | .bot => 0
  | .atoms _ => 1
  | .neg f => 1 + sizeOf_Form f
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q

-- [f1,f2] ⊢ x
inductive Sequent
  | seq : List Form → Form → Sequent
deriving Repr

instance : ToString Sequent where
  toString seq :=
  match seq with
  | .seq xs a => (List.map formToString xs).toString ++ "⊢" ++ formToString a

/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
Other option: vector with context length and booleans representing if we've "visited/looked at them"
 -/
-- [x, y], [f1, f2] ⊢ f
inductive Seq4Proof
  | seq4 : (context1 : List Atom) → (context2 : List Form) → Form → Seq4Proof
deriving Repr

instance : ToString Seq4Proof where
  toString seq4 :=
  match seq4 with
  | .seq4 as xs a => (List.map toString as).toString ++ (List.map formToString xs).toString ++ "⊢" ++ formToString a
/-
For determening termination we ignore the atomic list and only consider the sum value of all formulas and succedent to be decreasing
 -/
@[simp]
def termination_metric (s : Seq4Proof) : Nat :=
  match s with
  | .seq4 _ [] f => sizeOf_Form f
  | .seq4 a (x::xs) f =>
    sizeOf_Form x + termination_metric (.seq4 a xs f)
termination_by s
decreasing_by
  . simp

--def negation (x : Form) : Form := .imp x .bot
/-
TODO: rething representing negation as implication, feel like im skipping a few stepps like this and the definition isn't "pure"

imp₁ imp₂ imp₃ imp₄ were initially defined to help with termination and looping prevention (paper by Roy Dyckhoff),
but introduces other complexities...

Right now copies of formulas in the proof tree are left out (in impl and negl) to make sure automatedProof terminates.
reason for keeping copies- we may need to use them again to find our proof
 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (x : Form) (xs ys : List Form),
      Proof (.seq (xs ++ x :: ys) x)
  -- ∀ x Γ, (⊥, Γ ⊢ x)
  | botl :
    ∀ (x : Form) (xs ys : List Form),
      Proof (.seq (xs ++ .bot :: ys) x)
  -- ∀ a Γ, (Γ, a ⊢ ⊥) → (Γ ⊢ ¬a)
  | negr :
    ∀ (x : Form) (xs : List Form),
            Proof (.seq (xs ++ [x]) .bot) →
            Proof (.seq (xs) (.neg x))
  -- ∀ a b Γ, (Γ, ¬a ⊢ a) → (Γ, ¬a ⊢ b)
  | negl :
    ∀ (x y : Form) (xs ys : List Form),
            Proof (.seq (xs ++ ys) x) → --removed copy of .neg x from context
            Proof (.seq (xs ++ (.neg x) :: ys) y)
  -- ∀ a b c Γ, (Γ, a, b ⊢ c) → (Γ, a ∧ b ⊢ c)
  | andl :
    ∀ (a b c : Form) (xs ys : List Form),
      Proof (.seq (xs ++ a :: b :: ys) c) →
      Proof (.seq (xs ++ (.and a b) :: ys) c)
  -- ∀ a b c Γ, (Γ ⊢ a) → (Γ ⊢ b) → (Γ ⊢ a ∧ b)
  | andr :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq xs a) →
      Proof (.seq xs b) →
      Proof (.seq xs (.and a b))
  -- ∀ a b c Γ, (a, Γ ⊢ c) → (b, Γ ⊢ c) → (a ∨ b, Γ ⊢ c)
  | orl :
    ∀ (a b c : Form) (xs ys : List Form),
    Proof (.seq (xs ++ a :: ys) c) →
    Proof (.seq (xs ++ b :: ys) c) →
    Proof (.seq (xs ++ (.or a b) :: ys) c)
  -- ∀ a b Γ, (Γ ⊢ a) → (Γ ⊢ a ∨ b)
  | orr1 :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq xs a) →
      Proof (.seq xs (.or a b))
  -- ∀ a b Γ, (Γ ⊢ b) → (Γ ⊢ a ∨ b)
  | orr2 :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq xs b) →
      Proof (.seq xs (.or a b))
  -- ∀ a b c Γ, (a → b, Γ ⊢ a) → (b, Γ ⊢ c) → (a → b, Γ ⊢ c)
  | impl :
    ∀ (a b c : Form) (xs ys : List Form),
      Proof (.seq (xs ++ ys ) a) → -- removed copy of (.imp a b) from list
      Proof (.seq (xs ++ b :: ys ) c) →
      Proof (.seq (xs ++ (.imp a b) :: ys) c)
/-   -- a is atomic
  | impl₁ :
    ∀ (a : Atom) (b c : Form) (xs ys : List Form),
      Proof (.seq (xs ++ [.atoms a] ++ [b] ++ ys) c) → -- a ja b ei peaks olema järjest
      Proof (.seq (xs ++ [.imp (.atoms a) b] ++ [.atoms a] ++ ys) c)
  -- implications left side is and op
  | impl₂ :
    ∀ (a b c d : Form) (xs ys : List Form),
      Proof (.seq (xs ++ [.imp a (.imp b c)] ++ ys) d) →
      Proof (.seq (xs ++ [.imp (.and a b) c] ++ ys) d)
  -- left side is or op
  | impl₃ :
    ∀ (a b c d : Form) (xs ys : List Form),
      Proof (.seq (xs ++ [.imp a c] ++ [.imp b c] ++ ys) d) → -- sama mure ↑
      Proof (.seq (xs ++ [.imp (.or a b) c] ++ ys) d)
  | impl₄ :
    ∀ (a b c d : Form) (xs ys : List Form),
      Proof (.seq (xs ++ [.imp a b] ++ ys) (.imp c a)) →
      Proof (.seq (xs ++ [b] ++ ys) d) →
      Proof (.seq (xs ++ [.imp (.imp c a) b] ++ ys) d) -/
  -- ∀ a b Γ, (a, Γ ⊢ b) → (Γ ⊢ a → b)
  | impr :
    ∀ (a b : Form) (xs  : List Form),
      Proof (.seq (xs ++ [a] ) b) →
      Proof (.seq (xs) (.imp a b))
deriving Repr
open Proof

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map formToString)


def proofToString {seq : Sequent} : Proof seq → String
| .ax a xs ys =>
  s!"AX: {formToString a}, {listToString xs}, {listToString ys} ⊢ {formToString a}"
| .botl a xs ys =>
  s!"⊥L: ⊥, {listToString xs}, {listToString ys} ⊢ {formToString a}"
| .negr a xs proof =>
  s!"{proofToString proof} '\n' ¬R: {listToString xs} ⊢ ¬{formToString a}"
| .negl a b xs ys proof =>
  s!"{proofToString proof} '\n' ¬L: ¬{formToString a}, {listToString xs}, {listToString ys} ⊢ {formToString b}"
| .andl a b c xs ys proof =>
  s!"{proofToString proof} '\n' ∧L: ({formToString a} ∧ {formToString b}), {listToString xs}, {listToString ys} ⊢ {formToString c}"
| .andr a b xs proof₁ proof₂=>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' ∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}"
| .orl a b c xs ys proof₁ proof₂=>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' ∨L: ({formToString a} ∨ {formToString b}), {listToString xs}, {listToString ys} ⊢ {formToString c}"
| .orr1 a b xs proof =>
  s!"{proofToString proof} '\n' ∨R₁: {listToString xs} ⊢ {formToString a} ∨ {formToString b}"
| .orr2 a b xs proof =>
  s!"{proofToString proof} '\n' ∨R₂: {listToString xs} ⊢ {formToString a} ∨ {formToString b}"
| .impl a b c xs ys proof₁ proof₂ =>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' →L: ({formToString a} → {formToString b}), {listToString xs}, {listToString ys} ⊢ {formToString c}"
| .impr a b xs proof  =>
  s!"{proofToString proof} '\n' →R: {listToString xs} ⊢ {formToString a} → {formToString b}"

/-
all ToString instances are for pretty-printing purposes
 -/
def listProofToString : List (Proof seq) → String
| [] => ""
| x::xs => proofToString x ++ listProofToString xs

instance : ToString (List (Proof seq)) where
  toString proof := listProofToString proof


/-
Needed for finding proofs for atomic formulas ([a, b, c ,a, d], Γ ⊢ a) <- this can be split up many ways (2 different a forms) so essentially different proofs
 -/
def splitBy [DecidableEq α ] (xs : List α ) (a : α) : List (List α × List α) :=
  match xs with
  | [] => []
  | x::xs =>
    if x == a then
      ([], xs) :: (splitBy xs a ).map (λ (fst, snd) => (x::fst, snd))
    else
      (splitBy xs a ).map (λ (fst, snd) => (x::fst, snd))

#eval splitBy [1,2,1,2] 2

-- for any pair of returned list, fst+elem+snd = originaalne list
theorem splitByCorrectness [DecidableEq α] (xs : List α) (a : α) :
  ∀ pair ∈ (splitBy xs a), pair.1 ++ (a :: pair.2) = xs :=
  λ pair pair_in =>
  match xs with
  | [] => False.elim (by simp [splitBy] at pair_in) -- contra
  | x::xs => by
    unfold splitBy at pair_in
    by_cases cond : x == a
    . rw[cond] at pair_in
      simp only at pair_in
      simp only [↓reduceIte] at pair_in
      simp only [List.mem_cons] at pair_in
      match pair_in with
      | Or.inl left =>
        clear pair_in
        subst left
        simp only [List.nil_append, List.cons.injEq, and_true]
        simp only [beq_iff_eq] at cond
        subst cond
        apply Eq.refl
      | Or.inr right =>
        clear pair_in
        simp only [List.mem_map] at right
        let ⟨elem,elem_in,eq⟩ := right
        subst eq
        clear right
        have ih := splitByCorrectness xs a _ elem_in
        simp only [List.cons_append]
        simp only [List.cons.injEq]
        simp only [true_and]
        exact ih
    . simp only [Bool.not_eq_true] at cond
      rw[cond] at pair_in
      simp only [↓reduceIte] at pair_in
      simp only [Bool.false_eq_true] at pair_in
      simp only [if_false] at pair_in
      simp only [List.mem_map] at pair_in
      let ⟨elem,elem_in,eq⟩ := pair_in
      clear pair_in
      have ih := splitByCorrectness xs a _ elem_in
      subst eq
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact ih

/-
needed to find all possible pairings (of proofs) for cases like or, and ...
 -/
def getPairs (xs : List α ) (ys : List β ) : List (α × β) :=
  match xs with
  | [] => []
  | x::xs' => List.map (λ y => (x , y)) ys ++ getPairs xs' ys

@[simp]
def seqAtoms2seq (s : Seq4Proof) : Sequent :=
  match s with
  | .seq4 xs ys a =>
    Sequent.seq ((xs.map .atoms) ++ ys) a

theorem maybe2 as ys x a:
  termination_metric (Seq4Proof.seq4 as ys x) < 1 + sizeOf_Form x + termination_metric (Seq4Proof.seq4 as ys a) := by
  match ys with
  | [] =>
    simp
    have step1 : sizeOf_Form x < 1 + sizeOf_Form x := lt_one_add (sizeOf_Form x)
    match sizeOf_Form a with
    | 0 => exact step1
    | n + 1 => exact Nat.lt_add_right (n + 1) step1
  | b::bs =>
    have ih := maybe2 bs (as:=as) (x:=x) (a:=a)
    simp
    simp at ih
    have obv {a b : Nat} (c : Nat) : a < b → c + a < c + b := fun a_1 => Nat.add_lt_add_left a_1 c
    have step := obv (sizeOf_Form b) ih
    clear obv ih
    have helper (b x tma : Nat) : b + ((1 + x) + tma) = (1 + x) + (b + tma) := by
      conv => rhs; rw[←Nat.add_assoc (n:= 1 + x), Nat.add_comm (n:= 1 + x), Nat.add_assoc]
    rw[←helper (b:=sizeOf_Form b)]
    apply step

theorem maybe3 as ys a:
  termination_metric (Seq4Proof.seq4 (as ++ [x]) ys a) < 1 + termination_metric (Seq4Proof.seq4 as ys a) := by
  match ys with
  | [] => simp
  | b::bs =>
    have ih := maybe3 as bs a (x:=x)
    simp
    conv => rhs; rw[←Nat.add_assoc, Nat.add_comm 1, Nat.add_assoc]
    apply add_lt_add_left ih (sizeOf_Form b)

def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
  match s with
------proving succedent using only atomics from left side---------
  | .seq4 as [] (.atoms a) =>
      have zs_corr := splitByCorrectness as a
      match g : splitBy as a with
      | [] => []
      | x::xs => by
        rw [g] at zs_corr
        have h1 := zs_corr x (by simp)
        rw [←h1]
        have first_proof := ax (.atoms a) (List.map .atoms x.fst) (List.map .atoms x.snd)
        simp only [seqAtoms2seq, List.map_append, List.map_cons, List.append_nil]
        have rest_of_proofs := List.map (λ y => ax (.atoms a) (List.map .atoms x.fst) (List.map .atoms x.snd)) xs
        exact first_proof::rest_of_proofs
  | .seq4 as [] .bot => []
  | .seq4 as [] (.neg a) =>
    have h₁ := automatedProof (.seq4 as [a] .bot) -- list of proofs
    have h₂ := List.map (negr a (as.map .atoms)) h₁
    by unfold seqAtoms2seq
       simp only [List.append_nil]
       exact h₂
  | .seq4 as [] (.or a b) =>
      (automatedProof (.seq4 as [] a)).map (orr1 a b ((as.map .atoms)++[]))  ++
      (automatedProof (.seq4 as [] b)).map (orr2 a b ((as.map .atoms)++[]))
  | .seq4 as [] (.imp a b) =>
    have h₁ := (automatedProof (.seq4 as [a] b))
    have h₂ := List.map (impr a b ((as.map .atoms))) h₁
    by unfold seqAtoms2seq
       simp only [List.append_nil]
       exact h₂
  | .seq4 as [] (.and a b) =>
      (getPairs (automatedProof (.seq4 as [] a)) (automatedProof (.seq4 as [] b))).map
      ((andr a b ((as.map .atoms)++[])).uncurry)
------opening up the antecedent formulas one by one----------
  | .seq4 as ((.and x y) :: ys) a =>
    have h₁ := automatedProof (.seq4 as (x :: y :: ys) a)
    List.map (andl x y a (as.map .atoms) ys) h₁
  | .seq4 as ((.or x y) :: ys) a =>
      (getPairs (automatedProof (.seq4 as (x::ys) a)) (automatedProof (.seq4 as (y::ys) a))).map
      (orl x y a (as.map .atoms) ys).uncurry
  | .seq4 as ((.imp x y) :: ys) a =>
      (getPairs (automatedProof (.seq4 as (/- .imp x y -/ ys) x )) -- first draft wo copy
                (automatedProof (.seq4 as (y::ys) a))).map
      (impl x y a (as.map .atoms) ys).uncurry
  | .seq4 as ((.neg x) :: ys) a =>
    have h₁ := automatedProof (.seq4 as ys x) -- first draft wo copy of neg x
    have h₂ := negl x a (as.map .atoms) ys
    List.map h₂ h₁
  | .seq4 as ((.atoms x) :: ys) a =>
    have h₁ := automatedProof (.seq4 (as ++ [x]) ys a)
    by unfold seqAtoms2seq
       simp only
       unfold seqAtoms2seq at h₁
       simp at h₁
       exact h₁
  | .seq4 as (.bot :: ys) a => [botl a (as.map .atoms) ys] -- we have bottom on the left, so we can conclude a

termination_by termination_metric s
decreasing_by
  . simp only [termination_metric, sizeOf_Form, Nat.add_zero, Nat.lt_add_left_iff_pos,
    Nat.lt_add_one]
  . simp only [termination_metric, sizeOf_Form, gt_iff_lt]
    rw [Nat.add_comm 1 (sizeOf_Form a)]
    refine Nat.lt_add_right (sizeOf_Form b) ?_
    apply Nat.lt_succ_self
  . simp
  . simp
  . simp
    rw [Nat.add_comm 1 (sizeOf_Form a)]
    refine Nat.lt_add_right (sizeOf_Form b) ?_
    apply Nat.lt_succ_self
  . simp
  . simp only [termination_metric, sizeOf_Form]
    conv => lhs; rw [←Nat.add_assoc]
    have := Nat.le_succ (sizeOf_Form x + sizeOf_Form y + termination_metric (Seq4Proof.seq4 as ys a))
    simp only [Nat.add_lt_add_iff_right, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  . simp
    rw [Nat.add_comm 1 (sizeOf_Form x)]
    refine Nat.lt_add_right (sizeOf_Form y) ?_
    apply Nat.lt_succ_self
  . simp
  . simp only [termination_metric, sizeOf_Form]
    have lt := Nat.lt_add_left (sizeOf_Form y) (maybe2 as ys x a)
    conv => rhs; rw[Nat.add_comm (n:=1 + sizeOf_Form x)]
    conv => rhs; rw[Nat.add_assoc]
    apply lt
  . simp
  . simp only [termination_metric]
    simp only [sizeOf_Form]
    apply maybe2 as ys x a
  . simp only [termination_metric]
    simp only [sizeOf_Form]
    apply maybe3


def automatedProofHelper (s : Sequent) : List (Proof s) :=
  match s with
  | .seq xs a =>
    automatedProof (Seq4Proof.seq4 [] xs a)

--notation "a" => Form.atoms Atom.atom₁

--modusponens
#eval listProofToString (automatedProofHelper (.seq [.imp (.atoms .atom₁) (.atoms .atom₂), .atoms .atom₁] (.atoms .atom₂)))

--define parse for string to Seq and then use it in main
def parseForMain (s : String) : Sequent :=
  have xs := s.splitOn
  
  sorry

-- give input in format a a → b ⊢ b
def main (args : List String) : IO Unit := do
  match args with
  | [] => throw (IO.userError "ERROR: No input file.")
  | filename :: _ =>
    let contents ← IO.FS.readFile filename
    (← IO.getStdout).putStrLn s!"File content: {contents}"
    let result := parseForMain contents
    (← IO.getStdout).putStrLn s!"{result}"
