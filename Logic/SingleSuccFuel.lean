import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex

inductive Atom
  | atom₁ : Atom | atom₂ : Atom | atom₃ : Atom
deriving DecidableEq, Repr
open Atom

inductive Form
  | bot : Form
  | atoms : Atom → Form
  | neg : Form → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
deriving Repr
open Form

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

/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.

In addition we will seperate "special" forms (impl and negl), which require special treatment using a "fuel" counter
 -/
-- [x, y], [f1, f2], [imp1, imp2], fuel ⊢ f
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → (fuel : Nat) → Form → Seq4Proof
deriving Repr


/-

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
    ∀ (x : Form) (xs ys : List Form),
            Proof (.seq (xs ++ x :: ys) .bot) →
            Proof (.seq (xs ++ ys) (.neg x))
  -- ∀ a b Γ, (Γ, ¬a ⊢ a) → (Γ, ¬a ⊢ b)
  | negl :
    ∀ (x y : Form) (xs ys : List Form),
            Proof (.seq (xs ++ ys ++ [.neg x]) x) → -- copy of .neg x in context, also as last elem bc equality error in proof func
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
  | impr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq (xs ++ a :: ys) b) →
      Proof (.seq (xs ++ ys) (.imp a b))
  | impl :
    ∀ (a b c : Form) (xs ys : List Form),
      Proof (.seq (xs ++  ys ++ [(.imp a b)]) a) → -- copy of (.imp a b) in list as last elem bc of equality problem in proof func
      Proof (.seq (xs ++ b :: ys ) c) →
      Proof (.seq (xs ++ (.imp a b) :: ys) c)

deriving Repr
open Proof

#eval Proof.ax (.atoms .atom₁) [.atoms .atom₂] []

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
  | .seq4 atom forms imps _ a =>
    Sequent.seq ((atom.map .atoms) ++ forms ++ imps) a

/-
For determening termination we ignore the atomic list and only consider the sum value of all formulas and succedent to be decreasing
OR if it doesnt decrease- the fuel count(n) needs to decrease- so metric is a pair (sum, fuel)

try: leave out imps list from counting, so that first applycation of L→ rule terminates by form size. when dealing with imp list, we use fuel anyway
 -/
def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => sizeOf_Form f + size_sum fs

@[simp]
def termination_metric (s : Seq4Proof) : Nat × Nat :=
match s with
  | .seq4 _ forms _ n a => (n, size_sum forms + sizeOf_Form a)

mutual
---helper for handling implication list------
def handleImps (succ : Form) (as : List Atom) (imps : List Form) (n : Nat) : List (Proof (seqAtoms2seq (.seq4 as [] imps n succ))) :=
  match imps with
  | [] => []
  | (.imp x y) :: ys =>
    match n with
    | 0 => [] -- sorry
    | n' + 1 => by
      have pairs := getPairs (automatedProof (.seq4 as [] (ys ++ [.imp x y]) n' x))
                              (automatedProof (.seq4 as [y] ys n' succ))
      have funky := impl x y succ (as.map .atoms) ys
      simp at funky; simp at pairs
      have h₁ := List.map funky.uncurry pairs
      simp only [seqAtoms2seq, List.append_nil]
      exact h₁
  | (.neg x) :: ys =>
    match n with
    | 0 => [] -- sorry
    | n' + 1 => by
      have proofs := automatedProof (.seq4 as [] (ys ++ [.neg x]) n' x)
      have funky := negl x succ (as.map .atoms) ys
      simp; simp at funky; simp at proofs
      exact List.map funky proofs
  | _ :: ys => []
termination_by (n, sizeOf_Form succ)

def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
  match s with
  ------proving succedent using only atomics from left side---------
  | .seq4 as [] imps n (.atoms a) =>
      have zs_corr := splitByCorrectness as a
      -- case: a is not in as
      match g : splitBy as a with
      ------no atomic rule can be applied, start opening up copies of imp formulas------
      | [] =>
        match n with
        | 0 => []
        | n' + 1 => handleImps (.atoms a) as imps n' --not the best solution

      | x::xs => by
        rw [g] at zs_corr
        have h1 := zs_corr x (by simp)
        rw [←h1]
        have first_proof := ax (.atoms a) (List.map .atoms x.fst)  ((List.map .atoms x.snd) ++ imps)
        simp only [seqAtoms2seq, List.map_append, List.map_cons, List.append_nil]
        have rest_of_proofs := List.map (λ y => ax (.atoms a) (List.map .atoms x.fst) ((List.map .atoms x.snd) ++ imps)) xs
        simp
        exact first_proof::rest_of_proofs
  | .seq4 as [] imps n .bot =>
    match n with
    | 0 => []
    | n'+ 1 => handleImps .bot as imps n' --not the best solution
  | .seq4 as [] imps n (.neg a) => by
    have h₁ := automatedProof (.seq4 as [a] imps n .bot)
    simp at h₁
    have h₂ := List.map (negr a (as.map .atoms) imps) h₁
    unfold seqAtoms2seq
    simp only [List.append_nil]
    exact h₂
  | .seq4 as [] imps n (.and a b) =>
      (getPairs (automatedProof (.seq4 as [] imps n a)) (automatedProof (.seq4 as [] imps n b))).map
      ((andr a b ((as.map .atoms)++[]++imps)).uncurry)
  | .seq4 as [] imps n (.or a b) =>
      (automatedProof (.seq4 as [] imps n a)).map (orr1 a b ((as.map .atoms)++[]++imps))  ++
      (automatedProof (.seq4 as [] imps n b)).map (orr2 a b ((as.map .atoms)++[]++imps))
  | .seq4 as [] imps n (.imp a b) => by
    have h₁ := (automatedProof (.seq4 as [a] imps n b))
    simp at h₁
    have h₂ := List.map (impr a b (as.map .atoms) imps) h₁
    unfold seqAtoms2seq
    simp only [List.append_nil]
    exact h₂
------opening up the antecedent formulas one by one----------
  | .seq4 as ((.and x y) :: ys) imps n a => by
    have h₁ := automatedProof (.seq4 as (x :: y :: ys) imps n a)
    simp at h₁
    have h₂ := List.map (andl x y a (as.map .atoms) (ys++imps) ) h₁
    simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
    exact h₂
  | .seq4 as ((.or x y) :: ys) imps n a => by
    have pairList := getPairs (automatedProof (.seq4 as (x::ys) imps n a)) (automatedProof (.seq4 as (y::ys) imps n a))
    have funcy := (orl x y a (as.map .atoms) (ys++imps))
    simp at pairList
    have h₁ := List.map funcy.uncurry pairList
    simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
    exact h₁
  | .seq4 as ((.imp x y) :: ys) imps n a => by
      have pairList := getPairs (automatedProof (.seq4 as ys ( imps ++ [.imp x y]) n x )) (automatedProof (.seq4 as (y::ys) imps n a)) -- do i call the second recursive call with n or n'
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pairList
      have funcy :=  impl x y a (as.map .atoms) (ys++imps)
      simp only [List.append_assoc] at funcy
      have h₁ := List.map funcy.uncurry pairList
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
      exact h₁
  | .seq4 as ((.neg x) :: ys) imps n a => by
      have proofList := automatedProof (.seq4 as ys (imps ++ [.neg x]) n x)
      have funky := negl x a (as.map .atoms) (ys++imps)
      simp only [seqAtoms2seq, List.append_assoc] at proofList
      simp only [List.append_assoc] at funky
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
      exact List.map funky proofList
  | .seq4 as ((.atoms x) :: ys) imps n a =>
    have h₁ := automatedProof (.seq4 (as ++ [x]) ys imps n a)
    by unfold seqAtoms2seq
       simp only [List.append_assoc, List.cons_append]
       unfold seqAtoms2seq at h₁
       simp at h₁
       exact h₁
  | .seq4 as (.bot :: ys) imps n a => by
    have rule := [botl a (as.map .atoms) (ys++imps)]
    simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
    exact rule
termination_by (termination_metric s)
decreasing_by
. simp only [termination_metric]
  apply Prod.Lex.left
  simp
. simp
  apply Prod.Lex.left
  simp
. simp
  apply Prod.Lex.right
  unfold size_sum; unfold size_sum; simp
. simp
  apply Prod.Lex.right
  simp
  rw [Nat.add_comm 1 (sizeOf_Form a)]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. simp
  apply Prod.Lex.right
  simp
. simp; apply Prod.Lex.right; simp
  rw [Nat.add_comm 1 (sizeOf_Form a)]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. simp
  apply Prod.Lex.right
  simp
. simp; apply Prod.Lex.right
  unfold size_sum; simp
  unfold size_sum; simp
. simp; apply Prod.Lex.right; simp
  unfold size_sum; conv => rhs; unfold sizeOf_Form;
  conv => lhs; unfold size_sum
  rw [← Nat.add_assoc]
  simp only [add_lt_add_iff_right, lt_add_iff_pos_left, Nat.lt_one_iff, pos_of_gt]
. simp; apply Prod.Lex.right; simp
  unfold size_sum; conv => rhs; unfold sizeOf_Form;
  simp; rw[Nat.add_comm 1 _]; rw [Nat.add_assoc]
  simp
. simp; apply Prod.Lex.right; simp
  unfold size_sum; conv => rhs; unfold sizeOf_Form;
  simp;
. simp; apply Prod.Lex.right
  conv => rhs; unfold size_sum; simp only [sizeOf_Form]
  rw[Nat.add_comm _ (size_sum ys)]; conv => rhs; rw[Nat.add_comm _ (sizeOf_Form x)]; rw [← Nat.add_assoc]; rw [← Nat.add_assoc]
  refine Nat.lt_add_right (sizeOf_Form a) ?_; refine Nat.lt_add_right (sizeOf_Form y) ?_
  apply Nat.lt_succ_self
. simp; apply Prod.Lex.right; simp
  unfold size_sum; conv => rhs; unfold sizeOf_Form;
  simp
. simp; apply Prod.Lex.right
  conv => rhs; unfold size_sum; simp only [sizeOf_Form]
  rw[Nat.add_comm _ (size_sum ys)]; rw[Nat.add_comm 1 _]; rw [← Nat.add_assoc];
  refine Nat.lt_add_right (sizeOf_Form a) ?_; apply Nat.lt_succ_self
. simp; apply Prod.Lex.right; simp
  conv => rhs; unfold size_sum
  simp
end

def automatedProofHelper (s : Sequent) : List (Proof s) :=
  match s with
  | .seq xs a => by
    have proofs := automatedProof (Seq4Proof.seq4 [] xs [] 2 a)
    simp only [seqAtoms2seq, List.map_nil, List.nil_append, List.append_nil] at proofs
    exact proofs

---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString a :=
    match a with
    | atom₁ => "a"
    | atom₂ => "b"
    | atom₃ => "c"

def formToString (form : Form) : String :=
   match form with
    | .bot => "⊥"
    | .atoms a => toString a
    | .neg a => "¬" ++ formToString a
    | .and a b => "(" ++ formToString a ++ " ∧ " ++ formToString b ++ ")"
    | .or a b => "(" ++ formToString a ++ " ∨ " ++ formToString b ++ ")"
    | .imp a b => "(" ++ formToString a ++ " → " ++ formToString b ++ ")"

instance : ToString Form where
  toString form := formToString form

instance : ToString Sequent where
  toString seq :=
  match seq with
  | .seq xs a => (List.map formToString xs).toString ++ "⊢" ++ formToString a

instance : ToString Seq4Proof where
  toString seq4 :=
  match seq4 with
  | .seq4 as xs is _ a => (List.map toString as).toString ++ (List.map formToString xs).toString ++ (List.map formToString is).toString ++ "⊢" ++ formToString a

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map formToString)

def proofToString {seq : Sequent} : Proof seq → String
| .ax a xs ys =>
  s!"AX: {formToString a}, {listToString xs}, {listToString ys} ⊢ {formToString a}"
| .botl a xs ys =>
  s!"⊥L: ⊥, {listToString xs}, {listToString ys} ⊢ {formToString a}"
| .negr a xs ys proof =>
  s!"{proofToString proof} '\n' ¬R: {listToString xs}, {listToString ys} ⊢ ¬{formToString a}"
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
| .impr a b xs ys proof  =>
  s!"{proofToString proof} '\n' →R: {listToString xs}, {listToString ys} ⊢ {formToString a} → {formToString b}"

/-
all ToString instances are for pretty-printing purposes
 -/
def listProofToString : List (Proof seq) → String
| [] => ""
| x::xs => proofToString x ++ listProofToString xs

instance : ToString (List (Proof seq)) where
  toString proof := listProofToString proof

--modusponens "a → b, a ⊢ β"
#eval listProofToString (automatedProofHelper (.seq [.imp (.atoms .atom₁) (.atoms .atom₂), .atoms .atom₁] (.atoms .atom₂)))

--  (x ∨ y) ∧ z ⊢ (x ∧ z) ∨ (y ∧ z)
#eval listProofToString (automatedProofHelper (.seq [.and (.or (.atoms .atom₁) (.atoms .atom₂)) (.atoms .atom₃)] (.or (.and (.atoms .atom₁) (.atoms .atom₃) ) (.and (.atoms .atom₂) (.atoms .atom₃)))))

-- ⊢ ¬¬ (¬x ∨ x)
#eval listProofToString (automatedProofHelper (.seq [] (.neg (.neg (.or (.neg (.atoms .atom₁)) (.atoms .atom₁))))))
