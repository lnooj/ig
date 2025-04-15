-- import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw

--make this decidable, solvable

inductive Atom
  | x : Atom | y : Atom | z : Atom
  deriving DecidableEq

inductive Form
  | bot : Form
  | atoms : Atom → Form
  | neg : Form → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
  -- | forall : Atom → Form → Form
open Form

@[simp]
def sizeOf_Form : Form → Nat
  | .bot => 0
  | .atoms _ => 0
  | .neg f => 1 + sizeOf_Form f
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q

-- [f1,f2] ⊢ x
inductive Sequent
  | seq : (context : List Form) → Form → Sequent

-- [x, y], [f1, f2] ⊢ f
inductive Seq4Proof : Type
  | seq4 : (context1 : List Atom) → (context2 : List Form) → Form → Seq4Proof

@[simp]
def termination_metric (s : Seq4Proof) : Nat :=
  match s with
  | .seq4 _ [] f => sizeOf_Form f
  | .seq4 a (x::xs) f =>
    sizeOf_Form x + termination_metric (.seq4 a xs f)
termination_by s
decreasing_by
  . simp; exact Nat.pos_of_neZero (1 + sizeOf x)

@[simp]
def termination_metric' (s : Seq4Proof) : Nat :=
  match s with
  | .seq4 _ ys f => sizeOf_Form f + (ys.map sizeOf_Form).foldl (· + ·) 0


--def negation (x : Form) : Form := .imp x .bot

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
  | negr : ∀ (x : Form) (xs : List Form),
            Proof (.seq (xs ++ [x]) .bot) →
            Proof (.seq (xs) (.neg x))
  -- ∀ a b Γ, (Γ, ¬a ⊢ a) → (Γ, ¬a ⊢ b)
  | negl : ∀ (x y : Form) (xs ys : List Form),
            Proof (.seq (xs ++ (.neg x) :: ys) x) →
            Proof (.seq (xs ++ (.neg x) :: ys) y)
/-   | negr :
    ∀ (x : Form) (xs ys : List Form),
      Proof (.seq (xs ++ ys) (.imp x .bot)) →
      Proof (.seq (xs ++ ys) (.neg x)) -/
  -- ∀ a b Γ , (Γ, a → ⊥ ⊢ b) → (Γ, ¬a ⊢ b)
/-   | negl :
    ∀ (x y : Form) (xs ys : List Form),
      Proof (.seq (xs ++ (.imp x .bot) :: ys) y) →
      Proof (.seq (xs ++ .neg x :: ys) y) -/
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
      Proof (.seq (xs ++ .imp a b :: ys ) a) →
      Proof (.seq (xs ++ b :: ys ) c) →
      Proof (.seq (xs ++ (.imp a b) :: ys) c)
  -- ∀ a b Γ, (a, Γ ⊢ b) → (Γ ⊢ a → b)
  | impr :
    ∀ (a b : Form) (xs  : List Form),
      Proof (.seq (xs ++ [a] ) b) →
      Proof (.seq (xs) (.imp a b))
  -- how to define substitution for x → t
  --| alll :
  --  ∀ (x t : Atom) (a c : Form) (xs ys : List Form),
  --    Proof (.seq (xs ++ .forall x a :: a :: ys ) c) →
  --    Proof (.seq (xs ++ .forall x a :: ys ) c)
open Proof

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


 /-  match xs with
    | [] => simp [splitBy] at h
            match g : splitBy [] a with
            | [] => simp

    | x'::xs' => sorry -/

def getPairs (xs : List α ) (ys : List β ) : List (α × β) :=
  match xs with
  | [] => []
  | x::xs' => List.map (λ y => (x , y)) ys ++ getPairs xs' ys

@[simp]
def seqAtoms2seq (s : Seq4Proof) : Sequent :=
  match s with
  | .seq4 xs ys a =>
    Sequent.seq ((xs.map .atoms) ++ ys) a

/- def helper (xs : List Atom) (ys : List Form) : List Form :=
  ys ++ (xs.map .atoms) -/

def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
  match s with
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
  --bottom
  | .seq4 as ((.and x y)::ys) a =>
    have h₁ := automatedProof (.seq4 as (x :: y :: ys) a)
    List.map (andl x y a (as.map .atoms) ys) h₁
  | .seq4 as ((.or x y) :: ys) a =>
      (getPairs (automatedProof (.seq4 as (x::ys) a)) (automatedProof (.seq4 as (y::ys) a))).map
      (orl x y a (as.map .atoms) ys).uncurry
  | .seq4 as ((.imp x y) :: ys) a =>
      (getPairs (automatedProof (.seq4 as ((.imp x y) :: ys) x ))
                (automatedProof (.seq4 as (y::ys) a))).map
      (impl x y a (as.map .atoms) ys).uncurry
  | _ => sorry
termination_by termination_metric s
decreasing_by
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . simp only [termination_metric, sizeOf_Form]
    conv => lhs; rw [←Nat.add_assoc]
    have := Nat.le_succ (sizeOf_Form x + sizeOf_Form y + termination_metric (Seq4Proof.seq4 as ys a))
    simp only [Nat.add_lt_add_iff_right, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  . sorry
  . sorry
  . sorry
  . sorry



  /- dsimp [termination_metric, sizeOf_Form]
  simp only [List.map, List.foldl, Nat.zero_add]
  rw [Nat.add_comm 1 (sizeOf_Form a)]
  apply Nat.lt_add_of_pos_right
  exact Nat.zero_lt_one -/


/- decreasing_by
  dsimp [termination_metric, sizeOf_Form]
  simp only [Nat.zero_add,  Nat.lt_add_one]
  rw [Nat.add_comm 1 (sizeOf_Form a)]
  apply Nat.lt_succ_self
  exact Nat.lt_succ_self (sizeOf_Form a) -/


def automatedProofHelper (s : Sequent) : List (Proof s) :=
  match s with
  | .seq xs a => automatedProof (Seq4Proof.seq4 [] xs a)



-- p ∧ q ⊢ q ∧ p
def andCom :
  ∀ (a b : Form),
    Proof (.seq [.and a b] (.and b a)) := λ a b =>
  .andr
    (.andl [] [] (.ax b [a] []))
    (.andl [] [] (.ax a [] [b]))

def andCom' :
  ∀ (a b : Form),
    Proof (.seq [.and a b] (.and b a)) := λ a b =>
  .andl [] [] (.andr (.ax b [a] []) (.ax a [] [b]))
  --λ a b => by run_tac .andr

-- A ⊢ B → (A ∧ B)
def excercise :
  ∀ (a b : Form), Proof (.seq [a] (.imp b (.and a b))) :=
  λ a b => .impr b (.and a b) [a] [] (.andr (.ax a [] [b]) (.ax b [a] []))

-- ⊢ ¬(A ∧ ¬A)
def excludedMiddle :
  ∀ (a : Form), Proof (.seq [] (.neg (.and a (.neg a)))) :=
  λ a => .negr (.and a (.neg a)) [] []
            (.impr (.and a (.neg a)) .bot [] []
              (.andl [] [] (.negl a .bot [a] [] ( Proof.impl a .bot .bot [a] []
                (.ax (a) [] [.imp a .bot] ) (.ax .bot [a] []) ))))

-- ¬(A ∨ B) → ¬A ∧ ¬B
def deMorgan :
  ∀ (a b : Form), Proof (.seq [.neg (.or a b)] (.and (.neg a ) (.neg b))) :=
  λ a b => sorry
