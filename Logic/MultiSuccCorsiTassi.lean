import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic

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

def asImp : Form → Form
  | .neg a => .imp a .bot
  | f => f
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

-- [f1, f2] ⊢ [g1, g2]
inductive Sequent
  | seq : List Form → List Form → Sequent
deriving Repr

/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.

In addition we will seperate "special" forms (impl and negl), which require special treatment using a "fuel" counter
 -/
-- [x, y], usable[imp1, imp2], nonusable[imp1, imp2], [f1, f2] ⊢ [x, y], [imp1, imp2], [g1, g2]
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → List Form  → List Atom → List Form → List Form → Seq4Proof
deriving Repr

/-
Multi-succedent formulas Added a fortiori
 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (x : Form) (xs ys gs zs: List Form),
      Proof (.seq (xs ++ x :: ys) (gs ++ x :: zs)) --succ järjekord selline seq4toseq func pärast
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys gs : List Form),
      Proof (.seq (xs ++ .bot :: ys) gs)
  -- ∀ a Γ Δ, (Γ, a ⊢ ⊥) → (Γ ⊢ ¬a, Δ)
  | negr :
    ∀ (x : Form) (xs ys gs zs: List Form),
            Proof (.seq (xs ++ x :: ys) []) →
            Proof (.seq (xs ++ ys) (gs ++ (.neg x) :: zs))
  -- ∀ a Γ Δ, (Γ, ¬a ⊢ a, Δ) → (Γ, ¬a ⊢ Δ)
  | negl :
    ∀ (x : Form) (Γ₁ Γ₂ Δ₁ Δ₂: List Form),
            Proof (.seq (Γ₁ ++ .neg x :: Γ₂ ) (Δ₁ ++ x :: Δ₂)) → -- copy of .neg x in context, also as last elem bc equality error in proof func
            Proof (.seq (Γ₁ ++ .neg x :: Γ₂) (Δ₁ ++ Δ₂) )
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq (xs ++ a :: b :: ys) gs) → --antecedent järjekord?
      Proof (.seq (xs ++ (.and a b) :: ys) gs)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq xs (ys ++ a::gs)) →
      Proof (.seq xs (ys ++ b::gs)) →
      Proof (.seq xs (ys ++ (.and a b)::gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys gs : List Form),
    Proof (.seq (xs ++ a :: ys) gs) →
    Proof (.seq (xs ++ b :: ys) gs) →
    Proof (.seq (xs ++ (.or a b) :: ys) gs)
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq xs (ys ++ a :: b :: gs)) →   --TODO: a ja b järjekord ei tohiks oleneda
      Proof (.seq xs (ys ++ (.or a b) :: gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq (xs ++ a :: ys) [b]) →
      Proof (.seq (xs ++ ys) (gs ++ (.imp a b)::zs)) --succ järjestus
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq (xs ++ (.imp a b) :: ys) (gs ++ a :: zs)) →
      Proof (.seq (xs ++ b :: ys ) gs) →
      Proof (.seq (xs ++ (.imp a b) :: ys) gs)
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys gs : List Form),
      Proof (.seq xs (ys ++ b :: gs)) →
      Proof (.seq xs (ys ++ (.imp a b) :: gs))

deriving Repr
open Proof

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
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁  atoms₂ imps₂ forms₂ =>
    Sequent.seq ((atoms₁.map .atoms) ++ forms₁ ++ imps₁ ++ usedImps₁) ((atoms₂.map .atoms) ++ forms₂) -- imps₂ is to monitor R→ usage, not to display


def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => sizeOf_Form f + size_sum fs

@[simp]
def termination_metric (s : Seq4Proof) : Nat :=
match s with
  | .seq4 atoms₁ imps₁ usedImps₁ forms₁ atoms₂ imps₂ forms₂ => ( size_sum forms₁  + size_sum forms₂)

-- find common atoms in anticident atoms list and succedent atoms list-----
def findIntersection : List Atom → List Atom → List Atom
-- xs.filter (fun a => a ∈ ys) |>.eraseDups
  | _ ,[] => []
  | xs, y::ys =>
    if y ∈ xs then
      y :: findIntersection xs ys -- right now keeping duplicates, is that necessary?
    else findIntersection xs ys

/- theorem reorderAntOfProof :
  List.Perm Γ Γ' →
  Proof (Sequent.seq Γ Δ) →
  Proof (Sequent.seq Γ' Δ) := sorry
 -/
#check Multiset

/- METARULES
1. formula x can be principal of R→ (impr) only once
   - so whenever we apply R→ rule, we place it to the succedent imp list
2. a fortiori can be applied to formula x only when it has been analyzed by R→ rule
   - from succ forms list we  take a form and check if it is present in succ imps list, then can use a fortiori,

3. between two occurrences of L→ , there is an occurrence of R→ (on any form) in between
   - so when applying L→ , we place the copy of form to imp list on the left
     and enter inner rec function that we do until using R→, then exit and move on normally??
 how to add SIC pop n push functionality
 -/

partial def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
  match s with
  | .seq4 as forms₁ imps₁ usedImps₁  bs imps₂ forms₂ =>
    match forms₁ with
    | [] =>
      --open up forms on right side
      match forms₂ with
      | [] => -- succedent only has atoms left --
        match common : findIntersection as bs with
        -- no common atoms
        | [] => sorry
          -- fun stuff: we are left with left and right imp lists
        | y::ys => by
          have zs_corr := splitByCorrectness as y
          have g := splitBy as y -- we know this isn't empty, for y is in intersection
          sorry
      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) imps₂ succForms)
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | .bot :: succForms => sorry -- we are left with left and right imp lists
      | (.and a b) :: succForms => by
        have pair1 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs imps₂ (a :: succForms))
        have pair2 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs imps₂ (b :: succForms))
        unfold seqAtoms2seq at pair1; simp only [List.append_nil] at pair1
        unfold seqAtoms2seq at pair2; simp only [List.append_nil] at pair2
        have h := List.map (andr a b ((as.map .atoms)++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms).uncurry (getPairs pair1 pair2)
        unfold seqAtoms2seq; simp only [List.append_nil]
        exact h
      | (.or a b) :: succForms => by
        have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs imps₂ (a :: b :: succForms))--sus
        simp only [seqAtoms2seq, List.append_nil] at h₁
        have h₂ := List.map (orr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
        unfold seqAtoms2seq; simp only [List.append_nil]
        exact h₂
      | (.neg a) :: succForms => by --METARULE 1
        if (.neg a) ∉ imps₂ then
          have h₁ := automatedProof (.seq4 as [a] imps₁ usedImps₁ [] ((.neg a)::imps₂) []) -- forget stuff on right side
          simp at h₁
          have h₂ := List.map (negr a (as.map .atoms) (imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp
          exact h₂
        else -- HERE can try a fortiori METARULE 2
          have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs imps₂ (.bot :: succForms))--make rule for ⊥R, cus afort seperates this
          simp only [seqAtoms2seq, List.append_nil] at h₁
          have h₂ := List.map (afort a (.bot) ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp only [List.append_nil]
          --exact h₂ --TODO-- NEED TO DEFINE .NEG A AS A.IMP BOT
          sorry
      | (.imp a b) :: succForms => by --METARULE 1
        if (.imp a b) ∉ imps₂ then
          have h₁ := automatedProof (.seq4 as [a] imps₁ usedImps₁ [] ((.imp a b)::imps₂) [b])
          simp at h₁
          have h₂ := List.map (impr a b (as.map .atoms) (imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp
          exact h₂
        else
          have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs imps₂ (b :: succForms))
          simp only [seqAtoms2seq, List.append_nil] at h₁
          have h₂ := List.map (afort a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp only [List.append_nil]
          exact h₂

    -- open up forms on left side --
    | (.atoms a) :: antForms => by
      have h := automatedProof (.seq4 (as ++ [a]) antForms imps₁ usedImps₁ bs imps₂ forms₂)
      simp at h; simp; exact h
    | .bot :: antForms => by
      have h:= [botl (as.map .atoms) (antForms++imps₁++usedImps₁) ((bs.map .atoms)++forms₂)]
      simp only [List.append_assoc] at h
      simp
      exact h
    | (.neg a) :: antForms => sorry-- METARULE 3
    | (.and a b) :: antForms => by
      have h₁ := automatedProof (.seq4 as (a::b::antForms) imps₁ usedImps₁ bs imps₂ forms₂)
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at h₁
      rw [← List.append_assoc antForms imps₁ usedImps₁] at h₁
      have h₂ := List.map (andl a b ((as.map .atoms)) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂)) h₁
      unfold seqAtoms2seq; simp only [List.append_nil]
      simp only [← List.cons_append, ← List.append_assoc] at h₂
      exact h₂
    | (.or a b) :: antForms => by
      have pair₁ := automatedProof (.seq4 as (a::antForms) imps₁ usedImps₁ bs imps₂ forms₂)
      have pair₂ := automatedProof (.seq4 as (b::antForms) imps₁ usedImps₁ bs imps₂ forms₂)
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₁; rw [← List.append_assoc antForms imps₁ usedImps₁] at pair₁
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂; rw [← List.append_assoc antForms imps₁ usedImps₁] at pair₂
      have h := List.map (orl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂)).uncurry (getPairs pair₁ pair₂)
      simp only [← List.cons_append, ← List.append_assoc] at h
      exact h
    | (.imp a b) :: antForms => by -- METARULE 3
      have pair₁ := automatedProof (.seq4 as (antForms) imps₁ ((.imp a b):: usedImps₁) bs imps₂ (a::forms₂))
      have pair₂ := automatedProof (.seq4 as (b :: antForms) imps₁ ((.imp a b) :: usedImps₁) bs imps₂ (a::forms₂))
      simp only [seqAtoms2seq, List.append_assoc] at pair₁;
      have h := List.map (impl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) (bs.map .atoms) (forms₂)).uncurry (getPairs pair₁ pair₂)
      sorry
termination_by (termination_metric s)
decreasing_by
. simp
  conv => rhs; unfold size_sum; simp
  simp
