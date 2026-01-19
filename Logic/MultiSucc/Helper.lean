import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card

import Logic.MultiSucc.Core

namespace multiSucc
open multiSucc
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
  ∀ pair ∈ (splitBy xs a), pair.1 ++ (a :: pair.2) = xs := by
  sorry

/-
Atomic values get valued as one , not as 0, to help show termination for the atomic case in antecedent, same with bottom.
 -/
@[simp, grind]
def sizeOf_Form : Form → Nat
  | ⊥ => 1
  | .atoms _ => 1
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q

@[simp, grind]
def sizeOf_Form_increased : Form → Nat
  | ⊥ => 2
  | .atoms _ => 2
  | .and p q => 2 + sizeOf_Form_increased p + sizeOf_Form_increased q
  | .or p q => 2 + sizeOf_Form_increased p + sizeOf_Form_increased q
  | .imp p q => 2 + sizeOf_Form_increased p + sizeOf_Form_increased q


--complexity of set of principle formulas: nr of logical symbols occuring in them
@[grind,simp]
def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => 2 * sizeOf_Form f + size_sum fs

@[grind,simp]
def size_sum_increased : List Form → Nat
  | [] => 0
  | f :: fs => 2 * sizeOf_Form f + 1 + size_sum_increased fs


/-- weight function based on paper to prove termination :
- (r,n) where r is nr of R→ occurences there has been in this branch and
- n is the complexity of the set of forms that can be used as principle to any rule
-/
@[grind]
structure Weight (cap : ℕ) where
  r : ℕ
  n : ℕ
  hr : r ≤ cap

namespace Weight

@[simp]
instance instLT (cap : ℕ) : LT (Weight cap) where
  lt a b := a.r > b.r ∨ a.r = b.r ∧ a.n < b.n

instance instWellFoundedRelation {cap : ℕ} : WellFoundedRelation (Weight cap) where
  rel a b := a < b
  wf := by
    simp only [instLT]
    let rel' : WellFoundedRelation (Weight cap) :=
      invImage (fun x ↦ ⟨cap - x.r, x.n⟩) Prod.instWellFoundedRelation
    convert rel'.wf with a b
    simp only [WellFoundedRelation.rel, rel']
    grind [InvImage, Nat.lt_wfRel, sizeOf_nat]


end Weight


@[simp, grind]
def collectImps (x : Form) : Finset Form :=
match x with
  | .bot | .atoms _ =>  ∅
  | .and a b | .or a b => collectImps a ∪ collectImps b
  | .imp a b => {.imp a b} ∪ collectImps a ∪ collectImps b

/-- Limit for our Weight relatiom
- cap represents the max nr of forms that can be the principal for R→,
- it is a Finset (not a List as before), because any imp form can be principal of R→ ONLY ONCE, so we dont care about order nor duplicates
- we need it to still be a set, not just it's cardinality to show subset relations in proof (no new implications are made, set will only get smaller)
- cardinality of this set is used for proving well-foundedness
- every imp list is gone through recursively to collect ALL implications, exept the R→ list itsself (usedImps₂)-/
@[simp, grind]
def Seq4Proof.cap (p : Seq4Proof) : Finset Form:=
match p with
| .seq4 _  forms₁ imps₁ usedImps₁ _ forms₂ imps₂ usedImps₂  =>
   ((forms₁.toFinset.biUnion collectImps) ∪ (imps₁.toFinset.biUnion collectImps) ∪ (usedImps₁.toFinset.biUnion collectImps) /- usedImps₁  -/∪ -- toFinset.biUnion usedImps1 as well to ease proof on fist rec call
   usedImps₂.toFinset ∪ (imps₂.toFinset.biUnion collectImps) ∪ (forms₂.toFinset.biUnion collectImps))

/-- occurences of R→ rule so far, stored in usedImps₂  -/
@[simp, grind]
def Seq4Proof.r (p: Seq4Proof) : Finset Form :=
match p with
| .seq4 _ _ _ _ _ _ _ usedImps₂  => usedImps₂.toFinset

@[simp, grind .]
theorem Seq4Proof.r_subset_cap (p : Seq4Proof) : p.r ⊆ p.cap := by simp only [r, cap, Finset.union_assoc]; grind

/-- Local sequents Weight function
- given a sequent p, global cap.card and proof that current sequents cap is smaller than global
- sixeOf_Form is used, not complexity, for some cases this doesn't change
- the forms list size must be higher than the imp lists, for in our recursive calls we might only move the implications to appropriate lists,
  functionally doing nothing but it still must decrease. atoms donn't make a difference here -/
def Seq4Proof.weight (p : Seq4Proof) (cap : ℕ) (hcap : p.cap.card ≤ cap) : Weight cap :=
let r := p.r.card
let n :=
  match p with
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁ atoms₂ forms₂ imps₂ _  =>
      let cL := size_sum_increased forms₁--(countPrinciple forms₁ usedImps₁)-- forms in usedImps₁ can not be principle PRINCIPLE LOGIC NOT USED
      let cR := size_sum_increased forms₂ --any imp on right side can be principle, bc either a fort is used or R→
      let cImpL := size_sum imps₁
      let cImpR := size_sum imps₂
      cL + cR + cImpL + cImpR
let h : p.r.card ≤ p.cap.card := by
  simp only [Seq4Proof.cap, Finset.union_assoc, Seq4Proof.r];
  apply (Finset.card_le_card ?_); grind

let hr : p.r.card ≤ cap :=  Nat.le_trans h hcap
{ r, n := n, hr }



/-
needed to find all possible pairings (of proofs) for cases like or, and ...
 -/
def getPairs (xs : List α ) (ys : List β ) : List (α × β) :=
  match xs with
  | [] => []
  | x::xs' => List.map (λ y => (x , y)) ys ++ getPairs xs' ys


/- find common atoms in anticident atoms list and succedent atoms list.
  current: wo duplicates
  Maybe return positions, to be precise, List (Atom, (index from xs, index from ys)) -/
def findIntersection : List Atom → List Atom → List Atom
-- xs.filter (fun a => a ∈ ys) |>.eraseDups
  | _ ,[] => []
  | xs, y::ys =>
    if y ∈ xs then
      if y ∈ findIntersection xs ys then
        findIntersection xs ys
      else y :: findIntersection xs ys
    else findIntersection xs ys

#eval findIntersection [Atom.mk 1] [Atom.mk 1, Atom.mk 2, Atom.mk 1]

--TODO theorem: when findIntersection empty, no overlapping atoms in either lists

theorem findIntersCorr (xs : List Atom) (ys : List Atom) :
  ∀ x ∈ (findIntersection xs ys), x ∈ xs ∧ x ∈ ys :=
  λ xatom xatom_in =>
  match ys with
  | [] => by simp [findIntersection] at xatom_in
  | y' :: ys' => by
    unfold findIntersection at xatom_in
    by_cases cond₁: y' ∈ xs
    . simp [cond₁] at xatom_in
      by_cases cond₂: y' ∈ findIntersection xs ys'
      . simp [cond₂] at xatom_in
        have ih := findIntersCorr xs ys'
        have ⟨h₁, h₂⟩ := ih xatom xatom_in
        exact ⟨h₁, List.Mem.tail _ h₂⟩
      . simp [cond₂] at xatom_in
        match xatom_in with
        | Or.inl left =>
          simp [left] at xatom_in
          subst left
          exact ⟨ cond₁, List.mem_cons_self⟩
        | Or.inr right =>
          have ih := findIntersCorr xs ys'
          have ⟨h₁, h₂⟩ := ih xatom right
          exact ⟨h₁, List.mem_cons_of_mem _ h₂ ⟩
    . simp [cond₁] at xatom_in
      have ih := findIntersCorr xs ys'
      have ⟨h₁, h₂⟩ := ih xatom xatom_in
      exact ⟨h₁, List.Mem.tail _ h₂⟩

end multiSucc
