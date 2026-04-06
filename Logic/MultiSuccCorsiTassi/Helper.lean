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

import Logic.MultiSuccCorsiTassi.Core

namespace multiSucc
open multiSucc

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
- (r,n) where r is nr of R→ occurences there has been in this branch
- cap_r is the difference of the max r value and current and
- n is the complexity of the set of forms that can be used as principle to any rule
-/
@[grind]
structure Weight where
  cap_r : ℕ -- cap - r
  n : ℕ
  --hr : r ≤ cap

namespace Weight
-- now it is a Lex order
@[simp, grind]
def toPair (w : Weight) : ℕ × ℕ := (w.cap_r, w.n)

@[simp, grind]
instance : LT Weight :=
  ⟨fun a b => (toLex (toPair a) : ℕ ×ₗ ℕ) < toLex (toPair b)⟩

/-  @[grind]
def lt (a b : Weight ) := a.cap_r < b.cap_r ∨ a.cap_r = b.cap_r ∧ a.n < b.n
 -/

 @[simp, grind =]
theorem lt_iff {a b : Weight } : a < b ↔ a.cap_r < b.cap_r ∨ a.cap_r = b.cap_r ∧ a.n < b.n := by
  simpa [Weight.toPair] using
    (Prod.Lex.toLex_lt_toLex (x := toPair a) (y := toPair b))
/-
@[simp, grind]
theorem mk_lt_mk {a₁ a₂ b₁ b₂ : ℕ} :
    ({ cap_r := a₁, n := a₂ } : Weight) < { cap_r := b₁, n := b₂ }
      ↔ a₁ < b₁ ∨ a₁ = b₁ ∧ a₂ < b₂ := by
  rfl -/

/- @[simp]
theorem lt_toLex_iff (a b : Weight) :
  ((toLex (a.cap_r, a.n) : ℕ ×ₗ ℕ) < (toLex (b.cap_r, b.n) : ℕ ×ₗ ℕ)) ↔ a < b := by
  simpa [Weight.lt] using
    (Prod.Lex.toLex_lt_toLex
      (x := (a.cap_r, a.n)) (y := (b.cap_r, b.n)))
 -/
@[simp, grind]
instance instWellFoundedRelation : WellFoundedRelation (Weight ) where
  rel a b := a < b
  wf := by
    let rel' : WellFoundedRelation Weight :=
      invImage (fun x ↦ (toLex x.toPair : ℕ ×ₗ ℕ)) Prod.Lex.instWellFoundedRelationLexOfWellFoundedLT
    convert rel'.wf with a b

end Weight


@[simp, grind]
def collectImpsForm (x : Form) : Finset Imp :=
match x with
  | .bot | .atoms _ =>  ∅
  | .and a b | .or a b => collectImpsForm a ∪ collectImpsForm b
  | .imp a b => {⟨a, b⟩} ∪ collectImpsForm a ∪ collectImpsForm b

@[simp, grind]
def collectImpsImp (x : Imp) : Finset Imp := {x} ∪ collectImpsForm x.f ∪ collectImpsForm x.g

@[simp, grind =]
theorem collectImps_equality : ∀ (x : Imp), collectImpsImp x = collectImpsForm (x.toForm) :=
  by simp only [collectImpsImp, Finset.singleton_union, Finset.insert_union, Imp.toForm, collectImpsForm, implies_true]

/-- Limit for our Weight relatiom
- cap represents the max nr of forms that can be the principal for R→,
- it is a Finset (not a List as before), because any imp form can be principal of R→ ONLY ONCE, so we dont care about order nor duplicates
- we need it to still be a set, not just it's cardinality to show subset relations in proof (no new implications are made, set will only get smaller)
- cardinality of this set is used for proving well-foundedness
- every imp list is gone through recursively to collect ALL implications, exept the R→ list itsself (history)-/
@[simp, grind]
def Seq4Proof.cap (p : Seq4Proof) : Finset Imp:=
   p.fL.toFinset.biUnion collectImpsForm ∪ p.block.toFinset.biUnion collectImpsImp ∪ -- toFinset.biUnion usedImps1 as well to ease proof on fist rec call
  p.fR.toFinset.biUnion collectImpsForm ∪ p.impR.toFinset.biUnion collectImpsImp ∪ p.hist.toFinset -- rightImp gets also counted recursively, because when applying R→ the left and right side go to forms

/-- occurences of R→ rule so far, stored in history  -/
@[simp, grind]
def Seq4Proof.r (p: Seq4Proof) : Finset Imp := p.hist.toFinset

@[simp, grind .]
theorem Seq4Proof.r_subset_cap (p : Seq4Proof) : p.r ⊆ p.cap := by simp only [r, cap, Finset.union_assoc]; grind

/-- Local sequents Weight function
- given a sequent p, global cap.card and proof that current sequents cap is smaller than global
- sixeOf_Form is used, not complexity, for some cases this doesn't change
- the forms list size must be higher than the imp lists, for in our recursive calls we might only move the implications to appropriate lists,
  functionally doing nothing but it still must decrease. atoms donn't make a difference here -/
def Seq4Proof.weight (p : Seq4Proof) (cap : ℕ)  : Weight :=
let r := cap - p.r.card
let n :=
      let cL := size_sum p.fL--(countPrinciple forms₁ blocked)-- forms in blocked can not be principle PRINCIPLE LOGIC NOT USED
      let cR := size_sum_increased p.fR --any imp on right side can be principle, bc either a fort is used or R→
      --let cImpL := size_sum imps₁
      let cImpR := size_sum (p.impR.map Imp.toForm)
      cL + cR + cImpR--+ cImpL + cImpR
/- let h : p.r.card ≤ p.cap.card := by
  simp only [Seq4Proof.cap, Finset.union_assoc, Seq4Proof.r];
  apply (Finset.card_le_card ?_); grind
let hr : p.r.card ≤ cap :=  Nat.le_trans h hcap -/
{ cap_r := r , n := n}

@[simp, grind]
theorem Seq4Proof.weight_cap_r (p : Seq4Proof) (cap : ℕ) :
    (p.weight cap).cap_r = cap - p.r.card := by
  simp [Seq4Proof.weight]

@[simp, grind]
theorem Seq4Proof.weight_n (p : Seq4Proof) (cap : ℕ) :
    (p.weight cap).n =
      size_sum p.fL + size_sum_increased p.fR + size_sum (p.impR.map Imp.toForm) := by
  simp [Seq4Proof.weight]



/-
needed to find all possible pairings (of proofs) for cases like or, and ...
 -/
def getPairs (xs : List α ) (ys : List β ) : List (α × β) :=
  match xs with
  | [] => []
  | x::xs' => List.map (λ y => (x , y)) ys ++ getPairs xs' ys

#eval [1,2,3,3,4] ∩ [1,3,3]
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


theorem mem_findIntersection_iff (x : Atom) :
  x ∈ findIntersection xs ys ↔ x ∈ xs ∧ x ∈ ys := by
  induction ys with
  | nil => simp [findIntersection]
  | cons y ys ih =>
    unfold findIntersection
    by_cases hxy : y ∈ xs
    · grind
    . grind

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

--TODO theorem: when findIntersection empty, no overlapping atoms in either lists
theorem noIntersection (xs : List Atom) (ys : List Atom) :
  (findIntersection xs ys) = [] → (∀ x ∈ xs, x ∉ ys) ∧ (∀ y ∈ ys, y ∉ xs ):=
  λ h => by
  constructor
  . intro x hx hxy
    have : x ∈ findIntersection xs ys :=
      (mem_findIntersection_iff x).2 ⟨hx, hxy⟩
    simp [h] at this
  . intro y hy hyx
    have : y ∈ findIntersection xs ys :=
      (mem_findIntersection_iff y).2 ⟨hyx, hy⟩
    simp [h] at this

end multiSucc
