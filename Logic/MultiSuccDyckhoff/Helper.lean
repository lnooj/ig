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
import Mathlib.Data.Multiset.DershowitzManna

import Logic.MultiSuccDyckhoff.Core
import Logic.MultiSuccDyckhoff.Display

namespace multiSucc
open multiSucc
/- Based on paper
 To measure the "size" of sequents, we need to define the weight of a formula.
Gived a well-founded order relation > on formulae
 -/
@[simp]
def Form.weight : Form → Nat
  | .bot => 1
  | .atoms _ => 1
  | .and p q => 2 + p.weight + q.weight
  | .or p q => 1 + p.weight + q.weight
  | .imp p q => 1 + p.weight + q.weight

@[simp]
instance : LT Form := ⟨fun b a => b.weight < a.weight⟩


@[grind,simp]
def weight_sum : List Form → Nat
  | [] => 0
  | f :: fs => 2 * f.weight + weight_sum fs

@[grind,simp]
def weight_sum_increased : List Form → Nat
  | [] => 0
  | f :: fs => 2 * f.weight + 1 + weight_sum_increased fs


--Prove fell-foundedness of weight
instance formWeightWellFoundedRelation : WellFoundedRelation Form where
  rel b a := b < a
  wf := by
    let rel' : WellFoundedRelation Form := (invImage Form.weight Nat.lt_wfRel)
    convert rel'.wf with a b


/- size of the sequent is antecedent and goal forms weight together in a multiset

 -/
def Sequent.size : Sequent → Multiset Nat
  | .seq Δ Γ => (Δ.map Form.weight) + (Γ.map Form.weight)

/-
This is used as the second argument of a lexicographic order,
to show termination for the 2 cases where we move imps to imps list and atom to atoms list.
So the original forms list carries more wight than the distributed lists.
 -/
def Seq4Proof.size (s : Seq4Proof) : Nat :=
  match s with
  | .seq4 _ forms₁ imps₁ _ forms₂ imps₂ =>  (weight_sum_increased forms₁) + (weight_sum imps₁) + (weight_sum_increased forms₂) + (weight_sum imps₂)

/-
The Multiset Ordering. Based on Form.weight multisets
equivalent seqLE → Multiset.lt?
This has already been defined in Mathlib.Data.Multiset.DershowitzManna
 -/

instance sequentWellFoundedRelation : WellFoundedRelation Sequent where
  rel Δ' Δ := Multiset.IsDershowitzMannaLT Δ'.size Δ.size
  wf := (invImage Sequent.size (Multiset.instWellFoundedIsDershowitzMannaLT (α := Nat))).wf
#print axioms sequentWellFoundedRelation
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
