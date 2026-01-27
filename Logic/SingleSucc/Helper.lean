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


import Logic.SingleSucc.Core
import Logic.SingleSucc.Display

namespace singleSucc
open singleSucc
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

@[grind,simp]
def weight_sum : List Form → Nat
  | [] => 0
  | f :: fs => 2 * f.weight + weight_sum fs

@[grind,simp]
def weight_sum_increased : List Form → Nat
  | [] => 0
  | f :: fs => 2 * f.weight + 1 + weight_sum_increased fs

@[simp]
instance : LT Form := ⟨fun b a => b.weight < a.weight⟩

--Prove fell-foundedness of weight
instance formWeightWellFoundedRelation : WellFoundedRelation Form where
  rel b a := b < a
  wf := by
    let rel' : WellFoundedRelation Form := (invImage Form.weight Nat.lt_wfRel)
    convert rel'.wf with a b


/- size of the sequent is antecedent and goal forms weight together in a multiset

 -/
def Sequent.size : Sequent → Multiset Nat
  | .seq Δ G => ((Δ).map Form.weight) + {G.weight}

/-
This is used as the second argument of a lexicographic order,
to show termination for the 2 cases where we move imps to imps list and atom to atoms list.
So the original forms list carries more wight than the distributed lists.
 -/
def Seq4Proof.size (s : Seq4Proof) : Nat :=
  match s with
  | .seq4 _ forms imps goal =>  (weight_sum_increased forms) + (weight_sum imps) + goal.weight

/-
The Multiset Ordering. Based on Form.weight multisets
equivalent seqLE → Multiset.lt?
This has already been defined in Mathlib.Data.Multiset.DershowitzManna
 -/
/- instance seqLE : LE Sequent where
  le Δ' Δ := ∃ X Y : Multiset Nat,
              (∅ ≠ X ∧ X ⊆ Δ.size) ∧
              (Δ'.size = (Δ.size - X) ∪ Y ) ∧
              (∀ y ∈ Y, ∃ x ∈ X, x > y) -/

instance sequentWellFoundedRelation : WellFoundedRelation Sequent where
  rel Δ' Δ := Multiset.IsDershowitzMannaLT Δ'.size Δ.size
  wf := (invImage Sequent.size (Multiset.instWellFoundedIsDershowitzMannaLT (α := Nat))).wf

/-
needed to find all possible pairings (of proofs) for cases like or, and ...
 -/
def getPairs (xs : List α ) (ys : List β ) : List (α × β) :=
  match xs with
  | [] => []
  | x::xs' => List.map (λ y => (x , y)) ys ++ getPairs xs' ys


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
      simp only [Bool.false_eq_true] at pair_in
      simp only [if_false] at pair_in
      simp only [List.mem_map] at pair_in
      let ⟨elem,elem_in,eq⟩ := pair_in
      clear pair_in
      have ih := splitByCorrectness xs a _ elem_in
      subst eq
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact ih

end singleSucc
