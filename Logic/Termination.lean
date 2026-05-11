import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Lex

import Logic.Core

namespace multiSucc
open multiSucc

/-
Atomic values get valued as one , not as 0, to help show termination for the atomic case in antecedent, same with bottom.
 -/
@[simp, grind]
def Form.complexity : Form → Nat
  | ⊥ => 1
  | .atom _ => 1
  | .and p q => 1 + p.complexity + q.complexity
  | .or p q => 1 + p.complexity + q.complexity
  | .imp p q => 1 + p.complexity + q.complexity

--complexity of set of principle formulas: nr of logical symbols occuring in them
@[grind,simp]
def Form.listComplexity : List Form → Nat
  | [] => 0
  | f :: fs => 2 * complexity f + Form.listComplexity fs

@[grind,simp]
def Form.listComplexity' : List Form → Nat
  | [] => 0
  | f :: fs => 2 * complexity f + 1 + Form.listComplexity' fs


/-- weight function based on paper to prove termination :
- (r,n) where r is nr of R→ occurences there has been in this branch
- cap_r is the difference of the max r value and current and
- n is the complexity of the set of forms that can be used as principle to any rule
-/
@[grind]
structure Weight where
  cap_r : ℕ -- cap - r
  n : ℕ

namespace Weight
-- now it is a Lex order
@[simp, grind]
def toPair (w : Weight) : ℕ × ℕ := (w.cap_r, w.n)

@[simp, grind]
instance : LT Weight :=
  ⟨fun a b => (toLex (toPair a) : ℕ ×ₗ ℕ) < toLex (toPair b)⟩


 @[simp, grind =]
theorem lt_iff {a b : Weight } : a < b ↔ a.cap_r < b.cap_r ∨ a.cap_r = b.cap_r ∧ a.n < b.n := by
  simpa [Weight.toPair] using
    (Prod.Lex.toLex_lt_toLex (x := toPair a) (y := toPair b))

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
  | .bot | .atom _ =>  ∅
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
  functionally doing nothing but it still must decrease. atoms don't make a difference here -/
def Seq4Proof.weight (p : Seq4Proof) (cap : ℕ)  : Weight :=
let r := cap - p.r.card
let n :=
  let cL := Form.listComplexity p.fL
  let cR := Form.listComplexity' p.fR
  let cImpR := Form.listComplexity (p.impR.map Imp.toForm)
  cL + cR + cImpR
{ cap_r := r , n := n}

@[simp, grind]
theorem Seq4Proof.weight_cap_r (p : Seq4Proof) (cap : ℕ) :
    (p.weight cap).cap_r = cap - p.r.card := by
  simp [Seq4Proof.weight]

@[simp, grind]
theorem Seq4Proof.weight_n (p : Seq4Proof) (cap : ℕ) :
    (p.weight cap).n =
      Form.listComplexity p.fL + Form.listComplexity' p.fR + Form.listComplexity (p.impR.map Imp.toForm) := by
  simp [Seq4Proof.weight]

@[grind .]
theorem impR_cap
(block : List Imp)
(hist : List Imp)
(impR : List Imp)
(ha : { f := f, g := g } ∈ impR)
: insert { f := f, g := g }
    (collectImpsForm f ∪
      ((List.map Imp.toForm block).toFinset.biUnion collectImpsForm ∪ (collectImpsForm g ∪ hist.toFinset))) ⊆
  block.toFinset.biUnion collectImpsImp ∪ (impR.toFinset.biUnion collectImpsImp ∪ hist.toFinset) := by
  have inclusion : insert { f, g } ( collectImpsForm f ∪ collectImpsForm g) ⊆ impR.toFinset.biUnion collectImpsImp := by
    intro x hx
    simp at hx
    rcases hx with head | tail₁ | tail₂
    all_goals simp_all; grind
  have eq : block.toFinset.biUnion collectImpsImp = (block.map Imp.toForm).toFinset.biUnion collectImpsForm := by ext x; simp [Finset.mem_biUnion]
  grind


end multiSucc
#min_imports
