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
import Logic.MultiSucc.Syntax

namespace multiSucc
open multiSucc

/-
Multi-succedent formulas Added a fortiori
 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (x : Form) (xs ys gs zs: List Form),
      Proof (.seq ↑(xs ++ x :: ys) ↑(gs ++ x :: zs))
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys gs : List Form),
      Proof (.seq ↑(xs ++ ⊥ :: ys) ↑gs)
  | botr :
    ∀ (xs ys gs : List Form),
      Proof (.seq ↑xs ↑(ys ++ gs)) →
      Proof (.seq ↑xs ↑(ys ++ ⊥ :: gs))
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq ↑(xs ++ a :: b :: ys) ↑gs) →
      Proof (.seq ↑(xs ++ (a ∧∧ b) :: ys) ↑gs)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq ↑xs ↑(ys ++ a::gs)) →
      Proof (.seq ↑xs ↑(ys ++ b::gs)) →
      Proof (.seq ↑xs ↑(ys ++ (a ∧∧ b)::gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys gs : List Form),
    Proof (.seq ↑(xs ++ a :: ys) ↑gs) →
    Proof (.seq ↑(xs ++ b :: ys) ↑gs) →
    Proof (.seq ↑(xs ++ (a ∨∨ b) :: ys) ↑gs)
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys zs gs: List Form),
      Proof (.seq ↑xs ↑(ys ++ a :: zs ++ b :: gs)) →
      Proof (.seq ↑xs ↑(ys ++ ( a ∨∨ b) :: gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq ↑(xs ++ a :: ys) {b}) →
      Proof (.seq ↑(xs ++ ys) ↑(gs ++ (a ⊃ b)::zs)) --succ järjestus
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq ↑(xs ++ (a ⊃ b) :: ys) ↑(gs ++ a :: zs)) →
      Proof (.seq ↑(xs ++ b :: ys ) ↑(gs++zs)) →
      Proof (.seq ↑(xs ++ (a ⊃ b) :: ys) ↑(gs++zs))
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys gs : List Form),
      Proof (.seq ↑xs ↑(ys ++ b :: gs)) →
      Proof (.seq ↑xs ↑(ys ++ (a ⊃ b) :: gs))

--deriving Repr
open Proof


@[simp]
def seqAtoms2seq (s : Seq4Proof) : Sequent :=
  match s with
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁  atoms₂ forms₂ imps₂ _ =>
    have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁ ++ usedImps₁)
    have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂ ++ imps₂)  -- usedImps₂ is to monitor R→ usage, not to display
    Sequent.seq ant succ

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


--eligibility to be principle rules based on metarules
@[grind,simp]
def countPrinciple (toCheck: List Form) (nonusable: List Form): List Form :=
match toCheck with
  | [] => []
  | x :: xs => if x ∈ nonusable then countPrinciple xs nonusable
               else x :: countPrinciple xs nonusable


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

lemma atoms_inj: Function.Injective Form.atoms := by
  intro a b h
  cases h
  rfl

lemma erase_multiset_append
    {l : List Atom} (ctx : List Form) {x : Atom} (hx : x ∈ l) :
    Multiset.ofList (List.map Form.atoms (l.erase x) ++ Form.atoms x :: ctx) =
    Multiset.ofList (List.map Form.atoms l ++ ctx) := by
  rw [Multiset.coe_eq_coe,  ← List.singleton_append, ← List.append_assoc, List.perm_append_right_iff ctx]

  have base : l.Perm (x :: l.erase x) := by simp [List.perm_cons_erase hx]
  rw [← List.map_perm_map_iff atoms_inj] at base
  simp only [List.map_cons] at base
  have something:= List.perm_append_singleton (Form.atoms x) (List.map Form.atoms (l.erase x))
  rw [List.perm_comm]
  rw [List.perm_comm] at something
  exact (List.Perm.trans base something )


/- current: findIntersection returns just intersection, wo. duplicates.  -/

def findAtomicProofs (xs: List Atom)  (as : List Atom)
                    (imps₁ : List Form) (usedImps₁ : List Form)
                    (bs : List Atom) (imps₂ : List Form) (usedImps₂ : List Form)
                    (hxs : ∀ x ∈ xs, x ∈ (findIntersection as bs) )
                    : List (Proof (seqAtoms2seq (.seq4 as [] imps₁ usedImps₁ bs [] imps₂ usedImps₂))) :=
  have fin_corr := findIntersCorr as bs
  match xs with
  | [] => []
  | x :: xs' => by
    -- remove intersection atom x from atomic lists, as in rule
    have proof := ax (.atoms x) (List.map .atoms (as.erase x)) (imps₁ ++ usedImps₁) (List.map .atoms (bs.erase x)) imps₂
    simp

    have h : x ∈ (findIntersection as bs) := by simp [hxs]

    have corr_as : x ∈ as := (fin_corr x h).1
    have Γ₁ :
        Multiset.ofList (List.map .atoms (as.erase x) ++ .atoms x :: (imps₁ ++ usedImps₁)) =
        Multiset.ofList (List.map .atoms as ++ (imps₁ ++ usedImps₁)) :=
        erase_multiset_append (imps₁ ++ usedImps₁)  corr_as

    have corr_bs : x ∈ bs := (fin_corr x h).2
    have Γ₂ : Multiset.ofList (List.map Form.atoms (bs.erase x) ++ Form.atoms x :: imps₂) =
               Multiset.ofList (List.map Form.atoms bs ++ imps₂) := by
              have := erase_multiset_append imps₂ corr_bs
              simp only [List.append_nil] at this; exact this

    rw [Γ₁, Γ₂] at proof
    have new_hxs : ∀ x ∈ xs', x ∈ findIntersection as bs := by
      intro y hy
      apply hxs
      exact List.mem_cons_of_mem x hy

    have rest := findAtomicProofs xs' as imps₁ usedImps₁ bs imps₂ usedImps₂ new_hxs
    simp at rest
    exact (proof :: rest)



lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl

/- METARULES
1. formula x can be principal of R→ (impr) only once
   - so whenever we apply R→ rule, we place it to the succedent used imp list

2. a fortiori can be applied to formula x only when it has been analyzed by R→ rule
   - from succ forms list we  take a form and check if it is present in succ used imps list, then can use a fortiori,

3. between two occurrences of L→ , there is an occurrence of R→ (on any form) in between
   - so when applying L→ , we place the copy of form to usedImp list on the left
     and continue until all forms and imps have been looked at. When encountering R→ , we move all imps from Used list back to imp list

4. -our own- kõik mittepööratavad reeglid tuleb panna kõrvale ja jõuda pööratavate reeglite kasutusel kas aksioomini
   või küllastunud sekventsini, alles siis vaadata mittepööratavaid reegleid. So left side imps go straight to imps₁
 -/

def automatedProof (s : Seq4Proof) (cap : ℕ ) (hcap : s.cap.card ≤ cap := by simp at *; grind ) /- (hc : s.r ≤ cap := by grind) -/: List (Proof (seqAtoms2seq s)) :=
  match s with
  | .seq4 as forms₁ imps₁ usedImps₁  bs forms₂ imps₂ usedImps₂ =>
    match forms₁ with
    | [] =>
      --open up forms on right side
      match forms₂ with
      | [] => -- succedent only has atoms left --
        match common : findIntersection as bs with
        -- no common atoms
        | [] =>
          -- we are left with left imp lists (right usedImps₂ is for monitoring when we've used R→ )
          match imps₁ with
          | [] =>
            match imps₂ with
            | [] => []
            | (.imp a b) :: imps₂'  => by --METARULE 1
              if (.imp a b) ∉ usedImps₂ then-- use this info
               -- have needed :
                have h₁ := automatedProof (.seq4 as [a] ( usedImps₁) [] [] [b] [] ((a ⊃ b)::usedImps₂)) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) --move all usedimps back. TERMINATION PROBLEM
                simp at h₁
                have h₂ := List.map (impr a b (as.map .atoms) ( usedImps₁) (bs.map .atoms) imps₂') h₁
                unfold seqAtoms2seq; simp
                exact h₂
              else -- HERE can try a fortiori METARULE 2
                have h₁ := automatedProof (.seq4 as [] [] usedImps₁ bs  [b]  imps₂' usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
                simp at h₁
                have h₂ := List.map (afort a b ((as.map .atoms) ++ usedImps₁) (bs.map .atoms) imps₂') h₁
                unfold seqAtoms2seq; simp only [List.append_nil]
                exact h₂
            | _ => []
          | (.imp a b) :: imps₁' => by
            have pair₁ := automatedProof (.seq4 as [] imps₁' ((a ⊃ b) :: usedImps₁) bs [a] imps₂ usedImps₂ ) cap -- every implicative formula can be principal form of R→ only once!!
            have pair₂ := automatedProof (.seq4 as [b] imps₁' (usedImps₁) bs [] imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
            simp at pair₁; simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂;
            have hΓ :  Multiset.ofList (List.map Form.atoms as ++ (imps₁' ++ a.imp b :: usedImps₁)) =
              Multiset.ofList (List.map .atoms as ++ a.imp b :: (imps₁' ++ usedImps₁)) := by
              simp only [ Multiset.coe_eq_coe]
              rw [ List.perm_append_left_iff, List.append_cons]
              simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]

            rw [ hΓ] at pair₁
            have h := List.map (impl a b (as.map .atoms) (imps₁' ++ usedImps₁) (bs.map .atoms) imps₂).uncurry (getPairs pair₁ pair₂)
            simp at h; simp; clear hΓ
            exact h

          | _ :: xs => []
        -- atomic proofs exist
        | xs => by

          have Γ :  ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]

          exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (usedImps₂) (Γ)
          --exact findAtomicProofs' (x::xs) as (imps₁) (usedImps₁) bs (imps₂) (common)

      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) succForms imps₂ usedImps₂) cap
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | ⊥ :: succForms =>  by --botr rule, .bot is ignored
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs succForms imps₂ usedImps₂) cap
        simp at h; rw [← List.append_assoc] at h
        have rule := List.map (botr ((as.map .atoms)++imps₁++usedImps₁) (bs.map .atoms) (succForms ++ imps₂)) h
        unfold seqAtoms2seq; simp
        simp at rule
        exact rule

      | (.and a b) :: succForms => by
        have pair1 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (a :: succForms) imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind [Finset.union_comm, Finset.union_assoc] )
        have pair2 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (b :: succForms) imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind [Finset.union_comm, Finset.union_assoc] )
        unfold seqAtoms2seq at pair1; simp at pair1; rw [← List.append_assoc] at pair1
        unfold seqAtoms2seq at pair2; simp at pair2; rw [← List.append_assoc] at pair2
        have h := List.map (andr a b ((as.map .atoms)++ imps₁ ++ usedImps₁) (bs.map .atoms) (succForms++imps₂)).uncurry (getPairs pair1 pair2)
        unfold seqAtoms2seq; simp
        simp at h
        exact h
      | (.or a b) :: succForms => by
        have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs  (a :: b :: succForms) imps₂ usedImps₂) cap
        simp at h₁; rw [← List.singleton_append, ← List.append_assoc, ← List.append_assoc] at h₁
        have h₂ := List.map (orr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) [] (succForms++imps₂)) h₁
        simp; simp [List.append_assoc] at h₂
        exact h₂
      | (.imp a b) :: succForms => by --METARULE 4 move to imps list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs succForms ((.imp a b)::imps₂) usedImps₂ ) cap
        simp at h; simp
        have hΓ : Multiset.ofList (List.map Form.atoms bs ++ (succForms ++ a.imp b :: imps₂)) =
                  Multiset.ofList (List.map Form.atoms bs ++ a.imp b :: (succForms ++ imps₂)) := by
                  simp only [ Multiset.coe_eq_coe]
                  rw [ List.perm_append_left_iff, List.append_cons]
                  simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]
        simp [hΓ] at h; exact h


    -- open up forms on left side --
    | (.atoms a) :: antForms => by
      have h := automatedProof (.seq4 (as ++ [a]) antForms imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap
      simp at h; simp; exact h
    | .bot :: antForms => by
      have h:= [botl (as.map .atoms) (antForms++imps₁++usedImps₁) ((bs.map .atoms)++forms₂++imps₂)]
      simp only [List.append_assoc] at h
      simp
      exact h
    | (.and a b) :: antForms => by
      have h₁ := automatedProof (.seq4 as (a::b::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at h₁
      rw [← List.append_assoc antForms imps₁ usedImps₁] at h₁; rw [← List.append_assoc] at h₁
      have h₂ := List.map (andl a b ((as.map .atoms)) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂++imps₂)) h₁
      unfold seqAtoms2seq
      simp only [← List.cons_append, ← List.append_assoc] at h₂
      exact h₂
    | (.or a b) :: antForms => by
      have pair₁ := automatedProof (.seq4 as (a::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have pair₂ := automatedProof (.seq4 as (b::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      simp at pair₁; rw [← List.append_assoc antForms imps₁ usedImps₁, ← List.append_assoc] at pair₁
      simp at pair₂; rw [← List.append_assoc antForms imps₁ usedImps₁, ← List.append_assoc] at pair₂
      have h := List.map (orl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂++ imps₂)).uncurry (getPairs pair₁ pair₂)
      simp only [← List.cons_append, ← List.append_assoc] at h
      exact h
    | (.imp a b) :: antForms => by -- METARULE 4, move to imps, dont apply rule yet
      have h := automatedProof (.seq4 as antForms ((.imp a b)::imps₁) usedImps₁ bs forms₂ imps₂ usedImps₂) cap
      simp at h; simp
      have hΓ : Multiset.ofList (List.map Form.atoms as ++ (antForms ++ a.imp b :: (imps₁ ++ usedImps₁))) =
                Multiset.ofList (List.map Form.atoms as ++ a.imp b :: (antForms ++ (imps₁ ++ usedImps₁))) := by
                simp only [ Multiset.coe_eq_coe]
                rw [ List.perm_append_left_iff, List.append_cons]
                simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]
      simp [hΓ] at h; exact h

termination_by s.weight cap hcap
decreasing_by
all_goals simp [Seq4Proof.weight]; try grind
. grind [List.mem_toFinset]


---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString | .mk 1 => "p" | .mk 2 => "q" | .mk 3 => "r" | .mk _ => "undefined"

def formToString : Form → String
  | .bot => "⊥"
  | .atoms a => toString a
  | .neg a => s!"¬{formToString a}"
  | .and a b => s!"({formToString a} ∧ {formToString b})"
  | .or a b => "(" ++ formToString a ++ " ∨ " ++ formToString b ++ ")"
  | .imp a b => "(" ++ formToString a ++ " ⊃ " ++ formToString b ++ ")"

instance : ToString Form := ⟨formToString⟩

/-
  Ordering formulas is more tricky since we are dealing with tree-like structures
  We encode them into lists of nats (question: can we use `Nat` as encoding? Why or why not?)
-/
@[simp]
def Form.encode : Form → List Nat
  | bot        => [0]
  | atoms a    => [1, a.atom]
  | and f g    => [2, (encode f).length] ++ encode f ++ encode g
  | or f g     => [3, (encode f).length] ++ encode f ++ encode g
  | imp f g    => [4, (encode f).length] ++ encode f ++ encode g

lemma Atom.ext {a b : Atom} (h : a.atom = b.atom) : a = b := by
  cases a; cases b
  simp_all

theorem form_inj {f : Form} (h : f.encode = g.encode) :
  f = g := by
  match f, g with
  | .bot, .bot => rfl
  | .bot, .atoms _ => simp only [Form.encode, List.cons.injEq, zero_ne_one, List.ne_cons_self, and_self] at h
  | .atoms _, .bot => simp at h
  | .atoms a, .atoms b =>
    simp only [Form.encode, Atom.mk, List.cons.injEq, and_true, true_and] at h
    apply congrArg Form.atoms (Atom.ext h)
  | .and f g, .and f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .or f g, .or f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .imp f g, .imp f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩

/-
  We can give a canonical ordering to `Form`s using our encodings
  Note that there is already an instance of `LinearOrder (List α)` in the library
  Our definition of ordering is this: `f ≤ g ↔ Form.encode f ≤ Form.encode g`
-/

instance : LinearOrder Form :=
  LinearOrder.lift' Form.encode (fun _ _ h => form_inj h)

/- `LinearOrder Nat` is already defined in the library
   But `Form` is our own type, so we need to give it one
   Since `Form` is made up of `Atom` and `Form`, we need to take into account both
-/
def example1 : Multiset Nat := {3, 1, 2, 2}
def example2 : Multiset Form := {.atoms ( Atom.mk 1), .bot, .bot}

/-
   We can turn multisets into (computable) sorted lists with `sort`
   But `sort` needs a relation with respect to which it will sort the elements on the multiset

   Why?
   For example, given `{0, 1, 0}`, should we print it as `[0, 0, 1]` or `[0, 1, 0]`?
   We need some canonical order to decide this so in our case, we can use `≤` for sorting
-/

#eval Multiset.sort example1 LE.le
#eval Multiset.sort example2 LE.le

instance : ToString Sequent where
  toString xseq :=
  match xseq with
  | .seq Γ Δ => String.intercalate ", " (List.map formToString (Multiset.sort Γ LE.le ))
    ++ " ⊢ " ++ String.intercalate ", " (List.map formToString (Multiset.sort Δ LE.le ))

instance : ToString Seq4Proof where
  toString seq4 :=
  match seq4 with
  | .seq4 as forms₁ imps₁ usedImps₁  bs forms₂ imps₂ usedImps₂=>
  (List.map toString as).toString ++ (List.map formToString forms₁).toString ++ (List.map formToString imps₁).toString
  ++ "⊢" ++ (List.map toString bs).toString  ++ (List.map formToString forms₂).toString

def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => (String.join (List.replicate n "  "))++ line))

def horizontalLine (n : Nat) : String :=
  String.join (List.replicate n "-")

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map formToString)

def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax x xs ys gs zs  =>
  indent indentLvl s!"AX: {formToString x}, {listToString xs}, {listToString ys} ⊢ {formToString x}, {listToString gs}, {listToString zs} "
| .botl xs ys gs =>
  indent indentLvl s!"⊥L: ⊥, {listToString xs}, {listToString ys} ⊢ {listToString gs}"
| .botr xs ys gs proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {listToString xs} ⊢ ⊥, {listToString ys}, {listToString gs}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl a b xs ys gs proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: ({formToString a} ∧ {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs ys gs proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}, {listToString ys}, {listToString gs}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b xs ys gs proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({formToString a} ∨ {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr a b xs ys zs gs proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊢ {formToString a} ∨ {formToString b}, {listToString ys}, {listToString zs}, {listToString gs}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl a b xs ys gs zs proof₁ proof₂ =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L: ({formToString a} → {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}, {listToString zs}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys gs zs proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs}, {listToString ys} ⊢ {formToString a} → {formToString b}, {listToString gs}, {listToString zs}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort a b xs ys gs proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→a fortiori: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}, {listToString gs}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"


def listProofToString : List (Proof xseq) → String
| [] => ""
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs


instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof


def seq2seq4 : Sequent → Seq4Proof
| .seq Δ Γ =>
  have antecedent := Multiset.sort Δ LE.le
  have succedent := Multiset.sort Γ LE.le
  Seq4Proof.seq4 [] antecedent [] [] [] succedent [] []


def automatedProofHelper (s : Sequent) : Std.Format :=
  have seq4 := seq2seq4 s
  have proofs := automatedProof (seq2seq4 s)  (seq2seq4 s).cap.card (by simp)--stupid, no? it couldn't refer the h automatically when given seq4 instead of (seq2seq4 s)
  String.toFormat (listProofToString proofs)


--modusponens "a → b, a ⊢ β"
#eval automatedProofHelper (seq {(p → q), p ⊢ q})
#eval automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval automatedProofHelper (seq {p ⊢ (q ∨ p)})

#eval automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))})

#eval automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})
#eval automatedProofHelper (seq {(p → r), (q → ¬r) ⊢ ¬(p ∧ q)})
--from corsi tassi article
#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})

#print axioms automatedProofHelper
end multiSucc
