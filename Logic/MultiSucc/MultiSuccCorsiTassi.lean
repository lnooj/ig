import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort

import Logic.MultiSucc.Core
import Logic.MultiSucc.Syntax

namespace multiSucc
open multiSucc

/-
Atomic values get valued as one , not as 0, to help show termination for the atomic case in antecedent.
Bottom is valued as 0, for it is semantically different from all others and does not "add complexity" to our sequent
 -/
@[simp]
def sizeOf_Form : Form → Nat
  | ⊥ => 0
  | .atoms _ => 1
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q


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
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁  atoms₂ forms₂ imps₂ usedImps₂=>
    have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁ ++ usedImps₁)
    have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂ ++ imps₂)  -- usedImps₂ is to monitor R→ usage, not to display
    Sequent.seq ant succ


def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => sizeOf_Form f + size_sum fs

@[simp]
def termination_metric (s : Seq4Proof) : Nat  :=
match s with
  | .seq4 atoms₁ [] imps₁ usedImps₁ atoms₂ [] imps₂ usedImps₂ =>

    (size_sum imps₁ + size_sum imps₂)
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁ atoms₂ forms₂ imps₂ usedImps₂  => ( size_sum forms₁ + size_sum forms₂) --TODO what to do with imps₂??


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

--TODO when findIntersection empty, no overlapping atoms in either lists

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
   - so whenever we apply R→ rule, we place it to the succedent imp list
2. a fortiori can be applied to formula x only when it has been analyzed by R→ rule
   - from succ forms list we  take a form and check if it is present in succ imps list, then can use a fortiori,

3. between two occurrences of L→ , there is an occurrence of R→ (on any form) in between
   - so when applying L→ , we place the copy of form to usedImp list on the left
     and continue until all forms and imps have been looked at. When encountering R→ , we move all imps from Used list back to imp list

4. -our own- kõik mittepööratavad reeglid tuleb panna kõrvale ja jõuda pööratavate reeglite kasutusel kas aksioomini
   või küllastunud sekventsini, alles siis vaadata mittepööratavaid reegleid. So left side imps go straight to imps₁
 -/

partial def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
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
            | (.imp a b) :: imps /- | (.neg a) :: succForms -/ => by --METARULE 1
              if (.imp a b) ∉ usedImps₂ then
                have h₁ := automatedProof (.seq4 as [a] ( usedImps₁) [] [] [b] [] ((a ⊃ b)::usedImps₂) ) --move all usedimps back. TERMINATION PROBLEM
                simp at h₁
                have h₂ := List.map (impr a b (as.map .atoms) ( usedImps₁) (bs.map .atoms) imps) h₁
                unfold seqAtoms2seq; simp
                exact h₂
              else -- HERE can try a fortiori METARULE 2
                have h₁ := automatedProof (.seq4 as [] [] usedImps₁ bs  [b]  imps usedImps₂)
                simp at h₁
                have h₂ := List.map (afort a b ((as.map .atoms) ++ usedImps₁) (bs.map .atoms) imps) h₁
                unfold seqAtoms2seq; simp only [List.append_nil]
                exact h₂
            | _ => []
          | (.imp a b) :: xs => by
            have pair₁ := automatedProof (.seq4 as [] xs ((a ⊃ b) :: usedImps₁) bs [a] imps₂ usedImps₂ )
            have pair₂ := automatedProof (.seq4 as [b] xs (/- (.imp a b) :: -/ usedImps₁) bs [] imps₂ usedImps₂) -- by rule i cant keep copy of .imp a b in usedImps₁, do i need to?
            simp at pair₁; simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂; --rw [← List.append_assoc [] imps₁ usedImps₁] at pair₂
            have hΓ :  Multiset.ofList (List.map Form.atoms as ++ (xs ++ a.imp b :: usedImps₁)) =
              Multiset.ofList (List.map .atoms as ++ a.imp b :: (xs ++ usedImps₁)) := by
              simp only [ Multiset.coe_eq_coe]
              rw [ List.perm_append_left_iff, List.append_cons]
              simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]

            rw [ hΓ] at pair₁
            have h := List.map (impl a b (as.map .atoms) (xs ++ usedImps₁) (bs.map .atoms) imps₂).uncurry (getPairs pair₁ pair₂)
            simp at h; simp; clear hΓ
            exact h

          | _ :: xs => []
        -- atomic proofs exist
        | xs => by

          have Γ :  ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]

          exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (usedImps₂) (Γ)
          --exact findAtomicProofs' (x::xs) as (imps₁) (usedImps₁) bs (imps₂) (common)

      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) succForms imps₂ usedImps₂)
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | ⊥ :: succForms =>  by --botr rule, .bot is ignored
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs succForms imps₂ usedImps₂)
        simp at h; rw [← List.append_assoc] at h
        have rule := List.map (botr ((as.map .atoms)++imps₁++usedImps₁) (bs.map .atoms) (succForms ++ imps₂)) h
        unfold seqAtoms2seq; simp
        simp at rule
        exact rule

      | (.and a b) :: succForms => by
        have pair1 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (a :: succForms) imps₂ usedImps₂)
        have pair2 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (b :: succForms) imps₂ usedImps₂)
        unfold seqAtoms2seq at pair1; simp at pair1; rw [← List.append_assoc] at pair1
        unfold seqAtoms2seq at pair2; simp at pair2; rw [← List.append_assoc] at pair2
        have h := List.map (andr a b ((as.map .atoms)++ imps₁ ++ usedImps₁) (bs.map .atoms) (succForms++imps₂)).uncurry (getPairs pair1 pair2)
        unfold seqAtoms2seq; simp
        simp at h
        exact h
      | (.or a b) :: succForms => by
        have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs  (a :: b :: succForms) imps₂ usedImps₂)
        simp at h₁; rw [← List.singleton_append, ← List.append_assoc, ← List.append_assoc] at h₁
        have h₂ := List.map (orr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) [] (succForms++imps₂)) h₁
        simp; simp [List.append_assoc] at h₂
        exact h₂
      | (.imp a b) :: succForms => by --METARULE 4 move to imps list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs succForms ((.imp a b)::imps₂) usedImps₂ )
        simp at h; simp
        have hΓ : Multiset.ofList (List.map Form.atoms bs ++ (succForms ++ a.imp b :: imps₂)) =
                  Multiset.ofList (List.map Form.atoms bs ++ a.imp b :: (succForms ++ imps₂)) := by
                  simp only [ Multiset.coe_eq_coe]
                  rw [ List.perm_append_left_iff, List.append_cons]
                  simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]
        simp [hΓ] at h; exact h


    -- open up forms on left side --
    | (.atoms a) :: antForms => by
      have h := automatedProof (.seq4 (as ++ [a]) antForms imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂)
      simp at h; simp; exact h
    | .bot :: antForms => by
      have h:= [botl (as.map .atoms) (antForms++imps₁++usedImps₁) ((bs.map .atoms)++forms₂++imps₂)]
      simp only [List.append_assoc] at h
      simp
      exact h
    | (.and a b) :: antForms => by
      have h₁ := automatedProof (.seq4 as (a::b::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂)
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at h₁
      rw [← List.append_assoc antForms imps₁ usedImps₁] at h₁; rw [← List.append_assoc] at h₁
      have h₂ := List.map (andl a b ((as.map .atoms)) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂++imps₂)) h₁
      unfold seqAtoms2seq; simp only [List.append_nil]
      simp only [← List.cons_append, ← List.append_assoc] at h₂
      exact h₂
    | (.or a b) :: antForms => by
      have pair₁ := automatedProof (.seq4 as (a::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂)
      have pair₂ := automatedProof (.seq4 as (b::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂)
      simp at pair₁; rw [← List.append_assoc antForms imps₁ usedImps₁, ← List.append_assoc] at pair₁
      simp at pair₂; rw [← List.append_assoc antForms imps₁ usedImps₁, ← List.append_assoc] at pair₂
      have h := List.map (orl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂++ imps₂)).uncurry (getPairs pair₁ pair₂)
      simp only [← List.cons_append, ← List.append_assoc] at h
      exact h
    | (.imp a b) :: antForms => by -- METARULE 4, move to imps, dont apply rule yet
      have h := automatedProof (.seq4 as antForms ((.imp a b)::imps₁) usedImps₁ bs forms₂ imps₂ usedImps₂)
      simp at h; simp
      have hΓ : Multiset.ofList (List.map Form.atoms as ++ (antForms ++ a.imp b :: (imps₁ ++ usedImps₁))) =
                Multiset.ofList (List.map Form.atoms as ++ a.imp b :: (antForms ++ (imps₁ ++ usedImps₁))) := by
                simp only [ Multiset.coe_eq_coe]
                rw [ List.perm_append_left_iff, List.append_cons]
                simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]
      simp [hΓ] at h; exact h

termination_by (termination_metric s)
decreasing_by
. simp; simp only [size_sum]; simp; grind
. simp; apply Prod.Lex.left; simp only [size_sum]; simp
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
. simp; sorry
. simp; simp only [size_sum]; simp; grind
  have h : ¬(succForms = []) := by sorry
  -- prove this from context


. simp; simp only [size_sum]; simp
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
  rw [add_assoc, add_assoc, add_comm 1 _]
  apply Nat.lt_succ_self
. simp; simp only [size_sum]; simp-- difficult case, would work if first members could be a₁ ≠ a₂ then b₁ < b₂
/-   have h : size_sum (imps₁ ++ usedImps₁) = size_sum imps₁ + size_sum usedImps₁ :=
    by induction imps₁ with
    | nil => simp [size_sum]
    | cons x xs ih => simp [size_sum, ih]; rw [← Nat.add_assoc] -/
  sorry
  /- apply Prod.Lex.right; rw [add_assoc 1 _ _, add_comm 1 _]
  refine Nat.lt_add_right (size_sum succForms) ?_
  apply Nat.lt_succ_self
   -/
. simp; simp only [size_sum]; simp
. simp; --moving the .imp just to different list, how to show termination?
. simp; simp only [size_sum]; simp;
  rw [add_assoc, add_assoc ,add_comm 1 _]; apply Nat.lt_succ_self
. simp; apply Prod.Lex.right; simp only [size_sum]; simp; rw [add_comm 1 _]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. apply Prod.Lex.right; simp only [size_sum]; simp
. apply Prod.Lex.right; simp only [size_sum]; simp
  rw [add_assoc, add_comm _ (size_sum succForms + size_sum forms₂), add_comm _ (sizeOf_Form a), add_comm (sizeOf_Form a) _]
  simp only [← add_assoc]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. apply Prod.Lex.right; simp only [size_sum]; simp


---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString a :=
    match a with
    | .mk 1 => "p"
    | .mk 2 => "q"
    | .mk 3 => "r"
    | .mk _ => "undefined"

def formToString (xform : Form) : String :=
   match xform with
    | .bot => "⊥"
    | .atoms a => toString a
    | .neg a => "¬" ++ formToString a
    | .and a b => "(" ++ formToString a ++ " ∧ " ++ formToString b ++ ")"
    | .or a b => "(" ++ formToString a ++ " ∨ " ++ formToString b ++ ")"
    | .imp a b => "(" ++ formToString a ++ " ⊃ " ++ formToString b ++ ")"

instance : ToString Form where
  toString xform := formToString xform


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

#eval Multiset.sort LE.le example1
#eval Multiset.sort LE.le example2

instance : ToString Sequent where
  toString xseq :=
  match xseq with
  | .seq Γ Δ => String.intercalate ", " (List.map formToString (Multiset.sort LE.le Γ))
    ++ " ⊢ " ++ String.intercalate ", " (List.map formToString (Multiset.sort LE.le Δ))

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
  have antecedent := Multiset.sort LE.le Δ
  have succedent := Multiset.sort LE.le Γ
  Seq4Proof.seq4 [] antecedent [] [] [] succedent [] []


def automatedProofHelper (s : Sequent) : Std.Format :=
  have seq4 := seq2seq4 s
  have proofs := automatedProof seq4
  String.toFormat (listProofToString proofs)


--modusponens "a → b, a ⊢ β"
#eval automatedProofHelper (seq {(p → q), p ⊢ q})
#eval automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q}) --Works, so negation works
#eval automatedProofHelper (seq {p ⊢ (q ∨ p)})

#eval automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))})

#eval automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})
#eval automatedProofHelper (seq {(p → r), (q → ¬r) ⊢ ¬(p ∧ q)})
--from corsi tassi article
#eval automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})

end multiSucc
