import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort

namespace multiSucc

inductive Atom
  | atom₁ : Atom | atom₂ : Atom | atom₃ : Atom
deriving DecidableEq, Repr
open Atom

/-
  We need a way to order `Atom`s so we assign each constructor a unique number
  So our canonical order is `atom₁ ≤ atom₂ ≤ atom₃`
-/
def Atom.toNat : Atom → Nat
  | atom₁ => 0
  | atom₂ => 1
  | atom₃ => 2

  -- as an exercise you can prove this
theorem atom_inj {a : Atom} (h : a.toNat = b.toNat) : a = b := by
  --unfold Atom.toNat at h
  cases a
  <;>  cases b -- <;> applies tactic on all subgoals
  <;> simp [Atom.toNat] at h
  <;> rfl

inductive Form
  | bot : Form
  | atoms : Atom → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
deriving DecidableEq, Repr
open Form

/- Defining negation as → ⊥  from the getgo-/
def Form.neg (a : Form) : Form :=
  Form.imp a Form.bot

/-
Atomic values get valued as one , not as 0, to help show termination for the atomic case in antecedent.
Bottom is valued as 0, for it is semantically different from all others and does not "add complexity" to our sequent
 -/
@[simp]
def sizeOf_Form : Form → Nat
  | .bot => 0
  | .atoms _ => 1
  | .and p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .or p q => 1 + sizeOf_Form p + sizeOf_Form q
  | .imp p q => 1 + sizeOf_Form p + sizeOf_Form q


/- Using Multisets to not worry about order of forms -/
-- [f1, f2] ⊢ [g1, g2]
inductive Sequent
  | seq : Multiset Form → Multiset Form → Sequent
--deriving Repr

/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.

 -/
-- [x, y], [f1, f2], usable[imp1, imp2], nonusable[imp1, imp2] ⊢ [x, y], [g1, g2], [imp1, imp2]
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → List Form  → List Atom → List Form → List Form → Seq4Proof
--deriving Repr

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
      Proof (.seq ↑(xs ++ .bot :: ys) ↑gs)
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq ↑(xs ++ a :: b :: ys) ↑gs) →
      Proof (.seq ↑(xs ++ (.and a b) :: ys) ↑gs)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq ↑xs ↑(ys ++ a::gs)) →
      Proof (.seq ↑xs ↑(ys ++ b::gs)) →
      Proof (.seq ↑xs ↑(ys ++ (.and a b)::gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys gs : List Form),
    Proof (.seq ↑(xs ++ a :: ys) ↑gs) →
    Proof (.seq ↑(xs ++ b :: ys) ↑gs) →
    Proof (.seq ↑(xs ++ (.or a b) :: ys) ↑gs)
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys gs: List Form),
      Proof (.seq ↑xs ↑(ys ++ a :: b :: gs)) →   --TODO: a ja b järjekord ei tohiks oleneda
      Proof (.seq ↑xs ↑(ys ++ (.or a b) :: gs))
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq ↑(xs ++ a :: ys) {b}) →
      Proof (.seq ↑(xs ++ ys) ↑(gs ++ (.imp a b)::zs)) --succ järjestus
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys gs zs: List Form),
      Proof (.seq ↑(xs ++ (.imp a b) :: ys) ↑(gs ++ a :: zs)) →
      Proof (.seq ↑(xs ++ b :: ys ) ↑(gs++zs)) →
      Proof (.seq ↑(xs ++ (.imp a b) :: ys) ↑(gs++zs))
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys gs : List Form),
      Proof (.seq ↑xs ↑(ys ++ b :: gs)) →
      Proof (.seq ↑xs ↑(ys ++ (.imp a b) :: gs))

--deriving Repr
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
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁  atoms₂ forms₂ imps₂ =>
    have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁ ++ usedImps₁)
    have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂)  -- imps₂ is to monitor R→ usage, not to display
    Sequent.seq ant succ

--TODOD: seq2seqAtoms for proofHelper

def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => sizeOf_Form f + size_sum fs

@[simp]
def termination_metric (s : Seq4Proof) : Nat × Nat:=
match s with
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁ atoms₂ forms₂ imps₂  => ( size_sum imps₁ , size_sum forms₁ + size_sum forms₂)


/- find common atoms in anticident atoms list and succedent atoms list. current: wo duplicates
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

#eval findIntersection [atom₁] [atom₁, atom₂, atom₁]

theorem findIntersCorr (xs : List Atom) (ys : List Atom) :
  ∀ atom ∈ (findIntersection xs ys), atom ∈ xs ∧ atom ∈ ys :=
  λ atom atom_in =>
  match ys with
  | [] => by simp [findIntersection] at atom_in
  | y' :: ys' => by
    unfold findIntersection at atom_in
    by_cases cond₁: y' ∈ xs
    . simp [cond₁] at atom_in
      by_cases cond₂: y' ∈ findIntersection xs ys'
      . simp [cond₂] at atom_in
        have ih := findIntersCorr xs ys'
        have ⟨h₁, h₂⟩ := ih atom atom_in
        exact ⟨h₁, List.Mem.tail _ h₂⟩
      . simp [cond₂] at atom_in
        match atom_in with
        | Or.inl left =>
          simp [left] at atom_in
          subst left
          exact ⟨ cond₁, List.mem_cons_self⟩
        | Or.inr right =>
          have ih := findIntersCorr xs ys'
          have ⟨h₁, h₂⟩ := ih atom right
          exact ⟨h₁, List.mem_cons_of_mem _ h₂ ⟩
    . simp [cond₁] at atom_in
      have ih := findIntersCorr xs ys'
      have ⟨h₁, h₂⟩ := ih atom atom_in
      exact ⟨h₁, List.Mem.tail _ h₂⟩

lemma atoms_inj : Function.Injective atoms := by
  intro a b h
  cases h
  rfl

lemma erase_multiset_append
    {l : List Atom} (ctx : List Form) {x : Atom} (hx : x ∈ l) :
    Multiset.ofList (List.map atoms (l.erase x) ++ atoms x :: ctx) =
    Multiset.ofList (List.map atoms l ++ ctx) := by
  rw [Multiset.coe_eq_coe,  ← List.singleton_append, ← List.append_assoc, List.perm_append_right_iff ctx]

  have base : l.Perm (x :: l.erase x) := by simp [List.perm_cons_erase hx]
  rw [← List.map_perm_map_iff atoms_inj] at base
  simp only [List.map_cons] at base
  have something:= List.perm_append_singleton (atoms x) (List.map atoms (l.erase x))
  rw [List.perm_comm]
  rw [List.perm_comm] at something
  exact (List.Perm.trans base something )



/- current: findIntersection returns just intersection, wo. duplicates.  -/

def findAtomicProofs (xs: List Atom)  (as : List Atom)
                    (imps₁ : List Form) (usedImps₁ : List Form)
                    (bs : List Atom) (imps₂ : List Form)
                    (hxs : ∀ x ∈ xs, x ∈ (findIntersection as bs) )
                    : List (Proof (seqAtoms2seq (.seq4 as [] imps₁ usedImps₁ bs [] imps₂))) :=
  have fin_corr := findIntersCorr as bs
  match xs with
  | [] => []
  | x :: xs' => by
    -- remove intersection atom x from atomic lists, as in rule
    have proof := ax (.atoms x) (List.map .atoms (as.erase x)) (imps₁ ++ usedImps₁) (List.map atoms (bs.erase x)) []
    --have proof := ax (.atoms x) (List.map .atoms as) (imps₁ ++ usedImps₁) (List.map atoms bs) []
    simp

    have h : x ∈ (findIntersection as bs) := by simp [hxs]

    have corr_as : x ∈ as := (fin_corr x h).1
    have Γ₁ :
        Multiset.ofList (List.map atoms (as.erase x) ++ atoms x :: (imps₁ ++ usedImps₁)) =
        Multiset.ofList (List.map atoms as ++ (imps₁ ++ usedImps₁)) :=
        erase_multiset_append (imps₁ ++ usedImps₁)  corr_as

    have corr_bs : x ∈ bs := (fin_corr x h).2
    have Γ₂ : Multiset.ofList (List.map atoms (bs.erase x) ++ [atoms x]) =
               Multiset.ofList (List.map atoms bs) := by
              have := erase_multiset_append [] corr_bs
              simp only [List.append_nil] at this; exact this

    rw [Γ₁, Γ₂] at proof
    have new_hxs : ∀ x ∈ xs', x ∈ findIntersection as bs := by
      intro y hy
      apply hxs
      exact List.mem_cons_of_mem x hy

    have rest := findAtomicProofs xs' as imps₁ usedImps₁ bs imps₂ new_hxs
    simp at rest
    exact (proof :: rest)



lemma neg_eq_imp_bot (a : Form) :  .neg a = Form.imp a Form.bot := by rfl

/- METARULES
1. formula x can be principal of R→ (impr) only once
   - so whenever we apply R→ rule, we place it to the succedent imp list
2. a fortiori can be applied to formula x only when it has been analyzed by R→ rule
   - from succ forms list we  take a form and check if it is present in succ imps list, then can use a fortiori,

3. between two occurrences of L→ , there is an occurrence of R→ (on any form) in between
   - so when applying L→ , we place the copy of form to usedImp list on the left
     and continue until all forms and imps have been looked at. When encountering R→ , we move all imps from Used list back to imp list
 how to add SIC pop n push functionality
 -/

partial def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
  match s with
  | .seq4 as forms₁ imps₁ usedImps₁  bs forms₂ imps₂ =>
    match forms₁ with
    | [] =>
      --open up forms on right side
      match forms₂ with
      | [] => -- succedent only has atoms left --
        match common : findIntersection as bs with
        -- no common atoms
        | [] =>
          -- we are left with left imp list (right is for monitoring when we've used R→ )
          match imps₁ with
          | [] => []
          | (.imp a b) :: xs => by
            have pair₁ := automatedProof (.seq4 as [] xs ((.imp a b) :: usedImps₁) bs [a] imps₂ )
            have pair₂ := automatedProof (.seq4 as [b] xs (/- (.imp a b) :: -/ usedImps₁) bs [] imps₂) -- by rule i cant keep copy of .imp a b in usedImps₁, do i need to?
            simp at pair₁; simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂; --rw [← List.append_assoc [] imps₁ usedImps₁] at pair₂
            have hΓ :  Multiset.ofList (List.map atoms as ++ (xs ++ a.imp b :: usedImps₁)) =
              Multiset.ofList (List.map atoms as ++ a.imp b :: (xs ++ usedImps₁)) := by
              simp only [ Multiset.coe_eq_coe]
              rw [ List.perm_append_left_iff, List.append_cons]
              simp only [List.append_assoc,List.cons_append, List.nil_append, List.perm_middle]

            rw [ hΓ] at pair₁
            have h := List.map (impl a b (as.map .atoms) (xs ++ usedImps₁) (bs.map .atoms) []).uncurry (getPairs pair₁ pair₂)
            simp at h; simp; clear hΓ
            exact h

          | _ :: xs => []
        -- atomic proofs exist
        | xs => by

          have Γ :  ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]

          exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (Γ)
          --exact findAtomicProofs' (x::xs) as (imps₁) (usedImps₁) bs (imps₂) (common)

      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) succForms imps₂)
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | .bot :: succForms =>  by --RIGHT NOW JUST MOVED IT TO LAST???
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (succForms++ [.bot]) imps₂)
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        have Γ : Multiset.ofList (List.map atoms bs ++ (succForms ++ [bot])) =
                 Multiset.ofList (List.map atoms bs ++ bot :: succForms) := by
                 simp [Multiset.coe_eq_coe]; rw [List.perm_append_left_iff] ; apply List.perm_append_singleton

        rw [Γ] at h
        exact h

      | (.and a b) :: succForms => by
        have pair1 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (a :: succForms) imps₂)
        have pair2 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (b :: succForms) imps₂)
        unfold seqAtoms2seq at pair1; simp only [List.append_nil] at pair1
        unfold seqAtoms2seq at pair2; simp only [List.append_nil] at pair2
        have h := List.map (andr a b ((as.map .atoms)++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms).uncurry (getPairs pair1 pair2)
        unfold seqAtoms2seq; simp
        simp at h
        exact h
      | (.or a b) :: succForms => by
        have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs  (a :: b :: succForms) imps₂)--sus
        simp only [seqAtoms2seq, List.append_nil] at h₁
        have h₂ := List.map (orr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
        unfold seqAtoms2seq; simp only [List.append_nil]
        exact h₂
      | (.imp a b) :: succForms /- | (.neg a) :: succForms -/ => by --METARULE 1
        if (.imp a b) ∉ imps₂ then
          have h₁ := automatedProof (.seq4 as [a] (imps₁++usedImps₁) [] [] [b] ((.imp a b)::imps₂) ) --move all usedimps back. TERMINATION PROBLEM
          simp at h₁
          have h₂ := List.map (impr a b (as.map .atoms) (imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp
          exact h₂
        else -- HERE can try a fortiori METARULE 2
          have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (b :: succForms) imps₂)
          simp only [seqAtoms2seq, List.append_nil] at h₁
          have h₂ := List.map (afort a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms) succForms) h₁
          unfold seqAtoms2seq; simp only [List.append_nil]
          exact h₂

    -- open up forms on left side --
    | (.atoms a) :: antForms => by
      have h := automatedProof (.seq4 (as ++ [a]) antForms imps₁ usedImps₁ bs forms₂ imps₂)
      simp at h; simp; exact h
    | .bot :: antForms => by
      have h:= [botl (as.map .atoms) (antForms++imps₁++usedImps₁) ((bs.map .atoms)++forms₂)]
      simp only [List.append_assoc] at h
      simp
      exact h
    | (.and a b) :: antForms => by
      have h₁ := automatedProof (.seq4 as (a::b::antForms) imps₁ usedImps₁ bs forms₂ imps₂)
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at h₁
      rw [← List.append_assoc antForms imps₁ usedImps₁] at h₁
      have h₂ := List.map (andl a b ((as.map .atoms)) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂)) h₁
      unfold seqAtoms2seq; simp only [List.append_nil]
      simp only [← List.cons_append, ← List.append_assoc] at h₂
      exact h₂
    | (.or a b) :: antForms => by
      have pair₁ := automatedProof (.seq4 as (a::antForms) imps₁ usedImps₁ bs forms₂ imps₂)
      have pair₂ := automatedProof (.seq4 as (b::antForms) imps₁ usedImps₁ bs forms₂ imps₂)
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₁; rw [← List.append_assoc antForms imps₁ usedImps₁] at pair₁
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂; rw [← List.append_assoc antForms imps₁ usedImps₁] at pair₂
      have h := List.map (orl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂)).uncurry (getPairs pair₁ pair₂)
      simp only [← List.cons_append, ← List.append_assoc] at h
      exact h
    | (.imp a b) :: antForms => by -- METARULE 3
      have pair₁ := automatedProof (.seq4 as antForms imps₁ ((.imp a b):: usedImps₁) bs (a::forms₂) imps₂ )
      have pair₂ := automatedProof (.seq4 as (b :: antForms) imps₁ (/- (.imp a b) :: -/ usedImps₁) bs forms₂ imps₂) -- by rule i cant keep copy of .imp a b in usedImps₁, do i need to?
      simp at pair₁; simp only [seqAtoms2seq, List.append_assoc, List.cons_append] at pair₂; rw [← List.append_assoc antForms imps₁ usedImps₁] at pair₂
      have hΓ :  Multiset.ofList (List.map atoms as ++ (antForms ++ (imps₁ ++ a.imp b :: usedImps₁))) =
          Multiset.ofList (List.map atoms as ++ a.imp b :: (antForms ++ imps₁ ++ usedImps₁)) := by
          simp only [ Multiset.coe_eq_coe]; rw [List.perm_append_left_iff, ← List.append_assoc]; apply List.perm_middle
      rw [ hΓ] at pair₁
      have h := List.map (impl a b (as.map .atoms) (antForms++imps₁++ usedImps₁) (bs.map .atoms) (forms₂)).uncurry (getPairs pair₁ pair₂)
      simp at h; simp
      exact h
termination_by (termination_metric s)
decreasing_by
. simp; simp only [size_sum]; apply Prod.Lex.left; simp
. simp; apply Prod.Lex.left; simp only [size_sum]; simp
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
. sorry
. simp; apply Prod.Lex.right; simp only [size_sum]; simp; rw [add_comm 1 _];
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
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
. apply Prod.Lex.right; simp only [size_sum]; simp
. apply Prod.Lex.right; simp only [size_sum]; simp
. apply Prod.Lex.right; simp only [size_sum]; simp;
  rw [add_assoc, add_assoc ,add_comm 1 _]; apply Nat.lt_succ_self
. apply Prod.Lex.right; simp only [size_sum]; simp; rw [add_comm 1 _]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. apply Prod.Lex.right; simp only [size_sum]; simp
. apply Prod.Lex.right; simp only [size_sum]; simp
  rw [add_assoc, add_comm _ (size_sum succForms + size_sum forms₂), add_comm _ (sizeOf_Form a), add_comm (sizeOf_Form a) _]
  simp only [← add_assoc]
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. apply Prod.Lex.right; simp only [size_sum]; simp


/- TODO
def automatedProofHelper (s : Sequent) : List (Proof s) :=
  match s with
  | .seq xs a => by
    have proofs := automatedProof () -/

---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString a :=
    match a with
    | atom₁ => "p"
    | atom₂ => "q"
    | atom₃ => "r"

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

---------HELPED-------------
/-
  Ordering formulas is more tricky since we are dealing with tree-like structures
  We encode them into lists of nats (question: can we use `Nat` as encoding? Why or why not?)
-/
@[simp]
def Form.encode : Form → List Nat
  | bot        => [0]
  | atoms a    => [1, a.toNat]
  | and f g    => [2, (encode f).length] ++ encode f ++ encode g
  | or f g     => [3, (encode f).length] ++ encode f ++ encode g
  | imp f g    => [4, (encode f).length] ++ encode f ++ encode g

theorem form_inj {f : Form} (h : f.encode = g.encode) :
  f = g := by
  match f, g with
  | bot, bot => rfl
  | bot, atoms _ => simp only [encode, List.cons.injEq, zero_ne_one, List.ne_cons_self, and_self] at h
  | atoms _, bot => simp at h
  | atoms a, atoms b =>
    simp only [encode, toNat, List.cons.injEq, and_true, true_and] at h
    match a, b with
    | atom₁, atom₁ | atom₃, atom₃ | atom₂, atom₂ => rfl
    | atom₁, atom₂ | atom₁, atom₃ | atom₂, atom₁ | atom₂, atom₃ | atom₃, atom₁ | atom₃, atom₂ => simp at h
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
def example2 : Multiset Form := {atoms atom₁, bot, bot}

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
  toString seq :=
  match seq with
  | .seq Γ Δ => String.intercalate ", " (List.map formToString (Multiset.sort LE.le Γ))
    ++ " ⊢ " ++ String.intercalate ", " (List.map formToString (Multiset.sort LE.le Δ))

instance : ToString Seq4Proof where
  toString seq4 :=
  match seq4 with
  | .seq4 as forms₁ imps₁ usedImps₁  bs forms₂ imps₂ =>
  (List.map toString as).toString ++ (List.map formToString forms₁).toString ++ (List.map formToString imps₁).toString
  ++ "⊢" ++ (List.map toString bs).toString  ++ (List.map formToString forms₂).toString

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map formToString)

def proofToString {seq : Sequent} : Proof seq → String
| .ax x xs ys gs zs  =>
  s!"AX: {formToString x}, {listToString xs}, {listToString ys} ⊢ {listToString gs}, {listToString zs} "
| .botl xs ys gs =>
  s!"⊥L: ⊥, {listToString xs}, {listToString ys} ⊢ {listToString gs}"
| .andl a b xs ys gs proof =>
  s!"{proofToString proof} '\n' ∧L: ({formToString a} ∧ {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}"
| .andr a b xs ys gs proof₁ proof₂=>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' ∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}, {listToString ys}, {listToString gs}"
| .orl a b xs ys gs proof₁ proof₂=>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' ∨L: ({formToString a} ∨ {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}"
| .orr a b xs ys gs proof =>
  s!"{proofToString proof} '\n' ∨R: {listToString xs} ⊢ {formToString a} ∨ {formToString b}, {listToString ys}, {listToString gs}"
| .impl a b xs ys gs zs proof₁ proof₂ =>
  s!"{proofToString proof₁}    {proofToString proof₂} '\n' →L: ({formToString a} → {formToString b}), {listToString xs}, {listToString ys} ⊢ {listToString gs}, {listToString zs}"
| .impr a b xs ys gs zs proof  =>
  s!"{proofToString proof} '\n' →R: {listToString xs}, {listToString ys} ⊢ {formToString a} → {formToString b}, {listToString gs}, {listToString zs}"
| .afort a b xs ys gs proof  =>
  s!"{proofToString proof} '\n' →R: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}, {listToString gs}"

def listProofToString : List (Proof seq) → String
| [] => ""
| x::xs => proofToString x ++ listProofToString xs

instance : ToString (List (Proof seq)) where
  toString proof := listProofToString proof

#eval listProofToString (findAtomicProofs
  (findIntersection [atom₁] [atom₁, atom₂])
  [atom₁]
  []
  ([.imp (.atoms atom₁) (.atoms atom₂)])
  [atom₁, atom₂]
  []
  (by intros _ hx; exact hx))

--modusponens "a → b, a ⊢ β"
#eval String.toFormat ( listProofToString (automatedProof (.seq4 [] [.imp (.atoms .atom₁) (.atoms .atom₂), .atoms .atom₁] [] [] [] [(.atoms .atom₂)] [])))
-- ⊢ ¬¬ (¬x ∨ x)
--#eval listProofToString (automatedProof (.seq4 [] [] [] [] [] [(.neg (.neg (.or (.neg (.atoms .atom₁)) (.atoms .atom₁))))] []))

--#eval listProofToString (automatedProof (.seq4 [] [(.atoms .atom₂)] [] [] [] [(.or ( (.atoms .atom₁)) (.atoms .atom₂))] []))
-- a ⊢ ¬x ∨ a
--#eval listProofToString (automatedProof (.seq4 [] [(.atoms .atom₂)] [] [] [] [(.or (.neg (.atoms .atom₁)) (.atoms .atom₂))] []))
--  (x ∨ y) ∧ z ⊢ (x ∧ z) ∨ (y ∧ z)
#eval String.toFormat (listProofToString (automatedProof (.seq4 [] [.and (.or (.atoms .atom₁) (.atoms .atom₂)) (.atoms .atom₃)] [] [] [] [(.or (.and (.atoms .atom₁) (.atoms .atom₃) ) (.and (.atoms .atom₂) (.atoms .atom₃)))] [])))

--from corsi tassi article: ((((p → r) → p) → p) → ⊥)
--#eval listProofToString (automatedProof (.seq4 [] [] [] [] [] [.imp (.imp (.imp (.imp (.atoms .atom₁) (.atoms .atom₃)) (.atoms .atom₁)) (.atoms .atom₁)) .bot] []))

end multiSucc
