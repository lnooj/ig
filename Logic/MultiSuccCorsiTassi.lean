import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs

inductive Atom
  | atom₁ : Atom | atom₂ : Atom | atom₃ : Atom
deriving DecidableEq, Repr
open Atom

inductive Form
  | bot : Form
  | atoms : Atom → Form
  --| neg : Form → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
deriving DecidableEq
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
  --| .neg f => 1 + sizeOf_Form f
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

In addition we will seperate "special" forms (impl and negl), which require special treatment using a "fuel" counter
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
      Proof (.seq ↑(xs ++ a :: b :: ys) ↑gs) → --antecedent järjekord?
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


def size_sum : List Form → Nat
  | [] => 0
  | f :: fs => sizeOf_Form f + size_sum fs

@[simp]
def termination_metric (s : Seq4Proof) : Nat × Nat:=
match s with
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁ atoms₂ forms₂ imps₂  => ( size_sum imps₁ , size_sum forms₁ + size_sum forms₂)

#check Prod.lex
/- find common atoms in anticident atoms list and succedent atoms list. current: wo duplicates
  Maybe return positions, to be precise, List (Atom, (index from xs, index from ys)) -/
def findIntersection : List Atom → List Atom → List Atom
-- xs.filter (fun a => a ∈ ys) |>.eraseDups
  | _ ,[] => []
  | xs, y::ys =>
    if y ∈ xs then
      if y ∈ findIntersection xs ys then
        findIntersection xs ys
      else y :: findIntersection xs ys -- right now keeping duplicates, is that necessary?
    else findIntersection xs ys

theorem findIntersCorr (xs : List Atom) (ys : List Atom) :
  ∀ atom ∈ (findIntersection xs ys), atom ∈ xs ∧ atom ∈ ys := sorry /-
  λ atom atom_in =>
  match ys with
  | [] => by simp [findIntersection] at atom_in
  | y' :: ys' => by
    unfold findIntersection at atom_in
    by_cases cond: y' ∈ xs
    . simp [cond] at atom_in
      match atom_in with
      | Or.inl left =>
        clear atom_in; subst left; simp; apply cond
      | Or.inr right =>
        clear atom_in;
        have ih := findIntersCorr xs ys'
        have ⟨h₁, h₂⟩ := ih atom right
        exact ⟨h₁, List.Mem.tail _ h₂⟩
    . simp [cond] at atom_in
      have ih := findIntersCorr xs ys'
      have ⟨h₁, h₂⟩ := ih atom atom_in
      exact ⟨h₁, List.Mem.tail _ h₂⟩ -/

/- current: findIntersection returns just intersection, wo. duplicates.  -/
def findAtomicProofs (intersect : List Atom) (as : List Atom)
                    (imps₁ : List Form) (usedImps₁ : List Form)
                    (bs : List Atom) (imps₂ : List Form)
                    : List (Proof (seqAtoms2seq (.seq4 as [] imps₁ usedImps₁ bs [] imps₂))) :=
  have fin_corr := findIntersCorr as bs
  match intersect with
  | [] => []
  | x :: xs => by
    have proof := ax (.atoms x) (List.map .atoms (as.erase x)) (imps₁ ++ usedImps₁) (List.map atoms (bs.erase x)) []
    simp;
    have Γ₁ : Multiset.ofList (List.map atoms (as.erase x) ++ atoms x :: (imps₁ ++ usedImps₁)) =
               Multiset.ofList (List.map atoms as ++ (imps₁ ++ usedImps₁)) := by
               sorry
    have Γ₂ : Multiset.ofList (List.map atoms (bs.erase x) ++ [atoms x]) =
               Multiset.ofList (List.map atoms bs) := by
               sorry
    rw [Γ₁, Γ₂] at proof
    have rest := findAtomicProofs xs as imps₁ usedImps₁ bs imps₂
    simp at rest
    exact (proof :: rest)

/-     have zs_corr := splitByCorrectness as x
    match g : splitBy as x  with -- we know this isn't empty, for x is in intersection
    | [] => [] -- should never come here
    | pair::pairs => by
      rw [g] at zs_corr
      have h1 := zs_corr pair (by simp)
      simp; rw [←h1]
      have x_proof := ax (.atoms x) (List.map .atoms pair.fst) (List.map atoms pair.snd ++ imps₁ ++ usedImps₁) (List.map atoms (bs.erase x)) []
      let x_proofs :=
            List.map
              (λ y =>
                  ax (atoms x)
                    (List.map atoms y.fst)
                    (List.map atoms y.snd ++ imps₁ ++ usedImps₁)
                    (List.map atoms (bs.erase x))
                    []
              )
              pairs
      --simp at x_proofs
      simp; rw [List.append_cons] at h1;
      --exact (x_proof:: x_proofs ++ findAtomicProofs xs as antImps bs)
      have Γ : Multiset.ofList (List.map atoms (bs.erase x) ++ [atoms x]) =
               Multiset.ofList (List.map atoms bs) := by
               have h : x ∈ bs := by sorry

               simp only [Multiset.coe_eq_coe]; rw [List.perm_cons_erase h]
      exact (x_proof::(findAtomicProofs xs as imps₁ usedImps₁ bs imps₂)) -/



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

def automatedProof (s : Seq4Proof) : List (Proof (seqAtoms2seq s)) :=
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
          --| (.neg a) :: xs => sorry
          | _ :: xs => []
        -- atomic proofs exist
        | xs =>

          findAtomicProofs  xs as (imps₁) (usedImps₁) bs (imps₂)


      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) succForms imps₂)
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | .bot :: succForms => [] -- we are left with left and right imp lists
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
      | (.imp a b) :: succForms => by --METARULE 1
        if (.imp a b) ∉ imps₂ then
          have h₁ := automatedProof (.seq4 as [a] (imps₁++usedImps₁) [] [] [b] ((.imp a b)::imps₂) ) --move all usedimps back
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
--. sorry bottom
. simp; apply Prod.Lex.right; simp only [size_sum]; simp; rw [add_comm 1 _];
  refine Nat.lt_add_right (sizeOf_Form b) ?_
  apply Nat.lt_succ_self
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
. simp; apply Prod.Lex.right; simp only [size_sum]; simp
  rw [add_assoc, add_assoc, add_comm 1 _]
  apply Nat.lt_succ_self
. simp; simp only [size_sum]; simp--difficult case
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

---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString a :=
    match a with
    | atom₁ => "a"
    | atom₂ => "b"
    | atom₃ => "c"

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

/- def multisetToList (ms : Multiset Form) : List Form :=
  Multiset.induction_on (m := fun _ => List Form) ms
    []
    (fun a s acc => a :: acc) -/

/-
def multisetToList (ms : Multiset Form) : List Form :=
  Multiset.foldl (λ acc f => f :: acc) [] ms -/

def multisetToString (ms : Multiset Form) : String :=
  Quot.lift
    (fun l : List Form => String.intercalate ", " (l.map formToString))
    (by
      intros a b h
      unfold List.isSetoid at h
      ) ms


def seqToString (seq : Sequent) : String :=
  match seq with
  | .seq Δ Γ => (Δ.toList.map formToString).toString ++ "⊢" ++ (Γ.toList.map formToString).toString
