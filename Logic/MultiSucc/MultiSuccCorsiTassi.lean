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
import Logic.MultiSucc.Helper

import Logic.MultiSucc.Display


namespace multiSucc
open multiSucc

/-
Multi-succedent formulas.
Added a fortiori
 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x ++ Δ
  | ax :
    ∀ (x : Form) (xs ys: List Form),
      Proof (.seq ↑(x :: xs) ↑(x :: ys))
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys : List Form),
      Proof (.seq ↑(⊥ :: xs) ↑ys)
  | botr :
    ∀ (xs ys : List Form),
      Proof (.seq ↑xs ↑ys) →
      Proof (.seq ↑xs ↑(⊥ :: ys))
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys: List Form),
      Proof (.seq ↑(a :: b :: xs) ↑ys) →
      Proof (.seq ↑((a ∧∧ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys: List Form),
      Proof (.seq ↑xs ↑(a :: ys)) →
      Proof (.seq ↑xs ↑(b :: ys)) →
      Proof (.seq ↑xs ↑((a ∧∧ b) :: ys))
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys : List Form),
    Proof (.seq ↑(a :: xs) ↑ys) →
    Proof (.seq ↑(b :: xs) ↑ys) →
    Proof (.seq ↑((a ∨∨ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑xs ↑(a :: b :: ys)) →
      Proof (.seq ↑xs ↑(( a ∨∨ b) :: ys))
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys: List Form),
      Proof (.seq ↑(a :: xs) {b}) →
      Proof (.seq ↑(xs) ↑((a ⊃ b) :: ys)) --succ järjestus
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑((a ⊃ b) :: xs) ↑(a :: ys)) →
      Proof (.seq ↑(b :: xs ) ↑ys) →
      Proof (.seq ↑((a ⊃ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑xs ↑(b :: ys)) →
      Proof (.seq ↑xs ↑((a ⊃ b) :: ys))

--deriving Repr
open Proof


@[simp]
def seqAtoms2seq (s : Seq4Proof) : Sequent :=
  match s with
  | .seq4 atoms₁ forms₁ imps₁ usedImps₁  atoms₂ forms₂ imps₂ _ =>
    have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁ ++ usedImps₁)
    have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂ ++ imps₂)  -- usedImps₂ is to monitor R→ usage, not to display
    Sequent.seq ant succ

def Proof.castSeqList (x : List (Proof (Sequent.seq (Multiset.ofList a₁) (Multiset.ofList b₁))))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂) (hb : Multiset.ofList b₁ = Multiset.ofList b₂) :
    List (Proof (Sequent.seq (Multiset.ofList a₂) (Multiset.ofList b₂))) := by rw [ha, hb] at x; exact x


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
    have proof := ax (.atoms x) (List.map .atoms (as.erase x) ++ imps₁ ++ usedImps₁) (List.map .atoms (bs.erase x) ++ imps₂)
    simp only [seqAtoms2seq, List.append_nil, List.append_assoc]

    have h : x ∈ (findIntersection as bs) := by simp [hxs]

    have Γ₁ : Multiset.ofList (.atoms x :: (List.map .atoms (as.erase x) ++ imps₁ ++ usedImps₁)) =
              Multiset.ofList (List.map .atoms as ++ (imps₁ ++ usedImps₁)) :=
              by simp only [Multiset.coe_eq_coe]; grind

    have Γ₂ : Multiset.ofList ( Form.atoms x :: (List.map Form.atoms (bs.erase x) ++ imps₂)) =
              Multiset.ofList (List.map Form.atoms bs ++ imps₂) :=
              by simp only [Multiset.coe_eq_coe]; grind

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
              if (.imp a b) ∉ usedImps₂ then
                have h₁ := automatedProof (.seq4 as [a] ( usedImps₁) [] [] [b] [] ((a ⊃ b)::usedImps₂)) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
                have h₂ := List.map (impr a b (as.map .atoms ++ usedImps₁) (bs.map .atoms ++ imps₂')) (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                apply Proof.castSeqList h₂ (by simp only [List.append_nil]) (by simp only [Multiset.coe_eq_coe]; grind)
              else -- HERE can try a fortiori METARULE 2
                have h₁ := automatedProof (.seq4 as [] [] usedImps₁ bs  [b]  imps₂' usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
                simp only [seqAtoms2seq, List.append_nil] at h₁ ⊢
                have h₂ := List.map (afort a b ((as.map .atoms) ++ usedImps₁) (bs.map .atoms ++ imps₂')) (Proof.castSeqList h₁ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind))
                apply Proof.castSeqList h₂ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
            | _ => []
          | (.imp a b) :: imps₁' => by
            have pair₁ := automatedProof (.seq4 as [] imps₁' ((a ⊃ b) :: usedImps₁) bs [a] imps₂ usedImps₂ ) cap -- every implicative formula can be principal form of R→ only once!!
            have pair₂ := automatedProof (.seq4 as [b] imps₁' (usedImps₁) bs [] imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
            simp only [seqAtoms2seq, List.append_assoc, List.cons_append, List.append_nil, List.nil_append] at pair₁ pair₂ ⊢
            have h := List.map (impl a b (as.map .atoms ++ imps₁' ++ usedImps₁) (bs.map .atoms ++ imps₂)).uncurry
                      (getPairs
                        (Proof.castSeqList pair₁ (by simp only [Multiset.coe_eq_coe]; grind) (by simp only [Multiset.coe_eq_coe]; grind))
                        (Proof.castSeqList pair₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)))
            apply Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)

          | _ :: xs => []
        -- atomic proofs exist
        | xs => by
          have Γ :  ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (usedImps₂) (Γ)


      -- open up forms on right side
      | (.atoms a) :: succForms => by --move atom to succ atoms list
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁  (bs++[a]) succForms imps₂ usedImps₂) cap
        unfold seqAtoms2seq; simp
        unfold seqAtoms2seq at h; simp at h
        exact h
      | ⊥ :: succForms =>  by --botr rule, .bot is ignored
        have h := automatedProof (.seq4 as [] imps₁ usedImps₁ bs succForms imps₂ usedImps₂) cap
        simp only [seqAtoms2seq, List.append_nil] at h
        have rule := List.map (botr ((as.map .atoms)++imps₁++usedImps₁) (bs.map .atoms ++ succForms ++ imps₂)) h
        simp only [seqAtoms2seq, List.append_nil]
        apply Proof.castSeqList rule
        . simp only [List.append_assoc]
        . simp only [List.append_assoc, Multiset.coe_eq_coe]; grind
      | (.and a b) :: succForms => by
        have pair1 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (a :: succForms) imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind [Finset.union_comm, Finset.union_assoc] )
        have pair2 := automatedProof (.seq4 as [] imps₁ usedImps₁ bs (b :: succForms) imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind [Finset.union_comm, Finset.union_assoc] )
        simp only [seqAtoms2seq, List.append_nil] at pair1 pair2 ⊢
        have h := List.map (andr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms ++ succForms ++ imps₂)).uncurry (getPairs (Proof.castSeqList pair1 (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)) (Proof.castSeqList pair2 (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)))
        apply Proof.castSeqList h (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
      | (.or a b) :: succForms => by
        have h₁ := automatedProof (.seq4 as [] imps₁ usedImps₁ bs  (a :: b :: succForms) imps₂ usedImps₂) cap
        simp only [seqAtoms2seq, List.append_nil] at h₁ ⊢
        have h₂ := List.map (orr a b ((as.map .atoms) ++ imps₁ ++ usedImps₁) (bs.map .atoms ++ succForms++imps₂)) (Proof.castSeqList h₁ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind))
        apply Proof.castSeqList h₂ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
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
      have h:= [botl (as.map .atoms ++ antForms ++ imps₁ ++ usedImps₁) ((bs.map .atoms) ++ forms₂ ++ imps₂)]
      simp only [seqAtoms2seq, List.append_assoc, List.cons_append]
      apply Proof.castSeqList h
      . simp only [List.append_assoc, Multiset.coe_eq_coe]; grind
      . simp only [List.append_assoc]
    | (.and a b) :: antForms => by
      have h₁ := automatedProof (.seq4 as (a :: b :: antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap
      simp only [seqAtoms2seq] at h₁; simp only [seqAtoms2seq]
      have h₂ := List.map (andl a b ((as.map .atoms) ++ antForms ++ imps₁ ++ usedImps₁) ((bs.map .atoms) ++ forms₂ ++ imps₂)) (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
      apply Proof.castSeqList h₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
    | (.or a b) :: antForms => by
      have pair₁ := automatedProof (.seq4 as (a::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have pair₂ := automatedProof (.seq4 as (b::antForms) imps₁ usedImps₁ bs forms₂ imps₂ usedImps₂) cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      simp only [seqAtoms2seq] at pair₁ pair₂ ⊢
      have h := List.map (orl a b (as.map .atoms ++ antForms++imps₁++ usedImps₁) ((bs.map .atoms)++forms₂++ imps₂)).uncurry
                (getPairs
                  (Proof.castSeqList pair₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                  (Proof.castSeqList pair₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                )
      apply Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
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


def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax x xs ys =>
  indent indentLvl s!"AX: {formToString x}, {listToString xs} ⊢ {formToString x}, {listToString ys}"
| .botl xs ys =>
  indent indentLvl s!"⊥L: ⊥, {listToString xs} ⊢ {listToString ys}"
| .botr xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {listToString xs} ⊢ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl a b xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: ({formToString a} ∧ {formToString b}), {listToString xs} ⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}, {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({formToString a} ∨ {formToString b}), {listToString xs} ⊢ {listToString ys}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr a b xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊢ {formToString a} ∨ {formToString b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl a b xs ys proof₁ proof₂ =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L: ({formToString a} → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→a fortiori: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}"
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
  have proofs := automatedProof seq4 seq4.cap.card (by simp)
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
