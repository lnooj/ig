import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw

import Logic.MultiSuccDyckhoff.Core
import Logic.MultiSuccDyckhoff.Helper
import Logic.MultiSuccDyckhoff.Display
import Logic.MultiSuccDyckhoff.Syntax

namespace multiSucc
open multiSucc



/-
imp₁ imp₂ imp₃ imp₄ (imp₀) are defined to help with termination and looping prevention (paper by Roy Dyckhoff)

 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (a : Form) (xs ys : List Form), --TRY THIS WAY, GIVE PROOF OF INCLUSION
      (hxs : a ∈ xs) →
      (hys : a ∈ ys) →
      Proof (.seq ↑xs ↑ys)
  -- ∀ x Γ, (⊥, Γ ⊢ x)
  | botl :
    ∀ (xs ys : List Form),
      Proof (.seq ↑( ⊥ :: xs) ↑ys)
    -- ∀ Γ, ( ⊥, Γ ⊢ ⊥)
  | botr :
    ∀ (xs ys : List Form),
      Proof (.seq ↑xs ↑ys) →
      Proof (.seq ↑xs ↑(⊥ :: ys))
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑(a :: b :: xs) ↑ys) →
      Proof (.seq ↑((a ∧∧ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys : List Form),
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
      Proof (.seq ↑xs ↑((a ∨∨ b) :: ys))
  -- a is .bot IS THIS RULE NECESSARY? based on paper p800 proof e.iv
  | impl₀ :
    ∀ (b : Form) (xs  ys: List Form),
      Proof (.seq ↑xs ↑ys) →
      Proof (.seq ↑((⊥ ⊃ b) :: xs) ↑ys)
  -- a is atomic
  -- ∀ a b Γ Δ, (a, b, Γ ⊢ Δ) → (a → b, a, Γ ⊢ Δ)
  | impl₁ :
    ∀ (a : Atom) (b : Form) (xs ys : List Form), --HERE ALSO NEED PROOF OF a ∈ xs
      (h : (.atoms a) ∈ xs) →
      Proof (.seq ↑( b :: xs) ↑ys) →
      Proof (.seq ↑(((.atoms a) ⊃ b) :: xs) ↑ys)
  -- implications left side is and operation
  -- ∀ c d b Γ Δ, (c ⊃ (d ⊃ b), Γ ⊢ Δ) → ((c ∧∧ d) ⊃ b, Γ ⊢ Δ)
  | impl₂ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((c ⊃ (d ⊃ b)) :: xs) ↑ys) →
      Proof (.seq ↑(((c ∧∧ d) ⊃ b) :: xs) ↑ys)
  -- left side is or op
  -- ∀ c d b Γ Δ, (c ⊃ b, d ⊃ b, Γ ⊢ Δ) → ((c ∨∨ d) ⊃ b, Γ ⊢ Δ)
  | impl₃ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((c ⊃ b) :: (d ⊃ b) :: xs) ↑ys) →
      Proof (.seq ↑(((c ∨∨ d) ⊃ b) :: xs) ↑ys)
  -- left side is imp op
  -- ∀ c d b Γ Δ, ( d ⊃ b, Γ ⊢ c ⊃ d) → (b, Γ ⊢ Δ) → ((c ⊃ d) ⊃ b, Γ ⊢ Δ) OR USE THE OTHER RULE?
  | impl₄ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((d ⊃ b) :: xs) {c ⊃ d}) →
      Proof (.seq ↑( b :: xs) ↑ys) →
      Proof (.seq ↑(((c ⊃ d) ⊃ b) :: xs) ↑ys)
  -- ∀ a b Γ, (a, Γ ⊢ b) → (Γ ⊢ a → b)
  | impr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑(a :: xs) {b}) →
      Proof (.seq ↑xs ↑((a ⊃ b) :: ys))
open Proof


@[simp]
def Seq4Proof.toSeq : Seq4Proof → Sequent
| .seq4 atoms₁ forms₁ imps₁ atoms₂ forms₂ imps₂ =>
  have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁)
  have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂ ++ imps₂)
  Sequent.seq ant succ

def Sequent.toSeq4 : Sequent → Seq4Proof
| .seq Δ Γ => Seq4Proof.seq4 [] (Multiset.sort Δ LE.le) []  [] (Multiset.sort Γ LE.le) []

def Proof.castSeqList (x : List (Proof (Sequent.seq (Multiset.ofList a₁) (Multiset.ofList b₁))))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof (Sequent.seq (Multiset.ofList a₂) (Multiset.ofList b₂))) := by rw [ha, hb] at x; exact x

@[simp]
lemma multiset_ofList_map_append_singleton(f : α → β) (xs : List α) (x : α) :
  (Multiset.ofList (xs.map f ++ [f x])) = Multiset.ofList (xs.map f) + {f x} := by
  rw [←Multiset.coe_singleton, ←Multiset.coe_add]

lemma sequent_size_add_singleton (as : List Atom) (imps : List Form) (b : Form) (c : Nat) :
  Multiset.map Form.weight ↑(List.map Form.atoms as ++ b :: imps) + {c}
  = Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps) + {c} + {b.weight} := by
    rw [← List.singleton_append]; simp only [Multiset.map_coe, List.map_append, List.map_singleton];
    rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.add_comm (Multiset.ofList [b.weight])];
    rw [←Multiset.coe_add, Multiset.coe_singleton]; grind

@[simp]
def sequent_simp_dershowitz {as bs y₁ y₂ : Multiset Form} :
  (( (as + y₁ + bs)).IsDershowitzMannaLT (as + y₂ + bs)) =
  (((y₁)).IsDershowitzMannaLT ↑(y₂)) := by sorry

lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl


def automatedProof (s : Seq4Proof) : List (Proof s.toSeq) :=
  match s with
  | .seq4 as forms₁ imps₁ bs forms₂ imps₂ =>
    match forms₂ with
    | [] =>
      match forms₁ with
      | [] =>
        match common : findIntersection as bs with
        | [] =>
          match imps₁ with
          | [] =>
            match imps₂ with
            | [] => []
            | (.imp a b) :: succImps => by
              have h := automatedProof (.seq4 as [] [a] [] [b] [])
              simp [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have rule := List.map (impr a b (as.map .atoms) (bs.map .atoms ++ succImps)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
              apply Proof.castSeqList rule (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
            | _ :: imps => []
          | (.imp a b) :: antImps =>
            match a with
            | .atoms a =>
              if h : a ∈ as then by
                have h := automatedProof (.seq4 as [b] antImps bs [] imps₂)
                simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
                have proofs := List.map (impl₁ a b ((as.map .atoms) ++ antImps) (bs.map .atoms ++ imps₂) (by grind)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl) )
                apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
              else []
            | .and c d => by
              have h := automatedProof (.seq4 as [] ((c ⊃ (d ⊃ b)) :: antImps) bs [] imps₂) --put them straight into imps list
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₂ c d b ((as.map .atoms) ++ antImps) (bs.map .atoms ++ imps₂)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
              apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
            | .or c d => by
              have h := automatedProof (.seq4 as [] ((c ⊃ b) :: (d ⊃ b) :: antImps) bs [] imps₂) --put them straight into imps list
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₃ c d b ((as.map .atoms) ++ antImps) (bs.map .atoms ++ imps₂)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
              apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
            | .imp c d => by
              have h₁ := automatedProof (.seq4 as [] ((d ⊃ b) :: antImps) [] [] [c ⊃ d]) --put them straight into imps list
              have h₂ := automatedProof (.seq4 as [b] antImps bs [] imps₂)
              simp only [Seq4Proof.toSeq, List.append_nil] at h₁ h₂ ⊢
              have proofs := List.map (impl₄ c d b ((as.map .atoms) ++ antImps) (bs.map .atoms ++ imps₂)).uncurry
                  (getPairs (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                            (Proof.castSeqList h₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)))
              apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
            | .bot => by
              have h := automatedProof (.seq4 as [] antImps bs [] imps₂)
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₀ b ((as.map .atoms) ++ antImps) (bs.map .atoms ++ imps₂)) h
              apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
          | _ :: imps => []
        | xs => by
          have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          have corr := findIntersCorr as bs
          --exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (usedImps₂) (Γ)
          have proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        ax (.atoms x) ((as.map Form.atoms) ++ imps₁) ((bs.map Form.atoms) ++ imps₂)
                        (by simp [hx, Γ, corr])
                        (by simp [hx, Γ, corr]))
          dbg_trace "atomic proofs: {xs}"; simp only [Seq4Proof.toSeq, List.append_nil]; exact proofs

      | (.atoms a) :: antForms => --move to as
        Proof.castSeqList (automatedProof (.seq4 (a :: as) antForms imps₁ bs [] imps₂)) (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | ⊥ :: antForms => by
        simp only [Seq4Proof.toSeq, List.append_nil]
        exact Proof.castSeqList [(botl ((as.map .atoms) ++ antForms ++ imps₁) (bs.map .atoms ++ imps₂))] (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.and a b) :: antForms => by
        have h := automatedProof (.seq4 as antForms (a :: b :: imps₁) bs [] imps₂)
        simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
        have rule := List.map (andl a b ((as.map .atoms) ++ antForms ++ imps₁) (bs.map .atoms ++ imps₂)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
        apply Proof.castSeqList rule (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.or a b) :: antForms => by
        have h₁ := automatedProof (.seq4 as (a :: antForms) imps₁ bs [] imps₂)
        have h₂ := automatedProof (.seq4 as (b :: antForms) imps₁ bs [] imps₂)
        simp only [Seq4Proof.toSeq, List.append_nil] at h₁ h₂ ⊢
        have rule := List.map (orl a b ((as.map .atoms) ++ antForms ++ imps₁) (bs.map .atoms ++ imps₂)).uncurry
          (getPairs (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                    (Proof.castSeqList h₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)))
        apply Proof.castSeqList rule (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.imp a b) :: antForms => --move to imps₁
        Proof.castSeqList (automatedProof (.seq4 as antForms ((a ⊃ b) :: imps₁) bs [] imps₂)) (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
    | (.atoms a) :: succForms => --move to bs
      Proof.castSeqList (automatedProof (.seq4 as forms₁ imps₁ (a :: bs) succForms imps₂)) (by rfl)
    | ⊥ :: succForms => by
      have h := automatedProof (.seq4 as forms₁ imps₁ bs succForms imps₂)
      simp only [Seq4Proof.toSeq] at h ⊢
      have rule := List.map (botr ((as.map .atoms) ++ forms₁ ++ imps₁) (bs.map .atoms ++ succForms ++ imps₂)) h
      apply Proof.castSeqList rule (by rfl)
    | (.and a b) :: succForms => by
      have h₁ := automatedProof (.seq4 as forms₁ imps₁ bs (a :: succForms) imps₂)
      have h₂ := automatedProof (.seq4 as forms₁ imps₁ bs (b :: succForms) imps₂)
      simp only [Seq4Proof.toSeq] at h₁ h₂ ⊢
      have rule := List.map (andr a b ((as.map .atoms) ++ forms₁ ++ imps₁) (bs.map .atoms ++ succForms ++ imps₂)).uncurry  (getPairs (Proof.castSeqList h₁ (by rfl)) (Proof.castSeqList h₂ (by rfl)))
      apply Proof.castSeqList rule (by rfl)
    | (.or a b) :: succForms => by
      have h := automatedProof (.seq4 as forms₁ imps₁ bs (a :: b :: succForms) imps₂)
      simp only [Seq4Proof.toSeq] at h ⊢
      have rule := List.map (orr a b ((as.map .atoms) ++ forms₁ ++ imps₁) (bs.map .atoms ++ succForms ++ imps₂)) (Proof.castSeqList h (by rfl))
      apply Proof.castSeqList rule (by rfl)
    | (.imp a b) :: succForms =>  --move to imps₂
      Proof.castSeqList (automatedProof (.seq4 as forms₁ imps₁ bs succForms ((a ⊃ b) :: imps₂))) (by rfl)
termination_by ((Seq4Proof.toSeq s).size, s.size)
decreasing_by
all_goals simp only [Seq4Proof.toSeq, Sequent.size]
. apply Prod.Lex.left; simp only [Multiset.IsDershowitzMannaLT]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as)
  refine ⟨X, ↑([a.weight] ++ [b.weight]), Multiset.map Form.weight ↑((bs.map Form.atoms) ++ (( a ⊃ b)) :: succImps), ?_, ?_, ?_, ?_⟩
  . simp
  . simp [X]; rw [← Multiset.coe_singleton, Multiset.coe_add]; grind
  . simp only [X, List.append_nil]
  . intro y hy; simp at hy; simp [Form.weight];
    refine ⟨1 + a.weight + b.weight, ?_, ?_⟩
    . right; left; rfl
    . grind
. apply Prod.Lex.left; rw [← Multiset.coe_add _ antImps]; rw[ Multiset.map_add Form.weight _ (Multiset.ofList antImps)]
  simp only [List.append_nil]; --rw [← List.singleton_append (Form.atoms a ⊃ b), ← Multiset.coe_add _ antImps]; rw[ Multiset.map_add Form.weight _ (Multiset.ofList antImps)]
  simp only [Multiset.IsDershowitzMannaLT]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ antImps) + Multiset.map Form.weight ↑(List.map Form.atoms bs ++ imps₂)
  refine ⟨X, {b.weight}, {(Form.atoms a ⊃ b).weight}, ?_, ?_, ?_, ?_⟩
  . simp
  . simp [X] ; sorry
  . simp [X] ; sorry
  . simp
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
.  sorry
. sorry
. --apply Prod.Lex.left; apply sequent_simp_dershowitz (Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms₁ ++ imps₁)) ∅ _ _
  sorry
. sorry
. sorry
. sorry



def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax _ xs ys _ _=>
  indent indentLvl s!"AX: {listToString xs} ⊢ {listToString ys}"
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
| .impl₀ b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₀: ({formToString ⊥} → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ a b xs ys _ proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₁: ({formToString (.atoms a)} → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ c d b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₂: (({formToString c} ∧ {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₃ c d b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₃: (({formToString c} ∨ {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₄ c d b xs ys proof₁ proof₂  =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L₄: (({formToString c} → {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"


def listProofToString : List (Proof xseq) → String
| [] => "FAILURE"
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs

instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof


def automatedProofHelper (s : Sequent) : Std.Format :=
  have seq4 := Sequent.toSeq4 s
  have proofs := automatedProof seq4
  dbg_trace "{proofs.length}"; String.toFormat (listProofToString proofs)


#eval! automatedProofHelper (seq {(p → q), p ⊢ q})
#eval! automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval! automatedProofHelper (seq {p ⊢ (q ∨ p)})
#eval! automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {⊢ ((p → (p → q)) → (p → q))})
#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))}) --no proof in single succ system
#eval! automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})

#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})


#print axioms automatedProofHelper
end multiSucc
