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
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Display


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
      (hxs : x ∈ xs) →
      (hys : x ∈ ys) →
      Proof ⟨↑xs, ↑ys⟩
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys : List Form),
      Proof ⟨↑(⊥ :: xs), ↑ys⟩
  | botr :
    ∀ (xs ys : List Form),
      Proof ⟨↑xs, ↑ys⟩ →
      Proof ⟨↑xs, ↑(⊥ :: ys)⟩
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys: List Form),
      Proof ⟨↑(a :: b :: xs), ↑ys⟩ →
      Proof ⟨↑((a ∧∧ b) :: xs), ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys: List Form),
      Proof ⟨↑xs, ↑(a :: ys)⟩ →
      Proof ⟨↑xs, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑((a ∧∧ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys : List Form),
    Proof ⟨↑(a :: xs), ↑ys⟩ →
    Proof ⟨↑(b :: xs), ↑ys⟩ →
    Proof ⟨↑((a ∨∨ b) :: xs), ↑ys⟩
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof ⟨↑xs, ↑(a :: b :: ys)⟩ →
      Proof ⟨↑xs, ↑(( a ∨∨ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys: List Form),
      Proof ⟨↑(a :: xs), {b}⟩ →
      Proof ⟨↑(xs), ↑((a ⊃ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys : List Form),
      Proof ⟨↑((a ⊃ b) :: xs), ↑(a :: ys)⟩ →
      Proof ⟨↑(b :: xs ), ↑ys⟩ →
      Proof ⟨↑((a ⊃ b) :: xs), ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys : List Form),
      Proof ⟨↑xs, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑((a ⊃ b) :: ys)⟩

--deriving Repr
open Proof


@[simp]
def Seq4Proof.toSeq (p : Seq4Proof ): Sequent :=
  have ant := Multiset.ofList ((p.as.map .atoms) ++ p.fL ++ p.block.map Imp.toForm)
  have succ := Multiset.ofList ((p.bs.map Form.atoms) ++ p.fR ++ p.impR.map Imp.toForm)  -- hist is to monitor R→ usage, not to display
  ⟨ant, succ⟩

def Sequent.toSeq4 (s : Sequent) : Seq4Proof :=
Seq4Proof.mk [] (Multiset.sort s.Γ LE.le) [] [] (Multiset.sort s.Δ LE.le) [] []

def Proof.castSeqList (x : List (Proof ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩) := by rw [ha, hb] at x; exact x



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

def automatedProof (s : Seq4Proof) (cap : ℕ ) (hcap : s.cap.card ≤ cap := by simp at *; grind ) (metaR1 : s.impR ∩ s.hist = ∅ := by grw [metaR1]): List (Proof s.toSeq) :=
  match s with
  | {as, fL, block,  bs, fR, impR, hist} =>
    match fL with
    | [] =>
      match fR with
      | [] => -- succedent only has atoms left --
        match common : findIntersection as bs with
        -- no common atoms
        | [] =>
          match impR with
          | [] => []
          | impR => --METARULE 1 NONINVERTABLE REEGEL
            let impRApplications : List (Proof ⟨↑(as.map Form.atoms ++ block.map Imp.toForm), ↑(bs.map Form.atoms ++ impR.map Imp.toForm)⟩) :=
              impR.attach.flatMap (λ (⟨⟨a, b⟩ , ha⟩ : {i : Imp // i ∈ impR}) ↦ by

                  have inclusion : insert { left := a, right := b } ( collectImpsForm a ∪ collectImpsForm b) ⊆   impR.toFinset.biUnion collectImpsImp := by
                    intro x hx
                    apply Finset.mem_biUnion.mpr
                    refine ⟨⟨a,b⟩, by simpa using ha, ?_⟩
                    simp [collectImpsImp] at hx ⊢
                    exact hx

                  have eq : block.toFinset.biUnion collectImpsImp = (block.map Imp.toForm ).toFinset.biUnion collectImpsForm := by ext x; simp [Finset.mem_biUnion]

                  have premise := automatedProof ⟨as, (a :: (block.map Imp.toForm)), [], [], [b], [], (⟨ a, b⟩ :: hist)⟩ cap (by grw [← hcap]; simp; apply Finset.card_le_card ?_; grind) (by simp)

                  let f := (impr a b (as.map Form.atoms ++ block.map Imp.toForm) (bs.map Form.atoms ++ (impR.erase ⟨a, b⟩).map Imp.toForm))

                  simp only [Seq4Proof.toSeq] at premise f ⊢
                  let res := (Proof.castSeqList premise).map f
                  exact Proof.castSeqList res (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
                  )
            Proof.castSeqList impRApplications (by simp only [List.append_nil]) (by simp only [Multiset.coe_eq_coe]; grind)

        | xs => by
          have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          have corr := findIntersCorr as bs
          have proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        ax (.atoms x) ((as.map Form.atoms) ++ (block.map Imp.toForm)) ((bs.map Form.atoms) ++ (impR.map Imp.toForm))
                        (by simp [hx, Γ, corr])
                        (by simp [hx, Γ, corr]))
          simp only [Seq4Proof.toSeq, List.append_nil]; exact proofs

      -- open up forms on right side
      | (.atoms a) :: succForms =>  --move atom to succ atoms list
        Proof.castSeqList ( automatedProof ⟨as, [], block, a :: bs, succForms, impR, hist⟩ cap ) (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
      | ⊥ :: succForms =>  by --botr rule, .bot is ignored
        have premise := automatedProof ⟨as, [], block, bs, succForms, impR, hist⟩ cap
        simp only [Seq4Proof.toSeq, List.append_nil] at premise
        have rule := List.map (botr ((as.map .atoms)++ (block.map Imp.toForm)) (bs.map .atoms ++ succForms ++ (impR.map Imp.toForm))) premise
        simp only [Seq4Proof.toSeq, List.append_nil]
        apply Proof.castSeqList rule (by rfl) (by simp only [Multiset.coe_eq_coe]; grind )
      | (.and a b) :: succForms => by
        have premise₁ := automatedProof ⟨as, [], block, bs, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        simp only [Seq4Proof.toSeq, List.append_nil] at premise₁ premise₂ ⊢
        have rule := List.map (andr a b ((as.map .atoms) ++ (block.map Imp.toForm)) (bs.map .atoms ++ succForms ++ (impR.map Imp.toForm))).uncurry
                        (getPairs
                          (Proof.castSeqList premise₁ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind))
                          (Proof.castSeqList premise₂ (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)))
        apply Proof.castSeqList rule (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
      | (.or a b) :: succForms => by
        have premise := automatedProof ⟨as, [], block, bs, a :: b :: succForms, impR, hist⟩ cap
        simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
        have rule := List.map (orr a b ((as.map .atoms) ++ (block.map Imp.toForm)) (bs.map .atoms ++ succForms ++ (impR.map Imp.toForm))) (Proof.castSeqList premise (by rfl) (by simp only [Multiset.coe_eq_coe]; grind))
        apply Proof.castSeqList rule (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
      | (.imp a b) :: succForms => by --METARULE 4 move to imps list
        -- TODO apply afortiori immediately, if it is in usedImps₂. else: läheb imps listi
        if inc : ⟨a,b⟩ ∈ hist then
          have premise := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
          simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
          have rule := List.map (afort a b (as.map .atoms ++ block.map Imp.toForm) (bs.map .atoms ++ succForms ++ (impR.map Imp.toForm))) (Proof.castSeqList premise (by rfl) (by simp only [Multiset.coe_eq_coe]; grind))
          apply Proof.castSeqList rule (by rfl) (by simp only [Multiset.coe_eq_coe]; grind)
        else
          have proof := automatedProof ⟨as, [], block, bs, succForms, ⟨a,b⟩ :: impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) (by simp at metaR1; simp; grind)
          apply Proof.castSeqList proof (by rfl)

    -- open up forms on left side --
    | (.atoms a) :: antForms => by
      have proof := automatedProof ⟨as ++ [a], antForms, block, bs, fR, impR, hist⟩ cap
      simp [Seq4Proof.toSeq] at proof ⊢
      exact proof
    | .bot :: antForms => by
      have rule := [botl (as.map .atoms ++ antForms ++ (block.map Imp.toForm)) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm))]
      simp only [Seq4Proof.toSeq, List.append_assoc, List.cons_append]
      apply Proof.castSeqList rule
    | (.and a b) :: antForms => by
      have premise := automatedProof ⟨as, a :: b :: antForms, block, bs, fR, impR, hist⟩ cap
      simp only [Seq4Proof.toSeq] at premise; simp only [Seq4Proof.toSeq]
      have rule := List.map (andl a b ((as.map .atoms) ++ antForms ++ (block.map Imp.toForm)) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm))) (Proof.castSeqList premise (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
      apply Proof.castSeqList rule (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
    | (.or a b) :: antForms => by
      have premise₁ := automatedProof ⟨as, a::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have premise₂ := automatedProof ⟨as, b::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      simp only [Seq4Proof.toSeq] at premise₁ premise₂ ⊢
      have h := List.map (orl a b (as.map .atoms ++ antForms ++ (block.map Imp.toForm)) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm))).uncurry
                (getPairs
                  (Proof.castSeqList premise₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                  (Proof.castSeqList premise₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                )
      apply Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
    | (.imp a b) :: antForms => by -- TODO does .imp a b go into block on the second branch too?
      have premise₁ := automatedProof ⟨as, antForms, ⟨a, b⟩ :: block, bs, a::fR, impR, hist⟩ cap
      have premise₂ := automatedProof ⟨as, b::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      simp only [Seq4Proof.toSeq, List.append_assoc, List.cons_append] at premise₁ premise₂ ⊢
      have h := List.map (impl a b (as.map .atoms ++ antForms ++ (block.map Imp.toForm)) (bs.map .atoms ++ fR ++ (impR.map Imp.toForm))).uncurry
                (getPairs (Proof.castSeqList premise₁ ) (Proof.castSeqList premise₂ ))
      apply Proof.castSeqList h

termination_by s.weight cap hcap
decreasing_by
all_goals simp [Seq4Proof.weight]; try grind
. simp at *
  have hx : { left := a, right := b } ∉ hist := by
    intro hmem
    have : { left := a, right := b } ∈ impR ∩ hist := List.mem_inter_of_mem_of_mem ha hmem
    simp [metaR1] at this
  have hxFin : { left := a, right := b } ∉ hist.toFinset := by simp; exact hx
  have hcard : hist.toFinset.card < (insert { left := a, right := b } hist.toFinset).card := by
    have : (insert { left := a, right := b } hist.toFinset).card = hist.toFinset.card + 1 := Finset.card_insert_of_notMem hxFin
    grind
  grind



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
  let ruleLine := s!"∧L: ({a} ∧ {b}), {listToString xs} ⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {listToString xs} ⊢ {a} ∧ {b}, {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({a} ∨ {b}), {listToString xs} ⊢ {listToString ys}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr a b xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊢ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl a b xs ys proof₁ proof₂ =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L: ({a} → {b}), {listToString xs}⊢ {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs} ⊢ {a} → {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {listToString xs} ⊢ {a} → {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"


def listProofToString : List (Proof xseq) → String
| [] => ""
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs


instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof


def automatedProofHelper (s : Sequent) : Std.Format :=
  have proofs := automatedProof s.toSeq4 s.toSeq4.cap.card (by simp) (by simp [Sequent.toSeq4])
  String.toFormat (listProofToString proofs)


--modusponens "a → b, a ⊢ β"
#eval automatedProofHelper (seq {(p → q), p ⊢ q})
#eval automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval automatedProofHelper (seq {p ⊢ (q ∨ p)})

#eval! automatedProofHelper (seq {⊢ ((p → (p → q)) → (p → q))})
#eval automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))})

#eval automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})
#eval automatedProofHelper (seq {(p → r), (q → ¬r) ⊢ ¬(p ∧ q)})
--from corsi tassi article
#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})

#eval automatedProofHelper (seq { ⊢ ((¬ p → ¬ q) → (q → p))})
#print axioms automatedProofHelper
end multiSucc
