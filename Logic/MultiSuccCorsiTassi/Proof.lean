
import Logic.MultiSuccCorsiTassi.Core
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
    ∀ (x : Atom) (xs ys : List Form) (bl : List Imp),
      (hxs : .atoms x ∈ xs) →
      (hys : .atoms x ∈ ys) →
      Proof ⟨↑xs, ↑bl, ↑ys⟩
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(⊥ :: xs), ↑bl, ↑ys⟩
  | botr :
    ∀ (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑ys⟩ →
      Proof ⟨↑xs, ↑bl, ↑(⊥ :: ys)⟩
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(a :: b :: xs), ↑bl, ↑ys⟩ →
      Proof ⟨↑((a ∧∧ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(a :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    Proof ⟨↑(a :: xs), ↑bl, ↑ys⟩ →
    Proof ⟨↑(b :: xs), ↑bl, ↑ys⟩ →
    Proof ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(a :: b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑(( a ∨∨ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(a :: xs ++ bl.map Imp.toForm), {}, {b}⟩ →
      Proof ⟨↑(xs), ↑bl, ↑((a ⊃ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑(⟨a, b⟩ :: bl), ↑(a :: ys)⟩ →
      Proof ⟨↑(b :: xs ), ↑bl, ↑ys⟩ →
      Proof ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑((a ⊃ b) :: ys)⟩

def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax _ xs ys bl _ _=>
  indent indentLvl s!"AX: {Γ.ToString xs bl} ⊢ {listToString ys}"
| .botl xs ys bl =>
  indent indentLvl s!"⊥L: ⊥, {Γ.ToString xs bl} ⊢ {listToString ys}"
| .botr xs ys bl proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {Γ.ToString xs bl} ⊢ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl a b xs ys bl proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: ({a} ∧ {b}), {Γ.ToString xs bl} ⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs ys bl proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {Γ.ToString xs bl} ⊢ {a} ∧ {b}, {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b xs ys bl proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({a} ∨ {b}), {Γ.ToString xs bl} ⊢ {listToString ys}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr a b xs ys bl proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {Γ.ToString xs bl} ⊢ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl a b xs ys bl proof₁ proof₂ =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L: ({a} → {b}), {Γ.ToString xs bl}⊢ {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys bl proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {Γ.ToString xs bl} ⊢ {a} → {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort a b xs ys bl proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {Γ.ToString xs bl} ⊢ {a} → {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"




def listProofToString : List (Proof xseq) → String
| [] => ""
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs


instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof
