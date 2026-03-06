import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke

namespace multiSucc
open multiSucc

-- all multi premise rules for proofs now need only one for refutation
-- give hist as well
inductive Refutation : Sequent → (hs : List Imp) → Type
  -- ∀ x Γ,  Γ ⊬ Δ
  | ax hs :
    ∀ (as bs: List Atom) (xs : List Imp), --should be list of atoms?
      (intersection : as ∩ bs = []) →
      Refutation ⟨↑(as.map Form.atoms ++ xs.map Imp.toForm), ↑(bs.map Form.atoms)⟩ hs
-- Γ ⊬ Δ → Γ ⊬ ⊥,Δ
  | botr hs :
    ∀ (xs ys : List Form),
      Refutation ⟨↑xs, ↑ys⟩ hs →
      Refutation ⟨↑xs, ↑(⊥ :: ys)⟩ hs
  -- (Γ, a, b ⊬ Δ) → (Γ, a ∧ b ⊬ Δ)
  | andl hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑(a :: b :: xs), ↑ys⟩ hs →
      Refutation ⟨↑((a ∧∧ b) :: xs), ↑ys⟩ hs
  -- (Γ ⊬ a, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₁ hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑xs, ↑(a :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑((a ∧∧ b) :: ys)⟩ hs
  -- (Γ ⊬ b, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₂ hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑xs, ↑(b :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑((a ∧∧ b) :: ys)⟩ hs
  -- (a, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₁ hs :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation ⟨↑(a :: xs), ↑ys⟩ hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑ys⟩ hs
  -- (b, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₂ hs :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation ⟨↑(b :: xs), ↑ys⟩ hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑ys⟩ hs
  -- (Γ ⊬ a, b, Δ) → (Γ ⊬ a ∨ b, Δ)
  | orr hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑xs, ↑(a :: b :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑(( a ∨∨ b) :: ys)⟩ hs
  -- Γ ∩ Δ = ∅ → (a, Γ ⊬ b) →  Γ ⊬ a → b, Δ)
  | impr hs :
    ∀ (a b : Form) (as bs : List Atom) (xs ys: List Imp),
      (intersection : as ∩ bs = []) → -- checking that atoms dont have intersection, for we still have blocked list in ys and xs has all imps we want to use the rule on
      Refutation ⟨↑(a :: (as.map .atoms) ++ (xs.map Imp.toForm)), {b}⟩ (⟨a, b⟩ :: hs ) →
      Refutation ⟨↑((as.map Form.atoms) ++ (xs.map Imp.toForm)), ↑((bs.map Form.atoms) ++ (a ⊃ b) :: (ys.map Imp.toForm))⟩ hs
  -- (a → b, Γ ⊬ a, Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₁ hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑((a ⊃ b) :: xs), ↑(a :: ys)⟩ hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑ys⟩ hs
  --  (b, Γ ⊬ Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₂ hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑(b :: xs ), ↑ys⟩  hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑ys⟩ hs
  --  a ⊃ b ∈ hs → (Γ ⊬ b, Δ) → (Γ ⊬ a ⊃ b, Δ)
  | afort hs :
    ∀ (a b : Form) (xs ys : List Form),
      (hhs : ⟨a, b⟩ ∈ hs) → --or (hhs : a ∈ hs.map .left) →
      Refutation ⟨↑xs, ↑(b :: ys)⟩ hs→
      Refutation ⟨↑xs, ↑((a ⊃ b) :: ys)⟩ hs

def refutationToString  {xseq : Sequent} {h : List Imp} (indentLvl : Nat) : Refutation xseq h → String
| .ax h as bs ys _ =>
  indent indentLvl s!"AX: {listToString (as.map Form.atoms) ++ listToString (ys.map Imp.toForm)} ⊬ {listToString (bs.map Form.atoms)}"
| .botr h xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {listToString xs} ⊬ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {a} ∧ {b}, {listToString xs} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₁ h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {listToString xs} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₂ h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {listToString xs} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₁ h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {listToString xs} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₂ h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {listToString xs} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊬ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ h a b xs ys proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: ({a} → {b}), {listToString xs}⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ h a b xs ys proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: ({a} → {b}), {listToString xs}⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr h a b as bs xs ys _ proof  =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString (as.map .atoms) ++ listToString (xs.map Imp.toForm)} ⊬
                         {a} → {b}, {listToString (bs.map .atoms) ++ listToString (ys.map Imp.toForm)}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort h a b xs ys _ proof  =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {listToString xs} ⊬ {a} → {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"




def listRefutationToString : List (Refutation xseq h) → String
| [] => ""
| x::xs => (refutationToString 0 x).replace " ," "" ++ "\n \n" ++ listRefutationToString xs


instance : ToString (List (Refutation xseq h)) where
  toString proof := listRefutationToString proof

end multiSucc
