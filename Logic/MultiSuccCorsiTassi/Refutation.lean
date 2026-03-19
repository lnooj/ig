import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke

namespace multiSucc
open multiSucc

-- all multi premise rules for proofs now need only one for refutation
-- give hist as well
-- we need to carry blocked seperately to know exactly from which impl these imps came from, bc these will be evaluated as true
inductive Refutation : Sequent → (hs : List Imp) → Type
  -- ∀ x Γ,  Γ ⊬ Δ
  | ax hs :
    ∀ (as bs: List Atom) (bl : List Imp), --xs: blocked
      (intersection : as ∩ bs = []) →
      Refutation ⟨↑(as.map Form.atoms), ↑bl, ↑(bs.map Form.atoms)⟩ hs
-- Γ ⊬ Δ → Γ ⊬ ⊥,Δ
  | botr hs :
    ∀ (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑xs, ↑bl, ↑ys⟩ hs →
      Refutation ⟨↑xs, ↑bl, ↑(⊥ :: ys)⟩ hs
  -- (Γ, a, b ⊬ Δ) → (Γ, a ∧ b ⊬ Δ)
  | andl hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑(a :: b :: xs), ↑bl, ↑ys⟩ hs →
      Refutation ⟨↑((a ∧∧ b) :: xs), ↑bl, ↑ys⟩ hs
  -- (Γ ⊬ a, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑xs, ↑bl, ↑(a :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩ hs
  -- (Γ ⊬ b, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑xs, ↑bl, ↑(b :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩ hs
  -- (a, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    Refutation ⟨↑(a :: xs), ↑bl, ↑ys⟩ hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩ hs
  -- (b, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    Refutation ⟨↑(b :: xs), ↑bl, ↑ys⟩ hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩ hs
  -- (Γ ⊬ a, b, Δ) → (Γ ⊬ a ∨ b, Δ)
  | orr hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑xs, ↑bl, ↑(a :: b :: ys)⟩ hs →
      Refutation ⟨↑xs, ↑bl, ↑(( a ∨∨ b) :: ys)⟩ hs
  -- Γ ∩ Δ = ∅ →
  -- (a₁, Γ ⊬ b₁) | ...| (a₉, Γ ⊬ b₉) →
  -- Γ ⊬ a₁ ⊃ b₁, a₂ ⊃ b₂ ... a₉ ⊃ b₉ Δ)
  | impr hs :--here the xs left are the blocked ones, no more.
    ∀ (as bs : List Atom) (ys: List Imp) (bl : List Imp),
      (intersection : as ∩ bs = []) → -- checking that atoms dont have intersection, for we still have blocked list in ys and xs has all imps we want to use the rule on
    -- a function that applies the premise to all imps in ys
      ((a b : Form) → ⟨a,b⟩ ∈ ys →  Refutation ⟨↑(a :: (as.map .atoms) ++ (bl.map Imp.toForm)), {}, {b}⟩ (⟨a, b⟩ :: hs )) →
      Refutation ⟨↑(as.map Form.atoms), ↑bl, ↑((bs.map Form.atoms) ++ (ys.map Imp.toForm))⟩ hs
  -- (a ⊃ b, Γ ⊬ a, Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑ xs, ↑( ⟨a, b⟩ :: bl), ↑(a :: ys)⟩ hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩ hs
  --  (b, Γ ⊬ Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Refutation ⟨↑(b :: xs), ↑bl, ↑ys⟩ hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩ hs
  --  a ⊃ b ∈ hs → (Γ ⊬ b, Δ) → (Γ ⊬ a ⊃ b, Δ)
  | afort hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      (hhs : ⟨a, b⟩ ∈ hs) → --or (hhs : a ∈ hs.map .left) →
      Refutation ⟨↑(xs), ↑bl, ↑(b :: ys)⟩ hs →
      Refutation ⟨↑(xs), ↑bl, ↑((a ⊃ b) :: ys)⟩ hs

def refutationToString  {xseq : Sequent} {h : List Imp} (indentLvl : Nat) : Refutation xseq h → String
| .ax h as bs bl _ =>
  indent indentLvl s!"AX: {listToString (as.map Form.atoms) ++ listToStringB bl} , ⊬ {listToString (bs.map Form.atoms)}"
| .botr h xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {Γ.ToString xs bl}  ⊬ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {a} ∧ {b}, {Γ.ToString xs bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₁ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {Γ.ToString xs bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₂ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {Γ.ToString xs bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₁ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {Γ.ToString xs bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₂ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {Γ.ToString xs bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {Γ.ToString xs bl} ⊬ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ h a b xs ys bl proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: {a} → {b}, {Γ.ToString xs bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ h a b xs ys bl proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: {a} → {b}, {Γ.ToString xs bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr h as bs ys bl _ proof  =>
  let premise := ys.attach.map (λ ⟨⟨a, b⟩, h⟩ ↦ refutationToString (indentLvl + 1) (proof a b h) ) --refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString (as.map .atoms) ++ listToStringB bl} ⊬ {listToString (bs.map .atoms) ++ listToString (ys.map Imp.toForm)}"
  s!"{ premise.map (λ pre ↦ pre ++ "\n")}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort h a b xs ys bl _ proof  =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {Γ.ToString xs bl} ⊬ {a} → {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"




def listRefutationToString : List (Refutation xseq h) → String
| [] => ""
| x::xs => (refutationToString 0 x).replace " ," "" ++ "\n \n" ++ listRefutationToString xs


instance : ToString (List (Refutation xseq h)) where
  toString proof := listRefutationToString proof

end multiSucc
