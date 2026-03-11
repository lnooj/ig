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
inductive Refutation : Sequent → (blck : List Imp) → (hs : List Imp) → Type
  -- ∀ x Γ,  Γ ⊬ Δ
  | ax blck hs :
    ∀ (as bs: List Atom), --xs: blocked
      (intersection : as ∩ bs = []) →
      Refutation ⟨↑(as.map Form.atoms ++ blck.map Imp.toForm), ↑(bs.map Form.atoms)⟩ blck hs
-- Γ ⊬ Δ → Γ ⊬ ⊥,Δ
  | botr blck hs :
    ∀ (xs ys : List Form),
      Refutation ⟨↑(xs), ↑ys⟩ blck hs →
      Refutation ⟨↑(xs), ↑(⊥ :: ys)⟩ blck hs
  -- (Γ, a, b ⊬ Δ) → (Γ, a ∧ b ⊬ Δ)
  | andl blck hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑(a :: b :: xs), ↑ys⟩ blck hs →
      Refutation ⟨↑((a ∧∧ b) :: xs), ↑ys⟩ blck hs
  -- (Γ ⊬ a, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₁ blck hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑(xs), ↑(a :: ys)⟩ blck hs →
      Refutation ⟨↑(xs), ↑((a ∧∧ b) :: ys)⟩ blck hs
  -- (Γ ⊬ b, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₂ blck hs :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation ⟨↑(xs), ↑(b :: ys)⟩ blck hs →
      Refutation ⟨↑(xs), ↑((a ∧∧ b) :: ys)⟩ blck hs
  -- (a, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₁ blck hs :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation ⟨↑(a :: xs), ↑ys⟩ blck hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑ys⟩ blck hs
  -- (b, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₂ blck hs :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation ⟨↑(b :: xs), ↑ys⟩ blck hs →
    Refutation ⟨↑((a ∨∨ b) :: xs), ↑ys⟩ blck hs
  -- (Γ ⊬ a, b, Δ) → (Γ ⊬ a ∨ b, Δ)
  | orr blck hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑(xs), ↑(a :: b :: ys)⟩ blck hs →
      Refutation ⟨↑(xs), ↑(( a ∨∨ b) :: ys)⟩ blck hs
  -- Γ ∩ Δ = ∅ → (a, Γ ⊬ b) →  Γ ⊬ a → b, Δ)
/-   | impr blck hs :--here the xs left are the blocked ones, no more.
    ∀ (a b : Form) (as bs : List Atom) (ys: List Imp),
      (intersection : as ∩ bs = []) → -- checking that atoms dont have intersection, for we still have blocked list in ys and xs has all imps we want to use the rule on
      Refutation ⟨↑(a :: (as.map .atoms) ++ blck.map Imp.toForm), {b}⟩ [] (⟨a, b⟩ :: hs ) →
      Refutation ⟨↑(as.map Form.atoms ++ blck.map Imp.toForm), ↑((bs.map Form.atoms) ++ (a ⊃ b) :: (ys.map Imp.toForm))⟩ blck hs -/
  | impr blck hs :--here the xs left are the blocked ones, no more.
    ∀ (as bs : List Atom) (ys: List Imp),
      (intersection : as ∩ bs = []) → -- checking that atoms dont have intersection, for we still have blocked list in ys and xs has all imps we want to use the rule on
      ((a b : Form) → ⟨a,b⟩ ∈ ys →  Refutation ⟨↑(a :: (as.map .atoms) ++ blck.map Imp.toForm), {b}⟩ [] (⟨a, b⟩ :: hs )) →
      Refutation ⟨↑(as.map Form.atoms ++ blck.map Imp.toForm), ↑((bs.map Form.atoms) ++ (ys.map Imp.toForm))⟩ blck hs
  -- (a → b, Γ ⊬ a, Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₁ blck hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑((a ⊃ b) :: xs), ↑(a :: ys)⟩ (⟨a, b⟩ :: blck) hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑ys⟩ blck hs
  --  (b, Γ ⊬ Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₂ blck hs :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation ⟨↑(b :: xs), ↑ys⟩  blck hs →
      Refutation ⟨↑((a ⊃ b) :: xs), ↑ys⟩ blck hs
  --  a ⊃ b ∈ hs → (Γ ⊬ b, Δ) → (Γ ⊬ a ⊃ b, Δ)
  | afort blck hs :
    ∀ (a b : Form) (xs ys : List Form),
      (hhs : ⟨a, b⟩ ∈ hs) → --or (hhs : a ∈ hs.map .left) →
      Refutation ⟨↑(xs), ↑(b :: ys)⟩ blck hs →
      Refutation ⟨↑(xs), ↑((a ⊃ b) :: ys)⟩ blck hs

def refutationToString  {xseq : Sequent} {h : List Imp} (indentLvl : Nat) : Refutation xseq blck h → String
| .ax b h as bs _ =>
  indent indentLvl s!"AX: {listToString (as.map Form.atoms) ++ listToStringBlocked b}, ⊬ {listToString (bs.map Form.atoms)}"
| .botr b h xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {listToString xs ++ listToStringBlocked b} ⊬ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {a} ∧ {b}, {listToString xs ++ listToStringBlocked bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₁ bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {listToString xs ++ listToStringBlocked bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₂ bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: {listToString xs ++ listToStringBlocked bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₁ bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {listToString xs ++ listToStringBlocked bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₂ bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {a} ∨ {b}, {listToString xs ++ listToStringBlocked bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr bl h a b xs ys proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs ++ listToStringBlocked bl} ⊬ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ bl h a b xs ys proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: {a} → {b}, {listToString xs ++ listToStringBlocked bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ bl h a b xs ys proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L: {a} → {b}, {listToString xs ++ listToStringBlocked bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr bl h as bs ys _ proof  =>
  let premise := ys.attach.map (λ ⟨⟨a, b⟩, h⟩ ↦ refutationToString (indentLvl + 1) (proof a b h) ) --refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString (as.map .atoms) ++ listToString (bl.map Imp.toForm)} ⊬ {listToString (bs.map .atoms) ++ listToString (ys.map Imp.toForm)}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort bl h a b xs ys _ proof  =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {listToString xs ++ listToStringBlocked bl} ⊬ {a} → {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"




def listRefutationToString : List (Refutation xseq b h) → String
| [] => ""
| x::xs => (refutationToString 0 x).replace " ," "" ++ "\n \n" ++ listRefutationToString xs


instance : ToString (List (Refutation xseq b h)) where
  toString proof := listRefutationToString proof

end multiSucc
