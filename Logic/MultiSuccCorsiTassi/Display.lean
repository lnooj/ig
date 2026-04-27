import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Kripke
import Logic.MultiSuccCorsiTassi.Proof
import Logic.MultiSuccCorsiTassi.Refutation

namespace multiSucc
open multiSucc

/-! # Form, sequent and model display -/

instance : ToString Atom where
  toString | .mk 1 => "p" | .mk 2 => "q" | .mk 3 => "r" | .mk _ => "undefined"

def Form.toString : Form → String
  | .bot => "⊥"
  | .atoms a => ToString.toString a
  | .imp a .bot => s!"¬{a.toString}"
  | .and a b => s!"({a.toString} ∧ {b.toString})"
  | .or a b => "(" ++ a.toString ++ " ∨ " ++ b.toString ++ ")"
  | .imp a b => "(" ++ a.toString ++ " ⊃ " ++ b.toString ++ ")"

def Imp.toString (x : Imp) : String := x.toForm.toString

def Imp.toStringBlocked (x : Imp) : String := x.toString ++ "*"

instance : ToString Form := ⟨Form.toString⟩

instance : ToString World where
  toString world :=
  String.intercalate ", " (world.forced.sort.map toString)
    ++ " ⊢ " ++ String.intercalate ", " (world.rejected.sort.map toString)

def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => (String.join (List.replicate n "  "))++ line))

def mToString : Model → String
| ⟨w, []⟩ => toString w
| ⟨w, bs⟩ =>
  let bstrs := bs.map mToString
  toString w ++ "\n " ++ indent 0 (String.intercalate "  |  " bstrs)


instance : ToString Model where
  toString m := mToString m

instance : ToString TV where
  toString tv :=
  match tv with
  | .t => "T"
  | .f => "F"
  | .u => "U"


def horizontalLine (n : Nat) : String :=
  String.join (List.replicate n "-")

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map Form.toString)

def listToStringB (xs : List Imp) : String :=
  String.intercalate ", " (xs.map Imp.toStringBlocked)

def Γ.ToString (xs : List Form) (bl : List Imp) : String := s!"{listToString xs}, {listToStringB bl}"

def listModelToString (ms : List Model) : String := String.intercalate "\n \n" (ms.map mToString)

/-! # Proof display -/

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



/-! # Refutation display -/

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
  let ruleLine := s!"∧L₁: {Γ.ToString xs bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr₂ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"∧L₂: {Γ.ToString xs bl} ⊬ {a} ∧ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₁ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R₁: {a} ∨ {b}, {Γ.ToString xs bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orl₂ h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R₂: {a} ∨ {b}, {Γ.ToString xs bl} ⊬  {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr h a b xs ys bl proof =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {Γ.ToString xs bl} ⊬ {a} ∨ {b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ h a b xs ys bl proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L₁: {a} ⊃ {b}, {Γ.ToString xs bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ h a b xs ys bl proof =>
  let premise  := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→L₂: {a} ⊃ {b}, {Γ.ToString xs bl} ⊬ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr h as bs ys bl _ proof  =>
  let premises :=
    ys.attach.map (fun imp =>
      match imp with
      | ⟨⟨a, b⟩, hmem⟩ => refutationToString (indentLvl + 1) (proof a b hmem))
  let ruleLine := s!"→R: {listToString (as.map .atoms) ++ listToStringB bl} ⊬ {listToString (bs.map .atoms) ++ listToString (ys.map Imp.toForm)}"
  s!"{String.intercalate "\n" premises}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .afort h a b xs ys bl _ proof  =>
  let premise := refutationToString (indentLvl + 1) proof
  let ruleLine := s!"→AF: {Γ.ToString xs bl} ⊬ {a} ⊃ {b}, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"

def listRefutationToString : List (Refutation xseq h) → String
| [] => ""
| x::xs => (refutationToString 0 x).replace " ," "" ++ "\n \n" ++ listRefutationToString xs


instance : ToString (List (Refutation xseq h)) where
  toString proof := listRefutationToString proof

end multiSucc
