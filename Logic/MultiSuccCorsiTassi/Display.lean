import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex

import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Kripke

namespace multiSucc
open multiSucc

---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString | .mk 1 => "p" | .mk 2 => "q" | .mk 3 => "r" | .mk _ => "undefined"

def Form.toString : Form → String
  | .bot => "⊥"
  | .atoms a => ToString.toString a
  | .imp a .bot => s!"¬{a.toString}"
  -- | .neg a => s!"¬{formToString a}"
  | .and a b => s!"({a.toString} ∧ {b.toString})"
  | .or a b => "(" ++ a.toString ++ " ∨ " ++ b.toString ++ ")"
  | .imp a b => "(" ++ a.toString ++ " ⊃ " ++ b.toString ++ ")"

def Imp.toString (x : Imp) : String := x.toForm.toString

def Imp.toStringBlocked (x : Imp) : String := x.toString ++ "*"

instance : ToString Form := ⟨Form.toString⟩



instance : ToString Sequent where
  toString seq :=
  String.intercalate ", " ((Multiset.sort seq.Γ LE.le ).map Form.toString )
    ++ " ⊢ " ++ String.intercalate ", " ((Multiset.sort seq.Δ LE.le ).map Form.toString )

instance : ToString Seq4Proof where
  toString seq4 :=
  (seq4.as.map toString ).toString ++ (seq4.fL.map Form.toString ).toString ++ (seq4.block.map Imp.toStringBlocked ).toString
  ++ "⊢" ++ (seq4.bs.map toString).toString  ++ (seq4.fR.map Form.toString).toString ++ (seq4.impR.map Imp.toString ).toString

/- instance : ToString World where
  toString world :=
  String.intercalate ", " ((Multiset.sort world.forced LE.le).map toString) ++ world.forced.card.toSubscriptString
    ++ " ⊢ " ++ String.intercalate ", " ((Multiset.sort world.unforced LE.le).map toString) -/

instance : ToString World where
  toString world :=
  String.intercalate ", " (world.forced.map toString)
    ++ " ⊢ " ++ String.intercalate ", " (world.unforced.map toString)

def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => (String.join (List.replicate n "  "))++ line))

def horizontalLine (n : Nat) : String :=
  String.join (List.replicate n "-")

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map Form.toString)


end multiSucc
