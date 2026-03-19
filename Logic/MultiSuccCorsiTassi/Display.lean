import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

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
  | .and a b => s!"({a.toString} ∧ {b.toString})"
  | .or a b => "(" ++ a.toString ++ " ∨ " ++ b.toString ++ ")"
  | .imp a b => "(" ++ a.toString ++ " ⊃ " ++ b.toString ++ ")"

def Imp.toString (x : Imp) : String := x.toForm.toString

def Imp.toStringBlocked (x : Imp) : String := x.toString ++ "*"

instance : ToString Form := ⟨Form.toString⟩


instance : ToString Sequent where
  toString seq :=
  String.intercalate ", " ((seq.Γa_getList).map Form.toString ++
                          (seq.Γb_getList).map Imp.toStringBlocked) ++
  " ⊢ " ++
  String.intercalate ", " ((seq.Δ_getList).map Form.toString )


instance : ToString World where
  toString world :=
  String.intercalate ", " (world.forced.sort.map toString)
    ++ " ⊢ " ++ String.intercalate ", " (world.unforced.sort.map toString)

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

end multiSucc
