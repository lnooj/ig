import Mathlib.Data.Multiset.Basic

namespace multiSucc

structure Atom where
  atom : Nat
deriving DecidableEq, Repr

inductive Form
| bot : Form
| atoms : Atom → Form
| and : Form → Form → Form
| or : Form → Form → Form
| imp : Form → Form → Form
deriving DecidableEq, Repr

-- such notation is used as not to confuse with Lean's internal logic notation
notation "⊥" => Form.bot
infixl:50 " ∧∧ " => Form.and
infixl:50 " ∨∨ " => Form.or
infixl:60 " ⊃ " => Form.imp

def Form.neg (a : Form) : Form :=  a ⊃ ⊥

inductive Sequent
  | seq : Multiset Form → Multiset Form → Sequent

--TODO irreducable sequent
/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
Seperate atomic implications in the form a → P, bc these need to be handled last.
atoms, forms, imps, aimps ⊢ atoms, forms, imps
[x, y], [f1, f2], [imp1, imp2] [aImp] ⊢ [x, y], [g1, g2], [imp1, imp2]
 -/

 -- TODO maybe make seperate type Imp and specify which lists are Imp Lists
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → List Form → List Atom → List Form → List Form → Seq4Proof
--deriving Repr


end multiSucc
