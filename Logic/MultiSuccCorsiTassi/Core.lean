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

/- Defining negation as → ⊥  from the getgo-/
def Form.neg (a : Form) : Form :=  a ⊃ ⊥


/- Using Multisets to not worry about order of forms -/
-- [f1, f2] ⊢ [g1, g2]
inductive Sequent
  | seq : Multiset Form → Multiset Form → Sequent
--deriving Repr

/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
[x, y], [f1, f2], usable[imp1, imp2], nonusable[imp1, imp2] ⊢ [x, y], [g1, g2], usable[imp1, imp2], used[imp1, imp2]
 -/
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → List Form  → List Atom → List Form → List Form → List Form → Seq4Proof
--deriving Repr


end multiSucc
