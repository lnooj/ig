import Mathlib.Data.Multiset.Basic

namespace singleSucc


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
-- [f1, f2] ⊢ f
inductive Sequent
  | seq : Multiset Form → Form → Sequent


/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
Atomic formulas and implications are seperated.
 -/
-- [x, y], [f1, f2] [imps] ⊢ f
inductive Seq4Proof
  | seq4 : List Atom → List Form → List Form → Form → Seq4Proof


end singleSucc
