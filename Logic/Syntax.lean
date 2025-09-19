import Lean.PrettyPrinter.Delaborator
import Logic.MultiSuccCorsiTassi


open multiSucc
namespace mulSyntax

declare_syntax_cat atom
declare_syntax_cat sequent
declare_syntax_cat form
declare_syntax_cat multiset

syntax "atom" "{" atom "}" : atom
syntax "mult" "{" multiset "}" : term
syntax "seq " "{" sequent "}" : term
syntax multiset " ⊢ " multiset : sequent



syntax form  " → " form : form
syntax form " ∧ " form : form
syntax form " ∨ " form : form
syntax "¬" form : form
syntax "⊥" : form
syntax atom : 


syntax "form" "{" form "}" : term

macro_rules
--| `(seq {$a:multiset ⊢ $b} ) => `(Sequent.seq multiset {$a} multiset {$b})
| `(form {$a → $b} ) => `(Form.imp form {$a} form {$b})
| `(form {$a ∧ $b} ) => `(Form.and form {$a} form {$b})
| `(form {$a ∨ $b} ) => `(Form.or form {$a} form {$b})
| `(form {¬$a} ) => `(Form.imp form {$a} form {⊥})
| `(form { ⊥ }) => `(Form.bot)
| `(atom {$a}) =>  `(Atom.atom {$a})
| `(form {$a}) => `(Form.atoms atom {$a})
end mulSyntax
