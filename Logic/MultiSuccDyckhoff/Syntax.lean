import Lean.PrettyPrinter.Delaborator
import Mathlib.Data.Multiset.Basic

import Logic.MultiSuccDyckhoff.Core

open multiSucc

declare_syntax_cat atom
declare_syntax_cat form
declare_syntax_cat multiset
declare_syntax_cat sequent

syntax ident : atom

syntax "mult" "{" multiset "}" : term
syntax "seq " "{" sequent "}" : term

syntax form,* : multiset
syntax multiset " ⊢ " multiset : sequent

syntax "~" term:max : form

syntax "(" form " → " form ")" : form
syntax "(" form " ∧ " form ")" : form
syntax "(" form " ∨ " form ")" : form
syntax "¬" form        : form
syntax "⊥"             : form
syntax atom            : form

syntax "form" "{" form "}" : term
syntax "atom" "{" atom "}" : term


macro_rules
| `(atom {$id:ident}) =>
    match id.getId.toString with
    | "p" => `(Atom.mk 1)
    | "q" => `(Atom.mk 2)
    | "r" => `(Atom.mk 3)
    | s       => Lean.Macro.throwError s!"Unknown atom name: {s}"
| `(mult { $[$fs:form],* }) => `(Multiset.ofList [ $[form {$fs}],* ])
| `(seq { $Γ:multiset ⊢ $Δ:multiset }) =>
      `(Sequent.mk (mult {$Γ}) (mult {$Δ}))
| `(form {($a → $b)} ) => `(Form.imp form {$a} form {$b})
| `(form {($a ∧ $b)} ) => `(Form.and form {$a} form {$b})
| `(form {($a ∨ $b)} ) => `(Form.or form {$a} form {$b})
| `(form {¬$a} ) => `(Form.imp form {$a} form {⊥})
| `(form { ⊥ }) => `(Form.bot)
| `(form {$a:atom}) => `(Form.atoms (atom {$a}))

#check seq {p,( p → q) ⊢ r}
#check form {(p → q)}
#check seq { ⊢ r, p}
