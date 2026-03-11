import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex

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

@[grind]
structure Imp where
  f  : Form
  g : Form
deriving DecidableEq, Repr

-- such notation is used as not to confuse with Lean's internal logic notation
notation "⊥" => Form.bot
infixl:50 " ∧∧ " => Form.and
infixl:50 " ∨∨ " => Form.or
infixl:60 " ⊃ " => Form.imp
infixl:60 " ⊃ " => Imp

/- Defining negation as → ⊥  from the getgo-/
def Form.neg (a : Form) : Form :=  a ⊃ ⊥

@[simp, grind]
def Imp.toForm (i : Imp) : Form :=
  i.f ⊃ i.g

/- Using Multisets to not worry about order of forms -/
@[grind]
structure Sequent where
  Γ : Multiset Form
  Δ : Multiset Form
/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
[x, y], [f1, f2], usable[imp1, imp2], nonusable[imp1, imp2] ⊢ [x, y], [g1, g2], usable[imp1, imp2], used[imp1, imp2]
 -/
@[grind]
structure Seq4Proof where
  as : List Atom
  fL : List Form
  block : List Imp
  bs : List Atom
  fR : List Form
  impR : List Imp
  hist : List Imp

/-
  Ordering formulas is more tricky since we are dealing with tree-like structures
  We encode them into lists of nats (question: can we use `Nat` as encoding? Why or why not?)
-/
@[simp]
def Form.encode : Form → List Nat
  | bot        => [0]
  | atoms a    => [1, a.atom]
  | and f g    => [2, (encode f).length] ++ encode f ++ encode g
  | or f g     => [3, (encode f).length] ++ encode f ++ encode g
  | imp f g    => [4, (encode f).length] ++ encode f ++ encode g

@[simp]
def Imp.encode (x : Imp) : List Nat := x.f.encode ++ x.g.encode

lemma Atom.ext {a b : Atom} (h : a.atom = b.atom) : a = b := by
  cases a; cases b
  simp_all

theorem form_inj {f : Form} (h : f.encode = g.encode) :
  f = g := by
  match f, g with
  | .bot, .bot => rfl
  | .bot, .atoms _ => simp only [Form.encode, List.cons.injEq, Nat.zero_ne_one, List.ne_cons_self,
    and_self] at h
  | .atoms _, .bot => simp only [Form.encode, List.cons.injEq, Nat.succ_ne_self, List.cons_ne_self,
    and_self] at h
  | .atoms a, .atoms b =>
    simp only [Form.encode, List.cons.injEq, and_true, true_and] at h
    apply congrArg Form.atoms (Atom.ext h)
  | .and f g, .and f' g' =>
    simp_all only [Form.encode, List.cons_append, List.nil_append, List.cons.injEq, true_and,
      Form.and.injEq]
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .or f g, .or f' g' =>
    simp_all only [Form.encode, List.cons_append, List.nil_append, List.cons.injEq, true_and,
      Form.or.injEq]
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .imp f g, .imp f' g' =>
    simp_all only [Form.encode, List.cons_append, List.nil_append, List.cons.injEq, true_and,
      Form.imp.injEq]
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
/-
  We can give a canonical ordering to `Form`s using our encodings
  Note that there is already an instance of `LinearOrder (List α)` in the library
  Our definition of ordering is this: `f ≤ g ↔ Form.encode f ≤ Form.encode g`
-/

instance : LinearOrder Form :=
  LinearOrder.lift' Form.encode (fun _ _ h => form_inj h)

instance : LinearOrder Atom :=
  LinearOrder.lift' (fun a : Atom => a.atom) (fun _ _ h => Atom.ext h)

/- `LinearOrder Nat` is already defined in the library
   But `Form` is our own type, so we need to give it one
   Since `Form` is made up of `Atom` and `Form`, we need to take into account both
-/
def example1 : Multiset Nat := {3, 1, 2, 2}
def example2 : Multiset Form := {.atoms ( Atom.mk 1), .bot, .bot}

/-
   We can turn multisets into (computable) sorted lists with `sort`
   But `sort` needs a relation with respect to which it will sort the elements on the multiset

   Why?
   For example, given `{0, 1, 0}`, should we print it as `[0, 0, 1]` or `[0, 1, 0]`?
   We need some canonical order to decide this so in our case, we can use `≤` for sorting
-/

#eval Multiset.sort example1 LE.le
#eval Multiset.sort example2 LE.le


@[simp]
def Seq4Proof.toSeq (p : Seq4Proof ): Sequent :=
  have ant := Multiset.ofList ((p.as.map .atoms) ++ p.fL ++ p.block.map Imp.toForm) --blocked is not apart of seq anymore, sperate for evaling refs
  have succ := Multiset.ofList ((p.bs.map .atoms) ++ p.fR ++ p.impR.map Imp.toForm)  -- hist is to monitor R→ usage, not to display
  ⟨ant, succ⟩

def Sequent.toSeq4 (s : Sequent) : Seq4Proof :=
Seq4Proof.mk [] (Multiset.sort s.Γ LE.le) [] [] (Multiset.sort s.Δ LE.le) [] []

end multiSucc
