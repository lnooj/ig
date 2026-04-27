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
  f : Form
  g : Form
deriving DecidableEq, Repr

@[grind]
structure ImpB where
  f : Form
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
lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl

@[simp, grind]
def Imp.toForm (i : Imp) : Form := i.f ⊃ i.g

/- /- Top-level change to add impB to Seq. Sequent element is either a form or a blocked imp type -/
inductive SequentElem where
| pure   : Form → SequentElem
| blocked : Imp → SequentElem
deriving DecidableEq, Repr

@[simp]
def SequentElem.toForm : SequentElem → Form
| SequentElem.pure f   => f
| SequentElem.blocked b => Imp.toForm b -/

-- Using Multisets to not worry about order of forms
@[grind]
structure Sequent where
  Γa : Multiset Form
  Γb : Multiset Imp -- blocked implication seperate, seperate semantics
  Δ : Multiset Form

@[grind, simp]
def Sequent.Γ (s : Sequent) := s.Γa ∪ s.Γb.map Imp.toForm


/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
[x, y], [f1, f2], nonusable[imp1, imp2] ⊢ [x, y], [g1, g2], rightImp[imp1,imp2], used[imp1, imp2]
 -/
@[grind]
structure Seq4Proof where
  aL : List Atom
  fL : List Form
  block : List Imp
  aR : List Atom
  fR : List Form
  impR : List Imp
  hist : List Imp

/-
  Ordering formulas is more tricky since we are dealing with tree-like structures
  We encode them into lists of nats
-/
@[simp]
def Form.encode : Form → List Nat
  | bot        => [0]
  | atoms a    => [1, a.atom]
  | and f g    => [2, (encode f).length] ++ encode f ++ encode g
  | or f g     => [3, (encode f).length] ++ encode f ++ encode g
  | imp f g    => [4, (encode f).length] ++ encode f ++ encode g

@[simp]
def Imp.encode (x : Imp) : List Nat := x.toForm.encode

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

lemma Imp.ext {a b : Imp} (h : a.encode = b.encode) : a = b := by
  suffices a.toForm = b.toForm by grind [toForm]
  apply form_inj
  simp_all

/-
  We can give a canonical ordering to `Form`s using our encodings
  Our definition of ordering is this: `f ≤ g ↔ Form.encode f ≤ Form.encode g`
-/
instance : LinearOrder Form :=
  LinearOrder.lift' Form.encode (fun _ _ h => form_inj h)

instance : LinearOrder Atom :=
  LinearOrder.lift' (fun a : Atom => a.atom) (fun _ _ h => Atom.ext h)

instance : LinearOrder Imp :=
  LinearOrder.lift' Imp.encode (fun _ _ h => Imp.ext h)

def example1 : Multiset Nat := {3, 1, 2, 2}
def example2 : Multiset Form := {.atoms ( Atom.mk 1), .bot, .bot}

/-
   We can turn multisets into (computable) sorted lists with `sort`
   But `sort` needs a relation with respect to which it will sort the elements on the multiset
-/

#eval Multiset.sort example1 LE.le
#eval Multiset.sort example2 LE.le

def Sequent.Γa_getList { s : Sequent} : List Form := Multiset.sort s.Γa LE.le
def Sequent.Γb_getList { s : Sequent} : List Imp := Multiset.sort s.Γb LE.le
def Sequent.Δ_getList { s : Sequent} : List Form := Multiset.sort s.Δ LE.le


@[simp]
def Seq4Proof.toSeq (p : Seq4Proof ): Sequent :=
  have antPure := Multiset.ofList ((p.aL.map Form.atoms) ++ p.fL)
  have antBlocked := Multiset.ofList p.block
  have succ := Multiset.ofList ((p.aR.map Form.atoms) ++ p.fR ++ (p.impR.map Imp.toForm))
  ⟨antPure, antBlocked, succ⟩


def Sequent.toSeq4 (s : Sequent) : Seq4Proof :=
Seq4Proof.mk [] s.Γa_getList s.Γb_getList [] s.Δ_getList [] []

end multiSucc
