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

structure Imp where
  left : Form
  right : Form
deriving DecidableEq, Repr

structure aImp where
  a : Atom
  f : Form

-- such notation is used as not to confuse with Lean's internal logic notation
notation "⊥" => Form.bot
infixl:50 " ∧∧ " => Form.and
infixl:50 " ∨∨ " => Form.or
infixl:60 " ⊃ " => Form.imp

def Form.neg (a : Form) : Form :=  a ⊃ ⊥

@[simp, grind]
def Imp.toForm (i : Imp) : Form :=
  i.left ⊃ i.right

def aImp.toForm (i : aImp) : Form :=
  .atoms i.a ⊃ i.f

structure Sequent where
  Γ : Multiset Form
  Δ : Multiset Form


/-
Seq4Proof is needed to seperate the purely atomic formulas from the rest in antecedent.
This is required for easier algorithmic approach, where we can one by one open up the more complex formulas.
Seperate atomic implications in the form a → P, bc these need to be handled last.
atoms, forms, imps, aimps ⊢ atoms, forms, imps
[x, y], [f1, f2] [aImp] ⊢ [x, y], [g1, g2], [imp1, imp2]
 -/
structure Seq4proof where
  as : List Atom
  fL : List Form
  aimp : List aImp
  bs : List Atom
  fR : List Form
  impR : List Imp

/- def Seq4Proof.irreducable : Seq4Proof → Bool
| {as, [], aimp, bs, [], impR} =>
  if no a ∈ as in left of ∀  imp ∈  aimps -/

@[simp]
def Form.encode : Form → List Nat
  | bot        => [0]
  | atoms a    => [1, a.atom]
  | and f g    => [2, (encode f).length] ++ encode f ++ encode g
  | or f g     => [3, (encode f).length] ++ encode f ++ encode g
  | imp f g    => [4, (encode f).length] ++ encode f ++ encode g

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

instance : LinearOrder Atom :=
  LinearOrder.lift' (fun a : Atom => a.atom) (fun _ _ h => Atom.ext h)

instance : LinearOrder Form :=
  LinearOrder.lift' Form.encode (fun _ _ h => form_inj h)


@[simp]
def Seq4Proof.toSeq (p : Seq4proof ) : Sequent :=
  have ant := Multiset.ofList ((p.as.map .atoms) ++ p.fL ++ p.aimp.map aImp.toForm)
  have succ := Multiset.ofList ((p.bs.map .atoms) ++ p.fR ++ p.impR.map Imp.toForm)
  ⟨ant, succ⟩

def Sequent.toSeq4 (s : Sequent) : Seq4proof :=
Seq4proof.mk [] (Multiset.sort s.Γ LE.le) [] [] (Multiset.sort s.Δ LE.le) []


end multiSucc
