import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex

import Logic.MultiSucc.Core

namespace multiSucc
open multiSucc

---------------------------------PARSING-----------------------------
instance : ToString Atom where
  toString | .mk 1 => "p" | .mk 2 => "q" | .mk 3 => "r" | .mk _ => "undefined"

def formToString : Form → String
  | .bot => "⊥"
  | .atoms a => toString a
  | .neg a => s!"¬{formToString a}"
  | .and a b => s!"({formToString a} ∧ {formToString b})"
  | .or a b => "(" ++ formToString a ++ " ∨ " ++ formToString b ++ ")"
  | .imp a b => "(" ++ formToString a ++ " ⊃ " ++ formToString b ++ ")"

instance : ToString Form := ⟨formToString⟩

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

lemma Atom.ext {a b : Atom} (h : a.atom = b.atom) : a = b := by
  cases a; cases b
  simp_all

theorem form_inj {f g : Form} (h : f.encode = g.encode) :
  f = g := by
  match f, g with
  | .bot, .bot => rfl
  | .atoms a, .atoms b =>
    simp only [Form.encode, List.cons.injEq, and_true, true_and] at h
    apply congrArg Form.atoms (Atom.ext h)
  | .and f g, .and f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .or f g, .or f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | .imp f g, .imp f' g' =>
    simp_all
    let ⟨h1,h2⟩ := h
    have := List.append_inj_right h2 h1
    have hn := List.append_inj_left' h2 (congrArg List.length this)
    exact ⟨form_inj hn, form_inj this⟩
  | _, _ => 
    -- All mismatched constructor cases have different list prefixes and can't be equal
    absurd h
    cases f <;> cases g <;> 
    (first | rfl | (simp only [Form.encode, List.cons.injEq]; omega))

/-
  We can give a canonical ordering to `Form`s using our encodings
  Note that there is already an instance of `LinearOrder (List α)` in the library
  Our definition of ordering is this: `f ≤ g ↔ Form.encode f ≤ Form.encode g`
-/

instance : LinearOrder Form :=
  LinearOrder.lift' Form.encode (fun _ _ h => form_inj h)

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
#eval! Multiset.sort example2 LE.le

instance : ToString Sequent where
  toString xseq :=
  match xseq with
  | .seq Γ Δ => String.intercalate ", " (List.map formToString (Multiset.sort Γ LE.le ))
    ++ " ⊢ " ++ String.intercalate ", " (List.map formToString (Multiset.sort Δ LE.le ))

instance : ToString Seq4Proof where
  toString seq4 :=
  match seq4 with
  | .seq4 as forms₁ imps₁ _ bs forms₂ _ _ =>
  (List.map toString as).toString ++ (List.map formToString forms₁).toString ++ (List.map formToString imps₁).toString
  ++ "⊢" ++ (List.map toString bs).toString  ++ (List.map formToString forms₂).toString

def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => (String.join (List.replicate n "  "))++ line))

def horizontalLine (n : Nat) : String :=
  String.join (List.replicate n "-")

def listToString (xs : List Form) : String :=
  String.intercalate ", " (xs.map formToString)

-- Forward declaration needed for proofToString (requires Proof type from MultiSuccCorsiTassi)
-- proofToString and listProofToString will be defined in MultiSuccCorsiTassi.lean

end multiSucc
