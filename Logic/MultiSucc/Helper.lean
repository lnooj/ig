--import Logic.MultiSucc.MultiSuccCorsiTassi
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort

namespace multiSucc
open multiSucc
/-
Needed for finding proofs for atomic formulas ([a, b, c ,a, d], Γ ⊢ a) <- this can be split up many ways (2 different a forms) so essentially different proofs
 -/
def splitBy [DecidableEq α ] (xs : List α ) (a : α) : List (List α × List α) :=
  match xs with
  | [] => []
  | x::xs =>
    if x == a then
      ([], xs) :: (splitBy xs a ).map (λ (fst, snd) => (x::fst, snd))
    else
      (splitBy xs a ).map (λ (fst, snd) => (x::fst, snd))

#eval splitBy [1,2,1,2] 2

-- for any pair of returned list, fst+elem+snd = originaalne list
theorem splitByCorrectness [DecidableEq α] (xs : List α) (a : α) :
  ∀ pair ∈ (splitBy xs a), pair.1 ++ (a :: pair.2) = xs :=
  λ pair pair_in =>
  match xs with
  | [] => False.elim (by simp [splitBy] at pair_in) -- contra
  | x::xs => by
    unfold splitBy at pair_in
    by_cases cond : x == a
    . rw[cond] at pair_in
      simp only at pair_in
      simp only [↓reduceIte] at pair_in
      simp only [List.mem_cons] at pair_in
      match pair_in with
      | Or.inl left =>
        clear pair_in
        subst left
        simp only [List.nil_append, List.cons.injEq, and_true]
        simp only [beq_iff_eq] at cond
        subst cond
        apply Eq.refl
      | Or.inr right =>
        clear pair_in
        simp only [List.mem_map] at right
        let ⟨elem,elem_in,eq⟩ := right
        subst eq
        clear right
        have ih := splitByCorrectness xs a _ elem_in
        simp only [List.cons_append]
        simp only [List.cons.injEq]
        simp only [true_and]
        exact ih
    . simp only [Bool.not_eq_true] at cond
      rw[cond] at pair_in
      simp only [↓reduceIte] at pair_in
      simp only [Bool.false_eq_true] at pair_in
      simp only [if_false] at pair_in
      simp only [List.mem_map] at pair_in
      let ⟨elem,elem_in,eq⟩ := pair_in
      clear pair_in
      have ih := splitByCorrectness xs a _ elem_in
      subst eq
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact ih




end multiSucc
