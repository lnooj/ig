import Logic.MultiSuccCorsiTassi.Core
--import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
--import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke
--import Logic.MultiSuccCorsiTassi.MultiSuccCorsiTassi
import Logic.MultiSuccCorsiTassi.Proof

namespace multiSucc
open multiSucc

theorem Model_ertyu : ∀ m : Model, m.world.forced ∩ m.world.unforced = ∅ := by sorry

/-- If a sequent gets  countermodels as results, each of those models must refute the sequent  -/
/- theorem Model_correctness :
  ∀ (s : Sequent) {capProof} {metaR1} (ms : List Model),
    automatedProof s.toSeq4 s.toSeq4.cap.card capProof metaR1 = Result.m ms →
    ∀ m ∈ ms, evalSeq s m = TV.f := by
    intro s proof r1 ms res c h
    simp [evalSeq, conjTV, disjTV, Form.eval]; sorry -/
@[simp]
theorem evalAntB0 : ⋀* m, 0 = TV.t := by simp [evalAntB]

@[simp]
theorem evalBlocked_true_in_branch {i : Imp} {m m' : Model}
  (wf : m.wf )
  (hm_mem : m' ∈ m.all)
  (this : evalBlocked i m = TV.t) : (i.f ⊃ i.g).eval m' = TV.t := by
  rw [evalBlocked_true_iff] at this
  rw [eval_imp_true_iff]
  simp_all
  constructor
  . sorry
  . sorry

--TODO if all atoms in stuctures every world, then eval = .t
-- if eval u, then some atom ....
-- sequent holds if for all structures
theorem proof_correctness :
  ∀ (s : Sequent) (_ : Proof s) (m : Model) (_ : m.wf), s.eval m ≠ TV.f := by
  intro s pf m wf
  induction pf generalizing m with
  | ax x xs ys bl hxs hys =>
    simp only [ne_eq, Sequent.eval_false_iff, Classical.not_and_iff_not_or_not]
    have hxsM : Form.atoms x ∈ (↑xs : Multiset Form) := by simpa
    if xtv : x ∈ m.world.forced then
      suffices evalSucc ↑ys m = TV.t by grind
      apply evalSucc_true hys
      grind
    else if xtv' : x ∈ m.world.unforced then grind
    else grind
  | botl => grind
  | botr xs ys prem => simp_all
  | andl a b xs ys prem ih =>
    simp_all
  | andr a b xs ys prem1 prem2 =>
    simp_all only [ne_eq, Sequent.eval_false_iff]
    grind
  | orl a b xs ys prem1 prem2 =>
    simp_all only [ne_eq, Sequent.eval_false_iff, evalAnt_cons, not_and]
    grind
  | orr a b xs ys prem =>
    simp_all
  | impr a b xs ys bl prem ih => --tahame et a b oleks t,a on f u, b t, u
    apply eval_imp_righ_wo_ys
    simp_all--ih gives that b cant be false. ys throw away. ih on ms children as well to show that future imp is false
    intro h₁ h impF
    apply eval_imp_false_contradict at impF
    --simp_all
    contrapose! ih
    simp_all
    rcases impF with ⟨m', hm_mem, ⟨ha, hb⟩⟩
    . use m'
      have monoList : ∀ x ∈ xs, x.eval m' = TV.t := by grind [Model.mono_all_true]
      split_ands
      . apply Model.all_wf wf hm_mem
      . assumption
      . rintro x (h | ⟨i, h', _, _⟩)
        . grind
        . have : evalBlocked i m = TV.t := by grind
          grind [evalBlocked_true_in_branch]
          --grind [evalBlocked, eval_imp_true_iff]
      . assumption

  | impl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp_all
    intro h₁ h₂
    have impT := h₁
    rw [eval_imp_true_iff] at h₁
    simp at h₁
    cases h₁ with
    | intro himp hbranch =>
      cases himp with
      | inl h =>
        intro hbl
        apply ih₁ <;> try grind [evalBlocked_true_iff]
      | inr h => simp_all

  | afort a b xs ys bl prem ih =>
    simp_all
    intro h₁ h₂ i
    specialize ih m wf h₁ h₂
    apply_assumption
    apply imp_false_then_b_false i wf

#print axioms proof_correctness
