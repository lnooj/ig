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
    simp_all only [ne_eq, Sequent.eval_false_iff, not_and]
    grind
  | orr a b xs ys prem =>
    simp_all
  | impr a b xs ys bl prem ih => --tahame et a b oleks t,a on f u, b t, u
    --specialize ih m wf
    apply eval_imp_righ_wo_ys

    simp_all --ih gives that b cant be false. ys throw away. ih on ms children as well to show that future imp is false
    intro h₁ h₂ impF
    rw [eval_imp_false_iff] at impF

    have wf' :=  wf
    rw [Model.wf] at wf'
    simp_all

    rcases impF with ⟨att, bf⟩ | ⟨m', br,impF⟩
    . --have : m.branch = [] := by sorry
      --simp_all
      have ih' := ih m wf att
      contrapose! ih'
      simp_all
      rintro x (_ | ⟨x, xbl, _, _⟩)
      . grind [Model.mono_all_true]
      . specialize h₂ x xbl
        rw [evalBlocked_true_iff] at h₂
        simp at h₂


    . specialize ih m' (by sorry)
      sorry
/-     apply eval_imp_false_contradict at impF
    rcases impF with ⟨m', m'_in, h₃, h₄⟩
    specialize ih m' (by grind) h₃
    simp_all
    rcases ih with ⟨x, (_ | ⟨x , xbl, _, _⟩), xeval⟩
    . grind [Model.mono_all_true]
    . clear h₁ h₃ h₄
      specialize h₂ x xbl
      contrapose xeval
      rw [Model.all] at m'_in; simp_all
      rcases m'_in with parent | ⟨br, brc, brall⟩
      . sorry
      . specialize h₂ br brc
        apply Model.mono_all_true (by rw [Model.wf] at wf; simp at wf; grind) brall h₂
 -/

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


theorem proof_correctness' :
  ∀ (s : Sequent) (_ : Proof s) (m : Model) (_ : m.wf), s.eval m = TV.t := by
  intro s pf m wf
  induction pf generalizing m with
  | ax x xs ys bl hxs hys =>
    simp
    have hxsM : Form.atoms x ∈ (↑xs : Multiset Form) := by simpa
    if xtv : x ∈ m.world.forced then
      suffices evalSucc ↑ys m = TV.t by grind
      apply evalSucc_true hys
      grind
    else if xtv' : x ∈ m.world.unforced then grind
    else sorry
  | botl => grind
  | botr xs ys prem => simp_all
  | andl a b xs ys bl prem ih =>
    simp_all; specialize ih m wf; grind
  | andr a b xs ys bl prem1 prem2 ih =>
    simp_all; specialize ih m wf; grind
  | orl a b xs ys bl prem1 prem2 ih =>
    simp_all; specialize ih m wf; grind
  | orr a b xs ys bl prem ih =>
    simp_all; specialize ih m wf; grind
  | impr a b xs ys bl prem ih => --tahame et a b oleks t,a on f u, b t, u
    --specialize ih m wf
    apply eval_imp_righ_wo_ys_t
    simp_all
    have ih' := ih m wf
    rcases ih' with (h₁ | ⟨x, h₂, xtv⟩ ) | h₂
    . right
      rw [eval_imp_true_iff]
      simp_all
      generalize hatt : m.branch.attach = ts
      induction ts with
      | nil => simp_all
      | cons m' ms ms_ih =>
        specialize ih m' (by grind)
        sorry
    . left
      rcases h₂ with x_xs | ⟨x_bl, h, _, _⟩
      . left; grind
      . right
        rw [eval_imp_false_iff] at xtv
        use x_bl; simp_all
        rw [evalBlocked_false_iff]
        sorry
    . right
      sorry

  | impl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp_all
    specialize ih₁ m wf; specialize ih₂ m wf
    rcases ih₁ with (ih₁ | (ih₁ | ih₁) )| ih₁ | ih₁
    . left; left; right
      simp_all
    . sorry

    left; left; left
    rw [eval_imp_false_iff]
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
    specialize ih m wf
    rcases ih with (ih₁ | ( ih₁) )| ih₁ | ih₁
    . left; left; apply_assumption
    . left; right; apply_assumption
    . right; left
      apply b_true_then_imp_true_branch wf ih₁
    . right; right; apply_assumption
