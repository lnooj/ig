import Logic.MultiSuccCorsiTassi.Core
--import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
--import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke
--import Logic.MultiSuccCorsiTassi.MultiSuccCorsiTassi
import Logic.MultiSuccCorsiTassi.Proof

namespace multiSucc
open multiSucc




/- TODO: problem with showing impr correctness, because of blocked implication semantics -/
theorem proof_correctness :
  ∀ (s : Sequent) (_ : Proof s) (m : Model) (_ : m.wf), s.evalP m ≠ TV.f := by
  intro s pf m wf
  induction pf generalizing m with
  | ax x xs ys bl hxs hys =>
    simp
    have hxsM : Form.atoms x ∈ (↑xs : Multiset Form) := by simpa
    if xtv : x ∈ m.world.forced then
      suffices evalSucc ↑ys m = TV.t by grind
      apply evalSucc_true hys
      grind
    else if xtv' : x ∈ m.world.rejected then grind
    else grind
  | botl xs ys bl =>
    have hAnt : evalAnt ({ Γa := ↑(⊥ :: xs), Γb := ↑bl, Δ := ↑ys } : Sequent).Γ m = TV.f := by
      apply evalAnt_false (f := ⊥)
      · simp [Sequent.Γ]
      · simp
    grind
  | botr xs ys prem => simp_all
  | andl a b xs ys bl prem ih =>
    simp_all
    specialize ih m wf
    intro h
    apply ih
    intro x hx
    rcases hx with (⟨rfl, _⟩ | ⟨rfl, _⟩ | hx) | hbl
    · have hab : (a ∧∧ b).eval m = TV.t := h (a ∧∧ b) (by simp)
      rw [evaluate_and, conjTV_true_iff] at hab
      exact hab.1
    · have hab : (a ∧∧ b).eval m = TV.t := h (a ∧∧ b) (by simp)
      rw [evaluate_and, conjTV_true_iff] at hab
      exact hab.2
    · exact h x (by simp [hx])
    · exact h x (by simp [hbl])
  | andr a b xs ys prem1 prem2 =>
    simp_all only [ne_eq, Sequent.evalP_false_iff]
    grind
  | orl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp_all only [ne_eq, Sequent.evalP_false_iff, not_and]
    simp_all
    specialize ih₁ m wf
    specialize ih₂ m wf
    intro h
    have hor : (a ∨∨ b).eval m = TV.t := h (a ∨∨ b) (by simp)
    rw [evaluate_or, disjTV_true_iff] at hor
    grind
  | orr a b xs ys prem =>
    simp_all
  | impr a b xs ys bl prem ih =>
    apply eval_imp_righ_wo_ys
    simp_all
    intro h₁ impF
    apply eval_imp_false_contradict at impF
    contrapose! ih
    simp_all
    rcases impF with ⟨m', m'_in, h₃, h₄⟩
    . use m'
      simp_all
      constructor
      . grind only [Model.all_wf]
      . intro x h; specialize h₁ x  h
        grind [Model.mono_all_true]

  | impl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp_all
    intro h₁
    specialize ih₁ m wf
    specialize ih₂ m wf
    have hImp : (a ⊃ b).eval m = TV.t := h₁ (a ⊃ b) (by simp)
    grind

  | afort a b xs ys bl prem ih =>
    simp
    simp at ih
    intro h₁ h₂
    specialize ih m wf h₁
    apply_assumption
    apply imp_false_then_b_false h₂ wf

#print axioms proof_correctness

/- test proof for only the truth value. Here ax case can currently not be proved -/
theorem proof_correctness' :
  ∀ (s : Sequent) (_ : Proof s) (m : Model) (_ : m.wf), s.evalP m = TV.t := by
  intro s pf m wf
  induction pf generalizing m with
  | ax x xs ys bl hxs hys =>
    simp
    have hxsM : Form.atoms x ∈ (↑xs : Multiset Form) := by simpa
    if xtv : x ∈ m.world.forced then
      suffices evalSucc ↑ys m = TV.t by grind
      apply evalSucc_true hys
      grind
    else if xtv' : x ∈ m.world.rejected then grind
    else sorry
  | botl xs ys bl =>
    have hAnt : evalAnt ({ Γa := ↑(⊥ :: xs), Γb := ↑bl, Δ := ↑ys } : Sequent).Γ m = TV.f := by
      apply evalAnt_false (f := ⊥)
      · simp [Sequent.Γ]
      · simp
    grind
  | botr xs ys prem => simp_all
  | andl a b xs ys bl prem ih =>
    simp_all; specialize ih m wf; grind
  | andr a b xs ys bl prem1 prem2 ih =>
    simp_all; specialize ih m wf; grind
  | orl a b xs ys bl prem1 prem2 ih =>
    simp_all; specialize ih m wf; grind
  | orr a b xs ys bl prem ih =>
    simp_all; specialize ih m wf; grind
  | impr a b xs ys bl prem ih =>
    apply eval_imp_righ_wo_ys_t
    simp_all
    have ih' := ih m wf
    rcases ih' with (h₁ | ⟨x, h₂, xtv⟩) | h₂
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
      . use x; grind
      . let x := x_bl.f ⊃ x_bl.g
        use x; grind
    . right
      grind [b_true_then_imp_true_branch]

  | impl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp_all
    specialize ih₁ m wf
    specialize ih₂ m wf
    rcases ih₁ with ⟨x, hx, hxf⟩ | ha | hys
    · left; use x; grind
    . rcases ih₂ with ⟨x, hx, hxf⟩ | hys
      · left
        sorry
      . right; exact hys
    · right; exact hys

  | afort a b xs ys bl prem ih =>
    simp_all
    specialize ih m wf
    rcases ih with ⟨x, hx, hxf⟩ | hb | hys
    . left; grind
    . right;  left; grind [b_true_then_imp_true_branch]
    . right; right; exact hys

end multiSucc
