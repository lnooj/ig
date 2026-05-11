import Logic.Core
--import Logic.Syntax
import Logic.Helper
--import Logic.Display
import Logic.Kripke
--import Logic.MultiSuccCorsiTassi
import Logic.IG

namespace multiSucc
open multiSucc


theorem IG.soundness (s : Sequent) (p : IG s) :
  ∀ (m : Kripke), m.wf → s.evalP m ≠ TV.f := by
  intro m wf
  induction p generalizing m with
  | ax x xs ys bl hxs hys =>
    simp
    --have hxsM : Form.atoms x ∈ (↑xs : Multiset Form) := by simpa
    if xtv : x ∈ m.world.forced then grind
    else if xtv' : x ∈ m.world.rejected then grind
    else grind
  | botl xs ys bl =>
    have hAnt : evalAnt ({ Γ := ↑(⊥ :: xs), Θ := ↑bl, Δ := ↑ys } : Sequent).ant m = TV.f := by
      apply evalAnt_false (f := ⊥)
      · simp
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
      . grind only [Kripke.all_wf]
      . intro x h; specialize h₁ x  h
        grind [Kripke.mono_all_true]

  | impl a b xs ys bl prem1 prem2 ih₁ ih₂ =>
    simp
    intro h₁
    specialize ih₁ m wf
    specialize ih₂ m wf
    have hImp : (a ⊃ b).eval m = TV.t := h₁ (a ⊃ b) (by simp)
    simp at ih₁ ih₂
    grind

  | afort a b xs ys bl prem ih =>
    simp
    simp at ih
    intro h₁ h₂
    specialize ih m wf h₁
    apply_assumption
    apply imp_false_then_b_false h₂ wf

#print axioms IG.soundness
end multiSucc
