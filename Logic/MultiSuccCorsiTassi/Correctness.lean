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
  ∀ (s : Sequent) (_ : Proof s) (m : Model) (_ : m.wf), s.eval m ≠ TV.f := by
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
  | impr a b xs ys bl prem ih =>
    apply eval_imp_righ_wo_ys
    simp_all
    intro h₁ h₂ impF
    apply eval_imp_false_contradict at impF
    rcases impF with ⟨m', m'_in, h₃, h₄⟩
    specialize ih m' (by grind) h₃
    simp_all
    rcases ih with ⟨x, (_ | ⟨x, xbl, _, _⟩), xeval⟩
    . grind [Model.mono_all_true]
    . clear h₁ h₃ h₄
      contrapose xeval
      specialize h₂ x xbl
      sorry
      --exact evalBlocked_true_in_branch (i := x) (m := m) (m' := m') wf m'_in h₂

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

/- test proof for only the truth value. Here ax case can currently not be proved -/
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
    specialize ih₁ m wf
    specialize ih₂ m wf
    rcases ih₂ with h₂ | hys
    · rcases h₂ with hbf | hbl
      · rcases hbf with hb | hxs
        · rcases ih₁ with h₁ | hys
          · rcases h₁ with hxs | himp | hbl
            · exact Or.inl <| Or.inl <| Or.inr hxs
            · have hImpF : (a ⊃ b).eval m = TV.f := by
                rw [eval_imp_false_iff]
                right
                exact (evalBlocked_false_iff (x := ⟨a, b⟩) (m := m)).1 himp
              exact Or.inl <| Or.inl <| Or.inl hImpF
            · exact Or.inl <| Or.inr hbl
          · rcases hys with hat | hys
            · have hImpF : (a ⊃ b).eval m = TV.f := by
                rw [eval_imp_false_iff]
                left
                exact ⟨hat, hb⟩
              exact Or.inl <| Or.inl <| Or.inl hImpF
            · exact Or.inr hys
        · exact Or.inl <| Or.inl <| Or.inr hxs
      · exact Or.inl <| Or.inr hbl
    · exact Or.inr hys

  | afort a b xs ys bl prem ih =>
    simp_all
    specialize ih m wf
    rcases ih with (ih₁ | ih₁) | ih₁ | ih₁
    . left; left; apply_assumption
    . left; right; apply_assumption
    . right; left
      apply b_true_then_imp_true_branch wf ih₁
    . right; right; apply_assumption

end multiSucc
