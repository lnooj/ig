import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke
import Logic.MultiSuccCorsiTassi.MultiSuccCorsiTassi

namespace multiSucc
open multiSucc

theorem CM_ertyu : ∀ cm : CM, cm.world.forced ∩ cm.world.unforced = ∅ := by sorry
theorem CM_true_in_future : ∀ (cm : CM), cm.world.forced ∈ cm.branch.map (λ child ↦ child.world.forced) := by sorry


/-- If a sequent gets  countermodels as results, each of those models must refute the sequent  -/
theorem CM_correctness :
  ∀ (s : Sequent) {capProof} {metaR1} (cms : List CM),
    automatedProof s.toSeq4 s.toSeq4.cap.card capProof metaR1 = Result.cm cms →
    ∀ cm ∈ cms, evalSeq s cm = TV.f := by
    intro s proof r1 cms res c h
    simp [evalSeq, conjTV, disjTV, evaluate]; sorry
