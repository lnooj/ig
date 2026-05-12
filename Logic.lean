import Logic.Completeness
import Logic.Core
import Logic.Soundness
import Logic.Display
import Logic.Helper
import Logic.Kripke
import Logic.MultiSuccCorsiTassi
import Logic.IG
import Logic.RIG
import Logic.Result
import Logic.Syntax
import Logic.Termination

namespace multiSucc

theorem Completeness (s : Sequent) (h : ∀ (m : Kripke), m.wf → s.evalR [] m ≠ TV.f) :
    Nonempty (IG s) := by
  contrapose! h
  let res := automatedProof s.toSeq4 s.toSeq4.cap.card (by simp) (by simp [Sequent.toSeq4])
  rcases res with ⟨(_ | ⟨p, ps⟩), h'⟩ | ⟨(_ | ⟨r, rs⟩), h'⟩
  · contradiction
  · have : s.toSeq4.toSeq = s := by
      simp [Sequent.toSeq4, Sequent.Γ_getList, Sequent.Θ_getList, Sequent.Δ_getList]
    rw [this] at p
    absurd h
    simp
    use p
  · contradiction
  have := RIG.completeness _ r
  simp_all
  simp [Sequent.toSeq4, Sequent.Γ_getList, Sequent.Θ_getList, Sequent.Δ_getList] at this
  obtain ⟨⟨h₁, h₃⟩, h₂⟩ := this
  use r.getCM, r.cm_wf
  grind

theorem Completeness' (s : Sequent) (hp : IsEmpty (IG s)) :
    ∃ (r : RIG s h), s.evalR h r.getCM = TV.f := by
  sorry

theorem Completeness (s : Sequent) (r : RIG s h) :
    s.evalR h r.getCM = TV.f := by
  sorry
