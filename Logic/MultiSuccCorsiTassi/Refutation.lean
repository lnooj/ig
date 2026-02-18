import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke

namespace multiSucc
open multiSucc

-- all multi premise rules for proofs now need only one for refutation
-- give hist as well
inductive Refutation : List Imp → Sequent → Type
  -- ∀ x Γ,  Γ ⊬ Δ
  | ax :
    ∀ (xs ys: List Form), --should be list of atoms?
      (intersection : xs ∩ ys = []) →
      Refutation hs ⟨↑xs, ↑ys⟩
-- Γ ⊬ Δ → Γ ⊬ ⊥,Δ
  | botr :
    ∀ (xs ys : List Form),
      Refutation hs ⟨↑xs, ↑ys⟩ →
      Refutation hs ⟨↑xs, ↑(⊥ :: ys)⟩
  -- (Γ, a, b ⊬ Δ) → (Γ, a ∧ b ⊬ Δ)
  | andl :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation hs ⟨↑(a :: b :: xs), ↑ys⟩ →
      Refutation hs ⟨↑((a ∧∧ b) :: xs), ↑ys⟩
  -- (Γ ⊬ a, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₁ :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation hs ⟨↑xs, ↑(a :: ys)⟩ →
      Refutation hs ⟨↑xs, ↑((a ∧∧ b) :: ys)⟩
  -- (Γ ⊬ b, Δ) → (Γ ⊬ a ∧ b, Δ)
  | andr₂ :
    ∀ (a b : Form) (xs ys: List Form),
      Refutation hs ⟨↑xs, ↑(b :: ys)⟩ →
      Refutation hs ⟨↑xs, ↑((a ∧∧ b) :: ys)⟩
  -- (a, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₁ :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation hs ⟨↑(a :: xs), ↑ys⟩ →
    Refutation hs ⟨↑((a ∨∨ b) :: xs), ↑ys⟩
  -- (b, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ)
  | orl₂ :
    ∀ (a b : Form) (xs ys : List Form),
    Refutation hs ⟨↑(b :: xs), ↑ys⟩ →
    Refutation hs ⟨↑((a ∨∨ b) :: xs), ↑ys⟩
  -- (Γ ⊬ a, b, Δ) → (Γ ⊬ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation hs ⟨↑xs, ↑(a :: b :: ys)⟩ →
      Refutation hs ⟨↑xs, ↑(( a ∨∨ b) :: ys)⟩
  -- Γ ∩ Δ = ∅ → (a, Γ ⊬ b) →  Γ ⊬ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys: List Form),
      (intersection : xs ∩ ys = []) →
      Refutation (⟨a, b⟩ :: hs) ⟨↑(a :: xs), {b}⟩ →
      Refutation hs ⟨↑(xs), ↑((a ⊃ b) :: ys)⟩
  -- (a → b, Γ ⊬ a, Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₁ :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation hs ⟨↑((a ⊃ b) :: xs), ↑(a :: ys)⟩ →
      Refutation hs ⟨↑((a ⊃ b) :: xs), ↑ys⟩
  --  (b, Γ ⊬ Δ) → (a ⊃ b, Γ ⊬ Δ)
  | impl₂ :
    ∀ (a b : Form) (xs ys : List Form),
      Refutation hs ⟨↑((a ⊃ b) :: xs), ↑(a :: ys)⟩ →
      Refutation hs ⟨↑((a ⊃ b) :: xs), ↑ys⟩
  --  a ⊃ b ∈ hs → (Γ ⊬ b, Δ) → (Γ ⊬ a ⊃ b, Δ) TÄRNIGA IMP
  | afort :
    ∀ (a b : Form) (xs ys : List Form),
      (hhs : ⟨a, b⟩ ∈ hs) → --or (hhs : a ∈ hs.map .left) →
      Refutation hs ⟨↑xs, ↑(b :: ys)⟩ →
      Refutation hs ⟨↑xs, ↑((a ⊃ b) :: ys)⟩
