import Logic.MultiSuccCorsiTassi.Helper

namespace multiSucc
open multiSucc

inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x ++ Δ
  | ax :
    ∀ (x : Atom) (xs ys : List Form) (bl : List Imp),
      (hxs : .atoms x ∈ xs) →
      (hys : .atoms x ∈ ys) →
      Proof ⟨↑xs, ↑bl, ↑ys⟩
  -- ∀ Δ Γ, (⊥, Γ ⊢ Δ)
  | botl :
    ∀ (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(⊥ :: xs), ↑bl, ↑ys⟩
  | botr :
    ∀ (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑ys⟩ →
      Proof ⟨↑xs, ↑bl, ↑(⊥ :: ys)⟩
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(a :: b :: xs), ↑bl, ↑ys⟩ →
      Proof ⟨↑((a ∧∧ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(a :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    Proof ⟨↑(a :: xs), ↑bl, ↑ys⟩ →
    Proof ⟨↑(b :: xs), ↑bl, ↑ys⟩ →
    Proof ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(a :: b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑(( a ∨∨ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ)
  | impr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑(a :: xs ++ bl.map Imp.toForm), {}, {b}⟩ →
      Proof ⟨↑(xs), ↑bl, ↑((a ⊃ b) :: ys)⟩
  -- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ)
  | impl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑(⟨a, b⟩ :: bl), ↑(a :: ys)⟩ →
      Proof ⟨↑(b :: xs ), ↑bl, ↑ys⟩ →
      Proof ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩
  -- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ)
  | afort :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      Proof ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      Proof ⟨↑xs, ↑bl, ↑((a ⊃ b) :: ys)⟩

end multiSucc
#min_imports
