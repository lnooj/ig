import Logic.Core

namespace multiSucc
open multiSucc

/-- `IG` is the inductive proof rules of Corsi and Tassi -/
inductive IG : Sequent → Type
  /-- ∀ x Γ, x ++ Γ ⊢ x ++ Δ -/
  | ax :
    ∀ (x : Atom) (xs ys : List Form) (bl : List Imp),
      (hxs : .atom x ∈ xs) →
      (hys : .atom x ∈ ys) →
      IG ⟨↑xs, ↑bl, ↑ys⟩
  /-- ∀ Δ Γ, (⊥, Γ ⊢ Δ) -/
  | botl :
    ∀ (xs ys : List Form) (bl : List Imp),
      IG ⟨↑(⊥ :: xs), ↑bl, ↑ys⟩
  /-- ∀ Δ Γ, (Γ ⊢ Δ) → (Γ ⊢ ⊥, Δ) -/
  | botr :
    ∀ (xs ys : List Form) (bl : List Imp),
      IG ⟨↑xs, ↑bl, ↑ys⟩ →
      IG ⟨↑xs, ↑bl, ↑(⊥ :: ys)⟩
  /-- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ) -/
  | andl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑(a :: b :: xs), ↑bl, ↑ys⟩ →
      IG ⟨↑((a ∧∧ b) :: xs), ↑bl, ↑ys⟩
  /-- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ) -/
  | andr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑xs, ↑bl, ↑(a :: ys)⟩ →
      IG ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      IG ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩
  /-- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ) -/
  | orl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    IG ⟨↑(a :: xs), ↑bl, ↑ys⟩ →
    IG ⟨↑(b :: xs), ↑bl, ↑ys⟩ →
    IG ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩
  /-- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ) -/
  | orr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑xs, ↑bl, ↑(a :: b :: ys)⟩ →
      IG ⟨↑xs, ↑bl, ↑(( a ∨∨ b) :: ys)⟩
  /-- ∀ a b Γ Δ, (a, Γ ⊢ b) → ( Γ ⊢ a → b, Δ) -/
  | impr :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑(a :: xs ++ bl.map Imp.toForm), {}, {b}⟩ →
      IG ⟨↑(xs), ↑bl, ↑((a ⊃ b) :: ys)⟩
  /-- ∀ a b Γ Δ, (a → b, Γ ⊢ a, Δ) → (b, Γ ⊢ Δ) → (a → b, Γ ⊢ Δ) -/
  | impl :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑xs, ↑(⟨a, b⟩ :: bl), ↑(a :: ys)⟩ →
      IG ⟨↑(b :: xs ), ↑bl, ↑ys⟩ →
      IG ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩
  /-- ∀ a b Γ Δ, (Γ ⊢ b, Δ) → (Γ ⊢ a → b, Δ) -/
  | afort :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      IG ⟨↑xs, ↑bl, ↑(b :: ys)⟩ →
      IG ⟨↑xs, ↑bl, ↑((a ⊃ b) :: ys)⟩

end multiSucc
