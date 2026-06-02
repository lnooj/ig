import Logic.Core

namespace multiSucc
open multiSucc

/-- `RIG` is the inductive Refutation rules -/
inductive RIG : Sequent → (hs : List Imp) → Type
  /-- ∀ x Γ,  Γ ⊬ Δ -/
  | ax hs :
    ∀ (as bs: List Atom) (bl : List Imp), --xs: blocked
      (intersection : as ∩ bs = []) →
      RIG ⟨↑(as.map Form.atom), ↑bl, ↑(bs.map Form.atom)⟩ hs
  /-- Γ ⊬ Δ → Γ ⊬ ⊥,Δ -/
  | botr hs :
    ∀ (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑xs, ↑bl, ↑ys⟩ hs →
      RIG ⟨↑xs, ↑bl, ↑(⊥ :: ys)⟩ hs
  /-- (Γ, a, b ⊬ Δ) → (Γ, a ∧ b ⊬ Δ) -/
  | andl hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑(a :: b :: xs), ↑bl, ↑ys⟩ hs →
      RIG ⟨↑((a ∧∧ b) :: xs), ↑bl, ↑ys⟩ hs
  /-- (Γ ⊬ a, Δ) → (Γ ⊬ a ∧ b, Δ) -/
  | andr₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑xs, ↑bl, ↑(a :: ys)⟩ hs →
      RIG ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩ hs
  /-- (Γ ⊬ b, Δ) → (Γ ⊬ a ∧ b, Δ) -/
  | andr₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑xs, ↑bl, ↑(b :: ys)⟩ hs →
      RIG ⟨↑xs, ↑bl, ↑((a ∧∧ b) :: ys)⟩ hs
  /-- (a, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ) -/
  | orl₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    RIG ⟨↑(a :: xs), ↑bl, ↑ys⟩ hs →
    RIG ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩ hs
  /-- (b, Γ ⊬ Δ) → (a ∨ b, Γ ⊬ Δ) -/
  | orl₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
    RIG ⟨↑(b :: xs), ↑bl, ↑ys⟩ hs →
    RIG ⟨↑((a ∨∨ b) :: xs), ↑bl, ↑ys⟩ hs
  /-- (Γ ⊬ a, b, Δ) → (Γ ⊬ a ∨ b, Δ) -/
  | orr hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑xs, ↑bl, ↑(a :: b :: ys)⟩ hs →
      RIG ⟨↑xs, ↑bl, ↑(( a ∨∨ b) :: ys)⟩ hs
  /-- Γ ∩ Δ = ∅ →
   (a₁, Γ ⊬ b₁) | ...| (a₉, Γ ⊬ b₉) →
   Γ ⊬ a₁ ⊃ b₁, a₂ ⊃ b₂ ... a₉ ⊃ b₉ Δ) -/
  | impr hs :
    ∀ (as bs : List Atom) (ys: List Imp) (bl : List Imp),
      (intersection : as ∩ bs = []) →
      ((a b : Form) → ⟨a,b⟩ ∈ ys →  RIG ⟨↑(a :: (as.map .atom) ++ (bl.map Imp.toForm)), {}, {b}⟩ (⟨a, b⟩ :: hs )) →
      RIG ⟨↑(as.map Form.atom), ↑bl, ↑((bs.map Form.atom) ++ (ys.map Imp.toForm))⟩ hs
  /-- (a ⊃ b, Γ ⊬ a, Δ) → (a ⊃ b, Γ ⊬ Δ) -/
  | impl₁ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑ xs, ↑( ⟨a, b⟩ :: bl), ↑(a :: ys)⟩ hs →
      RIG ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩ hs
  /--  (b, Γ ⊬ Δ) → (a ⊃ b, Γ ⊬ Δ) -/
  | impl₂ hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      RIG ⟨↑(b :: xs), ↑bl, ↑ys⟩ hs →
      RIG ⟨↑((a ⊃ b) :: xs), ↑bl, ↑ys⟩ hs
  /--  a ⊃ b ∈ hs → (Γ ⊬ b, Δ) → (Γ ⊬ a ⊃ b, Δ) -/
  | afort hs :
    ∀ (a b : Form) (xs ys : List Form) (bl : List Imp),
      (hhs : ⟨a, b⟩ ∈ hs) → --or (hhs : a ∈ hs.map .left) →
      RIG ⟨↑xs, ↑bl, ↑(b :: ys)⟩ hs →
      RIG ⟨↑xs, ↑bl, ↑((a ⊃ b) :: ys)⟩ hs


end multiSucc
