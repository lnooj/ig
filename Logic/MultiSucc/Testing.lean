import Mathlib.Data.Nat.Cast.Synonym

structure Seq4Proof where
  x : ℕ

def Seq4Proof.weight (p : Seq4Proof) : ℕᵒᵈ × ℕ := ⟨p.x, p.x + 1⟩
def Seq4Proof.r : Seq4Proof → ℕ := (·.weight.fst)
def Seq4Proof.n : Seq4Proof → ℕ := (·.weight.snd)

@[simp]
instance : SizeOf (OrderDual ℕ) where
  sizeOf n := OrderDual.ofDual n

#eval sizeOf ((10 : Nat))

#eval sizeOf (10 : Nat)
#eval sizeOf (OrderDual.toDual (10 : Nat))

#eval Lean.versionString

@[simp]
theorem Seq4Proof.sizeOf_lt_iff (a b : Seq4Proof) :
      Prod.Lex (fun a₁ a₂ => a₂ < a₁) (fun x1 x2 => x2 < x1) b.weight a.weight
    ↔ a.r > b.r ∨ a.r = b.r ∧ a.n < b.n := by
  simp [r, n, Prod.lex_def]; rw [eq_comm]; rfl


def f (p : Seq4Proof) : ℕ :=
  if p.x = 0 then
    0
  else
    f ⟨p.x - 1⟩
termination_by p.weight
decreasing_by
  simp
  omega
