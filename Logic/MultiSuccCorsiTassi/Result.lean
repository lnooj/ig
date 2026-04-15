import Logic.MultiSuccCorsiTassi.Proof
import Logic.MultiSuccCorsiTassi.Refutation

@[grind =]
theorem List.prodcut_eq_nil {α β : Type u} {xs : List α} {ys : List β} :
    xs.product ys = [] ↔ xs = [] ∨ ys = [] := by
  simp [product]; cases xs with simp_all


namespace multiSucc
open multiSucc

--deriving Repr
open Proof
open Refutation
--give sequent, hist, blocked
inductive Result (s : Sequent) (h : List Imp) where
| proof (ps : List (Proof s)) : ps ≠ [] → Result s h
| refutation (rf : List (Refutation s h)) : rf ≠ []  → Result s h

def Result.proofs : Result s h → List (Proof s )
| .proof pf _ => pf
| _ => []

def Result.refutations : Result s h → List (Refutation s h)
| .refutation rs _ => rs
| _ => []


def Proof.castSeq (x : Proof ⟨a₁, b₁, c₁⟩)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    Proof ⟨a₂, b₂, c₂⟩ := by subst_eqs; assumption

def Proof.castSeqList (x : List (Proof ⟨a₁, b₁, c₁⟩))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof ⟨a₂, b₂, c₂⟩) := by subst_eqs; assumption

@[simp, grind =]
theorem Proof.castSeqList_eq_nil : Proof.castSeqList x ha hb = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def Refutation.castSeq (x :  Refutation ⟨a₁, b₁, c₁⟩ h)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    Refutation ⟨a₂, b₂, c₂⟩ h' := by subst_eqs; exact x

def Refutation.castSeqList (x : List (Refutation ⟨a₁, b₁, c₁⟩ h))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Refutation ⟨a₂, b₂, c₂⟩ h') := by subst_eqs; exact x

@[simp, grind =]
theorem Refutation.castSeqList_eq_nil : Refutation.castSeqList x ha hb bb hh = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def Result.castSeq (x : Result ⟨a₁, b₁, c₁⟩ h)
  (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
  Result ⟨a₂, b₂, c₂⟩ h' := by subst_eqs; exact x


def Result.map
  (r : Result s h)
  (h' : List Imp)
  (f₁ : Proof s → Proof s')
  (f₂ :  Refutation s h → Refutation s' h') :
  Result s' h' :=
  match r with
  | .proof ps _ => .proof (ps.map f₁) (by simpa)
  | .refutation rs _ => .refutation (rs.map f₂) (by simpa)

def Result.map2proof (r₁ : Result s1 h1) (r₂ : Result s2 h2)
  (fproof : (Proof s1) →
           (Proof s2) →
           (Proof s'))
  (ref₁ : (Refutation s1 h1) → (Refutation s' h'))
  (ref₂ : (Refutation s2 h2) → (Refutation s' h')): Result s' h':=
  match r₁, r₂ with
  | .proof pf₁ _, .proof pf₂ _ => .proof ((List.product (Proof.castSeqList pf₁) (Proof.castSeqList pf₂ )).map (fproof).uncurry) (by simp; grind)
  | .refutation rs₁ _, .refutation rs₂ _ => .refutation ( rs₁.map ref₁ ++ rs₂.map ref₂) (by simp; grind only)
  | .refutation  rs _, _ => .refutation (rs.map ref₁) (by simpa)
  | _, .refutation rs _ => .refutation (rs.map ref₂) (by simpa)

#min_imports
