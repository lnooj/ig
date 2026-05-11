import Logic.IG
import Logic.RIG

@[grind =]
theorem List.prodcut_eq_nil {α β : Type u} {xs : List α} {ys : List β} :
    xs.product ys = [] ↔ xs = [] ∨ ys = [] := by
  simp [product]; cases xs with simp_all


namespace multiSucc
open multiSucc

--deriving Repr
open IG
open RIG
--give sequent, hist, blocked
inductive Result (s : Sequent) (h : List Imp) where
| proof (ps : List (IG s)) : ps ≠ [] → Result s h
| refutation (rf : List (RIG s h)) : rf ≠ []  → Result s h

def Result.proofs : Result s h → List (IG s )
| .proof pf _ => pf
| _ => []

def Result.refutations : Result s h → List (RIG s h)
| .refutation rs _ => rs
| _ => []


def IG.castSeq (x : IG ⟨a₁, b₁, c₁⟩)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    IG ⟨a₂, b₂, c₂⟩ := by subst_eqs; assumption

def IG.castSeqList (x : List (IG ⟨a₁, b₁, c₁⟩))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (IG ⟨a₂, b₂, c₂⟩) := by subst_eqs; assumption

@[simp, grind =]
theorem IG.castSeqList_eq_nil : IG.castSeqList x ha hb = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def RIG.castSeq (x :  RIG ⟨a₁, b₁, c₁⟩ h)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    RIG ⟨a₂, b₂, c₂⟩ h' := by subst_eqs; exact x

def RIG.castSeqList (x : List (RIG ⟨a₁, b₁, c₁⟩ h))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (RIG ⟨a₂, b₂, c₂⟩ h') := by subst_eqs; exact x

@[simp, grind =]
theorem RIG.castSeqList_eq_nil : RIG.castSeqList x ha hb bb hh = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def Result.castSeq (x : Result ⟨a₁, b₁, c₁⟩ h)
  (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hc : c₁ = c₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
  Result ⟨a₂, b₂, c₂⟩ h' := by subst_eqs; exact x


def Result.map
  (r : Result s h)
  (h' : List Imp)
  (f₁ : IG s → IG s')
  (f₂ :  RIG s h → RIG s' h') :
  Result s' h' :=
  match r with
  | .proof ps _ => .proof (ps.map f₁) (by simpa)
  | .refutation rs _ => .refutation (rs.map f₂) (by simpa)

def Result.map2proof (r₁ : Result s1 h1) (r₂ : Result s2 h2)
  (fproof : (IG s1) →
           (IG s2) →
           (IG s'))
  (ref₁ : (RIG s1 h1) → (RIG s' h'))
  (ref₂ : (RIG s2 h2) → (RIG s' h')): Result s' h':=
  match r₁, r₂ with
  | .proof pf₁ _, .proof pf₂ _ => .proof ((List.product (IG.castSeqList pf₁) (IG.castSeqList pf₂ )).map (fproof).uncurry) (by simp; grind)
  | .refutation rs₁ _, .refutation rs₂ _ => .refutation ( rs₁.map ref₁ ++ rs₂.map ref₂) (by simp; grind only)
  | .refutation  rs _, _ => .refutation (rs.map ref₁) (by simpa)
  | _, .refutation rs _ => .refutation (rs.map ref₂) (by simpa)

#min_imports
