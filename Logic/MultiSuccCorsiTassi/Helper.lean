import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.List.ProdSigma

import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Refutation

def List.findSome {α β : Type*} (xs : List α) (p : α → Bool) (f : (a : α) → p a → β) (h : ∃ a ∈ xs, p a) : β :=
  xs.findSome? (λ a ↦ if h' : p a then some (f a h') else none ) |>.get (by simp_all)

def List.mapNonempty {α β : Type*} (f : α → β) (xs : List α) (h : xs ≠ []) : {ys : List β // ys ≠ []} :=
  ⟨xs.map f, by simp [h]⟩

def List.unattach_ne (hnotempty : ¬rfs = []) : ¬rfs.unattach = [] := by
  intro h
  have : rfs.unattach = [] → rfs = [] := by apply List.map_eq_nil_iff.mp
  grind

namespace multiSucc
open multiSucc

/-! # choices -/
-- [[1,2] [3] [4,5]] = [[1,3,4] [1,3,5] [2,3,4] [2,3,5]]
def choices : List (List α) → List (List α)
| [] => []
| [x] => x.map ([·])
| x::y::xs => x.product (choices (y::xs)) |>.map (fun ⟨a, as⟩ ↦ a :: as)

@[simp, grind =]
theorem product_length {as : List α} {bs : List β} :
    (as.product bs).length = as.length * bs.length := by
  simp [List.product, List.map_const']

attribute [grind =] List.pair_mem_product

@[simp, grind =]
theorem choices_length {xs : List (List α)} :
    (choices xs).length = if xs = [] then 0 else (xs.map (·.length)).prod := by
  fun_induction choices with grind
@[simp, grind .]
theorem mem_choices_length {xs : List (List α)} {x} (h : x ∈ choices xs) :
    x.length = xs.length := by
  fun_induction choices generalizing x with grind

@[grind =, simp]
theorem products_eq_nil {xs : List (List α)} : choices xs = [] ↔ xs = [] ∨ [] ∈ xs := by
  grind [List.eq_nil_iff_length_eq_zero, choices_length, List.prod_eq_zero_iff, List.length_eq_zero_iff]


@[grind ., simp]
theorem mem_of_mem_choices {xss : List (List α)} {xs : List α} {c : List α}
  (hc : c ∈ choices xss) (hxs : xs ∈ xss) : ∃ x ∈ xs, x ∈ c := by
  induction xss generalizing c with
  | nil =>
      cases hxs
  | cons x xss ih =>
      cases xss with
      | nil =>
          simp [choices] at hc hxs
          rcases hc with ⟨y, hy, rfl⟩
          subst hxs
          exact ⟨y, hy, by simp⟩
      | cons y ys =>
          rw [choices] at hc
          simp_all
          grind

@[grind =]
theorem mem_choices {xs : List (List α)} {x} :
      x ∈ choices xs
    ↔ ¬x = [] ∧ x.length = xs.length ∧
      ∀ i, (h : i < x.length) → (h' : i < xs.length) → x[i]'h ∈ xs[i]'h' := by
  fun_induction choices generalizing x with
  | case1 => grind
  | case2 y =>
    constructor
    · grind
    · simp only [List.length_cons, List.length_nil]; grind [cases List]
  | case3 y y' xs ih =>
    constructor
    · grind
    · simp only [List.length_cons]; intro ⟨_, _, h⟩; have := h 0; grind [Prod.exists, cases List]

/-! # pickproof -/
/-- Picks only proofs (α) if any, else returns all the refutations (β)
if .inl (proof) is returned, it is never empty, if .inr is returned, it is the length of the original input list -/
def pickProof : List (α ⊕ β) → List (α) ⊕ List (β)
  | [] => .inr [] --empty refutation
  | x::xs =>
    match x, pickProof xs with
    | .inl a, .inl as => .inl (a::as)
    | .inl a, .inr _  => .inl [a] --single proof
    | .inr _, .inl as => .inl as
    | .inr b, .inr bs => .inr (b::bs) --all refutations

attribute [local grind =] List.filterMap_eq_nil_iff in
@[grind .]
theorem pickProof_eq {xs : List (α ⊕ β)} {ys : List α ⊕ List β} :
    pickProof xs = ys ↔
      match ys with
      | .inl as => xs.filterMap Sum.getLeft? = as ∧ as ≠ []
      | .inr bs => xs = bs.map .inr := by
  fun_induction pickProof generalizing ys <;> rcases ys <;> simp_all <;> try grind [cases List]

@[simp, grind =]
theorem pickProof_eq_inl {xs : List (α ⊕ β)} {ys : List α} :
    pickProof xs = .inl ys ↔ xs.filterMap Sum.getLeft? = ys ∧ ¬ys = [] := by simp [pickProof_eq]
@[simp, grind =]
theorem pickProof_eq_inr {xs : List (α ⊕ β)} {ys : List β} :
    pickProof xs = .inr ys ↔ xs = ys.map .inr := by simp [pickProof_eq]

/-! # other -/
theorem unattach_flatten_notEmpty
(pf : List { pfs // pfs ≠ [] })
(h : pickProof impRApplications = Sum.inl pf)
: (pf.unattach).flatten ≠ [] := by
  simp [pickProof_eq_inl] at h
  rcases h with ⟨h₁, h₂⟩
  cases pf with
  | nil =>
      cases h₂ rfl
  | cons x xs => simp [x.property]

@[grind ., simp]
theorem List.findSome?_ne_none_of_mem {xs : List α} {f : α → Option β} {x : α}
  (hx : x ∈ xs) (hfx : f x ≠ none) : xs.findSome? f ≠ none := by grind


@[grind ., simp]
theorem Subtype.prop_map
(rfs : List { rf : List ((a : Form) ×
          (b : Form) ×
            Refutation { Γ := ↑(a :: List.map Form.atom as ++ List.map Imp.toForm block), Θ := ∅, Δ := {b} }
              ({ f := a, g := b } :: hist)) // rf ≠ [] }) : [] ∉ rfs.unattach := by
  simp_all only [ne_eq, List.mem_unattach, not_true_eq_false, IsEmpty.exists_iff, not_false_eq_true]



end multiSucc

#min_imports
