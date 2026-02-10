import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw

import Logic.SingleSuccDyckhoff.Core
import Logic.SingleSuccDyckhoff.Helper
import Logic.SingleSuccDyckhoff.Display
import Logic.SingleSuccDyckhoff.Syntax

namespace singleSucc
open singleSucc



/-
imp₁ imp₂ imp₃ imp₄ (imp₀) are defined to help with termination and looping prevention (paper by Roy Dyckhoff)

 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (a : Form) (xs : List Form) , --TRY THIS WAY, GIVE PROOF OF INCLUSION
      (h : a ∈ xs) →
      Proof (.seq ↑(xs) a)
  -- ∀ x Γ, (⊥, Γ ⊢ x)
  | botl :
    ∀ (x : Form) (xs : List Form),
      Proof (.seq ↑( ⊥ :: xs) x)
/-     -- ∀ Γ, ( ⊥, Γ ⊢ ⊥)
  | botr :
    ∀ (xs : List Form),
      (h : ⊥ ∈ xs) →
      Proof (.seq ↑xs ⊥) -/
  -- ∀ a b c Γ, (Γ, a, b ⊢ c) → (Γ, a ∧ b ⊢ c)
  | andl :
    ∀ (a b g : Form) (xs : List Form),
      Proof (.seq ↑(a :: b :: xs) g) →
      Proof (.seq ↑((a ∧∧ b) :: xs) g)
  -- ∀ a b c Γ, (Γ ⊢ a) → (Γ ⊢ b) → (Γ ⊢ a ∧ b)
  | andr :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq ↑xs a) →
      Proof (.seq ↑xs b) →
      Proof (.seq ↑xs (a ∧∧ b))
  -- ∀ a b c Γ, (a, Γ ⊢ c) → (b, Γ ⊢ c) → (a ∨ b, Γ ⊢ c)
  | orl :
    ∀ (a b g : Form) (xs : List Form),
    Proof (.seq ↑(a :: xs) g) →
    Proof (.seq ↑(b :: xs) g) →
    Proof (.seq ↑((a ∨∨ b) :: xs) g)
  -- ∀ a b Γ, (Γ ⊢ a) → (Γ ⊢ a ∨ b)
  | orr₁ :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq ↑xs a) →
      Proof (.seq ↑xs (a ∨∨ b))
  -- ∀ a b Γ, (Γ ⊢ b) → (Γ ⊢ a ∨ b)
  | orr₂ :
    ∀ (a b : Form) (xs : List Form),
      Proof (.seq ↑xs b) →
      Proof (.seq ↑xs (a ∨∨ b))

  -- a is .bot IS THIS RULE NECESSARY? based on paper p800 proof e.iv
  | impl₀ :
    ∀ (b g : Form) (xs : List Form),
      Proof (.seq ↑xs g) →
      Proof (.seq ↑((⊥ ⊃ b) :: xs) g)
  -- a is atomic
  -- ∀ a b g Γ, (a, b, Γ ⊢ g) → (a → b, a, Γ ⊢ g)
  | impl₁ :
    ∀ (a : Atom) (b g : Form) (xs : List Form), --HERE ALSO NEED PROOF OF a ∈ xs
      (h : (.atoms a) ∈ xs) →
      Proof (.seq ↑(b :: xs) g) →
      Proof (.seq ↑(((.atoms a) ⊃ b) :: xs) g)
  -- implications left side is and operation
  -- ∀ c d b g Γ, (c ⊃ (d ⊃ b), Γ ⊢ g) → ((c ∧∧ d) ⊃ b, Γ ⊢ g)
  | impl₂ :
    ∀ (c d b g : Form) (xs : List Form),
      Proof (.seq ↑((c ⊃ (d ⊃ b)) :: xs) g) →
      Proof (.seq ↑(((c ∧∧ d) ⊃ b) :: xs) g)
  -- left side is or op
  -- ∀ c d b g Γ, (c ⊃ b, d ⊃ b, Γ ⊢ g) → ((c ∨∨ d) ⊃ b, Γ ⊢ g)
  | impl₃ :
    ∀ (c d b g : Form) (xs : List Form),
      Proof (.seq ↑((c ⊃ b) :: (d ⊃ b) :: xs) g) →
      Proof (.seq ↑(((c ∨∨ d) ⊃ b) :: xs) g)
  -- left side is imp op
  -- ∀ c d b g Γ, ( d ⊃ b, Γ ⊢ c ⊃ d) → (b, Γ ⊢ g) → ((c ⊃ d) ⊃ b, Γ ⊢ g)
  | impl₄ :
    ∀ (c d b g : Form) (xs : List Form),
      Proof (.seq ↑((d ⊃ b) :: xs) (c ⊃ d)) →
      Proof (.seq ↑( b :: xs) g) →
      Proof (.seq ↑(((c ⊃ d) ⊃ b) :: xs) g)
  -- ∀ a b Γ, (a, Γ ⊢ b) → (Γ ⊢ a → b)
  | impr :
    ∀ (a b : Form) (xs  : List Form),
      Proof (.seq ↑(a :: xs) b) →
      Proof (.seq ↑xs (a ⊃ b))
open Proof


@[simp]
def Seq4Proof.toSeq : Seq4Proof → Sequent
| .seq4 atoms forms imps aimps g => Sequent.seq (Multiset.ofList ((atoms.map Form.atoms) ++ forms ++ imps ++ aimps)) g

def Sequent.toSeq4 : Sequent → Seq4Proof
| .seq Δ G => Seq4Proof.seq4 [] (Multiset.sort Δ LE.le) [] [] G

def Proof.castSeqList (x : List (Proof (Sequent.seq (Multiset.ofList a₁) g))) (h : Multiset.ofList a₁ = Multiset.ofList a₂ := by simp only [Multiset.coe_eq_coe]; grind) :
  List (Proof (Sequent.seq (Multiset.ofList a₂) g)) := by rw [h] at x; exact x

@[simp]
lemma multiset_ofList_map_append_singleton(f : α → β) (xs : List α) (x : α) :
  (Multiset.ofList (xs.map f ++ [f x])) = Multiset.ofList (xs.map f) + {f x} := by
  rw [←Multiset.coe_singleton, ←Multiset.coe_add]

lemma sequent_size_add_singleton (as : List Atom) (imps : List Form) (b : Form) (c : Nat) :
  Multiset.map Form.weight ↑(List.map Form.atoms as ++ b :: imps) + {c}
  = Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps) + {c} + {b.weight} := by
    rw [← List.singleton_append]; simp only [Multiset.map_coe, List.map_append, List.map_singleton];
    rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.add_comm (Multiset.ofList [b.weight])];
    rw [←Multiset.coe_add, Multiset.coe_singleton]; grind

--dont know how to show this
lemma dershowits_simp {first last a b : List Form} {g : Form}:
  (Multiset.map Form.weight (↑(first ++ a ++ last) ) + {g.weight}).IsDershowitzMannaLT
  (Multiset.map Form.weight (↑(first ++ b ++ last)) + {g.weight})  =
    (Multiset.map Form.weight a).IsDershowitzMannaLT (Multiset.map Form.weight b):= by sorry


def firstImpPremisePresent (imps : List Form) (atoms : List Atom) : Option Form :=
  match imps with
  | [] => (none)
  | (Form.imp (.atoms a) b) :: imps' =>
      if a ∈ atoms then
        (some (.atoms a ⊃ b))
      else
        firstImpPremisePresent imps' atoms
  | _ :: imps' =>
      firstImpPremisePresent imps' atoms

lemma firstImpPremisePresent_sound :
  firstImpPremisePresent imps atoms = (some f) →
  ∃ a b,
    f = (Form.imp (.atoms a) b) ∧
    f ∈ imps ∧
    a ∈ atoms := by
  fun_induction firstImpPremisePresent <;> grind


lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl


def automatedProof (s : Seq4Proof) : List (Proof s.toSeq) :=
  match s with
  | .seq4 as forms imps aimps g =>
    match g with
    | .atoms g /- | ⊥ -/ =>  -- check if we have axiom
      if h : g ∈ as then
        by -- find atomicproofs
        simp only [Seq4Proof.toSeq]
        exact dbg_trace "axiom rule applied"; [ax (.atoms g) ((as.map .atoms) ++ forms ++ imps ++ aimps) (by grind)]

      else -- no axiom, continue opening up left side
        match forms with
        | [] =>  --only imps remain
          match imps with
          | [] =>
            match impO : firstImpPremisePresent aimps as with
            | none => []
            | some (.imp (.atoms a ) b) => by
              have sound := firstImpPremisePresent_sound impO
              set rest := aimps.erase (Form.imp (.atoms a) b)

              have premise := automatedProof (.seq4 as [b] [] rest (.atoms g))
              simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢

              have proof := List.map ((impl₁ a b (.atoms g) (as.map .atoms ++ rest) ) (by grind)) (Proof.castSeqList premise )
              apply Proof.castSeqList proof
            | some _ => []
          | (.imp a b ):: imps' => -- apply four imp rules
            match a with
            | .atoms a => -- put to aimps
              Proof.castSeqList (automatedProof (.seq4 as [] imps' ((.imp (.atoms a) b):: aimps) (.atoms g))) (by simp; grind)
            | .and c d => by
              have h := automatedProof (.seq4 as [] ((c ⊃ (d ⊃ b))::imps') (aimps) (.atoms g)) --put them straight into imps list
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₂ c d b (.atoms g) ((as.map .atoms) ++ imps' ++ aimps)) (Proof.castSeqList h )
              apply Proof.castSeqList proofs
            | .or c d => by
              have h := automatedProof (.seq4 as [] ((c ⊃ b) :: (d ⊃ b) :: imps') (aimps) (.atoms g)) --put them straight into imps list
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₃ c d b (.atoms g) ((as.map .atoms) ++ imps' ++ aimps)) (Proof.castSeqList h )
              apply Proof.castSeqList proofs
            | .imp c d => by
              have h₁ := automatedProof (.seq4 as [] ((d ⊃ b) :: imps') (aimps) (c ⊃ d)) --put them straight into imps list
              have h₂ := automatedProof (.seq4 as [b] imps' aimps (.atoms g))
              simp only [Seq4Proof.toSeq, List.append_nil] at h₁ h₂ ⊢
              have proofs := List.map (impl₄ c d b (.atoms g) ((as.map .atoms) ++ imps' ++ aimps)).uncurry (getPairs (Proof.castSeqList h₁ ) (Proof.castSeqList h₂ ))
              apply Proof.castSeqList proofs
            | .bot => by
              have h := automatedProof (.seq4 as [] imps' aimps (.atoms g))
              simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have proofs := List.map (impl₀ b (.atoms g) ((as.map .atoms) ++ imps' ++ aimps)) h
              apply Proof.castSeqList proofs
          | _ =>  dbg_trace "empty";[]
        | (.atoms a) :: forms' =>  --just put into atoms
          Proof.castSeqList (automatedProof (.seq4 (a :: as) forms' imps aimps (.atoms g)))
        | ⊥ :: forms' => by
          have proof := botl (.atoms g) ((as.map .atoms) ++ forms' ++ imps ++ aimps)
          simp only [Seq4Proof.toSeq]
          apply Proof.castSeqList [proof]
        | (.and a b) :: forms' => by
          have h := automatedProof (.seq4 as (a :: b :: forms') imps aimps (.atoms g))
          simp only [Seq4Proof.toSeq] at h ⊢
          have proofs := List.map (andl a b (.atoms g) ((as.map .atoms) ++ forms' ++ imps ++ aimps)) (Proof.castSeqList h)
          apply Proof.castSeqList proofs
        | (.or a b) :: forms' => by
          have h₁ := automatedProof (.seq4 as (a :: forms') imps aimps (.atoms g))
          have h₂ := automatedProof (.seq4 as (b :: forms') imps aimps (.atoms g))
          simp only [Seq4Proof.toSeq] at h₁ h₂ ⊢
          have proofs := List.map (orl a b (.atoms g) ((as.map .atoms) ++ forms' ++ imps ++ aimps)).uncurry (getPairs (Proof.castSeqList h₁) (Proof.castSeqList h₂))
          apply Proof.castSeqList proofs
        | (.imp a b) :: forms' => --just put into imps
          Proof.castSeqList (automatedProof (.seq4 as forms' ((a ⊃ b) :: imps) aimps (.atoms g)))
    | ⊥ => sorry
    | (.and a b) => by
      have h₁ := automatedProof (.seq4 as forms imps aimps a)
      have h₂ := automatedProof (.seq4 as forms imps aimps b)
      simp only [Seq4Proof.toSeq] at h₁ h₂ ⊢
      have proofs := List.map (andr a b ((as.map .atoms) ++ forms ++ imps ++ aimps)).uncurry (getPairs h₁ h₂)
      exact dbg_trace "AND rule applied"; proofs
    | (.or a b) => by
      have h₁ := automatedProof (.seq4 as forms imps aimps a)
      simp only [Seq4Proof.toSeq] at h₁ ⊢
      have orr₁ := List.map (orr₁ a b ((as.map .atoms) ++ forms ++ imps ++ aimps)) h₁
      have h₂ := automatedProof (.seq4 as forms imps aimps b)
      simp only [Seq4Proof.toSeq] at h₂
      have orr₂ := List.map (orr₂ a b ((as.map .atoms) ++ forms ++ imps ++ aimps)) h₂
      exact dbg_trace "OR rule applied"; (orr₁ ++ orr₂)
    | (.imp a b) => by
      have h := automatedProof (.seq4 as (a :: forms) imps aimps b)
      simp only [Seq4Proof.toSeq] at h ⊢
      have impr := List.map (impr a b ((as.map .atoms) ++ forms ++ imps ++ aimps)) (Proof.castSeqList h )
      exact impr
termination_by ((Seq4Proof.toSeq s).size, s.size)
decreasing_by
all_goals simp only [Seq4Proof.toSeq, Sequent.size]
. sorry
. apply Prod.Lex.left; --prod.Lex.Right
  have h := dershowits_simp (first:= List.map Form.atoms as) (last := imps') (a := [b]) (b := [(Form.atoms a )⊃ b]) (g := Form.atoms g)
  simp at *; simp only [h]; clear h; simp only [Multiset.IsDershowitzMannaLT]
  refine ⟨0, {b.weight}, {2 + b.weight}, ?_, ?_, ?_, ?_⟩
  all_goals simp
. apply Prod.Lex.left;
  have h := dershowits_simp (first:= List.map Form.atoms as) (last := imps') (a := [ (c ⊃ (d ⊃ b))]) (b := [((c ∧∧ d) ⊃ b)]) (g := Form.atoms g)
  simp at *; simp only [h]; clear h; simp only [Multiset.IsDershowitzMannaLT]
  refine ⟨0, {1 + c.weight + (1 + d.weight + b.weight) }, {1 + (2 + c.weight + d.weight) + b.weight}, ?_, ?_, ?_, ?_⟩
  all_goals simp
  . grind
. apply Prod.Lex.left; simp only [Form.weight, List.append_nil]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps') + {1}
  refine ⟨X, Multiset.ofList ([(c ⊃ b).weight] ++ [(d ⊃ b).weight]) , { ((c ∨∨ d) ⊃ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X];
    rw [sequent_size_add_singleton as ((d ⊃ b)::imps') (c ⊃ b) 1]
    rw [sequent_size_add_singleton as (imps') (d ⊃ b) 1]
    rw [← Multiset.coe_add [(c ⊃ b).weight] _]; simp only [Multiset.coe_singleton]; grind
  . simp only [X]; apply sequent_size_add_singleton
  . intro y hy; simp at hy; simp [Form.weight]; grind
. apply Prod.Lex.left; simp only [List.append_nil]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps')
  refine ⟨X, Multiset.ofList ([(d ⊃ b).weight] ++ [(c ⊃ d).weight]), Multiset.ofList ([((c ⊃ d) ⊃ b).weight] ++ [(Form.atoms g).weight]), ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]
    rw [sequent_size_add_singleton, ← Multiset.coe_add [(d ⊃ b).weight] _]
    simp only [Multiset.coe_singleton]; grind
  . simp only [X]; rw [ sequent_size_add_singleton, ← Multiset.coe_add [((c ⊃ d) ⊃ b).weight] _ ]
    simp only [Multiset.coe_singleton]; grind
  . intro y hy; simp at hy; simp [Form.weight]; grind
. apply Prod.Lex.left; simp only [Form.weight, List.append_nil]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps') + {1}
  refine ⟨X, { b.weight }, { ((c ⊃ d) ⊃ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]; rw [List.append_assoc, List.singleton_append]; apply sequent_size_add_singleton
  . simp only [X]; apply sequent_size_add_singleton
  . simp
. apply Prod.Lex.left; simp only [Form.weight, List.append_nil]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ imps') + {1}
  refine ⟨X, ∅ , { (⊥ ⊃ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]; simp
  . simp only [X]; apply sequent_size_add_singleton
  . intro y hy; simp at hy
. simp only [Form.weight] --ATOM REPLACEMENT
  have hM : (Multiset.map Form.weight ↑(List.map Form.atoms (a :: as) ++ forms' ++ imps) + {1}) =
            (Multiset.map Form.weight ↑(List.map Form.atoms as ++ Form.atoms a :: forms' ++ imps) + {1}) := by
          simp only [Multiset.map_coe, ← Multiset.coe_singleton, Multiset.coe_add _ [1], Multiset.coe_eq_coe]; grind
  rw [hM]; apply Prod.Lex.right; simp only [Seq4Proof.size]; grind
. apply Prod.Lex.left; simp only [Form.weight]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms' ++ imps) + {1}
  refine ⟨X, Multiset.ofList ([a.weight] ++ [b.weight]) , {(a ∧∧ b).weight}, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]; rw [List.append_assoc, ← List.singleton_append, List.append_assoc, List.singleton_append]
    rw [sequent_size_add_singleton as (b :: forms' ++ imps) a 1, ← List.singleton_append, List.append_assoc, List.singleton_append]
    rw [sequent_size_add_singleton as (forms' ++ imps) b 1, ← Multiset.coe_add [a.weight]]; simp only [Multiset.coe_singleton]; grind
  . simp only [X]; rw [List.append_assoc, List.append_assoc]; apply sequent_size_add_singleton as (forms' ++ imps) (a ∧∧ b)
  . simp; grind
. apply Prod.Lex.left; simp only [Form.weight]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms' ++ imps) + {1}
  refine ⟨X, { a.weight }, { (a ∨∨ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]; rw [List.append_assoc, List.append_assoc]; apply sequent_size_add_singleton as (forms' ++ imps)
  . simp only [X]; rw [List.append_assoc, List.append_assoc]; apply sequent_size_add_singleton as (forms' ++ imps) (a ∨∨ b)
  . simp; grind
. apply Prod.Lex.left; simp only [Form.weight]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms' ++ imps) + {1}
  refine ⟨X, { b.weight }, { (a ∨∨ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]; rw [List.append_assoc, List.append_assoc]; apply sequent_size_add_singleton as (forms' ++ imps)
  . simp only [X]; rw [List.append_assoc, List.append_assoc]; apply sequent_size_add_singleton as (forms' ++ imps) (a ∨∨ b)
  . simp
. simp only [Form.weight] --MOVING IMP TO DIFFERENT PLACE, SEQ STAYS SAME
  have hM : (Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms' ++ (a ⊃ b) :: imps) + {1}) =
            (Multiset.map Form.weight ↑(List.map Form.atoms as ++ (a ⊃ b) :: forms' ++ imps) + {1}) := by
          simp only [Multiset.map_coe, ← Multiset.coe_singleton, Multiset.coe_add _ [1], Multiset.coe_eq_coe]; grind
  rw [hM]; apply Prod.Lex.right; simp only [Seq4Proof.size]; grind
. apply Prod.Lex.left; set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms ++ imps ++ aimps)
  refine ⟨X, { a.weight }, {(a ∧∧ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]
  . simp only [X]
  . simp; grind
. apply Prod.Lex.left; set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms ++ imps ++ aimps)
  refine ⟨X, { b.weight }, {(a ∧∧ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]
  . simp only [X]
  . simp
. apply Prod.Lex.left; set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms ++ imps ++ aimps)
  refine ⟨X, { a.weight }, {(a ∨∨ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]
  . simp only [X]
  . simp; grind
. apply Prod.Lex.left; set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms ++ imps ++ aimps)
  refine ⟨X, { b.weight }, {(a ∨∨ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X]
  . simp only [X]
  . simp
. apply Prod.Lex.left; set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms ++ imps ++ aimps)
  refine ⟨X,  Multiset.ofList ([a.weight] ++ [b.weight]) , {(a ⊃ b).weight }, ?_, ?_, ?_, ?_⟩
  . simp
  . simp only [X];
    rw [←List.singleton_append, ←List.append_assoc, List.append_assoc _ forms imps]
    rw [List.append_assoc, List.singleton_append, sequent_size_add_singleton as (forms++imps) a _]
    rw [← Multiset.coe_add [a.weight]]; simp only [Multiset.coe_singleton]; rw [Multiset.add_comm {a.weight} {b.weight}]; grind
  . simp only [X]
  . simp; grind




def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax x xs _ =>
  indent indentLvl s!"AX: {listToString xs} ⊢ {formToString x}"
| .botl x xs =>
  indent indentLvl s!"⊥L: ⊥, {listToString xs} ⊢ {formToString x}"
| .andl a b g xs proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: ({formToString a} ∧ {formToString b}), {listToString xs} ⊢ {formToString g}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b g xs proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({formToString a} ∨ {formToString b}), {listToString xs} ⊢ {formToString g}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr₁ a b xs proof | .orr₂ a b xs proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊢ {formToString a} ∨ {formToString b}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₀ b g xs proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₀: ({formToString ⊥} → {formToString b}), {listToString xs}⊢ {formToString g}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ a b g xs _ proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₁: ({formToString (.atoms a)} → {formToString b}), {listToString xs}⊢ {formToString g}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ c d b g xs proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₂: (({formToString c} ∧ {formToString d}) → {formToString b}), {listToString xs}⊢ {formToString g}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₃ c d b g xs proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₃: (({formToString c} ∨ {formToString d}) → {formToString b}), {listToString xs}⊢ {formToString g}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₄ c d b g xs proof₁ proof₂  =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L₄: (({formToString c} → {formToString d}) → {formToString b}), {listToString xs}⊢ {formToString g}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs} ⊢ {formToString a} → {formToString b}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"


def listProofToString : List (Proof xseq) → String
| [] => "FAILURE"
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs

instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof


def automatedProofHelper (s : Sequent) : Std.Format :=
  have seq4 := Sequent.toSeq4 s
  have proofs := automatedProof seq4
  dbg_trace "{proofs.length}"; String.toFormat (listProofToString proofs)


#eval automatedProofHelper (seq {(p → q), p ⊢ q})
#eval! automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval! automatedProofHelper (seq {p ⊢ (q ∨ p)})
#eval! automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {⊢ ((p → (p → q)) → (p → q))})
#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))}) --no proof in single succ system
#eval! automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})

#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})


#print axioms automatedProofHelper
end singleSucc
