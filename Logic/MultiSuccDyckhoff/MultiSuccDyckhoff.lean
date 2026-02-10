import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw

import Logic.MultiSuccDyckhoff.Core
import Logic.MultiSuccDyckhoff.Helper
import Logic.MultiSuccDyckhoff.Display
import Logic.MultiSuccDyckhoff.Syntax

namespace multiSucc
open multiSucc



/-
imp₁ imp₂ imp₃ imp₄ (imp₀) are defined to help with termination and looping prevention (paper by Roy Dyckhoff)

 -/
inductive Proof : Sequent → Type
  -- ∀ x Γ, x ++ Γ ⊢ x
  | ax :
    ∀ (a : Form) (xs ys : List Form), --TRY THIS WAY, GIVE PROOF OF INCLUSION
      (hxs : a ∈ xs) →
      (hys : a ∈ ys) →
      Proof (.seq ↑xs ↑ys)
  -- ∀ x Γ, (⊥, Γ ⊢ x)
  | botl :
    ∀ (xs ys : List Form),
      Proof (.seq ↑( ⊥ :: xs) ↑ys)
    -- ∀ Γ, ( ⊥, Γ ⊢ ⊥)
  | botr :
    ∀ (xs ys : List Form),
      Proof (.seq ↑xs ↑ys) →
      Proof (.seq ↑xs ↑(⊥ :: ys))
  -- ∀ a b Γ Δ, (Γ, a, b ⊢ Δ) → (Γ, a ∧ b ⊢ Δ)
  | andl :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑(a :: b :: xs) ↑ys) →
      Proof (.seq ↑((a ∧∧ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ, (Γ ⊢ a, Δ) → (Γ ⊢ b, Δ) → (Γ ⊢ a ∧ b, Δ)
  | andr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑xs ↑(a :: ys)) →
      Proof (.seq ↑xs ↑(b :: ys)) →
      Proof (.seq ↑xs ↑((a ∧∧ b) :: ys))
  -- ∀ a b Γ Δ, (a, Γ ⊢ Δ) → (b, Γ ⊢ Δ) → (a ∨ b, Γ ⊢ Δ)
  | orl :
    ∀ (a b : Form) (xs ys : List Form),
    Proof (.seq ↑(a :: xs) ↑ys) →
    Proof (.seq ↑(b :: xs) ↑ys) →
    Proof (.seq ↑((a ∨∨ b) :: xs) ↑ys)
  -- ∀ a b Γ Δ , (Γ ⊢ a, b, Δ) → (Γ ⊢ a ∨ b, Δ)
  | orr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑xs ↑(a :: b :: ys)) →
      Proof (.seq ↑xs ↑((a ∨∨ b) :: ys))
  -- a is .bot IS THIS RULE NECESSARY? based on paper p800 proof e.iv
  | impl₀ :
    ∀ (b : Form) (xs  ys: List Form),
      Proof (.seq ↑xs ↑ys) →
      Proof (.seq ↑((⊥ ⊃ b) :: xs) ↑ys)
  -- a is atomic
  -- ∀ a b Γ Δ, (a, b, Γ ⊢ Δ) → (a → b, a, Γ ⊢ Δ)
  | impl₁ :
    ∀ (a : Atom) (b : Form) (xs ys : List Form), --HERE ALSO NEED PROOF OF a ∈ xs
      (h : (.atoms a) ∈ xs) →
      Proof (.seq ↑( b :: xs) ↑ys) →
      Proof (.seq ↑(((.atoms a) ⊃ b) :: xs) ↑ys)
  -- implications left side is and operation
  -- ∀ c d b Γ Δ, (c ⊃ (d ⊃ b), Γ ⊢ Δ) → ((c ∧∧ d) ⊃ b, Γ ⊢ Δ)
  | impl₂ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((c ⊃ (d ⊃ b)) :: xs) ↑ys) →
      Proof (.seq ↑(((c ∧∧ d) ⊃ b) :: xs) ↑ys)
  -- left side is or op
  -- ∀ c d b Γ Δ, (c ⊃ b, d ⊃ b, Γ ⊢ Δ) → ((c ∨∨ d) ⊃ b, Γ ⊢ Δ)
  | impl₃ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((c ⊃ b) :: (d ⊃ b) :: xs) ↑ys) →
      Proof (.seq ↑(((c ∨∨ d) ⊃ b) :: xs) ↑ys)
  -- left side is imp op
  -- ∀ c d b Γ Δ, ( d ⊃ b, Γ ⊢ c ⊃ d) → (b, Γ ⊢ Δ) → ((c ⊃ d) ⊃ b, Γ ⊢ Δ) OR USE THE OTHER RULE?
  | impl₄ :
    ∀ (c d b : Form) (xs ys : List Form),
      Proof (.seq ↑((d ⊃ b) :: xs) {c ⊃ d}) →
      Proof (.seq ↑( b :: xs) ↑ys) →
      Proof (.seq ↑(((c ⊃ d) ⊃ b) :: xs) ↑ys)
  -- ∀ a b Γ, (a, Γ ⊢ b) → (Γ ⊢ a → b)
  | impr :
    ∀ (a b : Form) (xs ys : List Form),
      Proof (.seq ↑(a :: xs) {b}) →
      Proof (.seq ↑xs ↑((a ⊃ b) :: ys))
open Proof


@[simp]
def Seq4Proof.toSeq : Seq4Proof → Sequent
| .seq4 atoms₁ forms₁ imps₁ aimps atoms₂ forms₂ imps₂ =>
  have ant := Multiset.ofList ((atoms₁.map Form.atoms) ++ forms₁ ++ imps₁ ++ aimps)
  have succ := Multiset.ofList ( (atoms₂.map Form.atoms) ++  forms₂ ++ imps₂)
  Sequent.seq ant succ

def Sequent.toSeq4 : Sequent → Seq4Proof
| .seq Δ Γ => Seq4Proof.seq4 [] (Multiset.sort Δ LE.le) [] [] [] (Multiset.sort Γ LE.le) []

def Proof.castSeqList (x : List (Proof (Sequent.seq (Multiset.ofList a₁) (Multiset.ofList b₁))))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof (Sequent.seq (Multiset.ofList a₂) (Multiset.ofList b₂))) := by rw [ha, hb] at x; exact x

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

@[simp]
def sequent_simp_dershowitz {as bs y₁ y₂ : Multiset Form} :
  (( (as + y₁ + bs)).IsDershowitzMannaLT (as + y₂ + bs)) =
  (((y₁)).IsDershowitzMannaLT ↑(y₂)) := by sorry



/- def firstImpPremisePresent (imps : List Form) (atoms : List Atom) : Option Form :=
  match imps with
  | [] => (none)
  | (Form.imp (.atoms a) b) :: imps' =>
      if a ∈ atoms then
        (some (.atoms a ⊃ b))
      else
        firstImpPremisePresent imps' atoms
  | _ :: imps' =>
      firstImpPremisePresent imps' atoms -/

def firstImpPremisePresent (imps : List Form) (atoms : List Atom) : Option Form × List Form :=
match imps with
| [] => (none, [])
| (Form.imp (.atoms a) b) :: rest =>
    if a ∈ atoms then
      (some (Form.imp (.atoms a) b), rest)
    else
      let (res, rest') := firstImpPremisePresent rest atoms
      (res, (Form.imp (.atoms a) b) :: rest')
| f :: rest =>
    let (res, rest') := firstImpPremisePresent rest atoms
    (res, f :: rest')

/- lemma firstImpPremisePresent_sound :
  firstImpPremisePresent imps atoms = (some f) →
  ∃ a b,
    f = (Form.imp (.atoms a) b) ∧
    f ∈ imps ∧
    a ∈ atoms := by
  fun_induction firstImpPremisePresent <;> grind -/

theorem firstImpPremisePresent_atom_inclusion :
  firstImpPremisePresent imps atoms = (some f, xs) →
  ∃ a b,
    f = (Form.imp (.atoms a) b) ∧
    a ∈ atoms := by
  fun_induction firstImpPremisePresent
  . grind
  . grind
  . simp; sorry
  . sorry

theorem firstImpPremisePresent_rest_perm :
  firstImpPremisePresent imps atoms = (some f, xs) →
  (f :: xs).Perm imps := by
  fun_induction firstImpPremisePresent
  . grind
  . grind
  . simp; grind
  . sorry

lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl


def automatedProof (s : Seq4Proof) : List (Proof s.toSeq) :=
  match s with
  | .seq4 as forms₁ imps₁ aimps bs forms₂ imps₂ =>
    match forms₂ with
    | [] =>
      match forms₁ with
      | [] =>
        match common : findIntersection as bs with
        | [] =>
          match imps₂ with
            | [] =>
              match imps₁ with
                | [] =>
                  match impO : firstImpPremisePresent aimps as with
                  | (none, _)=> []
                  | (some (Form.imp (.atoms a) b), rest) =>  by
                    have atomIn := firstImpPremisePresent_atom_inclusion impO
                    have restPerm := firstImpPremisePresent_rest_perm impO
                    --have rest := aimps.erase (Form.imp (.atoms a) b)
                    have premise := automatedProof (.seq4 as [b] [] rest bs [] [])
                    simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢

                    have proof := List.map ((impl₁ a b (as.map .atoms ++ rest) (bs.map .atoms)) (by grind)) (Proof.castSeqList premise (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                    --simp [← Multiset.coe_eq_coe] at haimps
                    apply Proof.castSeqList proof (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                  | (some f, _) => []
                | (.imp a b) :: antImps =>
                  match a with
                  | .atoms a => -- impl₁ has to be done last, to ensure that all atoms are in as, this is also mentioned in the paper. move to aimps
                    Proof.castSeqList (automatedProof (.seq4 as [] antImps ((.atoms a ⊃ b) :: aimps) bs [] [])) (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                  | .and c d => by
                    have h := automatedProof (.seq4 as [] ((c ⊃ (d ⊃ b)) :: antImps) aimps bs [] []) --put them straight into imps list
                    simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
                    have proofs := List.map (impl₂ c d b ((as.map .atoms) ++ antImps ++ aimps) (bs.map .atoms)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                    apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                  | .or c d => by
                    have h := automatedProof (.seq4 as [] ((c ⊃ b) :: (d ⊃ b) :: antImps) aimps bs [] []) --put them straight into imps list
                    simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
                    have proofs := List.map (impl₃ c d b ((as.map .atoms) ++ antImps ++ aimps) (bs.map .atoms )) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                    apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                  | .imp c d => by
                    have h₁ := automatedProof (.seq4 as [] ((d ⊃ b) :: antImps) aimps [] [] [c ⊃ d]) --put them straight into imps list
                    have h₂ := automatedProof (.seq4 as [b] antImps aimps bs [] [])
                    simp only [Seq4Proof.toSeq, List.append_nil] at h₁ h₂ ⊢
                    have proofs := List.map (impl₄ c d b ((as.map .atoms) ++ antImps ++ aimps) (bs.map .atoms)).uncurry
                        (getPairs (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                                  (Proof.castSeqList h₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)))
                    apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                  | .bot => by
                    have h := automatedProof (.seq4 as [] antImps aimps bs [] [])
                    simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
                    have proofs := List.map (impl₀ b ((as.map .atoms) ++ antImps ++ aimps) (bs.map .atoms)) h
                    apply Proof.castSeqList proofs (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
                | _ :: antImps => dbg_trace "shouldnt get here 2"; []
            | (.imp a b) :: succImps => by
              have h := automatedProof (.seq4 as [a] imps₁ aimps [] [b] [])
              simp [Seq4Proof.toSeq, List.append_nil] at h ⊢
              have rule := List.map (impr a b (as.map .atoms ++ imps₁ ++ aimps) (bs.map .atoms ++ succImps)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
              apply Proof.castSeqList rule (by grind) (by simp only [Multiset.coe_eq_coe]; grind)
            | _ :: succImps => dbg_trace "shouldnt get here"; []

        | xs => by
          have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          have corr := findIntersCorr as bs
          --exact findAtomicProofs (xs) as (imps₁) (usedImps₁) bs (imps₂) (usedImps₂) (Γ)
          have proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        ax (.atoms x) ((as.map Form.atoms) ++ imps₁ ++ aimps) ((bs.map Form.atoms) ++ imps₂)
                        (by simp [hx, Γ, corr])
                        (by simp [hx, Γ, corr]))

          simp only [Seq4Proof.toSeq, List.append_nil]; exact dbg_trace "atomic proofs for {xs}"; proofs

      | (.atoms a) :: antForms => --move to as
        Proof.castSeqList (automatedProof (.seq4 (a :: as) antForms imps₁ aimps bs [] imps₂)) (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | ⊥ :: antForms => by
        simp only [Seq4Proof.toSeq, List.append_nil]
        exact Proof.castSeqList [(botl ((as.map .atoms) ++ antForms ++ imps₁ ++ aimps) (bs.map .atoms ++ imps₂))] (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.and a b) :: antForms => by
        have h := automatedProof (.seq4 as (a :: b :: antForms) imps₁ aimps bs [] imps₂)
        simp only [Seq4Proof.toSeq, List.append_nil] at h ⊢
        have rule := List.map (andl a b ((as.map .atoms) ++ antForms ++ imps₁ ++ aimps) (bs.map .atoms ++ imps₂)) (Proof.castSeqList h (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
        apply Proof.castSeqList rule (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.or a b) :: antForms => by
        have h₁ := automatedProof (.seq4 as (a :: antForms) imps₁ aimps bs [] imps₂)
        have h₂ := automatedProof (.seq4 as (b :: antForms) imps₁ aimps bs [] imps₂)
        simp only [Seq4Proof.toSeq, List.append_nil] at h₁ h₂ ⊢
        have rule := List.map (orl a b ((as.map .atoms) ++ antForms ++ imps₁ ++ aimps) (bs.map .atoms ++ imps₂)).uncurry
          (getPairs (Proof.castSeqList h₁ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl))
                    (Proof.castSeqList h₂ (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)))
        apply Proof.castSeqList rule (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
      | (.imp a b) :: antForms => --move to imps₁
        Proof.castSeqList (automatedProof (.seq4 as antForms ((a ⊃ b) :: imps₁) aimps bs [] imps₂)) (by simp only [Multiset.coe_eq_coe]; grind) (by rfl)
    | (.atoms a) :: succForms => --move to bs
      Proof.castSeqList (automatedProof (.seq4 as forms₁ imps₁ aimps (a :: bs) succForms imps₂)) (by rfl)
    | ⊥ :: succForms => by
      have h := automatedProof (.seq4 as forms₁ imps₁ aimps bs succForms imps₂)
      simp only [Seq4Proof.toSeq] at h ⊢
      have rule := List.map (botr ((as.map .atoms) ++ forms₁ ++ imps₁ ++ aimps) (bs.map .atoms ++ succForms ++ imps₂)) h
      apply Proof.castSeqList rule (by rfl)
    | (.and a b) :: succForms => by
      have h₁ := automatedProof (.seq4 as forms₁ imps₁ aimps bs (a :: succForms) imps₂)
      have h₂ := automatedProof (.seq4 as forms₁ imps₁ aimps bs (b :: succForms) imps₂)
      simp only [Seq4Proof.toSeq] at h₁ h₂ ⊢
      have rule := List.map (andr a b ((as.map .atoms) ++ forms₁ ++ imps₁ ++ aimps) (bs.map .atoms ++ succForms ++ imps₂)).uncurry  (getPairs (Proof.castSeqList h₁ (by rfl)) (Proof.castSeqList h₂ (by rfl)))
      apply Proof.castSeqList rule (by rfl)
    | (.or a b) :: succForms => by
      have h := automatedProof (.seq4 as forms₁ imps₁ aimps bs (a :: b :: succForms) imps₂)
      simp only [Seq4Proof.toSeq] at h ⊢
      have rule := List.map (orr a b ((as.map .atoms) ++ forms₁ ++ imps₁ ++ aimps) (bs.map .atoms ++ succForms ++ imps₂)) (Proof.castSeqList h (by rfl))
      apply Proof.castSeqList rule (by rfl)
    | (.imp a b) :: succForms =>  --move to imps₂
      Proof.castSeqList (automatedProof (.seq4 as forms₁ imps₁ aimps bs succForms ((a ⊃ b) :: imps₂))) (by rfl)
termination_by ((Seq4Proof.toSeq s).size, s.size)
decreasing_by
--all_goals simp only [Seq4Proof.toSeq, Sequent.size]
. apply Prod.Lex.left; --simp only [Seq4Proof.toSeq, Sequent.size];
  --simp only [Multiset.IsDershowitzMannaLT, List.append_nil, ← Multiset.map_add]
  simp [Multiset.IsDershowitzMannaLT]; simp only [Sequent.size]
  rw [← Multiset.map_add, ← Multiset.map_add, Multiset.coe_add, Multiset.coe_add]
  set X := Multiset.map Form.weight ↑(List.map Form.atoms as ++ List.map Form.atoms bs)
  refine ⟨X, (Multiset.map Form.weight ↑(b :: rest)), (Multiset.map Form.weight ↑(aimps)), ?_, ?_, ?_, ?_⟩
  . simp; sorry
  . simp [X]; grind
  . simp [X]; grind
  . intro y hy; simp at *
    refine ⟨ (Form.atoms a ⊃ b), ?_, ?_ ⟩
    . grind
    . simp [Form.weight]; sorry--rw [hy.left]
. have eq : (Seq4Proof.seq4 as [] antImps ((Form.atoms a ⊃ b) :: aimps) bs [] []).toSeq =
            (Seq4Proof.seq4 as [] ((Form.atoms a ⊃ b) :: antImps) aimps bs [] []).toSeq := by simp [Seq4Proof.toSeq]; grind
  rw [eq]; apply Prod.Lex.right; simp [Seq4Proof.size]
   /- apply Prod.Lex.left; simp only [Multiset.IsDershowitzMannaLT]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as)
  refine ⟨X, ↑([a.weight] ++ [b.weight]), Multiset.map Form.weight ↑((bs.map Form.atoms) ++ (( a ⊃ b)) :: succImps), ?_, ?_, ?_, ?_⟩
  . simp
  . simp [X]; rw [← Multiset.coe_singleton, Multiset.coe_add]; grind
  . simp only [X, List.append_nil]
  . intro y hy; simp at hy; simp [Form.weight];
    refine ⟨1 + a.weight + b.weight, ?_, ?_⟩
    . right; left; rfl
    . grind -/
. sorry /- apply Prod.Lex.left; rw [← Multiset.coe_add _ antImps]; rw[ Multiset.map_add Form.weight _ (Multiset.ofList antImps)]
  simp only [List.append_nil]; --rw [← List.singleton_append (Form.atoms a ⊃ b), ← Multiset.coe_add _ antImps]; rw[ Multiset.map_add Form.weight _ (Multiset.ofList antImps)]
  simp only [Multiset.IsDershowitzMannaLT]
  set X : Multiset Nat :=  Multiset.map Form.weight ↑(List.map Form.atoms as ++ antImps) + Multiset.map Form.weight ↑(List.map Form.atoms bs ++ imps₂)
  refine ⟨X, {b.weight}, {(Form.atoms a ⊃ b).weight}, ?_, ?_, ?_, ?_⟩
  . simp
  . simp [X] ; sorry
  . simp [X] ; sorry
  . simp -/
. sorry
. sorry
. sorry
. sorry
. sorry
. have eq : (Seq4Proof.seq4 (a :: as) antForms imps₁ aimps bs [] imps₂).toSeq =
            (Seq4Proof.seq4 as (Form.atoms a :: antForms) imps₁ aimps bs [] imps₂).toSeq := by simp [Seq4Proof.toSeq]; grind
  rw [eq]; apply Prod.Lex.right; simp [Seq4Proof.size]
. sorry
. sorry
. sorry
. have eq : (Seq4Proof.seq4 as antForms ((a ⊃ b) :: imps₁) aimps bs [] imps₂).toSeq =
            (Seq4Proof.seq4 as ((a ⊃ b) :: antForms) imps₁ aimps bs [] imps₂).toSeq := by simp [Seq4Proof.toSeq]; grind
  rw [eq]; apply Prod.Lex.right; simp [Seq4Proof.size]; grind
. have eq : (Seq4Proof.seq4 as forms₁ imps₁ aimps (a :: bs) succForms imps₂).toSeq =
            (Seq4Proof.seq4 as forms₁ imps₁ aimps bs (Form.atoms a :: succForms) imps₂).toSeq := by simp [Seq4Proof.toSeq]; grind
  rw [eq]; apply Prod.Lex.right; simp [Seq4Proof.size]
. sorry
. --apply Prod.Lex.left; apply sequent_simp_dershowitz (Multiset.map Form.weight ↑(List.map Form.atoms as ++ forms₁ ++ imps₁)) ∅ _ _
  sorry
. sorry
. sorry
. have eq : (Seq4Proof.seq4 as forms₁ imps₁ aimps bs succForms ((a ⊃ b) :: imps₂)).toSeq =
            (Seq4Proof.seq4 as forms₁ imps₁ aimps bs ((a ⊃ b) :: succForms) imps₂).toSeq := by simp [Seq4Proof.toSeq]; grind
  rw [eq]; apply Prod.Lex.right; simp [Seq4Proof.size]; grind



def proofToString  {xseq : Sequent} (indentLvl : Nat) : Proof xseq → String
| .ax _ xs ys _ _=>
  indent indentLvl s!"AX: {listToString xs} ⊢ {listToString ys}"
| .botl xs ys =>
  indent indentLvl s!"⊥L: ⊥, {listToString xs} ⊢ {listToString ys}"
| .botr xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine :=
  s!"⊥R: {listToString xs} ⊢ ⊥, {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andl a b xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"∧L: ({formToString a} ∧ {formToString b}), {listToString xs} ⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .andr a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∧R: {listToString xs} ⊢ {formToString a} ∧ {formToString b}, {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine (ruleLine.length))}\n{indent indentLvl ruleLine}"
| .orl a b xs ys proof₁ proof₂=>
  let left := proofToString  (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"∨L: ({formToString a} ∨ {formToString b}), {listToString xs} ⊢ {listToString ys}"
  s!"{left}\n{right}\n{horizontalLine (ruleLine.length)}\n{indent indentLvl ruleLine}"
| .orr a b xs ys proof =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!" ∨R: {listToString xs} ⊢ {formToString a} ∨ {formToString b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₀ b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₀: ({formToString ⊥} → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₁ a b xs ys _ proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₁: ({formToString (.atoms a)} → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₂ c d b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₂: (({formToString c} ∧ {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₃ c d b xs ys proof =>
  let premise  := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→L₃: (({formToString c} ∨ {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impl₄ c d b xs ys proof₁ proof₂  =>
  let left  := proofToString (indentLvl + 1) proof₁
  let right := proofToString (indentLvl + 1) proof₂
  let ruleLine := s!"→L₄: (({formToString c} → {formToString d}) → {formToString b}), {listToString xs}⊢ {listToString ys}"
  s!"{left}\n{right}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"
| .impr a b xs ys proof  =>
  let premise := proofToString (indentLvl + 1) proof
  let ruleLine := s!"→R: {listToString xs} ⊢ {formToString a} → {formToString b}, {listToString ys}"
  s!"{ premise}\n{indent indentLvl (horizontalLine ruleLine.length)}\n{indent indentLvl ruleLine}"


def listProofToString : List (Proof xseq) → String
| [] => "FAILURE"
| x::xs => (proofToString 0 x).replace " ," "" ++ "\n \n" ++ listProofToString xs

instance : ToString (List (Proof xseq)) where
  toString proof := listProofToString proof


def automatedProofHelper (s : Sequent) : Std.Format :=
  have seq4 := Sequent.toSeq4 s
  have proofs := automatedProof seq4
  dbg_trace "{proofs.length}"
  String.toFormat (listProofToString proofs)


#eval! automatedProofHelper (seq {(p → q), p ⊢ q})
#eval! automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval! automatedProofHelper (seq {p ⊢ (q ∨ p)})
#eval! automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {⊢ ((p → (p → q)) → (p → q))})
#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))}) --no proof in single succ system
#eval! automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})
#eval! automatedProofHelper (seq {(p → r), (q → ¬r) ⊢ ¬(p ∧ q)}) --example where

#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})


#print axioms automatedProofHelper
end multiSucc
