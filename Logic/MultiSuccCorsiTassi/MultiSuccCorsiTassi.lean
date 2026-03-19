import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card

import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Proof
import Logic.MultiSuccCorsiTassi.Syntax
import Logic.MultiSuccCorsiTassi.Helper
--import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Kripke
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

/- def Result.refutationss : List (Result s) → List (Refutation s b h)
| r :: rs =>
  match r with
  | .refutation rfs => rfs ++ Result.refutationss rs
  | _ =>  Result.refutationss rs
| [] => []

def Result.proofss : List (Result s) → List (Proof ⟨s.Γ ∪ ↑(b.map Imp.toForm) , s.Δ⟩)
| r :: rs =>
  match r with
  | .proof pf => pf ++ Result.proofss rs
  | _ => Result.proofss rs
| [] => [] -/

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


-- [[1,2] [3] [4,5]] = [[1,3,4] [1,3,5] [2,3,4] [2,3,5]]
def choices : List (List CM) → List (List CM)
| [] => []
| [x] => x.map ([·])
| x::y::xs => x.product (choices (y::xs)) |>.map (fun ⟨a, as⟩ ↦ a :: as)

/- @[simp, grind =]
theorem product_length {as : List α} {bs : List β} :
    (as.product bs).length = as.length * bs.length := by
  simp [List.product, List.map_const']

attribute [grind =] List.pair_mem_product -/

/- @[simp, grind =]
theorem choices_length {xs : List (List α)} :
    (choices xs).length = if xs = [] then 0 else (xs.map (·.length)).prod := by
  fun_induction choices with grind -/

@[grind =, simp]
theorem choices_eq_nil {xs : List (List α)} : choices xs = [] ↔ xs = [] ∨ [] ∈ xs := by
  fun_induction choices with
  | case1 => simp
  | case2 => simp
  | case3 => simp_all; grind

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





lemma neg_eq_imp_bot (a : Form) : .neg a = a ⊃ ⊥ := by rfl

/- METARULES
1. formula x can be principal of R→ (impr) only once
   - so whenever we apply R→ rule, we place it to the succedent used imp list

2. a fortiori can be applied to formula x only when it has been analyzed by R→ rule
   - from succ forms list we  take a form and check if it is present in succ used imps list, then can use a fortiori,

3. between two occurrences of L→ , there is an occurrence of R→ (on any form) in between
   - so when applying L→ , we place the copy of form to usedImp list on the left
     and continue until all forms and imps have been looked at. When encountering R→ , we move all imps from Used list back to imp list

4. -our own- kõik mittepööratavad reeglid tuleb panna kõrvale ja jõuda pööratavate reeglite kasutusel kas aksioomini
   või küllastunud sekventsini, alles siis vaadata mittepööratavaid reegleid. So left side imps go straight to imps₁
 -/

def automatedProof (s : Seq4Proof) (cap : ℕ )
                  (hcap : s.cap.card ≤ cap := by simp at *; grind )
                  (metaR1 : s.impR ∩ s.hist = ∅ := by grw [metaR1]) :
                   Result s.toSeq s.hist :=
  match s with
  | {as, fL, block,  bs, fR, impR, hist} =>
    match fL with
    | [] =>
      match fR with
      | [] => -- succedent only has atoms left --
        match common : as ∩ bs with --CHANGED
        -- no common atoms
        | [] =>
          match impR with
          | [] =>  by
            simp [Seq4Proof.toSeq, List.append_nil]
            let rule := [ax hist as bs block (by grind)]
            exact Result.refutation rule (by grind)
          --METARULE 1 NONINVERTABLE REEGEL
          | impR => by
            simp only [Seq4Proof.toSeq, List.append_nil]
            let impRApplications :
            -- find either a list of proofs for any of the imps, if none found, get the function required to get ALL refutations
                List (List (Proof ⟨↑(as.map Form.atoms), ↑block, ↑(bs.map Form.atoms ++ impR.map Imp.toForm)⟩)  ⊕
                      List ((a b : Form) × Refutation ⟨↑(a :: as.map Form.atoms ++ block.map Imp.toForm), {}, {b}⟩  (⟨a,b⟩ :: hist))) :=
              impR.attach.map (λ (⟨⟨f, g⟩ , ha⟩ : {i : Imp // i ∈ impR}) ↦
                have inclusion : insert { f, g } ( collectImpsForm f ∪ collectImpsForm g) ⊆   impR.toFinset.biUnion collectImpsImp := by
                  intro x hx
                  apply Finset.mem_biUnion.mpr
                  refine ⟨⟨f,g⟩, by simpa using ha, ?_⟩
                  simp [collectImpsImp] at hx ⊢
                  exact hx
                have eq : (block).toFinset.biUnion collectImpsImp = (block.map Imp.toForm).toFinset.biUnion collectImpsForm := by ext x; simp [Finset.mem_biUnion]

                have premise := automatedProof ⟨as, (f :: (block.map Imp.toForm)), [], [], [g], [], (⟨ f, g⟩ :: hist)⟩ cap
                                                (by grw [← hcap]; simp; apply Finset.card_le_card ?_; grind) (by simp)
                let xs := as.map Form.atoms; let ys := bs.map Form.atoms ++ (impR.erase ⟨f, g⟩).map Imp.toForm
                have ruleP := impr f g xs ys block
                --have ruleR := (Refutation.impr block hist as bs impR (by grind))
                match premise with
                | .proof pf neqE => .inl (pf.map (λ p ↦ (ruleP p.castSeq).castSeq))
                | .refutation rf neqE => .inr (rf.map (λ p ↦ ⟨ f, g , p.castSeq⟩))
                --(premise.castSeq.map (b := []) (h := ⟨f, g⟩ :: hist) block hist ruleP (λ r ↦ (ruleR r).castSeq)).castSeq
              )
            let res := pickProof impRApplications
            --let neqE : impRApplications.filterMap Sum.getLeft? = some ys
            match _ : pickProof impRApplications with
            | .inl pf => exact Result.proof pf.flatten (by simp_all; rename_i h; sorry )
            | .inr rfs =>
              have choices := choices rfs --all dif ways to construct refutation
              have ruleR := (Refutation.impr hist as bs impR block (by grind)) --new parent to choices
              exact .refutation (choices.attach.map (λ ⟨c, h⟩ ↦
                                                ruleR (λ a b hab ↦
                                                  (c.findSome? (λ ⟨a', b', r'⟩ ↦ -- find the same imp in child as in parent
                                                    if _ : a = a' ∧ b = b'
                                                      then some (r'.castSeq (hb := by grind) (hh := by grind) (hc := by grind))
                                                    else none)).get sorry)--prove that same imps can be found in choices as in parent
                                                    )
                                ) (by simp_all; intro a; sorry)
        | xs@(_::_) => by
          --have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          --have corr := findIntersCorr as bs
          let proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        Proof.ax x ((as.map Form.atoms)) ((bs.map Form.atoms) ++ (impR.map Imp.toForm)) block
                        (by grind)
                        (by grind))
          simp only [Seq4Proof.toSeq, List.append_nil]; exact Result.proof proofs (by grind)

      -- open up forms on right side
      | (.atoms a) :: succForms =>  --move atom to succ atoms list
        Result.castSeq (automatedProof ⟨as, [], block, a :: bs, succForms, impR, hist⟩ cap)

      | ⊥ :: succForms =>   --botr rule, .bot is ignored
        have premise := automatedProof ⟨as, [], block, bs, succForms, impR, hist⟩ cap
        --simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
        let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := Proof.botr (as.map .atoms) ys block; have ruleR := Refutation.botr hist (as.map .atoms) ys block
        --simp [xs, ys] at ruleP ruleR
        (premise.castSeq.map hist ruleP ruleR).castSeq

      | (.and a b) :: succForms =>
        have premise₁ := automatedProof ⟨as, [], block, bs, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        --simp [Seq4Proof.toSeq] at premise₁ premise₂ ⊢
        let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := andr a b (as.map .atoms) ys block;
        have ruleR₁ := andr₁ hist a b (as.map .atoms) ys block; have ruleR₂ := andr₂ hist a b (as.map .atoms) ys block
        (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

      | (.or a b) :: succForms =>
        have premise := automatedProof ⟨as, [], block, bs, a :: b :: succForms, impR, hist⟩ cap
        let xs := as.map .atoms; let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := orr a b xs ys block; have ruleR := orr hist a b xs ys block
        (premise.castSeq.map hist ruleP ruleR).castSeq

      | (.imp a b) :: succForms =>  --METARULE 2 apply afort only when R→ has been used (if it is in usedImps₂. else: läheb imps listi)
        if inc : ⟨a,b⟩ ∈ hist then
          have premise := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
          let xs := as.map .atoms; let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
          have ruleP := afort a b xs ys block; have ruleR := afort hist a b xs ys block (by grind)
          (premise.castSeq.map hist ruleP ruleR).castSeq
        else
          .castSeq (automatedProof ⟨as, [], block, bs, succForms, ⟨a,b⟩ :: impR, hist⟩ cap
                            (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) (by simp at metaR1; simp; grind))

    -- open up forms on left side --
    | (.atoms a) :: antForms =>
      .castSeq (automatedProof ⟨as ++ [a], antForms, block, bs, fR, impR, hist⟩ cap)

    | .bot :: antForms => by
      let rule := [botl (as.map .atoms ++ antForms) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)) block]
      simp only [Seq4Proof.toSeq]
      exact .proof (Proof.castSeqList rule) (by grind)

    | (.and a b) :: antForms =>
      have premise := automatedProof ⟨as, a :: b :: antForms, block, bs, fR, impR, hist⟩ cap
      let xs := (as.map .atoms) ++ antForms; let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := andl a b xs ys block; have ruleR := Refutation.andl hist a b xs ys block
      (premise.castSeq.map hist ruleP ruleR).castSeq

    | (.or a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, a :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have premise₂ := automatedProof ⟨as, b :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms; let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := orl a b xs ys block
      have ruleR₁ := orl₁ hist a b xs ys block; have ruleR₂ := orl₂ hist a b xs ys block
      (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

    | (.imp a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, antForms, ⟨a, b⟩ :: block, bs, a::fR, impR, hist⟩ cap
      have premise₂ := automatedProof ⟨as, b::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms; let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := impl a b xs ys block; have ruleR₁ := impl₁ hist a b xs ys block; have ruleR₂ := impl₂ hist a b xs ys block
      (Result.map2proof (premise₁.castSeq) premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

termination_by s.weight cap hcap
decreasing_by
all_goals simp_all [Seq4Proof.weight, Weight.lt_iff]; try grind [Seq4Proof.weight, Weight.instWellFoundedRelation, Weight.instLT];
. have hx : { f, g} ∉ hist := by
    intro hmem
    have : { f, g} ∈ impR ∩ hist := List.mem_inter_of_mem_of_mem ha hmem
    simp_all
  have hxFin : { f, g} ∉ hist.toFinset := by simp; exact hx
  have hcard : hist.toFinset.card < (insert { f, g} hist.toFinset).card := by
    have : (insert { f, g} hist.toFinset).card = hist.toFinset.card + 1 := Finset.card_insert_of_notMem hxFin
    grind
  grind


def automatedProofHelper (s : Sequent) : Std.Format :=
  have res := automatedProof s.toSeq4 s.toSeq4.cap.card (by simp) (by simp [Sequent.toSeq4])

  match res with
  | .proof ps _ =>  dbg_trace s!"have proof {ps.length}"; String.toFormat (listProofToString ps)
  | .refutation rf _ => dbg_trace s!"{rf.length}"; String.toFormat (listRefutationToString rf)

--modusponens "a → b, a ⊢ β"
#eval! automatedProofHelper (seq {(p → q), p ⊢ q})
#eval! automatedProofHelper (seq {(p ∨ q), ¬p ⊢ q})
#eval! automatedProofHelper (seq {p ⊢ (q ∨ p)})

#eval! automatedProofHelper (seq {⊢ ((p → (p → q)) → (p → q))})
#eval! automatedProofHelper (seq {p ⊢ (¬q ∨ p)})

#eval! automatedProofHelper (seq {((p ∨ q) ∧ r) ⊢ ((p ∧ r) ∨ (q ∧ r))})

#eval! automatedProofHelper (seq {⊢ ¬¬ (¬p ∨ p)})
#eval! automatedProofHelper (seq {(p → r), (q → ¬r) ⊢ ¬(p ∧ q)})
--from corsi tassi article
#eval! automatedProofHelper (seq { ⊢ (((((p → r) → p) → p) → ⊥) → ⊥)})

#eval! automatedProofHelper (seq { ⊢ ((¬ p → ¬ q) → (q → p))})
-- Pierce ((p → q )→ p) → p
#eval! automatedProofHelper (seq {⊢ (((p → q )→ p) → p)})
#eval! automatedProofHelper (seq {⊢ (p ∨ ¬p )})
#eval! automatedProofHelper (seq {⊢ ¬¬(p ∨ ¬p )})
--#eval! evaluate (form {((¬ p → ¬ q) → (q → p))})
#print axioms automatedProofHelper
end multiSucc
