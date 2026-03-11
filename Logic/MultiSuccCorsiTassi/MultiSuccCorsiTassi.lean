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
inductive Result (s : Sequent) (b h : List Imp) where
| proof (ps : List (Proof s)) : ps ≠ [] → Result s b h
| refutation (rf : List (Refutation s b h)) : rf ≠ []  → Result s b h

def Result.proofs : Result s b h → List (Proof s )
| .proof pf _ => pf
| _ => []

def Result.refutations : Result s b h → List (Refutation s b h)
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

def Proof.castSeq (x : Proof ⟨a₁, b₁⟩)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    Proof ⟨a₂, b₂⟩ := by rw [ha, hb] at x; exact x

def Proof.castSeqList (x : List (Proof ⟨a₁, b₁⟩))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof ⟨a₂, b₂⟩) := by rw [ha, hb] at x; exact x

@[simp, grind =]
theorem Proof.castSeqList_eq_nil : Proof.castSeqList x ha hb = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def Refutation.castSeq (x :  Refutation ⟨a₁, b₁⟩ b h)
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (bb : b = b' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    Refutation ⟨a₂, b₂⟩ b' h' := by subst_eqs; exact x

def Refutation.castSeqList (x : List (Refutation ⟨a₁, b₁⟩ b h))
    (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (bb : b = b' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Refutation ⟨a₂, b₂⟩ b' h') := by subst_eqs; exact x

@[simp, grind =]
theorem Refutation.castSeqList_eq_nil : Refutation.castSeqList x ha hb bb hh = [] ↔ x = [] := by subst_eqs; simp [castSeqList]

def Result.castSeq (x : Result ⟨a₁, b₁⟩ b h)
  (ha : a₁ = a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hb : b₁ = b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (bb : b = b' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hh : h = h' := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
  Result ⟨a₂, b₂⟩ b' h' := by subst_eqs; exact x

/- def Result.map' (r : Result s)
  (f₁ : List (Proof s) → List (Proof s'))
  (f₂ : List (Refutation s b h) → List (Refutation s' b' h')): Result s':=
  match r with
  | .proof ps => .proof (f₁ ps)
  | .refutation rs   => .refutation (f₂ rs) -/

def Result.map
  (r : Result s b h)
  (b' h' : List Imp)
  (f₁ : Proof s → Proof s')
  (f₂ :  Refutation s b h → Refutation s' b' h') :
  Result s' b' h' :=
  match r with
  | .proof ps _ => .proof (ps.map f₁) (by simpa)
  | .refutation rs _ => .refutation (rs.map f₂) (by simpa)
  /-  (λ pf ↦ by
          let res := (Proof.castSeqList pf).map f₁
          exact Proof.castSeqList res)
        (λ rs ↦ by
          let res := (Refutation.castSeqList rs).map f₂
          exact Refutation.castSeqList res
            ) -/

/- def Result.map2proofList (r₁ : Result s1 b1 h1) (r₂ : Result s2 b2 h2)
  (fproof : List (Proof s1) →
            List (Proof s2) →
            List (Proof s'))
  (ref₁ : List (Refutation s1 b1 h1) → List (Refutation s' b' h'))
  (ref₂ : List (Refutation s2 b2 h2) → List (Refutation s' b' h')): Result s' b' h':=
  match r₁, r₂ with
  | .proof ps₁ _, .proof ps₂ _ => .proof (fproof ps₁ ps₂) (by sorry)
  | .refutation rs₁ _, .refutation rs₂ _ => .refutation ( ref₁ rs₁ ++ ref₂ rs₂) (by sorry)
  | .refutation  rs _ , _ => .refutation (ref₁ rs) (by sorry)
  | _, .refutation rs _ => .refutation (ref₂ rs) (by sorry)
 -/

def Result.map2proof (r₁ : Result s1 b1 h1) (r₂ : Result s2 b2 h2)
  (fproof : (Proof s1) →
           (Proof s2) →
           (Proof s'))
  (ref₁ : (Refutation s1 b1 h1) → (Refutation s' b' h'))
  (ref₂ : (Refutation s2 b2 h2) → (Refutation s' b' h')): Result s' b' h':=
  match r₁, r₂ with
  | .proof pf₁ _, .proof pf₂ _ => .proof ((List.product (Proof.castSeqList pf₁) (Proof.castSeqList pf₂ )).map (fproof).uncurry) (by simp; grind)
  | .refutation rs₁ _, .refutation rs₂ _ => .refutation ( rs₁.map ref₁ ++ rs₂.map ref₂) (by simp; grind only)
  | .refutation  rs _, _ => .refutation (rs.map ref₁) (by simpa)
  | _, .refutation rs _ => .refutation (rs.map ref₂) (by simpa)
/-
have mmm := --premise.map ruleP ruleR
          premise.map
                (λ pf ↦ by
                  let res := (Proof.castSeqList pf).map ruleP
                  exact Proof.castSeqList res)
                (λ rs ↦ by
                  let res := (Refutation.castSeqList rs).map ruleR
                  exact Refutation.castSeqList res
                    )
                     -/

-- [[1,2] [3] [4,5]] = [[1,3,4] [1,3,5] [2,3,4] [2,3,5]]
def choicesCM : List (List CM) → List (List CM)
| [] => [[]]
| [] :: _ => []
| (x :: xs) :: xss =>
    (choicesCM xss).map (fun ys => x :: ys) ++
    choicesCM (xs :: xss)

/-- Picks only proofs if any, else returns []  -/
def pickproof : List (List A ⊕ List B) → List (List A) ⊕ List (List B)
| [] => .inl []
| .inl a::as =>
  match pickproof as with
  | .inl as' => .inl (a::as')
  | .inr _ => .inl [a]
| .inr b::bs =>
  match pickproof bs with
  | .inl as => .inl as
  | .inr bs' => .inr (b::bs')



def automatedProof.botr_
    (s : Seq4Proof)
(cap : ℕ)
(as : List Atom)
(fL : List Form)
(block : List Imp)
(bs : List Atom)
(fR : List Form)
(impR hist : List Imp)
(a b : Form)
(succForms : List Form)
(premise₁ : Result
  { Γ := ↑(List.map Form.atoms as ++ List.map Imp.toForm block),
    Δ := ↑(List.map Form.atoms bs ++ a :: (succForms ++ List.map Imp.toForm impR)) }
  block hist)
(premise₂ : Result
  { Γ := ↑(List.map Form.atoms as ++ List.map Imp.toForm block),
    Δ := ↑(List.map Form.atoms bs ++ b :: (succForms ++ List.map Imp.toForm impR)) }
  block hist)
: Result
  { Γ := ↑(List.map Form.atoms as ++ List.map Imp.toForm block),
    Δ := ↑(List.map Form.atoms bs ++ (a ∧∧ b) :: (succForms ++ List.map Imp.toForm impR)) }
  block hist
    := by

  let xs := (as.map .atoms) ++ (block.map Imp.toForm);
  let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
  have ruleP := andr a b xs ys;
  have ruleR₁ := andr₁ block hist a b xs ys; have ruleR₂ := andr₂ block hist a b xs ys
  exact (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq





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
                   Result s.toSeq s.block s.hist :=
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
            let rule := [ax block hist as bs (by grind)]
            exact Result.refutation rule (by grind)
          --METARULE 1 NONINVERTABLE REEGEL
          | impR => by
            simp only [Seq4Proof.toSeq, List.append_nil]
            let impRApplications :
                List (List (Proof ⟨↑(as.map Form.atoms ++ block.map Imp.toForm), ↑(bs.map Form.atoms ++ impR.map Imp.toForm)⟩)  ⊕
                      List ((a b : Form) × Refutation ⟨↑(a :: as.map Form.atoms ++ block.map Imp.toForm), {b}⟩ [] (⟨a,b⟩ :: hist))) :=

              impR.attach.map (λ (⟨⟨f, g⟩ , ha⟩ : {i : Imp // i ∈ impR}) ↦
                have inclusion : insert { f, g } ( collectImpsForm f ∪ collectImpsForm g) ⊆   impR.toFinset.biUnion collectImpsImp := by
                  intro x hx
                  apply Finset.mem_biUnion.mpr
                  refine ⟨⟨f,g⟩, by simpa using ha, ?_⟩
                  simp [collectImpsImp] at hx ⊢
                  exact hx
                have eq : block.toFinset.biUnion collectImpsImp = (block.map Imp.toForm ).toFinset.biUnion collectImpsForm := by ext x; simp [Finset.mem_biUnion]

                have premise := automatedProof ⟨as, (f :: (block.map Imp.toForm)), [], [], [g], [], (⟨ f, g⟩ :: hist)⟩ cap (by grw [← hcap]; simp; apply Finset.card_le_card ?_; grind) (by simp)
                let xs := as.map Form.atoms ++ block.map Imp.toForm; let ys := bs.map Form.atoms ++ (impR.erase ⟨f, g⟩).map Imp.toForm
                have ruleP := (impr f g xs ys)
                --have ruleR := (Refutation.impr block hist as bs impR (by grind))
                match premise with
                | .proof pf _ => .inl (pf.map (λ p ↦ (ruleP p.castSeq).castSeq))
                | .refutation rf _ => .inr (rf.map (λ p ↦ ⟨ f, g , p.castSeq⟩))
                --(premise.castSeq.map (b := []) (h := ⟨f, g⟩ :: hist) block hist ruleP (λ r ↦ (ruleR r).castSeq)).castSeq
              )
            let res := pickproof impRApplications
            match _ : pickproof impRApplications with
            | .inl pf => exact Result.proof pf.flatten (by rename_i h; subst_eqs; simp [pickproof] at h; sorry)
            | .inr rfs =>
              have choices := choicesCM rfs
              have ruleR := (Refutation.impr block hist as bs impR (by grind))
              exact .refutation (choices.attach.map (λ ⟨c, h⟩ ↦
                                                ruleR (λ a b hab ↦
                                                  (c.findSome? (λ ⟨a', b', r'⟩ ↦
                                                    if _ : a = a' ∧ b = b'
                                                      then some (r'.castSeq (hb := by grind) (hh := by grind))
                                                    else none)).get sorry)
                                                    )
                                ) sorry
        | xs@(_::_) => by
          --have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          --have corr := findIntersCorr as bs
          let proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        ax x ((as.map Form.atoms) ++ (block.map Imp.toForm)) ((bs.map Form.atoms) ++ (impR.map Imp.toForm))
                        (by grind)
                        (by grind))
          simp only [Seq4Proof.toSeq, List.append_nil]; exact Result.proof proofs (by grind)

      -- open up forms on right side
      | (.atoms a) :: succForms =>  --move atom to succ atoms list
        Result.castSeq (automatedProof ⟨as, [], block, a :: bs, succForms, impR, hist⟩ cap)

      | ⊥ :: succForms =>   --botr rule, .bot is ignored
        have premise := automatedProof ⟨as, [], block, bs, succForms, impR, hist⟩ cap
        --simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
        let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := Proof.botr xs ys; have ruleR := Refutation.botr block hist xs ys
        --simp [xs, ys] at ruleP ruleR
        (premise.castSeq.map block hist ruleP ruleR).castSeq

      | (.and a b) :: succForms =>
        have premise₁ := automatedProof ⟨as, [], block, bs, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        --simp [Seq4Proof.toSeq] at premise₁ premise₂ ⊢
        let xs := (as.map .atoms) ++ (block.map Imp.toForm);
        let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := andr a b xs ys;
        have ruleR₁ := andr₁ block hist a b xs ys; have ruleR₂ := andr₂ block hist a b xs ys
        (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

      | (.or a b) :: succForms =>
        have premise := automatedProof ⟨as, [], block, bs, a :: b :: succForms, impR, hist⟩ cap
        let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := orr a b xs ys; have ruleR := orr block hist a b xs ys
        (premise.castSeq.map block hist ruleP ruleR).castSeq

      | (.imp a b) :: succForms =>  --METARULE 2 apply afort only when R→ has been used (if it is in usedImps₂. else: läheb imps listi)
        if inc : ⟨a,b⟩ ∈ hist then
          have premise := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
          let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
          have ruleP := afort a b xs ys; have ruleR := afort block hist a b xs ys (by grind)
          (premise.castSeq.map block hist ruleP ruleR).castSeq
        else
          .castSeq (automatedProof ⟨as, [], block, bs, succForms, ⟨a,b⟩ :: impR, hist⟩ cap
                            (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) (by simp at metaR1; simp; grind))


    -- open up forms on left side --
    | (.atoms a) :: antForms =>
      .castSeq (automatedProof ⟨as ++ [a], antForms, block, bs, fR, impR, hist⟩ cap)

    | .bot :: antForms => by
      let rule := [botl (as.map .atoms ++ antForms ++ (block.map Imp.toForm)) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm))]
      simp only [Seq4Proof.toSeq]
      exact .proof (Proof.castSeqList rule) (by grind)

    | (.and a b) :: antForms =>
      have premise := automatedProof ⟨as, a :: b :: antForms, block, bs, fR, impR, hist⟩ cap
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := (andl a b xs ys); have ruleR := (Refutation.andl block hist a b xs ys)
      (premise.castSeq.map block hist ruleP ruleR).castSeq


    | (.or a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, a :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have premise₂ := automatedProof ⟨as, b :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := orl a b xs ys; have ruleR₁ := orl₁ block hist a b xs ys; have ruleR₂ := orl₂ block hist a b xs ys
      (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

    | (.imp a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, antForms, ⟨a, b⟩ :: block, bs, a::fR, impR, hist⟩ cap
      have premise₂ := automatedProof ⟨as, b::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := impl a b xs ys; have ruleR₁ := impl₁ block hist a b xs ys; have ruleR₂ := impl₂ block hist a b xs ys
      (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq



termination_by s.weight cap hcap
decreasing_by
all_goals simp_all [Seq4Proof.weight, Weight.instLT, Weight.instWellFoundedRelation]; try grind [Seq4Proof.weight, Weight.instWellFoundedRelation, Weight.instLT];
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
. sorry
 /- simp at *
  have hx : { f, g} ∉ hist := by
    intro hmem
    have : { f, g} ∈ impR ∩ hist := List.mem_inter_of_mem_of_mem ha hmem
    simp [metaR1] at this
  have hxFin : { f, g} ∉ hist.toFinset := by simp; exact hx
  have hcard : hist.toFinset.card < (insert { f, g} hist.toFinset).card := by
    have : (insert { f, g} hist.toFinset).card = hist.toFinset.card + 1 := Finset.card_insert_of_notMem hxFin
    grind
  sorry
. simp [Seq4Proof.weight, Weight.wellFoundedRelation, Weight.instLT] -/




def automatedProofHelper (s : Sequent) : Std.Format :=
  have res := automatedProof s.toSeq4 s.toSeq4.cap.card (by simp) (by simp [Sequent.toSeq4])

  match res with
  | .proof ps => String.toFormat (listProofToString ps)
  | .refutation rf => dbg_trace s!"{rf.length}"; String.toFormat (listRefutationToString rf)
/-     if cms.all (fun cm => evalSeq s cm == TV.f) then
      let strs := cms.map toString
      String.toFormat ("CM: [" ++ String.intercalate "]\n[ " strs ++ "]")
    else  dbg_trace "APPI {cms.map (fun cm => evalSeq s cm) }"
      let strs := cms.map toString
      String.toFormat ("CM: [" ++ String.intercalate "]\n[ " strs ++ "]") -/


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
