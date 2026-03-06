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


namespace multiSucc
open multiSucc

--deriving Repr
open Proof
open Refutation

--give sequent, hist, blocked
inductive Result (s : Sequent) /- (block : List Imp)-/ (hs : List Imp)  where
| proof : List (Proof (⟨s.Γ /- ∪ (block.map Imp.toForm)  -/, s.Δ⟩ )) → Result s hs /- block hist -/
--| cm : List Model → Result s/-  block hist -/
| refutation : List (Refutation s hs)  → Result s hs
-- | refutation List (Refutation (s, h, impB))

def Result.proofs : Result s h → List (Proof s)
| .proof pf => pf
| _ => []

def Result.refutations : Result s h → List (Refutation s h)
| .refutation rs => rs
| _ => []

def Result.refutationss : List (Result s h) → List (Refutation s h)
| r :: rs =>
  match r with
  | .refutation rfs => rfs ++ Result.refutationss rs
  | _ =>  Result.refutationss rs
| [] => []

def Result.proofss : List (Result s h) → List (Proof s)
| r :: rs =>
  match r with
  | .proof pf => pf ++ Result.proofss rs
  | _ => Result.proofss rs
| [] => []

def Proof.castSeq (x : Proof ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩)
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    Proof ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩ := by rw [ha, hb] at x; exact x

def Proof.castSeqList (x : List (Proof ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Proof ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩) := by rw [ha, hb] at x; exact x

def Refutation.castSeqList (x : List (Refutation ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩ h))
    (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
    (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
    List (Refutation ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩ h) := by rw [ha, hb] at x; exact x

def Result.castSeq (x : Result ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩ hist)
  (ha : Multiset.ofList a₁ = Multiset.ofList a₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind)
  (hb : Multiset.ofList b₁ = Multiset.ofList b₂ := by first | rfl | simp only [Multiset.coe_eq_coe]; grind) :
  Result ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩ hist := by rw [ha, hb] at x; exact x

def Result.map' (r : Result s h)
  (f₁ : List (Proof s) → List (Proof s'))
  (f₂ : List (Refutation s h) → List (Refutation s' h')): Result s' h':=
  match r with
  | .proof ps => .proof (f₁ ps)
  | .refutation rs   => .refutation (f₂ rs)

def Result.map (r : Result  ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩ h)
  (f₁ : Proof  ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩ → Proof ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩)
  (f₂ : Refutation  ⟨Multiset.ofList a₁, Multiset.ofList b₁⟩ h → Refutation ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩ h') :
  Result ⟨Multiset.ofList a₂, Multiset.ofList b₂⟩ h' :=
  r.map' (λ pf ↦ by
          let res := (Proof.castSeqList pf).map f₁
          exact Proof.castSeqList res)
        (λ rs ↦ by
          let res := (Refutation.castSeqList rs).map f₂
          exact Refutation.castSeqList res
            )

def Result.map2proof (r₁ : Result s1 h1) (r₂ : Result s2 h2)
  (fproof : List (Proof s1) → List (Proof s2) → List (Proof s'))
  (ref₁ : List (Refutation s1 h1) → List (Refutation s' h'))
  (ref₂ : List (Refutation s2 h2) → List (Refutation s' h')): Result s' h':=
  match r₁, r₂ with
  | .proof ps₁, .proof ps₂ => .proof (fproof ps₁ ps₂)
  | .refutation rs₁, .refutation rs₂  => .refutation ( ref₁ rs₁ ++ ref₂ rs₂)
  | .refutation rs, _ => .refutation (ref₁ rs)
  | _, .refutation rs => .refutation (ref₂ rs)
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
def pickproof : List (Result s h) → List (Result s h)
| rs =>
  rs.filter (fun
    | Result.proof _ => true
    | _ => false)




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
                   Result s.toSeq s.hist:=
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
            have rule := [ax hist as bs block (by grind)]
            exact Result.refutation rule
          --METARULE 1 NONINVERTABLE REEGEL
          | impR => by
            simp only [Seq4Proof.toSeq, List.append_nil]
            let impRApplications : List (Result ⟨↑(as.map Form.atoms ++ block.map Imp.toForm), ↑(bs.map Form.atoms ++ impR.map Imp.toForm)⟩ hist) :=
              impR.attach.map (λ (⟨⟨f, g⟩ , ha⟩ : {i : Imp // i ∈ impR}) ↦ by

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
                have ruleR := (impr hist f g as bs block (impR.erase ⟨f, g⟩) (by grind))

                simp at premise
                have mmm := --premise.map ruleP ruleR
                  premise.map'
                  (λ pf ↦ Proof.castSeqList ((Proof.castSeqList pf).map ruleP))
                  (λ rs ↦ Refutation.castSeqList ((Refutation.castSeqList rs).map ruleR))
                have erase :  Multiset.ofList ((f ⊃ g) :: (List.map Form.atoms bs ++ List.map Imp.toForm (impR.erase { f := f, g := g }))) =
                              Multiset.ofList (List.map Form.atoms bs ++ List.map Imp.toForm impR) := by simp; grind
                rw [erase] at mmm; exact mmm
              )
            have res := pickproof impRApplications
            if res ≠ [] then
              exact Result.proof <| (Result.proofss res)
            else -- res contains only cm results

              exact dbg_trace s!"res:{impRApplications.length},{( Result.refutationss impRApplications).length}, {( Result.proofss impRApplications).length}";Result.refutation <| (Result.refutationss impRApplications)

        | xs => by
          --have Γ : ∀ x ∈ xs, x ∈ (findIntersection as bs) := by simp [common]
          --have corr := findIntersCorr as bs
          have proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        ax x ((as.map Form.atoms) ++ (block.map Imp.toForm)) ((bs.map Form.atoms) ++ (impR.map Imp.toForm))
                        (by grind)
                        (by grind))
          simp only [Seq4Proof.toSeq, List.append_nil]; exact Result.proof proofs

      -- open up forms on right side
      | (.atoms a) :: succForms =>  --move atom to succ atoms list
        Result.castSeq (automatedProof ⟨as, [], block, a :: bs, succForms, impR, hist⟩ cap)

      | ⊥ :: succForms => by  --botr rule, .bot is ignored
        have premise := automatedProof ⟨as, [], block, bs, succForms, impR, hist⟩ cap
        simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
        let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := botr xs ys; have ruleR := botr hist xs ys
        have mmm := --premise.map ruleP ruleR
          premise.map'
                (λ pf ↦ Proof.castSeqList ((Proof.castSeqList pf ).map ruleP))
                (λ rs ↦ Refutation.castSeqList ((Refutation.castSeqList rs).map ruleR))
        exact Result.castSeq mmm

      | (.and a b) :: succForms =>
        have premise₁ := automatedProof ⟨as, [], block, bs, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        Result.map2proof premise₁ premise₂
          (λ pf₁ pf₂ ↦
          have rule := (getPairs (Proof.castSeqList pf₁) (Proof.castSeqList pf₂ )).map (andr a b xs ys).uncurry
          Proof.castSeqList rule)
          (λ rs₁ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₁).map (andr₁ hist a b xs ys)))
          (λ rs₂ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₂).map (andr₂ hist a b xs ys)))

      | (.or a b) :: succForms =>
        have premise := automatedProof ⟨as, [], block, bs, a :: b :: succForms, impR, hist⟩ cap
        let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := (orr a b xs ys); have ruleR := orr hist a b xs ys
        premise.map'
          (λ pf ↦ Proof.castSeqList ((Proof.castSeqList pf).map ruleP))
          (λ rs ↦ Refutation.castSeqList ((Refutation.castSeqList rs).map ruleR))

      | (.imp a b) :: succForms =>  --METARULE 2 apply afort only when R→ has been used (if it is in usedImps₂. else: läheb imps listi)
        if inc : ⟨a,b⟩ ∈ hist then
          have premise := automatedProof ⟨as, [], block, bs, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
          let xs := (as.map .atoms) ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
          have ruleP := afort a b xs ys; have ruleR := afort hist a b xs ys (by grind)
          premise.map'
            (λ pf ↦ Proof.castSeqList ((Proof.castSeqList pf).map ruleP))
            (λ rs ↦ Refutation.castSeqList ((Refutation.castSeqList rs).map ruleR))
        else
          .castSeq (automatedProof ⟨as, [], block, bs, succForms, ⟨a,b⟩ :: impR, hist⟩ cap
                            (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) (by simp at metaR1; simp; grind))


    -- open up forms on left side --
    | (.atoms a) :: antForms =>
      .castSeq (automatedProof ⟨as ++ [a], antForms, block, bs, fR, impR, hist⟩ cap)

    | .bot :: antForms => by
      have rule := [botl (as.map .atoms ++ antForms ++ (block.map Imp.toForm)) ((bs.map .atoms) ++ fR ++ (impR.map Imp.toForm))]
      simp only [Seq4Proof.toSeq]
      exact .proof (Proof.castSeqList rule)

    | (.and a b) :: antForms =>
      have premise := automatedProof ⟨as, a :: b :: antForms, block, bs, fR, impR, hist⟩ cap
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := (andl a b xs ys); have ruleR := (Refutation.andl hist a b xs ys)
      premise.map'
        (λ pf ↦ Proof.castSeqList ((Proof.castSeqList pf).map ruleP))
        (λ rs ↦ Refutation.castSeqList ((Refutation.castSeqList rs).map ruleR))

    | (.or a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, a :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have premise₂ := automatedProof ⟨as, b :: antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      Result.map2proof premise₁ premise₂
          (λ pf₁ pf₂ ↦ by
          have rule := (getPairs (Proof.castSeqList pf₁) (Proof.castSeqList pf₂ )).map
                          (orl a b xs ys).uncurry
          exact Proof.castSeqList rule)
          (λ rs₁ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₁).map ((Refutation.orl₁ hist a b xs ys))))
          (λ rs₂ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₂).map ((Refutation.orl₂ hist a b xs ys))))

    | (.imp a b) :: antForms =>
      have premise₁ := automatedProof ⟨as, antForms, ⟨a, b⟩ :: block, bs, a::fR, impR, hist⟩ cap
      have premise₂ := automatedProof ⟨as, b::antForms, block, bs, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (as.map .atoms) ++ antForms ++ (block.map Imp.toForm); let ys := (bs.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      Result.map2proof premise₁ premise₂
          (λ pf₁ pf₂ ↦ by
          have rule := (getPairs (Proof.castSeqList pf₁) (Proof.castSeqList pf₂ )).map
                          (impl a b xs ys).uncurry
          exact Proof.castSeqList rule)
          (λ rs₁ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₁).map (Refutation.impl₁ hist a b xs ys)))
          (λ rs₂ ↦ Refutation.castSeqList ((Refutation.castSeqList rs₂).map (Refutation.impl₂ hist a b xs ys)))


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
