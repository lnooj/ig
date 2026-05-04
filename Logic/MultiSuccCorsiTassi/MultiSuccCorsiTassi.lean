import Mathlib.Data.Nat.Cast.Order.Ring

import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Result
import Logic.MultiSuccCorsiTassi.Termination
import Logic.MultiSuccCorsiTassi.Helper

def List.findSome {α β : Type*} (xs : List α) (p : α → Bool) (f : (a : α) → p a → β) (h : ∃ a ∈ xs, p a) : β :=
  xs.findSome? (λ a ↦ if h' : p a then some (f a h') else none ) |>.get (by simp_all)



namespace multiSucc
open multiSucc

--deriving Repr
open Proof
open Refutation

@[grind ., simp]
theorem mem_of_mem_choices_tagged
  (impR hist block : List Imp)
  (as : List Atom)
  (rfs : List
    { rf :
        List ((a : Form) × (b : Form) ×
          Refutation
            { Γa := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm block), Γb := ∅, Δ := {b} }
            ({ f := a, g := b } :: hist))
      // rf ≠ [] })
  (hrows :
    ∀ x ∈ impR,
      ∃ row ∈ rfs.unattach,
        ∀ t ∈ row, t.1 = x.f ∧ t.2.1 = x.g)
  {c : List ((a : Form) × (b : Form) ×
      Refutation
        { Γa := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm block), Γb := ∅, Δ := {b} }
        ({ f := a, g := b } :: hist))}
  {x : Imp}
  (hx : x ∈ impR)
  (hc : c ∈ multiSucc.choices rfs.unattach) :
  ∃ r', ⟨x.f, x.g, r'⟩ ∈ c := by
  obtain ⟨row, hrow, htags⟩ := hrows x hx
  obtain ⟨t, htrow, htc⟩ := mem_of_mem_choices hc hrow
  rcases t with ⟨a, b, r'⟩
  have htag := htags ⟨a, b, r'⟩ htrow
  simp at htag
  rcases htag with ⟨ha, hb⟩
  subst ha
  subst hb
  exact ⟨r', htc⟩


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
  | {aL, fL, block, aR, fR, impR, hist} =>
    match fL with
    | [] =>
      match fR with
      | [] => -- succedent only has atoms left --
        match common : aL ∩ aR with --CHANGED
        -- no common atoms
        | [] =>
          if h : impR = [] then by
            subst_eqs
            simp [Seq4Proof.toSeq, List.append_nil]
            let rule := [ax hist aL aR block (by grind)]
            exact Result.refutation rule (by grind)
          --METARULE 1 NONINVERTABLE REEGEL
          else by
            simp only [Seq4Proof.toSeq, List.append_nil]
            let mkImpRApp :
                {i : Imp // i ∈ impR} →
                  {pf : List (Proof ⟨↑(aL.map Form.atoms), ↑block, ↑(aR.map Form.atoms ++ impR.map Imp.toForm)⟩) // pf ≠ []} ⊕
                  {rf : List ((a b : Form) × Refutation ⟨↑(a :: aL.map Form.atoms ++ block.map Imp.toForm), {}, {b}⟩ (⟨a,b⟩ :: hist)) // rf ≠ []}
                 := (λ (u : {i : Imp // i ∈ impR}) ↦
                  match u with
                  | ⟨⟨f, g⟩, ha⟩ =>
                    have premise := automatedProof ⟨aL, (f :: (block.map Imp.toForm)), [], [], [g], [], (⟨ f, g⟩ :: hist)⟩ cap
                                                    (by grw [← hcap]; simp; apply Finset.card_le_card ?_; simp_all; grind) (by simp)
                    let xs := aL.map Form.atoms
                    let ys := aR.map Form.atoms ++ (impR.erase ⟨f, g⟩).map Imp.toForm
                    have ruleP := impr f g xs ys block
                    match premise with
                    | .proof pf neqE => .inl ⟨pf.map (λ p ↦ (ruleP p.castSeq).castSeq), by simpa using neqE⟩
                    | .refutation rf neqE => .inr ⟨rf.map (λ p ↦ ⟨f, g, p.castSeq⟩), by simpa using neqE⟩)
            let imprA :
            -- find either a list of proofs for any of the imps, if none found, get the function required to get ALL refutations
                {l : List (
                  {pf : List (Proof ⟨↑(aL.map Form.atoms), ↑block, ↑(aR.map Form.atoms ++ impR.map Imp.toForm)⟩) // pf ≠ []} ⊕
                  {rf : List ((a b : Form) × Refutation ⟨↑(a :: aL.map Form.atoms ++ block.map Imp.toForm), {}, {b}⟩ (⟨a,b⟩ :: hist)) // rf ≠ []}
                ) // l ≠ [] } :=
                impR.attach.mapNonempty mkImpRApp (List.attach_ne_nil_iff.mpr h)
            let ⟨impRApplications, hnotempty⟩ := imprA

            match hpick : pickProof imprA.val with
            | .inl pf => exact Result.proof (pf.unattach |>.flatten) (by grind [unattach_flatten_notEmpty])
            | .inr rfs =>
              let choices := choices (rfs.unattach) --all dif ways to construct refutation
              have hrows :
                  ∀ x ∈ impR,
                    ∃ row ∈ rfs.unattach,
                      ∀ t ∈ row, t.1 = x.f ∧ t.2.1 = x.g := by


                have hpick' : imprA.1 = rfs.map Sum.inr := by
                  simpa [pickProof_eq_inr] using hpick
                intro x hx
                have hmem : mkImpRApp ⟨x, hx⟩ ∈ imprA.1 := by --sorry
                  have same : imprA.1 = List.map mkImpRApp impR.attach := by
                    rfl
                  rw [same]
                  refine List.mem_map.mpr ?_
                  exact ⟨⟨x, hx⟩, by simp, rfl⟩
                rw [hpick'] at hmem
                cases hmk : mkImpRApp ⟨x, hx⟩ with
                | inl pf => grind
                | inr row =>
                  use row.1
                  constructor
                  · have hrow : row ∈ rfs := by grind
                    change row.1 ∈ List.map Subtype.val rfs
                    exact List.mem_map.mpr ⟨row, hrow, rfl⟩
                  · intro t ht
                    cases x with
                    | mk f g =>
                      dsimp [mkImpRApp] at hmk
                      split at hmk
                      · cases hmk
                      · simp at hmk
                        rcases hmk with ⟨rfl⟩
                        rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
                        simp


              have ruleR := (Refutation.impr hist aL aR impR block (by grind)) --new parent to choices
              exact .refutation (choices.attach.map (λ ⟨c, h⟩ ↦
                                                ruleR (λ a b hab ↦
                                                      (c.findSome (λ ⟨a', b', r'⟩ ↦ a = a' ∧ b = b') -- find the same imp in child as in parent
                                                                  (λ ⟨a', b', r'⟩ _ ↦ (r'.castSeq (hb := by grind) (hh := by grind) (hc := by grind)))
                                                                  (by
                                                                    obtain ⟨r', hr'⟩ :=
                                                                      mem_of_mem_choices_tagged impR hist block aL rfs hrows hab (by simpa using h)
                                                                    exact ⟨⟨a, b, r'⟩, hr', by simp⟩ )) --prove that same imps can be found in choices as in parent
                                                      )
                                                    )
                                ) (by simp [choices]; apply List.attach_eq_nil_iff.not.mpr; simp; apply List.unattach_ne (by grind))
        | xs@(_::_) => by
          --have Γ : ∀ x ∈ xs, x ∈ (findIntersection as aR) := by simp [common]
          --have corr := findIntersCorr as aR
          let proofs := xs.attach.map (λ ⟨x, hx⟩ ↦
                        Proof.ax x ((aL.map Form.atoms)) ((aR.map Form.atoms) ++ (impR.map Imp.toForm)) block
                        (by grind)
                        (by grind))
          simp only [Seq4Proof.toSeq, List.append_nil]; exact Result.proof proofs (by grind)

      -- open up forms on right side
      | (.atoms a) :: succForms =>  --move atom to succ atoms list
        Result.castSeq (automatedProof ⟨aL, [], block, a :: aR, succForms, impR, hist⟩ cap)

      | ⊥ :: succForms =>   --botr rule, .bot is ignored
        have premise := automatedProof ⟨aL, [], block, aR, succForms, impR, hist⟩ cap
        --simp only [Seq4Proof.toSeq, List.append_nil] at premise ⊢
        let ys := (aR.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := Proof.botr (aL.map .atoms) ys block; have ruleR := Refutation.botr hist (aL.map .atoms) ys block
        --simp [xs, ys] at ruleP ruleR
        (premise.castSeq.map hist ruleP ruleR).castSeq

      | (.and a b) :: succForms =>
        have premise₁ := automatedProof ⟨aL, [], block, aR, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨aL, [], block, aR, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        --simp [Seq4Proof.toSeq] at premise₁ premise₂ ⊢
        let ys := (aR.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := andr a b (aL.map .atoms) ys block;
        have ruleR₁ := andr₁ hist a b (aL.map .atoms) ys block; have ruleR₂ := andr₂ hist a b (aL.map .atoms) ys block
        (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

      | (.or a b) :: succForms =>
        have premise := automatedProof ⟨aL, [], block, aR, a :: b :: succForms, impR, hist⟩ cap
        let xs := aL.map .atoms; let ys := (aR.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := orr a b xs ys block; have ruleR := orr hist a b xs ys block
        (premise.castSeq.map hist ruleP ruleR).castSeq

      | (.imp a b) :: succForms =>  --METARULE 2 apply afort only when R→ has been used (if it is in usedImps₂. else: läheb imps listi)
        if inc : ⟨a,b⟩ ∈ hist then
          have premise := automatedProof ⟨aL, [], block, aR, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
          let xs := aL.map .atoms; let ys := (aR.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
          have ruleP := afort a b xs ys block; have ruleR := afort hist a b xs ys block (by grind)
          (premise.castSeq.map hist ruleP ruleR).castSeq
        else
          .castSeq (automatedProof ⟨aL, [], block, aR, succForms, ⟨a,b⟩ :: impR, hist⟩ cap
                            (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind) (by simp at metaR1; simp; grind))

    -- open up forms on left side --
    | (.atoms a) :: antForms =>
      .castSeq (automatedProof ⟨aL ++ [a], antForms, block, aR, fR, impR, hist⟩ cap)

    | .bot :: antForms => by
      let rule := [botl (aL.map .atoms ++ antForms) ((aR.map .atoms) ++ fR ++ (impR.map Imp.toForm)) block]
      simp only [Seq4Proof.toSeq]
      exact .proof (Proof.castSeqList rule) (by grind)

    | (.and a b) :: antForms =>
      have premise := automatedProof ⟨aL, a :: b :: antForms, block, aR, fR, impR, hist⟩ cap
      let xs := (aL.map .atoms) ++ antForms; let ys := (aR.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := andl a b xs ys block; have ruleR := Refutation.andl hist a b xs ys block
      (premise.castSeq.map hist ruleP ruleR).castSeq

    | (.or a b) :: antForms =>
      have premise₁ := automatedProof ⟨aL, a :: antForms, block, aR, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      have premise₂ := automatedProof ⟨aL, b :: antForms, block, aR, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (aL.map .atoms) ++ antForms; let ys := (aR.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := orl a b xs ys block
      have ruleR₁ := orl₁ hist a b xs ys block; have ruleR₂ := orl₂ hist a b xs ys block
      (Result.map2proof premise₁.castSeq premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

    | (.imp a b) :: antForms =>
      have premise₁ := automatedProof ⟨aL, antForms, ⟨a, b⟩ :: block, aR, a::fR, impR, hist⟩ cap
      have premise₂ := automatedProof ⟨aL, b::antForms, block, aR, fR, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
      let xs := (aL.map .atoms) ++ antForms; let ys := (aR.map .atoms) ++ fR ++ (impR.map Imp.toForm)
      have ruleP := impl a b xs ys block; have ruleR₁ := impl₁ hist a b xs ys block; have ruleR₂ := impl₂ hist a b xs ys block
      (Result.map2proof (premise₁.castSeq) premise₂.castSeq ruleP ruleR₁ ruleR₂).castSeq

termination_by s.weight cap
decreasing_by
  all_goals
    simp_all [Seq4Proof.weight, Weight.lt_iff, Seq4Proof.r]
    try grind [= List.mem_map, -Seq4Proof.weight, Weight.instWellFoundedRelation, Weight.instLT]
  · left
    have hx : { f, g} ∉ hist := by
      intro hmem
      have : { f, g} ∈ impR ∩ hist := List.mem_inter_of_mem_of_mem ha hmem
      simp_all
    have : hist.toFinset.card + 1 ≤ cap := by
      have hxFin : {f, g} ∉ hist.toFinset := by simpa using hx
      have hsubset₁ :
          insert {f, g} hist.toFinset ⊆
            insert {f, g}
              (collectImpsForm f ∪
                ((List.map Imp.toForm block).toFinset.biUnion collectImpsForm ∪
                  (collectImpsForm g ∪ hist.toFinset))) := by
        intro x hx'
        simp only [Finset.mem_insert, Finset.mem_union] at hx' ⊢
        rcases hx' with rfl | hxh
        · simp
        · grind
      have hsubset₂ :
          insert {f, g} hist.toFinset ⊆
            (block.toFinset.biUnion collectImpsImp ∪ (impR.toFinset.biUnion collectImpsImp ∪ hist.toFinset)) :=
        Finset.Subset.trans hsubset₁ (impR_cap block hist impR (f := f) (g := g) ha)
      have hcard :
          (insert {f, g} hist.toFinset).card ≤ cap := by
        exact le_trans (Finset.card_le_card hsubset₂) hcap
      grind
    simp_all
    grind


def automatedProofHelper (s : Sequent) : Std.Format :=
  have res := automatedProof s.toSeq4 s.toSeq4.cap.card (by simp) (by simp [Sequent.toSeq4])

  match res with
  | .proof ps _ =>  dbg_trace s!"have proof {ps.length}"; String.toFormat (listProofToString ps)
  | .refutation rf _ => dbg_trace s!"{rf.length}"; String.toFormat (listRefutationToString rf /- ++ listModelToString (rf.map (λ r ↦ r.getCM)) -/)

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
#eval! automatedProofHelper (seq {⊢ (((p → r) → p) → r)})
--#eval! evaluate (form {((¬ p → ¬ q) → (q → p))})
#print axioms automatedProofHelper
end multiSucc

#min_imports
