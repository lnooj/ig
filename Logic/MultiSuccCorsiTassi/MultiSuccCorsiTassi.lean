import Mathlib.Data.Nat.Cast.Order.Ring

import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Result
import Logic.MultiSuccCorsiTassi.Termination
import Logic.MultiSuccCorsiTassi.Helper


namespace multiSucc
open multiSucc

--deriving Repr
open Proof
open Refutation

abbrev ImpRRefut (hist block : List Imp) (as : List Atom) : Type :=
  (a : Form) × (b : Form) ×
    Refutation
      { Γa := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm block), Γb := ∅, Δ := {b} }
      ({ f := a, g := b } :: hist)

abbrev ImpRRow (impR hist block : List Imp) (as : List Atom)
    (u : {i : Imp // i ∈ impR}) : Type :=
  { rf : List (ImpRRefut hist block as) //
    rf ≠ [] ∧ ∀ t ∈ rf, t.1 = u.1.f ∧ t.2.1 = u.1.g }

@[grind ., simp]
theorem mem_of_mem_choices_tagged
  (impR hist block : List Imp)
  (as : List Atom)
  (rows : List (Σ u : {i : Imp // i ∈ impR}, ImpRRow impR hist block as u))
  (hrows :
    ∀ (x : Imp) (hx : x ∈ impR),
      ∃ rw : ImpRRow impR hist block as ⟨x, hx⟩,
        (⟨⟨x, hx⟩, rw⟩ :
          Σ u : {i : Imp // i ∈ impR}, ImpRRow impR hist block as u) ∈ rows)
  {c : List (ImpRRefut hist block as)}
  {x : Imp}
  (hx : x ∈ impR)
  (hc : c ∈ multiSucc.choices (rows.map (fun tr => tr.2.1))) :
  ∃ r', ⟨x.f, x.g, r'⟩ ∈ c := by
  obtain ⟨row, hrow⟩ := hrows x hx
  have hrow' : row.1 ∈ rows.map (fun tr => tr.2.1) := by
    exact List.mem_map.mpr ⟨⟨⟨x, hx⟩, row⟩, hrow, rfl⟩
  obtain ⟨t, htrow, htc⟩ := mem_of_mem_choices hc hrow'
  rcases t with ⟨a, b, r'⟩
  have htag := row.2.2 ⟨a, b, r'⟩ htrow
  simp at htag
  rcases htag with ⟨ha, hb⟩
  subst a
  subst b
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

            let refut := ImpRRefut hist block aL

            let proof :=
              {pf : List (Proof ⟨↑(aL.map Form.atoms), ↑block,
                ↑(aR.map Form.atoms ++ impR.map Imp.toForm)⟩) // pf ≠ []}

            let row (u : {i : Imp // i ∈ impR}) :=
              ImpRRow impR hist block aL u

            have mkImpRApp : (u : {i : Imp // i ∈ impR}) → proof ⊕ row u
              := λ u ↦
                match u with
                | ⟨⟨f, g⟩, ha⟩ =>
                  have premise := automatedProof ⟨aL, (f :: (block.map Imp.toForm)), [], [], [g], [], (⟨ f, g⟩ :: hist)⟩ cap
                                                  (by grw [← hcap]; simp; apply Finset.card_le_card ?_; simp_all; grind) (by simp)
                  let xs := aL.map Form.atoms
                  let ys := aR.map Form.atoms ++ (impR.erase ⟨f, g⟩).map Imp.toForm
                  have ruleP := impr f g xs ys block
                  match premise with
                  | .proof pf neqE => .inl ⟨pf.map (λ p ↦ (ruleP p.castSeq).castSeq), by simpa using neqE⟩
                  | .refutation rf neqE =>
                      .inr ⟨rf.map (λ p ↦ ⟨f, g, p.castSeq⟩),
                      by simpa using neqE,
                      by
                        intro t ht
                        rcases List.mem_map.mp ht with ⟨p, hp, rfl⟩
                        simp⟩


            let toPick (u : {i : Imp // i ∈ impR}) : proof ⊕ Σ u : {i : Imp // i ∈ impR}, row u :=
            match mkImpRApp u with
            | .inl pf => .inl pf
            | .inr rw => .inr ⟨u, rw⟩

            have imprA :
                {l : List (proof ⊕  Σ u : {i : Imp // i ∈ impR}, row u) //
                  l ≠ [] ∧ l = impR.attach.map toPick} :=
              ⟨impR.attach.map toPick,
                by
                  constructor
                  · exact (impR.attach.mapNonempty toPick (List.attach_ne_nil_iff.mpr h)).2
                  · rfl⟩

            match hpick : pickProof imprA.val with
            | .inl pf => exact Result.proof (pf.unattach |>.flatten) (by grind [unattach_flatten_notEmpty])
            | .inr rows =>
              let rfs : List (List refut) := rows.map (fun tr => tr.2.1)
              let chs := choices rfs --all dif ways to construct refutation
              have hrows :
                  ∀ (x : Imp) (hx : x ∈ impR),
                    ∃ rw : row ⟨x, hx⟩,
                      (⟨⟨x, hx⟩, rw⟩ :
                        Σ u : {i : Imp // i ∈ impR}, row u) ∈ rows := by
                have hpick' : imprA.1 = rows.map Sum.inr := by grind
                  --simpa [pickProof_eq_inr] using hpick
                intro x hx
                have hmem : toPick ⟨x, hx⟩ ∈ imprA.1 := by grind
                  /- rw [imprA.2.2]
                  exact List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩ -/
                rw [hpick'] at hmem
                cases hmk : mkImpRApp ⟨x, hx⟩ with
                | inl pf => grind
                | inr rw =>
                    exact ⟨rw, by simpa [toPick, hmk] using hmem⟩

              have chs_ne : chs ≠ [] := by
                have hpick' : imprA.1 = rows.map Sum.inr := by simpa [pickProof_eq_inr] using hpick
                have rows_ne : rows ≠ [] := by grind
                have rfs_ne : rfs ≠ [] := by simpa [rfs] using rows_ne
                grind


              have ruleR := (Refutation.impr hist aL aR impR block (by grind)) --new parent to choices
              exact .refutation (chs.attach.map (λ ⟨c, h⟩ ↦
                                                ruleR (λ a b hab ↦
                                                      (c.findSome (λ ⟨a', b', r'⟩ ↦ a = a' ∧ b = b') -- find the same imp in child as in parent
                                                                  (λ ⟨a', b', r'⟩ _ ↦ (r'.castSeq (hb := by grind) (hh := by grind) (hc := by grind)))
                                                                  ( by
                                                                    obtain ⟨r', hr'⟩ :=
                                                                      mem_of_mem_choices_tagged impR hist block aL rows hrows hab (by simpa [chs, rfs] using h)
                                                                    exact ⟨⟨a, b, r'⟩, hr', by simp⟩ )) --prove that same imps can be found in choices as in parent
                                                      )
                                                )
                                ) (by
                                  intro hnil
                                  have : chs.attach = [] := List.map_eq_nil_iff.mp hnil
                                  exact (List.attach_ne_nil_iff.mpr chs_ne) this)
        | xs@(_::_) => by
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
        let ys := (aR.map .atoms) ++ succForms ++ (impR.map Imp.toForm)
        have ruleP := Proof.botr (aL.map .atoms) ys block; have ruleR := Refutation.botr hist (aL.map .atoms) ys block
        (premise.castSeq.map hist ruleP ruleR).castSeq

      | (.and a b) :: succForms =>
        have premise₁ := automatedProof ⟨aL, [], block, aR, a :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
        have premise₂ := automatedProof ⟨aL, [], block, aR, b :: succForms, impR, hist⟩ cap (by simp at *; apply le_trans (Finset.card_le_card ?_) hcap; grind)
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
    try grind [Seq4Proof.weight, Weight.instWellFoundedRelation, Weight.instLT]
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
