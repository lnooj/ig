import Mathlib.Data.Nat.Cast.Order.Ring

import Logic.MultiSuccCorsiTassi.Display
import Logic.MultiSuccCorsiTassi.Result


def List.mapNonempty {α β : Type*} (f : α → β) (xs : List α) (h : xs ≠ []) : {ys : List β // ys ≠ []} :=
  ⟨xs.map f, by simp [h]⟩

def List.unattach_ne (hnotempty : ¬rfs = []) : ¬rfs.unattach = [] := by
  intro h
  have : rfs.unattach = [] → rfs = [] := by apply List.map_eq_nil_iff.mp
  grind

namespace multiSucc
open multiSucc

--deriving Repr
open Proof
open Refutation

/-! # choices -/
-- [[1,2] [3] [4,5]] = [[1,3,4] [1,3,5] [2,3,4] [2,3,5]]
def choices : List (List CM) → List (List CM)
| [] => []
| [x] => x.map ([·])
| x::y::xs => x.product (choices (y::xs)) |>.map (fun ⟨a, as⟩ ↦ a :: as)

@[grind =, simp]
theorem choices_eq_nil {xs : List (List α)} : choices xs = [] ↔ xs = [] ∨ [] ∈ xs := by
  fun_induction choices with
  | case1 => simp
  | case2 => simp
  | case3 => simp_all; grind only [= List.prodcut_eq_nil]

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
theorem subtype_val_flatten_notEmpty
(pf : List { pfs // pfs ≠ [] })
(h : pickProof impRApplications = Sum.inl pf)
: (List.map Subtype.val pf).flatten ≠ [] := by
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
            Refutation { Γa := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm block), Γb := ∅, Δ := {b} }
              ({ f := a, g := b } :: hist)) // rf ≠ [] }) : [] ∉ rfs.unattach := by
  simp_all only [ne_eq, List.mem_unattach, not_true_eq_false, IsEmpty.exists_iff, not_false_eq_true]


@[grind .]
theorem impR_cap
(block : List Imp)
(hist : List Imp)
(impR : List Imp)
(ha : { f := f, g := g } ∈ impR)
: insert { f := f, g := g }
    (collectImpsForm f ∪
      ((List.map Imp.toForm block).toFinset.biUnion collectImpsForm ∪ (collectImpsForm g ∪ hist.toFinset))) ⊆
  block.toFinset.biUnion collectImpsImp ∪ (impR.toFinset.biUnion collectImpsImp ∪ hist.toFinset) := by
  have inclusion : insert { f, g } ( collectImpsForm f ∪ collectImpsForm g) ⊆ impR.toFinset.biUnion collectImpsImp := by
    intro x hx
    simp at hx
    rcases hx with head | tail₁ | tail₂
    all_goals simp_all; grind
  have eq : block.toFinset.biUnion collectImpsImp = (block.map Imp.toForm).toFinset.biUnion collectImpsForm := by ext x; simp [Finset.mem_biUnion]
  grind



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
          if h : impR = [] then by
            subst_eqs
            simp [Seq4Proof.toSeq, List.append_nil]
            let rule := [ax hist as bs block (by grind)]
            exact Result.refutation rule (by grind)
          --METARULE 1 NONINVERTABLE REEGEL
          else by
            simp only [Seq4Proof.toSeq, List.append_nil]
            have ⟨impRApplications, hnotempty⟩ :
            -- find either a list of proofs for any of the imps, if none found, get the function required to get ALL refutations
                {l : List (
                  {pf : List (Proof ⟨↑(as.map Form.atoms), ↑block, ↑(bs.map Form.atoms ++ impR.map Imp.toForm)⟩) // pf ≠ []} ⊕
                  {rf : List ((a b : Form) × Refutation ⟨↑(a :: as.map Form.atoms ++ block.map Imp.toForm), {}, {b}⟩ (⟨a,b⟩ :: hist)) // rf ≠ []}
                ) // l ≠ []} :=
                impR.attach.mapNonempty (λ (⟨⟨f, g⟩ , ha⟩ : {i : Imp // i ∈ impR}) ↦
                  have premise := automatedProof ⟨as, (f :: (block.map Imp.toForm)), [], [], [g], [], (⟨ f, g⟩ :: hist)⟩ cap
                                                  (by grw [← hcap]; simp; apply Finset.card_le_card ?_; simp_all; grind) (by simp)
                  let xs := as.map Form.atoms; let ys := bs.map Form.atoms ++ (impR.erase ⟨f, g⟩).map Imp.toForm
                  have ruleP := impr f g xs ys block
                  match premise with
                  | .proof pf neqE => .inl ⟨pf.map (λ p ↦ (ruleP p.castSeq).castSeq), by simpa using neqE⟩
                  | .refutation rf neqE => .inr ⟨rf.map (λ p ↦ ⟨f, g, p.castSeq⟩), by simpa using neqE⟩
                ) (List.attach_ne_nil_iff.mpr h)

            --let neqE : impRApplications.filterMap Sum.getLeft? = some ys
            match hpick : pickProof impRApplications with
            | .inl pf => exact Result.proof (pf.map Subtype.val |>.flatten) (by grind [subtype_val_flatten_notEmpty])
            | .inr rfs =>
              let choices := choices (rfs.map Subtype.val) --all dif ways to construct refutation
              have ruleR := (Refutation.impr hist as bs impR block (by grind)) --new parent to choices
              exact .refutation (choices.attach.map (λ ⟨c, h⟩ ↦
                                                ruleR (λ a b hab ↦
                                                      (c.findSome? (λ ⟨a', b', r'⟩ ↦ -- find the same imp in child as in parent
                                                        if _ : a = a' ∧ b = b'
                                                          then some (r'.castSeq (hb := by grind) (hh := by grind) (hc := by grind))
                                                        else none)).get (by simp; sorry))--prove that same imps can be found in choices as in parent
                                                    )
                                ) (by simp [choices]; apply List.attach_eq_nil_iff.not.mpr; simp; apply List.unattach_ne (by simp_all))
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
