import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Kripke
import Logic.MultiSuccCorsiTassi.Proof
import Logic.MultiSuccCorsiTassi.MultiSuccCorsiTassi

namespace multiSucc
open multiSucc


@[simp, grind]
def Refutation.getCM (ref : Refutation s b h) :  Model :=
match ref with
| ax bl hs as bs pf => ⟨⟨as.toFinset, bs.toFinset⟩, []⟩
| botr bl hs xs ys prem =>  prem.getCM
| andl bl hs a b xs ys prem => prem.getCM
| andr₁ bl hs a b xs ys prem => prem.getCM
| andr₂ bl hs a b xs ys prem => prem.getCM
| orl₁ bl hs a b xs ys prem => prem.getCM
| orl₂ bl hs a b xs ys prem => prem.getCM
| orr bl hs a b xs ys prem => prem.getCM
| impr bl hs as bs ys pf prem =>
  let children : List Model := ys.attach.map (λ ⟨⟨a, b⟩, yh⟩ ↦ (prem a b yh ).getCM)
  let cUn := Models.getUnforced children
  ⟨⟨as.toFinset, bs.toFinset ∪ cUn⟩, children⟩-- add children unforced to bs
| impl₁ bl hs a b xs ys prem => prem.getCM
| impl₂ bl hs a b xs ys prem => prem.getCM
| afort bl hs a b xs ys pf prem => prem.getCM

/- def Refutation.getPremise  (ref : Refutation s b h) : (List (Refutation s' b' h') ⊕ Refutation s' b' h') :=
match ref with
| ax bl hs as bs pf => .inl []
| botr bl hs xs ys prem =>  .inr (prem )
| andl bl hs a b xs ys prem => .inr prem
| andr₁ bl hs a b xs ys prem => .inr prem
| andr₂ bl hs a b xs ys prem => .inr prem
| orl₁ bl hs a b xs ys prem => .inr prem
| orl₂ bl hs a b xs ys prem => .inr prem
| orr bl hs a b xs ys prem => .inr prem
| impr bl hs as bs ys pf prem =>
  have children := ys.attach.map (λ ⟨⟨a, b⟩, yh⟩ ↦ (prem a b yh ))
  .inl children
| impl₁ bl hs a b xs ys prem => .inr prem
| impl₂ bl hs a b xs ys prem => .inr prem
| afort bl hs a b xs ys pf prem => .inr prem
 -/

def Result.getCMs (r : Result s b h) : List Model :=
match r with
| refutation rfs _ => rfs.map (λ rf ↦ Refutation.getCM rf )
| _ => []

--@[simp, grind =]
theorem Refutation.cm_wf (r : Refutation s b h) : r.getCM.wf := by
  induction r <;> try (rw [Refutation.getCM]; assumption)
  . rw [Refutation.getCM, Model.wf]; simp
  . rename_i i a ih; simp_all; rw [Model.wf]; simp;
    intro m imp imp_in imp_m; let ⟨f,g⟩ := imp
    specialize ih f g imp_in; --specialize a f g imp_in
    simp_all; set r := a f g imp_in


    sorry




/- lemma Refutation.impr_a_eval {a b : Form}
  (prem : Refutation
    { Γ := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm xs), Δ := {b} }
       ({ f := a, g := b } :: hs)) :
  Form.eval a (Refutation.impr hs a b as bs xs ys i prem).getCM = TV.t := by
  rw [getCM]
  sorry -/

/- theorem if_hs_then_impr
  (pf : { f := a, g := b } ∈ hs) (r : Refutation { Γ := ↑xs, Δ := ↑((a ⊃ b) :: ys) } hs ) :
  Refutation.impr ∈ r -/
--TODO


theorem Refutation.afort_corr {hs : List Imp} {a b : Form}
  (pf : { f := a, g := b } ∈ hs)
  (r : Refutation s bl hs )
  (wf : r.getCM.wf)
  --(hΔ : s.Δ = ↑((a ⊃ b) :: ys))
  : a.eval r.getCM = .t := by
  induction r  with
  | ax => simp_all; sorry
  | botr => simp_all
  | andl => simp_all
  | andr₁ => simp_all
  | andr₂ => simp_all
  | orl₁ => simp_all
  | orl₂ => simp_all
  | orr => simp_all
  | impr bl hs' as bs ys i prem ih =>
    simp_all; --rw [Model.wf] at wf; simp_all
    have : { f := a, g := b } ∈ ys := sorry
    have swf := wf; rw [Model.wf] at swf
    simp_all
    specialize ih a b this (by grind); specialize prem a b
    sorry--let := Model.momo_branch_true wf (by sorry) (by sorry)
  | impl₁ => simp_all
  | impl₂ => simp_all
  | afort =>  simp_all


theorem Refutation.blocked_corr {i : Imp}
  (r : Refutation { Γ := ↑(List.map Form.atoms as),
                    Δ := ↑(List.map Form.atoms bs) } bl hs)
  (ixs : i ∈ bl) : i.g.eval r.getCM = TV.t := sorry

theorem Refutation.correctness :
  ∀ (s : Sequent) ( r : Refutation s b h) (wf : r.getCM.wf )
    /- (histh : ⟨f,g⟩ ∈ h → f.eval r.getCM = TV.t) -/,
      evalSeq s r.getCM = TV.f := by
  intro s r wf
  induction r with
  | ax bl hs as bs i =>
    simp only [getCM] at wf ⊢
    simp_all only [evalSeq_false_iff, evalAnt_eq_true, Multiset.mem_coe, List.mem_append,
      List.mem_map, Imp.toForm, evalSucc_eq_false, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    constructor
    . intro x hx
      rcases hx with hx | h₂
      . obtain ⟨a, ain, a_atom⟩ := hx ; rw [← a_atom]; rw [Form.eval]; simp_all
      . obtain ⟨a, ain, a_imp⟩ := h₂; rw [← a_imp]; rw [Form.eval]; simp_all; sorry --need to show that blocked evaluates to true
    . intro b hb; rw [Form.eval]; simp_all
      rw [List.inter_eq_nil_iff_disjoint] at i;
      exact Not.imp (id (List.Disjoint.symm i) hb) fun a => a
      --have mm :=  List.disjoint_left i
  | botr => simp_all
  | andl => simp_all
  | andr₁ => simp_all
  | andr₂ => simp_all
  | orl₁ => simp_all
  | orl₂ => simp_all
  | orr => simp_all
  | impr bs hs as bs ys i prem ih =>
    simp_all; rw [Model.wf] at wf; simp_all
    intro imp; specialize ih f g
    constructor
    . intro x ih₁
      rcases ih₁ with ⟨ato, in_as, h₃⟩ | ⟨imp, in_bl, h₄⟩
      . subst_eqs; sorry -- atom in as true
      . let ⟨f, g⟩ := imp; sorry -- in blocked true
    . intro x ih₂
      rcases ih₂ with ⟨ato, in_bs, h₃⟩ | ⟨imp, in_ys, h₄⟩
      . subst_eqs; sorry --atom in bs false
      . let ⟨f, g⟩ := imp
        specialize ih f g in_ys; simp_all; sorry -- imp in ys false
  | impl₁ => simp_all
  | impl₂ bl hs a b xs ys prem ih =>
    simp only [getCM] at wf; specialize ih wf
    simp_all
    rcases ih with ⟨⟨h₁, h₂⟩, h₃⟩
    apply b_true_then_imp_true_branch wf h₁

  | afort bl hs a b xs ys pf prem ih =>
    simp only [getCM] at wf
    specialize ih wf
    simp_all
    rcases ih with ⟨h₁, h₂, h₃⟩
    have a_in_xs := Refutation.afort_corr pf prem
    grind
/-   induction r <;> try simp_all
  . sorry
  . rename_i i prem ih
    sorry
  . sorry
  . sorry  -/
--end multiSucc
