import Logic.MultiSuccCorsiTassi.Refutation
import Logic.MultiSuccCorsiTassi.Kripke

namespace multiSucc
open multiSucc


@[simp, grind]
def Refutation.getCM (ref : Refutation s h) :  Model :=
match ref with
| ax hs as bs bl pf => ⟨⟨as.toFinset, bs.toFinset⟩, []⟩
| botr hs xs ys bl prem
| andl hs a b xs ys bl prem
| andr₁ hs a b xs ys bl prem
| andr₂ hs a b xs ys bl prem
| orl₁ hs a b xs ys bl prem
| orl₂ hs a b xs ys bl prem
| orr hs a b xs ys bl prem
| impl₁ hs a b xs ys bl prem
| impl₂ hs a b xs ys bl prem
| afort hs a b xs ys bl pf prem => prem.getCM
| impr hs as bs ys bl pf prem =>
  let children : List Model := ys.attach.map (λ ⟨⟨a, b⟩, yh⟩ ↦ (prem a b yh).getCM)
  let cUn := Models.getRejected children
  ⟨⟨as.toFinset, bs.toFinset ∪ cUn⟩, children⟩
  -- add children.rejected to bs. this is necessary bc without it you can't prove ref.getCM.wf. goal would be b ∈ bs which is not true


@[simp, grind .]
theorem Refutation.ant_atom_forced (r : Refutation s h)
  (ha : Form.atom a ∈ s.Γ) : a ∈ r.getCM.world.forced := by
  induction r generalizing a <;> simp_all

@[simp, grind .]
theorem Refutation.ant_atom_rejected (r : Refutation s h)
  (ha : Form.atom a ∈ s.Δ) : a ∈ r.getCM.world.rejected := by
  induction r generalizing a <;> simp_all

/- def Result.getCMs (r : Result s b h) : List Model :=
match r with
| refutation rfs _ => rfs.map (λ rf ↦ Refutation.getCM rf )
| _ => [] -/

--@[simp, grind =]
theorem Refutation.cm_wf (r : Refutation s h) : r.getCM.wf := by
  induction r <;> try (rw [Refutation.getCM]; assumption)
  . rw [Refutation.getCM, Model.wf]; simp
  . rename_i hs as bs ys bl i prem ih; simp_all; rw [Model.wf]; simp;
    intro m imp imp_in imp_m; let ⟨f,g⟩ := imp; subst_eqs; simp_all
    specialize ih f g imp_in; --specialize prem f g imp_in
    split_ands
    . intro a ha
      have ha_forced : a ∈ (prem f g imp_in).getCM.world.forced := by
          apply Refutation.ant_atom_forced (prem f g imp_in)
          simp_all
      exact ha_forced
    . intro b hb
      suffices mm : b ∈ Models.getRejected (ys.attach.map (fun ⟨⟨a, b⟩, h⟩ => (prem a b h).getCM)) by simp_all
      have hmem : b ∈ (prem f g imp_in).getCM.world.rejected := by grind
      apply Models.getRejected_elem (by grind) b hmem


/- TODO: problem with proving that all left imp sides in hist list evaluate to true -/
theorem Refutation.completeness (s : Sequent) ( r : Refutation s h) :
  /- (i : (evalAnt s.Γ r.getCM ∧ h.eval r.getCM ) = TV.t) -/
      s.evalR h r.getCM = TV.f := by
  have wf := r.cm_wf
  induction r with
  | ax hs as bs bl i =>
    simp only [getCM] at wf ⊢
    simp_all
    constructor
    . constructor
      . intro x hx; rw [Form.eval]; simp_all
      . grind [evalBlocked_true_iff]
    . intro x hx; rw [Form.eval]; simp_all
      rw [List.inter_eq_nil_iff_disjoint] at i;
      exact Not.imp (id (List.Disjoint.symm i) hx) fun a => a
  | botr => simp_all
  | andl => simp_all
  | andr₁ => simp_all
  | andr₂ => simp_all
  | orl₁ => simp_all
  | orl₂ => simp_all
  | orr => simp_all
  | impr hs as bs ys bl i prem ih =>
    simp_all; rw [Model.wf] at wf; simp_all
    constructor
    . constructor
      . intro x ih; rw [Form.eval]; simp_all
      . intro ib hib; rw [evalBlocked_true_iff]; simp_all; grind
    . intro x h
      rcases h with ⟨ato, in_bs, h₁, _⟩ | ⟨imp, in_ys, h₄, _⟩
      . rw [Form.eval]; simp_all
        rw [List.inter_eq_nil_iff_disjoint] at i
        exact Not.imp (id (List.Disjoint.symm i) in_bs) fun a => a
      . grind [eval_imp_false_iff]

  | impl₁ hs a b xs ys bl prem ih =>
    simp at ⊢ wf ih
    grind [eval_imp_true_iff, evalBlocked_true_iff]
  | impl₂ hs a b xs ys prem ih => grind [b_true_then_imp_true_branch]
  | afort hs a b xs ys bl pf prem ih =>
    simp only [getCM] at wf
    specialize ih wf
    simp_all
    rcases ih with ⟨h₁, h₂, h₃⟩
    rw [eval_imp_false_iff]; simp_all; left
    sorry
    --have a_in_xs := Refutation.afort_corr pf prem
    --grind

end multiSucc
#min_imports
