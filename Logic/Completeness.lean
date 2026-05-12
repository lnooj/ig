import Logic.RIG
import Logic.Kripke

namespace multiSucc
open multiSucc


@[simp, grind]
def RIG.getCM (ref : RIG s h) :  Kripke :=
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
  let children : List Kripke := ys.attach.map (λ ⟨⟨a, b⟩, yh⟩ ↦ (prem a b yh).getCM)
  let cUn := Kripkes.getRejected children
  ⟨⟨as.toFinset, bs.toFinset ∪ cUn⟩, children⟩
  -- add children.rejected to bs. this is necessary bc without it you can't prove ref.getCM.wf. goal would be b ∈ bs which is not true


@[simp, grind .]
theorem RIG.ant_atom_forced (r : RIG s h)
  (ha : Form.atom a ∈ s.Γ) : a ∈ r.getCM.world.forced := by
  induction r generalizing a <;> simp_all

@[simp, grind .]
theorem RIG.ant_atom_rejected (r : RIG s h)
  (ha : Form.atom a ∈ s.Δ) : a ∈ r.getCM.world.rejected := by
  induction r generalizing a <;> simp_all

/- def Result.getCMs (r : Result s b h) : List Kripke :=
match r with
| refutation rfs _ => rfs.map (λ rf ↦ RIG.getCM rf )
| _ => [] -/

--@[simp, grind =]
theorem RIG.cm_wf (r : RIG s h) : r.getCM.wf := by
  induction r <;> try (rw [RIG.getCM]; assumption)
  . rw [RIG.getCM, Kripke.wf]; simp
  . rename_i hs as bs ys bl i prem ih; simp_all; rw [Kripke.wf]; simp;
    intro m imp imp_in imp_m; let ⟨f,g⟩ := imp; subst_eqs; simp_all
    specialize ih f g imp_in; --specialize prem f g imp_in
    split_ands
    . intro a ha
      have ha_forced : a ∈ (prem f g imp_in).getCM.world.forced := by
          apply RIG.ant_atom_forced (prem f g imp_in)
          simp_all
      exact ha_forced
    . intro b hb
      suffices mm : b ∈ Kripkes.getRejected (ys.attach.map (fun ⟨⟨a, b⟩, h⟩ => (prem a b h).getCM)) by simp_all
      have hmem : b ∈ (prem f g imp_in).getCM.world.rejected := hb
      apply Kripkes.getRejected_elem (by grind) b hmem


def RIG.wf (r : RIG s h) : Prop :=
( (r.getCM).evalAnt s = TV.t ∧ (r.getCM).evalSucc s.Δ = TV.f → (r.getCM).evalH h = TV.t) ∧
( r.getCM.evalΓ (s.Γ ∪ s.Θ.map (λ f ↦ f.toForm)) = TV.t → (r.getCM).evalH h = TV.t)

theorem RIG.wf_afort (wf : (RIG.afort hs a b xs ys bl hhs prem).wf) : prem.wf := by
  simp_all [RIG.wf]
  intro h₁ h₂ h₃ h₄
  replace wf := wf.left h₁ h₂
  apply wf _ h₄
  clear h₁ h₂ h₄ wf

  sorry

/- TODO: problem with proving that all left imp sides in hist list evaluate to true -/
theorem RIG.completeness (s : Sequent) (r : RIG s h)-- (i : r.wf)
  :

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
    simp_all; rw [Kripke.wf] at wf; simp_all
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
    --have a_in_xs := RIG.afort_corr pf prem
    --grind

end multiSucc
#min_imports
