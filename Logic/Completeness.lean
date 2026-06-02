import Logic.RIG
import Logic.Kripke

namespace multiSucc
open multiSucc

def Hist.getLeft (h : List Imp) : List Form := h.map (λ i ↦ i.f)


@[simp, grind]
def RIG.getCM (ref : RIG s h) :  Kripke :=
match ref with
| ax hs as bs bl pf =>
  ⟨⟨as.toFinset, bs.toFinset⟩, []⟩
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
  induction r generalizing a <;> simp_all [RIG.getCM]

@[simp, grind .]
theorem RIG.ant_atom_rejected (r : RIG s h)
  (ha : Form.atom a ∈ s.Δ) : a ∈ r.getCM.world.rejected := by
  induction r generalizing a <;> simp_all  [RIG.getCM]

/- def Result.getCMs (r : Result s b h) : List Kripke :=
match r with
| refutation rfs _ => rfs.map (λ rf ↦ RIG.getCM rf )
| _ => [] -/

@[simp, grind =]
theorem RIG.cm_wf (r : RIG s h) : r.getCM.wf := by
  induction r <;> try (rw [RIG.getCM]; assumption)
  . rw [RIG.getCM, Kripke.wf]; simp
  . rename_i hs as bs ys bl i prem ih; simp_all [getCM]; rw [Kripke.wf]; simp;
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


@[simp, grind .]
lemma RIG.impr_cm_branch (i : Imp) (h : i ∈ ys):
      (prem i.f i.g (by simp_all only)).getCM ∈
        (RIG.impr hs as bs ys bl x prem).getCM.branch := by
  simp [RIG.getCM]
  use i, h

lemma RIG.impr_mono (i : Imp) (impH : i ∈ ys)
  (wf : (impr hs as bs ys bl x prem).getCM.wf)
    (h : ∀ a ∈ hs, a.f.eval (impr hs as bs ys bl x prem).getCM = TV.t) :
      (∀ a ∈ hs, a.f.eval (prem i.f i.g impH).getCM = TV.t) := by
  intro a ah
  specialize h a ah
  grind only [Kripke.momo_branch_true, impr_cm_branch]



theorem RIG.completenessH {s : Sequent} (r : RIG s h)
  : s.evalH (Hist.getLeft h) r.getCM := by
  have wf := r.cm_wf
  induction r with
  | ax hs as bs bl i =>
    simp [Sequent.evalH, RIG.getCM, forcedBlockedH]
    constructor
    · intro a ha
      exact Form.forcedH.atom a (Hist.getLeft hs)
        ⟨⟨as.toFinset, bs.toFinset⟩, []⟩ (by simp [ha])
    · intro a hb
      rw [List.inter_eq_nil_iff_disjoint] at i
      have hnot : a ∉ as.toFinset := by
        intro ha
        exact i (by simpa using ha) hb
      exact Form.rejectedH.atom a (Hist.getLeft hs)
        ⟨⟨as.toFinset, bs.toFinset⟩, []⟩ (by simp [hb]) (by simpa using hnot)
  | botr hs xs ys bl prem ih
  | andl hs a b xs ys bl prem ih
  | andr₁ hs a b xs ys bl prem ih
  | andr₂ hs a b xs ys bl prem ih
  | orl₁ hs a b xs ys bl prem ih
  | orl₂ hs a b xs ys bl prem ih
  | orr hs a b xs ys bl prem ih => simp_all [Sequent.evalH, RIG.getCM]; grind
  | impr hs as bs ys bl i prem ih =>
    simp [Sequent.evalH, RIG.getCM, forcedBlockedH] at ih ⊢
    have hdisj : as.Disjoint bs := by simpa [List.inter_eq_nil_iff_disjoint] using i
    constructor
    · constructor
      · intro a ha
        exact Form.forcedH.atom a (Hist.getLeft hs) _ (by simp [ha])
      · intro j hj w' x hxys hw'
        subst w'
        specialize ih x.f x.g hxys
        have hz : x.f.forcedH (x.f :: Hist.getLeft hs) (prem x.f x.g hxys).getCM := by simpa [Hist.getLeft] using ih.1.1
        have hj_forced :
            (j.f ⊃ j.g).forcedH (x.f :: Hist.getLeft hs) (prem x.f x.g hxys).getCM := by
          simpa [Hist.getLeft] using
            ih.1.2 (j.f ⊃ j.g) (by right; exact ⟨j, hj, rfl⟩)
        exact forcedH_drop_history_head_of_self_forced (by grind) hz hj_forced
    · intro f hf
      rcases hf with hf | hf
      · rcases hf with ⟨a, ha_bs, rfl⟩
        have hnot : a ∉ as.toFinset := by
          intro ha_as
          exact hdisj (by simpa using ha_as) ha_bs
        exact Form.rejectedH.atom a (Hist.getLeft hs) _ (by simp [ha_bs]) (by simpa using hnot)
      · rcases hf with ⟨x, hxys, rfl⟩
        specialize ih x.f x.g hxys
        have hz : x.f.forcedH (x.f :: Hist.getLeft hs) (prem x.f x.g hxys).getCM := by
          simpa [Hist.getLeft] using ih.1.1
        have hx_forced : x.f.forcedH (Hist.getLeft hs) (prem x.f x.g hxys).getCM :=
          forcedH_drop_history_head_of_self_forced (by grind [RIG.cm_wf]) hz hz
        have hg_rejected : x.g.rejectedH (Hist.getLeft hs) (prem x.f x.g hxys).getCM :=
          rejectedH_drop_history_head_of_self_forced (by grind [RIG.cm_wf]) hz ih.2
        have hchild : (x.f ⊃ x.g).rejectedH (Hist.getLeft hs) (prem x.f x.g hxys).getCM :=
          Form.rejectedH.imp_root x.f x.g (Hist.getLeft hs)
            (prem x.f x.g hxys).getCM hx_forced hg_rejected
        have hbranch :
            (prem x.f x.g hxys).getCM ∈
              (RIG.impr hs as bs ys bl i prem).getCM.branch := by
          simp [RIG.getCM]
          exact ⟨x, hxys, rfl⟩
        exact Form.rejectedH.imp_branch hbranch hchild
  | impl₁ hs a b xs ys bl prem ih => --simp_all [Sequent.evalH, RIG.getCM]; grind
    simp [Sequent.evalH, RIG.getCM] at ih ⊢
    --have ih := ih (RIG.cm_wf prem)
    rcases ih with ⟨⟨hΓ, hΘ⟩, hΔ⟩
    exact ⟨⟨⟨Form.forcedH.imp_left a b (Hist.getLeft hs) prem.getCM
      hΔ.1 hΘ.1, hΓ⟩, hΘ.2⟩, hΔ.2⟩
  | impl₂ hs a b xs ys bl prem ih => simp_all; grind [forcedH_b_forces_imp]
  | afort hs a b xs ys bl pf prem ih =>
    simp_all [Sequent.evalH, RIG.getCM]
    rcases ih with ⟨⟨hΓ, hΘ⟩, hΔ⟩
    have haHist : a ∈ Hist.getLeft hs := by grind [Hist.getLeft]
    apply Form.rejectedH.imp_hist a b (Hist.getLeft hs) prem.getCM haHist hΔ.1


theorem RIG.completeness (s : Sequent) (r : RIG s h)
  (ih : ∀ x ∈ Hist.getLeft h, x.forcedH (Hist.getLeft h) r.getCM) :
  s.evalR r.getCM = TV.f := Sequent.evalH_to_evalR_false r.cm_wf ih r.completenessH


end multiSucc
#print axioms multiSucc.RIG.completeness
#min_imports
