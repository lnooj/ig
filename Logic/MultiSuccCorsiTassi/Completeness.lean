import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Helper
import Logic.MultiSuccCorsiTassi.Kripke
import Logic.MultiSuccCorsiTassi.Proof
import Logic.MultiSuccCorsiTassi.MultiSuccCorsiTassi

namespace multiSucc
open multiSucc


@[simp, grind]
def Refutation.getCM (ref : Refutation s h) /- (m : Model) (wf : m.wf) -/:  Model :=
match ref with
| ax hs as bs xs pf => ⟨⟨as.toFinset, bs.toFinset⟩, []⟩
| botr hs xs ys prem =>  Refutation.getCM prem
| andl hs a b xs ys prem => Refutation.getCM prem
| andr₁ hs a b xs ys prem => Refutation.getCM prem
| andr₂ hs a b xs ys prem => Refutation.getCM prem
| orl₁ hs a b xs ys prem => Refutation.getCM prem
| orl₂ hs a b xs ys prem => Refutation.getCM prem
| orr hs a b xs ys prem => Refutation.getCM prem
| impr hs a b as bs xs ys pf prem => ⟨⟨as.toFinset, bs.toFinset⟩, [Refutation.getCM prem]⟩
| impl₁ hs a b xs ys prem => Refutation.getCM prem
| impl₂ hs a b xs ys prem => Refutation.getCM prem
| afort hs a b xs ys pf prem => Refutation.getCM prem


/- @[simp] lemma Refutation.getCM_botr {xs ys : List Form} (r : Refutation ⟨↑xs, ↑ys⟩ hs) : (Refutation.botr hs xs ys r).getCM = r.getCM := by simp_all
@[simp] lemma Refutation.getCM_andl (r : Refu) -/

def Result.getCMs (r : Result s h) : List Model :=
match r with
| refutation rfs => rfs.map (λ rf ↦ Refutation.getCM rf )
| _ => []

--@[simp, grind =]
theorem Refutation.cm_wf (r : Refutation s h) : r.getCM.wf := by
  induction r <;> try (rw [Refutation.getCM]; assumption)
  . rw [Refutation.getCM, Model.wf]; simp
  . rename_i i a ih
    --rw [ Model.wf] at ih; simp at ih
    rw [Refutation.getCM, Model.wf]; simp only [Model.branch, decide_eq_true_eq];
    intro fm; sorry-- apply ih; grind [Refutation.getCM, Model.wf]




lemma Refutation.impr_a_eval {a b : Form}
  (prem : Refutation
    { Γ := ↑(a :: List.map Form.atoms as ++ List.map Imp.toForm xs), Δ := {b} }
       ({ f := a, g := b } :: hs)) :
  Form.eval a (Refutation.impr hs a b as bs xs ys i prem).getCM = TV.t := by
  rw [getCM]
  sorry

/- theorem if_hs_then_impr
  (pf : { f := a, g := b } ∈ hs) (r : Refutation { Γ := ↑xs, Δ := ↑((a ⊃ b) :: ys) } hs ) :
  Refutation.impr ∈ r -/
--TODO
theorem Refutation.afort_corr {hs : List Imp} {a b : Form}
  (pf : { f := a, g := b } ∈ hs)
  (r : Refutation s hs )
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
  | impr hs' a' b' as bs xs ys i prem ih => simp_all


theorem Refutation.blocked_corr {i : Imp}
  (r : Refutation { Γ := ↑(List.map Form.atoms as ++ List.map Imp.toForm blocked),
                    Δ := ↑(List.map Form.atoms bs) } hs)
  (ixs : i ∈ blocked) : i.g.eval r.getCM = TV.t := sorry

theorem Refutation.correctness :
  ∀ (s : Sequent) ( r : Refutation s b h) (wf : r.getCM.wf ), evalSeq ⟨s.Γ ∪ b.map Imp.toForm , s.Δ⟩ r.getCM = TV.f := by
  intro s r wf
  induction r with
  | ax hs as bs xs i =>
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
  | impr hs a b as bs xs ys i prem ih =>
/-     simp only [getCM] at wf; specialize ih wf; -- rw [Model.wf] at wf;
    simp_all
    obtain ⟨⟨h₁, h₃⟩, h₂⟩ := ih
    intro x xh
    specialize h₃ x
    rcases xh with m | mm | mmm
    . obtain ⟨a, abs, a_tom⟩ := m; rw [← a_tom]; -/

    simp only [getCM] at wf; rw [Model.wf] at wf; simp only [List.cons_append, List.attach_cons,
      List.attach_nil, List.map_nil, Subtype.forall, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at wf
    specialize wf prem.getCM rfl (by grind)
    obtain ⟨wf_h₁, wf_h₂, wf_h₃⟩ := wf
    specialize ih wf_h₁
    simp_all
    rcases ih with ⟨⟨h₁, h₃⟩, h₂⟩
    constructor
    . intro x pr; specialize h₃ x pr; sorry --x is tru in branch, why true in parent? have := Model.momo_branch_true wf_h₁ (by sorry)
    . intro x pr
      rcases pr with in_bs | imp | immp
      . obtain ⟨a_bs, atomn, aaaa⟩ := in_bs; sorry-- sth in bs is false, doable
      . sorry --difficult
      . sorry --stuff in ys false, also difficult
  | impl₁ => simp_all
  | impl₂ hs a b xs ys prem ih =>
    simp only [getCM] at wf; specialize ih wf
    simp_all
    rcases ih with ⟨⟨h₁, h₂⟩, h₃⟩
    apply b_true_then_imp_true_branch wf h₁

  | afort hs a b xs ys pf prem ih =>
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
