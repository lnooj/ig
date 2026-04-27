
import Logic.MultiSuccCorsiTassi.Termination

namespace multiSucc
open multiSucc

/-! # Kripke Semantics definitions -/
structure World where
  forced : Finset Atom
  rejected : Finset Atom
deriving DecidableEq

def Seq4Proof.forced (s : Seq4Proof) : Finset Atom := s.aL.toFinset

def Seq4Proof.rejected (s : Seq4Proof) : Finset Atom := s.aR.toFinset

def Seq4Proof.world (p : Seq4Proof) : World := ⟨p.forced, p.rejected⟩

structure Model where
  world : World
  branch : List Model
deriving BEq

--@[grind, simp]
def Model.wf (m : Model) : Bool :=
∀ fm ∈ m.branch.attach,
  fm.val.wf ∧
  m.world.forced ⊆ fm.val.world.forced ∧
  fm.val.world.rejected ⊆ m.world.rejected
decreasing_by
all_goals
  have : sizeOf m.branch < sizeOf m := by grind [Model]
  apply lt_trans _ this
  apply List.sizeOf_lt_of_mem
  grind

@[grind, simp]
def Models.getUnforced : List Model → Finset Atom
| [] => {}
| x :: xs => x.world.rejected ∪ Models.getUnforced xs

@[grind ., simp]
theorem Models.getUnforced_elem {ms : List Model} (mem: m ∈ ms):
  ∀ a ∈ m.world.rejected, a ∈ Models.getUnforced ms := by
  intro a ah; fun_induction getUnforced <;> grind

def Model.depth : Model → Nat
| ⟨_, branch⟩ =>
  1 + (branch.map Model.depth).max?.getD 0

theorem Model.depth_eq {m : Model} : m.depth = 1 + (m.branch.map Model.depth).max?.getD 0 := by
  cases m
  simp [depth]

lemma depth_lt_of_mem {m' m : Model} :
  m' ∈ m.branch → m'.depth < m.depth := by
  intro hmem
  simp [Model.depth_eq]
  have : m'.depth ∈ List.map Model.depth m.branch := by grind
  have := List.le_max?_getD_of_mem this (k:=0)
  simp [Model.depth_eq] at this
  omega

--@[grind, simp]
def Model.all (m : Model) : List Model :=
  m :: m.branch.attach.flatMap (all ·.val)
decreasing_by
  have : sizeOf m.branch < sizeOf m := by grind [Model]
  apply lt_trans _ this
  apply List.sizeOf_lt_of_mem
  grind


@[grind ., simp]
theorem Model.all_nested_in_all {m m' a : Model} (h₁ : a ∈ m.branch) (h₂ : m' ∈ a.all) : m' ∈ m.all := by
  fun_induction Model.all m with
  | case1 m ih => simp_all; right; grind

@[grind ., simp]
theorem Model.branch_wf {m m' : Model} (wf : m.wf) (mem : m' ∈ m.branch) : m'.wf := by rw [Model.wf] at wf; simp_all

@[grind ., simp]
theorem Model.all_wf {m m' : Model} (wf : m.wf) (mem : m' ∈ m.all) : m'.wf := by
  fun_induction Model.all with
  | case1 m ih =>
    simp_all
    rcases mem with h | ⟨a, h₁, h₂⟩
    . grind
    . rw [Model.wf] at wf
      simp_all
      apply ih a h₁ h₂


/-! # Truth values for evaluation -/
inductive TV  where
| t : TV
| f : TV
| u : TV
deriving DecidableEq

def conjTV : TV → TV → TV
| .t, .t => .t
| .f, _ => .f
| _, .f => .f
| _, _ => .u

def disjTV : TV → TV → TV
| .f, .f => .f
| .t, _ => .t
| _, .t => .t
| _, _ => .u

@[simp]
theorem conjTV_left_false : conjTV .f a = b ↔ b = .f := by
  grind [conjTV, cases TV]
@[simp]
theorem conjTV_right_false : conjTV a .f = b ↔ b = .f := by
  grind [conjTV, cases TV]
@[grind =, simp]
theorem conjTV_true_iff : conjTV a b = .t ↔ a = .t ∧ b = .t := by
  grind [conjTV, cases TV]
@[grind =, simp]
theorem conjTV_false_iff : conjTV a b = .f ↔ a = .f ∨ b = .f := by
  grind [conjTV, cases TV]
@[simp]
theorem disjTV_left_false : disjTV .f a = b ↔ b = a := by
  grind [disjTV, cases TV]
@[simp]
theorem disjTV_right_false : disjTV a .f = b ↔ b = a := by
  grind [disjTV, cases TV]
@[grind =, simp]
theorem disjTV_true_iff : disjTV a b = .t ↔ a = .t ∨ b = .t := by
  grind [disjTV, cases TV]
@[grind =, simp]
theorem disjTV_false_iff : disjTV a b = .f ↔ a = .f ∧ b = .f := by
  grind [disjTV, cases TV]

instance conjTV_rightCommutative : RightCommutative conjTV where
right_comm a b c := by cases a <;> cases b <;> cases c <;> rfl

instance disjTV_rightCommutative : RightCommutative disjTV where
right_comm a b c := by cases a <;> cases b <;> cases c <;> rfl

instance conjTV_commutative : Std.Commutative conjTV where
comm a b := by cases a <;> cases b <;> rfl

instance disjTV_commutative : Std.Commutative disjTV where
comm a b := by cases a <;> cases b <;> rfl

instance conjTV_associative : Std.Associative conjTV where
assoc a b c := by cases a <;> cases b <;> cases c <;> rfl

instance disjTV_associative : Std.Associative disjTV where
assoc a b c := by cases a <;> cases b <;> cases c <;> rfl


/-! # Main evaluation function -/
@[grind]
def Form.eval : Form → Model → TV
| .atoms a, m => if a ∈ m.world.forced then .t
       else if a ∈ m.world.rejected then .f
       else .u
| .bot, _ => .f
| .and a b, m => conjTV (a.eval m) (b.eval m )
| .or a b, m => disjTV (a.eval m) (b.eval m )
| .imp a b, m =>
  if (a.eval m = .f ∨ b.eval m = .t)
      ∧ (m.branch.attach.all (λ m' => (a ⊃ b).eval m'.val = .t)) then .t
  else if (a.eval m = .t ∧ b.eval m = .f)
      ∨ (m.branch.attach.any (λ m' => (a ⊃ b).eval m'.val = .f)) then .f --only one false
  else .u
termination_by fm m => (sizeOf_Form fm, m.depth)
decreasing_by
all_goals first | (apply Prod.Lex.left; grind) | (apply Prod.Lex.right; apply depth_lt_of_mem; grind)


@[grind ., simp] theorem evaluate_atom_t (h :  (Form.atoms a).eval m = .t) : a ∈ m.world.forced := by grind
@[grind ., simp] theorem evaluate_atom_f (h :  (Form.atoms a).eval m = .f) : a ∈ m.world.rejected := by grind
@[grind ., simp] theorem evaluate_atom_f_and (h :  (Form.atoms a).eval m = .f) : a ∈ m.world.rejected ∧ a ∉ m.world.forced:= by grind
@[grind =, simp] theorem evaluate_bot : Form.bot.eval m = .f := by grind
@[grind =, simp] theorem evaluate_and : (a ∧∧ b).eval m = conjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evaluate_or : (a ∨∨ b).eval m = disjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evaluate_atom_undef : (Form.atoms a).eval m = .u ↔ a ∉ m.world.forced ∧ a ∉ m.world.rejected := by grind



def evalBlocked : Imp → Model → TV
| {f, g}, m =>
  if (m.branch.attach.all (λ m' => (f ⊃ g).eval m'.val = .t)) then .t
  else if (m.branch.attach.any (λ m' => (f ⊃ g).eval m'.val = .f)) then .f
  else .u


def evalAnt (Γ : Multiset Form) (m : Model) : TV :=
  (Γ.map (fun f => f.eval m)).fold conjTV TV.t
scoped notation "⋀ " m:max ", " Γ:max => evalAnt Γ m

def evalAntB (Γ : Multiset Imp) (m : Model) : TV :=
  (Γ.map (fun f => evalBlocked f m)).fold conjTV TV.t
scoped notation "⋀* " m:max ", " Γ:max => evalAntB Γ m

@[simp]
theorem evalAntB0 : ⋀* m, 0 = TV.t := by simp [evalAntB]

def evalSucc (Δ : Multiset Form) (m : Model) : TV :=
  (Δ.map (fun f => f.eval m)).fold disjTV TV.f
scoped notation "⋁ " m:max ", " Γ:max => evalSucc Γ m

@[simp, grind]
def Sequent.evalΓ : Sequent → Model → TV
| ⟨Γa, Γb, _ ⟩,  m => conjTV (evalAnt Γa m) (evalAntB Γb m)

-- A sequent is refutable iff all its assumptions are satisfied (all forms in Γ are true) but none of the conclusions are (all Δ are false)
@[grind]
def Sequent.evalR : Sequent → Model → TV
| s,  m =>
  match s.evalΓ m, evalSucc s.Δ m with
  | .t, .f => .f
  | .f, _ | _, .t => .t
  | _, _ => .u

@[grind]
def Sequent.evalP : Sequent → Model → TV
| s,  m =>
  match evalAnt s.Γ m, evalSucc s.Δ m with
  | .t, .f => .f
  | .f, _ | _, .t => .t
  | _, _ => .u


lemma beq_f_true_eq {v : TV} :
  (v = TV.f) → v = TV.f := by
  cases v
  . intro f; cases f
  . grind
  . intro f; cases f

lemma beq_true_eq {x y : TV} :
  (x = y) → x = y := by
  intro h
  cases x <;> cases y <;>  try cases h <;> rfl

lemma beq_t_true_eq {v : TV} :
  (v = TV.t) → v = TV.t := by
  cases v
  . grind
  . intro f; cases f
  . intro f; cases f

variable {s : Sequent}
@[simp]
theorem Sequent.evalP_true_iff :
  s.evalP m = TV.t ↔
  evalAnt s.Γ m = TV.f ∨ evalSucc s.Δ m = TV.t := by
  grind

@[simp]
theorem Sequent.evalP_false_iff :
  s.evalP m = TV.f ↔
  evalAnt s.Γ m = TV.t ∧ evalSucc s.Δ m = TV.f := by
  simp [Sequent.evalP]
  split <;> grind

@[simp]
theorem Sequent.evalR_true_iff :
  s.evalR m = TV.t ↔
  s.evalΓ m = TV.f ∨ evalSucc s.Δ m = TV.t := by
  grind

@[simp]
theorem Sequent.evalR_false_iff :
  s.evalR m = TV.f ↔
  s.evalΓ m = TV.t ∧ evalSucc s.Δ m = TV.f := by
  simp [Sequent.evalR]
  split <;> grind

@[grind ., simp]
lemma evalAnt_not_t (h : x ∈ ys) (hx : x.eval m = .u) : ¬evalAnt ys m = TV.t := by
  induction ys using Multiset.induction with
  | empty => simp at h
  | cons y ys ih =>
    simp_all
    rcases h with (⟨⟨_⟩⟩ | h)
    · simp_all [evalAnt]
    · simp_all [evalAnt]

@[grind ., simp]
lemma evalSucc_not_f (h : x ∈ ys) (hx : x.eval m = .u) : ¬⋁ m, ys = TV.f := by
  induction ys using Multiset.induction with
  | empty => simp at h
  | cons y ys ih =>
    simp_all
    rcases h with (⟨⟨_⟩⟩ | h)
    · simp_all [evalSucc]
    · simp_all [evalSucc]

@[grind =, simp] lemma evalSucc_bot_cons : ⋁ m, ↑(⊥ :: xs) = ⋁ m, ↑xs := by simp [evalSucc]
@[grind =, simp] lemma evalAnt_bot_cons : ⋀ m, ↑(⊥ :: xs) = .f := by simp [evalAnt]
@[grind =, simp] lemma evalAnt_conj : ⋀ m, ↑((a ∧∧ b) :: xs) = ⋀ m, ↑(a :: b :: xs) := by simp [evalAnt]; grind
@[grind =, simp] lemma evalSucc_conj : ⋁ m, ↑((a ∨∨ b) :: xs) = ⋁ m, ↑(a :: b :: xs) := by simp [evalSucc]; grind
@[grind =, simp] lemma evalSucc_cons {xs : List Form} : ⋁ m, ↑(a :: xs) = disjTV (a.eval m) (⋁ m, ↑xs) := by simp [evalSucc]
@[grind =, simp] lemma evalAnt_cons {xs : List Form} : ⋀ m, ↑(a :: xs) = conjTV (a.eval m) (⋀ m, ↑xs) := by simp [evalAnt]

@[grind =, simp]
lemma evalAnt_eq_true :
    ⋀ m, xs = .t ↔ ∀ x ∈ xs, x.eval m = .t := by
  induction xs using Multiset.induction with simp_all [evalAnt]
@[grind =, simp]
lemma evalAnt_eq_false :
    ⋀ m, xs = .f ↔ ∃ x ∈ xs, x.eval m = .f := by
  induction xs using Multiset.induction with simp_all [evalAnt]
@[grind =, simp]
lemma evalAntB_eq_true :
    ⋀* m, xs = .t ↔ ∀ x ∈ xs, evalBlocked x m = .t := by
  induction xs using Multiset.induction with simp_all [evalAntB]
@[grind =, simp]
lemma evalAntB_eq_false :
    ⋀* m, xs = .f ↔ ∃ x ∈ xs, evalBlocked x m = .f := by
  induction xs using Multiset.induction with simp_all [evalAntB]
@[grind =, simp]
lemma evalSucc_eq_true :
    ⋁ m, xs = .t ↔ ∃ x ∈ xs, x.eval m = .t := by
  induction xs using Multiset.induction with simp_all [evalSucc]
@[grind =, simp]
lemma evalSucc_eq_false :
    ⋁ m, xs = .f ↔ ∀ x ∈ xs, x.eval m = .f := by
  induction xs using Multiset.induction with simp_all [evalSucc]
@[grind ., simp]
lemma evalSucc_true (fin : f ∈ Δ ) (ev : f.eval m = TV.t ): evalSucc Δ m = TV.t := by
 simp; grind
@[grind ., simp]
lemma evalAnt_false (h₁ : f ∈ Γ) (h₂ : f.eval m = TV.f) : evalAnt Γ m = TV.f := by
  simp; grind
@[grind ., simp]
lemma evalAntB_false (h₁ : f ∈ s.Γb) (h₂ : evalBlocked f m = TV.f) : s.evalΓ m = TV.f := by
  simp; grind



/-! # implication theorems -/
theorem eval_imp_true_iff :
  (a ⊃ b).eval m = TV.t ↔
    ((a.eval m = .f ∨ b.eval m = .t) ∧ (m.branch.all (λ m' => (a ⊃ b).eval m' = .t))) := by
  constructor
  . intro h; rw [Form.eval] at h; simp_all; grind [Form.eval]
  . intro h; rw [Form.eval]; simp_all

theorem evalBlocked_true_iff :
  evalBlocked x m = TV.t ↔
    (m.branch.all (λ m' => (x.f ⊃ x.g).eval m' = .t)) := by
  constructor
  . intro h; rw [evalBlocked] at h; simp_all only [List.all_eq_true, List.mem_attach,
    decide_eq_true_eq, forall_const, Subtype.forall]; grind [Form.eval]
  . intro h; rw [evalBlocked]; simp_all

theorem eval_imp_false_iff :
  (a ⊃ b).eval m = TV.f ↔
    a.eval m = .t ∧  b.eval m = .f ∨ ∃ x ∈ m.branch, ((a ⊃ b).eval x = TV.f) := by
  constructor
  . intro h; rw [Form.eval] at h; simp_all
    split_ifs at h
    . grind
  . intro h; rw [Form.eval]; simp_all; grind

theorem evalBlocked_false_iff :
  evalBlocked x m = TV.f ↔
    ∃ m' ∈ m.branch, ((x.f ⊃ x.g).eval m' = TV.f) := by
  constructor
  . intro h; rw [evalBlocked] at h; simp_all; grind
  . intro h; rw [evalBlocked]; simp_all; grind

theorem eval_imp_righ_wo_ys :
  Sequent.evalP { Γa := xs, Γb := xs', Δ := {a ⊃ b} } m ≠ TV.f →
  Sequent.evalP { Γa := xs, Γb := xs', Δ := ↑((a ⊃ b) :: ys) } m ≠ TV.f := by
  simp; intro h₁ h₂; simp_all

theorem eval_imp_righ_wo_ys_t :
  Sequent.evalP { Γa := xs, Γb := xs', Δ := {a ⊃ b} } m = TV.t →
  Sequent.evalP { Γa := xs, Γb := xs', Δ := ↑((a ⊃ b) :: ys) } m = TV.t := by
  simp; intro h₁; grind

@[grind ., simp]
theorem eval_imp_false_contradict :
  (a ⊃ b).eval m = TV.f → ∃ m' ∈ m.all, a.eval m' = .t ∧ b.eval m' = .f := by
  intro impF
  fun_induction Model.all with
  | case1 m ih =>
    rw [eval_imp_false_iff] at impF
    rcases impF with impF | ⟨m', impF⟩
    . grind
    . simp_all
      specialize ih m' (by grind) impF.right
      obtain ⟨m'', ih⟩ := ih
      grind

@[grind ., simp]
theorem evalBlocked_imp_true_then {m m': Model}
  (child : m' ∈ m.branch)
  (h : evalBlocked x m = TV.t) : (x.f ⊃ x.g).eval m' = TV.t := by
  simp_all [evalBlocked_true_iff]

theorem mmmmm {bl : List Imp} :
  ∀ x ∈ bl, evalBlocked x m = TV.t →  ∀ x ∈ bl, (x.f ⊃ x.g).eval m' = TV.t := by sorry
--MONOTONICITY--



/-! # Truth monotonicity -/
@[grind ., simp]
theorem Model.momo_branch_true {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.branch) (ftv : f.eval m = TV.t) :
    f.eval m' = TV.t := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.rejected ⊆ m.world.rejected := by
      unfold Model.wf at wf; simp at wf; exact wf
  specialize h m' mem
  obtain ⟨mf', fo, unfo⟩ := h
  match f with
  | .atoms a => grind
  | .bot => grind
  | .and a b =>
    simp_all
    constructor
    . obtain ⟨atv, btv⟩ := ftv
      apply Model.momo_branch_true wf mem
      exact atv
    . obtain ⟨atv, btv⟩ := ftv
      apply Model.momo_branch_true wf mem
      exact btv
  | .or a b =>
    simp_all
    cases ftv with
    | inl h =>
      left
      apply Model.momo_branch_true wf mem
      exact h
    | inr h =>
      right
      apply Model.momo_branch_true wf mem
      exact h
  | .imp a b =>
    rw [eval_imp_true_iff] at ftv
    obtain ⟨h₁, h₂⟩ := ftv
    grind

theorem Model.mono_all_true {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.all) (ftv : f.eval m = TV.t) :
  f.eval m' = TV.t := by
  rw [Model.all] at mem
  --rw [Model.wf] at wf
  simp_all
  rcases mem with h | ⟨a, h₁, h₂⟩
  . grind
  . have wf' : m'.wf = true := Model.all_wf wf (by grind)
    have aT := Model.momo_branch_true wf h₁ ftv
    have awf : a.wf := by
      rw [Model.wf] at wf; simp at wf
      grind
    apply Model.mono_all_true awf h₂ aT
termination_by (m.depth)
decreasing_by exact depth_lt_of_mem h₁

/-! # Falsity monotonicity proof -/
@[grind ., simp]
theorem Model.mono_branch_false {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.branch ) (ftv : f.eval m' = .f) :
  f.eval m = .f  := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.rejected ⊆ m.world.rejected := by
      unfold Model.wf at wf; simp at wf; exact wf
  specialize h m' mem
  obtain ⟨mf', fo, unfo⟩ := h
  match f with
  | .atoms a =>
    apply evaluate_atom_f_and at ftv; simp [Form.eval]; grind
  | .bot => grind
  | .and a b =>
    simp_all
    cases ftv with
    | inl h =>
      left
      apply Model.mono_branch_false wf mem
      exact h
    | inr h =>
      right
      apply Model.mono_branch_false wf mem
      exact h
  | .or a b =>
    simp_all
    constructor
    . obtain ⟨atv, btv⟩ := ftv
      apply Model.mono_branch_false wf mem
      exact atv
    . obtain ⟨atv, btv⟩ := ftv
      apply Model.mono_branch_false wf mem
      exact btv
  | .imp a b =>
    rw [eval_imp_false_iff]
    right
    use m'


theorem imp_false_branch {a b : Form} {m m' : Model}
(mem : m' ∈ m.branch) (h : (a ⊃ b).eval m' = TV.f) (wf : m.wf) :
b.eval m = TV.f := by
  rw [eval_imp_false_iff] at h
  rcases h with ⟨atv, btv⟩ | h
  . exact Model.mono_branch_false wf mem btv
  . obtain ⟨x, xmem, h⟩ := h
    have mwf : m'.wf = true := by rw [Model.wf] at wf; simp at wf; grind
    have := imp_false_branch xmem h mwf
    exact Model.mono_branch_false wf mem this
termination_by (m.depth)
decreasing_by exact depth_lt_of_mem mem

/-! # right side of imp importance -/
theorem imp_false_then_b_false  (impF : (a ⊃ b).eval m = TV.f) (wf : m.wf) : b.eval m = .f := by
  rw [eval_imp_false_iff] at impF
  cases impF with
  | inl h => grind
  | inr h =>
    rcases h with ⟨m', mem, h₂⟩
    exact imp_false_branch mem h₂ wf


theorem b_true_then_imp_true_branch {a b : Form} (wf : m.wf) (bT : b.eval m = TV.t) : (a ⊃ b).eval m = TV.t := by
  rw [eval_imp_true_iff]
  constructor
  . simp_all
  . simp; intro m' mh'
    have b_fut := Model.momo_branch_true wf mh' bT
    have m'_wf : m'.wf := by rw [Model.wf] at wf; simp_all
    apply  b_true_then_imp_true_branch m'_wf b_fut
termination_by (m.depth)
decreasing_by exact depth_lt_of_mem mh'

end multiSucc
