
import Logic.Termination

namespace multiSucc
open multiSucc

/- # Kripke Semantics definitions -/
structure World where
  forced : Finset Atom
  rejected : Finset Atom

deriving DecidableEq

structure Kripke where
  world : World
  branch : List Kripke
deriving BEq

def Kripke.wf (m : Kripke) : Bool :=
∀ fm ∈ m.branch.attach,
  fm.val.wf ∧
  m.world.forced ⊆ fm.val.world.forced ∧
  fm.val.world.rejected ⊆ m.world.rejected
decreasing_by
all_goals
  have : sizeOf m.branch < sizeOf m := by grind [Kripke]
  apply lt_trans _ this
  apply List.sizeOf_lt_of_mem
  grind

@[grind, simp]
def Kripkes.getRejected : List Kripke → Finset Atom
| [] => {}
| x :: xs => x.world.rejected ∪ Kripkes.getRejected xs

@[grind ., simp]
theorem Kripkes.getRejected_elem {ms : List Kripke} (mem: m ∈ ms):
  ∀ a ∈ m.world.rejected, a ∈ Kripkes.getRejected ms := by
  intro a ah; fun_induction getRejected <;> grind

def Kripke.depth : Kripke → Nat
| ⟨_, branch⟩ =>
  1 + (branch.map Kripke.depth).max?.getD 0

theorem Kripke.depth_eq {m : Kripke} : m.depth = 1 + (m.branch.map Kripke.depth).max?.getD 0 := by
  cases m
  simp [depth]

lemma depth_lt_of_mem {m' m : Kripke} :
  m' ∈ m.branch → m'.depth < m.depth := by
  intro hmem
  simp [Kripke.depth_eq]
  have : m'.depth ∈ List.map Kripke.depth m.branch := by grind
  have := List.le_max?_getD_of_mem this (k:=0)
  simp [Kripke.depth_eq] at this
  omega

def Kripke.all (m : Kripke) : List Kripke :=
  m :: m.branch.attach.flatMap (all ·.val)
decreasing_by
  have : sizeOf m.branch < sizeOf m := by grind [Kripke]
  apply lt_trans _ this
  apply List.sizeOf_lt_of_mem
  grind

@[grind ., simp]
theorem Kripke.all_def {w w' : Kripke} (h : w' ∈ w.all) : w' = w ∨ ∃ a ∈ w.branch, w' ∈ a.all := by
  rw [Kripke.all] at h; simp_all;

@[grind ., simp]
theorem Kripke.all_nested_in_all {m m' a : Kripke} (h₁ : a ∈ m.branch) (h₂ : m' ∈ a.all) : m' ∈ m.all := by
  fun_induction Kripke.all m with
  | case1 m ih => simp_all; right; grind

@[grind ., simp]
theorem Kripke.branch_wf {m m' : Kripke} (wf : m.wf) (mem : m' ∈ m.branch) : m'.wf := by rw [Kripke.wf] at wf; simp_all

@[grind ., simp]
theorem Kripke.all_wf {m m' : Kripke} (wf : m.wf) (mem : m' ∈ m.all) : m'.wf := by
  fun_induction Kripke.all with
  | case1 m ih =>
    simp_all
    rcases mem with h | ⟨a, h₁, h₂⟩
    . grind
    . rw [Kripke.wf] at wf
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
def Form.eval : Form → Kripke → TV
| .atom a, m =>
      if a ∈ m.world.forced then .t
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
termination_by fm m => (Form.complexity fm, m.depth)
decreasing_by
all_goals first | (apply Prod.Lex.left; grind) | (apply Prod.Lex.right; apply depth_lt_of_mem; grind)


@[grind ., simp] theorem evaluate_atom_t (h :  (Form.atom a).eval m = .t) : a ∈ m.world.forced := by grind
@[grind ., simp] theorem evaluate_atom_f (h :  (Form.atom a).eval m = .f) : a ∈ m.world.rejected := by grind
@[grind ., simp] theorem evaluate_atom_f_and (h :  (Form.atom a).eval m = .f) : a ∈ m.world.rejected ∧ a ∉ m.world.forced:= by grind
@[grind =, simp] theorem evaluate_bot : Form.bot.eval m = .f := by grind
@[grind =, simp] theorem evaluate_and : (a ∧∧ b).eval m = conjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evaluate_or : (a ∨∨ b).eval m = disjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evaluate_atom_undef : (Form.atom a).eval m = .u ↔ a ∉ m.world.forced ∧ a ∉ m.world.rejected := by grind


def evalBlocked : Imp → Kripke → TV
| {f, g}, m =>
  if (m.branch.attach.all (λ m' => (f ⊃ g).eval m'.val = .t)) then .t
  else if (m.branch.attach.any (λ m' => (f ⊃ g).eval m'.val = .f)) then .f
  else .u


def Kripke.evalΓ (Γ : Multiset Form) (m : Kripke) : TV :=
  (Γ.map (fun f => f.eval m)).fold conjTV TV.t
scoped notation "⋀ " m:max ", " Γ:max => Kripke.evalΓ Γ m

def Kripke.evalΘ (Θ : Multiset Imp) (m : Kripke) : TV :=
  (Θ.map (fun f => evalBlocked f m)).fold conjTV TV.t
scoped notation "⋀* " m:max ", " Θ:max => Kripke.evalΘ Θ m

@[simp]
theorem Kripke.evalΘ_0 : ⋀* m, 0 = TV.t := by simp [Kripke.evalΘ]

def Kripke.evalSucc (Δ : Multiset Form) (m : Kripke) : TV :=
  (Δ.map (fun f => f.eval m)).fold disjTV TV.f
scoped notation "⋁ " m:max ", " Γ:max => Kripke.evalSucc Γ m


@[simp, grind]
def Kripke.evalAnt : Sequent → Kripke → TV
| ⟨Γ, Θ, _ ⟩,  m => conjTV (Kripke.evalΓ Γ m) (Kripke.evalΘ Θ m)

-- A sequent is refutable iff all its assumptions are satisfied (all forms in Γ are true) but none of the conclusions are (all Δ are false)

@[grind]
def Sequent.evalP : Sequent → Kripke → TV
| s,  m =>
  match m.evalΓ s.ant, m.evalSucc s.Δ with
  | .t, .f => .f
  | .f, _ | _, .t => .t
  | _, _ => .u

@[grind]
def Sequent.evalR : Sequent → Kripke → TV
| s, m =>
  match m.evalAnt s, m.evalSucc s.Δ with
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
  Kripke.evalΓ s.ant m = TV.f ∨ Kripke.evalSucc s.Δ m = TV.t := by
  grind

@[simp]
theorem Sequent.evalP_false_iff :
  s.evalP m = TV.f ↔
  Kripke.evalΓ s.ant m = TV.t ∧ Kripke.evalSucc s.Δ m = TV.f := by
  simp [Sequent.evalP]
  split <;> grind

@[simp]
theorem Sequent.evalR_true_iff :
  s.evalR m = TV.t ↔
  Kripke.evalAnt s m = TV.f ∨ Kripke.evalSucc s.Δ m = TV.t := by
  grind

@[simp]
theorem Sequent.evalR_false_iff :
  s.evalR m = TV.f ↔
  Kripke.evalAnt s m = TV.t ∧ Kripke.evalSucc s.Δ m = TV.f := by
  simp [Sequent.evalR]
  split <;> grind

@[grind ., simp]
lemma Sequent.evalΓ_not_t (h : x ∈ ys) (hx : x.eval m = .u) : ¬Kripke.evalΓ ys m = TV.t := by
  induction ys using Multiset.induction with
  | empty => simp at h
  | cons y ys ih =>
    simp_all
    rcases h with (⟨⟨_⟩⟩ | h)
    · simp_all [Kripke.evalΓ]
    · simp_all [Kripke.evalΓ]

@[grind ., simp]
lemma evalSucc_not_f (h : x ∈ ys) (hx : x.eval m = .u) : ¬⋁ m, ys = TV.f := by
  induction ys using Multiset.induction with
  | empty => simp at h
  | cons y ys ih =>
    simp_all
    rcases h with (⟨⟨_⟩⟩ | h)
    · simp_all [Kripke.evalSucc]
    · simp_all [Kripke.evalSucc]

@[grind =, simp] lemma evalSucc_bot_cons : ⋁ m, ↑(⊥ :: xs) = ⋁ m, ↑xs := by simp [Kripke.evalSucc]
--@[grind =, simp] lemma evalSuccH_bot_cons : ⋁ₕ h, m, ↑(⊥ :: xs) = ⋁ₕ h, m, ↑xs := by simp [evalSuccH, evalHist_bot]
@[grind =, simp] lemma Sequent.evalΓ_bot_cons : ⋀ m, ↑(⊥ :: xs) = .f := by simp [Kripke.evalΓ]
@[grind =, simp] lemma Sequent.evalΓ_conj : ⋀ m, ↑((a ∧∧ b) :: xs) = ⋀ m, ↑(a :: b :: xs) := by simp [Kripke.evalΓ]; grind
@[grind =, simp] lemma evalSucc_conj : ⋁ m, ↑((a ∨∨ b) :: xs) = ⋁ m, ↑(a :: b :: xs) := by simp [Kripke.evalSucc]; grind
--@[grind =, simp] lemma evalSuccH_conj : ⋁ₕ h, m, ↑((a ∨∨ b) :: xs) = ⋁ₕ h, m, ↑(a :: b :: xs) := by simp [evalSuccH, evalHist_or]; grind
@[grind =, simp] lemma evalSucc_cons {xs : List Form} : ⋁ m, ↑(a :: xs) = disjTV (a.eval m) (⋁ m, ↑xs) := by simp [Kripke.evalSucc]
@[grind =, simp] lemma Sequent.evalΓ_cons {xs : List Form} : ⋀ m, ↑(a :: xs) = conjTV (a.eval m) (⋀ m, ↑xs) := by simp [Kripke.evalΓ]

@[grind =, simp]
lemma Sequent.evalΓ_eq_true :
    ⋀ m, xs = .t ↔ ∀ x ∈ xs, x.eval m = .t := by
  induction xs using Multiset.induction with simp_all [Kripke.evalΓ]
@[grind =, simp]
lemma Sequent.evalΓ_eq_false :
    ⋀ m, xs = .f ↔ ∃ x ∈ xs, x.eval m = .f := by
  induction xs using Multiset.induction with simp_all [Kripke.evalΓ]
@[grind =, simp]
lemma Sequent.evalΘ_eq_true :
    ⋀* m, xs = .t ↔ ∀ x ∈ xs, evalBlocked x m = .t := by
  induction xs using Multiset.induction with simp_all [Kripke.evalΘ]
@[grind =, simp]
lemma Sequent.evalΘ_eq_false :
    ⋀* m, xs = .f ↔ ∃ x ∈ xs, evalBlocked x m = .f := by
  induction xs using Multiset.induction with simp_all [Kripke.evalΘ]
@[grind =, simp]
lemma evalSucc_eq_true :
    ⋁ m, xs = .t ↔ ∃ x ∈ xs, x.eval m = .t := by
  induction xs using Multiset.induction with simp_all [Kripke.evalSucc]
@[grind =, simp]
lemma evalSucc_eq_false :
    ⋁ m, xs = .f ↔ ∀ x ∈ xs, x.eval m = .f := by
  induction xs using Multiset.induction with simp_all [Kripke.evalSucc]
@[grind ., simp]
lemma evalSucc_true (fin : f ∈ Δ ) (ev : f.eval m = TV.t ): Kripke.evalSucc Δ m = TV.t := by
 simp; use f
@[grind ., simp]
lemma evalΓ_false (h₁ : f ∈ Γ) (h₂ : f.eval m = TV.f) : Kripke.evalΓ Γ m = TV.f := by
  simp; use f
@[grind ., simp]
lemma evalΘ_false (h₁ : f ∈ Θ) (h₂ : evalBlocked f m = TV.f) : Kripke.evalΘ Θ m = TV.f := by
  simp; use f, h₁;



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
  Sequent.evalP { Γ := xs, Θ := xs', Δ := {a ⊃ b} } m ≠ TV.f →
  Sequent.evalP { Γ := xs, Θ := xs', Δ := ↑((a ⊃ b) :: ys) } m ≠ TV.f := by
  simp; intro h₁ h₂; simp_all

theorem eval_imp_righ_wo_ys_t :
  Sequent.evalP { Γ := xs, Θ := xs', Δ := {a ⊃ b} } m = TV.t →
  Sequent.evalP { Γ := xs, Θ := xs', Δ := ↑((a ⊃ b) :: ys) } m = TV.t := by
  simp; intro h₁; grind

@[grind ., simp]
theorem eval_imp_false_contradict :
  (a ⊃ b).eval m = TV.f → ∃ m' ∈ m.all, a.eval m' = .t ∧ b.eval m' = .f := by
  intro impF
  fun_induction Kripke.all with
  | case1 m ih =>
    rw [eval_imp_false_iff] at impF
    rcases impF with impF | ⟨m', impF⟩
    . grind
    . simp_all
      specialize ih m' (by grind) impF.right
      obtain ⟨m'', ih⟩ := ih
      grind

@[grind ., simp]
theorem evalBlocked_imp_true_then {m m': Kripke}
  (child : m' ∈ m.branch)
  (h : evalBlocked x m = TV.t) : (x.f ⊃ x.g).eval m' = TV.t := by
  simp_all [evalBlocked_true_iff]


/-! # Truth monotonicity -/
@[grind ., simp]
theorem Kripke.momo_branch_true {f : Form} {m m' : Kripke}
  (wf : m.wf) (mem : m' ∈ m.branch) (ftv : f.eval m = TV.t) :
    f.eval m' = TV.t := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.rejected ⊆ m.world.rejected := by
      unfold Kripke.wf at wf; simp at wf; exact wf
  specialize h m' mem
  obtain ⟨mf', fo, unfo⟩ := h
  match f with
  | .atom a => grind
  | .bot => grind
  | .and a b =>
    simp_all
    constructor
    . obtain ⟨atv, btv⟩ := ftv
      apply Kripke.momo_branch_true wf mem
      exact atv
    . obtain ⟨atv, btv⟩ := ftv
      apply Kripke.momo_branch_true wf mem
      exact btv
  | .or a b =>
    simp_all
    cases ftv with
    | inl h =>
      left
      apply Kripke.momo_branch_true wf mem
      exact h
    | inr h =>
      right
      apply Kripke.momo_branch_true wf mem
      exact h
  | .imp a b =>
    rw [eval_imp_true_iff] at ftv
    obtain ⟨h₁, h₂⟩ := ftv
    grind

theorem Kripke.mono_all_true {f : Form} {m m' : Kripke}
  (wf : m.wf) (mem : m' ∈ m.all) (ftv : f.eval m = TV.t) :
  f.eval m' = TV.t := by
  rw [Kripke.all] at mem
  --rw [Kripke.wf] at wf
  simp_all
  rcases mem with h | ⟨a, h₁, h₂⟩
  . grind
  . have wf' : m'.wf = true := Kripke.all_wf wf (by grind)
    have aT := Kripke.momo_branch_true wf h₁ ftv
    have awf : a.wf := by
      rw [Kripke.wf] at wf; simp at wf
      grind
    apply Kripke.mono_all_true awf h₂ aT
termination_by (m.depth)
decreasing_by exact depth_lt_of_mem h₁

/-! # Falsity monotonicity proof -/
@[grind ., simp]
theorem Kripke.mono_branch_false {f : Form} {m m' : Kripke}
  (wf : m.wf) (mem : m' ∈ m.branch ) (ftv : f.eval m' = .f) :
  f.eval m = .f  := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.rejected ⊆ m.world.rejected := by
      unfold Kripke.wf at wf; simp at wf; exact wf
  specialize h m' mem
  obtain ⟨mf', fo, unfo⟩ := h
  match f with
  | .atom a =>
    apply evaluate_atom_f_and at ftv; simp [Form.eval]; grind
  | .bot => grind
  | .and a b =>
    simp_all
    cases ftv with
    | inl h =>
      left
      apply Kripke.mono_branch_false wf mem
      exact h
    | inr h =>
      right
      apply Kripke.mono_branch_false wf mem
      exact h
  | .or a b =>
    simp_all
    constructor
    . obtain ⟨atv, btv⟩ := ftv
      apply Kripke.mono_branch_false wf mem
      exact atv
    . obtain ⟨atv, btv⟩ := ftv
      apply Kripke.mono_branch_false wf mem
      exact btv
  | .imp a b =>
    rw [eval_imp_false_iff]
    right
    use m'


theorem imp_false_branch {a b : Form} {m m' : Kripke}
(mem : m' ∈ m.branch) (h : (a ⊃ b).eval m' = TV.f) (wf : m.wf) :
b.eval m = TV.f := by
  rw [eval_imp_false_iff] at h
  rcases h with ⟨atv, btv⟩ | h
  . exact Kripke.mono_branch_false wf mem btv
  . obtain ⟨x, xmem, h⟩ := h
    have mwf : m'.wf = true := by rw [Kripke.wf] at wf; simp at wf; grind
    have := imp_false_branch xmem h mwf
    exact Kripke.mono_branch_false wf mem this
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
    have b_fut := Kripke.momo_branch_true wf mh' bT
    have m'_wf : m'.wf := by rw [Kripke.wf] at wf; simp_all
    apply  b_true_then_imp_true_branch m'_wf b_fut
termination_by (m.depth)
decreasing_by exact depth_lt_of_mem mh'

/- # INTERMITTENT SEMANTIC EVALUATION-/

mutual

@[grind]
inductive Form.forcedH : Form → List Form → Kripke →  Prop where
| atom a h w : a ∈ w.world.forced → forcedH (.atom a) h w
| and a b h w :
    forcedH a h w →
    forcedH b h w →
    forcedH (a ∧∧ b) h w
| or_left a b h w :
    forcedH a h w →
    forcedH (a ∨∨ b) h w
| or_right a b h w :
    forcedH b h w →
    forcedH (a ∨∨ b) h w
| imp_left a b h w :
    rejectedH a h w →
    (∀ w' ∈ w.branch, forcedH (a ⊃ b) h w') →
    forcedH (a ⊃ b) h w
| imp_right a b h w :
    forcedH b h w →
    (∀ w' ∈ w.branch, forcedH (a ⊃ b) h w') →
    forcedH (a ⊃ b) h w

@[grind]
inductive Form.rejectedH : Form → List Form → Kripke → Prop where
| atom a h w :
    a ∈ w.world.rejected →
    a ∉ w.world.forced →
    rejectedH (.atom a) h w
| bot h w :
    rejectedH ⊥ h w
| and_left a b h w :
    rejectedH a h w →
    rejectedH (a ∧∧ b) h w
| and_right a b h w :
    rejectedH b h w →
    rejectedH (a ∧∧ b) h w
| or a b h w :
    rejectedH a h w →
    rejectedH b h w →
    rejectedH (a ∨∨ b) h w
| imp_hist a b h w :
    a ∈ h →
    rejectedH b h w →
    rejectedH (a ⊃ b) h w
| imp_root a b h w :
    forcedH a h w →
    rejectedH b h w →
    rejectedH (a ⊃ b) h w
| imp_branch {h w w' a b} :
    w' ∈ w.branch →
    rejectedH (a ⊃ b) h w' →
    rejectedH (a ⊃ b) h w
end

def forcedBlockedH (i : Imp) (h : List Form) (w : Kripke) : Prop :=
  ∀ w' ∈ w.branch, (i.f ⊃ i.g).forcedH  h w'

def rejectedBlockedH (i : Imp) (h : List Form) (w : Kripke) : Prop :=
  ∃ w' ∈ w.branch, (i.f ⊃ i.g).rejectedH  h w'

@[simp, grind]
def Sequent.evalH (s : Sequent) (h : List Form) (m : Kripke) : Prop :=
  ((∀ f ∈ s.Γ, f.forcedH h m) ∧ (∀ i ∈ s.Θ, forcedBlockedH i h m)) ∧
    (∀ f ∈ s.Δ, f.rejectedH h m)

/-# Monotonicity-/
theorem forcedH_branch {a : Form} {h : List Form} {w w' : Kripke}
  (wf : w.wf) (mem : w' ∈ w.branch) (ha : a.forcedH h w) :
  a.forcedH h w' := by
  induction a generalizing w w' with
  | bot =>
      cases ha
  | atom a =>
      cases ha with
      | atom _ _ _ af =>
          have hwf : ∀ x ∈ w.branch,
              x.wf = true ∧
              w.world.forced ⊆ x.world.forced ∧
              x.world.rejected ⊆ w.world.rejected := by
            unfold Kripke.wf at wf
            simp at wf
            exact wf
          exact Form.forcedH.atom a h w' ((hwf w' mem).2.1 af)
  | and a b iha ihb =>
      cases ha with
      | and _ _ _ _ ha hb =>
          exact Form.forcedH.and a b h w' (iha wf mem ha) (ihb wf mem hb)
  | or a b iha ihb =>
      cases ha with
      | or_left _ _ _ _ ha =>
          exact Form.forcedH.or_left a b h w' (iha wf mem ha)
      | or_right _ _ _ _ hb =>
          exact Form.forcedH.or_right a b h w' (ihb wf mem hb)
  | imp a b iha ihb =>
      cases ha with
      | imp_left _ _ _ _ _ hbranch =>
          exact hbranch w' mem
      | imp_right _ _ _ _ _ hbranch =>
          exact hbranch w' mem

theorem forcedH_b_forces_imp {a b : Form} {h : List Form} {w : Kripke}
  (wf : w.wf) (hb : b.forcedH h w) :
  (a ⊃ b).forcedH h w := by
  apply Form.forcedH.imp_right
  · exact hb
  · intro w' hw'
    exact forcedH_b_forces_imp (a := a) (b := b) (h := h) (w := w')
      (Kripke.branch_wf wf hw') (forcedH_branch wf hw' hb)
termination_by w.depth
decreasing_by exact depth_lt_of_mem hw'

mutual
theorem forcedH_drop_history_head_of_self_forced {a z : Form} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hz : z.forcedH (z :: h) w) :
  a.forcedH (z :: h) w → a.forcedH h w := by
  intro ha
  match a with
  | .atom x =>
      cases ha with
      | atom _ _ _ hx =>
          exact Form.forcedH.atom x h w hx
  | .bot =>
      cases ha
  | .and x y =>
      cases ha with
      | and _ _ _ _ hx hy =>
          exact Form.forcedH.and x y h w
            (forcedH_drop_history_head_of_self_forced wf hz hx)
            (forcedH_drop_history_head_of_self_forced (a := y) (z := z) (h := h) (w := w) wf hz hy)
  | .or x y =>
      cases ha with
      | or_left _ _ _ _ hx =>
          exact Form.forcedH.or_left x y h w
            (forcedH_drop_history_head_of_self_forced (a := x) (z := z) (h := h) (w := w) wf hz hx)
      | or_right _ _ _ _ hy =>
          exact Form.forcedH.or_right x y h w
            (forcedH_drop_history_head_of_self_forced (a := y) (z := z) (h := h) (w := w) wf hz hy)
  | .imp x y =>
      cases ha with
      | imp_left _ _ _ _ hx hbranch =>
          exact Form.forcedH.imp_left x y h w
            (rejectedH_drop_history_head_of_self_forced (a := x) (z := z) (h := h) (w := w) wf hz hx)
            (by
              intro w' hw'
              exact forcedH_drop_history_head_of_self_forced
                (a := x ⊃ y) (z := z) (h := h) (w := w')
                (Kripke.branch_wf wf hw')
                (forcedH_branch wf hw' hz)
                (hbranch w' hw'))
      | imp_right _ _ _ _ hy hbranch =>
          exact Form.forcedH.imp_right x y h w
            (forcedH_drop_history_head_of_self_forced (a := y) (z := z) (h := h) (w := w) wf hz hy)
            (by
              intro w' hw'
              exact forcedH_drop_history_head_of_self_forced
                (a := x ⊃ y) (z := z) (h := h) (w := w')
                (Kripke.branch_wf wf hw')
                (forcedH_branch wf hw' hz)
                (hbranch w' hw'))
termination_by (a.complexity, w.depth)
decreasing_by
  all_goals first
  | apply Prod.Lex.left
    simp [Form.complexity]
    omega
  | apply Prod.Lex.right
    apply depth_lt_of_mem
    assumption

theorem rejectedH_drop_history_head_of_self_forced {a z : Form} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hz : z.forcedH (z :: h) w) :
  a.rejectedH (z :: h) w → a.rejectedH h w := by
  intro ha
  match a with
  | .atom x =>
      cases ha with
      | atom _ _ _ hx hnot =>
          exact Form.rejectedH.atom x h w hx hnot
  | .bot =>
      exact Form.rejectedH.bot h w
  | .and x y =>
      cases ha with
      | and_left _ _ _ _ hx =>
          exact Form.rejectedH.and_left x y h w
            (rejectedH_drop_history_head_of_self_forced wf hz hx)
      | and_right _ _ _ _ hy =>
          exact Form.rejectedH.and_right x y h w
            (rejectedH_drop_history_head_of_self_forced wf hz hy)
  | .or x y =>
      cases ha with
      | or _ _ _ _ hx hy =>
          exact Form.rejectedH.or x y h w
            (rejectedH_drop_history_head_of_self_forced wf hz hx)
            (rejectedH_drop_history_head_of_self_forced wf hz hy)
  | .imp x y =>
      cases ha with
      | imp_hist _ _ _ _ hx hy =>
          have hy' : y.rejectedH h w :=
            rejectedH_drop_history_head_of_self_forced wf hz hy
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact Form.rejectedH.imp_root x y h w
              (forcedH_drop_history_head_of_self_forced wf hz hz)
              hy'
          · exact Form.rejectedH.imp_hist x y h w hx' hy'
      | imp_root _ _ _ _ hx hy =>
          exact Form.rejectedH.imp_root x y h w
            (forcedH_drop_history_head_of_self_forced wf hz hx)
            (rejectedH_drop_history_head_of_self_forced wf hz hy)
      | @imp_branch _ _ w' _ _ hw' hy =>
          exact Form.rejectedH.imp_branch (h := h) (w := w) (w' := w') (a := x) (b := y)
            hw'
            (rejectedH_drop_history_head_of_self_forced
              (a := x ⊃ y) (z := z) (h := h) (w := w')
              (Kripke.branch_wf wf hw')
              (forcedH_branch wf hw' hz)
              hy)
termination_by (a.complexity, w.depth)
decreasing_by
  all_goals first
  | apply Prod.Lex.left
    simp [Form.complexity]
    omega
  | apply Prod.Lex.right
    apply depth_lt_of_mem
    assumption
end

/-# Transformation-/
mutual
theorem forcedH_to_eval {a : Form} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hist : ∀ f ∈ h, f.forcedH h w)
  (ha : a.forcedH h w) :
  a.eval w = TV.t := by
  match a with
  | .atom x =>
      cases ha with
      | atom _ _ _ hx =>
          rw [Form.eval]
          simp [hx]
  | .bot =>
      cases ha
  | .and x y =>
      cases ha with
      | and _ _ _ _ hx hy =>
          have hxT := forcedH_to_eval (a := x) (h := h) (w := w) wf hist hx
          have hyT := forcedH_to_eval (a := y) (h := h) (w := w) wf hist hy
          rw [evaluate_and, hxT, hyT]
          rfl
  | .or x y =>
      cases ha with
      | or_left _ _ _ _ hx =>
          have hxT := forcedH_to_eval (a := x) (h := h) (w := w) wf hist hx
          rw [evaluate_or, hxT]
          cases y.eval w <;> rfl
      | or_right _ _ _ _ hy =>
          have hyT := forcedH_to_eval (a := y) (h := h) (w := w) wf hist hy
          rw [evaluate_or, hyT]
          cases x.eval w <;> rfl
  | .imp x y =>
      rw [eval_imp_true_iff]
      cases ha with
      | imp_left _ _ _ _ hx hbranch =>
          constructor
          · left
            exact rejectedH_to_eval (a := x) (h := h) (w := w) wf hist hx
          · rw [List.all_eq_true]
            intro w' hw'
            have wf' : w'.wf := Kripke.branch_wf wf hw'
            have hist' : ∀ f ∈ h, f.forcedH h w' := by
              intro f hf
              exact forcedH_branch wf hw' (hist f hf)
            simpa using forcedH_to_eval (a := x ⊃ y) (h := h) (w := w') wf' hist' (hbranch w' hw')
      | imp_right _ _ _ _ hy hbranch =>
          constructor
          · right
            exact forcedH_to_eval (a := y) (h := h) (w := w) wf hist hy
          · rw [List.all_eq_true]
            intro w' hw'
            have wf' : w'.wf := Kripke.branch_wf wf hw'
            have hist' : ∀ f ∈ h, f.forcedH h w' := by
              intro f hf
              exact forcedH_branch wf hw' (hist f hf)
            simpa using forcedH_to_eval (a := x ⊃ y) (h := h) (w := w') wf' hist' (hbranch w' hw')
termination_by (a.complexity, w.depth)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; grind
  | apply Prod.Lex.right; apply depth_lt_of_mem; grind

theorem rejectedH_to_eval {a : Form} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hist : ∀ f ∈ h, f.forcedH h w)
  (ha : a.rejectedH h w) :
  a.eval w = TV.f := by
  match a with
  | .atom x =>
      cases ha with
      | atom _ _ _ xr xf =>
          rw [Form.eval]
          simp [xf, xr]
  | .bot =>
      rw [evaluate_bot]
  | .and x y =>
      cases ha with
      | and_left _ _ _ _ hx =>
          have hxF := rejectedH_to_eval wf hist hx
          rw [evaluate_and, hxF]
          cases y.eval w <;> rfl
      | and_right _ _ _ _ hy =>
          have hyF := rejectedH_to_eval wf hist hy
          rw [evaluate_and, hyF]
          cases x.eval w <;> rfl
  | .or x y =>
      cases ha with
      | or _ _ _ _ hx hy =>
          have hxF := rejectedH_to_eval wf hist hx
          have hyF := rejectedH_to_eval wf hist hy
          rw [evaluate_or, hxF, hyF]
          rfl
  | .imp x y =>
      rw [eval_imp_false_iff]
      cases ha with
      | imp_hist _ _ _ _ xh hy =>
          left
          constructor
          · exact forcedH_to_eval wf hist (hist x xh)
          · exact rejectedH_to_eval wf hist hy
      | imp_root _ _ _ _ hx hy =>
          left
          constructor
          · exact forcedH_to_eval wf hist hx
          · exact rejectedH_to_eval wf hist hy
      | @imp_branch h0 w0 wChild a0 b0 hw' hy =>
          right
          refine ⟨wChild, hw', ?_⟩
          have wf' : _ := Kripke.branch_wf wf hw'
          have hist' : ∀ f ∈ h, f.forcedH h wChild := by
            intro f hf
            exact forcedH_branch wf hw' (hist f hf)
          exact rejectedH_to_eval (a := x ⊃ y) (h := h) (w := wChild) wf' hist' hy
termination_by (a.complexity, w.depth)
decreasing_by
  all_goals first
  | apply Prod.Lex.left; grind
  | apply Prod.Lex.right; apply depth_lt_of_mem; grind

end

theorem forcedBlockedH_to_evalBlocked {i : Imp} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hist : ∀ f ∈ h, f.forcedH h w)
  (hi : forcedBlockedH i h w) :
  evalBlocked i w = TV.t := by
  rw [evalBlocked_true_iff]
  rw [List.all_eq_true]
  intro w' hw'
  have wf' : w'.wf := Kripke.branch_wf wf hw'
  have hist' : ∀ f ∈ h, f.forcedH h w' := by
    intro f hf
    exact forcedH_branch wf hw' (hist f hf)
  simpa using forcedH_to_eval (a := i.f ⊃ i.g) (h := h) (w := w') wf' hist' (hi w' hw')

theorem Sequent.evalH_to_evalR_false {s : Sequent} {h : List Form} {w : Kripke}
  (wf : w.wf)
  (hist : ∀ f ∈ h, f.forcedH h w)
  (hs : s.evalH h w) :
  s.evalR w = TV.f := by
  rw [Sequent.evalR_false_iff]
  constructor
  · have hΓ : Kripke.evalΓ s.Γ w = TV.t := by
      rw [Sequent.evalΓ_eq_true]
      intro f hf
      exact forcedH_to_eval (a := f) (h := h) (w := w) wf hist (hs.1.1 f hf)
    have hΘ : Kripke.evalΘ s.Θ w = TV.t := by
      rw [Sequent.evalΘ_eq_true]
      intro i hi
      exact forcedBlockedH_to_evalBlocked (i := i) (h := h) (w := w) wf hist (hs.1.2 i hi)
    simp [Kripke.evalAnt, hΓ, hΘ]
  · rw [evalSucc_eq_false]
    intro f hf
    exact rejectedH_to_eval (a := f) (h := h) (w := w) wf hist (hs.2 f hf)


end multiSucc
