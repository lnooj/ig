import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Helper
--import Logic.MultiSuccCorsiTassi.Display

namespace multiSucc
open multiSucc

structure World where
  forced : Finset Atom
  unforced : Finset Atom
 -- prop : Disjoint forced unforced
deriving DecidableEq
--TODO PROOF OF MONOTONICITY. FORCED STAY FORCED. u is if c isnt in any.
-- unforced vastupidi
--wellFormed World
def Seq4Proof.forced (s : Seq4Proof) : Finset Atom := s.as.toFinset

def Seq4Proof.unforced (s : Seq4Proof) : Finset Atom := s.bs.toFinset

def Seq4Proof.world (p : Seq4Proof) : World := ⟨p.forced, p.unforced⟩ -- , Finset.disjoint_sdiff⟩

-- attribute [grind .] World.prop


structure Model where
  world : World
  branch : List Model
deriving BEq

--@[grind, simp]
def Model.wf (m : Model) : Bool :=
∀ fm ∈ m.branch.attach,
  fm.val.wf ∧
  m.world.forced ⊆ fm.val.world.forced ∧
  fm.val.world.unforced ⊆ m.world.unforced
decreasing_by
all_goals
  have : sizeOf m.branch < sizeOf m := by grind [Model]
  apply lt_trans _ this
  apply List.sizeOf_lt_of_mem
  grind


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




/--Truth Value: true, false, unknown -/
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




@[grind]
def Form.eval : Form → Model → TV
| .atoms a, m => if a ∈ m.world.forced then .t
       else if a ∈ m.world.unforced then .f
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


@[grind ., simp] theorem evalute_atom_t (h :  (Form.atoms a).eval m = .t) : a ∈ m.world.forced := by grind
@[grind ., simp] theorem evalute_atom_f (h :  (Form.atoms a).eval m = .f) : a ∈ m.world.unforced := by grind
@[grind ., simp] theorem evalute_atom_f_and (h :  (Form.atoms a).eval m = .f) : a ∈ m.world.unforced ∧ a ∉ m.world.forced:= by grind
@[grind =, simp] theorem evalute_bot : Form.bot.eval m = .f := by grind
@[grind =, simp] theorem evalute_and : (a ∧∧ b).eval m = conjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evalute_or : (a ∨∨ b).eval m = disjTV (a.eval m) (b.eval m) := by grind
@[grind =, simp] theorem evalute_atom_undef : (Form.atoms a).eval m = .u ↔ a ∉ m.world.forced ∧ a ∉ m.world.unforced := by grind


/- def evalBlocked : Imp → Model → TV
| {f, g}, m =>
  if (m.branch.map (λ m' => (f ⊃ g).eval m' = .t)).all id then .t
  else if (m.branch.map (λ m' => (f ⊃ g).eval m' = .f)).any id then .f
  else .u -/


def evalAnt (Γ : Multiset Form) (m : Model) : TV :=
  (Γ.map (fun f => f.eval m)).fold conjTV TV.t
scoped notation "⋀ " m:max ", " Γ:max => evalAnt Γ m

def evalSucc (Δ : Multiset Form) (m : Model) : TV :=
  (Δ.map (fun f => f.eval m)).fold disjTV TV.f
scoped notation "⋁ " m:max ", " Γ:max => evalSucc Γ m

-- A sequent is refutable iff all its assumptions are satisfied (all forms in Γ are true) but none of the conclusions are (all Δ are false)
@[grind]
def evalSeq : Sequent /- → List Imp -/ → Model → TV
| ⟨Γ, Δ ⟩, /- bl, -/ m =>
  match (evalAnt Γ m) , (evalSucc Δ m) with
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

@[simp]
theorem evalSeq_true_iff :
  evalSeq s m = TV.t ↔
  evalAnt s.Γ m = TV.f ∨ evalSucc s.Δ m = TV.t := by
  grind

@[simp]
theorem evalSeq_false_iff :
  evalSeq s m = TV.f ↔
  evalAnt s.Γ m = TV.t ∧ evalSucc s.Δ m = TV.f := by
  simp [evalSeq]
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



--IMP EVAL--
theorem eval_imp_true_iff :
  (a ⊃ b).eval m = TV.t ↔
    ((a.eval m = .f ∨ b.eval m = .t) ∧ (m.branch.all (λ m' => (a ⊃ b).eval m' = .t))) := by
  constructor
  . intro h; rw [Form.eval] at h; simp_all; grind [Form.eval]
  . intro h; rw [Form.eval]; simp_all

theorem eval_imp_false_iff :
  (a ⊃ b).eval m = TV.f ↔
    a.eval m = .t ∧  b.eval m = .f ∨ ∃ x ∈ m.branch, ((a ⊃ b).eval x = TV.f) := by
  constructor
  . intro h; rw [Form.eval] at h; simp_all
    split_ifs at h
    . grind
  . intro h; rw [Form.eval]; simp_all; grind

theorem eval_imp_righ_wo_ys :
  evalSeq { Γ := ↑xs, Δ := {a ⊃ b} } m ≠ TV.f →
  evalSeq { Γ := ↑xs, Δ := ↑((a ⊃ b) :: ys) } m ≠ TV.f := by
  simp; intro h₁ h₂; simp_all

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


--MONOTONICITY--

/-
same as mode_branch_mono
theorem mono_true_form {a : Form} {m : Model} :
  ( a.eval m = .t) → (∀ x ∈ m.branch, a.eval x = .t)  := by sorry -/

@[grind ., simp]
theorem Model.all_nested_in_all {m m' a : Model} (h₁ : a ∈ m.branch) (h₂ : m' ∈ a.all) : m' ∈ m.all := by
  fun_induction Model.all m with
  | case1 m ih => simp_all; right; grind

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

--TODO IMPORTANT
@[grind ., simp]
theorem Model.momo_branch_true {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.branch) (ftv : f.eval m = TV.t) :
    f.eval m' = TV.t := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.unforced ⊆ m.world.unforced := by
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

-- IN USE
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

@[grind ., simp]
theorem Model.mono_branch_false {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.branch ) (ftv : f.eval m' = .f) :
  f.eval m = .f  := by
  have h : ∀ a ∈ m.branch, a.wf = true ∧
        m.world.forced ⊆ a.world.forced ∧
        a.world.unforced ⊆ m.world.unforced := by
      unfold Model.wf at wf; simp at wf; exact wf
  specialize h m' mem
  obtain ⟨mf', fo, unfo⟩ := h
  match f with
  | .atoms a =>
    apply evalute_atom_f_and at ftv; simp [Form.eval]; grind -- NEED DISJONINT PROOF ?!!? NO???
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

/- theorem mono_false_all_branch {f : Form} {m m' a : Model}
  (wf : m.wf) (mem : a ∈ m.branch) (mem' : m' ∈ a.all ) (ftv : f.eval m' = .f)  :
  f.eval a = .f := by
  rw [Model.all] at mem'; simp at mem'
  rcases mem' with id | ⟨mm, h₁, h₂⟩
  . grind
  . have awf : a.wf = true := by rw [Model.wf] at wf; simp at wf; grind
    have mmwf : mm.wf = true := by rw [Model.wf] at awf; simp at awf; grind
    sorry
    --have : f.eval mm = .f := Model.mono_branch_false mmwf mem ftv
    --exact mono_false_all_branch (by sorry) h₁ h₂


theorem mono_false_form_all {f : Form} {m m' : Model}
  (wf : m.wf) (mem : m' ∈ m.all ) (ftv : f.eval m' = .f) :
  f.eval m = .f  := by
  rw [Model.all] at mem
  simp_all
  rcases mem with h | ⟨a, h₁, h₂⟩
  . grind
  . have h := mono_false_all_branch wf h₁ h₂ ftv
    have wf' : m'.wf = true := Model.all_wf wf (by grind)
    exact Model.mono_branch_false wf h₁ h -/


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

-- IN USE
theorem imp_false_then_b_false  (impF : (a ⊃ b).eval m = TV.f) (wf : m.wf) : b.eval m = .f := by
  rw [eval_imp_false_iff] at impF
  cases impF with
  | inl h => grind
  | inr h =>
    rcases h with ⟨m', mem, h₂⟩
    exact imp_false_branch mem h₂ wf

end multiSucc
