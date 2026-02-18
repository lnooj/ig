import Logic.MultiSuccCorsiTassi.Core
import Logic.MultiSuccCorsiTassi.Helper
--import Logic.MultiSuccCorsiTassi.Display

namespace multiSucc
open multiSucc

structure World where
forced : List Atom
unforced : List Atom

def Seq4Proof.forced (s : Seq4Proof) : List Atom := s.as

def Seq4Proof.unforced (s : Seq4Proof) : List Atom := s.bs

def Seq4Proof.world (p : Seq4Proof) : World := ⟨p.forced, p.unforced⟩

structure CM where
world : World
branch : List CM

/--Truth Value: true, false, unknown -/
inductive TV  where
| t : TV
| f : TV
| u : TV
deriving BEq

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


instance conjTV_rightCommutative : RightCommutative conjTV where
right_comm a b c := by cases a <;> cases b <;> cases c <;> rfl

instance disjTV_rightCommutative : RightCommutative disjTV where
right_comm a b c := by cases a <;> cases b <;> cases c <;> rfl


/- def CM.depth : CM → Nat
| ⟨_, branch⟩ => 1 + branch.length --root+children
 -/
def CM.depth : CM → Nat
| ⟨_, branch⟩ =>
  1 + branch.foldl (fun m cm => max m cm.depth) 0



lemma depth_lt_of_mem {cm' cm : CM} :
  cm' ∈ cm.branch → cm'.depth < cm.depth := by
  intro hmem
  cases cm with
  | mk w branch =>
    simp [CM.depth]
    sorry

def evaluate : Form → CM → TV
| .atoms a, cm => if a ∈ cm.world.forced then .t
       else if a ∈ cm.world.unforced then .f
       else dbg_trace "atom undefined"; .u
| .bot, cm => .f
| .and f g, cm => conjTV (evaluate f cm) (evaluate g cm )
| .or f g, cm => disjTV (evaluate f cm) (evaluate g cm )
| .imp f g, cm =>
  if (evaluate f cm == .f || evaluate g cm == .t)
      && (cm.branch.map (λ cm' => evaluate (f ⊃ g) cm' == .t)).all id then .t
  else if (evaluate f cm == .t && evaluate g cm == .f)
      || (cm.branch.map (λ cm' => evaluate (f ⊃ g) cm' == .f)).any id then .f --only one false
  else dbg_trace "imp undefined";.u
| .impB f g, cm =>
  if (cm.branch.map (λ cm' => evaluate (f ⊃ g) cm' == .t)).all id then .t
  else if (cm.branch.map (λ cm' => evaluate (f ⊃ g) cm' == .f)).any id then .f
  else .u
termination_by fm cm => (sizeOf_Form fm, cm.depth)
decreasing_by
all_goals first | (apply Prod.Lex.left; grind) | (apply Prod.Lex.right; apply depth_lt_of_mem; grind)


def evalAnt (Γ : List Form) (cm : CM) : TV :=
match Γ with
| []      => TV.t
| f :: Γ' => conjTV (evaluate f cm) (evalAnt Γ' cm)

def evalSucc (Δ : List Form) (cm : CM) : TV :=
match Δ with
| []      => TV.f
| f :: Δ' => disjTV (evaluate f cm) (evalSucc Δ' cm)


-- A sequent is refutable iff all its assumptions are satisfied (all forms in Γ are true) but none of the conclusions are (all Δ are false)
def evalSeq : Sequent → CM → TV
| ⟨Γ, Δ ⟩, cm =>
  match (evalAnt (Multiset.sort Γ LE.le) cm) , (evalSucc (Multiset.sort Δ LE.le) cm) with
  | .u, _ | _, .u => .u
  | .t, .f => .f
  | _, _ => .t
