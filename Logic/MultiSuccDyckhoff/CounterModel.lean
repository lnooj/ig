
import Logic.MultiSuccDyckhoff.Core
import Logic.MultiSuccDyckhoff.Helper
import Logic.MultiSuccDyckhoff.Display
import Logic.MultiSuccDyckhoff.Syntax

namespace multiSucc
open multiSucc

--IRREDUCABLE secuent:
--antecedent Γ contains only atomic implications, nested implications and atomic formulae
--and none of the atoms of the atomic implications are equal to any of the atomic formulae
structure World [DecidableEq Atom] where
  forced : Multiset Atom
  unforced : Multiset Atom
  --disjunct : Multiset.inter forced unforced = ∅

def Seq4Proof.forced (s : Seq4Proof) : Multiset Atom :=
match s with
| .seq4 as _ _ _ _ _ _ => ↑as

def Seq4Proof.unforced (s : Seq4Proof) : Multiset Atom :=
match s with
| .seq4 _ _ _ _ bs _ _ => ↑bs


def Seq4Proof.world [DecidableEq Atom] (p : Seq4Proof) : World :=
  let forced   := p.forced
  let unforced := p.unforced
  have disjunct : Multiset.inter forced unforced = ∅ := by
    sorry
  { forced := forced
  , unforced := unforced
  --, disjunct := disjunct
  }

structure CounterModel where --T World [CounterModel]
