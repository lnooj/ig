import Logic.MultiSuccCorsiTassi.Core
--import Logic.MultiSuccCorsiTassi.Display

namespace multiSucc
open multiSucc

/- structure World where
forced : Multiset Atom
unforced : Multiset Atom

def Sequent.forced (s : Sequent) : Multiset Atom := s.toSeq4.as

def Sequent.unforced (s : Sequent) : Multiset Atom := s.toSeq4.bs

def Sequent.world (p : Sequent) : World := ⟨p.forced, p.unforced⟩ -/

structure World where
forced : List Atom
unforced : List Atom

def Seq4Proof.forced (s : Seq4Proof) : List Atom := s.as

def Seq4Proof.unforced (s : Seq4Proof) : List Atom := s.bs

def Seq4Proof.world (p : Seq4Proof) : World := ⟨p.forced, p.unforced⟩

structure CM where
world : World
branch : List CM
