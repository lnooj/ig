import Logic.Completeness
import Logic.Core
import Logic.Soundness
import Logic.Display
import Logic.Helper
import Logic.Kripke
import Logic.MultiSuccCorsiTassi
import Logic.IG
import Logic.RIG
import Logic.Result
import Logic.Syntax
import Logic.Termination

namespace multiSucc

/--
info: structure multiSucc.Kripke : Type
number of parameters: 0
fields:
  multiSucc.Kripke.world : World
  multiSucc.Kripke.branch : List Kripke
constructor:
  multiSucc.Kripke.mk (world : World) (branch : List Kripke) : Kripke
-/
#guard_msgs in #print Kripke
