import Results.EightEquidistantLines.Solution.KComp
import Results.EightEquidistantLines.Solution.Kdata.Insts
import Results.EightEquidistantLines.Solution.Kdata.Rows
import Results.EightEquidistantLines.Solution.Kdata.Cols
import Results.EightEquidistantLines.Solution.Kdata.Reps

/-!
# Selection of the generated data by level

`repsOf n` : orbit representatives on `n` labels (`n = 1..7`); `witsOf (n+1)` : for each
representative on `n` labels, the symmetry witnesses of its surviving extensions by label `n`;
`instsOf n`, `rowsOf n`, `colsOf n`, `kpOf n`, `doneOf n` : the constraint instances and packed level
data for the extension by label `n`.
-/

namespace Results.EightEquidistantLines.Ksel

open Kc Kdata

def repsOf : Nat → List (Nat × Nat)
  | 1 => reps1 | 2 => reps2 | 3 => reps3 | 4 => reps4 | 5 => reps5 | 6 => reps6 | 7 => reps7 | _ => []

def witsOf : Nat → List (List (Nat × Nat × Nat × Nat))
  | 2 => wits2 | 3 => wits3 | 4 => wits4 | 5 => wits5 | 6 => wits6 | 7 => wits7 | 8 => wits8 | _ => []

def instsOf : Nat → List Inst
  | 1 => insts1 | 2 => insts2 | 3 => insts3 | 4 => insts4 | 5 => insts5 | 6 => insts6 | 7 => insts7 | _ => []

def rowsOf : Nat → List (List Nat)
  | 1 => rows1 | 2 => rows2 | 3 => rows3 | 4 => rows4 | 5 => rows5 | 6 => rows6 | 7 => rows7 | _ => []

def colsOf : Nat → List Nat
  | 1 => cols1 | 2 => cols2 | 3 => cols3 | 4 => cols4 | 5 => cols5 | 6 => cols6 | 7 => cols7 | _ => []

def kpOf : Nat → Nat
  | 1 => kp1 | 2 => kp2 | 3 => kp3 | 4 => kp4 | 5 => kp5 | 6 => kp6 | 7 => kp7 | _ => 0

def doneOf : Nat → List Nat
  | 1 => done1 | 2 => done2 | 3 => done3 | 4 => done4 | 5 => done5 | 6 => done6 | 7 => done7 | _ => []

def lvOf (n : Nat) : Lv := ⟨rowsOf n, colsOf n, kpOf n, doneOf n⟩

end Results.EightEquidistantLines.Ksel
