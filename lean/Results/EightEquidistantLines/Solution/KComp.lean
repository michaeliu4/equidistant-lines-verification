
/-!
# The finite computation: definitions

Computational (kernel-evaluated) part of the finite verification.  Everything here is a plain
definition; the soundness theorems are in `KEqn`, `KDfs`, `KWit`, `KChain`.

**Joint bit-vectors.**  Sign data on labels `0..7` is packed in a natural number `x`: the
chirotope sign `χ_{abc}` (`a<b<c`) is bit `triIdx a b c` (`0..55`, colexicographic), the distance
sign `ε_{ab}` (`a<b`) is bit `vE a b = 56 + prIdx a b` (`56..83`); a set bit means *negative*.

**Equations.**  An `Eqn` is a list of bit indices (toggles) and a constant; it is *satisfied* by `x`
when the XOR of the toggled bits and the constant is `false`.  An `Inst` is a local constraint
instance (a 3-term GP relation, a circuit pattern, or a five-label obstruction slot); its
equations (padded to 8) are *all satisfied* exactly when the instance is violated.

**Extension search.**  Adding label `n` to a sign datum on labels `< n` introduces the
variables `orderOf n`.  For a list of instances the *level data* `Lv` packs, one bit per
(system `s`, equation `e`), the satisfaction status of all equations bit-parallel (`cols` = effect
of each variable, `kp` = status of the all-zero assignment), the bit of equation `e` of system `s`
being at position `e * S + s` (`S` = number of systems);
`leavesM` enumerates, by depth-first search, all assignments of the new variables not pruned by a
completely assigned, fully satisfied system (`done` = the systems completely assigned after each
depth).

The hot loops use the recursors `Nat.rec` / `List.rec` directly (the kernel evaluates these
about an order of magnitude faster than compiled structural recursion), hence `noncomputable`.
-/

namespace Results.EightEquidistantLines.Kc

/-! ### Indices -/

def triIdx (a b c : Nat) : Nat := c * (c - 1) * (c - 2) / 6 + b * (b - 1) / 2 + a
def prIdx (a b : Nat) : Nat := b * (b - 1) / 2 + a
def vE (a b : Nat) : Nat := 56 + prIdx a b

/-- Joint index of the (alternating-extended) triple sign `χ_{abc}` together with the parity of the
sorting permutation: `χ_{abc} = (-1)^parity χ_{sorted}`. -/
def xT (a b c : Nat) : Nat × Bool :=
  if a < b then
    if b < c then (triIdx a b c, false)
    else if a < c then (triIdx a c b, true)
    else (triIdx c a b, false)
  else
    if a < c then (triIdx b a c, true)
    else if b < c then (triIdx b c a, false)
    else (triIdx c b a, true)

/-! ### Equations and instances -/

structure Eqn where
  tog : List Nat
  c : Bool

namespace Eqn
def zero : Eqn := ⟨[], false⟩
def one : Eqn := ⟨[], true⟩
def add (p q : Eqn) : Eqn := ⟨p.tog ++ q.tog, p.c ^^ q.c⟩
def X (a b c : Nat) : Eqn := ⟨[(xT a b c).1], (xT a b c).2⟩
def E (a b : Nat) : Eqn := ⟨[if a < b then vE a b else vE b a], false⟩
def sum (l : List Eqn) : Eqn := l.foldl add zero
/-- Value of the equation on `x`: XOR of the toggled bits and the constant. Satisfied iff `false`. -/
def eval (q : Eqn) (x : Nat) : Bool := q.tog.foldl (fun acc i => acc ^^ x.testBit i) q.c
/-- Bit mask of the toggles (a variable toggled twice cancels). -/
def mask (q : Eqn) : Nat := q.tog.foldl (fun m i => m ^^^ (1 <<< i)) 0
/-- Code of an equation: the toggle mask (bits `0..83`) with the constant stored in bit `100`. -/
def code (q : Eqn) : Nat := q.mask ||| (bif q.c then 1 <<< 100 else 0)
end Eqn

/-- Matching test for a sign class of the six-edge graph on four vertices; `p` encodes the edge
flags (bit `t` for the `t`-th edge `01,02,03,12,13,23`). -/
def isMatching (p : Nat) (color : Bool) : Bool :=
  [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]].all fun inc =>
    (inc.filter fun t => p.testBit t == color).length ≤ 1

/-- The 20 edge-flag patterns in which one sign class is a matching. -/
def forbPats : List Nat := (List.range 64).filter fun p => isMatching p false || isMatching p true

/-- A local constraint instance (labels are natural numbers `< 8`). -/
inductive Inst where
  | gp (a b c d e : Nat)
  | circ (v0 v1 v2 v3 p : Nat)
  | forb (r s i j k : Nat)

/-- Equations of the three-term Grassmann–Plücker instance with pivot `a` (matched iff
`t1 = t2 = t3`, with `t1 = χ_abc χ_ade`, `t2 = -χ_abd χ_ace`, `t3 = χ_abe χ_acd`). -/
def gpEqs (a b c d e : Nat) : List Eqn :=
  let x1 := Eqn.X a b c
  let x2 := Eqn.X a d e
  let x3 := Eqn.X a b d
  let x4 := Eqn.X a c e
  let x5 := Eqn.X a b e
  let x6 := Eqn.X a c d
  let t1 := Eqn.add x1 x2
  let t2 := Eqn.add (Eqn.add x3 x4) Eqn.one
  let t3 := Eqn.add x5 x6
  [Eqn.add t1 t2, Eqn.add t2 t3]

/-- The six edge flags `σ_ij = ε_{v_i v_j} ⊕ α_i ⊕ α_j` of the circuit condition (before comparing
with a pattern). -/
def circBase (v0 v1 v2 v3 : Nat) : List Eqn :=
  let al0 := Eqn.X v1 v2 v3
  let al1 := Eqn.add Eqn.one (Eqn.X v0 v2 v3)
  let al2 := Eqn.X v0 v1 v3
  let al3 := Eqn.add Eqn.one (Eqn.X v0 v1 v2)
  [Eqn.add (Eqn.add (Eqn.E v0 v1) al0) al1, Eqn.add (Eqn.add (Eqn.E v0 v2) al0) al2,
   Eqn.add (Eqn.add (Eqn.E v0 v3) al0) al3, Eqn.add (Eqn.add (Eqn.E v1 v2) al1) al2,
   Eqn.add (Eqn.add (Eqn.E v1 v3) al1) al3, Eqn.add (Eqn.add (Eqn.E v2 v3) al2) al3]

/-- Equations of the circuit instance for the edge-flag pattern `p` (all satisfied iff `σ = p`). -/
def circEqs (v0 v1 v2 v3 p : Nat) : List Eqn :=
  ((circBase v0 v1 v2 v3).zip (List.range 6)).map fun (q, t) => ⟨q.tog, q.c ^^ p.testBit t⟩

/-- Equations of the five-label obstruction slot `(r, s; i, j, k)`: the seven parity equations
`h_i = h_j`, `h_j = h_k`, `H_i = H_j`, `H_j = H_k`, `h_i a_jk = H_i A_jk`, `H_i A_jk = w_ij`,
`w_ij = -w_ik` of the sign quantities `h*, H*, a*, A*, w*`. -/
def forbEqs (r s i j k : Nat) : List Eqn :=
  let ers := Eqn.E r s
  let xrsi := Eqn.X r s i
  let xrsj := Eqn.X r s j
  let xrsk := Eqn.X r s k
  let hi := Eqn.add (Eqn.add ers (Eqn.E r i)) xrsi
  let hj := Eqn.add (Eqn.add ers (Eqn.E r j)) xrsj
  let hk := Eqn.add (Eqn.add ers (Eqn.E r k)) xrsk
  let Hi := Eqn.add (Eqn.add Eqn.one (Eqn.E s i)) xrsi
  let Hj := Eqn.add (Eqn.add Eqn.one (Eqn.E s j)) xrsj
  let Hk := Eqn.add (Eqn.add Eqn.one (Eqn.E s k)) xrsk
  let ajk := Eqn.add (Eqn.add xrsj xrsk) (Eqn.X r j k)
  let Ajk := Eqn.add (Eqn.add (Eqn.add ers xrsj) xrsk) (Eqn.X s j k)
  let wij := Eqn.add (Eqn.add (Eqn.add (Eqn.add (Eqn.add (Eqn.add Eqn.one ers) (Eqn.E i j)) xrsi) xrsj) (Eqn.X r i j)) (Eqn.X s i j)
  let wik := Eqn.add (Eqn.add (Eqn.add (Eqn.add (Eqn.add (Eqn.add Eqn.one ers) (Eqn.E i k)) xrsi) xrsk) (Eqn.X r i k)) (Eqn.X s i k)
  [Eqn.add hi hj, Eqn.add hj hk, Eqn.add Hi Hj, Eqn.add Hj Hk,
   Eqn.add (Eqn.add hi ajk) (Eqn.add Hi Ajk), Eqn.add (Eqn.add Hi Ajk) wij, Eqn.add (Eqn.add wij wik) Eqn.one]

/-- Pad to exactly eight equations (the dummy equation is always satisfied). -/
def pad8 (l : List Eqn) : List Eqn := l ++ List.replicate (8 - l.length) Eqn.zero

/-- The eight equations of an instance; all satisfied iff the instance is violated. -/
def Inst.eqns : Inst → List Eqn
  | .gp a b c d e => pad8 (gpEqs a b c d e)
  | .circ v0 v1 v2 v3 p => pad8 (circEqs v0 v1 v2 v3 p)
  | .forb r s i j k => pad8 (forbEqs r s i j k)

/-- The labels of an instance. -/
def Inst.labs : Inst → List Nat
  | .gp a b c d e => [a, b, c, d, e]
  | .circ v0 v1 v2 v3 _ => [v0, v1, v2, v3]
  | .forb r s i j k => [r, s, i, j, k]

/-- Syntactic well-formedness of an instance for the extension by label `n`: the labels are
`≤ n`, pairwise distinct; for a circuit instance the pattern is one of the 20 forbidden patterns. -/
def Inst.wfB (n : Nat) (inst : Inst) : Bool :=
  inst.labs.all (· ≤ n) && inst.labs.Nodup &&
    (match inst with
     | .circ _ _ _ _ p => (isMatching p false || isMatching p true) && p < 64
     | _ => true)

/-- Codes of the eight equations of an instance. -/
def Inst.row (i : Inst) : List Nat := i.eqns.map Eqn.code

/-! ### Extension variables and level data -/

/-- The new variables when adding label `n`, in search order (stage `m = 0..n-1`: `ε_{m,n}`, then
`χ_{a,m,n}` for `a < m`). -/
def orderOf (n : Nat) : List Nat :=
  (List.range n).flatMap fun m =>
    vE m n :: (List.range m).map fun a => triIdx a m n

/-- Variables of labels `< n` (the base variables). -/
def baseVars (n : Nat) : List Nat :=
  ((List.range n).flatMap fun c => (List.range c).flatMap fun b => (List.range b).map fun a => triIdx a b c) ++
  ((List.range n).flatMap fun b => (List.range b).map fun a => vE a b)

/-- Packed level data (the generated literals `Kdata`): for the instance rows `rows`
(`rows[s]` = the eight equation codes), `cols[v]` has bit `e * S + s` iff variable `v` occurs in
equation `e` of system `s` (`S = rows.length`); `kp` has bit `e * S + s` iff equation `e` of `s` is
satisfied by the all-zero assignment; `done[d-1]` has bit `s` iff system `s` involves only new
variables among the first `d` ones. -/
structure Lv where
  rows : List (List Nat)
  cols : List Nat
  kp : Nat
  done : List Nat

/-- `∀ k < n, P k` as a boolean, by a direct recursor. -/
def allBelow (n : Nat) (P : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => and ih (P k)) n

/-- Stride of the transposition trick. -/
def SIG : Nat := 600

/-- All equation masks `e` of the systems packed with stride `SIG`: block `s` holds the code of
equation `e` of system `s`. -/
noncomputable def packE (rows : List (List Nat)) (e : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s => Nat.lor (Nat.shiftLeft (r.getD e 0) (SIG * s)) (ih (s + 1))) rows) 0

/-- `Σ_{s < S} 2^(SIG * s)`. -/
def onesS (S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun s ih => Nat.lor ih (Nat.shiftLeft 1 (SIG * s))) S

/-- Packed column of variable `v` (see `Lv`): bit `e * S + s` iff the code of equation `e` of system
`s` has bit `v` (here `S = rows.length`).  Computed bit-parallel by a transposition trick: the bits `v`
of the codes sit at the positions `SIG * s` of `packE rows e >>> v`; reduction modulo `2^(SIG-1) - 1`
(`2^SIG ≡ 2`) moves them to the positions `s`. -/
noncomputable def colSpec (rows : List (List Nat)) (v : Nat) : Nat :=
  let S := rows.length
  let ones := onesS S
  let md := 2 ^ (SIG - 1) - 1
  Nat.rec (motive := fun _ => Nat) 0
    (fun e ih => Nat.lor ih (Nat.shiftLeft (Nat.mod (Nat.land (Nat.shiftRight (packE rows e) v) ones) md) (e * S))) 8

/-- Packed status of the all-zero assignment: bit `e * S + s` iff the constant of equation `e` of
system `s` is `false` (satisfied). -/
noncomputable def kpSpec (rows : List (List Nat)) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s =>
      Nat.lor
        ((List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
          (fun q _ ih2 e =>
            bif Nat.beq (Nat.land (Nat.shiftRight q 100) 1) 1
            then ih2 (e + 1) else Nat.lor (Nat.shiftLeft 1 (e * rows.length + s)) (ih2 (e + 1)))
          r) 0)
        (ih (s + 1))) rows) 0

/-- Mask of the new variables among the first `d` of the order of `n`. -/
def assignedMask (n d : Nat) : Nat := (orderOf n).take d |>.foldl (fun m v => m ||| (1 <<< v)) 0

/-- Mask of all new variables for `n`. -/
def newMask (n : Nat) : Nat := assignedMask n (orderOf n).length

/-- Done-mask after the first `d` new variables are assigned: bit `s` iff the new variables
occurring in system `s` are among them. -/
noncomputable def doneAt (n : Nat) (rows : List (List Nat)) (d : Nat) : Nat :=
  let am := assignedMask n d
  let nm := newMask n
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s =>
      let vn := Nat.land (r.foldl (fun acc q => Nat.lor acc q) 0) nm
      bif Nat.beq (Nat.xor vn (Nat.land vn am)) 0 then Nat.lor (Nat.shiftLeft 1 s) (ih (s + 1)) else ih (s + 1))
    rows) 0

noncomputable def doneSpec (n : Nat) (rows : List (List Nat)) : List Nat :=
  (List.range (orderOf n).length).map fun d => doneAt n rows (d + 1)

/-! ### Depth-first search -/

/-- With `S` systems: bit `s` (`s < S`) of the result is set iff the eight equation bits
`e * S + s` (`e < 8`) of `q` are all set; higher bits are meaningless. -/
def red (S q : Nat) : Nat :=
  let a := Nat.land q (Nat.shiftRight q (4 * S))
  let b := Nat.land a (Nat.shiftRight a (2 * S))
  Nat.land b (Nat.shiftRight b S)

/-- Search steps: (bit of the new variable, its column, the done mask after assigning it). -/
def mkSteps (ord cols done : List Nat) : List (Nat × Nat × Nat) :=
  (ord.zip done).map fun (v, dn) => (1 <<< v, cols.getD v 0, dn)

/-- Depth-first search; state `(q, mq = red S q, x)`, leaves accumulated in `acc`. -/
noncomputable def dfsM (S : Nat) (xs : List (Nat × Nat × Nat)) : Nat → Nat → Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Nat → List Nat)
    (fun _ _ x acc => List.cons x acc)
    (fun t _ ih q mq x acc =>
      let q1 := Nat.xor q t.2.1
      let m1 := red S q1
      let acc1 := bif Nat.ble 1 (Nat.land m1 t.2.2) then acc else ih q1 m1 (Nat.lor x t.1) acc
      bif Nat.ble 1 (Nat.land mq t.2.2) then acc1 else ih q mq x acc1) xs

/-- The surviving extensions of the base datum `y` (joint bits of labels `< n`) by label `n`,
as joint bit-vectors on labels `≤ n` (leaf order: the `ε`/`χ` variables assigned `false` first). -/
noncomputable def leavesM (n : Nat) (lv : Lv) (y : Nat) : List Nat :=
  let q0 := (baseVars n).foldl (fun q v => bif Nat.testBit y v then Nat.xor q (lv.cols.getD v 0) else q) lv.kp
  dfsM lv.rows.length (mkSteps (orderOf n) lv.cols lv.done) q0 (red lv.rows.length q0) y []

/-! ### Symmetry witnesses -/

def xBit (x a b c : Nat) : Bool := Nat.testBit x (xT a b c).1 ^^ (xT a b c).2
def eBit (x a b : Nat) : Bool := Nat.testBit x (if a < b then vE a b else vE b a)
def piGet (pi k : Nat) : Nat := Nat.land (Nat.shiftRight pi (3 * k)) 7

/-- Witness check on `m` labels: the permutation (3 bits per label in `pi`) is a bijection of
`{0..m-1}`, and applying `(pi, g, nu)` to the joint datum `x` gives the joint datum `r`:
`r_{abc} = g_a ⊕ g_b ⊕ g_c ⊕ x_{π a π b π c}` and `r_{ab} = ν ⊕ g_a ⊕ g_b ⊕ x_{π a π b}`. -/
noncomputable def witOk (m : Nat) (x r pi g : Nat) (nu : Bool) : Bool :=
  and (allBelow m fun a => and (Nat.ble 1 (m - piGet pi a)) (allBelow m fun b => or (Nat.beq a b) (not (Nat.beq (piGet pi a) (piGet pi b)))))
  (and (allBelow m fun c => allBelow c fun b => allBelow b fun a =>
      not (Bool.xor (Nat.testBit r (triIdx a b c))
        (Bool.xor (Bool.xor (Nat.testBit g a) (Nat.testBit g b)) (Bool.xor (Nat.testBit g c) (xBit x (piGet pi a) (piGet pi b) (piGet pi c))))))
    (allBelow m fun b => allBelow b fun a =>
      not (Bool.xor (Nat.testBit r (vE a b))
        (Bool.xor (Bool.xor nu (Nat.testBit g a)) (Bool.xor (Nat.testBit g b) (eBit x (piGet pi a) (piGet pi b)))))))

/-- Check the list of leaves against its witnesses `(rep index, pi, g, nu)` (aligned, same length). -/
noncomputable def zipCheck (m : Nat) (reps : List Nat) : List Nat → List (Nat × Nat × Nat × Nat) → Bool
  | [], [] => true
  | l :: ls, (ri, pi, g, nu) :: ws =>
      Nat.ble (ri + 1) reps.length && witOk m l (reps.getD ri 0) pi g (Nat.beq nu 1) && zipCheck m reps ls ws
  | _, _ => false

/-- Joint bit-vector of a pair `(chi-mask, eps-mask)`. -/
def joint (p : Nat × Nat) : Nat := p.1 ||| (p.2 <<< 56)

/-- One base: `y` has no bit on the new variables, and all surviving extensions of `y` are covered
by the witnesses. -/
noncomputable def baseOk (n : Nat) (lv : Lv) (y : Nat) (ws : List (Nat × Nat × Nat × Nat)) (next : List Nat) : Bool :=
  Nat.beq (Nat.land y (newMask n)) 0 && zipCheck (n + 1) next (leavesM n lv y) ws

end Results.EightEquidistantLines.Kc
