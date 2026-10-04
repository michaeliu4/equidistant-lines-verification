import Results.EightEquidistantLines.Solution.KComp

/-!
# Bit-level semantics of the packed level data

Characterizations of the bits of `colSpec` (bit-parallel transposition trick), `kpSpec`, `doneAt`
(`assignedMask`, `newMask`) and `red` defined in `KComp`.  Here `codeAt rows s e` is the code of
equation `e` of system `s` (`0` outside the table).

Proof structure (helpers in `Results.EightEquidistantLines.KPack`): each raw recursor of `KComp` is
restated as a recursor with a free starting index (`bitsRec`, `kpRow`, `kpRec`, `packRec`; equal by
`rfl`), whose bits are computed by induction on the list.  For `colSpec`, the masked plane
`(packE rows e >>> v) &&& onesS S` is `bitsum 600 b S = Σ_{s<S} b_s 2^(600 s)`; since
`2^600 ≡ 2 (mod 2^599 - 1)` its residue is `bitsum 1 b S = Σ_{s<S} b_s 2^s < 2^S` (`S ≤ 598`).
-/

namespace Results.EightEquidistantLines.Kc

def codeAt (rows : List (List Nat)) (s e : Nat) : Nat := (rows.getD s []).getD e 0

end Results.EightEquidistantLines.Kc

namespace Results.EightEquidistantLines.KPack

open Kc

/-! ### The raw operations of `KComp` in notation form -/

theorem lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem shiftLeft_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem shiftRight_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

theorem testBit_one_shiftLeft (i k : Nat) : (1 <<< i).testBit k = decide (i = k) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- Decoding of the packed position `e * S + s`. -/
theorem idx_eq_iff {S e e' s s' : Nat} (hs : s < S) (hs' : s' < S) :
    e * S + s = e' * S + s' ↔ e = e' ∧ s = s' := by
  constructor
  · intro h
    have hS : 0 < S := by omega
    have hd : ∀ a b, b < S → (a * S + b) / S = a := fun a b hb => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hb, Nat.zero_add]
    have hm : ∀ a b, b < S → (a * S + b) % S = b := fun a b hb => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    refine ⟨?_, ?_⟩
    · rw [← hd e s hs, ← hd e' s' hs', h]
    · rw [← hm e s hs, ← hm e' s' hs', h]
  · rintro ⟨rfl, rfl⟩; rfl

theorem getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_of_ge {l : List Nat} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem getD_mem {l : List (List Nat)} {i : Nat} (h : i < l.length) : l.getD i [] ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-! ### `red` -/

theorem forall_lt_eight {P : Nat → Prop} :
    (∀ e, e < 8 → P e) ↔ (P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7) := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
      h 5 (by omega), h 6 (by omega), h 7 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ e he
    match e, he with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | _ + 8, h => exact absurd h (by omega)

theorem red_testBit' (S q s : Nat) :
    (red S q).testBit s = true ↔ ∀ e, e < 8 → q.testBit (e * S + s) = true := by
  simp only [red, land_eq, shiftRight_eq, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true,
    forall_lt_eight]
  rw [show 0 * S + s = s by omega, show 1 * S + s = S + s by omega,
    show 3 * S + s = 2 * S + (S + s) by omega, show 5 * S + s = 4 * S + (S + s) by omega,
    show 6 * S + s = 4 * S + (2 * S + s) by omega,
    show 7 * S + s = 4 * S + (2 * S + (S + s)) by omega]
  constructor
  · rintro ⟨⟨⟨h0, h4⟩, h2, h6⟩, ⟨h1, h5⟩, h3, h7⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨⟨h0, h4⟩, h2, h6⟩, ⟨h1, h5⟩, h3, h7⟩

/-! ### Masks -/

theorem testBit_foldl_or (l : List Nat) (m v : Nat) :
    (l.foldl (fun m v => m ||| (1 <<< v)) m).testBit v = (m.testBit v || decide (v ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, testBit_one_shiftLeft]
    by_cases h1 : v = a
    · subst h1; simp
    · have h2 : a ≠ v := fun h => h1 h.symm
      simp [h1, h2]

theorem testBit_assignedMask' (n d v : Nat) :
    (assignedMask n d).testBit v = decide (v ∈ (orderOf n).take d) := by
  unfold assignedMask
  rw [testBit_foldl_or, Nat.zero_testBit, Bool.false_or]

theorem testBit_newMask' (n v : Nat) : (newMask n).testBit v = decide (v ∈ orderOf n) := by
  unfold newMask
  rw [testBit_assignedMask', List.take_length]

/-! ### `doneAt` -/

/-- The recursor shape of `doneAt`: bit `s0 + j` is set iff row `j` satisfies `c`. -/
noncomputable def bitsRec (c : List Nat → Bool) : List (List Nat) → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s => bif c r then Nat.lor (Nat.shiftLeft 1 s) (ih (s + 1)) else ih (s + 1))

theorem bitsRec_low (c : List Nat → Bool) (rows : List (List Nat)) (s0 k : Nat) (hk : k < s0) :
    (bitsRec c rows s0).testBit k = false := by
  induction rows generalizing s0 with
  | nil => exact Nat.zero_testBit k
  | cons r rs ih =>
    show (bif c r then Nat.lor (Nat.shiftLeft 1 s0) (bitsRec c rs (s0 + 1))
      else bitsRec c rs (s0 + 1)).testBit k = false
    cases c r with
    | false => exact ih (s0 + 1) (by omega)
    | true =>
      rw [cond_true, lor_eq, shiftLeft_eq, Nat.testBit_or, testBit_one_shiftLeft,
        ih (s0 + 1) (by omega), Bool.or_false, decide_eq_false_iff_not]
      omega

theorem bitsRec_testBit (c : List Nat → Bool) (rows : List (List Nat)) (s0 j : Nat) :
    (bitsRec c rows s0).testBit (s0 + j) = (decide (j < rows.length) && c (rows.getD j [])) := by
  induction rows generalizing s0 j with
  | nil => show (0 : Nat).testBit _ = _; simp
  | cons r rs ih =>
    show (bif c r then Nat.lor (Nat.shiftLeft 1 s0) (bitsRec c rs (s0 + 1))
      else bitsRec c rs (s0 + 1)).testBit (s0 + j) = _
    cases j with
    | zero =>
      have h0 := bitsRec_low c rs (s0 + 1) (s0 + 0) (by omega)
      cases hc : c r
      · rw [cond_false, h0]; simp [hc]
      · rw [cond_true, lor_eq, shiftLeft_eq, Nat.testBit_or, h0, testBit_one_shiftLeft]; simp [hc]
    | succ j =>
      have h1 : (bitsRec c rs (s0 + 1)).testBit (s0 + (j + 1)) =
          (decide (j < rs.length) && c (rs.getD j [])) := by
        rw [show s0 + (j + 1) = s0 + 1 + j by omega]; exact ih (s0 + 1) j
      have h2 : (1 <<< s0).testBit (s0 + (j + 1)) = false := by
        rw [testBit_one_shiftLeft, decide_eq_false_iff_not]; omega
      have h3 : decide (j + 1 < (r :: rs).length) = decide (j < rs.length) := by
        simp
      cases hc : c r
      · rw [cond_false, h1, h3, List.getD_cons_succ]
      · rw [cond_true, lor_eq, shiftLeft_eq, Nat.testBit_or, h1, h2, Bool.false_or, h3,
          List.getD_cons_succ]

/-- The per-row condition of `doneAt`. -/
def doneCond (n d : Nat) (r : List Nat) : Bool :=
  Nat.beq (Nat.xor (Nat.land (r.foldl (fun acc q => Nat.lor acc q) 0) (newMask n))
    (Nat.land (Nat.land (r.foldl (fun acc q => Nat.lor acc q) 0) (newMask n)) (assignedMask n d))) 0

theorem doneAt_eq (n : Nat) (rows : List (List Nat)) (d : Nat) :
    doneAt n rows d = bitsRec (doneCond n d) rows 0 := rfl

theorem testBit_foldl_lor (r : List Nat) (m v : Nat) :
    (r.foldl (fun acc q => Nat.lor acc q) m).testBit v = true ↔
      (m.testBit v = true ∨ ∃ q ∈ r, q.testBit v = true) := by
  induction r generalizing m with
  | nil => simp
  | cons a r ih =>
    rw [List.foldl_cons, ih, lor_eq, Nat.testBit_or, Bool.or_eq_true]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem doneCond_iff (n d : Nat) (r : List Nat) :
    doneCond n d r = true ↔
      ∀ v, (∃ q ∈ r, q.testBit v = true) → v ∈ orderOf n → v ∈ (orderOf n).take d := by
  unfold doneCond
  rw [Nat.beq_eq]
  constructor
  · intro h v ⟨q, hq, hb⟩ hv
    have h1 := congrArg (fun x => x.testBit v) h
    simp only [xor_eq, land_eq, Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit] at h1
    have hA : (r.foldl (fun acc q => Nat.lor acc q) 0).testBit v = true :=
      (testBit_foldl_lor r 0 v).2 (Or.inr ⟨q, hq, hb⟩)
    have hN : (newMask n).testBit v = true := by rw [testBit_newMask']; exact decide_eq_true hv
    rw [hA, hN] at h1
    have hM : (assignedMask n d).testBit v = true := by
      revert h1; cases (assignedMask n d).testBit v <;> simp
    rw [testBit_assignedMask'] at hM
    exact of_decide_eq_true hM
  · intro h
    apply Nat.eq_of_testBit_eq
    intro v
    simp only [xor_eq, land_eq, Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit]
    cases hA : (r.foldl (fun acc q => Nat.lor acc q) 0).testBit v
    · simp
    · cases hN : (newMask n).testBit v
      · simp
      · have hv : v ∈ orderOf n := by rw [testBit_newMask'] at hN; exact of_decide_eq_true hN
        obtain ⟨q, hq, hb⟩ : ∃ q ∈ r, q.testBit v = true := by
          rcases (testBit_foldl_lor r 0 v).1 hA with h0 | h0
          · simp at h0
          · exact h0
        have hM : (assignedMask n d).testBit v = true := by
          rw [testBit_assignedMask']; exact decide_eq_true (h v ⟨q, hq, hb⟩ hv)
        simp [hM]

/-- Membership in a short row through `getD` indices. -/
theorem exists_mem_iff_getD (r : List Nat) (hr : r.length ≤ 8) (P : Nat → Prop) (hP : ¬ P 0) :
    (∃ q ∈ r, P q) ↔ ∃ e, e < 8 ∧ P (r.getD e 0) := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    exact ⟨i, by omega, by rw [getD_of_lt hi]; exact hpq⟩
  · rintro ⟨e, -, hpe⟩
    by_cases he : e < r.length
    · rw [getD_of_lt he] at hpe
      exact ⟨_, List.getElem_mem he, hpe⟩
    · rw [getD_of_ge (by omega)] at hpe
      exact absurd hpe hP

theorem doneAt_testBit_ge' (n : Nat) (rows : List (List Nat)) (d s : Nat) (hs : rows.length ≤ s) :
    (doneAt n rows d).testBit s = false := by
  have h := bitsRec_testBit (doneCond n d) rows 0 s
  rw [Nat.zero_add] at h
  rw [doneAt_eq, h, decide_eq_false (by omega), Bool.false_and]

/-- Corrected form of `doneAt_testBit`: needs rows of at most eight codes (`doneAt` reads all codes
of a row, the statement only the first eight). -/
theorem doneAt_testBit_of_le (n : Nat) (rows : List (List Nat)) (hlen : ∀ r ∈ rows, r.length ≤ 8)
    (d s : Nat) (hs : s < rows.length) :
    (doneAt n rows d).testBit s = true ↔
      (∀ v, (∃ e, e < 8 ∧ (codeAt rows s e).testBit v = true) → v ∈ orderOf n →
        v ∈ (orderOf n).take d) := by
  have h := bitsRec_testBit (doneCond n d) rows 0 s
  rw [Nat.zero_add] at h
  rw [doneAt_eq, h, decide_eq_true hs, Bool.true_and, doneCond_iff]
  have hr := hlen _ (getD_mem hs)
  constructor
  · intro H v hv
    exact H v ((exists_mem_iff_getD _ hr (fun q => q.testBit v = true) (by simp)).2 hv)
  · intro H v hv
    exact H v ((exists_mem_iff_getD _ hr (fun q => q.testBit v = true) (by simp)).1 hv)

/-- Exact semantics of `doneAt` (no assumption on the row lengths): all codes of the row count. -/
theorem doneAt_testBit_iff (n : Nat) (rows : List (List Nat)) (d s : Nat) (hs : s < rows.length) :
    (doneAt n rows d).testBit s = true ↔
      (∀ v, (∃ q ∈ rows.getD s [], q.testBit v = true) → v ∈ orderOf n →
        v ∈ (orderOf n).take d) := by
  have h := bitsRec_testBit (doneCond n d) rows 0 s
  rw [Nat.zero_add] at h
  rw [doneAt_eq, h, decide_eq_true hs, Bool.true_and, doneCond_iff]

/-- `doneAt_testBit` with the extra hypothesis that every row has exactly eight codes. -/
theorem doneAt_testBit_of_len (n : Nat) (rows : List (List Nat)) (hlen : ∀ r ∈ rows, r.length = 8)
    (d s : Nat) (hs : s < rows.length) :
    (doneAt n rows d).testBit s = true ↔
      (∀ v, (∃ e, e < 8 ∧ (codeAt rows s e).testBit v = true) → v ∈ orderOf n →
        v ∈ (orderOf n).take d) :=
  doneAt_testBit_of_le n rows (fun r hr => Nat.le_of_eq (hlen r hr)) d s hs

/-! ### `kpSpec` -/

/-- Inner recursor of `kpSpec` (row `s`, equations from index `e`). -/
noncomputable def kpRow (S s : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun q _ ih2 e =>
      bif Nat.beq (Nat.land (Nat.shiftRight q 100) 1) 1
      then ih2 (e + 1) else Nat.lor (Nat.shiftLeft 1 (e * S + s)) (ih2 (e + 1)))

/-- Outer recursor of `kpSpec` (rows from index `s`). -/
noncomputable def kpRec (S : Nat) : List (List Nat) → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s => Nat.lor (kpRow S s r 0) (ih (s + 1)))

theorem kpSpec_eq (rows : List (List Nat)) : kpSpec rows = kpRec rows.length rows 0 := rfl

theorem beq_bit100 (q : Nat) : Nat.beq (Nat.land (Nat.shiftRight q 100) 1) 1 = q.testBit 100 := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, land_eq,
    shiftRight_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem kpRow_cons (S s q : Nat) (qs : List Nat) (e : Nat) :
    kpRow S s (q :: qs) e =
      bif q.testBit 100 then kpRow S s qs (e + 1)
      else (1 <<< (e * S + s)) ||| kpRow S s qs (e + 1) := by
  show (bif Nat.beq (Nat.land (Nat.shiftRight q 100) 1) 1 then _ else _) = _
  rw [beq_bit100]; rfl

theorem kpRow_low (S s s' : Nat) (hs : s < S) (hs' : s' < S) (r : List Nat) (e0 e : Nat)
    (h : s' ≠ s ∨ e < e0) : (kpRow S s r e0).testBit (e * S + s') = false := by
  induction r generalizing e0 with
  | nil => exact Nat.zero_testBit _
  | cons q qs ih =>
    rw [kpRow_cons]
    have h1 := ih (e0 + 1) (by omega)
    cases q.testBit 100
    · rw [cond_false, Nat.testBit_or, h1, Bool.or_false, testBit_one_shiftLeft,
        decide_eq_false_iff_not, idx_eq_iff hs hs']
      omega
    · rw [cond_true, h1]

theorem kpRow_main (S s : Nat) (hs : s < S) (r : List Nat) (e0 j : Nat) :
    (kpRow S s r e0).testBit ((e0 + j) * S + s) =
      (decide (j < r.length) && !(r.getD j 0).testBit 100) := by
  induction r generalizing e0 j with
  | nil => show (0 : Nat).testBit _ = _; simp
  | cons q qs ih =>
    rw [kpRow_cons]
    cases j with
    | zero =>
      have h1 := kpRow_low S s s hs hs qs (e0 + 1) (e0 + 0) (Or.inr (by omega))
      cases hq : q.testBit 100
      · rw [cond_false, Nat.testBit_or, h1, Bool.or_false, testBit_one_shiftLeft]; simp [hq]
      · rw [cond_true, h1]; simp [hq]
    | succ j =>
      have h1 : (kpRow S s qs (e0 + 1)).testBit ((e0 + (j + 1)) * S + s) =
          (decide (j < qs.length) && !(qs.getD j 0).testBit 100) := by
        rw [show e0 + (j + 1) = e0 + 1 + j by omega]; exact ih (e0 + 1) j
      have h2 : (1 <<< (e0 * S + s)).testBit ((e0 + (j + 1)) * S + s) = false := by
        rw [testBit_one_shiftLeft, decide_eq_false_iff_not, idx_eq_iff hs hs]; omega
      have h3 : decide (j + 1 < (q :: qs).length) = decide (j < qs.length) := by simp
      cases q.testBit 100
      · rw [cond_false, Nat.testBit_or, h1, h2, Bool.false_or, h3, List.getD_cons_succ]
      · rw [cond_true, h1, h3, List.getD_cons_succ]

/-- Condition for bit `e` of row `r` in `kpSpec`. -/
def kpCond (r : List Nat) (e : Nat) : Bool := decide (e < r.length) && !(r.getD e 0).testBit 100

theorem kpRec_low (S : Nat) (rows : List (List Nat)) (s0 s' e : Nat) (hS : s0 + rows.length ≤ S)
    (hs' : s' < S) (h : s' < s0) : (kpRec S rows s0).testBit (e * S + s') = false := by
  induction rows generalizing s0 with
  | nil => exact Nat.zero_testBit _
  | cons r rs ih =>
    show (Nat.lor (kpRow S s0 r 0) (kpRec S rs (s0 + 1))).testBit (e * S + s') = false
    have hs0 : s0 < S := by simp at hS; omega
    rw [lor_eq, Nat.testBit_or, kpRow_low S s0 s' hs0 hs' r 0 e (Or.inl (by omega)),
      ih (s0 + 1) (by simp at hS; omega) (by omega)]
    rfl

theorem kpRec_main (S : Nat) (rows : List (List Nat)) (s0 j e : Nat) (hS : s0 + rows.length ≤ S)
    (hj : j < rows.length) :
    (kpRec S rows s0).testBit (e * S + (s0 + j)) = kpCond (rows.getD j []) e := by
  induction rows generalizing s0 j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons r rs ih =>
    show (Nat.lor (kpRow S s0 r 0) (kpRec S rs (s0 + 1))).testBit (e * S + (s0 + j)) = _
    have hs0 : s0 < S := by simp at hS; omega
    rw [lor_eq, Nat.testBit_or]
    cases j with
    | zero =>
      have h1 := kpRow_main S s0 hs0 r 0 e
      rw [Nat.zero_add] at h1
      rw [Nat.add_zero, h1, kpRec_low S rs (s0 + 1) s0 e (by simp at hS; omega) hs0 (by omega),
        Bool.or_false, List.getD_cons_zero]
      rfl
    | succ j =>
      have hj' : j < rs.length := by simp at hj; omega
      have h1 := ih (s0 + 1) j (by simp at hS; omega) hj'
      rw [show s0 + 1 + j = s0 + (j + 1) by omega] at h1
      rw [kpRow_low S s0 (s0 + (j + 1)) hs0 (by simp at hS; omega) r 0 e (Or.inl (by omega)),
        Bool.false_or, h1, List.getD_cons_succ]

/-- Corrected form of `kpSpec_testBit`: needs rows of at least eight codes (`kpSpec` sets no bit
for a missing code, while `codeAt` reads it as `0`). -/
theorem kpSpec_testBit_of_ge (rows : List (List Nat)) (hlen : ∀ r ∈ rows, 8 ≤ r.length)
    (e s : Nat) (he : e < 8) (hs : s < rows.length) :
    (kpSpec rows).testBit (e * rows.length + s) = !(codeAt rows s e).testBit 100 := by
  have h := kpRec_main rows.length rows 0 s e (by omega) hs
  rw [Nat.zero_add] at h
  rw [kpSpec_eq, h]
  have hr := hlen _ (getD_mem hs)
  unfold kpCond codeAt
  rw [decide_eq_true (by omega), Bool.true_and]

/-- Exact semantics of `kpSpec` (no assumption on the row lengths). -/
theorem kpSpec_testBit_eq (rows : List (List Nat)) (e s : Nat) (hs : s < rows.length) :
    (kpSpec rows).testBit (e * rows.length + s) =
      (decide (e < (rows.getD s []).length) && !(codeAt rows s e).testBit 100) := by
  have h := kpRec_main rows.length rows 0 s e (by omega) hs
  rw [Nat.zero_add] at h
  rw [kpSpec_eq, h]
  rfl

/-- `kpSpec_testBit` with the extra hypothesis that every row has exactly eight codes. -/
theorem kpSpec_testBit_of_len (rows : List (List Nat)) (hlen : ∀ r ∈ rows, r.length = 8)
    (e s : Nat) (he : e < 8) (hs : s < rows.length) :
    (kpSpec rows).testBit (e * rows.length + s) = !(codeAt rows s e).testBit 100 :=
  kpSpec_testBit_of_ge rows (fun r hr => Nat.le_of_eq (hlen r hr).symm) e s he hs

/-! ### `colSpec`: the transposition trick -/

theorem SIG_eq : SIG = 600 := rfl

/-- Recursor shape of `packE` (rows from index `s`). -/
noncomputable def packRec (e : Nat) : List (List Nat) → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun r _ ih s => Nat.lor (Nat.shiftLeft (r.getD e 0) (SIG * s)) (ih (s + 1)))

theorem packE_eq (rows : List (List Nat)) (e : Nat) : packE rows e = packRec e rows 0 := rfl

theorem getD_lt_of_codes {r : List Nat} (h : ∀ q ∈ r, q < 2 ^ 101) (e : Nat) :
    r.getD e 0 < 2 ^ 101 := by
  rw [List.getD_eq_getElem?_getD]
  cases hq : r[e]? with
  | none => exact Nat.two_pow_pos _
  | some q => exact h q (List.mem_of_getElem? hq)

/-- Bit `600 s + v` (`v < 600`) of the stride-`600` packing is bit `v` of block `s`. -/
theorem packRec_testBit (e : Nat) (rows : List (List Nat))
    (hcodes : ∀ r ∈ rows, ∀ q ∈ r, q < 2 ^ 101) (s0 s v : Nat) (hv : v < 600) :
    (packRec e rows s0).testBit (600 * s + v) =
      (decide (s0 ≤ s) && ((rows.getD (s - s0) []).getD e 0).testBit v) := by
  induction rows generalizing s0 with
  | nil => show (0 : Nat).testBit _ = _; simp
  | cons r rs ih =>
    show (Nat.lor (Nat.shiftLeft (r.getD e 0) (SIG * s0)) (packRec e rs (s0 + 1))).testBit
      (600 * s + v) = _
    rw [lor_eq, shiftLeft_eq, SIG_eq, Nat.testBit_or, Nat.testBit_shiftLeft,
      ih (fun r' hr' => hcodes r' (List.mem_cons_of_mem _ hr')) (s0 + 1)]
    have hr : r.getD e 0 < 2 ^ 101 := getD_lt_of_codes (hcodes r List.mem_cons_self) e
    rcases Nat.lt_trichotomy s s0 with h | rfl | h
    · have h1 : decide (600 * s + v ≥ 600 * s0) = false := decide_eq_false (by omega)
      have h2 : decide (s0 + 1 ≤ s) = false := decide_eq_false (by omega)
      have h3 : decide (s0 ≤ s) = false := decide_eq_false (by omega)
      rw [h1, h2, h3]; rfl
    · have h1 : decide (600 * s + v ≥ 600 * s) = true := decide_eq_true (by omega)
      have h2 : decide (s + 1 ≤ s) = false := decide_eq_false (by omega)
      have h3 : decide (s ≤ s) = true := decide_eq_true (by omega)
      rw [h1, h2, h3, Nat.sub_self, List.getD_cons_zero, show 600 * s + v - 600 * s = v by omega]
      simp
    · have h1 : (r.getD e 0).testBit (600 * s + v - 600 * s0) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : decide (s0 + 1 ≤ s) = true := decide_eq_true (by omega)
      have h3 : decide (s0 ≤ s) = true := decide_eq_true (by omega)
      rw [h1, h2, h3, Bool.and_false, Bool.false_or, Bool.true_and, Bool.true_and,
        show s - s0 = (s - (s0 + 1)) + 1 by omega, List.getD_cons_succ]

theorem onesS_testBit (S k : Nat) : (onesS S).testBit k = decide (k % 600 = 0 ∧ k / 600 < S) := by
  induction S with
  | zero => show (0 : Nat).testBit k = _; simp
  | succ S ih =>
    show (Nat.lor (onesS S) (Nat.shiftLeft 1 (SIG * S))).testBit k = _
    rw [lor_eq, shiftLeft_eq, SIG_eq, Nat.testBit_or, ih, testBit_one_shiftLeft, Bool.eq_iff_iff,
      Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega

/-- `Σ_{s < S} b_s 2^(c s)`. -/
def bitsum (c : Nat) (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | S + 1 => bitsum c b S + (b S).toNat * 2 ^ (c * S)

theorem bitsum_succ (c : Nat) (b : Nat → Bool) (S : Nat) :
    bitsum c b (S + 1) = bitsum c b S + (b S).toNat * 2 ^ (c * S) := rfl

theorem bitsum_lt (c : Nat) (hc : 0 < c) (b : Nat → Bool) (S : Nat) :
    bitsum c b S < 2 ^ (c * S) := by
  induction S with
  | zero => exact Nat.two_pow_pos _
  | succ S ih =>
    rw [bitsum_succ]
    have h1 : (b S).toNat * 2 ^ (c * S) ≤ 2 ^ (c * S) := by
      have := Nat.mul_le_mul_right (2 ^ (c * S)) (Bool.toNat_le (b S))
      rwa [Nat.one_mul] at this
    have h2 : 2 ^ (c * S) * 2 ≤ 2 ^ (c * (S + 1)) := by
      rw [← Nat.pow_succ]; apply Nat.pow_le_pow_right (by omega); rw [Nat.mul_succ]; omega
    omega

theorem bitsum_testBit (c : Nat) (hc : 0 < c) (b : Nat → Bool) (S s j : Nat) (hj : j < c) :
    (bitsum c b S).testBit (c * s + j) = (decide (j = 0) && decide (s < S) && b s) := by
  induction S with
  | zero => show (0 : Nat).testBit _ = _; simp
  | succ S ih =>
    rw [bitsum_succ, Nat.add_comm (bitsum c b S), Nat.mul_comm (b S).toNat,
      Nat.testBit_two_pow_mul_add _ (bitsum_lt c hc b S)]
    by_cases h : c * s + j < c * S
    · rw [if_pos h, ih]
      have hs : s < S := by
        rcases Nat.lt_or_ge s S with h' | h'
        · exact h'
        · exfalso; have := Nat.mul_le_mul_left c h'; omega
      rw [decide_eq_true hs, decide_eq_true (by omega : s < S + 1)]
    · rw [if_neg h, Nat.testBit_bool_toNat]
      have hs : S ≤ s := by
        rcases Nat.lt_or_ge s S with h' | h'
        · exfalso
          have := Nat.mul_le_mul_left c (show s + 1 ≤ S from h')
          rw [Nat.mul_succ] at this; omega
        · exact h'
      rcases Nat.lt_or_ge S s with h2 | h2
      · have := Nat.mul_le_mul_left c (show S + 1 ≤ s from h2)
        rw [Nat.mul_succ] at this
        rw [decide_eq_false (by omega : ¬ c * s + j - c * S = 0),
          decide_eq_false (by omega : ¬ s < S + 1)]
        simp
      · have hsS : s = S := by omega
        subst hsS
        rw [show c * s + j - c * s = j by omega, decide_eq_true (by omega : s < s + 1),
          Bool.and_true]

theorem two_pow_mod (c : Nat) : 2 ^ (c + 1) % (2 ^ c - 1) = 2 % (2 ^ c - 1) := by
  have h1 : 0 < 2 ^ c := Nat.two_pow_pos c
  rw [Nat.pow_succ]
  generalize 2 ^ c = P at h1 ⊢
  rw [show P * 2 = (P - 1) * 2 + 2 by omega, Nat.mul_add_mod]

theorem two_pow_pred_lt (c : Nat) (hc : 2 ≤ c) : 2 ^ (c - 1) < 2 ^ c - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.add_sub_cancel, Nat.pow_succ]
  generalize 2 ^ k = P at h2 ⊢
  rw [Nat.pow_one] at h2
  omega

theorem pow_mod_M (M : Nat) (hM : 2 ^ 600 % M = 2 % M) (s : Nat) :
    2 ^ (600 * s) % M = 2 ^ s % M := by
  rw [Nat.pow_mul, Nat.pow_mod, hM, ← Nat.pow_mod]

/-- If `2^600 ≡ 2 (mod M)` then `2^(600 s) ≡ 2^s`, so the stride-`600` sum reduces to the
stride-`1` sum. -/
theorem bitsum_mod (M : Nat) (hM : 2 ^ 600 % M = 2 % M) (b : Nat → Bool) (S : Nat) :
    bitsum 600 b S % M = bitsum 1 b S % M := by
  induction S with
  | zero => rfl
  | succ S ih =>
    rw [bitsum_succ, bitsum_succ, Nat.add_mod, ih, Nat.mul_mod, pow_mod_M M hM, Nat.one_mul,
      ← Nat.mul_mod, ← Nat.add_mod]

/-- The plane `e` of `colSpec` for a modulus `M` with `2^600 ≡ 2` and `2^S ≤ M`: the bits `v` of the
codes of plane `e`, at positions `s < S`. -/
theorem plane_eq (rows : List (List Nat)) (hcodes : ∀ r ∈ rows, ∀ q ∈ r, q < 2 ^ 101) (v : Nat)
    (hv : v < 84) (e M : Nat) (hM : 2 ^ 600 % M = 2 % M) (hlt : 2 ^ rows.length ≤ M) :
    Nat.mod (Nat.land (Nat.shiftRight (packE rows e) v) (onesS rows.length)) M =
      bitsum 1 (fun s => (codeAt rows s e).testBit v) rows.length := by
  have hT : (packE rows e >>> v) &&& onesS rows.length =
      bitsum 600 (fun s => (codeAt rows s e).testBit v) rows.length := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_shiftRight, onesS_testBit, ← Nat.div_add_mod k 600,
      bitsum_testBit 600 (by omega) _ _ _ _ (Nat.mod_lt _ (by omega)), Nat.mul_add_div (by omega),
      Nat.mul_add_mod, Nat.mod_mod, Nat.div_eq_of_lt (Nat.mod_lt _ (by omega)), Nat.add_zero]
    by_cases hk : k % 600 = 0
    · rw [hk, Nat.add_zero, Nat.add_comm, packE_eq, packRec_testBit e rows hcodes 0 _ v (by omega),
        Nat.sub_zero]
      unfold codeAt
      cases ((rows.getD (k / 600) []).getD e 0).testBit v <;> simp
    · rw [decide_eq_false (by omega : ¬ (k % 600 = 0 ∧ k / 600 < rows.length)),
        decide_eq_false hk]
      simp
  have h1 := bitsum_lt 1 (by omega) (fun s => (codeAt rows s e).testBit v) rows.length
  rw [Nat.one_mul] at h1
  rw [mod_eq, land_eq, shiftRight_eq, hT, bitsum_mod M hM, Nat.mod_eq_of_lt (by omega)]

/-- OR-accumulation of planes `f e` at offsets `e * S` (each plane `< 2^S`). -/
theorem orAcc_testBit (S : Nat) (f : Nat → Nat) (hf : ∀ e j, S ≤ j → (f e).testBit j = false)
    (e s : Nat) (hs : s < S) (E : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0 (fun e ih => Nat.lor ih (Nat.shiftLeft (f e) (e * S))) E :
      Nat).testBit (e * S + s) = (decide (e < E) && (f e).testBit s) := by
  induction E with
  | zero => show (0 : Nat).testBit _ = _; simp
  | succ E ih =>
    show (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun e ih => Nat.lor ih (Nat.shiftLeft (f e) (e * S))) E)
        (Nat.shiftLeft (f E) (E * S))).testBit (e * S + s) = _
    rw [lor_eq, shiftLeft_eq, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy e E with h | rfl | h
    · have h1 := Nat.mul_le_mul_right S (show e + 1 ≤ E from h)
      rw [Nat.succ_mul] at h1
      rw [decide_eq_true h, decide_eq_false (by omega : ¬ (e * S + s ≥ E * S)),
        decide_eq_true (by omega : e < E + 1)]
      simp
    · rw [decide_eq_false (Nat.lt_irrefl e), decide_eq_true (by omega : e * S + s ≥ e * S),
        decide_eq_true (by omega : e < e + 1), show e * S + s - e * S = s by omega]
      simp
    · have h1 := Nat.mul_le_mul_right S (show E + 1 ≤ e from h)
      rw [Nat.succ_mul] at h1
      rw [decide_eq_false (by omega : ¬ e < E), decide_eq_false (by omega : ¬ e < E + 1),
        hf E (e * S + s - E * S) (by omega)]
      simp

theorem colSpec_testBit' (rows : List (List Nat)) (hS : rows.length ≤ 598)
    (hcodes : ∀ r ∈ rows, ∀ q ∈ r, q < 2 ^ 101) (v : Nat) (hv : v < 84) (e s : Nat) (he : e < 8)
    (hs : s < rows.length) :
    (colSpec rows v).testBit (e * rows.length + s) = (codeAt rows s e).testBit v := by
  have hM : 2 ^ 600 % (2 ^ (SIG - 1) - 1) = 2 % (2 ^ (SIG - 1) - 1) := by
    have h := two_pow_mod (SIG - 1)
    rw [show SIG - 1 + 1 = 600 from rfl] at h
    exact h
  have hlt : 2 ^ rows.length ≤ 2 ^ (SIG - 1) - 1 := by
    have hSIG : SIG = 600 := rfl
    have h1 : 2 ^ rows.length ≤ 2 ^ (SIG - 1 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt h1 (two_pow_pred_lt (SIG - 1) (by omega)))
  have hplane : ∀ e', Nat.mod (Nat.land (Nat.shiftRight (packE rows e') v) (onesS rows.length))
      (2 ^ (SIG - 1) - 1) = bitsum 1 (fun s => (codeAt rows s e').testBit v) rows.length :=
    fun e' => plane_eq rows hcodes v hv e' _ hM hlt
  have hf : ∀ e' j, rows.length ≤ j →
      (Nat.mod (Nat.land (Nat.shiftRight (packE rows e') v) (onesS rows.length))
        (2 ^ (SIG - 1) - 1)).testBit j = false := by
    intro e' j hj
    rw [hplane e']
    apply Nat.testBit_lt_two_pow
    have h1 := bitsum_lt 1 (by omega) (fun s => (codeAt rows s e').testBit v) rows.length
    have h2 : 2 ^ (1 * rows.length) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  unfold colSpec
  dsimp only
  rw [orAcc_testBit rows.length (fun e' => Nat.mod (Nat.land (Nat.shiftRight (packE rows e') v)
    (onesS rows.length)) (2 ^ (SIG - 1) - 1)) hf e s hs 8, hplane e, decide_eq_true he,
    Bool.true_and]
  have h := bitsum_testBit 1 (by omega) (fun s => (codeAt rows s e).testBit v) rows.length s 0
    (by omega)
  rw [Nat.one_mul, Nat.add_zero] at h
  rw [h, decide_eq_true hs]
  rfl

end Results.EightEquidistantLines.KPack

namespace Results.EightEquidistantLines.Kc

/-- Bit `e * S + s` of the packed column of variable `v` is bit `v` of the code of equation `e` of
system `s` (`S = rows.length ≤ 598`, codes `< 2^101`, `v < 84`, `e < 8`, `s < S`). -/
theorem colSpec_testBit (rows : List (List Nat)) (hS : rows.length ≤ 598)
    (hcodes : ∀ r ∈ rows, ∀ q ∈ r, q < 2 ^ 101) (v : Nat) (hv : v < 84) (e s : Nat) (he : e < 8)
    (hs : s < rows.length) :
    (colSpec rows v).testBit (e * rows.length + s) = (codeAt rows s e).testBit v :=
  KPack.colSpec_testBit' rows hS hcodes v hv e s he hs

/-- Bit `e * S + s` of `kpSpec` says that the constant bit of the code is clear.  (The hypothesis that
every row has exactly eight codes is needed: `kpSpec` sets no bit for a missing code, while `codeAt`
reads it as `0`.) -/
theorem kpSpec_testBit (rows : List (List Nat)) (hlen : ∀ r ∈ rows, r.length = 8)
    (e s : Nat) (he : e < 8) (hs : s < rows.length) :
    (kpSpec rows).testBit (e * rows.length + s) = !(codeAt rows s e).testBit 100 :=
  KPack.kpSpec_testBit_of_len rows hlen e s he hs

theorem testBit_assignedMask (n d v : Nat) :
    (assignedMask n d).testBit v = decide (v ∈ (orderOf n).take d) :=
  KPack.testBit_assignedMask' n d v

theorem testBit_newMask (n v : Nat) : (newMask n).testBit v = decide (v ∈ orderOf n) :=
  KPack.testBit_newMask' n v

/-- `doneAt n rows d` has bit `s < S` iff every variable occurring in a code of system `s` that is
a new variable is among the first `d` new variables; it has no bits at positions `≥ S`.  (The hypothesis
that every row has exactly eight codes is needed: `doneAt` reads all codes of the row, the right side
only the first eight.) -/
theorem doneAt_testBit (n : Nat) (rows : List (List Nat)) (hlen : ∀ r ∈ rows, r.length = 8)
    (d s : Nat) (hs : s < rows.length) :
    (doneAt n rows d).testBit s = true ↔
      (∀ v, (∃ e, e < 8 ∧ (codeAt rows s e).testBit v = true) → v ∈ orderOf n →
        v ∈ (orderOf n).take d) :=
  KPack.doneAt_testBit_of_len n rows hlen d s hs

theorem doneAt_testBit_ge (n : Nat) (rows : List (List Nat)) (d s : Nat) (hs : rows.length ≤ s) :
    (doneAt n rows d).testBit s = false :=
  KPack.doneAt_testBit_ge' n rows d s hs

/-- Bit `s < S` of `red S q` is the conjunction of the bits `e * S + s`, `e < 8`, of `q`. -/
theorem red_testBit (S q s : Nat) (hs : s < S) :
    (red S q).testBit s = true ↔ ∀ e, e < 8 → q.testBit (e * S + s) = true :=
  (fun (_ : s < S) => KPack.red_testBit' S q s) hs

end Results.EightEquidistantLines.Kc
