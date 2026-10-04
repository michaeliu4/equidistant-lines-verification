import Results.EightEquidistantLines.Solution.KDfs
import Results.EightEquidistantLines.Solution.KWit

/-!
# The finite part: no valid sign data on eight labels

`Kc.ChainOk` collects the kernel-checked facts about the generated certificate data (orbit
representatives `reps n` on `n` labels, symmetry witnesses `wits (n+1)`, instance lists `insts n`
and level data `lv n`).  `Kc.no_valid8` proves, by induction over the number of labels, that no sign
datum satisfies all local constraints.
-/

namespace Results.EightEquidistantLines

open Kc

/-- The certificate checks for the extension from `n` to `n + 1` labels, `1 ≤ n ≤ 7`. -/
def Kc.ChainOk (reps : Nat → List (Nat × Nat)) (wits : Nat → List (List (Nat × Nat × Nat × Nat)))
    (insts : Nat → List Kc.Inst) (lv : Nat → Kc.Lv) : Prop :=
  reps 1 = [(0, 0)] ∧ reps 8 = [] ∧
  ∀ n, 1 ≤ n → n ≤ 7 →
    (lv n).Valid n (insts n) ∧
    ∀ i, i < (reps n).length →
      Kc.baseOk n (lv n) (Kc.joint ((reps n).getD i (0, 0))) ((wits (n + 1)).getD i [])
        ((reps (n + 1)).map Kc.joint) = true

namespace KChain

/-- Covering statement at level `n`: every valid sign datum has a valid symmetric image that is
represented, on the labels `< n`, by one of the `n`-label orbit representatives. -/
def Cover (reps : Nat → List (Nat × Nat)) (n : Nat) : Prop :=
  ∀ D : SD, D.Valid8 → ∃ D' : SD, D'.Valid8 ∧ ∃ i, i < (reps n).length ∧
    AgreeJ n D' (Kc.joint ((reps n).getD i (0, 0)))

/-- On one label there is nothing to agree on. -/
theorem agreeJ_one (D : SD) (x : Nat) : AgreeJ 1 D x := by
  refine ⟨fun a b c hab hbc hc => ?_, fun a b hab hb => ?_⟩
  · have h1 : a.val < b.val := hab
    have h2 : b.val < c.val := hbc
    exfalso
    omega
  · have h1 : a.val < b.val := hab
    exfalso
    omega

/-- Indexing a mapped list of representatives at a valid index. -/
theorem getD_map_joint (l : List (Nat × Nat)) (i : Nat) (hi : i < l.length) :
    (l.map Kc.joint).getD i 0 = Kc.joint (l.getD i (0, 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

/-- The induction step `n → n + 1`, `1 ≤ n ≤ 7`: extend a representative by the depth-first search
(`Kc.leaves_complete`), then map the surviving extension to a representative of level `n + 1` by
its witness (`Kc.zipCheck_sound`). -/
theorem cover_step (reps : Nat → List (Nat × Nat))
    (wits : Nat → List (List (Nat × Nat × Nat × Nat))) (insts : Nat → List Kc.Inst)
    (lv : Nat → Kc.Lv) (h : Kc.ChainOk reps wits insts lv) (n : Nat) (hn1 : 1 ≤ n) (hn7 : n ≤ 7)
    (hc : Cover reps n) : Cover reps (n + 1) := by
  intro D hD
  obtain ⟨D', hD', i, hi, hag⟩ := hc D hD
  obtain ⟨hlv, hbase⟩ := h.2.2 n hn1 hn7
  have hb := hbase i hi
  unfold Kc.baseOk at hb
  rw [Bool.and_eq_true] at hb
  obtain ⟨hy0b, hzip⟩ := hb
  have hy0 : Nat.land (Kc.joint ((reps n).getD i (0, 0))) (Kc.newMask n) = 0 :=
    Nat.eq_of_beq_eq_true hy0b
  obtain ⟨x, hxmem, hx⟩ := Kc.leaves_complete n hn7 (insts n) (lv n) hlv D' hD' _ hag hy0
  obtain ⟨w, ri, hri, hagr⟩ :=
    Kc.zipCheck_sound (n + 1) (by omega) _ _ _ hzip D' hD'.1 x hxmem hx
  rw [List.length_map] at hri
  refine ⟨D'.act w, SD.Valid8.act w hD', ri, hri, ?_⟩
  rwa [getD_map_joint _ ri hri] at hagr

end KChain

theorem Kc.no_valid8 (reps : Nat → List (Nat × Nat)) (wits : Nat → List (List (Nat × Nat × Nat × Nat)))
    (insts : Nat → List Kc.Inst) (lv : Nat → Kc.Lv) (h : Kc.ChainOk reps wits insts lv) (D : SD) :
    ¬ D.Valid8 := by
  intro hD
  have hall : ∀ k, k ≤ 7 → KChain.Cover reps (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro _ D hD
      have h1 : reps 1 = [(0, 0)] := h.1
      exact ⟨D, hD, 0, by simp [h1], KChain.agreeJ_one D _⟩
    | succ k ih =>
      intro hk
      exact KChain.cover_step reps wits insts lv h (k + 1) (by omega) hk (ih (by omega))
  obtain ⟨D', -, i, hi, -⟩ := hall 7 (by omega) D hD
  have h8 : reps (7 + 1) = [] := h.2.1
  rw [h8] at hi
  exact absurd hi (by simp)

end Results.EightEquidistantLines
