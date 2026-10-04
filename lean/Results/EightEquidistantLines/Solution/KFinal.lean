import Mathlib.Tactic.IntervalCases
import Results.EightEquidistantLines.Solution.KChain
import Results.EightEquidistantLines.Solution.KSel
import Results.EightEquidistantLines.Solution.KCheck.Levels
import Results.EightEquidistantLines.Solution.KCheck.Base1
import Results.EightEquidistantLines.Solution.KCheck.Base2
import Results.EightEquidistantLines.Solution.KCheck.Base3
import Results.EightEquidistantLines.Solution.KCheck.Base4
import Results.EightEquidistantLines.Solution.KCheck.Base5
import Results.EightEquidistantLines.Solution.KCheck.Base6a
import Results.EightEquidistantLines.Solution.KCheck.Base6b
import Results.EightEquidistantLines.Solution.KCheck.Base7

/-!
# The finite part, assembled

The generated certificate facts (`KCheck/*`) discharge `Kc.ChainOk` for the generated data; `Kc.no_valid8`
(`KChain`) then shows that no sign data satisfies all local constraints.
-/

namespace Results.EightEquidistantLines.Kfinal

open Kc Ksel Kcheck

theorem bases_1 : ∀ i, i < (repsOf 1).length →
    baseOk 1 (lvOf 1) (joint ((repsOf 1).getD i (0, 0))) ((witsOf 2).getD i []) ((repsOf 2).map joint) = true := by
  intro i hi
  have hlen : (repsOf 1).length = 1 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_1_0]

theorem level_1 : (lvOf 1).Valid 1 (instsOf 1) :=
  ⟨rows_1, cols_1, kp_1, done_1, len_1, List.all_eq_true.mp wf_1⟩

theorem bases_2 : ∀ i, i < (repsOf 2).length →
    baseOk 2 (lvOf 2) (joint ((repsOf 2).getD i (0, 0))) ((witsOf 3).getD i []) ((repsOf 3).map joint) = true := by
  intro i hi
  have hlen : (repsOf 2).length = 1 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_2_0]

theorem level_2 : (lvOf 2).Valid 2 (instsOf 2) :=
  ⟨rows_2, cols_2, kp_2, done_2, len_2, List.all_eq_true.mp wf_2⟩

theorem bases_3 : ∀ i, i < (repsOf 3).length →
    baseOk 3 (lvOf 3) (joint ((repsOf 3).getD i (0, 0))) ((witsOf 4).getD i []) ((repsOf 4).map joint) = true := by
  intro i hi
  have hlen : (repsOf 3).length = 1 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_3_0]

theorem level_3 : (lvOf 3).Valid 3 (instsOf 3) :=
  ⟨rows_3, cols_3, kp_3, done_3, len_3, List.all_eq_true.mp wf_3⟩

theorem bases_4 : ∀ i, i < (repsOf 4).length →
    baseOk 4 (lvOf 4) (joint ((repsOf 4).getD i (0, 0))) ((witsOf 5).getD i []) ((repsOf 5).map joint) = true := by
  intro i hi
  have hlen : (repsOf 4).length = 3 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_4_0, base_4_1, base_4_2]

theorem level_4 : (lvOf 4).Valid 4 (instsOf 4) :=
  ⟨rows_4, cols_4, kp_4, done_4, len_4, List.all_eq_true.mp wf_4⟩

theorem bases_5 : ∀ i, i < (repsOf 5).length →
    baseOk 5 (lvOf 5) (joint ((repsOf 5).getD i (0, 0))) ((witsOf 6).getD i []) ((repsOf 6).map joint) = true := by
  intro i hi
  have hlen : (repsOf 5).length = 9 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_5_0, base_5_1, base_5_2, base_5_3, base_5_4, base_5_5, base_5_6, base_5_7, base_5_8]

theorem level_5 : (lvOf 5).Valid 5 (instsOf 5) :=
  ⟨rows_5, cols_5, kp_5, done_5, len_5, List.all_eq_true.mp wf_5⟩

theorem bases_6 : ∀ i, i < (repsOf 6).length →
    baseOk 6 (lvOf 6) (joint ((repsOf 6).getD i (0, 0))) ((witsOf 7).getD i []) ((repsOf 7).map joint) = true := by
  intro i hi
  have hlen : (repsOf 6).length = 36 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_6_0, base_6_1, base_6_2, base_6_3, base_6_4, base_6_5, base_6_6, base_6_7, base_6_8, base_6_9, base_6_10, base_6_11, base_6_12, base_6_13, base_6_14, base_6_15, base_6_16, base_6_17, base_6_18, base_6_19, base_6_20, base_6_21, base_6_22, base_6_23, base_6_24, base_6_25, base_6_26, base_6_27, base_6_28, base_6_29, base_6_30, base_6_31, base_6_32, base_6_33, base_6_34, base_6_35]

theorem level_6 : (lvOf 6).Valid 6 (instsOf 6) :=
  ⟨rows_6, cols_6, kp_6, done_6, len_6, List.all_eq_true.mp wf_6⟩

theorem bases_7 : ∀ i, i < (repsOf 7).length →
    baseOk 7 (lvOf 7) (joint ((repsOf 7).getD i (0, 0))) ((witsOf 8).getD i []) ((repsOf 8).map joint) = true := by
  intro i hi
  have hlen : (repsOf 7).length = 16 := by decide
  rw [hlen] at hi
  interval_cases i
  exacts [base_7_0, base_7_1, base_7_2, base_7_3, base_7_4, base_7_5, base_7_6, base_7_7, base_7_8, base_7_9, base_7_10, base_7_11, base_7_12, base_7_13, base_7_14, base_7_15]

theorem level_7 : (lvOf 7).Valid 7 (instsOf 7) :=
  ⟨rows_7, cols_7, kp_7, done_7, len_7, List.all_eq_true.mp wf_7⟩

theorem chainOk : Kc.ChainOk repsOf witsOf instsOf lvOf := by
  refine ⟨rfl, rfl, ?_⟩
  intro n h1 h7
  interval_cases n
  · exact ⟨level_1, bases_1⟩
  · exact ⟨level_2, bases_2⟩
  · exact ⟨level_3, bases_3⟩
  · exact ⟨level_4, bases_4⟩
  · exact ⟨level_5, bases_5⟩
  · exact ⟨level_6, bases_6⟩
  · exact ⟨level_7, bases_7⟩

theorem no_valid8 (D : SD) : ¬ D.Valid8 := Kc.no_valid8 repsOf witsOf instsOf lvOf chainOk D

end Results.EightEquidistantLines.Kfinal
