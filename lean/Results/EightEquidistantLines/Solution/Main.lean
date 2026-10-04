import Results.EightEquidistantLines.Solution.Bridge
import Results.EightEquidistantLines.Solution.Scaling
import Results.EightEquidistantLines.Solution.Plucker
import Results.EightEquidistantLines.Solution.Circuit
import Results.EightEquidistantLines.Solution.Chart
import Results.EightEquidistantLines.Solution.KFinal

/-!
# Eight lines in ℝ³: proof of Theorem 1.1 and of the upper half of Corollary 1.2
-/

namespace Results.EightEquidistantLines

theorem thm_1_1 :
    ¬ ∃ L : Fin 8 → AffineSubspace ℝ E3,
      (∀ i, IsAffineLine (L i)) ∧ ∀ i j, i < j → setDist (L i) (L j) = 1 := by
  rintro ⟨L, hL, hd⟩
  obtain ⟨F⟩ := exists_ufam L hL hd
  exact Kfinal.no_valid8 F.sd ⟨F.sd_wf, F.sd_gp, F.sd_circ, F.sd_forb⟩

theorem cor_1_2_upper (n : ℕ) (hn : 8 ≤ n) (d : ℝ) (hd : 0 < d) :
    ¬ ∃ L : Fin n → AffineSubspace ℝ E3,
      (∀ i, IsAffineLine (L i)) ∧ ∀ i j, i < j → setDist (L i) (L j) = d := by
  rintro ⟨L, hL, hdist⟩
  obtain ⟨L', hL', hdist'⟩ := scale_lines n hn d hd L hL hdist
  exact thm_1_1 ⟨L', hL', hdist'⟩

end Results.EightEquidistantLines
