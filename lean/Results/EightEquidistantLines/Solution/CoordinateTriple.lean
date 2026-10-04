import Results.EightEquidistantLines.Solution.Family

/-!
# The coplanar coordinate triple obstruction

Three pairwise nonparallel members of a unit-distance family cannot have coplanar
directions.  The proof uses a common normal to turn the three line distances into
three pairwise differences of real coordinates.
-/

namespace Results.EightEquidistantLines

open V3

namespace CoordinateTriple

/-- Squaring the skew-line distance formula at distance one removes its square root. -/
theorem det_sq_eq_norm2_cross (F : UFam) {i j : Fin 8} (hij : i ≠ j)
    (hcross : cross (F.u i) (F.u j) ≠ 0) :
    det (F.p i - F.p j) (F.u i) (F.u j) ^ 2 =
      norm2 (cross (F.u i) (F.u j)) := by
  have hN : 0 < norm2 (cross (F.u i) (F.u j)) :=
    lt_of_le_of_ne (norm2_nonneg _) (fun h0 => hcross ((norm2_eq_zero_iff _).1 h0.symm))
  have hR : 0 < Real.sqrt (norm2 (cross (F.u i) (F.u j))) := Real.sqrt_pos.2 hN
  have hd := F.dist1 i j hij
  rw [lineDist3_skew _ _ _ _ hcross] at hd
  have habs : |det (F.p i - F.p j) (F.u i) (F.u j)| =
      Real.sqrt (norm2 (cross (F.u i) (F.u j))) := by
    exact (div_eq_one_iff_eq hR.ne').mp hd
  calc
    det (F.p i - F.p j) (F.u i) (F.u j) ^ 2 =
        |det (F.p i - F.p j) (F.u i) (F.u j)| ^ 2 := by rw [sq_abs]
    _ = Real.sqrt (norm2 (cross (F.u i) (F.u j))) ^ 2 := by rw [habs]
    _ = norm2 (cross (F.u i) (F.u j)) := Real.sq_sqrt (norm2_nonneg _)

end CoordinateTriple

/-- Three pairwise nonparallel directions in a unit-distance family cannot be coplanar. -/
theorem coordinate_triple_false (F : UFam) {i j k : Fin 8}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (cij : cross (F.u i) (F.u j) ≠ 0)
    (cik : cross (F.u i) (F.u k) ≠ 0)
    (cjk : cross (F.u j) (F.u k) ≠ 0)
    (hdet : det (F.u i) (F.u j) (F.u k) = 0) : False := by
  let a := F.u i
  let b := F.u j
  let c := F.u k
  let n := cross a b
  let N := norm2 n
  have hn : n ≠ 0 := by simpa [n, a, b] using cij
  have hN : 0 < N :=
    lt_of_le_of_ne (norm2_nonneg n) (fun h0 => hn ((norm2_eq_zero_iff n).1 h0.symm))
  have hcorth : dot c n = 0 := by
    calc
      dot c n = dot n c := dot_comm _ _
      _ = det a b c := (det_eq_dot_cross_left _ _ _).symm
      _ = 0 := by simpa [a, b, c] using hdet
  obtain ⟨s, t, hc⟩ := LineDist.exists_st a b c hn hcorth
  have hac : cross a c = (-t) • n := by
    rw [hc, cross_sub_right, cross_smul_right, cross_smul_right, cross_self]
    ext <;> simp [n, cross]
  have hbc : cross b c = (-s) • n := by
    rw [hc, cross_sub_right, cross_smul_right, cross_smul_right, cross_self]
    ext <;> simp [n, cross] <;> ring
  have ht : t ≠ 0 := by
    intro ht
    apply cik
    change cross a c = 0
    rw [hac, ht]
    ext <;> simp
  have hs : s ≠ 0 := by
    intro hs
    apply cjk
    change cross b c = 0
    rw [hbc, hs]
    ext <;> simp
  have hij_sq := CoordinateTriple.det_sq_eq_norm2_cross F hij cij
  have hik_sq := CoordinateTriple.det_sq_eq_norm2_cross F hik cik
  have hjk_sq := CoordinateTriple.det_sq_eq_norm2_cross F hjk cjk
  let x := dot (F.p i) n
  let y := dot (F.p j) n
  let z := dot (F.p k) n
  have hxy : (x - y) ^ 2 = N := by
    simpa only [det, sub_dot, a, b, n, N, x, y] using hij_sq
  have hxz_scaled : ((-t) * (x - z)) ^ 2 = (-t) ^ 2 * N := by
    calc
      ((-t) * (x - z)) ^ 2 = det (F.p i - F.p k) a c ^ 2 := by
        rw [det, hac, dot_smul_right, sub_dot]
      _ = norm2 (cross a c) := by simpa only [a, c] using hik_sq
      _ = norm2 ((-t) • n) := by rw [hac]
      _ = (-t) ^ 2 * N := by
        simp only [norm2, dot, smul_x, smul_y, smul_z, N]
        ring
  have hxz : (x - z) ^ 2 = N := by
    have ht2 : (-t) ^ 2 ≠ 0 := pow_ne_zero 2 (neg_ne_zero.mpr ht)
    apply (mul_left_cancel₀ ht2)
    nlinarith
  have hyz_scaled : ((-s) * (y - z)) ^ 2 = (-s) ^ 2 * N := by
    calc
      ((-s) * (y - z)) ^ 2 = det (F.p j - F.p k) b c ^ 2 := by
        rw [det, hbc, dot_smul_right, sub_dot]
      _ = norm2 (cross b c) := by simpa only [b, c] using hjk_sq
      _ = norm2 ((-s) • n) := by rw [hbc]
      _ = (-s) ^ 2 * N := by
        simp only [norm2, dot, smul_x, smul_y, smul_z, N]
        ring
  have hyz : (y - z) ^ 2 = N := by
    have hs2 : (-s) ^ 2 ≠ 0 := pow_ne_zero 2 (neg_ne_zero.mpr hs)
    apply (mul_left_cancel₀ hs2)
    nlinarith
  have hprod : ((x - z) - (y - z)) * ((x - z) + (y - z)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with heq | hneg
  · have : x - z = y - z := by linarith
    nlinarith
  · have : x - z = -(y - z) := by linarith
    nlinarith

end Results.EightEquidistantLines
