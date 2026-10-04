import Results.EightEquidistantLines.Defs

/-!
# Known-value tests for the statement layer (`E3`, `eucDist`, `IsAffineLine`, `setDist`)

These theorems pin the definitions of `Defs.lean` (`E3`, `eucDist`, `IsAffineLine`, `setDist`) to
cases whose answer is known independently of the main theorem, on both sides of each restriction.
They import only `Defs` (neither `Challenge` nor the `Solution` tree), and every proof is complete.
No norm or metric of `Fin 3 → ℝ` (Mathlib's default one is the sup metric) occurs below: every
distance is `eucDist`, and points of `E3` are written `![a, b, c]`.

* `IsAffineLine` accepts exactly the sets `p + ℝ v` with `v ≠ 0` (`test_isAffineLine_iff`, from
  `test_finrank_eq_one_iff`: the subspaces of dimension `1` are the spans of single non-zero
  vectors) and rejects the empty subspace, a point, a plane and the whole space
  (`test_not_isAffineLine_*`).
* `eucDist` is the Euclidean distance `√((x₀ - y₀)² + (x₁ - y₁)² + (x₂ - y₂)²)` (`test_eucDist_eq`);
  it is symmetric, non-negative and `0` from a point to itself.  Its values `5` between `(0,0,0)`
  and `(3,4,0)` and `√3` between `(0,0,0)` and `(1,1,1)` (`test_eucDist_345`, `test_eucDist_diag`)
  differ from those of the sup metric (`4` and `1`).
* For non-empty sets `A`, `B`, `setDist A B` is the greatest lower bound of the distances and
  agrees with the iterated infimum `inf_{x ∈ A} inf_{y ∈ B} eucDist x y` (`test_isGLB_setDist`,
  `test_setDist_eq_sInf_sInf`); a family of lines with a common non-zero `setDist` consists of
  distinct lines (`test_injective_of_common_setDist`).
* `setDist` is checked on lines parallel to a coordinate axis (`axisLine`; the coordinates
  `0, 1, 2` are `x, y, z`).  Two parallel axis lines have distance `√(sum of the squared offsets
  in the two other coordinates)`, two perpendicular axis lines have distance
  `|offset in the third coordinate|`.  Besides these formulas there are concrete values, among
  them a `3-4-5` case and a diagonal-offset case, which differ from the sup-metric values, and two
  negative cases with distance `2 ≠ 1`.  Pairs not parallel to a common axis are also covered: a
  perpendicular skew pair and a parallel pair with the non-axis direction `(1,1,0)`
  (`test_setDist_oblique`, `test_setDist_oblique_parallel`), and a skew pair meeting at `60°`
  with neither line parallel to an axis (`test_setDist_generic_skew`).
* The four lines `(t,0,0)`, `(t,1,0)`, `(0,t,1)`, `(1,t,1)` have all six pairwise distances `1`,
  so a four-line unit family exists in exactly the shape of the statement of Theorem 1.1 (with
  `Fin 4` instead of `Fin 8`): nothing in the definitions forbids small families.  The same holds
  for every common distance `d > 0` (`test_exists_four_lines_common_distance`).
-/

namespace Results.EightEquidistantLines

/-! ### `IsAffineLine`: lines are accepted, non-lines are rejected -/

/-- The subspaces of `ℝ³` of dimension `1`: a submodule `S` has `finrank ℝ S = 1` iff it is the
span of a single non-zero vector. -/
theorem test_finrank_eq_one_iff (S : Submodule ℝ E3) :
    Module.finrank ℝ S = 1 ↔ ∃ v : E3, v ≠ 0 ∧ S = Submodule.span ℝ {v} := by
  constructor
  · intro h
    have hr : Module.rank ℝ S = 1 := Module.rank_eq_one_iff_finrank_eq_one.mpr h
    obtain ⟨u, hu⟩ := Module.le_rank_iff.mp
      (show ((1 : ℕ) : Cardinal) ≤ Module.rank ℝ S by rw [hr, Nat.cast_one])
    have hu0 : ((u 0 : S) : E3) ≠ 0 := fun h0 => hu.ne_zero 0 (Subtype.ext h0)
    refine ⟨u 0, hu0, le_antisymm (fun w hw => ?_) ?_⟩
    · by_contra hwn
      have hli : LinearIndependent ℝ ![u 0, (⟨w, hw⟩ : S)] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        rw [Fin.sum_univ_two] at hg
        have hg' : g 0 • ((u 0 : S) : E3) + g 1 • w = 0 := by
          simpa using congrArg Subtype.val hg
        have hg1 : g 1 = 0 := by
          by_contra hne
          apply hwn
          rw [Submodule.mem_span_singleton]
          refine ⟨-(g 0) / g 1, ?_⟩
          funext k
          have hk := congrFun hg' k
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
          field_simp
          linarith
        have hg0 : g 0 = 0 := by
          rw [hg1, zero_smul, add_zero] at hg'
          exact (smul_eq_zero.mp hg').resolve_right hu0
        intro i
        fin_cases i
        · exact hg0
        · exact hg1
      have h2 : ((2 : ℕ) : Cardinal) ≤ Module.rank ℝ S := Module.le_rank_iff.mpr ⟨_, hli⟩
      rw [hr] at h2
      exact absurd (by exact_mod_cast h2 : (2 : ℕ) ≤ 1) (by norm_num)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (u 0).2
  · rintro ⟨v, hv, rfl⟩
    exact (LinearEquiv.toSpanNonzeroSingleton ℝ E3 v hv).finrank_eq.symm.trans
      (CommSemiring.finrank_self ℝ)

/-- For every vector `v`, the span `ℝ v` does not contain both coordinate vectors
`e₀ = (1, 0, 0)` and `e₁ = (0, 1, 0)`. -/
theorem test_e0_e1_not_mem_span_singleton (v : E3) :
    ¬ ((Pi.single 0 1 : E3) ∈ Submodule.span ℝ {v} ∧
      (Pi.single 1 1 : E3) ∈ Submodule.span ℝ {v}) := by
  rintro ⟨h0, h1⟩
  rw [Submodule.mem_span_singleton] at h0 h1
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have ha0 := congrFun ha 0
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  simp only [Pi.smul_apply, smul_eq_mul] at ha0 hb0 hb1
  rw [Pi.single_eq_same] at ha0 hb1
  rw [Pi.single_eq_of_ne (by decide)] at hb0
  -- now `a * v 0 = 1`, `b * v 0 = 0` and `b * v 1 = 1`
  have hb' : b = 0 := by
    calc b = b * (a * v 0) := by rw [ha0, mul_one]
      _ = a * (b * v 0) := by ring
      _ = 0 := by rw [hb0, mul_zero]
  rw [hb', zero_mul] at hb1
  exact zero_ne_one hb1

/-- The affine subspace through `p` with direction `ℝ v` is an affine line as soon as `v ≠ 0`. -/
theorem test_isAffineLine_axis (p v : E3) (hv : v ≠ 0) :
    IsAffineLine (AffineSubspace.mk' p (Submodule.span ℝ {v})) := by
  unfold IsAffineLine
  rw [AffineSubspace.direction_mk']
  exact (test_finrank_eq_one_iff _).mpr ⟨v, hv, rfl⟩

/-- The whole space is not an affine line (its direction `⊤` contains both `e₀` and `e₁`). -/
theorem test_not_isAffineLine_top : ¬ IsAffineLine (⊤ : AffineSubspace ℝ E3) := by
  unfold IsAffineLine
  rw [AffineSubspace.direction_top, test_finrank_eq_one_iff]
  rintro ⟨v, -, hv⟩
  exact test_e0_e1_not_mem_span_singleton v
    ⟨hv ▸ Submodule.mem_top, hv ▸ Submodule.mem_top⟩

/-- The empty subspace is not an affine line (its direction is `⊥`). -/
theorem test_not_isAffineLine_bot : ¬ IsAffineLine (⊥ : AffineSubspace ℝ E3) := by
  unfold IsAffineLine
  rw [AffineSubspace.direction_bot, test_finrank_eq_one_iff]
  rintro ⟨v, hv, hb⟩
  exact hv ((Submodule.mem_bot ℝ).mp (hb ▸ Submodule.mem_span_singleton_self v))

/-- A single point (the affine subspace through `p` with direction `⊥`) is not an affine line. -/
theorem test_not_isAffineLine_point (p : E3) :
    ¬ IsAffineLine (AffineSubspace.mk' p (⊥ : Submodule ℝ E3)) := by
  unfold IsAffineLine
  rw [AffineSubspace.direction_mk', test_finrank_eq_one_iff]
  rintro ⟨v, hv, hb⟩
  exact hv ((Submodule.mem_bot ℝ).mp (hb ▸ Submodule.mem_span_singleton_self v))

/-- A plane is not an affine line: here the plane `p + span {e₀, e₁}` with `e₀ = (1, 0, 0)` and
`e₁ = (0, 1, 0)` (the horizontal plane through `p`). -/
theorem test_not_isAffineLine_plane (p : E3) :
    ¬ IsAffineLine
      (AffineSubspace.mk' p (Submodule.span ℝ {(Pi.single 0 1 : E3), (Pi.single 1 1 : E3)})) := by
  unfold IsAffineLine
  rw [AffineSubspace.direction_mk', test_finrank_eq_one_iff]
  rintro ⟨v, -, hv⟩
  refine test_e0_e1_not_mem_span_singleton v ⟨?_, ?_⟩
  · rw [← hv]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · rw [← hv]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-- Exact description of the affine lines: `IsAffineLine L` holds iff `L` is `p + ℝ v` for some
point `p` and some nonzero vector `v`. -/
theorem test_isAffineLine_iff (L : AffineSubspace ℝ E3) :
    IsAffineLine L ↔ ∃ p v : E3, v ≠ 0 ∧ L = AffineSubspace.mk' p (Submodule.span ℝ {v}) := by
  constructor
  · intro h
    obtain ⟨v, hv, hdir⟩ := (test_finrank_eq_one_iff L.direction).mp h
    rcases L.eq_bot_or_nonempty with hb | ⟨p, hp⟩
    · exfalso
      subst hb
      rw [AffineSubspace.direction_bot] at hdir
      exact hv ((Submodule.mem_bot ℝ).mp (hdir ▸ Submodule.mem_span_singleton_self v))
    · refine ⟨p, v, hv, ?_⟩
      rw [← hdir]
      exact (AffineSubspace.mk'_eq hp).symm
  · rintro ⟨p, v, hv, rfl⟩
    exact test_isAffineLine_axis p v hv

/-- An affine line is non-empty; with `test_isGLB_setDist` this makes `setDist` of two lines the
genuine infimum of the distances. -/
theorem test_isAffineLine_nonempty {L : AffineSubspace ℝ E3} (h : IsAffineLine L) :
    (L : Set E3).Nonempty := by
  obtain ⟨p, v, -, rfl⟩ := (test_isAffineLine_iff L).mp h
  exact ⟨p, AffineSubspace.self_mem_mk' p _⟩

/-- The carrier of `mk' p (span {v})` is the set of points `p + t v`, `t ∈ ℝ`: the affine subspaces
used for lines below are the lines `{p + t v}`. -/
theorem test_mem_mk'_span_singleton (p v x : E3) :
    x ∈ AffineSubspace.mk' p (Submodule.span ℝ {v}) ↔ ∃ t : ℝ, x = p + t • v := by
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht, vsub_eq_sub]; abel
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [vsub_eq_sub]; abel⟩

/-! ### `eucDist`: the Euclidean distance, not the sup metric -/

/-- `eucDist` is the Euclidean distance: the square root of the sum of the three squared coordinate
differences. -/
theorem test_eucDist_eq (x y : E3) :
    eucDist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) := by
  rw [eucDist, Fin.sum_univ_three]

/-- `eucDist` is symmetric. -/
theorem test_eucDist_comm (x y : E3) : eucDist x y = eucDist y x := by
  rw [test_eucDist_eq, test_eucDist_eq]
  congr 1
  ring

/-- A point is at distance `0` from itself. -/
theorem test_eucDist_self (x : E3) : eucDist x x = 0 := by
  rw [test_eucDist_eq]
  simp

/-- `eucDist` is non-negative. -/
theorem test_eucDist_nonneg (x y : E3) : 0 ≤ eucDist x y :=
  Real.sqrt_nonneg _

/-- The points `(0, 0, 0)` and `(3, 4, 0)` are at distance `5` (the sup metric would give `4`). -/
theorem test_eucDist_345 : eucDist ![0, 0, 0] ![3, 4, 0] = 5 := by
  rw [test_eucDist_eq, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  norm_num [Matrix.cons_val_two]

/-- The points `(0, 0, 0)` and `(1, 1, 1)` (a diagonal vector) are at distance `√3` (the sup metric
would give `1`). -/
theorem test_eucDist_diag : eucDist ![0, 0, 0] ![1, 1, 1] = √3 := by
  rw [test_eucDist_eq]
  norm_num [Matrix.cons_val_two]

/-! ### `setDist`: general facts and the tool used for the known values -/

/-- `setDist A B = c` as soon as some pair of points of `A` and `B` is at distance `c` and every
pair is at distance at least `c`. -/
theorem test_setDist_eq_of_isLeast {A B : Set E3} {c : ℝ}
    (h₁ : ∃ x ∈ A, ∃ y ∈ B, eucDist x y = c)
    (h₂ : ∀ x ∈ A, ∀ y ∈ B, c ≤ eucDist x y) : setDist A B = c := by
  unfold setDist
  refine IsLeast.csInf_eq ⟨h₁, ?_⟩
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact h₂ x hx y hy

/-- `setDist` is non-negative. -/
theorem test_setDist_nonneg (A B : Set E3) : 0 ≤ setDist A B := by
  unfold setDist
  apply Real.sInf_nonneg
  rintro r ⟨x, _, y, _, rfl⟩
  exact test_eucDist_nonneg x y

/-- `setDist` is symmetric. -/
theorem test_setDist_comm (A B : Set E3) : setDist A B = setDist B A := by
  unfold setDist
  congr 1
  ext r
  constructor <;> rintro ⟨x, hx, y, hy, rfl⟩ <;> exact ⟨y, hy, x, hx, test_eucDist_comm _ _⟩

/-- On the empty set the infimum is the junk value `0` (`IsAffineLine` excludes the empty subspace,
see `test_not_isAffineLine_bot`). -/
theorem test_setDist_empty_left (B : Set E3) : setDist ∅ B = 0 := by
  unfold setDist
  simp

/-- The same junk value `0` when the second set is empty. -/
theorem test_setDist_empty_right (A : Set E3) : setDist A ∅ = 0 := by
  rw [test_setDist_comm]
  exact test_setDist_empty_left A

/-- The set whose infimum `setDist` takes is bounded below by `0`. -/
theorem test_setDist_bddBelow (A B : Set E3) :
    BddBelow {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, eucDist x y = r} :=
  ⟨0, by rintro r ⟨x, -, y, -, rfl⟩; exact test_eucDist_nonneg x y⟩

/-- `setDist` is a lower bound of all distances between points of the two sets. -/
theorem test_setDist_le {A B : Set E3} {x y : E3} (hx : x ∈ A) (hy : y ∈ B) :
    setDist A B ≤ eucDist x y :=
  csInf_le (test_setDist_bddBelow A B) ⟨x, hx, y, hy, rfl⟩

/-- For non-empty sets, `setDist` is the greatest lower bound of the distances (the paper's
`inf`). -/
theorem test_isGLB_setDist {A B : Set E3} (hA : A.Nonempty) (hB : B.Nonempty) :
    IsGLB {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, eucDist x y = r} (setDist A B) := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  exact isGLB_csInf ⟨eucDist x y, x, hx, y, hy, rfl⟩ (test_setDist_bddBelow A B)

/-- Agreement with the iterated infimum: for non-empty `A`, `B`,
`setDist A B = inf_{x ∈ A} inf_{y ∈ B} eucDist x y`. -/
theorem test_setDist_eq_sInf_sInf {A B : Set E3} (hA : A.Nonempty) (hB : B.Nonempty) :
    setDist A B = sInf ((fun x => sInf (eucDist x '' B)) '' A) := by
  have hin : ∀ x, BddBelow (eucDist x '' B) :=
    fun x => ⟨0, by rintro r ⟨y, -, rfl⟩; exact test_eucDist_nonneg x y⟩
  have hbdd : BddBelow ((fun x => sInf (eucDist x '' B)) '' A) :=
    ⟨0, by
      rintro r ⟨x, -, rfl⟩
      exact Real.sInf_nonneg (by rintro s ⟨y, -, rfl⟩; exact test_eucDist_nonneg x y)⟩
  apply le_antisymm
  · apply le_csInf (hA.image _)
    rintro r ⟨x, hx, rfl⟩
    show setDist A B ≤ sInf (eucDist x '' B)
    apply le_csInf (hB.image _)
    rintro s ⟨y, hy, rfl⟩
    exact test_setDist_le hx hy
  · obtain ⟨x0, hx0⟩ := hA
    obtain ⟨y0, hy0⟩ := hB
    show _ ≤ sInf {r : ℝ | ∃ x ∈ A, ∃ y ∈ B, eucDist x y = r}
    refine le_csInf ⟨eucDist x0 y0, x0, hx0, y0, hy0, rfl⟩ ?_
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact (csInf_le hbdd ⟨x, hx, rfl⟩).trans (csInf_le (hin x) ⟨y, hy, rfl⟩)

/-- A non-empty set has `setDist` zero from itself. -/
theorem test_setDist_self {A : Set E3} (hA : A.Nonempty) : setDist A A = 0 := by
  obtain ⟨x, hx⟩ := hA
  exact le_antisymm ((test_setDist_le hx hx).trans_eq (test_eucDist_self x))
    (test_setDist_nonneg A A)

/-- Aliasing is excluded by the hypotheses of the main theorems: a family of lines with a common
pairwise `setDist` `d ≠ 0` consists of distinct lines. -/
theorem test_injective_of_common_setDist {n : ℕ} (L : Fin n → AffineSubspace ℝ E3)
    (hL : ∀ i, IsAffineLine (L i)) {d : ℝ} (hd : d ≠ 0)
    (h : ∀ i j, i < j → setDist (L i) (L j) = d) : Function.Injective L := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h i j hlt
    rw [hij, test_setDist_self (test_isAffineLine_nonempty (hL j))] at this
    exact hd this.symm
  · have := h j i hlt
    rw [hij, test_setDist_self (test_isAffineLine_nonempty (hL j))] at this
    exact hd this.symm

/-! ### Lines parallel to a coordinate axis -/

/-- The line `{q + t e_i : t ∈ ℝ}` through `q` parallel to the `i`-th coordinate axis, where
`e_i = Pi.single i 1` (the coordinates `0, 1, 2` are `x, y, z`). -/
noncomputable def axisLine (i : Fin 3) (q : E3) : AffineSubspace ℝ E3 :=
  AffineSubspace.mk' q (Submodule.span ℝ {Pi.single i (1 : ℝ)})

theorem test_isAffineLine_axisLine (i : Fin 3) (q : E3) : IsAffineLine (axisLine i q) :=
  test_isAffineLine_axis q _ (by simp)

/-- A point lies on `axisLine i q` iff it agrees with `q` in every coordinate other than the
`i`-th. -/
theorem test_mem_axisLine (i : Fin 3) (q x : E3) :
    x ∈ axisLine i q ↔ ∀ k, k ≠ i → x k = q k := by
  unfold axisLine
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩ k hk
    have h := congrFun ht k
    simp [hk] at h
    linarith
  · intro h
    refine ⟨x i - q i, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk, h k hk]

/-- Moving `q` along the `i`-th axis stays on the line. -/
theorem test_axisLine_shift (i : Fin 3) (q : E3) (t : ℝ) :
    q + t • Pi.single i (1 : ℝ) ∈ axisLine i q := by
  rw [test_mem_axisLine]
  intro k hk
  simp [hk]

/-- If `i, j, l` are three distinct indices of `Fin 3`, every other index is `i` or `j`. -/
theorem test_fin3_third {i j l k : Fin 3} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hkl : k ≠ l) : k = i ∨ k = j := by
  revert i j l k; decide

/-- Two lines parallel to the same coordinate axis `i`: their distance is the square root of the
sum of the squared offsets in the two other coordinates. -/
theorem test_setDist_axisLine_parallel (i : Fin 3) (q q' : E3) :
    setDist (axisLine i q) (axisLine i q') =
      √(∑ k ∈ Finset.univ.erase i, (q k - q' k) ^ 2) := by
  apply test_setDist_eq_of_isLeast
  · refine ⟨q, ?_, q' + (q i - q' i) • Pi.single i (1 : ℝ), test_axisLine_shift i q' _, ?_⟩
    · rw [SetLike.mem_coe, test_mem_axisLine]
      intro k _
      rfl
    · unfold eucDist
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have h0 : (q i - (q' + (q i - q' i) • Pi.single i (1 : ℝ) : E3) i) ^ 2 = 0 := by simp
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [hk']
  · intro x hx y hy
    rw [SetLike.mem_coe, test_mem_axisLine] at hx hy
    unfold eucDist
    apply Real.sqrt_le_sqrt
    calc ∑ k ∈ Finset.univ.erase i, (q k - q' k) ^ 2
        = ∑ k ∈ Finset.univ.erase i, (x k - y k) ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≠ i := Finset.ne_of_mem_erase hk
          rw [hx k hk', hy k hk']
      _ ≤ ∑ k, (x k - y k) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => sq_nonneg _)

/-- Two lines parallel to different coordinate axes `i ≠ j` (they are skew or meet): with `l` the
third coordinate, their distance is the absolute value of the offset in the coordinate `l`. -/
theorem test_setDist_axisLine_skew {i j l : Fin 3} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (q q' : E3) :
    setDist (axisLine i q) (axisLine j q') = |q l - q' l| := by
  apply test_setDist_eq_of_isLeast
  · refine ⟨q + (q' i - q i) • Pi.single i (1 : ℝ), test_axisLine_shift i q _,
      q' + (q j - q' j) • Pi.single j (1 : ℝ), test_axisLine_shift j q' _, ?_⟩
    unfold eucDist
    have hsum : ∑ k, ((q + (q' i - q i) • Pi.single i (1 : ℝ) : E3) k -
        (q' + (q j - q' j) • Pi.single j (1 : ℝ) : E3) k) ^ 2 = (q l - q' l) ^ 2 := by
      rw [Finset.sum_eq_single l]
      · simp [hli, hlj]
      · intro k _ hkl
        rcases test_fin3_third hij hli hlj hkl with rfl | rfl
        · simp [hij]
        · simp [Ne.symm hij]
      · intro h
        exact absurd (Finset.mem_univ l) h
    rw [hsum, Real.sqrt_sq_eq_abs]
  · intro x hx y hy
    rw [SetLike.mem_coe, test_mem_axisLine] at hx hy
    unfold eucDist
    rw [← Real.sqrt_sq_eq_abs, ← hx l hli, ← hy l hlj]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => (x k - y k) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ l))

/-- A line parallel to a coordinate axis has distance `0` from itself. -/
theorem test_setDist_axisLine_self (i : Fin 3) (q : E3) :
    setDist (axisLine i q) (axisLine i q) = 0 := by
  rw [test_setDist_axisLine_parallel]
  simp

/-! ### The same formulas in explicit coordinates -/

theorem test_setDist_parallel_x (q q' : E3) :
    setDist (axisLine 0 q) (axisLine 0 q') = √((q 1 - q' 1) ^ 2 + (q 2 - q' 2) ^ 2) := by
  rw [test_setDist_axisLine_parallel, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Fin.sum_univ_three]
  congr 1
  ring

theorem test_setDist_parallel_y (q q' : E3) :
    setDist (axisLine 1 q) (axisLine 1 q') = √((q 0 - q' 0) ^ 2 + (q 2 - q' 2) ^ 2) := by
  rw [test_setDist_axisLine_parallel, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Fin.sum_univ_three]
  congr 1
  ring

theorem test_setDist_parallel_z (q q' : E3) :
    setDist (axisLine 2 q) (axisLine 2 q') = √((q 0 - q' 0) ^ 2 + (q 1 - q' 1) ^ 2) := by
  rw [test_setDist_axisLine_parallel, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Fin.sum_univ_three]
  congr 1
  ring

theorem test_setDist_skew_xy (q q' : E3) :
    setDist (axisLine 0 q) (axisLine 1 q') = |q 2 - q' 2| :=
  test_setDist_axisLine_skew (by decide) (by decide) (by decide) q q'

theorem test_setDist_skew_xz (q q' : E3) :
    setDist (axisLine 0 q) (axisLine 2 q') = |q 1 - q' 1| :=
  test_setDist_axisLine_skew (by decide) (by decide) (by decide) q q'

theorem test_setDist_skew_yz (q q' : E3) :
    setDist (axisLine 1 q) (axisLine 2 q') = |q 0 - q' 0| :=
  test_setDist_axisLine_skew (by decide) (by decide) (by decide) q q'

/-! ### Concrete values -/

/-- The `x`-axis and its parallel through `(0, 1, 0)`: distance `1`. -/
theorem test_setDist_xAxis_parallel_unit :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, 1, 0]) = 1 := by
  rw [test_setDist_parallel_x]
  simp

/-- The `x`-axis and its parallel through `(0, 2, 0)`: distance `2`. -/
theorem test_setDist_xAxis_parallel_two :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, 2, 0]) = 2 := by
  rw [test_setDist_parallel_x]
  simp

/-- Negative case: the `x`-axis and its parallel through `(0, 2, 0)` are not at distance `1`. -/
theorem test_setDist_xAxis_parallel_two_ne_one :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, 2, 0]) ≠ 1 := by
  rw [test_setDist_xAxis_parallel_two]
  norm_num

/-- Offsets `3` and `4` in the two other coordinates give distance `5` (this detects a wrong norm;
the offset `7` along the axis is irrelevant). -/
theorem test_setDist_parallel_345 :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![7, 3, 4]) = 5 := by
  rw [test_setDist_parallel_x, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  norm_num [Matrix.cons_val_two]

/-- The `x`-axis and its parallel through `(0, 1, 1)` (a diagonal offset): distance `√2` (the sup
metric would give `1`). -/
theorem test_setDist_parallel_diag :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, 1, 1]) = √2 := by
  rw [test_setDist_parallel_x]
  norm_num [Matrix.cons_val_two]

/-- The `x`-axis and the line `{(0, t, 1)}`: distance `1`. -/
theorem test_setDist_xAxis_skew_unit :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, 1]) = 1 := by
  rw [test_setDist_skew_xy]
  simp

/-- The `x`-axis and the line `{(0, t, 2)}`: distance `2`. -/
theorem test_setDist_xAxis_skew_two :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, 2]) = 2 := by
  rw [test_setDist_skew_xy]
  simp

/-- Negative case: the `x`-axis and the line `{(0, t, 2)}` are not at distance `1`. -/
theorem test_setDist_xAxis_skew_two_ne_one :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, 2]) ≠ 1 := by
  rw [test_setDist_xAxis_skew_two]
  norm_num

/-- The offset in the third coordinate decides: here `|0 - (-3)| = 3`, whatever the offsets `7`,
`9` in the other two coordinates. -/
theorem test_setDist_skew_offset :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![7, 9, -3]) = 3 := by
  rw [test_setDist_skew_xy]
  simp

/-- The `x`-axis and the `y`-axis meet at the origin: distance `0`. -/
theorem test_setDist_xAxis_yAxis :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, 0]) = 0 := by
  rw [test_setDist_skew_xy]
  simp

/-! ### Pairs not parallel to a common coordinate axis -/

/-- A skew pair with a non-axis direction: the `x`-axis and the line through `(0,0,1)` with direction
`(0,1,1)` (perpendicular to the `x`-axis) are at distance `√(1/2)` (common perpendicular from the
origin to `(0,-1/2,1/2)`). -/
theorem test_setDist_oblique :
    setDist (axisLine 0 ![0, 0, 0])
      (AffineSubspace.mk' (![0, 0, 1] : E3) (Submodule.span ℝ {(![0, 1, 1] : E3)})) =
        √(1 / 2) := by
  apply test_setDist_eq_of_isLeast
  · refine ⟨(![0, 0, 0] : E3), ?_, (![0, -1/2, 1/2] : E3), ?_, ?_⟩
    · rw [SetLike.mem_coe, test_mem_axisLine]
      intro k _
      rfl
    · rw [SetLike.mem_coe, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
      refine ⟨-1/2, ?_⟩
      funext k
      fin_cases k <;> norm_num [Matrix.cons_val_two]
    · rw [test_eucDist_eq]
      congr 1
      norm_num [Matrix.cons_val_two]
  · intro x hx y hy
    rw [SetLike.mem_coe, test_mem_axisLine] at hx
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hy
    obtain ⟨s, hs⟩ := hy
    have h0 := congrFun hs 0
    have h1 := congrFun hs 1
    have h2 := congrFun hs 2
    simp at h0 h1 h2
    have hx1 := hx 1 (by decide)
    have hx2 := hx 2 (by decide)
    simp at hx1 hx2
    rw [test_eucDist_eq]
    apply Real.sqrt_le_sqrt
    rw [hx1, hx2, ← h0]
    have hy1 : y 1 = s := by linarith
    have hy2 : y 2 = s + 1 := by linarith
    rw [hy1, hy2]
    nlinarith [sq_nonneg (x 0), sq_nonneg (s + 1 / 2)]

/-- A pair of parallel lines with the non-axis direction `(1,1,0)`, through the origin and through
`(1,-1,0)`: distance `√2`. -/
theorem test_setDist_oblique_parallel :
    setDist (AffineSubspace.mk' (![0, 0, 0] : E3) (Submodule.span ℝ {(![1, 1, 0] : E3)}))
      (AffineSubspace.mk' (![1, -1, 0] : E3) (Submodule.span ℝ {(![1, 1, 0] : E3)})) = √2 := by
  apply test_setDist_eq_of_isLeast
  · refine ⟨(![0, 0, 0] : E3), AffineSubspace.self_mem_mk' _ _, (![1, -1, 0] : E3),
      AffineSubspace.self_mem_mk' _ _, ?_⟩
    rw [test_eucDist_eq]
    congr 1
    norm_num [Matrix.cons_val_two]
  · intro x hx y hy
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hx hy
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    have a0 := congrFun hs 0
    have a1 := congrFun hs 1
    have a2 := congrFun hs 2
    have b0 := congrFun ht 0
    have b1 := congrFun ht 1
    have b2 := congrFun ht 2
    simp at a0 a1 a2 b0 b1 b2
    rw [test_eucDist_eq]
    apply Real.sqrt_le_sqrt
    have ex0 : x 0 = s := by linarith
    have ex1 : x 1 = s := by linarith
    have ex2 : x 2 = 0 := by linarith
    have ey0 : y 0 = t + 1 := by linarith
    have ey1 : y 1 = t - 1 := by linarith
    have ey2 : y 2 = 0 := by linarith
    rw [ex0, ex1, ex2, ey0, ey1, ey2]
    nlinarith [sq_nonneg (s - t)]

/-- A genuinely oblique skew pair (angle `60°`, neither line parallel to an axis, not perpendicular):
directions `(1,1,0)` and `(0,1,1)`, through `0` and `(0,0,1)`: distance `√(1/3)`
(`|(0,0,1)·(u×v)|/|u×v|` with `u×v = (1,-1,1)`). -/
theorem test_setDist_generic_skew :
    setDist (AffineSubspace.mk' (![0, 0, 0] : E3) (Submodule.span ℝ {(![1, 1, 0] : E3)}))
      (AffineSubspace.mk' (![0, 0, 1] : E3) (Submodule.span ℝ {(![0, 1, 1] : E3)})) =
        √(1 / 3) := by
  unfold setDist
  refine IsLeast.csInf_eq ⟨⟨(![-1/3, -1/3, 0] : E3), ?_, (![0, -2/3, 1/3] : E3), ?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, test_mem_mk'_span_singleton]
    exact ⟨-1/3, by funext k; fin_cases k <;> norm_num [Matrix.cons_val_two]⟩
  · rw [SetLike.mem_coe, test_mem_mk'_span_singleton]
    exact ⟨-2/3, by funext k; fin_cases k <;> norm_num [Matrix.cons_val_two]⟩
  · rw [eucDist, Fin.sum_univ_three]
    congr 1
    norm_num [Matrix.cons_val_two]
  · rintro r ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, test_mem_mk'_span_singleton] at hx hy
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    rw [eucDist, Fin.sum_univ_three]
    apply Real.sqrt_le_sqrt
    simp [Matrix.cons_val_two]
    nlinarith [sq_nonneg (s + 1/3), sq_nonneg (t + 2/3), sq_nonneg (s - t - 1/3)]

/-! ### A family of four lines at pairwise distance `d` -/

/-- The lines `(t,0,0)`, `(t,d,0)`, `(0,t,d)`, `(d,t,d)`: two lines parallel to the `x`-axis and
two parallel to the `y`-axis. -/
noncomputable def fourLines (d : ℝ) : Fin 4 → AffineSubspace ℝ E3 :=
  ![axisLine 0 ![0, 0, 0], axisLine 0 ![0, d, 0], axisLine 1 ![0, 0, d],
    axisLine 1 ![d, 0, d]]

/-- The four lines for `d = 1` as solution sets of coordinate equations: `(t,0,0)` is
`{x₁ = 0, x₂ = 0}`, `(t,1,0)` is `{x₁ = 1, x₂ = 0}`, `(0,t,1)` is `{x₀ = 0, x₂ = 1}` and `(1,t,1)`
is `{x₀ = 1, x₂ = 1}`. -/
theorem test_four_lines_membership (x : E3) :
    (x ∈ axisLine 0 ![0, 0, 0] ↔ x 1 = 0 ∧ x 2 = 0) ∧
    (x ∈ axisLine 0 ![0, 1, 0] ↔ x 1 = 1 ∧ x 2 = 0) ∧
    (x ∈ axisLine 1 ![0, 0, 1] ↔ x 0 = 0 ∧ x 2 = 1) ∧
    (x ∈ axisLine 1 ![1, 0, 1] ↔ x 0 = 1 ∧ x 2 = 1) := by
  simp [test_mem_axisLine, Fin.forall_fin_succ]

/-- The six pairwise distances of the four lines `(t,0,0)`, `(t,d,0)`, `(0,t,d)`, `(d,t,d)` for
`d > 0`. -/
theorem test_four_lines_six_distances_d (d : ℝ) (hd : 0 < d) :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, d, 0]) = d ∧
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, d]) = d ∧
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![d, 0, d]) = d ∧
    setDist (axisLine 0 ![0, d, 0]) (axisLine 1 ![0, 0, d]) = d ∧
    setDist (axisLine 0 ![0, d, 0]) (axisLine 1 ![d, 0, d]) = d ∧
    setDist (axisLine 1 ![0, 0, d]) (axisLine 1 ![d, 0, d]) = d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [test_setDist_parallel_x]; simp [Real.sqrt_sq hd.le]
  · rw [test_setDist_skew_xy]; simp [abs_of_pos hd]
  · rw [test_setDist_skew_xy]; simp [abs_of_pos hd]
  · rw [test_setDist_skew_xy]; simp [abs_of_pos hd]
  · rw [test_setDist_skew_xy]; simp [abs_of_pos hd]
  · rw [test_setDist_parallel_y]; simp [Real.sqrt_sq hd.le]

/-- The four lines `(t,0,0)`, `(t,1,0)`, `(0,t,1)`, `(1,t,1)` have all six pairwise distances
`1`. -/
theorem test_four_lines_six_distances :
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 0 ![0, 1, 0]) = 1 ∧
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![0, 0, 1]) = 1 ∧
    setDist (axisLine 0 ![0, 0, 0]) (axisLine 1 ![1, 0, 1]) = 1 ∧
    setDist (axisLine 0 ![0, 1, 0]) (axisLine 1 ![0, 0, 1]) = 1 ∧
    setDist (axisLine 0 ![0, 1, 0]) (axisLine 1 ![1, 0, 1]) = 1 ∧
    setDist (axisLine 1 ![0, 0, 1]) (axisLine 1 ![1, 0, 1]) = 1 :=
  test_four_lines_six_distances_d 1 one_pos

theorem test_fourLines_isAffineLine (d : ℝ) (i : Fin 4) : IsAffineLine (fourLines d i) := by
  fin_cases i <;> exact test_isAffineLine_axisLine _ _

theorem test_fourLines_setDist (d : ℝ) (hd : 0 < d) (i j : Fin 4) (hij : i < j) :
    setDist (fourLines d i) (fourLines d j) = d := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := test_four_lines_six_distances_d d hd
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

/-- For every `d > 0` there are four affine lines at pairwise distance `d`: the conclusion of the
upper bound of Corollary 1.2 (no `n` lines at pairwise distance `d`) fails for `n = 4`. -/
theorem test_exists_four_lines_common_distance (d : ℝ) (hd : 0 < d) :
    ∃ L : Fin 4 → AffineSubspace ℝ E3,
      (∀ i, IsAffineLine (L i)) ∧ ∀ i j, i < j → setDist (L i) (L j) = d :=
  ⟨fourLines d, test_fourLines_isAffineLine d, test_fourLines_setDist d hd⟩

/-- There are four affine lines at pairwise distance one, so the hypothesis of Theorem 1.1 can be
met (here with `Fin 4` in place of `Fin 8`): the analogue of Theorem 1.1 for four lines is false. -/
theorem test_exists_four_unit_lines :
    ∃ L : Fin 4 → AffineSubspace ℝ E3,
      (∀ i, IsAffineLine (L i)) ∧ ∀ i j, i < j → setDist (L i) (L j) = 1 :=
  test_exists_four_lines_common_distance 1 one_pos

end Results.EightEquidistantLines
