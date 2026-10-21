import ProperCircularArc.Coefficients

/-!
# Scalar identities among the coefficients `A(y ∣ s)`

These are the coefficientwise forms of the tableau identities of Proposition `identities`.
Each one follows from the insertion ratio (Equation (ratio)) after separating the finitely many
special positions where the ratio does not apply.
-/

namespace ProperCircularArc

open Finset

lemma Acoef_zero_left (s : Finset ℕ) : Acoef 0 s = 0 :=
  Acoef_of_not_mem fun h => by have := pos_of_mem_Tset h; omega

lemma cast_sub_ne_zero {y z : ℕ} (h : y ≠ z) : (y : ℚ) - z ≠ 0 :=
  sub_ne_zero.2 (by exact_mod_cast h)

lemma cast_sub_sub_one_ne_zero {y z : ℕ} (h : y ≠ z + 1) : (y : ℚ) - z - 1 ≠ 0 := by
  intro e
  apply h
  have : (y : ℚ) = ((z + 1 : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast this

lemma Acoef_insert_of_mem {a y : ℕ} {s : Finset ℕ} (ha : a ∈ s) : Acoef y (insert a s) = Acoef y s := by
  rw [insert_eq_of_mem ha]

/-- Scalar form of `S_{k-1} M_{k-1} M_{k-2} = M_{k-1} M_{k-2}`. -/
lemma scalar_MM (w : Finset ℕ) {y z : ℕ} (hyz : y ≠ z) :
    Acoef y w * Acoef z (insert y w) * (1 / ((z : ℚ) - y))
      + Acoef z w * Acoef y (insert z w) * (1 - 1 / ((y : ℚ) - z))
      = Acoef y w * Acoef z (insert y w) := by
  by_cases hy : y ∈ w
  · simp [Acoef_eq_zero_of_mem hy, Acoef_eq_zero_of_mem (mem_insert_of_mem hy)]
  by_cases hz : z ∈ w
  · simp [Acoef_eq_zero_of_mem hz, Acoef_eq_zero_of_mem (mem_insert_of_mem hz)]
  rcases Nat.eq_zero_or_pos y with rfl | hy1
  · simp [Acoef_zero_left]
  rcases Nat.eq_zero_or_pos z with rfl | hz1
  · simp [Acoef_zero_left]
  by_cases h1 : z = y + 1
  · subst h1
    rw [Acoef_succ_of_not_mem hy hy1]
    have : ((y + 1 : ℕ) : ℚ) - y = 1 := by push_cast; ring
    rw [this]
    ring
  by_cases h2 : y = z + 1
  · subst h2
    rw [Acoef_succ_of_not_mem hz hz1]
    have : ((z + 1 : ℕ) : ℚ) - z = 1 := by push_cast; ring
    rw [this]
    ring
  rw [Acoef_insert hy h1, Acoef_insert hz h2]
  have := cast_sub_ne_zero hyz
  have := cast_sub_ne_zero (Ne.symm hyz)
  have := cast_sub_sub_one_ne_zero h1
  have := cast_sub_sub_one_ne_zero h2
  field_simp
  ring

/-- Scalar form of the swap-delete identity `D_k R_k = R_{k-1} D_k S_1`. -/
lemma scalar_swapDelete (w : Finset ℕ) {a b : ℕ} (hab : a ≠ b) (ha : a ∉ w) (hb : b ∉ w)
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (y : ℕ) :
    Acoef y (insert b w) - Acoef y (insert a (insert b w))
      = 1 / ((b : ℚ) - a) * (Acoef y w - Acoef y (insert b w))
        + (1 - 1 / ((b : ℚ) - a)) * (Acoef y w - Acoef y (insert a w)) := by
  have hab' : a ∉ insert b w := by simp [hab, ha]
  have hba' : b ∉ insert a w := by simp [Ne.symm hab, hb]
  have hba : (b : ℚ) - a ≠ 0 := cast_sub_ne_zero (Ne.symm hab)
  have hcomm : insert a (insert b w) = insert b (insert a w) := insert_comm a b w
  rcases Nat.eq_zero_or_pos y with rfl | hy1
  · simp [Acoef_zero_left]
  by_cases hyw : y ∈ w
  · simp [Acoef_eq_zero_of_mem hyw, Acoef_eq_zero_of_mem (mem_insert_of_mem hyw),
      Acoef_eq_zero_of_mem (mem_insert_of_mem (mem_insert_of_mem hyw))]
  by_cases hya : y = a
  · subst hya
    rw [Acoef_eq_zero_of_mem (mem_insert_self _ _), Acoef_eq_zero_of_mem (mem_insert_self _ _)]
    by_cases hyb : y = b + 1
    · subst hyb
      rw [Acoef_succ_of_not_mem hb hb1]
      push_cast
      have : ((b : ℚ) - (b + 1)) = -1 := by ring
      rw [this]; ring
    · rw [Acoef_insert hb hyb]
      have := cast_sub_sub_one_ne_zero hyb
      field_simp
      ring
  by_cases hyb : y = b
  · subst hyb
    rw [Acoef_eq_zero_of_mem (mem_insert_self _ _),
      Acoef_eq_zero_of_mem (mem_insert_of_mem (mem_insert_self _ _))]
    by_cases hya1 : y = a + 1
    · subst hya1
      rw [Acoef_succ_of_not_mem ha ha1]
      push_cast; ring
    · rw [Acoef_insert ha hya1]
      have := cast_sub_sub_one_ne_zero hya1
      have hya' : (y : ℚ) - a ≠ 0 := cast_sub_ne_zero hya
      field_simp
      ring
  by_cases hya1 : y = a + 1
  · subst hya1
    have hb' : a + 1 ≠ b + 1 := by omega
    rw [Acoef_insert hb hb', Acoef_succ_of_not_mem ha ha1, hcomm, Acoef_insert hba' hb']
    push_cast
    have h3 : (a : ℚ) + 1 - b - 1 ≠ 0 := by
      intro e; apply hab; have : (a : ℚ) = b := by linarith
      exact_mod_cast this
    field_simp
    ring
  by_cases hyb1 : y = b + 1
  · subst hyb1
    rw [Acoef_insert hab' hya1, Acoef_insert ha hya1, Acoef_succ_of_not_mem hb hb1]
    push_cast
    have h3 : (b : ℚ) + 1 - a - 1 ≠ 0 := by
      intro e; apply hab; have : (a : ℚ) = b := by linarith
      exact_mod_cast this
    field_simp
    ring
  rw [Acoef_insert hab' hya1, Acoef_insert hb hyb1, Acoef_insert ha hya1]
  have := cast_sub_sub_one_ne_zero hya1
  have := cast_sub_sub_one_ne_zero hyb1
  field_simp
  ring

lemma cast_ne_of_ne {y z : ℕ} (h : y ≠ z) : (y : ℚ) ≠ z := by exact_mod_cast h

/-- Scalar form of `S_{k-1} M_{k-1} R_{k-1} = R_k M_{k-1}`. -/
lemma scalar_lastSwap (w : Finset ℕ) {a y z : ℕ} (ha : a ∉ w) (ha1 : 1 ≤ a) (hyz : y ≠ z) :
    (Acoef y w - Acoef y (insert a w)) * Acoef z (insert y w) * (1 / ((z : ℚ) - y))
      + (Acoef z w - Acoef z (insert a w)) * Acoef y (insert z w) * (1 - 1 / ((y : ℚ) - z))
      = Acoef y (insert a w) * (Acoef z (insert y w) - Acoef z (insert a (insert y w))) := by
  have hzy : (z : ℚ) - y ≠ 0 := cast_sub_ne_zero (Ne.symm hyz)
  have hyz' : (y : ℚ) - z ≠ 0 := cast_sub_ne_zero hyz
  -- degenerate `y`
  by_cases hy0 : y = 0 ∨ y ∈ w
  · have h1 : Acoef y w = 0 := by
      rcases hy0 with rfl | h
      · exact Acoef_zero_left _
      · exact Acoef_eq_zero_of_mem h
    have h2 : Acoef y (insert a w) = 0 := by
      rcases hy0 with rfl | h
      · exact Acoef_zero_left _
      · exact Acoef_eq_zero_of_mem (mem_insert_of_mem h)
    have h3 : Acoef y (insert z w) = 0 := by
      rcases hy0 with rfl | h
      · exact Acoef_zero_left _
      · exact Acoef_eq_zero_of_mem (mem_insert_of_mem h)
    simp [h1, h2, h3]
  push_neg at hy0
  obtain ⟨hy0, hyw⟩ := hy0
  have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.2 hy0
  -- degenerate `z`
  by_cases hz0 : z = 0 ∨ z ∈ w
  · have hz : ∀ s : Finset ℕ, w ⊆ s → Acoef z s = 0 := by
      intro s hs
      rcases hz0 with rfl | h
      · exact Acoef_zero_left _
      · exact Acoef_eq_zero_of_mem (hs h)
    rw [hz w le_rfl, hz _ (subset_insert _ _), hz _ (subset_insert _ _),
      hz _ ((subset_insert _ _).trans (subset_insert _ _))]
    ring
  push_neg at hz0
  obtain ⟨hz0, hzw⟩ := hz0
  have hz1 : 1 ≤ z := Nat.one_le_iff_ne_zero.2 hz0
  have hyw' : y ∉ insert z w := by simp [hyz, hyw]
  have hzw' : z ∉ insert y w := by simp [Ne.symm hyz, hzw]
  -- `y = a`
  by_cases hya : y = a
  · subst hya
    rw [Acoef_eq_zero_of_mem (mem_insert_self _ _), insert_idem]
    by_cases hz : z = y + 1
    · subst hz
      rw [Acoef_succ_of_not_mem hyw hy1, Acoef_insert hzw (by omega)]
      push_cast
      field_simp
      ring
    by_cases hy' : y = z + 1
    · subst hy'
      rw [Acoef_succ_of_not_mem hzw hz1]
      push_cast
      ring
    rw [Acoef_insert hyw hz, Acoef_insert hzw hy']
    have := cast_sub_sub_one_ne_zero hz
    have := cast_sub_sub_one_ne_zero hy'
    field_simp
    ring
  -- `z = a`
  by_cases hza : z = a
  · subst hza
    rw [Acoef_eq_zero_of_mem (mem_insert_self _ _),
      Acoef_eq_zero_of_mem (mem_insert_self _ _)]
    by_cases hz : z = y + 1
    · subst hz
      rw [Acoef_succ_of_not_mem hyw hy1, Acoef_insert hzw (by omega)]
      push_cast
      field_simp
      ring
    by_cases hy' : y = z + 1
    · subst hy'
      rw [Acoef_succ_of_not_mem hzw hz1, Acoef_insert hyw (by omega)]
      push_cast
      field_simp
      ring
    rw [Acoef_insert hyw hz, Acoef_insert hzw hy']
    have := cast_sub_sub_one_ne_zero hz
    have := cast_sub_sub_one_ne_zero hy'
    field_simp
    ring
  have hay : a ∉ insert y w := by simp [Ne.symm hya, ha]
  have hya' : y ∉ insert a w := by simp [hya, hyw]
  -- `z = y + 1`
  by_cases hz : z = y + 1
  · subst hz
    have hza1 : y + 1 ≠ a + 1 := by omega
    rw [Acoef_succ_of_not_mem hyw hy1, Acoef_insert ha hza1, Acoef_succ_of_not_mem hyw hy1,
      Acoef_insert hay hza1, Acoef_insert hzw (by omega)]
    by_cases hya1 : y = a + 1
    · subst hya1
      rw [Acoef_succ_of_not_mem ha ha1]
      push_cast
      field_simp
      ring
    rw [Acoef_insert ha hya1]
    have f1 := cast_sub_sub_one_ne_zero hya1
    have f2 := cast_sub_ne_zero hya
    push_cast at *
    have f3 : (y : ℚ) + 1 - a - 1 ≠ 0 := fun e => f2 (by linarith)
    field_simp
    ring
  -- `y = z + 1`
  by_cases hy' : y = z + 1
  · subst hy'
    have hya1 : z + 1 ≠ a + 1 := by omega
    rw [Acoef_succ_of_not_mem hzw hz1, Acoef_insert ha hya1, Acoef_succ_of_not_mem hzw hz1]
    push_cast
    ring
  -- `y = a + 1`
  by_cases hya1 : y = a + 1
  · subst hya1
    have hza1 : z ≠ a + 1 := hyz.symm
    rw [Acoef_succ_of_not_mem ha ha1, Acoef_insert hzw hy', Acoef_succ_of_not_mem ha ha1,
      Acoef_insert hyw hz, Acoef_insert ha hza1, Acoef_insert hay hza1, Acoef_insert hyw hz]
    have f1 := cast_sub_sub_one_ne_zero hz
    have f2 := cast_sub_sub_one_ne_zero hza1
    have f3 := cast_sub_ne_zero hza
    push_cast at *
    field_simp
    ring
  -- `z = a + 1`
  by_cases hza1 : z = a + 1
  · subst hza1
    rw [Acoef_succ_of_not_mem ha ha1, Acoef_insert hyw hz, Acoef_succ_of_not_mem ha ha1,
      Acoef_insert ha hya1, Acoef_insert hzw hy', insert_comm a y w, Acoef_insert hya' hz]
    have f1 := cast_sub_sub_one_ne_zero hz
    have f2 := cast_sub_sub_one_ne_zero hya1
    have f3 := cast_sub_sub_one_ne_zero hy'
    have f4 := cast_sub_ne_zero hya
    have f5 := cast_sub_ne_zero (Ne.symm hya)
    push_cast at *
    field_simp
    ring
  -- generic
  rw [Acoef_insert ha hya1, Acoef_insert hyw hz, Acoef_insert ha hza1, Acoef_insert hzw hy',
    Acoef_insert hay hza1, Acoef_insert hyw hz]
  have := cast_sub_sub_one_ne_zero hz
  have := cast_sub_sub_one_ne_zero hy'
  have := cast_sub_sub_one_ne_zero hya1
  have := cast_sub_sub_one_ne_zero hza1
  field_simp
  ring

end ProperCircularArc
