import ProperCircularArc.ExamplesCertificates
import ProperCircularArc.Gluing
import ProperCircularArc.Infinite
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# The worked examples

The path, the six-vertex proper circular arc graph, and the seven-vertex NUIG
are checked as actual graphs. Their formulas hold for every finite alphabet.
The graph-word identifications connect these calculations to the tableau matrices.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProperCircularArc.Examples

open MvPolynomial Finset Matrix

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev e (N k : ℕ) : Pol N := esymm (Fin N) ℚ k

lemma p_eq (N k : ℕ) : p N k = psum (Fin N) ℚ k := rfl

lemma power_1 (N : ℕ) : p N 1 = e N 1 := by simp [p, psum, esymm_one]

lemma power_2 (N : ℕ) : p N 2 = e N 1 ^ 2 - 2 * e N 2 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 2 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1] at h
  exact h.trans (by ring)

lemma power_3 (N : ℕ) : p N 3 = e N 1 ^ 3 - 3 * e N 1 * e N 2 + 3 * e N 3 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 3 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1, power_2] at h
  exact h.trans (by ring)

lemma power_4 (N : ℕ) : p N 4 = e N 1 ^ 4 - 4 * e N 1 ^ 2 * e N 2 + 4 * e N 1 * e N 3 + 2 * e N 2 ^ 2 - 4 * e N 4 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 4 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1, power_2, power_3] at h
  exact h.trans (by ring)

lemma power_5 (N : ℕ) : p N 5 = e N 1 ^ 5 - 5 * e N 1 ^ 3 * e N 2 + 5 * e N 1 ^ 2 * e N 3 + 5 * e N 1 * e N 2 ^ 2 - 5 * e N 1 * e N 4 - 5 * e N 2 * e N 3 + 5 * e N 5 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 5 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1, power_2, power_3, power_4] at h
  exact h.trans (by ring)

lemma power_6 (N : ℕ) : p N 6 = e N 1 ^ 6 - 6 * e N 1 ^ 4 * e N 2 + 6 * e N 1 ^ 3 * e N 3 + 9 * e N 1 ^ 2 * e N 2 ^ 2 - 6 * e N 1 ^ 2 * e N 4 - 12 * e N 1 * e N 2 * e N 3 + 6 * e N 1 * e N 5 - 2 * e N 2 ^ 3 + 6 * e N 2 * e N 4 + 3 * e N 3 ^ 2 - 6 * e N 6 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 6 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1, power_2, power_3, power_4, power_5] at h
  exact h.trans (by ring)

lemma power_7 (N : ℕ) : p N 7 = e N 1 ^ 7 - 7 * e N 1 ^ 5 * e N 2 + 7 * e N 1 ^ 4 * e N 3 + 14 * e N 1 ^ 3 * e N 2 ^ 2 - 7 * e N 1 ^ 3 * e N 4 - 21 * e N 1 ^ 2 * e N 2 * e N 3 + 7 * e N 1 ^ 2 * e N 5 - 7 * e N 1 * e N 2 ^ 3 + 14 * e N 1 * e N 2 * e N 4 + 7 * e N 1 * e N 3 ^ 2 - 7 * e N 1 * e N 6 + 7 * e N 2 ^ 2 * e N 3 - 7 * e N 2 * e N 5 - 7 * e N 3 * e N 4 + 7 * e N 7 := by
  have h := psum_eq_mul_esymm_sub_sum (Fin N) ℚ 7 (by decide)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Set.mem_Ioo, false_and, true_and, and_false, ite_true, ite_false] at h
  simp only [← p_eq] at h
  simp only [power_1, power_2, power_3, power_4, power_5, power_6] at h
  exact h.trans (by ring)

/-- An edge set, with both orientations allowed in the adjacency relation. -/
def edgeGraph {n : ℕ} (E : Finset (Fin n × Fin n)) (hE : ∀ v, (v, v) ∉ E) :
    SimpleGraph (Fin n) where
  Adj u v := (u, v) ∈ E ∨ (v, u) ∈ E
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => h.elim (hE v) (hE v)⟩

abbrev path3Edges : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 2)}
abbrev path2Edges : Finset (Fin 2 × Fin 2) := {(0, 1)}
abbrev sixEdges : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 4), (4, 5)}
abbrev sevenEdges : Finset (Fin 7 × Fin 7) :=
  {(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6)}

def path3 : SimpleGraph (Fin 3) := edgeGraph path3Edges (by decide)
def path2 : SimpleGraph (Fin 2) := edgeGraph path2Edges (by decide)
def six : SimpleGraph (Fin 6) := edgeGraph sixEdges (by decide)
def seven : SimpleGraph (Fin 7) := edgeGraph sevenEdges (by decide)

/-- Example `p3`. -/
theorem path3_csf (N : ℕ) : chromSym N path3 = e N 1 * e N 2 + 3 * e N 3 := by
  rw [chromSym_eq_weightedCSF N path3 path3Edges (fun _ _ => Iff.rfl)]
  change weightedCSF N ![1, 1, 1] path3Edges = _
  rw [path3_power, power_1, power_2, power_3]
  ring

/-- Example `pca-formula`: the trace of the marked path is `P₂`. -/
theorem path2_csf (N : ℕ) : chromSym N path2 = 2 * e N 2 := by
  rw [chromSym_eq_weightedCSF N path2 path2Edges (fun _ _ => Iff.rfl)]
  change weightedCSF N ![1, 1] path2Edges = _
  rw [path2_power, power_1, power_2]
  ring

/-- Example `pca`, in every alphabet (including `N < 6`). -/
theorem six_csf (N : ℕ) : chromSym N six =
    16 * e N 1 * e N 5 + 20 * e N 2 * e N 4 + 12 * e N 3 ^ 2 + 84 * e N 6 := by
  rw [chromSym_eq_weightedCSF N six sixEdges (fun _ _ => Iff.rfl)]
  change weightedCSF N ![1, 1, 1, 1, 1, 1] sixEdges = _
  rw [six_power, power_1, power_2, power_3, power_4, power_5, power_6]
  ring

/-- Example `stanstem`, in every alphabet. -/
theorem seven_csf (N : ℕ) : chromSym N seven =
    8 * e N 1 * e N 3 ^ 2 + 88 * e N 3 * e N 4 + 24 * e N 2 * e N 5 +
      40 * e N 1 * e N 6 + 56 * e N 7 := by
  rw [chromSym_eq_weightedCSF N seven sevenEdges (fun _ _ => Iff.rfl)]
  change weightedCSF N ![1, 1, 1, 1, 1, 1, 1] sevenEdges = _
  rw [seven_power, power_1, power_2, power_3, power_4, power_5, power_6, power_7]
  ring

/-- The marked path `(P₃, (3), (1))`, later operations outermost. -/
def pathWord : Word 1 1 := Word.nil.M.D.M.D

/-- The eight-vertex NUIG unrolled in Example `pca`. -/
def sixWord : Word 2 2 := Word.nil.M.D.D.M.D.M.D.M.D.M.M.D

/-- The seven-vertex word displayed in Example `stanstem`. -/
def sevenWord : Word 0 0 := Word.nil.M.M.M.D.D.M.D.M.M.D.M.D.D.D

instance {n : ℕ} (E : Finset (Fin n × Fin n)) (hE) :
    DecidableRel (edgeGraph E hE).Adj := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ E ∨ (v, u) ∈ E))

instance {n k : ℕ} (hk : k ≤ n) (G : SimpleGraph (Fin (n + k))) [DecidableRel G.Adj] :
    DecidableRel (cycTrace hk G).Adj := fun p q =>
  inferInstanceAs (Decidable (p ≠ q ∧ ∃ u v, piN hk u = p ∧ piN hk v = q ∧ G.Adj u v))

lemma pathWord_graph : Word.graph pathWord = path3 := by
  have h : ∀ u v : Fin 3, (Word.graph pathWord).Adj u v ↔ path3.Adj u v := by
    unfold path3
    decide +kernel
  ext u v
  exact h u v

lemma sevenWord_graph : Word.graph sevenWord = seven := by
  have h : ∀ u v : Fin 7, (Word.graph sevenWord).Adj u v ↔ seven.Adj u v := by
    unfold seven
    decide +kernel
  ext u v
  exact h u v

lemma sixWord_trace : cycTrace (n := 6) (k := 2) (by decide) (Word.graph sixWord) = six := by
  have h : ∀ u v : Fin 6,
      (cycTrace (n := 6) (k := 2) (by decide) (Word.graph sixWord)).Adj u v ↔ six.Adj u v := by
    unfold six
    decide +kernel
  ext u v
  exact h u v

/-- The trace of the unrolled six-vertex example gives its stated tableau formula. -/
theorem six_tableau (N : ℕ) : trace (Word.tabMat N sixWord) = algebraMap (Pol N) (KN N)
    (16 * e N 1 * e N 5 + 20 * e N 2 * e N 4 + 12 * e N 3 ^ 2 + 84 * e N 6) := by
  have hi : Word.inp sixWord = Fin.castLE (by decide : 2 ≤ 8) := by
    funext r; fin_cases r <;> rfl
  have ho : Word.mark sixWord = Fin.natAdd 6 := by
    funext r; fin_cases r <;> rfl
  have hloop : ∀ r : Fin 2, ¬(Word.graph sixWord).Adj
      (Fin.natAdd 6 r) (Fin.castLE (by decide : 2 ≤ 8) r) := by decide +kernel
  have h := pca_formula (n := 6) (k := 2) (Word.graph sixWord) (Word.graph_isNUIG sixWord)
    (by decide)
    (by decide +kernel) (by decide +kernel)
    (by intro r hr; exact hloop ⟨r, hr⟩) N
  rw [sixWord_trace, six_csf N] at h
  rw [← Word.hikMat_eq_tabMat, Word.trace_hikMat, hi, ho]
  exact h.symm

/-- The seven-vertex matrix product evaluates to the paper's polynomial. -/
theorem seven_tableau (N : ℕ) :
    trace (Word.tabMat N sevenWord) = algebraMap (Pol N) (KN N)
      (8 * e N 1 * e N 3 ^ 2 + 88 * e N 3 * e N 4 + 24 * e N 2 * e N 5 +
        40 * e N 1 * e N 6 + 56 * e N 7) := by
  rw [← (Word.stanstem_epositive N sevenWord).1, sevenWord_graph]
  exact congrArg (algebraMap (Pol N) (KN N)) (seven_csf N)

end ProperCircularArc.Examples
