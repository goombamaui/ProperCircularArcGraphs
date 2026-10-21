import ProperCircularArc.TraceGraph

/-!
# Theorems `pca` and `stanstem` for graphs given by words

* `pca_trace`: for a closed word `w` (a marked natural unit interval graph whose first and last
  `k` vertices are identified), `X_{tr w}(x_1, …, x_N) = tr M_w^{(N)}` for every `N`;
* `pca_epositive`: `X_{tr w}(x_1, …, x_N)` is a polynomial in `e_1, …, e_N` with nonnegative
  coefficients;
* `stanstem_epositive`: the same for the graph of a word from level `0` to level `0`, i.e. any
  natural unit interval graph.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

namespace Word

variable {k : ℕ}

/-- **Theorem `pca`, trace formula**: `X_{tr w}(x_1, …, x_N) = tr M_w^{(N)}`. -/
theorem pca_trace (N : ℕ) (w : Word k k) (hw : TraceOK w) :
    algebraMap (Pol N) (KN N) (chromSym N (trGraph w hw)) = trace (tabMat N w) := by
  rw [trace_tabMat, colMat_eq_map, chromSym_trGraph, trace, trace, map_sum]
  rfl

/-- **Theorem `pca`, `e`-positivity**: `X_{tr w}(x_1, …, x_N)` is a polynomial with nonnegative
coefficients in the elementary symmetric polynomials `e_1, …, e_N`. -/
theorem pca_epositive (N : ℕ) (w : Word k k) (hw : TraceOK w) :
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = chromSym N (trGraph w hw) := by
  obtain ⟨h1, h2⟩ := trace_tabMat_eq_phiL (N := N) w
  exact epos_of_nonneg (chromSym_isSymmetric N _) h2 (by rw [← h1, pca_trace])

/-- For a word from level `0` to level `0` there are no marked vertices, and the colour matrix is
the chromatic symmetric function of its graph. -/
lemma chromSym_graph (N : ℕ) (w : Word 0 0) :
    chromSym N (graph w) = trace (colMatP N w) := by
  classical
  have hu : (univ : Finset (Inj N 0)) = {Function.Embedding.ofIsEmpty} := by
    ext x
    simp only [mem_univ, mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [trace, hu, sum_singleton, diag_apply, colMatP_eq_colorSum, colorSum, chromSym]
  refine Fintype.sum_congr _ _ fun κ => ?_
  have hc : (IsProper (graph w) κ ∧ (∀ r : Fin 0, κ (mark w r) = Function.Embedding.ofIsEmpty r) ∧
      (∀ r : Fin 0, κ (inp w r) = Function.Embedding.ofIsEmpty r)) ↔ IsProper (graph w) κ := by
    simp
  have hp : ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp w)), (X (κ v) : Pol N) =
      ∏ v, X (κ v) := by
    congr 1; ext v; simp [Set.range_eq_empty]
  simp only [hc, hp]

/-- **Theorem `stanstem`**: the chromatic symmetric function of the graph of a word from level
`0` to level `0` equals the `1 × 1` tableau matrix and is `e`-positive. -/
theorem stanstem_epositive (N : ℕ) (w : Word 0 0) :
    algebraMap (Pol N) (KN N) (chromSym N (graph w)) = trace (tabMat N w) ∧
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = chromSym N (graph w) := by
  have htr : algebraMap (Pol N) (KN N) (chromSym N (graph w)) = trace (tabMat N w) := by
    rw [trace_tabMat, colMat_eq_map, chromSym_graph, trace, trace, map_sum]
    rfl
  refine ⟨htr, ?_⟩
  obtain ⟨h1, h2⟩ := trace_tabMat_eq_phiL (N := N) w
  exact epos_of_nonneg (chromSym_isSymmetric N _) h2 (by rw [← h1, htr])

end Word

end ProperCircularArc
