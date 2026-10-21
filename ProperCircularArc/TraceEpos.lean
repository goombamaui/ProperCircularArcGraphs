import ProperCircularArc.Positivity

/-!
# The trace of a tableau word is `e`-positive

The finite tableau matrices are specialisations of matrices over the Laurent polynomials
`LN N` with nonnegative coefficients.
-/

noncomputable section

namespace ProperCircularArc

open Finset Matrix AddMonoidAlgebra

/-- `E_a` in `LN N` (and `1` for `a = 0`). -/
def EL (N a : ℕ) : LN N :=
  if h : 1 ≤ a ∧ a ≤ N then single (Finsupp.single ⟨a - 1, by omega⟩ 1) 1 else 1

/-- `E_a⁻¹` in `LN N`. -/
def ELinv (N a : ℕ) : LN N :=
  if h : 1 ≤ a ∧ a ≤ N then single (Finsupp.single ⟨a - 1, by omega⟩ (-1)) 1 else 1

lemma phiL_EL {N a : ℕ} (ha : a ≤ N) : phiL N (EL N a) = eK N a := by
  unfold EL
  split_ifs with h
  · rw [phiL_single, one_smul, Finsupp.prod_single_index (by simp), zpow_one]
    congr 1; simp; omega
  · have : a = 0 := by omega
    subst this; simp

lemma phiL_ELinv {N a : ℕ} (ha : a ≤ N) : phiL N (ELinv N a) = (eK N a)⁻¹ := by
  unfold ELinv
  split_ifs with h
  · rw [phiL_single, one_smul, Finsupp.prod_single_index (by simp), zpow_neg, zpow_one]
    congr 2; simp; omega
  · have : a = 0 := by omega
    subst this; simp

lemma NonnegL.EL (N a : ℕ) : NonnegL (EL N a) := by
  unfold ProperCircularArc.EL; split_ifs
  · exact NonnegL.single _ zero_le_one
  · exact NonnegL.one

lemma NonnegL.ELinv (N a : ℕ) : NonnegL (ELinv N a) := by
  unfold ProperCircularArc.ELinv; split_ifs
  · exact NonnegL.single _ zero_le_one
  · exact NonnegL.one

/-- The Laurent version of `M_k^{(N)}`. -/
def MTL (N k : ℕ) : Matrix (Inj N (k + 1)) (Inj N k) (LN N) :=
  fun j i => if embInit j = i then
    algebraMap ℚ (LN N) (Acoef ((j (Fin.last k) : ℕ) + 1) (entries (shift i))) else 0

/-- The Laurent version of `D_{k+1}`. -/
def DTL (N k : ℕ) : Matrix (Inj N k) (Inj N (k + 1)) (LN N) :=
  fun i j => if embTail j = i then EL N ((j 0 : ℕ) + 1) * ELinv N (j 0 : ℕ) else 0

lemma MTL_map (N k : ℕ) : (MTL N k).map (phiL N) = MT N k := by
  ext j i
  simp only [map_apply, MTL, MT]
  split_ifs
  · rw [AlgHom.commutes, eq_ratCast]
  · rw [map_zero]

lemma DTL_map (N k : ℕ) : (DTL N k).map (phiL N) = DT N k := by
  ext i j
  simp only [map_apply, DTL, DT]
  split_ifs
  · rw [map_mul, phiL_EL (by have := (j 0).2; omega), phiL_ELinv (by have := (j 0).2; omega)]
  · rw [map_zero]

namespace Word

/-- The Laurent version of the tableau matrix of a word. -/
def tabMatL (N : ℕ) {a : ℕ} : {b : ℕ} → Word a b → Matrix (Inj N b) (Inj N a) (LN N)
  | _, nil => 1
  | _, M (b := b) w => MTL N b * tabMatL N w
  | _, D (b := b) w => DTL N b * tabMatL N w

lemma map_mul_phiL {N l m n : ℕ} (A : Matrix (Inj N l) (Inj N m) (LN N))
    (B : Matrix (Inj N m) (Inj N n) (LN N)) :
    (A * B).map (phiL N) = A.map (phiL N) * B.map (phiL N) :=
  Matrix.map_mul (f := (phiL N).toRingHom)

lemma tabMatL_map {N a : ℕ} : ∀ {b : ℕ} (w : Word a b),
    (tabMatL N w).map (phiL N) = tabMat N w
  | _, nil => by simp [tabMatL, tabMat, Matrix.map_one]
  | _, M w => by
    rw [tabMatL, tabMat, map_mul_phiL, tabMatL_map w, MTL_map]
  | _, D w => by
    rw [tabMatL, tabMat, map_mul_phiL, tabMatL_map w, DTL_map]

lemma tabMatL_nonneg {N a : ℕ} : ∀ {b : ℕ} (w : Word a b) (i j), NonnegL (tabMatL N w i j)
  | _, nil, i, j => by
    simp only [tabMatL, one_apply]
    split_ifs
    · exact NonnegL.one
    · exact NonnegL.zero
  | _, M w, i, j => by
    rw [tabMatL, Matrix.mul_apply]
    refine NonnegL.sum _ fun l _ => NonnegL.mul ?_ (tabMatL_nonneg w l j)
    simp only [MTL]
    split_ifs
    · exact NonnegL.ratCast (Acoef_nonneg _ _)
    · exact NonnegL.zero
  | _, D w, i, j => by
    rw [tabMatL, Matrix.mul_apply]
    refine NonnegL.sum _ fun l _ => NonnegL.mul ?_ (tabMatL_nonneg w l j)
    simp only [DTL]
    split_ifs
    · exact (NonnegL.EL _ _).mul (NonnegL.ELinv _ _)
    · exact NonnegL.zero

/-- The trace of the tableau matrix of a closed word is the specialisation of a Laurent
polynomial with nonnegative coefficients. -/
theorem trace_tabMat_eq_phiL {N k : ℕ} (w : Word k k) :
    trace (tabMat N w) = phiL N (trace (tabMatL N w)) ∧ NonnegL (trace (tabMatL N w)) := by
  refine ⟨?_, NonnegL.sum _ fun i _ => tabMatL_nonneg w i i⟩
  rw [← tabMatL_map w, trace, trace, map_sum]
  rfl

end Word

end ProperCircularArc
