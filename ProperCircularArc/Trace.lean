import ProperCircularArc.Invertible
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Words in `M̂`, `D̂` and the trace formula

A marked natural unit interval graph is built from its inputs by a word in the elementary marked
cliques (Lemma `word`).  We record words with the *last* letter outermost, so that the colour
matrix of `M̂ w` is `M̂ · (colour matrix of w)`, exactly as in `M̂_\bG = X̂_1 ⋯ X̂_m`.
-/

noncomputable section

namespace ProperCircularArc

open Matrix

/-- Words from level `a` to level `b` in the generators `M̂_k` and `D̂_k`. -/
inductive Word (a : ℕ) : ℕ → Type
  | nil : Word a a
  /-- attach a new vertex adjacent to the `b` marked vertices -/
  | M {b : ℕ} : Word a b → Word a (b + 1)
  /-- forget the oldest marked vertex -/
  | D {b : ℕ} : Word a (b + 1) → Word a b

namespace Word

variable {N : ℕ}

/-- The colour matrix `M̂_w` of a word, with `N` colours. -/
def colMat (N : ℕ) {a : ℕ} : {b : ℕ} → Word a b → Matrix (Inj N b) (Inj N a) (KN N)
  | _, nil => 1
  | _, M (b := b) w => Mmat N b * colMat N w
  | _, D (b := b) w => Dmat N b * colMat N w

/-- The tableau matrix `M_w^{(N)}` of a word. -/
def tabMat (N : ℕ) {a : ℕ} : {b : ℕ} → Word a b → Matrix (Inj N b) (Inj N a) (KN N)
  | _, nil => 1
  | _, M (b := b) w => MT N b * tabMat N w
  | _, D (b := b) w => DT N b * tabMat N w

/-- **Theorem `main`, applied to a word**: `U_b^{(N)} M_w^{(N)} = M̂_w U_a^{(N)}`. -/
theorem UN_tabMat {a : ℕ} : ∀ {b : ℕ} (w : Word a b), UN N b * tabMat N w = colMat N w * UN N a
  | _, nil => by simp [tabMat, colMat]
  | _, M (b := b) w => by
    rw [tabMat, colMat, ← Matrix.mul_assoc, UN_M, Matrix.mul_assoc, UN_tabMat w, Matrix.mul_assoc]
  | _, D (b := b) w => by
    rw [tabMat, colMat, ← Matrix.mul_assoc, ← UN_D, Matrix.mul_assoc, UN_tabMat w,
      Matrix.mul_assoc]

/-- **The trace formula**: the tableau matrix and the colour matrix of a closed word have the
same trace, for any number `N` of colours. -/
theorem trace_tabMat {k : ℕ} (w : Word k k) : trace (tabMat N w) = trace (colMat N w) := by
  by_cases hk : k ≤ N
  · have hU : IsUnit (UN N k) := mulVec_surjective_iff_isUnit.1 (UN_surjective N k hk)
    obtain ⟨V, hV1, hV2⟩ : ∃ V, V * UN N k = 1 ∧ UN N k * V = 1 := by
      refine ⟨(UN N k)⁻¹, Matrix.nonsing_inv_mul _ ?_, Matrix.mul_nonsing_inv _ ?_⟩ <;>
        exact (Matrix.isUnit_iff_isUnit_det _).1 hU
    calc trace (tabMat N w) = trace (V * UN N k * tabMat N w) := by rw [hV1, Matrix.one_mul]
      _ = trace (V * (colMat N w * UN N k)) := by rw [Matrix.mul_assoc, UN_tabMat]
      _ = trace (colMat N w * UN N k * V) := by rw [trace_mul_comm]
      _ = trace (colMat N w) := by rw [Matrix.mul_assoc, hV2, Matrix.mul_one]
  · haveI := isEmpty_Inj (N := N) (k := k) (by omega)
    simp [trace]

end Word

end ProperCircularArc
