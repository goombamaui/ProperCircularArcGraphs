import ProperCircularArc.Laurent
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# Power sums in terms of the elementary symmetric functions

The fresh-colour sum `D̂` needs the power sums `p_m = ∑_c x_c^m`.  In the formal model they are
defined from the `E j` by Newton's identities.
-/

noncomputable section

namespace ProperCircularArc

open Finset

/-- The formal power sums `P m`, defined by Newton's identities
`P k = (-1)^(k+1) k E_k - ∑_{0 < i < k} (-1)^i E_i P_{k-i}`. -/
def Pw : ℕ → Lam
  | 0 => 0
  | k + 1 => (-1) ^ (k + 2) * ((k + 1 : ℕ) : Lam) * E (k + 1) -
      ∑ i : Fin (k + 1), if h : 0 < (i : ℕ) then (-1) ^ (i : ℕ) * E i * Pw (k + 1 - i) else 0
termination_by k => k
decreasing_by omega

lemma Pw_succ (k : ℕ) : Pw (k + 1) = (-1) ^ (k + 2) * ((k + 1 : ℕ) : Lam) * E (k + 1) -
    ∑ i ∈ range (k + 1), if 0 < i then (-1) ^ i * E i * Pw (k + 1 - i) else 0 := by
  rw [Pw]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => if 0 < i then (-1) ^ i * E i * Pw (k + 1 - i) else 0)]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

lemma neg_one_pow_sub {a j : ℕ} (h : j + 1 ≤ a) :
    (-1 : Lam) ^ (a - (j + 1)) = (-1) ^ a * (-1) ^ (j + 1) := by
  rw [← pow_add]
  have : a + (j + 1) = a - (j + 1) + 2 * (j + 1) := by omega
  rw [this, pow_add, pow_mul]
  simp

/-- **Newton's identity** in the form used by `D̂ U_1`:
`a E_a = ∑_{j < a} (-1)^j E_{a-1-j} P_{j+1}`. -/
lemma newton (a : ℕ) :
    ((a : ℕ) : Lam) * E a = ∑ j ∈ range a, (-1) ^ j * E (a - 1 - j) * Pw (j + 1) := by
  rcases a with _ | a
  · simp
  rw [← sum_range_reflect]
  have hrefl : ∀ j ∈ range (a + 1), (-1 : Lam) ^ (a + 1 - 1 - j) *
      E (a + 1 - 1 - (a + 1 - 1 - j)) * Pw (a + 1 - 1 - j + 1)
      = (-1) ^ (a - j) * E j * Pw (a + 1 - j) := by
    intro j hj
    rw [mem_range] at hj
    have h1 : a + 1 - 1 - (a + 1 - 1 - j) = j := by omega
    have h2 : a + 1 - 1 - j + 1 = a + 1 - j := by omega
    have h3 : a + 1 - 1 - j = a - j := by omega
    rw [h1, h2, h3]
  rw [sum_congr rfl hrefl, sum_range_succ']
  simp only [E_zero, mul_one, Nat.sub_zero]
  rw [Pw_succ]
  have hsum : ∑ i ∈ range (a + 1), (if 0 < i then (-1 : Lam) ^ i * E i * Pw (a + 1 - i) else 0)
      = ∑ j ∈ range a, (-1) ^ (j + 1) * E (j + 1) * Pw (a + 1 - (j + 1)) := by
    rw [sum_range_succ']
    simp
  rw [hsum]
  have hS : ∑ j ∈ range a, (-1 : Lam) ^ (a - (j + 1)) * E (j + 1) * Pw (a + 1 - (j + 1))
      = (-1) ^ a * ∑ j ∈ range a, (-1) ^ (j + 1) * E (j + 1) * Pw (a + 1 - (j + 1)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [neg_one_pow_sub (by omega)]
    ring
  rw [hS]
  have hpow : ((-1 : Lam) ^ a) * (-1) ^ (a + 2) = 1 := by
    rw [← pow_add, show a + (a + 2) = 2 * (a + 1) by ring, pow_mul]; simp
  set S := ∑ j ∈ range a, (-1 : Lam) ^ (j + 1) * E (j + 1) * Pw (a + 1 - (j + 1))
  push_cast
  linear_combination (-(((a : Lam) + 1) * E (a + 1))) * hpow

end ProperCircularArc
