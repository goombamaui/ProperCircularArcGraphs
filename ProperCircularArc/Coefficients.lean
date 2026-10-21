import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The coefficients `A(y ∣ σ)`

For a finite set `s` of positive integers (the columns of the marked boxes), the possible
columns for a new box are `T(s) = {y ∉ s : y = 1 or y - 1 ∈ s}`, and the coefficient of the
tableau matrix `M_k` is

  `A(1 ∣ s) = ∏_{t ∈ s} (t - 1) / t`,
  `A(t + 1 ∣ s) = (t + 1)/t · ∏_{t' ∈ s, t' ≠ t} (t - t' + 1)/(t - t')`,

and `A(y ∣ s) = 0` for `y ∉ T(s)`.  Both cases are the single product formula
`A(y ∣ s) = c(y) · ∏_{t ∈ s, t ≠ y - 1} (y - t)/(y - 1 - t)` with `c(1) = 1` and
`c(y) = y/(y - 1)` otherwise.  The coefficient depends only on the *set* of entries of `σ`.
-/

namespace ProperCircularArc

open Finset

/-- The admissible new columns `T(s)`. -/
def Tset (s : Finset ℕ) : Finset ℕ := (insert 1 (s.image (· + 1))) \ s

/-- The starts of runs `Z(w) = {z ∈ w : z ≥ 2, z - 1 ∉ w}`. -/
def Zset (s : Finset ℕ) : Finset ℕ := s.filter (fun z => 2 ≤ z ∧ z - 1 ∉ s)

/-- The prefactor `c(y)`. -/
def cfac (y : ℕ) : ℚ := if y = 1 then 1 else (y : ℚ) / ((y : ℚ) - 1)

/-- The coefficient `A(y ∣ s)` of the tableau matrix `M_k`. -/
def Acoef (y : ℕ) (s : Finset ℕ) : ℚ :=
  if y ∈ Tset s then cfac y * ∏ t ∈ s.erase (y - 1), ((y : ℚ) - t) / ((y : ℚ) - 1 - t) else 0

lemma mem_Tset {s : Finset ℕ} {y : ℕ} : y ∈ Tset s ↔ y ∉ s ∧ (y = 1 ∨ (1 ≤ y ∧ y - 1 ∈ s)) := by
  unfold Tset
  simp only [mem_sdiff, mem_insert, mem_image]
  constructor
  · rintro ⟨h | ⟨t, ht, rfl⟩, hy⟩
    · exact ⟨hy, Or.inl h⟩
    · exact ⟨hy, Or.inr ⟨by omega, by simpa using ht⟩⟩
  · rintro ⟨hy, h | ⟨h1, h2⟩⟩
    · exact ⟨Or.inl h, hy⟩
    · exact ⟨Or.inr ⟨y - 1, h2, by omega⟩, hy⟩

lemma mem_Zset {s : Finset ℕ} {z : ℕ} : z ∈ Zset s ↔ z ∈ s ∧ 2 ≤ z ∧ z - 1 ∉ s := by
  simp [Zset]

lemma not_mem_of_mem_Tset {s : Finset ℕ} {y : ℕ} (h : y ∈ Tset s) : y ∉ s :=
  (mem_Tset.1 h).1

lemma pos_of_mem_Tset {s : Finset ℕ} {y : ℕ} (h : y ∈ Tset s) : 1 ≤ y := by
  rcases (mem_Tset.1 h).2 with h | h <;> omega

lemma Zset_subset (s : Finset ℕ) : Zset s ⊆ s := filter_subset _ _

lemma disjoint_Tset_Zset (s : Finset ℕ) : Disjoint (Tset s) (Zset s) := by
  rw [Finset.disjoint_left]
  intro y hT hZ
  exact (mem_Tset.1 hT).1 (Zset_subset s hZ)

@[simp] lemma Acoef_of_not_mem {y : ℕ} {s : Finset ℕ} (h : y ∉ Tset s) : Acoef y s = 0 := by
  simp [Acoef, h]

lemma Acoef_of_mem {y : ℕ} {s : Finset ℕ} (h : y ∈ Tset s) :
    Acoef y s = cfac y * ∏ t ∈ s.erase (y - 1), ((y : ℚ) - t) / ((y : ℚ) - 1 - t) := by
  simp [Acoef, h]

lemma Acoef_eq_zero_of_mem {y : ℕ} {s : Finset ℕ} (h : y ∈ s) : Acoef y s = 0 :=
  Acoef_of_not_mem fun hT => (mem_Tset.1 hT).1 h

lemma Acoef_ne_zero {y : ℕ} {s : Finset ℕ} (h : y ∈ Tset s) : Acoef y s ≠ 0 := by
  rw [Acoef_of_mem h]
  have hy := pos_of_mem_Tset h
  refine mul_ne_zero ?_ (prod_ne_zero_iff.2 fun t ht => ?_)
  · unfold cfac
    split_ifs with h1
    · norm_num
    · have : (2 : ℚ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
      exact div_ne_zero (by positivity) (by linarith)
  · have hts : t ∈ s := (mem_erase.1 ht).2
    have hty : t ≠ y - 1 := (mem_erase.1 ht).1
    have hyt : t ≠ y := fun e => (mem_Tset.1 h).1 (e ▸ hts)
    refine div_ne_zero (sub_ne_zero.2 ?_) ?_
    · exact_mod_cast hyt.symm
    · intro e
      apply hty
      have : (t : ℚ) = (y : ℚ) - 1 := by linarith
      have : ((t + 1 : ℕ) : ℚ) = y := by push_cast; linarith
      have := Nat.cast_injective this
      omega

/-- **Equation (ratio)**: inserting a new column `a` multiplies `A(y ∣ ·)` by
`(y - a)/(y - a - 1)` for every `y ≠ a + 1`. -/
lemma Acoef_insert {a y : ℕ} {s : Finset ℕ} (ha : a ∉ s) (hy : y ≠ a + 1) :
    Acoef y (insert a s) = ((y : ℚ) - a) / ((y : ℚ) - a - 1) * Acoef y s := by
  by_cases hya : y = a
  · subst hya
    rw [Acoef_eq_zero_of_mem (mem_insert_self _ _)]
    simp
  have hT : y ∈ Tset (insert a s) ↔ y ∈ Tset s := by
    simp only [mem_Tset, mem_insert]
    constructor
    · rintro ⟨h1, h2 | ⟨h2, h3 | h3⟩⟩
      · exact ⟨fun h => h1 (Or.inr h), Or.inl h2⟩
      · omega
      · exact ⟨fun h => h1 (Or.inr h), Or.inr ⟨h2, h3⟩⟩
    · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact ⟨by rintro (h | h) <;> [exact hya h; exact h1 h], Or.inl h2⟩
      · exact ⟨by rintro (h | h) <;> [exact hya h; exact h1 h], Or.inr ⟨h2, Or.inr h3⟩⟩
  by_cases hmem : y ∈ Tset s
  · have hmem' : y ∈ Tset (insert a s) := hT.2 hmem
    rw [Acoef_of_mem hmem, Acoef_of_mem hmem']
    have hay : a ≠ y - 1 := by
      have := pos_of_mem_Tset hmem
      omega
    rw [erase_insert_of_ne hay, prod_insert (fun h => ha (mem_erase.1 h).2)]
    ring
  · rw [Acoef_of_not_mem hmem, Acoef_of_not_mem (fun h => hmem (hT.1 h))]
    simp

/-- The value of `A(a + 1 ∣ s)` when `a ∉ s` and `a ≥ 1`: it vanishes. -/
lemma Acoef_succ_of_not_mem {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) (ha1 : 1 ≤ a) :
    Acoef (a + 1) s = 0 := by
  apply Acoef_of_not_mem
  rw [mem_Tset]
  rintro ⟨_, h | ⟨_, h⟩⟩
  · omega
  · simp at h
    exact ha h

/-! ## Counting: `|T(w)| = |Z(w)| + 1` -/

private lemma sum_indicator_succ (A : Finset ℕ) (n : ℕ) (hA : ∀ y ∈ A, 1 ≤ y ∧ y ≤ n) :
    ∑ i ∈ range n, (if i + 1 ∈ A then (1 : ℤ) else 0) = A.card := by
  have himg : ∑ i ∈ range n, (if i + 1 ∈ A then (1 : ℤ) else 0)
      = ∑ j ∈ (range n).image (· + 1), (if j ∈ A then (1 : ℤ) else 0) := by
    rw [sum_image (fun a _ b _ h => by simpa using h)]
  rw [himg, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext y
  simp only [mem_inter, mem_image, mem_range]
  constructor
  · exact fun h => h.2
  · intro hy
    refine ⟨⟨y - 1, ?_, ?_⟩, hy⟩ <;> have := hA y hy <;> omega

/-- `|T(s)| = |Z(s)| + 1` for every finite set of positive integers. -/
lemma card_Tset (s : Finset ℕ) (h0 : 0 ∉ s) : (Tset s).card = (Zset s).card + 1 := by
  set n := s.sup id + 1 with hn
  have hs : ∀ t ∈ s, t < n := fun t ht => Nat.lt_succ_of_le (le_sup (f := id) ht)
  let f : ℕ → ℤ := fun j => if j = 0 ∨ j ∈ s then 1 else 0
  have key : ∀ i, (if i + 1 ∈ Tset s then (1 : ℤ) else 0) - (if i + 1 ∈ Zset s then 1 else 0)
      = f i - f (i + 1) := by
    intro i
    simp only [f, mem_Tset, mem_Zset]
    by_cases hi : i ∈ s <;> by_cases hi1 : i + 1 ∈ s <;> by_cases hz : i = 0 <;>
      simp_all
  have hT : ((Tset s).card : ℤ) = ∑ i ∈ range n, if i + 1 ∈ Tset s then 1 else 0 := by
    rw [sum_indicator_succ]
    intro y hy
    rcases mem_Tset.1 hy with ⟨_, h | ⟨h1, h2⟩⟩
    · omega
    · have := hs _ h2; omega
  have hZ : ((Zset s).card : ℤ) = ∑ i ∈ range n, if i + 1 ∈ Zset s then 1 else 0 := by
    rw [sum_indicator_succ]
    intro y hy
    have := mem_Zset.1 hy
    have := hs _ this.1
    omega
  have tel : ∑ i ∈ range n, (f i - f (i + 1)) = f 0 - f n := sum_range_sub' f n
  have hf0 : f 0 = 1 := by simp [f]
  have hfn : f n = 0 := by
    have hn' : ¬(n = 0 ∨ n ∈ s) := by
      rintro (h | h)
      · omega
      · exact absurd (hs _ h) (lt_irrefl _)
    show (if n = 0 ∨ n ∈ s then (1 : ℤ) else 0) = 0
    exact (ite_eq_right_iff.2 fun h => absurd h hn')
  have : ((Tset s).card : ℤ) - (Zset s).card = 1 := by
    rw [hT, hZ, ← sum_sub_distrib]
    simp_rw [key]
    rw [tel, hf0, hfn]; norm_num
  omega

/-- The entries of the tableau matrices `M_k` are nonnegative. -/
lemma Acoef_nonneg (y : ℕ) (s : Finset ℕ) : 0 ≤ Acoef y s := by
  unfold Acoef
  split_ifs with h
  · have hy := pos_of_mem_Tset h
    have hys := not_mem_of_mem_Tset h
    refine mul_nonneg ?_ (prod_nonneg fun t ht => ?_)
    · unfold cfac
      split_ifs with h1
      · norm_num
      · have : (2 : ℚ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
        exact div_nonneg (by linarith) (by linarith)
    · have hts : t ∈ s := (mem_erase.1 ht).2
      have hty : t ≠ y - 1 := (mem_erase.1 ht).1
      have hne : t ≠ y := fun e => hys (e ▸ hts)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : t + 1 < y := by omega
        have h1 : (t : ℚ) + 1 < y := by exact_mod_cast this
        exact div_nonneg (by linarith) (by linarith)
      · have h1 : (y : ℚ) < t := by exact_mod_cast hgt
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · exact le_rfl

end ProperCircularArc
