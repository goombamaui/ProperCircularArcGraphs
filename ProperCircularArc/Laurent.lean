import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order

/-!
# Laurent polynomials in the elementary symmetric functions

The tableau matrices of the paper have entries that are nonnegative rationals and ratios
`e_a / e_{a-1}` of elementary symmetric functions.  We work with formal symbols
`E 1, E 2, …` that are *algebraically independent* and invertible: the ring

  `Lam = ℚ[E_1^{±1}, E_2^{±1}, …]`

of Laurent polynomials, realised as the additive monoid algebra of `ℕ →₀ ℤ`.  The
exponent of `E j` is the value at `j`; the coordinate `0` is never used, and `E 0 = 1`.
-/

noncomputable section

namespace ProperCircularArc

open AddMonoidAlgebra

/-- Laurent polynomials in the formal elementary symmetric functions `E 1, E 2, …`. -/
abbrev Lam := AddMonoidAlgebra ℚ (ℕ →₀ ℤ)

/-- The Laurent monomial `∏ E_j ^ m j`. -/
def mono (m : ℕ →₀ ℤ) : Lam := single m 1

/-- The formal elementary symmetric function `E j` (with `E 0 = 1`). -/
def E (j : ℕ) : Lam := mono (Finsupp.single j (if j = 0 then 0 else 1))

/-- The inverse `E j⁻¹` (with `E 0⁻¹ = 1`). -/
def Einv (j : ℕ) : Lam := mono (Finsupp.single j (if j = 0 then 0 else -1))

/-- The ratio `E a / E (a - 1)` appearing in the deletion matrices `D_k`. -/
def Eratio (a : ℕ) : Lam := E a * Einv (a - 1)

@[simp] lemma E_zero : E 0 = 1 := by
  simp [E, mono, one_def]

@[simp] lemma Einv_zero : Einv 0 = 1 := by
  simp [Einv, mono, one_def]

lemma mono_mul (m m' : ℕ →₀ ℤ) : mono m * mono m' = mono (m + m') := by
  simp [mono, single_mul_single]

lemma mono_zero : mono 0 = 1 := by simp [mono, one_def]

@[simp] lemma E_mul_Einv (j : ℕ) : E j * Einv j = 1 := by
  rw [E, Einv, mono_mul, ← Finsupp.single_add]
  split_ifs <;> simp [mono_zero]

@[simp] lemma Einv_mul_E (j : ℕ) : Einv j * E j = 1 := by
  rw [mul_comm, E_mul_Einv]

lemma E_isUnit (j : ℕ) : IsUnit (E j) := IsUnit.of_mul_eq_one (Einv j) (E_mul_Einv j)

lemma Eratio_mul_inv (a : ℕ) : Eratio a * (E (a - 1) * Einv a) = 1 := by
  rw [Eratio]
  calc E a * Einv (a - 1) * (E (a - 1) * Einv a)
      = (E a * Einv a) * (E (a - 1) * Einv (a - 1)) := by ring
    _ = 1 := by simp

/-! ## Nonnegative coefficients -/

/-- All coefficients are nonnegative rationals. -/
def Nonneg (f : Lam) : Prop := ∀ m, 0 ≤ f.coeff m

lemma Nonneg.zero : Nonneg 0 := fun _ => le_rfl

lemma Nonneg.add {f g : Lam} (hf : Nonneg f) (hg : Nonneg g) : Nonneg (f + g) :=
  fun m => by simpa [coeff_add] using add_nonneg (hf m) (hg m)

lemma Nonneg.mul {f g : Lam} (hf : Nonneg f) (hg : Nonneg g) : Nonneg (f * g) := by
  classical
  intro m
  rw [coeff_mul]
  refine Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => ?_
  dsimp only
  split_ifs
  · exact mul_nonneg (hf m₁) (hg m₂)
  · exact le_rfl

lemma Nonneg.sum {ι : Type*} (s : Finset ι) {f : ι → Lam} (hf : ∀ i ∈ s, Nonneg (f i)) :
    Nonneg (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Nonneg.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

lemma Nonneg.mono (m : ℕ →₀ ℤ) : Nonneg (mono m) := by
  classical
  intro m'
  simp only [ProperCircularArc.mono, coeff_single, Finsupp.single_apply]
  split_ifs <;> norm_num

lemma Nonneg.E (j : ℕ) : Nonneg (E j) := Nonneg.mono _

lemma Nonneg.Einv (j : ℕ) : Nonneg (Einv j) := Nonneg.mono _

lemma Nonneg.Eratio (a : ℕ) : Nonneg (Eratio a) := (Nonneg.E a).mul (Nonneg.Einv _)

lemma Nonneg.ratCast {q : ℚ} (hq : 0 ≤ q) : Nonneg (algebraMap ℚ Lam q) := by
  classical
  intro m
  rw [coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    coeff_single, Finsupp.single_apply]
  split_ifs <;> simp [hq]

lemma Nonneg.one : Nonneg 1 := by
  rw [one_def]
  exact Nonneg.mono 0

lemma Nonneg.smul {q : ℚ} (hq : 0 ≤ q) {f : Lam} (hf : Nonneg f) : Nonneg (q • f) := by
  intro m
  rw [coeff_smul_apply, smul_eq_mul]
  exact mul_nonneg hq (hf m)

end ProperCircularArc
