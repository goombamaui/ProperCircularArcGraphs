import ProperCircularArc.Tableaux

/-!
# Equation `weight-pr` and Hikita's probability formula

The column potential is a shape invariant: a column of height `h` contributes
`((y+1) e_{y+1}/e_y)^h`. `row_potential` identifies this with the paper's product
of `λ_r! e_{λ_r}` over rows. This makes the telescoping argument independent of
how rows of equal length are ordered.
-/

noncomputable section

namespace ProperCircularArc

open Finset

local instance (N : ℕ) : CharZero (KN N) := Algebra.charZero_of_charZero ℚ (KN N)

/-- The probability of a column assignment under Hikita's rule at `q = 1`. -/
def hprob (N : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ)
    (c : Fin n → Fin N) : ℚ :=
  ∏ v : Fin n, if a ≤ (v : ℕ) then
    Acoef ((c v : ℕ) + 1) (nbrCols G c v) / ((c v : ℕ) + 1) else 1

lemma hprob_nonneg {N n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) (c : Fin n → Fin N) :
    0 ≤ hprob N G a c := by
  unfold hprob
  apply Finset.prod_nonneg
  intro v _
  split_ifs
  · exact div_nonneg (Acoef_nonneg _ _) (by positivity)
  · exact zero_le_one

/-- The factor contributed by a box in column `y+1`. -/
def boxFactor (N : ℕ) (y : Fin N) : KN N := ((y : ℕ) + 1) * Erat N y

lemma boxFactor_ne_zero {N : ℕ} (y : Fin N) : boxFactor N y ≠ 0 := by
  unfold boxFactor
  apply mul_ne_zero
  · exact_mod_cast (Nat.succ_ne_zero (y : ℕ))
  · exact Erat_ne_zero y.2

/-- Shape potential in terms of column heights (columns are zero based). -/
def shapePotential (N : ℕ) (h : ℕ → ℕ) : KN N :=
  ∏ y : Fin N, boxFactor N y ^ h y

lemma shapePotential_ne_zero {N : ℕ} (h : ℕ → ℕ) : shapePotential N h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun y _ => pow_ne_zero _ (boxFactor_ne_zero y)

lemma row_telescope {N : ℕ} (r : ℕ) (hr : r ≤ N) :
    (∏ y ∈ range r, (((y + 1 : ℕ) : KN N) * Erat N y)) =
      (r.factorial : KN N) * eK N r := by
  induction r with
  | zero => simp [eK]
  | succ r ih =>
    rw [prod_range_succ, ih (by omega), Nat.factorial_succ, Nat.cast_mul]
    have he : eK N r ≠ 0 := eK_ne_zero (by omega)
    unfold Erat
    field_simp

/-- For rows `rows`, the column potential is exactly `∏ r, r! e_r`. -/
theorem row_potential {N : ℕ} (rows : List ℕ) (hr : ∀ r ∈ rows, r ≤ N) :
    shapePotential N (fun y => (rows.filter (fun r => y < r)).length) =
      (rows.map (fun r => (r.factorial : KN N) * eK N r)).prod := by
  induction rows with
  | nil => simp [shapePotential]
  | cons r rows ih =>
    have hr' : r ≤ N := hr r (by simp)
    have hrows : ∀ s ∈ rows, s ≤ N := fun s hs => hr s (by simp [hs])
    have hcol : shapePotential N (fun y => ((r :: rows).filter (fun s => y < s)).length) =
        (∏ y : Fin N, if (y : ℕ) < r then boxFactor N y else 1) *
        shapePotential N (fun y => (rows.filter (fun s => y < s)).length) := by
      unfold shapePotential
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun y _ => ?_
      by_cases hy : (y : ℕ) < r <;> simp [hy, pow_succ, mul_comm]
    rw [hcol, ih hrows, List.map_cons, List.prod_cons]
    congr 1
    have hp : (∏ y : Fin N, if (y : ℕ) < r then boxFactor N y else 1) =
        ∏ y ∈ range r, (((y + 1 : ℕ) : KN N) * Erat N y) := by
      rw [← Finset.prod_filter]
      exact Finset.prod_bij (fun y _ => (y : ℕ))
        (by intro y hy; simpa using (mem_filter.mp hy).2)
        (by intro _ _ _ _ h; exact Fin.ext h)
        (by intro y hy; exact ⟨⟨y, lt_of_lt_of_le (mem_range.mp hy) hr'⟩,
          by simpa using hy, rfl⟩) (by intro y _; simp [boxFactor])
    rw [hp, row_telescope r hr']

lemma added_potential {N n a : ℕ} (c : Fin n → Fin N) :
    shapePotential N (colH a c n) = shapePotential N (initH a c) *
      ∏ v : Fin n, if a ≤ (v : ℕ) then boxFactor N (c v) else 1 := by
  classical
  unfold shapePotential colH
  simp_rw [pow_add]
  rw [prod_mul_distrib]
  congr 1
  have hc : ∀ y : Fin N, boxFactor N y ^ addH a c n y =
      ∏ v : Fin n, if a ≤ (v : ℕ) ∧ c v = y then boxFactor N y else 1 := by
    intro y
    unfold addH
    rw [← prod_const, prod_filter]
    apply prod_congr rfl
    intro v _
    simp only [Fin.is_lt, true_and, Fin.ext_iff]
  simp_rw [hc]
  rw [prod_comm]
  refine prod_congr rfl fun v _ => ?_
  by_cases hv : a ≤ (v : ℕ)
  · simp [hv, eq_comm]
  · simp [hv]

/-- **Equation `weight-pr`**, including an arbitrary initial tableau `T_j`. -/
theorem weight_pr {N n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) (c : Fin n → Fin N) :
    hwt N G a c = (hprob N G a c : KN N) *
      (shapePotential N (colH a c n) / shapePotential N (initH a c)) := by
  classical
  rw [added_potential]
  have hS := shapePotential_ne_zero (N := N) (initH a c)
  rw [mul_div_cancel_left₀ _ hS]
  unfold hwt hprob
  rw [Rat.cast_prod]
  simp only [apply_ite (fun q : ℚ => (q : KN N)), Rat.cast_one]
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun v _ => ?_
  by_cases hv : a ≤ (v : ℕ)
  · simp only [hv, ite_true, Rat.cast_div, boxFactor]
    have hy : (((c v : ℕ) + 1 : ℕ) : KN N) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  · simp [hv]

/-- Equation `weight-pr` in the paper's row notation, for the initial and final shapes. -/
theorem weight_pr_rows {N n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) (c : Fin n → Fin N)
    (initial final : List ℕ) (hi : ∀ r ∈ initial, r ≤ N) (hf : ∀ r ∈ final, r ≤ N)
    (hci : ∀ y, initH a c y = (initial.filter (fun r => y < r)).length)
    (hcf : ∀ y, colH a c n y = (final.filter (fun r => y < r)).length) :
    hwt N G a c = (hprob N G a c : KN N) *
      ((final.map (fun r => (r.factorial : KN N) * eK N r)).prod /
       (initial.map (fun r => (r.factorial : KN N) * eK N r)).prod) := by
  rw [weight_pr, show colH a c n = _ from funext hcf,
    show initH a c = _ from funext hci, row_potential final hf, row_potential initial hi]

/-- Hikita's theorem in probability form; `row_potential` gives the row notation of the paper. -/
theorem hikita_probability {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsNUIG G) (N : ℕ) :
    algebraMap (Pol N) (KN N) (chromSym N G) =
      ∑ c : Fin n → Fin N, (hprob N G 0 c : KN N) * shapePotential N (colH 0 c n) := by
  rw [hikita_weight G hG N]
  refine sum_congr rfl fun c _ => ?_
  rw [weight_pr]
  have hi : initH 0 c = fun _ => 0 := by funext y; simp [initH]
  simp [hi, shapePotential]

open Classical in
/-- Hikita's probability formula as a sum over genuine tableau builds. -/
theorem hikita_probability_tableaux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsNUIG G) (N : ℕ) :
    algebraMap (Pol N) (KN N) (chromSym N G) =
      ∑ c : Fin n → Fin N, if IsBuild 0 c then
        (hprob N G 0 c : KN N) * shapePotential N (colH 0 c n) else 0 := by
  classical
  rw [hikita_tableaux G hG N]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [weight_pr]
    have hi : initH 0 c = fun _ => 0 := by funext y; simp [initH]
    simp [hi, shapePotential]
  · rfl

open Classical in
/-- Hikita's theorem in exactly the row notation of the paper. A choice of row lengths
is a shape precisely when its column heights agree with those of the built tableau. -/
theorem hikita_probability_rows {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsNUIG G) (N : ℕ) (rows : (Fin n → Fin N) → List ℕ)
    (hbound : ∀ c, IsBuild 0 c → ∀ r ∈ rows c, r ≤ N)
    (hshape : ∀ c, IsBuild 0 c → ∀ y,
      colH 0 c n y = ((rows c).filter (fun r => y < r)).length) :
    algebraMap (Pol N) (KN N) (chromSym N G) =
      ∑ c : Fin n → Fin N, if IsBuild 0 c then
        (hprob N G 0 c : KN N) *
          ((rows c).map (fun r => (r.factorial : KN N) * eK N r)).prod else 0 := by
  classical
  rw [hikita_probability_tableaux G hG N]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · rw [show colH 0 c n = _ from funext (hshape c hc), row_potential _ (hbound c hc)]
  · rfl

end ProperCircularArc
