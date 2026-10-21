import ProperCircularArc.TableauIdentities
import ProperCircularArc.Block
import ProperCircularArc.Rank
import ProperCircularArc.PowerSum
import Mathlib.Tactic.LinearCombination

/-!
# Construction of the change of basis `U_k`

At level `1` the paper gives `U_1 b_a = (1/(a e_{a-1})) ∑_c x_c e_{a-1}(x \ x_c) b̂_c`; in the
symbolic model this is `G_a(y) = (1/(a E_{a-1})) ∑_{j < a} E_{a-1-j} (-y)^j`, because
`e_{a-1}(x \ x_c) = ∑_j (-x_c)^j e_{a-1-j}`.

For `k ≥ 2` the columns are defined by induction on the rank, solving the block system for
`y ∈ T(w)` and the free equation for the other `y`.
-/

noncomputable section

namespace ProperCircularArc

open Finset MvPolynomial

/-! ## Level one -/

/-- `U_1 b_a` in the symbolic model. -/
def U1fn (a : ℕ) : CV Lam 1 :=
  if a = 0 then 0 else
    (qc (1 / (a : ℚ)) * Einv (a - 1)) • ∑ j ∈ range a, C (E (a - 1 - j)) * (-X 0) ^ j

lemma U1fn_one : U1fn 1 = 1 := by
  simp [U1fn]

lemma smul_eq_C_mul' {n : ℕ} (c : Lam) (G : CV Lam n) : c • G = C c * G := smul_eq_C_mul G c

lemma rot_zero_eq : (rot 0 : Fin 1 → Fin 1) = id := by
  funext i; exact Fin.ext (by omega)

lemma Rh_zero (G : CV Lam 1) : Rh 0 G = X 0 * G := by
  rw [Rh_apply, rot_zero_eq, rename_id_apply]
  rfl

/-- `R̂_1 U_1 = U_1 R_1` on `b_a`, in polynomial form. -/
lemma U1fn_R (a : ℕ) (ha : 1 ≤ a) :
    X 0 * U1fn a = Eratio a • (qc (1 / (a : ℚ)) • U1fn 1 -
      qc (((a : ℚ) + 1) / a) • U1fn (a + 1)) := by
  have ha0 : a ≠ 0 := by omega
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have ha1q : (a : ℚ) + 1 ≠ 0 := by positivity
  rw [U1fn_one, U1fn, if_neg ha0, U1fn, if_neg (by omega), Nat.add_sub_cancel]
  rw [sum_range_succ', Nat.sub_zero, pow_zero, mul_one]
  simp only [smul_eq_C_mul', Eratio]
  have hE : ∀ j ∈ range a, C (E (a - (j + 1))) * (-X 0 : CV Lam 1) ^ (j + 1) =
      -(X 0 * (C (E (a - 1 - j)) * (-X 0) ^ j)) := by
    intro j _
    rw [show a - (j + 1) = a - 1 - j by omega, pow_succ]
    ring
  rw [sum_congr rfl hE, sum_neg_distrib, ← mul_sum]
  set S := ∑ j ∈ range a, C (E (a - 1 - j)) * (-X 0 : CV Lam 1) ^ j
  have hq : qc (((a : ℚ) + 1) / a) * qc (1 / ((a + 1 : ℕ) : ℚ)) = qc (1 / (a : ℚ)) := by
    rw [← qc_mul]; congr 1; push_cast; field_simp
  have h1 : (C (E a) : CV Lam 1) * C (Einv a) = 1 := by rw [← map_mul, E_mul_Einv, map_one]
  have h2 : (C (qc (((a : ℚ) + 1) / a)) : CV Lam 1) * C (qc (1 / ((a + 1 : ℕ) : ℚ))) =
      C (qc (1 / (a : ℚ))) := by rw [← map_mul, hq]
  simp only [map_mul]
  linear_combination (C (E a) * C (Einv (a - 1)) * C (qc (1 / (a : ℚ))) -
      C (Einv (a - 1)) * C (qc (1 / (a : ℚ))) * (X 0 * S)) * h1 -
    (C (E a) * C (Einv (a - 1)) * C (Einv a) * (X 0 * S) -
      C (E a) * C (Einv (a - 1)) * C (Einv a) * C (E a)) * h2

lemma finSuccEquiv_C' {n : ℕ} (c : Lam) :
    finSuccEquiv Lam n (C c) = Polynomial.C (C c) := by
  rw [← algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply, algebraMap_eq]

lemma Dh_C_mul_X_pow (p : ℕ → Lam) (n : ℕ) (c : Lam) (m : ℕ) :
    Dh p n (C c * X 0 ^ m) = C c * freshQ p n m := by
  rw [Dh_apply, map_mul, map_pow, finSuccEquiv_X_zero, finSuccEquiv_C',
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index]
  simp

lemma qc_mul_natCast (a : ℕ) (ha : a ≠ 0) : qc (1 / (a : ℚ)) * ((a : ℕ) : Lam) = 1 := by
  rw [show ((a : ℕ) : Lam) = qc a from (map_natCast _ a).symm, ← qc_mul, one_div,
    inv_mul_cancel₀ (by exact_mod_cast ha), qc_one]

/-- `D̂_1 U_1 b_a = (e_a / e_{a-1}) U_0`. -/
lemma Dh_U1fn (a : ℕ) (ha : 1 ≤ a) : Dh Pw 0 (U1fn a) = C (Eratio a) := by
  have ha0 : a ≠ 0 := by omega
  rw [U1fn, if_neg ha0, map_smul, map_sum]
  have hterm : ∀ j ∈ range a, Dh Pw 0 (C (E (a - 1 - j)) * (-X 0 : CV Lam 1) ^ j) =
      C ((-1) ^ j * E (a - 1 - j) * Pw (j + 1)) := by
    intro j _
    rw [show (C (E (a - 1 - j)) * (-X 0 : CV Lam 1) ^ j) = C (E (a - 1 - j) * (-1) ^ j) * X 0 ^ j by
      rw [neg_pow, map_mul, map_pow, map_neg, map_one]; ring]
    rw [Dh_C_mul_X_pow, freshQ]
    simp only [Finset.univ_eq_empty, sum_empty, sub_zero, ← map_mul]
    ring_nf
  rw [sum_congr rfl hterm, ← map_sum, ← newton, smul_eq_C_mul', ← map_mul, Eratio]
  congr 1
  calc qc (1 / (a : ℚ)) * Einv (a - 1) * (((a : ℕ) : Lam) * E a)
      = (qc (1 / (a : ℚ)) * ((a : ℕ) : Lam)) * (E a * Einv (a - 1)) := by ring
    _ = E a * Einv (a - 1) := by rw [qc_mul_natCast a ha0, one_mul]

/-! ## Levels `k + 2 ≥ 2`: the recursion on the rank -/

lemma cons_last {k : ℕ} (a : ℕ) (w : Idx (k + 1)) : cons a w (Fin.last (k + 1)) = w (Fin.last k) := by
  rw [← Fin.succ_last]
  exact Fin.cons_succ (α := fun _ => ℕ) a w (Fin.last k)

lemma snoc_init_cons {k : ℕ} (a : ℕ) (w : Idx (k + 1)) :
    snoc (Fin.init (cons a w)) (w (Fin.last k)) = cons a w := by
  rw [← cons_last a w, snoc_eq_self]

/-- The columns `U_{k+2} b_{w,y}`, by well-founded recursion on the rank of `(w, y)`. -/
def Uwy (k : ℕ) (Uprev : Idx (k + 1) → CV Lam (k + 1)) (w : Idx (k + 1)) (y : ℕ) :
    CV Lam (k + 2) :=
  if hv : Valid (snoc w y) then
    if hy : y ∈ Tset (entries w) then
      ∑ r : Option (Zset (entries w)), qc (blockInv (entries w) r ⟨y, hy⟩) •
        (match r with
          | none => Mh (k + 1) (Uprev w)
          | some z => (E (z.1 - 2) * Einv (z.1 - 1)) •
              Rh (k + 1) (Uwy k Uprev (Fin.init (cons (z.1 - 1) w))
                (cons (z.1 - 1) w (Fin.last (k + 1)))))
    else
      qc (1 / Acoef y (insert (y - 1) (entries w))) •
        ((∑ z ∈ (Tset (entries w)).attach,
            qc (Acoef z.1 (entries w) / ((y : ℚ) - z.1)) • Uwy k Uprev w z.1)
          - (E (y - 2) * Einv (y - 1)) • Rh (k + 1) (Uwy k Uprev (Fin.init (cons (y - 1) w))
              (cons (y - 1) w (Fin.last (k + 1)))))
  else 0
termination_by rk (snoc w y)
decreasing_by
  all_goals simp_wf
  · rw [snoc_init_cons]; exact rk_block hv hy z.2
  · exact rk_free_block hv hy z.2
  · rw [snoc_init_cons]; exact rk_free_cons hv hy

/-- The columns of `U_k`. -/
def U : (k : ℕ) → Idx k → CV Lam k
  | 0 => fun _ => 1
  | 1 => fun σ => U1fn (σ 0)
  | k + 2 => fun σ => Uwy k (U (k + 1)) (Fin.init σ) (σ (Fin.last (k + 1)))

/-- `U_k : V_k → V̂_k`, extended linearly. -/
def Ul (k : ℕ) : V k →ₗ[Lam] CV Lam k := Finsupp.linearCombination Lam (U k)

@[simp] lemma Ul_bv {k : ℕ} (σ : Idx k) : Ul k (bv σ) = U k σ := by
  simp [Ul, bv]

lemma U_snoc {k : ℕ} (w : Idx (k + 1)) (y : ℕ) : U (k + 2) (snoc w y) = Uwy k (U (k + 1)) w y := by
  simp only [U, init_snoc', snoc_last']

lemma U_cons {k : ℕ} (a : ℕ) (w : Idx (k + 1)) :
    U (k + 2) (cons a w) = Uwy k (U (k + 1)) (Fin.init (cons a w)) (w (Fin.last k)) := by
  simp only [U]
  rw [cons_last]

/-- The right-hand sides of the block system. -/
def blockRhs {k : ℕ} (Uprev : Idx (k + 1) → CV Lam (k + 1)) (Ucur : Idx (k + 2) → CV Lam (k + 2))
    (w : Idx (k + 1)) : Option (Zset (entries w)) → CV Lam (k + 2)
  | none => Mh (k + 1) (Uprev w)
  | some z => (E (z.1 - 2) * Einv (z.1 - 1)) • Rh (k + 1) (Ucur (cons (z.1 - 1) w))

lemma Uwy_block {k : ℕ} {Uprev : Idx (k + 1) → CV Lam (k + 1)} {w : Idx (k + 1)} {y : ℕ}
    (hv : Valid (snoc w y)) (hy : y ∈ Tset (entries w)) :
    Uwy k Uprev w y = ∑ r : Option (Zset (entries w)), qc (blockInv (entries w) r ⟨y, hy⟩) •
      blockRhs Uprev (fun σ => Uwy k Uprev (Fin.init σ) (σ (Fin.last (k + 1)))) w r := by
  rw [Uwy, dif_pos hv, dif_pos hy]
  refine sum_congr rfl fun r _ => ?_
  rcases r with _ | z
  · rfl
  · rfl

lemma Uwy_free {k : ℕ} {Uprev : Idx (k + 1) → CV Lam (k + 1)} {w : Idx (k + 1)} {y : ℕ}
    (hv : Valid (snoc w y)) (hy : y ∉ Tset (entries w)) :
    Uwy k Uprev w y = qc (1 / Acoef y (insert (y - 1) (entries w))) •
      ((∑ z ∈ Tset (entries w), qc (Acoef z (entries w) / ((y : ℚ) - z)) • Uwy k Uprev w z)
        - (E (y - 2) * Einv (y - 1)) • Rh (k + 1) (Uwy k Uprev (Fin.init (cons (y - 1) w))
            (cons (y - 1) w (Fin.last (k + 1))))) := by
  rw [Uwy, dif_pos hv, dif_neg hy]
  congr 2
  exact sum_attach (Tset (entries w)) (fun z => qc (Acoef z (entries w) / ((y : ℚ) - z)) •
    Uwy k Uprev w z)

lemma Uwy_invalid {k : ℕ} {Uprev : Idx (k + 1) → CV Lam (k + 1)} {w : Idx (k + 1)} {y : ℕ}
    (hv : ¬Valid (snoc w y)) : Uwy k Uprev w y = 0 := by
  rw [Uwy, dif_neg hv]

lemma U_invalid {k : ℕ} {σ : Idx (k + 1)} (h : ¬Valid σ) : U (k + 1) σ = 0 := by
  rcases k with _ | k
  · simp only [U, U1fn]
    rw [if_pos]
    by_contra h0
    exact h ⟨fun i j _ => Fin.ext (by omega), fun i => by
      have : i = 0 := Fin.ext (by omega)
      subst this; omega⟩
  · show Uwy k (U (k + 1)) (Fin.init σ) (σ (Fin.last (k + 1))) = 0
    rw [Uwy_invalid]
    rwa [snoc_eq_self]

/-! ## Equation (M) -/

lemma qc_smul {n : ℕ} (q : ℚ) (G : CV Lam n) : qc q • G = q • G := algebraMap_smul Lam q G

lemma entries_zero (σ : Idx 0) : entries σ = ∅ := by
  simp [entries]

lemma valid_zero (σ : Idx 0) : Valid σ := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

lemma Tset_empty : Tset (∅ : Finset ℕ) = {1} := by
  ext y; simp [mem_Tset]

lemma Acoef_one_empty : Acoef 1 (∅ : Finset ℕ) = 1 := by
  rw [Acoef_of_mem (by rw [Tset_empty]; simp)]
  simp [cfac]

lemma valid_one {σ : Idx 1} : Valid σ ↔ 1 ≤ σ 0 := by
  constructor
  · intro h; exact h.2 0
  · intro h
    refine ⟨fun i j _ => Fin.ext (by omega), fun i => ?_⟩
    have : i = 0 := Fin.ext (by omega)
    subst this; exact h

/-- **Equation (M)**: `U_{k+1} M_k = M̂_k U_k`. -/
theorem U_M (k : ℕ) (σ : Idx k) : Ul (k + 1) (Mop k (bv σ)) = Mh k (U k σ) := by
  rcases k with _ | k
  · rw [Mop_bv_valid (valid_zero σ), entries_zero, Tset_empty, sum_singleton, Acoef_one_empty,
      qc_one, one_smul, Ul_bv]
    have : snoc σ 1 0 = 1 := snoc_last' σ 1
    simp only [U, this, U1fn_one, Mh, map_one]
  by_cases hσ : Valid σ
  swap
  · rw [Mop_bv_invalid hσ, map_zero, U_invalid hσ, map_zero]
  rw [Mop_bv_valid hσ, map_sum]
  simp only [map_smul, Ul_bv, U_snoc]
  rw [← sum_coe_sort (Tset (entries σ))]
  have : ∀ y : Tset (entries σ), qc (Acoef y (entries σ)) • Uwy k (U (k + 1)) σ y =
      blockC (entries σ) none y • ∑ r, blockInv (entries σ) r y •
        blockRhs (U (k + 1)) (fun τ => Uwy k (U (k + 1)) (Fin.init τ) (τ (Fin.last (k + 1)))) σ r := by
    intro y
    rw [Uwy_block (valid_snoc_of_mem_Tset hσ y.2) y.2, qc_smul]
    simp only [qc_smul]
    rfl
  rw [sum_congr rfl fun y _ => this y]
  have h0 : 0 ∉ entries σ := fun h => by
    obtain ⟨i, hi⟩ := mem_entries.1 h; have := hσ.2 i; omega
  rw [blockSolve (entries σ) h0]
  rfl

end ProperCircularArc
