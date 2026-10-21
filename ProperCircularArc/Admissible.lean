import ProperCircularArc.Specialize
import ProperCircularArc.Construction
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Admissibility of the columns of `U_k`

The paper notes that `U_k b_σ` only divides by `e_j` with `j < max σ`, so that one may set
`x_c = 0` for `c > N` whenever the entries of `σ` are at most `N + 1`.  Here: the coefficients
of `U_k b_σ` lie in the image of the admissible ring `LamN N` whenever `σ` is `N`-good.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset

/-! ## Power sums in `LamN` -/

/-- The power sums in `LamN N`, by the same Newton recursion as `Pw`. -/
def PwN (N : ℕ) : ℕ → LamN N
  | 0 => 0
  | k + 1 => (-1) ^ (k + 2) * ((k + 1 : ℕ) : LamN N) * EN N (k + 1) -
      ∑ i : Fin (k + 1), if h : 0 < (i : ℕ) then (-1) ^ (i : ℕ) * EN N i * PwN N (k + 1 - i) else 0
termination_by k => k
decreasing_by omega

lemma PwN_succ (N k : ℕ) : PwN N (k + 1) = (-1) ^ (k + 2) * ((k + 1 : ℕ) : LamN N) * EN N (k + 1) -
    ∑ i ∈ range (k + 1), if 0 < i then (-1) ^ i * EN N i * PwN N (k + 1 - i) else 0 := by
  rw [PwN]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => if 0 < i then (-1) ^ i * EN N i * PwN N (k + 1 - i)
    else 0)]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

lemma iotaN_PwN (N m : ℕ) : iotaN N (PwN N m) = Pw m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | k
    · simp [PwN, Pw]
    rw [PwN_succ, Pw_succ, map_sub, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
      iotaN_EN, map_sum]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    split_ifs with h
    · rw [map_mul, map_mul, map_pow, map_neg, map_one, iotaN_EN, ih _ (by omega)]
    · simp

lemma psiN_PwN (N m : ℕ) (hm : 1 ≤ m) :
    psiN N (PwN N m) = algebraMap (Pol N) (KN N) (psum (Fin N) ℚ m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [PwN_succ, psum_eq_mul_esymm_sub_sum (Fin N) ℚ (k + 1) (by omega)]
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, psiN_EN, map_sum]
    congr 1
    rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    conv_rhs => rw [sum_range_succ]
    rw [if_neg (by simp), add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    by_cases h : 0 < i
    · rw [if_pos h, if_pos (by simp; omega), map_mul, map_mul, map_pow, map_neg, map_one,
        psiN_EN, ih _ (by omega) (by omega)]
      simp [eK]
    · rw [if_neg h, if_neg (by simp; omega), map_zero]

/-! ## Specialising coefficients -/

/-- The `ℚ`-linear specialisation of coefficients `∏ E_j^{m_j} ↦ ∏ e_j^{m_j}`. -/
def specCoeff (N : ℕ) : Lam →ₗ[ℚ] KN N :=
  Finsupp.linearCombination ℚ (monoVal N) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℚ : Lam ≃ₗ[ℚ] ((ℕ →₀ ℤ) →₀ ℚ)).toLinearMap

lemma specCoeff_iotaN (N : ℕ) (g : LamN N) : specCoeff N (iotaN N g) = psiN N g := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single m c =>
    rw [iotaN_single, psiN_single]
    simp [specCoeff]

/-! ## Admissible coefficients and colour vectors -/

/-- Admissible coefficients. -/
def AdmC (N : ℕ) : Subalgebra ℚ Lam := (iotaN N).range

/-- Admissible colour vectors. -/
def AdmV (N k : ℕ) : Subalgebra ℚ (CV Lam k) :=
  (MvPolynomial.mapAlgHom (iotaN N) : MvPolynomial (Fin k) (LamN N) →ₐ[ℚ] CV Lam k).range

lemma mem_AdmV {N k : ℕ} {G : CV Lam k} :
    G ∈ AdmV N k ↔ ∃ G' : MvPolynomial (Fin k) (LamN N), map (iotaN N).toRingHom G' = G := by
  simp [AdmV, AlgHom.mem_range, MvPolynomial.mapAlgHom_apply]

lemma E_mem (N j : ℕ) : E j ∈ AdmC N := ⟨EN N j, iotaN_EN N j⟩

lemma Einv_mem {N j : ℕ} (hj : j ≤ N) : Einv j ∈ AdmC N := ⟨EinvN N j hj, iotaN_EinvN N j hj⟩

lemma qc_mem (N : ℕ) (q : ℚ) : qc q ∈ AdmC N := Subalgebra.algebraMap_mem _ q

lemma Pw_mem (N m : ℕ) : Pw m ∈ AdmC N := ⟨PwN N m, iotaN_PwN N m⟩

lemma C_mem {N k : ℕ} {c : Lam} (hc : c ∈ AdmC N) : (C c : CV Lam k) ∈ AdmV N k := by
  obtain ⟨c', rfl⟩ := hc
  exact mem_AdmV.2 ⟨C c', by simp⟩

lemma X_mem (N : ℕ) {k : ℕ} (r : Fin k) : (X r : CV Lam k) ∈ AdmV N k :=
  mem_AdmV.2 ⟨X r, by simp⟩

lemma smul_mem_AdmV {N k : ℕ} {c : Lam} {G : CV Lam k} (hc : c ∈ AdmC N) (hG : G ∈ AdmV N k) :
    c • G ∈ AdmV N k := by
  rw [smul_eq_C_mul']
  exact Subalgebra.mul_mem _ (C_mem hc) hG

lemma rename_mem {N k k' : ℕ} (f : Fin k → Fin k') {G : CV Lam k} (hG : G ∈ AdmV N k) :
    rename f G ∈ AdmV N k' := by
  obtain ⟨G', rfl⟩ := mem_AdmV.1 hG
  exact mem_AdmV.2 ⟨rename f G', map_rename _ _ _⟩

lemma Mh_mem {N k : ℕ} {G : CV Lam k} (hG : G ∈ AdmV N k) : Mh k G ∈ AdmV N (k + 1) :=
  rename_mem _ hG

lemma Rh_mem {N k : ℕ} {G : CV Lam (k + 1)} (hG : G ∈ AdmV N (k + 1)) : Rh k G ∈ AdmV N (k + 1) := by
  rw [Rh_apply]
  exact Subalgebra.mul_mem _ (X_mem N _) (rename_mem _ hG)

lemma Dh_mem {N k : ℕ} {G : CV Lam (k + 1)} (hG : G ∈ AdmV N (k + 1)) :
    Dh Pw k G ∈ AdmV N k := by
  obtain ⟨G', rfl⟩ := mem_AdmV.1 hG
  refine mem_AdmV.2 ⟨Dh (PwN N) k G', ?_⟩
  have h : ((iotaN N).toRingHom ∘ PwN N) = Pw := funext (iotaN_PwN N)
  rw [Dh_map, h]

/-! ## The columns of `U` are admissible -/

lemma Uwy_adm (N k : ℕ)
    (hprev : ∀ w : Idx (k + 1), (∀ i, w i ≤ N + 1) → U (k + 1) w ∈ AdmV N (k + 1)) :
    ∀ (w : Idx (k + 1)) (y : ℕ), (∀ i, w i ≤ N + 1) → (y ≤ N + 1 ∨ y ∈ Tset (entries w)) →
      Uwy k (U (k + 1)) w y ∈ AdmV N (k + 2) := by
  intro w y
  induction hn : rk (snoc w y) using Nat.strong_induction_on generalizing w y with
  | _ n ih =>
  intro hw hy
  by_cases hv : Valid (snoc w y)
  swap
  · rw [Uwy_invalid hv]; exact Subalgebra.zero_mem _
  by_cases hyT : y ∈ Tset (entries w)
  · rw [Uwy_block hv hyT]
    refine Subalgebra.sum_mem _ fun r _ => smul_mem_AdmV (qc_mem N _) ?_
    rcases r with _ | ⟨z, hz⟩
    · exact Mh_mem (hprev w hw)
    · obtain ⟨hzw, hz2, hz1⟩ := mem_Zset.1 hz
      obtain ⟨i, hi⟩ := mem_entries.1 hzw
      have hzN : z ≤ N + 1 := by rw [← hi]; exact hw i
      refine smul_mem_AdmV (Subalgebra.mul_mem _ (E_mem N _) (Einv_mem (j := z - 1) (by omega)))
        (Rh_mem ?_)
      show Uwy k (U (k + 1)) (Fin.init (cons (z - 1) w)) (cons (z - 1) w (Fin.last (k + 1)))
        ∈ AdmV N (k + 2)
      rw [cons_last]
      refine ih _ ?_ _ _ rfl ?_ (Or.inl (hw _))
      · rw [← hn, snoc_init_cons]; exact rk_block hv hyT hz
      · intro j
        rw [init_cons_eq]
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp; omega
        · simp [Fin.init]; exact hw _
  · have hyN : y ≤ N + 1 := hy.resolve_right hyT
    rw [Uwy_free hv hyT]
    refine smul_mem_AdmV (qc_mem N _) (Subalgebra.sub_mem _ (Subalgebra.sum_mem _ fun z hz =>
      smul_mem_AdmV (qc_mem N _) ?_) (smul_mem_AdmV (Subalgebra.mul_mem _ (E_mem N _)
        (Einv_mem (j := y - 1) (by omega))) (Rh_mem ?_)))
    · exact ih _ (hn ▸ rk_free_block hv hyT hz) w z rfl hw (Or.inr hz)
    · rw [cons_last]
      refine ih _ ?_ _ _ rfl ?_ (Or.inl (hw _))
      · rw [← hn, snoc_init_cons]; exact rk_free_cons hv hyT
      · intro j
        rw [init_cons_eq]
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp; omega
        · simp [Fin.init]; exact hw _

/-- **Admissibility**: if all entries of `σ` are at most `N + 1`, the coefficients of `U_k b_σ`
only invert `E_j` for `j ≤ N`. -/
theorem U_adm (N : ℕ) : ∀ k (σ : Idx k), (∀ i, σ i ≤ N + 1) → U k σ ∈ AdmV N k
  | 0, _, _ => Subalgebra.one_mem _
  | 1, σ, hσ => by
    show U1fn (σ 0) ∈ AdmV N 1
    unfold U1fn
    split_ifs with h
    · exact Subalgebra.zero_mem _
    · refine smul_mem_AdmV (Subalgebra.mul_mem _ (qc_mem N _) (Einv_mem (by have := hσ 0; omega)))
        (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (C_mem (E_mem N _))
          (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (X_mem N 0)) _))
  | k + 2, σ, hσ => by
    show Uwy k (U (k + 1)) (Fin.init σ) (σ (Fin.last (k + 1))) ∈ AdmV N (k + 2)
    exact Uwy_adm N k (fun w hw => U_adm N (k + 1) w hw) _ _ (fun i => hσ _) (Or.inl (hσ _))

end ProperCircularArc
