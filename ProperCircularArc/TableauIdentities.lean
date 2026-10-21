import ProperCircularArc.Tableau

/-!
# The tableau identities of Proposition `identities`
-/

noncomputable section

namespace ProperCircularArc

open Finset

/-! ## Entries by position -/

lemma getE_snoc_lt {n : ℕ} (σ : Idx n) (y : ℕ) {i : ℕ} (hi : i < n) :
    getE (snoc σ y) i = getE σ i := by
  simp only [getE, hi, Nat.lt_succ_of_lt hi, dite_true]
  exact Fin.snoc_castSucc (α := fun _ => ℕ) (p := σ) (x := y) (i := ⟨i, hi⟩)

lemma getE_snoc_last {n : ℕ} (σ : Idx n) (y : ℕ) : getE (snoc σ y) n = y := by
  simp only [getE, Nat.lt_succ_self, dite_true]
  exact Fin.snoc_last (α := fun _ => ℕ) (p := σ) (x := y)

lemma getE_succ {n : ℕ} (σ : Idx (n + 1)) (i : ℕ) : getE σ (i + 1) = getE (Fin.tail σ) i := by
  unfold getE
  by_cases hi : i < n
  · rw [dif_pos (by omega), dif_pos hi]; rfl
  · rw [dif_neg (by omega), dif_neg hi]

lemma swc_snoc {n s : ℕ} (σ : Idx n) (y : ℕ) (hs : s + 1 < n) : swc (snoc σ y) s = swc σ s := by
  simp [swc, getE_snoc_lt _ _ hs, getE_snoc_lt _ _ (show s < n by omega)]

lemma swc_tail {n s : ℕ} (σ : Idx (n + 1)) : swc σ (s + 1) = swc (Fin.tail σ) s := by
  simp [swc, getE_succ]

lemma snoc_comp_swapPerm {n s : ℕ} (σ : Idx n) (y : ℕ) (hs : s + 1 < n) :
    snoc σ y ∘ swapPerm (n + 1) s = snoc (σ ∘ swapPerm n s) y := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [Function.comp_apply]
    rw [swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)]
    simp
  | cast j =>
    simp only [Function.comp_apply]
    rw [swapPerm_castSucc hs]
    simp

lemma comp_swapPerm_zero {n s : ℕ} (σ : Idx (n + 1)) : (σ ∘ swapPerm (n + 1) (s + 1)) 0 = σ 0 := by
  simp [swapPerm_succ_zero]

lemma tail_comp_swapPerm {n s : ℕ} (σ : Idx (n + 1)) (hs : s + 1 < n) :
    Fin.tail (σ ∘ swapPerm (n + 1) (s + 1)) = Fin.tail σ ∘ swapPerm n s := by
  funext i
  simp [Fin.tail, swapPerm_succ hs]

/-! ## Swaps commute with `M` and `D` -/

lemma lhom_ext_bv {n m : ℕ} {f g : V n →ₗ[Lam] V m} (h : ∀ σ, f (bv σ) = g (bv σ)) : f = g := by
  apply Finsupp.lhom_ext
  intro σ c
  have : Finsupp.single σ c = c • bv σ := by simp [bv]
  rw [this, map_smul, map_smul, h]

/-- `S_s M = M S_s` for `s + 1 < n`. -/
lemma Sop_Mop {n s : ℕ} (hs : s + 1 < n) : Sop (n + 1) s ∘ₗ Mop n = Mop n ∘ₗ Sop n s := by
  apply lhom_ext_bv
  intro σ
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hσ : Valid σ
  · rw [Mop_bv_valid hσ, Sop_bv_valid hσ, map_sum, map_add, map_smul, map_smul,
      Mop_bv_valid hσ, Mop_bv_valid (valid_comp_perm hσ _), entries_comp_perm, smul_sum, smul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun y hy => ?_
    rw [map_smul, Sop_bv_valid (valid_snoc_of_mem_Tset hσ hy), swc_snoc _ _ hs,
      snoc_comp_swapPerm _ _ hs, smul_add, smul_comm (qc (Acoef y (entries σ))),
      smul_comm (qc (Acoef y (entries σ)))]
  · rw [Mop_bv_invalid hσ, map_zero, Sop_bv_invalid hσ, Mop_bv_invalid hσ]

/-- `S_s D = D S_{s+1}` for `s + 1 < n`. -/
lemma Sop_Dop {n s : ℕ} (hs : s + 1 < n) : Sop n s ∘ₗ Dop n = Dop n ∘ₗ Sop (n + 1) (s + 1) := by
  apply lhom_ext_bv
  intro σ
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hσ : Valid σ
  · rw [Dop_bv_valid hσ, Sop_bv_valid hσ, map_smul, Sop_bv_valid (valid_tail hσ), map_add,
      map_smul, map_smul, Dop_bv_valid hσ, Dop_bv_valid (valid_comp_perm hσ _),
      comp_swapPerm_zero, tail_comp_swapPerm _ hs, swc_tail, smul_add, smul_comm (Eratio (σ 0)),
      smul_comm (Eratio (σ 0))]
  · rw [Dop_bv_invalid hσ, map_zero, Sop_bv_invalid hσ, Dop_bv_invalid hσ]

/-- `S_s R = R S_{s+1}` for `s + 1 < n` (level `n + 1`). -/
lemma Sop_Rop {n s : ℕ} (hs : s + 1 < n) :
    Sop (n + 1) s ∘ₗ Rop n = Rop n ∘ₗ Sop (n + 1) (s + 1) := by
  rw [Rop, LinearMap.comp_sub, LinearMap.sub_comp]
  congr 1
  · calc Sop (n + 1) s ∘ₗ (Mop n ∘ₗ Dop n) = (Sop (n + 1) s ∘ₗ Mop n) ∘ₗ Dop n :=
          (LinearMap.comp_assoc _ _ _).symm
      _ = Mop n ∘ₗ (Sop n s ∘ₗ Dop n) := by rw [Sop_Mop hs, LinearMap.comp_assoc]
      _ = (Mop n ∘ₗ Dop n) ∘ₗ Sop (n + 1) (s + 1) := by
          rw [Sop_Dop hs, LinearMap.comp_assoc]
  · calc Sop (n + 1) s ∘ₗ (Dop (n + 1) ∘ₗ Mop (n + 1))
        = (Sop (n + 1) s ∘ₗ Dop (n + 1)) ∘ₗ Mop (n + 1) := (LinearMap.comp_assoc _ _ _).symm
      _ = Dop (n + 1) ∘ₗ (Sop (n + 2) (s + 1) ∘ₗ Mop (n + 1)) := by
          rw [Sop_Dop (show s + 1 < n + 1 by omega), LinearMap.comp_assoc]
      _ = (Dop (n + 1) ∘ₗ Mop (n + 1)) ∘ₗ Sop (n + 1) (s + 1) := by
          rw [Sop_Mop (show s + 1 + 1 < n + 1 by omega), LinearMap.comp_assoc]

lemma Sop_bv_of_not_lt {n s : ℕ} (σ : Idx n) (hs : ¬s + 1 < n) : Sop n s (bv σ) = bv σ := by
  by_cases hσ : Valid σ
  · have hsp : swapPerm n s = 1 := by simp [swapPerm, hs]
    rw [Sop_bv_valid hσ, hsp, Equiv.Perm.coe_one, Function.comp_id, ← add_smul, ← qc_add]
    simp
  · exact Sop_bv_invalid hσ

lemma swc_comp_swapPerm {n s : ℕ} (σ : Idx n) (hs : s + 1 < n) :
    swc (σ ∘ swapPerm n s) s = -swc σ s := by
  have h1 : getE (σ ∘ swapPerm n s) s = getE σ (s + 1) := by
    simp only [getE, show s < n by omega, hs, dite_true, Function.comp_apply]
    rw [swapPerm_apply_of_lt hs, Equiv.swap_apply_left]
  have h2 : getE (σ ∘ swapPerm n s) (s + 1) = getE σ s := by
    simp only [getE, show s < n by omega, hs, dite_true, Function.comp_apply]
    rw [swapPerm_apply_of_lt hs, Equiv.swap_apply_right]
  rw [swc, swc, h1, h2,
    show ((getE σ s : ℚ) - getE σ (s + 1)) = -((getE σ (s + 1) : ℚ) - getE σ s) by ring, div_neg]

lemma Sop_Sop_bv (n s : ℕ) (σ : Idx n) : Sop n s (Sop n s (bv σ)) = bv σ := by
  by_cases hσ : Valid σ
  · by_cases hs : s + 1 < n
    · have hv := valid_comp_perm hσ (swapPerm n s)
      have hcomp : (σ ∘ swapPerm n s) ∘ swapPerm n s = σ := by
        funext i; simp
      rw [Sop_bv_valid hσ, map_add, map_smul, map_smul, Sop_bv_valid hσ, Sop_bv_valid hv,
        swc_comp_swapPerm σ hs, hcomp]
      set c := swc σ s
      simp only [qc_sub, qc_one, qc_neg]
      module
    · rw [Sop_bv_of_not_lt σ hs, Sop_bv_of_not_lt σ hs]
  · rw [Sop_bv_invalid hσ, Sop_bv_invalid hσ]

/-- `S_s² = 1`. -/
lemma Sop_Sop (n s : ℕ) : Sop n s ∘ₗ Sop n s = LinearMap.id :=
  lhom_ext_bv fun σ => Sop_Sop_bv n s σ

end ProperCircularArc
