import ProperCircularArc.Tableau
import ProperCircularArc.ScalarIdentities
import Mathlib.Tactic.LinearCombination

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

/-! ## Bounding the possible new columns -/

lemma Tset_subset_range {s : Finset ℕ} {B : ℕ} (hB : 1 < B) (hs : ∀ t ∈ s, t + 1 < B) :
    Tset s ⊆ range B := by
  intro y hy
  rw [mem_range]
  rcases (mem_Tset.1 hy).2 with h | ⟨h1, h2⟩
  · omega
  · have := hs _ h2; omega

/-- A uniform bound for the columns appearing two steps after `s`. -/
def bound (s : Finset ℕ) : ℕ := s.sup id + 3

lemma le_sup_bound {s : Finset ℕ} {t : ℕ} (ht : t ∈ s) : t + 3 ≤ bound s := by
  unfold bound
  have := le_sup (f := id) ht
  simp only [id] at this
  omega

lemma Tset_subset_bound (s : Finset ℕ) : Tset s ⊆ range (bound s) :=
  Tset_subset_range (by unfold bound; omega) fun t ht => by have := le_sup_bound ht; omega

lemma Tset_insert_subset_bound {s : Finset ℕ} {y : ℕ} (hy : y ∈ Tset s) :
    Tset (insert y s) ⊆ range (bound s) := by
  refine Tset_subset_range (by unfold bound; omega) fun t ht => ?_
  rcases mem_insert.1 ht with rfl | ht
  · have := Tset_subset_range (s := s) (B := bound s - 1) (by unfold bound; omega)
      (fun t ht => by have := le_sup_bound ht; omega) hy
    rw [mem_range] at this
    omega
  · have := le_sup_bound ht; omega

lemma bound_mono {s s' : Finset ℕ} (h : s ⊆ s') : bound s ≤ bound s' := by
  unfold bound
  have := sup_mono (f := id) h
  omega

/-! ## Two appended columns -/

/-- The swap of the last two positions acting on a double sum. -/
lemma Sop_two {n : ℕ} (w : Idx n) (Y : Finset ℕ) (c : ℕ → ℕ → Lam)
    (hc : ∀ y z, ¬Valid (snoc (snoc w y) z) → c y z = 0) :
    Sop (n + 2) n (∑ y ∈ Y, ∑ z ∈ Y, c y z • bv (snoc (snoc w y) z)) =
      ∑ y ∈ Y, ∑ z ∈ Y, (c y z * qc (1 / ((z : ℚ) - y)) + c z y * qc (1 - 1 / ((y : ℚ) - z))) •
        bv (snoc (snoc w y) z) := by
  have hterm : ∀ y z, Sop (n + 2) n (c y z • bv (snoc (snoc w y) z)) =
      (c y z * qc (1 / ((z : ℚ) - y))) • bv (snoc (snoc w y) z) +
        (c y z * qc (1 - 1 / ((z : ℚ) - y))) • bv (snoc (snoc w z) y) := by
    intro y z
    by_cases hv : Valid (snoc (snoc w y) z)
    · rw [map_smul, Sop_bv_valid hv]
      have hswc : swc (snoc (snoc w y) z) n = 1 / ((z : ℚ) - y) := by
        rw [swc, getE_snoc_last, getE_snoc_lt _ _ (by omega), getE_snoc_last]
      have hcomp : snoc (snoc w y) z ∘ swapPerm (n + 2) n = snoc (snoc w z) y := by
        funext i
        induction i using Fin.lastCases with
        | last =>
          simp only [Function.comp_apply]
          rw [swapPerm_of_lt (by omega)]
          rw [show (Fin.last (n + 1)) = (⟨n + 1, by omega⟩ : Fin (n + 2)) from rfl,
            Equiv.swap_apply_right]
          show snoc (snoc w y) z (Fin.castSucc (Fin.last n)) =
            snoc (snoc w z) y (Fin.last (n + 1))
          simp
        | cast j =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Function.comp_apply]
            rw [swapPerm_of_lt (by omega)]
            rw [show (Fin.castSucc (Fin.last n)) = (⟨n, by omega⟩ : Fin (n + 2)) from rfl,
              Equiv.swap_apply_left]
            show snoc (snoc w y) z (Fin.last (n + 1)) =
              snoc (snoc w z) y (Fin.castSucc (Fin.last n))
            simp
          | cast k =>
            simp only [Function.comp_apply]
            rw [swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)]
            simp
      rw [hswc, hcomp, smul_add, smul_smul, smul_smul]
    · rw [hc y z hv]; simp
  rw [map_sum]
  simp_rw [map_sum, hterm, sum_add_distrib]
  rw [sum_comm (s := Y) (t := Y) (f := fun y z => (c y z * qc (1 - 1 / ((z : ℚ) - y))) •
    bv (snoc (snoc w z) y))]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  rw [add_smul]

/-- `M_{n+1} M_n b_w` as a double sum. -/
lemma Mop_Mop_bv {n : ℕ} {w : Idx n} (hw : Valid w) :
    Mop (n + 1) (Mop n (bv w)) = ∑ y ∈ range (bound (entries w)), ∑ z ∈ range (bound (entries w)),
      qc (Acoef y (entries w) * Acoef z (insert y (entries w))) • bv (snoc (snoc w y) z) := by
  rw [Mop_extend hw (Tset_subset_bound _), map_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ Tset (entries w)
  · have hv := valid_snoc_of_mem_Tset hw hy
    have hT : Tset (entries (snoc w y)) ⊆ range (bound (entries w)) := by
      rw [entries_snoc]; exact Tset_insert_subset_bound hy
    rw [map_smul, Mop_extend hv hT, smul_sum, entries_snoc]
    refine sum_congr rfl fun z _ => ?_
    rw [smul_smul, qc_mul]
  · simp [Acoef_of_not_mem hy]

lemma valid_of_coeff {n : ℕ} {w : Idx n} (hw : Valid w) {a y z : ℕ}
    (hy : Acoef y (entries w) ≠ 0 ∨ Acoef y (insert a (entries w)) ≠ 0)
    (hz : Acoef z (insert y (entries w)) ≠ 0) : Valid (snoc (snoc w y) z) := by
  have hy' : y ∈ Tset (entries w) ∨ y ∈ Tset (insert a (entries w)) := by
    rcases hy with h | h
    · exact Or.inl (by by_contra hh; exact h (Acoef_of_not_mem hh))
    · exact Or.inr (by by_contra hh; exact h (Acoef_of_not_mem hh))
  have hyw : y ∉ entries w ∧ 1 ≤ y := by
    rcases hy' with h | h
    · exact ⟨not_mem_of_mem_Tset h, pos_of_mem_Tset h⟩
    · exact ⟨fun hm => not_mem_of_mem_Tset h (mem_insert_of_mem hm), pos_of_mem_Tset h⟩
  have hzT : z ∈ Tset (insert y (entries w)) := by
    by_contra hh; exact hz (Acoef_of_not_mem hh)
  have h1 := valid_snoc hw hyw.1 hyw.2
  exact valid_snoc_of_mem_Tset h1 (by rwa [entries_snoc])

/-- `S_{k-1} M_{k-1} M_{k-2} = M_{k-1} M_{k-2}`. -/
lemma Sop_Mop_Mop (n : ℕ) : Sop (n + 2) n ∘ₗ Mop (n + 1) ∘ₗ Mop n = Mop (n + 1) ∘ₗ Mop n := by
  apply lhom_ext_bv
  intro w
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hw : Valid w
  · rw [Mop_Mop_bv hw, Sop_two]
    · refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
      congr 1
      by_cases hyz : y = z
      · subst hyz
        simp [Acoef_eq_zero_of_mem (mem_insert_self _ _)]
      · rw [← qc_mul, ← qc_mul, ← qc_add, scalar_MM _ hyz]
    · intro y z hv
      by_contra hne
      apply hv
      have h1 : Acoef y (entries w) ≠ 0 := fun e => hne (by simp [e])
      have h2 : Acoef z (insert y (entries w)) ≠ 0 := fun e => hne (by simp [e])
      exact valid_of_coeff (a := 0) hw (Or.inl h1) h2
  · rw [Mop_bv_invalid hw]; simp

lemma le_sup_of_mem_Tset {s : Finset ℕ} {y : ℕ} (hy : y ∈ Tset s) : y ≤ s.sup id + 1 := by
  rcases (mem_Tset.1 hy).2 with h | ⟨h1, h2⟩
  · omega
  · have := le_sup (f := id) h2; simp only [id] at this; omega

lemma Tset_subset_of_le {t S : Finset ℕ} (h : ∀ x ∈ t, x ≤ S.sup id + 1) :
    Tset t ⊆ range (bound S) :=
  Tset_subset_range (by unfold bound; omega) fun x hx => by have := h x hx; unfold bound; omega

lemma mem_le_sup {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : x ≤ S.sup id := by
  have := le_sup (f := id) hx; simpa using this

lemma Rop_bv_invalid {n : ℕ} {σ : Idx (n + 1)} (h : ¬Valid σ) : Rop n (bv σ) = 0 := by
  simp [Rop, Dop_bv_invalid h, Mop_bv_invalid h]

/-- `S_{k-1} M_{k-1} R_{k-1} = R_k M_{k-1}`. -/
lemma Sop_Mop_Rop (n : ℕ) :
    Sop (n + 2) n ∘ₗ Mop (n + 1) ∘ₗ Rop n = Rop (n + 1) ∘ₗ Mop (n + 1) := by
  apply lhom_ext_bv
  intro σ
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hσ : Valid σ
  swap
  · rw [Rop_bv_invalid hσ, Mop_bv_invalid hσ]; simp
  rw [← cons_eq_self σ] at hσ ⊢
  set a := σ 0
  set w := Fin.tail σ
  obtain ⟨hw, ha, ha1⟩ := valid_of_cons hσ
  set S := insert a (entries w) with hS
  have hwS : ∀ x ∈ entries w, x ≤ S.sup id := fun x hx => mem_le_sup (mem_insert_of_mem hx)
  have haS : a ≤ S.sup id := mem_le_sup (mem_insert_self _ _)
  set Y := range (bound S)
  have hT1 : Tset (entries w) ⊆ Y := Tset_subset_of_le fun x hx => by have := hwS x hx; omega
  have hT2 : Tset S ⊆ Y := Tset_subset_of_le fun x hx => by
    have := mem_le_sup hx; omega
  -- the coefficient of the inner sum
  set d : ℕ → ℚ := fun y => Acoef y (entries w) - Acoef y S
  have hd : ∀ y, d y ≠ 0 → y ∈ Tset (entries w) ∨ y ∈ Tset S := by
    intro y hy
    by_contra hh
    push Not at hh
    exact hy (by simp [d, Acoef_of_not_mem hh.1, Acoef_of_not_mem hh.2])
  have hyle : ∀ y, y ∈ Tset (entries w) ∨ y ∈ Tset S → y ≤ S.sup id + 1 := by
    intro y hy
    rcases hy with h | h
    · rcases (mem_Tset.1 h).2 with h' | ⟨_, h'⟩
      · omega
      · have := hwS _ h'; omega
    · exact le_sup_of_mem_Tset h
  have hTy : ∀ y, y ≤ S.sup id + 1 → Tset (insert y (entries w)) ⊆ Y := by
    intro y hy
    refine Tset_subset_of_le fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · omega
    · have := hwS x hx; omega
  have hTay : ∀ y, y ≤ S.sup id + 1 → Tset (insert a (insert y (entries w))) ⊆ Y := by
    intro y hy
    refine Tset_subset_of_le fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · omega
    · rcases mem_insert.1 hx with rfl | hx
      · omega
      · have := hwS x hx; omega
  -- left side
  have hL : Mop (n + 1) (Rop n (bv (cons a w))) = Eratio a • ∑ y ∈ Y, ∑ z ∈ Y,
      qc (d y * Acoef z (insert y (entries w))) • bv (snoc (snoc w y) z) := by
    rw [Rop_cons_diff hσ hT1 hT2, map_smul, map_sum]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    by_cases hdy : d y = 0
    · have : Acoef y (entries w) - Acoef y S = 0 := hdy
      rw [this]; simp [hdy]
    · have hy := hd y hdy
      have hv : Valid (snoc w y) := by
        rcases hy with h | h
        · exact valid_snoc_of_mem_Tset hw h
        · exact valid_snoc hw (fun hm => not_mem_of_mem_Tset h (mem_insert_of_mem hm))
            (pos_of_mem_Tset h)
      rw [map_smul, Mop_extend (Y := Y) hv (by rw [entries_snoc]; exact hTy y (hyle y hy)), smul_sum,
        entries_snoc]
      refine sum_congr rfl fun z _ => ?_
      rw [smul_smul, ← qc_mul]
  -- right side
  have hR : Rop (n + 1) (Mop (n + 1) (bv (cons a w))) = Eratio a • ∑ y ∈ Y, ∑ z ∈ Y,
      qc (Acoef y S * (Acoef z (insert y (entries w)) - Acoef z (insert a (insert y (entries w)))))
        • bv (snoc (snoc w y) z) := by
    rw [Mop_extend (Y := Y) hσ (by rw [entries_cons]; exact hT2), map_sum, smul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ Tset S
    · have hv : Valid (snoc (cons a w) y) := valid_snoc_of_mem_Tset hσ (by rwa [entries_cons])
      have hv' : Valid (cons a (snoc w y)) := by
        rwa [snoc_cons_comm] at hv
      rw [map_smul, entries_cons, snoc_cons_comm,
        Rop_cons_diff (Y := Y) hv' (by rw [entries_snoc]; exact hTy y (le_sup_of_mem_Tset hy))
          (by rw [entries_snoc]; exact hTay y (le_sup_of_mem_Tset hy)),
        entries_snoc, smul_sum, smul_sum, smul_sum]
      refine sum_congr rfl fun z _ => ?_
      rw [qc_mul]
      module
    · rw [entries_cons, Acoef_of_not_mem hy]; simp
  rw [hL, hR, map_smul, Sop_two]
  · congr 1
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    congr 1
    by_cases hyz : y = z
    · subst hyz
      simp [Acoef_eq_zero_of_mem (mem_insert_self _ _),
        Acoef_eq_zero_of_mem (mem_insert_of_mem (mem_insert_self y (entries w)))]
    · rw [← qc_mul, ← qc_mul, ← qc_add]
      congr 1
      have := scalar_lastSwap (entries w) ha ha1 hyz
      simp only [d, hS] at this ⊢
      linear_combination this
  · intro y z hv
    by_contra hne
    apply hv
    have h1 : d y ≠ 0 := fun e => hne (by simp [e])
    have h2 : Acoef z (insert y (entries w)) ≠ 0 := fun e => hne (by simp [e])
    have hy := hd y h1
    rcases hy with h | h
    · exact valid_of_coeff (a := a) hw (Or.inl (Acoef_ne_zero h)) h2
    · exact valid_of_coeff (a := a) hw (Or.inr (Acoef_ne_zero h)) h2

lemma Acoef_eq_zero_of_invalid {n : ℕ} {w : Idx n} (hw : Valid w) {y : ℕ}
    (h : ¬Valid (snoc w y)) {s : Finset ℕ} (hs : entries w ⊆ s) : Acoef y s = 0 := by
  by_cases hy : y ∈ entries w
  · exact Acoef_eq_zero_of_mem (hs hy)
  · have : y = 0 := by
      by_contra h0
      exact h (valid_snoc hw hy (Nat.one_le_iff_ne_zero.2 h0))
    subst this
    exact Acoef_zero_left _

lemma swap01_cons_cons {n : ℕ} (a b : ℕ) (τ : Idx n) :
    cons a (cons b τ) ∘ swapPerm (n + 2) 0 = cons b (cons a τ) := by
  funext i
  rw [Function.comp_apply, swapPerm_zero_two]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Equiv.swap_apply_left, show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    simp
  · refine Fin.cases ?_ (fun k => ?_) j
    · rw [show (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) from rfl, Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
      simp

/-- **Swap-delete**: `D_k R_k = R_{k-1} D_k S_1`. -/
lemma Dop_Rop (n : ℕ) : Dop (n + 1) ∘ₗ Rop (n + 1) = Rop n ∘ₗ Dop (n + 1) ∘ₗ Sop (n + 2) 0 := by
  apply lhom_ext_bv
  intro σ
  simp only [LinearMap.coe_comp, Function.comp_apply]
  by_cases hσ : Valid σ
  swap
  · rw [Rop_bv_invalid hσ, Sop_bv_invalid hσ, Dop_bv_invalid hσ]; simp
  have e1 : σ = cons (σ 0) (cons (Fin.tail σ 0) (Fin.tail (Fin.tail σ))) := by
    rw [cons_eq_self, cons_eq_self]
  rw [e1] at hσ ⊢
  set a := σ 0
  set b := Fin.tail σ 0
  set τ := Fin.tail (Fin.tail σ)
  obtain ⟨hbτ, ha, ha1⟩ := valid_of_cons hσ
  obtain ⟨hτ, hb, hb1⟩ := valid_of_cons hbτ
  rw [entries_cons] at ha
  have hab : a ≠ b := fun e => ha (e ▸ mem_insert_self _ _)
  have haτ : a ∉ entries τ := fun h => ha (mem_insert_of_mem h)
  set S := insert a (insert b (entries τ))
  set Y := range (bound S)
  have hle : ∀ t ∈ S, t ≤ S.sup id := fun t ht => mem_le_sup ht
  have hsub : ∀ {t : Finset ℕ}, t ⊆ S → Tset t ⊆ Y := fun {t} ht =>
    Tset_subset_of_le fun x hx => by have := hle x (ht hx); omega
  have hT0 : Tset (entries τ) ⊆ Y := hsub (fun x hx => mem_insert_of_mem (mem_insert_of_mem hx))
  have hTb : Tset (insert b (entries τ)) ⊆ Y := hsub (fun x hx => mem_insert_of_mem hx)
  have hTa : Tset (insert a (entries τ)) ⊆ Y := hsub (by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_of_mem hx))
  have hTab : Tset (insert a (insert b (entries τ))) ⊆ Y := hsub (subset_refl _)
  -- left side
  have hL : Dop (n + 1) (Rop (n + 1) (bv (cons a (cons b τ)))) = ∑ y ∈ Y,
      (Eratio a * Eratio b * qc (Acoef y (insert b (entries τ))
        - Acoef y (insert a (insert b (entries τ))))) • bv (snoc τ y) := by
    rw [Rop_cons_diff (Y := Y) hσ (by rw [entries_cons]; exact hTb)
      (by rw [entries_cons]; exact hTab), entries_cons, map_smul, map_sum, smul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hv : Valid (snoc (cons b τ) y)
    · rw [map_smul, Dop_bv_valid hv, snoc_cons_zero, tail_snoc_cons]
      module
    · rw [Acoef_eq_zero_of_invalid hbτ hv (by rw [entries_cons]),
        Acoef_eq_zero_of_invalid hbτ hv (by rw [entries_cons]; exact subset_insert _ _)]
      simp
  -- right side
  have hσ' : Valid (cons b (cons a τ)) := by
    rw [← swap01_cons_cons]; exact valid_comp_perm hσ _
  have hswc : swc (cons a (cons b τ)) 0 = 1 / ((b : ℚ) - a) := by
    simp [swc, getE]
  have hR : Rop n (Dop (n + 1) (Sop (n + 2) 0 (bv (cons a (cons b τ))))) = ∑ y ∈ Y,
      (qc (1 / ((b : ℚ) - a)) * Eratio a * Eratio b *
          qc (Acoef y (entries τ) - Acoef y (insert b (entries τ)))
        + qc (1 - 1 / ((b : ℚ) - a)) * Eratio b * Eratio a *
          qc (Acoef y (entries τ) - Acoef y (insert a (entries τ)))) • bv (snoc τ y) := by
    rw [Sop_bv_valid hσ, swap01_cons_cons, hswc, map_add, map_smul, map_smul, Dop_bv_valid hσ,
      Dop_bv_valid hσ']
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [map_add, map_smul, map_smul, map_smul, map_smul,
      Rop_cons_diff (Y := Y) hbτ hT0 hTb, Rop_cons_diff (Y := Y) (valid_cons hτ haτ ha1) hT0 hTa]
    simp only [smul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    module
  rw [hL, hR]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  rw [scalar_swapDelete (entries τ) hab haτ hb ha1 hb1 y, qc_add, qc_mul, qc_mul]
  ring

lemma Sop_Sop_apply (n s : ℕ) (v : V n) : Sop n s (Sop n s v) = v :=
  LinearMap.congr_fun (Sop_Sop n s) v

/-- `S_{k-1} R_k M_{k-1} = M_{k-1} R_{k-1}`. -/
lemma Sop_Rop_Mop_apply (n : ℕ) (v : V (n + 1)) :
    Sop (n + 2) n (Rop (n + 1) (Mop (n + 1) v)) = Mop (n + 1) (Rop n v) := by
  have := LinearMap.congr_fun (Sop_Mop_Rop n) v
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [← this, Sop_Sop_apply]

/-- `R_{k-1} D_k = D_k R_k S_1`. -/
lemma Rop_Dop_apply (n : ℕ) (v : V (n + 2)) :
    Rop n (Dop (n + 1) v) = Dop (n + 1) (Rop (n + 1) (Sop (n + 2) 0 v)) := by
  have := LinearMap.congr_fun (Dop_Rop n) (Sop (n + 2) 0 v)
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, Sop_Sop_apply]

/-- **Swap-square**: `S_{k-1} R_k² = R_k² S_1`. -/
lemma Sop_Rop_Rop_apply (n : ℕ) (v : V (n + 2)) :
    Sop (n + 2) n (Rop (n + 1) (Rop (n + 1) v)) = Rop (n + 1) (Rop (n + 1) (Sop (n + 2) 0 v)) := by
  conv_lhs => rw [show Rop (n + 1) v = Mop (n + 1) (Dop (n + 1) v) - Dop (n + 2) (Mop (n + 2) v)
    from rfl]
  rw [map_sub, map_sub, Sop_Rop_Mop_apply, Rop_Dop_apply]
  have h3 := LinearMap.congr_fun (Sop_Dop (n := n + 2) (s := n) (by omega))
    (Rop (n + 2) (Sop (n + 3) 0 (Mop (n + 2) v)))
  have h1 := LinearMap.congr_fun (Sop_Mop (n := n + 2) (s := 0) (by omega)) v
  simp only [LinearMap.coe_comp, Function.comp_apply] at h3 h1
  rw [Rop_Dop_apply (n + 1), h3, h1, Sop_Rop_Mop_apply (n + 1)]
  rfl

end ProperCircularArc
