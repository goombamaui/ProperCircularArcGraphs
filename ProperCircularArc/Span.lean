import ProperCircularArc.Construction

/-!
# Equation (rank-span)

Every basis vector `b_{w,y}` is a combination of `M_{k-1} b_w` and of vectors `R_k b_{a,w}` with
`a ∉ w`, `a + 1 ∈ w ∪ {y}`, whose source columns have smaller rank.  We record this as an
induction principle for submodules.
-/

noncomputable section

namespace ProperCircularArc

open Finset

lemma mem_of_bv_mem {n : ℕ} (W : Submodule Lam (V n)) (h : ∀ σ, bv σ ∈ W) (v : V n) : v ∈ W := by
  rw [← Finsupp.sum_single v]
  refine Submodule.finsuppSum_mem _ _ _ _ fun σ _ => ?_
  have : Finsupp.single σ (v σ) = v σ • bv σ := by simp [bv]
  rw [this]
  exact W.smul_mem _ (h σ)

lemma qc_smul_V {n : ℕ} (q : ℚ) (v : V n) : qc q • v = q • v := algebraMap_smul Lam q v

lemma zero_not_mem_entries {n : ℕ} {w : Idx n} (hw : Valid w) : 0 ∉ entries w := fun h => by
  obtain ⟨i, hi⟩ := mem_entries.1 h; have := hw.2 i; omega

/-- The rows of the block system on the tableau side. -/
lemma block_rows {k : ℕ} {w : Idx (k + 1)} (hw : Valid w) (r : Option (Zset (entries w))) :
    ∑ y : Tset (entries w), blockC (entries w) r y • bv (snoc w y) =
      match r with
      | none => Mop (k + 1) (bv w)
      | some z => (E (z.1 - 2) * Einv (z.1 - 1)) • Rop (k + 1) (bv (cons (z.1 - 1) w)) := by
  rcases r with _ | ⟨z, hz⟩
  · rw [Mop_bv_valid hw, ← sum_coe_sort (Tset (entries w))]
    refine sum_congr rfl fun y _ => ?_
    rw [qc_smul_V]; rfl
  · obtain ⟨hzw, hz2, hz1⟩ := mem_Zset.1 hz
    have hv : Valid (cons (z - 1) w) := valid_cons hw hz1 (by omega)
    show _ = (E (z - 2) * Einv (z - 1)) • Rop (k + 1) (bv (cons (z - 1) w))
    rw [Rop_cons hv, Acoef_eq_zero_of_mem (mem_insert_of_mem (show z - 1 + 1 ∈ entries w by
      rwa [Nat.sub_add_cancel (by omega)])), qc_zero, zero_smul, sub_zero, smul_smul,
      show z - 2 = z - 1 - 1 by omega, mul_comm (E (z - 1 - 1) * Einv (z - 1)), Eratio_mul_inv,
      one_smul, ← sum_coe_sort (Tset (entries w))]
    refine sum_congr rfl fun y _ => ?_
    rw [qc_smul_V]
    simp only [blockC]
    congr 2
    push_cast [show 1 ≤ z by omega]
    ring

/-- **Rank-span**, as an induction principle. -/
theorem span_induction {k : ℕ} (W : Submodule Lam (V (k + 2)))
    (hinv : ∀ σ, ¬Valid σ → bv σ ∈ W)
    (hM : ∀ v, Mop (k + 1) v ∈ W)
    (hR : ∀ (w : Idx (k + 1)) (y a : ℕ), Valid (snoc w y) → a ∉ entries w → 1 ≤ a →
      (a + 1 ∈ entries w ∨ a + 1 = y) →
      (∀ τ : Idx (k + 2), rk τ < rk (snoc w y) → bv τ ∈ W) →
      Rop (k + 1) (bv (cons a w)) ∈ W) :
    ∀ σ, bv σ ∈ W := by
  intro σ
  induction hn : rk σ using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
  by_cases hσ : Valid σ
  swap
  · exact hinv σ hσ
  have ih' : ∀ τ : Idx (k + 2), rk τ < rk σ → bv τ ∈ W := fun τ hτ => ih _ (hn ▸ hτ) τ rfl
  rw [← snoc_eq_self σ] at hσ ih' ⊢
  set w := Fin.init σ
  set y := σ (Fin.last (k + 1))
  obtain ⟨hw, hyw, hy1⟩ := valid_of_snoc hσ
  have h0 := zero_not_mem_entries hw
  by_cases hy : y ∈ Tset (entries w)
  · -- block case
    have := blockInvert (entries w) h0 (fun y' : Tset (entries w) => bv (snoc w y')) ⟨y, hy⟩
    rw [← this]
    refine W.sum_mem fun r _ => ?_
    rw [← qc_smul_V]
    refine W.smul_mem _ ?_
    rw [block_rows hw r]
    rcases r with _ | ⟨z, hz⟩
    · exact hM _
    · obtain ⟨hzw, hz2, hz1⟩ := mem_Zset.1 hz
      refine W.smul_mem _ (hR w y (z - 1) hσ hz1 (by omega) (Or.inl ?_) ih')
      rwa [Nat.sub_add_cancel (by omega)]
  · -- free case
    have hy2 : 2 ≤ y := by
      by_contra h; apply hy; rw [mem_Tset]; exact ⟨hyw, Or.inl (by omega)⟩
    have hy1w : y - 1 ∉ entries w := fun h => hy (mem_Tset.2 ⟨hyw, Or.inr ⟨by omega, h⟩⟩)
    have hvc : Valid (cons (y - 1) w) := valid_cons hw hy1w (by omega)
    have hc : Acoef y (insert (y - 1) (entries w)) ≠ 0 := by
      apply Acoef_ne_zero
      rw [mem_Tset]; simp only [mem_insert, not_or]
      exact ⟨⟨by omega, hyw⟩, Or.inr ⟨by omega, by simp⟩⟩
    have hRf := Rop_cons hvc
    rw [Nat.sub_add_cancel (by omega)] at hRf
    -- solve the free equation for `b_{w,y}`
    have key : bv (snoc w y) = qc (1 / Acoef y (insert (y - 1) (entries w))) •
        ((∑ z ∈ Tset (entries w), qc (Acoef z (entries w) / ((y - 1 : ℕ) + 1 - z : ℚ)) •
          bv (snoc w z)) - (E (y - 2) * Einv (y - 1)) • Rop (k + 1) (bv (cons (y - 1) w))) := by
      rw [hRf, smul_smul, show y - 2 = y - 1 - 1 by omega, mul_comm (E (y - 1 - 1) * _),
        Eratio_mul_inv, one_smul, sub_sub_cancel, smul_smul, ← qc_mul, one_div_mul_cancel hc,
        qc_one, one_smul]
    rw [key]
    refine W.smul_mem _ (W.sub_mem (W.sum_mem fun z hz => W.smul_mem _ ?_) (W.smul_mem _ ?_))
    · exact ih' _ (rk_free_block hσ hy hz)
    · exact hR w y (y - 1) hσ hy1w (by omega) (Or.inr (by omega)) ih'

/-- The coarse form: `V_{n+1} = M_n V_n + R_{n+1} V_{n+1}` up to invalid vectors. -/
theorem coarse_induction (n : ℕ) (W : Submodule Lam (V (n + 1)))
    (hinv : ∀ σ, ¬Valid σ → bv σ ∈ W) (hM : ∀ v, Mop n v ∈ W) (hR : ∀ v, Rop n v ∈ W) :
    ∀ v, v ∈ W := by
  refine mem_of_bv_mem W ?_
  rcases n with _ | k
  · -- level one: induction on the entry
    intro σ
    rw [← cons_eq_self σ]
    have hσ0 : Fin.tail σ = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hσ0]
    generalize σ 0 = a
    induction a with
    | zero =>
      apply hinv
      intro h
      have := h.2 0
      simp at this
    | succ a ih =>
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · have := hM (bv (Fin.elim0 : Idx 0))
        rw [Mop_bv_valid (valid_zero _), entries_zero, Tset_empty, sum_singleton,
          Acoef_one_empty, qc_one, one_smul] at this
        convert this using 2
        funext i; have : i = 0 := Fin.ext (by omega)
        subst this; rfl
      · have hva : Valid (cons a (Fin.elim0 : Idx 0)) := valid_cons (valid_zero _) (by simp [entries_zero]) ha
        have hRa := Rop_cons hva
        rw [entries_zero, Tset_empty, sum_singleton, Acoef_one_empty, insert_empty_eq a,
          Acoef_succ_singleton ha] at hRa
        have h1 : bv (snoc (Fin.elim0 : Idx 0) 1) ∈ W := by
          have := hM (bv (Fin.elim0 : Idx 0))
          rw [Mop_bv_valid (valid_zero _), entries_zero, Tset_empty, sum_singleton,
            Acoef_one_empty, qc_one, one_smul] at this
          exact this
        have hcons : ∀ b, cons b (Fin.elim0 : Idx 0) = snoc (Fin.elim0 : Idx 0) b := by
          intro b; funext i; have : i = 0 := Fin.ext (by omega)
          subst this; rfl
        rw [hcons]
        have haq : ((a : ℚ) + 1) / a ≠ 0 := by positivity
        have key : bv (snoc (Fin.elim0 : Idx 0) (a + 1)) =
            qc (1 / (((a : ℚ) + 1) / a)) • (qc (1 / ((a : ℚ) + 1 - (1 : ℕ))) •
              bv (snoc (Fin.elim0 : Idx 0) 1) - (E (a - 1) * Einv a) • Rop 0 (bv (cons a Fin.elim0))) := by
          rw [hRa, smul_smul, mul_comm (E (a - 1) * _), Eratio_mul_inv, one_smul, sub_sub_cancel,
            smul_smul, ← qc_mul, one_div_mul_cancel haq, qc_one, one_smul]
        rw [key]
        exact W.smul_mem _ (W.sub_mem (W.smul_mem _ h1) (W.smul_mem _ (hR _)))
  · exact span_induction W hinv hM (fun _ _ _ _ _ _ _ _ => hR _)

end ProperCircularArc
