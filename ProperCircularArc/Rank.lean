import ProperCircularArc.Tableau

/-!
# The rank used to construct `U_k`

For `σ = (w, y)` at level `k + 1`, the paper's rank vector `r(w, y)` has entry `k + 1 - s` at
the value `w_s` (0-based `s`), entry `1` at `y` if `y ∉ T(w)`, and `0` elsewhere; ranks are
compared at the largest differing index.  All entries are at most `k + 1`, so we encode the rank
vector as a number written in base `k + 2`.
-/

namespace ProperCircularArc

open Finset

/-! ## Base-`B` comparison -/

lemma sum_digits_lt_pow {B : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < B) (n : ℕ) :
    ∑ j ∈ range n, d j * B ^ j < B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have := hd n
    nlinarith [pow_pos (show 0 < B by omega) n]

lemma digits_lt {B M : ℕ} {d d' : ℕ → ℕ} (hd : ∀ j, d j < B) (j0 : ℕ) (hj0 : j0 < M)
    (hlt : d j0 < d' j0) (hhi : ∀ j, j0 < j → d j = d' j) :
    ∑ j ∈ range M, d j * B ^ j < ∑ j ∈ range M, d' j * B ^ j := by
  have hsplit : ∀ f : ℕ → ℕ, ∑ j ∈ range M, f j =
      ∑ j ∈ range j0, f j + f j0 + ∑ j ∈ Ico (j0 + 1) M, f j := by
    intro f
    rw [← sum_range_succ, sum_range_add_sum_Ico _ (by omega)]
  rw [hsplit, hsplit (fun j => d' j * B ^ j)]
  have hhigh : ∑ j ∈ Ico (j0 + 1) M, d j * B ^ j = ∑ j ∈ Ico (j0 + 1) M, d' j * B ^ j :=
    sum_congr rfl fun j hj => by rw [hhi j (by simp at hj; omega)]
  rw [hhigh]
  have hlow := sum_digits_lt_pow hd j0
  have : d j0 * B ^ j0 + B ^ j0 ≤ d' j0 * B ^ j0 := by
    have : (d j0 + 1) * B ^ j0 ≤ d' j0 * B ^ j0 := Nat.mul_le_mul_right _ hlt
    linarith
  have : 0 ≤ ∑ j ∈ range j0, d' j * B ^ j := Nat.zero_le _
  omega

/-! ## Digits of a tableau index -/

/-- The weight of position `i` of `σ = (w, y)`: `k + 1 - i` for `i < k`, and for the last
position `1` or `0` according to whether `y ∉ T(w)`. -/
def wt {k : ℕ} (σ : Idx (k + 1)) (i : Fin (k + 1)) : ℕ :=
  if (i : ℕ) < k then k + 1 - i
  else if σ (Fin.last k) ∈ Tset (entries (Fin.init σ)) then 0 else 1

/-- The entry of the rank vector at the value `j`. -/
def digit {k : ℕ} (σ : Idx (k + 1)) (j : ℕ) : ℕ := ∑ i, if σ i = j then wt σ i else 0

/-- The rank, as a number in base `k + 2`. -/
def rk {k : ℕ} (σ : Idx (k + 1)) : ℕ :=
  ∑ j ∈ range ((entries σ).sup id + 1), digit σ j * (k + 2) ^ j

lemma wt_le {k : ℕ} (σ : Idx (k + 1)) (i : Fin (k + 1)) : wt σ i ≤ k + 1 := by
  unfold wt; split_ifs <;> omega

lemma digit_eq_zero {k : ℕ} {σ : Idx (k + 1)} {j : ℕ} (hj : j ∉ entries σ) : digit σ j = 0 :=
  sum_eq_zero fun i _ => if_neg fun h => hj (mem_entries.2 ⟨i, h⟩)

lemma digit_eq_wt {k : ℕ} {σ : Idx (k + 1)} (hσ : Function.Injective σ) (i : Fin (k + 1)) :
    digit σ (σ i) = wt σ i := by
  unfold digit
  rw [sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [if_neg fun h => hi' (hσ h)]
  · simp

lemma digit_lt {k : ℕ} {σ : Idx (k + 1)} (hσ : Function.Injective σ) (j : ℕ) :
    digit σ j < k + 2 := by
  by_cases hj : j ∈ entries σ
  · obtain ⟨i, rfl⟩ := mem_entries.1 hj
    rw [digit_eq_wt hσ]
    have := wt_le σ i
    omega
  · rw [digit_eq_zero hj]; omega

lemma rk_eq {k : ℕ} (σ : Idx (k + 1)) {M : ℕ} (hM : ∀ t ∈ entries σ, t < M) :
    rk σ = ∑ j ∈ range M, digit σ j * (k + 2) ^ j := by
  unfold rk
  set M0 := (entries σ).sup id + 1
  have hzero : ∀ j, M0 ≤ j → digit σ j = 0 := by
    intro j hj
    apply digit_eq_zero
    intro hm
    have := le_sup (f := id) hm
    simp only [id] at this
    omega
  rcases le_total M0 M with h | h
  · rw [← sum_range_add_sum_Ico _ h]
    have : ∑ j ∈ Ico M0 M, digit σ j * (k + 2) ^ j = 0 :=
      sum_eq_zero fun j hj => by rw [hzero j (by simp at hj; omega), zero_mul]
    rw [this, add_zero]
  · rw [← sum_range_add_sum_Ico _ h]
    have : ∑ j ∈ Ico M M0, digit σ j * (k + 2) ^ j = 0 :=
      sum_eq_zero fun j hj => by
        have : j ∉ entries σ := fun hm => by have := hM j hm; simp at hj; omega
        rw [digit_eq_zero this, zero_mul]
    rw [this, add_zero]

/-- Comparison of ranks by the largest differing digit. -/
lemma rk_lt {k : ℕ} {σ τ : Idx (k + 1)} (hσ : Function.Injective σ) (j0 : ℕ)
    (hlt : digit σ j0 < digit τ j0) (hhi : ∀ j, j0 < j → digit σ j = digit τ j) :
    rk σ < rk τ := by
  set M := (entries σ ∪ entries τ ∪ {j0}).sup id + 1
  have hM : ∀ t ∈ entries σ ∪ entries τ ∪ {j0}, t < M := fun t ht => by
    have := le_sup (f := id) ht; simp only [id] at this; omega
  rw [rk_eq σ (M := M) (fun t ht => hM t (by simp [ht])),
    rk_eq τ (M := M) (fun t ht => hM t (by simp [ht]))]
  exact digits_lt (digit_lt hσ) j0 (hM j0 (by simp)) hlt hhi

/-! ## Digits of `(w, y)` and of `(a, w)` -/

lemma digit_snoc_of_lt {k : ℕ} {w : Idx k} {y : ℕ} (h : Function.Injective (snoc w y)) (s : Fin k) :
    digit (snoc w y) (w s) = k + 1 - s := by
  have := digit_eq_wt h s.castSucc
  simp only [Fin.snoc_castSucc] at this
  rw [this, wt, ite_cond_eq_true _ _ (eq_true (by simp))]
  simp

lemma digit_snoc_last {k : ℕ} {w : Idx k} {y : ℕ} (h : Function.Injective (snoc w y)) :
    digit (snoc w y) y = if y ∈ Tset (entries w) then 0 else 1 := by
  have := digit_eq_wt h (Fin.last k)
  simp only [Fin.snoc_last] at this
  rw [this, wt, ite_cond_eq_false _ _ (eq_false (by simp))]
  simp [Fin.init_snoc]

lemma init_cons_eq {k : ℕ} (a : ℕ) (w : Idx (k + 1)) :
    Fin.init (cons a w) = cons a (Fin.init w) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [Fin.init]

lemma digit_cons_head {k : ℕ} {a : ℕ} {w : Idx (k + 1)} (h : Function.Injective (cons a w)) :
    digit (cons a w) a = k + 2 := by
  have := digit_eq_wt h 0
  simp only [Fin.cons_zero] at this
  rw [this, wt, ite_cond_eq_true _ _ (eq_true (by simp))]
  simp

lemma digit_cons_tail_le {k : ℕ} {a : ℕ} {w : Idx (k + 1)} (h : Function.Injective (cons a w))
    (s : Fin (k + 1)) : digit (cons a w) (w s) ≤ k + 1 - s := by
  have := digit_eq_wt h s.succ
  simp only [Fin.cons_succ] at this
  rw [this, wt]
  split_ifs with h1 <;> simp at h1 ⊢; omega

/-! ## The three dependencies of the construction decrease the rank -/

lemma digit_snoc_of_not_mem {k : ℕ} {w : Idx k} {y j : ℕ} (hjw : j ∉ entries w) (hjy : j ≠ y) :
    digit (snoc w y) j = 0 :=
  digit_eq_zero (by rw [entries_snoc]; simp [hjw, hjy])

lemma digit_cons_of_not_mem {k : ℕ} {w : Idx k} {a j : ℕ} (hjw : j ∉ entries w) (hja : j ≠ a) :
    digit (cons a w) j = 0 :=
  digit_eq_zero (by rw [entries_cons]; simp [hjw, hja])

/-- Block equations: `r(z - 1, w) < r(w, y)` for `y ∈ T(w)`, `z ∈ Z(w)`. -/
lemma rk_block {k : ℕ} {w : Idx (k + 1)} {y z : ℕ} (hv : Valid (snoc w y))
    (hy : y ∈ Tset (entries w)) (hz : z ∈ Zset (entries w)) :
    rk (cons (z - 1) w) < rk (snoc w y) := by
  obtain ⟨hzw, hz2, hz1⟩ := mem_Zset.1 hz
  have hw := (valid_of_snoc hv).1
  have hvc : Valid (cons (z - 1) w) := valid_cons hw hz1 (by omega)
  have hne : (entries w).Nonempty := ⟨z, hzw⟩
  set m := (entries w).max' hne
  have hm : m ∈ entries w := max'_mem _ _
  have hle : ∀ t ∈ entries w, t ≤ m := fun t ht => le_max' _ _ ht
  obtain ⟨s, hs⟩ := mem_entries.1 hm
  have hzm : z - 1 < m := by have := hle z hzw; omega
  refine rk_lt hvc.1 m ?_ ?_
  · rw [← hs, digit_snoc_of_lt hv.1]
    have := digit_cons_tail_le hvc.1 s
    omega
  · intro j hj
    have hjw : j ∉ entries w := fun h => by have := hle j h; omega
    rw [digit_cons_of_not_mem hjw (by omega)]
    by_cases hjy : j = y
    · subst hjy; rw [digit_snoc_last hv.1, if_pos hy]
    · rw [digit_snoc_of_not_mem hjw hjy]

/-- Free equations, first dependency: `r(w, z) < r(w, y)` for `z ∈ T(w)`, `y ∉ T(w)`. -/
lemma rk_free_block {k : ℕ} {w : Idx k} {y z : ℕ} (hv : Valid (snoc w y))
    (hy : y ∉ Tset (entries w)) (hz : z ∈ Tset (entries w)) :
    rk (snoc w z) < rk (snoc w y) := by
  have hw := (valid_of_snoc hv).1
  have hyw := (valid_of_snoc hv).2.1
  have hvz : Valid (snoc w z) := valid_snoc_of_mem_Tset hw hz
  have hzy : z ≠ y := fun e => hy (e ▸ hz)
  have hzw : z ∉ entries w := not_mem_of_mem_Tset hz
  refine rk_lt hvz.1 y ?_ ?_
  · rw [digit_snoc_of_not_mem hyw (Ne.symm hzy), digit_snoc_last hv.1, if_neg hy]
    omega
  · intro j _
    by_cases hjw : j ∈ entries w
    · obtain ⟨s, rfl⟩ := mem_entries.1 hjw
      rw [digit_snoc_of_lt hvz.1, digit_snoc_of_lt hv.1]
    · by_cases hjz : j = z
      · subst hjz
        rw [digit_snoc_last hvz.1, if_pos hz, digit_snoc_of_not_mem hjw hzy]
      · by_cases hjy : j = y
        · omega
        · rw [digit_snoc_of_not_mem hjw hjz, digit_snoc_of_not_mem hjw hjy]

/-- Free equations, second dependency: `r(y - 1, w) < r(w, y)` for `y ∉ T(w)`. -/
lemma rk_free_cons {k : ℕ} {w : Idx (k + 1)} {y : ℕ} (hv : Valid (snoc w y))
    (hy : y ∉ Tset (entries w)) : rk (cons (y - 1) w) < rk (snoc w y) := by
  obtain ⟨hw, hyw, hy1⟩ := valid_of_snoc hv
  have hy2 : 2 ≤ y := by
    by_contra h
    apply hy
    rw [mem_Tset]
    exact ⟨hyw, Or.inl (by omega)⟩
  have hy1w : y - 1 ∉ entries w := fun h => hy (mem_Tset.2 ⟨hyw, Or.inr ⟨by omega, h⟩⟩)
  have hvc : Valid (cons (y - 1) w) := valid_cons hw hy1w (by omega)
  have hne : (entries w).Nonempty := ⟨w 0, mem_entries.2 ⟨0, rfl⟩⟩
  set m := (entries w).max' hne
  have hm : m ∈ entries w := max'_mem _ _
  have hle : ∀ t ∈ entries w, t ≤ m := fun t ht => le_max' _ _ ht
  rcases lt_or_gt_of_ne (show m ≠ y from fun e => hyw (e ▸ hm)) with hmy | hmy
  · -- `y` is the largest entry
    refine rk_lt hvc.1 y ?_ ?_
    · rw [digit_cons_of_not_mem hyw (by omega), digit_snoc_last hv.1, if_neg hy]
      omega
    · intro j hj
      have hjw : j ∉ entries w := fun h => by have := hle j h; omega
      rw [digit_cons_of_not_mem hjw (by omega), digit_snoc_of_not_mem hjw (by omega)]
  · -- the largest entry lies in `w`
    obtain ⟨s, hs⟩ := mem_entries.1 hm
    refine rk_lt hvc.1 m ?_ ?_
    · rw [← hs, digit_snoc_of_lt hv.1]
      have := digit_cons_tail_le hvc.1 s
      omega
    · intro j hj
      have hjw : j ∉ entries w := fun h => by have := hle j h; omega
      rw [digit_cons_of_not_mem hjw (by omega), digit_snoc_of_not_mem hjw (by omega)]

/-! ## Ranks of the `R`-columns in the rank-span -/

/-- `r(a, w) < r(w, y)` whenever `a ∉ w` and `a + 1 ∈ w ∪ {y}`. -/
lemma rk_cons_lt {k : ℕ} {w : Idx (k + 1)} {y a : ℕ} (hv : Valid (snoc w y))
    (ha : a ∉ entries w) (ha1 : 1 ≤ a) (hay : a + 1 ∈ entries w ∨ a + 1 = y) :
    rk (cons a w) < rk (snoc w y) := by
  obtain ⟨hw, hyw, hy1⟩ := valid_of_snoc hv
  have hvc : Valid (cons a w) := valid_cons hw ha ha1
  have hne : (entries w).Nonempty := ⟨w 0, mem_entries.2 ⟨0, rfl⟩⟩
  set m := (entries w).max' hne
  have hm : m ∈ entries w := max'_mem _ _
  have hle : ∀ t ∈ entries w, t ≤ m := fun t ht => le_max' _ _ ht
  have hym : y ≠ m := fun e => hyw (e ▸ hm)
  by_cases hA : y ∉ Tset (entries w) ∧ m < y
  · obtain ⟨hyT, hmy⟩ := hA
    have hay' : a < y := by
      rcases hay with h | h
      · have := hle _ h; omega
      · omega
    refine rk_lt hvc.1 y ?_ ?_
    · rw [digit_cons_of_not_mem hyw (by omega), digit_snoc_last hv.1, if_neg hyT]
      omega
    · intro j hj
      have hjw : j ∉ entries w := fun h => by have := hle j h; omega
      rw [digit_cons_of_not_mem hjw (by omega), digit_snoc_of_not_mem hjw (by omega)]
  · have ham : a < m := by
      rcases hay with h | h
      · have := hle _ h; omega
      · subst h
        by_contra hge
        push Not at hge
        apply hA
        refine ⟨fun hT => ?_, by omega⟩
        rcases (mem_Tset.1 hT).2 with h | ⟨_, h⟩
        · omega
        · exact ha (by simpa using h)
    obtain ⟨s, hs⟩ := mem_entries.1 hm
    refine rk_lt hvc.1 m ?_ ?_
    · rw [← hs, digit_snoc_of_lt hv.1]
      have := digit_cons_tail_le hvc.1 s
      omega
    · intro j hj
      have hjw : j ∉ entries w := fun h => by have := hle j h; omega
      rw [digit_cons_of_not_mem hjw (by omega)]
      by_cases hjy : j = y
      · subst hjy
        rw [digit_snoc_last hv.1]
        have : j ∈ Tset (entries w) := by
          by_contra hT; exact hA ⟨hT, hj⟩
        rw [if_pos this]
      · rw [digit_snoc_of_not_mem hjw hjy]

lemma tail_eq_cons {k : ℕ} (w : Idx (k + 1)) : w = cons (w 0) (Fin.tail w) := (cons_eq_self w).symm

/-- `r(τ_1(a, w)) < r(w, y)` whenever `a ∉ w`, `a + 1 ∈ w ∪ {y}` and `a + 1 ≠ w_1`. -/
lemma rk_swap_lt {k : ℕ} {w : Idx (k + 1)} {y a : ℕ} (hv : Valid (snoc w y))
    (ha : a ∉ entries w) (ha1 : 1 ≤ a) (hay : a + 1 ∈ entries w ∨ a + 1 = y) (ha0 : a + 1 ≠ w 0) :
    rk (cons (w 0) (cons a (Fin.tail w))) < rk (snoc w y) := by
  obtain ⟨hw, hyw, hy1⟩ := valid_of_snoc hv
  have hvc : Valid (cons a w) := valid_cons hw ha ha1
  set τ := cons (w 0) (cons a (Fin.tail w))
  have hτ : Valid τ := by
    have := valid_comp_perm hvc (swapPerm (k + 2) 0)
    have e : cons a w ∘ swapPerm (k + 2) 0 = τ := by
      conv_lhs => rw [tail_eq_cons w]
      funext i
      rw [Function.comp_apply, swapPerm_zero_two]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Equiv.swap_apply_left, show (1 : Fin (k + 2)) = Fin.succ 0 from rfl]; simp [τ]
      · refine Fin.cases ?_ (fun l => ?_) j
        · rw [show (Fin.succ (0 : Fin (k + 1))) = (1 : Fin (k + 2)) from rfl,
            Equiv.swap_apply_right]; simp [τ]
        · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
          simp [τ, Fin.tail]
    rwa [e] at this
  -- digits of `τ`
  have hd0 : digit τ (w 0) = digit (snoc w y) (w 0) := by
    have h1 := digit_eq_wt hτ.1 0
    have h2 := digit_snoc_of_lt hv.1 0
    simp only [τ, cons_zero'] at h1
    rw [h1, h2, wt]; simp
  have hdi : ∀ i : Fin k, digit τ (w i.succ) < digit (snoc w y) (w i.succ) := by
    intro i
    have h1 := digit_eq_wt hτ.1 i.succ.succ
    simp only [τ, cons_succ'] at h1
    rw [show Fin.tail w i = w i.succ from rfl] at h1
    rw [h1, digit_snoc_of_lt hv.1, wt]
    split_ifs with h <;> simp at h ⊢ <;> omega
  have hda : digit τ a ≤ k + 1 := by
    have h1 := digit_eq_wt hτ.1 (1 : Fin (k + 2))
    rw [show (1 : Fin (k + 2)) = Fin.succ 0 from rfl] at h1
    simp only [τ, cons_succ', cons_zero'] at h1
    rw [h1, wt]; split_ifs <;> simp <;> omega
  have hτentries : ∀ j, j ∈ entries τ ↔ j = w 0 ∨ j = a ∨ ∃ i : Fin k, w i.succ = j := by
    intro j
    rw [show entries τ = insert (w 0) (insert a (entries (Fin.tail w))) by
      simp [τ, entries_cons]]
    simp [mem_entries, Fin.tail]
  -- the candidates where the digit of `snoc w y` exceeds that of `τ`
  let Cw : Finset ℕ := univ.image (fun i : Fin k => w i.succ)
  let C : Finset ℕ := Cw ∪ (if y ∉ Tset (entries w) then {y} else ∅)
  have haC : a + 1 ∈ C := by
    rcases hay with h | h
    · obtain ⟨i, hi⟩ := mem_entries.1 h
      refine mem_union_left _ (mem_image.2 ⟨Fin.pred i (fun e => ha0 (by rw [← hi, e])), mem_univ _,
        by rw [Fin.succ_pred]; exact hi⟩)
    · have hyT : y ∉ Tset (entries w) := fun hT => by
        rcases (mem_Tset.1 hT).2 with h' | ⟨_, h'⟩
        · omega
        · exact ha (by rw [← h] at h'; simpa using h')
      exact mem_union_right _ (by rw [if_pos hyT]; exact mem_singleton.2 h)
  have hCne : C.Nonempty := ⟨_, haC⟩
  set M := C.max' hCne
  have hMC : M ∈ C := max'_mem _ _
  have hleC : ∀ t ∈ C, t ≤ M := fun t ht => le_max' _ _ ht
  have haM : a < M := by have := hleC _ haC; omega
  -- digits above `M` agree
  have hhi : ∀ j, M < j → digit τ j = digit (snoc w y) j := by
    intro j hj
    by_cases hj0 : j = w 0
    · subst hj0; exact hd0
    have hjτ : j ∉ entries τ := by
      rw [hτentries]
      rintro (h | h | ⟨i, hi⟩)
      · exact hj0 h
      · omega
      · have := hleC j (mem_union_left _ (mem_image.2 ⟨i, mem_univ _, hi⟩)); omega
    rw [digit_eq_zero hjτ]
    by_cases hjy : j = y
    · subst hjy
      rw [digit_snoc_last hv.1]
      by_cases hT : j ∈ Tset (entries w)
      · rw [if_pos hT]
      · exfalso
        have := hleC j (mem_union_right _ (by rw [if_pos hT]; exact mem_singleton_self _))
        omega
    · have hjw : j ∉ entries w := by
        intro h
        obtain ⟨i, hi⟩ := mem_entries.1 h
        rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨i', hi'⟩
        · exact hj0 (by rw [← hi, h0])
        · have := hleC j (mem_union_left _ (mem_image.2 ⟨i', mem_univ _, by rw [← hi, hi']⟩))
          omega
      rw [digit_snoc_of_not_mem hjw hjy]
  refine rk_lt hτ.1 M ?_ hhi
  rcases mem_union.1 hMC with h | h
  · obtain ⟨i, _, hi⟩ := mem_image.1 h
    rw [← hi]; exact hdi i
  · by_cases hyT : y ∉ Tset (entries w)
    · rw [if_pos hyT] at h
      have hMy : M = y := mem_singleton.1 h
      have hyτ : y ∉ entries τ := by
        rw [hτentries]
        rintro (h' | h' | ⟨i, hi⟩)
        · exact hyw (by rw [h']; exact mem_entries.2 ⟨0, rfl⟩)
        · omega
        · exact hyw (by rw [← hi]; exact mem_entries.2 ⟨_, rfl⟩)
      rw [hMy, digit_eq_zero hyτ, digit_snoc_last hv.1, if_neg hyT]
      omega
    · rw [if_neg hyT] at h
      simp at h

end ProperCircularArc
