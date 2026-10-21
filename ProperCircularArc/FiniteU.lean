import ProperCircularArc.FiniteColor
import ProperCircularArc.Intertwine

/-!
# The change of basis with `N` colours

`U_k^{(N)}` is the matrix whose column `σ` (a tuple of distinct columns in `[N]`) is the
specialisation of `U_k b_σ`.  We prove the vanishing lemma (Lemma `vanish`) and the finite
intertwining relations.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

/-- Columns `1, …, N` of a tuple of distinct elements of `Fin N`. -/
def shift {N k : ℕ} (σ : Inj N k) : Idx k := fun r => (σ r : ℕ) + 1

lemma shift_valid {N k : ℕ} (σ : Inj N k) : Valid (shift σ) :=
  ⟨fun a b h => σ.injective (Fin.ext (by simpa [shift] using h)), fun r => by simp [shift]⟩

lemma shift_le {N k : ℕ} (σ : Inj N k) (r : Fin k) : shift σ r ≤ N := by
  simp only [shift]; have := (σ r).2; omega

/-- The matrix `U_k^{(N)}`: rows are colour tuples, columns tableau tuples. -/
def UN (N k : ℕ) : Matrix (Inj N k) (Inj N k) (KN N) := fun i σ => specV N k (U k (shift σ)) i

lemma U_adm_of_le {N k : ℕ} {σ : Idx k} (h : ∀ r, σ r ≤ N + 1) : U k σ ∈ AdmV N k := U_adm N k σ h

lemma Eratio_mem {N a : ℕ} (ha : a ≤ N) : Eratio a ∈ AdmC N :=
  Subalgebra.mul_mem _ (E_mem N a) (Einv_mem (by omega))

lemma specCoeff_Eratio {N a : ℕ} (ha : a ≤ N) :
    specCoeff N (Eratio a) = eK N a * (eK N (a - 1))⁻¹ := by
  rw [Eratio, ← iotaN_EN N a, ← iotaN_EinvN N (a - 1) (by omega), ← map_mul, specCoeff_iotaN,
    map_mul, psiN_EN, psiN_EinvN]

lemma specCoeff_Eratio_ne_zero {N a : ℕ} (ha : a ≤ N) : specCoeff N (Eratio a) ≠ 0 := by
  rw [specCoeff_Eratio ha]
  exact mul_ne_zero (eK_ne_zero ha) (inv_ne_zero (eK_ne_zero (by omega)))

lemma isEmpty_Inj {N k : ℕ} (h : N < k) : IsEmpty (Inj N k) :=
  Function.Embedding.isEmpty_of_card_lt (by simpa using h)

/-- **Lemma `vanish`**: if all entries of `σ` are at most `N + 1` and one of them is `N + 1`,
the specialisation of `U_k b_σ` vanishes. -/
theorem vanish (N : ℕ) : ∀ d k, N + 1 = k + d → ∀ σ : Idx k, (∀ r, σ r ≤ N + 1) →
    (∃ r, σ r = N + 1) → specV N k (U k σ) = 0 := by
  intro d
  induction d with
  | zero =>
    intro k hk σ _ _
    haveI := isEmpty_Inj (N := N) (k := k) (by omega)
    funext i; exact isEmptyElim i
  | succ d ih =>
    intro k hk σ hσ hN
    by_cases hv : Valid σ
    swap
    · rcases k with _ | k
      · obtain ⟨r, _⟩ := hN; exact Fin.elim0 r
      · rw [U_invalid hv, specV_zero]
    -- a column in `[1, N]` not used by `σ`
    obtain ⟨a, ha1, haN, haσ⟩ : ∃ a, 1 ≤ a ∧ a ≤ N ∧ a ∉ entries σ := by
      by_contra hne
      push Not at hne
      have hsub : insert (N + 1) (Icc 1 N) ⊆ entries σ := by
        intro t ht
        rcases mem_insert.1 ht with rfl | ht
        · obtain ⟨r, hr⟩ := hN; exact mem_entries.2 ⟨r, hr⟩
        · rw [mem_Icc] at ht; exact hne t ht.1 ht.2
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem (by simp), Nat.card_Icc] at h1
      have h2 : (entries σ).card ≤ k := by
        rw [entries]; exact card_image_le.trans (by simp)
      omega
    have hτ : Valid (cons a σ) := valid_cons hv haσ ha1
    have hτN : ∀ r, cons a σ r ≤ N + 1 := by
      intro r; refine Fin.cases ?_ (fun r' => ?_) r
      · simp; omega
      · simpa using hσ r'
    have hτ0 := ih (k + 1) (by omega) (cons a σ) hτN (by
      obtain ⟨r, hr⟩ := hN; exact ⟨r.succ, by simpa using hr⟩)
    have hD := U_D k (bv (cons a σ))
    rw [Dop_bv_valid hτ, Ul_bv] at hD
    simp only [cons_zero', tail_cons', map_smul, Ul_bv] at hD
    have h2 := congrArg (specV N k) hD
    rw [specV_Dh (U_adm_of_le hτN), hτ0, mulVec_zero,
      specV_smul (Eratio_mem haN) (U_adm_of_le (fun r => hσ r))] at h2
    funext i
    have := congrFun h2 i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (specCoeff_Eratio_ne_zero haN)

/-! ## The finite tableau matrices -/

/-- The finite tableau matrix `M_k^{(N)}` (drop the terms `b_{σ, N+1}`). -/
def MT (N k : ℕ) : Matrix (Inj N (k + 1)) (Inj N k) (KN N) :=
  fun j i => if embInit j = i then (Acoef ((j (Fin.last k) : ℕ) + 1) (entries (shift i)) : KN N)
    else 0

/-- The finite tableau matrix `D_{k+1}` with `e_j = e_j(x_1, …, x_N)`. -/
def DT (N k : ℕ) : Matrix (Inj N k) (Inj N (k + 1)) (KN N) :=
  fun i j => if embTail j = i then eK N ((j 0 : ℕ) + 1) * (eK N (j 0 : ℕ))⁻¹ else 0

lemma shift_embTail {N k : ℕ} (j : Inj N (k + 1)) : shift (embTail j) = Fin.tail (shift j) := rfl

lemma shift_embInit {N k : ℕ} (j : Inj N (k + 1)) : shift (embInit j) = Fin.init (shift j) := rfl

/-- **Finite (D)**: `D̂_{k+1} U_{k+1}^{(N)} = U_k^{(N)} D_{k+1}`. -/
theorem UN_D (N k : ℕ) : Dmat N k * UN N (k + 1) = UN N k * DT N k := by
  ext i j
  rw [mul_apply, mul_apply]
  have hcol : (fun j' => UN N (k + 1) j' j) = specV N (k + 1) (U (k + 1) (shift j)) := rfl
  have h1 : ∑ j', Dmat N k i j' * UN N (k + 1) j' j = (Dmat N k *ᵥ specV N (k + 1)
      (U (k + 1) (shift j))) i := rfl
  rw [h1, ← specV_Dh (U_adm_of_le fun r => by have := shift_le j r; omega)]
  have hD := U_D k (bv (shift j))
  rw [Dop_bv_valid (shift_valid j), Ul_bv, map_smul, Ul_bv] at hD
  rw [hD, specV_smul (G := U k (Fin.tail (shift j))) (Eratio_mem (shift_le j 0))
    (U_adm_of_le fun r => Nat.le_succ_of_le (shift_le (embTail j) r))]
  rw [sum_eq_single (embTail j)]
  · simp only [DT, Pi.smul_apply, smul_eq_mul, UN, shift_embTail]
    rw [specCoeff_Eratio (shift_le j 0)]
    simp only [shift, if_true, Nat.add_sub_cancel]
    ring
  · intro σ _ hσ
    simp [DT, Ne.symm hσ]
  · simp

lemma sum_embInit {N k : ℕ} {M : Type*} [AddCommMonoid M] (i : Inj N k) (g : Inj N (k + 1) → M) :
    ∑ j, (if embInit j = i then g j else 0) =
      ∑ c : {c : Fin N // c ∉ Set.range i}, g (embSnoc i c.1 c.2) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun c _ => embSnoc i c.1 c.2) (by simp) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ h
    apply Subtype.ext
    have := congrArg (fun j : Inj N (k + 1) => j (Fin.last k)) h
    simpa [embSnoc] using this
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    refine ⟨⟨j (Fin.last k), fun ⟨r, hr⟩ => ?_⟩, mem_univ _, ?_⟩
    · rw [← hj] at hr
      exact Fin.castSucc_ne_last r (j.injective hr)
    · ext r
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · show ((Fin.snoc (α := fun _ => Fin N) i (j (Fin.last k)) (Fin.last k) : Fin N) : ℕ) = _
        simp
      · show ((Fin.snoc (α := fun _ => Fin N) i (j (Fin.last k)) r'.castSucc : Fin N) : ℕ) = _
        simp only [Fin.snoc_castSucc]
        rw [← hj]; rfl

lemma shift_embSnoc {N k : ℕ} (i : Inj N k) (c : Fin N) (h) :
    shift (embSnoc i c h) = snoc (shift i) ((c : ℕ) + 1) := by
  funext r
  refine Fin.lastCases ?_ (fun r' => ?_) r
  · simp [shift, embSnoc]
  · simp [shift, embSnoc]

lemma sum_fin_succ_eq_Ico {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ c : Fin N, g ((c : ℕ) + 1) = ∑ y ∈ Ico 1 (N + 1), g y := by
  rw [Fin.sum_univ_eq_sum_range (fun c => g (c + 1)), Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun c _ => by rw [add_comm]

/-- **Finite (M)**: `U_{k+1}^{(N)} M_k^{(N)} = M̂_k U_k^{(N)}`. -/
theorem UN_M (N k : ℕ) : UN N (k + 1) * MT N k = Mmat N k * UN N k := by
  ext i' i
  have hk : k + 1 ≤ N := by
    have := Fintype.card_le_of_embedding i'; simpa using this
  set S := entries (shift i)
  set f : ℕ → KN N := fun y => specV N (k + 1) (U (k + 1) (snoc (shift i) y)) i'
  have hfN : f (N + 1) = 0 := by
    have := vanish N (N - k) (k + 1) (by omega) (snoc (shift i) (N + 1)) (fun r => by
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · simp
      · simp; have := shift_le i r'; omega) ⟨Fin.last k, by simp⟩
    simp only [f, this, Pi.zero_apply]
  -- the common value
  have hcommon : ∑ c : Fin N, (Acoef ((c : ℕ) + 1) S : KN N) * f ((c : ℕ) + 1) =
      ∑ y ∈ Ico 1 (N + 1), (Acoef y S : KN N) * f y :=
    sum_fin_succ_eq_Ico N (fun y => (Acoef y S : KN N) * f y)
  -- left side
  have hL : (UN N (k + 1) * MT N k) i' i =
      ∑ c : Fin N, (Acoef ((c : ℕ) + 1) S : KN N) * f ((c : ℕ) + 1) := by
    rw [mul_apply]
    have : ∀ j, UN N (k + 1) i' j * MT N k j i =
        if embInit j = i then (Acoef ((j (Fin.last k) : ℕ) + 1) S : KN N) * UN N (k + 1) i' j
        else 0 := by
      intro j
      by_cases h : embInit j = i
      · simp only [MT, h, if_true]; ring
      · simp only [MT, h, if_false, mul_zero]
    rw [sum_congr rfl fun j _ => this j, sum_embInit]
    have hterm : ∀ c : {c : Fin N // c ∉ Set.range i},
        (Acoef (((embSnoc i c.1 c.2) (Fin.last k) : ℕ) + 1) S : KN N) *
          UN N (k + 1) i' (embSnoc i c.1 c.2) =
        (Acoef ((c.1 : ℕ) + 1) S : KN N) * f ((c.1 : ℕ) + 1) := by
      intro c
      have h1 : (embSnoc i c.1 c.2) (Fin.last k) = c.1 := by
        show Fin.snoc (α := fun _ => Fin N) i c.1 (Fin.last k) = c.1
        simp
      rw [h1]
      simp only [UN, f, shift_embSnoc]
    rw [Fintype.sum_congr _ _ hterm,
      ← Fintype.sum_subtype_add_sum_subtype (fun c : Fin N => c ∉ Set.range i)
        (fun c => (Acoef ((c : ℕ) + 1) S : KN N) * f ((c : ℕ) + 1))]
    have hzero : ∑ c : {c : Fin N // ¬(c ∉ Set.range i)},
        (Acoef ((c.1 : ℕ) + 1) S : KN N) * f ((c.1 : ℕ) + 1) = 0 := by
      refine Fintype.sum_eq_zero _ fun c => ?_
      obtain ⟨r, hr⟩ := not_not.1 c.2
      rw [Acoef_eq_zero_of_mem (mem_entries.2 ⟨r, by simp [shift, hr]⟩)]
      simp
    rw [hzero, add_zero]
  -- right side
  have hR : (Mmat N k * UN N k) i' i = ∑ y ∈ Ico 1 (N + 1), (Acoef y S : KN N) * f y := by
    rw [mul_apply]
    have h1 : ∑ l, Mmat N k i' l * UN N k l i = (Mmat N k *ᵥ specV N k (U k (shift i))) i' := rfl
    rw [h1, ← specV_Mh (U_adm_of_le fun r => Nat.le_succ_of_le (shift_le i r)), ← U_M,
      Mop_bv_valid (shift_valid i), map_sum, specV_sum, Finset.sum_apply]
    have hT : Tset S ⊆ Ico 1 (N + 2) := by
      intro y hy
      rw [mem_Ico]
      rcases (mem_Tset.1 hy).2 with h | ⟨h1, h2⟩
      · omega
      · obtain ⟨r, hr⟩ := mem_entries.1 h2
        have := shift_le i r; omega
    rw [Finset.sum_subset hT (fun y _ hy => by
      rw [map_smul, Ul_bv, qc_smul, specV_qsmul, Pi.smul_apply, Acoef_of_not_mem hy, zero_smul])]
    rw [Finset.sum_Ico_succ_top (by omega)]
    rw [map_smul, Ul_bv, qc_smul, specV_qsmul, Pi.smul_apply]
    have : specV N (k + 1) (U (k + 1) (snoc (shift i) (N + 1))) i' = 0 := hfN
    rw [this]
    have h0 : (Acoef (N + 1) (entries (shift i)) : ℚ) • (0 : KN N) = 0 := by
      rw [Algebra.smul_def, mul_zero]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, Ul_bv, qc_smul, specV_qsmul, Pi.smul_apply, Algebra.smul_def, eq_ratCast]
  rw [hL, hR, hcommon]

end ProperCircularArc
