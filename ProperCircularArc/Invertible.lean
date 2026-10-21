import ProperCircularArc.FiniteU
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

/-!
# Proposition `finite`: `U_k^{(N)}` is invertible for `k ≤ N`

The image of `U_{k+1}^{(N)}` contains `M̂_k V̂_k` (since `U_k^{(N)}` is invertible) and is stable
under `R̂ = M̂ D̂ - D̂ M̂`, which acts by `F(j) ↦ x_{j_last} F(j ∘ rot)`.  Its `(k+1)`-st power is
multiplication by `x_{j_1} ⋯ x_{j_{k+1}}`, and a Vandermonde argument shows that the image is
everything.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

/-- The cyclic relabelling of a colour tuple, `(j_1, …, j_n) ↦ (j_n, j_1, …, j_{n-1})`. -/
def rotE {N k : ℕ} (j : Inj N (k + 1)) : Inj N (k + 1) := (rot k).toEmbedding.trans j

@[simp] lemma rotE_apply {N k : ℕ} (j : Inj N (k + 1)) (r : Fin (k + 1)) :
    rotE j r = j (rot k r) := rfl

/-- The matrix of `R̂_{k+1}` with `N` colours. -/
def Rmat (N k : ℕ) : Matrix (Inj N (k + 1)) (Inj N (k + 1)) (KN N) :=
  Mmat N k * Dmat N k - Dmat N (k + 1) * Mmat N (k + 1)

lemma sum_subtype_eq_ite {N : ℕ} {M : Type*} [AddCommMonoid M] (P : Fin N → Prop) [DecidablePred P]
    (g : Fin N → M) : ∑ c : {c // P c}, g c = ∑ c, if P c then g c else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) g).symm

lemma embInit_embCons {N k : ℕ} (c : Fin N) (j : Inj N (k + 1)) (h : c ∉ Set.range j) :
    embInit (embCons c j h) = embCons c (embInit j) (fun ⟨r, hr⟩ => h ⟨r.castSucc, hr⟩) := by
  ext r
  refine Fin.cases ?_ (fun r' => ?_) r <;> rfl

lemma embCons_last {N k : ℕ} (c : Fin N) (j : Inj N (k + 1)) (h : c ∉ Set.range j) :
    embCons c j h (Fin.last (k + 1)) = j (Fin.last k) := by
  show Fin.cons (α := fun _ => Fin N) c j (Fin.last (k + 1)) = j (Fin.last k)
  rw [← Fin.succ_last, Fin.cons_succ]

/-- `R̂` acts by `F(j) ↦ x_{j_last} F(j ∘ rot)`. -/
lemma Rmat_mulVec {N k : ℕ} (F : Inj N (k + 1) → KN N) (j : Inj N (k + 1)) :
    (Rmat N k *ᵥ F) j = xK N (j (Fin.last k)) * F (rotE j) := by
  classical
  rw [Rmat, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Pi.sub_apply, Mmat_mulVec,
    Dmat_mulVec, Dmat_mulVec]
  simp only [Mmat_mulVec, embCons_last, embInit_embCons]
  rw [← Finset.mul_sum, ← mul_sub]
  congr 1
  set g : Fin N → KN N := fun c =>
    if h : c ∉ Set.range (embInit j) then F (embCons c (embInit j) h) else 0 with hg
  have h1 : ∑ c : {c // c ∉ Set.range (embInit j)}, F (embCons c.1 (embInit j) c.2) =
      ∑ c ∈ univ.filter (fun c => c ∉ Set.range (embInit j)), g c := by
    rw [Finset.sum_subtype (p := fun c => c ∉ Set.range (embInit j)) _ (by simp) g]
    refine Fintype.sum_congr _ _ fun c => ?_
    simp only [hg, dif_pos c.2]
  have h2 : ∑ c : {c // c ∉ Set.range j},
      F (embCons c.1 (embInit j) (fun ⟨r, hr⟩ => c.2 ⟨r.castSucc, hr⟩)) =
      ∑ c ∈ univ.filter (fun c => c ∉ Set.range j), g c := by
    rw [Finset.sum_subtype (p := fun c => c ∉ Set.range j) _ (by simp) g]
    refine Fintype.sum_congr _ _ fun c => ?_
    have : c.1 ∉ Set.range (embInit j) := fun ⟨r, hr⟩ => c.2 ⟨r.castSucc, hr⟩
    simp only [hg, dif_pos this]
  rw [h1, h2]
  have hlast : j (Fin.last k) ∉ Set.range (embInit j) := by
    rintro ⟨r, hr⟩
    exact Fin.castSucc_ne_last r (j.injective hr)
  have hsplit : univ.filter (fun c => c ∉ Set.range (embInit j)) =
      insert (j (Fin.last k)) (univ.filter (fun c => c ∉ Set.range j)) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, Set.mem_range, not_exists]
    constructor
    · intro h
      by_cases hc : c = j (Fin.last k)
      · exact Or.inl hc
      · refine Or.inr fun r hr => ?_
        induction r using Fin.lastCases with
        | last => exact hc hr.symm
        | cast r' => exact h r' hr
    · rintro (rfl | h) r hr
      · exact Fin.castSucc_ne_last r (j.injective hr)
      · exact h r.castSucc hr
  rw [hsplit, sum_insert (by simp), add_sub_cancel_right, hg]
  simp only [dif_pos hlast]
  congr 1
  ext r
  refine Fin.cases ?_ (fun r' => ?_) r
  · show (j (Fin.last k) : ℕ) = j (rot k 0)
    rw [rot_zero]
  · show (j r'.castSucc : ℕ) = j (rot k r'.succ)
    rw [rot_succ]

/-! ## Iterating the rotation -/

lemma rot_val_succ {k m : ℕ} (h : m + 1 < k + 1) : rot k ⟨m + 1, h⟩ = ⟨m, by omega⟩ := by
  have := rot_succ k ⟨m, by omega⟩
  simpa using this

lemma rot_iterate_last (k s : ℕ) (hs : s ≤ k) :
    (rot k)^[s] (Fin.last k) = ⟨k - s, by omega⟩ := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have : k - s = (k - (s + 1)) + 1 := by omega
    simp only [this]
    exact rot_val_succ (by omega)

lemma rot_iterate_val (k m : ℕ) (hm : m < k + 1) : (rot k)^[m] ⟨m, hm⟩ = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, rot_val_succ hm, ih (by omega)]

lemma rot_iterate_period (k : ℕ) (r : Fin (k + 1)) : (rot k)^[k + 1] r = r := by
  obtain ⟨m, hm⟩ := r
  have h := Function.iterate_add_apply (rot k) ((k - m) + 1) m ⟨m, hm⟩
  rw [show (k - m) + 1 + m = k + 1 by omega] at h
  rw [h, rot_iterate_val k m hm, Function.iterate_succ_apply, rot_zero,
    rot_iterate_last k (k - m) (by omega)]
  ext; simp; omega

lemma rotE_iterate {N k : ℕ} (t : ℕ) (j : Inj N (k + 1)) (r : Fin (k + 1)) :
    (rotE^[t] j) r = j ((rot k)^[t] r) := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih, rotE_apply, Function.iterate_succ_apply']

lemma rotE_iterate_period {N k : ℕ} (j : Inj N (k + 1)) : rotE^[k + 1] j = j := by
  ext r; rw [rotE_iterate, rot_iterate_period]

/-- The powers of `R̂`. -/
lemma Rmat_pow_mulVec {N k : ℕ} (t : ℕ) (F : Inj N (k + 1) → KN N) (j : Inj N (k + 1)) :
    (Rmat N k ^ t *ᵥ F) j =
      (∏ s ∈ range t, xK N (j ((rot k)^[s] (Fin.last k)))) * F (rotE^[t] j) := by
  induction t generalizing j with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, Rmat_mulVec, ih, prod_range_succ', Function.iterate_succ_apply]
    have : ∀ s ∈ range t, xK N ((rotE j) ((rot k)^[s] (Fin.last k))) =
        xK N (j ((rot k)^[s + 1] (Fin.last k))) := by
      intro s _; rw [rotE_apply, Function.iterate_succ_apply']
    rw [prod_congr rfl this]
    simp only [Function.iterate_zero_apply]
    ring

/-- `R̂^{k+1}` is multiplication by `x_{j_1} ⋯ x_{j_{k+1}}`. -/
lemma Rmat_pow_period {N k : ℕ} (F : Inj N (k + 1) → KN N) (j : Inj N (k + 1)) :
    (Rmat N k ^ (k + 1) *ᵥ F) j = (∏ r, xK N (j r)) * F j := by
  rw [Rmat_pow_mulVec, rotE_iterate_period]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun s => xK N (j ((rot k)^[s] (Fin.last k)))) (k + 1)]
  have : ∀ s : Fin (k + 1), (rot k)^[(s : ℕ)] (Fin.last k) = Fin.rev s := by
    intro s
    rw [rot_iterate_last k s (by omega)]
    ext; simp [Fin.val_rev]
  simp only [this]
  exact Equiv.prod_comp Fin.revPerm (fun r => xK N (j r))

/-! ## Surjectivity -/

lemma xK_ne_zero (N : ℕ) (c : Fin N) : xK N c ≠ 0 := by
  intro h
  apply X_ne_zero (R := ℚ) c
  apply algebraMap_injective_KN N
  rw [map_zero]; exact h

lemma xK_injective (N : ℕ) : Function.Injective (xK N) :=
  fun _ _ h => X_injective (algebraMap_injective_KN N h)

lemma UN_zero (N : ℕ) : UN N 0 = 1 := by
  ext i σ
  have hσ : σ = i := Subsingleton.elim _ _
  subst hσ
  rw [one_apply_eq]
  show specV N 0 (U 0 (shift σ)) σ = 1
  have : (U 0 (shift σ) : CV Lam 0) = map (iotaN N).toRingHom 1 := by simp [U]
  rw [this, specV_map]
  simp

lemma Rmat_UN (N k : ℕ) : Rmat N k * UN N (k + 1) =
    UN N (k + 1) * (MT N k * DT N k - DT N (k + 1) * MT N (k + 1)) := by
  have h1 := UN_D N k
  have h2 := UN_M N k
  have h3 := UN_M N (k + 1)
  have h4 := UN_D N (k + 1)
  calc Rmat N k * UN N (k + 1)
      = Mmat N k * (Dmat N k * UN N (k + 1)) - Dmat N (k + 1) * (Mmat N (k + 1) * UN N (k + 1)) := by
        rw [Rmat, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (Mmat N k * UN N k) * DT N k - (Dmat N (k + 1) * UN N (k + 2)) * MT N (k + 1) := by
        rw [h1, ← h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = (UN N (k + 1) * MT N k) * DT N k - (UN N (k + 1) * DT N (k + 1)) * MT N (k + 1) := by
        rw [← h2, h4]
    _ = _ := by rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **Proposition `finite`** (surjectivity): for `k ≤ N` the matrix `U_k^{(N)}` is onto. -/
theorem UN_surjective (N : ℕ) : ∀ k, k ≤ N → Function.Surjective (fun v => UN N k *ᵥ v) := by
  intro k
  induction k with
  | zero =>
    intro _ v
    refine ⟨v, ?_⟩
    show UN N 0 *ᵥ v = v
    rw [UN_zero, one_mulVec]
  | succ k ih =>
    intro hk
    have IH := ih (by omega)
    set Img := LinearMap.range (UN N (k + 1)).mulVecLin
    have mem_Img : ∀ u, UN N (k + 1) *ᵥ u ∈ Img := fun u => ⟨u, rfl⟩
    -- `M̂ V̂_k ⊆ Img`
    have hM : ∀ F, Mmat N k *ᵥ F ∈ Img := by
      intro F
      obtain ⟨u, rfl⟩ := IH F
      rw [mulVec_mulVec, ← UN_M, ← mulVec_mulVec]
      exact mem_Img _
    -- stability under `R̂` and `R̂^{k+1}`
    have hR : ∀ v ∈ Img, Rmat N k *ᵥ v ∈ Img := by
      rintro v ⟨u, rfl⟩
      show Rmat N k *ᵥ (UN N (k + 1) *ᵥ u) ∈ Img
      rw [mulVec_mulVec, Rmat_UN, ← mulVec_mulVec]
      exact mem_Img _
    have hRpow : ∀ t, ∀ v ∈ Img, Rmat N k ^ t *ᵥ v ∈ Img := by
      intro t
      induction t with
      | zero => intro v hv; rwa [pow_zero, one_mulVec]
      | succ t iht =>
        intro v hv
        rw [pow_succ', ← mulVec_mulVec]
        exact hR _ (iht v hv)
    -- the vectors `w i u`
    let w : Inj N k → ℕ → Inj N (k + 1) → KN N := fun i u j =>
      if embInit j = i then xK N (j (Fin.last k)) ^ (u + 1) else 0
    have hw : ∀ i u, w i u ∈ Img := by
      intro i u
      have hbase : Mmat N k *ᵥ Pi.single i 1 = w i 0 := by
        funext j
        rw [Mmat_mulVec]
        simp only [w, Pi.single_apply, zero_add, pow_one]
        split_ifs <;> simp
      have hpow : Rmat N k ^ ((k + 1) * u) *ᵥ w i 0 = (∏ r, xK N (i r)) ^ u • w i u := by
        funext j
        rw [pow_mul]
        have : ∀ (t : ℕ) (F : Inj N (k + 1) → KN N), ((Rmat N k ^ (k + 1)) ^ t *ᵥ F) j =
            (∏ r, xK N (j r)) ^ t * F j := by
          intro t
          induction t with
          | zero => intro F; simp
          | succ t iht =>
            intro F
            rw [pow_succ', ← mulVec_mulVec, Rmat_pow_period, iht, pow_succ]
            ring
        rw [this, Pi.smul_apply, smul_eq_mul]
        simp only [w]
        split_ifs with h
        · rw [Fin.prod_univ_castSucc]
          have : ∀ r : Fin k, j r.castSucc = i r := fun r => by rw [← h]; rfl
          simp only [this]
          ring
        · simp
      have hmem := hRpow ((k + 1) * u) _ (hbase ▸ hM (Pi.single i 1))
      rw [hpow] at hmem
      have hne : (∏ r, xK N (i r)) ^ u ≠ 0 := pow_ne_zero _ (prod_ne_zero_iff.2 fun r _ => xK_ne_zero N _)
      have := Img.smul_mem ((∏ r, xK N (i r)) ^ u)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    -- every basis vector lies in `Img`
    have hsingle : ∀ j, Pi.single j (1 : KN N) ∈ Img := by
      intro j
      set i := embInit j
      set c0 := j (Fin.last k)
      set S : Finset (Fin N) := univ.filter fun c => c ∉ Set.range i
      have hc0 : c0 ∈ S := by
        simp only [S, mem_filter, mem_univ, true_and]
        rintro ⟨r, hr⟩
        exact Fin.castSucc_ne_last r (j.injective hr)
      set P : Polynomial (KN N) := Polynomial.X * Lagrange.nodal (S.erase c0) (xK N)
      have hdeg : P.natDegree = S.card := by
        rw [Polynomial.natDegree_X_mul Lagrange.nodal_ne_zero, Lagrange.natDegree_nodal,
          card_erase_of_mem hc0, Nat.sub_add_cancel (card_pos.2 ⟨c0, hc0⟩)]
      have heval : ∀ y, P.eval y = ∑ u ∈ range S.card, P.coeff (u + 1) * y ^ (u + 1) := by
        intro y
        rw [Polynomial.eval_eq_sum_range' (n := S.card + 1) (by omega), sum_range_succ',
          Polynomial.coeff_X_mul_zero, zero_mul, add_zero]
      have hPc0 : P.eval (xK N c0) ≠ 0 := by
        simp only [P, Polynomial.eval_mul, Polynomial.eval_X, Lagrange.eval_nodal]
        refine mul_ne_zero (xK_ne_zero N c0) (prod_ne_zero_iff.2 fun c hc => ?_)
        exact sub_ne_zero.2 fun e => (mem_erase.1 hc).1 (xK_injective N e).symm
      have hcomb : Pi.single j (1 : KN N) = ∑ u ∈ range S.card,
          (P.coeff (u + 1) / P.eval (xK N c0)) • w i u := by
        funext j'
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, w]
        by_cases hj' : embInit j' = i
        · simp only [hj', if_true]
          have : ∑ u ∈ range S.card, P.coeff (u + 1) / P.eval (xK N c0) *
              xK N (j' (Fin.last k)) ^ (u + 1) = P.eval (xK N (j' (Fin.last k))) / P.eval (xK N c0) := by
            rw [heval (xK N (j' (Fin.last k))), Finset.sum_div]
            exact sum_congr rfl fun u _ => by ring
          rw [this]
          by_cases hl : j' (Fin.last k) = c0
          · have : j' = j := by
              ext r
              induction r using Fin.lastCases with
              | last => rw [hl]
              | cast r' =>
                have := congrArg (fun e : Inj N k => e r') hj'
                simp only [i] at this
                exact congrArg Fin.val this
            subst this
            rw [Pi.single_eq_same, hl, div_self hPc0]
          · rw [Pi.single_eq_of_ne (fun e => hl (by rw [e])), eq_comm, div_eq_zero_iff]
            left
            have hmem : j' (Fin.last k) ∈ S.erase c0 := by
              refine mem_erase.2 ⟨hl, ?_⟩
              simp only [S, mem_filter, mem_univ, true_and]
              rintro ⟨r, hr⟩
              rw [← hj'] at hr
              exact Fin.castSucc_ne_last r (j'.injective hr)
            simp only [P, Polynomial.eval_mul, Polynomial.eval_X]
            rw [Lagrange.eval_nodal_at_node hmem, mul_zero]
        · simp only [hj', if_false, mul_zero, sum_const_zero]
          rw [Pi.single_eq_of_ne]
          intro e; apply hj'; rw [e]
      rw [hcomb]
      exact Img.sum_mem fun u _ => Img.smul_mem _ (hw i u)
    intro v
    have : v ∈ Img := by
      rw [pi_eq_sum_univ v]
      refine Img.sum_mem fun j _ => Img.smul_mem _ ?_
      have e : (fun j' => if j = j' then (1 : KN N) else 0) = Pi.single j 1 := by
        funext j'; simp [Pi.single_apply, eq_comm]
      rw [e]; exact hsingle j
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩

end ProperCircularArc
