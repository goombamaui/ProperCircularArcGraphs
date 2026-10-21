import ProperCircularArc.Arcs

/-!
# Tableau matrices of graphs (Section 7)

A tableau built from `T_j` by adding the vertices of a NUIG in increasing order is determined by
the columns of its vertices, and its weight (Definition `weight`)

  `w(T ∣ T_j, G) = ∏_{v ∈ T \ T_j} A(c_T(v) ∣ c_T(N(v))) · e_{c_T(v)} / e_{c_T(v) - 1}`

depends only on these columns. We therefore sum over *column assignments*
`c : vertices → Fin N` (column `c v + 1`, at most `N` columns, `e_j = e_j(x_1, …, x_N)`).
Assignments that are not tableaux have weight `0`: two adjacent vertices in the same column give
a factor `A(y ∣ σ)` with `y ∈ σ`.

* `hikMat` is the matrix `𝓜_\bG^{(N)}` of Definition `graph-tableau`.
* `Word.hikMat_eq_tabMat` is **Theorem `tableau`**: `𝓜_\bG^{(N)} = M_\bG^{(N)}`. The steps
  `hikSum_M` and `hikSum_D` are Lemma `tableau-mult` for one marked clique combined with
  Proposition `tableau-word`.
* `pca_formula` is **Theorem `pca-formula`**, and `hikita_weight` is the case `a = b = 0`
  (Theorem `hikita` in weight form).
-/

noncomputable section

namespace ProperCircularArc

open Finset Matrix

variable {N : ℕ}

/-- `e_{x+1} / e_x` with `e_j = e_j(x_1, …, x_N)`: the factor of a box in column `x + 1`. -/
def Erat (N x : ℕ) : KN N := eK N (x + 1) * (eK N x)⁻¹

lemma Erat_ne_zero {x : ℕ} (h : x < N) : Erat N x ≠ 0 :=
  mul_ne_zero (eK_ne_zero (by omega)) (inv_ne_zero (eK_ne_zero (by omega)))

/-- `ε(σ) = ∏_r e_{σ_r} / e_{σ_r - 1}` for the columns `σ_r = o_r + 1`. -/
def epsK (N : ℕ) {b : ℕ} (o : Inj N b) : KN N := ∏ r, Erat N (o r)

lemma epsK_ne_zero {b : ℕ} (o : Inj N b) : epsK N o ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun r _ => Erat_ne_zero (o r).2

open Classical in
/-- The columns `c_T(N(v))` of the smaller neighbours of `v`. -/
def nbrCols {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin N) (v : Fin n) : Finset ℕ :=
  (univ.filter fun u => u < v ∧ G.Adj u v).image fun u => (c u : ℕ) + 1

/-- The weight `w(T ∣ T_j, G)` (Definition `weight`) of the column assignment `c`, where the
vertices `v ≥ a` are added to `T_j`. -/
def hwt (N : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) (c : Fin n → Fin N) : KN N :=
  ∏ v : Fin n, if a ≤ (v : ℕ) then (Acoef ((c v : ℕ) + 1) (nbrCols G c v) : KN N) * Erat N (c v) else 1

open Classical in
/-- The sum of the weights of the tableaux built from `T_i` whose outputs are in the columns
`o`. -/
def hikSum (N : ℕ) {n a b : ℕ} (G : SimpleGraph (Fin n)) (inp : Fin a → Fin n)
    (out : Fin b → Fin n) (o : Inj N b) (i : Inj N a) : KN N :=
  ∑ c : Fin n → Fin N, if (∀ r, c (out r) = o r) ∧ (∀ r, c (inp r) = i r) then hwt N G a c else 0

/-- The matrix `𝓜_\bG^{(N)}` of Definition `graph-tableau`:
`𝓜 b_i = ∑_T w(T ∣ T_i, G) ε(i) / ε(c_T(α)) b_{c_T(α)}`. -/
def hikMat (N : ℕ) {n a b : ℕ} (G : SimpleGraph (Fin n)) (inp : Fin a → Fin n)
    (out : Fin b → Fin n) : Matrix (Inj N b) (Inj N a) (KN N) :=
  fun o i => epsK N i * (epsK N o)⁻¹ * hikSum N G inp out o i

/-- Two adjacent vertices in the same column give weight `0`. -/
lemma hwt_eq_zero {n a : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin N) {u v : Fin n}
    (huv : u < v) (hadj : G.Adj u v) (hv : a ≤ (v : ℕ)) (hc : c u = c v) : hwt N G a c = 0 := by
  classical
  refine Finset.prod_eq_zero (mem_univ v) ?_
  rw [if_pos hv, Acoef_eq_zero_of_mem, Rat.cast_zero, zero_mul]
  unfold nbrCols
  exact mem_image.2 ⟨u, by simp [huv, hadj], by rw [hc]⟩

/-- `hikSum` only depends on the graph up to relabelling by `Fin.cast`. -/
lemma hikSum_cast {n n' a b : ℕ} (h : n = n') (G : SimpleGraph (Fin n))
    (G' : SimpleGraph (Fin n')) (hG : ∀ u v, G.Adj u v ↔ G'.Adj (Fin.cast h u) (Fin.cast h v))
    (inp : Fin a → Fin n) (inp' : Fin a → Fin n') (hi : ∀ r, Fin.cast h (inp r) = inp' r)
    (out : Fin b → Fin n) (out' : Fin b → Fin n') (ho : ∀ r, Fin.cast h (out r) = out' r)
    (o : Inj N b) (i : Inj N a) : hikSum N G inp out o i = hikSum N G' inp' out' o i := by
  subst h
  have hG' : G = G' := by ext u v; simpa using hG u v
  have hi' : inp = inp' := funext fun r => by simpa using hi r
  have ho' : out = out' := funext fun r => by simpa using ho r
  subst hG' hi' ho'
  rfl

namespace Word

variable {a : ℕ}

lemma a_le_nv : ∀ {b : ℕ} (w : Word a b), a ≤ nv w
  | _, nil => le_rfl
  | _, M w => by have := a_le_nv w; simp only [nv]; omega
  | _, D w => a_le_nv w

/-! ## The empty word -/

lemma hikSum_nil (o i : Inj N a) :
    hikSum N (graph (nil : Word a a)) (inp nil) (mark nil) o i = if o = i then 1 else 0 := by
  classical
  unfold hikSum
  have hw : ∀ c : Fin (nv (nil : Word a a)) → Fin N, hwt N (graph (nil : Word a a)) a c = 1 := by
    intro c
    refine Finset.prod_eq_one fun v _ => if_neg ?_
    have := v.2
    simp only [nv] at this
    omega
  simp only [hw]
  let o' : Fin (nv (nil : Word a a)) → Fin N := show Fin a → Fin N from ⇑o
  have hcond : ∀ c : Fin (nv (nil : Word a a)) → Fin N,
      ((∀ r, c (mark nil r) = o r) ∧ (∀ r, c (inp nil r) = i r)) ↔ (c = o' ∧ o = i) := by
    intro c
    constructor
    · rintro ⟨h1, h2⟩
      have e1 : c = o' := funext fun r => h1 r
      refine ⟨e1, ?_⟩
      ext r
      have := h2 r
      rw [show inp (nil : Word a a) r = r from rfl, e1] at this
      exact congrArg Fin.val (show o r = i r from this)
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun r => rfl, fun r => rfl⟩
  simp only [hcond]
  by_cases h : o = i
  · rw [if_pos h, Finset.sum_eq_single o']
    · simp [h]
    · intro c _ hc; simp [hc]
    · simp
  · rw [if_neg h]; simp [h]

/-! ## Adding a vertex adjacent to the marked vertices (`M_k`) -/

lemma nbrCols_M_cast {b : ℕ} (w : Word a b) (c : Fin (nv w) → Fin N) (y : Fin N)
    (v : Fin (nv w)) :
    nbrCols (graph (M w)) (snocM w c y) v.castSucc = nbrCols (graph w) c v := by
  classical
  ext x
  simp only [nbrCols, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨hu, hadj⟩, rfl⟩
    induction u using Fin.lastCases with
    | last => exact absurd hu (not_lt.2 (Fin.castSucc_lt_last v).le)
    | cast u' =>
      refine ⟨u', ⟨Fin.castSucc_lt_castSucc_iff.1 hu, ?_⟩, by rw [snocM_cast]⟩
      simpa [graph, adj] using hadj
  · rintro ⟨u, ⟨hu, hadj⟩, rfl⟩
    exact ⟨u.castSucc, ⟨Fin.castSucc_lt_castSucc_iff.2 hu, by simpa [graph, adj] using hadj⟩,
      by rw [snocM_cast]⟩

lemma nbrCols_M_last {b : ℕ} (w : Word a b) (c : Fin (nv w) → Fin N) (y : Fin N) :
    nbrCols (graph (M w)) (snocM w c y) (Fin.last (nv w)) =
      univ.image fun r => (c (mark w r) : ℕ) + 1 := by
  classical
  ext x
  simp only [nbrCols, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨hu, hadj⟩, rfl⟩
    induction u using Fin.lastCases with
    | last => exact absurd hu (lt_irrefl _)
    | cast u' =>
      simp only [graph, adj, extendAdj_cl] at hadj
      obtain ⟨r, rfl⟩ := hadj
      exact ⟨r, by rw [snocM_cast]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨(mark w r).castSucc, ⟨Fin.castSucc_lt_last _, by simp [graph, adj]⟩,
      by rw [snocM_cast]⟩

lemma hwt_M {b : ℕ} (w : Word a b) (c : Fin (nv w) → Fin N) (y : Fin N) :
    hwt N (graph (M w)) a (snocM w c y) = hwt N (graph w) a c *
      ((Acoef ((y : ℕ) + 1) (univ.image fun r => (c (mark w r) : ℕ) + 1) : KN N) * Erat N y) := by
  unfold hwt
  erw [Fin.prod_univ_castSucc]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun v _ => ?_) ?_
  · simp only [nbrCols_M_cast, snocM_cast, Fin.coe_castSucc]
  · have := a_le_nv w
    simp only [Fin.val_last, nbrCols_M_last, snocM_last]
    rw [if_pos (by omega)]

lemma hikSum_M {b : ℕ} (w : Word a b) (o : Inj N (b + 1)) (i : Inj N a) :
    hikSum N (graph (M w)) (inp (M w)) (mark (M w)) o i =
      ((Acoef ((o (Fin.last b) : ℕ) + 1) (entries (shift (embInit o))) : KN N) *
        Erat N (o (Fin.last b))) * hikSum N (graph w) (inp w) (mark w) (embInit o) i := by
  classical
  unfold hikSum
  have hsplit : ∀ F : (Fin (nv (M w)) → Fin N) → KN N,
      ∑ κ, F κ = ∑ c : Fin N, ∑ κ : Fin (nv w) → Fin N, F (snocM w κ c) := by
    intro F
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.snocEquiv (n := nv w) (fun _ => Fin N)).symm _ _
      (fun κ => by simp [snocM, Fin.snocEquiv])
  refine (hsplit _).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have hm : ∀ c, (∀ r, snocM w κ c (mark (M w) r) = o r) ↔
      (∀ r, κ (mark w r) = embInit o r) ∧ c = o (Fin.last b) := by
    intro c
    rw [Fin.forall_fin_succ']
    simp only [mark, Fin.snoc_castSucc, Fin.snoc_last, snocM_cast, snocM_last]
    rfl
  have hi : ∀ c, (∀ r, snocM w κ c (inp (M w) r) = i r) ↔ (∀ r, κ (inp w r) = i r) := by
    intro c
    simp only [inp, snocM_cast]
  simp only [hm, hi, hwt_M]
  rw [Finset.sum_eq_single (o (Fin.last b))]
  · by_cases hA : (∀ r, κ (mark w r) = embInit o r) ∧ (∀ r, κ (inp w r) = i r)
    · rw [if_pos ⟨⟨hA.1, rfl⟩, hA.2⟩, if_pos hA]
      have himg : (univ.image fun r => (κ (mark w r) : ℕ) + 1) = entries (shift (embInit o)) := by
        simp only [hA.1]
        rfl
      rw [himg]
      ring
    · rw [if_neg (fun h => hA ⟨h.1.1, h.2⟩), if_neg hA, mul_zero]
  · intro c _ hc
    rw [if_neg (fun h => hc h.1.2)]
  · simp

/-! ## Forgetting the oldest marked vertex (`D_k`) -/

lemma hwt_adj_eq_zero_of_lt {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (i : Inj N a)
    (hi : ∀ r, κ (inp w r) = i r) {u v : Fin (nv w)} (huv : u < v) (hadj : adj w u v)
    (h : κ u = κ v) : hwt N (graph w) a κ = 0 := by
  by_cases hv : a ≤ (v : ℕ)
  · exact hwt_eq_zero (graph w) κ huv hadj hv h
  · exfalso
    have huv' : (u : ℕ) < v := huv
    have hu : (u : ℕ) < a := by omega
    have hv' : (v : ℕ) < a := by omega
    have e1 : inp w ⟨u, hu⟩ = u := Fin.ext (inp_val w _)
    have e2 : inp w ⟨v, hv'⟩ = v := Fin.ext (inp_val w _)
    have : i ⟨u, hu⟩ = i ⟨v, hv'⟩ := by rw [← hi, ← hi, e1, e2, h]
    have := congrArg Fin.val (i.injective this)
    simp only at this
    omega

lemma hwt_adj_eq_zero {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (i : Inj N a)
    (hi : ∀ r, κ (inp w r) = i r) {u v : Fin (nv w)} (hadj : adj w u v) (h : κ u = κ v) :
    hwt N (graph w) a κ = 0 := by
  rcases lt_trichotomy u v with huv | rfl | huv
  · exact hwt_adj_eq_zero_of_lt w κ i hi huv hadj h
  · exact absurd hadj (adj_irrefl w u)
  · exact hwt_adj_eq_zero_of_lt w κ i hi huv (adj_symm w u v hadj) h.symm

lemma hikSum_D {b : ℕ} (w : Word a (b + 1)) (o : Inj N b) (i : Inj N a) :
    hikSum N (graph (D w)) (inp (D w)) (mark (D w)) o i =
      ∑ c : {c : Fin N // c ∉ Set.range o}, hikSum N (graph w) (inp w) (mark w)
        (embCons c.1 o c.2) i := by
  classical
  unfold hikSum
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have hB : ∀ c : {c : Fin N // c ∉ Set.range o},
      ((∀ r, κ (mark w r) = embCons c.1 o c.2 r) ∧ (∀ r, κ (inp w r) = i r)) ↔
      (κ (mark w 0) = c.1 ∧ (∀ r, κ (mark w r.succ) = o r) ∧ (∀ r, κ (inp w r) = i r)) := by
    intro c
    rw [Fin.forall_fin_succ]
    simp only [embCons]
    constructor
    · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨h2, h3, h4⟩
    · rintro ⟨h2, h3, h4⟩; exact ⟨⟨h2, h3⟩, h4⟩
  show (if (∀ r, κ (mark w r.succ) = o r) ∧ (∀ r, κ (inp w r) = i r)
      then hwt N (graph w) a κ else 0) = _
  simp only [hB]
  by_cases hA : (∀ r, κ (mark w r.succ) = o r) ∧ (∀ r, κ (inp w r) = i r)
  · obtain ⟨hm, hi⟩ := hA
    by_cases hc0 : κ (mark w 0) ∈ Set.range o
    · obtain ⟨r, hr⟩ := hc0
      have hz : hwt N (graph w) a κ = 0 := by
        refine hwt_adj_eq_zero w κ i hi (mark_clique w 0 r.succ (Fin.succ_ne_zero r).symm) ?_
        rw [hm r, hr]
      rw [if_pos ⟨hm, hi⟩, hz]
      symm
      refine Fintype.sum_eq_zero _ fun c => ?_
      simp
    · rw [if_pos ⟨hm, hi⟩, Fintype.sum_eq_single ⟨κ (mark w 0), hc0⟩]
      · rw [if_pos ⟨rfl, hm, hi⟩]
      · intro c hc
        rw [if_neg]
        rintro ⟨h, _⟩
        exact hc (Subtype.ext h.symm)
  · rw [if_neg hA]
    symm
    refine Fintype.sum_eq_zero _ fun c => if_neg ?_
    rintro ⟨_, h3, h4⟩
    exact hA ⟨h3, h4⟩

/-! ## Theorem `tableau` -/

/-- **Theorem `tableau`**: for the graph of every word, the matrix `𝓜_\bG^{(N)}` defined by
Hikita's tableaux equals the tableau matrix `M_\bG^{(N)}`. -/
theorem hikMat_eq_tabMat : ∀ {b : ℕ} (w : Word a b),
    hikMat N (graph w) (inp w) (mark w) = tabMat N w
  | _, nil => by
    ext o i
    simp only [hikMat, hikSum_nil, tabMat, one_apply]
    split_ifs with h
    · subst h
      rw [mul_one, mul_inv_cancel₀ (epsK_ne_zero _)]
    · rw [mul_zero]
  | _, M (b := b) w => by
    ext o i
    rw [tabMat, Matrix.mul_apply]
    simp only [MT, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← hikMat_eq_tabMat w]
    simp only [hikMat, hikSum_M]
    have ho : epsK N o = epsK N (embInit o) * Erat N (o (Fin.last b)) := by
      unfold epsK
      rw [Fin.prod_univ_castSucc]
      rfl
    have hE := Erat_ne_zero (o (Fin.last b)).2
    rw [ho, mul_inv]
    field_simp
  | _, D (b := b) w => by
    ext o i
    rw [tabMat, Matrix.mul_apply]
    simp only [DT, ite_mul, zero_mul]
    rw [sum_embTail]
    simp only [← hikMat_eq_tabMat w]
    simp only [hikMat, hikSum_D, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun c => ?_
    have ho : epsK N (embCons c.1 o c.2) = Erat N c.1 * epsK N o := by
      unfold epsK
      rw [Fin.prod_univ_succ]
      rfl
    have hE := Erat_ne_zero c.1.2
    have hO := epsK_ne_zero o
    have h0 : embCons c.1 o c.2 0 = c.1 := rfl
    have h1 : eK N ((c.1 : ℕ) + 1) ≠ 0 := eK_ne_zero (by have := c.1.2; omega)
    have h2 : eK N (c.1 : ℕ) ≠ 0 := eK_ne_zero (by have := c.1.2; omega)
    rw [ho, mul_inv, h0]
    unfold Erat
    field_simp

/-- On the diagonal the factors `ε` cancel. -/
lemma trace_hikMat {k : ℕ} (w : Word k k) :
    trace (hikMat N (graph w) (inp w) (mark w)) = ∑ j, hikSum N (graph w) (inp w) (mark w) j j := by
  unfold trace
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [diag_apply, hikMat, mul_inv_cancel₀ (epsK_ne_zero j), one_mul]

end Word

/-! ## Theorem `pca-formula` -/

/-- **Theorem `pca-formula`**: let `Γ = cycTrace G` be the trace of a marked NUIG `G` on
`Fin (n + k)` as in Lemma `pca`. Then `X_Γ(x_1, …, x_N)` is the sum, over injective `j`, of the
weights of the tableaux built from `T_j` whose last `k` vertices return to the columns `j`. -/
theorem pca_formula {n k : ℕ} (G : SimpleGraph (Fin (n + k))) [DecidableRel G.Adj]
    (hG : IsNUIG G) (hk : k ≤ n)
    (hin : ∀ i j : Fin (n + k), (i : ℕ) < k → (j : ℕ) < k → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin (n + k), n ≤ (i : ℕ) → n ≤ (j : ℕ) → i ≠ j → G.Adj i j)
    (hloop : ∀ r : ℕ, (hr : r < k) → ¬G.Adj ⟨n + r, by omega⟩ ⟨r, by omega⟩) (N : ℕ) :
    algebraMap (Pol N) (KN N) (chromSym N (cycTrace hk G)) =
      ∑ j : Inj N k, hikSum N G (Fin.castLE (by omega)) (Fin.natAdd n) j j := by
  obtain ⟨w, h, hw, hadj, hinp, hmark, ⟨e⟩⟩ := cycTrace_word G hG hk hin hout hloop
  rw [← chromSym_iso N e, Word.pca_trace, ← Word.hikMat_eq_tabMat, Word.trace_hikMat]
  refine Fintype.sum_congr _ _ fun j => hikSum_cast h _ _ hadj _ _ (fun r => ?_) _ _
    (fun r => ?_) j j
  · exact Fin.ext (by simp [hinp])
  · exact Fin.ext (by simp [hmark])

/-- Theorem `pca-formula` written out: `X_Γ(x_1, …, x_N)` is the sum over injective `j` and
column assignments `c` with `c(r) = c(n + r) = j_r` of
`∏_{v ≥ k} A(c(v) ∣ c(N(v))) e_{c(v)} / e_{c(v) - 1}`. -/
theorem pca_formula' {n k : ℕ} (G : SimpleGraph (Fin (n + k))) [DecidableRel G.Adj]
    (hG : IsNUIG G) (hk : k ≤ n)
    (hin : ∀ i j : Fin (n + k), (i : ℕ) < k → (j : ℕ) < k → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin (n + k), n ≤ (i : ℕ) → n ≤ (j : ℕ) → i ≠ j → G.Adj i j)
    (hloop : ∀ r : ℕ, (hr : r < k) → ¬G.Adj ⟨n + r, by omega⟩ ⟨r, by omega⟩) (N : ℕ) :
    algebraMap (Pol N) (KN N) (chromSym N (cycTrace hk G)) =
      ∑ j : Inj N k, ∑ c : Fin (n + k) → Fin N,
        if (∀ r, c (Fin.natAdd n r) = j r) ∧ (∀ r, c (Fin.castLE (by omega) r) = j r) then
          ∏ v : Fin (n + k), (if k ≤ (v : ℕ) then
            (Acoef ((c v : ℕ) + 1) (nbrCols G c v) : KN N) *
              (eK N ((c v : ℕ) + 1) * (eK N (c v))⁻¹) else 1)
        else 0 := by
  rw [pca_formula G hG hk hin hout hloop N]
  unfold hikSum hwt Erat
  congr! 3

/-- **Theorem `hikita`** (`q = 1`, weight form): for a NUIG `G`, `X_G(x_1, …, x_N)` is the sum of
the weights of all tableaux built from the empty tableau. -/
theorem hikita_weight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : IsNUIG G)
    (N : ℕ) : algebraMap (Pol N) (KN N) (chromSym N G) = ∑ c : Fin n → Fin N, hwt N G 0 c := by
  classical
  obtain ⟨w, h, hadj, -, -⟩ := word_of_nuig hG 0 0 (by omega) (by omega)
    (fun i _ hi => absurd hi (by omega)) (fun i _ hi => absurd hi (by have := i.2; omega))
  let e : SimpleGraph.Iso (Word.graph w) G :=
    { toEquiv := finCongr h
      map_rel_iff' := fun {u v} => (hadj u v).symm }
  obtain ⟨htr, -⟩ := Word.stanstem_epositive N w
  rw [← chromSym_iso N e, htr, ← Word.hikMat_eq_tabMat, Word.trace_hikMat]
  have hu : (univ : Finset (Inj N 0)) = {Function.Embedding.ofIsEmpty} := by
    ext x
    simp only [mem_univ, mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [hu, sum_singleton, hikSum_cast h _ G hadj _ (fun r => r.elim0) (fun r => r.elim0) _
    (fun r => r.elim0) (fun r => r.elim0)]
  unfold hikSum
  simp

end ProperCircularArc
