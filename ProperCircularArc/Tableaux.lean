import ProperCircularArc.Hikita

/-!
# Column assignments of nonzero weight are tableaux

Hikita's rule adds the vertices `v ≥ a` of a NUIG `G` in increasing order, each on top of its
column `c v` (columns are `0`-based here). Rows increase to the right and columns increase upward
automatically, because `v` is the largest entry so far, so the only condition is that the shape
stays a partition: column `c v` must be shorter than column `c v - 1`. A tableau built from `T_j`
is therefore the same thing as a column assignment satisfying `IsBuild`.

The paper remarks (after Definition `hikita-rule`) that `v` can be added on top of column `y`
whenever `A(y ∣ c_T(N(v))) ≠ 0`. `isBuild_of_hwt_ne_zero` proves this, so the sums over column
assignments in `Hikita.lean` are sums over tableaux (`hikSum_eq_sum_builds`, `pca_formula_tableaux`,
`hikita_tableaux`).
-/

noncomputable section

namespace ProperCircularArc

open Finset

variable {N n : ℕ}

/-- Height of column `y` of the initial tableau `T_j`, whose row `r < a` has length `c r + 1`. -/
def initH (a : ℕ) (c : Fin n → Fin N) (y : ℕ) : ℕ :=
  (univ.filter fun r : Fin n => (r : ℕ) < a ∧ y ≤ (c r : ℕ)).card

/-- The number of vertices `a ≤ u < t` added to column `y`. -/
def addH (a : ℕ) (c : Fin n → Fin N) (t y : ℕ) : ℕ :=
  (univ.filter fun u : Fin n => a ≤ (u : ℕ) ∧ (u : ℕ) < t ∧ (c u : ℕ) = y).card

/-- Height of column `y` just before vertex `t` is added. -/
def colH (a : ℕ) (c : Fin n → Fin N) (t y : ℕ) : ℕ := initH a c y + addH a c t y

/-- `c` describes a tableau build: every vertex `v ≥ a` goes on top of column `c v`, which is
either the first column or shorter than the column to its left. -/
def IsBuild (a : ℕ) (c : Fin n → Fin N) : Prop :=
  ∀ v : Fin n, a ≤ (v : ℕ) → (c v : ℕ) = 0 ∨ colH a c v (c v) < colH a c v ((c v : ℕ) - 1)

variable {a : ℕ} {c : Fin n → Fin N}

lemma initH_anti (y : ℕ) : initH a c y ≤ initH a c (y - 1) :=
  card_le_card fun r hr => by
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr.1, by omega⟩

lemma initH_lt (r : Fin n) (hr : (r : ℕ) < a) {y : ℕ} (hcr : (c r : ℕ) + 1 = y) :
    initH a c y < initH a c (y - 1) := by
  refine card_lt_card ((ssubset_iff_of_subset fun x hx => ?_).2 ⟨r, ?_, ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · simp only [mem_filter, mem_univ, true_and]
    exact ⟨hr, by omega⟩
  · simp only [mem_filter, mem_univ, true_and]
    omega

lemma addH_mono {t t' : ℕ} (h : t ≤ t') (y : ℕ) : addH a c t y ≤ addH a c t' y :=
  card_le_card fun u hu => by
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact ⟨hu.1, by omega, hu.2.2⟩

lemma addH_eq_of_none {t t' y : ℕ} (h : t ≤ t')
    (hno : ∀ w : Fin n, a ≤ (w : ℕ) → t ≤ (w : ℕ) → (w : ℕ) < t' → (c w : ℕ) ≠ y) :
    addH a c t' y = addH a c t y := by
  unfold addH
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    by_contra h4
    exact hno w h1 (by omega) h2 h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, h3⟩

lemma addH_zero (y : ℕ) : addH a c 0 y = 0 := by
  unfold addH
  rw [card_eq_zero, filter_eq_empty_iff]
  intro u _ h
  omega

lemma addH_succ {t : ℕ} (htn : t < n) (y : ℕ) :
    addH a c (t + 1) y = addH a c t y +
      if a ≤ t ∧ (c ⟨t, htn⟩ : ℕ) = y then 1 else 0 := by
  unfold addH
  rw [card_filter, card_filter]
  have hs : (if a ≤ t ∧ (c ⟨t, htn⟩ : ℕ) = y then 1 else 0) =
      ∑ u : Fin n, if u = ⟨t, htn⟩ then (if a ≤ t ∧ (c u : ℕ) = y then 1 else 0) else 0 := by
    simp
  rw [hs, ← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : (u : ℕ) = t
  · have e : u = ⟨t, htn⟩ := Fin.ext hu
    subst e
    simp only [if_true]
    split_ifs <;> omega
  · have e : u ≠ ⟨t, htn⟩ := fun e => hu (by rw [e])
    rw [if_neg e, add_zero]
    split_ifs <;> omega

/-- Column heights decrease from left to right as long as the vertices so far were placed
validly. -/
lemma colH_anti : ∀ t : ℕ, (∀ v : Fin n, a ≤ (v : ℕ) → (v : ℕ) < t →
    (c v : ℕ) = 0 ∨ colH a c v (c v) < colH a c v ((c v : ℕ) - 1)) →
    ∀ y, 1 ≤ y → colH a c t y ≤ colH a c t (y - 1)
  | 0, _, y, _ => by
    unfold colH
    rw [addH_zero, addH_zero]
    simpa using initH_anti (a := a) (c := c) y
  | t + 1, hb, y, hy => by
    have ih := colH_anti t (fun v h1 h2 => hb v h1 (by omega)) y hy
    unfold colH at ih ⊢
    by_cases htn : t < n
    · rw [addH_succ htn, addH_succ htn]
      by_cases hat : a ≤ t
      · have hv := hb ⟨t, htn⟩ hat (by simp)
        by_cases h1 : (c ⟨t, htn⟩ : ℕ) = y
        · simp only at hv
          rw [h1] at hv
          unfold colH at hv
          split_ifs <;> omega
        · split_ifs <;> omega
      · split_ifs <;> omega
    · rw [addH_eq_of_none (t := t) (t' := t + 1) (Nat.le_succ t)
        (fun w _ h2 h3 => absurd w.2 (by omega)),
        addH_eq_of_none (t := t) (t' := t + 1) (Nat.le_succ t)
        (fun w _ h2 h3 => absurd w.2 (by omega))]
      exact ih

/-- **Hikita's rule is well defined**: in a NUIG, a column assignment of nonzero weight is a
tableau build. -/
theorem isBuild_of_hwt_ne_zero {G : SimpleGraph (Fin n)} (hG : IsNUIG G)
    (h : hwt N G a c ≠ 0) : IsBuild a c := by
  classical
  suffices H : ∀ t : ℕ, ∀ v : Fin n, (v : ℕ) = t → a ≤ (v : ℕ) →
      (c v : ℕ) = 0 ∨ colH a c v (c v) < colH a c v ((c v : ℕ) - 1) from
    fun v hv => H v v rfl hv
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro v hvt hav
  subst hvt
  -- the factor of `v` is nonzero
  have hfac : (Acoef ((c v : ℕ) + 1) (nbrCols G c v) : KN N) ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.1 h) v (mem_univ v)
    rw [if_pos hav] at this
    exact left_ne_zero_of_mul this
  have hA : Acoef ((c v : ℕ) + 1) (nbrCols G c v) ≠ 0 := fun e => hfac (by rw [e, Rat.cast_zero])
  have hT : (c v : ℕ) + 1 ∈ Tset (nbrCols G c v) := by
    by_contra hT
    exact hA (Acoef_of_not_mem hT)
  rw [mem_Tset] at hT
  obtain ⟨hnot, hcase⟩ := hT
  by_cases hy0 : (c v : ℕ) = 0
  · exact Or.inl hy0
  right
  have hyS : (c v : ℕ) ∈ nbrCols G c v := by
    rcases hcase with h1 | ⟨_, h2⟩
    · omega
    · simpa using h2
  unfold nbrCols at hyS hnot
  obtain ⟨u, hu, hcu⟩ := mem_image.1 hyS
  simp only [mem_filter, mem_univ, true_and] at hu
  -- no vertex between `u` and `v` lies in column `c v`
  have hno : ∀ w : Fin n, u < w → w < v → (c w : ℕ) ≠ c v := by
    intro w h1 h2 hw
    apply hnot
    exact mem_image.2 ⟨w, mem_filter.2 ⟨mem_univ _, h2, (hG u v hu.1 hu.2 w h1 h2).2⟩,
      by rw [hw]⟩
  have huv : (u : ℕ) < v := hu.1
  by_cases hua : a ≤ (u : ℕ)
  · -- `u` was added before `v`: compare the heights just before `u`
    have hanti := colH_anti (a := a) (c := c) u
      (fun w hw hwu => ih w (by omega) w rfl hw) (c v) (by omega)
    have e1 : addH a c v (c v) = addH a c (u + 1) (c v) :=
      addH_eq_of_none (by omega) fun w _ h1 h2 => hno w (by
        show (u : ℕ) < w; omega) h2
    have e2 : addH a c (u + 1) (c v) = addH a c u (c v) := by
      rw [addH_succ u.2]
      rw [if_neg (by simp only [Fin.eta]; omega)]
      rfl
    have e3 : addH a c (u + 1) ((c v : ℕ) - 1) = addH a c u ((c v : ℕ) - 1) + 1 := by
      rw [addH_succ u.2, if_pos ⟨hua, by simp only [Fin.eta]; omega⟩]
    have e4 : addH a c (u + 1) ((c v : ℕ) - 1) ≤ addH a c v ((c v : ℕ) - 1) :=
      addH_mono (by omega) _
    unfold colH at hanti ⊢
    omega
  · -- `u` is an input: compare with the initial tableau
    have e1 : addH a c v (c v) = addH a c a (c v) :=
      addH_eq_of_none hav fun w hw _ h2 => hno w (by show (u : ℕ) < w; omega) h2
    have e0 : addH a c a (c v) = 0 := by
      unfold addH
      rw [card_eq_zero, filter_eq_empty_iff]
      intro w _ hw
      omega
    have hI := initH_lt (a := a) (c := c) u (by omega) hcu
    unfold colH
    omega

open Classical in
/-- The sums of `Hikita.lean` are sums over tableaux. -/
theorem hikSum_eq_sum_builds {b : ℕ} {G : SimpleGraph (Fin n)} (hG : IsNUIG G)
    (inp : Fin a → Fin n) (out : Fin b → Fin n) (o : Inj N b) (i : Inj N a) :
    hikSum N G inp out o i = ∑ c : Fin n → Fin N,
      if ((∀ r, c (out r) = o r) ∧ (∀ r, c (inp r) = i r)) ∧ IsBuild a c then hwt N G a c
      else 0 := by
  unfold hikSum
  refine Fintype.sum_congr _ _ fun c => ?_
  by_cases hb : IsBuild a c
  · simp [hb]
  · have hz : hwt N G a c = 0 := by
      by_contra hne
      exact hb (isBuild_of_hwt_ne_zero hG hne)
    simp [hz]

open Classical in
/-- **Theorem `pca-formula`**, as a sum over tableaux `T ⊇ T_j`. -/
theorem pca_formula_tableaux {n k : ℕ} (G : SimpleGraph (Fin (n + k))) [DecidableRel G.Adj]
    (hG : IsNUIG G) (hk : k ≤ n)
    (hin : ∀ i j : Fin (n + k), (i : ℕ) < k → (j : ℕ) < k → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin (n + k), n ≤ (i : ℕ) → n ≤ (j : ℕ) → i ≠ j → G.Adj i j)
    (hloop : ∀ r : ℕ, (hr : r < k) → ¬G.Adj ⟨n + r, by omega⟩ ⟨r, by omega⟩) (N : ℕ) :
    algebraMap (Pol N) (KN N) (chromSym N (cycTrace hk G)) =
      ∑ j : Inj N k, ∑ c : Fin (n + k) → Fin N,
        if ((∀ r, c (Fin.natAdd n r) = j r) ∧ (∀ r, c (Fin.castLE (by omega) r) = j r)) ∧
          IsBuild k c then hwt N G k c else 0 := by
  rw [pca_formula G hG hk hin hout hloop N]
  exact Fintype.sum_congr _ _ fun j => hikSum_eq_sum_builds hG _ _ j j

open Classical in
/-- **Theorem `hikita`** (`q = 1`, weight form) as a sum over tableaux. -/
theorem hikita_tableaux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : IsNUIG G)
    (N : ℕ) : algebraMap (Pol N) (KN N) (chromSym N G) =
      ∑ c : Fin n → Fin N, if IsBuild 0 c then hwt N G 0 c else 0 := by
  rw [hikita_weight G hG N]
  refine Fintype.sum_congr _ _ fun c => ?_
  by_cases hb : IsBuild 0 c
  · simp [hb]
  · have hz : hwt N G 0 c = 0 := by
      by_contra hne
      exact hb (isBuild_of_hwt_ne_zero hG hne)
    simp [hb, hz]

/-- **Theorem `tableau`** for a marked NUIG `(G, α, β)` with inputs `β = (1, …, a)` and outputs
`α = (n - b + 1, …, n)`: its Hikita matrix `𝓜_\bG^{(N)}` is the tableau matrix `M_\bG^{(N)}` of
the word of `G` given by Lemma `word`. -/
theorem tableau_nuig {n a b : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : IsNUIG G)
    (ha : a ≤ n) (hb : b ≤ n)
    (hin : ∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < a → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin n, n - b ≤ (i : ℕ) → n - b ≤ (j : ℕ) → i ≠ j → G.Adj i j) (N : ℕ) :
    ∃ w : Word a b, Nonempty (SimpleGraph.Iso (Word.graph w) G) ∧
      hikMat N G (Fin.castLE ha) (fun s => ⟨n - b + s, by omega⟩) = Word.tabMat N w := by
  obtain ⟨w, h, hadj, hinp, hmark⟩ := word_of_nuig hG a b ha hb hin hout
  refine ⟨w, ⟨{ toEquiv := finCongr h, map_rel_iff' := fun {u v} => (hadj u v).symm }⟩, ?_⟩
  rw [← Word.hikMat_eq_tabMat]
  ext o i
  unfold hikMat
  rw [hikSum_cast h (Word.graph w) G hadj (Word.inp w) (Fin.castLE ha)
    (fun r => Fin.ext (by simp [hinp])) (Word.mark w) (fun s => ⟨n - b + s, by omega⟩)
    (fun s => Fin.ext (by simp [hmark]))]

end ProperCircularArc
