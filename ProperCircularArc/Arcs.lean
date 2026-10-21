import ProperCircularArc.PCATrace
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Proper circular arc graphs are `e`-positive

An arc of the circle `ℝ/ℤ` is `[s, s + ℓ]` with `0 ≤ ℓ < 1`; we work with its preimage
`arcLift s ℓ ⊆ ℝ`. A *proper circular arc graph* is the intersection graph of finitely many
arcs, none of which contains another.

**Lemma `pca`**: cut the circle at `0`, sort the arcs by their starting points, and unroll. Each
arc gives the interval `A_v = [s_v, s_v + ℓ_v]`, and each arc through `1` (a *wrapping* arc) also
gives `B_v = A_v - 1`. Sorted by left endpoints, the `B`'s come first and the wrapping `A`'s
last, the intervals form a natural unit interval graph `H` on `Fin (n + k)`, and identifying
`A_v` with `B_v` gives back the original graph. Then Theorem `pca` (`pca_epositive`) applies.
-/

noncomputable section

namespace ProperCircularArc

open Finset

/-- The preimage in `ℝ` of the closed arc `[s, s + ℓ]` of `ℝ/ℤ`. -/
def arcLift (s ℓ : ℝ) : Set ℝ := {x | ∃ m : ℤ, s + m ≤ x ∧ x ≤ s + ℓ + m}

/-- A proper circular-arc model of a graph on `V`. -/
structure PCAModel (V : Type*) where
  /-- starting points -/
  s : V → ℝ
  /-- lengths -/
  len : V → ℝ
  len_nonneg : ∀ v, 0 ≤ len v
  len_lt_one : ∀ v, len v < 1
  /-- no arc contains another -/
  proper : ∀ u v, u ≠ v → ¬arcLift (s u) (len u) ⊆ arcLift (s v) (len v)

/-- The intersection graph of a circular-arc model. -/
def PCAModel.graph {V : Type*} (P : PCAModel V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (arcLift (P.s u) (P.len u) ∩ arcLift (P.s v) (P.len v)).Nonempty
  symm := ⟨fun u v ⟨h, x, hx⟩ => ⟨h.symm, x, hx.2, hx.1⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- Proper circular arc graphs. -/
def IsPCA {V : Type*} (G : SimpleGraph V) : Prop := ∃ P : PCAModel V, P.graph = G

/-! ## Arcs -/

lemma arcLift_add_int (s ℓ : ℝ) (j : ℤ) : arcLift (s + j) ℓ = arcLift s ℓ := by
  ext x
  simp only [arcLift, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m + j, by push_cast; linarith, by push_cast; linarith⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m - j, by push_cast; linarith, by push_cast; linarith⟩

lemma arcLift_mono {a b ℓ ℓ' : ℝ} (h1 : b ≤ a) (h2 : a + ℓ ≤ b + ℓ') :
    arcLift a ℓ ⊆ arcLift b ℓ' := by
  rintro x ⟨m, hm1, hm2⟩
  exact ⟨m, by linarith, by linarith⟩

lemma mem_arcLift_of_le {s ℓ x : ℝ} (h1 : s ≤ x) (h2 : x ≤ s + ℓ) : x ∈ arcLift s ℓ :=
  ⟨0, by simpa using h1, by simpa using h2⟩

lemma fract_mem_arcLift {s ℓ x : ℝ} (h : x ∈ arcLift s ℓ) : Int.fract x ∈ arcLift s ℓ := by
  obtain ⟨m, h1, h2⟩ := h
  refine ⟨m - ⌊x⌋, ?_, ?_⟩ <;> rw [Int.fract] <;> push_cast <;> linarith

/-- A point of `[0, 1)` on the arc `[s, s + ℓ]`, `0 ≤ s < 1`, lies in `[s, s + ℓ]` or, if the arc
passes through `1`, in `[s - 1, s + ℓ - 1]`. -/
lemma mem_arcLift_unit {s ℓ y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hℓ : ℓ < 1) (hy0 : 0 ≤ y)
    (hy1 : y < 1) (h : y ∈ arcLift s ℓ) :
    (s ≤ y ∧ y ≤ s + ℓ) ∨ (1 ≤ s + ℓ ∧ s - 1 ≤ y ∧ y ≤ s + ℓ - 1) := by
  obtain ⟨m, h1, h2⟩ := h
  have hm1 : m < 1 := by exact_mod_cast (by linarith : (m : ℝ) < 1)
  have hm2 : -2 < m := by exact_mod_cast (by linarith : (-2 : ℝ) < m)
  rcases (show m = 0 ∨ m = -1 by omega) with rfl | rfl
  · left
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  · right
    push_cast at h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩

/-! ## Rotating the circle -/

lemma mem_arcLift_sub {s ℓ x c : ℝ} :
    x - c ∈ arcLift (Int.fract (s - c)) ℓ ↔ x ∈ arcLift s ℓ := by
  simp only [arcLift, Set.mem_setOf_eq, Int.fract]
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m - ⌊s - c⌋, by push_cast; linarith, by push_cast; linarith⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m + ⌊s - c⌋, by push_cast; linarith, by push_cast; linarith⟩

lemma arcLift_rotate (s ℓ c : ℝ) :
    arcLift s ℓ = (fun y => y + c) '' arcLift (Int.fract (s - c)) ℓ := by
  ext x
  constructor
  · intro hx
    exact ⟨x - c, mem_arcLift_sub.2 hx, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← mem_arcLift_sub (c := c)]
    simpa using hy

/-- A rotated model: the starting points become `fract (s v - c)`. -/
def PCAModel.rotate {V : Type*} (P : PCAModel V) (c : ℝ) : PCAModel V where
  s v := Int.fract (P.s v - c)
  len := P.len
  len_nonneg := P.len_nonneg
  len_lt_one := P.len_lt_one
  proper u v huv h := P.proper u v huv (by
    rw [arcLift_rotate (P.s u) _ c, arcLift_rotate (P.s v) _ c]
    exact Set.image_mono h)

lemma PCAModel.rotate_graph {V : Type*} (P : PCAModel V) (c : ℝ) :
    (P.rotate c).graph = P.graph := by
  ext u v
  simp only [PCAModel.graph, PCAModel.rotate]
  rw [arcLift_rotate (P.s u) _ c, arcLift_rotate (P.s v) _ c,
    ← Set.image_inter (add_left_injective c), Set.image_nonempty]

/-! ## Sorted models -/

/-- A model on `Fin n` with starting points in `[0, 1)`, sorted increasingly, in which the arcs
through `1` are exactly the last `n - m`. -/
structure SortedModel (n : ℕ) extends PCAModel (Fin n) where
  s_nonneg : ∀ i, 0 ≤ s i
  s_lt_one : ∀ i, s i < 1
  mono : StrictMono s
  /-- the number of arcs not through `1` -/
  m : ℕ
  m_le : m ≤ n
  wrap_iff : ∀ i : Fin n, 1 ≤ s i + len i ↔ m ≤ (i : ℕ)

namespace SortedModel

variable {n : ℕ} (S : SortedModel n)

/-- The number of wrapping arcs. -/
def k : ℕ := n - S.m

lemma m_add_k : S.m + S.k = n := by unfold k; have := S.m_le; omega

lemma k_le : S.k ≤ n := Nat.sub_le _ _

/-- The arc underlying the `u`-th interval: `B` of the `u`-th wrapping arc for `u < k`, and `A`
of the `(u - k)`-th arc otherwise. -/
def src (u : Fin (n + S.k)) : Fin n :=
  if h : (u : ℕ) < S.k then ⟨S.m + u, by have := S.m_add_k; omega⟩
  else ⟨u - S.k, by have := u.2; omega⟩

lemma src_val (u : Fin (n + S.k)) :
    (S.src u : ℕ) = if (u : ℕ) < S.k then S.m + u else u - S.k := by
  unfold src; split_ifs <;> rfl

/-- Left endpoint of the `u`-th interval. -/
def left (u : Fin (n + S.k)) : ℝ := if (u : ℕ) < S.k then S.s (S.src u) - 1 else S.s (S.src u)

/-- Right endpoint of the `u`-th interval. -/
def right (u : Fin (n + S.k)) : ℝ := S.left u + S.len (S.src u)

lemma left_le_right (u : Fin (n + S.k)) : S.left u ≤ S.right u := by
  unfold right; linarith [S.len_nonneg (S.src u)]

lemma left_strictMono : StrictMono S.left := by
  intro u v huv
  have huv' : (u : ℕ) < v := huv
  have hu' := S.src_val u
  have hv' := S.src_val v
  unfold left
  by_cases hu : (u : ℕ) < S.k <;> by_cases hv : (v : ℕ) < S.k
  · rw [if_pos hu, if_pos hv]
    rw [if_pos hu] at hu'
    rw [if_pos hv] at hv'
    have : S.src u < S.src v := by rw [Fin.lt_def, hu', hv']; omega
    linarith [S.mono this]
  · rw [if_pos hu, if_neg hv]
    linarith [S.s_lt_one (S.src u), S.s_nonneg (S.src v)]
  · omega
  · rw [if_neg hu, if_neg hv]
    rw [if_neg hu] at hu'
    rw [if_neg hv] at hv'
    exact S.mono (by rw [Fin.lt_def, hu', hv']; omega)

lemma arcLift_left (u : Fin (n + S.k)) :
    arcLift (S.left u) (S.len (S.src u)) = arcLift (S.s (S.src u)) (S.len (S.src u)) := by
  unfold left
  split_ifs
  · rw [sub_eq_add_neg, show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, arcLift_add_int]
  · rfl

lemma mem_of_left_le (u : Fin (n + S.k)) {x : ℝ} (h1 : S.left u ≤ x) (h2 : x ≤ S.right u) :
    x ∈ arcLift (S.s (S.src u)) (S.len (S.src u)) := by
  rw [← S.arcLift_left]
  exact mem_arcLift_of_le h1 h2

/-- Right endpoints are increasing too: otherwise one arc would contain another. -/
lemma right_strictMono : StrictMono S.right := by
  intro u v huv
  by_contra hle
  push Not at hle
  have hl := S.left_strictMono huv
  by_cases he : S.src u = S.src v
  · unfold right at hle
    rw [he] at hle
    linarith
  · apply S.proper (S.src v) (S.src u) (Ne.symm he)
    rw [← S.arcLift_left v, ← S.arcLift_left u]
    exact arcLift_mono hl.le hle

/-- The unrolled interval graph on `Fin (n + k)`. -/
def H : SimpleGraph (Fin (n + S.k)) where
  Adj u v := u ≠ v ∧ S.left u ≤ S.right v ∧ S.left v ≤ S.right u
  symm := ⟨fun u v ⟨h, h1, h2⟩ => ⟨h.symm, h2, h1⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- An interval graph whose left and right endpoints are both increasing is a NUIG. -/
lemma isNUIG_of_strictMono {p : ℕ} (G : SimpleGraph (Fin p)) (a b : Fin p → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (hadj : ∀ u v, G.Adj u v ↔ u ≠ v ∧ a u ≤ b v ∧ a v ≤ b u) : IsNUIG G := by
  intro i j hij h l hil hlj
  rw [hadj] at h
  have := ha hil; have := ha hlj; have := hb hil; have := hb hlj
  exact ⟨(hadj _ _).2 ⟨hil.ne, by linarith, by linarith⟩,
    (hadj _ _).2 ⟨hlj.ne, by linarith, by linarith⟩⟩

lemma isNUIG : IsNUIG S.H :=
  isNUIG_of_strictMono S.H S.left S.right S.left_strictMono S.right_strictMono
    fun _ _ => Iff.rfl

lemma hin : ∀ i j : Fin (n + S.k), (i : ℕ) < S.k → (j : ℕ) < S.k → i ≠ j → S.H.Adj i j := by
  intro i j hi hj hij
  have hwi := (S.wrap_iff (S.src i)).2 (by rw [S.src_val, if_pos hi]; omega)
  have hwj := (S.wrap_iff (S.src j)).2 (by rw [S.src_val, if_pos hj]; omega)
  refine ⟨hij, ?_, ?_⟩ <;> unfold right left <;> rw [if_pos hi, if_pos hj] <;>
    linarith [S.s_lt_one (S.src i), S.s_lt_one (S.src j)]

lemma hout : ∀ i j : Fin (n + S.k), n ≤ (i : ℕ) → n ≤ (j : ℕ) → i ≠ j → S.H.Adj i j := by
  intro i j hi hj hij
  have := S.m_add_k
  have hi' : ¬(i : ℕ) < S.k := by omega
  have hj' : ¬(j : ℕ) < S.k := by omega
  have hwi := (S.wrap_iff (S.src i)).2 (by rw [S.src_val, if_neg hi']; omega)
  have hwj := (S.wrap_iff (S.src j)).2 (by rw [S.src_val, if_neg hj']; omega)
  refine ⟨hij, ?_, ?_⟩ <;> unfold right left <;> rw [if_neg hi', if_neg hj'] <;>
    linarith [S.s_lt_one (S.src i), S.s_lt_one (S.src j)]

lemma hloop : ∀ r : ℕ, (hr : r < S.k) → ¬S.H.Adj ⟨n + r, by omega⟩ ⟨r, by omega⟩ := by
  intro r hr ⟨_, h1, _⟩
  have := S.m_add_k
  have e : S.src ⟨n + r, by omega⟩ = S.src ⟨r, by omega⟩ := by
    apply Fin.ext
    rw [S.src_val, S.src_val]
    simp only
    rw [if_neg (by omega), if_pos hr]
    omega
  unfold right left at h1
  simp only at h1
  rw [if_neg (by omega), if_pos hr, e] at h1
  linarith [S.len_lt_one (S.src ⟨r, by omega⟩)]

/-! ## The trace of `H` is the arc graph -/

/-- The arc of the `p`-th vertex of `cycTrace H`. -/
def g (p : Fin n) : Fin n := S.src ⟨p, by omega⟩

lemma g_injective : Function.Injective S.g := by
  intro p q h
  have h' := congrArg Fin.val h
  simp only [g, S.src_val] at h'
  have := S.m_add_k
  have := p.2; have := q.2
  apply Fin.ext
  split_ifs at h' <;> omega

lemma src_eq_g (u : Fin (n + S.k)) : S.src u = S.g (piN S.k_le u) := by
  apply Fin.ext
  have := S.m_add_k
  have := u.2
  unfold piN g
  split_ifs with hu
  · rfl
  · rw [S.src_val, S.src_val]
    simp only
    split_ifs <;> omega

lemma exists_lift (i : Fin n) {y : ℝ} (hy : y ∈ arcLift (S.s i) (S.len i)) (hy0 : 0 ≤ y)
    (hy1 : y < 1) : ∃ u, S.src u = i ∧ S.left u ≤ y ∧ y ≤ S.right u := by
  have := S.m_add_k
  have := i.2
  rcases mem_arcLift_unit (S.s_nonneg i) (S.s_lt_one i) (S.len_lt_one i) hy0 hy1 hy with
    ⟨h1, h2⟩ | ⟨hw, h1, h2⟩
  · have hs : S.src ⟨i + S.k, by omega⟩ = i := by
      apply Fin.ext
      rw [S.src_val]
      simp only
      rw [if_neg (by omega)]
      omega
    refine ⟨⟨i + S.k, by omega⟩, hs, ?_, ?_⟩ <;> (try unfold right) <;> unfold left <;> simp only <;>
      rw [if_neg (by omega), hs] <;> linarith
  · have hmi : S.m ≤ i := (S.wrap_iff i).1 hw
    have hs : S.src ⟨i - S.m, by omega⟩ = i := by
      apply Fin.ext
      rw [S.src_val]
      simp only
      rw [if_pos (by omega)]
      omega
    refine ⟨⟨i - S.m, by omega⟩, hs, ?_, ?_⟩ <;> (try unfold right) <;> unfold left <;> simp only <;>
      rw [if_pos (by omega), hs] <;> linarith

/-- **Lemma `pca`**: the trace of the unrolled graph is the arc graph. -/
def iso : SimpleGraph.Iso (cycTrace S.k_le S.H) S.toPCAModel.graph where
  toEquiv := Equiv.ofBijective S.g (Finite.injective_iff_bijective.1 S.g_injective)
  map_rel_iff' := by
    intro p q
    show S.toPCAModel.graph.Adj (S.g p) (S.g q) ↔ (cycTrace S.k_le S.H).Adj p q
    constructor
    · rintro ⟨hne, x, hx1, hx2⟩
      have hpq : p ≠ q := fun h => hne (by rw [h])
      obtain ⟨u, hu, hu1, hu2⟩ := S.exists_lift (S.g p) (fract_mem_arcLift hx1)
        (Int.fract_nonneg x) (Int.fract_lt_one x)
      obtain ⟨v, hv, hv1, hv2⟩ := S.exists_lift (S.g q) (fract_mem_arcLift hx2)
        (Int.fract_nonneg x) (Int.fract_lt_one x)
      refine ⟨hpq, u, v, S.g_injective (by rw [← S.src_eq_g, hu]),
        S.g_injective (by rw [← S.src_eq_g, hv]), ?_, by linarith, by linarith⟩
      intro h
      apply hne
      rw [← hu, ← hv, h]
    · rintro ⟨hpq, u, v, rfl, rfl, huv, h1, h2⟩
      refine ⟨S.g_injective.ne hpq, max (S.left u) (S.left v), ?_, ?_⟩
      · rw [← S.src_eq_g]
        exact S.mem_of_left_le u (le_max_left _ _) (max_le (S.left_le_right u) h2)
      · rw [← S.src_eq_g]
        exact S.mem_of_left_le v (le_max_right _ _) (max_le h1 (S.left_le_right v))

/-- Theorem `pca` for sorted models. -/
theorem epositive (N : ℕ) :
    (∃ w : Word S.k S.k, algebraMap (Pol N) (KN N) (chromSym N S.toPCAModel.graph) =
        Matrix.trace (Word.tabMat N w)) ∧
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      MvPolynomial.aeval (fun j : Fin N => MvPolynomial.esymm (Fin N) ℚ ((j : ℕ) + 1)) P =
        chromSym N S.toPCAModel.graph := by
  classical
  obtain ⟨⟨w, hw⟩, P, hP, hPe⟩ :=
    pca_epositive S.H S.isNUIG S.k_le S.hin S.hout S.hloop N
  rw [chromSym_iso N S.iso] at hw hPe
  exact ⟨⟨w, hw⟩, P, hP, hPe⟩

end SortedModel

/-! ## Every model can be sorted -/

/-- Every proper circular-arc model is isomorphic to a sorted one. -/
theorem PCAModel.exists_sorted {V : Type*} [Fintype V] (P : PCAModel V) :
    ∃ (S : SortedModel (Fintype.card V)) (σ : Fin (Fintype.card V) ≃ V),
      ∀ i j, S.toPCAModel.graph.Adj i j ↔ P.graph.Adj (σ i) (σ j) := by
  classical
  set Q := P.rotate 0 with hQ
  have hQg : Q.graph = P.graph := P.rotate_graph 0
  have hs0 : ∀ v, 0 ≤ Q.s v := fun v => Int.fract_nonneg _
  have hs1 : ∀ v, Q.s v < 1 := fun v => Int.fract_lt_one _
  -- starting points are distinct
  have hinj : Function.Injective Q.s := by
    intro u v huv
    by_contra hne
    rcases le_total (Q.len u) (Q.len v) with h | h
    · exact Q.proper u v hne (arcLift_mono huv.ge (by rw [huv]; linarith))
    · exact Q.proper v u (Ne.symm hne) (arcLift_mono huv.le (by rw [huv]; linarith))
  -- sort by starting point
  let _ : LinearOrder V := LinearOrder.lift' Q.s hinj
  let σ := Fintype.orderIsoFinOfCardEq V (rfl : Fintype.card V = Fintype.card V)
  have hmono : StrictMono (fun i => Q.s (σ i)) := by
    intro i j h
    have h' := σ.strictMono h
    rw [lt_iff_le_not_ge] at h' ⊢
    exact h'
  -- the wrapping arcs come last
  have hup : ∀ i j : Fin (Fintype.card V), i < j → 1 ≤ Q.s (σ i) + Q.len (σ i) →
      1 ≤ Q.s (σ j) + Q.len (σ j) := by
    intro i j hij hi
    by_contra hj
    push Not at hj
    exact Q.proper (σ j) (σ i) (σ.injective.ne (ne_of_gt hij))
      (arcLift_mono (hmono hij).le (by linarith))
  let D := univ.filter (fun i : Fin (Fintype.card V) => Q.s (σ i) + Q.len (σ i) < 1)
  have hwrap : ∀ i : Fin (Fintype.card V), 1 ≤ Q.s (σ i) + Q.len (σ i) ↔ D.card ≤ i := by
    intro i
    constructor
    · intro hi
      calc D.card ≤ (Iio i).card := card_le_card (fun j hj => by
              simp only [D, mem_filter, mem_univ, true_and] at hj
              rw [mem_Iio]
              by_contra hji
              push Not at hji
              rcases hji.lt_or_eq with h | h
              · linarith [hup i j h hi]
              · rw [h] at hi; linarith)
        _ = i := Fin.card_Iio i
    · intro hi
      by_contra hlt
      push Not at hlt
      have : (Iic i).card ≤ D.card := card_le_card (fun j hj => by
        simp only [D, mem_filter, mem_univ, true_and]
        rw [mem_Iic] at hj
        by_contra hj'
        push Not at hj'
        rcases hj.lt_or_eq with h | h
        · linarith [hup j i h hj']
        · rw [h] at hj'; linarith)
      rw [Fin.card_Iic] at this
      omega
  refine ⟨{ s := fun i => Q.s (σ i)
            len := fun i => Q.len (σ i)
            len_nonneg := fun i => Q.len_nonneg _
            len_lt_one := fun i => Q.len_lt_one _
            proper := fun i j h => Q.proper _ _ (σ.injective.ne h)
            s_nonneg := fun i => hs0 _
            s_lt_one := fun i => hs1 _
            mono := hmono
            m := D.card
            m_le := by simpa using card_le_univ D
            wrap_iff := hwrap }, σ.toEquiv, fun i j => ?_⟩
  rw [← hQg]
  show (i ≠ j ∧ _) ↔ (σ i ≠ σ j ∧ _)
  rw [σ.injective.ne_iff]
  exact Iff.rfl

/-- **Theorem `pca`**: every proper circular arc graph is `e`-positive. For every `N`, its
chromatic symmetric function `X_G(x_1, …, x_N)` is the trace of a tableau matrix, and it equals
`P(e_1, …, e_N)` for a polynomial `P` with nonnegative rational coefficients. -/
theorem pca_graph_epositive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsPCA G) (N : ℕ) :
    (∃ (k : ℕ) (w : Word k k), algebraMap (Pol N) (KN N) (chromSym N G) =
        Matrix.trace (Word.tabMat N w)) ∧
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      MvPolynomial.aeval (fun j : Fin N => MvPolynomial.esymm (Fin N) ℚ ((j : ℕ) + 1)) P =
        chromSym N G := by
  obtain ⟨P, rfl⟩ := hG
  obtain ⟨S, σ, hσ⟩ := P.exists_sorted
  let e : SimpleGraph.Iso S.toPCAModel.graph P.graph :=
    { toEquiv := σ, map_rel_iff' := fun {i j} => (hσ i j).symm }
  obtain ⟨⟨w, hw⟩, Q, hQ, hQe⟩ := S.epositive N
  rw [chromSym_iso N e] at hw hQe
  exact ⟨⟨S.k, w, hw⟩, Q, hQ, hQe⟩

end ProperCircularArc
