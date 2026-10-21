import ProperCircularArc.MainWord
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Lemma `word`: every marked natural unit interval graph is the graph of a word

A graph on `Fin n` is a *natural unit interval graph* (NUIG) if `i < j` adjacent implies
`i ∼ l ∼ j` for all `i < l < j`.  Building the graph one vertex at a time, the earlier neighbours
of each new vertex `v` are the `c(v)` most recently added vertices, so `v` is attached by `D̂`
steps followed by one `M̂` step.
-/

noncomputable section

namespace ProperCircularArc

open Finset

/-- Natural unit interval graphs. -/
def IsNUIG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n, i < j → G.Adj i j → ∀ l : Fin n, i < l → l < j → G.Adj i l ∧ G.Adj l j

namespace Word

variable {a : ℕ}

lemma level_le_nv : ∀ {b : ℕ} (w : Word a b), b ≤ nv w
  | _, nil => le_rfl
  | _, M w => by have := level_le_nv w; simp only [nv]; omega
  | _, D w => by have := level_le_nv w; simp only [nv]; omega

lemma inp_val : ∀ {b : ℕ} (w : Word a b) (r : Fin a), (inp w r : ℕ) = r
  | _, nil, _ => rfl
  | _, M w, r => by simp only [inp, Fin.val_castSucc]; exact inp_val w r
  | _, D w, r => inp_val w r

/-- The marked vertices are the last `b` vertices. -/
lemma mark_val : ∀ {b : ℕ} (w : Word a b) (s : Fin b), (mark w s : ℕ) = nv w - b + s
  | _, nil, s => by simp [mark, nv]
  | _, M (b := b) w, s => by
    have hb := level_le_nv w
    induction s using Fin.lastCases with
    | last => simp only [mark, Fin.snoc_last, Fin.val_last, nv]; omega
    | cast s' =>
      simp only [mark, Fin.snoc_castSucc, Fin.val_castSucc, nv, mark_val w s']
      omega
  | _, D (b := b) w, s => by
    have hb := level_le_nv w
    simp only [mark, nv, mark_val w s.succ, Fin.val_succ]
    omega

/-- The adjacency relation of a word graph, described on vertex numbers. -/
def AdjSpec {b : ℕ} (w : Word a b) (R : ℕ → ℕ → Prop) : Prop :=
  ∀ u v : Fin (nv w), adj w u v ↔ R u v

lemma adjSpec_M {b : ℕ} {w : Word a b} {R : ℕ → ℕ → Prop} (h : AdjSpec w R) :
    AdjSpec (M w) fun u v =>
      (u < nv w ∧ v < nv w ∧ R u v) ∨ (v = nv w ∧ nv w - b ≤ u ∧ u < nv w) ∨
        (u = nv w ∧ nv w - b ≤ v ∧ v < nv w) := by
  have hb := level_le_nv w
  have hS : ∀ x : Fin (nv w), (∃ r, mark w r = x) ↔ nv w - b ≤ x := by
    intro x
    constructor
    · rintro ⟨r, rfl⟩; rw [mark_val]; omega
    · intro hx
      refine ⟨⟨x - (nv w - b), by omega⟩, Fin.ext ?_⟩
      rw [mark_val]; simp; omega
  intro u v
  induction u using Fin.lastCases with
  | last =>
    induction v using Fin.lastCases with
    | last => simp [adj]
    | cast v' =>
      simp only [adj, extendAdj_lc, hS, Fin.val_last, Fin.val_castSucc]
      constructor
      · intro hv; exact Or.inr (Or.inr ⟨by simp, hv, v'.2⟩)
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2, _⟩)
        · omega
        · omega
        · exact h2
  | cast u' =>
    induction v using Fin.lastCases with
    | last =>
      simp only [adj, extendAdj_cl, hS, Fin.val_last, Fin.val_castSucc]
      constructor
      · intro hu; exact Or.inr (Or.inl ⟨by simp, hu, u'.2⟩)
      · rintro (⟨_, h1, _⟩ | ⟨_, h2, _⟩ | ⟨h1, _⟩)
        · omega
        · exact h2
        · omega
    | cast v' =>
      simp only [adj, extendAdj_cc, Fin.val_castSucc]
      rw [h u' v']
      constructor
      · intro hr; exact Or.inl ⟨u'.2, v'.2, hr⟩
      · rintro (⟨_, _, hr⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
        · exact hr
        · omega
        · omega

/-- Drop the `t` oldest marked vertices. -/
def DW {c : ℕ} : (t : ℕ) → Word a (c + t) → Word a c
  | 0, w => w
  | t + 1, w => DW t (D w)

lemma nv_DW {c : ℕ} : ∀ (t : ℕ) (w : Word a (c + t)), nv (DW t w) = nv w
  | 0, _ => rfl
  | t + 1, w => nv_DW t (D w)

lemma adjSpec_DW {c : ℕ} {R : ℕ → ℕ → Prop} : ∀ (t : ℕ) (w : Word a (c + t)),
    AdjSpec w R → AdjSpec (DW t w) R
  | 0, _, h => h
  | t + 1, w, h => adjSpec_DW t (D w) h

/-- Transport a word along an equality of levels. -/
def castW {b b' : ℕ} (h : b = b') (w : Word a b) : Word a b' := h ▸ w

lemma nv_castW {b b' : ℕ} (h : b = b') (w : Word a b) : nv (castW h w) = nv w := by
  subst h; rfl

lemma adjSpec_castW {b b' : ℕ} (h : b = b') {w : Word a b} {R : ℕ → ℕ → Prop} (hw : AdjSpec w R) :
    AdjSpec (castW h w) R := by
  subst h; exact hw

end Word

/-! ## Earlier neighbours in a NUIG -/

section Earlier

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The number of earlier neighbours of `v`. -/
def earlier (v : Fin n) : ℕ := (univ.filter fun u : Fin n => u < v ∧ G.Adj u v).card

/-- In a NUIG the earlier neighbours of `v` are exactly the `earlier G v` vertices preceding it. -/
lemma adj_iff_earlier (hG : IsNUIG G) {u v : Fin n} (huv : u < v) :
    G.Adj u v ↔ (v : ℕ) - earlier G v ≤ u := by
  set S := univ.filter fun u : Fin n => u < v ∧ G.Adj u v
  have hS : earlier G v = S.card := rfl
  have hv := Fin.lt_def.1 huv
  rw [hS]
  -- `S` is an upper interval of `[0, v)`
  have hup : ∀ x y : Fin n, x ∈ S → x ≤ y → y < v → y ∈ S := by
    intro x y hx hxy hyv
    simp only [S, mem_filter, mem_univ, true_and] at hx ⊢
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact hx
    · exact ⟨hyv, (hG x v hx.1 hx.2 y hlt hyv).2⟩
  constructor
  · intro h
    -- every `y ∈ [u, v)` lies in `S`, so `|S| ≥ v - u`
    have hsub : (univ.filter fun y : Fin n => u ≤ y ∧ y < v) ⊆ S := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      exact hup u y (by simp [S, huv, h]) hy.1 hy.2
    have hcard : (univ.filter fun y : Fin n => u ≤ y ∧ y < v).card = v - u := by
      rw [show (univ.filter fun y : Fin n => u ≤ y ∧ y < v) = Finset.Ico u v by ext; simp]
      simp
    have := card_le_card hsub
    omega
  · intro h
    by_contra hnot
    -- all elements of `S` exceed `u`
    have hsub : S ⊆ (univ.filter fun y : Fin n => u < y ∧ y < v) := by
      intro y hy
      have hyS := hy
      simp only [S, mem_filter, mem_univ, true_and] at hy
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨?_, hy.1⟩
      by_contra hle
      push Not at hle
      exact hnot (by
        have := hup y u hyS hle huv
        simp only [S, mem_filter, mem_univ, true_and] at this
        exact this.2)
    have hcard : (univ.filter fun y : Fin n => u < y ∧ y < v).card = v - u - 1 := by
      rw [show (univ.filter fun y : Fin n => u < y ∧ y < v) = Finset.Ioo u v by ext; simp]
      simp
    have := card_le_card hsub
    omega

/-- In a NUIG, `earlier (v + 1) ≤ earlier v + 1`. -/
lemma earlier_succ_le (hG : IsNUIG G) {v w : Fin n} (hvw : (w : ℕ) = v + 1) :
    earlier G w ≤ earlier G v + 1 := by
  by_contra hlt
  push Not at hlt
  -- the vertex `u = w - earlier w` is adjacent to `w` but not to `v`
  have hpos : earlier G w ≤ w := by
    unfold earlier
    calc _ ≤ (univ.filter fun u : Fin n => u < w).card := card_le_card (by
            intro x; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.1)
      _ = w := by
          rw [show (univ.filter fun u : Fin n => u < w) = Finset.Iio w by ext; simp]
          simp
  set u : Fin n := ⟨w - earlier G w, by omega⟩
  have huw : u < w := by
    rw [Fin.lt_def]; simp only [u]
    have : 0 < earlier G w := by omega
    omega
  have hadj : G.Adj u w := (adj_iff_earlier G hG huw).2 (by simp [u])
  have huv : u < v := by rw [Fin.lt_def]; simp only [u]; omega
  have hadj' := (hG u w huw hadj v huv (by rw [Fin.lt_def]; omega)).1
  have := (adj_iff_earlier G hG huv).1 hadj'
  simp only [u] at this
  omega

end Earlier

/-! ## Building the word -/

section Build

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma earlier_le (v : Fin n) : earlier G v ≤ v := by
  unfold earlier
  calc _ ≤ (univ.filter fun u : Fin n => u < v).card := card_le_card (by
          intro x; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.1)
    _ = v := by
        rw [show (univ.filter fun u : Fin n => u < v) = Finset.Iio v by ext; simp]
        simp

/-- The number of earlier neighbours, on vertex numbers. -/
def cnt (v : ℕ) : ℕ := if h : v < n then earlier G ⟨v, h⟩ else 0

/-- Adjacency on vertex numbers. -/
def GR (u v : ℕ) : Prop := ∃ (hu : u < n) (hv : v < n), G.Adj ⟨u, hu⟩ ⟨v, hv⟩

variable (a : ℕ)

/-- The word building the first `a + t` vertices. -/
def build : (t : ℕ) → Σ ℓ : ℕ, Word a ℓ
  | 0 => ⟨a, .nil⟩
  | t + 1 =>
    let p := build t
    let r := min (cnt G (a + t)) p.1
    ⟨r + 1, .M (Word.DW (p.1 - r) (Word.castW (by omega : p.1 = r + (p.1 - r)) p.2))⟩

lemma nv_build : ∀ t, Word.nv (build G a t).2 = a + t
  | 0 => rfl
  | t + 1 => by
    show Word.nv (Word.DW _ (Word.castW _ (build G a t).2)) + 1 = a + (t + 1)
    rw [Word.nv_DW, Word.nv_castW, nv_build t]; ring

variable {G}

lemma level_build (hG : IsNUIG G) : ∀ t, a + t < n → cnt G (a + t) ≤ (build G a t).1
  | 0, h => by
    show cnt G (a + 0) ≤ a
    unfold cnt; rw [dif_pos h]
    have := earlier_le G ⟨a + 0, h⟩; simpa using this
  | t + 1, h => by
    show cnt G (a + (t + 1)) ≤ min (cnt G (a + t)) (build G a t).1 + 1
    rw [min_eq_left (level_build hG t (by omega))]
    unfold cnt
    rw [dif_pos h, dif_pos (by omega)]
    exact earlier_succ_le G hG (by simp; omega)

lemma adjSpec_build (hG : IsNUIG G) (hin : ∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < a → i ≠ j →
    G.Adj i j) : ∀ t, a + t ≤ n → Word.AdjSpec (build G a t).2 (GR G)
  | 0, h => by
    intro u v
    show u ≠ v ↔ GR G u v
    constructor
    · intro huv
      refine ⟨by have := u.2; simp [build, Word.nv] at this; omega,
        by have := v.2; simp [build, Word.nv] at this; omega, hin _ _ ?_ ?_ ?_⟩
      · have := u.2; simp [build, Word.nv] at this; simpa using this
      · have := v.2; simp [build, Word.nv] at this; simpa using this
      · intro e; apply huv; ext; simpa using congrArg Fin.val e
    · rintro ⟨_, _, h⟩ e
      subst e
      exact G.loopless.irrefl _ h
  | t + 1, h => by
    have ih := adjSpec_build hG hin t (by omega)
    set w := (build G a t).2
    set r := min (cnt G (a + t)) (build G a t).1 with hr
    have hr' : r = cnt G (a + t) := min_eq_left (level_build a hG t (by omega))
    have hw : Word.AdjSpec (Word.DW ((build G a t).1 - r)
        (Word.castW (by omega : (build G a t).1 = r + ((build G a t).1 - r)) w)) (GR G) :=
      Word.adjSpec_DW _ _ (Word.adjSpec_castW _ ih)
    have hM := Word.adjSpec_M hw
    have hnv : Word.nv (Word.DW ((build G a t).1 - r)
        (Word.castW (by omega : (build G a t).1 = r + ((build G a t).1 - r)) w)) = a + t := by
      rw [Word.nv_DW, Word.nv_castW, nv_build]
    intro u v
    have hu := u.2
    have hv := v.2
    change Word.nv (Word.DW _ _) + 1 > u at hu
    change Word.nv (Word.DW _ _) + 1 > v at hv
    rw [hnv] at hu hv
    show Word.adj (Word.M _) u v ↔ _
    rw [hM u v, hnv]
    -- compare with `GR` on the new vertex `a + t`
    have hlast : ∀ x : ℕ, x < a + t →
        ((a + t - r ≤ x ∧ x < a + t) ↔ GR G x (a + t)) := by
      intro x hx
      have hxn : x < n := by omega
      have hm : a + t < n := by omega
      have key := adj_iff_earlier G hG (u := ⟨x, hxn⟩) (v := ⟨a + t, hm⟩) (by simp [Fin.lt_def]; omega)
      have hcnt : cnt G (a + t) = earlier G ⟨a + t, hm⟩ := by unfold cnt; rw [dif_pos hm]
      constructor
      · rintro ⟨h1, _⟩
        exact ⟨hxn, hm, key.2 (by simp; rw [← hcnt, ← hr']; omega)⟩
      · rintro ⟨_, _, hadj⟩
        refine ⟨?_, hx⟩
        have := key.1 hadj
        simp only at this
        rw [hr', hcnt]; exact this
    have hGRsymm : ∀ x y, GR G x y → GR G y x := fun x y ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact h3
      · rw [h1]; exact (hlast u h3).1 ⟨h2, h3⟩
      · rw [h1]; exact hGRsymm _ _ ((hlast v h3).1 ⟨h2, h3⟩)
    · intro hg
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hu) with hu' | hu' <;>
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hv' | hv'
      · exact Or.inl ⟨hu', hv', hg⟩
      · refine Or.inr (Or.inl ⟨hv', ?_⟩)
        rw [hv'] at hg
        exact (hlast u hu').2 hg
      · refine Or.inr (Or.inr ⟨hu', ?_⟩)
        rw [hu'] at hg
        exact (hlast v hv').2 (hGRsymm _ _ hg)
      · exfalso
        obtain ⟨_, _, hadj⟩ := hg
        have : (⟨(u : ℕ), by omega⟩ : Fin n) = ⟨v, by omega⟩ := Fin.ext (by simp; omega)
        rw [this] at hadj
        exact G.loopless.irrefl _ hadj

end Build

/-! ## Lemma `word` -/

section LemmaWord

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma level_build_final (hG : IsNUIG G) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (hout : ∀ i j : Fin n, n - b ≤ (i : ℕ) → n - b ≤ (j : ℕ) → i ≠ j → G.Adj i j) :
    b ≤ (build G a (n - a)).1 := by
  rcases Nat.eq_or_lt_of_le ha with rfl | hlt
  · simp [build]; exact hb
  obtain ⟨t, ht⟩ : ∃ t, n - a = t + 1 := ⟨n - a - 1, by omega⟩
  rw [ht]
  show b ≤ min (cnt G (a + t)) (build G a t).1 + 1
  rw [min_eq_left (level_build a hG t (by omega))]
  by_cases hb1 : b ≤ 1
  · omega
  have hm : a + t < n := by omega
  have hlast : a + t = n - 1 := by omega
  have hadj : G.Adj ⟨n - b, by omega⟩ ⟨a + t, hm⟩ := hout _ _ (by simp) (by simp; omega)
    (by intro e; have := congrArg Fin.val e; simp at this; omega)
  have := (adj_iff_earlier G hG (u := ⟨n - b, by omega⟩) (v := ⟨a + t, hm⟩)
    (by simp [Fin.lt_def]; omega)).1 hadj
  unfold cnt; rw [dif_pos hm]
  simp only at this
  omega

/-- **Lemma `word`**: a marked NUIG on `Fin n` whose first `a` and last `b` vertices form cliques
is the graph of a word from level `a` to level `b`, with inputs `0, …, a - 1` and outputs
`n - b, …, n - 1`. -/
theorem word_of_nuig (hG : IsNUIG G) (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (hin : ∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < a → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin n, n - b ≤ (i : ℕ) → n - b ≤ (j : ℕ) → i ≠ j → G.Adj i j) :
    ∃ (w : Word a b) (h : Word.nv w = n),
      (∀ u v, Word.adj w u v ↔ G.Adj (Fin.cast h u) (Fin.cast h v)) ∧
      (∀ r, (Word.inp w r : ℕ) = r) ∧ (∀ s, (Word.mark w s : ℕ) = n - b + s) := by
  set W := build G a (n - a)
  have hbW : b ≤ W.1 := level_build_final hG ha hb hout
  let w : Word a b := Word.DW (W.1 - b) (Word.castW (by omega : W.1 = b + (W.1 - b)) W.2)
  have hnv : Word.nv w = n := by
    simp only [w]; rw [Word.nv_DW, Word.nv_castW, nv_build]; omega
  refine ⟨w, hnv, ?_, Word.inp_val w, fun s => by rw [Word.mark_val, hnv]⟩
  have hspec : Word.AdjSpec w (GR G) :=
    Word.adjSpec_DW _ _ (Word.adjSpec_castW _ (adjSpec_build a hG hin (n - a) (by omega)))
  intro u v
  rw [hspec u v]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨_, _, h⟩

end LemmaWord

/-! ## Consequences -/

section Consequences

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

/-- The chromatic symmetric function is an isomorphism invariant. -/
lemma chromSym_iso (N : ℕ) {G : SimpleGraph V} {G' : SimpleGraph V'} (e : SimpleGraph.Iso G G') :
    chromSym N G = chromSym N G' := by
  classical
  unfold chromSym
  refine Fintype.sum_equiv (Equiv.arrowCongr e.toEquiv (Equiv.refl _)) _ _ fun κ => ?_
  have hP : IsProper G' (Equiv.arrowCongr e.toEquiv (Equiv.refl _) κ) ↔ IsProper G κ := by
    simp only [IsProper, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
    constructor
    · intro h u v huv
      have := h (e u) (e v) (e.map_rel_iff.2 huv)
      convert this using 2 <;> exact (e.toEquiv.symm_apply_apply _).symm
    · intro h u v huv
      have := h (e.symm u) (e.symm v) (by rwa [← e.map_rel_iff, e.apply_symm_apply,
        e.apply_symm_apply])
      exact this
  rw [hP]
  split_ifs
  · exact Fintype.prod_equiv e.toEquiv (fun v => MvPolynomial.X (κ v))
      (fun v' => MvPolynomial.X (Equiv.arrowCongr e.toEquiv (Equiv.refl _) κ v'))
      (fun v => by
        first
          | exact congrArg (fun c => MvPolynomial.X c) (congrArg κ (e.symm_apply_apply v).symm)
          | simp [e.toEquiv.symm_apply_apply])
  · rfl

end Consequences

/-- **Theorem `stanstem`** (natural unit interval graphs): for every NUIG `G` and every number
`N` of colours, `X_G(x_1, …, x_N)` is the trace of a tableau matrix and is a polynomial in
`e_1, …, e_N` with nonnegative coefficients. -/
theorem nuig_epositive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : IsNUIG G)
    (N : ℕ) :
    (∃ w : Word 0 0, algebraMap (Pol N) (KN N) (chromSym N G) = Matrix.trace (Word.tabMat N w)) ∧
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      MvPolynomial.aeval (fun j : Fin N => MvPolynomial.esymm (Fin N) ℚ ((j : ℕ) + 1)) P =
        chromSym N G := by
  obtain ⟨w, h, hadj, -, -⟩ := word_of_nuig hG 0 0 (by omega) (by omega)
    (fun i _ hi => absurd hi (by omega)) (fun i _ hi => absurd hi (by have := i.2; omega))
  let e : SimpleGraph.Iso (Word.graph w) G :=
    { toEquiv := finCongr h
      map_rel_iff' := fun {u v} => (hadj u v).symm }
  obtain ⟨htr, P, hP, hPe⟩ := Word.stanstem_epositive N w
  rw [chromSym_iso N e] at htr hPe
  exact ⟨⟨w, htr⟩, P, hP, hPe⟩

end ProperCircularArc
