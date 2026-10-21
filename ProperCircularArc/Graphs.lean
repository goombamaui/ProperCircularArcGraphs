import ProperCircularArc.TraceEpos
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Chromatic symmetric functions and the graph of a word

* `chromSym N G` is the chromatic symmetric function `X_G(x_1, …, x_N)`.
* A word `w` in `M̂`, `D̂` builds a marked natural unit interval graph `Word.graph w` (Lemma `word`):
  `M̂` attaches a new vertex adjacent to all marked vertices and marks it, `D̂` unmarks the oldest
  marked vertex.
* **Lemma `color`**: the colour matrix of `w` counts proper colourings of `Word.graph w` with
  prescribed colours on the marked and input vertices.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

/-! ## Chromatic symmetric functions in `N` variables -/

section Chrom

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Proper colourings with colours `Fin N`. -/
def IsProper (G : SimpleGraph V) {N : ℕ} (κ : V → Fin N) : Prop := ∀ u v, G.Adj u v → κ u ≠ κ v

open Classical in
/-- The chromatic symmetric function `X_G(x_1, …, x_N)`. -/
def chromSym (N : ℕ) (G : SimpleGraph V) : Pol N :=
  ∑ κ : V → Fin N, if IsProper G κ then ∏ v, X (κ v) else 0

/-- `X_G` is a symmetric polynomial. -/
theorem chromSym_isSymmetric (N : ℕ) (G : SimpleGraph V) : (chromSym N G).IsSymmetric := by
  classical
  intro e
  simp only [chromSym, map_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl V) e) _ _ fun κ => ?_
  have hP : IsProper G (Equiv.arrowCongr (Equiv.refl V) e κ) ↔ IsProper G κ := by
    simp only [IsProper, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
      Equiv.refl_symm, id]
    exact forall₂_congr fun u v => imp_congr_right fun _ => e.injective.ne_iff
  simp only [hP]
  split_ifs
  · simp [map_prod]
  · simp

end Chrom

/-! ## The graph of a word -/

/-- Extend a relation on `Fin n` by a new vertex `last` related exactly to the vertices in `S`. -/
def extendAdj {n : ℕ} (A : Fin n → Fin n → Prop) (S : Fin n → Prop) : Fin (n + 1) → Fin (n + 1) → Prop :=
  fun u v => Fin.lastCases (motive := fun _ => Prop)
    (Fin.lastCases (motive := fun _ => Prop) False (fun v' => S v') v)
    (fun u' => Fin.lastCases (motive := fun _ => Prop) (S u') (fun v' => A u' v') v) u

@[simp] lemma extendAdj_cc {n : ℕ} (A : Fin n → Fin n → Prop) (S) (u v : Fin n) :
    extendAdj A S u.castSucc v.castSucc = A u v := by simp [extendAdj]

@[simp] lemma extendAdj_lc {n : ℕ} (A : Fin n → Fin n → Prop) (S) (v : Fin n) :
    extendAdj A S (Fin.last n) v.castSucc = S v := by simp [extendAdj]

@[simp] lemma extendAdj_cl {n : ℕ} (A : Fin n → Fin n → Prop) (S) (u : Fin n) :
    extendAdj A S u.castSucc (Fin.last n) = S u := by simp [extendAdj]

@[simp] lemma extendAdj_ll {n : ℕ} (A : Fin n → Fin n → Prop) (S) :
    extendAdj A S (Fin.last n) (Fin.last n) = False := by simp [extendAdj]

namespace Word

variable {a : ℕ}

/-- The number of vertices of the graph of a word. -/
def nv : {b : ℕ} → Word a b → ℕ
  | _, nil => a
  | _, M w => nv w + 1
  | _, D w => nv w

/-- The marked vertices, oldest first. -/
def mark : {b : ℕ} → (w : Word a b) → Fin b → Fin (nv w)
  | _, nil => id
  | _, M w => Fin.snoc (α := fun _ => Fin (nv w + 1)) (fun r => (mark w r).castSucc) (Fin.last (nv w))
  | _, D w => fun r => mark w r.succ

/-- The input vertices. -/
def inp : {b : ℕ} → (w : Word a b) → Fin a → Fin (nv w)
  | _, nil => id
  | _, M w => fun r => (inp w r).castSucc
  | _, D w => inp w

/-- The adjacency relation of the graph of a word. -/
def adj : {b : ℕ} → (w : Word a b) → Fin (nv w) → Fin (nv w) → Prop
  | _, nil => fun u v => u ≠ v
  | _, M w => extendAdj (adj w) (fun u => ∃ r, mark w r = u)
  | _, D w => adj w

lemma adj_symm : ∀ {b : ℕ} (w : Word a b) (u v : Fin (nv w)), adj w u v → adj w v u
  | _, nil, u, v, h => Ne.symm h
  | _, M w, u, v, h => by
    induction u using Fin.lastCases with
    | last =>
      induction v using Fin.lastCases with
      | last => simp [adj] at h
      | cast v' => simpa [adj] using h
    | cast u' =>
      induction v using Fin.lastCases with
      | last => simpa [adj] using h
      | cast v' => simp only [adj, extendAdj_cc] at h ⊢; exact adj_symm w _ _ h
  | _, D w, u, v, h => adj_symm w u v h

lemma adj_irrefl : ∀ {b : ℕ} (w : Word a b) (u : Fin (nv w)), ¬adj w u u
  | _, nil, u, h => h rfl
  | _, M w, u, h => by
    induction u using Fin.lastCases with
    | last => simp [adj] at h
    | cast u' => simp only [adj, extendAdj_cc] at h; exact adj_irrefl w u' h
  | _, D w, u, h => adj_irrefl w u h

/-- The graph of a word. -/
def graph {b : ℕ} (w : Word a b) : SimpleGraph (Fin (nv w)) where
  Adj := adj w
  symm := ⟨fun u v h => adj_symm w u v h⟩
  loopless := ⟨fun u h => adj_irrefl w u h⟩

lemma mark_injective : ∀ {b : ℕ} (w : Word a b), Function.Injective (mark w)
  | _, nil => Function.injective_id
  | _, M w => by
    intro r s h
    induction r using Fin.lastCases with
    | last =>
      induction s using Fin.lastCases with
      | last => rfl
      | cast s' => simp [mark] at h; exact absurd h.symm (Fin.castSucc_ne_last _)
    | cast r' =>
      induction s using Fin.lastCases with
      | last => simp [mark] at h; exact absurd h (Fin.castSucc_ne_last _)
      | cast s' =>
        simp [mark] at h
        rw [mark_injective w (Fin.castSucc_injective _ h)]
  | _, D w => fun r s h => Fin.succ_injective _ (mark_injective w h)

/-- The marked vertices form a clique. -/
lemma mark_clique : ∀ {b : ℕ} (w : Word a b) (r s : Fin b), r ≠ s → adj w (mark w r) (mark w s)
  | _, nil, r, s, h => h
  | _, M w, r, s, h => by
    induction r using Fin.lastCases with
    | last =>
      induction s using Fin.lastCases with
      | last => exact absurd rfl h
      | cast s' => simp [adj, mark]
    | cast r' =>
      induction s using Fin.lastCases with
      | last => simp [adj, mark]
      | cast s' =>
        simp only [adj, mark, Fin.snoc_castSucc, extendAdj_cc]
        exact mark_clique w r' s' fun e => h (by rw [e])
  | _, D w, r, s, h => mark_clique w r.succ s.succ fun e => h (Fin.succ_injective _ e)

lemma inp_injective : ∀ {b : ℕ} (w : Word a b), Function.Injective (inp w)
  | _, nil => Function.injective_id
  | _, M w => fun r s h => inp_injective w (Fin.castSucc_injective _ h)
  | _, D w => inp_injective w

/-! ## Lemma `color` -/

/-- The polynomial version of `M̂_k`. -/
def MmatP (N k : ℕ) : Matrix (Inj N (k + 1)) (Inj N k) (Pol N) :=
  fun j i => if embInit j = i then X (j (Fin.last k)) else 0

/-- The polynomial version of `D̂_{k+1}`. -/
def DmatP (N k : ℕ) : Matrix (Inj N k) (Inj N (k + 1)) (Pol N) :=
  fun i j => if embTail j = i then 1 else 0

/-- The colour matrix with polynomial entries. -/
def colMatP (N : ℕ) : {b : ℕ} → Word a b → Matrix (Inj N b) (Inj N a) (Pol N)
  | _, nil => 1
  | _, M (b := b) w => MmatP N b * colMatP N w
  | _, D (b := b) w => DmatP N b * colMatP N w

lemma colMat_eq_map {N : ℕ} : ∀ {b : ℕ} (w : Word a b),
    colMat N w = (colMatP N w).map (algebraMap (Pol N) (KN N))
  | _, nil => by simp [colMat, colMatP, Matrix.map_one]
  | _, M (b := b) w => by
    rw [colMat, colMatP, Matrix.map_mul, colMat_eq_map w]
    congr 1
    ext j i; simp only [Mmat, MmatP, map_apply]; split_ifs <;> simp [xK]
  | _, D (b := b) w => by
    rw [colMat, colMatP, Matrix.map_mul, colMat_eq_map w]
    congr 1
    ext j i; simp only [Dmat, DmatP, map_apply]; split_ifs <;> simp

open Classical in
/-- The colour matrix of a marked graph: proper colourings with prescribed colours on the marked
and the input vertices, weighted by the non-input vertices. -/
def colorSum (N : ℕ) {b : ℕ} (w : Word a b) (o : Inj N b) (i : Inj N a) : Pol N :=
  ∑ κ : Fin (nv w) → Fin N,
    if IsProper (graph w) κ ∧ (∀ r, κ (mark w r) = o r) ∧ (∀ r, κ (inp w r) = i r) then
      ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp w)), X (κ v) else 0

lemma sum_embTail {N k : ℕ} {R : Type*} [AddCommMonoid R] (i : Inj N k) (g : Inj N (k + 1) → R) :
    ∑ j, (if embTail j = i then g j else 0) =
      ∑ c : {c : Fin N // c ∉ Set.range i}, g (embCons c.1 i c.2) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun c _ => embCons c.1 i c.2) (by simp) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ h
    apply Subtype.ext
    have := congrArg (fun j : Inj N (k + 1) => j 0) h
    simpa [embCons] using this
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    refine ⟨⟨j 0, fun ⟨r, hr⟩ => ?_⟩, mem_univ _, ?_⟩
    · rw [← hj] at hr
      exact Fin.succ_ne_zero r (j.injective hr)
    · ext r
      refine Fin.cases ?_ (fun r' => ?_) r
      · rfl
      · show (i r' : ℕ) = j r'.succ
        rw [← hj]; rfl

open Classical in
lemma colorSum_nil (N : ℕ) (o i : Inj N a) :
    colorSum N (nil : Word a a) o i = if o = i then 1 else 0 := by
  unfold colorSum
  have hprod : ∀ κ : Fin (nv (nil : Word a a)) → Fin N,
      ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp (nil : Word a a))), (X (κ v) : Pol N) = 1 := by
    intro κ
    refine Finset.prod_eq_one fun v hv => ?_
    simp only [mem_filter, mem_univ, true_and] at hv
    exact absurd ⟨v, rfl⟩ hv
  simp only [hprod]
  let o' : Fin (nv (nil : Word a a)) → Fin N := show Fin a → Fin N from ⇑o
  have hcond : ∀ κ : Fin (nv (nil : Word a a)) → Fin N,
      (IsProper (graph (nil : Word a a)) κ ∧ (∀ r, κ (mark nil r) = o r) ∧
        (∀ r, κ (inp nil r) = i r)) ↔ (κ = o' ∧ o = i) := by
    intro κ
    constructor
    · rintro ⟨_, h1, h2⟩
      have e1 : κ = o' := funext fun r => h1 r
      refine ⟨e1, ?_⟩
      ext r
      have := h2 r
      rw [show inp (nil : Word a a) r = r from rfl, e1] at this
      exact congrArg Fin.val (show o r = i r from this)
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun u v huv e => huv (o.injective e), fun r => rfl, fun r => rfl⟩
  simp only [hcond]
  by_cases h : o = i
  · rw [if_pos h, Finset.sum_eq_single o']
    · simp [h]
    · intro κ _ hκ; simp [hκ]
    · simp
  · rw [if_neg h]; simp [h]

variable {N : ℕ}

/-- Colour a word graph after an `M̂` step: old colouring plus the colour of the new vertex. -/
def snocM {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (c : Fin N) : Fin (nv (M w)) → Fin N :=
  Fin.snoc (α := fun _ => Fin N) κ c

lemma snocM_cast {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (c : Fin N) (v : Fin (nv w)) :
    snocM w κ c v.castSucc = κ v := by simp [snocM]

lemma snocM_last {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (c : Fin N) :
    snocM w κ c (Fin.last (nv w)) = c := by simp [snocM]

lemma isProper_snocM {b : ℕ} (w : Word a b) (κ : Fin (nv w) → Fin N) (c : Fin N) :
    IsProper (graph (M w)) (snocM w κ c) ↔ IsProper (graph w) κ ∧ ∀ r, κ (mark w r) ≠ c := by
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, fun r => ?_⟩
    · have := h u.castSucc v.castSucc (by simpa [graph, adj] using huv)
      rwa [snocM_cast, snocM_cast] at this
    · have := h (mark w r).castSucc (Fin.last (nv w)) (by simp [graph, adj])
      rwa [snocM_cast, snocM_last] at this
  · rintro ⟨h1, h2⟩ u v huv
    induction u using Fin.lastCases with
    | last =>
      induction v using Fin.lastCases with
      | last => simp [graph, adj] at huv
      | cast v' =>
        simp only [graph, adj, extendAdj_lc] at huv
        obtain ⟨r, rfl⟩ := huv
        rw [snocM_last, snocM_cast]; exact (h2 r).symm
    | cast u' =>
      induction v using Fin.lastCases with
      | last =>
        simp only [graph, adj, extendAdj_cl] at huv
        obtain ⟨r, rfl⟩ := huv
        rw [snocM_last, snocM_cast]; exact h2 r
      | cast v' =>
        simp only [graph, adj, extendAdj_cc] at huv
        rw [snocM_cast, snocM_cast]; exact h1 u' v' huv

open Classical in
lemma colorSum_M {b : ℕ} (w : Word a b) (o : Inj N (b + 1)) (i : Inj N a) :
    colorSum N (M w) o i = X (o (Fin.last b)) * colorSum N w (embInit o) i := by
  unfold colorSum
  have hsplit : ∀ F : (Fin (nv (M w)) → Fin N) → Pol N,
      ∑ κ, F κ = ∑ c : Fin N, ∑ κ : Fin (nv w) → Fin N, F (snocM w κ c) := by
    intro F
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.snocEquiv (n := nv w) (fun _ => Fin N)).symm _ _
      (fun κ => by simp [snocM, Fin.snocEquiv])
  refine (hsplit _).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  -- the product over non-input vertices
  have hprod : ∀ c, ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp (M w))), X (snocM w κ c v) =
      (∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp w)), (X (κ v) : Pol N)) * X c := by
    intro c
    rw [Finset.prod_filter, Finset.prod_filter]
    erw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      have hiff : (v.castSucc ∉ Set.range (inp (M w))) ↔ v ∉ Set.range (inp w) := by
        constructor
        · rintro h ⟨r, hr⟩; exact h ⟨r, by rw [← hr]; rfl⟩
        · rintro h ⟨r, hr⟩; exact h ⟨r, Fin.castSucc_injective _ hr⟩
      rw [snocM_cast]
      split_ifs <;> first | rfl | (exfalso; tauto)
    · have : Fin.last (nv w) ∉ Set.range (inp (M w)) := by
        rintro ⟨r, hr⟩; exact Fin.castSucc_ne_last _ hr
      split_ifs with h
      · exact absurd h this
      · simp [snocM_last]
  simp only [hprod]
  -- the conditions
  have hcond : ∀ c, (IsProper (graph (M w)) (snocM w κ c) ∧ (∀ r, snocM w κ c (mark (M w) r) = o r) ∧
      (∀ r, snocM w κ c (inp (M w) r) = i r)) ↔
      ((IsProper (graph w) κ ∧ (∀ r, κ (mark w r) = embInit o r) ∧ (∀ r, κ (inp w r) = i r)) ∧
        c = o (Fin.last b)) := by
    intro c
    have hm : (∀ r, snocM w κ c (mark (M w) r) = o r) ↔
        (∀ r, κ (mark w r) = embInit o r) ∧ c = o (Fin.last b) := by
      rw [Fin.forall_fin_succ']
      simp only [mark, Fin.snoc_castSucc, Fin.snoc_last, snocM_cast, snocM_last]
      rfl
    have hi : (∀ r, snocM w κ c (inp (M w) r) = i r) ↔ (∀ r, κ (inp w r) = i r) := by
      simp only [inp, snocM_cast]
    rw [isProper_snocM, hm, hi]
    constructor
    · rintro ⟨⟨hp, _⟩, ⟨hmk, hc⟩, hin⟩; exact ⟨⟨hp, hmk, hin⟩, hc⟩
    · rintro ⟨⟨hp, hmk, hin⟩, rfl⟩
      refine ⟨⟨hp, fun r e => ?_⟩, ⟨hmk, rfl⟩, hin⟩
      rw [hmk r] at e
      exact Fin.castSucc_ne_last r (o.injective e)
  simp only [hcond]
  rw [Finset.sum_eq_single (o (Fin.last b))]
  · split_ifs <;> simp_all [mul_comm]
  · intro c _ hc; simp [hc]
  · simp

open Classical in
lemma colorSum_D {b : ℕ} (w : Word a (b + 1)) (o : Inj N b) (i : Inj N a) :
    colorSum N (D w) o i =
      ∑ c : {c : Fin N // c ∉ Set.range o}, colorSum N w (embCons c.1 o c.2) i := by
  unfold colorSum
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  set PP := ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp w)), (X (κ v) : Pol N)
  have hB : ∀ c : {c : Fin N // c ∉ Set.range o},
      (IsProper (graph w) κ ∧ (∀ r, κ (mark w r) = embCons c.1 o c.2 r) ∧ (∀ r, κ (inp w r) = i r)) ↔
      (IsProper (graph w) κ ∧ κ (mark w 0) = c.1 ∧ (∀ r, κ (mark w r.succ) = o r) ∧
        (∀ r, κ (inp w r) = i r)) := by
    intro c
    rw [Fin.forall_fin_succ]
    simp only [embCons]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩
  show (if IsProper (graph w) κ ∧ (∀ r, κ (mark w r.succ) = o r) ∧ (∀ r, κ (inp w r) = i r)
      then PP else 0) = _
  simp only [hB]
  by_cases hA : IsProper (graph w) κ ∧ (∀ r, κ (mark w r.succ) = o r) ∧ (∀ r, κ (inp w r) = i r)
  · obtain ⟨hp, hm, hi⟩ := hA
    have hc0 : κ (mark w 0) ∉ Set.range o := by
      rintro ⟨r, hr⟩
      rw [← hm r] at hr
      exact hp _ _ (mark_clique w 0 r.succ (Fin.succ_ne_zero r).symm) hr.symm
    rw [if_pos ⟨hp, hm, hi⟩, Fintype.sum_eq_single ⟨κ (mark w 0), hc0⟩]
    · rw [if_pos ⟨hp, rfl, hm, hi⟩]
    · intro c hc
      rw [if_neg]
      rintro ⟨_, h, _⟩
      exact hc (Subtype.ext h.symm)
  · rw [if_neg hA]
    symm
    refine Fintype.sum_eq_zero _ fun c => if_neg ?_
    rintro ⟨h1, _, h3, h4⟩
    exact hA ⟨h1, h3, h4⟩

/-- **Lemma `color`** for words: the colour matrix of a word counts proper colourings of its
graph with prescribed colours on the marked and input vertices. -/
theorem colMatP_eq_colorSum : ∀ {b : ℕ} (w : Word a b) (o : Inj N b) (i : Inj N a),
    colMatP N w o i = colorSum N w o i
  | _, nil, o, i => by
    rw [colorSum_nil, colMatP, one_apply]
  | _, M (b := b) w, o, i => by
    rw [colMatP, colorSum_M, Matrix.mul_apply]
    simp only [MmatP, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), colMatP_eq_colorSum w]
  | _, D (b := b) w, o, i => by
    rw [colMatP, colorSum_D, Matrix.mul_apply]
    simp only [DmatP, ite_mul, one_mul, zero_mul]
    rw [sum_embTail]
    exact Fintype.sum_congr _ _ fun c => colMatP_eq_colorSum w _ _

end Word





end ProperCircularArc
