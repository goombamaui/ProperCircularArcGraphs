import ProperCircularArc.Tableaux

/-!
# Exact graph-polynomial certificates

Weighted deletion-contraction evaluates the worked examples with small certificates.
The identities are proved for every number of colours; no floating-point or native
computation is trusted.
-/

noncomputable section

namespace ProperCircularArc

open Finset MvPolynomial

/-- The chromatic sum of an edge list with positive integer vertex weights.
Loops are allowed in the data and force the sum to vanish. -/
def weightedCSF (N : ℕ) {n : ℕ} (w : Fin n → ℕ) (E : Finset (Fin n × Fin n)) : Pol N :=
  ∑ c : Fin n → Fin N, if ∀ e ∈ E, c e.1 ≠ c e.2 then ∏ v, X (c v) ^ w v else 0

/-- Identify the last vertex with `u`. -/
def contractVertex {n : ℕ} (u : Fin n) : Fin (n + 1) → Fin n := Fin.lastCases u id

/-- Add the last vertex's weight to `u`. -/
def contractWeight {n : ℕ} (w : Fin (n + 1) → ℕ) (u : Fin n) : Fin n → ℕ :=
  fun v => w v.castSucc + if v = u then w (Fin.last n) else 0

/-- Images of the remaining edges, including loops when appropriate. -/
def contractEdges {n : ℕ} (E : Finset (Fin (n + 1) × Fin (n + 1))) (u : Fin n) :
    Finset (Fin n × Fin n) := E.image fun e => (contractVertex u e.1, contractVertex u e.2)

lemma weightedCSF_loop (N : ℕ) {n : ℕ} (w : Fin n → ℕ)
    (E : Finset (Fin n × Fin n)) (v : Fin n) (hv : (v, v) ∈ E) : weightedCSF N w E = 0 := by
  classical
  apply sum_eq_zero
  intro c _
  rw [ite_eq_right]
  intro hc
  exact hc (v, v) hv rfl

lemma weightedCSF_empty (N : ℕ) : weightedCSF N (fun v : Fin 0 => v.elim0) ∅ = 1 := by
  classical
  simp [weightedCSF]

lemma weightedCSF_congr (N : ℕ) {n : ℕ} {w w' : Fin n → ℕ}
    {E E' : Finset (Fin n × Fin n)} (hw : w = w')
    (hE : ∀ c : Fin n → Fin N, (∀ e ∈ E, c e.1 ≠ c e.2) ↔ (∀ e ∈ E', c e.1 ≠ c e.2)) :
    weightedCSF N w E = weightedCSF N w' E' := by
  classical
  subst w'
  unfold weightedCSF
  simp_rw [hE]

lemma weighted_product_contract {N n : ℕ} (w : Fin (n + 1) → ℕ) (u : Fin n)
    (c : Fin n → Fin N) :
    (∏ v : Fin (n + 1), (X (Fin.snoc (α := fun _ => Fin N) c (c u) v) : Pol N) ^ w v) =
      ∏ v : Fin n, X (c v) ^ contractWeight w u v := by
  classical
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, contractWeight, pow_add, prod_mul_distrib]
  congr 1
  simp

lemma weightedCSF_equal_last (N : ℕ) {n : ℕ} (w : Fin (n + 1) → ℕ)
    (E : Finset (Fin (n + 1) × Fin (n + 1))) (u : Fin n) :
    (∑ c : Fin (n + 1) → Fin N,
      if (∀ e ∈ E, c e.1 ≠ c e.2) ∧ c (Fin.last n) = c u.castSucc then
        ∏ v, (X (c v) : Pol N) ^ w v else 0) =
      weightedCSF N (contractWeight w u) (contractEdges E u) := by
  classical
  have hsplit : ∀ F : (Fin (n + 1) → Fin N) → Pol N,
      ∑ c, F c = ∑ y : Fin N, ∑ c : Fin n → Fin N, F (Fin.snoc (α := fun _ => Fin N) c y) := by
    intro F
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.snocEquiv (n := n) (fun _ => Fin N)).symm _ _ (by intro c; simp [Fin.snocEquiv])
  rw [hsplit, sum_comm]
  unfold weightedCSF
  apply sum_congr rfl
  intro c _
  rw [sum_eq_single (c u)]
  · have hproper : (∀ e ∈ E, Fin.snoc (α := fun _ => Fin N) c (c u) e.1 ≠ Fin.snoc (α := fun _ => Fin N) c (c u) e.2) ↔
        ∀ e ∈ contractEdges E u, c e.1 ≠ c e.2 := by
      have hc : ∀ v, Fin.snoc (α := fun _ => Fin N) c (c u) v = c (contractVertex u v) := by
        intro v; induction v using Fin.lastCases <;> simp [contractVertex]
      simp only [contractEdges, forall_mem_image, hc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, and_true, hproper]
    rw [weighted_product_contract]
  · intro y _ hy
    simp [hy]
  · simp

/-- Deletion-contraction on an edge incident to the last vertex. -/
theorem weightedCSF_delete_contract (N : ℕ) {n : ℕ} (w : Fin (n + 1) → ℕ)
    (E : Finset (Fin (n + 1) × Fin (n + 1))) (u : Fin n) :
    weightedCSF N w (insert (u.castSucc, Fin.last n) E) = weightedCSF N w E -
      weightedCSF N (contractWeight w u) (contractEdges E u) := by
  classical
  rw [← weightedCSF_equal_last]
  unfold weightedCSF
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  simp only [forall_mem_insert]
  split_ifs <;> simp_all [Ne, eq_comm]

/-- An isolated last vertex contributes its power sum. -/
theorem weightedCSF_isolated (N : ℕ) {n : ℕ} (w : Fin (n + 1) → ℕ)
    (E : Finset (Fin n × Fin n)) :
    weightedCSF N w (E.image fun e => (e.1.castSucc, e.2.castSucc)) =
      (∑ y : Fin N, (X y : Pol N) ^ w (Fin.last n)) * weightedCSF N (fun v => w v.castSucc) E := by
  classical
  unfold weightedCSF
  rw [mul_sum]
  have hsplit : ∀ F : (Fin (n + 1) → Fin N) → Pol N,
      ∑ c, F c = ∑ y : Fin N, ∑ c : Fin n → Fin N, F (Fin.snoc (α := fun _ => Fin N) c y) := by
    intro F
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Fin.snocEquiv (n := n) (fun _ => Fin N)).symm _ _ (by intro c; simp [Fin.snocEquiv])
  rw [hsplit, sum_comm]
  apply sum_congr rfl
  intro c _
  have hproper : ∀ y : Fin N,
      (∀ e ∈ E.image (fun e => (e.1.castSucc, e.2.castSucc)),
        Fin.snoc (α := fun _ => Fin N) c y e.1 ≠ Fin.snoc (α := fun _ => Fin N) c y e.2) ↔
        (∀ e ∈ E, c e.1 ≠ c e.2) := by
    intro y
    simp only [forall_mem_image, Fin.snoc_castSucc]
  simp_rw [hproper]
  split_ifs
  · simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← mul_sum]
    ring
  · simp

/-- Relate an edge certificate to a simple graph's CSF. -/
theorem chromSym_eq_weightedCSF (N : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (E : Finset (Fin n × Fin n))
    (hE : ∀ u v, G.Adj u v ↔ (u, v) ∈ E ∨ (v, u) ∈ E) :
    chromSym N G = weightedCSF N (fun _ => 1) E := by
  classical
  unfold chromSym weightedCSF
  apply sum_congr rfl
  intro c _
  have hp : IsProper G c ↔ ∀ e ∈ E, c e.1 ≠ c e.2 := by
    constructor
    · intro h e he; exact h _ _ ((hE _ _).mpr (Or.inl he))
    · intro h u v huv
      rcases (hE u v).mp huv with he | he
      · exact h (u, v) he
      · exact (h (v, u) he).symm
  simp [hp]

end ProperCircularArc
