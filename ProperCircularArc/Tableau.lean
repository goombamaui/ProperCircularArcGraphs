import ProperCircularArc.Laurent
import ProperCircularArc.Coefficients
import ProperCircularArc.Color
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Module

/-!
# Tableau operators

The tableau space `V_k` has a basis `b_σ` indexed by `k`-tuples `σ` of distinct positive
integers (the columns of the marked boxes).  We index by arbitrary tuples `σ : Fin k → ℕ`
and let all operators vanish on *invalid* tuples (repeated or zero entries).

* `M_k b_σ = ∑_y A(y ∣ σ) b_{σ,y}`,
* `D_k b_σ = (e_{σ_1} / e_{σ_1 - 1}) b_{σ_2, …, σ_k}`,
* `S_s b_σ = (1/(σ_{s+1} - σ_s)) b_σ + (1 - 1/(σ_{s+1} - σ_s)) b_{τ_s σ}`,
* `R_k = M_{k-1} D_k - D_{k+1} M_k`.
-/

noncomputable section

namespace ProperCircularArc

open Finset

/-- Tableau indices at level `n`. -/
abbrev Idx (n : ℕ) := Fin n → ℕ

/-- The set of entries of a tuple. -/
def entries {n : ℕ} (σ : Idx n) : Finset ℕ := univ.image σ

/-- A tuple of distinct positive integers. -/
def Valid {n : ℕ} (σ : Idx n) : Prop := Function.Injective σ ∧ ∀ i, 1 ≤ σ i

open Classical in
noncomputable instance {n : ℕ} : DecidablePred (Valid (n := n)) := fun _ => inferInstance

/-- The tableau space `V_n`. -/
abbrev V (n : ℕ) := Idx n →₀ Lam

/-- The basis vector `b_σ`. -/
def bv {n : ℕ} (σ : Idx n) : V n := Finsupp.single σ 1

/-- Rational numbers inside `Lam`. -/
def qc (q : ℚ) : Lam := algebraMap ℚ Lam q

@[simp] lemma qc_zero : qc 0 = 0 := map_zero _
@[simp] lemma qc_one : qc 1 = 1 := map_one _
lemma qc_add (a b : ℚ) : qc (a + b) = qc a + qc b := map_add _ _ _
lemma qc_sub (a b : ℚ) : qc (a - b) = qc a - qc b := map_sub _ _ _
lemma qc_mul (a b : ℚ) : qc (a * b) = qc a * qc b := map_mul _ _ _
lemma qc_neg (a : ℚ) : qc (-a) = -qc a := map_neg _ _

/-- Append an entry at the end. -/
abbrev snoc {n : ℕ} (σ : Idx n) (y : ℕ) : Idx (n + 1) := Fin.snoc (α := fun _ => ℕ) σ y

/-- Prepend an entry. -/
abbrev cons {n : ℕ} (a : ℕ) (σ : Idx n) : Idx (n + 1) := Fin.cons (α := fun _ => ℕ) a σ

@[simp] lemma snoc_last' {n : ℕ} (σ : Idx n) (y : ℕ) : snoc σ y (Fin.last n) = y :=
  Fin.snoc_last (α := fun _ => ℕ) (p := σ) (x := y)

@[simp] lemma snoc_castSucc' {n : ℕ} (σ : Idx n) (y : ℕ) (i : Fin n) :
    snoc σ y i.castSucc = σ i :=
  Fin.snoc_castSucc (α := fun _ => ℕ) (p := σ) (x := y) (i := i)

@[simp] lemma init_snoc' {n : ℕ} (σ : Idx n) (y : ℕ) : Fin.init (snoc σ y) = σ :=
  Fin.init_snoc (α := fun _ => ℕ) (p := σ) (x := y)

@[simp] lemma cons_zero' {n : ℕ} (a : ℕ) (σ : Idx n) : cons a σ 0 = a := rfl

@[simp] lemma cons_succ' {n : ℕ} (a : ℕ) (σ : Idx n) (i : Fin n) : cons a σ i.succ = σ i := rfl

@[simp] lemma tail_cons' {n : ℕ} (a : ℕ) (σ : Idx n) : Fin.tail (cons a σ) = σ := rfl

/-- Entry `i` of a tuple, or `0` if out of range. -/
def getE {n : ℕ} (σ : Idx n) (i : ℕ) : ℕ := if h : i < n then σ ⟨i, h⟩ else 0

/-- The weight `1/(σ_{s+1} - σ_s)` of the swap operator. -/
def swc {n : ℕ} (σ : Idx n) (s : ℕ) : ℚ := 1 / ((getE σ (s + 1) : ℚ) - getE σ s)

/-- The image of a basis vector under `M_n`. -/
def Mvec {n : ℕ} (σ : Idx n) : V (n + 1) :=
  if Valid σ then ∑ y ∈ Tset (entries σ), qc (Acoef y (entries σ)) • bv (snoc σ y) else 0

/-- `M_n : V_n → V_{n+1}`. -/
def Mop (n : ℕ) : V n →ₗ[Lam] V (n + 1) := Finsupp.linearCombination Lam Mvec

/-- `D_{n+1} : V_{n+1} → V_n`. -/
def Dop (n : ℕ) : V (n + 1) →ₗ[Lam] V n :=
  Finsupp.linearCombination Lam fun σ => if Valid σ then Eratio (σ 0) • bv (Fin.tail σ) else 0

/-- `S_s : V_n → V_n` (positions `s, s+1`, 0-based); the identity on invalid tuples. -/
def Sop (n s : ℕ) : V n →ₗ[Lam] V n :=
  Finsupp.linearCombination Lam fun σ =>
    if Valid σ then qc (swc σ s) • bv σ + qc (1 - swc σ s) • bv (σ ∘ swapPerm n s) else bv σ

/-- `R_{n+1} = M_n D_{n+1} - D_{n+2} M_{n+1} : V_{n+1} → V_{n+1}`. -/
def Rop (n : ℕ) : V (n + 1) →ₗ[Lam] V (n + 1) := Mop n ∘ₗ Dop n - Dop (n + 1) ∘ₗ Mop (n + 1)

/-! ## Evaluation on basis vectors -/

lemma Mop_bv {n : ℕ} (σ : Idx n) : Mop n (bv σ) = Mvec σ := by
  simp [Mop, bv]

lemma Mop_bv_valid {n : ℕ} {σ : Idx n} (h : Valid σ) :
    Mop n (bv σ) = ∑ y ∈ Tset (entries σ), qc (Acoef y (entries σ)) • bv (snoc σ y) := by
  simp [Mop_bv, Mvec, h]

lemma Mop_bv_invalid {n : ℕ} {σ : Idx n} (h : ¬Valid σ) : Mop n (bv σ) = 0 := by
  simp [Mop_bv, Mvec, h]

lemma Dop_bv_valid {n : ℕ} {σ : Idx (n + 1)} (h : Valid σ) :
    Dop n (bv σ) = Eratio (σ 0) • bv (Fin.tail σ) := by
  simp [Dop, bv, h]

lemma Dop_bv_invalid {n : ℕ} {σ : Idx (n + 1)} (h : ¬Valid σ) : Dop n (bv σ) = 0 := by
  simp [Dop, bv, h]

lemma Sop_bv_valid {n s : ℕ} {σ : Idx n} (h : Valid σ) :
    Sop n s (bv σ) = qc (swc σ s) • bv σ + qc (1 - swc σ s) • bv (σ ∘ swapPerm n s) := by
  simp [Sop, bv, h]

lemma Sop_bv_invalid {n s : ℕ} {σ : Idx n} (h : ¬Valid σ) : Sop n s (bv σ) = bv σ := by
  simp [Sop, bv, h]

/-! ## Entries and validity -/

lemma entries_snoc {n : ℕ} (σ : Idx n) (y : ℕ) : entries (snoc σ y) = insert y (entries σ) := by
  ext x
  simp only [entries, mem_image, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast j => exact Or.inr ⟨j, by simp⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last n, by simp⟩
    · exact ⟨j.castSucc, by simp⟩

lemma entries_cons {n : ℕ} (a : ℕ) (σ : Idx n) : entries (cons a σ) = insert a (entries σ) := by
  ext x
  simp only [entries, mem_image, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => simp
    | succ j => exact Or.inr ⟨j, by simp⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨j.succ, by simp⟩

lemma entries_comp_perm {n : ℕ} (σ : Idx n) (π : Equiv.Perm (Fin n)) :
    entries (σ ∘ π) = entries σ := by
  ext x
  simp only [entries, mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨π i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨π.symm i, by simp⟩

lemma mem_entries {n : ℕ} {σ : Idx n} {x : ℕ} : x ∈ entries σ ↔ ∃ i, σ i = x := by
  simp [entries]

lemma valid_snoc {n : ℕ} {σ : Idx n} (h : Valid σ) {y : ℕ} (hy : y ∉ entries σ) (hy1 : 1 ≤ y) :
    Valid (snoc σ y) := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j' =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd (mem_entries.2 ⟨j', hij.symm⟩) hy
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd (mem_entries.2 ⟨i', hij⟩) hy
      | cast j' =>
        simp only [Fin.snoc_castSucc] at hij
        rw [h.1 hij]
  · induction i using Fin.lastCases with
    | last => simpa using hy1
    | cast i' => simpa using h.2 i'

lemma valid_snoc_of_mem_Tset {n : ℕ} {σ : Idx n} (h : Valid σ) {y : ℕ}
    (hy : y ∈ Tset (entries σ)) : Valid (snoc σ y) :=
  valid_snoc h (not_mem_of_mem_Tset hy) (pos_of_mem_Tset hy)

lemma valid_cons {n : ℕ} {σ : Idx n} (h : Valid σ) {a : ℕ} (ha : a ∉ entries σ) (ha1 : 1 ≤ a) :
    Valid (cons a σ) := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j' =>
        simp only [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd (mem_entries.2 ⟨j', hij.symm⟩) ha
    | succ i' =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd (mem_entries.2 ⟨i', hij⟩) ha
      | succ j' =>
        simp only [Fin.cons_succ] at hij
        rw [h.1 hij]
  · induction i using Fin.cases with
    | zero => simpa using ha1
    | succ i' => simpa using h.2 i'

lemma valid_of_cons {n : ℕ} {a : ℕ} {σ : Idx n} (h : Valid (cons a σ)) :
    Valid σ ∧ a ∉ entries σ ∧ 1 ≤ a := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun hm => ?_, ?_⟩
  · have := h.1 (show cons a σ i.succ = cons a σ j.succ by simpa using hij)
    exact Fin.succ_injective _ this
  · simpa using h.2 i.succ
  · obtain ⟨i, hi⟩ := mem_entries.1 hm
    have := h.1 (show cons a σ i.succ = cons a σ 0 by simpa using hi)
    exact Fin.succ_ne_zero _ this
  · simpa using h.2 0

lemma valid_of_snoc {n : ℕ} {y : ℕ} {σ : Idx n} (h : Valid (snoc σ y)) :
    Valid σ ∧ y ∉ entries σ ∧ 1 ≤ y := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun hm => ?_, ?_⟩
  · have := h.1 (show snoc σ y i.castSucc = snoc σ y j.castSucc by simpa using hij)
    exact Fin.castSucc_injective _ this
  · simpa using h.2 i.castSucc
  · obtain ⟨i, hi⟩ := mem_entries.1 hm
    have := h.1 (show snoc σ y i.castSucc = snoc σ y (Fin.last n) by simpa using hi)
    exact Fin.castSucc_ne_last _ this
  · simpa using h.2 (Fin.last n)

lemma cons_eq_self {n : ℕ} (σ : Idx (n + 1)) : cons (σ 0) (Fin.tail σ) = σ := Fin.cons_self_tail σ

lemma snoc_eq_self {n : ℕ} (σ : Idx (n + 1)) : snoc (Fin.init σ) (σ (Fin.last n)) = σ :=
  Fin.snoc_init_self σ

lemma valid_tail {n : ℕ} {σ : Idx (n + 1)} (h : Valid σ) : Valid (Fin.tail σ) := by
  have h' : Valid (cons (σ 0) (Fin.tail σ)) := by rwa [cons_eq_self]
  exact (valid_of_cons h').1

lemma valid_init {n : ℕ} {σ : Idx (n + 1)} (h : Valid σ) : Valid (Fin.init σ) := by
  have h' : Valid (snoc (Fin.init σ) (σ (Fin.last n))) := by rwa [snoc_eq_self]
  exact (valid_of_snoc h').1

lemma valid_comp_perm {n : ℕ} {σ : Idx n} (h : Valid σ) (π : Equiv.Perm (Fin n)) :
    Valid (σ ∘ π) :=
  ⟨h.1.comp π.injective, fun i => h.2 _⟩

lemma snoc_cons_comm {n : ℕ} (a : ℕ) (w : Idx n) (y : ℕ) :
    snoc (cons a w) y = cons a (snoc w y) := (Fin.cons_snoc_eq_snoc_cons _ _ _).symm

lemma tail_snoc_cons {n : ℕ} (a : ℕ) (w : Idx n) (y : ℕ) :
    Fin.tail (snoc (cons a w) y) = snoc w y := by
  rw [show snoc (cons a w) y = cons a (snoc w y) from (Fin.cons_snoc_eq_snoc_cons _ _ _).symm]
  rfl

lemma snoc_cons_zero {n : ℕ} (a : ℕ) (w : Idx n) (y : ℕ) : snoc (cons a w) y 0 = a := by
  rw [show snoc (cons a w) y = cons a (snoc w y) from (Fin.cons_snoc_eq_snoc_cons _ _ _).symm]
  rfl

/-! ## Equation (R) -/

lemma Mop_extend {n : ℕ} {σ : Idx n} (h : Valid σ) {Y : Finset ℕ} (hY : Tset (entries σ) ⊆ Y) :
    Mop n (bv σ) = ∑ y ∈ Y, qc (Acoef y (entries σ)) • bv (snoc σ y) := by
  rw [Mop_bv_valid h]
  refine sum_subset hY fun y _ hy => ?_
  simp [Acoef_of_not_mem hy]

/-- The difference form of `R_k b_{a,w}`. -/
lemma Rop_cons_diff {n : ℕ} {a : ℕ} {w : Idx n} (h : Valid (cons a w)) {Y : Finset ℕ}
    (hY1 : Tset (entries w) ⊆ Y) (hY2 : Tset (insert a (entries w)) ⊆ Y) :
    Rop n (bv (cons a w)) = Eratio a •
      ∑ y ∈ Y, qc (Acoef y (entries w) - Acoef y (insert a (entries w))) • bv (snoc w y) := by
  obtain ⟨hw, ha, ha1⟩ := valid_of_cons h
  simp only [Rop, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [Dop_bv_valid h]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [map_smul, Mop_extend hw hY1, Mop_bv_valid h, entries_cons, map_sum]
  have : ∑ y ∈ Tset (insert a (entries w)), Dop (n + 1) (qc (Acoef y (insert a (entries w))) •
        bv (snoc (cons a w) y))
      = ∑ y ∈ Y, Eratio a • qc (Acoef y (insert a (entries w))) • bv (snoc w y) := by
    rw [← sum_subset hY2 (fun y _ hy => by simp [Acoef_of_not_mem hy])]
    refine sum_congr rfl fun y hy => ?_
    have hv : Valid (snoc (cons a w) y) := valid_snoc_of_mem_Tset h (by rwa [entries_cons])
    rw [map_smul, Dop_bv_valid hv, snoc_cons_zero, tail_snoc_cons, smul_comm]
  rw [this, smul_sum, ← sum_sub_distrib, smul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [qc_sub, sub_smul, smul_sub]

/-- **Equation (R)**: `R_k b_{a,w} = (e_a/e_{a-1}) (∑_{y ∈ T(w)} A(y|w)/(a+1-y) b_{w,y}
 - A(a+1 ∣ a,w) b_{w,a+1})`. -/
lemma Rop_cons {n : ℕ} {a : ℕ} {w : Idx n} (h : Valid (cons a w)) :
    Rop n (bv (cons a w)) = Eratio a •
      ((∑ y ∈ Tset (entries w), qc (Acoef y (entries w) / ((a : ℚ) + 1 - y)) • bv (snoc w y))
        - qc (Acoef (a + 1) (insert a (entries w))) • bv (snoc w (a + 1))) := by
  obtain ⟨hw, ha, ha1⟩ := valid_of_cons h
  have haT : a + 1 ∉ Tset (entries w) := fun hm => Acoef_ne_zero hm (Acoef_succ_of_not_mem ha ha1)
  set Y := insert (a + 1) (Tset (entries w))
  have hY1 : Tset (entries w) ⊆ Y := subset_insert _ _
  have hY2 : Tset (insert a (entries w)) ⊆ Y := by
    intro y hy
    by_cases hya : y = a + 1
    · simp [Y, hya]
    · refine mem_insert_of_mem ?_
      rw [mem_Tset] at hy ⊢
      simp only [mem_insert, not_or] at hy
      rcases hy with ⟨⟨_, hy1⟩, h2 | ⟨h3, h4 | h4⟩⟩
      · exact ⟨hy1, Or.inl h2⟩
      · omega
      · exact ⟨hy1, Or.inr ⟨h3, h4⟩⟩
  rw [Rop_cons_diff h hY1 hY2, sum_insert haT, Acoef_of_not_mem haT, zero_sub, qc_neg, neg_smul]
  congr 1
  rw [sub_eq_add_neg, add_comm (_ : V (n + 1))]
  congr 1
  refine sum_congr rfl fun y hy => ?_
  have hya : y ≠ a + 1 := fun e => haT (e ▸ hy)
  rw [Acoef_insert ha hya]
  congr 2
  have : (y : ℚ) - a - 1 ≠ 0 := by
    intro e
    apply hya
    have : (y : ℚ) = ((a + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h2 : (a : ℚ) + 1 - y ≠ 0 := fun e => this (by linarith)
  field_simp
  ring

end ProperCircularArc
