import ProperCircularArc.Coefficients
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The block linear system

For `w` with admissible columns `T = T(w)` and run starts `Z = Z(w)`, the columns
`U_k b_{w,y}`, `y ∈ T`, are determined by the square system

  `∑_y A(y|w) u_y = r_0`,   `∑_y A(y|w)/(z - y) u_y = r_z`   (`z ∈ Z`).

We show that its coefficient matrix is invertible (the paper's null-vector argument with the
polynomial `P`), and package a two-sided inverse.
-/

noncomputable section

namespace ProperCircularArc

open Finset Polynomial

/-- The paper's argument: a null vector of the Cauchy-type system vanishes. -/
lemma cauchy_null (T Z : Finset ℚ) (hTZ : Disjoint T Z) (hcard : T.card = Z.card + 1)
    (c : ℚ → ℚ) (h0 : ∑ y ∈ T, c y = 0) (hz : ∀ z ∈ Z, ∑ y ∈ T, c y / (z - y) = 0) :
    ∀ y ∈ T, c y = 0 := by
  classical
  let P : ℚ[X] := ∑ y ∈ T, C (c y) * Lagrange.nodal (T.erase y) id
  have hdeg_each : ∀ y ∈ T, (C (c y) * Lagrange.nodal (T.erase y) id).natDegree ≤ T.card - 1 := by
    intro y hy
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Lagrange.natDegree_nodal, card_erase_of_mem hy]
  have hdeg : P.natDegree ≤ T.card - 1 := by
    refine (natDegree_sum_le _ _).trans ?_
    exact Finset.sup_le fun y hy => hdeg_each y hy
  have hcoeff : P.coeff (T.card - 1) = 0 := by
    simp only [P, finset_sum_coeff, coeff_C_mul]
    rw [← h0]
    refine sum_congr rfl fun y hy => ?_
    have hm : (Lagrange.nodal (T.erase y) (id : ℚ → ℚ)).Monic := Lagrange.nodal_monic
    have : (Lagrange.nodal (T.erase y) (id : ℚ → ℚ)).natDegree = T.card - 1 := by
      rw [Lagrange.natDegree_nodal, card_erase_of_mem hy]
    rw [← this, hm.coeff_natDegree, mul_one]
  have hdeg1 := natDegree_le_pred hdeg hcoeff
  have hevalZ : ∀ z ∈ Z, P.eval z = 0 := by
    intro z hzZ
    have hzT : z ∉ T := fun h => Finset.disjoint_left.1 hTZ h hzZ
    simp only [P, eval_finsetSum, eval_mul, eval_C, Lagrange.eval_nodal, id]
    have hQ : ∀ y ∈ T, ∏ y' ∈ T.erase y, (z - y') = (∏ y' ∈ T, (z - y')) / (z - y) := by
      intro y hy
      have hne : z - y ≠ 0 := sub_ne_zero.2 fun e => hzT (e ▸ hy)
      rw [eq_div_iff hne, prod_erase_mul _ _ hy]
    rw [sum_congr rfl fun y hy => by rw [hQ y hy]]
    have : ∑ y ∈ T, c y * ((∏ y' ∈ T, (z - y')) / (z - y))
        = (∏ y' ∈ T, (z - y')) * ∑ y ∈ T, c y / (z - y) := by
      rw [mul_sum]; refine sum_congr rfl fun y _ => by ring
    rw [this, hz z hzZ, mul_zero]
  have hP : P = 0 := by
    by_cases hZ : Z.card = 0
    · have hd0 : P.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero hd0]
      have : T.card - 1 = 0 := by omega
      rw [this] at hcoeff
      rw [hcoeff, C_0]
    · exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Z hevalZ (by omega)
  intro y0 hy0
  have h := congrArg (eval y0) hP
  simp only [P, eval_finsetSum, eval_mul, eval_C, Lagrange.eval_nodal, id, eval_zero] at h
  rw [← sum_erase_add _ _ hy0] at h
  rw [sum_eq_zero (fun y hy => by
    have hy0' : y0 ∈ T.erase y := mem_erase.2 ⟨fun e => (mem_erase.1 hy).1 e.symm, hy0⟩
    rw [prod_eq_zero hy0' (sub_self _), mul_zero]), zero_add] at h
  have hprod : ∏ y' ∈ T.erase y0, (y0 - y') ≠ 0 :=
    prod_ne_zero_iff.2 fun y' hy' => sub_ne_zero.2 fun e => (mem_erase.1 hy').1 e.symm
  exact (mul_eq_zero.1 h).resolve_right hprod

/-! ## The system attached to a column set -/

/-- The coefficient of the block system: row `none` is the `M`-equation and row `some z` the
`R`-equation at the run start `z`. -/
def blockC (s : Finset ℕ) (r : Option (Zset s)) (y : Tset s) : ℚ :=
  match r with
  | none => Acoef y s
  | some z => Acoef y s / ((z : ℚ) - y)

lemma blockC_injective (s : Finset ℕ) (h0 : 0 ∉ s) (v : Tset s → ℚ)
    (hv : ∀ r, ∑ y, blockC s r y * v y = 0) : v = 0 := by
  classical
  let Tq : Finset ℚ := (Tset s).image (fun y : ℕ => (y : ℚ))
  let Zq : Finset ℚ := (Zset s).image (fun y : ℕ => (y : ℚ))
  have hinj : Function.Injective (fun y : ℕ => (y : ℚ)) := Nat.cast_injective
  let c : ℚ → ℚ := fun q => if h : ∃ y : Tset s, (y : ℚ) = q then
    Acoef h.choose s * v h.choose else 0
  have hc : ∀ y : Tset s, c y = Acoef y s * v y := by
    intro y
    have hex : ∃ y' : Tset s, (y' : ℚ) = (y : ℚ) := ⟨y, rfl⟩
    simp only [c, dif_pos hex]
    have : hex.choose = y := Subtype.ext (Nat.cast_injective hex.choose_spec)
    rw [this]
  have hsumT : ∀ f : ℚ → ℚ, ∑ q ∈ Tq, f q = ∑ y : Tset s, f y := by
    intro f
    rw [sum_image (fun a _ b _ h => hinj h)]
    exact (sum_coe_sort (Tset s) (fun y => f y)).symm
  have h0' : ∑ q ∈ Tq, c q = 0 := by
    rw [hsumT]
    simpa [hc, blockC] using hv none
  have hz' : ∀ z ∈ Zq, ∑ q ∈ Tq, c q / (z - q) = 0 := by
    intro z hz
    obtain ⟨z0, hz0, rfl⟩ := mem_image.1 hz
    rw [hsumT]
    have := hv (some ⟨z0, hz0⟩)
    simp only [blockC] at this
    rw [← this]
    refine sum_congr rfl fun y _ => ?_
    rw [hc]; ring
  have hTZ : Disjoint Tq Zq := by
    rw [disjoint_image hinj]; exact disjoint_Tset_Zset s
  have hcard : Tq.card = Zq.card + 1 := by
    rw [card_image_of_injective _ hinj, card_image_of_injective _ hinj, card_Tset s h0]
  have := cauchy_null Tq Zq hTZ hcard c h0' hz'
  funext y
  have hy := this y (mem_image_of_mem _ y.2)
  rw [hc] at hy
  exact (mul_eq_zero.1 hy).resolve_left (Acoef_ne_zero y.2)

/-- The block map as a linear map. -/
def blockMap (s : Finset ℕ) : (Tset s → ℚ) →ₗ[ℚ] (Option (Zset s) → ℚ) where
  toFun v r := ∑ y, blockC s r y * v y
  map_add' v w := by funext r; simp [mul_add, sum_add_distrib]
  map_smul' a v := by funext r; simp [mul_sum, mul_left_comm]

lemma blockMap_surjective (s : Finset ℕ) (h0 : 0 ∉ s) : Function.Surjective (blockMap s) := by
  have hinj : Function.Injective (blockMap s) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact blockC_injective s h0 v fun r => congrFun hv r
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_option, card_Tset s h0]

/-- A right inverse of the block system: `blockInv s r` solves the system with right-hand side
the indicator of row `r`. -/
def blockInv (s : Finset ℕ) (r : Option (Zset s)) (y : Tset s) : ℚ :=
  if h0 : 0 ∉ s then (blockMap_surjective s h0 (Pi.single r 1)).choose y else 0

lemma blockC_blockInv (s : Finset ℕ) (h0 : 0 ∉ s) (r r' : Option (Zset s)) :
    ∑ y, blockC s r' y * blockInv s r y = if r' = r then 1 else 0 := by
  have := congrFun (blockMap_surjective s h0 (Pi.single r 1)).choose_spec r'
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk] at this
  simp only [blockInv, dif_pos h0]
  refine this.trans ?_
  simp [Pi.single_apply]

lemma blockInv_blockC (s : Finset ℕ) (h0 : 0 ∉ s) (y y' : Tset s) :
    ∑ r, blockInv s r y * blockC s r y' = if y = y' then 1 else 0 := by
  classical
  -- apply injectivity to the difference of the two columns
  let v : Tset s → ℚ := fun y => ∑ r, blockInv s r y * blockC s r y' - if y = y' then 1 else 0
  have hv : ∀ r', ∑ y, blockC s r' y * v y = 0 := by
    intro r'
    have e1 : ∑ y, blockC s r' y * v y
        = ∑ r, (∑ y, blockC s r' y * blockInv s r y) * blockC s r y' - blockC s r' y' := by
      simp only [v, mul_sub, sum_sub_distrib, mul_sum, sum_mul]
      congr 1
      · rw [sum_comm]
        exact sum_congr rfl fun r _ => sum_congr rfl fun y _ => by ring
      · simp [mul_ite]
    rw [e1]
    simp_rw [blockC_blockInv s h0]
    simp
  have := congrFun (blockC_injective s h0 v hv) y
  simp only [v, Pi.zero_apply] at this
  linarith

/-- Solving the block system with right-hand sides in any `ℚ`-module. -/
lemma blockSolve {M : Type*} [AddCommGroup M] [Module ℚ M] (s : Finset ℕ) (h0 : 0 ∉ s)
    (rhs : Option (Zset s) → M) (r' : Option (Zset s)) :
    ∑ y, blockC s r' y • (∑ r, blockInv s r y • rhs r) = rhs r' := by
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [← sum_smul]
  rw [sum_eq_single r']
  · rw [blockC_blockInv s h0 r' r', if_pos rfl, one_smul]
  · intro r _ hr
    rw [blockC_blockInv s h0 r r', if_neg (Ne.symm hr), zero_smul]
  · intro h; exact absurd (mem_univ _) h

/-- Inverting the block system: if `rhs r = ∑_y C r y • x y` then `x y = ∑_r D y r • rhs r`. -/
lemma blockInvert {M : Type*} [AddCommGroup M] [Module ℚ M] (s : Finset ℕ) (h0 : 0 ∉ s)
    (x : Tset s → M) (y : Tset s) :
    ∑ r, blockInv s r y • (∑ y', blockC s r y' • x y') = x y := by
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [← sum_smul, blockInv_blockC s h0]
  simp

end ProperCircularArc
