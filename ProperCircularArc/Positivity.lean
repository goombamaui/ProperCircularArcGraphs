import ProperCircularArc.Trace
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# `e`-positivity of the trace

The finite tableau matrices have entries that are nonnegative rationals and ratios
`e_a / e_{a-1}`; we realise them over the Laurent polynomials `LN N = ℚ[E_1^{±1}, …, E_N^{±1}]`.
Specialising `E_j ↦ e_j(x_1, …, x_N)` is injective on `LN N` because `e_1, …, e_N` are
algebraically independent.  A symmetric polynomial that is the specialisation of a Laurent
polynomial with nonnegative coefficients is therefore a polynomial in `e_1, …, e_N` with
nonnegative coefficients.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset AddMonoidAlgebra

/-- Laurent polynomials in `E_1, …, E_N` (coordinate `j` is the exponent of `E_{j+1}`). -/
abbrev LN (N : ℕ) := AddMonoidAlgebra ℚ (Fin N →₀ ℤ)

/-- `∏ E_{j+1}^{m_j} ↦ ∏ e_{j+1}^{m_j}`. -/
def valL (N : ℕ) : Multiplicative (Fin N →₀ ℤ) →* KN N where
  toFun m := (Multiplicative.toAdd m).prod fun j n => eK N (j + 1) ^ n
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    exact Finsupp.prod_add_index' (fun _ => zpow_zero _)
      (fun j _ _ => zpow_add₀ (eK_ne_zero (by omega)) _ _)

/-- The specialisation `LN N → K_N`. -/
def phiL (N : ℕ) : LN N →ₐ[ℚ] KN N := AddMonoidAlgebra.lift ℚ (KN N) (Fin N →₀ ℤ) (valL N)

lemma phiL_single (N : ℕ) (m : Fin N →₀ ℤ) (c : ℚ) :
    phiL N (single m c) = c • m.prod fun j n => eK N (j + 1) ^ n := by
  simp only [phiL, lift_single]; rfl

/-! ## Nonnegative coefficients -/

/-- All coefficients are nonnegative. -/
def NonnegL {N : ℕ} (f : LN N) : Prop := ∀ m, 0 ≤ f.coeff m

lemma NonnegL.add {N : ℕ} {f g : LN N} (hf : NonnegL f) (hg : NonnegL g) : NonnegL (f + g) :=
  fun m => by simpa [coeff_add] using add_nonneg (hf m) (hg m)

lemma NonnegL.mul {N : ℕ} {f g : LN N} (hf : NonnegL f) (hg : NonnegL g) : NonnegL (f * g) := by
  classical
  intro m
  rw [AddMonoidAlgebra.coeff_mul]
  refine Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => ?_
  dsimp only
  split_ifs
  · exact mul_nonneg (hf m₁) (hg m₂)
  · exact le_rfl

lemma NonnegL.zero {N : ℕ} : NonnegL (0 : LN N) := fun _ => le_rfl

lemma NonnegL.sum {N : ℕ} {ι : Type*} (s : Finset ι) {f : ι → LN N}
    (hf : ∀ i ∈ s, NonnegL (f i)) : NonnegL (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NonnegL.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

lemma NonnegL.single {N : ℕ} (m : Fin N →₀ ℤ) {c : ℚ} (hc : 0 ≤ c) : NonnegL (single m c) := by
  classical
  intro m'
  rw [coeff_single, Finsupp.single_apply]
  split_ifs <;> simp [hc]

lemma NonnegL.one {N : ℕ} : NonnegL (1 : LN N) := by
  rw [AddMonoidAlgebra.one_def]; exact NonnegL.single _ zero_le_one

lemma NonnegL.ratCast {N : ℕ} {q : ℚ} (hq : 0 ≤ q) : NonnegL (algebraMap ℚ (LN N) q) := by
  rw [coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact NonnegL.single _ hq

/-! ## Injectivity of the specialisation -/

/-- Polynomials in `E_1, …, E_N` inside `LN N`. -/
def embQ (N : ℕ) : MvPolynomial (Fin N) ℚ →ₐ[ℚ] LN N :=
  MvPolynomial.aeval fun j => single (Finsupp.single j 1) 1

lemma single_one_pow {N : ℕ} (m : Fin N →₀ ℤ) (n : ℕ) :
    (single m (1 : ℚ) : LN N) ^ n = single (n • m) 1 := by
  induction n with
  | zero => simp [AddMonoidAlgebra.one_def]
  | succ n ih => rw [pow_succ, ih, single_mul_single, succ_nsmul, mul_one]

lemma prod_single_one {N : ℕ} {ι : Type*} (s : Finset ι) (m : ι → Fin N →₀ ℤ) :
    ∏ i ∈ s, (single (m i) (1 : ℚ) : LN N) = single (∑ i ∈ s, m i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, single_mul_single, mul_one]

lemma embQ_monomial (N : ℕ) (e : Fin N →₀ ℕ) (c : ℚ) :
    embQ N (monomial e c) = single (e.mapRange Int.ofNat rfl) c := by
  classical
  rw [embQ, aeval_monomial, Finsupp.prod]
  simp_rw [single_one_pow]
  rw [prod_single_one, coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, single_mul_single, zero_add, mul_one]
  congr 1
  ext i
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Finsupp.mapRange_apply, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · simp
  · simp [Finsupp.notMem_support_iff.1 h]

lemma embQ_coeff (N : ℕ) (Q : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    (embQ N Q).coeff (e.mapRange Int.ofNat rfl) = Q.coeff e := by
  classical
  have hinj : Function.Injective (fun d : Fin N →₀ ℕ => d.mapRange Int.ofNat rfl) := by
    intro a b h
    ext i
    have := congrArg (fun d : Fin N →₀ ℤ => d i) h
    simpa using this
  induction Q using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [embQ_monomial, coeff_single_apply, coeff_monomial]
    by_cases h : d = e
    · subst h; simp
    · rw [if_neg (fun h' => h (hinj h')), if_neg h]
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, MvPolynomial.coeff_add]

/-- `phiL ∘ embQ` is `q ↦ q(e_1, …, e_N)`. -/
lemma phiL_embQ (N : ℕ) (q : MvPolynomial (Fin N) ℚ) :
    phiL N (embQ N q) = algebraMap (Pol N) (KN N)
      (MvPolynomial.aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) q) := by
  have : ((phiL N).comp (embQ N) : MvPolynomial (Fin N) ℚ →ₐ[ℚ] KN N) =
      ((IsScalarTower.toAlgHom ℚ (Pol N) (KN N)).comp
        (MvPolynomial.aeval fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1))) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, embQ, aeval_X, phiL_single, one_smul,
      IsScalarTower.coe_toAlgHom']
    rw [Finsupp.prod_single_index (by simp), zpow_one]
    rfl
  exact congr($this q)

lemma aeval_esymm_injective (N : ℕ) :
    Function.Injective (MvPolynomial.aeval (R := ℚ) (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1))) := by
  intro p q h
  apply esymmAlgHom_injective ℚ (σ := Fin N) (n := N) (by simp)
  apply Subtype.ext
  simpa [esymmAlgHom_apply] using h

lemma exists_clear {N : ℕ} (f : LN N) :
    ∃ d : Fin N →₀ ℕ, f * single (d.mapRange Int.ofNat rfl) 1 ∈ (embQ N).range := by
  classical
  have hsingle : ∀ (e : Fin N →₀ ℕ) (c : ℚ), single (e.mapRange Int.ofNat rfl) c ∈ (embQ N).range :=
    fun e c => ⟨monomial e c, embQ_monomial N e c⟩
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨d₁, h₁⟩ := hf
    obtain ⟨d₂, h₂⟩ := hg
    refine ⟨d₁ + d₂, ?_⟩
    have e : ((d₁ + d₂).mapRange Int.ofNat rfl : Fin N →₀ ℤ) =
        d₁.mapRange Int.ofNat rfl + d₂.mapRange Int.ofNat rfl := by
      ext i; simp
    rw [add_mul, e, ← mul_one (1 : ℚ), ← single_mul_single, ← mul_assoc,
      mul_comm (single (d₁.mapRange Int.ofNat rfl) 1), ← mul_assoc]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ h₁ (hsingle _ _))
      (Subalgebra.mul_mem _ h₂ (hsingle _ _))
  | single m c =>
    refine ⟨m.mapRange (fun z => (-z).toNat) (by simp), ?_⟩
    rw [single_mul_single, mul_one]
    have : m + (m.mapRange (fun z => (-z).toNat) (by simp)).mapRange Int.ofNat rfl =
        (m.mapRange (fun z => (z + (-z).toNat).toNat) (by simp)).mapRange Int.ofNat rfl := by
      ext i; simp; omega
    rw [this]
    exact hsingle _ _

lemma phiL_injective (N : ℕ) : Function.Injective (phiL N) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨d, hd⟩ := exists_clear f
  obtain ⟨q, hq⟩ := hd
  have hq : embQ N q = f * single (d.mapRange Int.ofNat rfl) 1 := hq
  have h1 : phiL N (embQ N q) = 0 := by rw [hq, map_mul, hf, zero_mul]
  rw [phiL_embQ] at h1
  have h2 : MvPolynomial.aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) q = 0 :=
    algebraMap_injective_KN N (by rw [h1, map_zero])
  have h3 : q = 0 := aeval_esymm_injective N (by rw [h2, map_zero])
  rw [h3, map_zero] at hq
  have hu : (single (d.mapRange Int.ofNat rfl) (1 : ℚ) : LN N) *
      single (-(d.mapRange Int.ofNat rfl)) 1 = 1 := by
    rw [single_mul_single, add_neg_cancel, mul_one, AddMonoidAlgebra.one_def]
  calc f = f * single (d.mapRange Int.ofNat rfl) 1 * single (-(d.mapRange Int.ofNat rfl)) 1 := by
        rw [mul_assoc, hu, mul_one]
    _ = 0 := by rw [← hq, zero_mul]

/-- **`e`-positivity**: a symmetric polynomial that is the specialisation of a Laurent
polynomial in the `E_j` with nonnegative coefficients is a polynomial in `e_1, …, e_N` with
nonnegative coefficients. -/
theorem epos_of_nonneg {N : ℕ} {P0 : Pol N} (hsym : P0.IsSymmetric) {T : LN N} (hT : NonnegL T)
    (h : phiL N T = algebraMap (Pol N) (KN N) P0) :
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      MvPolynomial.aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = P0 := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_surjective ℚ (σ := Fin N) (n := N) (by simp) ⟨P0, hsym⟩
  have hQ' : MvPolynomial.aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) Q = P0 := by
    have := congrArg Subtype.val hQ
    simpa [esymmAlgHom_apply] using this
  refine ⟨Q, fun e => ?_, hQ'⟩
  have hT' : embQ N Q = T := phiL_injective N (by rw [phiL_embQ, hQ', h])
  rw [← embQ_coeff, hT']
  exact hT _

end ProperCircularArc
