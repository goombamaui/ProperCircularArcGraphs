import ProperCircularArc.PowerSum
import ProperCircularArc.Color
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Specialisation to `N` colours

With `N` colours we work in `K N = ℚ(x_1, …, x_N)` and send `E j ↦ e_j(x_1, …, x_N)`, which
vanishes for `j > N`.  This is an algebra map on Laurent monomials whose exponents at `j > N` are
nonnegative; we realise these as the monoid algebra `LamN N` over the submonoid `MN N`.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial

/-- Polynomials in `N` colours. -/
abbrev Pol (N : ℕ) := MvPolynomial (Fin N) ℚ

/-- The field `ℚ(x_1, …, x_N)`. -/
abbrev KN (N : ℕ) := FractionRing (Pol N)

/-- The colour variable `x_c`. -/
def xK (N : ℕ) (c : Fin N) : KN N := algebraMap (Pol N) (KN N) (X c)

/-- The elementary symmetric polynomial `e_j(x_1, …, x_N)`. -/
def eK (N j : ℕ) : KN N := algebraMap (Pol N) (KN N) (esymm (Fin N) ℚ j)

lemma algebraMap_injective_KN (N : ℕ) : Function.Injective (algebraMap (Pol N) (KN N)) :=
  IsFractionRing.injective _ _

@[simp] lemma eK_zero (N : ℕ) : eK N 0 = 1 := by simp [eK, esymm_zero]

lemma esymm_eq_zero_of_lt {N j : ℕ} (h : N < j) : esymm (Fin N) ℚ j = 0 := by
  rw [esymm_eq_multiset_esymm, Multiset.esymm, Multiset.powersetCard_eq_empty]
  · simp
  · simpa using h

lemma eK_eq_zero {N j : ℕ} (h : N < j) : eK N j = 0 := by
  simp [eK, esymm_eq_zero_of_lt h]

lemma esymm_ne_zero {N j : ℕ} (h1 : 1 ≤ j) (h : j ≤ N) : esymm (Fin N) ℚ j ≠ 0 := by
  intro e
  have hinj := esymmAlgHom_injective ℚ (σ := Fin N) (n := N) (by simp)
  have : esymmAlgHom (Fin N) ℚ N (X ⟨j - 1, by omega⟩) = esymmAlgHom (Fin N) ℚ N 0 := by
    apply Subtype.ext
    simp only [esymmAlgHom, aeval_X, map_zero, ZeroMemClass.coe_zero]
    show esymm (Fin N) ℚ (j - 1 + 1) = 0
    rwa [Nat.sub_add_cancel h1]
  exact X_ne_zero _ (hinj this)

lemma eK_ne_zero {N j : ℕ} (h : j ≤ N) : eK N j ≠ 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · simp
  · intro e
    apply esymm_ne_zero h1 h
    apply algebraMap_injective_KN N
    rw [map_zero]; exact e

/-! ## Admissible Laurent monomials -/

/-- Exponent vectors that are nonnegative beyond `N`. -/
def MN (N : ℕ) : AddSubmonoid (ℕ →₀ ℤ) where
  carrier := {m | ∀ j, N < j → 0 ≤ m j}
  add_mem' {a b} ha hb j hj := by simpa using add_nonneg (ha j hj) (hb j hj)
  zero_mem' j _ := le_rfl

/-- Admissible Laurent polynomials. -/
abbrev LamN (N : ℕ) := AddMonoidAlgebra ℚ (MN N)

/-- The inclusion `LamN N → Lam`. -/
def iotaN (N : ℕ) : LamN N →ₐ[ℚ] Lam :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (MN N).subtype

lemma iotaN_single (N : ℕ) (m : MN N) (c : ℚ) :
    iotaN N (AddMonoidAlgebra.single m c) = AddMonoidAlgebra.single (m : ℕ →₀ ℤ) c := by
  simp [iotaN]

lemma iotaN_injective (N : ℕ) : Function.Injective (iotaN N) := by
  intro f g h
  apply AddMonoidAlgebra.coeff_injective
  have h' := congrArg AddMonoidAlgebra.coeff h
  simp only [iotaN, AddMonoidAlgebra.mapDomainAlgHom, AlgHom.coe_mk,
    AddMonoidAlgebra.mapDomainRingHom] at h'
  exact Finsupp.mapDomain_injective Subtype.val_injective h'

/-- The value of an admissible monomial: `∏_j e_j ^ m_j`. -/
def monoVal (N : ℕ) (m : ℕ →₀ ℤ) : KN N := m.prod fun j n => eK N j ^ n

lemma zpow_add_of_adm {N j : ℕ} {a b : ℤ} (ha : N < j → 0 ≤ a) (hb : N < j → 0 ≤ b) :
    eK N j ^ (a + b) = eK N j ^ a * eK N j ^ b := by
  by_cases hj : j ≤ N
  · exact zpow_add₀ (eK_ne_zero hj) a b
  · push Not at hj
    lift a to ℕ using ha hj
    lift b to ℕ using hb hj
    rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

lemma monoVal_add (N : ℕ) (m m' : MN N) :
    monoVal N ((m + m' : MN N) : ℕ →₀ ℤ) = monoVal N m * monoVal N m' := by
  classical
  simp only [monoVal, AddSubmonoid.coe_add]
  set S := (m : ℕ →₀ ℤ).support ∪ (m' : ℕ →₀ ℤ).support
  have h0 : ∀ j, eK N j ^ (0 : ℤ) = 1 := fun j => zpow_zero _
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_add) _ (fun j _ => h0 j),
    Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (fun j _ => h0 j),
    Finsupp.prod_of_support_subset _ Finset.subset_union_right _ (fun j _ => h0 j),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finsupp.add_apply]
  exact zpow_add_of_adm (m.2 j) (m'.2 j)

/-- `∏ E_j^{m_j} ↦ ∏ e_j^{m_j}` as a monoid homomorphism. -/
def valHom (N : ℕ) : Multiplicative (MN N) →* KN N where
  toFun m := monoVal N ((Multiplicative.toAdd m : MN N) : ℕ →₀ ℤ)
  map_one' := by simp [monoVal]
  map_mul' m m' := monoVal_add N (Multiplicative.toAdd m) (Multiplicative.toAdd m')

/-- The specialisation `E_j ↦ e_j(x_1, …, x_N)`. -/
def psiN (N : ℕ) : LamN N →ₐ[ℚ] KN N := AddMonoidAlgebra.lift ℚ (KN N) (MN N) (valHom N)

lemma psiN_single (N : ℕ) (m : MN N) (c : ℚ) :
    psiN N (AddMonoidAlgebra.single m c) = c • monoVal N m := by
  simp only [psiN, AddMonoidAlgebra.lift_single]
  rfl

/-! ## The formal generators in `LamN` -/

/-- `E j` in `LamN N`. -/
def EN (N j : ℕ) : LamN N :=
  AddMonoidAlgebra.single ⟨Finsupp.single j (if j = 0 then 0 else 1), fun i _ => by
    simp only [Finsupp.single_apply]; split_ifs <;> omega⟩ 1

/-- `E j⁻¹` in `LamN N`, for `j ≤ N`. -/
def EinvN (N j : ℕ) (hj : j ≤ N) : LamN N :=
  AddMonoidAlgebra.single ⟨Finsupp.single j (if j = 0 then 0 else -1), fun i hi => by
    simp only [Finsupp.single_apply]; split_ifs <;> omega⟩ 1

@[simp] lemma iotaN_EN (N j : ℕ) : iotaN N (EN N j) = E j := by
  rw [EN, iotaN_single]; rfl

@[simp] lemma iotaN_EinvN (N j : ℕ) (hj : j ≤ N) : iotaN N (EinvN N j hj) = Einv j := by
  rw [EinvN, iotaN_single]; rfl

@[simp] lemma psiN_EN (N j : ℕ) : psiN N (EN N j) = eK N j := by
  rw [EN, psiN_single, one_smul, monoVal]
  split_ifs with h
  · subst h; simp
  · rw [Finsupp.prod_single_index (by simp)]; simp

@[simp] lemma psiN_EinvN (N j : ℕ) (hj : j ≤ N) : psiN N (EinvN N j hj) = (eK N j)⁻¹ := by
  rw [EinvN, psiN_single, one_smul, monoVal]
  split_ifs with h
  · subst h; simp
  · rw [Finsupp.prod_single_index (by simp)]; simp

end ProperCircularArc
