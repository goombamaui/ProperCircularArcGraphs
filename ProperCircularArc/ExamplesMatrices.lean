import ProperCircularArc.Gluing

/-! # The `3 × 3` tableau matrices of Example `p3` -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProperCircularArc.Examples

open Finset Matrix

local instance (N : ℕ) : CharZero (KN N) := Algebra.charZero_of_charZero ℚ (KN N)

/-- Identify a one-entry injective tuple with its single entry. -/
def oneIndex (N : ℕ) : Fin N ≃ Inj N 1 where
  toFun c := ⟨fun _ => c, fun _ _ _ => Subsingleton.elim _ _⟩
  invFun i := i 0
  left_inv _ := rfl
  right_inv i := by ext r; fin_cases r; rfl

/-- A level-one matrix with its rows and columns indexed by `Fin N`. -/
def oneMatrix {N : ℕ} (A : Matrix (Inj N 1) (Inj N 1) (KN N)) :
    Matrix (Fin N) (Fin N) (KN N) := fun o i => A (oneIndex N o) (oneIndex N i)

lemma oneMatrix_mul {N : ℕ} (A B : Matrix (Inj N 1) (Inj N 1) (KN N)) :
    oneMatrix (A * B) = oneMatrix A * oneMatrix B := by
  ext o i
  unfold oneMatrix
  simp only [mul_apply]
  exact Fintype.sum_equiv (oneIndex N).symm _ _ (by intro j; simp)

lemma DM_entry {N : ℕ} (o i : Fin N) :
    oneMatrix (DT N 1 * MT N 1) o i =
      if i ≠ o then Erat N i * (Acoef ((o : ℕ) + 1) {((i : ℕ) + 1)} : KN N) else 0 := by
  classical
  unfold oneMatrix
  rw [mul_apply]
  simp only [DT, ite_mul, zero_mul]
  rw [Word.sum_embTail]
  have hi : ∀ c : {c : Fin N // c ∉ Set.range (oneIndex N o)},
      embInit (embCons c.1 (oneIndex N o) c.2) = oneIndex N i ↔ c.1 = i := by
    intro c
    constructor
    · intro h; exact congrArg (fun j : Inj N 1 => j 0) h
    · intro h; ext r; fin_cases r; exact congrArg Fin.val h
  have he : entries (shift (oneIndex N i)) = {((i : ℕ) + 1)} := by
    ext x
    change x ∈ entries (fun _ : Fin 1 => (i : ℕ) + 1) ↔ x ∈ {((i : ℕ) + 1)}
    simp [entries]
  have h0 : ∀ c : {c : Fin N // c ∉ Set.range (oneIndex N o)},
      embCons c.1 (oneIndex N o) c.2 0 = c.1 := fun _ => rfl
  have h1 : ∀ c : {c : Fin N // c ∉ Set.range (oneIndex N o)},
      embCons c.1 (oneIndex N o) c.2 (Fin.last 1) = o := fun _ => rfl
  simp only [MT, hi, h0, h1, he]
  change (∑ c : {c : Fin N // c ∉ Set.range (oneIndex N o)},
    Erat N c.1 * (if c.1 = i then (Acoef ((o : ℕ) + 1) {((i : ℕ) + 1)} : KN N) else 0)) = _
  by_cases hio : i ≠ o
  · have hc : i ∉ Set.range (oneIndex N o) := by simpa [oneIndex] using hio
    rw [ite_eq_left hio, Finset.sum_eq_single ⟨i, hc⟩]
    · simp
    · intro c _ hci
      rw [ite_eq_right (by intro he; exact hci (Subtype.ext he)), mul_zero]
    · simp
  · have hio' : i = o := not_ne_iff.mp hio
    rw [ite_eq_right hio]
    apply sum_eq_zero
    intro c _
    rw [ite_eq_right, mul_zero]
    intro h
    exact c.2 ⟨0, hio' ▸ h.symm⟩

/-- The displayed `D₂ M₁` matrix, with columns `1,2,3` represented by `0,1,2`. -/
theorem path_step_matrix : oneMatrix (DT 3 1 * MT 3 1) =
    !![0, eK 3 2 / (2 * eK 3 1), 2 * eK 3 3 / (3 * eK 3 2);
       2 * eK 3 1, 0, 0;
       0, 3 * eK 3 2 / (2 * eK 3 1), 0] := by
  ext o i
  rw [DM_entry]
  fin_cases o <;> fin_cases i <;>
    norm_num [Acoef, cfac, Tset, Erat, eK_zero, Finset.prod_insert] <;> ring

/-- The displayed square `(D₂ M₁)²`. -/
theorem path_square_matrix : oneMatrix ((DT 3 1 * MT 3 1) * (DT 3 1 * MT 3 1)) =
    !![eK 3 2, eK 3 3 / eK 3 1, 0;
       0, eK 3 2, 4 * eK 3 1 * eK 3 3 / (3 * eK 3 2);
       3 * eK 3 2, 0, 0] := by
  rw [oneMatrix_mul, path_step_matrix]
  ext o i
  fin_cases o <;> fin_cases i <;>
    simp [mul_apply, Fin.sum_univ_succ] <;>
    field_simp [eK_ne_zero (N := 3) (j := 1) (by omega),
      eK_ne_zero (N := 3) (j := 2) (by omega)] <;> ring

open MvPolynomial in
/-- The first three symbolic columns of `U₁`, over the admissible coefficient ring. -/
def smallU (i : Fin 3) : MvPolynomial (Fin 1) (LamN 3) :=
  if i = 0 then 1 else if i = 1 then
    C ((algebraMap ℚ (LamN 3)) (1 / 2) * EinvN 3 1 (by omega)) * (C (EN 3 1) - X 0)
  else
    C ((algebraMap ℚ (LamN 3)) (1 / 3) * EinvN 3 2 (by omega)) *
      (C (EN 3 2) - C (EN 3 1) * X 0 + X 0 ^ 2)

open MvPolynomial in
lemma smallU_map (i : Fin 3) :
    MvPolynomial.map (iotaN 3).toRingHom (smallU i) = U1fn ((i : ℕ) + 1) := by
  fin_cases i <;>
    norm_num [smallU, U1fn, Finset.sum_range_succ, smul_eq_C_mul', qc,
      iotaN_EN, iotaN_EinvN, iotaN_single, ← AddMonoidAlgebra.one_def] <;> ring

open MvPolynomial in
/-- An entry formula for the displayed `U₁` matrix. -/
theorem path_U_entry (o i : Fin 3) : oneMatrix (UN 3 1) o i =
    if i = 0 then xK 3 o else if i = 1 then
      xK 3 o * (eK 3 1 - xK 3 o) / (2 * eK 3 1)
    else xK 3 o * (eK 3 2 - eK 3 1 * xK 3 o + xK 3 o ^ 2) / (3 * eK 3 2) := by
  change specV 3 1 (U1fn ((i : ℕ) + 1)) (oneIndex 3 o) = _
  rw [← smallU_map, specV_map]
  fin_cases i <;>
    norm_num [smallU, Fin.prod_univ_succ, monoX, MvPolynomial.eval_map,
      psiN_EN, psiN_EinvN, psiN_single, monoVal, oneIndex, Algebra.smul_def, AlgHom.commutes] <;> ring

lemma elementary_three :
    eK 3 1 = xK 3 0 + xK 3 1 + xK 3 2 ∧
    eK 3 2 = xK 3 0 * xK 3 1 + xK 3 0 * xK 3 2 + xK 3 1 * xK 3 2 ∧
    eK 3 3 = xK 3 0 * xK 3 1 * xK 3 2 := by
  have h1 : powersetCard 1 (univ : Finset (Fin 3)) = {{0}, {1}, {2}} := by decide
  have h2 : powersetCard 2 (univ : Finset (Fin 3)) = {{0, 1}, {0, 2}, {1, 2}} := by decide
  have h3 : powersetCard 3 (univ : Finset (Fin 3)) = {{0, 1, 2}} := by decide
  have hn1 : ({0, 1} : Finset (Fin 3)) ∉ ({{0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide
  have hn2 : ({0, 2} : Finset (Fin 3)) ∉ ({{1, 2}} : Finset (Finset (Fin 3))) := by decide
  norm_num [eK, MvPolynomial.esymm, h1, h2, h3, xK, hn1, hn2, Finset.sum_insert]
  all_goals repeat' constructor
  all_goals ring

/-- The exact change-of-basis matrix printed in Example `p3`. -/
theorem path_U_matrix : oneMatrix (UN 3 1) =
    !![xK 3 0, xK 3 0 * (xK 3 1 + xK 3 2) / (2 * eK 3 1), eK 3 3 / (3 * eK 3 2);
       xK 3 1, xK 3 1 * (xK 3 0 + xK 3 2) / (2 * eK 3 1), eK 3 3 / (3 * eK 3 2);
       xK 3 2, xK 3 2 * (xK 3 0 + xK 3 1) / (2 * eK 3 1), eK 3 3 / (3 * eK 3 2)] := by
  ext o i
  rw [path_U_entry]
  fin_cases o <;> fin_cases i <;>
    norm_num [elementary_three.1, elementary_three.2.1, elementary_three.2.2] <;> ring

end ProperCircularArc.Examples
