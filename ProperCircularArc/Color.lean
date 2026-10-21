import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Colour matrices in infinitely many colours, symbolically

A colour vector at level `n` with infinitely many colours is a formal sum
`∑_i F(x_{i_1}, …, x_{i_n}) b̂_i` over tuples of distinct colours, where `F` is divisible by
`x_{i_1} ⋯ x_{i_n}`.  We record it by the polynomial `G = F / (y_1 ⋯ y_n)` in `n` variables
`y_1, …, y_n` over a coefficient ring `R` (in the paper, `R = ℚ(e_1, e_2, …)`).  The
operators of the paper act as follows:

* `M̂_n` (attach a new vertex adjacent to all marked ones): `G ↦ G`, read in `n + 1`
  variables;
* `D̂_n` (forget the oldest marked vertex): sum over a fresh colour `c` not among the others,
  `y_1^m ↦ p_{m+1} - ∑_{r ≥ 2} y_r^{m+1}`, where `p_j` are the power sums;
* `R̂_n` (cyclic shift): `G ↦ y_n · G(y_n, y_1, …, y_{n-1})`;
* `Ŝ_s` (swap two marked vertices): swap the variables `y_s, y_{s+1}`.

Everything here is generic in the commutative ring `R` and the sequence `p` of power sums,
so that the same definitions describe the infinite-colour model and its finite
specialisations.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Symbolic colour vectors at level `n`. -/
abbrev CV (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin n) R

/-- `M̂_n : CV n → CV (n+1)`. -/
def Mh (n : ℕ) : CV R n →ₐ[R] CV R (n + 1) := rename Fin.castSucc

/-- The image of `y_1^m` under the fresh-colour sum. -/
def freshQ (p : ℕ → R) (n m : ℕ) : CV R n := C (p (m + 1)) - ∑ r : Fin n, X r ^ (m + 1)

/-- The fresh-colour sum on polynomials in the fresh variable. -/
def freshL (p : ℕ → R) (n : ℕ) : Polynomial (CV R n) →ₗ[R] CV R n :=
  Polynomial.lsum fun m => LinearMap.mulRight R (freshQ p n m)

/-- `D̂_n : CV (n+1) → CV n`: sum over the colour of the first marked vertex. -/
def Dh (p : ℕ → R) (n : ℕ) : CV R (n + 1) →ₗ[R] CV R n :=
  freshL p n ∘ₗ (finSuccEquiv R n).toLinearMap

/-- The relabelling `0 ↦ last`, `j + 1 ↦ j`. -/
def rot (n : ℕ) : Equiv.Perm (Fin (n + 1)) := (finRotate (n + 1)).symm

@[simp] lemma rot_zero (n : ℕ) : rot n 0 = Fin.last n := by
  rw [rot, Equiv.symm_apply_eq, finRotate_last]

@[simp] lemma rot_succ (n : ℕ) (j : Fin n) : rot n j.succ = j.castSucc := by
  rw [rot, Equiv.symm_apply_eq, finRotate_apply, Fin.coeSucc_eq_succ]

/-- `R̂_n : CV (n+1) → CV (n+1)`, `G ↦ y_last · G(y_last, y_1, …)`. -/
def Rh (n : ℕ) : CV R (n + 1) →ₗ[R] CV R (n + 1) :=
  LinearMap.mulLeft R (X (Fin.last n)) ∘ₗ (rename (rot n)).toLinearMap

/-- The transposition of the positions `s` and `s + 1` (0-based), or the identity if
`s + 1 ≥ n`. -/
def swapPerm (n s : ℕ) : Equiv.Perm (Fin n) :=
  if h : s + 1 < n then Equiv.swap ⟨s, by omega⟩ ⟨s + 1, h⟩ else 1

/-- `Ŝ_s` on colour vectors. -/
def Sh (n s : ℕ) : CV R n →ₐ[R] CV R n := rename (swapPerm n s)

/-! ## Basic formulas -/

lemma Dh_apply (p : ℕ → R) (n : ℕ) (G : CV R (n + 1)) :
    Dh p n G = (finSuccEquiv R n G).sum fun m c => c * freshQ p n m := by
  simp [Dh, freshL, Polynomial.lsum_apply]

lemma Rh_apply (n : ℕ) (G : CV R (n + 1)) :
    Rh n G = X (Fin.last n) * rename (rot n) G := rfl

lemma freshL_C_mul (p : ℕ → R) (n : ℕ) (f : CV R n) (F : Polynomial (CV R n)) :
    freshL p n (Polynomial.C f * F) = f * freshL p n F := by
  simp only [freshL, Polynomial.lsum_apply, LinearMap.mulRight_apply]
  rw [Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  have hsupp : (Polynomial.C f * F).support ⊆ F.support := by
    intro m hm
    rw [Polynomial.mem_support_iff, Polynomial.coeff_C_mul] at hm
    exact Polynomial.mem_support_iff.2 (right_ne_zero_of_mul hm)
  rw [Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.coeff_C_mul, mul_assoc]
  · intro m _ hm
    rw [Polynomial.notMem_support_iff.1 hm, zero_mul]

lemma freshL_map (p : ℕ → R) (n : ℕ) (π : Equiv.Perm (Fin n)) (F : Polynomial (CV R n)) :
    freshL p n (F.map (rename π).toRingHom) = rename π (freshL p n F) := by
  simp only [freshL, Polynomial.lsum_apply, LinearMap.mulRight_apply]
  rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
  have hsupp : (F.map (rename π).toRingHom).support ⊆ F.support := Polynomial.support_map_subset _ _
  rw [Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.coeff_map, map_mul]
    congr 1
    simp only [freshQ, map_sub, map_sum, map_pow, rename_X, rename_C]
    congr 1
    exact (Equiv.sum_comp π (fun r => (X r : CV R n) ^ (m + 1))).symm
  · intro m _ hm
    rw [Polynomial.notMem_support_iff.1 hm, zero_mul]

/-- Extending a relabelling `f` of the old variables by fixing the fresh variable `0`. -/
def liftFresh {n n' : ℕ} (f : Fin n → Fin n') : Fin (n + 1) → Fin (n' + 1) :=
  Fin.cases 0 (fun j => (f j).succ)

lemma finSuccEquiv_rename_liftFresh {n n' : ℕ} (f : Fin n → Fin n') (G : CV R (n + 1)) :
    finSuccEquiv R n' (rename (liftFresh f) G) = (finSuccEquiv R n G).map (rename f).toRingHom := by
  have : ((finSuccEquiv R n').toAlgHom.comp (rename (liftFresh f)) : CV R (n + 1) →ₐ[R] _) =
      (Polynomial.mapAlgHom (rename f)).comp (finSuccEquiv R n).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [liftFresh, finSuccEquiv_X_zero]
    · simp [liftFresh, finSuccEquiv_X_succ]
  exact congr($this G)

lemma liftFresh_castSucc (n : ℕ) : liftFresh (Fin.castSucc : Fin n → Fin (n + 1)) = Fin.castSucc := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [liftFresh, Fin.cases_succ]
    ext
    simp

/-- Naturality of `D̂` under permutations of the non-fresh colours. -/
lemma Dh_rename_liftFresh (p : ℕ → R) (n : ℕ) (π : Equiv.Perm (Fin n)) (G : CV R (n + 1)) :
    Dh p n (rename (liftFresh π) G) = rename π (Dh p n G) := by
  simp only [Dh, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
  rw [finSuccEquiv_rename_liftFresh, freshL_map]

/-- `D̂` is linear over polynomials in the non-fresh colours. -/
lemma Dh_mul_succ (p : ℕ → R) (n : ℕ) (f : CV R n) (G : CV R (n + 1)) :
    Dh p n (rename Fin.succ f * G) = f * Dh p n G := by
  simp only [Dh, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
  have : finSuccEquiv R n (rename Fin.succ f) = Polynomial.C f := by
    have h : ((finSuccEquiv R n).toAlgHom.comp (rename Fin.succ) : CV R n →ₐ[R] _) =
        (Polynomial.CAlgHom : CV R n →ₐ[R] Polynomial (CV R n)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [finSuccEquiv_X_succ]
    exact congr($h f)
  rw [this, freshL_C_mul]

lemma eval_finSuccEquiv (n : ℕ) (G : CV R (n + 1)) :
    (finSuccEquiv R n G).eval₂ (rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom
      (X (Fin.last n)) = rename (rot n) G := by
  have : ((Polynomial.eval₂AlgHom (rename (Fin.castSucc : Fin n → Fin (n + 1)))
      (X (Fin.last n)) (fun a => Commute.all _ _)).comp (finSuccEquiv R n).toAlgHom :
        CV R (n + 1) →ₐ[R] CV R (n + 1)) = rename (rot n) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]
  exact congr($this G)

/-- **The commutator** `M̂_n D̂_n - D̂_{n+1} M̂_{n+1} = R̂_n`. -/
lemma Mh_Dh_sub_Dh_Mh (p : ℕ → R) (n : ℕ) (G : CV R (n + 1)) :
    Mh n (Dh p n G) - Dh p (n + 1) (Mh (n + 1) G) = Rh n G := by
  have hM : (Mh (n + 1) G : CV R (n + 2)) = rename (liftFresh (Fin.castSucc : Fin n → Fin (n + 1))) G := by
    rw [liftFresh_castSucc]; rfl
  rw [hM]
  simp only [Dh, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
  rw [finSuccEquiv_rename_liftFresh, Rh_apply, ← eval_finSuccEquiv]
  set F := finSuccEquiv R n G
  simp only [freshL, Polynomial.lsum_apply, LinearMap.mulRight_apply, Mh]
  have h2 : (F.map (rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom).sum
      (fun m c => c * freshQ p (n + 1) m)
      = ∑ m ∈ F.support, rename Fin.castSucc (F.coeff m) * freshQ p (n + 1) m := by
    rw [Polynomial.sum_def, Finset.sum_subset (Polynomial.support_map_subset _ F)]
    · exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.coeff_map]; rfl
    · intro m _ hm
      rw [Polynomial.notMem_support_iff.1 hm, zero_mul]
  rw [h2, Polynomial.sum_def, map_sum, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [freshQ, map_mul, map_sub, map_sum, map_pow, rename_X, rename_C, Fin.sum_univ_castSucc,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

/-! ## The hatted identities of Proposition `identities` -/

lemma rename_congr_fun {n m : ℕ} {f g : Fin n → Fin m} (h : ∀ i, f i = g i) (G : CV R n) :
    rename f G = rename g G := by
  rw [funext h]

lemma swapPerm_of_lt {n s : ℕ} (h : s + 1 < n) :
    swapPerm n s = Equiv.swap (⟨s, by omega⟩ : Fin n) ⟨s + 1, h⟩ := by
  simp [swapPerm, h]

lemma swapPerm_apply_of_lt {n s : ℕ} (h : s + 1 < n) (i : Fin n) :
    swapPerm n s i = Equiv.swap (⟨s, by omega⟩ : Fin n) ⟨s + 1, h⟩ i := by
  rw [swapPerm_of_lt h]

lemma swapPerm_apply_of_ne {n s : ℕ} (i : Fin n) (h1 : (i : ℕ) ≠ s) (h2 : (i : ℕ) ≠ s + 1) :
    swapPerm n s i = i := by
  unfold swapPerm
  split_ifs with h
  · exact Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff, h1]) (by simp [Fin.ext_iff, h2])
  · rfl

@[simp] lemma swapPerm_swapPerm (n s : ℕ) (i : Fin n) : swapPerm n s (swapPerm n s i) = i := by
  unfold swapPerm; split_ifs <;> simp

lemma Sh_Sh (n s : ℕ) (G : CV R n) : Sh n s (Sh n s G) = G := by
  simp only [Sh, rename_rename]
  rw [rename_congr_fun (g := id) (fun i => by simp)]
  simp

lemma swapPerm_castSucc {n s : ℕ} (h : s + 1 < n) (i : Fin n) :
    swapPerm (n + 1) s i.castSucc = (swapPerm n s i).castSucc := by
  rw [swapPerm_apply_of_lt h, swapPerm_apply_of_lt (by omega)]
  ext
  simp only [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_castSucc]
  split_ifs <;> simp_all

/-- `Ŝ_s M̂ = M̂ Ŝ_s` for `s + 1 < n`. -/
lemma Sh_Mh {n s : ℕ} (h : s + 1 < n) (G : CV R n) :
    Sh (n + 1) s (Mh n G) = Mh n (Sh n s G) := by
  simp only [Sh, Mh, rename_rename]
  exact rename_congr_fun (fun i => swapPerm_castSucc h i) G

lemma swapPerm_succ {n s : ℕ} (h : s + 1 < n) (i : Fin n) :
    swapPerm (n + 1) (s + 1) i.succ = (swapPerm n s i).succ := by
  rw [swapPerm_apply_of_lt h, swapPerm_apply_of_lt (by omega)]
  ext
  simp only [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_succ]
  split_ifs <;> simp_all

lemma swapPerm_succ_zero (n s : ℕ) : swapPerm (n + 1) (s + 1) 0 = 0 :=
  swapPerm_apply_of_ne _ (by simp) (by simp)

lemma swapPerm_succ_eq_liftFresh {n s : ℕ} (h : s + 1 < n) :
    (swapPerm (n + 1) (s + 1) : Fin (n + 1) → Fin (n + 1)) = liftFresh (swapPerm n s) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftFresh, swapPerm_succ_zero]
  · simp [liftFresh, swapPerm_succ h]

/-- `Ŝ_s D̂ = D̂ Ŝ_{s+1}`. -/
lemma Sh_Dh (p : ℕ → R) {n s : ℕ} (h : s + 1 < n) (G : CV R (n + 1)) :
    Sh n s (Dh p n G) = Dh p n (Sh (n + 1) (s + 1) G) := by
  simp only [Sh]
  rw [swapPerm_succ_eq_liftFresh h, Dh_rename_liftFresh]

lemma swapPerm_rot {n s : ℕ} (h : s + 1 < n) (i : Fin (n + 1)) :
    swapPerm (n + 1) s (rot n i) = rot n (swapPerm (n + 1) (s + 1) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [swapPerm_succ_zero, rot_zero]
    exact swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)
  · rw [rot_succ, swapPerm_succ h, rot_succ, swapPerm_castSucc h]

/-- `Ŝ_s R̂ = R̂ Ŝ_{s+1}` for `s + 1 < n` (level `n + 1`). -/
lemma Sh_Rh {n s : ℕ} (h : s + 1 < n) (G : CV R (n + 1)) :
    Sh (n + 1) s (Rh n G) = Rh n (Sh (n + 1) (s + 1) G) := by
  simp only [Rh_apply, Sh, map_mul, rename_X, rename_rename]
  rw [swapPerm_apply_of_ne (Fin.last n) (by simp; omega) (by simp; omega)]
  congr 1
  exact rename_congr_fun (fun i => swapPerm_rot h i) G

lemma swapPerm_zero_two (n : ℕ) : swapPerm (n + 2) 0 = Equiv.swap (0 : Fin (n + 2)) 1 := by
  rw [swapPerm_of_lt (by omega)]; rfl

lemma rot_succ_eq (n : ℕ) (i : Fin (n + 2)) :
    rot (n + 1) i = liftFresh (rot n) (swapPerm (n + 2) 0 i) := by
  rw [swapPerm_zero_two]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [rot_zero, Equiv.swap_apply_left]
    show Fin.last (n + 1) = Fin.cases 0 (fun j => (rot n j).succ) (Fin.succ (0 : Fin (n + 1)))
    rw [Fin.cases_succ, rot_zero, Fin.succ_last]
  · refine Fin.cases ?_ (fun k => ?_) j
    · rw [rot_succ, show (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) from rfl,
        Equiv.swap_apply_right]
      rfl
    · rw [rot_succ, Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff])]
      simp [liftFresh, rot_succ]

/-- **Swap-delete (hatted)**: `D̂_k R̂_k = R̂_{k-1} D̂_k Ŝ_1`. -/
lemma Dh_Rh (p : ℕ → R) (n : ℕ) (G : CV R (n + 2)) :
    Dh p (n + 1) (Rh (n + 1) G) = Rh n (Dh p (n + 1) (Sh (n + 2) 0 G)) := by
  rw [Rh_apply, Rh_apply]
  have hX : (X (Fin.last (n + 1)) : CV R (n + 2)) = rename Fin.succ (X (Fin.last n)) := by
    rw [rename_X, Fin.succ_last]
  rw [hX, Dh_mul_succ]
  congr 1
  have : rename (rot (n + 1)) G = rename (liftFresh (rot n)) (Sh (n + 2) 0 G) := by
    rw [Sh, rename_rename]
    exact rename_congr_fun (fun i => rot_succ_eq n i) G
  rw [this, Dh_rename_liftFresh]

lemma swapPerm_last_castSucc (n : ℕ) :
    swapPerm (n + 2) n (Fin.last n).castSucc = Fin.last (n + 1) := by
  rw [swapPerm_of_lt (by omega)]
  exact Equiv.swap_apply_left _ _

lemma swap_castSucc_rot (n : ℕ) (i : Fin (n + 1)) :
    swapPerm (n + 2) n (rot n i).castSucc = rot (n + 1) i.castSucc := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [rot_zero, swapPerm_last_castSucc, Fin.castSucc_zero, rot_zero]
  · rw [rot_succ, ← Fin.succ_castSucc, rot_succ]
    exact swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)

/-- `Ŝ_{k-1} M̂_{k-1} R̂_{k-1} = R̂_k M̂_{k-1}`. -/
lemma Sh_Mh_Rh (n : ℕ) (G : CV R (n + 1)) :
    Sh (n + 2) n (Mh (n + 1) (Rh n G)) = Rh (n + 1) (Mh (n + 1) G) := by
  rw [Rh_apply, Rh_apply, Sh, Mh, map_mul, map_mul, rename_X, rename_X, rename_rename,
    rename_rename, rename_rename, swapPerm_last_castSucc]
  rw [rename_congr_fun (f := (⇑(swapPerm (n + 2) n) ∘ Fin.castSucc) ∘ ⇑(rot n))
    (g := ⇑(rot (n + 1)) ∘ Fin.castSucc) (fun i => swap_castSucc_rot n i) G]

/-- `Ŝ_{k-1} M̂_{k-1} M̂_{k-2} = M̂_{k-1} M̂_{k-2}`. -/
lemma Sh_Mh_Mh (n : ℕ) (G : CV R n) :
    Sh (n + 2) n (Mh (n + 1) (Mh n G)) = Mh (n + 1) (Mh n G) := by
  simp only [Sh, Mh, rename_rename]
  refine rename_congr_fun (fun i => ?_) G
  exact swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)

lemma swap_rot_rot (n : ℕ) (i : Fin (n + 2)) :
    swapPerm (n + 2) n (rot (n + 1) (rot (n + 1) i)) =
      rot (n + 1) (rot (n + 1) (swapPerm (n + 2) 0 i)) := by
  have h2 : rot (n + 1) (Fin.last (n + 1)) = (Fin.last n).castSucc := by
    rw [← Fin.succ_last, rot_succ]
  rw [swapPerm_zero_two]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [rot_zero, h2, swapPerm_last_castSucc, Equiv.swap_apply_left,
      show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, rot_succ, Fin.castSucc_zero, rot_zero]
  · refine Fin.cases ?_ (fun k => ?_) j
    · rw [rot_succ, Fin.castSucc_zero, rot_zero,
        show (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) from rfl, Equiv.swap_apply_right,
        rot_zero, h2, swapPerm_of_lt (by omega)]
      exact Equiv.swap_apply_right _ _
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]),
        rot_succ, ← Fin.succ_castSucc, rot_succ]
      exact swapPerm_apply_of_ne _ (by simp; omega) (by simp; omega)

/-- `Ŝ_{k-1} R̂_k² = R̂_k² Ŝ_1` at level `k = n + 2`. -/
lemma Sh_Rh_Rh (n : ℕ) (G : CV R (n + 2)) :
    Sh (n + 2) n (Rh (n + 1) (Rh (n + 1) G)) = Rh (n + 1) (Rh (n + 1) (Sh (n + 2) 0 G)) := by
  simp only [Rh_apply, Sh, map_mul, rename_X, rename_rename]
  have h1 : swapPerm (n + 2) n (Fin.last (n + 1)) = (Fin.last n).castSucc := by
    rw [swapPerm_of_lt (by omega)]
    exact Equiv.swap_apply_right _ _
  have h2 : rot (n + 1) (Fin.last (n + 1)) = (Fin.last n).castSucc := by
    rw [← Fin.succ_last, rot_succ]
  rw [h1, h2, swapPerm_last_castSucc]
  rw [← mul_assoc, ← mul_assoc, mul_comm (X (Fin.last (n + 1))) (X (Fin.last n).castSucc)]
  rw [rename_congr_fun (f := ⇑(swapPerm (n + 2) n) ∘ ⇑(rot (n + 1)) ∘ ⇑(rot (n + 1)))
    (g := ⇑(rot (n + 1)) ∘ ⇑(rot (n + 1)) ∘ ⇑(swapPerm (n + 2) 0)) (fun i => swap_rot_rot n i) G]

end ProperCircularArc
