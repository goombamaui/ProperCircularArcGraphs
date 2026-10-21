import ProperCircularArc.Admissible
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fintype

/-!
# Colour matrices with `N` colours

With `N` colours the colour vectors at level `k` are functions on tuples of `k` distinct colours,
i.e. on embeddings `Fin k ↪ Fin N`.  We define the matrices of `M̂_k` and `D̂_k`, and the
specialisation `specV` of a symbolic colour vector, and show that the specialisation intertwines
the symbolic operators with these matrices.
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

/-- Tuples of `k` distinct colours among `N`. -/
abbrev Inj (N k : ℕ) := Fin k ↪ Fin N

/-- Forget the last colour. -/
def embInit {N k : ℕ} (j : Inj N (k + 1)) : Inj N k :=
  ⟨fun r => j r.castSucc, fun _ _ h => Fin.castSucc_injective _ (j.injective h)⟩

/-- Forget the first colour. -/
def embTail {N k : ℕ} (j : Inj N (k + 1)) : Inj N k :=
  ⟨fun r => j r.succ, fun _ _ h => Fin.succ_injective _ (j.injective h)⟩

/-- Prepend a new colour. -/
def embCons {N k : ℕ} (c : Fin N) (i : Inj N k) (h : c ∉ Set.range i) : Inj N (k + 1) :=
  ⟨Fin.cons c i, Fin.cons_injective_iff.2 ⟨h, i.injective⟩⟩

/-- Append a new colour. -/
def embSnoc {N k : ℕ} (i : Inj N k) (c : Fin N) (h : c ∉ Set.range i) : Inj N (k + 1) :=
  ⟨Fin.snoc (α := fun _ => Fin N) i c, Fin.snoc_injective_iff.2 ⟨i.injective, h⟩⟩

@[simp] lemma embTail_embCons {N k : ℕ} (c : Fin N) (i : Inj N k) (h) :
    embTail (embCons c i h) = i := by
  ext r; rfl

@[simp] lemma embInit_embSnoc {N k : ℕ} (i : Inj N k) (c : Fin N) (h) :
    embInit (embSnoc i c h) = i := by
  ext r
  show (Fin.snoc (α := fun _ => Fin N) i c r.castSucc : ℕ) = i r
  simp

/-- The matrix of `M̂_k` with `N` colours. -/
def Mmat (N k : ℕ) : Matrix (Inj N (k + 1)) (Inj N k) (KN N) :=
  fun j i => if embInit j = i then xK N (j (Fin.last k)) else 0

/-- The matrix of `D̂_{k+1}` with `N` colours. -/
def Dmat (N k : ℕ) : Matrix (Inj N k) (Inj N (k + 1)) (KN N) :=
  fun i j => if embTail j = i then 1 else 0

lemma Mmat_mulVec {N k : ℕ} (F : Inj N k → KN N) (j : Inj N (k + 1)) :
    (Mmat N k *ᵥ F) j = xK N (j (Fin.last k)) * F (embInit j) := by
  simp [Mmat, mulVec, dotProduct, ite_mul]

/-- `D̂` sums over a fresh colour. -/
lemma Dmat_mulVec {N k : ℕ} (F : Inj N (k + 1) → KN N) (i : Inj N k) :
    (Dmat N k *ᵥ F) i = ∑ c : {c : Fin N // c ∉ Set.range i}, F (embCons c.1 i c.2) := by
  simp only [Dmat, mulVec, dotProduct, ite_mul, one_mul, zero_mul]
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

/-! ## Specialising colour vectors -/

/-- The monomial `∏ x_{i_r}^{d_r}`. -/
def monoX {N k : ℕ} (i : Inj N k) (d : Fin k →₀ ℕ) : KN N := ∏ r, xK N (i r) ^ d r

/-- The specialisation of a symbolic colour vector to `N` colours:
`G ↦ (i ↦ x_{i_1} ⋯ x_{i_k} G(x_{i_1}, …, x_{i_k}))`. -/
def specV (N k : ℕ) (G : CV Lam k) (i : Inj N k) : KN N :=
  (∏ r, xK N (i r)) * ∑ d ∈ G.support, specCoeff N (G.coeff d) * monoX i d

lemma specV_eq_sum {N k : ℕ} (G : CV Lam k) {S : Finset (Fin k →₀ ℕ)} (hS : G.support ⊆ S)
    (i : Inj N k) :
    specV N k G i = (∏ r, xK N (i r)) * ∑ d ∈ S, specCoeff N (G.coeff d) * monoX i d := by
  rw [specV]
  congr 1
  refine sum_subset hS fun d _ hd => ?_
  rw [notMem_support_iff.1 hd, map_zero, zero_mul]

lemma specV_add {N k : ℕ} (G H : CV Lam k) : specV N k (G + H) = specV N k G + specV N k H := by
  classical
  funext i
  rw [Pi.add_apply, specV_eq_sum G (S := G.support ∪ H.support) subset_union_left,
    specV_eq_sum H (S := G.support ∪ H.support) subset_union_right,
    specV_eq_sum (G + H) (S := G.support ∪ H.support) support_add, ← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

lemma specV_zero {N k : ℕ} : specV N k 0 = 0 := by
  funext i; simp [specV]

lemma specV_qsmul {N k : ℕ} (q : ℚ) (G : CV Lam k) : specV N k (q • G) = q • specV N k G := by
  funext i
  rw [Pi.smul_apply, specV_eq_sum (q • G) (S := G.support) support_smul, specV]
  have hq : q • G = C (qc q) * G := by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]; rfl
  rw [hq]
  simp only [coeff_C_mul]
  have h : ∀ d, specCoeff N (qc q * G.coeff d) = algebraMap ℚ (KN N) q * specCoeff N (G.coeff d) :=
    fun d => by
      rw [show qc q * G.coeff d = q • G.coeff d from (Algebra.smul_def q _).symm, map_smul,
        Algebra.smul_def]
  simp_rw [h, Algebra.smul_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

lemma specV_sub {N k : ℕ} (G H : CV Lam k) : specV N k (G - H) = specV N k G - specV N k H := by
  have := specV_add (N := N) (G - H) H
  rw [sub_add_cancel] at this
  rw [this]; ring

lemma specV_sum {N k : ℕ} {ι : Type*} (s : Finset ι) (G : ι → CV Lam k) :
    specV N k (∑ a ∈ s, G a) = ∑ a ∈ s, specV N k (G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [specV_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, specV_add, ih]

lemma specV_map {N k : ℕ} (G' : MvPolynomial (Fin k) (LamN N)) (i : Inj N k) :
    specV N k (map (iotaN N).toRingHom G') i =
      (∏ r, xK N (i r)) * eval (fun r => xK N (i r)) (map (psiN N).toRingHom G') := by
  rw [specV, support_map_of_injective _ (iotaN_injective N), eval_eq']
  congr 1
  rw [sum_subset (support_map_subset _ G')]
  · refine sum_congr rfl fun d _ => ?_
    rw [coeff_map, coeff_map]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, specCoeff_iotaN, monoX]
  · intro d _ hd
    rw [notMem_support_iff.1 hd, zero_mul]

lemma specV_Mh {N k : ℕ} {G : CV Lam k} (hG : G ∈ AdmV N k) :
    specV N (k + 1) (Mh k G) = Mmat N k *ᵥ specV N k G := by
  obtain ⟨G', rfl⟩ := mem_AdmV.1 hG
  funext j
  rw [Mmat_mulVec, Mh, ← map_rename, specV_map, specV_map, map_rename, eval_rename,
    Fin.prod_univ_castSucc]
  have e1 : (fun r => xK N ((embInit j) r)) = (fun r => xK N (j r)) ∘ Fin.castSucc := rfl
  have e2 : ∏ r, xK N ((embInit j) r) = ∏ i : Fin k, xK N (j i.castSucc) := rfl
  rw [e1]
  simp only [Function.comp_def]
  ring

/-- The core computation of `D̂`: summing over a fresh colour. -/
lemma eval_Dh_fresh {N k : ℕ} (H : MvPolynomial (Fin (k + 1)) (KN N)) (i : Inj N k) :
    eval (fun r => xK N (i r)) (Dh (fun m => ∑ c, xK N c ^ m) k H) =
      ∑ c : {c : Fin N // c ∉ Set.range i},
        xK N c.1 * eval (Fin.cons (xK N c.1) (fun r => xK N (i r))) H := by
  classical
  rw [Dh_apply, Polynomial.sum_def, map_sum]
  have hfresh : ∀ m, eval (fun r => xK N (i r)) (freshQ (fun m => ∑ c, xK N c ^ m) k m) =
      ∑ c : {c : Fin N // c ∉ Set.range i}, xK N c.1 ^ (m + 1) := by
    intro m
    simp only [freshQ, map_sub, eval_C, map_sum, map_pow, eval_X]
    rw [← Finset.sum_compl_add_sum (univ.map i), Finset.sum_map, add_sub_cancel_right]
    refine Finset.sum_subtype _ (fun c => ?_) _
    simp [Set.mem_range]
  simp_rw [map_mul, hfresh, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [pow_succ]; ring

lemma Dh_congr {R : Type*} [CommRing R] {p p' : ℕ → R} (h : ∀ m, p (m + 1) = p' (m + 1)) {n : ℕ}
    (G : CV R (n + 1)) : Dh p n G = Dh p' n G := by
  rw [Dh_apply, Dh_apply]
  congr 1
  funext m c
  simp [freshQ, h m]

lemma psiN_PwN_succ (N m : ℕ) : psiN N (PwN N (m + 1)) = ∑ c, xK N c ^ (m + 1) := by
  rw [psiN_PwN N (m + 1) (by omega), psum, map_sum]
  simp [xK]

lemma xK_comp_cons {N k : ℕ} (c : Fin N) (i : Inj N k) (h : c ∉ Set.range i) :
    (fun r => xK N ((embCons c i h) r)) = Fin.cons (xK N c) (fun r => xK N (i r)) := by
  funext r
  refine Fin.cases ?_ (fun r' => ?_) r <;> rfl

/-- `D̂` on specialised colour vectors is the sum over a fresh colour. -/
lemma specV_Dh {N k : ℕ} {G : CV Lam (k + 1)} (hG : G ∈ AdmV N (k + 1)) :
    specV N k (Dh Pw k G) = Dmat N k *ᵥ specV N (k + 1) G := by
  obtain ⟨G', rfl⟩ := mem_AdmV.1 hG
  funext i
  rw [Dmat_mulVec]
  have hPw : ((iotaN N).toRingHom ∘ PwN N) = Pw := funext (iotaN_PwN N)
  rw [← hPw, ← Dh_map, specV_map, Dh_map,
    Dh_congr (p' := fun m => ∑ c, xK N c ^ m) (fun m => psiN_PwN_succ N m), eval_Dh_fresh,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [specV_map, xK_comp_cons, Fin.prod_univ_succ]
  show _ = (xK N c * ∏ r : Fin k, xK N (i r)) * _
  ring

/-- Specialisation is multiplicative for admissible scalars. -/
lemma specV_smul {N k : ℕ} {c : Lam} {G : CV Lam k} (hc : c ∈ AdmC N) (hG : G ∈ AdmV N k) :
    specV N k (c • G) = specCoeff N c • specV N k G := by
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨G', rfl⟩ := mem_AdmV.1 hG
  funext i
  have : (iotaN N).toRingHom c' • map (iotaN N).toRingHom G' =
      map (iotaN N).toRingHom (C c' * G') := by
    rw [smul_eq_C_mul', map_mul, map_C]
  rw [this, specV_map, show (iotaN N).toRingHom c' = iotaN N c' from rfl, Pi.smul_apply, specV_map, map_mul, map_C, eval_mul, eval_C,
    specCoeff_iotaN, smul_eq_mul]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end ProperCircularArc
