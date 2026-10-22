import ProperCircularArc.Tableaux
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Passing to infinitely many variables

A symmetric function is represented by all of its finite-alphabet specializations.
We prove that a single polynomial in formal elementary generators gives the chromatic
symmetric function in every alphabet, and that its coefficients are nonnegative.
Thus the coefficients are independent of the chosen finite alphabet.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProperCircularArc

open MvPolynomial Finset

/-- Set colours `N, …, M-1` to zero. -/
def restrictVars (N M : ℕ) : Pol M →ₐ[ℚ] Pol N :=
  aeval fun i => if h : (i : ℕ) < N then X ⟨i, h⟩ else 0

@[simp] lemma restrictVars_X {N M : ℕ} (i : Fin M) :
    restrictVars N M (X i) = if h : (i : ℕ) < N then X ⟨i, h⟩ else 0 := aeval_X _ _

lemma restrictVars_esymm {N M : ℕ} (h : N ≤ M) (k : ℕ) :
    restrictVars N M (esymm (Fin M) ℚ k) = esymm (Fin N) ℚ k := by
  classical
  let e : Fin N ↪ Fin M := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  let s : Finset (Fin M) := univ.map e
  have hs : ∀ i : Fin M, i ∈ s ↔ (i : ℕ) < N := by
    intro i
    simp only [s, mem_map, mem_univ, true_and]
    exact ⟨by rintro ⟨j, rfl⟩; exact j.2,
      fun hi => ⟨⟨i, hi⟩, Fin.ext rfl⟩⟩
  unfold esymm
  rw [map_sum]
  trans ∑ t ∈ s.powersetCard k, restrictVars N M (∏ i ∈ t, X i)
  · symm
    apply sum_subset (fun _ ht => powersetCard_mono (subset_univ _) ht) ?_
    intro t ht hts
    have hnot : ¬t ⊆ s := by
      intro hsub
      exact hts (mem_powersetCard.mpr ⟨hsub, (mem_powersetCard.mp ht).2⟩)
    obtain ⟨i, hit, his⟩ := Set.not_subset.mp hnot
    rw [map_prod]
    apply prod_eq_zero hit
    rw [restrictVars_X, dite_eq_right (fun hx => his ((hs i).mpr hx))]
  · dsimp only [s]
    rw [powersetCard_map, sum_map]
    apply sum_congr rfl
    intro t _
    change restrictVars N M (∏ i ∈ t.map e, X i) = _
    rw [map_prod, prod_map]
    apply prod_congr rfl
    intro i _
    rw [restrictVars_X, dite_eq_left (show (e i : ℕ) < N from i.2)]
    rfl

lemma restrictVars_chromSym {V : Type*} [Fintype V] [DecidableEq V]
    {N M : ℕ} (h : N ≤ M) (G : SimpleGraph V) :
    restrictVars N M (chromSym M G) = chromSym N G := by
  classical
  let e : (V → Fin N) ↪ (V → Fin M) :=
    ⟨fun c v => Fin.castLE h (c v), fun c d he => funext fun v => Fin.ext (congrArg (fun f => (f v : ℕ)) he)⟩
  unfold chromSym
  rw [map_sum]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro c hc
    have hbad : ∃ v, ¬(c v : ℕ) < N := by
      by_contra! hall
      exact hc ⟨fun v => ⟨c v, hall v⟩, rfl⟩
    obtain ⟨v, hv⟩ := hbad
    split_ifs
    · rw [map_prod]
      exact prod_eq_zero (mem_univ v) (by rw [restrictVars_X, dite_eq_right hv])
    · simp
  · intro c
    have hp : IsProper G (e c) ↔ IsProper G c := by
      apply forall₂_congr
      intro u v
      exact imp_congr_right fun _ => (Fin.castLE_injective h).ne_iff
    rw [hp]
    split_ifs
    · rw [map_prod]
      exact prod_congr rfl fun v _ => by
        change X (c v) = restrictVars N M (X (Fin.castLE h (c v)))
        rw [restrictVars_X, dite_eq_left (show (Fin.castLE h (c v) : ℕ) < N from (c v).2)]
        rfl
    · simp

/-- `X_G` is homogeneous of degree `|V(G)|`. -/
lemma chromSym_homogeneous {V : Type*} [Fintype V] [DecidableEq V]
    (N : ℕ) (G : SimpleGraph V) : (chromSym N G).IsHomogeneous (Fintype.card V) := by
  classical
  unfold chromSym
  apply IsHomogeneous.sum
  intro c _
  split_ifs
  · simpa using IsHomogeneous.prod (univ : Finset V) (fun v => (X (c v) : Pol N))
      (fun _ => 1) (fun v _ => isHomogeneous_X ℚ (c v))
  · exact isHomogeneous_zero (n := Fintype.card V) (σ := Fin N) ℚ

lemma esymm_homogeneous (N k : ℕ) : (esymm (Fin N) ℚ k).IsHomogeneous k := by
  classical
  unfold esymm
  apply IsHomogeneous.sum
  intro t ht
  convert IsHomogeneous.prod t (fun i => (X i : Pol N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℚ i) using 1
  simp [(mem_powersetCard.mp ht).2]

/-- Evaluation in elementary symmetric functions preserves weighted degree. -/
lemma elementary_monomial_homogeneous {N M : ℕ} (d : Fin N →₀ ℕ) (q : ℚ) :
    (aeval (fun j : Fin N => esymm (Fin M) ℚ ((j : ℕ) + 1)) (monomial d q)).IsHomogeneous
      (Finsupp.weight (fun j : Fin N => (j : ℕ) + 1) d) := by
  rw [aeval_monomial]
  apply IsHomogeneous.C_mul
  unfold Finsupp.prod
  convert IsHomogeneous.prod d.support (fun j => esymm (Fin M) ℚ ((j : ℕ) + 1) ^ d j)
    (fun j => ((j : ℕ) + 1) * d j) (fun j _ => (esymm_homogeneous M _).pow _) using 1
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_comm]

lemma elementary_homogeneousComponent {N M n : ℕ} (P : Pol N) :
    aeval (fun j : Fin N => esymm (Fin M) ℚ ((j : ℕ) + 1))
        (weightedHomogeneousComponent (fun j : Fin N => (j : ℕ) + 1) n P) =
      homogeneousComponent n (aeval (fun j : Fin N => esymm (Fin M) ℚ ((j : ℕ) + 1)) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial d q =>
    have hw := isWeightedHomogeneous_monomial (fun j : Fin N => (j : ℕ) + 1) d q rfl
    have hh := elementary_monomial_homogeneous (M := M) d q
    rw [weightedHomogeneousComponent_of_mem hw, homogeneousComponent_of_mem hh]
    split_ifs <;> simp

/-- The elementary expansion of a homogeneous symmetric polynomial is weighted homogeneous. -/
lemma elementary_homogeneous {N n : ℕ} {P : Pol N} {f : Pol N}
    (hf : f.IsHomogeneous n)
    (he : aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = f) :
    P.IsWeightedHomogeneous (fun j : Fin N => (j : ℕ) + 1) n := by
  have hp : weightedHomogeneousComponent (fun j : Fin N => (j : ℕ) + 1) n P = P := by
    apply aeval_esymm_injective N
    rw [elementary_homogeneousComponent, he, homogeneousComponent_eq_self hf]
  rw [← hp]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- Only `E_1, …, E_n` occur in weighted degree `n`. -/
lemma elementary_vars_bound {M n : ℕ} {P : Pol M}
    (hp : P.IsWeightedHomogeneous (fun j : Fin M => (j : ℕ) + 1) n)
    {j : Fin M} (hj : j ∈ P.vars) : (j : ℕ) < n := by
  obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
  have hw := hp (mem_support_iff.mp hd)
  have hl := Finsupp.le_weight_of_ne_zero' (fun j : Fin M => (j : ℕ) + 1)
    (Finsupp.mem_support_iff.mp hjd)
  omega

/-- **Finite-to-infinite step.** One polynomial in `E_1, …, E_|V|` works in every alphabet. -/
theorem stable_epositive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hpos : ∀ N, ∃ P : Pol N, (∀ d, 0 ≤ P.coeff d) ∧
      aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = chromSym N G) :
    ∃ P : Pol (Fintype.card V), (∀ d, 0 ≤ P.coeff d) ∧ ∀ N,
      aeval (fun j : Fin (Fintype.card V) => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = chromSym N G := by
  classical
  let n := Fintype.card V
  obtain ⟨P, hp, he⟩ := hpos n
  refine ⟨P, hp, fun N => ?_⟩
  let L := max n N
  have hnL : n ≤ L := le_max_left _ _
  have hNL : N ≤ L := le_max_right _ _
  obtain ⟨Q, _, hQ⟩ := hpos L
  have hhom := elementary_homogeneous (chromSym_homogeneous L G) hQ
  obtain ⟨Q', hQ'⟩ := exists_rename_eq_of_vars_subset_range Q (Fin.castLE hnL)
    (Fin.castLE_injective hnL) (by
      intro j hj
      exact ⟨⟨j, elementary_vars_bound hhom hj⟩, Fin.ext rfl⟩)
  have hspec : ∀ K, K ≤ L →
      aeval (fun j : Fin n => esymm (Fin K) ℚ ((j : ℕ) + 1)) Q' = chromSym K G := by
    intro K hKL
    have ht := congrArg (restrictVars K L) hQ
    rw [← hQ', aeval_rename, restrictVars_chromSym hKL] at ht
    rw [← AlgHom.comp_apply, comp_aeval] at ht
    simpa only [Function.comp_def, restrictVars_esymm hKL, Fin.val_castLE] using ht
  have hPQ : Q' = P := aeval_esymm_injective n ((hspec n hnL).trans he.symm)
  rw [← hPQ]
  exact hspec N hNL

/-- The ring of symmetric functions over `ℚ`, with variable `j` representing `e_{j+1}`. -/
abbrev Symm := MvPolynomial ℕ ℚ

/-- Specialization of symmetric functions to `N` colours. -/
def specializeSymm (N : ℕ) : Symm →ₐ[ℚ] Pol N :=
  aeval fun j => esymm (Fin N) ℚ (j + 1)

/-- Finite-alphabet specializations jointly distinguish symmetric functions. -/
theorem specializeSymm_jointly_injective {P Q : Symm}
    (h : ∀ N, specializeSymm N P = specializeSymm N Q) : P = Q := by
  classical
  let n := (P - Q).vars.sup id + 1
  obtain ⟨R, hR⟩ := exists_rename_eq_of_vars_subset_range (P - Q)
    (fun j : Fin n => (j : ℕ)) Fin.val_injective (by
      intro j hj
      exact ⟨⟨j, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩, rfl⟩)
  have hz : specializeSymm n (P - Q) = 0 := by rw [map_sub, h n, sub_self]
  rw [← hR, specializeSymm, aeval_rename] at hz
  have hzero : R = 0 := aeval_esymm_injective n (by
    simpa only [Function.comp_def, map_zero] using hz)
  rw [hzero, map_zero] at hR
  exact sub_eq_zero.mp hR.symm

/-- The canonical elementary expansion of the CSF, extracted in `|V|` variables. -/
def chromSymInf {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Symm :=
  rename Fin.val ((esymmAlgEquiv (Fin (Fintype.card V)) ℚ (n := Fintype.card V) (by simp)).symm
    ⟨chromSym (Fintype.card V) G, chromSym_isSymmetric _ _⟩)

/-- `e`-positivity in infinitely many variables, with all finite specializations identified. -/
theorem chromSymInf_epositive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hpos : ∀ N, ∃ P : Pol N, (∀ d, 0 ≤ P.coeff d) ∧
      aeval (fun j : Fin N => esymm (Fin N) ℚ ((j : ℕ) + 1)) P = chromSym N G) :
    (∀ d, 0 ≤ (chromSymInf G).coeff d) ∧
      ∀ N, specializeSymm N (chromSymInf G) = chromSym N G := by
  classical
  obtain ⟨P, hp, he⟩ := stable_epositive G hpos
  have hcan : chromSymInf G = rename Fin.val P := by
    unfold chromSymInf
    congr 1
    apply aeval_esymm_injective (Fintype.card V)
    have hc := (esymmAlgEquiv (Fin (Fintype.card V)) ℚ (n := Fintype.card V) (by simp)).apply_symm_apply
      ⟨chromSym (Fintype.card V) G, chromSym_isSymmetric _ _⟩
    simpa only [esymmAlgEquiv_apply, esymmAlgHom_apply] using
      (congrArg Subtype.val hc).trans (he _).symm
  rw [hcan]
  constructor
  · intro d
    by_cases hd : (rename Fin.val P).coeff d = 0
    · rw [hd]
    obtain ⟨e, rfl, _⟩ := coeff_rename_ne_zero _ _ _ hd
    rw [coeff_rename_mapDomain _ Fin.val_injective]
    exact hp e
  · intro N
    simpa only [specializeSymm, aeval_rename, Function.comp_def] using he N

/-- Theorem `stanstem` over the ring of symmetric functions. -/
theorem nuig_epositive_infinite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsNUIG G) : (∀ d, 0 ≤ (chromSymInf G).coeff d) ∧
      ∀ N, specializeSymm N (chromSymInf G) = chromSym N G :=
  chromSymInf_epositive G fun N => (nuig_epositive G hG N).2

/-- Theorem `pca` over the ring of symmetric functions. -/
theorem pca_graph_epositive_infinite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPCA G) :
    (∀ d, 0 ≤ (chromSymInf G).coeff d) ∧
      ∀ N, specializeSymm N (chromSymInf G) = chromSym N G :=
  chromSymInf_epositive G fun N => (pca_graph_epositive G hG N).2

end ProperCircularArc
