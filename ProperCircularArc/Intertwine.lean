import ProperCircularArc.Span

/-!
# Theorem `main`: the change of basis intertwines the tableau and colour operators

We prove, in the infinite-colour model,

* (M) `U_{k+1} M_k = M̂_k U_k`,
* (R) `U_k R_k = R̂_k U_k`,
* (S) `U_k S_s = Ŝ_s U_k`,
* (D) `D̂_k U_k = U_{k-1} D_k`,

following the paper: (S) by induction on the rank together with
`U_k S_{k-1} R_k = Ŝ_{k-1} R̂_k U_k`, and then (D) by a second induction on the rank.
-/

noncomputable section

namespace ProperCircularArc

open Finset

lemma lhom_ext_bv_gen {n : ℕ} {M : Type*} [AddCommGroup M] [Module Lam M] {f g : V n →ₗ[Lam] M}
    (h : ∀ σ, f (bv σ) = g (bv σ)) : f = g := by
  apply Finsupp.lhom_ext
  intro σ c
  have : Finsupp.single σ c = c • bv σ := by simp [bv]
  rw [this, map_smul, map_smul, h]

/-- (M) for all vectors. -/
theorem U_M' (k : ℕ) (v : V k) : Ul (k + 1) (Mop k v) = Mh k (Ul k v) := by
  have : Ul (k + 1) ∘ₗ Mop k = (Mh k).toLinearMap ∘ₗ Ul k :=
    lhom_ext_bv_gen fun σ => by simp [U_M]
  exact LinearMap.congr_fun this v

/-- (R) for all vectors. -/
theorem U_R' (k : ℕ) (v : V (k + 1)) : Ul (k + 1) (Rop k v) = Rh k (Ul (k + 1) v) := by
  have : Ul (k + 1) ∘ₗ Rop k = Rh k ∘ₗ Ul (k + 1) :=
    lhom_ext_bv_gen fun σ => by simp [U_R]
  exact LinearMap.congr_fun this v

lemma Ul_invalid {k : ℕ} {σ : Idx (k + 1)} (h : ¬Valid σ) : Ul (k + 1) (bv σ) = 0 := by
  rw [Ul_bv, U_invalid h]

/-- The statement (S) at level `n`. -/
def SwapProp (n : ℕ) : Prop :=
  ∀ s, s + 1 < n → ∀ v : V n, Ul n (Sop n s v) = Sh n s (Ul n v)

/-- (S) together with `U_k S_{k-1} R_k = Ŝ_{k-1} R̂_k U_k`, as a submodule. -/
def swapSub (k : ℕ) : Submodule Lam (V (k + 2)) :=
  (⨅ s : Fin (k + 1), LinearMap.eqLocus (Ul (k + 2) ∘ₗ Sop (k + 2) s)
      ((Sh (k + 2) s).toLinearMap ∘ₗ Ul (k + 2))) ⊓
    LinearMap.eqLocus (Ul (k + 2) ∘ₗ Sop (k + 2) k ∘ₗ Rop (k + 1))
      ((Sh (k + 2) k).toLinearMap ∘ₗ Rh (k + 1) ∘ₗ Ul (k + 2))

lemma mem_swapSub {k : ℕ} {v : V (k + 2)} : v ∈ swapSub k ↔
    (∀ s, s + 1 < k + 2 → Ul (k + 2) (Sop (k + 2) s v) = Sh (k + 2) s (Ul (k + 2) v)) ∧
      Ul (k + 2) (Sop (k + 2) k (Rop (k + 1) v)) = Sh (k + 2) k (Rh (k + 1) (Ul (k + 2) v)) := by
  simp only [swapSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun s hs => h1 ⟨s, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s => h1 s (by omega), h2⟩

/-- **(S)**, by induction on the level and the rank. -/
theorem U_S : ∀ n, SwapProp n
  | 0 => fun s hs => by omega
  | 1 => fun s hs => by omega
  | k + 2 => by
    have IH : SwapProp (k + 1) := U_S (k + 1)
    -- the `M`-part, `s ≤ k - 1`
    have hMs : ∀ s, s + 1 < k + 1 → ∀ v, Ul (k + 2) (Sop (k + 2) s (Mop (k + 1) v)) =
        Sh (k + 2) s (Ul (k + 2) (Mop (k + 1) v)) := by
      intro s hs v
      have := LinearMap.congr_fun (Sop_Mop (n := k + 1) hs) v
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, U_M', IH s hs v, U_M', Sh_Mh hs]
    -- the `M`-part, `s = k`, by the coarse span at level `k + 1`
    have hMk : ∀ v, Ul (k + 2) (Sop (k + 2) k (Mop (k + 1) v)) =
        Sh (k + 2) k (Ul (k + 2) (Mop (k + 1) v)) := by
      intro v
      let W' : Submodule Lam (V (k + 1)) :=
        LinearMap.eqLocus (Ul (k + 2) ∘ₗ Sop (k + 2) k ∘ₗ Mop (k + 1))
          ((Sh (k + 2) k).toLinearMap ∘ₗ Ul (k + 2) ∘ₗ Mop (k + 1))
      have hW' : ∀ u, u ∈ W' ↔ Ul (k + 2) (Sop (k + 2) k (Mop (k + 1) u)) =
          Sh (k + 2) k (Ul (k + 2) (Mop (k + 1) u)) := fun u => by
        simp [W', LinearMap.mem_eqLocus]
      refine (hW' v).1 (coarse_induction k W' ?_ ?_ ?_ v)
      · intro σ hσ
        rw [hW', Mop_bv_invalid hσ]; simp
      · intro u
        rw [hW']
        have := LinearMap.congr_fun (Sop_Mop_Mop k) u
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [this, U_M', U_M', Sh_Mh_Mh]
      · intro u
        rw [hW']
        have := LinearMap.congr_fun (Sop_Mop_Rop k) u
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [this, U_R', U_M', U_M', U_R', Sh_Mh_Rh]
    have hS := span_induction (swapSub k) ?hinv ?hM ?hR
    · intro s hs v
      exact (mem_swapSub.1 (mem_of_bv_mem _ hS v)).1 s hs
    case hinv =>
      intro σ hσ
      rw [mem_swapSub]
      refine ⟨fun s _ => ?_, ?_⟩
      · rw [Sop_bv_invalid hσ, Ul_invalid hσ, map_zero]
      · rw [Rop_bv_invalid hσ, map_zero, map_zero, Ul_invalid hσ, map_zero, map_zero]
    case hM =>
      intro v
      rw [mem_swapSub]
      refine ⟨fun s hs => ?_, ?_⟩
      · rcases lt_or_eq_of_le (show s ≤ k by omega) with h | h
        · exact hMs s (by omega) v
        · subst h; exact hMk v
      · rw [Sop_Rop_Mop_apply, U_M', U_R', U_M']
        have := Sh_Mh_Rh (R := Lam) k (Ul (k + 1) v)
        rw [← this, Sh_Sh]
    case hR =>
      intro w y a hv ha ha1 hay ih
      have hτ := ih _ (rk_cons_lt hv ha ha1 hay)
      rw [mem_swapSub] at hτ ⊢
      obtain ⟨hτS, hτR⟩ := hτ
      refine ⟨fun s hs => ?_, ?_⟩
      · rcases lt_or_eq_of_le (show s ≤ k by omega) with h | h
        · have := LinearMap.congr_fun (Sop_Rop (n := k + 1) (s := s) (by omega)) (bv (cons a w))
          simp only [LinearMap.coe_comp, Function.comp_apply] at this
          rw [this, U_R', hτS (s + 1) (by omega), U_R', Sh_Rh (by omega)]
        · subst h
          rw [hτR, U_R']
      · rw [Sop_Rop_Rop_apply, U_R', U_R', hτS 0 (by omega), U_R', Sh_Rh_Rh]

/-- (S) in its final form. -/
theorem U_S' {n s : ℕ} (hs : s + 1 < n) (v : V n) : Ul n (Sop n s v) = Sh n s (Ul n v) :=
  U_S n s hs v

/-- **(D)**: `D̂_{k+1} U_{k+1} = U_k D_{k+1}`. -/
theorem U_D : ∀ k (v : V (k + 1)), Dh Pw k (Ul (k + 1) v) = Ul k (Dop k v)
  | 0, v => by
    have : (Dh Pw 0 ∘ₗ Ul 1 : V 1 →ₗ[Lam] CV Lam 0) = Ul 0 ∘ₗ Dop 0 := by
      refine lhom_ext_bv_gen fun σ => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply]
      by_cases hσ : Valid σ
      · rw [Dop_bv_valid hσ, map_smul]
        simp only [Ul_bv]
        show Dh Pw 0 (U1fn (σ 0)) = Eratio (σ 0) • (1 : CV Lam 0)
        rw [Dh_U1fn _ (hσ.2 0), smul_eq_C_mul', mul_one]
      · rw [Ul_invalid hσ, map_zero, Dop_bv_invalid hσ, map_zero]
    exact LinearMap.congr_fun this v
  | k + 1, v => by
    have IH := U_D k
    let W : Submodule Lam (V (k + 2)) :=
      LinearMap.eqLocus (Dh Pw (k + 1) ∘ₗ Ul (k + 2)) (Ul (k + 1) ∘ₗ Dop (k + 1))
    have hW : ∀ u, u ∈ W ↔ Dh Pw (k + 1) (Ul (k + 2) u) = Ul (k + 1) (Dop (k + 1) u) :=
      fun u => by simp [W, LinearMap.mem_eqLocus]
    refine (hW v).1 (mem_of_bv_mem W (span_induction W ?_ ?_ ?_) v)
    · intro σ hσ
      rw [hW, Ul_invalid hσ, map_zero, Dop_bv_invalid hσ, map_zero]
    · intro u
      rw [hW, U_M']
      have h1 := Mh_Dh_sub_Dh_Mh Pw k (Ul (k + 1) u)
      have h2 : Dh Pw (k + 1) (Mh (k + 1) (Ul (k + 1) u)) =
          Mh k (Dh Pw k (Ul (k + 1) u)) - Rh k (Ul (k + 1) u) := by
        rw [← h1]; abel
      rw [h2, IH, ← U_M', ← U_R', ← map_sub]
      congr 1
      simp only [Rop, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply]
      abel
    · intro w y a hv ha ha1 hay ih
      rw [hW]
      -- `S_1 b_{a,w}` lies in `W`
      have hτ := ih _ (rk_cons_lt hv ha ha1 hay)
      have hS0 : Sop (k + 2) 0 (bv (cons a w)) ∈ W := by
        have hvc := valid_cons (valid_of_snoc hv).1 ha ha1
        rw [Sop_bv_valid hvc]
        by_cases ha0 : a + 1 = w 0
        · have hc : swc (cons a w) 0 = 1 := by
            simp [swc, getE, ← ha0]
          rw [hc, sub_self, qc_zero, zero_smul, add_zero, qc_one, one_smul]
          exact hτ
        · refine W.add_mem (W.smul_mem _ hτ) (W.smul_mem _ ?_)
          have e : cons a w ∘ swapPerm (k + 2) 0 = cons (w 0) (cons a (Fin.tail w)) := by
            conv_lhs => rw [tail_eq_cons w]
            exact swap01_cons_cons a (w 0) (Fin.tail w)
          rw [e]
          exact ih _ (rk_swap_lt hv ha ha1 hay ha0)
      have hS0' := (hW _).1 hS0
      rw [U_R', Dh_Rh, ← U_S' (n := k + 2) (s := 0) (by omega), hS0']
      have := LinearMap.congr_fun (Dop_Rop k) (bv (cons a w))
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, U_R']

/-! ## Theorem `main` -/

/-- **Theorem `main`** (infinite-colour form): the maps `U_k` intertwine the tableau operators
with the colour operators. -/
theorem main_intertwine (k : ℕ) :
    (∀ v : V k, Ul (k + 1) (Mop k v) = Mh k (Ul k v)) ∧
    (∀ v : V (k + 1), Dh Pw k (Ul (k + 1) v) = Ul k (Dop k v)) :=
  ⟨U_M' k, U_D k⟩

end ProperCircularArc
