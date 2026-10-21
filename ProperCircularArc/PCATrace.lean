import ProperCircularArc.NUIG

/-!
# Theorem `pca` for traces of marked natural unit interval graphs

For a NUIG `G` on `Fin (n + k)` whose first and last `k` vertices form cliques, the graph
`cycTrace G` on `Fin n` identifies vertex `n + r` with vertex `r`.
-/

noncomputable section

namespace ProperCircularArc

open Finset

variable {n k : ℕ}

/-- The identification `n + r ↦ r`. -/
def piN (hk : k ≤ n) (u : Fin (n + k)) : Fin n :=
  if h : (u : ℕ) < n then ⟨u, h⟩ else ⟨u - n, by have := u.2; omega⟩

/-- The trace of a marked NUIG on `Fin (n + k)`: vertex `n + r` is identified with `r`. -/
def cycTrace (hk : k ≤ n) (G : SimpleGraph (Fin (n + k))) : SimpleGraph (Fin n) where
  Adj p q := p ≠ q ∧ ∃ u v, piN hk u = p ∧ piN hk v = q ∧ G.Adj u v
  symm := ⟨fun p q ⟨hpq, u, v, hu, hv, h⟩ => ⟨hpq.symm, v, u, hv, hu, h.symm⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- **Theorem `pca`** (combinatorial form): if `G` is a NUIG on `Fin (n + k)` whose first and last
`k` vertices form cliques, `k ≤ n`, and vertex `n + r` is not adjacent to vertex `r`, then the
chromatic symmetric function of the trace `cycTrace G` is, for every `N`, the trace of a tableau
matrix and a polynomial in `e_1, …, e_N` with nonnegative coefficients. -/
theorem pca_epositive (G : SimpleGraph (Fin (n + k))) [DecidableRel G.Adj] (hG : IsNUIG G)
    (hk : k ≤ n)
    (hin : ∀ i j : Fin (n + k), (i : ℕ) < k → (j : ℕ) < k → i ≠ j → G.Adj i j)
    (hout : ∀ i j : Fin (n + k), n ≤ (i : ℕ) → n ≤ (j : ℕ) → i ≠ j → G.Adj i j)
    (hloop : ∀ r : ℕ, (hr : r < k) → ¬G.Adj ⟨n + r, by omega⟩ ⟨r, by omega⟩) (N : ℕ) :
    (∃ w : Word k k, algebraMap (Pol N) (KN N) (chromSym N (cycTrace hk G)) =
        Matrix.trace (Word.tabMat N w)) ∧
    ∃ P : MvPolynomial (Fin N) ℚ, (∀ e, 0 ≤ P.coeff e) ∧
      MvPolynomial.aeval (fun j : Fin N => MvPolynomial.esymm (Fin N) ℚ ((j : ℕ) + 1)) P =
        chromSym N (cycTrace hk G) := by
  obtain ⟨w, h, hadj, hinp, hmark⟩ := word_of_nuig hG k k (by omega) (by omega) hin
    (fun i j hi hj hij => hout i j (by omega) (by omega) hij)
  have hmark' : ∀ s, (Word.mark w s : ℕ) = n + s := fun s => by rw [hmark]; omega
  have hw : Word.TraceOK w := by
    refine ⟨fun r s e => ?_, fun r hr => ?_⟩
    · have := congrArg Fin.val e
      rw [hmark', hinp] at this
      have := s.2; omega
    · rw [hadj] at hr
      have e1 : Fin.cast h (Word.mark w r) = ⟨n + r, by omega⟩ := Fin.ext (by simp [hmark'])
      have e2 : Fin.cast h (Word.inp w r) = ⟨r, by omega⟩ := Fin.ext (by simp [hinp])
      rw [e1, e2] at hr
      exact hloop r r.2 hr
  -- the non-output vertices are the vertices below `n`
  have hnot : ∀ u : Fin (Word.nv w), u ∉ Set.range (Word.mark w) ↔ (u : ℕ) < n := by
    intro u
    constructor
    · intro hu
      by_contra hge
      push Not at hge
      have hu' : (u : ℕ) < n + k := by have := u.2; omega
      exact hu ⟨⟨u - n, by omega⟩, Fin.ext (by rw [hmark']; simp; omega)⟩
    · rintro hu ⟨s, rfl⟩
      rw [hmark'] at hu; omega
  -- the isomorphism `tr w ≃ cycTrace G`
  let φ : Word.TV w → Fin n := fun p => ⟨p.1, (hnot p.1).1 p.2⟩
  let ψ : Fin n → Word.TV w := fun p =>
    ⟨⟨p, by have := p.2; omega⟩, (hnot _).2 p.2⟩
  have hφψ : ∀ p, φ (ψ p) = p := fun p => rfl
  have hψφ : ∀ p, ψ (φ p) = p := fun p => rfl
  have hproj : ∀ u : Fin (Word.nv w), φ (Word.proj w hw u) = piN hk (Fin.cast h u) := by
    intro u
    by_cases hu : u ∈ Set.range (Word.mark w)
    · obtain ⟨s, rfl⟩ := hu
      rw [Word.proj_mark]
      ext
      simp only [φ, piN, Fin.coe_cast, hmark', hinp]
      rw [dif_neg (by omega)]
      simp
    · rw [Word.proj_of_not_mem hw hu]
      ext
      simp only [φ, piN, Fin.coe_cast]
      rw [dif_pos ((hnot u).1 hu)]
  have hφinj : Function.Injective φ := fun a b hab => by rw [← hψφ a, ← hψφ b, hab]
  let e : SimpleGraph.Iso (Word.trGraph w hw) (cycTrace hk G) :=
    { toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      map_rel_iff' := by
        intro P Q
        show (cycTrace hk G).Adj (φ P) (φ Q) ↔ (Word.trGraph w hw).Adj P Q
        constructor
        · rintro ⟨hne, u', v', hu', hv', hG'⟩
          refine ⟨fun e => hne (by rw [e]), Fin.cast h.symm u', Fin.cast h.symm v', ?_, ?_, ?_⟩
          · apply hφinj; rw [hproj, ← hu']; rfl
          · apply hφinj; rw [hproj, ← hv']; rfl
          · show Word.adj w _ _
            rw [hadj]; exact hG'
        · rintro ⟨hne, u, v, hu, hv, hadj'⟩
          refine ⟨fun e => hne (hφinj e), Fin.cast h u, Fin.cast h v, ?_, ?_, (hadj u v).1 hadj'⟩
          · rw [← hproj, hu]
          · rw [← hproj, hv] }
  obtain ⟨P, hP, hPe⟩ := Word.pca_epositive N w hw
  rw [chromSym_iso N e] at hPe
  refine ⟨⟨w, ?_⟩, P, hP, hPe⟩
  rw [← chromSym_iso N e, Word.pca_trace]

end ProperCircularArc
