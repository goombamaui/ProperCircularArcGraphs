import ProperCircularArc.Graphs

/-!
# The trace of a marked graph

For a word `w` from level `k` to level `k`, the trace graph `tr w` identifies the `r`-th output
with the `r`-th input.  Its vertices are the vertices of `graph w` that are not outputs.  We show
`X_{tr w}(x_1, …, x_N) = tr M̂_w` (Lemma `color`, trace part).
-/

noncomputable section

namespace ProperCircularArc

open MvPolynomial Finset Matrix

namespace Word

variable {k : ℕ}

lemma inp_clique : ∀ {a b : ℕ} (w : Word a b) (r s : Fin a), r ≠ s → adj w (inp w r) (inp w s)
  | _, _, nil, r, s, h => h
  | _, _, M w, r, s, h => by simp only [adj, inp, extendAdj_cc]; exact inp_clique w r s h
  | _, _, D w, r, s, h => inp_clique w r s h

/-- Hypotheses making the trace a simple graph: outputs and inputs are disjoint, and no output is
adjacent to its own input. -/
structure TraceOK (w : Word k k) : Prop where
  disj : ∀ r s, mark w r ≠ inp w s
  noloop : ∀ r, ¬adj w (mark w r) (inp w r)

/-- The vertices of the trace graph: the non-output vertices. -/
abbrev TV (w : Word k k) := {v : Fin (nv w) // v ∉ Set.range (mark w)}

open Classical in
/-- The identification map: an output goes to the corresponding input. -/
def proj (w : Word k k) (hw : TraceOK w) (v : Fin (nv w)) : TV w :=
  if h : ∃ r, mark w r = v then ⟨inp w h.choose, fun ⟨s, hs⟩ => hw.disj s _ hs⟩ else ⟨v, h⟩

lemma proj_of_not_mem {w : Word k k} (hw : TraceOK w) {v : Fin (nv w)} (h : v ∉ Set.range (mark w)) :
    proj w hw v = ⟨v, h⟩ := by
  unfold proj
  have h' : ¬∃ r, mark w r = v := fun ⟨r, hr⟩ => h ⟨r, hr⟩
  rw [dif_neg h']

lemma proj_mark {w : Word k k} (hw : TraceOK w) (r : Fin k) :
    proj w hw (mark w r) = ⟨inp w r, fun ⟨s, hs⟩ => hw.disj s r hs⟩ := by
  unfold proj
  have h : ∃ s, mark w s = mark w r := ⟨r, rfl⟩
  rw [dif_pos h]
  congr 2
  exact mark_injective w h.choose_spec

lemma proj_val {w : Word k k} (hw : TraceOK w) (p : TV w) : proj w hw p.1 = p :=
  proj_of_not_mem hw p.2

/-- The trace graph `tr w`. -/
def trGraph (w : Word k k) (hw : TraceOK w) : SimpleGraph (TV w) where
  Adj p q := p ≠ q ∧ ∃ u v, proj w hw u = p ∧ proj w hw v = q ∧ adj w u v
  symm := ⟨fun p q ⟨hpq, u, v, hu, hv, h⟩ => ⟨hpq.symm, v, u, hv, hu, adj_symm w u v h⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

lemma proj_ne_of_adj {w : Word k k} (hw : TraceOK w) {u v : Fin (nv w)} (h : adj w u v) :
    proj w hw u ≠ proj w hw v := by
  intro e
  by_cases hu : u ∈ Set.range (mark w) <;> by_cases hv : v ∈ Set.range (mark w)
  · obtain ⟨r, rfl⟩ := hu; obtain ⟨s, rfl⟩ := hv
    rw [proj_mark, proj_mark] at e
    have := inp_injective w (congrArg Subtype.val e)
    subst this
    exact adj_irrefl w _ h
  · obtain ⟨r, rfl⟩ := hu
    rw [proj_mark, proj_of_not_mem hw hv] at e
    have : v = inp w r := (congrArg Subtype.val e).symm
    subst this
    exact hw.noloop r h
  · obtain ⟨s, rfl⟩ := hv
    rw [proj_mark, proj_of_not_mem hw hu] at e
    have : u = inp w s := congrArg Subtype.val e
    subst this
    exact hw.noloop s (adj_symm w _ _ h)
  · rw [proj_of_not_mem hw hu, proj_of_not_mem hw hv] at e
    have : u = v := congrArg Subtype.val e
    subst this
    exact adj_irrefl w _ h

lemma proj_injOn {w : Word k k} (hw : TraceOK w) {u v : Fin (nv w)}
    (hu : u ∉ Set.range (inp w)) (hv : v ∉ Set.range (inp w)) (e : proj w hw u = proj w hw v) :
    u = v := by
  by_cases hu' : u ∈ Set.range (mark w) <;> by_cases hv' : v ∈ Set.range (mark w)
  · obtain ⟨r, rfl⟩ := hu'; obtain ⟨s, rfl⟩ := hv'
    rw [proj_mark, proj_mark] at e
    rw [inp_injective w (congrArg Subtype.val e)]
  · obtain ⟨r, rfl⟩ := hu'
    rw [proj_mark, proj_of_not_mem hw hv'] at e
    exact absurd ⟨r, congrArg Subtype.val e⟩ hv
  · obtain ⟨s, rfl⟩ := hv'
    rw [proj_mark, proj_of_not_mem hw hu'] at e
    exact absurd ⟨s, (congrArg Subtype.val e).symm⟩ hu
  · rw [proj_of_not_mem hw hu', proj_of_not_mem hw hv'] at e
    exact congrArg Subtype.val e

lemma proj_surj {w : Word k k} (hw : TraceOK w) (p : TV w) :
    ∃ v, v ∉ Set.range (inp w) ∧ proj w hw v = p := by
  by_cases hp : p.1 ∈ Set.range (inp w)
  · obtain ⟨r, hr⟩ := hp
    refine ⟨mark w r, fun ⟨s, hs⟩ => hw.disj r s hs.symm, ?_⟩
    rw [proj_mark]; exact Subtype.ext hr
  · exact ⟨p.1, hp, proj_val hw p⟩

variable {N : ℕ}

open Classical in
/-- **Lemma `color`, trace part**: `X_{tr w}(x_1, …, x_N) = tr M̂_w`. -/
theorem chromSym_trGraph (w : Word k k) (hw : TraceOK w) :
    chromSym N (trGraph w hw) = trace (colMatP N w) := by
  -- the trace as a sum over colourings of `graph w`
  have h1 : trace (colMatP N w) = ∑ κ : Fin (nv w) → Fin N,
      if IsProper (graph w) κ ∧ (∀ r, κ (mark w r) = κ (inp w r)) then
        ∏ v ∈ univ.filter (fun v => v ∉ Set.range (inp w)), X (κ v) else 0 := by
    simp only [trace, diag_apply, colMatP_eq_colorSum, colorSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    by_cases hA : IsProper (graph w) κ ∧ (∀ r, κ (mark w r) = κ (inp w r))
    · have hinj : Function.Injective fun r => κ (inp w r) := by
        intro r s e
        by_contra hrs
        exact hA.1 _ _ (inp_clique w r s hrs) e
      rw [if_pos hA, Finset.sum_eq_single ⟨fun r => κ (inp w r), hinj⟩]
      · rw [if_pos ⟨hA.1, fun r => hA.2 r, fun r => rfl⟩]
      · intro o _ ho
        rw [if_neg]
        rintro ⟨_, _, h3⟩
        exact ho (DFunLike.ext _ _ fun r => (h3 r).symm)
      · simp
    · rw [if_neg hA]
      refine Finset.sum_eq_zero fun o _ => if_neg ?_
      rintro ⟨h1, h2, h3⟩
      exact hA ⟨h1, fun r => by rw [h2, h3]⟩
  rw [h1, chromSym, ← Finset.sum_filter, ← Finset.sum_filter]
  -- the bijection `κ ↦ κ ∘ proj`
  have hκproj : ∀ kt : Fin (nv w) → Fin N, (∀ r, kt (mark w r) = kt (inp w r)) →
      ∀ v, kt (proj w hw v).1 = kt v := by
    intro kt hc v
    by_cases hv : v ∈ Set.range (mark w)
    · obtain ⟨r, rfl⟩ := hv
      rw [proj_mark, hc]
    · rw [proj_of_not_mem hw hv]
  refine Finset.sum_bij' (fun κ _ => κ ∘ proj w hw) (fun kt _ => kt ∘ Subtype.val) ?_ ?_ ?_ ?_ ?_
  · intro κ hκ
    simp only [mem_filter, mem_univ, true_and] at hκ ⊢
    refine ⟨fun u v huv => hκ _ _ ⟨proj_ne_of_adj hw huv, u, v, rfl, rfl, huv⟩, fun r => ?_⟩
    simp only [Function.comp_apply]
    rw [proj_mark, proj_of_not_mem hw (fun ⟨s, hs⟩ => hw.disj s r hs)]
  · intro kt hkt
    simp only [mem_filter, mem_univ, true_and] at hkt ⊢
    rintro p q ⟨_, u, v, rfl, rfl, huv⟩
    simp only [Function.comp_apply, hκproj kt hkt.2]
    exact hkt.1 u v huv
  · intro κ _
    funext p
    simp only [Function.comp_apply, proj_val]
  · intro kt hkt
    simp only [mem_filter, mem_univ, true_and] at hkt
    funext v
    simp only [Function.comp_apply, hκproj kt hkt.2]
  · intro κ _
    symm
    refine Finset.prod_bij (fun v _ => proj w hw v) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro u hu v hv e
      simp only [mem_filter, mem_univ, true_and] at hu hv
      exact proj_injOn hw hu hv e
    · intro p _
      obtain ⟨v, hv, e⟩ := proj_surj hw p
      exact ⟨v, by simpa using hv, e⟩

end Word


end ProperCircularArc
