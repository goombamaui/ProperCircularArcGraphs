import ProperCircularArc.Tableaux

/-!
# Products of marked graphs and Lemma `tableau-mult`

Words represent arbitrary marked NUIGs by `word_of_nuig`. Composition executes the
right-hand graph first and identifies its outputs with the left-hand graph's inputs.
The two inclusions below describe the graph gluing, including overlapping input and
output cliques and the empty word.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ProperCircularArc

namespace Word

variable {a b c N : ℕ}

/-- Execute `h`, then `g`: the product `G + H` in the paper's matrix order. -/
def comp (h : Word a b) : {c : ℕ} → Word b c → Word a c
  | _, nil => h
  | _, M g => M (comp h g)
  | _, D g => D (comp h g)

lemma tabMat_comp (h : Word a b) : ∀ {c : ℕ} (g : Word b c),
    tabMat N (comp h g) = tabMat N g * tabMat N h
  | _, nil => by simp [comp, tabMat]
  | _, M g => by rw [comp, tabMat, tabMat, tabMat_comp h g, Matrix.mul_assoc]
  | _, D g => by rw [comp, tabMat, tabMat, tabMat_comp h g, Matrix.mul_assoc]

/-- **Lemma `tableau-mult`** for arbitrary marked NUIGs, represented by words. -/
theorem hikMat_comp (h : Word a b) (g : Word b c) :
    hikMat N (graph (comp h g)) (inp (comp h g)) (mark (comp h g)) =
      hikMat N (graph g) (inp g) (mark g) * hikMat N (graph h) (inp h) (mark h) := by
  simp only [hikMat_eq_tabMat, tabMat_comp]

/-- Inclusion of the vertices of the graph executed first. -/
def compLeft (h : Word a b) : {c : ℕ} → (g : Word b c) → Fin (nv h) → Fin (nv (comp h g))
  | _, nil => id
  | _, M g => fun v => (compLeft h g v).castSucc
  | _, D g => compLeft h g

/-- Inclusion of the vertices of the graph executed second; its initial clique is identified
with the outputs of the first graph. -/
def compRight (h : Word a b) : {c : ℕ} → (g : Word b c) → Fin (nv g) → Fin (nv (comp h g))
  | _, nil => mark h
  | _, M g => Fin.snoc (α := fun _ => Fin (nv (comp h g) + 1))
      (fun v => (compRight h g v).castSucc) (Fin.last _)
  | _, D g => compRight h g

@[simp] lemma compRight_cast (h : Word a b) (g : Word b c) (v : Fin (nv g)) :
    compRight h (M g) v.castSucc = (compRight h g v).castSucc := by simp [compRight]

@[simp] lemma compRight_last (h : Word a b) (g : Word b c) :
    compRight h (M g) (Fin.last _) = Fin.last _ := by simp [compRight]

lemma compLeft_injective (h : Word a b) : ∀ {c : ℕ} (g : Word b c),
    Function.Injective (compLeft h g)
  | _, nil => Function.injective_id
  | _, M g => (Fin.castSucc_injective _).comp (compLeft_injective h g)
  | _, D g => compLeft_injective h g

lemma compRight_injective (h : Word a b) : ∀ {c : ℕ} (g : Word b c),
    Function.Injective (compRight h g)
  | _, nil => mark_injective h
  | _, M g => by
    rw [compRight, Fin.snoc_injective_iff]
    exact ⟨(Fin.castSucc_injective _).comp (compRight_injective h g), by
      rintro ⟨v, hv⟩; exact Fin.castSucc_ne_last _ hv⟩
  | _, D g => compRight_injective h g

@[simp] lemma comp_mark (h : Word a b) : ∀ {c : ℕ} (g : Word b c) (r : Fin c),
    mark (comp h g) r = compRight h g (mark g r)
  | _, nil, r => rfl
  | _, M g, r => by
    induction r using Fin.lastCases <;> simp [comp, mark, comp_mark]
  | _, D g, r => comp_mark h g r.succ

@[simp] lemma comp_inp (h : Word a b) : ∀ {c : ℕ} (g : Word b c) (r : Fin a),
    inp (comp h g) r = compLeft h g (inp h r)
  | _, nil, r => rfl
  | _, M g, r => by simp [comp, inp, compLeft, comp_inp]
  | _, D g, r => comp_inp h g r

/-- Exactly the prescribed clique vertices are identified. -/
lemma comp_overlap (h : Word a b) : ∀ {c : ℕ} (g : Word b c) (u : Fin (nv h)) (v : Fin (nv g)),
    compLeft h g u = compRight h g v ↔ ∃ r : Fin b, u = mark h r ∧ v = inp g r
  | _, nil, u, v => by
    change u = mark h v ↔ ∃ r, u = mark h r ∧ v = r
    exact ⟨fun e => ⟨v, e, rfl⟩, by rintro ⟨r, e, rfl⟩; exact e⟩
  | _, M g, u, v => by
    induction v using Fin.lastCases with
    | last =>
      simp only [compLeft, compRight_last, inp, Fin.castSucc_ne_last, false_iff]
      rintro ⟨r, _, hr⟩
      exact Fin.castSucc_ne_last _ hr.symm
    | cast v => simpa [compLeft, inp, compRight] using comp_overlap h g u v
  | _, D g, u, v => comp_overlap h g u v

/-- Every vertex of the composite comes from one of the two graphs. -/
lemma comp_cover (h : Word a b) : ∀ {c : ℕ} (g : Word b c) (v : Fin (nv (comp h g))),
    (∃ u, compLeft h g u = v) ∨ ∃ u, compRight h g u = v
  | _, nil, v => Or.inl ⟨v, rfl⟩
  | _, M g, v => by
    induction v using Fin.lastCases with
    | last => exact Or.inr ⟨Fin.last _, by simp⟩
    | cast v =>
      rcases comp_cover h g v with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact Or.inl ⟨u, rfl⟩
      · exact Or.inr ⟨u.castSucc, by simp⟩
  | _, D g, v => comp_cover h g v

/-- The edges of the composite are exactly the images of the edges of the two factors.
Together with `comp_overlap` and `comp_cover`, this identifies `comp` with graph gluing. -/
theorem adj_comp (h : Word a b) : ∀ {c : ℕ} (g : Word b c) (x y : Fin (nv (comp h g))),
    adj (comp h g) x y ↔
      (∃ u v, adj h u v ∧ compLeft h g u = x ∧ compLeft h g v = y) ∨
      (∃ u v, adj g u v ∧ compRight h g u = x ∧ compRight h g v = y)
  | _, nil, x, y => by
    simp only [comp, compLeft, compRight, id_eq, adj]
    constructor
    · intro hxy; exact Or.inl ⟨x, y, hxy, rfl, rfl⟩
    · rintro (⟨u, v, huv, rfl, rfl⟩ | ⟨u, v, huv, rfl, rfl⟩)
      · exact huv
      · exact mark_clique h u v huv
  | _, M g, x, y => by
    induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last =>
        simp only [comp, adj, extendAdj_ll]
        constructor
        · exact False.elim
        · rintro (⟨u, v, _, hu, _⟩ | ⟨u, v, huv, hu, hv⟩)
          · exact Fin.castSucc_ne_last _ hu
          · have hu' : u = Fin.last _ := compRight_injective h (M g) (by simpa only [compRight_last] using hu)
            have hv' : v = Fin.last _ := compRight_injective h (M g) (by simpa only [compRight_last] using hv)
            subst u v; exact adj_irrefl (M g) _ huv
      | cast y =>
        simp only [comp, adj, extendAdj_lc]
        constructor
        · rintro ⟨r, hr⟩
          exact Or.inr ⟨Fin.last _, (mark g r).castSucc, by simp, by simp,
            by rw [compRight_cast, ← comp_mark, hr]⟩
        · rintro (⟨u, v, _, hu, _⟩ | ⟨u, v, huv, hu, hv⟩)
          · exact False.elim (Fin.castSucc_ne_last _ hu)
          · have hu' : u = Fin.last _ := compRight_injective h (M g) (by simpa only [compRight_last] using hu)
            subst u
            induction v using Fin.lastCases with
            | last => exact False.elim (adj_irrefl (M g) _ huv)
            | cast v =>
              obtain ⟨r, rfl⟩ := (show ∃ r, mark g r = v from by simpa [adj] using huv)
              exact ⟨r, by rw [comp_mark]; exact Fin.castSucc_injective _ (by simpa only [compRight_cast] using hv)⟩
    | cast x =>
      induction y using Fin.lastCases with
      | last =>
        simp only [comp, adj, extendAdj_cl]
        constructor
        · rintro ⟨r, hr⟩
          exact Or.inr ⟨(mark g r).castSucc, Fin.last _, by simp,
            by rw [compRight_cast, ← comp_mark, hr], by simp⟩
        · rintro (⟨u, v, _, _, hv⟩ | ⟨u, v, huv, hu, hv⟩)
          · exact False.elim (Fin.castSucc_ne_last _ hv)
          · have hv' : v = Fin.last _ := compRight_injective h (M g) (by simpa only [compRight_last] using hv)
            subst v
            induction u using Fin.lastCases with
            | last => exact False.elim (adj_irrefl (M g) _ huv)
            | cast u =>
              obtain ⟨r, rfl⟩ := (show ∃ r, mark g r = u from by simpa [adj] using huv)
              exact ⟨r, by rw [comp_mark]; exact Fin.castSucc_injective _ (by simpa only [compRight_cast] using hu)⟩
      | cast y =>
        simp only [comp, adj, extendAdj_cc]
        rw [adj_comp h g]
        constructor
        · rintro (⟨u, v, huv, hu, hv⟩ | ⟨u, v, huv, hu, hv⟩)
          · exact Or.inl ⟨u, v, huv, congrArg Fin.castSucc hu, congrArg Fin.castSucc hv⟩
          · exact Or.inr ⟨u.castSucc, v.castSucc, by simpa [adj] using huv,
              by rw [compRight_cast, hu], by rw [compRight_cast, hv]⟩
        · rintro (⟨u, v, huv, hu, hv⟩ | ⟨u, v, huv, hu, hv⟩)
          · exact Or.inl ⟨u, v, huv, Fin.castSucc_injective _ hu, Fin.castSucc_injective _ hv⟩
          · induction u using Fin.lastCases with
            | last => exact False.elim (Fin.castSucc_ne_last _ (by simpa only [compRight_last] using hu.symm))
            | cast u =>
              induction v using Fin.lastCases with
              | last => exact False.elim (Fin.castSucc_ne_last _ (by simpa only [compRight_last] using hv.symm))
              | cast v => exact Or.inr ⟨u, v, by simpa [adj] using huv,
                  Fin.castSucc_injective _ (by simpa only [compRight_cast] using hu),
                  Fin.castSucc_injective _ (by simpa only [compRight_cast] using hv)⟩
  | _, D g, x, y => adj_comp h g x y

/-- Computable adjacency for word graphs, used by exact finite example checks. -/
@[instance_reducible] def decidableAdj {a : ℕ} : ∀ {b : ℕ} (w : Word a b), DecidableRel (adj w)
  | _, nil => by dsimp [adj]; infer_instance
  | _, D w => decidableAdj w
  | _, M w => by
    intro u v
    induction u using Fin.lastCases with
    | last =>
      induction v using Fin.lastCases with
      | last => exact isFalse (by simp [adj])
      | cast v =>
          exact decidable_of_iff (∃ r, mark w r = v) (by simp only [adj, extendAdj_lc])
    | cast u =>
      induction v using Fin.lastCases with
      | last =>
          exact decidable_of_iff (∃ r, mark w r = u) (by simp only [adj, extendAdj_cl])
      | cast v =>
        letI := decidableAdj w u v
        exact decidable_of_iff (adj w u v) (by simp only [adj, extendAdj_cc])

instance {a b : ℕ} (w : Word a b) : DecidableRel (graph w).Adj := decidableAdj w

/-- Word graphs are NUIGs, including words that forget all their marked vertices. -/
lemma graph_isNUIG : ∀ {a b : ℕ} (w : Word a b), IsNUIG (graph w)
  | _, _, nil => by
    intro i j hij _ l hil hlj
    exact ⟨ne_of_lt hil, ne_of_lt hlj⟩
  | _, _, D w => graph_isNUIG w
  | _, _, M (b := b) w => by
    intro i j hij hadj l hil hlj
    induction j using Fin.lastCases with
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.castSucc_lt_last j).le) hij)
      | cast i =>
        induction l using Fin.lastCases with
        | last => exact False.elim ((not_lt_of_ge (Fin.castSucc_lt_last j).le) hlj)
        | cast l =>
            simpa only [graph, adj, extendAdj_cc] using
              graph_isNUIG w i j (Fin.castSucc_lt_castSucc_iff.mp hij)
                (by simpa only [graph, adj, extendAdj_cc] using hadj) l
                (Fin.castSucc_lt_castSucc_iff.mp hil) (Fin.castSucc_lt_castSucc_iff.mp hlj)
    | last =>
      induction i using Fin.lastCases with
      | last => exact False.elim (lt_irrefl _ hij)
      | cast i =>
        induction l using Fin.lastCases with
        | last => exact False.elim (lt_irrefl _ hlj)
        | cast l =>
          obtain ⟨r, hr⟩ := (show ∃ r, mark w r = i from by simpa only [graph, adj, extendAdj_cl] using hadj)
          have hstart : nv w - b ≤ (l : ℕ) := by
            have hv := mark_val w r
            have hil' : (i : ℕ) < l := Fin.castSucc_lt_castSucc_iff.mp hil
            rw [hr] at hv
            omega
          have hb := level_le_nv w
          let s : Fin b := ⟨(l : ℕ) - (nv w - b), by have := l.2; omega⟩
          have hs : mark w s = l := Fin.ext (by rw [mark_val]; dsimp [s]; omega)
          constructor
          · simp only [graph, adj, extendAdj_cc]
            rw [← hr, ← hs]
            apply mark_clique w r s
            intro he
            have hil' := Fin.castSucc_lt_castSucc_iff.mp hil
            have hei : i = l := hr.symm.trans (he ▸ hs)
            exact ne_of_lt hil' hei
          · simp only [graph, adj, extendAdj_cl]
            exact ⟨s, hs⟩

end Word

/-- A marked NUIG with the paper's canonical ordered input and output cliques. -/
structure MarkedNUIG (a b : ℕ) where
  n : ℕ
  graph : SimpleGraph (Fin n)
  nuig : IsNUIG graph
  input_le : a ≤ n
  output_le : b ≤ n
  input_clique : ∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < a → i ≠ j → graph.Adj i j
  output_clique : ∀ i j : Fin n, n - b ≤ (i : ℕ) → n - b ≤ (j : ℕ) → i ≠ j → graph.Adj i j

namespace MarkedNUIG

variable {a b c : ℕ}

/-- A word realizes any marked NUIG; this choice affects no tableau matrix. -/
def word (G : MarkedNUIG a b) : Word a b := by
  classical
  exact (word_of_nuig G.nuig a b G.input_le G.output_le G.input_clique G.output_clique).choose

lemma word_spec (G : MarkedNUIG a b) : ∃ h : Word.nv G.word = G.n,
    (∀ u v, Word.adj G.word u v ↔ G.graph.Adj (Fin.cast h u) (Fin.cast h v)) ∧
    (∀ r, (Word.inp G.word r : ℕ) = r) ∧
    (∀ s, (Word.mark G.word s : ℕ) = G.n - b + s) := by
  classical
  exact (word_of_nuig G.nuig a b G.input_le G.output_le G.input_clique G.output_clique).choose_spec

/-- The matrix defined directly by tableaux on this graph. -/
def matrix (N : ℕ) (G : MarkedNUIG a b) : Matrix (Inj N b) (Inj N a) (KN N) :=
  hikMat N G.graph (Fin.castLE G.input_le) (fun s => ⟨G.n - b + s, by have := G.output_le; omega⟩)

lemma matrix_eq_word (N : ℕ) (G : MarkedNUIG a b) : G.matrix N = Word.tabMat N G.word := by
  obtain ⟨h, hadj, hi, ho⟩ := G.word_spec
  rw [← Word.hikMat_eq_tabMat]
  ext o i
  unfold matrix hikMat
  rw [hikSum_cast h _ _ hadj _ (Fin.castLE G.input_le)
    (fun r => Fin.ext (by simp [hi])) _ (fun s => ⟨G.n - b + s, by have := G.output_le; omega⟩)
    (fun s => Fin.ext (by simp [ho]))]

/-- Regard the graph of a word as a marked NUIG. -/
def ofWord (w : Word a b) : MarkedNUIG a b where
  n := Word.nv w
  graph := Word.graph w
  nuig := Word.graph_isNUIG w
  input_le := Word.a_le_nv w
  output_le := Word.level_le_nv w
  input_clique := by
    intro i j hi hj hne
    have hei : Word.inp w ⟨i, hi⟩ = i := Fin.ext (Word.inp_val w _)
    have hej : Word.inp w ⟨j, hj⟩ = j := Fin.ext (Word.inp_val w _)
    -- Inputs retain their initial clique.
    have H : ∀ {a b} (w : Word a b) (r s : Fin a), r ≠ s →
        Word.adj w (Word.inp w r) (Word.inp w s) := by
      intro a b w
      induction w with
      | nil => exact fun _ _ h => h
      | M w ih => simpa only [Word.inp, Word.adj, extendAdj_cc] using ih
      | D w ih => exact ih
    rw [← hei, ← hej]
    exact H w _ _ (fun he => hne (Fin.ext (congrArg (fun z : Fin a => (z : ℕ)) he)))
  output_clique := by
    intro i j hi hj hne
    have hb := Word.level_le_nv w
    let r : Fin b := ⟨(i : ℕ) - (Word.nv w - b), by have := i.2; omega⟩
    let s : Fin b := ⟨(j : ℕ) - (Word.nv w - b), by have := j.2; omega⟩
    have hr : Word.mark w r = i := Fin.ext (by rw [Word.mark_val]; dsimp [r]; omega)
    have hs : Word.mark w s = j := Fin.ext (by rw [Word.mark_val]; dsimp [s]; omega)
    rw [← hr, ← hs]
    exact Word.mark_clique w r s (by intro he; rw [he, hs] at hr; exact hne hr.symm)

lemma matrix_ofWord (N : ℕ) (w : Word a b) : (ofWord w).matrix N = Word.tabMat N w := by
  rw [← Word.hikMat_eq_tabMat]
  have hi : Fin.castLE (Word.a_le_nv w) = Word.inp w :=
    funext fun r => Fin.ext (Word.inp_val w r).symm
  have ho : (fun s : Fin b => (⟨Word.nv w - b + s, by
      have := Word.level_le_nv w; have := s.2; omega⟩ : Fin (Word.nv w))) = Word.mark w :=
    funext fun r => Fin.ext (Word.mark_val w r).symm
  dsimp only [matrix, ofWord]
  rw [hi, ho]

/-- Product of arbitrary marked NUIGs. `Word.adj_comp`, `Word.comp_overlap` and
`Word.comp_cover` identify this with gluing along the common boundary clique. -/
def comp (G : MarkedNUIG b c) (H : MarkedNUIG a b) : MarkedNUIG a c :=
  ofWord (Word.comp H.word G.word)

/-- **Lemma `tableau-mult`** for two arbitrary marked NUIGs. -/
theorem tableau_mult (N : ℕ) (G : MarkedNUIG b c) (H : MarkedNUIG a b) :
    (G.comp H).matrix N = G.matrix N * H.matrix N := by
  rw [comp, matrix_ofWord, Word.tabMat_comp, matrix_eq_word, matrix_eq_word]

end MarkedNUIG

end ProperCircularArc
