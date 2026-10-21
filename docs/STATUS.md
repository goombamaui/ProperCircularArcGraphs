# Status

Every numbered result of the paper is formalized, except as noted below. Nothing uses `sorry`, and
[Verification.lean](../Verification.lean) checks that the main theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`.

| Paper | Status | Lean |
| --- | --- | --- |
| Definitions, Lemma `color`, Lemma `word` | done | `colMatP_eq_colorSum`, `chromSym_trGraph`, `word_of_nuig` |
| Proposition `identities`, Equation (R), Theorem `main` | done | `TableauIdentities.lean`, `main_intertwine` |
| Section 6: Lemma `vanish`, Proposition `finite` | done | `vanish`, `UN_M`, `UN_D`, `UN_surjective` |
| Lemma `pca` (unrolling a proper circular-arc model) | done | `PCAModel.exists_sorted`, `SortedModel.iso` |
| Theorem `pca` | done | `pca_graph_epositive` (arc models), `pca_epositive` (traces of marked NUIGs) |
| Theorem `stanstem` | done | `nuig_epositive` |
| Hikita's rule is well defined (remark after Definition `hikita-rule`) | done | `isBuild_of_hwt_ne_zero` |
| Definitions `weight`, `graph-tableau` | done | `hwt`, `hikSum`, `hikMat` |
| Proposition `tableau-word`, Lemma `tableau-mult` | done for one marked clique at a time | `hikSum_M`, `hikSum_D` |
| Theorem `tableau` | done | `Word.hikMat_eq_tabMat`, `tableau_nuig` |
| Theorem `pca-formula` | done | `pca_formula`, `pca_formula'`, `pca_formula_tableaux` |
| Theorem `hikita` (cited, `q = 1`) | weight form done | `hikita_weight`, `hikita_tableaux` |
| Examples (`P_3`, the 6-vertex graph, the 7-vertex NUIG) | not planned | |

## Differences from the paper

* **Finite alphabets.** Every statement about chromatic symmetric functions is proved in
  `x_1, …, x_N` for every `N`. `e`-positivity in infinitely many variables follows from the case
  `N ≥ n`, because the `e_λ` with `λ_1 ≤ N` are linearly independent in `N` variables. This step is
  standard and is not formalized.
* **Lemma `tableau-mult`.** The paper proves Theorem `tableau` by splitting `\bG` into marked
  cliques and applying Lemma `tableau-mult`. The formalization proves the multiplicativity for one
  marked clique at a time (`hikSum_M`, `hikSum_D`) and inducts on the word. The general product
  `\bG + \bH` of two marked graphs is not defined in Lean.
* **Tableaux as column assignments.** A tableau built from `T_j` is recorded by the columns of its
  vertices (`IsBuild`). `isBuild_of_hwt_ne_zero` shows that assignments of nonzero weight are
  tableaux, so the sums over all assignments in `Hikita.lean` are sums over tableaux.
* **Hikita's theorem.** The formalization gives Hikita's formula in weight form,
  `X_G = ∑_T w(T ∣ ∅, G)`. Rewriting the weights as probabilities (Equation `weight-pr`) is a
  telescoping product over the rows of `T` and is not formalized.
* **Arc models.** A proper circular-arc model consists of closed arcs `[s, s + ℓ]` of `ℝ/ℤ` with
  `0 ≤ ℓ < 1`, none containing another (`PCAModel`).
