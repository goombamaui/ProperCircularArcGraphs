# ProperCircularArcGraphs

Lean 4 formalization accompanying Aarush Vailaya,
*Proper circular arc graphs are e-positive* ([manuscript](paper/ProperCircularArcGraphs.pdf)).
It proves that the chromatic symmetric function of every proper circular arc graph is
`e`-positive. It does this by constructing the paper's change of basis `U_k` between tableau
matrices and colour matrices. It also proves the explicit tableau formula of Section 7. As a
special case it gives a new proof that natural unit interval graphs are `e`-positive.

## Results

| Paper | Statement | Lean entry point |
| --- | --- | --- |
| Theorem `main` | `U_k M_{k-1} = M̂_{k-1} U_{k-1}`, `D̂_k U_k = U_{k-1} D_k` | [`main_intertwine`](ProperCircularArc/Intertwine.lean) |
| Proposition `identities` | swap, swap-delete, last-swap, swap-square (tableau and colour sides) | [TableauIdentities.lean](ProperCircularArc/TableauIdentities.lean), [Color.lean](ProperCircularArc/Color.lean) |
| Equation (R) | `R_k b_{a,w}` | [`Rop_cons`](ProperCircularArc/Tableau.lean) |
| Equation (rank-span) | induction on the rank | [`span_induction`](ProperCircularArc/Span.lean) |
| Block system | invertibility (null-vector argument) | [`cauchy_null`](ProperCircularArc/Block.lean) |
| Section 6 | `U_k^{(N)}` well defined (denominators `e_j`, `j ≤ N`) | [`U_adm`](ProperCircularArc/Admissible.lean) |
| Lemma `vanish` | `U_k^{(N)} b_σ = 0` if `N + 1 ∈ σ` | [`vanish`](ProperCircularArc/FiniteU.lean) |
| Proposition `finite` | finite intertwining, `U_k^{(N)}` invertible for `k ≤ N` | [`UN_M`, `UN_D`](ProperCircularArc/FiniteU.lean), [`UN_surjective`](ProperCircularArc/Invertible.lean) |
| Lemma `color` | colour matrices count proper colourings; trace | [`colMatP_eq_colorSum`](ProperCircularArc/Graphs.lean), [`chromSym_trGraph`](ProperCircularArc/TraceGraph.lean) |
| Lemma `word` | marked NUIGs are words in `M̂`, `D̂` | [`word_of_nuig`](ProperCircularArc/NUIG.lean) |
| Lemma `pca` | unrolling a proper circular-arc model into a marked NUIG | [`PCAModel.exists_sorted`, `SortedModel.iso`](ProperCircularArc/Arcs.lean) |
| Theorem `pca` | every proper circular arc graph is `e`-positive; `X_Γ(x_1,…,x_N) = tr M_G^{(N)}` | [`pca_graph_epositive`](ProperCircularArc/Arcs.lean), [`pca_epositive`](ProperCircularArc/PCATrace.lean), [`Word.pca_trace`](ProperCircularArc/MainWord.lean) |
| Theorem `stanstem` | NUIGs are `e`-positive | [`nuig_epositive`](ProperCircularArc/NUIG.lean) |
| Hikita's rule | a vertex can be placed whenever its factor `A` is nonzero | [`isBuild_of_hwt_ne_zero`](ProperCircularArc/Tableaux.lean) |
| Theorem `tableau` | `𝓜_\bG^{(N)} = M_\bG^{(N)}` | [`Word.hikMat_eq_tabMat`](ProperCircularArc/Hikita.lean), [`tableau_nuig`](ProperCircularArc/Tableaux.lean) |
| Theorem `pca-formula` | explicit tableau formula for `X_Γ` | [`pca_formula`, `pca_formula'`](ProperCircularArc/Hikita.lean), [`pca_formula_tableaux`](ProperCircularArc/Tableaux.lean) |
| Theorem `hikita` (`q = 1`) | `X_G = ∑_T w(T ∣ ∅, G)` | [`hikita_weight`](ProperCircularArc/Hikita.lean), [`hikita_tableaux`](ProperCircularArc/Tableaux.lean) |

Stable alphabets, graph products, probabilities, and examples are developed in
[Infinite.lean](ProperCircularArc/Infinite.lean),
[Gluing.lean](ProperCircularArc/Gluing.lean), [Probability.lean](ProperCircularArc/Probability.lean),
[Examples.lean](ProperCircularArc/Examples.lean), and
[ExamplesMatrices.lean](ProperCircularArc/ExamplesMatrices.lean).

`e`-positivity is proved in the ring of symmetric functions, represented by polynomials in
formal elementary generators. One polynomial with nonnegative rational coefficients
specializes to the chromatic symmetric function in every finite alphabet. The colourings
and the tableau side are defined independently and proved to agree.

[Verification.lean](Verification.lean) prints the axioms of the main theorems. All of them
depend only on `propext`, `Classical.choice` and `Quot.sound`; the project uses no `sorry` and
no custom axioms.

## Status

The formalization includes infinitely many variables, products of arbitrary marked NUIGs,
Hikita's probability formula, and the worked CSF and matrix examples.
See [docs/STATUS.md](docs/STATUS.md) for the precise representations and theorem names.

## Build

Pinned to Lean **4.34.0** and the Mathlib revision in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

## Manuscript

- **Version 1:** the original [arXiv submission](https://arxiv.org/abs/2609.33124v1),
  September 27, 2026 ([PDF](paper/v1/ProperCircularArcGraphs.pdf),
  [TeX](paper/v1/ProperCircularArcGraphs.tex)).
- **Version 2:** the current manuscript, October 21, 2026
  ([PDF](paper/ProperCircularArcGraphs.pdf), [TeX](paper/ProperCircularArcGraphs.tex)).

## Layout

- [ProperCircularArc/](ProperCircularArc): the formalization, one file per step of the paper.
- [Verification.lean](Verification.lean): axiom audit.
- [paper/](paper): the current manuscript and the original version in `v1/`.
- [docs/](docs): design notes and the correspondence with the paper.
- [scripts/](scripts): the exact Sympy prototype and the generator for Lean example certificates.
