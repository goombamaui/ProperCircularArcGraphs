# ProperCircularArc

Lean 4 formalization accompanying Aarush Vailaya,
*Proper circular arc graphs are e-positive* ([manuscript](paper/ProperCircularArcGraphs.pdf)).
It proves that the chromatic symmetric function of a proper circular arc graph, presented as
the trace of a marked natural unit interval graph, is `e`-positive. It does this by
constructing the paper's change of basis `U_k` between tableau matrices and colour matrices.
As a special case it gives a new proof that natural unit interval graphs are `e`-positive.

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
| Theorem `pca` | `X_{tr G}(x_1,…,x_N) = tr M_G^{(N)}`, `e`-positive | [`Word.pca_trace`, `Word.pca_epositive`](ProperCircularArc/MainWord.lean), [`pca_epositive`](ProperCircularArc/PCATrace.lean) |
| Theorem `stanstem` | NUIGs are `e`-positive | [`nuig_epositive`](ProperCircularArc/NUIG.lean) |

`e`-positivity is stated for every finite alphabet `x_1, …, x_N`: the chromatic symmetric
function `X(x_1, …, x_N)` equals `P(e_1, …, e_N)` for a polynomial `P` with nonnegative
rational coefficients. The colourings and the tableau side are defined independently
and proved to agree.

[Verification.lean](Verification.lean) prints the axioms of the main theorems. All of them
depend only on `propext`, `Classical.choice` and `Quot.sound`; the project uses no `sorry` and
no custom axioms.

## Status

Formalized: Sections 3–6 of the paper and Theorem `pca` for traces of marked natural unit
interval graphs (the combinatorial form of the theorem). In progress: Lemma `pca` (unrolling a
geometric circular-arc model into a marked NUIG) and Section 7 (Hikita's rule and Theorem
`pca-formula`). See [docs/STATUS.md](docs/STATUS.md).

## Build

Pinned to Lean **4.34.0** and the Mathlib revision in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

## Layout

- [ProperCircularArc/](ProperCircularArc): the formalization, one file per step of the paper.
- [Verification.lean](Verification.lean): axiom audit.
- [paper/](paper): the manuscript.
- [docs/](docs): design notes and the correspondence with the paper.
- [scripts/prototype.py](scripts/prototype.py): an exact sympy prototype of the symbolic model,
  used to test the formulas before formalizing them.
