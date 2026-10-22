# Formalization notes

## The infinite-colour model

The paper constructs `U_k` with infinitely many colours, `N = ∞`, where a colour vector is a
formal sum `∑_i F(x_{i_1}, …, x_{i_k}) b̂_i` with `F` divisible by `x_{i_1} ⋯ x_{i_k}`. We record
such a vector by the polynomial `G = F / (y_1 ⋯ y_k)` in `k` variables
([Color.lean](../ProperCircularArc/Color.lean)). Its coefficients lie in

  `Lam = ℚ[E_1^{±1}, E_2^{±1}, …]`

([Laurent.lean](../ProperCircularArc/Laurent.lean)), where the `E_j` are formal, algebraically
independent elementary symmetric functions. The colour operators become:

* `M̂`: `G ↦ G` in one more variable;
* `D̂`: `y_1^m ↦ P_{m+1} - ∑_{r ≥ 2} y_r^{m+1}`, where `P_m` are the power sums written in the `E_j`
  by Newton's identities ([PowerSum.lean](../ProperCircularArc/PowerSum.lean));
* `R̂`: `G ↦ y_k G(y_k, y_1, …, y_{k-1})`;
* `Ŝ_s`: swap two variables.

The hatted identities of Proposition `identities` follow from three facts: `D̂` commutes with
permutations of the non-fresh variables, `D̂` is linear over the non-fresh variables, and
`M̂D̂ - D̂M̂ = R̂`.

## Tableau indices

Tableau indices are tuples `σ : Fin k → ℕ`. Every operator kills tuples with a repeated or zero
entry, except `S_s`, which acts as the identity on them so that `S_s² = 1` holds as an identity of
linear maps ([Tableau.lean](../ProperCircularArc/Tableau.lean)).

The coefficient `A(y ∣ σ)` is written as one product,
`c(y) ∏_{t ∈ σ, t ≠ y-1} (y - t)/(y - 1 - t)`, and Equation (ratio) is
[`Acoef_insert`](../ProperCircularArc/Coefficients.lean). The paper's "remaining cases are
similar" are done in full in [ScalarIdentities.lean](../ProperCircularArc/ScalarIdentities.lean).

## The construction of `U_k`

* Level 1 uses the paper's explicit formula `U1fn`.
* For level `k + 2`, the columns `U b_{w,y}` are defined by well-founded recursion on the rank
  `r(w, y)`, which is encoded as a number in base `k + 2`
  ([Rank.lean](../ProperCircularArc/Rank.lean)).
* The block system for `y ∈ T(w)` is solved with an explicit two-sided inverse
  ([Block.lean](../ProperCircularArc/Block.lean)). The free equation is solved directly.

Equations (M) and (R) then hold by construction
([Construction.lean](../ProperCircularArc/Construction.lean)). Equations (S) and (D) are proved
by the paper's induction on the rank, using
[`span_induction`](../ProperCircularArc/Span.lean).

## Finitely many colours

* **Specialization.** `E_j ↦ e_j(x_1, …, x_N)`, which is `0` for `j > N`, is an algebra map on
  the Laurent monomials whose exponents are nonnegative beyond `N`
  ([Specialize.lean](../ProperCircularArc/Specialize.lean)).
* **Admissibility.** The coefficients of `U_k b_σ` lie in this ring whenever the entries of `σ`
  are at most `N + 1` ([`U_adm`](../ProperCircularArc/Admissible.lean)). This is the paper's remark
  that only `e_j` with `j < max σ` is inverted.
* **Colour vectors.** With `N` colours they are functions on embeddings `Fin k ↪ Fin N`
  ([FiniteColor.lean](../ProperCircularArc/FiniteColor.lean)).
* **Invertibility.** `U_k^{(N)}` is invertible by the paper's argument
  ([Invertible.lean](../ProperCircularArc/Invertible.lean)): `R̂^{k+1}` is multiplication by
  `x_{j_1} ⋯ x_{j_{k+1}}`, followed by a Lagrange (Vandermonde) step.

## Positivity

The finite tableau matrices are specializations of matrices over
`ℚ[E_1^{±1}, …, E_N^{±1}]` whose entries have nonnegative coefficients
([TraceEpos.lean](../ProperCircularArc/TraceEpos.lean)). Their specialization is injective,
because `e_1, …, e_N` are algebraically independent (`esymmAlgHom_injective`). Combined with the
fundamental theorem of symmetric polynomials, this gives `e`-positivity
([Positivity.lean](../ProperCircularArc/Positivity.lean)).

## Graphs

A word in `M̂`, `D̂` (last letter outermost) builds a marked NUIG
([Graphs.lean](../ProperCircularArc/Graphs.lean)), and its colour matrix counts proper colourings
(Lemma `color`). The trace graph identifies outputs with inputs
([TraceGraph.lean](../ProperCircularArc/TraceGraph.lean)). Lemma `word` constructs the word of
any marked NUIG ([NUIG.lean](../ProperCircularArc/NUIG.lean)).

## Circular-arc models

A model assigns to each vertex a closed arc `[s, s + ℓ]` of `ℝ/ℤ` with `0 ≤ ℓ < 1`
([Arcs.lean](../ProperCircularArc/Arcs.lean)). Lemma `pca` is proved as follows:

1. Reduce the starting points modulo `1`. They are distinct, since otherwise the shorter arc
   would lie inside the longer one.
2. Sort the arcs by starting point. The arcs through `1` (with `s + ℓ ≥ 1`) come last, since an
   earlier arc through `1` would contain a later arc that does not pass through `1`.
3. Unroll. Every arc gives the interval `A_v = [s, s + ℓ]`, and every arc through `1` also gives
   `B_v = A_v - 1`. Sorted by left endpoint, the `k` intervals `B_v` come first and the `k`
   intervals `A_v` of arcs through `1` come last.
4. Right endpoints are sorted as well, since otherwise one arc would contain another. Hence
   the intervals form a NUIG, and the first and last `k` intervals form cliques (they contain
   `0` and `1`).
5. `B_v` and `A_v` are disjoint because `ℓ < 1`. Identifying them gives back the arc graph,
   because any point of an arc can be moved into `[0, 1)`.

## Hikita's tableaux

A tableau built from `T_j` is recorded by the columns of its vertices
([Hikita.lean](../ProperCircularArc/Hikita.lean)). The weight of Definition `weight` is
`hwt`, and the matrix of Definition `graph-tableau` is `hikMat`. Theorem `tableau` is proved
by induction on the word. Adding a vertex adjacent to the marked vertices multiplies by
`M_k^{(N)}` (`hikSum_M`). Forgetting a marked vertex multiplies by `D_k^{(N)}` (`hikSum_D`),
because assignments that put two adjacent vertices in the same column have weight `0`.
[Tableaux.lean](../ProperCircularArc/Tableaux.lean) shows that assignments of nonzero weight are
genuine tableau builds, which is the remark after Definition `hikita-rule`.


## Stable alphabets and symmetric functions

[Infinite.lean](../ProperCircularArc/Infinite.lean) defines the ring of symmetric functions
as `Symm = ℚ[E₁,E₂,…]`, using zero-based indices for the generators. Restriction of colour
variables commutes with both the chromatic sum and the elementary symmetric polynomials.
The elementary expansion of a homogeneous CSF is weighted homogeneous, with `weight E_j = j`.
Thus a CSF of degree `n` uses only `E₁,…,E_n`. Algebraic independence in `n` variables then
identifies the expansion in every larger alphabet, and restriction gives every smaller
alphabet, including the empty one. This proves `stable_epositive` and the infinite-alphabet
positivity theorems. The specialization maps are jointly injective.

## General marked products

[Gluing.lean](../ProperCircularArc/Gluing.lean) defines `MarkedNUIG` and its product.
The word realization of a graph is supplied by the existing `word_of_nuig` theorem.
Composition identifies the inputs of the second word with the outputs of the first;
`comp_overlap`, `comp_cover`, and `adj_comp` prove the vertex and edge description of this
clique gluing. `matrix_eq_word` transports the independently defined Hikita matrix to its
word, and `MarkedNUIG.tableau_mult` proves Lemma `tableau-mult` for arbitrary factors.

## Probability normalization of weights

[Probability.lean](../ProperCircularArc/Probability.lean) defines `hprob` by the paper's
product `∏ A(y|σ)/y`. A column of height `h_y` contributes `(y e_y/e_{y-1})^{h_y}` to the
shape potential. Each newly added box multiplies this potential by `y e_y/e_{y-1}`,
and along a row the product telescopes to `λ!e_λ`. `weight_pr_rows` proves Equation
`weight-pr` for arbitrary initial and final shapes. `hikita_probability_tableaux` and
`hikita_probability_rows` give the probability form of Hikita's theorem.

## Exact example certificates

[Examples.lean](../ProperCircularArc/Examples.lean) checks the graph words and all four
CSF polynomials (`P₃`, `P₂`, the six-vertex PCA graph, and the seven-vertex NUIG) in every
alphabet. [ExamplesMatrices.lean](../ProperCircularArc/ExamplesMatrices.lean) checks the
three displayed matrices in Example `p3`. The CSF computations use the general weighted
deletion-contraction identity in [DeletionContraction.lean](../ProperCircularArc/DeletionContraction.lean).
The generated certificates in [ExamplesCertificates.lean](../ProperCircularArc/ExamplesCertificates.lean)
are ordinary Lean proofs using deletion-contraction, finite decisions, and `ring`.
They can be regenerated with `python3 scripts/generate_examples.py` (requires Sympy);
Python and Sympy are not needed to build or verify the Lean proofs.
