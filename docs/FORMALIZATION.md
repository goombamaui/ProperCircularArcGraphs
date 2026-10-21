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
