import ProperCircularArc

/-!
# Axiom audit

Every theorem below should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Theorem `main` (infinite colours): the change of basis intertwines `M`, `R`, `S`, `D`.
#print axioms ProperCircularArc.main_intertwine
#print axioms ProperCircularArc.U_M
#print axioms ProperCircularArc.U_R
#print axioms ProperCircularArc.U_S'
#print axioms ProperCircularArc.U_D

-- Proposition `identities` (tableau and colour sides).
#print axioms ProperCircularArc.Rop_cons
#print axioms ProperCircularArc.Dop_Rop
#print axioms ProperCircularArc.Sop_Mop_Rop
#print axioms ProperCircularArc.Sop_Mop_Mop
#print axioms ProperCircularArc.Sop_Rop_Rop_apply
#print axioms ProperCircularArc.Mh_Dh_sub_Dh_Mh
#print axioms ProperCircularArc.Dh_Rh
#print axioms ProperCircularArc.Sh_Mh_Rh

-- Equation (rank-span) and the block system.
#print axioms ProperCircularArc.span_induction
#print axioms ProperCircularArc.cauchy_null

-- Section 6: finitely many colours.
#print axioms ProperCircularArc.U_adm
#print axioms ProperCircularArc.vanish
#print axioms ProperCircularArc.UN_M
#print axioms ProperCircularArc.UN_D
#print axioms ProperCircularArc.UN_surjective
#print axioms ProperCircularArc.Word.trace_tabMat
#print axioms ProperCircularArc.epos_of_nonneg

-- Lemma `color` and the trace graph.
#print axioms ProperCircularArc.Word.colMatP_eq_colorSum
#print axioms ProperCircularArc.Word.chromSym_trGraph

-- Lemma `word`.
#print axioms ProperCircularArc.word_of_nuig

-- Theorems `pca` and `stanstem`.
#print axioms ProperCircularArc.Word.pca_trace
#print axioms ProperCircularArc.Word.pca_epositive
#print axioms ProperCircularArc.Word.stanstem_epositive
#print axioms ProperCircularArc.nuig_epositive
#print axioms ProperCircularArc.pca_epositive

-- Lemma `pca` (unrolling an arc model) and Theorem `pca` for proper circular arc graphs.
#print axioms ProperCircularArc.SortedModel.iso
#print axioms ProperCircularArc.PCAModel.exists_sorted
#print axioms ProperCircularArc.pca_graph_epositive

-- Section 7: Theorem `tableau`, Theorem `pca-formula`, Theorem `hikita` (weight form).
#print axioms ProperCircularArc.Word.hikMat_eq_tabMat
#print axioms ProperCircularArc.pca_formula
#print axioms ProperCircularArc.pca_formula'
#print axioms ProperCircularArc.hikita_weight

-- Hikita's rule is well defined; the formulas are sums over tableaux.
#print axioms ProperCircularArc.isBuild_of_hwt_ne_zero
#print axioms ProperCircularArc.pca_formula_tableaux
#print axioms ProperCircularArc.hikita_tableaux
#print axioms ProperCircularArc.tableau_nuig

-- Remaining paper statements: stable alphabets, arbitrary graph products, and probabilities.
#print axioms ProperCircularArc.stable_epositive
#print axioms ProperCircularArc.chromSymInf_epositive
#print axioms ProperCircularArc.nuig_epositive_infinite
#print axioms ProperCircularArc.pca_graph_epositive_infinite
#print axioms ProperCircularArc.Word.adj_comp
#print axioms ProperCircularArc.Word.comp_overlap
#print axioms ProperCircularArc.MarkedNUIG.tableau_mult
#print axioms ProperCircularArc.weight_pr
#print axioms ProperCircularArc.weight_pr_rows
#print axioms ProperCircularArc.hikita_probability_tableaux
#print axioms ProperCircularArc.hikita_probability_rows

-- Exact worked examples and the graphs/words used by their certificates.
#print axioms ProperCircularArc.weightedCSF_delete_contract
#print axioms ProperCircularArc.Examples.path3_csf
#print axioms ProperCircularArc.Examples.path2_csf
#print axioms ProperCircularArc.Examples.six_csf
#print axioms ProperCircularArc.Examples.seven_csf
#print axioms ProperCircularArc.Examples.pathWord_graph
#print axioms ProperCircularArc.Examples.sixWord_trace
#print axioms ProperCircularArc.Examples.sevenWord_graph
#print axioms ProperCircularArc.Examples.six_tableau
#print axioms ProperCircularArc.Examples.seven_tableau
#print axioms ProperCircularArc.Examples.path_step_matrix
#print axioms ProperCircularArc.Examples.path_square_matrix
#print axioms ProperCircularArc.Examples.path_U_entry
#print axioms ProperCircularArc.Examples.path_U_matrix
#print axioms ProperCircularArc.specializeSymm_jointly_injective
