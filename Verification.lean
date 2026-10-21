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
