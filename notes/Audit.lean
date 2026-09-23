import LatentError.Statements.Main
import LatentError.Statements.Conditional
import LatentError.Facts.Unconditional
import LatentError.Lemmas.NonVacuity

open PCError

#print axioms PCError.cor2_realized_duality
#print axioms PCError.cor3_large_n
#print axioms PCError.cor3_remark_independent_factors
#print axioms PCError.corollary1_aggregate
#print axioms PCError.eq25_projection_norms
#print axioms PCError.exact_split
#print axioms PCError.lemma1_gram_duality
#print axioms PCError.lemma2_i_eigenpair_convergence
#print axioms PCError.lemma2_ii_sign_pinning
#print axioms PCError.lemma3_change_of_basis
#print axioms PCError.lemma4_specific_concentration
#print axioms PCError.lemma5_uncorrelated
#print axioms PCError.lemma6_indeterminacy
#print axioms PCError.prop1_principal_coordinates
#print axioms PCError.prop2_remark
#print axioms PCError.prop2_systematic_limits
#print axioms PCError.prop3_b_frobenius_identity
#print axioms PCError.prop3_observable_dual
#print axioms PCError.theorem1_error_decomposition
#print axioms PCError.theorem2_observable_floor
#print axioms PCError.theorem3_rotation_error_not_estimable
#print axioms PCError.thm1Limit_snr
#print axioms PCError.joint_to_conditional
#print axioms PCError.tower_upgrade

-- the three background facts, now proved
#print axioms PCError.fact1_slln
#print axioms PCError.fact2_weyl
#print axioms PCError.fact3_eigCont
-- headline results with the facts discharged
#print axioms PCError.theorem1_error_decomposition_unconditional
#print axioms PCError.theorem2_observable_floor_unconditional
#print axioms PCError.theorem3_rotation_error_not_estimable_unconditional
#print axioms PCError.corollary1_aggregate_unconditional

-- non-vacuity: the hypothesis bundles are inhabited
#print axioms PCError.loadingParams_nonempty
#print axioms PCError.assumptions56_satisfiable
#print axioms PCError.noiseModel_nonempty
