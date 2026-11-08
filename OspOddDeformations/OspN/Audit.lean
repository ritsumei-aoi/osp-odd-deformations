import OspOddDeformations.OspN.Controls
import OspOddDeformations.OspN.ControlN1
import OspOddDeformations.OspN.SourceUniqueness
import OspOddDeformations.OspN.Multi.Statements
import OspOddDeformations.OspN.Multi.TierB
import OspOddDeformations.OspN.Multi.ThetaSeries
import OspOddDeformations.OspN.Multi.Remarks
import OspOddDeformations.OspN.IndependenceR
import OspOddDeformations.OspN.Normalization
import OspOddDeformations.OspN.Special
import OspOddDeformations.OspN.Multi.Conjugation
import OspOddDeformations.OspN.Presented.Recovery
import OspOddDeformations.OspN.Presented.MultiUntwist
import OspOddDeformations.OspN.Presented.MultiRecovery
import OspOddDeformations.OspN.Presented.BracketAll
import OspOddDeformations.OspN.GroupB.NormalForm
import OspOddDeformations.OspN.GroupB.AllPrimitives
import OspOddDeformations.OspN.GroupB.Complex
import OspOddDeformations.OspN.GroupB.ThetaStarExp
import OspOddDeformations.OspN.GroupB.D21

/-!
# Axiom audit of `OspOddDeformations.OspN`

One `#print axioms` for every headline declaration of the development (for every `N`: the laws of
`[·,·]_0`, `Γ_β = δh̃`, the intertwining, `base_realization`, `recovery`, uniqueness, `f_β`, the
identification `rho_*`; the statements for multiple odd parameters; the presented algebras), for
the `C(2)` control, and for every declaration of the `N = 1` control against `osp-triviality`
(`ControlN1.lean`). A build prints each result: no `sorryAx`, standard axioms only.
-/

namespace OspOddDeformations
namespace OspN

#print axioms bracket0Basis_degree
#print axioms bracket0Basis_super_skew
#print axioms evenIdx_basis_card_1_1
#print axioms Gamma_eq_delta_hTilde
#print axioms intertwining
#print axioms A0Grading_gradedAlgebra
#print axioms base_realization
#print axioms recovery
#print axioms recovery_delta
#print axioms X0A0_linearIndependent
#print axioms iota0_injective
#print axioms kappa_iota0_injective_inj
#print axioms kappa_iota0_injective
#print axioms recovery_unique
#print axioms recovery_unique_delta
#print axioms evenC2_GammaBasis_SF
#print axioms evenC2_GammaBasis_FF
#print axioms evenC2_GammaBasis_LS
#print axioms Zbeta_odd
#print axioms v_sum_J
#print axioms v_sum_J_neg
#print axioms bracket0_Fof_Lof
#print axioms fBeta_L
#print axioms bracket0_Fof_Fof
#print axioms g_dual_delta
#print axioms fBeta_F
#print axioms fBeta_S
#print axioms Gamma_eN_eN
#print axioms delta_eN_eN
#print axioms fBeta_zero
#print axioms fBeta_add
#print axioms fBeta_smul
#print axioms TBetaF_eq
#print axioms falsePart_TBetaF
#print axioms TBetaF_zero
#print axioms TBetaF_add
#print axioms TBetaF_smul
#print axioms TBetaF_sum
#print axioms TBetaF_sum'
#print axioms TBetaF_eR_false
#print axioms TBetaF_eR_true
#print axioms coefAB_mul
#print axioms coefAB_comm_coefAB
#print axioms cdwv_identity
#print axioms iota0_bracket0_homog
#print axioms eN_homog
#print axioms bracket0_homog_right
#print axioms delta_ad_eq_zero_basis
#print axioms delta_ad_eq_zero
#print axioms Gamma_eq_delta_fBeta_basis
#print axioms Gamma_eq_delta_fBeta
#print axioms intertwining_fBeta_basis
#print axioms intertwining_fBeta
#print axioms eN_eq_algebraMap
#print axioms algebraMap_smul_eq
#print axioms isConstAt_zero
#print axioms isConstAt_eN
#print axioms isConstAt_add
#print axioms isConstAt_neg
#print axioms isConstAt_sub
#print axioms isConstAt_smul
#print axioms isConstAt_Sof
#print axioms isConstAt_to_algebraMap
#print axioms bracket0Basis_const
#print axioms Bpair_eNM_eNM
#print axioms Bpair_add_left
#print axioms Bpair_smul_left
#print axioms Bpair_zero_left
#print axioms Bpair_add_right
#print axioms Bpair_smul_right
#print axioms Bpair_zero_right
#print axioms Bpair_neg_left
#print axioms Bpair_neg_right
#print axioms Bpair_sub_left
#print axioms Bpair_sub_right
#print axioms gsign_zero_left
#print axioms rho_ospCond
#print axioms eNM_I_eq
#print axioms J_diag_ne_zero
#print axioms L_indep_other
#print axioms L_indep_full
#print axioms g_dual_right
#print axioms eNM_K_eq
#print axioms S_indep_other
#print axioms S_indep_full
#print axioms eNM_inl_inr_eq_zero
#print axioms F_indep_other
#print axioms F_indep_full
#print axioms rhoBasis_linearIndependent
#print axioms eNM_inr_inl_eq_zero
#print axioms rhoBasis_homogeneous
#print axioms Bpair_sum_left
#print axioms Bpair_sum_right
#print axioms rhoCombo_ospCond
#print axioms rhoCombo_homogeneous
#print axioms Homogeneous_sub
#print axioms ospCond_sub
#print axioms Bpair_eNM_inl
#print axioms cOdd_support
#print axioms cOdd_inl_inr
#print axioms cOdd_inl_inl
#print axioms rho_span_odd
#print axioms Bpair_eNM_inl_left
#print axioms S_block_antisym
#print axioms sym_sum_split
#print axioms cEven_S_inl_inl
#print axioms Bpair_eNM_inr
#print axioms Bpair_eNM_inr_left
#print axioms Idual_Idual
#print axioms J_dual_eq
#print axioms L_block_relation
#print axioms sym_sum_split_I
#print axioms J_Idual_left
#print axioms CFun_symm
#print axioms CFun_full_sum
#print axioms sym_sum_full_I
#print axioms cEven_L_inr_inr
#print axioms cEven_support
#print axioms cEven_inr_inr
#print axioms cEven_inl_inl
#print axioms rho_span_even
#print axioms rho_span
#print axioms bracket0BasisQ_antisymm
#print axioms rho_bracket_reversal
#print axioms Lof_ne_inr
#print axioms rhoBasis_Lof
#print axioms bracket0BasisQ_Lof_Lof
#print axioms rhoOp_Lof_Lof_inr
#print axioms rho_bracket_LL_inl
#print axioms rho_bracket_LL_inr
#print axioms rho_bracket_LL_inr_inl
#print axioms rho_bracket_LL
#print axioms rho_bracket_LS
#print axioms rhoBasis_Fof_inl
#print axioms rhoBasis_Fof_inr
#print axioms rhoBasis_Lof_inl_eq_zero
#print axioms bracket0BasisQ_Lof_Fof
#print axioms rhoOp_Lof_Fof_inl_inr
#print axioms rhoOp_Lof_Fof_inl_inl
#print axioms rhoOp_Lof_Fof_inr_zero
#print axioms rhoOp_Fof_Lof_inl_zero
#print axioms rhoOp_Fof_Lof_inr_inr_zero
#print axioms rhoOp_Fof_Lof_inr_inl
#print axioms rhoBasis_LF_rhs
#print axioms rho_bracket_LF_inl
#print axioms rho_bracket_LF_inr
#print axioms rho_bracket_LF
#print axioms rhoBasis_S_inl
#print axioms rhoBasis_S_inr_zero
#print axioms rhoOp_S_inr_zero
#print axioms rhoOp_S_S_inl_inl
#print axioms SofRho_inr_zero
#print axioms SofRho_inl_inl
#print axioms SofRho_inl_inr_zero
#print axioms bracket0BasisQ_S_S
#print axioms rho_sum_eN
#print axioms rho_sum_neg_eN
#print axioms bracket0BasisQ_Sof_apply
#print axioms rho_sum_Sof
#print axioms rhoBasis_SS_rhs
#print axioms rho_bracket_SS_inr
#print axioms rho_bracket_SS_inl
#print axioms rho_bracket_SS
#print axioms rhoOp_S_Fof_inl_zero
#print axioms rhoOp_Fof_S_inr_zero
#print axioms rhoOp_S_Fof_inr
#print axioms rhoOp_Fof_S_inl
#print axioms bracket0BasisQ_S_F
#print axioms rhoBasis_SF_rhs
#print axioms rho_bracket_SF_inl
#print axioms rho_bracket_SF_inr
#print axioms rho_bracket_SF
#print axioms rhoOp_Fof_Fof_inl
#print axioms rhoOp_Fof_Fof_inr
#print axioms bracket0BasisQ_F_F
#print axioms rhoBasis_FF_rhs
#print axioms rho_bracket_FF_inl
#print axioms rho_bracket_FF_inr
#print axioms rho_bracket_FF
#print axioms Lof_eq_sigma
#print axioms rho_bracket
#print axioms k0_eq_none
#print axioms IKey_index0nInvFun
#print axioms indexProdN1
#print axioms controlBasisEquivN1
#print axioms controlRingEquivN1
#print axioms controlTransportN1
#print axioms controlTransportN1_add
#print axioms controlTransportN1_neg
#print axioms controlTransportN1_smul
#print axioms controlTransportN1_eN
#print axioms qsmul_eq_Csmul_Pn
#print axioms controlBasisEquivN1_Lof
#print axioms controlBasisEquivN1_Fof
#print axioms control_N1_bracket
#print axioms controlTransportN1_smul_ring
#print axioms controlRingEquivN1_beta
#print axioms control_N1_gamma
#print axioms controlTransportN1_sum
#print axioms idx_even_N1
#print axioms idx_odd_N1
#print axioms control_N1_hTilde
#print axioms control_N1_fBeta

/-! ## Multiple odd parameters (coordinate level): the statements and the reduction -/

#print axioms Multi.gs_comm
#print axioms Multi.gs_cocycle
#print axioms Multi.gmul_assoc
#print axioms Multi.gsmul_gmul
#print axioms Multi.gmul_comm_of_even
#print axioms Multi.gs_self_singleton
#print axioms Multi.gs_singleton_anticomm
#print axioms Multi.bracketBetaMBasis_r1
#print axioms Multi.UM_bijective
#print axioms Multi.thetaHalf_spec
#print axioms Multi.uMat_parity
#print axioms Multi.intertwining_of_core
#print axioms Multi.UM_eq_comp
#print axioms Multi.thetaStar_bracket
#print axioms Multi.lift_intertwine
#print axioms Multi.vChi_bracket
#print axioms Multi.intertwining_multi
#print axioms Multi.VChi_comp
#print axioms Multi.TS_comm
#print axioms Multi.TProd_eq
#print axioms Multi.ThetaStar_comp
#print axioms Multi.UM_eq_ThetaStar_TProd
#print axioms Multi.ThetaStar_not_aut
#print axioms Multi.thetaSeries_spec
#print axioms Multi.intertwining_thetaSeries
#print axioms Multi.UM_thetaSeries_bijective
#print axioms Multi.thetaSeries_eq_thetaHalf
#print axioms Multi.T1_defect_Luv
#print axioms Multi.T1_not_intertwine
#print axioms Multi.TProd_not_intertwine
#print axioms Multi.ThetaStar_sub_one_not_derivation
#print axioms Multi.thetaG_spec
#print axioms iota0R_injective

#print axioms TBetaInv_TBeta
#print axioms TBeta_TBetaInv
#print axioms TBetaFInv_TBetaF
#print axioms TBetaF_TBetaFInv
#print axioms odd_eq_zero_of_ad_Lof
#print axioms fBeta_unique_vanishing_sp
#print axioms hTilde_Fof_ne_zero
#print axioms fBeta_Sof_ne_zero
#print axioms no_primitive_vanishing_sp_so
#print axioms d21_even_card
#print axioms d21_odd_card
#print axioms d21_Gamma_eq_delta_hTilde
#print axioms d21_intertwining
#print axioms d21_intertwining_fBeta
#print axioms Multi.bracketBetaM_eq_conj
#print axioms Multi.coreId_thetaSeries

-- The source algebra presented by generators and relations (`Presented/`).
#print axioms Presented.untwist
#print axioms Presented.untwist_b
#print axioms Presented.untwist_symm_b
#print axioms Presented.untwist_a
#print axioms Presented.untwist_κ
#print axioms Presented.untwist_parity
#print axioms Presented.rho_iotaP
#print axioms Presented.iotaP_injective
#print axioms Presented.κ_mul_iotaP_injective
#print axioms Presented.iotaRP_injective
#print axioms Presented.base_realization
#print axioms Presented.untwist_Xp_eq
#print axioms Presented.untwist_iotaP
#print axioms Presented.scomm_XhatP
#print axioms Presented.scomm_XhatP_delta
#print axioms Presented.recovery
#print axioms Presented.recovery_delta
#print axioms Presented.recovery_unique
#print axioms Presented.iotaRP_beta_injective
#print axioms Presented.bracketBeta_unique

-- Thm 5.1 for the presented algebras over `R_r`.
#print axioms Presented.omegaM_mem_center
#print axioms Presented.omegaM_antisymm
#print axioms Presented.kDeg_eq_bot
#print axioms Presented.bM_mul_cM
#print axioms Presented.thetaOf_J_thetaOfT
#print axioms Presented.thetaInv_conj
#print axioms Presented.thetaM_J_thetaMT
#print axioms Presented.thetaInvM_conj
#print axioms Presented.QZM_pow_eq_zero
#print axioms Presented.untwistM
#print axioms Presented.untwistR
#print axioms Presented.untwistR_b
#print axioms Presented.untwistR_symm_b
#print axioms Presented.untwistR_a
#print axioms Presented.untwistR_κ
#print axioms Presented.untwistR_parity

-- Prop 3.3, Prop 5.2 and Thm 5.3 for the presented algebras over `R_r`.
#print axioms Presented.κS_mul_κS
#print axioms Presented.embG_mul
#print axioms Presented.embG_one
#print axioms Presented.embG_gammaR
#print axioms Presented.embG_OmegaR
#print axioms Presented.embG_thetaSeries
#print axioms Presented.iotaM_zero_injective
#print axioms Presented.base_realizationM
#print axioms Presented.untwistR_XpM
#print axioms Presented.untwistR_iotaM
#print axioms Presented.iota0_scomm
#print axioms Presented.recoveryM
#print axioms Presented.iotaM_beta_injective
#print axioms Presented.bracketBetaM_unique

-- `[·,·]_β` as the supercommutator of the lifts on all of `𝔤_R`.
#print axioms Presented.scommR_eR
#print axioms Presented.scommM_homog

-- Prop 3.4 (last statement), Thm 4.9, Cor 4.10, Cor 4.11, the text after Prop 5.4, Remark 6.2
-- (the Killing form and the superdimension of `osp(4|2)`); with the general files
-- `General/StructureConstants` and `General/ExpDerivation`.
#print axioms gram_ordOdd
#print axioms gram_ordEven
#print axioms ordOdd_bijective
#print axioms ordEven_bijective
#print axioms der_eq_ad
#print axioms primitive_eq_hTilde_sub_ad
#print axioms fBeta_unique_primitive
#print axioms no_primitive_vanishing
#print axioms General.intertwine_map
#print axioms complex_parameters
#print axioms TBetaC_bijective
#print axioms General.exp_bilin_of_derivation
#print axioms GroupB.jacobi_eP
#print axioms GroupB.bracket0M_derivation
#print axioms GroupB.exp_adM_aut
#print axioms GroupB.ThetaStar_ne_exp_ad
#print axioms GroupB.ThetaStar_sub_id_not_derivation
#print axioms GroupB.bracket0Basis_eq_c4
#print axioms GroupB.d21_killing_zero
#print axioms GroupB.sdim_9_8_iff

end OspN
end OspOddDeformations
