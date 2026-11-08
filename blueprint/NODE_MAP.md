# Node map: the paper's statements and the declarations that formalize them

The blueprint's input besides the paper. For each statement of the paper (by its LaTeX label), its
status and the declarations of this development that formalize it, and how far. `gen_chapters.py`
transcribes it into the chapters; `check_nodes.py` checks the built site against it. Numbers are
the paper's.

## Status values
- **formalized**: the statement as the paper states it.
- **partial**: what is formalized is said in the "Lean" column; the rest is paper-only.
- **paper**: not formalized.

These are displayed in the node, as a sentence. VersoBlueprint's `statementStatus` is left to its
own computation. The check is on `missingExternalDecl` only.

Namespaces: `N.` is `OspOddDeformations.OspN.`, `M.` is `OspOddDeformations.OspN.Multi.`, `P.` is `OspOddDeformations.OspN.Presented.`, `B.` is
`OspOddDeformations.OspN.GroupB.`, and `G.` is `OspOddDeformations.General.`.

| # | label (tex) | kind, title | status | declarations | Lean covers (for partial) |
|---|---|---|---|---|---|
| 1 | `rem:central` | Remark, Even-central specialization | paper | — | |
| 2 | `lem:untwist` | Lemma, Untwisting | formalized | `P.untwist`, `P.untwist_b`, `P.untwist_symm_b`, `P.untwist_a`, `P.untwist_κ`, `P.untwist_parity` | |
| 3 | `lem:base` | Lemma, The base bracket | formalized | `N.bracket0Basis_super_skew`, `N.bracket0Basis_degree`, `N.base_realization`, `P.base_realization` | |
| 4 | `prop:independence` | Proposition, Independence | formalized | `N.iota0R_injective`, `N.X0A0_linearIndependent`, `N.iota0_injective`, `N.kappa_iota0_injective`, `P.iotaRP_injective` | |
| 5 | `prop:osp` | Proposition, The orthosymplectic identification | formalized | `N.rho_ospCond`, `N.rho_bracket`, `N.rhoBasis_linearIndependent`, `N.rho_span`, `N.gram_ordOdd`, `N.gram_ordEven`, `N.ordOdd_bijective`, `N.ordEven_bijective` | |
| 6 | `prop:lift-change` | Proposition (the change of lifts) | formalized | `N.Xhat_eq_iota0_add`, `P.untwist_Xp_eq`, `P.untwist_iotaP` | |
| 7 | `thm:recovery` | Theorem, Recovery | formalized | `N.recovery`, `N.recovery_delta`, `P.recovery`, `P.recovery_delta` | |
| 8 | `thm:unique` | Theorem, Uniqueness | formalized | `N.recovery_unique`, `N.recovery_unique_delta`, `P.recovery_unique` | |
| 9 | `prop:gamma` | Proposition, The explicit coefficient | formalized | `N.Gamma_eq_delta_hTilde`, `N.deltaBasis_hTilde_swap` | |
| 10 | `thm:triv-single` | Theorem, Triviality for one odd parameter | formalized | `N.intertwining`, `N.Gamma_eq_delta_hTilde`, `N.TBetaInv_TBeta`, `N.TBeta_TBetaInv`, `P.iotaRP_beta_injective`, `P.bracketBeta_unique`, `P.scommR_eR` | |
| 11 | `lem:inner` | Lemma | formalized | `N.delta_ad_eq_zero` | |
| 12 | `thm:fbeta` | Theorem | formalized | `N.fBeta_L`, `N.fBeta_F`, `N.fBeta_S`, `N.Gamma_eq_delta_fBeta` | |
| 13 | `cor:tbeta` | Corollary | formalized | `N.intertwining_fBeta`, `N.TBetaFInv_TBetaF`, `N.TBetaF_TBetaFInv` | |
| 14 | `thm:all-primitives` | Theorem | formalized | `N.primitive_eq_hTilde_sub_ad`, `N.der_eq_ad` | |
| 15 | `cor:normalization` | Corollary, Normalization | formalized | `N.fBeta_L`, `N.fBeta_unique_vanishing_sp`, `N.fBeta_Sof_ne_zero`, `N.no_primitive_vanishing_sp_so`, `N.fBeta_unique_primitive`, `N.no_primitive_vanishing` | |
| 16 | `cor:complex` | Corollary, Complex parameters | formalized | `N.complex_parameters`, `N.TBetaC_bijective`, `G.intertwine_map` | |
| 17 | `thm:untwist-multi` | Theorem (untwisting, `r` parameters) | formalized | `P.untwistR`, `P.untwistR_b`, `P.untwistR_symm_b`, `P.untwistR_a`, `P.untwistR_κ`, `P.untwistR_parity`, `P.thetaM_J_thetaMT`, `P.QZM_pow_eq_zero`, `M.thetaSeries_spec`, `M.thetaSeries_eq_thetaHalf`, `M.thetaHalf_spec` | |
| 18 | `prop:lift-change-multi` | Proposition (change of lifts, `r` parameters) | formalized | `M.UM`, `M.UM_bijective`, `M.UM_thetaSeries_bijective`, `P.untwistR_XpM`, `P.untwistR_iotaM` | |
| 19 | `thm:multi` | Theorem, Triviality for `r` odd parameters | formalized | `P.recoveryM`, `P.iotaM_beta_injective`, `P.bracketBetaM_unique`, `P.scommM_homog`, `M.intertwining_multi`, `M.intertwining_thetaSeries`, `M.bracketBetaM`, `M.bracketBetaM_eq_conj` | |
| 20 | `prop:factor` | Proposition (the factorization) | formalized | `M.TS_comm`, `M.UM_eq_ThetaStar_TProd`, `M.TProd_eq`, `M.VChi_comp`, `M.ThetaStar_comp`, `M.vChi_bracket`, `M.thetaStar_bracket`, `M.ThetaStar_not_aut` | (with `U` and (5.3) as in #19) |
| 21 | `rem:even-generated` | Remark, The odd parameters generate an even perturbation | paper | — | |
| 22 | `rem:fock` | Remark, The Fock module | paper | — | |
| 23 | `rem:even` | Remark, The even direction | partial | `M.thetaG_spec` | the claim that `J − Ω` is equivalent to `J` by `Θ = (𝕀+ΩJ)^{1/2}`, for an even antisymmetric `Ω` whose entries have `κ`-degree 2 |
| 24 | `rem:d21` | Remark, D(2,1) | partial | `N.d21_even_card`, `N.d21_odd_card`, `N.d21_Gamma_eq_delta_hTilde`, `N.d21_intertwining`, `N.d21_intertwining_fBeta`, `B.d21_killing_zero`, `B.sdim_9_8_iff` | the superdimension of `osp(4|2)`: 9 even and 8 odd basis elements, and Theorem 4.2's `Γ_β = δh̃`, Theorem 4.5 and Corollary 4.8 at `N = 4`, `n = 1`; the Killing form of `osp(4|2)` vanishes; `osp(4|2)` is the only `osp(N|2n)` of superdimension `(9|8)`. The Killing form of every `D(n+1,n)`, and which `D(2,1;α)` are isomorphic to `D(2,1)`, are not formalized |
| 25 | `prop:not-additive` | Proposition, The trivialization is not additive | formalized | `M.TProd_not_intertwine`, `M.T1_not_intertwine`, `M.T1_defect_Luv` | |

Two more nodes, without a tex label:
- **C1, Controls** (App. A, item 9), status **partial**, covers: "the controls for `N = 1` and the
  three values of `Γ_β` at `C(2)`; their agreement with an exact computation of the bracket in `A_β`
  is checked outside the development". Declarations: `N.control_N1_bracket`, `N.control_N1_gamma`,
  `N.control_N1_hTilde`, `N.control_N1_fBeta`, `N.evenIdx_basis_card_1_1`,
  `N.evenC2_GammaBasis_SF`, `N.evenC2_GammaBasis_FF`, `N.evenC2_GammaBasis_LS`. Its text is App. A
  item 9, verbatim.
- **C2, the text after Prop 5.4** ("In particular … not a derivation"): **partial**, declarations
  `M.ThetaStar_sub_one_not_derivation`, `B.ThetaStar_ne_exp_ad`, `B.exp_adM_aut`, `B.bracket0M_derivation`,
  `B.ThetaStar_sub_id_not_derivation`, covers: "if `Ω ≠ 0`, `Θ_*` is not `exp(ad Y)` for any even `Y` with `ad Y`
  nilpotent, since `exp(ad Y)` is an automorphism of `[·,·]_0`; for `r ≤ 3`, `Θ_* − id` is not a derivation of
  `[·,·]_0` when `Ω ≠ 0`, and in general it is not one when its square vanishes; that for `r ≤ 3` the map
  `Θ_* − id` has `κ`-degree 2 and its square vanishes is not formalized". It **uses `prop:factor`**,
  as its first words say; this edge is added to the mechanical ones.

## Text rules for the builder
- A node's statement is the paper's statement environment, **verbatim**, converted mechanically from
  LaTeX to the blueprint's markup. Macros are expanded by the paper's own `\newcommand`s. A macro whose
  expansion is unclear is resolved by hand, never guessed.
- A node's proof is one line: "Proof: the paper, §x.y." No new prose.
- The status sentence is one of three fixed forms:
  - "Formalized in Lean: <declarations>." — followed by " (<cell>)" when the row has a cell (#20);
  - "Partially formalized: <the 'Lean covers' cell, verbatim>. Declarations: <…>.";
  - "Not formalized." — or "Not formalized: <cell>." when the row has a cell.
- `uses` edges are mechanical: node A uses node B if A's proof environment contains `\ref`/`\eqref`
  of B's label, or of an equation label inside B's environment. `uses_edges.txt` lists every edge.
- Chapters follow the paper's sections (§2–§6, App. A for C1).
