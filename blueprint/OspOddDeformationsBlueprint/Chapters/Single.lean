import Verso
import VersoManual
import VersoBlueprint
import OspOddDeformations.OspN.Audit

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The deformed bracket for one odd parameter" =>

# The lifts and the coefficient

:::proposition "prop_lift_change" (lean := "OspOddDeformations.OspN.Xhat_eq_iota0_add, OspOddDeformations.OspN.Presented.untwist_Xp_eq, OspOddDeformations.OspN.Presented.untwist_iotaP")
*Proposition 4.1 (the change of lifts).* For every basis element $`X` of $`\mathfrak g`, $`\Phi(\iota_\beta X)=\iota_0(X+\kappa\tilde h(X))`, where $`\tilde h`
is the odd $`P`-linear map


$$`\tilde h(L_{uv})=\sum_i\bigl(\beta_{u,i^*}F_{v,i}+\beta_{v,i^*}F_{u,i}\bigr),\qquad \tilde h(S_{ij})=0,\qquad \tilde h(F_{u,i})=\tfrac12\sum_j\beta_{u,j^*}S_{ji}.`

Formalized in Lean: `OspOddDeformations.OspN.Xhat_eq_iota0_add`, `OspOddDeformations.OspN.Presented.untwist_Xp_eq`, `OspOddDeformations.OspN.Presented.untwist_iotaP`.
:::

:::proof "prop_lift_change"
Proof: the paper, §4.1.
:::

:::theorem "thm_recovery" (lean := "OspOddDeformations.OspN.recovery, OspOddDeformations.OspN.recovery_delta, OspOddDeformations.OspN.Presented.recovery, OspOddDeformations.OspN.Presented.recovery_delta")
*Theorem 4.2 (Recovery).* For all basis elements $`X,Y` of $`\mathfrak g`,


$$`[\iota_\beta X,\iota_\beta Y]=\iota_\beta\bigl([X,Y]_0+\kappa\,\delta\tilde h(X,Y)\bigr).`


In particular no $`1` or $`\kappa\cdot1` term occurs.

Formalized in Lean: `OspOddDeformations.OspN.recovery`, `OspOddDeformations.OspN.recovery_delta`, `OspOddDeformations.OspN.Presented.recovery`, `OspOddDeformations.OspN.Presented.recovery_delta`.
:::

:::proof "thm_recovery" (uses := "prop_lift_change, lem_base")
Proof: the paper, §4.1.
:::

:::theorem "thm_unique" (lean := "OspOddDeformations.OspN.recovery_unique, OspOddDeformations.OspN.recovery_unique_delta, OspOddDeformations.OspN.Presented.recovery_unique")
*Theorem 4.3 (Uniqueness).* Let $`X,Y` be basis elements of $`\mathfrak g`. If $`[\iota_\beta X,\iota_\beta Y]=\iota_\beta([X,Y]_0)+\kappa\,\iota_\beta(\Gamma')` with
$`\Gamma'\in\mathfrak g_P`, then $`\Gamma'=\Gamma_\beta(X,Y)`.

Formalized in Lean: `OspOddDeformations.OspN.recovery_unique`, `OspOddDeformations.OspN.recovery_unique_delta`, `OspOddDeformations.OspN.Presented.recovery_unique`.
:::

:::proof "thm_unique" (uses := "thm_recovery, prop_lift_change, prop_independence")
Proof: the paper, §4.1.
:::

:::proposition "prop_gamma" (lean := "OspOddDeformations.OspN.Gamma_eq_delta_hTilde, OspOddDeformations.OspN.deltaBasis_hTilde_swap")
*Proposition 4.4 (The explicit coefficient).* For all indices,


$$`\begin{align*} \Gamma_\beta(L_{uv},L_{wz})&=0,\qquad \Gamma_\beta(S_{ij},S_{kl})=0, \tag{4.2} \\ \Gamma_\beta(L_{uv},S_{ij})&=\beta_{u,i}F_{v,j}-\beta_{u,j}F_{v,i} +\beta_{v,i}F_{u,j}-\beta_{v,j}F_{u,i}, \tag{4.3} \\ \Gamma_\beta(L_{uv},F_{w,k})&=\tfrac12\bigl(\beta_{u,k}L_{vw}+\beta_{v,k}L_{uw}\bigr), \tag{4.4} \\ \Gamma_\beta(S_{ij},F_{w,k})&=\tfrac12\bigl(\beta_{w,j}S_{ik}-\beta_{w,i}S_{jk}\bigr), \tag{4.5} \\ \Gamma_\beta(F_{u,i},F_{v,j})&=-\tfrac12\bigl(\beta_{u,j}F_{v,i}+\beta_{v,i}F_{u,j}\bigr), \tag{4.6} \end{align*}`


and $`\Gamma_\beta(Y,X)=-(-1)^{p(X)p(Y)}\Gamma_\beta(X,Y)`.

Formalized in Lean: `OspOddDeformations.OspN.Gamma_eq_delta_hTilde`, `OspOddDeformations.OspN.deltaBasis_hTilde_swap`.
:::

:::proof "prop_gamma" (uses := "lem_base, prop_lift_change")
Proof: the paper, §4.1.
:::

# Triviality and the primitives

:::theorem "thm_triv_single" (lean := "OspOddDeformations.OspN.intertwining, OspOddDeformations.OspN.Gamma_eq_delta_hTilde, OspOddDeformations.OspN.TBetaInv_TBeta, OspOddDeformations.OspN.TBeta_TBetaInv, OspOddDeformations.OspN.Presented.iotaRP_beta_injective, OspOddDeformations.OspN.Presented.bracketBeta_unique, OspOddDeformations.OspN.Presented.scommR_eR")
*Theorem 4.5 (Triviality for one odd parameter).* The maps $`T=\mathrm{id}+\kappa\tilde h_R` and $`T^{-1}=\mathrm{id}-\kappa\tilde h_R` are even,
$`R`-linear, mutually inverse, and satisfy


$$`[TX,TY]_0=T([X,Y]_\beta)`


for all $`X,Y\in\mathfrak g_R`, where $`[\cdot,\cdot]_\beta` is the bracket of Section 4.1.

Formalized in Lean: `OspOddDeformations.OspN.intertwining`, `OspOddDeformations.OspN.Gamma_eq_delta_hTilde`, `OspOddDeformations.OspN.TBetaInv_TBeta`, `OspOddDeformations.OspN.TBeta_TBetaInv`, `OspOddDeformations.OspN.Presented.iotaRP_beta_injective`, `OspOddDeformations.OspN.Presented.bracketBeta_unique`, `OspOddDeformations.OspN.Presented.scommR_eR`.
:::

:::proof "thm_triv_single" (uses := "thm_recovery")
Proof: the paper, §4.2.
:::

:::lemma_ "lem_inner" (lean := "OspOddDeformations.OspN.delta_ad_eq_zero")
*Lemma 4.6.* For every $`Z\in P\otimes\mathfrak g_{\bar1}`, $`\delta(\operatorname{ad} Z)=0`.

Formalized in Lean: `OspOddDeformations.OspN.delta_ad_eq_zero`.
:::

:::proof "lem_inner"
Proof: the paper, §4.2.
:::

:::theorem "thm_fbeta" (lean := "OspOddDeformations.OspN.fBeta_L, OspOddDeformations.OspN.fBeta_F, OspOddDeformations.OspN.fBeta_S, OspOddDeformations.OspN.Gamma_eq_delta_fBeta")
*Theorem 4.7.* We have $`\Gamma_\beta=\delta f_\beta`, and for all indices


$$`f_\beta(L_{uv})=0,\qquad f_\beta(F_{w,j})=-\sum_t\check\beta_{t,j}L_{tw},\qquad f_\beta(S_{ij})=2\sum_t\bigl(\check\beta_{t,j}F_{t,i}-\check\beta_{t,i}F_{t,j}\bigr).`


So $`f_\beta` vanishes on $`\mathfrak{sp}(2n)`, maps the odd part into $`\mathfrak{sp}(2n)`
and maps $`\mathfrak{so}(N)` into the odd part. For $`N=1`, $`f_\beta` is the primitive of \[Aoi26, Theorem 4.1\].

Formalized in Lean: `OspOddDeformations.OspN.fBeta_L`, `OspOddDeformations.OspN.fBeta_F`, `OspOddDeformations.OspN.fBeta_S`, `OspOddDeformations.OspN.Gamma_eq_delta_fBeta`.
:::

:::proof "thm_fbeta" (uses := "lem_inner, lem_base")
Proof: the paper, §4.2.
:::

:::corollary "cor_tbeta" (lean := "OspOddDeformations.OspN.intertwining_fBeta, OspOddDeformations.OspN.TBetaFInv_TBetaF, OspOddDeformations.OspN.TBetaF_TBetaFInv")
*Corollary 4.8.* The map $`T_\beta=\mathrm{id}+\kappa(f_\beta)_R` has inverse $`\mathrm{id}-\kappa(f_\beta)_R` and
satisfies $`[T_\beta X,T_\beta Y]_0=T_\beta([X,Y]_\beta)` for all $`X,Y\in\mathfrak g_R`.

Formalized in Lean: `OspOddDeformations.OspN.intertwining_fBeta`, `OspOddDeformations.OspN.TBetaFInv_TBetaF`, `OspOddDeformations.OspN.TBetaF_TBetaFInv`.
:::

:::proof "cor_tbeta" (uses := "thm_triv_single")
Proof: the paper, §4.2.
:::

:::theorem "thm_all_primitives" (lean := "OspOddDeformations.OspN.primitive_eq_hTilde_sub_ad, OspOddDeformations.OspN.der_eq_ad")
*Theorem 4.9.* Let $`f` be an odd $`P`-linear map $`\mathfrak g_P\to\mathfrak g_P` with $`\delta f=\Gamma_\beta`.
Then $`f=\tilde h-\operatorname{ad} Z` for a unique $`Z\in P\otimes\mathfrak g_{\bar1}`. Equivalently, every odd
$`P`-linear map $`D\colon\mathfrak g_P\to\mathfrak g_P` with $`\delta D=0`, that is, every odd $`P`-linear
derivation of $`\mathfrak g_P`, is $`\operatorname{ad} Z` for a unique $`Z\in P\otimes\mathfrak g_{\bar1}`.

Formalized in Lean: `OspOddDeformations.OspN.primitive_eq_hTilde_sub_ad`, `OspOddDeformations.OspN.der_eq_ad`.
:::

:::proof "thm_all_primitives" (uses := "prop_osp, lem_inner, lem_base")
Proof: the paper, §4.2.
:::

:::corollary "cor_normalization" (lean := "OspOddDeformations.OspN.fBeta_L, OspOddDeformations.OspN.fBeta_unique_vanishing_sp, OspOddDeformations.OspN.fBeta_Sof_ne_zero, OspOddDeformations.OspN.no_primitive_vanishing_sp_so, OspOddDeformations.OspN.fBeta_unique_primitive, OspOddDeformations.OspN.no_primitive_vanishing")
*Corollary 4.10 (Normalization).* The map $`f_\beta` is the unique odd primitive of $`\Gamma_\beta` vanishing on $`\mathfrak{sp}(2n)`.
For $`N\geq2`, no odd primitive vanishes on $`\mathfrak{sp}(2n)\oplus\mathfrak{so}(N)`.

Formalized in Lean: `OspOddDeformations.OspN.fBeta_L`, `OspOddDeformations.OspN.fBeta_unique_vanishing_sp`, `OspOddDeformations.OspN.fBeta_Sof_ne_zero`, `OspOddDeformations.OspN.no_primitive_vanishing_sp_so`, `OspOddDeformations.OspN.fBeta_unique_primitive`, `OspOddDeformations.OspN.no_primitive_vanishing`.
:::

:::proof "cor_normalization" (uses := "thm_all_primitives")
Proof: the paper, §4.2.
:::

:::corollary "cor_complex" (lean := "OspOddDeformations.OspN.complex_parameters, OspOddDeformations.OspN.TBetaC_bijective, OspOddDeformations.General.intertwine_map")
*Corollary 4.11 (Complex parameters).* For any values $`\beta_{u,i}\in\mathbb C`, the specialized bracket on
$`(\mathbb C\oplus\kappa\mathbb C)\otimes\mathfrak g` is isomorphic to the undeformed bracket
via $`\mathrm{id}+\kappa f_\beta`.

Formalized in Lean: `OspOddDeformations.OspN.complex_parameters`, `OspOddDeformations.OspN.TBetaC_bijective`, `OspOddDeformations.General.intertwine_map`.
:::

:::proof "cor_complex" (uses := "thm_fbeta, cor_tbeta")
Proof: the paper, §4.2.
:::

