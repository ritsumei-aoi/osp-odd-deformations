import Verso
import VersoManual
import VersoBlueprint
import OspOddDeformations.OspN.Audit

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The deformed bracket for multiple odd parameters" =>

# Recovery and triviality

:::theorem "thm_untwist_multi" (lean := "OspOddDeformations.OspN.Presented.untwistR, OspOddDeformations.OspN.Presented.untwistR_b, OspOddDeformations.OspN.Presented.untwistR_symm_b, OspOddDeformations.OspN.Presented.untwistR_a, OspOddDeformations.OspN.Presented.untwistR_κ, OspOddDeformations.OspN.Presented.untwistR_parity, OspOddDeformations.OspN.Presented.thetaM_J_thetaMT, OspOddDeformations.OspN.Presented.QZM_pow_eq_zero, OspOddDeformations.OspN.Multi.thetaSeries_spec, OspOddDeformations.OspN.Multi.thetaSeries_eq_thetaHalf, OspOddDeformations.OspN.Multi.thetaHalf_spec")
*Theorem 5.1 (untwisting, `r` parameters).* Let $`\Theta=(\mathbb I+\Omega J)^{1/2}=\sum_{k\geq0}\binom{1/2}{k}(\Omega J)^k`, a finite sum ending at
$`k=\lfloor r/2\rfloor`, since the entries of $`(\Omega J)^k` have $`\kappa`-degree $`2k`. There are
mutually inverse even isomorphisms of $`R_r`-superalgebras $`\Phi_r\colon A_\beta\to A_0` and
$`\Psi_r\colon A_0\to A_\beta`, both fixing the $`a_i` and $`R_r`, with


$$`\Phi_r(b_u)=\sum_w\Theta_{uw}B_w+c_u,\qquad \Psi_r(B_u)=\sum_w(\Theta^{-1})_{uw}(b_w-c_w).`

 In $`A_\beta`, $`c_w` denotes the
same expression $`\sum_i\gamma_{w,i^*}a_i`.

Formalized in Lean: `OspOddDeformations.OspN.Presented.untwistR`, `OspOddDeformations.OspN.Presented.untwistR_b`, `OspOddDeformations.OspN.Presented.untwistR_symm_b`, `OspOddDeformations.OspN.Presented.untwistR_a`, `OspOddDeformations.OspN.Presented.untwistR_κ`, `OspOddDeformations.OspN.Presented.untwistR_parity`, `OspOddDeformations.OspN.Presented.thetaM_J_thetaMT`, `OspOddDeformations.OspN.Presented.QZM_pow_eq_zero`, `OspOddDeformations.OspN.Multi.thetaSeries_spec`, `OspOddDeformations.OspN.Multi.thetaSeries_eq_thetaHalf`, `OspOddDeformations.OspN.Multi.thetaHalf_spec`.
:::

:::proof "thm_untwist_multi" (uses := "lem_untwist")
Proof: the paper, §5.1.
:::

:::proposition "prop_lift_change_multi" (lean := "OspOddDeformations.OspN.Multi.UM, OspOddDeformations.OspN.Multi.UM_bijective, OspOddDeformations.OspN.Multi.UM_thetaSeries_bijective, OspOddDeformations.OspN.Presented.untwistR_XpM, OspOddDeformations.OspN.Presented.untwistR_iotaM")
*Proposition 5.2 (change of lifts, `r` parameters).* For every basis element $`X` of $`\mathfrak g`, $`\Phi_r(\iota_\beta X)=\iota_0(UX)`, where $`U` is the even
$`R_r`-linear map with $`U(S_{ij})=S_{ij}`,


$$`\begin{align*} U(L_{uv})&=\sum_{w,z}\Theta_{uw}\Theta_{vz}L_{wz} +\sum_{w,i}\bigl(\Theta_{uw}\gamma_{v,i^*}+\Theta_{vw}\gamma_{u,i^*}\bigr)F_{w,i} -\tfrac12\sum_{i,j}\gamma_{u,i^*}\gamma_{v,j^*}S_{ij}, \\ U(F_{u,i})&=\sum_w\Theta_{uw}F_{w,i}+\tfrac12\sum_j\gamma_{u,j^*}S_{ji}. \end{align*}`


The map $`U-\mathrm{id}` raises the $`\kappa`-degree, so it is nilpotent and $`U` is invertible.

Formalized in Lean: `OspOddDeformations.OspN.Multi.UM`, `OspOddDeformations.OspN.Multi.UM_bijective`, `OspOddDeformations.OspN.Multi.UM_thetaSeries_bijective`, `OspOddDeformations.OspN.Presented.untwistR_XpM`, `OspOddDeformations.OspN.Presented.untwistR_iotaM`.
:::

:::proof "prop_lift_change_multi" (uses := "prop_lift_change")
Proof: the paper, §5.1.
:::

:::theorem "thm_multi" (lean := "OspOddDeformations.OspN.Presented.recoveryM, OspOddDeformations.OspN.Presented.iotaM_beta_injective, OspOddDeformations.OspN.Presented.bracketBetaM_unique, OspOddDeformations.OspN.Presented.scommM_homog, OspOddDeformations.OspN.Multi.intertwining_multi, OspOddDeformations.OspN.Multi.intertwining_thetaSeries, OspOddDeformations.OspN.Multi.bracketBetaM, OspOddDeformations.OspN.Multi.bracketBetaM_eq_conj")
*Theorem 5.3 (Triviality for $`r` odd parameters).* For all basis elements $`X,Y` of $`\mathfrak g`,


$$`[\iota_\beta X,\iota_\beta Y]=\iota_\beta\bigl(U^{-1}[UX,UY]_0\bigr),`


so the supercommutator of two lifts in $`A_\beta` is an $`R_r`-linear combination of lifts, with no
scalar term, and $`\iota_\beta` is injective. Thus
$`[\cdot,\cdot]_\beta` is defined on $`\mathfrak g_R` as in the case $`r=1` (Section 4.1), and the even $`R_r`-linear map $`U` satisfies
$`[UX,UY]_0=U([X,Y]_\beta)` for all $`X,Y\in\mathfrak g_R`.
Moreover


$$`[X,Y]_\beta=[X,Y]_0+\sum_{s=1}^r\kappa_s\,\Gamma^{(s)}(X,Y), \tag{5.3}`


where $`\Gamma^{(s)}` is the coefficient $`\Gamma_\beta` of Proposition 4.4
with $`\beta^{(s)}` in place of $`\beta`.

Formalized in Lean: `OspOddDeformations.OspN.Presented.recoveryM`, `OspOddDeformations.OspN.Presented.iotaM_beta_injective`, `OspOddDeformations.OspN.Presented.bracketBetaM_unique`, `OspOddDeformations.OspN.Presented.scommM_homog`, `OspOddDeformations.OspN.Multi.intertwining_multi`, `OspOddDeformations.OspN.Multi.intertwining_thetaSeries`, `OspOddDeformations.OspN.Multi.bracketBetaM`, `OspOddDeformations.OspN.Multi.bracketBetaM_eq_conj`.
:::

:::proof "thm_multi" (uses := "prop_lift_change_multi, prop_independence, thm_triv_single, lem_base, thm_recovery")
Proof: the paper, §5.1.
:::

# Factorization through an even deformation

:::proposition "prop_factor" (lean := "OspOddDeformations.OspN.Multi.TS_comm, OspOddDeformations.OspN.Multi.UM_eq_ThetaStar_TProd, OspOddDeformations.OspN.Multi.TProd_eq, OspOddDeformations.OspN.Multi.VChi_comp, OspOddDeformations.OspN.Multi.ThetaStar_comp, OspOddDeformations.OspN.Multi.vChi_bracket, OspOddDeformations.OspN.Multi.thetaStar_bracket, OspOddDeformations.OspN.Multi.ThetaStar_not_aut")
*Proposition 5.4 (the factorization).* The $`T^{(s)}` commute with each other, and


$$`U=\Theta_*T^{(1)}\cdots T^{(r)}.`


The product $`T^{(1)}\cdots T^{(r)}` intertwines $`[\cdot,\cdot]_\beta` with $`[\cdot,\cdot]_{J-\Omega}`, and
$`\Theta_*` intertwines $`[\cdot,\cdot]_{J-\Omega}` with $`[\cdot,\cdot]_0`. If $`\Omega\neq0`, then $`\Theta_*` is not an
automorphism of $`[\cdot,\cdot]_0`.

Formalized in Lean: `OspOddDeformations.OspN.Multi.TS_comm`, `OspOddDeformations.OspN.Multi.UM_eq_ThetaStar_TProd`, `OspOddDeformations.OspN.Multi.TProd_eq`, `OspOddDeformations.OspN.Multi.VChi_comp`, `OspOddDeformations.OspN.Multi.ThetaStar_comp`, `OspOddDeformations.OspN.Multi.vChi_bracket`, `OspOddDeformations.OspN.Multi.thetaStar_bracket`, `OspOddDeformations.OspN.Multi.ThetaStar_not_aut`. (with `U` and (5.3) as in #19)
:::

:::proof "prop_factor" (uses := "thm_untwist_multi, lem_base, prop_lift_change_multi, thm_multi")
Proof: the paper, §5.2.
:::

:::proposition "after_prop_factor" (uses := "prop_factor") (lean := "OspOddDeformations.OspN.Multi.ThetaStar_sub_one_not_derivation, OspOddDeformations.OspN.GroupB.ThetaStar_ne_exp_ad, OspOddDeformations.OspN.GroupB.exp_adM_aut, OspOddDeformations.OspN.GroupB.bracket0M_derivation, OspOddDeformations.OspN.GroupB.ThetaStar_sub_id_not_derivation")
*Text after Proposition 5.4.* In particular, if $`\Omega\neq0`, then $`U(T^{(1)}\cdots T^{(r)})^{-1}=\Theta_*` is not of the
form $`\exp(\operatorname{ad} Y)` for any even $`Y\in\mathfrak g_R` with $`\operatorname{ad} Y` nilpotent: such a map is an automorphism of $`[\cdot,\cdot]_0`. For $`r\leq3`, $`\Theta=\mathbb I+\tfrac12\Omega J`, so the map $`\Theta_*-\mathrm{id}` has $`\kappa`-degree $`2` and its square
vanishes. In that case, if $`\Omega\neq0`, the map $`\Theta_*-\mathrm{id}` is not a derivation of $`[\cdot,\cdot]_0`, since otherwise
$`\Theta_*=\exp(\Theta_*-\mathrm{id})` would be an automorphism.

Partially formalized: if `Ω ≠ 0`, `Θ_*` is not `exp(ad Y)` for any even `Y` with `ad Y` nilpotent, since `exp(ad Y)` is an automorphism of `[·,·]_0`; for `r ≤ 3`, `Θ_* − id` is not a derivation of `[·,·]_0` when `Ω ≠ 0`, and in general it is not one when its square vanishes; that for `r ≤ 3` the map `Θ_* − id` has `κ`-degree 2 and its square vanishes is not formalized. Declarations: `OspOddDeformations.OspN.Multi.ThetaStar_sub_one_not_derivation`, `OspOddDeformations.OspN.GroupB.ThetaStar_ne_exp_ad`, `OspOddDeformations.OspN.GroupB.exp_adM_aut`, `OspOddDeformations.OspN.GroupB.bracket0M_derivation`, `OspOddDeformations.OspN.GroupB.ThetaStar_sub_id_not_derivation`.
:::

:::proposition "prop_not_additive" (lean := "OspOddDeformations.OspN.Multi.TProd_not_intertwine, OspOddDeformations.OspN.Multi.T1_not_intertwine, OspOddDeformations.OspN.Multi.T1_defect_Luv")
*Proposition 5.5 (The trivialization is not additive).* Suppose $`\Omega\neq0`. Then neither $`T^{(1)}\cdots T^{(r)}` nor the truncation
$`U_{\le1}=\mathrm{id}+\sum_s\kappa_s\tilde h^{(s)}_R` of $`U` to degree $`1` intertwines
$`[\cdot,\cdot]_\beta` with $`[\cdot,\cdot]_0`.

Formalized in Lean: `OspOddDeformations.OspN.Multi.TProd_not_intertwine`, `OspOddDeformations.OspN.Multi.T1_not_intertwine`, `OspOddDeformations.OspN.Multi.T1_defect_Luv`.
:::

:::proof "prop_not_additive" (uses := "thm_multi, prop_factor, prop_gamma, lem_base")
Proof: the paper, §5.2.
:::

:::proposition "rem_even_generated"
*Remark 5.6 (The odd parameters generate an even perturbation).* Proposition 5.4 shows where the even perturbation enters. The product of the
single-parameter trivializations carries the odd deformation onto $`[\cdot,\cdot]_{J-\Omega}`. At
second order this is the even central perturbation $`-\Omega` of the bosonic form $`J`, in the
even nilpotent parameters $`\kappa_s\kappa_{s'}`. The map $`\Theta_*` removes it, and $`\Theta` is not symplectic:
$`\Theta J\Theta^{\mathsf T}=J-\Omega` by the proof of Theorem 5.1. In
$`[\Phi_rb_u,\Phi_rb_v]` the same cancellation appears as the commutator $`[c_u,c_v]=\Omega_{uv}`
of the shifts $`c_u`. The even direction of Remark 6.1 is thus reached from the odd
one, although it is not treated here.

Not formalized.
:::

:::proposition "rem_fock"
*Remark 5.7 (The Fock module).* In this remark $`k,l` run over $`\{1,\ldots,n\}`.
Let $`\mathcal F=R_r[x_1,\ldots,x_n]\otimes_{\mathbb Q}\mathrm{Cl}(N)`, with the $`x_k` even and $`\mathrm{Cl}(N)`
acting on itself by left multiplication. Sending $`B_{2k-1}\mapsto\partial_{x_k}` and $`B_{2k}\mapsto x_k`
represents $`A_0` on $`\mathcal F`, and composing with $`\Phi_r` represents $`A_\beta`, faithfully, as in the case $`N=1`, $`r=1` of \[Aoi26\]. For $`N=n=r=1` this is the Fock space of \[BS17, Section 4\], where the mixed relation
is realized by an odd derivation and the annihilated element is $`1` (see \[Aoi26\]). Put
$`\eta_{kl}=\Theta_{(2k-1)(2l-1)}` and $`\zeta_{kl}=\Theta_{(2k-1)(2l)}`. Since $`\Theta` is $`\mathbb I` plus a matrix with entries of
$`\kappa`-degree at least $`2`, so is $`\eta`, and $`\eta` is invertible. Put $`\Xi=\eta^{-1}\zeta` and $`\tilde c_k=\sum_l(\eta^{-1})_{kl}c_{2l-1}`, and let $`\Xi^+` and $`\Xi^-` be the
symmetric and antisymmetric parts of $`\Xi`. The elements annihilated by every $`b_{2k-1}` are
exactly the $`\varpi\,\sigma` with $`\sigma\in R_r\otimes\mathrm{Cl}(N)`, where


$$`\varpi=\exp\Bigl(-\tfrac12\sum_{k,l}\Xi^+_{kl}x_kx_l-\sum_kx_k\tilde c_k\Bigr),`


a finite sum. Indeed, $`\mathfrak b_k=\sum_l(\eta^{-1})_{kl}b_{2l-1}` acts as
$`\partial_{x_k}+\sum_l\Xi_{kl}x_l+\tilde c_k`, and the $`\mathfrak b_k` commute, since $`J_{(2k-1)(2l-1)}=0`. This gives
$`[\tilde c_k,\tilde c_l]=2\Xi^-_{kl}`, a central scalar. With $`\xi=\sum_kx_k\tilde c_k`, one has
$`\partial_{x_k}e^{-\xi}=-(\tilde c_k-\tfrac12[\xi,\tilde c_k])e^{-\xi}`. The Gaussian factor
$`\exp(-\tfrac12\sum_{k,l}\Xi^+_{kl}x_kx_l)` is central in $`\mathcal F`, and $`\partial_{x_k}` multiplies it by $`-(\Xi^+x)_k`, which absorbs the
symmetric part of $`\Xi`. The $`\tilde c_k` act by left multiplication. The antisymmetric part $`\Xi^-` cancels
the term $`\tfrac12[\xi,\tilde c_k]=-(\Xi^-x)_k`, which arises because the $`\tilde c_k` do not commute. So $`\mathfrak b_k\varpi=0`. Conversely, $`\varpi` is invertible, and $`\mathfrak b_k(\varpi\sigma')=\varpi\,\partial_{x_k}\sigma'` for every
$`\sigma'\in\mathcal F`. With $`\Omega^{\mathrm{oo}}_{kl}=\Omega_{(2k-1)(2l-1)}`, $`\Omega^{\mathrm{oe}}_{kl}=\Omega_{(2k-1)(2l)}` and
$`c_{\mathrm o}=(c_{2k-1})_k`, the table below lists the cases worked out. In it, $`\theta`, $`f` and $`\lambda` are even central elements
of $`R_r`.



$$`\begin{array}{llll} \text{case} & \Theta & \Xi & \varpi \\ \hline r=1 & \mathbb I & 0 & 1-\sum_kx_kc_{2k-1} \\ r=2 & \mathbb I+\tfrac12\Omega J & \tfrac12\Omega^{\mathrm{oo}} & \exp(-\sum_kx_kc_{2k-1}) \\ r=3 & \mathbb I+\tfrac12\Omega J & \tfrac12\Omega^{\mathrm{oo}} & \exp(-\sum_kx_k\tilde c_k) \text{,} \tilde c=(\mathbb I+\tfrac12\Omega^{\mathrm{oe}})c_{\mathrm o} \\ n=1 & \theta\,\mathbb I & 0 & \exp(-\theta^{-1}x_1c_1) \\ N=1 & \mathbb I+f\,\Omega J & \lambda\,(\gamma_{2k-1,0}\gamma_{2l-1,0})_{kl} & \exp(-\sum_kx_k\tilde c_k) \end{array}`



For $`r=2`, $`\eta^{-1}=\mathbb I+\tfrac12\Omega^{\mathrm{oe}}` and $`\Omega^{\mathrm{oe}}c_{\mathrm o}` has $`\kappa`-degree $`3`, so
$`\tilde c=c_{\mathrm o}`. For $`n=1`, $`\Omega=\omega J` and $`\Theta=(1-\omega)^{1/2}\mathbb I`. For $`N=1`, $`(\Omega J)^2` is an
even multiple of $`\Omega J`, which gives the form of $`\Theta`. The Gaussian factor
$`\exp(-\tfrac12\sum_{k,l}\Xi^+_{kl}x_kx_l)` is $`1` unless $`N,n\geq2` and $`r\geq4`. Indeed, $`\Xi^+=0` in three cases. For $`r\leq3`, $`\Theta=\mathbb I+\tfrac12\Omega J` and
$`\Xi=\tfrac12(\Omega_{(2k-1)(2l-1)})_{kl}`, which is antisymmetric. For $`n=1`, $`\Theta` is a multiple of
$`\mathbb I`, so $`\zeta=0` and $`\Xi=0`. For $`N=1`, $`\Omega_{uv}=-\gamma_{u,0}\gamma_{v,0}` has rank $`1`, and
$`\Xi_{kl}=\lambda\,\gamma_{2k-1,0}\gamma_{2l-1,0}` with a single even $`\lambda` for all $`k,l`, so $`\Xi` is
antisymmetric. For $`N,n\geq2` and $`r\geq4`, $`\Xi^+` need not vanish. Its part of $`\kappa`-degree $`4` is
$`\tfrac18(\Omega^{\mathrm{oe}}\Omega^{\mathrm{oo}}-\Omega^{\mathrm{oo}}(\Omega^{\mathrm{oe}})^{\mathsf T})`. At $`N=n=2`, $`r=4`, with
$`\gamma_{1,1^+}=\kappa_1`, $`\gamma_{3,1^-}=\kappa_2`, $`\gamma_{1,1^-}=\kappa_3`, $`\gamma_{4,1^+}=\kappa_4` and the other
$`\gamma_{u,i}=0`, one has $`\Omega_{13}=-\kappa_1\kappa_2` and $`\Omega_{14}=-\kappa_3\kappa_4`, and this gives
$`\Xi^+_{11}=-\tfrac14\Omega_{13}\Omega_{14}=-\tfrac14\kappa_1\kappa_2\kappa_3\kappa_4`. The factor depends on the
choice of $`\Theta`: replacing $`\Theta` by $`\Theta\mathcal S`, with $`\mathcal S_{(2k-1)(2l)}=q_{kl}` for a symmetric
nilpotent even $`q` and $`\mathcal S` otherwise the identity, keeps $`\Theta J\Theta^{\mathsf T}=J-\Omega` and changes
$`\Xi^+` into $`\Xi^++q`.

Not formalized.
:::

