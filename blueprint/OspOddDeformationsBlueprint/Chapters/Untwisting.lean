import Verso
import VersoManual
import VersoBlueprint
import OspOddDeformations.OspN.Audit

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The untwisting and the identification with osp(N|2n)" =>

:::lemma_ "lem_untwist" (lean := "OspOddDeformations.OspN.Presented.untwist, OspOddDeformations.OspN.Presented.untwist_b, OspOddDeformations.OspN.Presented.untwist_symm_b, OspOddDeformations.OspN.Presented.untwist_a, OspOddDeformations.OspN.Presented.untwist_κ, OspOddDeformations.OspN.Presented.untwist_parity")
*Lemma 3.1 (Untwisting).* Put $`c_u=\kappa\sum_{i\in K_N}\beta_{u,i^*}a_i\in A_0`, and write $`c_u` also for the same expression in
$`A_\beta`. There are mutually inverse even
isomorphisms of $`R`-superalgebras $`\Phi\colon A_\beta\to A_0` and $`\Psi\colon A_0\to A_\beta`,
both fixing the $`a_i` and $`R`, with


$$`\Phi(b_u)=B_u+c_u,\qquad \Psi(B_u)=b_u-c_u .`

Formalized in Lean: `OspOddDeformations.OspN.Presented.untwist`, `OspOddDeformations.OspN.Presented.untwist_b`, `OspOddDeformations.OspN.Presented.untwist_symm_b`, `OspOddDeformations.OspN.Presented.untwist_a`, `OspOddDeformations.OspN.Presented.untwist_κ`, `OspOddDeformations.OspN.Presented.untwist_parity`.
:::

:::proof "lem_untwist"
Proof: the paper, §3.
:::

:::lemma_ "lem_base" (lean := "OspOddDeformations.OspN.bracket0Basis_super_skew, OspOddDeformations.OspN.bracket0Basis_degree, OspOddDeformations.OspN.base_realization, OspOddDeformations.OspN.Presented.base_realization")
*Lemma 3.2 (The base bracket).* In $`A_0` the lifts satisfy, for all indices,


$$`\begin{align*} [L^0_{uv},L^0_{wz}]&=\tfrac12\bigl(J_{vw}L^0_{uz}+J_{uw}L^0_{vz}+J_{vz}L^0_{uw} +J_{uz}L^0_{vw}\bigr), \tag{3.1} \\ [S^0_{ij},S^0_{kl}]&=g_{jk}S^0_{il}-g_{ik}S^0_{jl}-g_{jl}S^0_{ik}+g_{il}S^0_{jk}, \tag{3.2} \\ [L^0_{uv},S^0_{ij}]&=0, \tag{3.3} \\ [L^0_{uv},F^0_{w,i}]&=\tfrac12\bigl(J_{vw}F^0_{u,i}+J_{uw}F^0_{v,i}\bigr), \tag{3.4} \\ [S^0_{jk},F^0_{w,i}]&=g_{ki}F^0_{w,j}-g_{ji}F^0_{w,k}, \tag{3.5} \\ \{F^0_{u,i},F^0_{v,j}\}&=\tfrac14J_{uv}S^0_{ij}+\tfrac12g_{ij}L^0_{uv}. \tag{3.6} \end{align*}`


The remaining brackets follow by super-skew symmetry. No scalar term occurs.

Formalized in Lean: `OspOddDeformations.OspN.bracket0Basis_super_skew`, `OspOddDeformations.OspN.bracket0Basis_degree`, `OspOddDeformations.OspN.base_realization`, `OspOddDeformations.OspN.Presented.base_realization`.
:::

:::proof "lem_base"
Proof: the paper, §3.
:::

:::proposition "prop_independence" (lean := "OspOddDeformations.OspN.iota0R_injective, OspOddDeformations.OspN.X0A0_linearIndependent, OspOddDeformations.OspN.iota0_injective, OspOddDeformations.OspN.kappa_iota0_injective, OspOddDeformations.OspN.Presented.iotaRP_injective")
*Proposition 3.3 (Independence).* The map $`\iota_0\colon\mathfrak g_R\to A_0` is injective.

Formalized in Lean: `OspOddDeformations.OspN.iota0R_injective`, `OspOddDeformations.OspN.X0A0_linearIndependent`, `OspOddDeformations.OspN.iota0_injective`, `OspOddDeformations.OspN.kappa_iota0_injective`, `OspOddDeformations.OspN.Presented.iotaRP_injective`.
:::

:::proof "prop_independence"
Proof: the paper, §3.
:::

:::proposition "prop_osp" (lean := "OspOddDeformations.OspN.rho_ospCond, OspOddDeformations.OspN.rho_bracket, OspOddDeformations.OspN.rhoBasis_linearIndependent, OspOddDeformations.OspN.rho_span, OspOddDeformations.OspN.gram_ordOdd, OspOddDeformations.OspN.gram_ordEven, OspOddDeformations.OspN.ordOdd_bijective, OspOddDeformations.OspN.ordEven_bijective")
*Proposition 3.4 (The orthosymplectic identification).* Let $`M` have even basis $`e_i` ($`i\in K_N`) and odd basis $`e_u` ($`u\in I`). In this
proposition and its proof, $`i,j,k` run over $`K_N` and $`u,v,w` over $`I`. Let
$`\mathcal B` be the supersymmetric form with $`\mathcal B(e_i,e_k)=-g_{ik}`,
$`\mathcal B(e_u,e_w)=J_{uw}` and $`\mathcal B(e_i,e_u)=0`. Define $`\rho\colon\mathfrak g\to \operatorname{End}(M)` by


$$`\rho(L_{uv})\colon e_w\mapsto\tfrac12(J_{vw}e_u+J_{uw}e_v),\qquad \rho(S_{ij})\colon e_k\mapsto g_{jk}e_i-g_{ik}e_j,`




$$`\rho(F_{u,i})\colon e_k\mapsto\tfrac12g_{ik}e_u,\quad e_w\mapsto\tfrac12J_{uw}e_i,`


with $`\rho(L_{uv})` zero on the $`e_i` and $`\rho(S_{ij})` zero on the $`e_u`. Then $`\rho`
is an isomorphism of $`(\mathfrak g,[\cdot,\cdot]_0)` onto $`\mathfrak{osp}(M,\mathcal B)`, the span of the
homogeneous $`T\in\operatorname{End}(M)` with


$$`\mathcal B(Tx,y)+(-1)^{p(T)p(x)}\mathcal B(x,Ty)=0\qquad\text{for all homogeneous }x,y\in M.`


In the basis $`e_{1^+},\ldots,e_{m^+},e_{1^-},\ldots,e_{m^-}` ($`e_0` last if $`N` is odd),
then $`e_2,e_4,\ldots,e_{2n},e_1,e_3,\ldots,e_{2n-1}`, the Gram matrix of $`-\mathcal B` is
the matrix $`G` of \[FSS00, §2.27\].

Formalized in Lean: `OspOddDeformations.OspN.rho_ospCond`, `OspOddDeformations.OspN.rho_bracket`, `OspOddDeformations.OspN.rhoBasis_linearIndependent`, `OspOddDeformations.OspN.rho_span`, `OspOddDeformations.OspN.gram_ordOdd`, `OspOddDeformations.OspN.gram_ordEven`, `OspOddDeformations.OspN.ordOdd_bijective`, `OspOddDeformations.OspN.ordEven_bijective`.
:::

:::proof "prop_osp" (uses := "lem_base")
Proof: the paper, §3.
:::

