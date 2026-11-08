import Verso
import VersoManual
import VersoBlueprint
import OspOddDeformations.OspN.Audit

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Specializations and remarks" =>

:::proposition "rem_even" (lean := "OspOddDeformations.OspN.Multi.thetaG_spec")
*Remark 6.1 (The even direction).* The construction of \[BS17, Section 4\] has an even, $`K`-valued part as well as the
odd, $`\kappa`-valued part treated here: the homogeneous relations $`[b_u,b_v]=KJ_{uv}` and
$`\{a_i,a_j\}=Kg_{ij}`, which this paper specializes to $`K=1` (Remark 2.1).
Deformations in $`K`, with $`K` kept as an indeterminate, are not considered. The argument does,
however, give the following. For an even antisymmetric $`\Omega` with $`\Omega J` nilpotent,
the perturbed bosonic form $`J-\Omega` is equivalent to $`J`: $`\Theta J\Theta^{\mathsf T}=J-\Omega`
with $`\Theta=(\mathbb I+\Omega J)^{1/2}`, by the proof of Theorem 5.1. With
multiple odd parameters such a perturbation arises at second order from the odd one
(Remark 5.6).

Partially formalized: the claim that `J − Ω` is equivalent to `J` by `Θ = (𝕀+ΩJ)^{1/2}`, for an even antisymmetric `Ω` whose entries have `κ`-degree 2. Declarations: `OspOddDeformations.OspN.Multi.thetaG_spec`.
:::

:::proposition "rem_d21" (lean := "OspOddDeformations.OspN.d21_even_card, OspOddDeformations.OspN.d21_odd_card, OspOddDeformations.OspN.d21_Gamma_eq_delta_hTilde, OspOddDeformations.OspN.d21_intertwining, OspOddDeformations.OspN.d21_intertwining_fBeta, OspOddDeformations.OspN.GroupB.d21_killing_zero, OspOddDeformations.OspN.GroupB.sdim_9_8_iff")
*Remark 6.2 ($`D(2,1)`).* For $`N=4`, $`n=1` the algebra is $`D(2,1)=\mathfrak{osp}(4|2)`, the member $`\alpha=1` of the family
$`D(2,1;\alpha)` \[FSS00, §2.20\]. Its Killing form vanishes \[FSS00, §2.23\], as does that of every $`D(n+1,n)`. The results above hold for
these cases without change, since the argument does not use the Killing form of
$`\mathfrak{osp}(N|2n)`. In particular, Theorem 4.9 uses Whitehead's lemma only for
$`\mathfrak{sp}(2n)`. Since $`\mathfrak{osp}(4|2)` is
the only $`\mathfrak{osp}(N|2n)` of superdimension $`(9|8)`, a member $`D(2,1;\alpha)` of the family lies in
the present setting exactly when it is isomorphic to $`D(2,1)`, as it is for
$`\alpha\in\{1,-2,-\tfrac12\}` \[FSS00, §2.20\].

Partially formalized: the superdimension of `osp(4|2)`: 9 even and 8 odd basis elements, and Theorem 4.2's `Γ_β = δh̃`, Theorem 4.5 and Corollary 4.8 at `N = 4`, `n = 1`; the Killing form of `osp(4|2)` vanishes; `osp(4|2)` is the only `osp(N|2n)` of superdimension `(9|8)`. The Killing form of every `D(n+1,n)`, and which `D(2,1;α)` are isomorphic to `D(2,1)`, are not formalized. Declarations: `OspOddDeformations.OspN.d21_even_card`, `OspOddDeformations.OspN.d21_odd_card`, `OspOddDeformations.OspN.d21_Gamma_eq_delta_hTilde`, `OspOddDeformations.OspN.d21_intertwining`, `OspOddDeformations.OspN.d21_intertwining_fBeta`, `OspOddDeformations.OspN.GroupB.d21_killing_zero`, `OspOddDeformations.OspN.GroupB.sdim_9_8_iff`.
:::

