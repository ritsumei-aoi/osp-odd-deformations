import Verso
import VersoManual
import VersoBlueprint
import OspOddDeformations.OspN.Audit

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Machine-checked formalization" =>

# What is proved

:::proposition "app_controls" (lean := "OspOddDeformations.OspN.control_N1_bracket, OspOddDeformations.OspN.control_N1_gamma, OspOddDeformations.OspN.control_N1_hTilde, OspOddDeformations.OspN.control_N1_fBeta, OspOddDeformations.OspN.evenIdx_basis_card_1_1, OspOddDeformations.OspN.evenC2_GammaBasis_SF, OspOddDeformations.OspN.evenC2_GammaBasis_FF, OspOddDeformations.OspN.evenC2_GammaBasis_LS")
*Controls (Appendix A.1, item 9).* For $`N=1` the bracket $`[\cdot,\cdot]_0`, $`\Gamma_\beta`, $`\tilde h` and $`f_\beta`
coincide, under the evident identification of bases and coefficients, with those of the
formalization \[Repo\] of \[Aoi26\]. In particular, $`\tilde h` is the map $`h` and
$`f_\beta` the primitive of \[Aoi26, Theorem 4.1\]. For $`C(2)=\mathfrak{osp}(2|2)` the basis has
$`8` elements, and three values of $`\Gamma_\beta` are evaluated there. They
agree with an exact computation of the bracket in $`A_\beta`, made outside the
development.

Partially formalized: the controls for `N = 1` and the three values of `Γ_β` at `C(2)`; their agreement with an exact computation of the bracket in `A_β` is checked outside the development. Declarations: `OspOddDeformations.OspN.control_N1_bracket`, `OspOddDeformations.OspN.control_N1_gamma`, `OspOddDeformations.OspN.control_N1_hTilde`, `OspOddDeformations.OspN.control_N1_fBeta`, `OspOddDeformations.OspN.evenIdx_basis_card_1_1`, `OspOddDeformations.OspN.evenC2_GammaBasis_SF`, `OspOddDeformations.OspN.evenC2_GammaBasis_FF`, `OspOddDeformations.OspN.evenC2_GammaBasis_LS`.
:::

