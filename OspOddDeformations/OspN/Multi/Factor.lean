import OspOddDeformations.OspN.Multi.FactorDefs
import OspOddDeformations.OspN.Multi.Factorization
import OspOddDeformations.OspN.Multi.ThetaStarBracket
import OspOddDeformations.OspN.Multi.VChiBracket

/-!
# Statements of the factorization `U = Θ_* ∘ V_γ` (paper Prop 5.4)

The definitions are in `Multi/FactorDefs.lean`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-! ## Statements -/

/-- **Prop 5.4**: `U = Θ_* ∘ V_γ` (for even `Θ`). -/
theorem UM_eq_comp (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (x : RModM F n r) :
    UM Θ x = ThetaStar Θ (VChi gammaR x) :=
  UM_eq_comp' Θ hEven x

/-- **(i)** `Θ_*` intertwines `[·,·]_{J-Ω}` with `[·,·]_0` (Prop 5.4, second intertwining). -/
theorem thetaStar_bracket (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (x y : RModM F n r) :
    bracket0M (ThetaStar Θ x) (ThetaStar Θ y) = ThetaStar Θ (bracketJM JmOmega x y) :=
  thetaStar_bracket' Θ hEven hΘ x y

/-- **(ii)** `V_γ` intertwines `[·,·]_β` with `[·,·]_{J-Ω}` (Prop 5.4, first intertwining). -/
theorem vChi_bracket (x y : RModM F n r) :
    bracketJM JmOmega (VChi gammaR x) (VChi gammaR y) = VChi gammaR (bracketBetaM x y) :=
  vChi_bracket' x y

end Multi
end OspN
end OspOddDeformations
