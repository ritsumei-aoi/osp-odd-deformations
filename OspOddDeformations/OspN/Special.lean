import OspOddDeformations.OspN.FBeta

/-!
# `D(2,1) = osp(4|2)` (paper Remark 6.2)

The fermionic index of `N = 4` is `evenIdx 2`, and `n = 1`. The superdimension is `(9|8)`, and the
results hold without change: the headline statements, instantiated.
-/

namespace OspOddDeformations
namespace OspN

/-- Paper Remark 6.2: `osp(4|2)` has 9 even basis elements. -/
theorem d21_even_card :
    (Finset.univ.filter (fun X : OspBasis (evenIdx 2) 1 => parity X = 0)).card = 9 := by
  decide

/-- Paper Remark 6.2: `osp(4|2)` has 8 odd basis elements. -/
theorem d21_odd_card :
    (Finset.univ.filter (fun X : OspBasis (evenIdx 2) 1 => parity X = 1)).card = 8 := by
  decide

/-- Paper Remark 6.2, Theorem 4.2's coefficient at `D(2,1)`: `Γ_β = δh̃`. -/
theorem d21_Gamma_eq_delta_hTilde (x y : OspMod (evenIdx 2) 1) :
    Gamma x y = delta hTilde x y := by
  exact Gamma_eq_delta_hTilde x y

/-- Paper Remark 6.2, Theorem 4.5 at `D(2,1)`. -/
theorem d21_intertwining (x y : RMod (evenIdx 2) 1) :
    bracketR (TBeta x) (TBeta y) = TBeta (bracketRBeta x y) := by
  exact intertwining x y

/-- Paper Remark 6.2, Corollary 4.8 at `D(2,1)`. -/
theorem d21_intertwining_fBeta (x y : RMod (evenIdx 2) 1) :
    bracketR (TBetaF x) (TBetaF y) = TBetaF (bracketRBeta x y) := by
  exact intertwining_fBeta x y

end OspN
end OspOddDeformations
