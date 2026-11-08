import OspOddDeformations.OspN.Multi.Defs
import OspOddDeformations.OspN.Multi.Grassmann
import OspOddDeformations.OspN.Multi.UMBij
import OspOddDeformations.OspN.Multi.Theta
import OspOddDeformations.OspN.Multi.R1
import OspOddDeformations.OspN.Multi.Parity
import OspOddDeformations.OspN.Multi.Factor

/-!
# Multiple odd parameters: the statements (definitions in `Multi/Defs.lean`)

The definitions are in `Multi/Defs.lean`, so that the lemma modules can import them; the
statements below are proved with `Multi/Grassmann.lean` etc.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-! ## The intertwining, the invertibility of `U`, and `Θ` for `r ≤ 3` -/

/-- For every even `Θ` with `ΘJΘᵀ = J − Ω`, `U` intertwines the deformed bracket (5.3) with
`[·,·]_0` (Thm 5.3: `[UX,UY]_0 = U([X,Y]_β)` for all `X,Y ∈ 𝔤_R`), for all `x y`. No condition on
`Θ`'s constant part: the paper's proof uses only `ΘJΘᵀ = J − Ω`. -/
theorem intertwining_multi (Θ : I n → I n → GR F n r)
    (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v)
    (x y : RModM F n r) :
    bracket0M (UM Θ x) (UM Θ y) = UM Θ (bracketBetaM x y) := by
  rw [UM_eq_comp Θ hEven x, UM_eq_comp Θ hEven y, UM_eq_comp Θ hEven (bracketBetaM x y),
    thetaStar_bracket Θ hEven hΘ, vChi_bracket]

/-- `U` is invertible (Prop 5.2's last sentence). Needs only the constant part `𝕀`. -/
theorem UM_bijective (Θ : I n → I n → GR F n r)
    (hId : ∀ u w, Θ u w ∅ = if u = w then 1 else 0) :
    Function.Bijective (UM Θ) :=
  UM_bijective_of_id Θ hId

/-- At `r ≤ 3`, `Θ = 𝕀 + ½ΩJ` is even, has identity constant part, and satisfies
`ΘJΘᵀ = J − Ω`. -/
theorem thetaHalf_spec (hr : r ≤ 3) :
    (∀ u w, IsEvenGR (thetaHalf (F := F) (n := n) (r := r) u w)) ∧
    (∀ u w, thetaHalf (F := F) (n := n) (r := r) u w ∅ = if u = w then 1 else 0) ∧
    (∀ u v, thetaJthetaT (thetaHalf (F := F) (n := n) (r := r)) u v = JR u v - OmegaR u v) :=
  ⟨thetaHalf_even, thetaHalf_empty, thetaHalf_JThetaT hr⟩

/-! ## Checks on the presentation (as `kappaMulR_sq` etc. are for `r = 1`) -/

/-- `κ_s κ_s = 0`. -/
theorem gs_self_singleton (s : Fin r) : gs {s} {s} = 0 := by
  exact gs_eq_zero_of_not_disjoint (by simp)

/-- `κ_s κ_t = - κ_t κ_s` for `s ≠ t`. -/
theorem gs_singleton_anticomm (s t : Fin r) (h : s ≠ t) : gs {s} {t} = - gs {t} {s} := by
  -- `h` is not needed (both sides vanish at `s = t`); the hypothesis is kept in the statement.
  have _ := h
  rw [gs_comm {s} {t}]; simp

/-- At `r = 1` the deformed bracket is `Kappa.lean`'s `bracketRBetaBasis` (Thm 4.5's), in all four
cases. -/
theorem bracketBetaMBasis_r1 (p q : RBasis F n) :
    bracketBetaMBasis (F := F) (n := n) (r := 1) (p.1, toS1 p.2) (q.1, toS1 q.2) =
      ofR1 (bracketRBetaBasis p q) := by
  exact bracketBetaMBasis_r1' p q

end Multi
end OspN
end OspOddDeformations
