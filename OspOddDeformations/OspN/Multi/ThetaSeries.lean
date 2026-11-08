import OspOddDeformations.OspN.Multi.Statements
import Mathlib.RingTheory.Binomial
import OspOddDeformations.OspN.Multi.ThetaSeriesCore

/-!
# `Θ = (𝕀+ΩJ)^{1/2}` for every `r`

Paper Thm 5.1: `Θ = Σ_{k≥0} C(1/2,k)(ΩJ)^k`, a finite sum ending at `k = ⌊r/2⌋`, satisfies
`ΘJΘᵀ = J − Ω`. `thetaHalf_spec` gives this at `r ≤ 3` for `𝕀 + ½ΩJ`; here it is
proved for every `r`, with the binomial coefficients `Ring.choose (1/2 : ℚ) k`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- `Q = ΩJ`. -/
noncomputable def QMat (u w : I n) : GR F n r :=
  ∑ z : I n, gmul (OmegaR u z) (JR z w)

/-- `Q^k`, as a matrix over `R_r`: `Q^0 = 𝕀`, `Q^{k+1} = Q^k Q`. -/
noncomputable def QPow : ℕ → I n → I n → GR F n r
  | 0 => fun u w => if u = w then gone else 0
  | k + 1 => fun u w => ∑ z : I n, gmul (QPow k u z) (QMat z w)

/-- `Θ = Σ_{k ≤ ⌊r/2⌋} C(1/2,k) (ΩJ)^k`, Thm 5.1. -/
noncomputable def thetaSeries (u w : I n) : GR F n r :=
  ∑ k ∈ Finset.range (r / 2 + 1), Ring.choose (1 / 2 : ℚ) k • QPow (F := F) (r := r) k u w

theorem QPow_eq_QPowG (k : ℕ) :
    QPow (F := F) (n := n) (r := r) k = QPowG OmegaR k := by
  induction k with
  | zero => rfl
  | succ k ih => funext u w; simp only [QPow, QPowG, ih]; rfl

theorem thetaSeries_eq_thetaG :
    thetaSeries (F := F) (n := n) (r := r) = thetaG OmegaR := by
  funext u w
  simp only [thetaSeries, thetaG, QPow_eq_QPowG]

/-- **Thm 5.1**: for every `r`, `Θ` is even, has constant part `𝕀`, and `ΘJΘᵀ = J − Ω`. -/
theorem thetaSeries_spec :
    (∀ u w, IsEvenGR (thetaSeries (F := F) (n := n) (r := r) u w)) ∧
    (∀ u w, thetaSeries (F := F) (n := n) (r := r) u w ∅ = if u = w then 1 else 0) ∧
    (∀ u v, thetaJthetaT (thetaSeries (F := F) (n := n) (r := r)) u v = JR u v - OmegaR u v) := by
  rw [thetaSeries_eq_thetaG]
  exact thetaG_spec OmegaR HasCard_OmegaR OmegaR_antisymm

/-- For every `r`, the deformed bracket (5.3) is intertwined with `[·,·]_0` by `U` at this `Θ`
(Thm 5.3's identity for all `X,Y ∈ 𝔤_R`, with the `Θ` of Thm 5.1). -/
theorem intertwining_thetaSeries (x y : RModM F n r) :
    bracket0M (UM thetaSeries x) (UM thetaSeries y) = UM thetaSeries (bracketBetaM x y) := by
  obtain ⟨hE, -, hΘ⟩ := thetaSeries_spec (F := F) (n := n) (r := r)
  exact intertwining_multi thetaSeries hE hΘ x y

/-- For every `r`, `U` at this `Θ` is invertible. -/
theorem UM_thetaSeries_bijective :
    Function.Bijective (UM (thetaSeries (F := F) (n := n) (r := r))) := by
  obtain ⟨-, hI, -⟩ := thetaSeries_spec (F := F) (n := n) (r := r)
  exact UM_bijective thetaSeries hI

/-- Check: at `r ≤ 3` the series is `𝕀 + ½ΩJ`. -/
theorem thetaSeries_eq_thetaHalf (hr : r ≤ 3) :
    thetaSeries (F := F) (n := n) (r := r) = thetaHalf := by
  funext u w
  have hQ : ∀ a b : I n, QMat (F := F) (r := r) a b = ∑ z : I n, gmul (OmegaR a z) (JR z b) :=
    fun _ _ => rfl
  have hQ1 : QPow (F := F) (r := r) 1 u w = QMat u w := by
    simp only [QPow]
    rw [Finset.sum_eq_single u]
    · simp [gone_gmul]
    · intro z _ hz
      simp [hz.symm, gmul_zero_left]
    · simp
  unfold thetaSeries thetaHalf
  rcases (by omega : r < 2 ∨ r / 2 = 1) with h | h
  · have h0 : r / 2 = 0 := by omega
    have hΩ : ∀ a b : I n, OmegaR (F := F) (r := r) a b = 0 := fun a b =>
      HasCard.of_lt h (HasCard_OmegaR a b)
    rw [h0]
    simp [QPow, hΩ, gmul_zero_left]
  · rw [h]
    rw [Finset.sum_range_succ, Finset.sum_range_one, hQ1, hQ]
    simp only [QPow, Ring.choose_zero_right, one_smul, Ring.choose_one_right]

end Multi
end OspN
end OspOddDeformations
