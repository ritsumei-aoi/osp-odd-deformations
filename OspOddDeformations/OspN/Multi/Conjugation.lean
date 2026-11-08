import OspOddDeformations.OspN.Multi.ThetaSeries
import OspOddDeformations.OspN.Multi.Reduction

/-!
# The paper's definition of `[·,·]_β` (Theorem 5.3)

Theorem 5.3 defines `[X,Y]_β := U⁻¹[UX,UY]_0`; the development defines `bracketBetaM` by (5.3).
They agree, for the `Θ` of Theorem 5.1. Also the hypothesis `CoreId` of the reduction lemma
`intertwining_of_core`, at that `Θ`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- Paper Theorem 5.3: `[X,Y]_β` (here defined by (5.3)) is `U⁻¹[UX,UY]_0`, i.e. it is the unique
`z` with `Uz = [UX,UY]_0`. -/
theorem bracketBetaM_eq_conj (x y z : RModM F n r) :
    UM thetaSeries z = bracket0M (UM thetaSeries x) (UM thetaSeries y) ↔
      z = bracketBetaM x y := by
  constructor
  · intro h
    apply (UM_thetaSeries_bijective (F := F) (n := n) (r := r)).1
    rw [h, intertwining_thetaSeries]
  · rintro rfl
    exact (intertwining_thetaSeries x y).symm

/-- The basis vector `κ_∅ X` of `𝔤_{R_r}`, for evaluating an intertwining at one basis pair. -/
noncomputable def eM0 (X : OspBasis F n) : RModM F n r :=
  fun q => if q = (X, (∅ : Finset (Fin r))) then 1 else 0

theorem grComp_eM0 (X Z : OspBasis F n) :
    grComp (eM0 (r := r) X) Z = if Z = X then gone else 0 := by
  funext B
  by_cases h : Z = X
  · subst h; by_cases hB : B = ∅ <;> simp [grComp, eM0, gone, hB]
  · simp [grComp, eM0, h]

/-- The double sum of `stepL`/`stepR` at `x = κ_∅X`, `y = κ_∅Y` collapses to its `(X, Y)` term. -/
theorem sum_eM0_collapse (X Y : OspBasis F n) (c : OspBasis F n → OspBasis F n → GR F n r) :
    ∑ Z : OspBasis F n, ∑ Z' : OspBasis F n,
      gmul (gmul (grComp (eM0 (r := r) X) Z) (sigPow (parity Z) (grComp (eM0 (r := r) Y) Z')))
        (c Z Z') = c X Y := by
  rw [Finset.sum_eq_single X, Finset.sum_eq_single Y]
  · simp [grComp_eM0, sigPow_gone, gone_gmul]
  · intro Z' _ h
    have h0 : sigPow (parity X) (0 : GR F n r) = 0 := by simp [sigPow, sig_zero]
    simp [grComp_eM0, h, h0, gmul_zero_right, gmul_zero_left]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro Z _ h; simp [grComp_eM0, h, gmul_zero_left]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The hypothesis `CoreId` of `intertwining_of_core` holds at the `Θ` of Theorem 5.1. -/
theorem coreId_thetaSeries : CoreId (thetaSeries (F := F) (n := n) (r := r)) := by
  intro X Y V
  obtain ⟨hE, -, -⟩ := thetaSeries_spec (F := F) (n := n) (r := r)
  have h := congrArg (fun z => grComp z V)
    (intertwining_thetaSeries (F := F) (n := n) (r := r) (eM0 X) (eM0 Y))
  rw [stepL _ (uMat_parity _ hE), stepR, sum_eM0_collapse, sum_eM0_collapse] at h
  exact h

end Multi
end OspN
end OspOddDeformations
