import OspOddDeformations.OspN.Multi.FactorDefs
import OspOddDeformations.OspN.Multi.Reduction

/-!
# Generic linear maps and bracket lifts in coefficient form

`linM A0` is the even left-`R_r`-linear map with basis images `A0`; `UM`, `ThetaStar`, `VChi` are of
this form. `liftB B0` is the super-bilinear bracket with basis data `B0`; `bracketJM J'` is of this
form. In `grComp` form (coefficient functions `OspBasis → GR`) both become matrix products, and an
intertwining `[A x, A y]_{B1} = C [x, y]_{B2}` reduces to an identity of matrices in `GR`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- The even left-`R_r`-linear map with images `A0 X` of the basis symbols. -/
noncomputable def linM (A0 : OspBasis F n → RModM F n r) (x : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, x p • gsmul (gmono p.2 1) (A0 p.1)

/-- The super-bilinear bracket with basis data `B0`. -/
noncomputable def liftB (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r) :
    RModM F n r :=
  ∑ p : RBasisM F n r, ∑ q : RBasisM F n r,
    (x p * y q) • (((-1 : ℚ) ^ (q.2.card * (parity p.1).val)) •
      gsmul (gmono p.2 1) (gsmul (gmono q.2 1) (B0 p.1 q.1)))

theorem UM_eq_linM (Θ : I n → I n → GR F n r) : UM Θ = linM (UBasis0 Θ) := rfl
theorem ThetaStar_eq_linM (Θ : I n → I n → GR F n r) : ThetaStar Θ = linM (ThetaStarBasis0 Θ) := rfl
theorem VChi_eq_linM (χ : I n → F.K → GR F n r) : VChi χ = linM (VBasis0 χ) := rfl
theorem bracketJM_eq_liftB (J' : I n → I n → GR F n r) :
    bracketJM J' = liftB (bracketJBasis0 J') := rfl

theorem grComp_linM (A0 : OspBasis F n → RModM F n r) (x : RModM F n r) (W : OspBasis F n) :
    grComp (linM A0 x) W = ∑ Z : OspBasis F n, gmul (grComp x Z) (grComp (A0 Z) W) := by
  funext T
  simp only [grComp, linM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    gsmul_apply_eq]
  refine Finset.sum_congr rfl fun Z _ => ?_
  conv_rhs => simp only [gmul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [gmul_gmono_one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [mul_smul_comm]; rfl
  · simp

theorem ite_sum' {α M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p] (s : Finset α)
    (f : α → M) : (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem grComp_liftB (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r)
    (V : OspBasis F n) :
    grComp (liftB B0 x y) V = ∑ Z : OspBasis F n, ∑ Z' : OspBasis F n,
      gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z'))) (grComp (B0 Z Z') V) := by
  funext T
  simp only [grComp, liftB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    gsmul_apply_eq]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Z' _ => ?_
  rw [gmul_gmul_apply]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  rw [comp_gsmul, gmul_gmono_one_apply]
  simp only [gmul_gmono_one_apply, Finset.smul_sum, smul_ite, smul_zero]
  simp_rw [ite_sum']
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.sum_eq_single (S' ∪ C)]
  · by_cases h : S ∪ (S' ∪ C) = T
    · simp only [h, Finset.union_assoc, ite_true]
      rw [gs_cocycle S S' C, sigPow_apply]
      simp only [grComp, Algebra.smul_def, map_mul, map_pow, map_neg, map_one, mul_comm S'.card]
      ring
    · simp [h, Finset.union_assoc]
  · intro D _ hD; simp [Ne.symm hD]
  · simp

/-- **Reduction of an intertwining to a matrix identity.** -/
theorem lift_intertwine (A0 C0 : OspBasis F n → RModM F n r)
    (B1 B2 : OspBasis F n → OspBasis F n → RModM F n r)
    (hA : ∀ Z W, HasParity (parity Z + parity W) (grComp (A0 Z) W))
    (core : ∀ Z Z' V,
      ∑ W : OspBasis F n, ∑ W' : OspBasis F n,
        gmul (gmul (grComp (A0 Z) W) (sigPow (parity W) (grComp (A0 Z') W')))
          (grComp (B1 W W') V)
      = ∑ V' : OspBasis F n, gmul (grComp (B2 Z Z') V') (grComp (C0 V') V))
    (x y : RModM F n r) :
    liftB B1 (linM A0 x) (linM A0 y) = linM C0 (liftB B2 x y) := by
  funext ⟨V, T⟩
  have h : grComp (liftB B1 (linM A0 x) (linM A0 y)) V = grComp (linM C0 (liftB B2 x y)) V := by
    rw [grComp_liftB, grComp_linM]
    simp only [grComp_linM, grComp_liftB]
    have key : ∀ W W' : OspBasis F n,
        gmul (∑ Z, gmul (grComp x Z) (grComp (A0 Z) W))
          (sigPow (parity W) (∑ Z', gmul (grComp y Z') (grComp (A0 Z') W'))) =
        ∑ Z, ∑ Z', gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z')))
          (gmul (grComp (A0 Z) W) (sigPow (parity W) (grComp (A0 Z') W'))) := by
      intro W W'
      rw [sigPow_sum, gmul_sum_left]
      refine Finset.sum_congr rfl fun Z _ => ?_
      rw [gmul_sum_right]
      refine Finset.sum_congr rfl fun Z' _ => ?_
      exact core_term (parity Z) (parity W) _ _ _ _ (hA Z W)
    simp only [key, gmul_sum_left, gmul_assoc]
    rw [sum_comm4']
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Z _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Z' _ => ?_
    have hc := core Z Z' V
    simp only [gmul_assoc] at hc
    simp only [← gmul_sum_right]
    refine congrArg (fun q => gmul (grComp x Z) (gmul (sigPow (parity Z) (grComp y Z')) q)) ?_
    simp only [gmul_sum_right]
    exact hc
  exact congrFun h T

end Multi
end OspN
end OspOddDeformations
