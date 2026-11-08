import OspOddDeformations.OspN.Presented.MultiDefs
import OspOddDeformations.OspN.Multi.ThetaSeriesCore
import Mathlib.Algebra.Ring.GeomSum

/-!
# `Θ = (𝕀 + ΩJ)^{1/2}` and its inverse

Over any commutative `ℚ`-algebra `Z`: if `J² = −1`, `Jᵀ = −J`, `Ωᵀ = −Ω` and `(ΩJ)^m = 0`, then
`Θ = Σ_{k<m} C(1/2,k)(ΩJ)^k` satisfies `Θ² = 𝕀 + ΩJ` and `ΘJΘᵀ = J − Ω`, and
`Θ⁻¹ = Θ Σ_{k<m} (−ΩJ)^k` is a two-sided inverse with `Θ⁻¹(J − Ω)Θ⁻ᵀ = J`. This is the algebra of
`Multi/ThetaSeriesCore.lean`, restated for a general ring (its `sqrtPoly` is reused).

Applied to the centre of the presented algebra over `R_r`, with `m = ⌊r/2⌋ + 1` (`thetaM`): the
entries of `(ΩJ)^k` are combinations of products of `2k` of the `κ_s`, which vanish for `2k > r`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open scoped Matrix

section general

variable {Z : Type} [CommRing Z] [Algebra ℚ Z] {ι : Type} [Fintype ι] [DecidableEq ι]
variable (Jm Om : Matrix ι ι Z) (m : ℕ)

/-- `Θ = Σ_{k<m} C(1/2,k) (ΩJ)^k`. -/
noncomputable def thetaOf : Matrix ι ι Z :=
  ∑ k ∈ Finset.range m, Ring.choose (1 / 2 : ℚ) k • (Om * Jm) ^ k

/-- `Θ⁻¹ = Θ Σ_{k<m} (−ΩJ)^k`. -/
noncomputable def thetaInvOf : Matrix ι ι Z :=
  thetaOf Jm Om m * ∑ k ∈ Finset.range m, (-(Om * Jm)) ^ k

variable {Jm Om m}

open Polynomial in
/-- `Σ_{k<m} (−X)^k`. -/
noncomputable def geomNeg (m : ℕ) : ℚ[X] := ∑ k ∈ Finset.range m, (-X) ^ k

open Polynomial in
theorem thetaOf_eq_aeval : thetaOf Jm Om m = aeval (Om * Jm) (Multi.sqrtPoly m) := by
  unfold thetaOf Multi.sqrtPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Algebra.smul_def]

open Polynomial in
theorem thetaInvOf_eq_aeval :
    thetaInvOf Jm Om m = aeval (Om * Jm) (Multi.sqrtPoly m * geomNeg m) := by
  rw [thetaInvOf, thetaOf_eq_aeval, map_mul, geomNeg, map_sum]
  simp

open Polynomial in
theorem aeval_X_pow_mul (hQ : (Om * Jm) ^ m = 0) (h : ℚ[X]) :
    aeval (Om * Jm) (X ^ m * h) = 0 := by
  rw [map_mul, map_pow, aeval_X, hQ, zero_mul]

theorem thetaOf_mul_self (hQ : (Om * Jm) ^ m = 0) :
    thetaOf Jm Om m * thetaOf Jm Om m = 1 + Om * Jm := by
  obtain ⟨h, hh⟩ := Multi.sqrtPoly_sq_dvd m
  have hp : Multi.sqrtPoly m * Multi.sqrtPoly m = (1 + Polynomial.X) + Polynomial.X ^ m * h := by
    rw [← hh]; ring
  rw [thetaOf_eq_aeval, ← map_mul, hp, map_add, aeval_X_pow_mul hQ]
  simp

open Polynomial in
theorem sqrtPoly_mul_inv (m : ℕ) : ∃ h : ℚ[X],
    Multi.sqrtPoly m * (Multi.sqrtPoly m * geomNeg m) = 1 + X ^ m * h := by
  obtain ⟨h, hh⟩ := Multi.sqrtPoly_sq_dvd m
  have hg := geom_sum_mul_neg (-X : ℚ[X]) m
  refine ⟨h * geomNeg m - (-1) ^ m, ?_⟩
  have hp : Multi.sqrtPoly m * Multi.sqrtPoly m = (1 + X) + X ^ m * h := by rw [← hh]; ring
  rw [← mul_assoc, hp, geomNeg]
  rw [show (1 - -X : ℚ[X]) = 1 + X by ring] at hg
  rw [add_mul, mul_comm (1 + X), hg, neg_pow]
  ring

theorem thetaOf_mul_inv (hQ : (Om * Jm) ^ m = 0) : thetaOf Jm Om m * thetaInvOf Jm Om m = 1 := by
  obtain ⟨h, hh⟩ := sqrtPoly_mul_inv m
  rw [thetaOf_eq_aeval, thetaInvOf_eq_aeval, ← map_mul, hh, map_add, aeval_X_pow_mul hQ, map_one,
    add_zero]

theorem thetaInv_mul_thetaOf (hQ : (Om * Jm) ^ m = 0) :
    thetaInvOf Jm Om m * thetaOf Jm Om m = 1 := by
  obtain ⟨h, hh⟩ := sqrtPoly_mul_inv m
  rw [thetaOf_eq_aeval, thetaInvOf_eq_aeval, ← map_mul, mul_comm, hh, map_add, aeval_X_pow_mul hQ,
    map_one, add_zero]

omit [Algebra ℚ Z] in
theorem J_mul_QT_pow (hJJ : Jm * Jm = -1) (hJt : Jmᵀ = -Jm) (hOt : Omᵀ = -Om) (k : ℕ) :
    Jm * ((Om * Jm)ᵀ) ^ k = (Om * Jm) ^ k * Jm := by
  have h1 : Jm * (Om * Jm)ᵀ = (Om * Jm) * Jm := by
    simp only [Matrix.transpose_mul, hJt, hOt, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [← Matrix.mul_assoc, hJJ, Matrix.mul_assoc, hJJ, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one]
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
  | succ k ih =>
    rw [pow_succ' (Om * Jm)ᵀ, pow_succ' (Om * Jm), ← Matrix.mul_assoc, h1, Matrix.mul_assoc, ih]
    simp only [Matrix.mul_assoc]

theorem thetaOf_J_thetaOfT (hJJ : Jm * Jm = -1) (hJt : Jmᵀ = -Jm) (hOt : Omᵀ = -Om)
    (hQ : (Om * Jm) ^ m = 0) : thetaOf Jm Om m * Jm * (thetaOf Jm Om m)ᵀ = Jm - Om := by
  have hJT : Jm * (thetaOf Jm Om m)ᵀ = thetaOf Jm Om m * Jm := by
    unfold thetaOf
    rw [Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.transpose_pow, J_mul_QT_pow hJJ hJt hOt,
      Matrix.smul_mul]
  rw [Matrix.mul_assoc, hJT, ← Matrix.mul_assoc, thetaOf_mul_self hQ, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_neg, Matrix.mul_one, sub_eq_add_neg]

theorem thetaInv_conj (hJJ : Jm * Jm = -1) (hJt : Jmᵀ = -Jm) (hOt : Omᵀ = -Om)
    (hQ : (Om * Jm) ^ m = 0) :
    thetaInvOf Jm Om m * (Jm - Om) * (thetaInvOf Jm Om m)ᵀ = Jm := by
  rw [← thetaOf_J_thetaOfT hJJ hJt hOt hQ]
  calc thetaInvOf Jm Om m * (thetaOf Jm Om m * Jm * (thetaOf Jm Om m)ᵀ) * (thetaInvOf Jm Om m)ᵀ
      = (thetaInvOf Jm Om m * thetaOf Jm Om m) * Jm
          * (thetaInvOf Jm Om m * thetaOf Jm Om m)ᵀ := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Jm := by rw [thetaInv_mul_thetaOf hQ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end general

/-! ## In the centre of the presented algebra over `R_r` -/

section presented

variable {P : Type} [CommRing P] {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
variable {r : ℕ} (J : I → I → P) (g : K → K → P) (β : Fin r → I → K → P) (δ : Fin r → I → K → P)

/-- The centre of `SrcM J g β`, a commutative ring. -/
abbrev ZM : Type := Subalgebra.center P (SrcM J g β)

/-- `J`, in the centre. -/
noncomputable def JZM : Matrix I I (ZM J g β) := (Matrix.of J).map (algebraMap P (ZM J g β))

/-- `Ω`, in the centre. -/
noncomputable def OmZM : Matrix I I (ZM J g β) :=
  Matrix.of fun u v => ⟨omegaM δ u v, omegaM_mem_center δ u v⟩

variable {J g β δ}

omit [Fintype I] [DecidableEq I] in
theorem OmZM_transpose : (OmZM J g β δ)ᵀ = -OmZM J g β δ := by
  ext u v
  simp only [Matrix.transpose_apply, OmZM, Matrix.of_apply, Matrix.neg_apply, NegMemClass.coe_neg]
  exact omegaM_antisymm δ u v

omit [DecidableEq I] [Fintype K] in
theorem coe_matrix_mul_apply (A B : Matrix I I (ZM J g β)) (u w : I) :
    ((A * B) u w : SrcM J g β) = ∑ z, (A u z : SrcM J g β) * (B z w : SrcM J g β) := by
  rw [Matrix.mul_apply]
  push_cast
  rfl

omit [DecidableEq I] in
theorem QZM_mem_kDeg (u w : I) : ((OmZM J g β δ * JZM J g β) u w : SrcM J g β) ∈ kDeg 2 := by
  rw [coe_matrix_mul_apply]
  refine Submodule.sum_mem _ fun z _ => ?_
  have h : ((JZM J g β z w : ZM J g β) : SrcM J g β) = J z w • (1 : SrcM J g β) := by
    simp [JZM, Algebra.smul_def]
  rw [h, mul_smul_comm, mul_one]
  exact Submodule.smul_mem _ _ (omegaM_mem_kDeg δ u z)

theorem QZM_pow_mem_kDeg (k : ℕ) (u w : I) :
    (((OmZM J g β δ * JZM J g β) ^ k) u w : SrcM J g β) ∈ kDeg (2 * k) := by
  induction k generalizing u w with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact Submodule.subset_span ⟨[], rfl, by simp⟩
    · simp
  | succ k ih =>
    rw [pow_succ, coe_matrix_mul_apply]
    refine Submodule.sum_mem _ fun z _ => ?_
    have h := kDeg_mul (ih u z) (QZM_mem_kDeg (δ := δ) z w)
    rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at h

theorem QZM_pow_eq_zero : (OmZM J g β δ * JZM J g β) ^ (r / 2 + 1) = 0 := by
  ext u w
  have h := QZM_pow_mem_kDeg (J := J) (g := g) (β := β) (δ := δ) (r / 2 + 1) u w
  rw [kDeg_eq_bot (by omega), Submodule.mem_bot] at h
  rw [h]
  rfl

variable [Algebra ℚ P]

noncomputable instance : Algebra ℚ (ZM J g β) :=
  ((algebraMap P (ZM J g β)).comp (algebraMap ℚ P)).toAlgebra

/-- `Θ = (𝕀 + ΩJ)^{1/2} = Σ_{k≤⌊r/2⌋} C(1/2,k)(ΩJ)^k`, in the centre (Thm 5.1). -/
noncomputable def thetaM : Matrix I I (ZM J g β) :=
  thetaOf (JZM J g β) (OmZM J g β δ) (r / 2 + 1)

/-- `Θ⁻¹`, in the centre. -/
noncomputable def thetaInvM : Matrix I I (ZM J g β) :=
  thetaInvOf (JZM J g β) (OmZM J g β δ) (r / 2 + 1)

variable (hJJ : JZM J g β * JZM J g β = -1) (hJt : (JZM J g β)ᵀ = -JZM J g β)
include hJJ hJt

/-- `ΘJΘᵀ = J − Ω` (the proof of Thm 5.1). -/
theorem thetaM_J_thetaMT :
    thetaM (δ := δ) * JZM J g β * (thetaM (δ := δ))ᵀ = JZM J g β - OmZM J g β δ :=
  thetaOf_J_thetaOfT hJJ hJt OmZM_transpose QZM_pow_eq_zero

/-- `Θ⁻¹(J − Ω)Θ⁻ᵀ = J`. -/
theorem thetaInvM_conj :
    thetaInvM (δ := δ) * (JZM J g β - OmZM J g β δ) * (thetaInvM (δ := δ))ᵀ = JZM J g β :=
  thetaInv_conj hJJ hJt OmZM_transpose QZM_pow_eq_zero

omit hJJ hJt

theorem thetaM_mul_inv : thetaM (J := J) (g := g) (β := β) (δ := δ) * thetaInvM (δ := δ) = 1 :=
  thetaOf_mul_inv QZM_pow_eq_zero

theorem thetaInvM_mul : thetaInvM (J := J) (g := g) (β := β) (δ := δ) * thetaM (δ := δ) = 1 :=
  thetaInv_mul_thetaOf QZM_pow_eq_zero

end presented

end Presented
end OspN
end OspOddDeformations
