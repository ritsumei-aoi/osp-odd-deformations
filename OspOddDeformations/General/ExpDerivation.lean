import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The exponential of nilpotent derivations of a bilinear map

For an `R`-bilinear map `μ : M →ₗ N →ₗ P` and nilpotent endomorphisms `D_M`, `D_N`, `D_P` with
`D_P (μ x y) = μ (D_M x) y + μ x (D_N y)`, the exponentials satisfy
`exp D_P (μ x y) = μ (exp D_M x) (exp D_N y)` (`exp_bilin_of_derivation`). With
`M = N = P` and one `D`, the exponential of a nilpotent derivation of any bilinear product (not
necessarily associative, nor a Lie bracket) is an automorphism of it
(`exp_bilin_of_derivation'`). This generalizes mathlib's
`Module.End.exp_mul_of_derivation`, whose proof it follows.

This file depends on mathlib only.
-/

namespace OspOddDeformations
namespace General

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] [Module ℚ M] [Module ℚ N] [Module ℚ P]

theorem exp_bilin_of_derivation (μ : M →ₗ[R] N →ₗ[R] P) (DM : Module.End R M)
    (DN : Module.End R N) (DP : Module.End R P)
    (h_der : ∀ x y, DP (μ x y) = μ (DM x) y + μ x (DN y))
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP) (x : M) (y : N) :
    exp DP (μ x y) = μ (exp DM x) (exp DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DN.lTensor M
  let DR : Module.End R (M ⊗[R] N) := DM.rTensor N
  have h_nilL : IsNilpotent DL := hN.map <| lTensorAlgHom R N M
  have h_nilR : IsNilpotent DR := hM.map <| rTensorAlgHom R M N
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift μ with hm
  have h₁ : exp DP (μ x y) = m (exp (DL + DR) (x ⊗ₜ[R] y)) := by
    suffices exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) by
      simpa [hm] using LinearMap.congr_fun this (x ⊗ₜ[R] y)
    apply commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) hP
    ext a b
    simp [DL, DR, hm, h_der, add_comm]
  have h₂ : exp DL = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have h₃ : exp DR = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  simp [h₁, exp_add_of_commute h_comm h_nilL h_nilR, h₂, h₃, hm]

/-- One derivation `D` of a bilinear product `μ` on `M`: `exp D` is an automorphism of `μ`. -/
theorem exp_bilin_of_derivation' (μ : M →ₗ[R] M →ₗ[R] M) (D : Module.End R M)
    (h_der : ∀ x y, D (μ x y) = μ (D x) y + μ x (D y)) (h_nil : IsNilpotent D) (x y : M) :
    exp D (μ x y) = μ (exp D x) (exp D y) :=
  exp_bilin_of_derivation μ D D D h_der h_nil h_nil h_nil x y

end General
end OspOddDeformations
