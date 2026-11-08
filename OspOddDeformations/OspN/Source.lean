import OspOddDeformations.OspN.Kappa
import InhomogeneousDeformations.SourceWeyl
import InhomogeneousDeformations.SourceTensor
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# `Cl F`, `R F n` and `A0 F n`: the data of the realization

The realization of the source algebras for an arbitrary `FermionIndex F`: the Clifford algebra
`Cl F` with its generators `a_i`, the coefficient ring `R F n = P ⊕ κP`, and
`A0 F n = W_n ⊗ Cl F` with its grading `A0Grading`. These are pure data, written with
`F.K`/`F.dual`/`F.g`; `BK`/`QK`/`Cl`/`a`/`a_odd`/`a_mul_a_add_swap` hold over any finite index
with an involution. `R F n` depends only on `Pmn F n` (`OspN/Basis.lean`), not on the fermion
index at all.

`OspN/SourceTensor.lean` proves the `GradedAlgebra` instance of `A0Grading`, defines
`AB F n = R F n ⊗ A0 F n`, the lifts, `ι₀`, `ι_β` and `scomm`, and proves `base_realization`,
`recovery` and `recovery_delta`; `iota0_injective` is proved in `OspN/SourceIndependence.lean`,
and `recovery_unique`, `recovery_unique_delta` in `OspN/SourceUniqueness.lean`. -/

namespace OspOddDeformations
namespace OspN

open scoped TensorProduct DirectSum
open Bmn (I J)

/-! ## `Cl F` -/

/-- `BK`'s bilinear form, for a general `FermionIndex`: `BK x y := ½ Σ_i x(i)·y(F.dual i)`. -/
noncomputable def BK (F : FermionIndex) : (F.K → ℚ) →ₗ[ℚ] (F.K → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => (1 / 2 : ℚ) * ∑ i : F.K, x i * y (F.dual i))
    (by intro x1 x2 y
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; simp only [Pi.add_apply]; ring)
    (by intro c x y
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show (∑ i : F.K, c * x i * y (F.dual i)) = c * ∑ i : F.K, x i * y (F.dual i) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
        ring)
    (by intro x y1 y2
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; simp only [Pi.add_apply]; ring)
    (by intro c x y
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show (∑ i : F.K, x i * (c * y (F.dual i))) = c * ∑ i : F.K, x i * y (F.dual i) from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
        ring)

theorem BK_apply (F : FermionIndex) (x y : F.K → ℚ) :
    BK F x y = (1 / 2 : ℚ) * ∑ i : F.K, x i * y (F.dual i) := rfl

noncomputable def QK (F : FermionIndex) : QuadraticForm ℚ (F.K → ℚ) :=
  LinearMap.BilinMap.toQuadraticMap (BK F)

theorem QK_apply (F : FermionIndex) (x : F.K → ℚ) : QK F x = BK F x x := rfl

theorem polar_QK_apply (F : FermionIndex) (x y : F.K → ℚ) :
    QuadraticMap.polar (QK F) x y = BK F x y + BK F y x :=
  LinearMap.BilinMap.polar_toQuadraticMap (B := BK F) x y

noncomputable abbrev Cl (F : FermionIndex) : Type := CliffordAlgebra (QK F)

noncomputable def e (F : FermionIndex) (i : F.K) : F.K → ℚ := Pi.single i 1

noncomputable def a (F : FermionIndex) (i : F.K) : Cl F := CliffordAlgebra.ι (QK F) (e F i)

theorem a_odd (F : FermionIndex) (i : F.K) : a F i ∈ CliffordAlgebra.evenOdd (QK F) 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one (QK F) _

theorem e_apply (F : FermionIndex) (i k : F.K) : e F i k = if k = i then 1 else 0 := by
  unfold e; exact Pi.single_apply i 1 k

theorem BK_e_add_swap (F : FermionIndex) (i j : F.K) :
    BK F (e F i) (e F j) + BK F (e F j) (e F i) = F.g i j := by
  simp only [BK_apply]
  by_cases hji : j = F.dual i
  · have hij : i = F.dual j := by rw [hji, F.dual_dual]
    have h1 : (∑ k : F.K, e F i k * e F j (F.dual k)) = 1 := by
      rw [Fintype.sum_eq_single i (fun b hb => by rw [e_apply, ite_eq_right hb, zero_mul])]
      rw [e_apply, ite_eq_left rfl, one_mul, e_apply, ite_eq_left hji.symm]
    have h2 : (∑ k : F.K, e F j k * e F i (F.dual k)) = 1 := by
      rw [Fintype.sum_eq_single j (fun b hb => by rw [e_apply, ite_eq_right hb, zero_mul])]
      rw [e_apply, ite_eq_left rfl, one_mul, e_apply, ite_eq_left hij.symm]
    rw [h1, h2]
    unfold FermionIndex.g
    rw [ite_eq_left hji]; ring
  · have hij : i ≠ F.dual j := fun h => hji (by rw [h, F.dual_dual])
    have h1 : (∑ k : F.K, e F i k * e F j (F.dual k)) = 0 := by
      rw [Fintype.sum_eq_single i (fun b hb => by rw [e_apply, ite_eq_right hb, zero_mul])]
      rw [e_apply, ite_eq_left rfl, one_mul, e_apply, ite_eq_right (fun h => hji h.symm)]
    have h2 : (∑ k : F.K, e F j k * e F i (F.dual k)) = 0 := by
      rw [Fintype.sum_eq_single j (fun b hb => by rw [e_apply, ite_eq_right hb, zero_mul])]
      rw [e_apply, ite_eq_left rfl, one_mul, e_apply, ite_eq_right (fun h => hij h.symm)]
    rw [h1, h2]
    unfold FermionIndex.g
    rw [ite_eq_right hji]; ring

theorem a_mul_a_add_swap (F : FermionIndex) (i j : F.K) :
    a F i * a F j + a F j * a F i = (F.g i j) • (1 : Cl F) := by
  unfold a
  rw [CliffordAlgebra.ι_mul_ι_add_swap, polar_QK_apply, Algebra.algebraMap_eq_smul_one,
    BK_e_add_swap]

noncomputable abbrev ClGrading (F : FermionIndex) : ZMod 2 → Submodule ℚ (Cl F) :=
  CliffordAlgebra.evenOdd (QK F)

noncomputable instance ClGrading_gradedAlgebra (F : FermionIndex) : GradedAlgebra (ClGrading F) :=
  CliffordAlgebra.gradedAlgebra (QK F)

/-! ## `R F n = Pmn F n ⊕ κ(Pmn F n)` -/

noncomputable def Qzero (F : FermionIndex) (n : ℕ) : QuadraticForm (Pmn F n) (Pmn F n) := 0

noncomputable abbrev R (F : FermionIndex) (n : ℕ) : Type := CliffordAlgebra (Qzero F n)

noncomputable def kappa (F : FermionIndex) (n : ℕ) : R F n := CliffordAlgebra.ι (Qzero F n) 1

theorem kappa_sq (F : FermionIndex) (n : ℕ) : kappa F n * kappa F n = 0 := by
  unfold kappa
  rw [CliffordAlgebra.ι_sq_scalar]
  rw [show Qzero F n 1 = 0 from rfl]
  simp

noncomputable abbrev RGrading (F : FermionIndex) (n : ℕ) : ZMod 2 → Submodule (Pmn F n) (R F n) :=
  CliffordAlgebra.evenOdd (Qzero F n)

theorem kappa_mem_RGrading_one (F : FermionIndex) (n : ℕ) :
    kappa F n ∈ RGrading F n 1 := CliffordAlgebra.ι_mem_evenOdd_one (Qzero F n) 1

noncomputable instance RGradedAlgebra (F : FermionIndex) (n : ℕ) :
    GradedAlgebra (RGrading F n) := CliffordAlgebra.gradedAlgebra (Qzero F n)

/-- `κ ≠ 0`, by a lift to `TrivSqZeroExt`; no `F`-dependence at all. -/
theorem kappa_ne_zero (F : FermionIndex) (n : ℕ) : kappa F n ≠ 0 := by
  set G : R F n →ₐ[Pmn F n] TrivSqZeroExt (Pmn F n) (Pmn F n) :=
    CliffordAlgebra.lift (Qzero F n)
      ⟨TrivSqZeroExt.inrHom (Pmn F n) (Pmn F n), fun v => by
        change TrivSqZeroExt.inr v * TrivSqZeroExt.inr v = _
        rw [TrivSqZeroExt.inr_mul_inr, show Qzero F n v = 0 from rfl, map_zero]⟩ with hG
  have hGkappa : G (kappa F n) = TrivSqZeroExt.inr 1 := by
    rw [kappa, hG, CliffordAlgebra.lift_ι_apply]
    rfl
  intro h
  rw [h, map_zero] at hGkappa
  exact one_ne_zero (by
    have := congrArg TrivSqZeroExt.snd hGkappa.symm
    rwa [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] at this)

noncomputable instance R_algebra_rat (F : FermionIndex) (n : ℕ) : Algebra ℚ (R F n) :=
  Algebra.restrictScalars ℚ (Pmn F n) (R F n)

noncomputable instance R_isScalarTower (F : FermionIndex) (n : ℕ) :
    IsScalarTower ℚ (Pmn F n) (R F n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable abbrev RGradingQ (F : FermionIndex) (n : ℕ) : ZMod 2 → Submodule ℚ (R F n) :=
  fun i => (RGrading F n i).restrictScalars ℚ

noncomputable instance RGradedAlgebraQ (F : FermionIndex) (n : ℕ) :
    GradedAlgebra (RGradingQ F n) := inferInstance

/-! ## `A0 F n = W_n ⊗ Cl F`, `AB F n = R F n ⊗ A0 F n` -/

noncomputable abbrev A0 (F : FermionIndex) (n : ℕ) : Type :=
  GradedTensorProduct ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)

noncomputable def A0GradingMap (F : FermionIndex) (n : ℕ) (k : ZMod 2) :
    (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗[ℚ] (ClGrading F k) →ₗ[ℚ] A0 F n :=
  (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).toLinearMap
    ∘ₗ TensorProduct.map LinearMap.id (ClGrading F k).subtype

noncomputable def A0Grading (F : FermionIndex) (n : ℕ) (k : ZMod 2) : Submodule ℚ (A0 F n) :=
  LinearMap.range (A0GradingMap F n k)

-- `A0Grading_gradedAlgebra` is proved in `OspN/SourceTensor.lean`.


end OspN
end OspOddDeformations
