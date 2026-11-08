import OspOddDeformations.OspN.SourceTensor
import InhomogeneousDeformations.SourceIndependence
import InhomogeneousDeformations.SourceQuadraticIndependence
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# `X0A0`, ℚ-independence, and `ι₀` injectivity, for every `osp(N|2n)`

Paper Proposition 3.3 on `𝔤_P`, in the realization, for a general `FermionIndex`. No step inspects
the concrete shape of `F.K` — the double- and single-contraction machinery (`dcontract2`,
`A0contract1`) uses only `F.K`'s `Fintype`/`DecidableEq` and the coordinate functionals
`LinearMap.proj`/`e F i`, all already general; the fermion-index-specific fact used throughout,
`e F i k = if k = i then 1 else 0`, is `Source.lean`'s own `e_apply`, proved for a general `F`.

Proves item 1 (`X0A0`, the `A0`-factor of the base lifts, and `X0_eq_tmul`), item 2
(`X0A0_linearIndependent`, via the S/L-separation and F-independence pieces then their
assembly), and item 3 (`iota0_injective`).
-/

namespace OspOddDeformations
namespace OspN

open scoped TensorProduct
open Bmn (I IKey index0nToFun indexEquiv0n)

/-! ## Two small right-tensor bridge lemmas, mirroring `SourceTensor.lean`'s `tmul_add_left`
but on the `A0`-side of `AB F n = R F n ᵍ⊗ₜ A0 F n` instead of the `R`-side. -/

theorem tmul_add_right (F : FermionIndex) (n : ℕ) (r : R F n) (x y : A0 F n) :
    (r ᵍ⊗ₜ[ℚ] (x + y) : AB F n) = r ᵍ⊗ₜ[ℚ] x + r ᵍ⊗ₜ[ℚ] y := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] (x + y))
    = GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] x)
      + GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] y)
  rw [← map_add, TensorProduct.tmul_add]

theorem tmul_sub_right (F : FermionIndex) (n : ℕ) (r : R F n) (x y : A0 F n) :
    (r ᵍ⊗ₜ[ℚ] (x - y) : AB F n) = r ᵍ⊗ₜ[ℚ] x - r ᵍ⊗ₜ[ℚ] y := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] (x - y))
    = GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] x)
      - GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] y)
  rw [← map_sub, TensorProduct.tmul_sub]

theorem tmul_smul_right (F : FermionIndex) (n : ℕ) (r : R F n) (c : ℚ) (x : A0 F n) :
    (r ᵍ⊗ₜ[ℚ] (c • x) : AB F n) = c • (r ᵍ⊗ₜ[ℚ] x) := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] (c • x))
    = c • GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] x)
  rw [← map_smul, TensorProduct.tmul_smul]

/-- The embedding `A0 F n → AB F n`, `x ↦ (1:R F n) ᵍ⊗ₜ x`, is a ring homomorphism (no
Koszul sign) since its `R`-side is always the fixed degree-`0` element `1` —
`GradedTensorProduct.includeRight`, restated with the bare `ᵍ⊗ₜ` notation used
throughout this development. -/
theorem tmul_one_mul_tmul_one (F : FermionIndex) (n : ℕ) (x y : A0 F n) :
    ((1 : R F n) ᵍ⊗ₜ[ℚ] x : AB F n) * ((1 : R F n) ᵍ⊗ₜ[ℚ] y) = (1 : R F n) ᵍ⊗ₜ[ℚ] (x * y) := by
  have h := map_mul (GradedTensorProduct.includeRight (RGradingQ F n) (A0Grading F n)) x y
  simpa [GradedTensorProduct.includeRight_apply] using h.symm

/-! ## Item 1 — `X0A0`, the `A0`-factor of the base lifts -/

/-- `L⁰ₐ`, the `A0`-factor of `L0` — `L0`'s own formula, one tensor level down, in terms
of `Bu0` (`SourceTensor.lean`) rather than `BuAB`. -/
noncomputable def L0A0 (F : FermionIndex) (n : ℕ) (u v : I n) : A0 F n :=
  (1 / 4 : ℚ) • (Bu0 F n u * Bu0 F n v + Bu0 F n v * Bu0 F n u)

/-- `S⁰ₐ`, the `A0`-factor of `S0`. -/
noncomputable def S0A0 (F : FermionIndex) (n : ℕ) (i j : F.K) : A0 F n :=
  (1 / 2 : ℚ) • (aA0 F n i * aA0 F n j - aA0 F n j * aA0 F n i)

/-- `F⁰ₐ`, the `A0`-factor of `F0`. -/
noncomputable def F0A0 (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : A0 F n :=
  (1 / 4 : ℚ) • (aA0 F n i * Bu0 F n u + Bu0 F n u * aA0 F n i)

/-- **`X⁰ₐ` (item 1's headline datum): the `A0`-factor of `X0`, by kind.** -/
noncomputable def X0A0 (F : FermionIndex) (n : ℕ) : OspBasis F n → A0 F n
  | .inl ⟨(u, v), _⟩ => L0A0 F n u v
  | .inr (.inl ⟨(i, j), _⟩) => S0A0 F n i j
  | .inr (.inr (u, i)) => F0A0 F n u i

theorem L0_eq_tmul (F : FermionIndex) (n : ℕ) (u v : I n) :
    L0 F n u v = (1 : R F n) ᵍ⊗ₜ[ℚ] L0A0 F n u v := by
  unfold L0 L0A0 BuAB
  rw [tmul_one_mul_tmul_one, tmul_one_mul_tmul_one, ← tmul_add_right, ← tmul_smul_right]

theorem S0_eq_tmul (F : FermionIndex) (n : ℕ) (i j : F.K) :
    S0 F n i j = (1 : R F n) ᵍ⊗ₜ[ℚ] S0A0 F n i j := by
  unfold S0 S0A0 aAB
  rw [tmul_one_mul_tmul_one, tmul_one_mul_tmul_one, ← tmul_sub_right, ← tmul_smul_right]

theorem F0_eq_tmul (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    F0 F n u i = (1 : R F n) ᵍ⊗ₜ[ℚ] F0A0 F n u i := by
  unfold F0 F0A0 BuAB aAB
  rw [tmul_one_mul_tmul_one, tmul_one_mul_tmul_one, ← tmul_add_right, ← tmul_smul_right]

/-- **`X0_eq_tmul` (item 1's other half): `X0 X = (1 : R F n) ᵍ⊗ₜ X0A0 X`.** -/
theorem X0_eq_tmul (F : FermionIndex) (n : ℕ) (X : OspBasis F n) :
    X0 F n X = (1 : R F n) ᵍ⊗ₜ[ℚ] X0A0 F n X := by
  match X with
  | .inl ⟨(u, v), _⟩ => exact L0_eq_tmul F n u v
  | .inr (.inl ⟨(i, j), _⟩) => exact S0_eq_tmul F n i j
  | .inr (.inr (u, i)) => exact F0_eq_tmul F n u i

/-! ## Item 2, S-vs-L separation

Instead of the
`CliffordAlgebra.equivExterior`/`ExteriorAlgebra` machinery, this uses a double
`CliffordAlgebra.contractLeft` by the coordinate functionals dual to `e_k`/`e_l`
directly inside `Cl F`, landing back in `Cl F` via `algebraMap` rather than in
`ExteriorAlgebra`. This avoids needing the finer wedge-degree basis of the exterior
algebra at all: `contractLeft`'s own recursion (`contractLeft_ι_mul`,
`contractLeft_ι`, `contractLeft_one`) already isolates exactly the coefficient of a
single ordered pair `(k,l)` inside a length-2 product, which is all this section needs. -/

/-- The double contraction by the two coordinate functionals dual to `e_k`, `e_l`. -/
noncomputable def dcontract2 (F : FermionIndex) (k l : F.K) : Cl F →ₗ[ℚ] Cl F :=
  (CliffordAlgebra.contractLeft (LinearMap.proj l)).comp
    (CliffordAlgebra.contractLeft (LinearMap.proj k))

theorem dcontract2_one (F : FermionIndex) (k l : F.K) : dcontract2 F k l 1 = 0 := by
  unfold dcontract2
  simp [CliffordAlgebra.contractLeft_one]

/-- `proj k (e F i) = [k = i]`, as a `ℚ`-value `if`. -/
theorem proj_e (F : FermionIndex) (k i : F.K) :
    (LinearMap.proj k : (F.K → ℚ) →ₗ[ℚ] ℚ) (e F i) = if k = i then (1 : ℚ) else 0 := by
  rw [LinearMap.proj_apply, e_apply, eq_comm]

/-- One contraction of `a_i * a_j`, in closed form: `d⌋(a_i a_j) = d(e_i)•a_j - d(e_j)•a_i`. -/
theorem contractLeft_a_mul_a (F : FermionIndex) (k i j : F.K) :
    CliffordAlgebra.contractLeft (LinearMap.proj k) (a F i * a F j)
      = (if k = i then (1 : ℚ) else 0) • a F j - (if k = j then (1 : ℚ) else 0) • a F i := by
  unfold a
  rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
  simp only [proj_e]
  rw [← Algebra.commutes, ← Algebra.smul_def]

/-- The double contraction of `a_i * a_j`, in closed form. -/
theorem dcontract2_a_mul_a (F : FermionIndex) (k l i j : F.K) :
    dcontract2 F k l (a F i * a F j)
      = algebraMap ℚ (Cl F)
          ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
            - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)) := by
  unfold dcontract2 a
  rw [LinearMap.comp_apply]
  rw [show CliffordAlgebra.contractLeft (LinearMap.proj k)
        (CliffordAlgebra.ι (QK F) (e F i) * CliffordAlgebra.ι (QK F) (e F j))
      = (if k = i then (1 : ℚ) else 0) • CliffordAlgebra.ι (QK F) (e F j)
        - (if k = j then (1 : ℚ) else 0) • CliffordAlgebra.ι (QK F) (e F i) from
      contractLeft_a_mul_a F k i j]
  rw [map_sub, map_smul, map_smul, CliffordAlgebra.contractLeft_ι, CliffordAlgebra.contractLeft_ι]
  simp only [proj_e]
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_sub]

/-- `aA0 i * aA0 j` reduces to the embedding of the `Cl F`-level product — extracted from
`SourceTensor.lean`'s `aAB_mul_aAB`'s own inline `hinner` derivation, exposed here as a
standalone lemma since this section needs it directly (not only through the `AB`-level
wrapper). -/
theorem aA0_mul_aA0 (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aA0 F n i * aA0 F n j
      = (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i * a F j) := by
  unfold aA0
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
    (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
    (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (⟨a F i, a_odd F i⟩ : ClGrading F
        1)
    (⟨1, trivial⟩ : InhomogeneousDeformations.Source.WGrading n 0) (a F j)]
  simp only [mul_one]

/-- `S0A0`'s `Cl F`-content, made explicit as a pure tensor with `1_W` on the left —
mirrors `X0_eq_tmul`'s own shape for `S0A0` specifically, one level further than
`S0_eq_tmul` (which targets `S0`, not `S0A0`). -/
theorem S0A0_eq_tmul (F : FermionIndex) (n : ℕ) (i j : F.K) :
    S0A0 F n i j = (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ]
      ((1 / 2 : ℚ) • (a F i * a F j - a F j * a F i) : Cl F) := by
  unfold S0A0
  rw [aA0_mul_aA0, aA0_mul_aA0]
  change (1 / 2 : ℚ) • (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n)
        (ClGrading F) ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ (a F i * a F
            j))
      - GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ (a F j * a F i)))
    = GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ
          ((1 / 2 : ℚ) • (a F i * a F j - a F j * a F i)))
  rw [← map_sub, ← map_smul, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_smul]

/-- The `A0`-level double contraction: act as the identity on the `W_n` factor and as
`dcontract2` on the `Cl F` factor. Well-typed because `A0 F n` (`GradedTensorProduct`) is
a type synonym for the plain tensor product `(Module.End ℚ (WPoly n)) ⊗[ℚ] (Cl F)`
(`GradedTensorProduct.of = LinearEquiv.refl`), so `TensorProduct.map` applies directly
through `.of`/`.symm`, exactly as `A0_decompose_lin` (`SourceTensor.lean`) already does. -/
noncomputable def A0dcontract2 (F : FermionIndex) (n : ℕ) (k l : F.K) : A0 F n →ₗ[ℚ] A0 F n :=
  (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).toLinearMap
    ∘ₗ TensorProduct.map (LinearMap.id : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)
        →ₗ[ℚ] Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (dcontract2 F k l)
    ∘ₗ (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading
        F)).symm.toLinearMap

theorem A0dcontract2_tmul (F : FermionIndex) (n : ℕ) (k l : F.K)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : Cl F) :
    A0dcontract2 F n k l (w ᵍ⊗ₜ[ℚ] c) = w ᵍ⊗ₜ[ℚ] (dcontract2 F k l c) := by
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      (TensorProduct.map LinearMap.id (dcontract2 F k l)
        ((GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).symm
          (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w
              ⊗ₜ c))))
    = GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
        (w ⊗ₜ (dcontract2 F k l c))
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem A0dcontract2_L_part (F : FermionIndex) (n : ℕ) (k l : F.K)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) :
    A0dcontract2 F n k l (w ᵍ⊗ₜ[ℚ] (1 : Cl F)) = 0 := by
  rw [A0dcontract2_tmul, dcontract2_one]
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w ⊗ₜ
      0) = 0
  rw [TensorProduct.tmul_zero, map_zero]

theorem A0dcontract2_S0A0 (F : FermionIndex) (n : ℕ) (k l i j : F.K) :
    A0dcontract2 F n k l (S0A0 F n i j)
      = ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
          - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)) • (1 : A0 F n) := by
  rw [S0A0_eq_tmul, A0dcontract2_tmul, map_smul, map_sub, dcontract2_a_mul_a, dcontract2_a_mul_a]
  rw [show (1 / 2 : ℚ) •
      (algebraMap ℚ (Cl F)
          ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
            - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))
        - algebraMap ℚ (Cl F)
          ((if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)
            - (if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)))
      = algebraMap ℚ (Cl F)
          ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
            - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)) from by
    rw [← map_sub, Algebra.smul_def, ← map_mul]; congr 1; ring]
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ
        (algebraMap ℚ (Cl F)
          ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
            - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))))
    = ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)
        - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)) • (1 : A0 F n)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul, ←
      Algebra.TensorProduct.one_def,
    GradedTensorProduct.of_one]

/-- The double sum of `A0dcontract2_S0A0`'s coefficient against an antisymmetric `d`
collapses to `2 • d k l`: the first delta pattern `[k=i][l=j]` picks out `d k l`
directly (nested `Fintype.sum_eq_single`), the second `[k=j][l=i]` picks out `d l k`,
and `d l k = - d k l` by antisymmetry. -/
theorem sum_S0A0_coeff (F : FermionIndex) (k l : F.K) (d : F.K → F.K → ℚ)
    (hanti : ∀ i j, d j i = -d i j) :
    ∑ i : F.K, ∑ j : F.K, d i j *
        (((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0))
          - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))
      = 2 * d k l := by
  have e2 : ∑ i : F.K, ∑ j : F.K, d i j *
      ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0)) = d k l := by
    rw [Fintype.sum_eq_single k (fun i hik => by
      apply Fintype.sum_eq_zero; intro j; simp [Ne.symm hik])]
    rw [Fintype.sum_eq_single l (fun j hjl => by simp [Ne.symm hjl])]
    simp
  have e3 : ∑ i : F.K, ∑ j : F.K, d i j *
      ((if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0)) = d l k := by
    rw [Fintype.sum_eq_single l (fun i hil => by
      apply Fintype.sum_eq_zero; intro j; simp [Ne.symm hil])]
    rw [Fintype.sum_eq_single k (fun j hjk => by simp [Ne.symm hjk])]
    simp
  have e4 : ∑ i : F.K, ∑ j : F.K, d i j *
      (((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0))
        - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))
      = (∑ i : F.K, ∑ j : F.K, d i j * ((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else
          0)))
        - ∑ i : F.K, ∑ j : F.K, d i j * ((if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ)
            else 0)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e4, e2, e3, hanti k l]
  ring

/-- `(1 : A0 F n) ≠ 0`. `A0 F n` is (via `GradedTensorProduct.of = LinearEquiv.refl`) a
type synonym for the plain tensor product `Module.End ℚ (WPoly n) ⊗[ℚ] Cl F`, whose own
`1` is `Algebra.TensorProduct.one_def`'s `(1:W) ⊗ₜ (1:C)`. Both factors are individually
nontrivial ℚ-vector spaces (`Module.End` over a nontrivial module; `CliffordAlgebra` of
any quadratic form given `Invertible (2:ℚ)` — both automatic instances, no nondegeneracy
needed), so their pure tensor `1 ⊗ₜ 1` is nonzero: pick any bases of each factor, form
the product basis (`Module.Basis.tensorProduct`), and note `1`'s own coordinate vector is
nonzero in each factor (since `1 ≠ 0` and `Basis.repr` is injective), so some
product-basis coordinate of `1 ⊗ₜ 1` is a nonzero product of two nonzero rationals. -/
theorem A0_one_ne_zero (F : FermionIndex) (n : ℕ) : (1 : A0 F n) ≠ 0 := by
  classical
  have : Nontrivial (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) :=
    inferInstance
  have : Nontrivial (Cl F) := inferInstance
  set bW := Module.Basis.ofVectorSpace ℚ
    (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) with hbW
  set bC := Module.Basis.ofVectorSpace ℚ (Cl F) with hbC
  set bWC := bW.tensorProduct bC with hbWC
  have hW1 : bW.repr (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ≠ 0 := by
    intro hz
    exact (one_ne_zero (α := Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)))
      (bW.repr.injective (by rw [hz, map_zero]))
  have hC1 : bC.repr (1 : Cl F) ≠ 0 := by
    intro hz
    exact (one_ne_zero (α := Cl F)) (bC.repr.injective (by rw [hz, map_zero]))
  obtain ⟨i, hi⟩ : ∃ i,
      bW.repr (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hW1 (Finsupp.ext hcon)
  obtain ⟨j, hj⟩ : ∃ j, bC.repr (1 : Cl F) j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hC1 (Finsupp.ext hcon)
  have htmul_ne :
      (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ] (1 : Cl F) ≠ 0 := by
    intro hz
    have hne : bWC.repr
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ] (1 : Cl F))
        (i, j) ≠ 0 := by
      rw [hbWC, Module.Basis.tensorProduct_repr_tmul_apply]
      simp only [smul_eq_mul]
      exact mul_ne_zero hj hi
    exact hne (by rw [hz, map_zero, Finsupp.zero_apply])
  intro h
  apply htmul_ne
  have h2 := congrArg
    (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).symm h
  rwa [GradedTensorProduct.of_symm_one, map_zero, Algebra.TensorProduct.one_def] at h2

/-- **S-vs-L separation (item 2; not through `equivExterior`, see this section's
header)**: inside `A0 F n`, an arbitrary
"L-shaped" element `w ᵍ⊗ₜ 1` — the shape every ℚ-linear combination of `L0A0 u v` has,
since each `L0A0 u v` is itself `ℓ_{uv} ᵍ⊗ₜ 1` for some Weyl-algebra element `ℓ_{uv}`
(`L0A0`'s own definition) — can never cancel a nontrivial combination of `S0A0 i j`
terms: the `S`-coefficients are forced to vanish individually, for every `(k,l)`
(including `k = l`, where both sides are automatically `0`; no need to restrict to
`k < l` in the statement). The proof of `X0A0_linearIndependent` below
instantiates `w` with the actual `L`-combination it needs to rule out. -/
theorem S0A0_separated_from_L0A0 (F : FermionIndex) (n : ℕ)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (d : F.K → F.K → ℚ)
    (hanti : ∀ i j, d j i = -d i j)
    (h : w ᵍ⊗ₜ[ℚ] (1 : Cl F) + ∑ i : F.K, ∑ j : F.K, d i j • S0A0 F n i j = 0) :
    ∀ k l : F.K, d k l = 0 := by
  intro k l
  have happly := congrArg (A0dcontract2 F n k l) h
  rw [map_add, map_zero, A0dcontract2_L_part, zero_add, map_sum] at happly
  simp only [map_sum, map_smul, A0dcontract2_S0A0, smul_smul] at happly
  rw [show (∑ i : F.K, ∑ j : F.K,
        (d i j * (((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0))
          - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))) • (1 : A0 F n))
      = (∑ i : F.K, ∑ j : F.K,
          d i j * (((if k = i then (1 : ℚ) else 0) * (if l = j then (1 : ℚ) else 0))
            - (if k = j then (1 : ℚ) else 0) * (if l = i then (1 : ℚ) else 0))) • (1 : A0 F n) from
                by
    simp only [← Finset.sum_smul]] at happly
  rw [sum_S0A0_coeff F k l d hanti] at happly
  rcases smul_eq_zero.mp happly with h2 | h1
  · linarith
  · exact absurd h1 (A0_one_ne_zero F n)

/-! ## Item 2, F-independence -/

/-- `F0A0` as a pure tensor: since `Module.End ℚ (WPoly n)` sits entirely in `WGrading n
0` (trivially: every element's degree-0 membership proof is `trivial`), both orderings
`aA0 i * Bu0 u` and `Bu0 u * aA0 i` pick up no Koszul sign and land on the same pure
tensor `B_u ᵍ⊗ₜ a_i`. -/
theorem F0A0_eq_tmul (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    F0A0 F n u i = (1 / 2 : ℚ) •
      ((InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (a F i) : A0 F n) := by
  unfold F0A0 Bu0 aA0
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
    (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
    (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
    (⟨a F i, a_odd F i⟩ : ClGrading F 1)
    (⟨InhomogeneousDeformations.Source.B n (index0nToFun n u), trivial⟩ :
      InhomogeneousDeformations.Source.WGrading n 0)
    (1 : Cl F)]
  rw [GradedTensorProduct.tmul_one_mul_one_tmul
    (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
    (InhomogeneousDeformations.Source.B n (index0nToFun n u)) (a F i)]
  simp only [one_mul, mul_one]
  rw [← two_smul ℚ, smul_smul]
  norm_num

/-- `{a_i}` is linearly independent in `Cl F` — a single `contractLeft` per index
isolates each coefficient, exactly as `sum_S0A0_coeff`'s double-contraction does for
`S0A0`, one level simpler. -/
theorem a_linearIndependent (F : FermionIndex) : LinearIndependent ℚ (a F) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have happly := congrArg (CliffordAlgebra.contractLeft (LinearMap.proj k)) hg
  rw [map_sum, map_zero] at happly
  simp only [map_smul] at happly
  have hstep : ∀ i : F.K, CliffordAlgebra.contractLeft (LinearMap.proj k) (a F i)
      = algebraMap ℚ (Cl F) (if k = i then (1 : ℚ) else 0) := by
    intro i
    unfold a
    rw [CliffordAlgebra.contractLeft_ι, proj_e]
  simp only [hstep] at happly
  rw [Fintype.sum_eq_single k (fun i hik => by simp [Ne.symm hik])] at happly
  have : Nontrivial (Cl F) := inferInstance
  rcases smul_eq_zero.mp happly with h | h
  · exact h
  · rw [show (if k = k then (1 : ℚ) else 0) = 1 from ite_eq_left rfl, map_one] at h
    exact absurd h one_ne_zero

/-- The embedding `w ↦ w ᵍ⊗ₜ 1 : Module.End ℚ (WPoly n) → A0 F n` is injective —
generalizes `A0_one_ne_zero`'s own basis argument from the single element `w = 1` to
an arbitrary `w`. -/
theorem tmul_one_injective (F : FermionIndex) (n : ℕ) :
    Function.Injective (fun w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n) =>
      (w ᵍ⊗ₜ[ℚ] (1 : Cl F) : A0 F n)) := by
  classical
  have : Nontrivial (Cl F) := inferInstance
  set bC := Module.Basis.ofVectorSpace ℚ (Cl F) with hbC
  set bW := Module.Basis.ofVectorSpace ℚ
    (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) with hbW
  set bWC := bW.tensorProduct bC with hbWC
  have hC1 : bC.repr (1 : Cl F) ≠ 0 := by
    intro hz
    exact (one_ne_zero (α := Cl F)) (bC.repr.injective (by rw [hz, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j, bC.repr (1 : Cl F) j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hC1 (Finsupp.ext hcon)
  intro w1 w2 heq
  simp only at heq
  have h2 := congrArg
    (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).symm heq
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h2
  have hsub : (w1 - w2) ⊗ₜ[ℚ] (1 : Cl F) = 0 := by
    rw [TensorProduct.sub_tmul, h2, sub_self]
  have hcoord : ∀ i, bW.repr (w1 - w2) i = 0 := by
    intro i
    have hne : bWC.repr ((w1 - w2) ⊗ₜ[ℚ] (1 : Cl F)) (i, j) = 0 := by
      rw [hsub, map_zero, Finsupp.zero_apply]
    rw [hbWC, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul] at hne
    rcases mul_eq_zero.mp hne with h | h
    · exact absurd h hj
    · exact h
  have hzero : bW.repr (w1 - w2) = 0 := Finsupp.ext (fun i => by rw [hcoord i]; rfl)
  have hw : w1 - w2 = 0 := bW.repr.injective (by rw [hzero, map_zero])
  exact sub_eq_zero.mp hw

/-- Left-side additivity of `ᵍ⊗ₜ` at the `A0 F n` level, mirroring `SourceTensor.lean`'s
`tmul_add_left` but on the `W`-side here instead of the `R`-side. -/
theorem tmul_add_left_A0 (F : FermionIndex) (n : ℕ)
    (w1 w2 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : Cl F) :
    ((w1 + w2) ᵍ⊗ₜ[ℚ] c : A0 F n) = w1 ᵍ⊗ₜ[ℚ] c + w2 ᵍ⊗ₜ[ℚ] c := by
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      ((w1 + w2) ⊗ₜ c)
    = GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w1 ⊗ₜ c)
      + GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w2 ⊗ₜ
          c)
  rw [← map_add, TensorProduct.add_tmul]

theorem tmul_smul_left_A0 (F : FermionIndex) (n : ℕ) (k : ℚ)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : Cl F) :
    ((k • w) ᵍ⊗ₜ[ℚ] c : A0 F n) = k • (w ᵍ⊗ₜ[ℚ] c) := by
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      ((k • w) ⊗ₜ c)
    = k • GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w ⊗ₜ
        c)
  rw [← map_smul, TensorProduct.smul_tmul']

theorem tmul_smul_right_A0 (F : FermionIndex) (n : ℕ) (k : ℚ)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : Cl F) :
    (w ᵍ⊗ₜ[ℚ] (k • c) : A0 F n) = k • (w ᵍ⊗ₜ[ℚ] c) := by
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      (w ⊗ₜ (k • c))
    = k • GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w ⊗ₜ
        c)
  rw [← map_smul, TensorProduct.tmul_smul]

/-- `w ↦ w ᵍ⊗ₜ 1`, bundled as a `LinearMap` so `LinearIndependent.map'` applies. -/
noncomputable def tmulOneMap (F : FermionIndex) (n : ℕ) :
    Module.End ℚ (InhomogeneousDeformations.Source.WPoly n) →ₗ[ℚ] A0 F n where
  toFun w := w ᵍ⊗ₜ[ℚ] (1 : Cl F)
  map_add' w1 w2 := tmul_add_left_A0 F n w1 w2 1
  map_smul' k w := tmul_smul_left_A0 F n k w 1

/-- `{Bu0 u}` is linearly independent in `A0 F n`: `Source.B_linearIndependent`, reindexed
via `index0nToFun` (injective, part of `indexEquiv0n`'s equiv), then carried across by
`tmulOneMap`'s injectivity. -/
theorem Bu0_linearIndependent (F : FermionIndex) (n : ℕ) : LinearIndependent ℚ (Bu0 F n) := by
  have hB : LinearIndependent ℚ
      (InhomogeneousDeformations.Source.B n ∘ index0nToFun n) :=
    (InhomogeneousDeformations.Source.B_linearIndependent n).comp
      (index0nToFun n) (indexEquiv0n n).injective
  have hker : LinearMap.ker (tmulOneMap F n) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (tmul_one_injective F n)
  have hmapped := hB.map' (tmulOneMap F n) hker
  exact hmapped

/-- The `A0`-level single contraction: identity on the `W_n` factor, `contractLeft (proj
i₀)` on the `Cl F` factor — the single-contraction analogue of `A0dcontract2`. -/
noncomputable def A0contract1 (F : FermionIndex) (n : ℕ) (i₀ : F.K) : A0 F n →ₗ[ℚ] A0 F n :=
  (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).toLinearMap
    ∘ₗ TensorProduct.map (LinearMap.id : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)
        →ₗ[ℚ] Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
      (CliffordAlgebra.contractLeft (LinearMap.proj i₀))
    ∘ₗ (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading
        F)).symm.toLinearMap

theorem A0contract1_tmul (F : FermionIndex) (n : ℕ) (i₀ : F.K)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : Cl F) :
    A0contract1 F n i₀ (w ᵍ⊗ₜ[ℚ] c) = w ᵍ⊗ₜ[ℚ] (CliffordAlgebra.contractLeft (LinearMap.proj i₀) c)
        := by
  change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
      (TensorProduct.map LinearMap.id (CliffordAlgebra.contractLeft (LinearMap.proj i₀))
        ((GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)).symm
          (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F) (w
              ⊗ₜ c))))
    = GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
        (w ⊗ₜ (CliffordAlgebra.contractLeft (LinearMap.proj i₀) c))
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]

/-- `A0contract1` applied to `B_u ᵍ⊗ₜ a_i` isolates the `i₀`-coefficient, scaled by `Bu0
u`. -/
theorem A0contract1_Bu0_a (F : FermionIndex) (n : ℕ) (i₀ : F.K) (u : I n) (i : F.K) :
    A0contract1 F n i₀
        ((InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (a F i))
      = (if i₀ = i then (1 : ℚ) else 0) • Bu0 F n u := by
  rw [A0contract1_tmul]
  unfold a
  rw [CliffordAlgebra.contractLeft_ι, proj_e]
  unfold Bu0
  rw [Algebra.algebraMap_eq_smul_one, tmul_smul_right_A0]

/-- **Item 2, F-independence: `{F0A0 u i}` is ℚ-linearly independent in `A0 F n`.** -/
theorem F0A0_linearIndependent (F : FermionIndex) (n : ℕ) :
    LinearIndependent ℚ (fun p : I n × F.K => F0A0 F n p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rintro ⟨u₀, i₀⟩
  have hc' : ∑ u : I n, ∑ i : F.K, c (u, i) • F0A0 F n u i = 0 := by
    rw [Fintype.sum_prod_type] at hc; exact hc
  have happly := congrArg (A0contract1 F n i₀) hc'
  rw [map_zero, map_sum] at happly
  simp only [map_sum, map_smul, F0A0_eq_tmul, smul_smul] at happly
  simp only [A0contract1_Bu0_a, smul_smul] at happly
  rw [show (∑ x : I n, ∑ x_1 : F.K,
        (c (x, x_1) * (1 / 2) * if i₀ = x_1 then (1 : ℚ) else 0) • Bu0 F n x)
      = ∑ x : I n, ((1 / 2) * c (x, i₀)) • Bu0 F n x from by
    congr 1; ext x
    rw [Fintype.sum_eq_single i₀ (fun i hi => by simp [Ne.symm hi])]
    simp [mul_comm]] at happly
  have hBu0 := (Bu0_linearIndependent F n)
  rw [Fintype.linearIndependent_iff] at hBu0
  have hzero := hBu0 (fun x => (1 / 2) * c (x, i₀)) happly u₀
  linarith

/-! ## Item 2, L-independence

`L0A0` needs no Koszul-sign or Clifford-side analysis at all: both factors being
multiplied have trivial `Cl F`-part `1`, exactly as `BuAB_comm`'s own `hB` sub-proof
(`SourceTensor.lean`) already computes. -/

/-- `L0A0` as a pure tensor with trivial `Cl F`-part. -/
theorem L0A0_eq_tmul (F : FermionIndex) (n : ℕ) (u v : I n) :
    L0A0 F n u v = ((1 / 4 : ℚ) •
      (InhomogeneousDeformations.Source.B n (index0nToFun n u)
        * InhomogeneousDeformations.Source.B n (index0nToFun n v)
        + InhomogeneousDeformations.Source.B n (index0nToFun n v)
        * InhomogeneousDeformations.Source.B n (index0nToFun n u)))
      ᵍ⊗ₜ[ℚ] (1 : Cl F) := by
  unfold L0A0 Bu0
  rw [show (InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
        * (InhomogeneousDeformations.Source.B n (index0nToFun n v)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
      = (InhomogeneousDeformations.Source.B n (index0nToFun n u)
          * InhomogeneousDeformations.Source.B n (index0nToFun n v)) ᵍ⊗ₜ[ℚ] (1 : Cl F) from by
    rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
      (InhomogeneousDeformations.Source.B n (index0nToFun n u))
      (⟨1, SetLike.one_mem_graded (ClGrading F)⟩ : ClGrading F 0)
      (⟨InhomogeneousDeformations.Source.B n (index0nToFun n v), trivial⟩ :
        InhomogeneousDeformations.Source.WGrading n 0) (1 : Cl F)]
    simp,
    show (InhomogeneousDeformations.Source.B n (index0nToFun n v)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
        * (InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
      = (InhomogeneousDeformations.Source.B n (index0nToFun n v)
          * InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F) from by
    rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
      (InhomogeneousDeformations.Source.B n (index0nToFun n v))
      (⟨1, SetLike.one_mem_graded (ClGrading F)⟩ : ClGrading F 0)
      (⟨InhomogeneousDeformations.Source.B n (index0nToFun n u), trivial⟩ :
        InhomogeneousDeformations.Source.WGrading n 0) (1 : Cl F)]
    simp]
  rw [← tmul_add_left_A0, ← tmul_smul_left_A0]

/-- Reindexes `Source.B_sum_linearIndependent`'s domain (`Fin (2n)` sorted pairs) to `I n`
sorted pairs, via `index0nToFun` -- well-typed since `(index0nToFun n u).val = IKey u`
literally (`Bmn/Base.lean`). -/
def reindexL {n : ℕ} (p : {p : I n × I n // IKey p.1 ≤ IKey p.2}) :
    {q : Fin (2 * n) × Fin (2 * n) // q.1 ≤ q.2} :=
  ⟨(index0nToFun n p.1.1, index0nToFun n p.1.2), by
    rw [Fin.le_iff_val_le_val]; exact p.2⟩

theorem reindexL_injective (n : ℕ) : Function.Injective (reindexL (n := n)) := by
  intro p q hpq
  have hval : (reindexL p).val = (reindexL q).val := congrArg Subtype.val hpq
  unfold reindexL at hval
  simp only [Prod.mk.injEq] at hval
  obtain ⟨h1, h2⟩ := hval
  have e1 : p.1.1 = q.1.1 := (indexEquiv0n n).injective h1
  have e2 : p.1.2 = q.1.2 := (indexEquiv0n n).injective h2
  exact Subtype.ext (Prod.ext e1 e2)

/-- `Source.B_sum_linearIndependent`, reindexed from `Fin (2n)` sorted pairs to `I n`
sorted pairs. -/
theorem BB_sum_linearIndependent (n : ℕ) :
    LinearIndependent ℚ (fun p : {p : I n × I n // IKey p.1 ≤ IKey p.2} =>
      InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        + InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1)) :=
  (InhomogeneousDeformations.Source.B_sum_linearIndependent n).comp
    (reindexL (n := n)) (reindexL_injective n)

/-- The scalar-multiplication self-map `x ↦ (1/4 : ℚ) • x`, bundled as a `LinearMap`, to
carry `BB_sum_linearIndependent` through the fixed `(1/4)` scaling in `L0A0_eq_tmul`. -/
noncomputable def quarterSmulMap (n : ℕ) :
    Module.End ℚ (InhomogeneousDeformations.Source.WPoly n) →ₗ[ℚ]
      Module.End ℚ (InhomogeneousDeformations.Source.WPoly n) :=
  (1 / 4 : ℚ) • LinearMap.id

theorem quarterSmulMap_injective (n : ℕ) : Function.Injective (quarterSmulMap n) := by
  intro x y hxy
  simp only [quarterSmulMap, LinearMap.smul_apply, LinearMap.id_apply] at hxy
  have h4 : (1 / 4 : ℚ) ≠ 0 := by norm_num
  exact smul_right_injective _ h4 hxy

/-- `BB_sum_linearIndependent`, scaled by the fixed nonzero `(1/4)`. -/
theorem L0A0_W_linearIndependent (n : ℕ) :
    LinearIndependent ℚ (fun p : {p : I n × I n // IKey p.1 ≤ IKey p.2} =>
      (1 / 4 : ℚ) • (InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        + InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1))) :=
  (BB_sum_linearIndependent n).map' (quarterSmulMap n)
    (LinearMap.ker_eq_bot.mpr (quarterSmulMap_injective n))

/-- **Item 2, L-independence: `{L0A0 u v}` is ℚ-linearly independent in `A0 F n`.** -/
theorem L0A0_linearIndependent (F : FermionIndex) (n : ℕ) :
    LinearIndependent ℚ (fun p : {p : I n × I n // IKey p.1 ≤ IKey p.2} =>
      L0A0 F n p.1.1 p.1.2) := by
  have h := (L0A0_W_linearIndependent n).map' (tmulOneMap F n)
    (LinearMap.ker_eq_bot.mpr (tmul_one_injective F n))
  have heq : (fun p : {p : I n × I n // IKey p.1 ≤ IKey p.2} => L0A0 F n p.1.1 p.1.2)
      = (tmulOneMap F n) ∘ (fun p : {p : I n × I n // IKey p.1 ≤ IKey p.2} =>
          (1 / 4 : ℚ) • (InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1)
            * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
            + InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
            * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1))) := by
    funext p
    rw [Function.comp_apply]
    change L0A0 F n p.1.1 p.1.2 = (1 / 4 : ℚ) • (InhomogeneousDeformations.Source.B n (index0nToFun
        n p.1.1)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        + InhomogeneousDeformations.Source.B n (index0nToFun n p.1.2)
        * InhomogeneousDeformations.Source.B n (index0nToFun n p.1.1)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
    exact L0A0_eq_tmul F n p.1.1 p.1.2
  rw [heq]
  exact h

/-! ## Item 2, assembly: `X0A0_linearIndependent`

Combines `L0A0_linearIndependent`, `S0A0_separated_from_L0A0`'s own double-contraction
machinery (sharpened here to isolate each `S0A0` coefficient directly), and
`F0A0_linearIndependent`'s single-contraction machinery, by splitting the vanishing sum
over `OspBasis F n = L-sub ⊕ (S-sub ⊕ F)` into its three kind-parts and eliminating them
in the order S (double contraction kills L and F), then F (single contraction kills L,
already-zero S), then L (direct). -/

/-- Double-contracting a single generator `a_i` always vanishes: the first contraction
lands on a central scalar (`algebraMap ℚ (Cl F) _`), and any second contraction of a
central scalar vanishes via `contractLeft_one`. -/
theorem dcontract2_a (F : FermionIndex) (k l i : F.K) : dcontract2 F k l (a F i) = 0 := by
  unfold dcontract2
  rw [LinearMap.comp_apply]
  unfold a
  rw [CliffordAlgebra.contractLeft_ι, proj_e, Algebra.algebraMap_eq_smul_one, map_smul,
    CliffordAlgebra.contractLeft_one, smul_zero]

/-- `A0dcontract2` kills every `F0A0` term: its Clifford content is a single generator
`a_i`, and `dcontract2_a` shows any double contraction of a single generator vanishes. -/
theorem A0dcontract2_F0A0_eq_zero (F : FermionIndex) (n : ℕ) (k l : F.K) (u : I n) (i : F.K) :
    A0dcontract2 F n k l (F0A0 F n u i) = 0 := by
  rw [F0A0_eq_tmul, map_smul, A0dcontract2_tmul, dcontract2_a]
  change (1 / 2 : ℚ) • GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n)
      (ClGrading F) ((InhomogeneousDeformations.Source.B n (index0nToFun n u)) ⊗ₜ (0 : Cl F)) = 0
  rw [TensorProduct.tmul_zero, map_zero, smul_zero]

/-- `A0contract1` kills every `L0A0` term: the single-contraction analogue of
`A0dcontract2_L_part`, at the level of `L0A0`'s own pure-tensor form. -/
theorem A0contract1_L0A0_eq_zero (F : FermionIndex) (n : ℕ) (i₀ : F.K) (u v : I n) :
    A0contract1 F n i₀ (L0A0 F n u v) = 0 := by
  rw [L0A0_eq_tmul, tmul_smul_left_A0, map_smul, A0contract1_tmul, CliffordAlgebra.contractLeft_one]
  change (1 / 4 : ℚ) • GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n)
      (ClGrading F) ((InhomogeneousDeformations.Source.B n (index0nToFun n u)
        * InhomogeneousDeformations.Source.B n (index0nToFun n v)
        + InhomogeneousDeformations.Source.B n (index0nToFun n v)
        * InhomogeneousDeformations.Source.B n (index0nToFun n u)) ⊗ₜ (0 : Cl F)) = 0
  rw [TensorProduct.tmul_zero, map_zero, smul_zero]

/-- Two distinct sorted fermion pairs can never share the "reversed" match: if
`s₀.1.1 = s.1.2` and `s₀.1.2 = s.1.1`, then combining both pairs' own sortedness
(`F.key p.1 < F.key p.2`) gives `F.key s.1.2 < F.key s.1.1` and `F.key s.1.1 < F.key s.1.2`
simultaneously — impossible. -/
theorem S0A0_pair_ne_zero_second {F : FermionIndex}
    (s s₀ : {p : F.K × F.K // F.key p.1 < F.key p.2}) :
    ¬ (s₀.1.1 = s.1.2 ∧ s₀.1.2 = s.1.1) := by
  rintro ⟨h1, h2⟩
  have hs0 := s₀.2
  have hs := s.2
  rw [h1, h2] at hs0
  omega

/-- `A0dcontract2 F n s₀.1.1 s₀.1.2`, applied to the sum of `S0A0` over sorted pairs,
isolates exactly the `s₀` coefficient. -/
theorem A0dcontract2_SS_eq_single (F : FermionIndex) (n : ℕ) (c : OspBasis F n → ℚ)
    (s₀ : {p : F.K × F.K // F.key p.1 < F.key p.2}) :
    A0dcontract2 F n s₀.1.1 s₀.1.2
        (∑ s : {p : F.K × F.K // F.key p.1 < F.key p.2},
          c (Sum.inr (Sum.inl s)) • S0A0 F n s.1.1 s.1.2)
      = c (Sum.inr (Sum.inl s₀)) • (1 : A0 F n) := by
  rw [map_sum]
  simp only [map_smul, A0dcontract2_S0A0]
  have hne0 : s₀.1.1 ≠ s₀.1.2 := fun h => absurd (h ▸ s₀.2) (lt_irrefl _)
  rw [Fintype.sum_eq_single s₀]
  · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hne0, ite_eq_right (Ne.symm hne0)]
    norm_num
  · intro s hs
    have hsecond : ¬ (s₀.1.1 = s.1.2 ∧ s₀.1.2 = s.1.1) := S0A0_pair_ne_zero_second s s₀
    have hfirst : ¬ (s₀.1.1 = s.1.1 ∧ s₀.1.2 = s.1.2) := by
      rintro ⟨h1, h2⟩
      exact hs (Subtype.ext (Prod.ext h1 h2)).symm
    have e1 : ((if s₀.1.1 = s.1.1 then (1 : ℚ) else 0)
        * (if s₀.1.2 = s.1.2 then (1 : ℚ) else 0)) = 0 := by
      by_cases h1 : s₀.1.1 = s.1.1
      · rw [ite_eq_left h1]
        by_cases h2 : s₀.1.2 = s.1.2
        · exact absurd ⟨h1, h2⟩ hfirst
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    have e2 : ((if s₀.1.1 = s.1.2 then (1 : ℚ) else 0)
        * (if s₀.1.2 = s.1.1 then (1 : ℚ) else 0)) = 0 := by
      by_cases h1 : s₀.1.1 = s.1.2
      · rw [ite_eq_left h1]
        by_cases h2 : s₀.1.2 = s.1.1
        · exact absurd ⟨h1, h2⟩ hsecond
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    rw [e1, e2, sub_zero, zero_smul, smul_zero]

/-- **Item 2: `{X0A0 X}` is ℚ-linearly independent in `A0 F n`.** -/
theorem X0A0_linearIndependent (F : FermionIndex) (n : ℕ) : LinearIndependent ℚ (X0A0 F n) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : ∑ i : {p : I n × I n // IKey p.1 ≤ IKey p.2}
      ⊕ {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K), c i • X0A0 F n i = 0 := hc
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hc0
  set SL : A0 F n := ∑ l : {p : I n × I n // IKey p.1 ≤ IKey p.2},
      c (Sum.inl l) • X0A0 F n (Sum.inl l) with hSL
  set SS : A0 F n := ∑ s : {p : F.K × F.K // F.key p.1 < F.key p.2},
      c (Sum.inr (Sum.inl s)) • X0A0 F n (Sum.inr (Sum.inl s)) with hSS
  set SF : A0 F n := ∑ f : I n × F.K,
      c (Sum.inr (Sum.inr f)) • X0A0 F n (Sum.inr (Sum.inr f)) with hSF
  have hc' : SL + (SS + SF) = 0 := hc0
  have hSSeq : SS = ∑ s : {p : F.K × F.K // F.key p.1 < F.key p.2},
      c (Sum.inr (Sum.inl s)) • S0A0 F n s.1.1 s.1.2 := by
    rw [hSS]; apply Finset.sum_congr rfl; intro s _; rfl
  have hSFeq : SF = ∑ f : I n × F.K, c (Sum.inr (Sum.inr f)) • F0A0 F n f.1 f.2 := by
    rw [hSF]; apply Finset.sum_congr rfl; intro f _; rfl
  have hSLeq : SL = ∑ l : {p : I n × I n // IKey p.1 ≤ IKey p.2},
      c (Sum.inl l) • L0A0 F n l.1.1 l.1.2 := by
    rw [hSL]; apply Finset.sum_congr rfl; intro l _; rfl
  -- Stage 1: every `S`-coefficient vanishes.
  have hSzero : ∀ s₀ : {p : F.K × F.K // F.key p.1 < F.key p.2},
      c (Sum.inr (Sum.inl s₀)) = 0 := by
    intro s₀
    have happly := congrArg (A0dcontract2 F n s₀.1.1 s₀.1.2) hc'
    rw [map_zero, map_add, map_add] at happly
    have hL0 : A0dcontract2 F n s₀.1.1 s₀.1.2 SL = 0 := by
      rw [hSLeq, map_sum]
      apply Finset.sum_eq_zero
      intro l _
      rw [map_smul]
      have : A0dcontract2 F n s₀.1.1 s₀.1.2 (L0A0 F n l.1.1 l.1.2) = 0 := by
        rw [L0A0_eq_tmul, tmul_smul_left_A0, map_smul, A0dcontract2_L_part, smul_zero]
      rw [this, smul_zero]
    have hF0 : A0dcontract2 F n s₀.1.1 s₀.1.2 SF = 0 := by
      rw [hSFeq, map_sum]
      apply Finset.sum_eq_zero
      intro f _
      rw [map_smul, A0dcontract2_F0A0_eq_zero, smul_zero]
    rw [hL0, zero_add, hSSeq, A0dcontract2_SS_eq_single, hF0, add_zero] at happly
    rcases smul_eq_zero.mp happly with h | h
    · exact h
    · exact absurd h (A0_one_ne_zero F n)
  have hSSzero : SS = 0 := by
    rw [hSSeq]; apply Finset.sum_eq_zero; intro s _; rw [hSzero s, zero_smul]
  -- Stage 2: with `S` zero, every `F`-coefficient vanishes.
  have hFzero : ∀ f₀ : I n × F.K, c (Sum.inr (Sum.inr f₀)) = 0 := by
    intro f₀
    have happly := congrArg (A0contract1 F n f₀.2) hc'
    rw [map_zero, map_add, map_add, hSSzero, map_zero, zero_add] at happly
    have hL0 : A0contract1 F n f₀.2 SL = 0 := by
      rw [hSLeq, map_sum]
      apply Finset.sum_eq_zero
      intro l _
      rw [map_smul, A0contract1_L0A0_eq_zero, smul_zero]
    rw [hL0, zero_add, hSFeq, map_sum] at happly
    simp only [map_smul, F0A0_eq_tmul, smul_smul] at happly
    simp only [A0contract1_tmul] at happly
    have hcoll : ∑ f : I n × F.K,
        (c (Sum.inr (Sum.inr f)) * (1 / 2 : ℚ)) •
          ((InhomogeneousDeformations.Source.B n (index0nToFun n f.1)) ᵍ⊗ₜ[ℚ]
            (CliffordAlgebra.contractLeft (LinearMap.proj f₀.2) (a F f.2)) : A0 F n)
        = ∑ u : I n, (c (Sum.inr (Sum.inr (u, f₀.2))) * (1 / 2 : ℚ)) •
            ((InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F) : A0 F n)
                := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      rw [Fintype.sum_eq_single f₀.2 (fun i hi => by
        unfold a
        rw [CliffordAlgebra.contractLeft_ι, proj_e, ite_eq_right (Ne.symm hi),
            Algebra.algebraMap_eq_smul_one,
          zero_smul]
        change (c (Sum.inr (Sum.inr (u, i))) * (1 / 2 : ℚ)) •
            GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
              ((InhomogeneousDeformations.Source.B n (index0nToFun n u)) ⊗ₜ (0 : Cl F)) = 0
        rw [TensorProduct.tmul_zero, map_zero, smul_zero])]
      unfold a
      rw [CliffordAlgebra.contractLeft_ι, proj_e, ite_eq_left rfl, Algebra.algebraMap_eq_smul_one,
        one_smul]
    rw [hcoll] at happly
    have hBu0eq : ∀ u : I n, ((InhomogeneousDeformations.Source.B n (index0nToFun n u))
        ᵍ⊗ₜ[ℚ] (1 : Cl F) : A0 F n) = Bu0 F n u := fun u => rfl
    simp only [hBu0eq] at happly
    have hBu0 := (Bu0_linearIndependent F n)
    rw [Fintype.linearIndependent_iff] at hBu0
    have hz := hBu0 (fun u => c (Sum.inr (Sum.inr (u, f₀.2))) * (1 / 2 : ℚ)) happly f₀.1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · norm_num at h
  have hSFzero : SF = 0 := by
    rw [hSFeq]; apply Finset.sum_eq_zero; intro f _; rw [hFzero f, zero_smul]
  -- Stage 3: with `S` and `F` both zero, every `L`-coefficient vanishes directly.
  have hLzero : ∀ l₀ : {p : I n × I n // IKey p.1 ≤ IKey p.2}, c (Sum.inl l₀) = 0 := by
    have hSL0 : SL = 0 := by
      have := hc'
      rw [hSSzero, hSFzero, add_zero, add_zero] at this
      exact this
    rw [hSLeq] at hSL0
    have hL0A0 := (L0A0_linearIndependent F n)
    rw [Fintype.linearIndependent_iff] at hL0A0
    intro l₀
    exact hL0A0 (fun l => c (Sum.inl l)) hSL0 l₀
  intro X
  match X with
  | .inl l => exact hLzero l
  | .inr (.inl s) => exact hSzero s
  | .inr (.inr f) => exact hFzero f

/-! ## Item 3 — `ι₀` injective -/

/-- `iota0 F n x`, rewritten to a plain sum of pure tensors in the underlying tensor
product `R F n ⊗[ℚ] A0 F n` (bridging out of `AB F n`'s `GradedTensorProduct` via
`.symm`): each term's `A0`-side factor `(1 : A0 F n)` and `R`-side factor `(1 : R F n)`
cancel via `GradedTensorProduct.tmul_one_mul_one_tmul`, needing no grading-membership
side conditions at all. -/
theorem iota0_eq_tmul_sum (F : FermionIndex) (n : ℕ) (x : OspMod F n) :
    (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)).symm (iota0 F n x)
      = ∑ X : OspBasis F n, (algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (X0A0 F n X) := by
  unfold iota0
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [X0_eq_tmul,
    GradedTensorProduct.tmul_one_mul_one_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (algebraMap (Pmn F n) (R F n) (x X)) (X0A0 F n X)]
  rfl

/-- `algebraMap (Pmn F n) (R F n)` is injective, reusing `kappa_ne_zero`'s own
`TrivSqZeroExt`-lift technique (`Source.lean`): the same algebra map `φ : R F n
→ₐ[Pmn F n] TrivSqZeroExt (Pmn F n) (Pmn F n)` sends `algebraMap c` to `TrivSqZeroExt.inl
c` (`AlgHom.commutes`), and `inl` is injective. -/
theorem algebraMap_Pmn_R_injective (F : FermionIndex) (n : ℕ) :
    Function.Injective (algebraMap (Pmn F n) (R F n)) := by
  set φ : R F n →ₐ[Pmn F n] TrivSqZeroExt (Pmn F n) (Pmn F n) :=
    CliffordAlgebra.lift (Qzero F n)
      ⟨TrivSqZeroExt.inrHom (Pmn F n) (Pmn F n), fun v => by
        change TrivSqZeroExt.inr v * TrivSqZeroExt.inr v = _
        rw [TrivSqZeroExt.inr_mul_inr, show Qzero F n v = 0 from rfl, map_zero]⟩ with hφ
  intro c c' hcc'
  have h1 : φ (algebraMap (Pmn F n) (R F n) c) = TrivSqZeroExt.inl c := φ.commutes c
  have h2 : φ (algebraMap (Pmn F n) (R F n) c') = TrivSqZeroExt.inl c' := φ.commutes c'
  have heq : (TrivSqZeroExt.inl c : TrivSqZeroExt (Pmn F n) (Pmn F n)) = TrivSqZeroExt.inl c' := by
    rw [← h1, ← h2, hcc']
  exact TrivSqZeroExt.inl_injective heq

/-- **Item 3: `ι₀` is injective.** -/
theorem iota0_injective (F : FermionIndex) (n : ℕ) : Function.Injective (iota0 F n) := by
  have hker : ∀ x : OspMod F n, iota0 F n x = 0 → x = 0 := by
    intro x hx
    set g : (OspBasis F n →₀ ℚ) →ₗ[ℚ] A0 F n := Finsupp.linearCombination ℚ (X0A0 F n) with hgdef
    have hg_inj : Function.Injective g := X0A0_linearIndependent F n
    have : Module.Flat ℚ (R F n) := inferInstance
    have hgl_inj : Function.Injective (g.lTensor (R F n)) :=
      Module.Flat.lTensor_preserves_injective_linearMap g hg_inj
    have hzero : (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)).symm (iota0 F n x)
        = 0 := by rw [hx, map_zero]
    rw [iota0_eq_tmul_sum] at hzero
    have hpre : g.lTensor (R F n)
        (∑ X : OspBasis F n, (algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ)))
        = 0 := by
      rw [map_sum]
      rw [show (∑ X : OspBasis F n, g.lTensor (R F n)
            ((algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))))
          = ∑ X : OspBasis F n, (algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (X0A0 F n X) from by
        apply Finset.sum_congr rfl
        intro X _
        rw [LinearMap.lTensor_tmul, hgdef, Finsupp.linearCombination_single, one_smul]]
      exact hzero
    have hsum0 : ∑ X : OspBasis F n,
        (algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))
        = (0 : R F n ⊗[ℚ] (OspBasis F n →₀ ℚ)) := hgl_inj (by rw [hpre, map_zero])
    funext X₀
    have happly := congrArg
      (TensorProduct.map (LinearMap.id : R F n →ₗ[ℚ] R F n) (Finsupp.lapply X₀)) hsum0
    rw [map_sum, map_zero] at happly
    rw [show (∑ X : OspBasis F n,
          TensorProduct.map (LinearMap.id : R F n →ₗ[ℚ] R F n) (Finsupp.lapply X₀)
            ((algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))))
        = (algebraMap (Pmn F n) (R F n) (x X₀)) ⊗ₜ[ℚ] (1 : ℚ) from by
      rw [Fintype.sum_eq_single X₀ (fun Y hY => by
        rw [TensorProduct.map_tmul, LinearMap.id_apply, Finsupp.lapply_apply,
          Finsupp.single_eq_of_ne (Ne.symm hY), TensorProduct.tmul_zero])]
      rw [TensorProduct.map_tmul, LinearMap.id_apply, Finsupp.lapply_apply, Finsupp.single_eq_same]]
      at happly
    have := congrArg (TensorProduct.rid ℚ (R F n)) happly
    rw [TensorProduct.rid_tmul, one_smul, map_zero] at this
    have hx0 : algebraMap (Pmn F n) (R F n) (x X₀) = 0 := this
    have := algebraMap_Pmn_R_injective F n hx0
    rw [this]
    rfl
  intro a b hab
  have h : iota0 F n (a - b) = 0 := by
    have : iota0 F n (a - b) = iota0 F n a - iota0 F n b := by
      rw [sub_eq_add_neg, sub_eq_add_neg, iota0_add, iota0_neg]
    rw [this, hab, sub_self]
  have := hker (a - b) h
  exact sub_eq_zero.mp this


end OspN
end OspOddDeformations
