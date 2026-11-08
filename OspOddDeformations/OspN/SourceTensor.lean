import OspOddDeformations.OspN.Source

/-!
# `A0Grading`, `AB`'s ring structure, the relations, and the recovery, for every `osp(N|2n)`

Built on the data of `OspN/Source.lean`, for a general `FermionIndex`: the `GradedAlgebra`
instance of `A0Grading`, the algebra `AB F n = R F n ⊗ A0 F n` with its generators and lifts,
the relations of the source algebra, the untwisting relations, `Xhat_eq_iota0_add`,
`base_realization` and `recovery`. The `SetLike.GradedMonoid`/`DirectSum.Decomposition`
combinator work of the instance uses only `Cl F`'s `ClGrading_gradedAlgebra` and
`InhomogeneousDeformations.Source.WGrading`/`WPoly` (no fermion-index dependence at all), never
the concrete shape of the fermion index; it follows `osp-triviality`'s `SourceTensor.lean`.
-/

-- Toolchain port (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; restore
-- the pre-v4.34 type-transparency behaviour of `isDefEq` for this file.
set_option backward.isDefEq.respectTransparency.types false


namespace OspOddDeformations
namespace OspN

open scoped TensorProduct DirectSum
open Bmn (I J index0nToFun J_correspondence0n)

/-- `A0Grading`'s decomposition map, given explicitly — `AB F n`'s multiplication (the Koszul
signs) comes from this instance's decomposition, so an opaque decomposition would leave every
statement about `AB F n` about an unspecified algebra. Built from `Cl F`'s own decomposition
(`ClGrading_gradedAlgebra`, `Source.lean`, from Mathlib's
`CliffordAlgebra.gradedAlgebra`) exactly as `osp-triviality`'s `SourceTensor.lean`'s
`A0_decompose_lin n` does for its fixed Clifford factor `C`/`CGrading`, here for
`Cl F`/`ClGrading F`, arbitrary `(F,n)`. A pure composition of Mathlib combinators:
`A0 F n = (End W_n) ⊗ Cl F ≃ (End W_n) ⊗ (⨁ k, ClGrading F k) ≃ ⨁ k, (End W_n) ⊗ (ClGrading
F k)`, corestricted degreewise into `A0Grading F n k`. -/
noncomputable def A0_decompose_lin (F : FermionIndex) (n : ℕ) :
    A0 F n →ₗ[ℚ] ⨁ k : ZMod 2, A0Grading F n k :=
  (DirectSum.lmap fun k => LinearMap.rangeRestrict (A0GradingMap F n k)) ∘ₗ
    (TensorProduct.directSumRight ℚ ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
        (fun k => ClGrading F k)).toLinearMap ∘ₗ
    (TensorProduct.congr (LinearEquiv.refl ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly
        n)))
      (DirectSum.decomposeLinearEquiv (ClGrading F))).toLinearMap ∘ₗ
    (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading
        F)).symm.toLinearMap

theorem A0GradingMap_tmul (F : FermionIndex) (n : ℕ) (k : ZMod 2)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : ClGrading F k) :
    A0GradingMap F n k (w ⊗ₜ c) = w ᵍ⊗ₜ[ℚ] (c : Cl F) := rfl

theorem A0Grading_mem_of_tmul (F : FermionIndex) (n : ℕ) (k : ZMod 2)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : ClGrading F k) :
    w ᵍ⊗ₜ[ℚ] (c : Cl F) ∈ A0Grading F n k :=
  ⟨w ⊗ₜ c, A0GradingMap_tmul F n k w c⟩

/-- Transliterated from `osp-triviality`'s `A0Grading_setLike`, with `Cl F`/`ClGrading F` for
`C`/`CGrading`. -/
instance A0Grading_setLike (F : FermionIndex) (n : ℕ) : SetLike.GradedMonoid (A0Grading F n) where
  one_mem := by
    have h := A0Grading_mem_of_tmul F n 0 1 (⟨1, SetLike.one_mem_graded (ClGrading F)⟩ : ClGrading F
        0)
    simpa [GradedTensorProduct.tmul, ← GradedTensorProduct.of_one,
      Algebra.TensorProduct.one_def] using h
  mul_mem := by
    intro i j gi gj hgi hgj
    obtain ⟨xi, hxi⟩ := hgi
    obtain ⟨xj, hxj⟩ := hgj
    subst hxi
    subst hxj
    induction xi using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, add_mul]; exact add_mem hx hy
    | tmul w c =>
      induction xj using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, mul_add]; exact add_mem hx hy
      | tmul w' c' =>
        rw [A0GradingMap_tmul, A0GradingMap_tmul,
          GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
            (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
            w c (⟨w', trivial⟩ : InhomogeneousDeformations.Source.WGrading n 0) c']
        exact A0Grading_mem_of_tmul F n (i + j) (w * w')
          (⟨(c : Cl F) * (c' : Cl F), SetLike.mul_mem_graded c.2 c'.2⟩ : ClGrading F (i + j))

/-- `A0_decompose_lin` on a pure tensor `w ᵍ⊗ₜ (c : Cl F)` with `c` already homogeneous of
degree `k`: lands exactly on the `k`-th summand, tagged by the obvious membership witness.
The computational core both `left_inv` and `right_inv` reduce to, transliterated from
`osp-triviality`'s `A0_decompose_lin_tmul_coe`. -/
theorem A0_decompose_lin_tmul_coe (F : FermionIndex) (n : ℕ) (k : ZMod 2)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : ClGrading F k) :
    A0_decompose_lin F n (w ᵍ⊗ₜ[ℚ] (c : Cl F)) =
      DirectSum.lof ℚ (ZMod 2) (fun k => A0Grading F n k) k
        ⟨w ᵍ⊗ₜ[ℚ] (c : Cl F), A0Grading_mem_of_tmul F n k w c⟩ := by
  change (DirectSum.lmap fun k => LinearMap.rangeRestrict (A0GradingMap F n k))
      ((TensorProduct.directSumRight ℚ ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
          (fun k => ClGrading F k))
        ((TensorProduct.congr
            (LinearEquiv.refl ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)))
            (DirectSum.decomposeLinearEquiv (ClGrading F))) (w ⊗ₜ (c : Cl F)))) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_coe, ← DirectSum.lof_eq_of ℚ, TensorProduct.directSumRight_tmul_lof,
    DirectSum.lmap_lof]
  rfl

/-- `A0_decompose_lin_tmul_coe`, restated with the tensor factor written as the *bare* `⊗ₜ`
(rather than `ᵍ⊗ₜ`) — needed wherever a term arrives already in bare-tensor form. -/
theorem A0_decompose_lin_tmul (F : FermionIndex) (n : ℕ) (k : ZMod 2)
    (w : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (c : ClGrading F k) :
    A0_decompose_lin F n (w ⊗ₜ[ℚ] (c : Cl F) : A0 F n) =
      DirectSum.lof ℚ (ZMod 2) (fun k => A0Grading F n k) k
        ⟨(w ⊗ₜ[ℚ] (c : Cl F) : A0 F n), A0Grading_mem_of_tmul F n k w c⟩ :=
  A0_decompose_lin_tmul_coe F n k w c

-- lint: the `show` in the proof fields is kept, so that the instance's text is unchanged.
set_option linter.style.show false in
/-- The grading `A0Grading` forms a `GradedAlgebra` —
`decompose'` is `A0_decompose_lin` above (explicit data), and both
`DirectSum.Decomposition` laws are proved, transliterated from `osp-triviality`'s
`A0GradedAlgebra`. -/
noncomputable instance A0Grading_gradedAlgebra (F : FermionIndex) (n : ℕ) : GradedAlgebra (A0Grading
    F n) :=
  { A0Grading_setLike F n with
    toDecomposition := DirectSum.Decomposition.ofLinearMap (A0Grading F n)
      (A0_decompose_lin F n)
      (by
        apply TensorProduct.ext'
        intro w c
        show (DirectSum.coeLinearMap (A0Grading F n)) ((A0_decompose_lin F n) (w ⊗ₜ c)) = w ⊗ₜ c
        have key :
            ((DirectSum.coeLinearMap (A0Grading F n) ∘ₗ A0_decompose_lin F n).comp
                (TensorProduct.mk ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
                  (Cl F) w)).comp
              (DirectSum.decomposeLinearEquiv (ClGrading F)).symm.toLinearMap =
            ((TensorProduct.mk ℚ (Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))
                (Cl F) w)).comp
              (DirectSum.decomposeLinearEquiv (ClGrading F)).symm.toLinearMap := by
          apply DirectSum.linearMap_ext ℚ
          intro k
          apply LinearMap.ext; intro x
          show (DirectSum.coeLinearMap (A0Grading F n))
              ((A0_decompose_lin F n) (w ⊗ₜ[ℚ] ((DirectSum.decomposeLinearEquiv (ClGrading F)).symm
                (DirectSum.lof ℚ (ZMod 2) (fun i => ClGrading F i) k x)))) =
            w ⊗ₜ[ℚ] ((DirectSum.decomposeLinearEquiv (ClGrading F)).symm
              (DirectSum.lof ℚ (ZMod 2) (fun i => ClGrading F i) k x))
          rw [DirectSum.decomposeLinearEquiv_symm_lof, A0_decompose_lin_tmul,
            DirectSum.coeLinearMap_lof]
        have := DFunLike.congr_fun key ((DirectSum.decomposeLinearEquiv (ClGrading F)) c)
        show (DirectSum.coeLinearMap (A0Grading F n)) ((A0_decompose_lin F n) (w ⊗ₜ[ℚ] c))
            = w ⊗ₜ[ℚ] c
        rw [show c = (DirectSum.decomposeLinearEquiv (ClGrading F)).symm
          ((DirectSum.decomposeLinearEquiv (ClGrading F)) c) from
          (LinearEquiv.symm_apply_apply _ c).symm]
        exact this)
      (by
        apply DirectSum.linearMap_ext ℚ
        intro k
        apply LinearMap.ext; intro z
        simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
        obtain ⟨y, hy⟩ := z.2
        have hz : z = ⟨A0GradingMap F n k y, LinearMap.mem_range_self (A0GradingMap F n k) y⟩ :=
          Subtype.ext hy.symm
        subst hz
        clear hy
        have key : A0_decompose_lin F n ∘ₗ A0GradingMap F n k =
            (DirectSum.lof ℚ (ZMod 2) (fun i => A0Grading F n i) k).comp
              (LinearMap.rangeRestrict (A0GradingMap F n k)) := by
          apply TensorProduct.ext'
          intro w c
          show A0_decompose_lin F n (A0GradingMap F n k (w ⊗ₜ c)) = _
          rw [A0GradingMap_tmul, A0_decompose_lin_tmul_coe]
          rfl
        exact DFunLike.congr_fun key y) }

noncomputable abbrev AB (F : FermionIndex) (n : ℕ) : Type :=
  GradedTensorProduct ℚ (RGradingQ F n) (A0Grading F n)

noncomputable def ABGradingMap (F : FermionIndex) (n : ℕ) (i j : ZMod 2) :
    (RGradingQ F n i) ⊗[ℚ] (A0Grading F n j) →ₗ[ℚ] AB F n :=
  (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)).toLinearMap ∘ₗ
    TensorProduct.map (RGradingQ F n i).subtype (A0Grading F n j).subtype

noncomputable def ABGrading (F : FermionIndex) (n : ℕ) (k : ZMod 2) : Submodule ℚ (AB F n) :=
  LinearMap.range (ABGradingMap F n 0 k) ⊔ LinearMap.range (ABGradingMap F n 1 (k + 1))

/-! ## The generators and lifts, in `AB F n` -/

noncomputable def Bu0 (F : FermionIndex) (n : ℕ) (u : I n) : A0 F n :=
  (InhomogeneousDeformations.Source.B n (Bmn.index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F)

noncomputable def aA0 (F : FermionIndex) (n : ℕ) (i : F.K) : A0 F n :=
  (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i)

noncomputable def BuAB (F : FermionIndex) (n : ℕ) (u : I n) : AB F n :=
  (1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n u)

noncomputable def aAB (F : FermionIndex) (n : ℕ) (i : F.K) : AB F n :=
  (1 : R F n) ᵍ⊗ₜ[ℚ] (aA0 F n i)

noncomputable def kappaAB (F : FermionIndex) (n : ℕ) : AB F n := (kappa F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n)


/-! ## Embeddings into `A0 F n`, then `AB F n` -/

/-! ## Membership lemmas -/

theorem Bu0_mem_A0Grading_zero (F : FermionIndex) (n : ℕ) (u : I n) : Bu0 F n u ∈ A0Grading F n 0 :=
  A0Grading_mem_of_tmul F n 0 (InhomogeneousDeformations.Source.B n (index0nToFun n u))
    (⟨1, SetLike.one_mem_graded (ClGrading F)⟩ : ClGrading F 0)

theorem aA0_mem_A0Grading_one (F : FermionIndex) (n : ℕ) (i : F.K) : aA0 F n i ∈ A0Grading F n 1 :=
  A0Grading_mem_of_tmul F n 1 1 (⟨a F i, a_odd F i⟩ : ClGrading F 1)

/-! ## The relations of the source algebra, in `AB F n` -/

/-- `a_i` commutes with `B_u`, in `A0 F n` — `W_n` is purely even
(`InhomogeneousDeformations.Source.WGrading n 0 = ⊤`), so its embedding is always
degree `0` and picks up no Koszul sign against anything. -/
theorem aA0_comm_Bu0 (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    aA0 F n i * Bu0 F n u = Bu0 F n u * aA0 F n i := by
  unfold Bu0 aA0
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
      (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (⟨a F i, a_odd F i⟩ : ClGrading
          F 1)
      (⟨InhomogeneousDeformations.Source.B n (index0nToFun n u), trivial⟩ :
        InhomogeneousDeformations.Source.WGrading n 0) (1 : Cl F),
    GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
      (InhomogeneousDeformations.Source.B n (index0nToFun n u))
      (⟨1, SetLike.one_mem_graded (ClGrading F)⟩ : ClGrading F 0)
      (⟨1, trivial⟩ : InhomogeneousDeformations.Source.WGrading n 0) (a F i)]
  simp

/-- **`B_u a_i = a_i B_u`, in `AB F n`** — `W_n` is purely even, so it commutes with
everything on the `Cl F` side. -/
theorem BuAB_comm_aAB (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    BuAB F n u * aAB F n i = aAB F n i * BuAB F n u := by
  unfold BuAB aAB
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (1 : R F n) (⟨Bu0 F n u, Bu0_mem_A0Grading_zero F n u⟩ : A0Grading F n 0)
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (aA0 F n i),
    GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (1 : R F n) (⟨aA0 F n i, aA0_mem_A0Grading_one F n i⟩ : A0Grading F n 1)
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (Bu0 F n u)]
  simp only [mul_one]
  rw [aA0_comm_Bu0]

/-- `a_i * a_j`, in `AB F n`, reduces to the embedding of the `Cl F`-level product — both
tensor factors (`R F n`, `W_n`) contribute `1` at degree `0` on both sides, so no sign
appears at either level. -/
theorem aAB_mul_aAB (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aAB F n i * aAB F n j
      = (1 : R F n) ᵍ⊗ₜ[ℚ]
          ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ]
            (a F i * a F j) : A0 F n) := by
  unfold aAB aA0
  have hinner : ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i) :
        A0 F n)
        * ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F j))
      = (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i * a F j) := by
    rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (𝒜 := InhomogeneousDeformations.Source.WGrading n) (ℬ := ClGrading F)
      (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) (⟨a F i, a_odd F i⟩ : ClGrading
          F 1)
      (⟨1, trivial⟩ : InhomogeneousDeformations.Source.WGrading n 0) (a F j)]
    simp only [mul_one]
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨(1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i),
        A0Grading_mem_of_tmul F n 1 1 (⟨a F i, a_odd F i⟩ : ClGrading F 1)⟩ : A0Grading F n 1)
      (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0)
      ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F j))]
  simp only [mul_one]
  rw [hinner]

/-- **`{a_i,a_j} = g_{ij}`, in `AB F n`** — lifted from `Cl F`'s own
`a_mul_a_add_swap` (`Source.lean`) through the embedding into `AB`. -/
theorem aAB_mul_add_swap (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aAB F n i * aAB F n j + aAB F n j * aAB F n i = (F.g i j) • (1 : AB F n) := by
  rw [aAB_mul_aAB, aAB_mul_aAB]
  rw [show ((1 : R F n) ᵍ⊗ₜ[ℚ]
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F i * a F j))
      + (1 : R F n) ᵍ⊗ₜ[ℚ]
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ] (a F j * a F i))
      : AB F n)
      = (1 : R F n) ᵍ⊗ₜ[ℚ]
        ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ]
          (a F i * a F j + a F j * a F i)) from by
    change (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] ((GradedTensorProduct.of ℚ
            (InhomogeneousDeformations.Source.WGrading n) (ClGrading F))
            ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ]
              (a F i * a F j)))) : AB F n)
        + GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] ((GradedTensorProduct.of ℚ
            (InhomogeneousDeformations.Source.WGrading n) (ClGrading F))
            ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ]
              (a F j * a F i))))
      = GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] ((GradedTensorProduct.of ℚ
            (InhomogeneousDeformations.Source.WGrading n) (ClGrading F))
            ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ]
              (a F i * a F j + a F j * a F i))))
    simp only [← map_add, ← TensorProduct.tmul_add]]
  rw [a_mul_a_add_swap]
  change ((1 : R F n) ᵍ⊗ₜ[ℚ]
      ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ]
        ((F.g i j) • (1 : Cl F))) : AB F n) = (F.g i j) • (1 : AB F n)
  rw [show ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ᵍ⊗ₜ[ℚ]
        ((F.g i j) • (1 : Cl F)) : A0 F n) = (F.g i j) • (1 : A0 F n) from by
      change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
          ((1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n)) ⊗ₜ[ℚ]
            ((F.g i j) • (1 : Cl F)))
        = (F.g i j) • (1 : A0 F n)
      rw [TensorProduct.tmul_smul, map_smul, ← Algebra.TensorProduct.one_def,
        GradedTensorProduct.of_one]]
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
      ((1 : R F n) ⊗ₜ[ℚ] ((F.g i j) • (1 : A0 F n))) = (F.g i j) • (1 : AB F n)
  rw [TensorProduct.tmul_smul, map_smul, ← Algebra.TensorProduct.one_def,
      GradedTensorProduct.of_one]

/-- `JnQ` at the two `index0nToFun`-embedded indices equals `Bmn`'s own `J`: applying
`MvPolynomial.constantCoeff` to `J_correspondence0n` (`Bmn/Base.lean`) and simplifying
`constantCoeff (cratN c) = constantCoeff (C c) = c`. -/
theorem JnQ_correspondence0n (n : ℕ) (u v : I n) :
    InhomogeneousDeformations.Source.JnQ n (index0nToFun n u) (index0nToFun n v) = J n u v := by
  unfold InhomogeneousDeformations.Source.JnQ
  rw [J_correspondence0n]
  unfold InhomogeneousDeformations.Indexed.cratN
  simp

/-- **`[B_u,B_v] = J_{uv}`, in `AB F n`** — lifted from `Source.B_comm`
(`osp-triviality`), through `index0nToFun`'s correspondence between `Bmn`'s own `J`
and `Source.JnQ` (`JnQ_correspondence0n` above). -/
theorem BuAB_comm (F : FermionIndex) (n : ℕ) (u v : I n) :
    BuAB F n u * BuAB F n v - BuAB F n v * BuAB F n u = (J n u v) • (1 : AB F n) := by
  have huv : BuAB F n u * BuAB F n v = (1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n u * Bu0 F n v) := by
    unfold BuAB
    exact GradedTensorProduct.tmul_coe_mul_one_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨Bu0 F n u, Bu0_mem_A0Grading_zero F n u⟩ : A0Grading F n 0) (Bu0 F n v)
  have hvu : BuAB F n v * BuAB F n u = (1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n v * Bu0 F n u) := by
    unfold BuAB
    exact GradedTensorProduct.tmul_coe_mul_one_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨Bu0 F n v, Bu0_mem_A0Grading_zero F n v⟩ : A0Grading F n 0) (Bu0 F n u)
  rw [huv, hvu]
  rw [show ((1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n u * Bu0 F n v) : AB F n)
        - (1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n v * Bu0 F n u)
      = (1 : R F n) ᵍ⊗ₜ[ℚ] (Bu0 F n u * Bu0 F n v - Bu0 F n v * Bu0 F n u) from by
    change (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] (Bu0 F n u * Bu0 F n v)) : AB F n)
        - GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] (Bu0 F n v * Bu0 F n u))
      = GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] (Bu0 F n u * Bu0 F n v - Bu0 F n v * Bu0 F n u))
    rw [← map_sub, TensorProduct.tmul_sub]]
  have hB : Bu0 F n u * Bu0 F n v - Bu0 F n v * Bu0 F n u
      = (J n u v) • (1 : A0 F n) := by
    unfold Bu0
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
    rw [show (InhomogeneousDeformations.Source.B n (index0nToFun n u)
            * InhomogeneousDeformations.Source.B n (index0nToFun n v)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
          - (InhomogeneousDeformations.Source.B n (index0nToFun n v)
              * InhomogeneousDeformations.Source.B n (index0nToFun n u)) ᵍ⊗ₜ[ℚ] (1 : Cl F)
        = (InhomogeneousDeformations.Source.opComm
            (InhomogeneousDeformations.Source.B n (index0nToFun n u))
            (InhomogeneousDeformations.Source.B n (index0nToFun n v))) ᵍ⊗ₜ[ℚ] (1 : Cl F) from by
      change _ = (GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading
          F))
          ((InhomogeneousDeformations.Source.opComm
            (InhomogeneousDeformations.Source.B n (index0nToFun n u))
            (InhomogeneousDeformations.Source.B n (index0nToFun n v))) ⊗ₜ[ℚ] (1 : Cl F))
      unfold InhomogeneousDeformations.Source.opComm
      rw [TensorProduct.sub_tmul, map_sub],
      InhomogeneousDeformations.Source.B_comm, JnQ_correspondence0n]
    change GradedTensorProduct.of ℚ (InhomogeneousDeformations.Source.WGrading n) (ClGrading F)
        (((J n u v) • (1 : Module.End ℚ (InhomogeneousDeformations.Source.WPoly n))) ⊗ₜ[ℚ]
          (1 : Cl F))
      = (J n u v) • (1 : A0 F n)
    rw [← TensorProduct.smul_tmul', map_smul, ← Algebra.TensorProduct.one_def,
      GradedTensorProduct.of_one]
  rw [hB]
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
      ((1 : R F n) ⊗ₜ[ℚ] ((J n u v) • (1 : A0 F n))) = (J n u v) • (1 : AB F n)
  rw [TensorProduct.tmul_smul, map_smul, ← Algebra.TensorProduct.one_def,
      GradedTensorProduct.of_one]


noncomputable def betaKappa (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : R F n :=
  algebraMap (Pmn F n) (R F n) (beta F n u i) * kappa F n

noncomputable def betaKappaAB (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : AB F n :=
  (betaKappa F n u i) ᵍ⊗ₜ[ℚ] (1 : A0 F n)

noncomputable def cAB (F : FermionIndex) (n : ℕ) (u : I n) : AB F n :=
  ∑ i : F.K, betaKappaAB F n u i * aAB F n (F.dual i)

noncomputable def bU (F : FermionIndex) (n : ℕ) (u : I n) : AB F n := BuAB F n u + cAB F n u

/-! ## Untwisting relations

No step inspects the concrete shape of `F.K` (the one `g`-unfolding step, `hgval` in
`bU_comm_aAB`, uses only `F.dual_dual`, a `FermionIndex` field). Needed by
`Xhat_eq_iota0_add` (below) and hence `recovery`. -/

theorem ABGradingMap_tmul (F : FermionIndex) (n : ℕ) (i j : ZMod 2) (r : RGradingQ F n i) (x :
    A0Grading F n j) :
    ABGradingMap F n i j (r ⊗ₜ x) = (r : R F n) ᵍ⊗ₜ[ℚ] (x : A0 F n) := rfl

theorem ABGradingMap_range_le (F : FermionIndex) (n : ℕ) (i j : ZMod 2) :
    LinearMap.range (ABGradingMap F n i j) ≤ ABGrading F n (i + j) := by
  rcases InhomogeneousDeformations.Source.ZMod2_eq_zero_or_one i with hi | hi <;> subst hi
  · rw [zero_add]; exact le_sup_left
  · change LinearMap.range (ABGradingMap F n 1 j) ≤
      LinearMap.range (ABGradingMap F n 0 (1 + j)) ⊔ LinearMap.range (ABGradingMap F n 1 ((1 + j) +
          1))
    rw [show (1 + j : ZMod 2) + 1 = j from by revert j; decide]
    exact le_sup_right

theorem ABGrading_mem_of_tmul (F : FermionIndex) (n : ℕ) (i j : ZMod 2) (r : RGradingQ F n i) (x :
    A0Grading F n j) :
    (r : R F n) ᵍ⊗ₜ[ℚ] (x : A0 F n) ∈ ABGrading F n (i + j) :=
  ABGradingMap_range_le F n i j ⟨r ⊗ₜ x, rfl⟩

/-- The grading `ABGrading` of `AB F n` is a graded monoid. -/
instance ABGrading_setLike (F : FermionIndex) (n : ℕ) : SetLike.GradedMonoid (ABGrading F n) where
  one_mem := by
    have h : (1 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) ∈ ABGrading F n (0 + 0) :=
      ABGrading_mem_of_tmul F n 0 0
        (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0)
        (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    have h1 : (1 : AB F n) = (1 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) := by
      rw [GradedTensorProduct.tmul, ← GradedTensorProduct.of_one, Algebra.TensorProduct.one_def]
    rw [h1]; simpa using h
  mul_mem := by
    intro i j gi gj hgi hgj
    have mul_mem_aux : ∀ {i' j' i'' j'' : ZMod 2} (x y : AB F n),
        x ∈ LinearMap.range (ABGradingMap F n i' j') →
        y ∈ LinearMap.range (ABGradingMap F n i'' j'') →
        x * y ∈ ABGrading F n ((i' + i'') + (j' + j'')) := by
      intro i' j' i'' j'' x y hx hy
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      induction x using TensorProduct.inductionOn with
      | add x1 x2 hx1 hx2 => simp only [map_add, add_mul]; exact add_mem hx1 hx2
      | tmul r1 x1 =>
        induction y using TensorProduct.inductionOn with
        | add y1 y2 hy1 hy2 => simp only [map_add, mul_add]; exact add_mem hy1 hy2
        | tmul r2 x2 =>
          rw [ABGradingMap_tmul, ABGradingMap_tmul,
            GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
              (r1 : R F n) x1 r2 (x2 : A0 F n)]
          exact Submodule.smul_mem _ _
            (ABGrading_mem_of_tmul F n (i' + i'') (j' + j'')
              (⟨(r1 : R F n) * (r2 : R F n), SetLike.mul_mem_graded r1.2 r2.2⟩ :
                RGradingQ F n (i' + i''))
              (⟨(x1 : A0 F n) * (x2 : A0 F n), SetLike.mul_mem_graded x1.2 x2.2⟩ :
                A0Grading F n (j' + j'')))
    obtain ⟨deg00, deg01, deg10, deg11⟩ := InhomogeneousDeformations.Source.ZMod2_total_degree_cases
        i j
    obtain ⟨gi0, hgi0, gi1, hgi1, rfl⟩ := Submodule.mem_sup.mp hgi
    obtain ⟨gj0, hgj0, gj1, hgj1, rfl⟩ := Submodule.mem_sup.mp hgj
    have expand : (gi0 + gi1) * (gj0 + gj1) = gi0 * gj0 + gi0 * gj1 + gi1 * gj0 + gi1 * gj1 := by
      noncomm_ring
    rw [expand]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · rw [deg00]; exact mul_mem_aux gi0 gj0 hgi0 hgj0
    · rw [deg01]; exact mul_mem_aux gi0 gj1 hgi0 hgj1
    · rw [deg10]; exact mul_mem_aux gi1 gj0 hgi1 hgj0
    · rw [deg11]; exact mul_mem_aux gi1 gj1 hgi1 hgj1

theorem betaKappa_mem_RGrading_one (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    betaKappa F n u i ∈ RGrading F n 1 := by
  unfold betaKappa
  have h0 : algebraMap (Pmn F n) (R F n) (beta F n u i) ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  have h1 := SetLike.mul_mem_graded h0 (kappa_mem_RGrading_one F n)
  rwa [zero_add] at h1

theorem betaKappa_mem_RGradingQ_one (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    betaKappa F n u i ∈ RGradingQ F n 1 := betaKappa_mem_RGrading_one F n u i

theorem betaKappaAB_mem_ABGrading_one (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    betaKappaAB F n u i ∈ ABGrading F n 1 := by
  have h := ABGrading_mem_of_tmul F n 1 0
    (⟨betaKappa F n u i, betaKappa_mem_RGradingQ_one F n u i⟩ : RGradingQ F n 1)
    (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
  simpa [betaKappaAB] using h

theorem aAB_mem_ABGrading_one (F : FermionIndex) (n : ℕ) (i : F.K) : aAB F n i ∈ ABGrading F n 1 :=
    by
  have h := ABGrading_mem_of_tmul F n 0 1
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0)
    (⟨aA0 F n i, aA0_mem_A0Grading_one F n i⟩ : A0Grading F n 1)
  simpa [aAB] using h

/-- **`c_u` is even.** -/
theorem cAB_mem_ABGrading_zero (F : FermionIndex) (n : ℕ) (u : I n) : cAB F n u ∈ ABGrading F n 0 :=
    by
  unfold cAB
  apply Submodule.sum_mem
  intro i _
  have h := SetLike.mul_mem_graded (betaKappaAB_mem_ABGrading_one F n u i)
    (aAB_mem_ABGrading_one F n (F.dual i))
  rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h

theorem aAB_mul_betaKappaAB (F : FermionIndex) (n : ℕ) (v : I n) (j : F.K) (i : F.K) :
    aAB F n i * betaKappaAB F n v j = -(betaKappaAB F n v j * aAB F n i) := by
  unfold aAB betaKappaAB
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (1 : R F n) (⟨aA0 F n i, aA0_mem_A0Grading_one F n i⟩ : A0Grading F n 1)
    (⟨betaKappa F n v j, betaKappa_mem_RGradingQ_one F n v j⟩ : RGradingQ F n 1) (1 : A0 F n),
    GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (betaKappa F n v j) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (aA0 F n i)]
  simp only [one_mul, mul_one]
  norm_num

theorem betaKappa_mul_betaKappa (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) (v : I n) (j : F.K) :
    betaKappa F n u i * betaKappa F n v j = 0 := by
  unfold betaKappa
  have hcomm : kappa F n * algebraMap (Pmn F n) (R F n) (beta F n v j)
      = algebraMap (Pmn F n) (R F n) (beta F n v j) * kappa F n :=
    (Algebra.commutes _ _).symm
  calc algebraMap (Pmn F n) (R F n) (beta F n u i) * kappa F n
        * (algebraMap (Pmn F n) (R F n) (beta F n v j) * kappa F n)
      = algebraMap (Pmn F n) (R F n) (beta F n u i)
          * (kappa F n * algebraMap (Pmn F n) (R F n) (beta F n v j)) * kappa F n := by
        noncomm_ring
    _ = algebraMap (Pmn F n) (R F n) (beta F n u i)
          * (algebraMap (Pmn F n) (R F n) (beta F n v j) * kappa F n) * kappa F n := by
        rw [hcomm]
    _ = algebraMap (Pmn F n) (R F n) (beta F n u i * beta F n v j) * (kappa F n * kappa F n) := by
        rw [map_mul]; noncomm_ring
    _ = 0 := by rw [kappa_sq, mul_zero]

theorem betaKappaAB_mul_betaKappaAB (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) (v : I n) (j :
    F.K) :
    betaKappaAB F n u i * betaKappaAB F n v j = 0 := by
  unfold betaKappaAB
  rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (betaKappa F n u i) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    (⟨betaKappa F n v j, betaKappa_mem_RGradingQ_one F n v j⟩ : RGradingQ F n 1) (1 : A0 F n)]
  rw [betaKappa_mul_betaKappa, mul_one]
  simp [GradedTensorProduct.tmul]

theorem cross_term_zero (F : FermionIndex) (n : ℕ) (u v : I n) (i j : F.K) :
    (betaKappaAB F n u i * aAB F n (F.dual i)) * (betaKappaAB F n v j * aAB F n (F.dual j)) = 0 :=
        by
  have e : (betaKappaAB F n u i * aAB F n (F.dual i)) * (betaKappaAB F n v j * aAB F n (F.dual j))
      = betaKappaAB F n u i * (aAB F n (F.dual i) * betaKappaAB F n v j) * aAB F n (F.dual j) := by
    noncomm_ring
  rw [e, aAB_mul_betaKappaAB]
  rw [show betaKappaAB F n u i * (-(betaKappaAB F n v j * aAB F n (F.dual i))) * aAB F n (F.dual j)
      = -((betaKappaAB F n u i * betaKappaAB F n v j)
          * (aAB F n (F.dual i) * aAB F n (F.dual j))) from by noncomm_ring,
    betaKappaAB_mul_betaKappaAB]
  simp

/-- **`c_u · c_v = 0`, for all `u,v`.** -/
theorem cAB_mul_cAB (F : FermionIndex) (n : ℕ) (u v : I n) : cAB F n u * cAB F n v = 0 := by
  unfold cAB
  rw [Finset.sum_mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact cross_term_zero F n u v i j

/-- **`[bU u, a_i] = β_{u,i}κ`**. -/
theorem bU_comm_aAB (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    bU F n u * aAB F n i - aAB F n i * bU F n u = betaKappaAB F n u i := by
  have hB : BuAB F n u * aAB F n i - aAB F n i * BuAB F n u = 0 := by
    rw [BuAB_comm_aAB]; abel
  have hterm : ∀ j : F.K,
      betaKappaAB F n u j * aAB F n (F.dual j) * aAB F n i
        - aAB F n i * (betaKappaAB F n u j * aAB F n (F.dual j))
      = if i = j then betaKappaAB F n u j else 0 := by
    intro j
    have e0 : aAB F n i * (betaKappaAB F n u j * aAB F n (F.dual j))
        = -(betaKappaAB F n u j * aAB F n i * aAB F n (F.dual j)) := by
      rw [show aAB F n i * (betaKappaAB F n u j * aAB F n (F.dual j))
          = (aAB F n i * betaKappaAB F n u j) * aAB F n (F.dual j) from by noncomm_ring,
        aAB_mul_betaKappaAB, neg_mul]
    rw [e0, sub_neg_eq_add]
    have hac := aAB_mul_add_swap F n (F.dual j) i
    have hgval : F.g (F.dual j) i = if i = j then 1 else 0 := by
      unfold FermionIndex.g; rw [F.dual_dual]
    rw [hgval] at hac
    have hcombine : betaKappaAB F n u j * aAB F n (F.dual j) * aAB F n i
        + betaKappaAB F n u j * aAB F n i * aAB F n (F.dual j)
        = betaKappaAB F n u j * (aAB F n (F.dual j) * aAB F n i + aAB F n i * aAB F n (F.dual j)) :=
            by
      noncomm_ring
    rw [hcombine, hac]
    split_ifs <;> simp
  unfold bU
  have hexp : (BuAB F n u + cAB F n u) * aAB F n i - aAB F n i * (BuAB F n u + cAB F n u)
      = (BuAB F n u * aAB F n i - aAB F n i * BuAB F n u)
        + (cAB F n u * aAB F n i - aAB F n i * cAB F n u) := by noncomm_ring
  rw [hexp, hB, zero_add]
  unfold cAB
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl]
  · intro j _ hj; rw [ite_eq_right (fun h => hj h.symm)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem BuAB_comm_betaKappaAB (F : FermionIndex) (n : ℕ) (u v : I n) (j : F.K) :
    BuAB F n u * betaKappaAB F n v j = betaKappaAB F n v j * BuAB F n u := by
  unfold BuAB betaKappaAB
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨Bu0 F n u, Bu0_mem_A0Grading_zero F n u⟩ : A0Grading F n 0)
      (⟨betaKappa F n v j, betaKappa_mem_RGradingQ_one F n v j⟩ : RGradingQ F n 1) (1 : A0 F n),
    GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (betaKappa F n v j) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
      (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (Bu0 F n u)]
  simp only [mul_zero, mul_one, one_mul, uzpow_zero, one_smul]

theorem BuAB_comm_betaKappaAB_mul_aAB (F : FermionIndex) (n : ℕ) (u v : I n) (j : F.K) :
    BuAB F n u * (betaKappaAB F n v j * aAB F n (F.dual j))
      = (betaKappaAB F n v j * aAB F n (F.dual j)) * BuAB F n u := by
  rw [show BuAB F n u * (betaKappaAB F n v j * aAB F n (F.dual j))
      = (BuAB F n u * betaKappaAB F n v j) * aAB F n (F.dual j) from by noncomm_ring,
    BuAB_comm_betaKappaAB]
  rw [show betaKappaAB F n v j * BuAB F n u * aAB F n (F.dual j)
      = betaKappaAB F n v j * (BuAB F n u * aAB F n (F.dual j)) from by noncomm_ring,
    BuAB_comm_aAB]
  noncomm_ring

theorem BuAB_comm_cAB (F : FermionIndex) (n : ℕ) (u v : I n) :
    BuAB F n u * cAB F n v = cAB F n v * BuAB F n u := by
  unfold cAB
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => BuAB_comm_betaKappaAB_mul_aAB F n u v j)

/-- **`[bU u, bU v] = J_{uv}`.** -/
theorem bU_comm_bU (F : FermionIndex) (n : ℕ) (u v : I n) :
    bU F n u * bU F n v - bU F n v * bU F n u = (J n u v) • (1 : AB F n) := by
  unfold bU
  have hexp : (BuAB F n u + cAB F n u) * (BuAB F n v + cAB F n v)
      - (BuAB F n v + cAB F n v) * (BuAB F n u + cAB F n u)
      = (BuAB F n u * BuAB F n v - BuAB F n v * BuAB F n u)
        + (BuAB F n u * cAB F n v - cAB F n v * BuAB F n u)
        + (cAB F n u * BuAB F n v - BuAB F n v * cAB F n u)
        + (cAB F n u * cAB F n v - cAB F n v * cAB F n u) := by noncomm_ring
  rw [hexp, BuAB_comm_cAB, sub_self, add_zero,
    show cAB F n u * BuAB F n v - BuAB F n v * cAB F n u = 0 from by
      rw [BuAB_comm_cAB]; abel,
    add_zero, cAB_mul_cAB, cAB_mul_cAB, sub_self, add_zero, BuAB_comm]

noncomputable def L0 (F : FermionIndex) (n : ℕ) (u v : I n) : AB F n :=
  (1 / 4 : ℚ) • (BuAB F n u * BuAB F n v + BuAB F n v * BuAB F n u)

noncomputable def S0 (F : FermionIndex) (n : ℕ) (i j : F.K) : AB F n :=
  (1 / 2 : ℚ) • (aAB F n i * aAB F n j - aAB F n j * aAB F n i)

noncomputable def F0 (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : AB F n :=
  (1 / 4 : ℚ) • (aAB F n i * BuAB F n u + BuAB F n u * aAB F n i)

noncomputable def Lhat (F : FermionIndex) (n : ℕ) (u v : I n) : AB F n :=
  (1 / 4 : ℚ) • (bU F n u * bU F n v + bU F n v * bU F n u)

noncomputable def Shat (F : FermionIndex) (n : ℕ) (i j : F.K) : AB F n := S0 F n i j

noncomputable def Fhat (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : AB F n :=
  (1 / 4 : ℚ) • (aAB F n i * bU F n u + bU F n u * aAB F n i)

noncomputable def X0 (F : FermionIndex) (n : ℕ) : OspBasis F n → AB F n
  | .inl ⟨(u, v), _⟩ => L0 F n u v
  | .inr (.inl ⟨(i, j), _⟩) => S0 F n i j
  | .inr (.inr (u, i)) => F0 F n u i

noncomputable def Xhat (F : FermionIndex) (n : ℕ) : OspBasis F n → AB F n
  | .inl ⟨(u, v), _⟩ => Lhat F n u v
  | .inr (.inl ⟨(i, j), _⟩) => Shat F n i j
  | .inr (.inr (u, i)) => Fhat F n u i

noncomputable def iota0 (F : FermionIndex) (n : ℕ) (x : OspMod F n) : AB F n :=
  ∑ X : OspBasis F n, ((algebraMap (Pmn F n) (R F n) (x X)) ᵍ⊗ₜ[ℚ] (1 : A0 F n)) * X0 F n X

noncomputable def iotaB (F : FermionIndex) (n : ℕ) (x : OspMod F n) : AB F n :=
  iota0 F n x + kappaAB F n * iota0 F n (hTilde x)

noncomputable def scomm {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (x y : AB F n) :
    AB F n := x * y - gsign (parity X) (parity Y) • (y * x)

/-! ## `iota0`'s linearity and collapse, and `Xhat_eq_iota0_add`

No step uses the concrete shape of `F.K` beyond what `sum_dual`/`F.key_injective`/`F.dual_dual`
supply generically. Needed by `recovery`/`recovery_delta` below. -/

theorem tmul_add_left (F : FermionIndex) (n : ℕ) (r1 r2 : R F n) (x : A0 F n) :
    ((r1 + r2) ᵍ⊗ₜ[ℚ] x : AB F n) = r1 ᵍ⊗ₜ[ℚ] x + r2 ᵍ⊗ₜ[ℚ] x := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) ((r1 + r2) ⊗ₜ[ℚ] x)
    = GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r1 ⊗ₜ[ℚ] x)
      + GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r2 ⊗ₜ[ℚ] x)
  rw [← map_add, TensorProduct.add_tmul]

theorem tmul_zero_left (F : FermionIndex) (n : ℕ) (x : A0 F n) : ((0 : R F n) ᵍ⊗ₜ[ℚ] x : AB F n) = 0
    := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) ((0 : R F n) ⊗ₜ[ℚ] x) = 0
  rw [TensorProduct.zero_tmul, map_zero]

theorem tmul_neg_left (F : FermionIndex) (n : ℕ) (r : R F n) (x : A0 F n) :
    ((-r) ᵍ⊗ₜ[ℚ] x : AB F n) = -(r ᵍ⊗ₜ[ℚ] x) := by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) ((-r) ⊗ₜ[ℚ] x)
    = -(GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n) (r ⊗ₜ[ℚ] x))
  rw [← map_neg, TensorProduct.neg_tmul]

theorem iota0_add (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    iota0 F n (x + y) = iota0 F n x + iota0 F n y := by
  unfold iota0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro X _
  rw [ospMod_add_apply, map_add, tmul_add_left, add_mul]

theorem iota0_zero (F : FermionIndex) (n : ℕ) : iota0 F n (0 : OspMod F n) = 0 := by
  unfold iota0
  apply Finset.sum_eq_zero
  intro X _
  rw [ospMod_zero_apply, map_zero, tmul_zero_left, zero_mul]

theorem iota0_neg (F : FermionIndex) (n : ℕ) (x : OspMod F n) : iota0 F n (-x) = -iota0 F n x := by
  have h : iota0 F n (-x) + iota0 F n x = 0 := by
    rw [← iota0_add, neg_add_cancel, iota0_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem iota0_sum (F : FermionIndex) (n : ℕ) {α : Type*} (s : Finset α) (f : α → OspMod F n) :
    iota0 F n (∑ a ∈ s, f a) = ∑ a ∈ s, iota0 F n (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [iota0_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, iota0_add, ih, Finset.sum_insert ha]

theorem one_tmul_one (F : FermionIndex) (n : ℕ) : ((1 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n) = 1 :=
    by
  change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
      ((1 : R F n) ⊗ₜ[ℚ] (1 : A0 F n)) = 1
  rw [← Algebra.TensorProduct.one_def, GradedTensorProduct.of_one]

theorem iota0_eN (F : FermionIndex) (n : ℕ) (X : OspBasis F n) : iota0 F n (eN X) = X0 F n X := by
  unfold iota0
  rw [Finset.sum_eq_single X]
  · simp [eN, map_one, one_tmul_one]
  · intro Y _ hY
    simp [eN, hY, tmul_zero_left]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iota0_smul_eN (F : FermionIndex) (n : ℕ) (c : Pmn F n) (X : OspBasis F n) :
    iota0 F n (c • eN X) = (algebraMap (Pmn F n) (R F n) c) ᵍ⊗ₜ[ℚ] (1 : A0 F n) * X0 F n X := by
  unfold iota0
  rw [Finset.sum_eq_single X]
  · simp [eN]
  · intro Y _ hY
    simp [eN, hY, tmul_zero_left]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iota0_smul (F : FermionIndex) (n : ℕ) (c : Pmn F n) (x : OspMod F n) :
    iota0 F n (c • x)
      = (algebraMap (Pmn F n) (R F n) c) ᵍ⊗ₜ[ℚ] (1 : A0 F n) * iota0 F n x := by
  unfold iota0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  have hmem : algebraMap (Pmn F n) (R F n) (x X) ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  rw [ospMod_smul_apply, map_mul, ← mul_assoc,
    GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (algebraMap (Pmn F n) (R F n) c)
      (⟨algebraMap (Pmn F n) (R F n) (x X), hmem⟩ : RGradingQ F n 0)
      (1 : A0 F n)]

theorem iota0_smul_rat (F : FermionIndex) (n : ℕ) (c : ℚ) (x : OspMod F n) :
    iota0 F n (c • x) = c • iota0 F n x := by
  rw [qsmul_eq_Csmul, iota0_smul]
  have hc : (algebraMap (Pmn F n) (R F n) (MvPolynomial.C c) : R F n) = c • (1 : R F n) := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply ℚ (Pmn F n) (R F n),
      Algebra.algebraMap_eq_smul_one]
    rfl
  rw [show (algebraMap (Pmn F n) (R F n) (MvPolynomial.C c) : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n)
      = c • ((1 : R F n) ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n) from by
    rw [hc]
    change GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
        ((c • (1 : R F n)) ⊗ₜ[ℚ] (1 : A0 F n))
      = c • GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)
          ((1 : R F n) ⊗ₜ[ℚ] (1 : A0 F n))
    rw [← map_smul, TensorProduct.smul_tmul']
    rfl]
  rw [one_tmul_one, smul_mul_assoc, one_mul]

theorem iota0_Sof (F : FermionIndex) (n : ℕ) (p q : F.K) : iota0 F n (Sof p q) = S0 F n p q := by
  unfold Sof
  split
  · rw [iota0_eN]; rfl
  · rename_i h1
    split
    · rename_i h2
      rw [iota0_neg, iota0_eN]
      show -(X0 F n (Sum.inr (Sum.inl ⟨(q, p), h2⟩) : OspBasis F n)) = S0 F n p q
      change -(S0 F n q p) = S0 F n p q
      unfold S0
      rw [← smul_neg]
      congr 1
      abel
    · rename_i h2
      have hpq : p = q := F.key_injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
      subst hpq
      rw [iota0_zero]
      unfold S0
      simp

theorem BuAB_mul_aAB_eq_two_F0 (F : FermionIndex) (n : ℕ) (u : I n) (k : F.K) :
    BuAB F n u * aAB F n k = (2 : ℚ) • F0 F n u k := by
  have h := BuAB_comm_aAB F n u k
  unfold F0
  rw [← h]
  module

theorem kappaAB_mul_algebraMap_beta_tmul_one (F : FermionIndex) (n : ℕ) (a : I n) (b : F.K) :
    kappaAB F n * (algebraMap (Pmn F n) (R F n) (beta F n a b)) ᵍ⊗ₜ[ℚ] (1 : A0 F n)
      = betaKappaAB F n a b := by
  unfold kappaAB betaKappaAB betaKappa
  have hmem : algebraMap (Pmn F n) (R F n) (beta F n a b) ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  rw [GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (kappa F n) (⟨algebraMap (Pmn F n) (R F n) (beta F n a b), hmem⟩ : RGradingQ F n 0)
    (1 : A0 F n)]
  congr 1
  change kappa F n * (algebraMap (Pmn F n) (R F n) (beta F n a b))
      = (algebraMap (Pmn F n) (R F n) (beta F n a b)) * kappa F n
  exact (Algebra.commutes (beta F n a b) (kappa F n)).symm

/-- **For every basis element `X`: `X̂ = ι₀(eN X) + κ·ι₀(h̃(eN X))`** (paper
Proposition 4.1, in the realization), with `hTilde` of `HTilde.lean`, not a restatement — the tie
between the source side and the coordinate side. -/
theorem Xhat_eq_iota0_add (F : FermionIndex) (n : ℕ) (X : OspBasis F n) :
    Xhat F n X = iota0 F n (eN X) + kappaAB F n * iota0 F n (hTilde (eN X)) := by
  match X with
  | .inr (.inl ⟨(i, j), h⟩) =>
    rw [iota0_eN, hTilde_eN]
    change Shat F n i j = X0 F n (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n)
      + kappaAB F n * iota0 F n (hTildeBasis (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n))
    have hz : hTildeBasis (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) = 0 := rfl
    rw [hz, iota0_zero, mul_zero, add_zero]
    change Shat F n i j = S0 F n i j
    rfl
  | .inl ⟨(u, v), h⟩ =>
    change Lhat F n u v = iota0 F n (eN (Sum.inl ⟨(u, v), h⟩ : OspBasis F n))
      + kappaAB F n * iota0 F n (hTilde (eN (Sum.inl ⟨(u, v), h⟩ : OspBasis F n)))
    have hLhat_eq : Lhat F n u v
        = L0 F n u v
          + ∑ i : F.K, (betaKappaAB F n u (F.dual i) * F0 F n v i
              + betaKappaAB F n v (F.dual i) * F0 F n u i) := by
      unfold Lhat
      have hexp : bU F n u * bU F n v + bU F n v * bU F n u
          = (BuAB F n u * BuAB F n v + BuAB F n v * BuAB F n u)
            + (BuAB F n u * cAB F n v + cAB F n v * BuAB F n u)
            + (cAB F n u * BuAB F n v + BuAB F n v * cAB F n u)
            + (cAB F n u * cAB F n v + cAB F n v * cAB F n u) := by
        unfold bU; noncomm_ring
      rw [hexp]
      have hL4 : BuAB F n u * BuAB F n v + BuAB F n v * BuAB F n u = (4 : ℚ) • L0 F n u v := by
        unfold L0; rw [smul_smul]; norm_num
      have hcc0 : cAB F n u * cAB F n v + cAB F n v * cAB F n u = 0 := by
        rw [cAB_mul_cAB, cAB_mul_cAB]; abel
      have hBv_cu : BuAB F n u * cAB F n v
          = (2 : ℚ) • ∑ i : F.K, betaKappaAB F n v (F.dual i) * F0 F n u i := by
        unfold cAB
        rw [Finset.mul_sum]
        have hstep : ∀ j : F.K, BuAB F n u * (betaKappaAB F n v j * aAB F n (F.dual j))
            = (2 : ℚ) • (betaKappaAB F n v j * F0 F n u (F.dual j)) := by
          intro j
          rw [show BuAB F n u * (betaKappaAB F n v j * aAB F n (F.dual j))
              = (BuAB F n u * betaKappaAB F n v j) * aAB F n (F.dual j) from by noncomm_ring,
            BuAB_comm_betaKappaAB, mul_assoc, BuAB_mul_aAB_eq_two_F0, mul_smul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.smul_sum]
        congr 1
        have hr := sum_dual (M := AB F n)
          (fun i => betaKappaAB F n v (F.dual i) * F0 F n u i)
        simpa only [F.dual_dual] using hr
      have hBc : BuAB F n u * cAB F n v + cAB F n v * BuAB F n u
          = (2 : ℚ) • ((2 : ℚ) • ∑ i : F.K, betaKappaAB F n v (F.dual i) * F0 F n u i) := by
        rw [← BuAB_comm_cAB, hBv_cu]; module
      have hcv_Bu : cAB F n u * BuAB F n v
          = (2 : ℚ) • ∑ i : F.K, betaKappaAB F n u (F.dual i) * F0 F n v i := by
        unfold cAB
        rw [Finset.sum_mul]
        have hstep : ∀ j : F.K, betaKappaAB F n u j * aAB F n (F.dual j) * BuAB F n v
            = (2 : ℚ) • (betaKappaAB F n u j * F0 F n v (F.dual j)) := by
          intro j
          rw [show betaKappaAB F n u j * aAB F n (F.dual j) * BuAB F n v
              = betaKappaAB F n u j * (aAB F n (F.dual j) * BuAB F n v) from by noncomm_ring,
            ← BuAB_comm_aAB, BuAB_mul_aAB_eq_two_F0, mul_smul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.smul_sum]
        congr 1
        have hr := sum_dual (M := AB F n)
          (fun i => betaKappaAB F n u (F.dual i) * F0 F n v i)
        simpa only [F.dual_dual] using hr
      have hcB : cAB F n u * BuAB F n v + BuAB F n v * cAB F n u
          = (2 : ℚ) • ((2 : ℚ) • ∑ i : F.K, betaKappaAB F n u (F.dual i) * F0 F n v i) := by
        rw [BuAB_comm_cAB, hcv_Bu]; module
      have hcombine : (∑ i : F.K, (betaKappaAB F n u (F.dual i) * F0 F n v i
            + betaKappaAB F n v (F.dual i) * F0 F n u i) : AB F n)
          = (∑ i : F.K, betaKappaAB F n u (F.dual i) * F0 F n v i)
            + ∑ i : F.K, betaKappaAB F n v (F.dual i) * F0 F n u i :=
        Finset.sum_add_distrib
      rw [hL4, hBc, hcB, hcc0, add_zero, hcombine]
      module
    rw [hLhat_eq, iota0_eN, hTilde_eN]
    have hX0 : X0 F n (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) = L0 F n u v := rfl
    have hHt : hTildeBasis (Sum.inl ⟨(u, v), h⟩ : OspBasis F n)
        = ∑ i : F.K, (beta F n u (F.dual i) • eN (Fof v i)
            + beta F n v (F.dual i) • eN (Fof u i)) := rfl
    rw [hX0, hHt, iota0_sum]
    have hterm : ∀ i : F.K, iota0 F n (beta F n u (F.dual i) • eN (Fof v i)
          + beta F n v (F.dual i) • eN (Fof u i))
        = (algebraMap (Pmn F n) (R F n) (beta F n u (F.dual i))) ᵍ⊗ₜ[ℚ] (1 : A0 F n)
            * F0 F n v i
          + (algebraMap (Pmn F n) (R F n) (beta F n v (F.dual i))) ᵍ⊗ₜ[ℚ] (1 : A0 F n)
            * F0 F n u i := by
      intro i
      rw [iota0_add, iota0_smul_eN, iota0_smul_eN]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_add, ← mul_assoc, ← mul_assoc, kappaAB_mul_algebraMap_beta_tmul_one,
      kappaAB_mul_algebraMap_beta_tmul_one]
  | .inr (.inr (u, i)) =>
    change Fhat F n u i = iota0 F n (eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
      + kappaAB F n * iota0 F n (hTilde (eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n)))
    have hFhat_eq : Fhat F n u i
        = F0 F n u i + (1 / 2 : ℚ) • ∑ j : F.K, betaKappaAB F n u j * S0 F n (F.dual j) i := by
      unfold Fhat
      have hexp : aAB F n i * bU F n u + bU F n u * aAB F n i
          = (aAB F n i * BuAB F n u + BuAB F n u * aAB F n i)
            + (aAB F n i * cAB F n u + cAB F n u * aAB F n i) := by
        unfold bU; noncomm_ring
      rw [hexp]
      have hB4 : aAB F n i * BuAB F n u + BuAB F n u * aAB F n i = (4 : ℚ) • F0 F n u i := by
        unfold F0
        rw [smul_smul]
        norm_num
      have hc2 : aAB F n i * cAB F n u + cAB F n u * aAB F n i
          = (2 : ℚ) • ∑ j : F.K, betaKappaAB F n u j * S0 F n (F.dual j) i := by
        unfold cAB
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have e0 : aAB F n i * (betaKappaAB F n u j * aAB F n (F.dual j))
            = -(betaKappaAB F n u j * (aAB F n i * aAB F n (F.dual j))) := by
          rw [show aAB F n i * (betaKappaAB F n u j * aAB F n (F.dual j))
              = (aAB F n i * betaKappaAB F n u j) * aAB F n (F.dual j) from by noncomm_ring,
            aAB_mul_betaKappaAB]
          noncomm_ring
        have e1 : (betaKappaAB F n u j * aAB F n (F.dual j)) * aAB F n i
            = betaKappaAB F n u j * (aAB F n (F.dual j) * aAB F n i) := by noncomm_ring
        have hS : aAB F n (F.dual j) * aAB F n i - aAB F n i * aAB F n (F.dual j)
            = (2 : ℚ) • S0 F n (F.dual j) i := by
          unfold S0; rw [smul_smul]; norm_num
        rw [e0, e1,
          show -(betaKappaAB F n u j * (aAB F n i * aAB F n (F.dual j)))
              + betaKappaAB F n u j * (aAB F n (F.dual j) * aAB F n i)
            = betaKappaAB F n u j
                * (aAB F n (F.dual j) * aAB F n i - aAB F n i * aAB F n (F.dual j)) from by
            noncomm_ring,
          hS, mul_smul_comm]
      rw [hB4, hc2, smul_add, smul_smul, smul_smul]
      norm_num
    rw [hFhat_eq, iota0_eN, hTilde_eN]
    change F0 F n u i
        + (1 / 2 : ℚ) • ∑ j : F.K, betaKappaAB F n u j * S0 F n (F.dual j) i
      = X0 F n (Sum.inr (Sum.inr (u, i)) : OspBasis F n)
        + kappaAB F n
          * iota0 F n (hTildeBasis (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
    have hX0 : X0 F n (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = F0 F n u i := rfl
    have hHt : hTildeBasis (Sum.inr (Sum.inr (u, i)) : OspBasis F n)
        = (1 / 2 : ℚ) • ∑ j : F.K, beta F n u j • Sof (F.dual j) i := rfl
    rw [hX0, hHt, iota0_smul_rat, iota0_sum]
    have hterm : ∀ j : F.K, iota0 F n (beta F n u j • Sof (F.dual j) i)
        = (algebraMap (Pmn F n) (R F n) (beta F n u j)) ᵍ⊗ₜ[ℚ] (1 : A0 F n) * S0 F n (F.dual j) i :=
            by
      intro j
      rw [iota0_smul, iota0_Sof]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    congr 1
    rw [mul_smul_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, kappaAB_mul_algebraMap_beta_tmul_one]

/-! ## `base_realization`

No step inspects the concrete shape of `F.K`, only `F.g`/`F.dual`/`gsign`/`parity`. `scomm` itself
and `X0`/`Xhat` etc. are already declared above; this section adds the remaining infrastructure
(`X0_Lof`, `X0_Fof`, `gsign_sq`, `scomm_antisymm`, the swap/adjoint-action lemmas, the six forward
kind-pairs `base_LL`/`base_LS`/`base_LF`/`base_SS`/`base_SF`/`base_FF`) then `base_realization`
itself. -/

theorem X0_Lof (F : FermionIndex) (n : ℕ) (u v : I n) : X0 F n (Lof u v) = L0 F n u v := by
  unfold Lof
  split
  · rfl
  · change L0 F n v u = L0 F n u v
    unfold L0
    rw [add_comm]

/-- `X0 (Fof u i) = F0 u i`, a free `rfl` -- `Fof` needs no sorting (`Basis.lean`), unlike
`Lof`, so no bridging work is needed. -/
theorem X0_Fof (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : X0 F n (Fof u i) = F0 F n u i := rfl

/-! ## `scomm`'s graded antisymmetry, and `gsign`'s square -/

theorem gsign_sq (p q : ZMod 2) : gsign p q * gsign p q = 1 := by
  unfold gsign
  split_ifs <;> norm_num

/-- `scomm` is itself graded-antisymmetric, the same law `bracket0Basis_super_skew`
gives `bracket0Basis`. Purely algebraic from `scomm`'s own definition, `gsign_sq` and
`gsign_symm` (`Coboundary.lean`) -- no dependence on `X,Y`'s kind. Used to get the three
reversed kinds (`SL`,`FL`,`FS`) of `base_realization` from the three forward kinds
(`LS`,`LF`,`SF`) for free. -/
theorem scomm_antisymm {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (x y : AB F n) :
    scomm Y X y x = -(gsign (parity X) (parity Y)) • scomm X Y x y := by
  unfold scomm
  rw [gsign_symm (parity Y) (parity X), smul_sub, smul_smul,
    show -gsign (parity X) (parity Y) * gsign (parity X) (parity Y) = -1 from by
      rw [neg_mul, gsign_sq]]
  rw [neg_one_smul, neg_smul, sub_neg_eq_add]
  abel

/-! ## Swap lemmas: moving one generator past another, additive form -/

theorem BuAB_swap (F : FermionIndex) (n : ℕ) (u v : I n) :
    BuAB F n u * BuAB F n v = BuAB F n v * BuAB F n u + J n u v • (1 : AB F n) := by
  have h : BuAB F n u * BuAB F n v - BuAB F n v * BuAB F n u - J n u v • (1 : AB F n) = 0 := by
    rw [BuAB_comm]; abel
  have h3 : BuAB F n u * BuAB F n v
      = (BuAB F n v * BuAB F n u + J n u v • (1 : AB F n))
        + (BuAB F n u * BuAB F n v - BuAB F n v * BuAB F n u - J n u v • (1 : AB F n)) := by
    abel
  rw [h3, h, add_zero]

theorem aAB_swap (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aAB F n i * aAB F n j = F.g i j • (1 : AB F n) - aAB F n j * aAB F n i := by
  have h : aAB F n i * aAB F n j + aAB F n j * aAB F n i - F.g i j • (1 : AB F n) = 0 := by
    rw [aAB_mul_add_swap]; abel
  have h3 : aAB F n i * aAB F n j
      = (F.g i j • (1 : AB F n) - aAB F n j * aAB F n i)
        + (aAB F n i * aAB F n j + aAB F n j * aAB F n i - F.g i j • (1 : AB F n)) := by
    abel
  rw [h3, h, add_zero]

/-! ## Primitive commutators: `L0`/`S0` against a single generator -/

theorem L0_comm_aAB (F : FermionIndex) (n : ℕ) (u v : I n) (k : F.K) :
    L0 F n u v * aAB F n k = aAB F n k * L0 F n u v := by
  unfold L0
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : BuAB F n u * BuAB F n v * aAB F n k = aAB F n k * (BuAB F n u * BuAB F n v) := by
    rw [mul_assoc, BuAB_comm_aAB, ← mul_assoc, BuAB_comm_aAB, mul_assoc]
  have h2 : BuAB F n v * BuAB F n u * aAB F n k = aAB F n k * (BuAB F n v * BuAB F n u) := by
    rw [mul_assoc, BuAB_comm_aAB, ← mul_assoc, BuAB_comm_aAB, mul_assoc]
  rw [add_mul, mul_add, h1, h2]

theorem S0_comm_BuAB (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) :
    S0 F n i j * BuAB F n w = BuAB F n w * S0 F n i j := by
  unfold S0
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : aAB F n i * aAB F n j * BuAB F n w = BuAB F n w * (aAB F n i * aAB F n j) := by
    rw [mul_assoc, ← BuAB_comm_aAB, ← mul_assoc, ← BuAB_comm_aAB, mul_assoc]
  have h2 : aAB F n j * aAB F n i * BuAB F n w = BuAB F n w * (aAB F n j * aAB F n i) := by
    rw [mul_assoc, ← BuAB_comm_aAB, ← mul_assoc, ← BuAB_comm_aAB, mul_assoc]
  rw [sub_mul, mul_sub, h1, h2]

/-- **Adjoint action, `L0` against a generator**: `⟦L⁰_{uv}, B_w⟧ = ½(J_{vw}B_u +
J_{uw}B_v)`, a degree-3 computation (not the full `L,L`
degree-4 computation). -/
theorem L0_comm_BuAB (F : FermionIndex) (n : ℕ) (u v w : I n) :
    L0 F n u v * BuAB F n w - BuAB F n w * L0 F n u v
      = (1 / 2 : ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v) := by
  have huvw : BuAB F n u * BuAB F n v * BuAB F n w - BuAB F n w * (BuAB F n u * BuAB F n v)
      = J n u w • BuAB F n v + J n v w • BuAB F n u := by
    have step1 : BuAB F n u * BuAB F n v * BuAB F n w
        = BuAB F n w * (BuAB F n u * BuAB F n v) + J n u w • BuAB F n v + J n v w • BuAB F n u := by
      rw [mul_assoc, BuAB_swap F n v w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swap F n u w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  have hvuw : BuAB F n v * BuAB F n u * BuAB F n w - BuAB F n w * (BuAB F n v * BuAB F n u)
      = J n v w • BuAB F n u + J n u w • BuAB F n v := by
    have step1 : BuAB F n v * BuAB F n u * BuAB F n w
        = BuAB F n w * (BuAB F n v * BuAB F n u) + J n v w • BuAB F n u + J n u w • BuAB F n v := by
      rw [mul_assoc, BuAB_swap F n u w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swap F n v w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  unfold L0
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [add_mul, mul_add]
  rw [show BuAB F n u * BuAB F n v * BuAB F n w + BuAB F n v * BuAB F n u * BuAB F n w
        - (BuAB F n w * (BuAB F n u * BuAB F n v) + BuAB F n w * (BuAB F n v * BuAB F n u))
      = (BuAB F n u * BuAB F n v * BuAB F n w - BuAB F n w * (BuAB F n u * BuAB F n v))
        + (BuAB F n v * BuAB F n u * BuAB F n w - BuAB F n w * (BuAB F n v * BuAB F n u))
      from by abel]
  rw [huvw, hvuw]
  module

/-- **Adjoint action, `S0` against a generator**: `⟦S⁰_{ij}, a_k⟧ = g_{jk}a_i −
g_{ik}a_j`, the fermionic (anticommuting) analogue of `L0_comm_BuAB`, using `a`'s
anticommutation (`aAB_swap`) at each swap instead of `B`'s plain commutation. -/
theorem S0_comm_aAB (F : FermionIndex) (n : ℕ) (i j k : F.K) :
    S0 F n i j * aAB F n k - aAB F n k * S0 F n i j
      = F.g j k • aAB F n i - F.g i k • aAB F n j := by
  have hikj : aAB F n i * aAB F n j * aAB F n k - aAB F n k * (aAB F n i * aAB F n j)
      = F.g j k • aAB F n i - F.g i k • aAB F n j := by
    have step1 : aAB F n i * aAB F n j * aAB F n k
        = aAB F n k * (aAB F n i * aAB F n j) + F.g j k • aAB F n i - F.g i k • aAB F n j := by
      rw [mul_assoc, aAB_swap F n j k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swap F n i k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  have hjik : aAB F n j * aAB F n i * aAB F n k - aAB F n k * (aAB F n j * aAB F n i)
      = F.g i k • aAB F n j - F.g j k • aAB F n i := by
    have step1 : aAB F n j * aAB F n i * aAB F n k
        = aAB F n k * (aAB F n j * aAB F n i) + F.g i k • aAB F n j - F.g j k • aAB F n i := by
      rw [mul_assoc, aAB_swap F n i k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swap F n j k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  unfold S0
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [sub_mul, mul_sub]
  rw [show aAB F n i * aAB F n j * aAB F n k - aAB F n j * aAB F n i * aAB F n k
        - (aAB F n k * (aAB F n i * aAB F n j) - aAB F n k * (aAB F n j * aAB F n i))
      = (aAB F n i * aAB F n j * aAB F n k - aAB F n k * (aAB F n i * aAB F n j))
        - (aAB F n j * aAB F n i * aAB F n k - aAB F n k * (aAB F n j * aAB F n i))
      from by abel]
  rw [hikj, hjik]
  module

/-! ## From a commutator identity to an explicit sum, generically -/

theorem eq_add_of_sub_eq' {R : Type*} [AddCommGroup R] {a b c : R} (h : a - b = c) :
    a = b + c := by
  have h3 : a = (b + c) + (a - b - c) := by abel
  have h2 : a - b - c = 0 := by rw [h]; abel
  rw [h3, h2, add_zero]

theorem iota0_sub (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    iota0 F n (x - y) = iota0 F n x - iota0 F n y := by
  rw [sub_eq_add_neg, iota0_add, iota0_neg, sub_eq_add_neg]

/-! ## Plain-equality forms of the adjoint-action lemmas, and `F0`/`4L0`/`2S0` identities -/

theorem L0_BuAB_eq (F : FermionIndex) (n : ℕ) (u v w : I n) :
    L0 F n u v * BuAB F n w
      = BuAB F n w * L0 F n u v
        + (1 / 2 : ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v) :=
  eq_add_of_sub_eq' (L0_comm_BuAB F n u v w)

theorem S0_aAB_eq (F : FermionIndex) (n : ℕ) (i j k : F.K) :
    S0 F n i j * aAB F n k
      = aAB F n k * S0 F n i j + (F.g j k • aAB F n i - F.g i k • aAB F n j) :=
  eq_add_of_sub_eq' (S0_comm_aAB F n i j k)

theorem F0_eq_half_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (u : I n) (k : F.K) :
    F0 F n u k = (1 / 2 : ℚ) • (BuAB F n u * aAB F n k) := by
  rw [BuAB_mul_aAB_eq_two_F0, smul_smul]
  norm_num

theorem BuAB_add_comm_eq_four_L0 (F : FermionIndex) (n : ℕ) (u v : I n) :
    BuAB F n u * BuAB F n v + BuAB F n v * BuAB F n u = (4 : ℚ) • L0 F n u v := by
  unfold L0
  rw [smul_smul]
  norm_num

theorem aAB_sub_comm_eq_two_S0 (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aAB F n i * aAB F n j - aAB F n j * aAB F n i = (2 : ℚ) • S0 F n i j := by
  unfold S0
  rw [smul_smul]
  norm_num

/-! ## `L0`/`S0` against a `B*a`, `B*B`, `a*a`-type product, additive form -/

theorem L0_comm_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (u v w : I n) (k : F.K) :
    L0 F n u v * (BuAB F n w * aAB F n k) - BuAB F n w * aAB F n k * L0 F n u v
      = ((1 / 2 : ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v)) * aAB F n k := by
  rw [← mul_assoc, L0_BuAB_eq, add_mul, mul_assoc, L0_comm_aAB, ← mul_assoc]
  abel

theorem S0_comm_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0 F n i j * (BuAB F n w * aAB F n k) - BuAB F n w * aAB F n k * S0 F n i j
      = BuAB F n w * (F.g j k • aAB F n i - F.g i k • aAB F n j) := by
  rw [← mul_assoc, S0_comm_BuAB, mul_assoc, S0_aAB_eq, mul_add, ← mul_assoc]
  abel

theorem L0_comm_BuAB_mul_BuAB (F : FermionIndex) (n : ℕ) (u v w z : I n) :
    L0 F n u v * (BuAB F n w * BuAB F n z) - BuAB F n w * BuAB F n z * L0 F n u v
      = ((1 / 2 : ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v)) * BuAB F n z
        + BuAB F n w * ((1 / 2 : ℚ) • (J n v z • BuAB F n u + J n u z • BuAB F n v)) := by
  rw [← mul_assoc, L0_BuAB_eq, add_mul, mul_assoc, L0_BuAB_eq, mul_add,
    mul_assoc (BuAB F n w) (BuAB F n z) (L0 F n u v)]
  abel

theorem S0_comm_aAB_mul_aAB (F : FermionIndex) (n : ℕ) (i j p q : F.K) :
    S0 F n i j * (aAB F n p * aAB F n q) - aAB F n p * aAB F n q * S0 F n i j
      = (F.g j p • aAB F n i - F.g i p • aAB F n j) * aAB F n q
        + aAB F n p * (F.g j q • aAB F n i - F.g i q • aAB F n j) := by
  rw [← mul_assoc, S0_aAB_eq, add_mul, mul_assoc, S0_aAB_eq, mul_add,
    mul_assoc (aAB F n p) (aAB F n q) (S0 F n i j)]
  abel

/-! ## The six forward kind-pairs of base realization -/

theorem base_LS (F : FermionIndex) (n : ℕ) (u v : I n) (i j : F.K) :
    L0 F n u v * S0 F n i j - S0 F n i j * L0 F n u v = 0 := by
  unfold S0
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul]
  have h1 : L0 F n u v * (aAB F n i * aAB F n j) = aAB F n i * aAB F n j * L0 F n u v := by
    rw [← mul_assoc, L0_comm_aAB, mul_assoc, L0_comm_aAB, ← mul_assoc]
  have h2 : L0 F n u v * (aAB F n j * aAB F n i) = aAB F n j * aAB F n i * L0 F n u v := by
    rw [← mul_assoc, L0_comm_aAB, mul_assoc, L0_comm_aAB, ← mul_assoc]
  rw [h1, h2, sub_self, smul_zero]

theorem base_LF (F : FermionIndex) (n : ℕ) (u v w : I n) (k : F.K) :
    L0 F n u v * F0 F n w k - F0 F n w k * L0 F n u v
      = (1 / 2 : ℚ) • (J n v w • F0 F n u k + J n u w • F0 F n v k) := by
  rw [F0_eq_half_BuAB_mul_aAB, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    L0_comm_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB]
  simp only [smul_mul_assoc, add_mul]
  module

theorem base_SF (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0 F n i j * F0 F n w k - F0 F n w k * S0 F n i j
      = F.g j k • F0 F n w i - F.g i k • F0 F n w j := by
  rw [F0_eq_half_BuAB_mul_aAB, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    S0_comm_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB]
  simp only [mul_sub, mul_smul_comm]
  module

theorem base_LL (F : FermionIndex) (n : ℕ) (u v w z : I n) :
    L0 F n u v * L0 F n w z - L0 F n w z * L0 F n u v
      = (1 / 2 : ℚ) • (J n v w • L0 F n u z + J n u w • L0 F n v z
          + J n v z • L0 F n u w + J n u z • L0 F n v w) := by
  have hLwz : L0 F n w z
      = (1 / 4 : ℚ) • (BuAB F n w * BuAB F n z + BuAB F n z * BuAB F n w) := rfl
  rw [hLwz, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_add, add_mul,
    show L0 F n u v * (BuAB F n w * BuAB F n z) + L0 F n u v * (BuAB F n z * BuAB F n w)
        - (BuAB F n w * BuAB F n z * L0 F n u v + BuAB F n z * BuAB F n w * L0 F n u v)
      = (L0 F n u v * (BuAB F n w * BuAB F n z) - BuAB F n w * BuAB F n z * L0 F n u v)
        + (L0 F n u v * (BuAB F n z * BuAB F n w) - BuAB F n z * BuAB F n w * L0 F n u v)
      from by abel,
    L0_comm_BuAB_mul_BuAB, L0_comm_BuAB_mul_BuAB]
  have hcomb :
      ((1/2:ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v)) * BuAB F n z
        + BuAB F n w * ((1/2:ℚ) • (J n v z • BuAB F n u + J n u z • BuAB F n v))
        + (((1/2:ℚ) • (J n v z • BuAB F n u + J n u z • BuAB F n v)) * BuAB F n w
          + BuAB F n z * ((1/2:ℚ) • (J n v w • BuAB F n u + J n u w • BuAB F n v)))
      = (1/2:ℚ) • (J n v w • (BuAB F n u * BuAB F n z + BuAB F n z * BuAB F n u)
          + J n u w • (BuAB F n v * BuAB F n z + BuAB F n z * BuAB F n v)
          + J n v z • (BuAB F n u * BuAB F n w + BuAB F n w * BuAB F n u)
          + J n u z • (BuAB F n v * BuAB F n w + BuAB F n w * BuAB F n v)) := by
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add]
    abel
  rw [hcomb, BuAB_add_comm_eq_four_L0, BuAB_add_comm_eq_four_L0,
    BuAB_add_comm_eq_four_L0, BuAB_add_comm_eq_four_L0]
  module

theorem base_SS (F : FermionIndex) (n : ℕ) (i j k l : F.K) :
    S0 F n i j * S0 F n k l - S0 F n k l * S0 F n i j
      = F.g j k • S0 F n i l - F.g i k • S0 F n j l
        - F.g j l • S0 F n i k + F.g i l • S0 F n j k := by
  have hSkl : S0 F n k l
      = (1 / 2 : ℚ) • (aAB F n k * aAB F n l - aAB F n l * aAB F n k) := rfl
  rw [hSkl, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul,
    show S0 F n i j * (aAB F n k * aAB F n l) - S0 F n i j * (aAB F n l * aAB F n k)
        - (aAB F n k * aAB F n l * S0 F n i j - aAB F n l * aAB F n k * S0 F n i j)
      = (S0 F n i j * (aAB F n k * aAB F n l) - aAB F n k * aAB F n l * S0 F n i j)
        - (S0 F n i j * (aAB F n l * aAB F n k) - aAB F n l * aAB F n k * S0 F n i j)
      from by abel,
    S0_comm_aAB_mul_aAB, S0_comm_aAB_mul_aAB]
  have hcomb :
      (F.g j k • aAB F n i - F.g i k • aAB F n j) * aAB F n l
        + aAB F n k * (F.g j l • aAB F n i - F.g i l • aAB F n j)
        - ((F.g j l • aAB F n i - F.g i l • aAB F n j) * aAB F n k
          + aAB F n l * (F.g j k • aAB F n i - F.g i k • aAB F n j))
      = F.g j k • (aAB F n i * aAB F n l - aAB F n l * aAB F n i)
        - F.g i k • (aAB F n j * aAB F n l - aAB F n l * aAB F n j)
        - F.g j l • (aAB F n i * aAB F n k - aAB F n k * aAB F n i)
        + F.g i l • (aAB F n j * aAB F n k - aAB F n k * aAB F n j) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [hcomb, aAB_sub_comm_eq_two_S0, aAB_sub_comm_eq_two_S0,
    aAB_sub_comm_eq_two_S0, aAB_sub_comm_eq_two_S0]
  module

/-- A pure-ring identity (no commutativity of `X,Y,P,Q` needed): `X*P+Y*Q` is the
"half-sum-plus-half-difference" combination `½[(X+Y)(P+Q)+(X-Y)(P-Q)]`. Used by
`base_FF` to turn `BuAB u*BuAB v` and `aAB i*aAB j`'s SEPARATE sum/difference facts
into the anticommutator `F0(u,i)*F0(v,j)+F0(v,j)*F0(u,i)` directly, without solving
for `BuAB u*BuAB v` or `aAB i*aAB j` individually. -/
theorem mul_add_mul_eq_half (F : FermionIndex) (n : ℕ) (X Y P Q : AB F n) :
    X * P + Y * Q = (1 / 2 : ℚ) • ((X + Y) * (P + Q) + (X - Y) * (P - Q)) := by
  have expand : (X + Y) * (P + Q) + (X - Y) * (P - Q)
      = (X * P + Y * Q) + (X * P + Y * Q) := by
    rw [add_mul, mul_add, mul_add, sub_mul, mul_sub, mul_sub]
    abel
  rw [expand, ← two_smul ℚ, smul_smul]
  norm_num

theorem base_FF (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) (v : I n) (j : F.K) :
    F0 F n u i * F0 F n v j + F0 F n v j * F0 F n u i
      = (1 / 4 : ℚ) • (J n u v • S0 F n i j) + (1 / 2 : ℚ) • (F.g i j • L0 F n u v) := by
  rw [F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmove1 : BuAB F n u * aAB F n i * (BuAB F n v * aAB F n j)
      = BuAB F n u * BuAB F n v * (aAB F n i * aAB F n j) := by
    rw [mul_assoc, ← mul_assoc (aAB F n i), ← BuAB_comm_aAB, mul_assoc, ← mul_assoc]
  have hmove2 : BuAB F n v * aAB F n j * (BuAB F n u * aAB F n i)
      = BuAB F n v * BuAB F n u * (aAB F n j * aAB F n i) := by
    rw [mul_assoc, ← mul_assoc (aAB F n j), ← BuAB_comm_aAB, mul_assoc, ← mul_assoc]
  rw [hmove1, hmove2,
    show (1 / 2 * (1 / 2) : ℚ)
          • (BuAB F n u * BuAB F n v * (aAB F n i * aAB F n j))
        + (1 / 2 * (1 / 2) : ℚ)
          • (BuAB F n v * BuAB F n u * (aAB F n j * aAB F n i))
      = (1 / 4 : ℚ) • (BuAB F n u * BuAB F n v * (aAB F n i * aAB F n j)
          + BuAB F n v * BuAB F n u * (aAB F n j * aAB F n i))
      from by rw [show (1 / 2 * (1 / 2) : ℚ) = 1 / 4 from by norm_num, ← smul_add],
    mul_add_mul_eq_half F n (BuAB F n u * BuAB F n v) (BuAB F n v * BuAB F n u)
      (aAB F n i * aAB F n j) (aAB F n j * aAB F n i),
    BuAB_add_comm_eq_four_L0, BuAB_comm, aAB_mul_add_swap, aAB_sub_comm_eq_two_S0]
  simp only [smul_smul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
  module

/-- **Lemma 3.2, in the realization**: the supercommutator of the base lifts equals `ι₀` of the
undeformed bracket. -/
theorem base_realization (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (X0 F n X) (X0 F n Y) = iota0 F n (bracket0Basis X Y) := by
  match X, Y with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    change L0 F n u v * L0 F n w z - gsign 0 0 • (L0 F n w z * L0 F n u v)
        = iota0 F n (bracketLL u v w z)
    rw [gsign_00, one_smul, base_LL]
    unfold bracketLL
    rw [iota0_add, iota0_add, iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_smul_rat,
      iota0_smul_rat, iota0_eN, iota0_eN, iota0_eN, iota0_eN, X0_Lof, X0_Lof, X0_Lof, X0_Lof,
      smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  | .inl ⟨(u, v), _⟩, .inr (.inl ⟨(i, j), _⟩) =>
    change L0 F n u v * S0 F n i j - gsign 0 0 • (S0 F n i j * L0 F n u v) = iota0 F n (0 : OspMod F
        n)
    rw [gsign_00, one_smul, base_LS, iota0_zero]
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) =>
    change L0 F n u v * F0 F n w i - gsign 0 1 • (F0 F n w i * L0 F n u v)
        = iota0 F n (bracketLF u v w i)
    rw [gsign_01, one_smul, base_LF]
    unfold bracketLF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof,
      smul_add, smul_smul, smul_smul]
  | .inr (.inl ⟨(i, j), _⟩), .inl ⟨(u, v), _⟩ =>
    change S0 F n i j * L0 F n u v - gsign 0 0 • (L0 F n u v * S0 F n i j) = iota0 F n (0 : OspMod F
        n)
    rw [gsign_00, one_smul,
      show S0 F n i j * L0 F n u v - L0 F n u v * S0 F n i j
          = -(L0 F n u v * S0 F n i j - S0 F n i j * L0 F n u v) from by abel,
      base_LS, neg_zero, iota0_zero]
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) =>
    change S0 F n i j * S0 F n k l - gsign 0 0 • (S0 F n k l * S0 F n i j)
        = iota0 F n (bracketSS i j k l)
    rw [gsign_00, one_smul, base_SS]
    unfold bracketSS
    rw [iota0_add, iota0_sub, iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_smul_rat,
      iota0_smul_rat, iota0_Sof, iota0_Sof, iota0_Sof, iota0_Sof]
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) =>
    change S0 F n j k * F0 F n w i - gsign 0 1 • (F0 F n w i * S0 F n j k)
        = iota0 F n (bracketSF j k w i)
    rw [gsign_01, one_smul, base_SF]
    unfold bracketSF
    rw [iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof]
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ =>
    change F0 F n w i * L0 F n u v - gsign 1 0 • (L0 F n u v * F0 F n w i)
        = iota0 F n (-bracketLF u v w i)
    rw [gsign_10, one_smul,
      show F0 F n w i * L0 F n u v - L0 F n u v * F0 F n w i
          = -(L0 F n u v * F0 F n w i - F0 F n w i * L0 F n u v) from by abel,
      base_LF, iota0_neg]
    unfold bracketLF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof,
      smul_add, smul_smul, smul_smul]
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) =>
    change F0 F n w i * S0 F n j k - gsign 1 0 • (S0 F n j k * F0 F n w i)
        = iota0 F n (-bracketSF j k w i)
    rw [gsign_10, one_smul,
      show F0 F n w i * S0 F n j k - S0 F n j k * F0 F n w i
          = -(S0 F n j k * F0 F n w i - F0 F n w i * S0 F n j k) from by abel,
      base_SF, iota0_neg]
    unfold bracketSF
    rw [iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof]
  | .inr (.inr (u, i)), .inr (.inr (v, j)) =>
    change F0 F n u i * F0 F n v j - gsign 1 1 • (F0 F n v j * F0 F n u i)
        = iota0 F n (bracketFF u i v j)
    rw [gsign_11, neg_smul, one_smul, sub_neg_eq_add, base_FF]
    unfold bracketFF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_Sof, iota0_eN, X0_Lof, smul_smul,
      smul_smul]

/-! ## `recovery`/`recovery_delta`

No step inspects the concrete shape of `F.K`. Adds the `κ`-graded-commutation infrastructure
(`kappaAB_comm_X0`, `coefAB` and its commutation, `kappaAB_comm_iota0_homog`), the
linearized `base_realization` (`iota0_bracket0_eN_*_homog`), and the abstract
`(P+κp)(Q+κq)` expansion (`expand_kappa_product`), then `recovery` and
`recovery_delta` themselves. -/

theorem gsign_one_add (d1 d2 : ZMod 2) : gsign 1 (d1 + d2) = gsign 1 d1 * gsign 1 d2 := by
  have h : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases h d1 with rfl | rfl <;> rcases h d2 with rfl | rfl <;>
    simp only [show (0 : ZMod 2) + 0 = 0 from rfl, show (0 : ZMod 2) + 1 = 1 from rfl,
      show (1 : ZMod 2) + 0 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl] <;>
    norm_num [gsign_00, gsign_01, gsign_10, gsign_11]

/-- `κ² = 0`, lifted to `AB F n`. -/
theorem kappaAB_sq (F : FermionIndex) (n : ℕ) : kappaAB F n * kappaAB F n = 0 := by
  unfold kappaAB
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (kappa F n) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    (⟨kappa F n, kappa_mem_RGrading_one F n⟩ : RGradingQ F n 1) (1 : A0 F n)]
  simp only [zero_mul, uzpow_zero, one_smul, one_mul]
  rw [kappa_sq]
  exact tmul_zero_left F n 1

/-- `κ` graded-commutes with `B_u`'s embedding, sign `gsign 1 0 = 1` (plain commutation,
`B_u` has `AB`-degree `0`). -/
theorem kappaAB_comm_BuAB (F : FermionIndex) (n : ℕ) (u : I n) :
    kappaAB F n * BuAB F n u = gsign 1 0 • (BuAB F n u * kappaAB F n) := by
  rw [gsign_10, one_smul]
  unfold kappaAB BuAB
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (kappa F n) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (Bu0 F n u),
    GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (1 : R F n) (⟨Bu0 F n u, Bu0_mem_A0Grading_zero F n u⟩ : A0Grading F n 0)
    (⟨kappa F n, kappa_mem_RGrading_one F n⟩ : RGradingQ F n 1) (1 : A0 F n)]
  simp only [mul_one, one_mul, uzpow_zero, one_smul]

/-- `κ` graded-anticommutes with `a_i`'s embedding, sign `gsign 1 1 = -1` (`a_i` has
`AB`-degree `1`). -/
theorem kappaAB_comm_aAB (F : FermionIndex) (n : ℕ) (i : F.K) :
    kappaAB F n * aAB F n i = gsign 1 1 • (aAB F n i * kappaAB F n) := by
  rw [gsign_11]
  unfold kappaAB aAB
  rw [GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (kappa F n) (⟨1, SetLike.one_mem_graded (A0Grading F n)⟩ : A0Grading F n 0)
    (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (aA0 F n i),
    GradedTensorProduct.tmul_coe_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
    (1 : R F n) (⟨aA0 F n i, aA0_mem_A0Grading_one F n i⟩ : A0Grading F n 1)
    (⟨kappa F n, kappa_mem_RGrading_one F n⟩ : RGradingQ F n 1) (1 : A0 F n)]
  simp

/-- The graded-commutation rule against `kappaAB` is multiplicative: if `x` and `y` each
graded-commute with `kappaAB` at degrees `dx`/`dy`, so does `x*y`, at degree `dx+dy`. -/
theorem kappaAB_comm_mul {F : FermionIndex} {n : ℕ} (x y : AB F n) (dx dy : ZMod 2)
    (hx : kappaAB F n * x = gsign 1 dx • (x * kappaAB F n))
    (hy : kappaAB F n * y = gsign 1 dy • (y * kappaAB F n)) :
    kappaAB F n * (x * y) = gsign 1 (dx + dy) • (x * y * kappaAB F n) := by
  rw [gsign_one_add, ← mul_assoc, hx, smul_mul_assoc, mul_assoc, hy, mul_smul_comm, smul_smul,
    mul_assoc]

/-- Same, for a sum of two terms at the same degree. -/
theorem kappaAB_comm_add {F : FermionIndex} {n : ℕ} (x y : AB F n) (d : ZMod 2)
    (hx : kappaAB F n * x = gsign 1 d • (x * kappaAB F n))
    (hy : kappaAB F n * y = gsign 1 d • (y * kappaAB F n)) :
    kappaAB F n * (x + y) = gsign 1 d • ((x + y) * kappaAB F n) := by
  rw [mul_add, hx, hy, add_mul, smul_add]

/-- Same, for a `ℚ`-scalar multiple. -/
theorem kappaAB_comm_smul {F : FermionIndex} {n : ℕ} (c : ℚ) (x : AB F n) (d : ZMod 2)
    (hx : kappaAB F n * x = gsign 1 d • (x * kappaAB F n)) :
    kappaAB F n * (c • x) = gsign 1 d • ((c • x) * kappaAB F n) := by
  rw [mul_smul_comm, hx, smul_comm, ← smul_mul_assoc]

/-- `X0 X` graded-commutes with `κ`, at
degree `parity X` -- proved by cases on `X`'s kind, unfolding `L0`/`S0`/`F0` into
`BuAB`/`aAB` products and using multiplicativity. -/
theorem kappaAB_comm_X0 (F : FermionIndex) (n : ℕ) (X : OspBasis F n) :
    kappaAB F n * X0 F n X = gsign 1 (parity X) • (X0 F n X * kappaAB F n) := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    change kappaAB F n * L0 F n u v = gsign 1 0 • (L0 F n u v * kappaAB F n)
    unfold L0
    refine kappaAB_comm_smul _ _ 0 ?_
    have h1 := kappaAB_comm_mul (BuAB F n u) (BuAB F n v) 0 0
      (kappaAB_comm_BuAB F n u) (kappaAB_comm_BuAB F n v)
    have h2 := kappaAB_comm_mul (BuAB F n v) (BuAB F n u) 0 0
      (kappaAB_comm_BuAB F n v) (kappaAB_comm_BuAB F n u)
    simpa using kappaAB_comm_add _ _ 0 h1 h2
  | .inr (.inl ⟨(i, j), _⟩) =>
    change kappaAB F n * S0 F n i j = gsign 1 0 • (S0 F n i j * kappaAB F n)
    unfold S0
    refine kappaAB_comm_smul _ _ 0 ?_
    have h1 := kappaAB_comm_mul (aAB F n i) (aAB F n j) 1 1
      (kappaAB_comm_aAB F n i) (kappaAB_comm_aAB F n j)
    have h2 := kappaAB_comm_mul (aAB F n j) (aAB F n i) 1 1
      (kappaAB_comm_aAB F n j) (kappaAB_comm_aAB F n i)
    have h2' : kappaAB F n * (-(aAB F n j * aAB F n i))
        = gsign 1 (1 + 1) • (-(aAB F n j * aAB F n i) * kappaAB F n) := by
      rw [mul_neg, h2, neg_mul, smul_neg]
    have h3 := kappaAB_comm_add _ _ (1 + 1) h1 h2'
    have e : (1 + 1 : ZMod 2) = 0 := by decide
    rw [e, ← sub_eq_add_neg] at h3
    exact h3
  | .inr (.inr (u, i)) =>
    change kappaAB F n * F0 F n u i = gsign 1 1 • (F0 F n u i * kappaAB F n)
    unfold F0
    refine kappaAB_comm_smul _ _ 1 ?_
    have h1 := kappaAB_comm_mul (aAB F n i) (BuAB F n u) 1 0
      (kappaAB_comm_aAB F n i) (kappaAB_comm_BuAB F n u)
    have h2 := kappaAB_comm_mul (BuAB F n u) (aAB F n i) 0 1
      (kappaAB_comm_BuAB F n u) (kappaAB_comm_aAB F n i)
    simpa using kappaAB_comm_add _ _ 1 h1 h2

/-- `c ↦ algebraMap c ᵍ⊗ₜ 1`, `iota0`'s own coefficient embedding, named for reuse. -/
noncomputable def coefAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) : AB F n :=
  (algebraMap (Pmn F n) (R F n) c) ᵍ⊗ₜ[ℚ] (1 : A0 F n)

theorem iota0_smul_coefAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) (x : OspMod F n) :
    iota0 F n (c • x) = coefAB F n c * iota0 F n x := iota0_smul F n c x

theorem iota0_smul_eN_coefAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) (X : OspBasis F n) :
    iota0 F n (c • eN X) = coefAB F n c * X0 F n X := iota0_smul_eN F n c X

theorem coefAB_zero (F : FermionIndex) (n : ℕ) : coefAB F n 0 = 0 := by
  unfold coefAB; rw [map_zero]; exact tmul_zero_left F n 1

theorem coefAB_comm_BuAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) (u : I n) :
    coefAB F n c * BuAB F n u = BuAB F n u * coefAB F n c := by
  unfold coefAB BuAB
  have hmem : algebraMap (Pmn F n) (R F n) c ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  rw [GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (algebraMap (Pmn F n) (R F n) c)
      (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (Bu0 F n u),
    GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨Bu0 F n u, Bu0_mem_A0Grading_zero F n u⟩ : A0Grading F n 0)
      (⟨algebraMap (Pmn F n) (R F n) c, hmem⟩ : RGradingQ F n 0) (1 : A0 F n)]
  simp only [mul_one, one_mul]

theorem coefAB_comm_aAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) (i : F.K) :
    coefAB F n c * aAB F n i = aAB F n i * coefAB F n c := by
  unfold coefAB aAB
  have hmem : algebraMap (Pmn F n) (R F n) c ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  rw [GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (algebraMap (Pmn F n) (R F n) c)
      (⟨1, SetLike.one_mem_graded (RGradingQ F n)⟩ : RGradingQ F n 0) (aA0 F n i),
    GradedTensorProduct.tmul_coe_mul_zero_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (1 : R F n) (⟨aA0 F n i, aA0_mem_A0Grading_one F n i⟩ : A0Grading F n 1)
      (⟨algebraMap (Pmn F n) (R F n) c, hmem⟩ : RGradingQ F n 0) (1 : A0 F n)]
  simp only [mul_one, one_mul]

theorem coefAB_comm_mul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : AB F n)
    (hx : coefAB F n c * x = x * coefAB F n c) (hy : coefAB F n c * y = y * coefAB F n c) :
    coefAB F n c * (x * y) = (x * y) * coefAB F n c := by
  rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

theorem coefAB_comm_add {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : AB F n)
    (hx : coefAB F n c * x = x * coefAB F n c) (hy : coefAB F n c * y = y * coefAB F n c) :
    coefAB F n c * (x + y) = (x + y) * coefAB F n c := by
  rw [mul_add, hx, hy, add_mul]

theorem coefAB_comm_neg {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : AB F n)
    (hx : coefAB F n c * x = x * coefAB F n c) :
    coefAB F n c * (-x) = (-x) * coefAB F n c := by
  rw [mul_neg, hx, neg_mul]

theorem coefAB_comm_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (r : ℚ) (x : AB F n)
    (hx : coefAB F n c * x = x * coefAB F n c) :
    coefAB F n c * (r • x) = (r • x) * coefAB F n c := by
  rw [mul_smul_comm, hx, smul_mul_assoc]

/-- `coefAB` commutes plainly with every `X0`-built element -- the `coefAB` analogue of
`kappaAB_comm_X0`, without any sign bookkeeping (a coefficient's own degree is always
`0`). -/
theorem coefAB_comm_X0 (F : FermionIndex) (n : ℕ) (c : Pmn F n) (X : OspBasis F n) :
    coefAB F n c * X0 F n X = X0 F n X * coefAB F n c := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    change coefAB F n c * L0 F n u v = L0 F n u v * coefAB F n c
    unfold L0
    exact coefAB_comm_smul c _ _
      (coefAB_comm_add c _ _
        (coefAB_comm_mul c _ _ (coefAB_comm_BuAB F n c u) (coefAB_comm_BuAB F n c v))
        (coefAB_comm_mul c _ _ (coefAB_comm_BuAB F n c v) (coefAB_comm_BuAB F n c u)))
  | .inr (.inl ⟨(i, j), _⟩) =>
    change coefAB F n c * S0 F n i j = S0 F n i j * coefAB F n c
    unfold S0
    refine coefAB_comm_smul c _ _ ?_
    rw [sub_eq_add_neg]
    exact coefAB_comm_add c _ _
      (coefAB_comm_mul c _ _ (coefAB_comm_aAB F n c i) (coefAB_comm_aAB F n c j))
      (coefAB_comm_neg c _
        (coefAB_comm_mul c _ _ (coefAB_comm_aAB F n c j) (coefAB_comm_aAB F n c i)))
  | .inr (.inr (u, i)) =>
    change coefAB F n c * F0 F n u i = F0 F n u i * coefAB F n c
    unfold F0
    exact coefAB_comm_smul c _ _
      (coefAB_comm_add c _ _
        (coefAB_comm_mul c _ _ (coefAB_comm_aAB F n c i) (coefAB_comm_BuAB F n c u))
        (coefAB_comm_mul c _ _ (coefAB_comm_BuAB F n c u) (coefAB_comm_aAB F n c i)))

/-- `kappaAB` commutes plainly with `coefAB` (both are `R`-degree `0`/central-`Pmn`-image
elements) -- the general-coefficient form of `kappaAB_mul_algebraMap_beta_tmul_one`
(above), which is its `c = beta a b` special case (there landing on
`betaKappaAB` instead of a bare commutation). -/
theorem kappaAB_comm_coefAB (F : FermionIndex) (n : ℕ) (c : Pmn F n) :
    kappaAB F n * coefAB F n c = coefAB F n c * kappaAB F n := by
  unfold kappaAB coefAB
  have hmem : algebraMap (Pmn F n) (R F n) c ∈ RGrading F n 0 :=
    SetLike.algebraMap_mem_graded _ _
  rw [GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (kappa F n) (⟨algebraMap (Pmn F n) (R F n) c, hmem⟩ : RGradingQ F n 0) (1 : A0 F n),
    GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
      (algebraMap (Pmn F n) (R F n) c) (⟨kappa F n, kappa_mem_RGrading_one F n⟩ : RGradingQ F n 1)
      (1 : A0 F n)]
  congr 1
  exact (Algebra.commutes c (kappa F n)).symm

/-- `kappaAB`'s graded commutation, lifted from `X0`-built elements (`kappaAB_comm_X0`) to
`iota0` of an arbitrary *parity-homogeneous* `OspMod` element -- one whose only nonzero
basis-components sit at a single fixed parity `p`, the generality `hTildeBasis X`
(parity `parity X + 1`, `hTildeBasis_apply_eq_zero_of_parity_ne`) needs. -/
theorem kappaAB_comm_iota0_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → parity Z = p) :
    kappaAB F n * iota0 F n x = gsign 1 p • (iota0 F n x * kappaAB F n) := by
  have hterm : ∀ i : OspBasis F n,
      kappaAB F n * (coefAB F n (x i) * X0 F n i)
        = gsign 1 p • (coefAB F n (x i) * X0 F n i * kappaAB F n) := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi, coefAB_zero]
    · have hpi : parity i = p := hx i hxi
      calc kappaAB F n * (coefAB F n (x i) * X0 F n i)
          = kappaAB F n * coefAB F n (x i) * X0 F n i := by rw [mul_assoc]
        _ = coefAB F n (x i) * kappaAB F n * X0 F n i := by rw [kappaAB_comm_coefAB]
        _ = coefAB F n (x i) * (kappaAB F n * X0 F n i) := by rw [mul_assoc]
        _ = coefAB F n (x i) * (gsign 1 (parity i) • (X0 F n i * kappaAB F n)) := by
              rw [kappaAB_comm_X0]
        _ = coefAB F n (x i) * (gsign 1 p • (X0 F n i * kappaAB F n)) := by rw [hpi]
        _ = gsign 1 p • (coefAB F n (x i) * (X0 F n i * kappaAB F n)) := by rw [mul_smul_comm]
        _ = gsign 1 p • (coefAB F n (x i) * X0 F n i * kappaAB F n) := by rw [mul_assoc]
  change kappaAB F n * (∑ i : OspBasis F n, coefAB F n (x i) * X0 F n i)
      = gsign 1 p • ((∑ i : OspBasis F n, coefAB F n (x i) * X0 F n i) * kappaAB F n)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

theorem gsign_shift_left (p q : ZMod 2) : gsign (p + 1) q = gsign p q * gsign 1 q := by
  rw [gsign_symm (p + 1) q, gsign_shift_right q p, gsign_symm q p, gsign_symm q 1]

/-- `base_realization`, linearized on the right: `bracket0 x (eN Y)` against a
parity-`p`-homogeneous `x`, pushed through `iota0`. Reduces to `base_realization` termwise
via `bracket0_eN_right` and `iota0`'s own `Pmn`-linearity, moving `coefAB` across `X0 F n Y`
with `coefAB_comm_X0`. -/
theorem iota0_bracket0_eN_right_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → parity Z = p) (Y : OspBasis F n) :
    iota0 F n (bracket0 x (eN Y))
      = iota0 F n x * X0 F n Y - gsign p (parity Y) • (X0 F n Y * iota0 F n x) := by
  rw [bracket0_eN_right, iota0_sum]
  have hterm : ∀ i : OspBasis F n, iota0 F n (x i • bracket0Basis i Y)
      = coefAB F n (x i) * X0 F n i * X0 F n Y
        - gsign p (parity Y) • (X0 F n Y * (coefAB F n (x i) * X0 F n i)) := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi, coefAB_zero, iota0_zero]
    · have hpi : parity i = p := hx i hxi
      have hbr := base_realization F n i Y
      unfold scomm at hbr
      rw [iota0_smul_coefAB, ← hbr, hpi, mul_sub, mul_smul_comm, ← mul_assoc,
        show coefAB F n (x i) * (X0 F n Y * X0 F n i) = X0 F n Y * (coefAB F n (x i) * X0 F n i)
          from by rw [← mul_assoc, coefAB_comm_X0, mul_assoc]]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_mul]; rfl
  · have : (∑ i : OspBasis F n, X0 F n Y * (coefAB F n (x i) * X0 F n i))
        = X0 F n Y * iota0 F n x := by rw [← Finset.mul_sum]; rfl
    rw [← Finset.smul_sum, this]

/-- Mirror of `iota0_bracket0_eN_right_homog`, with the basis vector on the left. -/
theorem iota0_bracket0_eN_left_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (y : OspMod F n)
    (hy : ∀ Z : OspBasis F n, y Z ≠ 0 → parity Z = p) (X : OspBasis F n) :
    iota0 F n (bracket0 (eN X) y)
      = X0 F n X * iota0 F n y - gsign (parity X) p • (iota0 F n y * X0 F n X) := by
  rw [bracket0_eN_left, iota0_sum]
  have hterm : ∀ j : OspBasis F n, iota0 F n (y j • bracket0Basis X j)
      = X0 F n X * (coefAB F n (y j) * X0 F n j)
        - gsign (parity X) p • (coefAB F n (y j) * X0 F n j * X0 F n X) := by
    intro j
    by_cases hyj : y j = 0
    · simp [hyj, coefAB_zero, iota0_zero]
    · have hpj : parity j = p := hy j hyj
      have hbr := base_realization F n X j
      unfold scomm at hbr
      rw [iota0_smul_coefAB, ← hbr, hpj, mul_sub, mul_smul_comm,
        show coefAB F n (y j) * (X0 F n X * X0 F n j) = X0 F n X * (coefAB F n (y j) * X0 F n j)
          from by rw [← mul_assoc, coefAB_comm_X0, mul_assoc],
        ← mul_assoc (coefAB F n (y j)) (X0 F n j) (X0 F n X)]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.mul_sum]; rfl
  · have : (∑ j : OspBasis F n, coefAB F n (y j) * X0 F n j * X0 F n X)
        = iota0 F n y * X0 F n X := by rw [← Finset.sum_mul]; rfl
    rw [← Finset.smul_sum, this]

/-- The pure-algebra identity underlying both cross-products in `recovery`'s expansion of
`scomm` on `Xhat X = X0 X + κ·(...)`: given `κ` graded-commutes with `P` at sign `α` and
with `p` at sign `σ` (both self-inverse, as every `gsign` value is) and `κ² = 0`, the
`(κp)(κq)` term vanishes and `P(κq)` picks up the sign `α` moving `κ` to the front. -/
theorem expand_kappa_product {F : FermionIndex} {n : ℕ} (P Q p q : AB F n) (α σ : ℚ)
    (hP : kappaAB F n * P = α • (P * kappaAB F n))
    (hp : kappaAB F n * p = σ • (p * kappaAB F n))
    (hα : α * α = 1) (hσ : σ * σ = 1) :
    (P + kappaAB F n * p) * (Q + kappaAB F n * q)
      = P * Q + kappaAB F n * (α • (P * q) + p * Q) := by
  have hPκ : P * kappaAB F n = α • (kappaAB F n * P) := by rw [hP, smul_smul, hα, one_smul]
  have hpκ : p * kappaAB F n = σ • (kappaAB F n * p) := by rw [hp, smul_smul, hσ, one_smul]
  have hκ2 : kappaAB F n * kappaAB F n = 0 := kappaAB_sq F n
  have expand : (P + kappaAB F n * p) * (Q + kappaAB F n * q)
      = P * Q + P * (kappaAB F n * q) + (kappaAB F n * p) * Q
        + (kappaAB F n * p) * (kappaAB F n * q) := by noncomm_ring
  have h1 : P * (kappaAB F n * q) = α • (kappaAB F n * (P * q)) := by
    rw [← mul_assoc, hPκ, smul_mul_assoc, mul_assoc]
  have h2 : (kappaAB F n * p) * Q = kappaAB F n * (p * Q) := by rw [mul_assoc]
  have h3 : (kappaAB F n * p) * (kappaAB F n * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p, hpκ, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
      hκ2, zero_mul, zero_mul, smul_zero]
  rw [expand, h1, h2, h3, add_zero, ← mul_smul_comm, add_assoc, ← mul_add]

/-- **Recovery** (paper Theorem 4.2, in the realization): for all basis elements
`X Y`, the supercommutator of the *deformed* lifts equals `ι_β` of the undeformed bracket
plus `κ·ι₀` of the explicit `Γ` rule. Proved by expanding `Xhat X = X0 X + κ·ι₀(h̃X)`
(`Xhat_eq_iota0_add`) on both sides of `scomm` (`expand_kappa_product`, twice), reducing
the base term to `base_realization`, and matching the `κ`-coefficient against
`GammaBasis = deltaBasis hTilde` (`Gamma_eq_delta_hTilde_basis`) via the linearized
`base_realization` (`iota0_bracket0_eN_*_homog`) and the `gsign` shift identities. -/
theorem recovery (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (Xhat F n X) (Xhat F n Y)
      = iotaB F n (bracket0Basis X Y) + kappaAB F n * iota0 F n (GammaBasis X Y) := by
  have hXeq : Xhat F n X = X0 F n X + kappaAB F n * iota0 F n (hTildeBasis X) := by
    rw [Xhat_eq_iota0_add, iota0_eN, hTilde_eN]
  have hYeq : Xhat F n Y = X0 F n Y + kappaAB F n * iota0 F n (hTildeBasis Y) := by
    rw [Xhat_eq_iota0_add, iota0_eN, hTilde_eN]
  have hXhom : ∀ Z : OspBasis F n, hTildeBasis X Z ≠ 0 → parity Z = parity X + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTildeBasis_apply_eq_zero_of_parity_ne X Z hne)
  have hYhom : ∀ Z : OspBasis F n, hTildeBasis Y Z ≠ 0 → parity Z = parity Y + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTildeBasis_apply_eq_zero_of_parity_ne Y Z hne)
  set A := X0 F n X
  set B := X0 F n Y
  set a := iota0 F n (hTildeBasis X) with ha
  set b := iota0 F n (hTildeBasis Y) with hb
  have hκA : kappaAB F n * A = gsign 1 (parity X) • (A * kappaAB F n) := kappaAB_comm_X0 F n X
  have hκB : kappaAB F n * B = gsign 1 (parity Y) • (B * kappaAB F n) := kappaAB_comm_X0 F n Y
  have hκa : kappaAB F n * a = gsign 1 (parity X + 1) • (a * kappaAB F n) :=
    kappaAB_comm_iota0_homog (parity X + 1) (hTildeBasis X) hXhom
  have hκb : kappaAB F n * b = gsign 1 (parity Y + 1) • (b * kappaAB F n) :=
    kappaAB_comm_iota0_homog (parity Y + 1) (hTildeBasis Y) hYhom
  have hprod1 : (A + kappaAB F n * a) * (B + kappaAB F n * b)
      = A * B + kappaAB F n * (gsign 1 (parity X) • (A * b) + a * B) :=
    expand_kappa_product A B a b (gsign 1 (parity X)) (gsign 1 (parity X + 1)) hκA hκa
      (gsign_sq 1 (parity X)) (gsign_sq 1 (parity X + 1))
  have hprod2 : (B + kappaAB F n * b) * (A + kappaAB F n * a)
      = B * A + kappaAB F n * (gsign 1 (parity Y) • (B * a) + b * A) :=
    expand_kappa_product B A b a (gsign 1 (parity Y)) (gsign 1 (parity Y + 1)) hκB hκb
      (gsign_sq 1 (parity Y)) (gsign_sq 1 (parity Y + 1))
  have hbase : A * B - gsign (parity X) (parity Y) • (B * A) = iota0 F n (bracket0Basis X Y) := by
    have := base_realization F n X Y
    unfold scomm at this
    exact this
  have hΓ : iota0 F n (hTilde (bracket0Basis X Y)) + iota0 F n (GammaBasis X Y)
      = iota0 F n (bracket0 (hTildeBasis X) (eN Y))
        + gsign (parity X) 1 • iota0 F n (bracket0 (eN X) (hTildeBasis Y)) := by
    rw [Gamma_eq_delta_hTilde_basis]
    unfold deltaBasis
    simp only [hTilde_eN]
    rw [bracket0_eN_eN, iota0_sub, iota0_add, iota0_smul_rat]
    abel
  have hRHSa : iota0 F n (bracket0 (hTildeBasis X) (eN Y))
      = a * B - gsign (parity X + 1) (parity Y) • (B * a) :=
    iota0_bracket0_eN_right_homog (parity X + 1) (hTildeBasis X) hXhom Y
  have hRHSb : iota0 F n (bracket0 (eN X) (hTildeBasis Y))
      = A * b - gsign (parity X) (parity Y + 1) • (b * A) :=
    iota0_bracket0_eN_left_homog (parity Y + 1) (hTildeBasis Y) hYhom X
  have e1 : gsign (parity X) (parity Y) * gsign 1 (parity Y) = gsign (parity X + 1) (parity Y) :=
    (gsign_shift_left (parity X) (parity Y)).symm
  have e2 : gsign (parity X) 1 * gsign (parity X) (parity Y + 1) = gsign (parity X) (parity Y) := by
    rw [gsign_mul_shift_right (parity Y) (parity X), gsign_symm (parity Y) (parity X)]
  have e3 : gsign 1 (parity X) = gsign (parity X) 1 := gsign_symm 1 (parity X)
  have hkey : gsign 1 (parity X) • (A * b) + a * B
      - gsign (parity X) (parity Y) • (gsign 1 (parity Y) • (B * a) + b * A)
      = iota0 F n (hTilde (bracket0Basis X Y)) + iota0 F n (GammaBasis X Y) := by
    rw [hΓ, hRHSa, hRHSb]
    simp only [smul_sub, smul_add, smul_smul, e1, e2, e3]
    module
  unfold scomm
  rw [hXeq, hYeq, hprod1, hprod2]
  unfold iotaB
  have hregroup : A * B + kappaAB F n * (gsign 1 (parity X) • (A * b) + a * B)
        - gsign (parity X) (parity Y) • (B * A
          + kappaAB F n * (gsign 1 (parity Y) • (B * a) + b * A))
      = (A * B - gsign (parity X) (parity Y) • (B * A))
        + (kappaAB F n * (gsign 1 (parity X) • (A * b) + a * B)
          - kappaAB F n * (gsign (parity X) (parity Y) • (gsign 1 (parity Y) • (B * a) + b * A)))
      := by
    rw [smul_add,
      show gsign (parity X) (parity Y)
            • (kappaAB F n * (gsign 1 (parity Y) • (B * a) + b * A))
          = kappaAB F n * (gsign (parity X) (parity Y)
              • (gsign 1 (parity Y) • (B * a) + b * A))
        from (mul_smul_comm _ _ _).symm]
    abel
  rw [hregroup, ← mul_sub, hbase, hkey, mul_add]
  abel

/-- `recovery` with `GammaBasis` replaced by `deltaBasis hTilde`
via `Gamma_eq_delta_hTilde_basis`. -/
theorem recovery_delta (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (Xhat F n X) (Xhat F n Y)
      = iotaB F n (bracket0Basis X Y) + kappaAB F n * iota0 F n (deltaBasis hTilde X Y) := by
  rw [← Gamma_eq_delta_hTilde_basis]
  exact recovery F n X Y

-- `iota0_injective` is proved in `OspN/SourceIndependence.lean`.

-- `kappa_iota0_injective`, `recovery_unique`, `recovery_unique_delta` are proved in
-- `OspN/SourceUniqueness.lean`.


end OspN
end OspOddDeformations
