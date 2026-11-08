import OspOddDeformations.OspN.SourceIndependence

/-!
# κ-cancellation and uniqueness, for every `osp(N|2n)`

Proves `κ-cancellation` (`kappa_iota0_injective`: `c ↦ κ · ι₀(c)` injective on `OspMod F n`) and the
uniqueness theorem (paper Theorem 4.3, in the realization; `recovery_unique`: the coefficient `c` in
`recovery`'s own identity is forced to be `GammaBasis X Y`), with a `δh̃` corollary
(`recovery_unique_delta`) citing `Gamma_eq_delta_hTilde_basis` directly. The local
`TrivSqZeroExt`-lift algebra map is named `φ`, as in `algebraMap_Pmn_R_injective`
(`OspN/SourceIndependence.lean`), since `F` names the `FermionIndex` parameter.
-/

namespace OspOddDeformations
namespace OspN

/-! ## κ-cancellation -/

/-- `κ · algebraMap p = 0 ↔ p = 0` — reuses `kappa_ne_zero`'s own `TrivSqZeroExt`-lift
`φ` (`Source.lean`) a second time: `φ (κ · algebraMap p) = φ(κ) * φ(algebraMap p)
= inr 1 * inl p = inr p` (`TrivSqZeroExt.inr_mul_inl`), and `inr p = 0 ↔ p = 0`
(`TrivSqZeroExt.snd`). -/
theorem kappa_mul_algebraMap_eq_zero_iff (F : FermionIndex) (n : ℕ) (p : Pmn F n) :
    kappa F n * algebraMap (Pmn F n) (R F n) p = 0 ↔ p = 0 := by
  set φ : R F n →ₐ[Pmn F n] TrivSqZeroExt (Pmn F n) (Pmn F n) :=
    CliffordAlgebra.lift (Qzero F n)
      ⟨TrivSqZeroExt.inrHom (Pmn F n) (Pmn F n), fun v => by
        change TrivSqZeroExt.inr v * TrivSqZeroExt.inr v = _
        rw [TrivSqZeroExt.inr_mul_inr, show Qzero F n v = 0 from rfl, map_zero]⟩ with hφ
  have hφkappa : φ (kappa F n) = TrivSqZeroExt.inr 1 := by
    rw [kappa, hφ, CliffordAlgebra.lift_ι_apply]
    rfl
  have hφalg : φ (algebraMap (Pmn F n) (R F n) p) = TrivSqZeroExt.inl p := φ.commutes p
  constructor
  · intro h
    have hφ0 : φ (kappa F n * algebraMap (Pmn F n) (R F n) p) = 0 := by rw [h, map_zero]
    rw [map_mul, hφkappa, hφalg, TrivSqZeroExt.inr_mul_inl] at hφ0
    have := congrArg TrivSqZeroExt.snd hφ0
    rw [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] at this
    simpa using this
  · intro h
    rw [h, map_zero, mul_zero]

/-- **κ-cancellation: `c ↦ κ · ι₀(c)` is injective on `OspMod F n`**, as a
`Function.Injective` statement. -/
theorem kappa_iota0_injective_inj (F : FermionIndex) (n : ℕ) :
    Function.Injective (fun c : OspMod F n => kappaAB F n * iota0 F n c) := by
  have hker : ∀ x : OspMod F n, kappaAB F n * iota0 F n x = 0 → x = 0 := by
    intro x hx
    set g : (OspBasis F n →₀ ℚ) →ₗ[ℚ] A0 F n := Finsupp.linearCombination ℚ (X0A0 F n) with hgdef
    have hg_inj : Function.Injective g := X0A0_linearIndependent F n
    have : Module.Flat ℚ (R F n) := inferInstance
    have hgl_inj : Function.Injective (g.lTensor (R F n)) :=
      Module.Flat.lTensor_preserves_injective_linearMap g hg_inj
    have hbridge : (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)).symm
        (kappaAB F n * iota0 F n x)
        = ∑ X : OspBasis F n,
            (kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (X0A0 F n X) := by
      unfold iota0
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro X _
      have hmem : algebraMap (Pmn F n) (R F n) (x X) ∈ RGrading F n 0 :=
        SetLike.algebraMap_mem_graded _ _
      rw [show (kappaAB F n *
            ((algebraMap (Pmn F n) (R F n) (x X)) ᵍ⊗ₜ[ℚ] (1 : A0 F n) * X0 F n X) : AB F n)
          = ((kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ᵍ⊗ₜ[ℚ] (1 : A0 F n) : AB F n)
              * X0 F n X from by
        rw [← mul_assoc]
        congr 1
        unfold kappaAB
        exact GradedTensorProduct.tmul_one_mul_coe_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
          (kappa F n) (⟨algebraMap (Pmn F n) (R F n) (x X), hmem⟩ : RGradingQ F n 0) (1 : A0 F n)]
      rw [X0_eq_tmul,
        GradedTensorProduct.tmul_one_mul_one_tmul (𝒜 := RGradingQ F n) (ℬ := A0Grading F n)
          (kappa F n * algebraMap (Pmn F n) (R F n) (x X)) (X0A0 F n X)]
      rfl
    have hzero : (GradedTensorProduct.of ℚ (RGradingQ F n) (A0Grading F n)).symm
        (kappaAB F n * iota0 F n x) = 0 := by rw [hx, map_zero]
    rw [hbridge] at hzero
    have hpre : g.lTensor (R F n)
        (∑ X : OspBasis F n,
          (kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ)))
        = 0 := by
      rw [map_sum]
      rw [show (∑ X : OspBasis F n, g.lTensor (R F n)
            ((kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))))
          = ∑ X : OspBasis F n,
              (kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (X0A0 F n X) from by
        apply Finset.sum_congr rfl
        intro X _
        rw [LinearMap.lTensor_tmul, hgdef, Finsupp.linearCombination_single, one_smul]]
      exact hzero
    have hsum0 : ∑ X : OspBasis F n,
        (kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))
        = (0 : TensorProduct ℚ (R F n) (OspBasis F n →₀ ℚ)) := hgl_inj (by rw [hpre, map_zero])
    funext X₀
    have happly := congrArg
      (TensorProduct.map (LinearMap.id : R F n →ₗ[ℚ] R F n) (Finsupp.lapply X₀)) hsum0
    rw [map_sum, map_zero] at happly
    rw [show (∑ X : OspBasis F n,
          TensorProduct.map (LinearMap.id : R F n →ₗ[ℚ] R F n) (Finsupp.lapply X₀)
            ((kappa F n * algebraMap (Pmn F n) (R F n) (x X)) ⊗ₜ[ℚ] (Finsupp.single X (1 : ℚ))))
        = (kappa F n * algebraMap (Pmn F n) (R F n) (x X₀)) ⊗ₜ[ℚ] (1 : ℚ) from by
      rw [Fintype.sum_eq_single X₀ (fun Y hY => by
        rw [TensorProduct.map_tmul, LinearMap.id_apply, Finsupp.lapply_apply,
          Finsupp.single_eq_of_ne (Ne.symm hY), TensorProduct.tmul_zero])]
      rw [TensorProduct.map_tmul, LinearMap.id_apply, Finsupp.lapply_apply, Finsupp.single_eq_same]]
      at happly
    have := congrArg (TensorProduct.rid ℚ (R F n)) happly
    rw [TensorProduct.rid_tmul, one_smul, map_zero] at this
    have hx0 : kappa F n * algebraMap (Pmn F n) (R F n) (x X₀) = 0 := this
    have := (kappa_mul_algebraMap_eq_zero_iff F n (x X₀)).mp hx0
    rw [this]
    rfl
  intro a b hab
  simp only at hab
  have h : kappaAB F n * iota0 F n (a - b) = 0 := by
    have : iota0 F n (a - b) = iota0 F n a - iota0 F n b := by
      rw [sub_eq_add_neg, sub_eq_add_neg, iota0_add, iota0_neg]
    rw [this, mul_sub, hab, sub_self]
  have := hker (a - b) h
  exact sub_eq_zero.mp this

/-- **κ-cancellation, pointwise form** — `kappa_iota0_injective_inj` unfolded pointwise; the
two forms are equivalent. -/
theorem kappa_iota0_injective (F : FermionIndex) (n : ℕ) {x y : OspMod F n}
    (h : kappaAB F n * iota0 F n x = kappaAB F n * iota0 F n y) : x = y :=
  kappa_iota0_injective_inj F n h

/-! ## Uniqueness -/

/-- **Uniqueness (paper Theorem 4.3): the coefficient `c` in `recovery`'s own identity is
forced to be `GammaBasis X Y`.** -/
theorem recovery_unique (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) (c : OspMod F n)
    (h : scomm X Y (Xhat F n X) (Xhat F n Y)
      = iotaB F n (bracket0Basis X Y) + kappaAB F n * iota0 F n c) :
    c = GammaBasis X Y := by
  have hrec := recovery F n X Y
  rw [hrec] at h
  have heq : kappaAB F n * iota0 F n c
      = kappaAB F n * iota0 F n (GammaBasis X Y) :=
    (add_left_cancel h).symm
  have hzero : kappaAB F n * iota0 F n (c - GammaBasis X Y) = 0 := by
    have hsub : iota0 F n (c - GammaBasis X Y)
        = iota0 F n c - iota0 F n (GammaBasis X Y) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, iota0_add, iota0_neg]
    rw [hsub, mul_sub, heq, sub_self]
  have hz2 : (fun d : OspMod F n => kappaAB F n * iota0 F n d) (c - GammaBasis X Y)
      = (fun d : OspMod F n => kappaAB F n * iota0 F n d) (0 : OspMod F n) := by
    simp only
    rw [hzero, iota0_zero, mul_zero]
  have := kappa_iota0_injective_inj F n hz2
  exact sub_eq_zero.mp this

/-- **The `δh̃` form of uniqueness**, citing `Gamma_eq_delta_hTilde_basis` directly
(`OspN/Coboundary.lean`). -/
theorem recovery_unique_delta (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) (c : OspMod F n)
    (h : scomm X Y (Xhat F n X) (Xhat F n Y)
      = iotaB F n (bracket0Basis X Y) + kappaAB F n * iota0 F n c) :
    c = deltaBasis hTilde X Y := by
  rw [← Gamma_eq_delta_hTilde_basis]
  exact recovery_unique F n X Y c h

end OspN
end OspOddDeformations
