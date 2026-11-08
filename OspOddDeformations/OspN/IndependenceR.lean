import OspOddDeformations.OspN.Kappa
import OspOddDeformations.OspN.SourceUniqueness

/-!
# Prop 3.3 in full

Paper Prop 3.3: `ι_0 : 𝔤_R → A_0` is injective, `R = P ⊗ Λ(κ)`. `iota0_injective` gives it on
`𝔤_P`, and `kappa_iota0_injective` for `x ↦ κ ι_0(x)`; here it is proved on `𝔤_R`, whose
elements are `x_0 + κ x_1` (`falsePart`, `truePart`).
-/

namespace OspOddDeformations
namespace OspN

/-- `ι_0` on `𝔤_R`: `x_0 + κ x_1 ↦ ι_0(x_0) + κ ι_0(x_1)`. -/
noncomputable def iota0R (F : FermionIndex) (n : ℕ) (x : RMod F n) : AB F n :=
  iota0 F n (falsePart x) + kappaAB F n * iota0 F n (truePart x)

/-- **Prop 3.3**: `ι_0` is injective on `𝔤_R`. -/
theorem iota0R_injective (F : FermionIndex) (n : ℕ) : Function.Injective (iota0R F n) := by
  intro x y h
  unfold iota0R at h
  have hκ := congrArg (fun z => kappaAB F n * z) h
  simp only [mul_add, ← mul_assoc, kappaAB_sq, zero_mul, add_zero] at hκ
  have h0 : falsePart x = falsePart y := kappa_iota0_injective F n hκ
  rw [h0, add_right_inj] at h
  have h1 : truePart x = truePart y := kappa_iota0_injective F n h
  funext ⟨i, b⟩
  cases b
  · exact congrFun h0 i
  · exact congrFun h1 i

end OspN
end OspOddDeformations
