import OspOddDeformations.OspN.Multi.LinM

/-!
# `U = Θ_* ∘ V_γ`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem linM_comp (A0 C0 : OspBasis F n → RModM F n r) (x : RModM F n r) :
    linM A0 (linM C0 x) = linM (fun Z => linM A0 (C0 Z)) x := by
  refine RModM_ext_grComp fun W => ?_
  simp only [grComp_linM]
  simp only [gmul_sum_left, gmul_sum_right, gmul_assoc]
  rw [Finset.sum_comm]

theorem gtens_add_left (a b : GR F n r) (v : OspMod F n) :
    gtens (a + b) v = gtens a v + gtens b v := by
  funext p; simp [gtens_apply, add_mul]

theorem gtens_sum_left {ι : Type*} (s : Finset ι) (a : ι → GR F n r) (v : OspMod F n) :
    gtens (∑ i ∈ s, a i) v = ∑ i ∈ s, gtens (a i) v := by
  funext p; simp [gtens_apply, Finset.sum_mul]

theorem gtens_rsmul_left (q : ℚ) (a : GR F n r) (v : OspMod F n) :
    q • gtens a v = gtens (q • a) v := by
  funext p; simp [gtens_apply]

theorem gsmul_gone_gtens (a : GR F n r) (v : OspMod F n) :
    gsmul a (gtens gone v) = gtens a v := by
  rw [gsmul_gtens, gmul_gone]

theorem ThetaStar_SCompat (Θ : I n → I n → GR F n r) : SCompat (ThetaStarBasis0 Θ) :=
  fun _ _ _ => rfl

/-- The `F`-part of `U L_{uv}` equals the `F`-part of `Θ_* (V_γ L_{uv})`. -/
theorem factor_L_F_sum (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (u v : I n) :
    ∑ w : I n, ∑ i : F.K, gtens (gmul (Θ u w) (gammaR v (F.dual i)) +
          gmul (Θ v w) (gammaR u (F.dual i))) (eN (Fof w i)) =
      ∑ x : F.K, (gsmul (gammaR v (F.dual x)) (ThetaStarBasis0 Θ (Fof u x)) +
        gsmul (gammaR u (F.dual x)) (ThetaStarBasis0 Θ (Fof v x))) := by
  have T0F : ∀ (a : I n) (x : F.K), ThetaStarBasis0 Θ (Fof a x) =
      ∑ w : I n, gtens (Θ a w) (eN (Fof w x)) := fun _ _ => rfl
  have h1 : ∀ w i, gtens (gmul (Θ u w) (gammaR v (F.dual i)) +
      gmul (Θ v w) (gammaR u (F.dual i))) (eN (Fof w i)) =
      gtens (gmul (gammaR v (F.dual i)) (Θ u w)) (eN (Fof w i)) +
      gtens (gmul (gammaR u (F.dual i)) (Θ v w)) (eN (Fof w i)) := by
    intro w i
    rw [gtens_add_left, gmul_comm_of_even (hEven u w), gmul_comm_of_even (hEven v w)]
  simp only [h1, T0F, gsmul_sum_right, gsmul_gtens, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) Finset.sum_comm Finset.sum_comm

theorem UBasis0_eq_linM (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (Z : OspBasis F n) :
    UBasis0 Θ Z = linM (ThetaStarBasis0 Θ) (VBasis0 gammaR Z) := by
  rcases Z with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · have hL : (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h⟩ := Lof_of_le h
    simp only [UBasis0, VBasis0, linM_sub, linM_add, linM_rsmul, linM_sum, hL,
      gsmul_gone, linM_gtens, sum_emb0_Sof _ (ThetaStar_SCompat Θ),
      sum_emb0_eN, gsmul_sum_right, gsmul_gtens, gmul_gone]
    have e1 : ∑ Y : OspBasis F n, emb0 (r := r) (eN (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) Y) •
        ThetaStarBasis0 Θ Y = ThetaStarBasis0 Θ (Sum.inl ⟨(u, v), h⟩) :=
      sum_emb0_eN (ThetaStarBasis0 Θ) _
    have hB := factor_L_F_sum Θ hEven u v
    rw [e1, hB]
    rfl
  · simp only [UBasis0, VBasis0]
    rw [linM_gtens, sum_emb0_Sof _ (ThetaStar_SCompat Θ), gsmul_gone_gtens]
  · simp only [UBasis0, VBasis0, linM_add, linM_rsmul, linM_sum, linM_gtens_eN, gsmul_gone]
    simp only [linM_gtens, sum_emb0_Sof _ (ThetaStar_SCompat Θ), gsmul_gone_gtens]
    rfl

theorem UM_eq_comp' (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (x : RModM F n r) : UM Θ x = ThetaStar Θ (VChi gammaR x) := by
  rw [UM_eq_linM, ThetaStar_eq_linM, VChi_eq_linM, linM_comp]
  congr 1
  funext Z
  exact UBasis0_eq_linM Θ hEven Z

end Multi
end OspN
end OspOddDeformations
