import OspOddDeformations.OspN.Multi.TierBLemmas

/-!
# `Θ_*` is not an automorphism of `[·,·]_0` when `Ω ≠ 0`

Witness `[L_{uu}, F_{w,i}]` (`Ω_{uw} ≠ 0`): the difference `[·,·]_{J-Ω} - [·,·]_0` is
`-Ω_{uw} F_{u,i}`, and `Θ_*` is injective on it because `Θ_{ua}(∅) ≠ 0` for some `a` (from
`ΘJΘᵀ = J - Ω` in degree `0`).
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

-- Toolchain (v4.34): `OspBasis` is a plain `def` whose sum structure the proofs use; as in
-- `ThetaStarBracket.lean`, restore the pre-v4.34 type-transparency behaviour of `isDefEq` here.
set_option backward.isDefEq.respectTransparency.types false
-- `OspBasis` is a plain `def`, as in `ThetaStarBracket.lean` and `VChiBracket.lean`

variable {F : FermionIndex} {n r : ℕ}

theorem witness_diff (u w : I n) (i : F.K) :
    bracketJM JmOmega (gtens gone (eN (Lof u u : OspBasis F n)) : RModM F n r)
        (gtens gone (eN (Fof w i))) -
      bracket0M (gtens gone (eN (Lof u u : OspBasis F n)) : RModM F n r) (gtens gone (eN (Fof w i)))
    = -gtens (OmegaR u w) (eN (Fof u i)) := by
  rw [bracketJM_eq_liftB, bracket0M_eq_liftB, liftBJ_eN_eN, liftB0_gtens_eN]
  have hL : (Lof u u : OspBasis F n) = Sum.inl ⟨(u, u), le_refl _⟩ := Lof_of_le (le_refl _)
  rw [hL]
  simp only [sigPow_gone, gmul_gone, gsmul_gone]
  rw [bracketJBasis0_L_F]
  change _ - gtens gone (bracketLF u u w i) = _
  simp only [bracketLF, gtens_JmOmega, gtens_add_right, gtens_rsmul_right]
  module

/-- A row of `Θ` has a nonzero `∅`-component. -/
theorem exists_theta_empty_ne (Θ : I n → I n → GR F n r)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u : I n) :
    ∃ a : I n, Θ u a ∅ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hΘ u (u.1, !u.2)
  have h2 : thetaJthetaT Θ u (u.1, !u.2) ∅ = 0 := by
    unfold thetaJthetaT
    simp only [Finset.sum_apply, gmul_empty_apply, hcon, zero_mul]
    simp
  have h3 : (JR u (u.1, !u.2) - OmegaR u (u.1, !u.2) : GR F n r) ∅ ≠ 0 := by
    have hO : (OmegaR (F := F) (r := r) u (u.1, !u.2)) ∅ = 0 :=
      HasCard_OmegaR u _ ∅ (by simp)
    simp only [Pi.sub_apply, hO, sub_zero]
    rw [JR_eq]
    simp [gone, J_eq_ite]
    cases u.2 <;> simp
  exact h3 (h1 ▸ h2)

theorem gmul_top_apply (a b : GR F n r) (T : Finset (Fin r)) (k : ℕ) (hT : T.card = k)
    (ha : HasCard k a) : gmul a b T = a T * b ∅ := by
  unfold gmul
  rw [Finset.sum_eq_single T]
  · rw [Finset.sum_eq_single ∅]
    · simp [gs_empty_right]
    · intro B _ hB
      by_cases hU : T ∪ B = T
      · have hBT : B ⊆ T := hU ▸ Finset.subset_union_right
        by_cases hd : Disjoint T B
        · exact absurd (by simpa using hd.symm.mono_right hBT) hB
        · simp [gs_eq_zero_of_not_disjoint hd]
      · simp [hU]
    · simp
  · intro A _ hA
    refine Finset.sum_eq_zero fun B _ => ?_
    by_cases hU : A ∪ B = T
    · have hAT : A ⊆ T := hU ▸ Finset.subset_union_left
      by_cases hc : A.card = k
      · exact absurd (Finset.eq_of_subset_of_card_le hAT (by omega)) hA
      · simp [ha A hc]
    · simp [hU]
  · simp

theorem gmul_theta_eq_zero_of_ThetaStar (Θ : I n → I n → GR F n r) (c : GR F n r) (u : I n)
    (i : F.K) (hz : ThetaStar Θ (gtens c (eN (Fof u i))) = 0) (a : I n) :
    gmul c (Θ u a) = 0 := by
  rw [ThetaStar_eq_linM, linM_gtens_eN, T0_F] at hz
  simp only [gsmul_sum_right, gsmul_gtens] at hz
  funext T
  have h := congrFun hz (Fof a i, T)
  simp only [Finset.sum_apply, gtens_apply, emb0_eN] at h
  rw [Finset.sum_eq_single a] at h
  · simpa using h
  · intro x _ hx
    have : (Fof a i : OspBasis F n) ≠ Fof x i := fun e => hx (by
      have := congrArg (fun z : OspBasis F n => match z with
        | Sum.inr (Sum.inr (y, _)) => y
        | _ => a) e
      simpa [Fof] using this.symm)
    simp [this]
  · simp

end Multi
end OspN
end OspOddDeformations
