import OspOddDeformations.OspN.Presented.MultiRealize

/-!
# Prop 5.2 (the change of lifts over `R_r`), for the presented algebras

`Φ_r(ι_β X) = ι_0(U X)` for every basis element `X` (`untwistR_XpM`), with the coordinate-level
`U` (`Multi.UM`) at `Θ = (𝕀 + ΩJ)^{1/2}` (`Multi.thetaSeries`). The computation is that of
`LiftChange.lean`, with
`Φ_r(b_u) = Σ_w Θ_{uw} B_w + c_u` (`untwistR_b`):

* `Φ_r(Ŝ_{ij}) = S^0_{ij}`;
* `Φ_r(F̂_{u,i}) = Σ_w Θ_{uw} F^0_{w,i} + ½ Σ_j γ_{u,j} S^0_{j,i}`;
* `Φ_r(L̂_{uv}) = Σ_{w,z} Θ_{uw} Θ_{vz} L^0_{wz}
  + Σ_{w,i} (Θ_{uw} γ_{v,i} + Θ_{vw} γ_{u,i}) F^0_{w,i} − ½ Σ_{i,j} γ_{u,i} γ_{v,j} S^0_{ij}`.

On the other side `U(eM X) = UBasis0 Θ X` (`UM_eM`), and `ι_0(a ⊗ v) = embG(a) ι(v)`
(`iotaM_gtens`); `embG_mul`, `embG_one`, `embG_gammaR` and `embG_thetaSeries`
(`MultiRealize.lean`) carry the coordinate-level `Θ` and `γ` to those of `A_0`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-! The auxiliary lemmas of the proof are in the namespace `A7b`. -/

namespace A7b

section general

variable (β' : Fin r → I n → F.K → Multi.PmnR F n r)

/-- `ι` on `𝔤` with coefficients carried by `emb0`: `v ↦ Σ_X emb0(v_X) X̂`. -/
noncomputable def iotaE (v : OspMod F n) : AM F n r β' :=
  ∑ X, (Multi.emb0 (v X) : Multi.PmnR F n r) • XpM β' X

theorem embG_add (a b : Multi.GR F n r) : embG β' (a + b) = embG β' a + embG β' b := by
  simp only [embG, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem iotaM_add (x y : Multi.RModM F n r) : iotaM β' (x + y) = iotaM β' x + iotaM β' y := by
  simp only [iotaM, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem iotaM_sub (x y : Multi.RModM F n r) : iotaM β' (x - y) = iotaM β' x - iotaM β' y := by
  simp only [iotaM, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem iotaM_rsmul (q : ℚ) (x : Multi.RModM F n r) : iotaM β' (q • x) = q • iotaM β' x := by
  simp only [iotaM, Pi.smul_apply, smul_assoc, Finset.smul_sum]

theorem iotaM_sum {α : Type*} (s : Finset α) (f : α → Multi.RModM F n r) :
    iotaM β' (∑ a ∈ s, f a) = ∑ a ∈ s, iotaM β' (f a) := by
  simp only [iotaM, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem iotaM_gtens (a : Multi.GR F n r) (v : OspMod F n) :
    iotaM β' (Multi.gtens a v) = embG β' a * iotaE β' v := by
  simp only [iotaM, Multi.gtens, embG, iotaE, Fintype.sum_prod_type, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun S _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem iotaE_eN (X : OspBasis F n) : iotaE β' (eN X) = XpM β' X := by
  unfold iotaE
  rw [Finset.sum_eq_single X]
  · simp [eN]
  · intro Y _ hY
    simp [eN, hY]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iotaE_neg (v : OspMod F n) : iotaE β' (-v) = -iotaE β' v := by
  simp only [iotaE, ospMod_neg_apply, map_neg, neg_smul, Finset.sum_neg_distrib]

theorem iotaE_zero : iotaE β' (0 : OspMod F n) = 0 := by
  simp only [iotaE, ospMod_zero_apply, map_zero, zero_smul, Finset.sum_const_zero]

theorem iotaE_Sof (i j : F.K) : iotaE β' (Sof i j) = SpM β' i j := by
  unfold Sof
  split_ifs with h1 h2
  · erw [iotaE_eN]; rfl
  · erw [iotaE_neg, iotaE_eN]
    change -(SpM β' j i) = SpM β' i j
    unfold SpM
    rw [← smul_neg]
    congr 1
    abel
  · have hij : i = j := F.key_injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    subst hij
    rw [iotaE_zero]
    unfold SpM
    simp

theorem iotaE_Lof (u v : I n) : iotaE β' (eN (Lof u v)) = LpM β' u v := by
  rw [iotaE_eN]
  by_cases h : Bmn.IKey u ≤ Bmn.IKey v
  · simp only [Lof, h, ↓reduceDIte]; rfl
  · simp only [Lof, h, ↓reduceDIte]
    change LpM β' v u = LpM β' u v
    unfold LpM
    rw [add_comm]

theorem iotaE_Fof (u : I n) (i : F.K) : iotaE β' (eN (Fof u i)) = FpM β' u i := by
  rw [iotaE_eN]; rfl

end general

theorem UM_eM (Θ : I n → I n → Multi.GR F n r) (X : OspBasis F n) :
    Multi.UM Θ (eM X) = Multi.UBasis0 Θ X := by
  have he : ∀ p : Multi.RBasisM F n r, eM X p = if p = (X, ∅) then 1 else 0 := by
    rintro ⟨Y, S⟩
    by_cases hS : S = ∅ <;> by_cases hY : Y = X <;>
      simp [eM, Multi.kap, Multi.liftBy, eN, hS, hY]
  have hg : (Multi.gmono ∅ 1 : Multi.GR F n r) = Multi.gone := by
    funext T; simp [Multi.gmono, Multi.gone]
  simp only [Multi.UM, he, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, hg, Multi.gsmul_gone]

section paper

set_option hygiene false in
/-- The zero parameters, `A_0 = AM F n r 0`. -/
local notation "β₀" => (0 : Fin r → I n → F.K → Multi.PmnR F n r)

theorem bM_zero_comm_aM (w : I n) (i : F.K) :
    bM (jR F n r) (gR F n r) β₀ w * aM _ _ β₀ i = aM _ _ β₀ i * bM _ _ β₀ w := by
  rw [bM_mul_aM]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem aM_mul_gammaM_zero (u : I n) (i j : F.K) :
    aM (jR F n r) (gR F n r) β₀ i * gammaM (deltaR F n r) u j
      = -(gammaM (deltaR F n r) u j * aM _ _ β₀ i) := by
  rw [gammaM_mul_aM, neg_neg]

/-- `{a_i, Σ_w Θ_{uw} B_w + c_u} = Σ_w Θ_{uw} {a_i, B_w} + Σ_j γ_{u,j} [a_j, a_i]`. -/
theorem aM_anticomm_bTilde (u : I n) (i : F.K) :
    aM (jR F n r) (gR F n r) β₀ i
        * ((∑ w, thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w) + cM (deltaR F n r) u)
      + ((∑ w, thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w) + cM (deltaR F n r) u)
        * aM _ _ β₀ i
      = (∑ w, thetaV (deltaR F n r) β₀ u w
          * (aM _ _ β₀ i * bM _ _ β₀ w + bM _ _ β₀ w * aM _ _ β₀ i))
        + ∑ j, gammaM (deltaR F n r) u j
            * (aM _ _ β₀ j * aM _ _ β₀ i - aM _ _ β₀ i * aM _ _ β₀ j) := by
  have hT : aM (jR F n r) (gR F n r) β₀ i * (∑ w, thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w)
      + (∑ w, thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w) * aM _ _ β₀ i
      = ∑ w, thetaV (deltaR F n r) β₀ u w
          * (aM _ _ β₀ i * bM _ _ β₀ w + bM _ _ β₀ w * aM _ _ β₀ i) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_add, ← mul_assoc, ← thetaV_central, mul_assoc, mul_assoc]
  have hc : aM (jR F n r) (gR F n r) β₀ i * cM (deltaR F n r) u + cM (deltaR F n r) u * aM _ _ β₀ i
      = ∑ j, gammaM (deltaR F n r) u j
          * (aM _ _ β₀ j * aM _ _ β₀ i - aM _ _ β₀ i * aM _ _ β₀ j) := by
    rw [cM, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, aM_mul_gammaM_zero]
    noncomm_ring
  rw [mul_add, add_mul, ← hT, ← hc]
  abel

theorem untwistR_FpM (u : I n) (i : F.K) :
    untwistR F n r (FpM (Multi.betaR F n r) u i)
      = (∑ w, thetaV (deltaR F n r) β₀ u w * FpM β₀ w i)
        + (1 / 2 : ℚ) • ∑ j, gammaM (deltaR F n r) u j * SpM β₀ j i := by
  rw [FpM, map_rat_smul, map_add, map_mul, map_mul, untwistR_a, untwistR_b,
    aM_anticomm_bTilde]
  rw [smul_add]
  congr 1
  · simp only [FpM, mul_smul_comm, Finset.smul_sum]
  · simp only [SpM, mul_smul_comm, Finset.smul_sum, smul_smul]
    norm_num

theorem expand_anticomm {A : Type*} [Ring A] (T T' c c' : A) :
    (T + c) * (T' + c') + (T' + c') * (T + c)
      = (T * T' + T' * T) + ((T * c' + c' * T) + (T' * c + c * T')) + (c * c' + c' * c) := by
  noncomm_ring

theorem FpM_zero (w : I n) (i : F.K) :
    FpM β₀ w i = (1 / 2 : ℚ) • (bM (jR F n r) (gR F n r) β₀ w * aM _ _ β₀ i) := by
  rw [FpM, ← bM_zero_comm_aM, ← two_smul ℚ, smul_smul]
  norm_num

/-- `{Σ_w Θ_{uw} B_w, Σ_z Θ_{vz} B_z} = Σ_{w,z} Θ_{uw} Θ_{vz} {B_w, B_z}`. -/
theorem T_anticomm_T (u v : I n) :
    (∑ w, thetaV (deltaR F n r) β₀ u w * bM (jR F n r) (gR F n r) β₀ w)
        * (∑ z, thetaV (deltaR F n r) β₀ v z * bM _ _ β₀ z)
      + (∑ z, thetaV (deltaR F n r) β₀ v z * bM _ _ β₀ z)
        * (∑ w, thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w)
      = ∑ w, ∑ z, thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z
          * (bM _ _ β₀ w * bM _ _ β₀ z + bM _ _ β₀ z * bM _ _ β₀ w) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun z w => thetaV (deltaR F n r) β₀ v z * bM (jR F n r) (gR F n r) β₀ z
      * (thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 := thetaV_central (δ := deltaR F n r) (β' := β₀) v z (bM (jR F n r) (gR F n r) β₀ w)
  have h2 := thetaV_central (δ := deltaR F n r) (β' := β₀) u w (bM (jR F n r) (gR F n r) β₀ z)
  have h3 := thetaV_central (J := jR F n r) (g := gR F n r) (δ := deltaR F n r) (β' := β₀) u w
    (thetaV (deltaR F n r) β₀ v z)
  have e1 : thetaV (deltaR F n r) β₀ u w * bM (jR F n r) (gR F n r) β₀ w
      * (thetaV (deltaR F n r) β₀ v z * bM _ _ β₀ z)
      = thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z
        * (bM _ _ β₀ w * bM _ _ β₀ z) := by
    rw [mul_assoc, ← mul_assoc (bM _ _ β₀ w), ← h1]
    simp only [mul_assoc]
  have e2 : thetaV (deltaR F n r) β₀ v z * bM (jR F n r) (gR F n r) β₀ z
      * (thetaV (deltaR F n r) β₀ u w * bM _ _ β₀ w)
      = thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z
        * (bM _ _ β₀ z * bM _ _ β₀ w) := by
    rw [h3, mul_assoc, ← mul_assoc (bM _ _ β₀ z), ← h2]
    simp only [mul_assoc]
  rw [mul_add, e1, e2]

/-- `{Σ_w Θ_{xw} B_w, c_y} = 2 Σ_{w,i} Θ_{xw} γ_{y,i} B_w a_i`. -/
theorem T_anticomm_c (x y : I n) :
    (∑ w, thetaV (deltaR F n r) β₀ x w * bM (jR F n r) (gR F n r) β₀ w) * cM (deltaR F n r) y
      + cM (deltaR F n r) y * (∑ w, thetaV (deltaR F n r) β₀ x w * bM _ _ β₀ w)
      = (2 : ℚ) • ∑ w, ∑ i, thetaV (deltaR F n r) β₀ x w * gammaM (deltaR F n r) y i
          * (bM _ _ β₀ w * aM _ _ β₀ i) := by
  have hc := comb_comm (thetaV (deltaR F n r) β₀) (thetaV_central (δ := deltaR F n r))
    (bM (jR F n r) (gR F n r) β₀) (cM (deltaR F n r) y)
    (fun w => bM_mul_cM_zero (deltaR F n r) w y) x
  rw [← hc, ← two_smul ℚ]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← mul_assoc (bM _ _ β₀ w), ← gammaM_mul_bM]
  simp only [mul_assoc]

/-- `{c_u, c_v} = −Σ_{i,j} γ_{u,i} γ_{v,j} [a_i, a_j]`. -/
theorem c_anticomm_c (u v : I n) :
    cM (J := jR F n r) (g := gR F n r) (β := β₀) (deltaR F n r) u * cM (deltaR F n r) v
      + cM (deltaR F n r) v * cM (deltaR F n r) u
      = -∑ i, ∑ j, gammaM (deltaR F n r) u i * gammaM (deltaR F n r) v j
          * (aM _ _ β₀ i * aM _ _ β₀ j - aM _ _ β₀ j * aM _ _ β₀ i) := by
  rw [cM, cM, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ)
    (t := Finset.univ) (f := fun j i => gammaM (J := jR F n r) (g := gR F n r) (β := β₀)
      (deltaR F n r) v j * aM _ _ β₀ j * (gammaM (deltaR F n r) u i * aM _ _ β₀ i)),
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaga, gaga, gammaM_mul_gammaM (deltaR F n r) v u j i]
  noncomm_ring

theorem untwistR_LpM (u v : I n) :
    untwistR F n r (LpM (Multi.betaR F n r) u v)
      = (∑ w, ∑ z, thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z * LpM β₀ w z)
        + (∑ w, ∑ i, (thetaV (deltaR F n r) β₀ u w * gammaM (deltaR F n r) v i
            + thetaV (deltaR F n r) β₀ v w * gammaM (deltaR F n r) u i) * FpM β₀ w i)
        - (1 / 2 : ℚ) • ∑ i, ∑ j,
            gammaM (deltaR F n r) u i * gammaM (deltaR F n r) v j * SpM β₀ i j := by
  rw [LpM, map_rat_smul, map_add, map_mul, map_mul, untwistR_b, untwistR_b, expand_anticomm,
    T_anticomm_T, T_anticomm_c, T_anticomm_c, c_anticomm_c]
  have hX : (∑ w, ∑ z, thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z
      * LpM β₀ w z)
      = (1 / 4 : ℚ) • ∑ w, ∑ z, thetaV (deltaR F n r) β₀ u w * thetaV (deltaR F n r) β₀ v z
          * (bM (jR F n r) (gR F n r) β₀ w * bM _ _ β₀ z + bM _ _ β₀ z * bM _ _ β₀ w) := by
    simp only [LpM, mul_smul_comm, Finset.smul_sum]
  have hY : (∑ w, ∑ i, (thetaV (deltaR F n r) β₀ u w * gammaM (deltaR F n r) v i
      + thetaV (deltaR F n r) β₀ v w * gammaM (deltaR F n r) u i) * FpM β₀ w i)
      = (1 / 2 : ℚ) • (∑ w, ∑ i, thetaV (deltaR F n r) β₀ u w * gammaM (deltaR F n r) v i
          * (bM (jR F n r) (gR F n r) β₀ w * aM _ _ β₀ i))
        + (1 / 2 : ℚ) • (∑ w, ∑ i, thetaV (deltaR F n r) β₀ v w * gammaM (deltaR F n r) u i
          * (bM (jR F n r) (gR F n r) β₀ w * aM _ _ β₀ i)) := by
    simp only [FpM_zero, add_mul, mul_smul_comm, Finset.sum_add_distrib, Finset.smul_sum,
      smul_add]
  have hZ : (∑ i, ∑ j, gammaM (J := jR F n r) (g := gR F n r) (β := β₀) (deltaR F n r) u i
      * gammaM (deltaR F n r) v j * SpM β₀ i j)
      = (1 / 2 : ℚ) • ∑ i, ∑ j, gammaM (deltaR F n r) u i * gammaM (deltaR F n r) v j
          * (aM (jR F n r) (gR F n r) β₀ i * aM _ _ β₀ j - aM _ _ β₀ j * aM _ _ β₀ i) := by
    simp only [SpM, mul_smul_comm, Finset.smul_sum]
  rw [hX, hY, hZ]
  module

theorem untwistR_SpM (i j : F.K) :
    untwistR F n r (SpM (Multi.betaR F n r) i j) = SpM β₀ i j := by
  rw [SpM, map_rat_smul, map_sub, map_mul, map_mul, untwistR_a, untwistR_a, SpM]

end paper

end A7b

open A7b in
/-- **Prop 5.2**, for the presented algebras: `Φ_r(ι_β X) = ι_0(U X)`, with the
coordinate-level `U` at `Θ = (𝕀 + ΩJ)^{1/2}`. -/
theorem untwistR_XpM (X : OspBasis F n) :
    untwistR F n r (XpM (Multi.betaR F n r) X)
      = iotaM 0 (Multi.UM Multi.thetaSeries (eM X)) := by
  rw [UM_eM]
  match X with
  | .inl ⟨(u, v), _⟩ =>
    simp only [XpM, Multi.UBasis0, iotaM_sub, iotaM_add, iotaM_rsmul, iotaM_sum, iotaM_gtens,
      embG_add, embG_mul, embG_thetaSeries, embG_gammaR, iotaE_Lof, iotaE_Fof, iotaE_Sof]
    exact untwistR_LpM u v
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [XpM, Multi.UBasis0, iotaM_gtens, embG_one, one_mul, iotaE_Sof, untwistR_SpM]
  | .inr (.inr (u, i)) =>
    simp only [XpM, Multi.UBasis0, iotaM_add, iotaM_rsmul, iotaM_sum, iotaM_gtens,
      embG_thetaSeries, embG_gammaR, iotaE_Fof, iotaE_Sof]
    exact untwistR_FpM u i

end Presented
end OspN
end OspOddDeformations
