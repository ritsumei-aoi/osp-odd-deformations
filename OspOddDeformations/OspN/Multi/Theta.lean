import OspOddDeformations.OspN.Multi.Degree
import OspOddDeformations.OspN.Multi.UMBij

/-!
# `Θ = 𝕀 + ½ΩJ` for `r ≤ 3`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem J_eq_ite (a b : I n) :
    J n a b = if b = (a.1, !a.2) then (if a.2 then -1 else 1) else 0 := by
  obtain ⟨k, x⟩ := a
  obtain ⟨l, y⟩ := b
  cases x <;> cases y <;> simp [J, Prod.ext_iff, eq_comm]

/-- `J² = -𝕀`. -/
theorem J_mul_J (a v : I n) : ∑ z, J n a z * J n z v = if a = v then -1 else 0 := by
  classical
  rw [Finset.sum_eq_single (a.1, !a.2)]
  · rw [J_eq_ite a, J_eq_ite (a.1, !a.2) v]
    obtain ⟨k, x⟩ := a
    obtain ⟨l, y⟩ := v
    cases x <;> cases y <;> simp [Prod.ext_iff, eq_comm]
  · intro z _ hz
    rw [J_eq_ite a z]; simp [hz]
  · simp

/-- `J Jᵀ = 𝕀`. -/
theorem J_mul_J_transpose (u a : I n) : ∑ z, J n u z * J n a z = if u = a then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single (u.1, !u.2)]
  · rw [J_eq_ite u, J_eq_ite a (u.1, !u.2)]
    obtain ⟨k, x⟩ := u
    obtain ⟨l, y⟩ := a
    cases x <;> cases y <;> simp [Prod.ext_iff, eq_comm]
  · intro z _ hz
    rw [J_eq_ite u z]; simp [hz]
  · simp

/-- Graded commutativity for homogeneous elements. -/
theorem gmul_comm_of_card {j k : ℕ} {a b : GR F n r} (ha : HasCard j a) (hb : HasCard k b) :
    gmul a b = ((-1 : ℚ) ^ (j * k)) • gmul b a := by
  funext T
  simp only [gmul, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.union_comm B A]
  by_cases hA : A.card = j
  · by_cases hB : B.card = k
    · by_cases hU : A ∪ B = T
      · simp only [hU, ite_true]
        rw [gs_comm A B, hA, hB, smul_smul, mul_comm (b B) (a A)]
      · simp [hU]
    · simp [hb B hB]
  · simp [ha A hA]

theorem gammaR_anticomm (u v : I n) (i j : F.K) :
    gmul (gammaR (r := r) u i) (gammaR v j) = - gmul (gammaR v j) (gammaR u i) := by
  have := gmul_comm_of_card (HasCard_gammaR (r := r) u i) (HasCard_gammaR v j)
  simpa using this

theorem OmegaR_antisymm (u v : I n) : OmegaR (F := F) (r := r) v u = - OmegaR u v := by
  have hinv : Function.Involutive F.dual := F.dual_dual
  have key : ∑ i, gmul (gammaR (r := r) v i) (gammaR u (F.dual i))
      = - ∑ i, gmul (gammaR u i) (gammaR v (F.dual i)) := by
    rw [← Equiv.sum_comp hinv.toPerm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.Involutive.coe_toPerm, hinv i]
    exact gammaR_anticomm v u (F.dual i) i
  unfold OmegaR
  rw [key]

/-! ## `JR` acts by the scalar `J` -/

theorem JR_eq (u v : I n) :
    JR (F := F) (r := r) u v = (MvPolynomial.C (J n u v) : PmnR F n r) • gone := by
  funext T
  by_cases hT : T = ∅
  · simp [JR, gone, hT]
  · simp [JR, gone, hT]

theorem gmul_JR_left (u v : I n) (x : GR F n r) :
    gmul (JR u v) x = (MvPolynomial.C (J n u v) : PmnR F n r) • x := by
  rw [JR_eq, gmul_smul_left, gone_gmul]

theorem gmul_JR_right (x : GR F n r) (u v : I n) :
    gmul x (JR u v) = (MvPolynomial.C (J n u v) : PmnR F n r) • x := by
  rw [JR_eq, gmul_smul_right, gmul_gone]

theorem HasCard.smul {k : ℕ} (c : PmnR F n r) {a : GR F n r} (ha : HasCard k a) :
    HasCard k (c • a) := fun T h => by simp [ha T h]

/-- `(ΩJ)_{uw}`, as a sum of scalar multiples of `Ω`. -/
noncomputable def Kmat (u w : I n) : GR F n r :=
  ∑ a, (MvPolynomial.C (J n a w) : PmnR F n r) • OmegaR u a

theorem thetaHalf_apply (u w : I n) :
    thetaHalf (F := F) (n := n) (r := r) u w =
      (if u = w then gone else 0) + (1 / 2 : ℚ) • Kmat u w := by
  unfold Kmat
  unfold thetaHalf
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gmul_JR_right]

theorem HasCard_Kmat (u w : I n) : HasCard 2 (Kmat (F := F) (r := r) u w) :=
  HasCard.sum _ fun a _ => (HasCard_OmegaR u a).smul _

theorem Kmat_mul_Kmat (hr : r ≤ 3) (u w v z : I n) :
    gmul (Kmat (F := F) (r := r) u w) (Kmat v z) = 0 :=
  HasCard.of_lt (by omega) ((HasCard_Kmat u w).gmul (HasCard_Kmat v z))

theorem gmul_thetaHalf (hr : r ≤ 3) (u w v z : I n) :
    gmul (thetaHalf (F := F) (n := n) (r := r) u w) (thetaHalf v z) =
      (if u = w ∧ v = z then gone else 0) + (1 / 2 : ℚ) • (if u = w then Kmat v z else 0)
        + (1 / 2 : ℚ) • (if v = z then Kmat u w else 0) := by
  rw [thetaHalf_apply, thetaHalf_apply]
  by_cases hu : u = w <;> by_cases hv : v = z <;>
    simp [hu, hv, gmul_add_left, gmul_add_right, gmul_rsmul_left, gmul_rsmul_right, gone_gmul,
      gmul_gone, Kmat_mul_Kmat hr]
  abel

theorem C_sum_J_J (u a : I n) :
    ∑ z, (MvPolynomial.C (J n u z) : PmnR F n r) * MvPolynomial.C (J n a z)
      = if u = a then 1 else 0 := by
  simp_rw [← map_mul]
  rw [← map_sum, J_mul_J_transpose]
  split_ifs <;> simp

theorem C_sum_J_J' (a v : I n) :
    ∑ w, (MvPolynomial.C (J n w v) : PmnR F n r) * MvPolynomial.C (J n a w)
      = if a = v then -1 else 0 := by
  simp_rw [mul_comm (MvPolynomial.C (J n _ v)), ← map_mul]
  rw [← map_sum, J_mul_J]
  split_ifs <;> simp

theorem sum_J_smul_Kmat_left (u v : I n) :
    ∑ z, (MvPolynomial.C (J n u z) : PmnR F n r) • Kmat (F := F) (r := r) v z = OmegaR v u := by
  classical
  unfold Kmat
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, C_sum_J_J]
  simp [ite_smul]

theorem sum_J_smul_Kmat_right (u v : I n) :
    ∑ w, (MvPolynomial.C (J n w v) : PmnR F n r) • Kmat (F := F) (r := r) u w = - OmegaR u v := by
  classical
  unfold Kmat
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, C_sum_J_J']
  simp [ite_smul]

theorem thetaHalf_JThetaT (hr : r ≤ 3) (u v : I n) :
    thetaJthetaT (thetaHalf (F := F) (n := n) (r := r)) u v = JR u v - OmegaR u v := by
  classical
  have hterm : ∀ w z : I n, gmul (thetaHalf u w) (gmul (JR w z) (thetaHalf v z)) =
      (MvPolynomial.C (J n w z) : PmnR F n r) •
        ((if u = w ∧ v = z then (gone : GR F n r) else 0)
          + (1 / 2 : ℚ) • (if u = w then Kmat v z else 0)
          + (1 / 2 : ℚ) • (if v = z then Kmat u w else 0)) := by
    intro w z
    rw [gmul_JR_left, gmul_smul_right, gmul_thetaHalf hr]
  unfold thetaJthetaT
  simp_rw [hterm]
  simp only [smul_add, Finset.sum_add_distrib, smul_comm _ (1 / 2 : ℚ)]
  have e1 : ∑ w : I n, ∑ z : I n, (MvPolynomial.C (J n w z) : PmnR F n r) •
      (if u = w ∧ v = z then (gone : GR F n r) else 0) = JR u v := by
    rw [Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single v]
      · simp [JR_eq]
      · intro z _ hz; simp [Ne.symm hz]
      · simp
    · intro w _ hw
      exact Finset.sum_eq_zero fun z _ => by simp [Ne.symm hw]
    · simp
  have e2 : ∑ w : I n, ∑ z : I n, (1 / 2 : ℚ) • (MvPolynomial.C (J n w z) : PmnR F n r) •
      (if u = w then Kmat (F := F) (r := r) v z else 0) = (1 / 2 : ℚ) • OmegaR v u := by
    rw [Finset.sum_eq_single u]
    · rw [← Finset.smul_sum]
      simp [sum_J_smul_Kmat_left]
    · intro w _ hw
      exact Finset.sum_eq_zero fun z _ => by simp [Ne.symm hw]
    · simp
  have e3 : ∑ w : I n, ∑ z : I n, (1 / 2 : ℚ) • (MvPolynomial.C (J n w z) : PmnR F n r) •
      (if v = z then Kmat (F := F) (r := r) u w else 0) = (1 / 2 : ℚ) • (- OmegaR u v) := by
    rw [Finset.sum_comm, Finset.sum_eq_single v]
    · rw [← Finset.smul_sum]
      simp [sum_J_smul_Kmat_right]
    · intro z _ hz
      exact Finset.sum_eq_zero fun w _ => by simp [Ne.symm hz]
    · simp
  rw [e1, e2, e3, OmegaR_antisymm]
  module

theorem thetaHalf_even (u w : I n) : IsEvenGR (thetaHalf (F := F) (n := n) (r := r) u w) := by
  rw [thetaHalf_apply]
  exact ((HasCard_gone_ite (u = w)).isEven (by norm_num)).add
    (((HasCard_Kmat u w).rsmul _).isEven (by norm_num))

theorem thetaHalf_empty (u w : I n) :
    thetaHalf (F := F) (n := n) (r := r) u w ∅ = if u = w then 1 else 0 := by
  rw [thetaHalf_apply]
  have hK : Kmat (F := F) (r := r) u w ∅ = 0 := HasCard_Kmat u w ∅ (by simp)
  simp only [Pi.add_apply, Pi.smul_apply, hK, smul_zero, add_zero]
  split_ifs <;> simp [gone]

end Multi
end OspN
end OspOddDeformations
