import OspOddDeformations.OspN.Multi.TierB
import OspOddDeformations.OspN.Multi.TierBAut
import OspOddDeformations.OspN.Multi.ThetaSeries

/-!
# Helper lemmas for `Remarks.lean`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

set_option backward.isDefEq.respectTransparency.types false
-- `OspBasis` is a plain `def`, as in `ThetaStarBracket.lean` and `VChiBracket.lean`

variable {F : FermionIndex} {n r : ℕ}

theorem neg_gammaR_odd (u : I n) (i : F.K) :
    HasParity 1 ((-gammaR (F := F) (r := r) : I n → F.K → GR F n r) u i) := by
  simpa using (HasCard_gammaR (F := F) (n := n) (r := r) u i).neg.parity

/-- `V_γ` is onto (`V_{-γ}` is a right inverse). -/
theorem VChi_gammaR_surjective :
    Function.Surjective (VChi (gammaR (F := F) (n := n) (r := r))) := by
  intro a
  refine ⟨VChi (-gammaR) a, ?_⟩
  rw [VChi_comp' _ _ gammaR_odd neg_gammaR_odd, add_neg_cancel, VChi_zero]

/-- A pair of basis vectors at which `[·,·]_{J-Ω}` and `[·,·]_0` differ, when `Ω ≠ 0`. -/
theorem exists_witness_ne (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) :
    ∃ x y : RModM F n r, bracketJM JmOmega x y ≠ bracket0M x y := by
  obtain ⟨u, w, hΩ'⟩ := hΩ
  have hK : Nonempty F.K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    exact hΩ' (by simp [OmegaR])
  obtain ⟨i⟩ := hK
  obtain ⟨T, hT⟩ : ∃ T, OmegaR (F := F) (r := r) u w T ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΩ' (funext hcon)
  refine ⟨gtens gone (eN (Lof u u : OspBasis F n)), gtens gone (eN (Fof w i)), fun h => ?_⟩
  have h2 := witness_diff (F := F) (r := r) u w i
  rw [h, sub_self] at h2
  have h3 := congrFun (neg_eq_zero.mp h2.symm) (Fof u i, T)
  simp only [gtens_apply, emb0_eN, ite_true, mul_one] at h3
  exact hT h3

/-! ## The `κ`-degree filtration on `𝔤_{R_r}` -/

/-- Every component of `κ`-degree `< k` vanishes. -/
def RMin (k : ℕ) (x : RModM F n r) : Prop := ∀ p : RBasisM F n r, p.2.card < k → x p = 0

theorem RMin_bracket0M {j k : ℕ} {x y : RModM F n r} (hx : RMin j x) (hy : RMin k y) :
    RMin (j + k) (bracket0M x y) := by
  rintro ⟨Z, T⟩ hT
  simp only [bracket0M, Finset.sum_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  by_cases hxp : x p = 0
  · simp [hxp]
  by_cases hyq : y q = 0
  · simp [hyq]
  have hp : j ≤ p.2.card := by by_contra h; exact hxp (hx p (by omega))
  have hq : k ≤ q.2.card := by by_contra h; exact hyq (hy q (by omega))
  by_cases hd : Disjoint p.2 q.2
  · by_cases hTe : T = p.2 ∪ q.2
    · exfalso
      rw [hTe, Finset.card_union_of_disjoint hd] at hT
      omega
    · simp [bracket0MBasis, kap, hTe]
  · simp [bracket0MBasis, gs_eq_zero_of_not_disjoint hd]

theorem RMin.eq_zero {k : ℕ} (hk : r < k) {x : RModM F n r} (hx : RMin k x) : x = 0 := by
  funext p
  exact hx p (lt_of_le_of_lt (by simpa using Finset.card_le_univ p.2) hk)

theorem thetaHalf_low (u w : I n) (T : Finset (Fin r)) (hT : T.card < 2) :
    thetaHalf (F := F) (n := n) (r := r) u w T = if u = w then gone T else 0 := by
  rw [thetaHalf_apply]
  have hK : Kmat (F := F) (r := r) u w T = 0 := HasCard_Kmat u w T (by omega)
  simp only [Pi.add_apply, Pi.smul_apply, hK, smul_zero, add_zero]
  split_ifs <;> simp

theorem RMin_Dy (w : I n) (i : F.K) :
    RMin 2 (ThetaStar (thetaHalf (F := F) (n := n) (r := r)) (gtens gone (eN (Fof w i)))
      - gtens gone (eN (Fof w i))) := by
  rintro ⟨Z, T⟩ hT
  rw [ThetaStar_eq_linM, linM_gtens_eN, gsmul_gone, T0_F]
  simp only [Pi.sub_apply, Finset.sum_apply, gtens_apply, thetaHalf_low _ _ _ hT]
  rw [Finset.sum_eq_single w]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem gmul_low (a a' b b' : GR F n r) (T : Finset (Fin r)) (hT : T.card < 2)
    (ha : ∀ A : Finset (Fin r), A.card < 2 → a A = a' A)
    (hb : ∀ B : Finset (Fin r), B.card < 2 → b B = b' B) : gmul a b T = gmul a' b' T := by
  unfold gmul
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs with h
  · have hA : A.card < 2 := lt_of_le_of_lt (Finset.card_le_card (h ▸ Finset.subset_union_left)) hT
    have hB : B.card < 2 := lt_of_le_of_lt (Finset.card_le_card (h ▸ Finset.subset_union_right)) hT
    rw [ha A hA, hb B hB]
  · rfl

theorem gmul_thetaHalf_low (u w b : I n) (T : Finset (Fin r)) (hT : T.card < 2) :
    gmul (thetaHalf (F := F) (n := n) (r := r) u w) (thetaHalf u b) T =
      if w = u ∧ b = u then gone T else 0 := by
  rw [gmul_low _ (if w = u then gone else 0) _ (if b = u then gone else 0) T hT
    (fun A hA => by
      rw [thetaHalf_low _ _ _ hA]
      by_cases h : w = u
      · simp [h]
      · simp [h, Ne.symm h])
    (fun B hB => by
      rw [thetaHalf_low _ _ _ hB]
      by_cases h : b = u
      · simp [h]
      · simp [h, Ne.symm h])]
  by_cases h1 : w = u <;> by_cases h2 : b = u <;>
    simp [h1, h2, gone_gmul, gmul_gone, gmul_zero_left]

theorem RMin_Dx (u : I n) :
    RMin 2 (ThetaStar (thetaHalf (F := F) (n := n) (r := r)) (gtens gone (eN (Lof u u)))
      - gtens gone (eN (Lof u u))) := by
  rintro ⟨Z, T⟩ hT
  rw [ThetaStar_eq_linM, linM_gtens_eN, gsmul_gone, T0_Lof _ thetaHalf_even]
  simp only [Pi.sub_apply, Finset.sum_apply, gtens_apply, gmul_thetaHalf_low _ _ _ _ hT]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [ha]
  · simp

theorem nonempty_K_of_Omega (u w : I n) (h : OmegaR (F := F) (r := r) u w ≠ 0) : Nonempty F.K := by
  by_contra hK
  rw [not_nonempty_iff] at hK
  exact h (by simp [OmegaR])

/-- The witness pair of `ThetaStar_not_aut`: if `Θ_*` preserves `[·,·]_0` on it, then
`Ω_{uw} = 0`. -/
theorem false_of_pair (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v) (u w : I n) (i : F.K)
    (hΩ' : OmegaR (F := F) (r := r) u w ≠ 0)
    (h : bracket0M (ThetaStar Θ (gtens gone (eN (Lof u u : OspBasis F n))))
        (ThetaStar Θ (gtens gone (eN (Fof w i)))) =
      ThetaStar Θ (bracket0M (gtens gone (eN (Lof u u : OspBasis F n)))
        (gtens gone (eN (Fof w i)))))
    : False := by
  rw [thetaStar_bracket Θ hEven hΘ] at h
  have hsub : ∀ P Q : RModM F n r, ThetaStar Θ (P - Q) = ThetaStar Θ P - ThetaStar Θ Q := by
    intro P Q; rw [ThetaStar_eq_linM]; exact linM_sub _ _ _
  have h2 : ThetaStar Θ (gtens (OmegaR u w) (eN (Fof u i))) = 0 := by
    have h3 := hsub (bracketJM JmOmega (gtens gone (eN (Lof u u : OspBasis F n)))
      (gtens gone (eN (Fof w i)))) (bracket0M (gtens gone (eN (Lof u u : OspBasis F n)))
      (gtens gone (eN (Fof w i))))
    rw [h, sub_self, witness_diff, ThetaStar_eq_linM, linM_neg, neg_eq_zero] at h3
    rw [ThetaStar_eq_linM]
    exact h3
  obtain ⟨T, hT⟩ : ∃ T, OmegaR (F := F) (r := r) u w T ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΩ' (funext hcon)
  have hcard : T.card = 2 := by
    by_contra hc
    exact hT (HasCard_OmegaR u w T hc)
  obtain ⟨a, ha⟩ := exists_theta_empty_ne Θ hΘ u
  have h4 := congrFun (gmul_theta_eq_zero_of_ThetaStar Θ _ u i h2 a) T
  rw [gmul_top_apply _ _ T 2 hcard (HasCard_OmegaR u w)] at h4
  exact mul_ne_zero hT ha h4

theorem liftB_eN_eN_gen (B0 : OspBasis F n → OspBasis F n → RModM F n r) (a a' : GR F n r)
    (b b' : OspBasis F n) :
    liftB B0 (gtens a (eN b)) (gtens a' (eN b')) =
      gsmul (gmul a (sigPow (parity b) a')) (B0 b b') := by
  have hv : ∀ W, emb0 (F := F) (n := n) (r := r) (eN b W) ≠ 0 → parity W = parity b :=
    fun W h => by rw [hv_eN b W h]
  rw [liftB_gtens B0 a a' (eN b) (eN b') (parity b) hv, sum2_emb0_eN]

theorem Bbeta_LL (a b c d : I n) :
    Bbeta (F := F) (n := n) (r := r) (Lof a b) (Lof c d) = B0data (Lof a b) (Lof c d) := by
  obtain ⟨p, h, e⟩ := Lof_cases (F := F) a b
  obtain ⟨q, h', e'⟩ := Lof_cases (F := F) c d
  rw [e, e']
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have h0 : ∀ s : Fin r, liftBy (embS s) (0 : OspMod F n) = 0 := fun s => by
    funext k; simp [liftBy]
  have h1 : (kap (∅ : Finset (Fin r)) (0 : OspBasis F n → PmnR F n r) : RModM F n r) = 0 := by
    funext p; simp [kap]
  have h2 : ∀ (a : GR F n r), gsmul a (0 : RModM F n r) = 0 := fun a => by
    funext p
    rw [gsmul_apply_eq, show grComp (0 : RModM F n r) p.1 = 0 from rfl, gmul_zero_right]
    rfl
  simp [Bbeta, GammaSBasis, GammaBasis, h0, h1, h2]

end Multi
end OspN
end OspOddDeformations
