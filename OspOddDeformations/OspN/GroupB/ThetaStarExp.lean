import OspOddDeformations.OspN.Presented.MultiRecovery
import OspOddDeformations.OspN.Multi.TierB
import OspOddDeformations.General.ExpDerivation
import Mathlib.Tactic.NoncommRing

/-!
# `Θ_*` is not of the form `exp(ad Y)` (the text after Prop 5.4)

* The super-Jacobi identity of `[·,·]_0` over `R_r` on basis elements (`jacobi_eP`), pulled back
  from the associative product of `A_0` through the injective `ι_0` (`iota0_scomm`,
  `iotaM_zero_injective`), as `delta_ad_eq_zero_basis` does over `P`. Hence `ad Y` is a
  derivation of `[·,·]_0` for every even `Y` (`bracket0M_derivation`).
* By the general `exp_bilin_of_derivation'` (`General/ExpDerivation.lean`), `exp(ad Y)` is then an
  automorphism of `[·,·]_0` whenever `ad Y` is nilpotent (`exp_adM_aut`); with
  `ThetaStar_not_aut`, if `Ω ≠ 0` then `Θ_* ≠ exp(ad Y)` (`ThetaStar_ne_exp_ad`).
* If `(Θ_* − id)² = 0` and `Ω ≠ 0`, then `Θ_* − id` is not a derivation of `[·,·]_0`
  (`ThetaStar_sub_id_not_derivation`). That the square vanishes for `r ≤ 3` is the paper's and is
  not formalized here; it enters as the hypothesis.
-/

namespace OspOddDeformations
namespace OspN
namespace GroupB

open Bmn (I J)
open Multi Presented General

variable {F : FermionIndex} {n r : ℕ}

/-- The basis element `κ_T W` of `𝔤_{R_r}`. -/
noncomputable def eP (P : RBasisM F n r) : RModM F n r := Pi.single P 1

theorem bracket0M_eP (P Q : RBasisM F n r) : bracket0M (eP P) (eP Q) = bracket0MBasis P Q := by
  simp [bracket0M, eP, Pi.single_apply, Finset.sum_ite_eq']

theorem HomM_eP (P : RBasisM F n r) : HomM (parB P) (eP P) := by
  intro Q hQ
  by_contra h
  have hne : Q ≠ P := fun e => h (e ▸ rfl)
  exact hQ (by simp [eP, hne])

theorem HomM_bracket0MBasis (P Q : RBasisM F n r) :
    HomM (parB P + parB Q) (bracket0MBasis P Q) := by
  intro R hR
  have h1 : R.2 = P.2 ∪ Q.2 := by
    by_contra h; exact hR (by simp [bracket0MBasis, kap, h])
  have h2 : Disjoint P.2 Q.2 := by
    by_contra h; exact hR (by simp [bracket0MBasis, gs_eq_zero_of_not_disjoint h])
  have h3 : bracket0Basis P.1 Q.1 R.1 ≠ 0 := by
    intro h; exact hR (by simp [bracket0MBasis, kap, liftBy, h])
  have h4 := bracket0Basis_degree _ _ _ h3
  simp only [parB, h1, Finset.card_union_of_disjoint h2, Nat.cast_add, h4]
  ring

theorem HomM_bracket0M_eP (P Q : RBasisM F n r) :
    HomM (parB P + parB Q) (bracket0M (eP P) (eP Q)) := by
  rw [bracket0M_eP]; exact HomM_bracket0MBasis P Q

/-- **Super-Jacobi** for `[·,·]_0` over `R_r`, on basis elements. -/
theorem jacobi_eP (P Q R : RBasisM F n r) :
    bracket0M (eP P) (bracket0M (eP Q) (eP R))
      = bracket0M (bracket0M (eP P) (eP Q)) (eP R)
        + gsign (parB P) (parB Q) • bracket0M (eP Q) (bracket0M (eP P) (eP R)) := by
  apply iotaM_zero_injective
  rw [A7b.iotaM_add, A7b.iotaM_rsmul,
    ← iota0_scomm (HomM_eP P) (HomM_bracket0M_eP Q R),
    ← iota0_scomm (HomM_bracket0M_eP P Q) (HomM_eP R),
    ← iota0_scomm (HomM_eP Q) (HomM_bracket0M_eP P R),
    ← iota0_scomm (HomM_eP Q) (HomM_eP R), ← iota0_scomm (HomM_eP P) (HomM_eP Q),
    ← iota0_scomm (HomM_eP P) (HomM_eP R)]
  set a := iotaM 0 (eP P)
  set b := iotaM 0 (eP Q)
  set c := iotaM 0 (eP R)
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (parB P) with hp | hp <;> rcases zmod2_cases (parB Q) with hq | hq <;>
    rcases zmod2_cases (parB R) with hr | hr <;>
    simp only [hp, hq, hr, h11, zero_add, add_zero, gsign_00, gsign_01, gsign_10, gsign_11,
      one_smul, neg_one_smul] <;>
    noncomm_ring

theorem bracket0M_add_left (x x' y : RModM F n r) :
    bracket0M (x + x') y = bracket0M x y + bracket0M x' y := by
  simp [bracket0M, add_mul, add_smul, Finset.sum_add_distrib]

theorem bracket0M_add_right (x y y' : RModM F n r) :
    bracket0M x (y + y') = bracket0M x y + bracket0M x y' := by
  simp [bracket0M, mul_add, add_smul, Finset.sum_add_distrib]

theorem bracket0M_smul_left (c : PmnR F n r) (x y : RModM F n r) :
    bracket0M (c • x) y = c • bracket0M x y := by
  simp [bracket0M, Finset.smul_sum, smul_smul, mul_assoc]

theorem bracket0M_smul_right (c : PmnR F n r) (x y : RModM F n r) :
    bracket0M x (c • y) = c • bracket0M x y := by
  simp [bracket0M, Finset.smul_sum, smul_smul, mul_left_comm]

/-- `[·,·]_0` as a `P_r`-bilinear map. -/
noncomputable def bracket0L :
    RModM F n r →ₗ[PmnR F n r] RModM F n r →ₗ[PmnR F n r] RModM F n r :=
  LinearMap.mk₂ (PmnR F n r) bracket0M bracket0M_add_left bracket0M_smul_left
    bracket0M_add_right bracket0M_smul_right

theorem bracket0L_apply (x y : RModM F n r) : bracket0L x y = bracket0M x y := rfl

theorem gsign_zero_left (q : ZMod 2) : gsign 0 q = 1 := by
  unfold gsign; simp

theorem jacobi_even_eP (P : RBasisM F n r) (hP : parB P = 0) (x z : RModM F n r) :
    bracket0M (eP P) (bracket0M x z)
      = bracket0M (bracket0M (eP P) x) z + bracket0M x (bracket0M (eP P) z) := by
  have h : (bracket0L (F := F) (n := n) (r := r)).compr₂ (bracket0L (eP P))
      = bracket0L.comp (bracket0L (eP P)) + bracket0L.compl₂ (bracket0L (eP P)) := by
    refine LinearMap.ext_basis (Pi.basisFun (PmnR F n r) (RBasisM F n r))
      (Pi.basisFun (PmnR F n r) (RBasisM F n r)) fun Q R => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.compl₂_apply, Pi.basisFun_apply, bracket0L_apply]
    have := jacobi_eP P Q R
    simp only [eP, hP, gsign_zero_left, one_smul] at this
    exact this
  exact LinearMap.congr_fun₂ h x z

/-- `ad Y` is a derivation of `[·,·]_0` for every even `Y` (super-Jacobi). -/
theorem bracket0M_derivation (Y : RModM F n r) (hY : HomM 0 Y) (x z : RModM F n r) :
    bracket0M Y (bracket0M x z) = bracket0M (bracket0M Y x) z + bracket0M x (bracket0M Y z) := by
  have hY' : Y = ∑ P, Y P • eP P := by
    conv_lhs => rw [← Finset.univ_sum_single Y]
    refine Finset.sum_congr rfl fun P _ => ?_
    funext Q
    by_cases h : Q = P <;> simp [eP, h]
  simp only [← bracket0L_apply]
  rw [hY']
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases hP : Y P = 0
  · simp [hP]
  · simp only [bracket0L_apply]
    rw [jacobi_even_eP P (hY P hP)]

/-- `ad Y` for `[·,·]_0`, as a `ℚ`-linear endomorphism of `𝔤_{R_r}`. -/
noncomputable def adM (Y : RModM F n r) : Module.End ℚ (RModM F n r) :=
  (bracket0L Y).restrictScalars ℚ

/-- `exp(ad Y)` is an automorphism of `[·,·]_0` for even `Y` with `ad Y` nilpotent. -/
theorem exp_adM_aut (Y : RModM F n r) (hY : HomM 0 Y) (hnil : IsNilpotent (adM Y))
    (x y : RModM F n r) :
    IsNilpotent.exp (adM Y) (bracket0M x y)
      = bracket0M (IsNilpotent.exp (adM Y) x) (IsNilpotent.exp (adM Y) y) :=
  exp_bilin_of_derivation' (bracket0L.restrictScalars₁₂ ℚ ℚ) (adM Y)
    (fun a b => bracket0M_derivation Y hY a b) hnil x y

/-- **The text after Prop 5.4**: if `Ω ≠ 0`, then `Θ_*` is not `exp(ad Y)` for any even `Y` with
`ad Y` nilpotent. -/
theorem ThetaStar_ne_exp_ad (Θ : I n → I n → GR F n r) (hEven : IsEvenMatrix Θ)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v)
    (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0)
    (Y : RModM F n r) (hY : HomM 0 Y) (hnil : IsNilpotent (adM Y)) :
    ⇑(IsNilpotent.exp (adM Y)) ≠ ThetaStar Θ := by
  intro h
  apply ThetaStar_not_aut Θ hEven hΘ hΩ
  intro x y
  rw [← h]
  exact (exp_adM_aut Y hY hnil x y).symm

/-- `Θ_* − id`, as a `ℚ`-linear endomorphism. -/
noncomputable def ThetaStarSubId (Θ : I n → I n → GR F n r) : Module.End ℚ (RModM F n r) where
  toFun x := ThetaStar Θ x - x
  map_add' x y := by rw [ThetaStar_eq_linM, linM_add]; abel
  map_smul' c x := by rw [ThetaStar_eq_linM, linM_rsmul, RingHom.id_apply, smul_sub]

/-- **The text after Prop 5.4**, second statement: if `(Θ_* − id)² = 0` and `Ω ≠ 0`, then
`Θ_* − id` is not a derivation of `[·,·]_0`. -/
theorem ThetaStar_sub_id_not_derivation (Θ : I n → I n → GR F n r) (hEven : IsEvenMatrix Θ)
    (hΘ : ∀ u v, thetaJthetaT Θ u v = JR u v - OmegaR u v)
    (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) (hsq : ThetaStarSubId Θ ^ 2 = 0) :
    ¬ ∀ x y : RModM F n r, ThetaStarSubId Θ (bracket0M x y)
      = bracket0M (ThetaStarSubId Θ x) y + bracket0M x (ThetaStarSubId Θ y) := by
  intro hder
  apply ThetaStar_not_aut Θ hEven hΘ hΩ
  intro x y
  have hexp : ∀ z, IsNilpotent.exp (ThetaStarSubId Θ) z = ThetaStar Θ z := by
    intro z
    rw [IsNilpotent.exp_eq_sum hsq]
    simp [Finset.sum_range_succ, ThetaStarSubId]
  have := exp_bilin_of_derivation' (bracket0L.restrictScalars₁₂ ℚ ℚ) (ThetaStarSubId Θ) hder
    ⟨2, hsq⟩ x y
  rw [hexp, hexp, hexp] at this
  exact this.symm

end GroupB
end OspN
end OspOddDeformations
