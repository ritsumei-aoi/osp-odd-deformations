import OspOddDeformations.OspN.Presented.MultiLiftChange
import OspOddDeformations.OspN.Presented.MultiRealize
import OspOddDeformations.OspN.Presented.MultiBase
import Mathlib.Tactic.LinearCombination

/-!
# Thm 5.3 in the presented `A_β` over `R_r`

* `ι` is `R_r`-linear: `ι(a · w) = embG(a) ι(w)` (`iotaM_gsmul`), so with Prop 5.2
  (`MultiLiftChange.lean`), `Φ_r(ι_β z) = ι_0(U z)` for every `z ∈ 𝔤_{R_r}` (`untwistR_iotaM`);
* in `A_0`, the supercommutator of `ι_0 x` and `ι_0 y`, for homogeneous `x`, `y`, is
  `ι_0([x,y]_0)` with the coordinate-level `[·,·]_0` (`iota0_scomm`, from Lemma 3.2 over `R_r`,
  `MultiBase.lean`);
* hence, through the isomorphism `Φ_r` and the coordinate-level `[UX,UY]_0 = U[X,Y]_β`,
  **Thm 5.3** in `A_β`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ} (β' : Fin r → I n → F.K → Multi.PmnR F n r)

theorem iotaM_smulP (c : Multi.PmnR F n r) (x : Multi.RModM F n r) :
    iotaM β' (c • x) = c • iotaM β' x := by
  simp only [iotaM, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- `ι(a · w) = embG(a) ι(w)`. -/
theorem iotaM_gsmul (a : Multi.GR F n r) (w : Multi.RModM F n r) :
    iotaM β' (Multi.gsmul a w) = embG β' a * iotaM β' w := by
  have L : iotaM β' (Multi.gsmul a w)
      = ∑ W, ∑ A, ∑ B, (Multi.gs A B • (a A * w (W, B))) • (κS β' (A ∪ B) * XpM β' W) := by
    simp only [iotaM, Fintype.sum_prod_type, Multi.gsmul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have R : embG β' a * iotaM β' w
      = ∑ W, ∑ A, ∑ B, (Multi.gs A B • (a A * w (W, B))) • (κS β' (A ∪ B) * XpM β' W) := by
    rw [embG, iotaM, Fintype.sum_prod_type, Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun A _ =>
      Finset.sum_congr rfl fun B _ => ?_
    rw [smul_mul_smul_comm, ← mul_assoc, κS_mul_κS, smul_mul_assoc, smul_comm (a A * _),
      smul_assoc]
  rw [L, R]

theorem untwistR_κS (S : Finset (Fin r)) : untwistR F n r (κS _ S) = κS 0 S := by
  simp only [κS, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, untwistR_κ]

/-- `Φ_r(ι_β z) = ι_0(U z)` (Prop 5.2 extended `R_r`-linearly). -/
theorem untwistR_iotaM (z : Multi.RModM F n r) :
    untwistR F n r (iotaM (Multi.betaR F n r) z) = iotaM 0 (Multi.UM Multi.thetaSeries z) := by
  have hU : Multi.UM (Multi.thetaSeries (F := F) (n := n) (r := r)) z
      = ∑ p : Multi.RBasisM F n r,
          z p • Multi.gsmul (Multi.gmono p.2 1) (Multi.UM Multi.thetaSeries (eM p.1)) := by
    simp only [A7b.UM_eM]
    rfl
  rw [hU, A7b.iotaM_sum, iotaM, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_mul, untwistR_κS, untwistR_XpM, iotaM_smulP, iotaM_gsmul,
    embG_gmono, one_smul]

/-! ## Signs -/

/-- `(−1)^p` for `p ∈ ℤ/2`. -/
def sg (p : ZMod 2) : ℚ := if p = 1 then -1 else 1

theorem sg_sq (p : ZMod 2) : sg p * sg p = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem zmod2_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by revert p; decide

theorem sg_add (p q : ZMod 2) : sg (p + q) = sg p * sg q := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod2_cases p with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl <;>
    simp [sg, h11, h01]

theorem gsign_eq_sg (p q : ZMod 2) : gsign p q = sg (p * q) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod2_cases p with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl <;>
    simp [sg, gsign, h01]

theorem neg_one_pow_eq_sg (m : ℕ) : (-1 : ℚ) ^ m = sg (m : ZMod 2) := by
  induction m with
  | zero => simp [sg]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, sg_add]
    simp [sg]

theorem sg_pow (p : ZMod 2) (k : ℕ) : sg p ^ k = sg (p * k) := by
  induction k with
  | zero => simp [sg]
  | succ k ih => rw [pow_succ, ih, ← sg_add, Nat.cast_succ, mul_add, mul_one]

theorem sign_identity (a b : ZMod 2) (k l : ℕ) :
    gsign (a + k) (b + l) * sg b ^ k * (-1 : ℚ) ^ (k * l) = sg a ^ l * gsign a b := by
  rw [gsign_eq_sg, gsign_eq_sg, sg_pow, sg_pow, neg_one_pow_eq_sg, ← sg_add, ← sg_add, ← sg_add]
  congr 1
  have key : ∀ a b k l : ZMod 2, (a + k) * (b + l) + b * k + k * l = a * l + a * b := by decide
  push_cast
  exact key a b k l

theorem sg_pow_eq (p : ZMod 2) (l : ℕ) : sg p ^ l = (-1 : ℚ) ^ (l * p.val) := by
  rw [neg_one_pow_eq_sg, sg_pow, Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]

/-! ## `κ` against the lifts of `A_0` -/

theorem κM_mul_X0M (t : Fin r) (W : OspBasis F n) :
    κM _ _ 0 t * X0M F n r W = sg (OspN.parity W) • (X0M F n r W * κM _ _ 0 t) := by
  have hb : ∀ u, κM (jR F n r) (gR F n r) 0 t * BPM F n r u = BPM F n r u * κM _ _ 0 t :=
    fun u => κM_mul_bM t u
  have ha : ∀ i, κM (jR F n r) (gR F n r) 0 t * aPM F n r i = -(aPM F n r i * κM _ _ 0 t) :=
    fun i => κM_mul_aM t i
  have hBB : ∀ u v, κM (jR F n r) (gR F n r) 0 t * (BPM F n r u * BPM F n r v)
      = BPM F n r u * BPM F n r v * κM _ _ 0 t := fun u v => by
    rw [← mul_assoc, hb, mul_assoc, hb, ← mul_assoc]
  have haa : ∀ i j, κM (jR F n r) (gR F n r) 0 t * (aPM F n r i * aPM F n r j)
      = aPM F n r i * aPM F n r j * κM _ _ 0 t := fun i j => by
    rw [← mul_assoc, ha, neg_mul, mul_assoc, ha, mul_neg, neg_neg, ← mul_assoc]
  have haB : ∀ i u, κM (jR F n r) (gR F n r) 0 t * (aPM F n r i * BPM F n r u)
      = -(aPM F n r i * BPM F n r u * κM _ _ 0 t) := fun i u => by
    rw [← mul_assoc, ha, neg_mul, mul_assoc, hb, ← mul_assoc]
  have hBa : ∀ u i, κM (jR F n r) (gR F n r) 0 t * (BPM F n r u * aPM F n r i)
      = -(BPM F n r u * aPM F n r i * κM _ _ 0 t) := fun u i => by
    rw [← mul_assoc, hb, mul_assoc, ha, mul_neg, ← mul_assoc]
  match W with
  | .inl ⟨(u, v), _⟩ =>
    simp only [X0M, L0M, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hBB]
    simp [sg, OspN.parity]
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [X0M, S0M, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, haa]
    simp [sg, OspN.parity]
  | .inr (.inr (u, i)) =>
    simp only [X0M, F0M, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, haB, hBa]
    simp [sg, OspN.parity, smul_neg]

theorem prod_mul_X0M (l : List (Fin r)) (W : OspBasis F n) :
    (l.map (κM (jR F n r) (gR F n r) 0)).prod * X0M F n r W
      = sg (OspN.parity W) ^ l.length • (X0M F n r W * (l.map (κM _ _ 0)).prod) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc, κM_mul_X0M,
      smul_mul_assoc, smul_smul, mul_assoc, List.length_cons, pow_succ, mul_comm (sg _ ^ _)]

theorem κS_mul_X0M (T : Finset (Fin r)) (W : OspBasis F n) :
    κS 0 T * X0M F n r W = sg (OspN.parity W) ^ T.card • (X0M F n r W * κS 0 T) := by
  rw [κS, prod_mul_X0M, Finset.length_sort]

theorem X0M_mul_κS (T : Finset (Fin r)) (W : OspBasis F n) :
    X0M F n r W * κS 0 T = sg (OspN.parity W) ^ T.card • (κS 0 T * X0M F n r W) := by
  rw [κS_mul_X0M, smul_smul, ← mul_pow, sg_sq, one_pow, one_smul]

/-! ## The supercommutator of `ι_0 x` and `ι_0 y` -/

theorem iotaE_zero_eq (u : OspMod F n) : A7b.iotaE 0 u = iota0M F n r u := by
  simp only [A7b.iotaE, iota0M, XpM_zero]

theorem iotaM_kap (S : Finset (Fin r)) (u : OspMod F n) :
    iotaM β' (Multi.kap S (Multi.liftBy Multi.emb0 u)) = κS β' S * A7b.iotaE β' u := by
  rw [iotaM, Fintype.sum_prod_type, A7b.iotaE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_eq_single S]
  · simp [Multi.kap, Multi.liftBy]
  · intro T _ hT; simp [Multi.kap, hT]
  · intro h; exact absurd (Finset.mem_univ S) h

/-- The basis element `κ_T W^0` of `A_0`. -/
noncomputable def eB (p : Multi.RBasisM F n r) : AM F n r 0 := κS 0 p.2 * X0M F n r p.1

/-- The parity of a basis element of `𝔤_{R_r}`. -/
def parB (p : Multi.RBasisM F n r) : ZMod 2 := OspN.parity p.1 + (p.2.card : ZMod 2)

theorem eB_scomm (P Q : Multi.RBasisM F n r) :
    eB P * eB Q - gsign (parB P) (parB Q) • (eB Q * eB P)
      = iotaM 0 (Multi.bracket0MBasis P Q) := by
  obtain ⟨W, T⟩ := P
  obtain ⟨W', T'⟩ := Q
  have hPQ : eB (W, T) * eB (W', T')
      = (sg (OspN.parity W) ^ T'.card * Multi.gs T T') •
          (κS 0 (T ∪ T') * (X0M F n r W * X0M F n r W')) := by
    simp only [eB]
    rw [mul_assoc, ← mul_assoc (X0M F n r W), X0M_mul_κS, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, ← mul_assoc, κS_mul_κS]
    simp only [smul_mul_assoc, smul_smul, mul_assoc]
  have hQP : eB (W', T') * eB (W, T)
      = (sg (OspN.parity W') ^ T.card * ((-1 : ℚ) ^ (T.card * T'.card) * Multi.gs T T')) •
          (κS 0 (T ∪ T') * (X0M F n r W' * X0M F n r W)) := by
    simp only [eB]
    rw [mul_assoc, ← mul_assoc (X0M F n r W'), X0M_mul_κS, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, ← mul_assoc, κS_mul_κS, Multi.gs_comm T' T, Finset.union_comm]
    simp only [smul_mul_assoc, smul_smul, mul_assoc]
    congr 1
    ring
  have hbase := base_realizationM F n r W W'
  simp only [scomm] at hbase
  rw [hPQ, hQP, Multi.bracket0MBasis, A7b.iotaM_rsmul, iotaM_kap, iotaE_zero_eq, ← hbase,
    smul_smul]
  simp only [parB]
  rw [mul_sub, smul_sub, mul_smul_comm, smul_smul]
  congr 1
  · congr 1
    rw [sg_pow_eq]
  · congr 1
    have := sign_identity (OspN.parity W) (OspN.parity W') T.card T'.card
    rw [← sg_pow_eq]
    linear_combination (Multi.gs T T') * this

/-- `x ∈ 𝔤_{R_r}` is homogeneous of parity `p`. -/
def HomM (p : ZMod 2) (x : Multi.RModM F n r) : Prop := ∀ P, x P ≠ 0 → parB P = p

theorem iotaM_zero_eq_sum (x : Multi.RModM F n r) : iotaM 0 x = ∑ P, x P • eB P := by
  simp only [iotaM, eB, XpM_zero]

/-- The supercommutator of `ι_0 x` and `ι_0 y`, `x`, `y` homogeneous, is `ι_0([x,y]_0)`. -/
theorem iota0_scomm {p q : ZMod 2} {x y : Multi.RModM F n r} (hx : HomM p x) (hy : HomM q y) :
    iotaM 0 x * iotaM 0 y - gsign p q • (iotaM 0 y * iotaM 0 x)
      = iotaM 0 (Multi.bracket0M x y) := by
  rw [iotaM_zero_eq_sum, iotaM_zero_eq_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun Q P => y Q • eB Q * (x P • eB P)),
    Finset.smul_sum, ← Finset.sum_sub_distrib, Multi.bracket0M, A7b.iotaM_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, A7b.iotaM_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [iotaM_smulP, smul_mul_smul_comm, smul_mul_smul_comm, smul_comm (gsign p q),
    mul_comm (y Q) (x P), ← smul_sub]
  by_cases hP : x P = 0
  · simp [hP]
  by_cases hQ : y Q = 0
  · simp [hQ]
  rw [← hx P hP, ← hy Q hQ, eB_scomm]

theorem HomM_UM_eM (X : OspBasis F n) :
    HomM (OspN.parity X) (Multi.UM (r := r) Multi.thetaSeries (eM X)) := by
  rintro ⟨W, T⟩ hne
  rw [A7b.UM_eM] at hne
  have hp := Multi.uMat_parity Multi.thetaSeries (Multi.thetaSeries_spec.1) X W T
  have hT : (T.card : ZMod 2) = OspN.parity X + OspN.parity W := by
    by_contra h
    exact hne (hp h)
  simp only [parB, hT]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [add_comm (OspN.parity X), ← add_assoc, h2, zero_add]

theorem untwistR_rat_smul (q : ℚ) (x : AM F n r (Multi.betaR F n r)) :
    untwistR F n r (q • x) = q • untwistR F n r x := by
  rw [← algebraMap_smul (Multi.PmnR F n r) q x, map_smul, algebraMap_smul]

/-- **Thm 5.3** in the presented `A_β`. -/
theorem recoveryM (X Y : OspBasis F n) :
    scomm X Y (XpM (Multi.betaR F n r) X) (XpM (Multi.betaR F n r) Y)
      = iotaM (Multi.betaR F n r) (Multi.bracketBetaM (eM X) (eM Y)) := by
  apply (untwistR F n r).injective
  rw [untwistR_iotaM, ← Multi.intertwining_thetaSeries,
    ← iota0_scomm (HomM_UM_eM X) (HomM_UM_eM Y), ← untwistR_XpM, ← untwistR_XpM,
    scomm, map_sub, map_mul, untwistR_rat_smul, map_mul]

/-- `ι_β` is injective over `R_r`. -/
theorem iotaM_beta_injective :
    Function.Injective (iotaM (F := F) (n := n) (r := r) (Multi.betaR F n r)) := by
  intro x y h
  apply (Multi.UM_thetaSeries_bijective (F := F) (n := n) (r := r)).1
  apply iotaM_zero_injective
  rw [← untwistR_iotaM, ← untwistR_iotaM, h]

/-- **Thm 5.3**: `[X,Y]_β` is the unique element whose `ι_β` is the supercommutator of the
lifts, and `U` carries it to `[UX,UY]_0`. -/
theorem bracketBetaM_unique (X Y : OspBasis F n) :
    (∃! z : Multi.RModM F n r,
      iotaM (Multi.betaR F n r) z
        = scomm X Y (XpM (Multi.betaR F n r) X) (XpM (Multi.betaR F n r) Y)) ∧
    Multi.UM (r := r) Multi.thetaSeries (Multi.bracketBetaM (eM X) (eM Y))
      = Multi.bracket0M (Multi.UM Multi.thetaSeries (eM X)) (Multi.UM Multi.thetaSeries (eM Y)) :=
  ⟨⟨Multi.bracketBetaM (eM X) (eM Y), (recoveryM X Y).symm,
    fun _ hz => iotaM_beta_injective (hz.trans (recoveryM X Y))⟩,
   (Multi.intertwining_thetaSeries _ _).symm⟩

end Presented
end OspN
end OspOddDeformations
