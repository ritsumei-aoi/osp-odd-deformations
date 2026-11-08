import OspOddDeformations.OspN.Multi.LinM
import OspOddDeformations.OspN.Multi.CompFormulas
import OspOddDeformations.OspN.Multi.Factorization

/-!
# `liftB` on vectors `gtens a v`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem grComp_gsmul (a : GR F n r) (w : RModM F n r) (W : OspBasis F n) :
    grComp (gsmul a w) W = gmul a (grComp w W) := rfl

theorem grComp_smulP (c : PmnR F n r) (f : RModM F n r) (W : OspBasis F n) :
    grComp (c • f) W = c • grComp f W := rfl

theorem liftB_gtens (B0 : OspBasis F n → OspBasis F n → RModM F n r) (a a' : GR F n r)
    (v v' : OspMod F n) (π : ZMod 2)
    (hv : ∀ W, emb0 (F := F) (n := n) (r := r) (v W) ≠ 0 → parity W = π) :
    liftB B0 (gtens a v) (gtens a' v') = gsmul (gmul a (sigPow π a'))
      (∑ W : OspBasis F n, ∑ W' : OspBasis F n,
        (emb0 (F := F) (n := n) (r := r) (v W) * emb0 (v' W')) • B0 W W') := by
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_liftB, grComp_gsmul, grComp_sum]
  simp only [grComp_sum, grComp_smulP, gmul_sum_right, grComp_gtens]
  refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun W' _ => ?_
  by_cases h : emb0 (F := F) (n := n) (r := r) (v W) = 0
  · simp only [sigPow_smul, gmul_smul_right, h, zero_smul, smul_zero,
      zero_mul, gmul_zero_left, gmul_zero_right]
  · rw [hv W h]
    simp only [sigPow_smul, gmul_smul_right, gmul_smul_left, smul_smul, mul_comm (emb0 (v' W'))]

theorem liftB_add_left (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x x' y : RModM F n r) :
    liftB B0 (x + x') y = liftB B0 x y + liftB B0 x' y := by
  unfold liftB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.add_apply, add_mul, add_smul]

theorem liftB_add_right (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y y' : RModM F n r) :
    liftB B0 x (y + y') = liftB B0 x y + liftB B0 x y' := by
  unfold liftB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.add_apply, mul_add, add_smul]

theorem liftB_zero_left (B0 : OspBasis F n → OspBasis F n → RModM F n r) (y : RModM F n r) :
    liftB B0 0 y = 0 := by unfold liftB; simp

theorem liftB_zero_right (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x : RModM F n r) :
    liftB B0 x 0 = 0 := by unfold liftB; simp

theorem liftB_neg_left (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r) :
    liftB B0 (-x) y = - liftB B0 x y := by
  unfold liftB
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.neg_apply, neg_mul, neg_smul]

theorem liftB_neg_right (B0 : OspBasis F n → OspBasis F n → RModM F n r) (x y : RModM F n r) :
    liftB B0 x (-y) = - liftB B0 x y := by
  unfold liftB
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.neg_apply, mul_neg, neg_smul]

theorem liftB_rsmul_left (B0 : OspBasis F n → OspBasis F n → RModM F n r) (c : ℚ)
    (x y : RModM F n r) : liftB B0 (c • x) y = c • liftB B0 x y := by
  unfold liftB
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_mul_assoc, smul_assoc]

theorem liftB_rsmul_right (B0 : OspBasis F n → OspBasis F n → RModM F n r) (c : ℚ)
    (x y : RModM F n r) : liftB B0 x (c • y) = c • liftB B0 x y := by
  unfold liftB
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, mul_smul_comm, smul_assoc]

theorem liftB_sum_left {ι : Type*} (B0 : OspBasis F n → OspBasis F n → RModM F n r)
    (s : Finset ι) (f : ι → RModM F n r) (y : RModM F n r) :
    liftB B0 (∑ i ∈ s, f i) y = ∑ i ∈ s, liftB B0 (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [liftB_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, liftB_add_left, ih]

theorem liftB_sum_right {ι : Type*} (B0 : OspBasis F n → OspBasis F n → RModM F n r)
    (x : RModM F n r) (s : Finset ι) (f : ι → RModM F n r) :
    liftB B0 x (∑ i ∈ s, f i) = ∑ i ∈ s, liftB B0 x (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [liftB_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, liftB_add_right, ih]

/-- The base bracket as a `liftB`. -/
noncomputable def B0data : OspBasis F n → OspBasis F n → RModM F n r :=
  fun Z Z' => gtens gone (bracket0Basis Z Z')

theorem bracket0M_eq_liftB : bracket0M (F := F) (n := n) (r := r) = liftB B0data := by
  funext x y
  refine RModM_ext_grComp fun V => ?_
  rw [grComp_bracket0M, grComp_liftB]
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
  rw [B0data, grComp_gtens, gmul_smul_right, gmul_gone]

/-- **Vector form of the reduction.** -/
theorem lift_intertwine_vec (A0 C0 : OspBasis F n → RModM F n r)
    (B1 B2 : OspBasis F n → OspBasis F n → RModM F n r)
    (hA : ∀ Z W, HasParity (parity Z + parity W) (grComp (A0 Z) W))
    (hvec : ∀ Z Z', liftB B1 (A0 Z) (A0 Z') = linM C0 (B2 Z Z')) (x y : RModM F n r) :
    liftB B1 (linM A0 x) (linM A0 y) = linM C0 (liftB B2 x y) := by
  refine lift_intertwine A0 C0 B1 B2 hA (fun Z Z' V => ?_) x y
  have h := congrArg (fun f => grComp f V) (hvec Z Z')
  simpa only [grComp_liftB, grComp_linM] using h

theorem gtens_add_right (a : GR F n r) (v w : OspMod F n) :
    gtens a (v + w) = gtens a v + gtens a w := by
  funext p; simp [gtens_apply, mul_add]

theorem gtens_zero_right (a : GR F n r) : gtens a (0 : OspMod F n) = 0 := by
  funext p; simp [gtens_apply]

theorem gtens_sum_right {ι : Type*} (a : GR F n r) (s : Finset ι) (f : ι → OspMod F n) :
    gtens a (∑ i ∈ s, f i) = ∑ i ∈ s, gtens a (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gtens_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gtens_add_right, ih]

theorem gtens_pmn_smul (a : GR F n r) (c : Pmn F n) (v : OspMod F n) :
    gtens a (c • v) = emb0 (r := r) c • gtens a v := by
  funext p; simp [gtens_apply]; ring

theorem gtens_rsmul_right (a : GR F n r) (q : ℚ) (v : OspMod F n) :
    gtens a (q • v) = q • gtens a v := by
  funext p; simp [gtens_apply, Algebra.smul_def]; ring

theorem liftB0_gtens (a a' : GR F n r) (v v' : OspMod F n) (π : ZMod 2)
    (hv : ∀ W, emb0 (F := F) (n := n) (r := r) (v W) ≠ 0 → parity W = π) :
    liftB B0data (gtens a v) (gtens a' v') = gtens (gmul a (sigPow π a')) (bracket0 v v') := by
  rw [liftB_gtens _ _ _ _ _ _ hv, ← gsmul_gone_gtens]
  congr 1
  unfold bracket0
  simp only [gtens_sum_right, gtens_pmn_smul, B0data]
  refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun W' _ => ?_
  simp only [map_mul]

end Multi
end OspN
end OspOddDeformations
