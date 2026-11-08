import OspOddDeformations.OspN.Multi.Lift
import OspOddDeformations.OspN.Multi.Parity

/-!
# Calculus of `linM` on vectors `gtens a v`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem RModM_ext_grComp {f g : RModM F n r} (h : ∀ V, grComp f V = grComp g V) : f = g := by
  funext ⟨V, T⟩
  exact congrFun (h V) T

theorem linM_add (A0 : OspBasis F n → RModM F n r) (x y : RModM F n r) :
    linM A0 (x + y) = linM A0 x + linM A0 y := by
  unfold linM; simp [add_smul, Finset.sum_add_distrib]

theorem linM_zero (A0 : OspBasis F n → RModM F n r) : linM A0 0 = 0 := by
  unfold linM; simp

theorem linM_sub (A0 : OspBasis F n → RModM F n r) (x y : RModM F n r) :
    linM A0 (x - y) = linM A0 x - linM A0 y := by
  unfold linM; simp [sub_smul, Finset.sum_sub_distrib]

theorem linM_neg (A0 : OspBasis F n → RModM F n r) (x : RModM F n r) :
    linM A0 (-x) = - linM A0 x := by
  unfold linM; simp

theorem linM_rsmul (A0 : OspBasis F n → RModM F n r) (q : ℚ) (x : RModM F n r) :
    linM A0 (q • x) = q • linM A0 x := by
  unfold linM
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  funext c
  simp

theorem linM_sum {ι : Type*} (A0 : OspBasis F n → RModM F n r) (s : Finset ι)
    (f : ι → RModM F n r) : linM A0 (∑ i ∈ s, f i) = ∑ i ∈ s, linM A0 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [linM_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, linM_add, ih]

theorem gsmul_gtens (a b : GR F n r) (v : OspMod F n) :
    gsmul a (gtens b v) = gtens (gmul a b) v := by
  funext p
  rw [gsmul_apply_eq, grComp_gtens, gmul_smul_right]
  simp [gtens_apply, mul_comm]

theorem gsmul_sum_right {ι : Type*} (a : GR F n r) (s : Finset ι) (f : ι → RModM F n r) :
    gsmul a (∑ i ∈ s, f i) = ∑ i ∈ s, gsmul a (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    funext p
    have e : grComp (0 : RModM F n r) p.1 = 0 := rfl
    rw [Finset.sum_empty, gsmul_apply_eq, e, gmul_zero_right]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gsmul_add_right, ih]

theorem gsmul_neg_right (a : GR F n r) (w : RModM F n r) : gsmul a (-w) = - gsmul a w := by
  funext p
  have e : grComp (-w) p.1 = - grComp w p.1 := rfl
  rw [gsmul_apply_eq, e, gmul_neg_right]; rfl

theorem gsmul_rsmul_right (a : GR F n r) (q : ℚ) (w : RModM F n r) :
    gsmul a (q • w) = q • gsmul a w := by
  funext p
  have e : grComp (q • w) p.1 = q • grComp w p.1 := rfl
  rw [gsmul_apply_eq, e, gmul_rsmul_right]; rfl

theorem linM_gtens (A0 : OspBasis F n → RModM F n r) (a : GR F n r) (v : OspMod F n) :
    linM A0 (gtens a v) = gsmul a (∑ Y : OspBasis F n, emb0 (r := r) (v Y) • A0 Y) := by
  refine RModM_ext_grComp fun W => ?_
  rw [grComp_linM]
  change _ = gmul a (grComp (∑ Y : OspBasis F n, emb0 (r := r) (v Y) • A0 Y) W)
  have : grComp (∑ Y : OspBasis F n, emb0 (r := r) (v Y) • A0 Y) W
      = ∑ Y : OspBasis F n, emb0 (r := r) (v Y) • grComp (A0 Y) W := by
    rw [grComp_sum]; rfl
  rw [this, gmul_sum_right]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [grComp_gtens, gmul_smul_left, gmul_smul_right]

theorem sum_emb0_eN (A0 : OspBasis F n → RModM F n r) (b : OspBasis F n) :
    ∑ Y : OspBasis F n, emb0 (r := r) (eN b Y) • A0 Y = A0 b := by
  rw [Finset.sum_eq_single b]
  · rw [emb0_eN, ite_eq_left rfl, one_smul]
  · intro Y _ hY
    rw [emb0_eN, ite_eq_right hY, zero_smul]
  · simp

theorem linM_gtens_eN (A0 : OspBasis F n → RModM F n r) (a : GR F n r) (b : OspBasis F n) :
    linM A0 (gtens a (eN b)) = gsmul a (A0 b) := by
  rw [linM_gtens, sum_emb0_eN]

theorem gtens_neg_right (a : GR F n r) (v : OspMod F n) : gtens a (-v) = - gtens a v := by
  funext p; simp [gtens_apply]

/-- A basis map that is the identity on the `S`-symbols. -/
def SCompat (A0 : OspBasis F n → RModM F n r) : Prop :=
  ∀ (i j : F.K) (h : F.key i < F.key j),
    A0 (Sum.inr (Sum.inl ⟨(i, j), h⟩)) = gtens gone (Sof i j)

theorem sum_emb0_Sof (A0 : OspBasis F n → RModM F n r) (hS : SCompat A0) (i j : F.K) :
    ∑ Y : OspBasis F n, emb0 (r := r) (Sof i j Y) • A0 Y = gtens gone (Sof i j) := by
  rcases lt_trichotomy (F.key i) (F.key j) with h | h | h
  · have e : (Sof i j : OspMod F n) = eN (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) :=
      Sof_of_lt h
    conv_lhs => rw [e]
    exact (sum_emb0_eN A0 _).trans (hS i j h)
  · have e : (Sof i j : OspMod F n) = 0 := by
      unfold Sof
      have h1 : ¬ F.key i < F.key j := by omega
      have h2 : ¬ F.key j < F.key i := by omega
      simp only [h1, h2, ↓reduceDIte]
    rw [e]
    funext p
    simp [gtens_apply]
  · have h' : F.key j < F.key i := h
    have e : (Sof i j : OspMod F n) = - Sof j i := Sof_antisymm i j
    have e2 : (Sof j i : OspMod F n) = eN (Sum.inr (Sum.inl ⟨(j, i), h'⟩) : OspBasis F n) :=
      Sof_of_lt h'
    have hsum : ∑ Y : OspBasis F n, emb0 (r := r) ((-eN (Sum.inr (Sum.inl ⟨(j, i), h'⟩) :
        OspBasis F n) : OspMod F n) Y) • A0 Y = - A0 (Sum.inr (Sum.inl ⟨(j, i), h'⟩)) := by
      rw [← sum_emb0_eN A0 (Sum.inr (Sum.inl ⟨(j, i), h'⟩)), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun Y _ => ?_
      simp [neg_smul]
    calc ∑ Y : OspBasis F n, emb0 (r := r) (Sof i j Y) • A0 Y
        = - A0 (Sum.inr (Sum.inl ⟨(j, i), h'⟩)) := by
          conv_lhs => rw [e, e2]
          exact hsum
      _ = - gtens gone (Sof j i) := by rw [hS j i h']
      _ = gtens gone (Sof i j) := by rw [e, gtens_neg_right]

end Multi
end OspN
end OspOddDeformations
