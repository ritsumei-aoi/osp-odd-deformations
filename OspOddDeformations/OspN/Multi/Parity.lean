import OspOddDeformations.OspN.Multi.Reduction

/-!
# `U` preserves the parity: `uMat Θ X W` has parity `parity X + parity W`
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem HasParity.zero (π : ZMod 2) : HasParity π (0 : GR F n r) := fun _ _ => rfl

theorem HasParity.add {π : ZMod 2} {a b : GR F n r} (ha : HasParity π a) (hb : HasParity π b) :
    HasParity π (a + b) := fun T h => by simp [ha T h, hb T h]

theorem HasParity.neg {π : ZMod 2} {a : GR F n r} (ha : HasParity π a) : HasParity π (-a) :=
  fun T h => by simp [ha T h]

theorem HasParity.sub {π : ZMod 2} {a b : GR F n r} (ha : HasParity π a) (hb : HasParity π b) :
    HasParity π (a - b) := fun T h => by simp [ha T h, hb T h]

theorem HasParity.rsmul {π : ZMod 2} (q : ℚ) {a : GR F n r} (ha : HasParity π a) :
    HasParity π (q • a) := fun T h => by simp [ha T h]

theorem HasParity.smul {π : ZMod 2} (c : PmnR F n r) {a : GR F n r} (ha : HasParity π a) :
    HasParity π (c • a) := fun T h => by simp [ha T h]

theorem HasParity.sum {π : ZMod 2} {ι : Type*} (s : Finset ι) {f : ι → GR F n r}
    (hf : ∀ i ∈ s, HasParity π (f i)) : HasParity π (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using HasParity.zero π
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem HasParity.gmul {π ρ : ZMod 2} {a b : GR F n r} (ha : HasParity π a) (hb : HasParity ρ b) :
    HasParity (π + ρ) (gmul a b) := by
  intro T hT
  refine Finset.sum_eq_zero fun A _ => Finset.sum_eq_zero fun B _ => ?_
  by_cases hU : A ∪ B = T
  · by_cases hd : Disjoint A B
    · by_cases hA : (A.card : ZMod 2) = π
      · by_cases hB : (B.card : ZMod 2) = ρ
        · exfalso; apply hT
          rw [← hU, Finset.card_union_of_disjoint hd, Nat.cast_add, hA, hB]
        · simp [hU, hb B hB]
      · simp [hU, ha A hA]
    · simp [hU, gs_eq_zero_of_not_disjoint hd]
  · simp [hU]

theorem HasCard.parity {k : ℕ} {a : GR F n r} (ha : HasCard k a) : HasParity (k : ZMod 2) a :=
  fun T hT => ha T fun h => hT (by rw [h])

theorem IsEvenGR.parity {a : GR F n r} (ha : IsEvenGR a) : HasParity 0 a := by
  intro T hT
  apply ha
  by_contra hc
  apply hT
  have : T.card % 2 = 0 := by omega
  exact (ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr this))

theorem grComp_gtens (a : GR F n r) (v : OspMod F n) (W : OspBasis F n) :
    grComp (gtens a v) W = emb0 (r := r) (v W) • a := by
  funext T; simp [grComp, gtens, mul_comm]

theorem HasParity.smul_of {π ρ : ZMod 2} {a : GR F n r} (ha : HasParity ρ a) (c : PmnR F n r)
    (hc : c ≠ 0 → π = ρ) : HasParity π (c • a) := by
  by_cases h : c = 0
  · subst h; simpa using HasParity.zero π
  · rw [hc h]; exact ha.smul c

theorem parity_of_emb0_eN {b W : OspBasis F n} (h : emb0 (F := F) (n := n) (r := r) (eN b W) ≠ 0) :
    W = b := by
  by_contra hne
  apply h
  rw [emb0_eN, ite_eq_right hne]

theorem parity_of_emb0_Sof {i j : F.K} {W : OspBasis F n}
    (h : emb0 (F := F) (n := n) (r := r) (Sof i j W) ≠ 0) : parity W = 0 := by
  by_contra hne
  apply h
  unfold Sof
  split_ifs with h1 h2
  · have : W ≠ (Sum.inr (Sum.inl ⟨(i, j), h1⟩) : OspBasis F n) := by
      rintro rfl; exact hne rfl
    unfold eN; rw [ite_eq_right this]; simp
  · have : W ≠ (Sum.inr (Sum.inl ⟨(j, i), h2⟩) : OspBasis F n) := by
      rintro rfl; exact hne rfl
    simp only [Pi.neg_apply]; unfold eN; rw [ite_eq_right this]; simp
  · simp

theorem grComp_add (f g : RModM F n r) (W : OspBasis F n) :
    grComp (f + g) W = grComp f W + grComp g W := rfl

theorem grComp_sub (f g : RModM F n r) (W : OspBasis F n) :
    grComp (f - g) W = grComp f W - grComp g W := rfl

theorem grComp_rsmul (q : ℚ) (f : RModM F n r) (W : OspBasis F n) :
    grComp (q • f) W = q • grComp f W := rfl

theorem grComp_sum {ι : Type*} (s : Finset ι) (f : ι → RModM F n r) (W : OspBasis F n) :
    grComp (∑ i ∈ s, f i) W = ∑ i ∈ s, grComp (f i) W := by
  funext T; simp [grComp, Finset.sum_apply]

theorem parity_Lof (w z : I n) : parity (Lof w z : OspBasis F n) = 0 := by
  by_cases h : Bmn.IKey w ≤ Bmn.IKey z
  · rw [Lof_of_le h]; rfl
  · have : (Lof w z : OspBasis F n) = Sum.inl ⟨(z, w), (Nat.not_le.mp h).le⟩ := by
      unfold Lof; exact dite_eq_right h
    rw [this]; rfl

theorem parity_Fof (w : I n) (i : F.K) : parity (Fof w i : OspBasis F n) = 1 := rfl

theorem uMat_parity (Θ : I n → I n → GR F n r) (hEven : ∀ u w, IsEvenGR (Θ u w))
    (X W : OspBasis F n) : HasParity (parity X + parity W) (uMat Θ X W) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases X with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · have h0 : parity (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [uMat, UBasis0, grComp_add, grComp_sub, grComp_rsmul, grComp_sum, grComp_gtens]
    refine (HasParity.add (HasParity.sum _ fun w _ => HasParity.sum _ fun z _ => ?_)
      (HasParity.sum _ fun w _ => HasParity.sum _ fun i _ => ?_)).sub
      (HasParity.rsmul _ (HasParity.sum _ fun i _ => HasParity.sum _ fun j _ => ?_))
    · refine HasParity.smul_of ((hEven u w).parity.gmul (hEven v z).parity) _ fun hc => ?_
      rw [parity_of_emb0_eN hc, parity_Lof]; simp
    · refine HasParity.smul_of (((hEven u w).parity.gmul (HasCard_gammaR v (F.dual i)).parity).add
        ((hEven v w).parity.gmul (HasCard_gammaR u (F.dual i)).parity)) _ fun hc => ?_
      rw [parity_of_emb0_eN hc, parity_Fof]; simp
    · refine HasParity.smul_of ((HasCard_gammaR u (F.dual i)).parity.gmul
        (HasCard_gammaR v (F.dual j)).parity) _ fun hc => ?_
      rw [parity_of_emb0_Sof hc]
      simp [h11]
  · have h0 : parity (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) = 0 := rfl
    rw [h0, zero_add]
    simp only [uMat, UBasis0, grComp_gtens]
    refine HasParity.smul_of (HasCard_gone (F := F) (n := n) (r := r)).parity _ fun hc => ?_
    rw [parity_of_emb0_Sof hc]; simp
  · have h0 : parity (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = 1 := rfl
    rw [h0]
    simp only [uMat, UBasis0, grComp_add, grComp_rsmul, grComp_sum, grComp_gtens]
    refine (HasParity.sum _ fun w _ => ?_).add
      (HasParity.rsmul _ (HasParity.sum _ fun j _ => ?_))
    · refine HasParity.smul_of (hEven u w).parity _ fun hc => ?_
      rw [parity_of_emb0_eN hc, parity_Fof]; simp [h11]
    · refine HasParity.smul_of (HasCard_gammaR u (F.dual j)).parity _ fun hc => ?_
      rw [parity_of_emb0_Sof hc]; simp

end Multi
end OspN
end OspOddDeformations
