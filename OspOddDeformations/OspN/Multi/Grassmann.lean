import OspOddDeformations.OspN.Multi.Defs

/-!
# The `GR` library: the sign `gs`

Inversion count `invCount A B` behind `gs`, its additivity in each argument on disjoint unions,
`invCount A B + invCount B A = |A||B|` for disjoint `A B`, and from these `gs`'s graded
commutativity and cocycle identity.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

variable {r : ℕ}

/-- The number of inversions `t < s`, `s ∈ S`, `t ∈ T`, defining `gs`. -/
def invCount (S T : Finset (Fin r)) : ℕ := ((S ×ˢ T).filter (fun p => p.2 < p.1)).card

theorem gs_eq_of_disjoint {S T : Finset (Fin r)} (h : Disjoint S T) :
    gs S T = (-1) ^ invCount S T := by
  unfold gs invCount; rw [ite_eq_left h]

theorem gs_eq_zero_of_not_disjoint {S T : Finset (Fin r)} (h : ¬ Disjoint S T) : gs S T = 0 := by
  unfold gs; rw [ite_eq_right h]

theorem inv_union_left {A B : Finset (Fin r)} (C : Finset (Fin r)) (h : Disjoint A B) :
    invCount (A ∪ B) C = invCount A C + invCount B C := by
  unfold invCount
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl h))

theorem inv_union_right (A : Finset (Fin r)) {B C : Finset (Fin r)} (h : Disjoint B C) :
    invCount A (B ∪ C) = invCount A B + invCount A C := by
  unfold invCount
  rw [Finset.product_union, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inr h))

theorem inv_add_inv {A B : Finset (Fin r)} (h : Disjoint A B) :
    invCount A B + invCount B A = A.card * B.card := by
  unfold invCount
  have h1 : ((B ×ˢ A).filter (fun p => p.2 < p.1)).card
      = ((A ×ˢ B).filter (fun p => p.1 < p.2)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
  rw [h1, ← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun p _ h1 h2 =>
    absurd h1 (not_lt.mpr h2.le)), ← Finset.filter_or, ← Finset.card_product]
  congr 1
  refine (Finset.filter_true_of_mem fun p hp => ?_)
  simp only [Finset.mem_product] at hp
  have hne : p.1 ≠ p.2 := fun e => Finset.disjoint_left.mp h hp.1 (e ▸ hp.2)
  exact lt_or_gt_of_ne (Ne.symm hne)

/-- `κ_Sκ_T = (-1)^{|S||T|} κ_Tκ_S`. -/
theorem gs_comm (A B : Finset (Fin r)) : gs A B = (-1) ^ (A.card * B.card) * gs B A := by
  by_cases h : Disjoint A B
  · rw [gs_eq_of_disjoint h, gs_eq_of_disjoint h.symm, ← inv_add_inv h, pow_add, mul_assoc,
      ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [gs_eq_zero_of_not_disjoint h, gs_eq_zero_of_not_disjoint (fun h' => h h'.symm)]
    simp

/-- The cocycle identity behind associativity of `gmul`. -/
theorem gs_cocycle (A B C : Finset (Fin r)) :
    gs A B * gs (A ∪ B) C = gs B C * gs A (B ∪ C) := by
  by_cases hAB : Disjoint A B
  · by_cases hBC : Disjoint B C
    · by_cases hAC : Disjoint A C
      · have h1 : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
        have h2 : Disjoint A (B ∪ C) := Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩
        rw [gs_eq_of_disjoint hAB, gs_eq_of_disjoint h1, gs_eq_of_disjoint hBC,
          gs_eq_of_disjoint h2, ← pow_add, ← pow_add, inv_union_left C hAB,
          inv_union_right A hBC]
        congr 1; omega
      · have h2 : ¬ Disjoint (A ∪ B) C := fun h => hAC (Finset.disjoint_union_left.mp h).1
        have h3 : ¬ Disjoint A (B ∪ C) := fun h => hAC (Finset.disjoint_union_right.mp h).2
        rw [gs_eq_zero_of_not_disjoint h2, gs_eq_zero_of_not_disjoint h3]; simp
    · have h2 : ¬ Disjoint (A ∪ B) C := fun h => hBC (Finset.disjoint_union_left.mp h).2
      rw [gs_eq_zero_of_not_disjoint hBC, gs_eq_zero_of_not_disjoint h2]; simp
  · have h3 : ¬ Disjoint A (B ∪ C) := fun h => hAB (Finset.disjoint_union_right.mp h).1
    rw [gs_eq_zero_of_not_disjoint hAB, gs_eq_zero_of_not_disjoint h3]; simp

/-! ## `gmul`: bilinearity and unit -/

variable {F : FermionIndex} {n : ℕ}

theorem gs_empty_left (T : Finset (Fin r)) : gs ∅ T = 1 := by
  rw [gs_eq_of_disjoint (Finset.disjoint_empty_left T)]; simp [invCount]

theorem gs_empty_right (S : Finset (Fin r)) : gs S ∅ = 1 := by
  rw [gs_eq_of_disjoint (Finset.disjoint_empty_right S)]; simp [invCount]

theorem gmul_add_left (a a' b : GR F n r) : gmul (a + a') b = gmul a b + gmul a' b := by
  funext T; simp only [gmul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs <;> simp [add_mul, smul_add]

theorem gmul_add_right (a b b' : GR F n r) : gmul a (b + b') = gmul a b + gmul a b' := by
  funext T; simp only [gmul, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs <;> simp [mul_add, smul_add]

theorem gone_gmul (b : GR F n r) : gmul gone b = b := by
  funext T
  simp only [gmul, gone]
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single T]
    · simp [gs_empty_left]
    · intro B _ hB; simp [hB]
    · simp
  · intro A _ hA; simp [hA]
  · simp

theorem gmul_gone (a : GR F n r) : gmul a gone = a := by
  funext T
  simp only [gmul, gone]
  rw [Finset.sum_eq_single T]
  · rw [Finset.sum_eq_single ∅]
    · simp [gs_empty_right]
    · intro B _ hB; simp [hB]
    · simp
  · intro A _ hA
    apply Finset.sum_eq_zero; intro B _
    by_cases hB : B = ∅
    · subst hB; simp [hA]
    · simp [hB]
  · simp

theorem gmul_zero_left (b : GR F n r) : gmul 0 b = 0 := by
  funext T; simp [gmul]

theorem gmul_zero_right (a : GR F n r) : gmul a 0 = 0 := by
  funext T; simp [gmul]

/-- Even elements are central: `gmul a b = gmul b a` if `a` is even. -/
theorem gmul_comm_of_even {a : GR F n r} (ha : IsEvenGR a) (b : GR F n r) :
    gmul a b = gmul b a := by
  funext T
  simp only [gmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.union_comm B A]
  by_cases hA : a A = 0
  · simp [hA]
  · have hev : A.card % 2 = 0 := by
      by_contra hc; exact hA (ha A (by omega))
    have : gs A B = gs B A := by
      rw [gs_comm A B, ((Nat.even_iff.mpr hev).mul_right B.card).neg_one_pow, one_mul]
    rw [this, mul_comm]

theorem sum_comm4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : δ → γ → α → β → M) :
    ∑ d, ∑ c, ∑ a, ∑ b, f d c a b = ∑ a, ∑ b, ∑ c, ∑ d, f d c a b := by
  calc ∑ d, ∑ c, ∑ a, ∑ b, f d c a b = ∑ d, ∑ a, ∑ b, ∑ c, f d c a b := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f d c a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f d c a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Triple-sum form of `(a b) c`. -/
theorem gmul_gmul_apply (a b c : GR F n r) (T : Finset (Fin r)) :
    gmul (gmul a b) c T = ∑ A, ∑ B, ∑ C,
      if A ∪ B ∪ C = T then (gs A B * gs (A ∪ B) C) • (a A * b B * c C) else 0 := by
  classical
  have h1 : ∀ D C : Finset (Fin r), (if D ∪ C = T then gs D C • (gmul a b D * c C) else 0)
      = ∑ A, ∑ B, if A ∪ B = D then (if D ∪ C = T then (gs A B * gs D C) • (a A * b B * c C)
          else 0) else 0 := by
    intro D C
    by_cases hDC : D ∪ C = T
    · simp only [hDC, ite_true, gmul, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      by_cases hAB : A ∪ B = D
      · simp only [hAB, ite_true, smul_mul_assoc, smul_smul, mul_comm (gs D C)]
      · simp [hAB]
    · simp [hDC]
  change (∑ D, ∑ C, if D ∪ C = T then gs D C • (gmul a b D * c C) else 0) = _
  simp_rw [h1]
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl
    fun C _ => ?_
  rw [Finset.sum_eq_single (A ∪ B)]
  · simp
  · intro D _ hD; simp [Ne.symm hD]
  · simp

/-- Triple-sum form of `a (b c)`. -/
theorem gmul_gmul_apply' (a b c : GR F n r) (T : Finset (Fin r)) :
    gmul a (gmul b c) T = ∑ A, ∑ B, ∑ C,
      if A ∪ (B ∪ C) = T then (gs B C * gs A (B ∪ C)) • (a A * (b B * c C)) else 0 := by
  classical
  have h1 : ∀ A D : Finset (Fin r), (if A ∪ D = T then gs A D • (a A * gmul b c D) else 0)
      = ∑ B, ∑ C, if B ∪ C = D then (if A ∪ D = T then
          (gs B C * gs A D) • (a A * (b B * c C)) else 0) else 0 := by
    intro A D
    by_cases hAD : A ∪ D = T
    · simp only [hAD, ite_true, gmul, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ => ?_
      by_cases hBC : B ∪ C = D
      · simp only [hBC, ite_true, mul_smul_comm, smul_smul, mul_comm (gs A D)]
      · simp [hBC]
    · simp [hAD]
  change (∑ A, ∑ D, if A ∪ D = T then gs A D • (a A * gmul b c D) else 0) = _
  simp_rw [h1]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.sum_eq_single (B ∪ C)]
  · simp
  · intro D _ hD; simp [Ne.symm hD]
  · simp

theorem gmul_assoc (a b c : GR F n r) : gmul (gmul a b) c = gmul a (gmul b c) := by
  funext T
  rw [gmul_gmul_apply, gmul_gmul_apply']
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ =>
    Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.union_assoc, gs_cocycle, mul_assoc]

/-! ## scalars, negation, sums, monomials -/

theorem gmul_smul_left (c : PmnR F n r) (a b : GR F n r) : gmul (c • a) b = c • gmul a b := by
  funext T; simp only [gmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [mul_smul_comm, mul_assoc]
  · simp

theorem gmul_smul_right (c : PmnR F n r) (a b : GR F n r) : gmul a (c • b) = c • gmul a b := by
  funext T; simp only [gmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [mul_smul_comm, mul_left_comm]
  · simp

theorem gmul_rsmul_left (q : ℚ) (a b : GR F n r) : gmul (q • a) b = q • gmul a b := by
  funext T; simp only [gmul, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [smul_mul_assoc, smul_comm]
  · simp

theorem gmul_rsmul_right (q : ℚ) (a b : GR F n r) : gmul a (q • b) = q • gmul a b := by
  funext T; simp only [gmul, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [mul_smul_comm, smul_comm]
  · simp

theorem gmul_neg_left (a b : GR F n r) : gmul (-a) b = -gmul a b := by
  have := gmul_rsmul_left (-1 : ℚ) a b
  simpa using this

theorem gmul_neg_right (a b : GR F n r) : gmul a (-b) = -gmul a b := by
  have := gmul_rsmul_right (-1 : ℚ) a b
  simpa using this

theorem gmul_sum_left {ι : Type*} (s : Finset ι) (f : ι → GR F n r) (b : GR F n r) :
    gmul (∑ i ∈ s, f i) b = ∑ i ∈ s, gmul (f i) b := by
  classical
  induction s using Finset.induction with
  | empty => simp [gmul_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gmul_add_left, ih]

theorem gmul_sum_right {ι : Type*} (s : Finset ι) (a : GR F n r) (f : ι → GR F n r) :
    gmul a (∑ i ∈ s, f i) = ∑ i ∈ s, gmul a (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gmul_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gmul_add_right, ih]

theorem gmono_gmul_gmono (S T : Finset (Fin r)) (c d : PmnR F n r) :
    gmul (gmono S c) (gmono T d) = gmono (S ∪ T) (gs S T • (c * d)) := by
  funext U
  simp only [gmul, gmono]
  rw [Finset.sum_eq_single S]
  · rw [Finset.sum_eq_single T]
    · by_cases hU : S ∪ T = U
      · simp [hU]
      · simp [hU, Ne.symm hU]
    · intro B _ hB; simp [hB]
    · simp
  · intro A _ hA
    exact Finset.sum_eq_zero fun B _ => by simp [hA]
  · simp

/-! ## `gsmul` as the left `GR`-action -/

/-- The `Z`-component of `w`, as an element of `GR`. -/
def grComp (w : RModM F n r) (Z : OspBasis F n) : GR F n r := fun B => w (Z, B)

theorem gsmul_apply_eq (a : GR F n r) (w : RModM F n r) (p : RBasisM F n r) :
    gsmul a w p = gmul a (grComp w p.1) p.2 := rfl

theorem comp_gsmul (a : GR F n r) (w : RModM F n r) (Z : OspBasis F n) :
    grComp (gsmul a w) Z = gmul a (grComp w Z) := rfl

theorem gsmul_gone (w : RModM F n r) : gsmul gone w = w := by
  funext p; rw [gsmul_apply_eq, gone_gmul]; rfl

theorem gsmul_gmul (a b : GR F n r) (w : RModM F n r) :
    gsmul (gmul a b) w = gsmul a (gsmul b w) := by
  funext p; rw [gsmul_apply_eq, gsmul_apply_eq, comp_gsmul, gmul_assoc]

theorem gsmul_add_left (a a' : GR F n r) (w : RModM F n r) :
    gsmul (a + a') w = gsmul a w + gsmul a' w := by
  funext p; rw [gsmul_apply_eq, gmul_add_left]; rfl

theorem gsmul_add_right (a : GR F n r) (w w' : RModM F n r) :
    gsmul a (w + w') = gsmul a w + gsmul a w' := by
  funext p
  exact congrFun (gmul_add_right a (grComp w p.1) (grComp w' p.1)) p.2

end Multi
end OspN
end OspOddDeformations
