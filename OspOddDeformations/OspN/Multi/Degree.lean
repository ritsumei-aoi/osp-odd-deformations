import OspOddDeformations.OspN.Multi.Grassmann

/-!
# κ-degree in `GR`

`HasCard k a`: `a` is supported on subsets of cardinality exactly `k`. `gmul` adds degrees; `γ` has
degree 1, `Ω` degree 2, `gone` and `JR` degree 0; degree `> r` vanishes.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- `a` is homogeneous of κ-degree `k`. -/
def HasCard (k : ℕ) (a : GR F n r) : Prop := ∀ T, T.card ≠ k → a T = 0

theorem HasCard.zero (k : ℕ) : HasCard k (0 : GR F n r) := fun _ _ => rfl

theorem HasCard.add {k : ℕ} {a b : GR F n r} (ha : HasCard k a) (hb : HasCard k b) :
    HasCard k (a + b) := fun T h => by simp [ha T h, hb T h]

theorem HasCard.neg {k : ℕ} {a : GR F n r} (ha : HasCard k a) : HasCard k (-a) :=
  fun T h => by simp [ha T h]

theorem HasCard.sub {k : ℕ} {a b : GR F n r} (ha : HasCard k a) (hb : HasCard k b) :
    HasCard k (a - b) := fun T h => by simp [ha T h, hb T h]

theorem HasCard.rsmul {k : ℕ} (q : ℚ) {a : GR F n r} (ha : HasCard k a) : HasCard k (q • a) :=
  fun T h => by simp [ha T h]

theorem HasCard.sum {k : ℕ} {ι : Type*} (s : Finset ι) {f : ι → GR F n r}
    (hf : ∀ i ∈ s, HasCard k (f i)) : HasCard k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using HasCard.zero k
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem HasCard.gmul {j k : ℕ} {a b : GR F n r} (ha : HasCard j a) (hb : HasCard k b) :
    HasCard (j + k) (gmul a b) := by
  intro T hT
  refine Finset.sum_eq_zero fun A _ => Finset.sum_eq_zero fun B _ => ?_
  by_cases hU : A ∪ B = T
  · by_cases hd : Disjoint A B
    · by_cases hA : A.card = j
      · by_cases hB : B.card = k
        · exact absurd (by rw [← hU, Finset.card_union_of_disjoint hd, hA, hB]) hT
        · simp [hU, hb B hB]
      · simp [hU, ha A hA]
    · simp [hU, gs_eq_zero_of_not_disjoint hd]
  · simp [hU]

theorem HasCard.eval_eq_zero {k : ℕ} {a : GR F n r} (ha : HasCard k a) {T : Finset (Fin r)}
    (h : T.card ≠ k) : a T = 0 := ha T h

theorem HasCard.of_lt {k : ℕ} {a : GR F n r} (hk : r < k) (ha : HasCard k a) : a = 0 := by
  funext T
  exact ha T (by have := Finset.card_le_univ T; simp at this; omega)

theorem HasCard.isEven {k : ℕ} (hk : k % 2 = 0) {a : GR F n r} (ha : HasCard k a) : IsEvenGR a :=
  fun T hT => ha T (by omega)

theorem IsEvenGR.add {a b : GR F n r} (ha : IsEvenGR a) (hb : IsEvenGR b) : IsEvenGR (a + b) :=
  fun T h => by simp [ha T h, hb T h]

theorem HasCard_gone : HasCard 0 (gone : GR F n r) := by
  intro T hT
  have : T ≠ ∅ := fun h => hT (by simp [h])
  simp [gone, this]

theorem HasCard_gone_ite (c : Prop) [Decidable c] :
    HasCard 0 (if c then (gone : GR F n r) else 0) := by
  split_ifs
  · exact HasCard_gone
  · exact HasCard.zero 0

theorem HasCard_gammaR (u : I n) (i : F.K) : HasCard 1 (gammaR (r := r) u i) := by
  intro T hT
  simp only [gammaR, Finset.sum_apply, gmono]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : T ≠ {s} := fun h => hT (by simp [h])
  simp [this]

theorem HasCard_OmegaR (u v : I n) : HasCard 2 (OmegaR (F := F) (r := r) u v) := by
  unfold OmegaR
  exact (HasCard.sum _ fun i _ => (HasCard_gammaR u i).gmul (HasCard_gammaR v (F.dual i))).neg

theorem HasCard_JR (u v : I n) : HasCard 0 (JR (F := F) (r := r) u v) := by
  intro T hT
  have : T ≠ ∅ := fun h => hT (by simp [h])
  simp [JR, this]

end Multi
end OspN
end OspOddDeformations
