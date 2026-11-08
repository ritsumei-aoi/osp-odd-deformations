import OspOddDeformations.OspN.Multi.Grassmann
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `UM` is unitriangular for the filtration by `|S|`

The `∅`-component of `UBasis0 Θ Z` is `eN Z` (if `Θ` has constant part `𝕀`), and `gsmul (κ_S)`
only moves components from `S` to supersets; so the matrix of `UM Θ` is triangular for `|S|` with
`1` on the diagonal blocks.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)
open scoped Matrix

variable {F : FermionIndex} {n r : ℕ}

theorem gmul_empty_apply (a b : GR F n r) : gmul a b ∅ = a ∅ * b ∅ := by
  simp only [gmul]
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [gs_empty_left]
    · intro B _ hB
      simp [hB]
    · simp
  · intro A _ hA
    refine Finset.sum_eq_zero fun B _ => ?_
    have : ¬ (A ∪ B = ∅) := fun h => hA (Finset.union_eq_empty.mp h).1
    simp [this]
  · simp

theorem gammaR_empty (u : I n) (i : F.K) : gammaR (r := r) u i ∅ = 0 := by
  simp [gammaR, gmono, Finset.sum_apply]

theorem gmono_empty_apply {S : Finset (Fin r)} (hS : S ≠ ∅) (c : PmnR F n r) :
    gmono S c ∅ = 0 := by
  simp [gmono, Ne.symm hS]

theorem gtens_apply (a : GR F n r) (v : OspMod F n) (p : RBasisM F n r) :
    gtens a v p = a p.2 * emb0 (v p.1) := rfl

theorem emb0_eN (b k : OspBasis F n) :
    emb0 (F := F) (n := n) (r := r) (eN b k) = if k = b then 1 else 0 := by
  unfold eN; split_ifs <;> simp

theorem Sof_of_lt {i j : F.K} (h : F.key i < F.key j) :
    Sof (n := n) i j = eN (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) := by
  unfold Sof; rw [dite_eq_left h]

theorem Lof_of_le {u v : I n} (h : Bmn.IKey u ≤ Bmn.IKey v) :
    (Lof u v : OspBasis F n) = Sum.inl ⟨(u, v), h⟩ := by
  unfold Lof; exact dite_eq_left h

theorem UBasis0_empty (Θ : I n → I n → GR F n r)
    (hId : ∀ u w, Θ u w ∅ = if u = w then 1 else 0) (Z Z' : OspBasis F n) :
    UBasis0 Θ Z (Z', ∅) = if Z' = Z then 1 else 0 := by
  rcases Z with ⟨⟨u, v⟩, h⟩ | ⟨⟨i, j⟩, h⟩ | ⟨u, i⟩
  · have e : ∀ w z, emb0 (F := F) (n := n) (r := r) (eN (Lof w z) Z') =
        if Z' = Lof w z then 1 else 0 := fun w z => emb0_eN _ _
    simp only [UBasis0, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, gtens_apply,
      gmul_empty_apply, hId, Pi.add_apply, gammaR_empty, mul_zero, zero_mul, add_zero,
      Finset.sum_const_zero, smul_zero, sub_zero, e, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single v]
      · rw [Lof_of_le (u := u) (v := v) h]; simp
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro x _ hx
      exact Finset.sum_eq_zero fun c _ => by simp [Ne.symm hx]
    · simp
  · simp only [UBasis0, gtens_apply, Sof_of_lt h]
    simp only [gone, ite_true, one_mul]
    exact emb0_eN (Sum.inr (Sum.inl ⟨(i, j), h⟩)) Z'
  · have e : ∀ w, emb0 (F := F) (n := n) (r := r) (eN (Fof w i) Z') =
        if Z' = Fof w i then 1 else 0 := fun w => emb0_eN _ _
    simp only [UBasis0, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, gtens_apply, hId,
      gammaR_empty, zero_mul, Finset.sum_const_zero, smul_zero, add_zero, e, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

/-! ## The matrix of `UM` -/

/-- The matrix entry: the `q`-component of `UM Θ (eR p)`. -/
noncomputable def Mx (Θ : I n → I n → GR F n r) (p q : RBasisM F n r) : PmnR F n r :=
  gsmul (gmono p.2 1) (UBasis0 Θ p.1) q

theorem UM_apply (Θ : I n → I n → GR F n r) (x : RModM F n r) (q : RBasisM F n r) :
    UM Θ x q = ∑ p, x p * Mx Θ p q := by
  simp only [UM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Mx]

theorem gmul_gmono_one_apply (S : Finset (Fin r)) (w : GR F n r) (T : Finset (Fin r)) :
    gmul (gmono S (1 : PmnR F n r)) w T = ∑ B, if S ∪ B = T then gs S B • w B else 0 := by
  simp only [gmul, gmono]
  rw [Finset.sum_eq_single S]
  · simp
  · intro A _ hA
    exact Finset.sum_eq_zero fun B _ => by simp [hA]
  · simp

theorem Mx_eq_zero_of_not_subset (Θ : I n → I n → GR F n r) {p q : RBasisM F n r}
    (h : ¬ p.2 ⊆ q.2) : Mx Θ p q = 0 := by
  unfold Mx
  rw [gsmul_apply_eq, gmul_gmono_one_apply]
  refine Finset.sum_eq_zero fun B _ => ?_
  have : ¬ (p.2 ∪ B = q.2) := fun e => h (e ▸ Finset.subset_union_left)
  simp [this]

theorem Mx_of_same (Θ : I n → I n → GR F n r)
    (hId : ∀ u w, Θ u w ∅ = if u = w then 1 else 0) {p q : RBasisM F n r} (h : p.2 = q.2) :
    Mx Θ p q = if q.1 = p.1 then 1 else 0 := by
  unfold Mx
  rw [gsmul_apply_eq, gmul_gmono_one_apply, Finset.sum_eq_single ∅]
  · rw [← h]
    simp [gs_empty_right, grComp, UBasis0_empty Θ hId]
  · intro B _ hB
    by_cases hd : Disjoint p.2 B
    · have : ¬ (p.2 ∪ B = q.2) := by
        intro e
        have hsub : B ⊆ p.2 := by rw [h, ← e]; exact Finset.subset_union_right
        exact hB (Finset.subset_empty.mp fun x hx =>
          absurd hx (Finset.disjoint_left.mp hd (hsub hx)))
      simp [this]
    · rw [gs_eq_zero_of_not_disjoint hd]; simp
  · simp

theorem UM_bijective_of_id (Θ : I n → I n → GR F n r)
    (hId : ∀ u w, Θ u w ∅ = if u = w then 1 else 0) : Function.Bijective (UM Θ) := by
  classical
  let A : Matrix (RBasisM F n r) (RBasisM F n r) (PmnR F n r) := fun p q => Mx Θ p q
  have hUM : ∀ x, UM Θ x = x ᵥ* A := fun x => by
    funext q; rw [UM_apply]; rfl
  have hbt : A.BlockTriangular (fun p => p.2.card) := by
    intro i j hij
    exact Mx_eq_zero_of_not_subset Θ fun hsub => absurd (Finset.card_le_card hsub) (not_le.mpr hij)
  have hdet : A.det = 1 := by
    rw [Matrix.BlockTriangular.det hbt]
    refine Finset.prod_eq_one fun a _ => ?_
    have : A.toSquareBlock (fun p => p.2.card) a = 1 := by
      refine Matrix.ext fun ⟨p, hp⟩ ⟨q, hq⟩ => ?_
      have hM : A.toSquareBlock (fun p => p.2.card) a ⟨p, hp⟩ ⟨q, hq⟩ = Mx Θ p q := rfl
      rw [hM, Matrix.one_apply]
      simp only [Subtype.mk.injEq]
      have hpq : p.2.card = q.2.card := hp.trans hq.symm
      by_cases hs : p.2 ⊆ q.2
      · have he : p.2 = q.2 := Finset.eq_of_subset_of_card_le hs hpq.ge
        rw [Mx_of_same Θ hId he]
        by_cases h1 : q.1 = p.1
        · have : p = q := Prod.ext h1.symm he
          simp [h1, this]
        · have : ¬ p = q := fun e => h1 (e ▸ rfl)
          simp [h1, this]
      · rw [Mx_eq_zero_of_not_subset Θ hs]
        have : ¬ p = q := fun e => hs (e ▸ Finset.Subset.refl _)
        simp [this]
    rw [this, Matrix.det_one]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  refine Function.bijective_iff_has_inverse.mpr ⟨fun x => x ᵥ* A⁻¹, fun x => ?_, fun x => ?_⟩
  · dsimp only
    rw [hUM, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hu, Matrix.vecMul_one]
  · dsimp only
    rw [hUM, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hu, Matrix.vecMul_one]

end Multi
end OspN
end OspOddDeformations
