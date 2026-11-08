import OspOddDeformations.OspN.Multi.Sigma
import OspOddDeformations.OspN.Multi.UMBij

/-!
# The three operations in coefficient (`grComp`) form
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

theorem grComp_bracket0M (x y : RModM F n r) (V : OspBasis F n) :
    grComp (bracket0M x y) V = ∑ Z : OspBasis F n, ∑ Z' : OspBasis F n,
      emb0 (r := r) (bracket0Basis Z Z' V) •
        gmul (grComp x Z) (sigPow (parity Z) (grComp y Z')) := by
  funext T
  simp only [grComp, bracket0M, Finset.sum_apply, Pi.smul_apply, bracket0MBasis, kap, liftBy,
    smul_eq_mul, Fintype.sum_prod_type, gmul, Pi.smul_apply, sigPow_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Z' _ => Finset.sum_congr rfl fun S _ =>
    Finset.sum_congr rfl fun S' _ => ?_
  by_cases h : S ∪ S' = T
  · subst h
    simp only [ite_true, Algebra.smul_def, map_mul, map_pow, map_neg, map_one]
    ring
  · have h' : ¬ T = S ∪ S' := fun e => h e.symm
    simp [h, h']

theorem grComp_UM (Θ : I n → I n → GR F n r) (x : RModM F n r) (W : OspBasis F n) :
    grComp (UM Θ x) W = ∑ Z : OspBasis F n, gmul (grComp x Z) (grComp (UBasis0 Θ Z) W) := by
  funext T
  simp only [grComp, UM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    gsmul_apply_eq]
  refine Finset.sum_congr rfl fun Z _ => ?_
  conv_rhs => simp only [gmul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [gmul_gmono_one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [mul_smul_comm]; rfl
  · simp

theorem bracketBetaM_split (x y : RModM F n r) :
    bracketBetaM x y = bracket0M x y + ∑ p : RBasisM F n r, ∑ q : RBasisM F n r,
      (x p * y q) • ∑ s : Fin r,
        ((-1 : ℚ) ^ (q.2.card * (parity p.1).val) * gs p.2 q.2 * gs (p.2 ∪ q.2) {s}) •
          kap (p.2 ∪ q.2 ∪ {s}) (GammaSBasis s p.1 q.1) := by
  unfold bracketBetaM bracket0M
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [bracketBetaMBasis, smul_add]

theorem sum_comm5 {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [AddCommMonoid M] (f : α → β → γ → δ → ε → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ e, ∑ a, ∑ c, ∑ b, ∑ d, f a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ b, ∑ e, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ e, ∑ b, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ c, ∑ b, ∑ d, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem grComp_bracketBetaM (x y : RModM F n r) (V : OspBasis F n) :
    grComp (bracketBetaM x y) V = grComp (bracket0M x y) V + ∑ s : Fin r, ∑ Z : OspBasis F n,
      ∑ Z' : OspBasis F n, embS s (GammaBasis Z Z' V) •
        gmul (gmul (grComp x Z) (sigPow (parity Z) (grComp y Z'))) (gmono {s} 1) := by
  rw [bracketBetaM_split]
  funext T
  simp only [grComp, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, kap, GammaSBasis, liftBy,
    smul_eq_mul, Fintype.sum_prod_type]
  congr 1
  simp only [Finset.mul_sum]
  rw [sum_comm5]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun Z _ =>
    Finset.sum_congr rfl fun Z' _ => ?_
  rw [gmul_gmul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [Finset.sum_eq_single {s}]
  · by_cases h : S ∪ S' ∪ {s} = T
    · subst h
      simp only [ite_true, gmono, sigPow_apply, Algebra.smul_def, map_mul, map_pow, map_neg,
        map_one, grComp]
      ring
    · have h' : ¬ T = S ∪ S' ∪ {s} := fun e => h e.symm
      simp only [h, h', ite_false, mul_zero, smul_zero]
  · intro C _ hC
    simp [gmono, hC]
  · simp

end Multi
end OspN
end OspOddDeformations
