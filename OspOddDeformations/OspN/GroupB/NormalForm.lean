import OspOddDeformations.OspN.Identification
import Mathlib.Data.Matrix.Block

/-!
# Prop 3.4, last statement: the Gram matrix of `−𝓑` in the paper's order

In the basis `e_{1+},…,e_{m+}, e_{1−},…,e_{m−}` (`e_0` last if `N` is odd), then
`e_2,e_4,…,e_{2n}`, `e_1,e_3,…,e_{2n−1}`, the Gram matrix of `−𝓑` (`Bform`) is the block
matrix
`diag( [[0, 𝕀_m], [𝕀_m, 0]] (⊕ (1) if N is odd), [[0, 𝕀_n], [−𝕀_n, 0]] )`, which is the matrix
`G` of FSS00 §2.27 (`GOdd`, `GEven`, transcribed). Here `e_{k+}` is `(k, false)`, `e_{k−}` is
`(k, true)`,
`e_{2k−1}` is `(k, false)` and `e_{2k}` is `(k, true)` (`k` from `0`).
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I J)
open Matrix

variable (m n : ℕ)

/-- The paper's order for odd `N = 2m+1`: `(e_{k+})_k, (e_{k−})_k, e_0`, then `(e_{2k})_k`,
`(e_{2k−1})_k`. -/
def ordOdd : ((Fin m ⊕ Fin m) ⊕ Unit) ⊕ (Fin n ⊕ Fin n) → Midx (oddIdx m) n
  | .inl (.inl (.inl k)) => .inl (some (k, false))
  | .inl (.inl (.inr k)) => .inl (some (k, true))
  | .inl (.inr _) => .inl none
  | .inr (.inl k) => .inr (k, true)
  | .inr (.inr k) => .inr (k, false)

/-- The paper's order for even `N = 2m`. -/
def ordEven : (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n) → Midx (evenIdx m) n
  | .inl (.inl k) => .inl (k, false)
  | .inl (.inr k) => .inl (k, true)
  | .inr (.inl k) => .inr (k, true)
  | .inr (.inr k) => .inr (k, false)

/-- FSS00's `G` for `osp(2m+1|2n)`. -/
def GOdd : Matrix (((Fin m ⊕ Fin m) ⊕ Unit) ⊕ (Fin n ⊕ Fin n))
    (((Fin m ⊕ Fin m) ⊕ Unit) ⊕ (Fin n ⊕ Fin n)) ℚ :=
  fromBlocks (fromBlocks (fromBlocks 0 1 1 0) 0 0 1) 0 0 (fromBlocks 0 1 (-1) 0)

/-- FSS00's `G` for `osp(2m|2n)`. -/
def GEven : Matrix ((Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)) ((Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)) ℚ :=
  fromBlocks (fromBlocks 0 1 1 0) 0 0 (fromBlocks 0 1 (-1) 0)

/-- **Prop 3.4, last statement**, odd `N`: the Gram matrix of `−𝓑` in the paper's order is `G`. -/
theorem gram_ordOdd : (Matrix.of fun a b => -Bform (ordOdd m n a) (ordOdd m n b)) = GOdd m n := by
  ext a b
  rcases a with ((a | a) | a) | (a | a) <;> rcases b with ((b | b) | b) | (b | b) <;>
    (simp [GOdd, ordOdd, Bform, FermionIndex.g, oddIdx, Bmn.dual, Bmn.J, Matrix.one_apply,
      eq_comm]
     try split_ifs <;> norm_num)

/-- **Prop 3.4, last statement**, even `N`. -/
theorem gram_ordEven :
    (Matrix.of fun a b => -Bform (ordEven m n a) (ordEven m n b)) = GEven m n := by
  ext a b
  rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
    (simp [GEven, ordEven, Bform, FermionIndex.g, evenIdx, Bmn.J, Matrix.one_apply]
     try split_ifs <;> simp_all)

/-- The orders are bijections onto the basis of `M`. -/
theorem ordOdd_bijective : Function.Bijective (ordOdd m n) := by
  constructor
  · intro a b h
    rcases a with ((a | a) | a) | (a | a) <;> rcases b with ((b | b) | b) | (b | b) <;>
      (simp only [ordOdd] at h; cases h; try rfl)
  · rintro (i | ⟨k, b⟩)
    · rcases i with _ | ⟨k, b⟩
      · exact ⟨.inl (.inr ()), rfl⟩
      · cases b
        · exact ⟨.inl (.inl (.inl k)), rfl⟩
        · exact ⟨.inl (.inl (.inr k)), rfl⟩
    · cases b
      · exact ⟨.inr (.inr k), rfl⟩
      · exact ⟨.inr (.inl k), rfl⟩

theorem ordEven_bijective : Function.Bijective (ordEven m n) := by
  constructor
  · intro a b h
    rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
      (simp only [ordEven] at h; cases h; try rfl)
  · rintro (⟨k, b⟩ | ⟨k, b⟩)
    · cases b
      · exact ⟨.inl (.inl k), rfl⟩
      · exact ⟨.inl (.inr k), rfl⟩
    · cases b
      · exact ⟨.inr (.inr k), rfl⟩
      · exact ⟨.inr (.inl k), rfl⟩

end OspN
end OspOddDeformations
