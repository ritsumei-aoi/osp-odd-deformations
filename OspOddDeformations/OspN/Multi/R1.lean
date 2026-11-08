import OspOddDeformations.OspN.Multi.Theta

/-!
# At `r = 1` the deformed bracket is `Kappa.lean`'s

The base bracket has rational constant coefficients, so `emb0` (evaluation at `β = 0`) and `embS s`
(renaming) agree on it.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- A polynomial that is a rational constant. -/
def IsQ (x : Pmn F n) : Prop := ∃ c : ℚ, x = MvPolynomial.C c

theorem IsQ.zero : IsQ (0 : Pmn F n) := ⟨0, by simp⟩
theorem IsQ.one : IsQ (1 : Pmn F n) := ⟨1, by simp⟩
theorem IsQ.add {x y : Pmn F n} (hx : IsQ x) (hy : IsQ y) : IsQ (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by simp⟩
theorem IsQ.neg {x : Pmn F n} (hx : IsQ x) : IsQ (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by simp⟩
theorem IsQ.sub {x y : Pmn F n} (hx : IsQ x) (hy : IsQ y) : IsQ (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, by simp⟩
theorem IsQ.rsmul (q : ℚ) {x : Pmn F n} (hx : IsQ x) : IsQ (q • x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨q * a, by simp [MvPolynomial.smul_eq_C_mul]⟩

theorem IsQ_eN (b k : OspBasis F n) : IsQ (eN b k) := by
  unfold eN; split_ifs
  · exact IsQ.one
  · exact IsQ.zero

theorem IsQ_Sof (i j : F.K) (k : OspBasis F n) : IsQ (Sof i j k) := by
  unfold Sof; split_ifs
  · exact IsQ_eN _ _
  · simpa using (IsQ_eN _ _).neg
  · exact IsQ.zero

theorem emb0_eq_embS {x : Pmn F n} (hx : IsQ x) (s : Fin r) :
    emb0 (r := r) x = embS s x := by
  obtain ⟨c, rfl⟩ := hx
  simp [emb0, embS]

theorem IsQ_bracketLL (u v w z : I n) (k : OspBasis F n) : IsQ (bracketLL (F := F) u v w z k) := by
  simp only [bracketLL, Pi.add_apply, Pi.smul_apply]
  exact ((((IsQ_eN _ _).rsmul _).add ((IsQ_eN _ _).rsmul _)).add ((IsQ_eN _ _).rsmul _)).add
    ((IsQ_eN _ _).rsmul _)

theorem IsQ_bracketSS (i j k l : F.K) (m : OspBasis F n) : IsQ (bracketSS (n := n) i j k l m) := by
  simp only [bracketSS, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact ((((IsQ_Sof _ _ _).rsmul _).sub ((IsQ_Sof _ _ _).rsmul _)).sub
    ((IsQ_Sof _ _ _).rsmul _)).add ((IsQ_Sof _ _ _).rsmul _)

theorem IsQ_bracketLF (u v w : I n) (i : F.K) (k : OspBasis F n) :
    IsQ (bracketLF u v w i k) := by
  simp only [bracketLF, Pi.add_apply, Pi.smul_apply]
  exact ((IsQ_eN _ _).rsmul _).add ((IsQ_eN _ _).rsmul _)

theorem IsQ_bracketSF (j k : F.K) (w : I n) (i : F.K) (m : OspBasis F n) :
    IsQ (bracketSF j k w i m) := by
  simp only [bracketSF, Pi.sub_apply, Pi.smul_apply]
  exact ((IsQ_eN _ _).rsmul _).sub ((IsQ_eN _ _).rsmul _)

theorem IsQ_bracketFF (u : I n) (i : F.K) (v : I n) (j : F.K) (k : OspBasis F n) :
    IsQ (bracketFF u i v j k) := by
  simp only [bracketFF, Pi.add_apply, Pi.smul_apply]
  exact ((IsQ_Sof _ _ _).rsmul _).add ((IsQ_eN _ _).rsmul _)

theorem IsQ_bracket0Basis (X Y Z : OspBasis F n) : IsQ (bracket0Basis X Y Z) := by
  rcases X with ⟨⟨u, v⟩, hx⟩ | ⟨⟨i, j⟩, hx⟩ | ⟨u, i⟩ <;>
  rcases Y with ⟨⟨w, z⟩, hy⟩ | ⟨⟨k, l⟩, hy⟩ | ⟨w, k⟩
  · exact IsQ_bracketLL _ _ _ _ _
  · exact IsQ.zero
  · exact IsQ_bracketLF _ _ _ _ _
  · exact IsQ.zero
  · exact IsQ_bracketSS _ _ _ _ _
  · exact IsQ_bracketSF _ _ _ _ _
  · simpa [bracket0Basis] using (IsQ_bracketLF _ _ _ _ _).neg
  · simpa [bracket0Basis] using (IsQ_bracketSF _ _ _ _ _).neg
  · exact IsQ_bracketFF _ _ _ _ _

theorem fin1_cases (U : Finset (Fin 1)) : U = ∅ ∨ U = {0} := by
  rcases U.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · right
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    obtain ⟨y, hy⟩ := h
    have : y = 0 := Subsingleton.elim _ _
    subst this
    simpa using hy

-- the case analysis is closed by one `simp` over the definitions; the residual goals are stated
-- and closed explicitly below
theorem bracketBetaMBasis_r1' (p q : RBasis F n) :
    bracketBetaMBasis (F := F) (n := n) (r := 1) (p.1, toS1 p.2) (q.1, toS1 q.2) =
      ofR1 (bracketRBetaBasis p q) := by
  obtain ⟨X, a⟩ := p
  obtain ⟨Y, b⟩ := q
  funext ⟨Z, U⟩
  rcases fin1_cases U with rfl | rfl <;> cases a <;> cases b <;>
    simp only [bracketBetaMBasis, bracket0MBasis, toS1, Finset.card_empty, zero_mul, pow_zero,
      gs, disjoint_self, Finset.bot_eq_empty, ↓reduceIte, Finset.product_empty,
      Finset.filter_empty, mul_one, Finset.union_idempotent, one_smul, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Finset.disjoint_singleton_right, Finset.notMem_empty,
      not_false_eq_true, Finset.product_singleton, Finset.map_empty, Finset.empty_union,
      GammaSBasis, Finset.sum_singleton, Pi.add_apply, kap, liftBy, Finset.empty_ne_singleton,
      add_zero, ofR1, bracketRBetaBasis, iotaR, Bool.false_eq_true, kappaEmbed,
      Finset.card_singleton, one_mul, Finset.disjoint_singleton_left, Finset.mem_singleton,
      Finset.map_singleton, Function.Embedding.sectL_apply, ite_not, mul_ite, mul_zero,
      Finset.singleton_union, ite_smul, zero_smul, Pi.smul_apply, smul_zero, Pi.zero_apply,
      map_zero, Finset.union_empty, ite_self, Finset.sum_const_zero,
      Finset.singleton_ne_empty, zero_add, map_smul]
  · exact emb0_eq_embS (IsQ_bracket0Basis X Y Z) 0
  · rw [emb0_eq_embS (IsQ_bracket0Basis X Y Z) 0]
    have hg : ((-1 : ℚ) ^ (parity X).val) = gsign (parity X) 1 := by
      generalize parity X = z
      have h0 : (0 : ZMod 2) ≠ 1 := by decide
      have v1 : (1 : ZMod 2).val = 1 := rfl
      have v0 : (0 : ZMod 2).val = 0 := rfl
      have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases hz z with rfl | rfl
      · simp [gsign, h0, v0]
      · simp [gsign, v1]
    rw [hg]
  · exact emb0_eq_embS (IsQ_bracket0Basis X Y Z) 0

end Multi
end OspN
end OspOddDeformations
