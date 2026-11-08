import OspOddDeformations.OspN.Bracket

/-!
# The degree law and super-skew symmetry of `[·,·]_0`, for every `osp(N|2n)`

`bracket0Basis_degree` and `bracket0Basis_super_skew` for a general `FermionIndex`, using
`F.key`/`F.dual`/`F.g`/`F.g_symm`. The bosonic lemmas (`Bmn.IKey_injective`, `Bmn.J_antisymm`)
are reused directly by import. Nothing in the argument uses the concrete shape of the fermion
index (for odd `N`, `Option (Fin m × Bool)`).
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I J IKey IKey_injective J_antisymm)

theorem Lof_comm {F : FermionIndex} {n : ℕ} (u v : I n) : (Lof u v : OspBasis F n) = Lof v u := by
  rcases eq_or_ne u v with heq | hne
  · subst heq; rfl
  · rcases lt_trichotomy (IKey u) (IKey v) with hlt | heqk | hgt
    · have hji : ¬ IKey v ≤ IKey u := by omega
      unfold Lof
      simp only [hlt.le, hji, ↓reduceDIte]; rfl
    · exact absurd (IKey_injective heqk) hne
    · have hij : ¬ IKey u ≤ IKey v := by omega
      unfold Lof
      simp only [hij, hgt.le, ↓reduceDIte]; rfl

theorem Sof_antisymm {F : FermionIndex} {n : ℕ} (i j : F.K) :
    (Sof i j : OspMod F n) = -Sof j i := by
  rcases lt_trichotomy (F.key i) (F.key j) with h | h | h
  · have hji : ¬ F.key j < F.key i := by omega
    unfold Sof
    simp only [h, hji, ↓reduceDIte]
    simp
  · unfold Sof
    have h1 : ¬ F.key i < F.key j := by omega
    have h2 : ¬ F.key j < F.key i := by omega
    simp only [h1, h2, ↓reduceDIte]
    simp
  · have hij : ¬ F.key i < F.key j := by omega
    unfold Sof
    simp only [hij, h, ↓reduceDIte]

@[simp] theorem eN_Lof_apply_inr {F : FermionIndex} {n : ℕ} (u v : I n)
    (x : {q : F.K × F.K // F.key q.1 < F.key q.2} ⊕ (I n × F.K)) :
    eN (Lof u v : OspBasis F n) (Sum.inr x) = 0 := by
  unfold Lof
  by_cases hc : IKey u ≤ IKey v <;> simp only [hc, ↓reduceDIte] <;> simp [eN]

@[simp] theorem eN_Fof_apply_inl {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K)
    (p : {q : I n × I n // IKey q.1 ≤ IKey q.2}) :
    eN (Fof u i : OspBasis F n) (Sum.inl p) = 0 := by
  unfold eN Fof; rw [ite_eq_right]; intro hh; cases hh

@[simp] theorem eN_Fof_apply_inrS {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K)
    (s : {q : F.K × F.K // F.key q.1 < F.key q.2}) :
    eN (Fof u i : OspBasis F n) (Sum.inr (Sum.inl s)) = 0 := by
  unfold eN Fof; rw [ite_eq_right]; intro hh; cases hh

@[simp] theorem Sof_apply_inl {F : FermionIndex} {n : ℕ} (i j : F.K)
    (p : {q : I n × I n // IKey q.1 ≤ IKey q.2}) :
    (Sof i j : OspMod F n) (Sum.inl p) = 0 := by
  unfold Sof
  split_ifs
  · unfold eN; rw [ite_eq_right]; intro hh; cases hh
  · change -eN _ (Sum.inl p) = 0
    unfold eN; rw [ite_eq_right]
    · ring
    · intro hh; cases hh
  · rfl

@[simp] theorem Sof_apply_inrF {F : FermionIndex} {n : ℕ} (i j : F.K) (u : I n) (q : F.K) :
    (Sof i j : OspMod F n) (Sum.inr (Sum.inr (u, q))) = 0 := by
  unfold Sof
  split_ifs
  · unfold eN; rw [ite_eq_right]; intro hh; cases hh
  · change -eN _ (Sum.inr (Sum.inr (u, q))) = 0
    unfold eN; rw [ite_eq_right]
    · ring
    · intro hh; cases hh
  · rfl

/-! ## The degree law -/

theorem bracket0Basis_degree {F : FermionIndex} {n : ℕ} (i j k : OspBasis F n)
    (h : bracket0Basis i j k ≠ 0) : parity k = parity i + parity j := by
  -- toolchain port (v4.34): the `OspMod` evaluation lemmas, restated on the sum type itself
  have happ : ∀ (x y : OspMod F n) (k : {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕
      {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)), (x + y) k = x k + y k :=
    fun _ _ _ => rfl
  have hsm : ∀ (c : Pmn F n) (x : OspMod F n) (k : {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕
      {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)), (c • x) k = c * x k :=
    fun _ _ _ => rfl
  have hng : ∀ (x : OspMod F n) (k : {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕
      {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)), (-x) k = -x k :=
    fun _ _ => rfl
  have hsq : ∀ (c : ℚ) (x : OspMod F n) (k : {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕
      {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)), (c • x) k = c • x k :=
    fun _ _ _ => rfl
  have hsb : ∀ (x y : OspMod F n) (k : {p : I n × I n // IKey p.1 ≤ IKey p.2} ⊕
      {p : F.K × F.K // F.key p.1 < F.key p.2} ⊕ (I n × F.K)), (x - y) k = x k - y k :=
    fun _ _ _ => rfl
  match i, j with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    match k with
    | .inl _ => rfl
    | .inr (.inl ⟨(r, s), _⟩) => exfalso; apply h; simp [bracket0Basis, bracketLL, happ,
        hsq]
    | .inr (.inr (w', p')) => exfalso; apply h; simp [bracket0Basis, bracketLL, happ,
        hsq]
  | .inl _, .inr (.inl _) => exact absurd rfl h
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, p)) =>
    match k with
    | .inr (.inr _) => rfl
    | .inl ⟨(a, b), _⟩ => exfalso; apply h; simp [bracket0Basis, bracketLF, happ,
        hsq]
    | .inr (.inl ⟨(r, s), _⟩) => exfalso; apply h; simp [bracket0Basis, bracketLF, happ,
        hsq]
  | .inr (.inl _), .inl _ => exact absurd rfl h
  | .inr (.inl ⟨(p, q), _⟩), .inr (.inl ⟨(r, s), _⟩) =>
    match k with
    | .inr (.inl _) => rfl
    | .inl ⟨(a, b), _⟩ =>
      exfalso; apply h
      simp [bracket0Basis, bracketSS, happ, hsq, hsb]
    | .inr (.inr (w', p')) =>
      exfalso; apply h
      simp [bracket0Basis, bracketSS, happ, hsq, hsb]
  | .inr (.inl ⟨(p, q), _⟩), .inr (.inr (w, r)) =>
    match k with
    | .inr (.inr _) => rfl
    | .inl ⟨(a, b), _⟩ => exfalso; apply h; simp [bracket0Basis, bracketSF, hsq,
        hsb]
    | .inr (.inl ⟨(c, d), _⟩) => exfalso; apply h; simp [bracket0Basis, bracketSF, hsq,
        hsb]
  | .inr (.inr (w, p)), .inl ⟨(u, v), _⟩ =>
    match k with
    | .inr (.inr _) => rfl
    | .inl ⟨(a, b), _⟩ => exfalso; apply h; simp [bracket0Basis, bracketLF, happ, hng,
        hsq]
    | .inr (.inl ⟨(r, s), _⟩) => exfalso; apply h; simp [bracket0Basis, bracketLF, happ, hng,
        hsq]
  | .inr (.inr (w, p)), .inr (.inl ⟨(r, s), _⟩) =>
    match k with
    | .inr (.inr _) => rfl
    | .inl ⟨(a, b), _⟩ => exfalso; apply h; simp [bracket0Basis, bracketSF, hng, hsq,
        hsb]
    | .inr (.inl ⟨(c, d), _⟩) => exfalso; apply h; simp [bracket0Basis, bracketSF, hng, hsq,
        hsb]
  | .inr (.inr (u, p)), .inr (.inr (v, q)) =>
    match k with
    | .inl _ => rfl
    | .inr (.inl _) => rfl
    | .inr (.inr (w', p')) =>
      exfalso; apply h
      simp [bracket0Basis, bracketFF, happ, hsq]

/-! ## Super-skew symmetry -/

theorem gsign_00 : gsign (0 : ZMod 2) (0 : ZMod 2) = 1
    := by unfold gsign; rw [ite_eq_right (by decide)]
theorem gsign_01 : gsign (0 : ZMod 2) (1 : ZMod 2) = 1
    := by unfold gsign; rw [ite_eq_right (by decide)]
theorem gsign_10 : gsign (1 : ZMod 2) (0 : ZMod 2) = 1
    := by unfold gsign; rw [ite_eq_right (by decide)]
theorem gsign_11 : gsign (1 : ZMod 2) (1 : ZMod 2) = -1
    := by unfold gsign; rw [ite_eq_left (by decide)]

theorem superskew_LL {F : FermionIndex} {n : ℕ} (u v w z : I n) :
    (bracketLL u v w z : OspMod F n) = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • bracketLL w z u v := by
  rw [gsign_00, neg_smul, one_smul]
  unfold bracketLL
  rw [J_antisymm v w, J_antisymm u w, J_antisymm v z, J_antisymm u z,
      Lof_comm (F := F) w v, Lof_comm (F := F) z v, Lof_comm (F := F) w u, Lof_comm (F := F) z u]
  simp only [mul_neg, neg_smul]
  abel

theorem superskew_SS {F : FermionIndex} {n : ℕ} (p q r s : F.K) :
    (bracketSS p q r s : OspMod F n) = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • bracketSS r s p q := by
  rw [gsign_00, neg_smul, one_smul]
  unfold bracketSS
  rw [F.g_symm q r, F.g_symm p r, F.g_symm q s, F.g_symm p s,
      Sof_antisymm (F := F) (n := n) p s, Sof_antisymm (F := F) (n := n) q s,
      Sof_antisymm (F := F) (n := n) p r, Sof_antisymm (F := F) (n := n) q r]
  simp only [smul_neg]
  abel

theorem superskew_LF {F : FermionIndex} {n : ℕ} (u v w : I n) (p : F.K) :
    (bracketLF u v w p : OspMod F n)
      = -(gsign (0 : ZMod 2) (1 : ZMod 2)) • (-bracketLF u v w p) := by
  rw [gsign_01, neg_smul, one_smul, neg_neg]

theorem superskew_FL {F : FermionIndex} {n : ℕ} (u v w : I n) (p : F.K) :
    (-bracketLF u v w p : OspMod F n) = -(gsign (1 : ZMod 2) (0 : ZMod 2)) • bracketLF u v w p := by
  rw [gsign_10, neg_smul, one_smul]

theorem superskew_SF {F : FermionIndex} {n : ℕ} (p q : F.K) (w : I n) (r : F.K) :
    (bracketSF p q w r : OspMod F n)
      = -(gsign (0 : ZMod 2) (1 : ZMod 2)) • (-bracketSF p q w r) := by
  rw [gsign_01, neg_smul, one_smul, neg_neg]

theorem superskew_FS {F : FermionIndex} {n : ℕ} (p q : F.K) (w : I n) (r : F.K) :
    (-bracketSF p q w r : OspMod F n) = -(gsign (1 : ZMod 2) (0 : ZMod 2)) • bracketSF p q w r := by
  rw [gsign_10, neg_smul, one_smul]

theorem superskew_FF {F : FermionIndex} {n : ℕ} (u : I n) (p : F.K) (v : I n) (q : F.K) :
    (bracketFF u p v q : OspMod F n) = -(gsign (1 : ZMod 2) (1 : ZMod 2)) • bracketFF v q u p := by
  rw [gsign_11, neg_neg, one_smul]
  unfold bracketFF
  rw [J_antisymm u v, F.g_symm p q, Sof_antisymm (F := F) (n := n) p q, Lof_comm (F := F) v u]
  simp only [mul_neg, neg_smul, smul_neg, neg_neg]

theorem bracket0Basis_super_skew {F : FermionIndex} {n : ℕ} (i j : OspBasis F n) :
    bracket0Basis i j = -(gsign (parity i) (parity j)) • bracket0Basis j i := by
  match i, j with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    change bracketLL u v w z = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • bracketLL w z u v
    exact superskew_LL u v w z
  | .inl _, .inr (.inl _) =>
    change (0 : OspMod F n) = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • (0 : OspMod F n)
    simp
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, p)) =>
    change bracketLF u v w p = -(gsign (0 : ZMod 2) (1 : ZMod 2)) • (-bracketLF u v w p)
    exact superskew_LF u v w p
  | .inr (.inl _), .inl _ =>
    change (0 : OspMod F n) = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • (0 : OspMod F n)
    simp
  | .inr (.inl ⟨(p, q), _⟩), .inr (.inl ⟨(r, s), _⟩) =>
    change bracketSS p q r s = -(gsign (0 : ZMod 2) (0 : ZMod 2)) • bracketSS r s p q
    exact superskew_SS p q r s
  | .inr (.inl ⟨(p, q), _⟩), .inr (.inr (w, r)) =>
    change bracketSF p q w r = -(gsign (0 : ZMod 2) (1 : ZMod 2)) • (-bracketSF p q w r)
    exact superskew_SF p q w r
  | .inr (.inr (w, p)), .inl ⟨(u, v), _⟩ =>
    change (-bracketLF u v w p : OspMod F n)
      = -(gsign (1 : ZMod 2) (0 : ZMod 2)) • bracketLF u v w p
    exact superskew_FL u v w p
  | .inr (.inr (w, p)), .inr (.inl ⟨(r, s), _⟩) =>
    change (-bracketSF r s w p : OspMod F n)
      = -(gsign (1 : ZMod 2) (0 : ZMod 2)) • bracketSF r s w p
    exact superskew_FS r s w p
  | .inr (.inr (u, p)), .inr (.inr (v, q)) =>
    change bracketFF u p v q = -(gsign (1 : ZMod 2) (1 : ZMod 2)) • bracketFF v q u p
    exact superskew_FF u p v q

end OspN
end OspOddDeformations
