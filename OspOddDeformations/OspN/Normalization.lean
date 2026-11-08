import OspOddDeformations.OspN.FBeta

/-!
# The normalization of `f_β` that does not need Whitehead's lemma; the inverse of `T_β`

Paper: Corollary 4.8 (the inverse of `T_β = id + κ(f_β)_R`), Corollary 4.10 and Section 6 ("The
`so(N)` correction"). What is stated here ranges over the primitives of the form `h̃ − ad Z` with
`Z` odd. Theorem 4.9, that these are all the odd primitives, is proved in
`GroupB/AllPrimitives.lean` (with a grading element of `sp(2n)` instead of Whitehead's lemma), and
Corollary 4.10 over all odd primitives follows there.
-/

-- `OspBasis` is a plain `def` whose sum structure the proofs below use (`Lof_self`, `eN_Fof_Fof`);
-- restore the pre-v4.34 type-transparency behaviour of `isDefEq`, as in `OspN/SourceTensor.lean`.
set_option backward.isDefEq.respectTransparency.types false

namespace OspOddDeformations
namespace OspN

open Bmn (I J)

/-- `T_β⁻¹ = id − κ(f_β)_R` (paper Corollary 4.8). -/
noncomputable def TBetaFInv {F : FermionIndex} {n : ℕ} (r : RMod F n) : RMod F n :=
  r - kappaMulR (fBetaR r)

theorem TBetaFInv_eq {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    TBetaFInv r = r - kappaEmbed (fBeta F n (falsePart r)) := by
  unfold TBetaFInv fBetaR
  rw [kappaMulR_add, kappaMulR_iotaR, kappaMulR_kappaEmbed, add_zero]

theorem falsePart_TBetaFInv {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    falsePart (TBetaFInv r) = falsePart r := by
  rw [TBetaFInv_eq, sub_eq_add_neg, falsePart_add, falsePart_neg, falsePart_kappaEmbed, neg_zero,
    add_zero]

/-- Paper Corollary 4.8, the inverse: `id − κ(f_β)_R` is a left inverse of `T_β`. -/
theorem TBetaFInv_TBetaF {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    TBetaFInv (TBetaF r) = r := by
  rw [TBetaFInv_eq, falsePart_TBetaF, TBetaF_eq]
  abel

/-- Paper Corollary 4.8, the inverse: `id − κ(f_β)_R` is a right inverse of `T_β`. -/
theorem TBetaF_TBetaFInv {F : FermionIndex} {n : ℕ} (r : RMod F n) :
    TBetaF (TBetaFInv r) = r := by
  rw [TBetaF_eq, falsePart_TBetaFInv, TBetaFInv_eq]
  abel

/-! ### Coordinates of basis vectors, used below -/

theorem Lof_self {F : FermionIndex} {n : ℕ} (u : I n) :
    (Lof u u : OspBasis F n) = Sum.inl ⟨(u, u), le_refl _⟩ := by
  unfold Lof; simp only [le_refl, ↓reduceDIte]

theorem eN_Fof_Fof {F : FermionIndex} {n : ℕ} (u u' : I n) (i i' : F.K) :
    eN (Fof u i : OspBasis F n) (Fof u' i') = if u' = u ∧ i' = i then 1 else 0 := by
  unfold eN
  by_cases h : u' = u ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have hne : (Fof u' i' : OspBasis F n) ≠ Fof u i := by
      intro e
      apply h
      simp only [Fof] at e
      exact Prod.mk.inj (Sum.inr.inj (Sum.inr.inj e))
    simp [hne, h]

/-- `[F_{t,i}, L_{uu}]_0 = -J_{ut} F_{u,i}`. -/
theorem bracket0Basis_Fof_Luu {F : FermionIndex} {n : ℕ} (t u : I n) (i : F.K) :
    bracket0Basis (Fof t i : OspBasis F n) (Lof u u) = -((J n u t : ℚ) • eN (Fof u i)) := by
  rw [Lof_self]
  change -bracketLF u u t i = _
  unfold bracketLF
  rw [← add_smul]
  congr 2
  ring

/-- `J_{t̄,t'}` (with `t̄` the partner of `t`) vanishes unless `t' = t`, and `J_{t̄,t} = ±1`. -/
theorem J_partner {n : ℕ} (t t' : I n) : (J n (t.1, !t.2) t' ≠ 0) ↔ t' = t := by
  obtain ⟨k, b⟩ := t
  obtain ⟨k', b'⟩ := t'
  cases b <;> cases b' <;> simp [J, eq_comm]

/-- The `S_{pq}`-coordinate (`p < q`) of `S_{ab}`: `+1` if `(a,b) = (p,q)`, `-1` if
`(a,b) = (q,p)`. -/
theorem Sof_apply_S {F : FermionIndex} {n : ℕ} (a b p q : F.K) (hpq : F.key p < F.key q) :
    (Sof a b : OspMod F n) (Sum.inr (Sum.inl ⟨(p, q), hpq⟩)) =
      (if a = p ∧ b = q then 1 else 0) - (if a = q ∧ b = p then 1 else 0) := by
  have inj : ∀ {x y : F.K × F.K} {hx : F.key x.1 < F.key x.2} {hy : F.key y.1 < F.key y.2},
      (Sum.inr (Sum.inl ⟨x, hx⟩) : OspBasis F n) = Sum.inr (Sum.inl ⟨y, hy⟩) → x = y :=
    fun e => congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj e))
  unfold Sof eN
  by_cases h1 : F.key a < F.key b
  · simp only [h1, ↓reduceDIte]
    have hn2 : ¬(a = q ∧ b = p) := by
      rintro ⟨rfl, rfl⟩; exact lt_irrefl _ (h1.trans hpq)
    by_cases e : a = p ∧ b = q
    · obtain ⟨rfl, rfl⟩ := e
      simp only [hn2, and_self, ↓reduceIte, sub_zero]
    · have hne : (Sum.inr (Sum.inl ⟨(p, q), hpq⟩) : OspBasis F n) ≠
          Sum.inr (Sum.inl ⟨(a, b), h1⟩) :=
        fun e' => e (by
          have := inj e'; simp only [Prod.mk.injEq] at this; exact ⟨this.1.symm, this.2.symm⟩)
      simp only [e, hn2, ↓reduceIte, sub_zero]
      split_ifs with hc
      · exact absurd hc hne
      · rfl
  · simp only [h1, ↓reduceDIte]
    have hn1 : ¬(a = p ∧ b = q) := by
      rintro ⟨rfl, rfl⟩; exact h1 hpq
    by_cases h2 : F.key b < F.key a
    · simp only [h2, ↓reduceDIte]
      by_cases e : a = q ∧ b = p
      · obtain ⟨rfl, rfl⟩ := e
        simp only [hn1, and_self, ↓reduceIte, zero_sub, Pi.neg_apply]
      · have hne : (Sum.inr (Sum.inl ⟨(p, q), hpq⟩) : OspBasis F n) ≠
            Sum.inr (Sum.inl ⟨(b, a), h2⟩) :=
          fun e' => e (by
            have := inj e'; simp only [Prod.mk.injEq] at this; exact ⟨this.2.symm, this.1.symm⟩)
        simp only [e, hn1, ↓reduceIte, sub_zero, Pi.neg_apply]
        split_ifs with hc
        · exact absurd hc hne
        · simp
    · simp only [h2, ↓reduceDIte]
      have hab : a = b := F.key_injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
      have hn2 : ¬(a = q ∧ b = p) := by
        rintro ⟨rfl, rfl⟩; subst hab; exact lt_irrefl _ hpq
      simp only [hn1, hn2, ↓reduceIte, sub_zero]
      rfl

theorem dual_eq_iff {F : FermionIndex} (j k : F.K) : F.dual j = k ↔ j = F.dual k := by
  constructor
  · rintro rfl; rw [F.dual_dual]
  · rintro rfl; rw [F.dual_dual]

theorem beta_ne_zero {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K) : beta F n u i ≠ 0 :=
  MvPolynomial.X_ne_zero _

/-- The step in the proof of Corollary 4.10: an odd element whose adjoint action vanishes on
`sp(2n)` (the `L_{uw}`) is zero. -/
theorem odd_eq_zero_of_ad_Lof {F : FermionIndex} {n : ℕ} (W : OspMod F n)
    (hW : ∀ k : OspBasis F n, W k ≠ 0 → parity k = 1)
    (h : ∀ u w : I n, ad W (eN (Lof u w) : OspMod F n) = 0) : W = 0 := by
  funext k
  match k with
  | .inl p =>
    by_contra hne
    exact absurd (hW _ hne) (by simp [parity])
  | .inr (.inl s) =>
    by_contra hne
    exact absurd (hW _ hne) (by simp [parity])
  | .inr (.inr (t, i)) =>
    have h1 := congrFun (h (t.1, !t.2) (t.1, !t.2)) (Fof (t.1, !t.2) i)
    simp only [ad, bracket0_eN_right, Finset.sum_apply, ospMod_smul_apply, ospMod_zero_apply] at h1
    rw [Finset.sum_eq_single (Fof t i)] at h1
    · rw [bracket0Basis_Fof_Luu, ospMod_neg_apply, qsmul_eq_Csmul, ospMod_smul_apply,
        eN_Fof_Fof] at h1
      have hJ : (J n (t.1, !t.2) t : ℚ) ≠ 0 := (J_partner t t).mpr rfl
      simp only [and_self, ↓reduceIte, mul_one] at h1
      have h2 : W (Fof t i) * MvPolynomial.C (J n (t.1, !t.2) t) = 0 := by
        rw [← neg_eq_zero, ← mul_neg]; exact h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd ((MvPolynomial.C_eq_zero).mp h3) hJ
    · intro j _ hj
      by_cases hWj : W j = 0
      · rw [hWj, zero_mul]
      · match j, hj, hW j hWj with
        | .inl _, _, hp => exact absurd hp (by simp [parity])
        | .inr (.inl _), _, hp => exact absurd hp (by simp [parity])
        | .inr (.inr (t', i')), hj, _ =>
          have hb : bracket0Basis (Fof t' i' : OspBasis F n) (Lof (t.1, !t.2) (t.1, !t.2))
              (Fof (t.1, !t.2) i) = 0 := by
            rw [bracket0Basis_Fof_Luu, ospMod_neg_apply, qsmul_eq_Csmul, ospMod_smul_apply,
              eN_Fof_Fof]
            by_cases hi : i = i'
            · have ht : t' ≠ t := by
                intro e; apply hj; rw [e, ← hi]; rfl
              have hJ0 : (J n (t.1, !t.2) t' : ℚ) = 0 := by
                by_contra hc; exact ht ((J_partner t t').mp hc)
              simp [hJ0]
            · simp [hi]
          exact (congrArg (W (Sum.inr (Sum.inr (t', i'))) * ·) hb).trans (mul_zero _)
    · intro hn; exact absurd (Finset.mem_univ _) hn

/-- Paper Corollary 4.10, first sentence, within the primitives `h̃ − ad Z` (`Z` odd): such a
primitive vanishes on `sp(2n)` exactly when `Z = Z_β`, i.e. when it is `f_β`. -/
theorem fBeta_unique_vanishing_sp {F : FermionIndex} {n : ℕ} (Z : OspMod F n)
    (hZ : ∀ k : OspBasis F n, Z k ≠ 0 → parity k = 1)
    (h : ∀ u w : I n, hTilde (eN (Lof u w) : OspMod F n) - ad Z (eN (Lof u w)) = 0) :
    Z = Zbeta F n := by
  have hodd : ∀ k : OspBasis F n, (Z - Zbeta F n) k ≠ 0 → parity k = 1 := by
    intro k hk
    by_cases hz : Z k = 0
    · have : Zbeta F n k ≠ 0 := by
        intro h0; apply hk; simp [hz, h0]
      exact Zbeta_odd F n k this
    · exact hZ k hz
  have hzero := odd_eq_zero_of_ad_Lof (Z - Zbeta F n) hodd (fun u w => by
    have h1 := h u w
    have h2 := fBeta_L F n u w
    simp only [fBeta] at h2
    simp only [ad] at h1 h2 ⊢
    rw [bracket0_sub_left]
    rw [sub_eq_zero] at h1 h2 ⊢
    rw [← h1, ← h2])
  exact sub_eq_zero.mp hzero

/-- Paper Section 6, "The `so(N)` correction": `h̃(F_{u,i}) ≠ 0` as soon as `K` has an index
other than `i` (so for every `N ≥ 2`). -/
theorem hTilde_Fof_ne_zero {F : FermionIndex} {n : ℕ} (u : I n) (i : F.K)
    (h : ∃ k : F.K, k ≠ i) : hTilde (eN (Fof u i) : OspMod F n) ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hTilde_eN, hTildeBasis_Fof]
  intro h0
  rcases lt_trichotomy (F.key k) (F.key i) with hlt | heq | hgt
  · have h1 := congrFun h0 (Sum.inr (Sum.inl ⟨(k, i), hlt⟩))
    simp only [qsmul_eq_Csmul, ospMod_smul_apply, Finset.sum_apply, ospMod_zero_apply,
      Sof_apply_S, dual_eq_iff] at h1
    simp [hk.symm, beta_ne_zero] at h1
  · exact hk (F.key_injective heq)
  · have h1 := congrFun h0 (Sum.inr (Sum.inl ⟨(i, k), hgt⟩))
    simp only [qsmul_eq_Csmul, ospMod_smul_apply, Finset.sum_apply, ospMod_zero_apply,
      Sof_apply_S, dual_eq_iff] at h1
    simp [hk.symm, beta_ne_zero] at h1

/-- Paper Corollary 4.10's proof and Section 6: `f_β(S_{ij}) ≠ 0` for `i ≠ j` (so
`f_β(so(N)) ≠ 0` for every `N ≥ 2`), when `n ≥ 1`. -/
theorem fBeta_Sof_ne_zero (F : FermionIndex) (n : ℕ) (hn : 0 < n) (i j : F.K) (hij : i ≠ j) :
    fBeta F n (Sof i j) ≠ 0 := by
  rw [fBeta_S]
  intro h0
  have h1 := congrFun h0 (Fof (⟨0, hn⟩, false) i)
  simp only [qsmul_eq_Csmul, ospMod_smul_apply, Finset.sum_apply, ospMod_zero_apply, Pi.sub_apply,
    eN_Fof_Fof] at h1
  have hC : (MvPolynomial.C (2 : ℚ) : Pmn F n) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; norm_num
  simp [hij, hC, v, beta_ne_zero] at h1

/-- Paper Corollary 4.10, second sentence, within the primitives `h̃ − ad Z` (`Z` odd): for
`N ≥ 2` and `n ≥ 1`, none vanishes on `sp(2n) ⊕ so(N)`. -/
theorem no_primitive_vanishing_sp_so {F : FermionIndex} {n : ℕ} (hn : 0 < n)
    (hK : ∃ i j : F.K, i ≠ j) (Z : OspMod F n)
    (hZ : ∀ k : OspBasis F n, Z k ≠ 0 → parity k = 1) :
    ¬ ((∀ u w : I n, hTilde (eN (Lof u w) : OspMod F n) - ad Z (eN (Lof u w)) = 0) ∧
      ∀ i j : F.K, hTilde (Sof i j : OspMod F n) - ad Z (Sof i j) = 0) := by
  rintro ⟨hL, hS⟩
  have hZb := fBeta_unique_vanishing_sp Z hZ hL
  obtain ⟨i, j, hij⟩ := hK
  apply fBeta_Sof_ne_zero F n hn i j hij
  have := hS i j
  rw [hZb] at this
  exact this

end OspN
end OspOddDeformations
