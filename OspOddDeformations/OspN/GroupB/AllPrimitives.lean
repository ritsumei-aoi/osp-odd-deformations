import OspOddDeformations.OspN.Normalization

/-!
# Thm 4.9 (every odd primitive is `h̃ − ad Z`) and Cor 4.10 in full

The proof differs from the paper's (which uses Whitehead's lemma for `sp(2n)`): it uses the grading
element `h = Σ_k 2 L_{(k,−),(k,+)}` of `sp(2n)`. `ad h` is diagonal on the basis with integer
eigenvalues (`ad_hEl`), even on `𝔤₀̄` and odd (`±1`) on `𝔤₁̄`. An odd derivation `D` is first made
to vanish at `h` by subtracting `ad Z₀`; then `D'([h,X]) = [h, D'X]` forces `D'X`, whose parity is
the other one, to have only coordinates with eigenvalue `= wt X`, which are of the wrong parity: so
`D' = 0`. Uniqueness is `odd_eq_zero_of_ad_Lof`.
-/

namespace OspOddDeformations
namespace OspN

open Bmn (I J)

variable {F : FermionIndex} {n : ℕ}

/-- `μ_{(k,b)} = ±1`. -/
def mu (w : I n) : ℚ := if w.2 then 1 else -1

/-- The eigenvalue of `ad h` on a basis element. -/
def wt : OspBasis F n → ℚ
  | .inl ⟨(w, z), _⟩ => mu w + mu z
  | .inr (.inl _) => 0
  | .inr (.inr (w, _)) => mu w

/-- The grading element `h = Σ_k 2 L_{(k,false),(k,true)}` of `sp(2n)`. -/
noncomputable def hEl (F : FermionIndex) (n : ℕ) : OspMod F n :=
  ∑ k : Fin n, (2 : ℚ) • eN (Lof (k, false) (k, true))

theorem J_kt (k : Fin n) (w : I n) : J n (k, true) w = if w = (k, false) then -1 else 0 := by
  obtain ⟨k', b⟩ := w; cases b <;> simp [J, eq_comm]

theorem J_kf (k : Fin n) (w : I n) : J n (k, false) w = if w = (k, true) then 1 else 0 := by
  obtain ⟨k', b⟩ := w; cases b <;> simp [J, eq_comm]

theorem Lof_kk (k : Fin n) :
    (Lof (k, false) (k, true) : OspBasis F n)
      = Sum.inl ⟨((k, false), (k, true)), by simp [Bmn.IKey]⟩ := by
  have h : Bmn.IKey (k, false) ≤ Bmn.IKey (k, true) := by simp [Bmn.IKey]
  simp only [Lof, h, ↓reduceDIte]
  rfl

theorem hEl_bracket (Y : OspBasis F n) :
    bracket0 (hEl F n) (eN Y)
      = ∑ k : Fin n, (2 : ℚ) • bracket0Basis (Lof (k, false) (k, true) : OspBasis F n) Y := by
  rw [hEl, bracket0_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bracket0_smul_left_rat, bracket0_eN_eN]

theorem ad_hEl_eN (Y : OspBasis F n) : bracket0 (hEl F n) (eN Y) = wt Y • eN Y := by
  rw [hEl_bracket]
  match Y with
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [Lof_kk]
    simp [bracket0Basis, wt]
  | .inr (.inr ((k0, b), i)) =>
    simp only [Lof_kk]
    rw [Finset.sum_eq_single k0]
    · cases b <;> simp [bracket0Basis, bracketLF, J_kt, J_kf, wt, mu, smul_smul] <;> rfl
    · intro k _ hk
      simp [bracket0Basis, bracketLF, J_kt, J_kf, Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  | .inl ⟨(w, z), hwz⟩ =>
    have hX : (Sum.inl ⟨(w, z), hwz⟩ : OspBasis F n) = Lof w z := by
      simp only [Lof, hwz, ↓reduceDIte]
    have key : ∀ x y : I n,
        ∑ k : Fin n, ((2 : ℚ) * (1 / 2 * J n (k, true) x)) • (eN (Lof (k, false) y) : OspMod F n)
          + ∑ k : Fin n, ((2 : ℚ) * (1 / 2 * J n (k, false) x)) • eN (Lof (k, true) y)
          = mu x • eN (Lof x y) := by
      intro x y
      obtain ⟨k0, b⟩ := x
      rw [← Finset.sum_add_distrib, Finset.sum_eq_single k0]
      · cases b <;> simp [J_kt, J_kf, mu]
      · intro k _ hk
        simp [J_kt, J_kf, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Lof_kk]
    change ∑ k : Fin n, (2 : ℚ) • bracketLL (k, false) (k, true) w z = _
    simp only [bracketLL, smul_add, smul_smul, Finset.sum_add_distrib]
    have k1 := key w z
    have k2 := key z w
    rw [Lof_comm z w] at k2
    rw [show ∀ a b c d : OspMod F n, a + b + c + d = (a + b) + (c + d) by intros; abel, k1]
    simp only [Lof_comm _ w] at k2 ⊢
    rw [k2, ← add_smul, wt, hX]

/-! ## `ad h` on coordinates, and the separation of the eigenvalues -/

theorem ospMod_eq_sum (x : OspMod F n) : x = ∑ X, x X • eN X := by
  funext Y
  simp [Finset.sum_apply, eN]

theorem bracket0_hEl_apply (y : OspMod F n) (Y : OspBasis F n) :
    bracket0 (hEl F n) y Y = MvPolynomial.C (wt Y) * y Y := by
  conv_lhs => rw [ospMod_eq_sum y, bracket0_sum_right]
  simp only [bracket0_smul_right, ad_hEl_eN, Finset.sum_apply, ospMod_smul_apply, qsmul_eq_Csmul]
  rw [Finset.sum_eq_single Y]
  · simp [eN]; ring
  · intro X _ hX; simp [eN, Ne.symm hX]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem wt_ne_of_parity_ne (X Y : OspBasis F n) (h : parity X ≠ parity Y) : wt X ≠ wt Y := by
  have hmu : ∀ w : I n, mu w = 1 ∨ mu w = -1 := fun w => by unfold mu; split_ifs <;> simp
  match X, Y with
  | .inl _, .inl _ => exact absurd rfl h
  | .inl _, .inr (.inl _) => exact absurd rfl h
  | .inr (.inl _), .inl _ => exact absurd rfl h
  | .inr (.inl _), .inr (.inl _) => exact absurd rfl h
  | .inr (.inr _), .inr (.inr _) => exact absurd rfl h
  | .inl ⟨(w, z), _⟩, .inr (.inr (v, _)) =>
    simp only [wt]; rcases hmu w with h1 | h1 <;> rcases hmu z with h2 | h2 <;>
      rcases hmu v with h3 | h3 <;> rw [h1, h2, h3] <;> norm_num
  | .inr (.inl _), .inr (.inr (v, _)) =>
    simp only [wt]; rcases hmu v with h3 | h3 <;> rw [h3] <;> norm_num
  | .inr (.inr (v, _)), .inl ⟨(w, z), _⟩ =>
    simp only [wt]; rcases hmu w with h1 | h1 <;> rcases hmu z with h2 | h2 <;>
      rcases hmu v with h3 | h3 <;> rw [h1, h2, h3] <;> norm_num
  | .inr (.inr (v, _)), .inr (.inl _) =>
    simp only [wt]; rcases hmu v with h3 | h3 <;> rw [h3] <;> norm_num

theorem wt_sq_odd (w : I n) (i : F.K) : wt (Fof w i : OspBasis F n) * wt (Fof w i) = 1 := by
  simp only [Fof, wt, mu]; split_ifs <;> norm_num

/-! ## Linear maps on `𝔤_P` -/

/-- `ad Z` as a `P`-linear map. -/
noncomputable def adLin (Z : OspMod F n) : OspMod F n →ₗ[Pmn F n] OspMod F n where
  toFun := ad Z
  map_add' x y := bracket0_add_right Z x y
  map_smul' c x := bracket0_smul_right c Z x

/-- `h̃` as a `P`-linear map. -/
noncomputable def hTildeLin : OspMod F n →ₗ[Pmn F n] OspMod F n where
  toFun := hTilde
  map_add' := hTilde_add
  map_smul' := hTilde_smul

/-- An odd `P`-linear map: it raises the parity of each basis element by `1`. -/
def IsOddLin (D : OspMod F n →ₗ[Pmn F n] OspMod F n) : Prop :=
  ∀ X k, D (eN X) k ≠ 0 → parity k = parity X + 1

/-- A derivation of `[·,·]_0`: `δD = 0` on basis elements. -/
def IsDer (D : OspMod F n →ₗ[Pmn F n] OspMod F n) : Prop := ∀ X Y, deltaBasis D X Y = 0

/-! ## Thm 4.9 -/

theorem deltaBasis_sub (D E : OspMod F n →ₗ[Pmn F n] OspMod F n) (X Y : OspBasis F n) :
    deltaBasis (D - E) X Y = deltaBasis D X Y - deltaBasis E X Y := by
  simp only [deltaBasis, LinearMap.sub_apply, bracket0_sub_left, bracket0_sub_right, smul_sub]
  abel

theorem linMap_rat_smul (D : OspMod F n →ₗ[Pmn F n] OspMod F n) (q : ℚ) (x : OspMod F n) :
    D (q • x) = q • D x := by
  rw [qsmul_eq_Csmul, map_smul, ← qsmul_eq_Csmul]

theorem bracket0_hEl_left (y : OspMod F n) :
    bracket0 (hEl F n) y = ∑ k : Fin n, (2 : ℚ) • bracket0 (eN (Lof (k, false) (k, true))) y := by
  rw [hEl, bracket0_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bracket0_smul_left_rat]

theorem linMap_hEl (D : OspMod F n →ₗ[Pmn F n] OspMod F n) :
    D (hEl F n) = ∑ k : Fin n, (2 : ℚ) • D (eN (Lof (k, false) (k, true))) := by
  rw [hEl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linMap_rat_smul]

theorem parity_Lof_kk (k : Fin n) : parity (Lof (k, false) (k, true) : OspBasis F n) = 0 := by
  rw [Lof_kk]; rfl

/-- A derivation commutes with `ad h` up to `[D h, ·]`. -/
theorem der_hEl (D : OspMod F n →ₗ[Pmn F n] OspMod F n) (hder : IsDer D) (X : OspBasis F n) :
    bracket0 (D (hEl F n)) (eN X) + bracket0 (hEl F n) (D (eN X))
      = D (bracket0 (hEl F n) (eN X)) := by
  have hk : ∀ k : Fin n,
      bracket0 (D (eN (Lof (k, false) (k, true)))) (eN X)
        + bracket0 (eN (Lof (k, false) (k, true))) (D (eN X))
        = D (bracket0 (eN (Lof (k, false) (k, true))) (eN X)) := by
    intro k
    have h := hder (Lof (k, false) (k, true)) X
    rw [deltaBasis, parity_Lof_kk, gsign_01, one_smul, sub_eq_zero] at h
    exact h
  rw [linMap_hEl, bracket0_sum_left, bracket0_hEl_left, bracket0_hEl_left, map_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bracket0_smul_left_rat, linMap_rat_smul, ← smul_add, hk]

theorem odd_coord (D : OspMod F n →ₗ[Pmn F n] OspMod F n) (hodd : IsOddLin D) (x : OspMod F n)
    (hx : ∀ k, x k ≠ 0 → parity k = 0) : ∀ k, D x k ≠ 0 → parity k = 1 := by
  intro k hk
  rw [ospMod_eq_sum x, map_sum, Finset.sum_apply] at hk
  obtain ⟨X, -, hX⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  rw [map_smul, ospMod_smul_apply] at hX
  have h1 : x X ≠ 0 := left_ne_zero_of_mul hX
  have h2 : D (eN X) k ≠ 0 := right_ne_zero_of_mul hX
  rw [hodd X k h2, hx X h1, zero_add]

/-- `[z, L] = −[L, z]` for odd `z` and a basis element `L` of `sp(2n)`. -/
theorem bracket0_odd_Lof (z : OspMod F n) (hz : ∀ k, z k ≠ 0 → parity k = 1) (k : Fin n) :
    bracket0 z (eN (Lof (k, false) (k, true))) = -bracket0 (eN (Lof (k, false) (k, true))) z := by
  rw [bracket0_eN_right, bracket0_eN_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : z i = 0
  · simp [hi]
  rw [bracket0Basis_super_skew, hz i hi, parity_Lof_kk, gsign_10, neg_one_smul, smul_neg]

/-- **Thm 4.9**, second form: every odd `P`-linear derivation of `[·,·]_0` is `ad Z` for a unique
odd `Z`. -/
theorem der_eq_ad (D : OspMod F n →ₗ[Pmn F n] OspMod F n) (hodd : IsOddLin D) (hder : IsDer D) :
    ∃! Z : OspMod F n, (∀ k, Z k ≠ 0 → parity k = 1) ∧ ∀ x, D x = ad Z x := by
  set d := D (hEl F n) with hd
  have hd_odd : ∀ k, d k ≠ 0 → parity k = 1 := by
    apply odd_coord D hodd
    intro k hk
    rw [hEl, Finset.sum_apply] at hk
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    rw [qsmul_eq_Csmul, ospMod_smul_apply] at hj
    have := right_ne_zero_of_mul hj
    by_contra hne
    apply this
    simp only [eN]
    rw [ite_eq_right_iff.mpr]
    intro e; exact absurd (by rw [e, parity_Lof_kk]) hne
  let Z0 : OspMod F n := fun Y => -(MvPolynomial.C (wt Y) * d Y)
  have hZ0 : ∀ k, Z0 k ≠ 0 → parity k = 1 := by
    intro k hk
    apply hd_odd
    intro h; apply hk; simp [Z0, h]
  have hZ0h : ad Z0 (hEl F n) = d := by
    have h1 : ad Z0 (hEl F n) = -bracket0 (hEl F n) Z0 := by
      rw [ad, hEl, bracket0_sum_right, bracket0_sum_left, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [bracket0_smul_right_rat, bracket0_smul_left_rat, bracket0_odd_Lof Z0 hZ0, smul_neg]
    rw [h1]
    funext Y
    rw [ospMod_neg_apply, bracket0_hEl_apply]
    simp only [Z0]
    by_cases hY : d Y = 0
    · simp [hY]
    have hp := hd_odd Y hY
    have hw : wt Y * wt Y = 1 := by
      match Y, hp with
      | .inl _, hp => exact absurd hp (by simp [parity])
      | .inr (.inl _), hp => exact absurd hp (by simp [parity])
      | .inr (.inr (w, i)), _ => exact wt_sq_odd w i
    calc -(MvPolynomial.C (wt Y) * -(MvPolynomial.C (wt Y) * d Y))
        = MvPolynomial.C (wt Y * wt Y) * d Y := by rw [MvPolynomial.C_mul]; ring
      _ = d Y := by rw [hw, MvPolynomial.C_1, one_mul]
  -- `D' = D − ad Z₀` is an odd derivation vanishing at `h`
  set D' := D - adLin Z0 with hD'
  have hD'odd : IsOddLin D' := by
    intro X k hk
    rw [hD', LinearMap.sub_apply, Pi.sub_apply] at hk
    by_cases h1 : D (eN X) k = 0
    · rw [h1, zero_sub, neg_ne_zero] at hk
      have := bracket0_homog_right 1 Z0 hZ0 X k hk
      rw [this, add_comm]
    · exact hodd X k h1
  have hD'der : IsDer D' := by
    intro X Y
    rw [hD', deltaBasis_sub, hder X Y, zero_sub, neg_eq_zero]
    exact delta_ad_eq_zero_basis Z0 hZ0 X Y
  have hD'h : D' (hEl F n) = 0 := by
    rw [hD', LinearMap.sub_apply, ← hd]
    exact sub_eq_zero.mpr hZ0h.symm
  have hD'X : ∀ X, D' (eN X) = 0 := by
    intro X
    have hc := der_hEl D' hD'der X
    rw [hD'h, bracket0_zero_left, zero_add, ad_hEl_eN, linMap_rat_smul] at hc
    funext Y
    have hY := congrFun hc Y
    rw [bracket0_hEl_apply, qsmul_eq_Csmul, ospMod_smul_apply] at hY
    by_contra hne
    have hp := hD'odd X Y hne
    have hdiff : MvPolynomial.C (wt Y - wt X) * D' (eN X) Y = 0 := by
      rw [MvPolynomial.C_sub, sub_mul, hY, sub_self]
    rcases mul_eq_zero.mp hdiff with h | h
    · rw [MvPolynomial.C_eq_zero, sub_eq_zero] at h
      apply wt_ne_of_parity_ne Y X _ h
      rw [hp]
      have h2 : ∀ a : ZMod 2, a + 1 ≠ a := by decide
      exact h2 _
    · exact hne h
  have hD'0 : ∀ x, D' x = 0 := by
    intro x
    rw [ospMod_eq_sum x, map_sum]
    exact Finset.sum_eq_zero fun X _ => by rw [map_smul, hD'X, smul_zero]
  refine ⟨Z0, ⟨hZ0, fun x => ?_⟩, ?_⟩
  · have := hD'0 x
    rw [hD', LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  · rintro Z' ⟨hZ', hDZ'⟩
    have hsub : Z' - Z0 = 0 := by
      apply odd_eq_zero_of_ad_Lof
      · intro k hk
        by_cases h1 : Z' k = 0
        · rw [Pi.sub_apply, h1, zero_sub, neg_ne_zero] at hk; exact hZ0 k hk
        · exact hZ' k h1
      · intro u w
        rw [ad, bracket0_sub_left]
        have e1 := hDZ' (eN (Lof u w))
        have e2 := hD'0 (eN (Lof u w))
        rw [hD', LinearMap.sub_apply, sub_eq_zero] at e2
        rw [← ad, ← ad, ← e1]
        exact sub_eq_zero.mpr e2
    exact sub_eq_zero.mp hsub

theorem hTildeLin_odd : IsOddLin (hTildeLin (F := F) (n := n)) := by
  intro X k hk
  by_contra h
  exact hk (hTilde_eN_apply_eq_zero_of_parity_ne X k h)

/-- **Thm 4.9**: every odd `P`-linear primitive `f` of `Γ_β` (`δf = Γ_β`) is `h̃ − ad Z` for a
unique odd `Z ∈ P ⊗ 𝔤₁̄`. -/
theorem primitive_eq_hTilde_sub_ad (f : OspMod F n →ₗ[Pmn F n] OspMod F n) (hodd : IsOddLin f)
    (hprim : ∀ X Y, deltaBasis f X Y = GammaBasis X Y) :
    ∃! Z : OspMod F n, (∀ k, Z k ≠ 0 → parity k = 1) ∧ ∀ x, f x = hTilde x - ad Z x := by
  have hDodd : IsOddLin (f - hTildeLin) := by
    intro X k hk
    rw [LinearMap.sub_apply, Pi.sub_apply] at hk
    by_cases h1 : f (eN X) k = 0
    · rw [h1, zero_sub, neg_ne_zero] at hk; exact hTildeLin_odd X k hk
    · exact hodd X k h1
  have hDder : IsDer (f - hTildeLin) := by
    intro X Y
    rw [deltaBasis_sub, hprim X Y, Gamma_eq_delta_hTilde_basis]
    exact sub_self _
  obtain ⟨Z, ⟨hZ, hDZ⟩, huniq⟩ := der_eq_ad (f - hTildeLin) hDodd hDder
  have hneg : ∀ k, (-Z) k ≠ 0 → parity k = 1 := fun k hk => hZ k (by simpa using hk)
  refine ⟨-Z, ⟨hneg, fun x => ?_⟩, ?_⟩
  · have := hDZ x
    rw [LinearMap.sub_apply, sub_eq_iff_eq_add] at this
    rw [this, ad, ad, bracket0_neg_left, sub_neg_eq_add, add_comm]
    rfl
  · rintro Z' ⟨hZ', hfZ'⟩
    have : -Z' = Z := huniq (-Z') ⟨fun k hk => hZ' k (by simpa using hk), fun x => by
      rw [LinearMap.sub_apply, hfZ' x, ad, ad, bracket0_neg_left]
      change hTilde x - bracket0 Z' x - hTilde x = -bracket0 Z' x
      abel⟩
    rw [← this, neg_neg]

/-- **Cor 4.10**, first statement, in full: `f_β` is the unique odd primitive of `Γ_β` vanishing on
`sp(2n)`. -/
theorem fBeta_unique_primitive (f : OspMod F n →ₗ[Pmn F n] OspMod F n) (hodd : IsOddLin f)
    (hprim : ∀ X Y, deltaBasis f X Y = GammaBasis X Y)
    (hsp : ∀ u w : I n, f (eN (Lof u w)) = 0) : ∀ x, f x = fBeta F n x := by
  obtain ⟨Z, ⟨hZ, hfZ⟩, -⟩ := primitive_eq_hTilde_sub_ad f hodd hprim
  have hZb : Z = Zbeta F n := fBeta_unique_vanishing_sp Z hZ fun u w => by rw [← hfZ, hsp]
  intro x
  rw [hfZ, hZb]
  rfl

/-- **Cor 4.10**, second statement, in full: for `N ≥ 2`, no odd primitive of `Γ_β` vanishes on
`sp(2n) ⊕ so(N)`. -/
theorem no_primitive_vanishing (hn : 0 < n) (hK : ∃ i j : F.K, i ≠ j)
    (f : OspMod F n →ₗ[Pmn F n] OspMod F n) (hodd : IsOddLin f)
    (hprim : ∀ X Y, deltaBasis f X Y = GammaBasis X Y) :
    ¬ ((∀ u w : I n, f (eN (Lof u w)) = 0) ∧ ∀ i j : F.K, f (Sof i j) = 0) := by
  obtain ⟨Z, ⟨hZ, hfZ⟩, -⟩ := primitive_eq_hTilde_sub_ad f hodd hprim
  rintro ⟨hL, hS⟩
  exact no_primitive_vanishing_sp_so hn hK Z hZ
    ⟨fun u w => by rw [← hfZ, hL], fun i j => by rw [← hfZ, hS]⟩

end OspN
end OspOddDeformations
