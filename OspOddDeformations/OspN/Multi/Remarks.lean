import OspOddDeformations.OspN.Multi.TierB
import OspOddDeformations.OspN.Multi.ThetaSeries
import OspOddDeformations.OspN.Multi.RemarksAux

/-!
# Prop 5.5 and the text after Prop 5.4

* Prop 5.5: when `Ω ≠ 0`, neither `T^{(1)} ⋯ T^{(r)} = V_γ` nor the truncation
  `U_{≤1} = id + Σ_s κ_s h̃^{(s)}_R` of `U` to degree `1` intertwines `[·,·]_β` with `[·,·]_0`. The
  witness for `U_{≤1}` is `X = L_{uu}`, `Y = L_{vv}`: the `L_{uv}`-coefficient of the defect is
  `2 Ω_{uv}` (the paper's `−2 Σ_i (β^{(1)}_{1,i*} β^{(2)}_{2,i} − β^{(2)}_{1,i*} β^{(1)}_{2,i})`
  at `u, v = 1, 2`).
* The text after Prop 5.4: for `r ≤ 3`, `Θ_* − id` is not a derivation of `[·,·]_0` when `Ω ≠ 0`.
The case of Rem 6.1's claim in which `Ω` is even, antisymmetric and of `κ`-degree `2` (`J − Ω` is
equivalent to `J`) is `thetaG_spec`.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- The basis vector `κ_S X` of `𝔤_{R_r}`. -/
noncomputable def eM (p : RBasisM F n r) : RModM F n r := fun q => if q = p then 1 else 0

/-- `U_{≤1} = id + Σ_s κ_s h̃^{(s)}_R` (`T1`) on the basis symbols: `U` with `Θ = 𝕀`,
truncated to degree `1`
in `γ`
(dual index on the coefficient):
`U_{≤1}(L_{uv}) = L_{uv} + Σ_i (γ_{v,i*} F_{u,i} + γ_{u,i*} F_{v,i})`, `U_{≤1}(S_{ij}) = S_{ij}`,
`U_{≤1}(F_{u,i}) = F_{u,i} + ½ Σ_j γ_{u,j*} S_{ji}`. -/
noncomputable def T1Basis0 : OspBasis F n → RModM F n r
  | .inl ⟨(u, v), _⟩ =>
      gtens gone (eN (Lof u v))
      + ∑ i : F.K, (gtens (gammaR v (F.dual i)) (eN (Fof u i))
          + gtens (gammaR u (F.dual i)) (eN (Fof v i)))
  | .inr (.inl ⟨(i, j), _⟩) => gtens gone (Sof i j)
  | .inr (.inr (u, i)) =>
      gtens gone (eN (Fof u i)) + (1 / 2 : ℚ) • ∑ j : F.K, gtens (gammaR u (F.dual j)) (Sof j i)

/-- `U_{≤1}` (`T1`), even and `R_r`-linear. -/
noncomputable def T1 (x : RModM F n r) : RModM F n r :=
  ∑ p : RBasisM F n r, x p • gsmul (gmono p.2 1) (T1Basis0 p.1)

/-- Prop 5.5's coefficient: for `u ≠ v`, the `L_{uv}`-component of
`[U_{≤1} L_{uu}, U_{≤1} L_{vv}]_0 − U_{≤1} [L_{uu}, L_{vv}]_β` is `2 Ω_{uv}`. -/
theorem T1_defect_Luv (u v : I n) (h : u ≠ v) :
    grComp (bracket0M (T1 (eM (Lof u u, ∅))) (T1 (eM (Lof v v, ∅)))
      - T1 (bracketBetaM (eM (Lof u u, ∅)) (eM (Lof v v, ∅)))) (Lof u v)
      = (2 : ℚ) • OmegaR (F := F) (r := r) u v := by
  have _ := h
  have hM : ∀ b : OspBasis F n, eM (b, (∅ : Finset (Fin r))) = gtens gone (eN b) := fun b => by
    funext ⟨Z, T⟩
    simp only [eM, gtens_apply, emb0_eN, gone, Prod.mk.injEq]
    by_cases hZ : Z = b <;> by_cases hT : T = ∅ <;> simp [hZ, hT]
  have hT1 : ∀ b : OspBasis F n, T1 (gtens gone (eN b) : RModM F n r) = T1Basis0 b := fun b => by
    change linM T1Basis0 _ = _
    rw [linM_gtens_eN, gsmul_gone]
  rw [hM, hM, hT1, hT1, grComp_sub]
  have hFL : ∀ (x : I n) (i : F.K) (a b : I n),
      (eN (Fof x i : OspBasis F n) : OspMod F n) (Lof a b) = 0 := by
    intro x i a b
    obtain ⟨p, hp, e⟩ := Lof_cases (F := F) a b
    rw [e]; exact eN_Fof_apply_inl x i _
  have hSL : ∀ (i j : F.K) (a b : I n), (Sof i j : OspMod F n) (Lof a b) = 0 := by
    intro i j a b
    obtain ⟨p, hp, e⟩ := Lof_cases (F := F) a b
    rw [e]; exact Sof_apply_inl i j _
  have hcomp : ∀ (Z : OspBasis F n) (a b : I n),
      grComp (T1Basis0 (r := r) Z) (Lof a b) = if Z = Lof a b then gone else 0 := by
    intro Z a b
    rcases Z with ⟨⟨x, y⟩, hxy⟩ | ⟨⟨i, j⟩, hij⟩ | ⟨x, i⟩
    · have hL : (Lof x y : OspBasis F n) = Sum.inl ⟨(x, y), hxy⟩ := Lof_of_le hxy
      have hd : T1Basis0 (r := r) (Sum.inl ⟨(x, y), hxy⟩ : OspBasis F n) =
          gtens gone (eN (Lof x y)) + ∑ i : F.K, (gtens (gammaR y (F.dual i)) (eN (Fof x i))
            + gtens (gammaR x (F.dual i)) (eN (Fof y i))) := rfl
      rw [hd, ← hL]
      simp only [grComp_add, grComp_sum, grComp_gtens, hFL, emb0_eN, map_zero, zero_smul,
        Finset.sum_const_zero, add_zero]
      by_cases hh : (Lof a b : OspBasis F n) = Lof x y
      · simp [hh]
      · simp [hh, Ne.symm hh]
    · have hd : T1Basis0 (r := r) (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : OspBasis F n) =
          gtens gone (Sof i j) := rfl
      rw [hd]
      simp only [grComp_gtens, hSL, map_zero, zero_smul]
      classical
      split_ifs with heq
      · exfalso
        obtain ⟨p, hp, e⟩ := Lof_cases (F := F) a b
        rw [e] at heq
        cases heq
      · rfl
    · have hd : T1Basis0 (r := r) (Sum.inr (Sum.inr (x, i)) : OspBasis F n) =
          gtens gone (eN (Fof x i)) + (1 / 2 : ℚ) • ∑ j : F.K, gtens (gammaR x (F.dual j))
            (Sof j i) := rfl
      rw [hd]
      simp only [grComp_add, grComp_rsmul, grComp_sum, grComp_gtens, hSL, hFL, map_zero, zero_smul,
        Finset.sum_const_zero, smul_zero, add_zero]
      classical
      split_ifs with heq
      · exfalso
        obtain ⟨p, hp, e⟩ := Lof_cases (F := F) a b
        rw [e] at heq
        cases heq
      · rfl
  have hT1c : ∀ (z : RModM F n r) (a b : I n), grComp (T1 z) (Lof a b) = grComp z (Lof a b) := by
    intro z a b
    change grComp (linM T1Basis0 z) _ = _
    rw [grComp_linM]
    simp only [hcomp]
    rw [Finset.sum_eq_single (Lof a b)]
    · simp [gmul_gone]
    · intro Z _ hZ
      simp [hZ, gmul_zero_right]
    · simp
  have hβ : grComp (bracketBetaM (gtens gone (eN (Lof u u) : OspMod F n) : RModM F n r)
      (gtens gone (eN (Lof v v)))) (Lof u v) =
        emb0 (r := r) (bracketLL (F := F) u u v v (Lof u v)) • (gone : GR F n r) := by
    rw [bracketBetaM_eq_liftB, liftB_eN_eN_gen, Bbeta_LL]
    simp only [sigPow_gone, gmul_gone, gsmul_gone, B0data, grComp_gtens, bracket0Basis_Lof_Lof]
  rw [hT1c, hβ]
  have hd : ∀ w : I n, T1Basis0 (r := r) (Lof w w : OspBasis F n) =
      gtens gone (eN (Lof w w)) + ∑ i : F.K, (gtens (gammaR w (F.dual i)) (eN (Fof w i))
        + gtens (gammaR w (F.dual i)) (eN (Fof w i))) := by
    intro w
    have hL : (Lof w w : OspBasis F n) = Sum.inl ⟨(w, w), le_refl _⟩ := Lof_of_le (le_refl _)
    calc T1Basis0 (r := r) (Lof w w : OspBasis F n)
        = T1Basis0 (r := r) (Sum.inl ⟨(w, w), le_refl _⟩ : OspBasis F n) := by rw [hL]
      _ = _ := rfl
  rw [hd u, hd v]
  simp only [bracket0M_eq_liftB, liftB_add_left, liftB_add_right, liftB_sum_left, liftB_sum_right,
    liftB0_gtens_eN, grComp_add, grComp_sum, grComp_gtens]
  have hLL : emb0 (r := r) (bracket0Basis (Lof u u : OspBasis F n) (Lof v v) (Lof u v)) =
      emb0 (r := r) (bracketLL (F := F) u u v v (Lof u v)) := by rw [bracket0Basis_Lof_Lof]
  have hFL0 : ∀ i : F.K, emb0 (r := r)
      (bracket0Basis (Fof u i : OspBasis F n) (Lof v v) (Lof u v)) = 0 := by
    intro i
    have e : (Lof v v : OspBasis F n) = Sum.inl ⟨(v, v), le_refl _⟩ := Lof_of_le (le_refl _)
    rw [e]
    change emb0 ((-bracketLF (F := F) v v u i) (Lof u v)) = 0
    simp [bracketLF, hFL]
  have hLF0 : ∀ i : F.K, emb0 (r := r)
      (bracket0Basis (Lof u u : OspBasis F n) (Fof v i) (Lof u v)) = 0 := by
    intro i
    have e : (Lof u u : OspBasis F n) = Sum.inl ⟨(u, u), le_refl _⟩ := Lof_of_le (le_refl _)
    rw [e]
    change emb0 ((bracketLF (F := F) u u v i) (Lof u v)) = 0
    simp [bracketLF, hFL]
  have hFF : ∀ i j : F.K, emb0 (r := r)
      (bracket0Basis (Fof u i : OspBasis F n) (Fof v j) (Lof u v)) =
        ((1 / 2 * F.g i j : ℚ)) • (1 : PmnR F n r) := by
    intro i j
    change emb0 ((bracketFF (F := F) u i v j) (Lof u v)) = _
    simp [bracketFF, hSL, emb0_eN]
  simp only [hLL, hFL0, hLF0, hFF, parity_Lof, parity_Fof, sigPow_zero, sigPow_gone, gmul_gone,
    zero_smul, add_zero, Finset.sum_const_zero, sigPow_one_gammaR, gmul_neg_right]
  have hkey : ∑ x : F.K, ∑ x1 : F.K, (((1 / 2 * F.g x1 x : ℚ)) • (1 : PmnR F n r)) •
      -gmul (gammaR (F := F) (r := r) u (F.dual x1)) (gammaR v (F.dual x)) =
        (1 / 2 : ℚ) • OmegaR (F := F) (r := r) u v := by
    have hinv : Function.Involutive F.dual := F.dual_dual
    simp only [smul_assoc, one_smul]
    rw [Finset.sum_comm]
    simp only [FermionIndex.g, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, smul_neg]
    unfold OmegaR
    rw [← Equiv.sum_comp hinv.toPerm]
    simp only [Function.Involutive.coe_toPerm, hinv _, smul_neg, Finset.smul_sum,
      Finset.sum_neg_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [zero_add, Finset.sum_add_distrib, hkey]
  rw [add_sub_cancel_left]
  module

/-- **Prop 5.5**: if `Ω ≠ 0`, the truncation `U_{≤1}` does not intertwine `[·,·]_β` with
`[·,·]_0`. -/
theorem T1_not_intertwine (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) :
    ¬ ∀ x y : RModM F n r, bracket0M (T1 x) (T1 y) = T1 (bracketBetaM x y) := by
  intro hall
  obtain ⟨u, v, hΩ'⟩ := hΩ
  have huv : u ≠ v := by
    rintro rfl
    apply hΩ'
    have h1 : OmegaR (F := F) (r := r) u u = -OmegaR u u := OmegaR_antisymm u u
    have h2 : (2 : ℚ) • OmegaR (F := F) (r := r) u u = 0 := by
      rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    have := congrArg (fun z => (1 / 2 : ℚ) • z) h2
    simpa [smul_smul] using this
  have h := T1_defect_Luv (F := F) (n := n) (r := r) u v huv
  rw [hall, sub_self] at h
  have h0 : (2 : ℚ) • OmegaR (F := F) (r := r) u v = 0 := by rw [← h]; rfl
  apply hΩ'
  have := congrArg (fun z => (1 / 2 : ℚ) • z) h0
  simpa [smul_smul] using this

/-- **Prop 5.5**: if `Ω ≠ 0`, the product `T^{(1)} ⋯ T^{(r)} = V_γ` does not intertwine `[·,·]_β`
with
`[·,·]_0`. -/
theorem TProd_not_intertwine (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) :
    ¬ ∀ x y : RModM F n r, bracket0M (TProd x) (TProd y) = TProd (bracketBetaM x y) := by
  intro h
  obtain ⟨x0, y0, hne⟩ := exists_witness_ne hΩ
  obtain ⟨x, rfl⟩ := VChi_gammaR_surjective x0
  obtain ⟨y, rfl⟩ := VChi_gammaR_surjective y0
  have := h x y
  rw [TProd_eq, TProd_eq, TProd_eq, ← vChi_bracket] at this
  exact hne this.symm

/-- **After Prop 5.4**: for `r ≤ 3` and `Ω ≠ 0`, `Θ_* − id` (with `Θ = 𝕀 + ½ΩJ`) is not a
derivation of
`[·,·]_0`. -/
theorem ThetaStar_sub_one_not_derivation (hr : r ≤ 3)
    (hΩ : ∃ u v : I n, OmegaR (F := F) (r := r) u v ≠ 0) :
    ¬ ∀ x y : RModM F n r,
      ThetaStar thetaHalf (bracket0M x y) - bracket0M x y =
        bracket0M (ThetaStar thetaHalf x - x) y + bracket0M x (ThetaStar thetaHalf y - y) := by
  intro h
  obtain ⟨u, w, hΩ'⟩ := hΩ
  obtain ⟨i⟩ := nonempty_K_of_Omega u w hΩ'
  obtain ⟨hE, -, hΘ⟩ := thetaHalf_spec (F := F) (n := n) (r := r) hr
  set x : RModM F n r := gtens gone (eN (Lof u u : OspBasis F n)) with hx
  set y : RModM F n r := gtens gone (eN (Fof w i)) with hy
  have hDD : bracket0M (ThetaStar thetaHalf x - x) (ThetaStar thetaHalf y - y) = 0 :=
    RMin.eq_zero (by omega : r < 2 + 2) (RMin_bracket0M (RMin_Dx u) (RMin_Dy w i))
  have hder := h x y
  refine false_of_pair thetaHalf hE hΘ u w i hΩ' ?_
  have e1 : ThetaStar thetaHalf x = x + (ThetaStar thetaHalf x - x) := by abel
  have e2 : ThetaStar thetaHalf y = y + (ThetaStar thetaHalf y - y) := by abel
  rw [e1, e2]
  simp only [bracket0M_eq_liftB, liftB_add_left, liftB_add_right] at hDD hder ⊢
  rw [hDD, add_zero]
  rw [sub_eq_iff_eq_add] at hder
  rw [hder]
  abel

end Multi
end OspN
end OspOddDeformations
