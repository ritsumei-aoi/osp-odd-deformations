import OspOddDeformations.OspN.Presented.MultiTheta

/-!
# Thm 5.1 (untwisting with `r` odd parameters), for the presented algebras

`Φ_r : A_β → A_0`, `b_u ↦ Σ_w Θ_{uw} B_w + c_u`, and `Ψ_r : A_0 → A_β`,
`B_u ↦ Σ_w (Θ⁻¹)_{uw}(b_w − c_w)`, both fixing the `a_i`, the `κ_s` and `P`, are defined by the
universal property and are mutually inverse; both commute with the parity, so they are even.
Here `Θ = (𝕀 + ΩJ)^{1/2}` of `MultiTheta.lean`, in each algebra its own (`thetaV`), and `Ψ_r`
carries the one of `A_0` to the one of `A_β` (`map_thetaV`).
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open scoped Matrix

/-- The supercommutator of two combinations with central coefficients:
`[Σ_w M_{uw} y_w, Σ_z M_{vz} y_z] = (M N Mᵀ)_{uv}` when `[y_w, y_z] = N_{wz}`. -/
theorem comm_of_central_comb {A : Type} [Ring A] {ι : Type} [Fintype ι] (M N : Matrix ι ι A)
    (hM : ∀ u w x, M u w * x = x * M u w) (y : ι → A) (hN : ∀ w z, y w * y z - y z * y w = N w z)
    (u v : ι) :
    (∑ w, M u w * y w) * (∑ z, M v z * y z) - (∑ z, M v z * y z) * (∑ w, M u w * y w)
      = (M * N * Mᵀ) u v := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 : M u w * y w * (M v z * y z) = M u w * (M v z * (y w * y z)) := by
    simp only [mul_assoc]
    rw [← mul_assoc (y w) (M v z), ← hM v z (y w), mul_assoc]
  have e2 : M v z * y z * (M u w * y w) = M u w * (M v z * (y z * y w)) := by
    simp only [mul_assoc]
    rw [← mul_assoc (y z) (M u w), ← hM u w (y z), mul_assoc (M u w), ← mul_assoc (M v z),
      ← hM u w (M v z), mul_assoc]
  rw [e1, e2, ← mul_sub, ← mul_sub, hN, hM v z, mul_assoc]

variable {P : Type} [CommRing P] [Algebra ℚ P] {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
variable {r : ℕ} {J : I → I → P} {g : K → K → P} (δ : Fin r → I → K → P)

/-! ## `Ω`, `J`, `Θ` and `Θ⁻¹` as matrices over the algebra itself -/

/-- `Ω`, over `SrcM J g β'`. -/
def OmV (β' : Fin r → I → K → P) : Matrix I I (SrcM J g β') := Matrix.of (omegaM δ)

/-- `J`, over `SrcM J g β'`. -/
noncomputable def JV (β' : Fin r → I → K → P) : Matrix I I (SrcM J g β') :=
  (Matrix.of J).map (algebraMap P _)

/-- `Θ = Σ_{k≤⌊r/2⌋} C(1/2,k)(ΩJ)^k`, over `SrcM J g β'`. -/
noncomputable def thetaV (β' : Fin r → I → K → P) : Matrix I I (SrcM J g β') :=
  ∑ k ∈ Finset.range (r / 2 + 1),
    algebraMap ℚ P (Ring.choose (1 / 2 : ℚ) k) • (OmV δ β' * JV β') ^ k

/-- `Θ⁻¹`, over `SrcM J g β'`. -/
noncomputable def thetaInvV (β' : Fin r → I → K → P) : Matrix I I (SrcM J g β') :=
  thetaV δ β' * ∑ k ∈ Finset.range (r / 2 + 1), (-(OmV δ β' * JV β')) ^ k

variable {δ}

section center

variable {β' : Fin r → I → K → P}

/-- The inclusion of the centre. -/
abbrev cval : ZM J g β' →ₐ[P] SrcM J g β' := (Subalgebra.center P (SrcM J g β')).val

omit [Algebra ℚ P] in
theorem mapMatrix_OmZM :
    (cval (J := J) (g := g) (β' := β')).mapMatrix (OmZM J g β' δ) = OmV δ β' := by
  ext u v; rfl

omit [Algebra ℚ P] [Fintype K] in
theorem mapMatrix_JZM : (cval (J := J) (g := g) (β' := β')).mapMatrix (JZM J g β') = JV β' := by
  ext u v
  simp [JZM, JV]

omit [Fintype I] [DecidableEq I] [Fintype K] in
theorem rat_smul_ZM (q : ℚ) (A : Matrix I I (ZM J g β')) : q • A = algebraMap ℚ P q • A := by
  ext u v
  simp only [Matrix.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

theorem mapMatrix_thetaM :
    (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaM (δ := δ)) = thetaV δ β' := by
  unfold thetaM thetaOf thetaV
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rat_smul_ZM, map_smul, map_pow, map_mul, mapMatrix_OmZM, mapMatrix_JZM]

theorem mapMatrix_thetaInvM :
    (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaInvM (δ := δ)) = thetaInvV δ β' := by
  unfold thetaInvM thetaInvOf thetaInvV
  rw [map_mul, ← thetaM, mapMatrix_thetaM, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_pow]
  erw [map_neg]
  rw [map_mul, mapMatrix_OmZM, mapMatrix_JZM]

theorem thetaV_central (u w : I) (x : SrcM J g β') :
    thetaV δ β' u w * x = x * thetaV δ β' u w := by
  rw [← mapMatrix_thetaM]
  exact ((Subalgebra.mem_center_iff.mp (thetaM (J := J) (g := g) (β := β') (δ := δ) u w).2 x)).symm

theorem thetaInvV_central (u w : I) (x : SrcM J g β') :
    thetaInvV δ β' u w * x = x * thetaInvV δ β' u w := by
  rw [← mapMatrix_thetaInvM]
  exact ((Subalgebra.mem_center_iff.mp
    (thetaInvM (J := J) (g := g) (β := β') (δ := δ) u w).2 x)).symm

omit [Algebra ℚ P] [Fintype I] [DecidableEq I] [Fintype K] in
theorem JV_apply (u v : I) : JV (J := J) (g := g) β' u v = algebraMap P _ (J u v) := rfl

omit [Algebra ℚ P] [Fintype K] in
theorem JZM_mul_self (hJJ : Matrix.of J * Matrix.of J = -1) :
    JZM J g β' * JZM J g β' = -1 := by
  have h := congrArg (algebraMap P (ZM J g β')).mapMatrix hJJ
  rw [map_mul, map_neg, map_one] at h
  exact h

omit [Algebra ℚ P] [Fintype I] [DecidableEq I] [Fintype K] in
theorem JZM_transpose (hJt : (Matrix.of J)ᵀ = -Matrix.of J) :
    (JZM J g β')ᵀ = -JZM J g β' := by
  rw [JZM, ← Matrix.transpose_map, hJt, Matrix.map_neg _ (map_neg _)]

variable (hJJ : Matrix.of J * Matrix.of J = -1) (hJt : (Matrix.of J)ᵀ = -Matrix.of J)
include hJJ hJt

theorem thetaV_J_thetaVT :
    thetaV (J := J) (g := g) δ β' * JV β' * (thetaV δ β')ᵀ = JV β' - OmV δ β' := by
  have h := congrArg (cval (J := J) (g := g) (β' := β')).mapMatrix
    (thetaM_J_thetaMT (δ := δ) (JZM_mul_self hJJ) (JZM_transpose hJt))
  rw [map_mul, map_mul, map_sub,
    show (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaM (δ := δ))ᵀ
      = ((cval (J := J) (g := g) (β' := β')).mapMatrix (thetaM (δ := δ)))ᵀ by ext; rfl,
    mapMatrix_thetaM, mapMatrix_JZM, mapMatrix_OmZM] at h
  exact h

theorem thetaInvV_conj :
    thetaInvV (J := J) (g := g) δ β' * (JV β' - OmV δ β') * (thetaInvV δ β')ᵀ = JV β' := by
  have h := congrArg (cval (J := J) (g := g) (β' := β')).mapMatrix
    (thetaInvM_conj (δ := δ) (JZM_mul_self hJJ) (JZM_transpose hJt))
  rw [map_mul, map_mul, map_sub,
    show (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaInvM (δ := δ))ᵀ
      = ((cval (J := J) (g := g) (β' := β')).mapMatrix (thetaInvM (δ := δ)))ᵀ by ext; rfl,
    mapMatrix_thetaInvM, mapMatrix_JZM, mapMatrix_OmZM] at h
  exact h

omit hJJ hJt

theorem thetaV_mul_inv :
    thetaV (J := J) (g := g) δ β' * thetaInvV δ β' = (1 : Matrix I I (SrcM J g β')) := by
  have h := congrArg (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaM_mul_inv (δ := δ))
  rwa [map_mul, map_one, mapMatrix_thetaM, mapMatrix_thetaInvM] at h

theorem thetaInvV_mul :
    thetaInvV (J := J) (g := g) δ β' * thetaV δ β' = (1 : Matrix I I (SrcM J g β')) := by
  have h := congrArg (cval (J := J) (g := g) (β' := β')).mapMatrix (thetaInvM_mul (δ := δ))
  rwa [map_mul, map_one, mapMatrix_thetaM, mapMatrix_thetaInvM] at h

end center

/-! ## Maps that fix the `c_u` fix `Ω`, `J`, `Θ` and `Θ⁻¹` -/

section maps

variable {β₁ β₂ : Fin r → I → K → P} (f : SrcM J g β₁ →ₐ[P] SrcM J g β₂)
variable (hc : ∀ u, f (cM δ u) = cM δ u)
include hc

omit [Algebra ℚ P] in
theorem mapMatrix_OmV : f.mapMatrix (OmV δ β₁) = OmV δ β₂ := by
  ext u v
  simp [OmV, omegaM, hc]

theorem mapMatrix_thetaV : f.mapMatrix (thetaV δ β₁) = thetaV δ β₂ := by
  have hJ : f.mapMatrix (JV β₁) = JV (J := J) (g := g) β₂ := by ext u v; simp [JV]
  unfold thetaV
  simp only [map_sum, map_smul, map_pow, map_mul, mapMatrix_OmV f hc, hJ]

theorem mapMatrix_thetaInvV : f.mapMatrix (thetaInvV δ β₁) = thetaInvV δ β₂ := by
  have hJ : f.mapMatrix (JV β₁) = JV (J := J) (g := g) β₂ := by ext u v; simp [JV]
  unfold thetaInvV
  simp only [map_mul, map_sum, map_pow, map_neg, mapMatrix_thetaV f hc, mapMatrix_OmV f hc, hJ]

end maps


/-! ## `Φ_r` and `Ψ_r` -/

section untwist

variable (δ)

omit [Algebra ℚ P] [Fintype I] [DecidableEq I] in
theorem κM_mul_cM {β' : Fin r → I → K → P} (t : Fin r) (u : I) :
    κM J g β' t * cM δ u = cM δ u * κM J g β' t := by
  simp only [cM, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, κM_mul_gammaM, neg_mul, mul_assoc, κM_mul_aM, mul_neg, neg_neg, mul_assoc]

omit [Algebra ℚ P] [Fintype I] [DecidableEq I] in
theorem parityM_cM {β' : Fin r → I → K → P} (u : I) :
    parityM (cM (J := J) (g := g) (β := β') δ u) = cM δ u := by
  simp only [cM, gammaM, map_sum, map_mul, map_smul, parityM_κ, parityM_a, smul_neg,
    Finset.sum_neg_distrib, neg_mul_neg]

omit [Algebra ℚ P] [DecidableEq I] [Fintype K] in
/-- `B̃_u = Σ_w M_{uw} B_w` with central `M` commutes with whatever every `B_w` commutes with. -/
theorem comb_comm {β' : Fin r → I → K → P} (M : Matrix I I (SrcM J g β'))
    (hM : ∀ u w x, M u w * x = x * M u w) (y : I → SrcM J g β') (x : SrcM J g β')
    (hy : ∀ w, y w * x = x * y w) (u : I) :
    (∑ w, M u w * y w) * x = x * ∑ w, M u w * y w := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, hy, ← mul_assoc, hM, mul_assoc]

variable {β : Fin r → I → K → P}

/-- The images of the generators under `Φ_r`: `b_u ↦ Σ_w Θ_{uw} B_w + c_u`. -/
noncomputable def phiGenM : GenM I K r → SrcM J g (0 : Fin r → I → K → P)
  | Sum.inl u => (∑ w, thetaV δ 0 u w * bM J g 0 w) + cM δ u
  | Sum.inr (Sum.inl i) => aM J g 0 i
  | Sum.inr (Sum.inr s) => κM J g 0 s

/-- The images of the generators under `Ψ_r`: `B_u ↦ Σ_w (Θ⁻¹)_{uw}(b_w − c_w)`. -/
noncomputable def psiGenM (β : Fin r → I → K → P) : GenM I K r → SrcM J g β
  | Sum.inl u => ∑ w, thetaInvV δ β u w * (bM J g β w - cM δ w)
  | Sum.inr (Sum.inl i) => aM J g β i
  | Sum.inr (Sum.inr s) => κM J g β s

variable (hg : ∀ i j, g i j = g j i) (hδ : ∀ s u j, ∑ i, δ s u i * g j i = β s u j)
variable (hJJ : Matrix.of J * Matrix.of J = -1) (hJt : (Matrix.of J)ᵀ = -Matrix.of J)

omit [Algebra ℚ P] [Fintype I] [DecidableEq I] in
include hg hδ in
theorem cM_mul_aM_eq {β₀ : Fin r → I → K → P} (u : I) (j : K) :
    cM (J := J) (g := g) (β := β₀) δ u * aM J g β₀ j
      = aM J g β₀ j * cM δ u + ∑ s, β s u j • κM J g β₀ s := by
  rw [cM_mul_aM]
  congr 2
  funext s
  rw [← hδ s u j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg]

include hg hδ hJJ hJt in
theorem phiGenM_rel (x y : FreeAlgebra P (GenM I K r)) (h : RelM J g β x y) :
    FreeAlgebra.lift P (phiGenM (J := J) (g := g) δ) x = FreeAlgebra.lift P (phiGenM δ) y := by
  have hθ := thetaV_central (J := J) (g := g) (β' := 0) (δ := δ)
  cases h with
  | bb u v =>
    simp only [map_mul, map_add, AlgHom.commutes, bMF, FreeAlgebra.lift_ι_apply, phiGenM]
    have h1 := comm_of_central_comb (thetaV δ 0) (JV 0) hθ (bM J g 0)
      (fun w z => by rw [bM_mul_bM, JV_apply]; abel) u v
    rw [thetaV_J_thetaVT hJJ hJt] at h1
    have h3 := comb_comm (thetaV δ 0) hθ (bM J g 0) (cM δ v) (fun w => bM_mul_cM_zero δ w v) u
    have h4 := comb_comm (thetaV δ 0) hθ (bM J g 0) (cM δ u) (fun w => bM_mul_cM_zero δ w u) v
    have h2 : cM (J := J) (g := g) (β := 0) δ u * cM δ v
        = cM δ v * cM δ u + omegaM δ u v := by rw [omegaM]; abel
    rw [Matrix.sub_apply, JV_apply] at h1
    rw [add_mul, mul_add, mul_add, h3, h2, add_mul, mul_add, mul_add, ← h4,
      show (∑ w, thetaV δ 0 u w * bM J g 0 w) * (∑ z, thetaV δ 0 v z * bM J g 0 z)
        = (∑ z, thetaV δ 0 v z * bM J g 0 z) * (∑ w, thetaV δ 0 u w * bM J g 0 w)
          + (algebraMap P _ (J u v) - OmV δ 0 u v) by rw [← h1]; abel]
    simp only [OmV, Matrix.of_apply]
    abel
  | aa i j =>
    simp only [map_mul, map_add, AlgHom.commutes, aMF, FreeAlgebra.lift_ι_apply, phiGenM]
    exact aM_mul_aM_add i j
  | ba u i =>
    simp only [map_mul, map_add, map_sum, map_smul, aMF, bMF, kMF, FreeAlgebra.lift_ι_apply,
      phiGenM]
    have hB := comb_comm (thetaV δ 0) hθ (bM J g 0) (aM J g 0 i)
      (fun w => by rw [bM_mul_aM]; simp) u
    rw [add_mul, mul_add, hB, cM_mul_aM_eq δ hg hδ]
    abel
  | kk s t =>
    simp only [map_mul, map_add, map_zero, kMF, FreeAlgebra.lift_ι_apply, phiGenM]
    rw [κM_mul_κM, neg_add_cancel]
  | kss s =>
    simp only [map_mul, map_zero, kMF, FreeAlgebra.lift_ι_apply, phiGenM]
    exact κM_sq s
  | kb s u =>
    simp only [map_mul, kMF, bMF, FreeAlgebra.lift_ι_apply, phiGenM]
    have hB := comb_comm (thetaV δ 0) hθ (bM J g 0) (κM J g 0 s)
      (fun w => (κM_mul_bM s w).symm) u
    rw [mul_add, add_mul, hB, κM_mul_cM]
  | ka s i =>
    simp only [map_mul, map_add, map_zero, kMF, aMF, FreeAlgebra.lift_ι_apply, phiGenM]
    rw [κM_mul_aM, neg_add_cancel]

include hg hδ hJJ hJt in
theorem psiGenM_rel (x y : FreeAlgebra P (GenM I K r)) (h : RelM J g 0 x y) :
    FreeAlgebra.lift P (psiGenM (J := J) (g := g) δ β) x
      = FreeAlgebra.lift P (psiGenM δ β) y := by
  have hθ := thetaInvV_central (J := J) (g := g) (β' := β) (δ := δ)
  have hb' : ∀ w z, (bM J g β w - cM δ w) * (bM J g β z - cM δ z)
      - (bM J g β z - cM δ z) * (bM J g β w - cM δ w)
      = (JV β - OmV δ β : Matrix I I (SrcM J g β)) w z := by
    intro w z
    have e1 := bM_mul_cM (J := J) δ hg hδ w z
    have e2 := bM_mul_cM (J := J) δ hg hδ z w
    have e3 := omegaM_antisymm (J := J) (g := g) (β := β) δ w z
    rw [Matrix.sub_apply, JV_apply]
    simp only [OmV, Matrix.of_apply]
    have e4 : cM (J := J) (g := g) (β := β) δ w * cM δ z = cM δ z * cM δ w + omegaM δ w z := by
      rw [omegaM]; abel
    rw [sub_mul, mul_sub, mul_sub, sub_mul, mul_sub, mul_sub, bM_mul_bM, e1, e4, e2, e3]
    abel
  cases h with
  | bb u v =>
    simp only [map_mul, map_add, AlgHom.commutes, bMF, FreeAlgebra.lift_ι_apply, psiGenM]
    have h1 := comm_of_central_comb (thetaInvV δ β) (JV β - OmV δ β) hθ
      (fun w => bM J g β w - cM δ w) hb' u v
    rw [thetaInvV_conj hJJ hJt, JV_apply] at h1
    rw [← sub_eq_iff_eq_add', h1]
  | aa i j =>
    simp only [map_mul, map_add, AlgHom.commutes, aMF, FreeAlgebra.lift_ι_apply, psiGenM]
    exact aM_mul_aM_add i j
  | ba u i =>
    simp only [map_mul, aMF, bMF, kMF, FreeAlgebra.lift_ι_apply,
      psiGenM, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    refine comb_comm (thetaInvV δ β) hθ (fun w => bM J g β w - cM δ w) (aM J g β i) ?_ u
    intro w
    rw [sub_mul, mul_sub, bM_mul_aM, cM_mul_aM_eq δ hg hδ]
    abel
  | kk s t =>
    simp only [map_mul, map_add, map_zero, kMF, FreeAlgebra.lift_ι_apply, psiGenM]
    rw [κM_mul_κM, neg_add_cancel]
  | kss s =>
    simp only [map_mul, map_zero, kMF, FreeAlgebra.lift_ι_apply, psiGenM]
    exact κM_sq s
  | kb s u =>
    simp only [map_mul, kMF, bMF, FreeAlgebra.lift_ι_apply, psiGenM]
    exact (comb_comm (thetaInvV δ β) hθ (fun w => bM J g β w - cM δ w) (κM J g β s)
      (fun w => by rw [sub_mul, mul_sub, κM_mul_bM, κM_mul_cM]) u).symm
  | ka s i =>
    simp only [map_mul, map_add, map_zero, kMF, aMF, FreeAlgebra.lift_ι_apply, psiGenM]
    rw [κM_mul_aM, neg_add_cancel]

include hg hδ hJJ hJt

/-- `Φ_r : A_β → A_0`. -/
noncomputable def phiM : SrcM J g β →ₐ[P] SrcM J g (0 : Fin r → I → K → P) :=
  liftM (phiGenM δ) (phiGenM_rel δ hg hδ hJJ hJt)

/-- `Ψ_r : A_0 → A_β`. -/
noncomputable def psiM : SrcM J g (0 : Fin r → I → K → P) →ₐ[P] SrcM J g β :=
  liftM (psiGenM δ β) (psiGenM_rel δ hg hδ hJJ hJt)

theorem phiM_b (u : I) :
    phiM δ hg hδ hJJ hJt (bM J g β u) = (∑ w, thetaV δ 0 u w * bM J g 0 w) + cM δ u := by
  simp only [phiM, bM, liftM_mk, bMF, FreeAlgebra.lift_ι_apply, phiGenM]
theorem phiM_a (i : K) : phiM δ hg hδ hJJ hJt (aM J g β i) = aM J g 0 i := by
  simp only [phiM, aM, liftM_mk, aMF, FreeAlgebra.lift_ι_apply, phiGenM]
theorem phiM_κ (s : Fin r) : phiM δ hg hδ hJJ hJt (κM J g β s) = κM J g 0 s := by
  simp only [phiM, κM, liftM_mk, kMF, FreeAlgebra.lift_ι_apply, phiGenM]
theorem psiM_b (u : I) :
    psiM δ hg hδ hJJ hJt (bM J g 0 u) = ∑ w, thetaInvV δ β u w * (bM J g β w - cM δ w) := by
  simp only [psiM, bM, liftM_mk, bMF, FreeAlgebra.lift_ι_apply, psiGenM]
theorem psiM_a (i : K) : psiM δ hg hδ hJJ hJt (aM J g 0 i) = aM J g β i := by
  simp only [psiM, aM, liftM_mk, aMF, FreeAlgebra.lift_ι_apply, psiGenM]
theorem psiM_κ (s : Fin r) : psiM δ hg hδ hJJ hJt (κM J g 0 s) = κM J g β s := by
  simp only [psiM, κM, liftM_mk, kMF, FreeAlgebra.lift_ι_apply, psiGenM]

theorem phiM_cM (u : I) : phiM δ hg hδ hJJ hJt (cM δ u) = cM δ u := by
  simp only [cM, gammaM, map_sum, map_mul, map_smul, phiM_a, phiM_κ]
theorem psiM_cM (u : I) : psiM δ hg hδ hJJ hJt (cM δ u) = cM δ u := by
  simp only [cM, gammaM, map_sum, map_mul, map_smul, psiM_a, psiM_κ]

theorem phiM_thetaInvV (u w : I) :
    phiM δ hg hδ hJJ hJt (thetaInvV δ β u w) = thetaInvV δ 0 u w := by
  have h := mapMatrix_thetaInvV (δ := δ) (phiM δ hg hδ hJJ hJt) (phiM_cM δ hg hδ hJJ hJt)
  exact congrFun (congrFun h u) w

theorem psiM_thetaV (u w : I) : psiM δ hg hδ hJJ hJt (thetaV δ 0 u w) = thetaV δ β u w := by
  have h := mapMatrix_thetaV (δ := δ) (psiM δ hg hδ hJJ hJt) (psiM_cM δ hg hδ hJJ hJt)
  exact congrFun (congrFun h u) w

omit [Algebra ℚ P] [Fintype K] hg hδ hJJ hJt in
/-- `Σ_w M_{uw} Σ_z N_{wz} y_z = Σ_z (MN)_{uz} y_z`; with `MN = 𝕀` this is `y_u`. -/
theorem sum_sum_eq_of_mul_eq_one {β' : Fin r → I → K → P} (M N : Matrix I I (SrcM J g β'))
    (hMN : M * N = 1) (y : I → SrcM J g β') (u : I) :
    ∑ w, M u w * ∑ z, N w z * y z = y u := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  have h : ∀ z, ∑ w, M u w * N w z = (1 : Matrix I I (SrcM J g β')) u z := fun z => by
    rw [← hMN, Matrix.mul_apply]
  simp only [h, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

theorem psiM_comp_phiM : (psiM δ hg hδ hJJ hJt).comp (phiM δ hg hδ hJJ hJt) = AlgHom.id P _ := by
  refine algHom_extM (fun u => ?_) (fun i => ?_) (fun s => ?_)
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, phiM_b, map_add, map_sum, map_mul, psiM_b,
      psiM_thetaV, psiM_cM]
    rw [sum_sum_eq_of_mul_eq_one _ _ (thetaV_mul_inv (δ := δ)), sub_add_cancel]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, phiM_a, psiM_a]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, phiM_κ, psiM_κ]

theorem phiM_comp_psiM : (phiM δ hg hδ hJJ hJt).comp (psiM δ hg hδ hJJ hJt) = AlgHom.id P _ := by
  refine algHom_extM (fun u => ?_) (fun i => ?_) (fun s => ?_)
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, psiM_b, map_sum, map_mul, map_sub, phiM_b,
      phiM_cM, phiM_thetaInvV, add_sub_cancel_right]
    exact sum_sum_eq_of_mul_eq_one _ _ (thetaInvV_mul (δ := δ)) _ u
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, psiM_a, phiM_a]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, psiM_κ, phiM_κ]

/-- `Φ_r` is even. -/
theorem phiM_parity (x : SrcM J g β) :
    phiM δ hg hδ hJJ hJt (parityM x) = parityM (phiM δ hg hδ hJJ hJt x) := by
  have hθ : ∀ u w, parityM (thetaV (J := J) (g := g) δ 0 u w) = thetaV δ 0 u w := fun u w =>
    congrFun (congrFun (mapMatrix_thetaV (δ := δ) parityM (parityM_cM δ)) u) w
  have h : (phiM δ hg hδ hJJ hJt).comp parityM = parityM.comp (phiM δ hg hδ hJJ hJt) := by
    refine algHom_extM (fun u => ?_) (fun i => ?_) (fun s => ?_)
    · simp only [AlgHom.comp_apply, parityM_b, phiM_b, map_add, map_sum, map_mul, hθ,
        parityM_cM]
    · simp only [AlgHom.comp_apply, parityM_a, phiM_a, map_neg]
    · simp only [AlgHom.comp_apply, parityM_κ, phiM_κ, map_neg]
  exact congrArg (fun φ => φ x) h

/-- **Thm 5.1 (untwisting, `r` odd parameters)**, for the presented algebras: `Φ_r` as an even
isomorphism `A_β ≃ A_0` fixing the `a_i`, the `κ_s` and `P`, with
`Φ_r(b_u) = Σ_w Θ_{uw} B_w + c_u` and `Φ_r⁻¹(B_u) = Σ_w (Θ⁻¹)_{uw}(b_w − c_w)`. -/
noncomputable def untwistM : SrcM J g β ≃ₐ[P] SrcM J g (0 : Fin r → I → K → P) :=
  AlgEquiv.ofAlgHom (phiM δ hg hδ hJJ hJt) (psiM δ hg hδ hJJ hJt) (phiM_comp_psiM δ hg hδ hJJ hJt)
    (psiM_comp_phiM δ hg hδ hJJ hJt)

end untwist

/-! ## The paper's instance -/

section paper

variable (F : FermionIndex) (n r : ℕ)

/-- `J` with values in `P_r`. -/
noncomputable def jR (u v : Bmn.I n) : Multi.PmnR F n r := algebraMap ℚ _ (Bmn.J n u v)
/-- `g` with values in `P_r`. -/
noncomputable def gR (i j : F.K) : Multi.PmnR F n r := algebraMap ℚ _ (F.g i j)
/-- `δ^{(s)}_{u,i} = β^{(s)}_{u,i*}`. -/
noncomputable def deltaR (s : Fin r) (u : Bmn.I n) (i : F.K) : Multi.PmnR F n r :=
  Multi.betaR F n r s u (F.dual i)

theorem J_mul_J_rat : Matrix.of (Bmn.J n) * Matrix.of (Bmn.J n) = -1 := by
  ext ⟨k1, b1⟩ ⟨k2, b2⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  cases b1 <;> cases b2 <;> simp [Bmn.J, Matrix.one_apply, Prod.ext_iff, eq_comm]
  split_ifs <;> simp

theorem J_transpose_rat : (Matrix.of (Bmn.J n))ᵀ = -Matrix.of (Bmn.J n) := by
  ext ⟨k1, b1⟩ ⟨k2, b2⟩
  cases b1 <;> cases b2 <;> simp [Bmn.J, eq_comm] <;> split_ifs <;> simp

theorem jR_mul_jR : Matrix.of (jR F n r) * Matrix.of (jR F n r) = -1 := by
  have h := congrArg (algebraMap ℚ (Multi.PmnR F n r)).mapMatrix (J_mul_J_rat n)
  rw [map_mul, map_neg, map_one] at h
  exact h

theorem jR_transpose : (Matrix.of (jR F n r))ᵀ = -Matrix.of (jR F n r) := by
  have h := congrArg (fun M => M.map (algebraMap ℚ (Multi.PmnR F n r))) (J_transpose_rat n)
  simp only [Matrix.transpose_map] at h
  rw [Matrix.map_neg _ (map_neg _)] at h
  exact h

theorem gR_symm (i j : F.K) : gR F n r i j = gR F n r j i := by rw [gR, gR, F.g_symm]

theorem sum_deltaR_mul_gR (s : Fin r) (u : Bmn.I n) (j : F.K) :
    ∑ i, deltaR F n r s u i * gR F n r j i = Multi.betaR F n r s u j := by
  rw [Fintype.sum_eq_single (F.dual j) (fun i hi => by
    simp only [gR, FermionIndex.g, ite_eq_right_iff.mpr (fun h => absurd h hi), map_zero,
      mul_zero])]
  simp only [deltaR, gR, FermionIndex.g, F.dual_dual, ite_true, map_one, mul_one]

/-- **Thm 5.1**, the paper's instance: `A_β ≃ A_0` over `R_r`, with
`c_u = Σ_i γ_{u,i*} a_i`, `γ_{u,i} = Σ_s β^{(s)}_{u,i} κ_s`. -/
noncomputable def untwistR :
    SrcM (jR F n r) (gR F n r) (Multi.betaR F n r)
      ≃ₐ[Multi.PmnR F n r] SrcM (jR F n r) (gR F n r) (0 : Fin r → Bmn.I n → F.K → _) :=
  untwistM (deltaR F n r) (gR_symm F n r) (sum_deltaR_mul_gR F n r) (jR_mul_jR F n r)
    (jR_transpose F n r)

theorem untwistR_b (u : Bmn.I n) :
    untwistR F n r (bM _ _ _ u)
      = (∑ w, thetaV (deltaR F n r) 0 u w * bM _ _ 0 w) + cM (deltaR F n r) u :=
  phiM_b _ _ _ _ _ u

theorem untwistR_symm_b (u : Bmn.I n) :
    (untwistR F n r).symm (bM _ _ 0 u)
      = ∑ w, thetaInvV (deltaR F n r) (Multi.betaR F n r) u w
          * (bM _ _ _ w - cM (deltaR F n r) w) :=
  psiM_b _ _ _ _ _ u

theorem untwistR_a (i : F.K) : untwistR F n r (aM _ _ _ i) = aM _ _ 0 i := phiM_a _ _ _ _ _ i

theorem untwistR_κ (s : Fin r) : untwistR F n r (κM _ _ _ s) = κM _ _ 0 s := phiM_κ _ _ _ _ _ s

/-- **Thm 5.1**: the untwisting is even. -/
theorem untwistR_parity (x : SrcM (jR F n r) (gR F n r) (Multi.betaR F n r)) :
    untwistR F n r (parityM x) = parityM (untwistR F n r x) :=
  phiM_parity _ _ _ _ _ x

end paper

end Presented
end OspN
end OspOddDeformations
