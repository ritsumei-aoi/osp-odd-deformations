import OspOddDeformations.OspN.Presented.Defs

/-!
# Lemma 3.1 (untwisting), for the presented algebras

`c_u = κ Σ_i γ_{u,i} a_i` with `Σ_i γ_{u,i} g_{ji} = β_{u,j}` (in the paper `γ_{u,i} = β_{u,i*}`).
`Φ : A_β → A_0`, `b_u ↦ B_u + c_u`, and `Ψ : A_0 → A_β`, `B_u ↦ b_u − c_u`, both fixing the
`a_i`, `κ` and `P`, are defined by the universal property and are mutually inverse. Both commute
with `parity`, so they are even. The paper's instance is
`untwist F n : ABeta F n ≃ₐ[Pmn F n] AZero F n`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

variable {P : Type} [CommRing P] {I K : Type} [Fintype K]
variable {J : I → I → P} {g : K → K → P}

/-- `c_u = κ Σ_i γ_{u,i} a_i`, in `Src J g β'` for any `β'`. -/
def c (β' : I → K → P) (γ : I → K → P) (u : I) : Src J g β' :=
  κ J g β' * ∑ i, γ u i • a J g β' i

/-! ## Identities of `c_u` -/

section c_lemmas

variable {β' : I → K → P}

theorem c_mul_κ (γ : I → K → P) (u : I) : c (J := J) (g := g) β' γ u * κ J g β' = 0 := by
  rw [c, mul_assoc, Finset.sum_mul]
  simp only [smul_mul_assoc]
  have h : ∀ i, a J g β' i * κ J g β' = -(κ J g β' * a J g β' i) := fun i => by
    rw [κ_mul_a, neg_neg]
  simp only [h, smul_neg, Finset.sum_neg_distrib, mul_neg, Finset.mul_sum, mul_smul_comm,
    ← mul_assoc, κ_mul_κ, zero_mul, smul_zero, Finset.sum_const_zero, neg_zero]

theorem κ_mul_c (γ : I → K → P) (u : I) : κ J g β' * c β' γ u = 0 := by
  rw [c, ← mul_assoc, κ_mul_κ, zero_mul]

theorem c_mul_c (γ : I → K → P) (u v : I) : c (J := J) (g := g) β' γ u * c β' γ v = 0 := by
  rw [show c (J := J) (g := g) β' γ u * c β' γ v
      = (c β' γ u * κ J g β') * ∑ i, γ v i • a J g β' i by simp only [c, mul_assoc],
    c_mul_κ, zero_mul]

/-- `[c_u, a_j] = (Σ_i γ_{u,i} g_{ji}) κ`. -/
theorem c_mul_a (γ : I → K → P) (u : I) (j : K) :
    c (J := J) (g := g) β' γ u * a J g β' j
      = a J g β' j * c β' γ u + (∑ i, γ u i * g j i) • κ J g β' := by
  have hcomm : a J g β' j * c β' γ u
      = -(κ J g β' * ∑ i, γ u i • (a J g β' j * a J g β' i)) := by
    rw [c, ← mul_assoc,
      show a J g β' j * κ J g β' = -(κ J g β' * a J g β' j) by rw [κ_mul_a, neg_neg],
      neg_mul, mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm]
  rw [hcomm, c, mul_assoc, Finset.sum_mul, Finset.sum_smul]
  simp only [smul_mul_assoc]
  rw [← sub_eq_iff_eq_add', sub_neg_eq_add, ← mul_add, ← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, a_mul_a_add, mul_smul_comm, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← Algebra.commutes (g j i) (κ J g β'), mul_assoc]

/-- `[b_u, c_v] = 0`. -/
theorem b_mul_c (γ : I → K → P) (u v : I) :
    b J g β' u * c β' γ v = c β' γ v * b J g β' u := by
  rw [c, ← mul_assoc, ← κ_mul_b, mul_assoc, mul_assoc, Finset.mul_sum, Finset.sum_mul,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, b_mul_a, mul_smul_comm, mul_smul_comm, mul_add,
    mul_smul_comm, κ_mul_κ, smul_zero, add_zero]

theorem parity_c (γ : I → K → P) (u : I) : parity (c (J := J) (g := g) β' γ u) = c β' γ u := by
  simp only [c, map_mul, map_sum, map_smul, parity_κ, parity_a, smul_neg, Finset.sum_neg_distrib,
    neg_mul_neg]

end c_lemmas

section untwist

variable {β : I → K → P} {γ : I → K → P} (hγ : ∀ u j, ∑ i, γ u i * g j i = β u j)

/-- The images of the generators under `Φ`: `b_u ↦ B_u + c_u`, `a_i ↦ a_i`, `κ ↦ κ`. -/
def phiGen (γ : I → K → P) : Gen I K → Src J g 0
  | Sum.inl u => b J g 0 u + c 0 γ u
  | Sum.inr (Sum.inl i) => a J g 0 i
  | Sum.inr (Sum.inr _) => κ J g 0

/-- The images of the generators under `Ψ`: `B_u ↦ b_u − c_u`, `a_i ↦ a_i`, `κ ↦ κ`. -/
def psiGen (β : I → K → P) (γ : I → K → P) : Gen I K → Src J g β
  | Sum.inl u => b J g β u - c β γ u
  | Sum.inr (Sum.inl i) => a J g β i
  | Sum.inr (Sum.inr _) => κ J g β

include hγ in
theorem phiGen_rel (x y : FreeAlgebra P (Gen I K)) (h : Rel J g β x y) :
    FreeAlgebra.lift P (phiGen (J := J) (g := g) γ) x = FreeAlgebra.lift P (phiGen γ) y := by
  cases h with
  | bb u v =>
    simp only [map_mul, map_add, AlgHom.commutes, bF, FreeAlgebra.lift_ι_apply, phiGen]
    rw [add_mul, mul_add, mul_add, b_mul_b, c_mul_c, add_mul, mul_add, mul_add, c_mul_c,
      b_mul_c γ v u, b_mul_c γ u v]
    abel
  | aa i j =>
    simp only [map_mul, map_add, AlgHom.commutes, aF, FreeAlgebra.lift_ι_apply, phiGen]
    exact a_mul_a_add i j
  | ba u i =>
    simp only [map_mul, map_add, map_smul, aF, bF, kF, FreeAlgebra.lift_ι_apply, phiGen]
    rw [add_mul, mul_add, b_mul_a, c_mul_a, hγ, Pi.zero_apply, Pi.zero_apply, zero_smul,
      add_zero]
    abel
  | kk =>
    simp only [map_mul, map_zero, kF, FreeAlgebra.lift_ι_apply, phiGen]
    exact κ_mul_κ
  | kb u =>
    simp only [map_mul, kF, bF, FreeAlgebra.lift_ι_apply, phiGen]
    rw [mul_add, add_mul, κ_mul_b, κ_mul_c, c_mul_κ]
  | ka i =>
    simp only [map_mul, map_add, map_zero, kF, aF, FreeAlgebra.lift_ι_apply, phiGen]
    rw [κ_mul_a, neg_add_cancel]

include hγ in
theorem psiGen_rel (x y : FreeAlgebra P (Gen I K)) (h : Rel J g 0 x y) :
    FreeAlgebra.lift P (psiGen (J := J) (g := g) β γ) x
      = FreeAlgebra.lift P (psiGen β γ) y := by
  cases h with
  | bb u v =>
    simp only [map_mul, map_add, AlgHom.commutes, bF, FreeAlgebra.lift_ι_apply, psiGen]
    rw [sub_mul, mul_sub, mul_sub, b_mul_b, c_mul_c, sub_mul, mul_sub, mul_sub, c_mul_c,
      b_mul_c γ v u, b_mul_c γ u v]
    abel
  | aa i j =>
    simp only [map_mul, map_add, AlgHom.commutes, aF, FreeAlgebra.lift_ι_apply, psiGen]
    exact a_mul_a_add i j
  | ba u i =>
    simp only [map_mul, map_add, map_smul, aF, bF, kF, FreeAlgebra.lift_ι_apply, psiGen]
    rw [sub_mul, mul_sub, b_mul_a, c_mul_a, hγ, Pi.zero_apply, Pi.zero_apply, zero_smul,
      add_zero]
    abel
  | kk =>
    simp only [map_mul, map_zero, kF, FreeAlgebra.lift_ι_apply, psiGen]
    exact κ_mul_κ
  | kb u =>
    simp only [map_mul, kF, bF, FreeAlgebra.lift_ι_apply, psiGen]
    rw [mul_sub, sub_mul, κ_mul_b, κ_mul_c, c_mul_κ]
  | ka i =>
    simp only [map_mul, map_add, map_zero, kF, aF, FreeAlgebra.lift_ι_apply, psiGen]
    rw [κ_mul_a, neg_add_cancel]

/-- `Φ : A_β → A_0`. -/
def phi : Src J g β →ₐ[P] Src J g 0 := liftSrc (phiGen γ) (phiGen_rel hγ)

/-- `Ψ : A_0 → A_β`. -/
def psi : Src J g 0 →ₐ[P] Src J g β := liftSrc (psiGen β γ) (psiGen_rel hγ)

theorem phi_b (u : I) : phi hγ (b J g β u) = b J g 0 u + c 0 γ u := by
  simp only [phi, b, liftSrc_mk, bF, FreeAlgebra.lift_ι_apply, phiGen]
theorem phi_a (i : K) : phi hγ (a J g β i) = a J g 0 i := by
  simp only [phi, a, liftSrc_mk, aF, FreeAlgebra.lift_ι_apply, phiGen]
theorem phi_κ : phi hγ (κ J g β) = κ J g 0 := by
  simp only [phi, κ, liftSrc_mk, kF, FreeAlgebra.lift_ι_apply, phiGen]
theorem psi_b (u : I) : psi hγ (b J g 0 u) = b J g β u - c β γ u := by
  simp only [psi, b, liftSrc_mk, bF, FreeAlgebra.lift_ι_apply, psiGen]
theorem psi_a (i : K) : psi hγ (a J g 0 i) = a J g β i := by
  simp only [psi, a, liftSrc_mk, aF, FreeAlgebra.lift_ι_apply, psiGen]
theorem psi_κ : psi hγ (κ J g 0) = κ J g β := by
  simp only [psi, κ, liftSrc_mk, kF, FreeAlgebra.lift_ι_apply, psiGen]

theorem phi_c (u : I) : phi (J := J) hγ (c β γ u) = c 0 γ u := by
  simp only [c, map_mul, map_sum, map_smul, phi_a hγ, phi_κ hγ]
theorem psi_c (u : I) : psi (J := J) hγ (c 0 γ u) = c β γ u := by
  simp only [c, map_mul, map_sum, map_smul, psi_a hγ, psi_κ hγ]

theorem psi_comp_phi : (psi hγ).comp (phi hγ) = AlgHom.id P (Src J g β) := by
  refine algHom_ext (fun u => ?_) (fun i => ?_) ?_
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [phi_b hγ, map_add, psi_b hγ, psi_c hγ, sub_add_cancel]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [phi_a hγ, psi_a hγ]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [phi_κ hγ, psi_κ hγ]

theorem phi_comp_psi : (phi hγ).comp (psi hγ) = AlgHom.id P (Src J g 0) := by
  refine algHom_ext (fun u => ?_) (fun i => ?_) ?_
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [psi_b hγ, map_sub, phi_b hγ, phi_c hγ, add_sub_cancel_right]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [psi_a hγ, phi_a hγ]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [psi_κ hγ, phi_κ hγ]

/-- `Φ` is even. -/
theorem phi_parity (x : Src J g β) : phi hγ (parity x) = parity (phi hγ x) := by
  have h : (phi (J := J) hγ).comp parity = parity.comp (phi hγ) := by
    refine algHom_ext (fun u => ?_) (fun i => ?_) ?_
    · simp only [AlgHom.comp_apply, parity_b, phi_b hγ, map_add, parity_c]
    · simp only [AlgHom.comp_apply, parity_a, phi_a hγ, map_neg]
    · simp only [AlgHom.comp_apply, parity_κ, phi_κ hγ, map_neg]
  exact congrArg (fun φ => φ x) h

/-- `Φ` as an isomorphism. -/
def untwistOf : Src J g β ≃ₐ[P] Src J g 0 :=
  AlgEquiv.ofAlgHom (phi hγ) (psi hγ) (phi_comp_psi hγ) (psi_comp_phi hγ)

end untwist

/-! ## The paper's instance -/

/-- `Σ_i β_{u,i*} g_{ji} = β_{u,j}`. -/
theorem sum_beta_dual_mul_g (F : FermionIndex) (n : ℕ) (u : Bmn.I n) (j : F.K) :
    ∑ i, beta F n u (F.dual i) * gP F n j i = beta F n u j := by
  rw [Fintype.sum_eq_single (F.dual j) (fun i hi => by
    simp only [gP, FermionIndex.g, ite_eq_right_iff.mpr (fun h => absurd h hi), map_zero,
      mul_zero])]
  simp only [gP, FermionIndex.g, F.dual_dual, ite_true, map_one, mul_one]

/-- **Lemma 3.1 (untwisting).** With `c_u = κ Σ_i β_{u,i*} a_i`, an isomorphism `Φ : A_β ≃ A_0` of
`P`-algebras fixing the `a_i` and `κ`, with `Φ(b_u) = B_u + c_u` and `Φ⁻¹(B_u) = b_u − c_u`. -/
noncomputable def untwist (F : FermionIndex) (n : ℕ) : ABeta F n ≃ₐ[Pmn F n] AZero F n :=
  untwistOf (γ := fun u i => beta F n u (F.dual i)) (sum_beta_dual_mul_g F n)

theorem untwist_b (F : FermionIndex) (n : ℕ) (u : Bmn.I n) :
    untwist F n (b _ _ _ u) = b _ _ _ u + c 0 (fun u i => beta F n u (F.dual i)) u :=
  phi_b _ u
theorem untwist_symm_b (F : FermionIndex) (n : ℕ) (u : Bmn.I n) :
    (untwist F n).symm (b _ _ _ u)
      = b _ _ _ u - c (beta F n) (fun u i => beta F n u (F.dual i)) u :=
  psi_b _ u
theorem untwist_a (F : FermionIndex) (n : ℕ) (i : F.K) :
    untwist F n (a _ _ _ i) = a _ _ _ i :=
  phi_a _ i
theorem untwist_κ (F : FermionIndex) (n : ℕ) : untwist F n (κ _ _ _) = κ _ _ _ :=
  phi_κ _
/-- **Lemma 3.1**: the untwisting is even. -/
theorem untwist_parity (F : FermionIndex) (n : ℕ) (x : ABeta F n) :
    untwist F n (parity x) = parity (untwist F n x) :=
  phi_parity _ x

end Presented
end OspN
end OspOddDeformations
