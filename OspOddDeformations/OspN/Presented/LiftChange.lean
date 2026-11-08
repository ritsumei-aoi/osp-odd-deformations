import OspOddDeformations.OspN.Presented.Base

/-!
# Prop 4.1 (the change of lifts), for the presented algebras

`Φ(ι_β X) = ι_0(X + κ h̃(X))` for every basis element `X` (`untwist_Xp`), and hence
`Φ(ι_β x) = ι_0(x) + κ ι_0(h̃ x)` for `x ∈ 𝔤_P` (`untwist_iotaP`). `Φ` is `untwist F n` of
`Untwist.lean`. In `A_0` the image `Φ(b_u) = B_u + c_u` is written `bUP`, with
`c_u = Σ_i β_{u,i} κ a_{i*}` (`cP`, equal to `Untwist.c` by re-indexing, `c_eq_cP`); the computation
of `Φ(X̂)` is that of the realization (`Xhat_eq_iota0_add` in `SourceTensor.lean`), transcribed.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable (F : FermionIndex) (n : ℕ)

/-- `κ` in `A_0`. -/
noncomputable abbrev κP : AZero F n := κ _ _ 0
/-- A coefficient `c ∈ P` in `A_0`. -/
noncomputable abbrev coefP (c : Pmn F n) : AZero F n := algebraMap (Pmn F n) (AZero F n) c
/-- `β_{u,i} κ` in `A_0`. -/
noncomputable def betaKappaP (u : I n) (i : F.K) : AZero F n := coefP F n (beta F n u i) * κP F n
/-- `c_u = Σ_i β_{u,i} κ a_{i*}` in `A_0`. -/
noncomputable def cP (u : I n) : AZero F n := ∑ i : F.K, betaKappaP F n u i * aP F n (F.dual i)
/-- `Φ(b_u) = B_u + c_u`. -/
noncomputable def bUP (u : I n) : AZero F n := BP F n u + cP F n u
/-- `Φ(L̂_{uv})`. -/
noncomputable def LhatP (u v : I n) : AZero F n :=
  (1 / 4 : ℚ) • (bUP F n u * bUP F n v + bUP F n v * bUP F n u)
/-- `Φ(Ŝ_{ij}) = S^0_{ij}`. -/
noncomputable def ShatP (i j : F.K) : AZero F n := S0P F n i j
/-- `Φ(F̂_{u,i})`. -/
noncomputable def FhatP (u : I n) (i : F.K) : AZero F n :=
  (1 / 4 : ℚ) • (aP F n i * bUP F n u + bUP F n u * aP F n i)
/-- `Φ` of the lifts of `A_β`. -/
noncomputable def XhatP : OspBasis F n → AZero F n
  | .inl ⟨(u, v), _⟩ => LhatP F n u v
  | .inr (.inl ⟨(i, j), _⟩) => ShatP F n i j
  | .inr (.inr (u, i)) => FhatP F n u i

theorem c_eq_cP (u : I n) : c 0 (fun u i => beta F n u (F.dual i)) u = cP F n u := by
  rw [c, Finset.mul_sum, cP, ← sum_dual (fun i => betaKappaP F n u i * aP F n (F.dual i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.dual_dual, betaKappaP, mul_smul_comm, Algebra.smul_def, ← mul_assoc]

theorem BP_comm_betaKappaP (u v : I n) (j : F.K) :
    BP F n u * betaKappaP F n v j = betaKappaP F n v j * BP F n u := by
  rw [betaKappaP, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc]
  congr 1
  exact (κ_mul_b u).symm

theorem aP_mul_betaKappaP (v : I n) (j : F.K) (i : F.K) :
    aP F n i * betaKappaP F n v j = -(betaKappaP F n v j * aP F n i) := by
  rw [betaKappaP, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc, ← mul_neg]
  congr 1
  rw [κ_mul_a, neg_neg]

theorem cP_mul_cP (u v : I n) : cP F n u * cP F n v = 0 := by
  rw [← c_eq_cP, ← c_eq_cP, c_mul_c]

theorem BP_comm_cP (u v : I n) : BP F n u * cP F n v = cP F n v * BP F n u := by
  rw [← c_eq_cP, b_mul_c]

theorem κP_mul_coefP_beta (u : I n) (i : F.K) :
    κP F n * coefP F n (beta F n u i) = betaKappaP F n u i := by
  rw [betaKappaP, Algebra.commutes]

theorem iota0P_smul_eN (c : Pmn F n) (X : OspBasis F n) :
    iota0P F n (c • eN X) = coefP F n c * X0P F n X := by
  unfold iota0P
  rw [Finset.sum_eq_single X]
  · simp [eN, Algebra.smul_def]
  · intro Y _ hY
    simp [eN, hY]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iota0P_smul (c : Pmn F n) (x : OspMod F n) :
    iota0P F n (c • x) = coefP F n c * iota0P F n x := by
  simp only [iota0P, Finset.mul_sum, ospMod_smul_apply, Algebra.smul_def, map_mul, mul_assoc]

theorem iota0P_sum {α : Type*} (s : Finset α) (f : α → OspMod F n) :
    iota0P F n (∑ a ∈ s, f a) = ∑ a ∈ s, iota0P F n (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [iota0_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, iota0_add, ih, Finset.sum_insert ha]

theorem untwist_Xp (X : OspBasis F n) : untwist F n (Xp (beta F n) X) = XhatP F n X := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    simp only [Xp, Lp, XhatP, LhatP, map_smul, map_add, map_mul, untwist_b, c_eq_cP]
    rw [q4_smul]
    rfl
  | .inr (.inl ⟨(i, j), _⟩) =>
    simp only [Xp, Sp, XhatP, ShatP, S0P, map_smul, map_sub, map_mul, untwist_a]
    rw [q2_smul]
  | .inr (.inr (u, i)) =>
    simp only [Xp, Fp, XhatP, FhatP, map_smul, map_add, map_mul, untwist_a, untwist_b, c_eq_cP]
    rw [q4_smul]
    rfl

theorem XhatP_eq (X : OspBasis F n) :
    XhatP F n X = iota0P F n (eN X) + κP F n * iota0P F n (hTilde (eN X)) := by
  match X with
  | .inr (.inl ⟨(i, j), h⟩) =>
    erw [iota0_eN, hTilde_eN]
    change ShatP F n i j = X0P F n (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n)
      + κP F n * iota0P F n (hTildeBasis (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n))
    have hz : hTildeBasis (Sum.inr (Sum.inl ⟨(i, j), h⟩) : OspBasis F n) = 0 := rfl
    rw [hz, iota0_zero, mul_zero, add_zero]
    change ShatP F n i j = S0P F n i j
    rfl
  | .inl ⟨(u, v), h⟩ =>
    change LhatP F n u v = iota0P F n (eN (Sum.inl ⟨(u, v), h⟩ : OspBasis F n))
      + κP F n * iota0P F n (hTilde (eN (Sum.inl ⟨(u, v), h⟩ : OspBasis F n)))
    have hLhat_eq : LhatP F n u v
        = L0P F n u v
          + ∑ i : F.K, (betaKappaP F n u (F.dual i) * F0P F n v i
              + betaKappaP F n v (F.dual i) * F0P F n u i) := by
      unfold LhatP
      have hexp : bUP F n u * bUP F n v + bUP F n v * bUP F n u
          = (BP F n u * BP F n v + BP F n v * BP F n u)
            + (BP F n u * cP F n v + cP F n v * BP F n u)
            + (cP F n u * BP F n v + BP F n v * cP F n u)
            + (cP F n u * cP F n v + cP F n v * cP F n u) := by
        unfold bUP; noncomm_ring
      rw [hexp]
      have hL4 : BP F n u * BP F n v + BP F n v * BP F n u = (4 : ℚ) • L0P F n u v := by
        unfold L0P; rw [smul_smul]; norm_num
      have hcc0 : cP F n u * cP F n v + cP F n v * cP F n u = 0 := by
        rw [cP_mul_cP, cP_mul_cP]; abel
      have hBv_cu : BP F n u * cP F n v
          = (2 : ℚ) • ∑ i : F.K, betaKappaP F n v (F.dual i) * F0P F n u i := by
        unfold cP
        rw [Finset.mul_sum]
        have hstep : ∀ j : F.K, BP F n u * (betaKappaP F n v j * aP F n (F.dual j))
            = (2 : ℚ) • (betaKappaP F n v j * F0P F n u (F.dual j)) := by
          intro j
          rw [show BP F n u * (betaKappaP F n v j * aP F n (F.dual j))
              = (BP F n u * betaKappaP F n v j) * aP F n (F.dual j) from by noncomm_ring,
            BP_comm_betaKappaP, mul_assoc, BuAB_mul_aAB_eq_two_F0, mul_smul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.smul_sum]
        congr 1
        have hr := sum_dual (M := AZero F n)
          (fun i => betaKappaP F n v (F.dual i) * F0P F n u i)
        simpa only [F.dual_dual] using hr
      have hBc : BP F n u * cP F n v + cP F n v * BP F n u
          = (2 : ℚ) • ((2 : ℚ) • ∑ i : F.K, betaKappaP F n v (F.dual i) * F0P F n u i) := by
        rw [← BP_comm_cP, hBv_cu]; module
      have hcv_Bu : cP F n u * BP F n v
          = (2 : ℚ) • ∑ i : F.K, betaKappaP F n u (F.dual i) * F0P F n v i := by
        unfold cP
        rw [Finset.sum_mul]
        have hstep : ∀ j : F.K, betaKappaP F n u j * aP F n (F.dual j) * BP F n v
            = (2 : ℚ) • (betaKappaP F n u j * F0P F n v (F.dual j)) := by
          intro j
          rw [show betaKappaP F n u j * aP F n (F.dual j) * BP F n v
              = betaKappaP F n u j * (aP F n (F.dual j) * BP F n v) from by noncomm_ring,
            ← BP_comm_aP, BuAB_mul_aAB_eq_two_F0, mul_smul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.smul_sum]
        congr 1
        have hr := sum_dual (M := AZero F n)
          (fun i => betaKappaP F n u (F.dual i) * F0P F n v i)
        simpa only [F.dual_dual] using hr
      have hcB : cP F n u * BP F n v + BP F n v * cP F n u
          = (2 : ℚ) • ((2 : ℚ) • ∑ i : F.K, betaKappaP F n u (F.dual i) * F0P F n v i) := by
        rw [BP_comm_cP, hcv_Bu]; module
      have hcombine : (∑ i : F.K, (betaKappaP F n u (F.dual i) * F0P F n v i
            + betaKappaP F n v (F.dual i) * F0P F n u i) : AZero F n)
          = (∑ i : F.K, betaKappaP F n u (F.dual i) * F0P F n v i)
            + ∑ i : F.K, betaKappaP F n v (F.dual i) * F0P F n u i :=
        Finset.sum_add_distrib
      rw [hL4, hBc, hcB, hcc0, add_zero, hcombine]
      module
    erw [hLhat_eq, iota0_eN, hTilde_eN]
    have hX0 : X0P F n (Sum.inl ⟨(u, v), h⟩ : OspBasis F n) = L0P F n u v := rfl
    have hHt : hTildeBasis (Sum.inl ⟨(u, v), h⟩ : OspBasis F n)
        = ∑ i : F.K, (beta F n u (F.dual i) • eN (Fof v i)
            + beta F n v (F.dual i) • eN (Fof u i)) := rfl
    rw [hX0, hHt, iota0P_sum]
    have hterm : ∀ i : F.K, iota0P F n (beta F n u (F.dual i) • eN (Fof v i)
          + beta F n v (F.dual i) • eN (Fof u i))
        = coefP F n (beta F n u (F.dual i))
            * F0P F n v i
          + coefP F n (beta F n v (F.dual i))
            * F0P F n u i := by
      intro i
      rw [iota0_add, iota0P_smul_eN, iota0P_smul_eN]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_add, ← mul_assoc, ← mul_assoc, κP_mul_coefP_beta,
      κP_mul_coefP_beta]
  | .inr (.inr (u, i)) =>
    change FhatP F n u i = iota0P F n (eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
      + κP F n * iota0P F n (hTilde (eN (Sum.inr (Sum.inr (u, i)) : OspBasis F n)))
    have hFhat_eq : FhatP F n u i
        = F0P F n u i + (1 / 2 : ℚ) • ∑ j : F.K, betaKappaP F n u j * S0P F n (F.dual j) i := by
      unfold FhatP
      have hexp : aP F n i * bUP F n u + bUP F n u * aP F n i
          = (aP F n i * BP F n u + BP F n u * aP F n i)
            + (aP F n i * cP F n u + cP F n u * aP F n i) := by
        unfold bUP; noncomm_ring
      rw [hexp]
      have hB4 : aP F n i * BP F n u + BP F n u * aP F n i = (4 : ℚ) • F0P F n u i := by
        unfold F0P
        rw [smul_smul]
        norm_num
      have hc2 : aP F n i * cP F n u + cP F n u * aP F n i
          = (2 : ℚ) • ∑ j : F.K, betaKappaP F n u j * S0P F n (F.dual j) i := by
        unfold cP
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have e0 : aP F n i * (betaKappaP F n u j * aP F n (F.dual j))
            = -(betaKappaP F n u j * (aP F n i * aP F n (F.dual j))) := by
          rw [show aP F n i * (betaKappaP F n u j * aP F n (F.dual j))
              = (aP F n i * betaKappaP F n u j) * aP F n (F.dual j) from by noncomm_ring,
            aP_mul_betaKappaP]
          noncomm_ring
        have e1 : (betaKappaP F n u j * aP F n (F.dual j)) * aP F n i
            = betaKappaP F n u j * (aP F n (F.dual j) * aP F n i) := by noncomm_ring
        have hS : aP F n (F.dual j) * aP F n i - aP F n i * aP F n (F.dual j)
            = (2 : ℚ) • S0P F n (F.dual j) i := by
          unfold S0P; rw [smul_smul]; norm_num
        rw [e0, e1,
          show -(betaKappaP F n u j * (aP F n i * aP F n (F.dual j)))
              + betaKappaP F n u j * (aP F n (F.dual j) * aP F n i)
            = betaKappaP F n u j
                * (aP F n (F.dual j) * aP F n i - aP F n i * aP F n (F.dual j)) from by
            noncomm_ring,
          hS, mul_smul_comm]
      rw [hB4, hc2, smul_add, smul_smul, smul_smul]
      norm_num
    erw [hFhat_eq, iota0_eN, hTilde_eN]
    change F0P F n u i
        + (1 / 2 : ℚ) • ∑ j : F.K, betaKappaP F n u j * S0P F n (F.dual j) i
      = X0P F n (Sum.inr (Sum.inr (u, i)) : OspBasis F n)
        + κP F n
          * iota0P F n (hTildeBasis (Sum.inr (Sum.inr (u, i)) : OspBasis F n))
    have hX0 : X0P F n (Sum.inr (Sum.inr (u, i)) : OspBasis F n) = F0P F n u i := rfl
    have hHt : hTildeBasis (Sum.inr (Sum.inr (u, i)) : OspBasis F n)
        = (1 / 2 : ℚ) • ∑ j : F.K, beta F n u j • Sof (F.dual j) i := rfl
    rw [hX0, hHt, iota0_smul_rat, iota0P_sum]
    have hterm : ∀ j : F.K, iota0P F n (beta F n u j • Sof (F.dual j) i)
        = coefP F n (beta F n u j) * S0P F n (F.dual j) i :=
            by
      intro j
      rw [iota0P_smul, iota0_Sof]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    congr 1
    rw [mul_smul_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, κP_mul_coefP_beta]


/-- **Prop 4.1**, for the presented algebras: `Φ(ι_β X) = ι_0(X + κ h̃ X)` for a basis element. -/
theorem untwist_Xp_eq (X : OspBasis F n) :
    untwist F n (Xp (beta F n) X) = iota0P F n (eN X) + κP F n * iota0P F n (hTilde (eN X)) := by
  rw [untwist_Xp, XhatP_eq]

/-- **Prop 4.1**, on `𝔤_P`: `Φ(ι_β x) = ι_0(x) + κ ι_0(h̃ x)`. -/
theorem untwist_iotaP (x : OspMod F n) :
    untwist F n (iotaP (beta F n) x) = iota0P F n x + κP F n * iota0P F n (hTilde x) := by
  rw [iotaP, map_sum]
  simp only [map_smul, untwist_Xp_eq, smul_add, Finset.sum_add_distrib, iota0_eN, hTilde_eN]
  congr 1
  rw [hTilde, iota0P_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [iota0P_smul, Algebra.smul_def, ← mul_assoc, ← mul_assoc, Algebra.commutes]

end Presented
end OspN
end OspOddDeformations
