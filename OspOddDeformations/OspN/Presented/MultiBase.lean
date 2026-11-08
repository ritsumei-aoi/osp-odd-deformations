import OspOddDeformations.OspN.Presented.MultiLifts

/-!
# Lemma 3.2 in the presented `A_0` over `R_r`

The bracket of the lifts `L^0`, `S^0`, `F^0` in `AM F n r 0` (the presented `A_0` over `R_r`),
transcribed from `Base.lean`, which transcribed `SourceTensor.lean`: the proofs use only the
relations. The coefficients of `[·,·]_0` are rational and enter through `Multi.emb0`, as in the
coordinate-level `Multi/Defs.lean`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable {F : FermionIndex} {n r : ℕ}

/-- `B_u` in `A_0` over `R_r`. -/
noncomputable abbrev BPM (F : FermionIndex) (n r : ℕ) (u : I n) : AM F n r 0 := bM _ _ 0 u
/-- `a_i` in `A_0` over `R_r`. -/
noncomputable abbrev aPM (F : FermionIndex) (n r : ℕ) (i : F.K) : AM F n r 0 := aM _ _ 0 i

theorem algebraMap_rat_eqM (q : ℚ) :
    algebraMap (Multi.PmnR F n r) (AM F n r 0) (algebraMap ℚ (Multi.PmnR F n r) q) = q • 1 := by
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

theorem BPM_comm (F : FermionIndex) (n r : ℕ) (u v : I n) :
    BPM F n r u * BPM F n r v - BPM F n r v * BPM F n r u = J n u v • (1 : AM F n r 0) := by
  rw [bM_mul_bM, jR, algebraMap_rat_eqM]; abel

theorem aPM_mul_add_swap (F : FermionIndex) (n r : ℕ) (i j : F.K) :
    aPM F n r i * aPM F n r j + aPM F n r j * aPM F n r i = F.g i j • (1 : AM F n r 0) := by
  rw [aM_mul_aM_add, gR, algebraMap_rat_eqM]

theorem BPM_comm_aPM (F : FermionIndex) (n r : ℕ) (u : I n) (i : F.K) :
    BPM F n r u * aPM F n r i = aPM F n r i * BPM F n r u := by
  rw [bM_mul_aM]
  simp

/-- `L^0_{uv}`. -/
noncomputable def L0M (F : FermionIndex) (n r : ℕ) (u v : I n) : AM F n r 0 :=
  (1 / 4 : ℚ) • (BPM F n r u * BPM F n r v + BPM F n r v * BPM F n r u)
/-- `S^0_{ij}`. -/
noncomputable def S0M (F : FermionIndex) (n r : ℕ) (i j : F.K) : AM F n r 0 :=
  (1 / 2 : ℚ) • (aPM F n r i * aPM F n r j - aPM F n r j * aPM F n r i)
/-- `F^0_{u,i}`. -/
noncomputable def F0M (F : FermionIndex) (n r : ℕ) (u : I n) (i : F.K) : AM F n r 0 :=
  (1 / 4 : ℚ) • (aPM F n r i * BPM F n r u + BPM F n r u * aPM F n r i)

/-- The lifts in `A_0` over `R_r`. -/
noncomputable def X0M (F : FermionIndex) (n r : ℕ) : OspBasis F n → AM F n r 0
  | .inl ⟨(u, v), _⟩ => L0M F n r u v
  | .inr (.inl ⟨(i, j), _⟩) => S0M F n r i j
  | .inr (.inr (u, i)) => F0M F n r u i

/-- `ι_0` on `𝔤` with coefficients carried to `P_r` by `emb0`. -/
noncomputable def iota0M (F : FermionIndex) (n r : ℕ) (x : OspMod F n) : AM F n r 0 :=
  ∑ X, Multi.emb0 (r := r) (x X) • X0M F n r X

theorem XpM_zero (X : OspBasis F n) : XpM 0 X = X0M F n r X := by
  match X with
  | .inl ⟨(u, v), _⟩ => rfl
  | .inr (.inl ⟨(i, j), _⟩) => rfl
  | .inr (.inr (u, i)) => rfl

/-! ## `ι_0`'s linearity -/

theorem iota0_addM (F : FermionIndex) (n r : ℕ) (x y : OspMod F n) :
    iota0M F n r (x + y) = iota0M F n r x + iota0M F n r y := by
  simp only [iota0M, ospMod_add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem iota0_zeroM (F : FermionIndex) (n r : ℕ) : iota0M F n r (0 : OspMod F n) = 0 := by
  simp only [iota0M, Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]

theorem iota0_negM (F : FermionIndex) (n r : ℕ) (x : OspMod F n) :
    iota0M F n r (-x) = -iota0M F n r x := by
  simp only [iota0M, Pi.neg_apply, map_neg, neg_smul, Finset.sum_neg_distrib]

theorem iota0_subM (F : FermionIndex) (n r : ℕ) (x y : OspMod F n) :
    iota0M F n r (x - y) = iota0M F n r x - iota0M F n r y := by
  simp only [iota0M, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem iota0_eNM (F : FermionIndex) (n r : ℕ) (X : OspBasis F n) :
    iota0M F n r (eN X) = X0M F n r X := by
  unfold iota0M
  rw [Finset.sum_eq_single X]
  · simp [eN]
  · intro Y _ hY
    simp [eN, hY]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iota0_smul_ratM (F : FermionIndex) (n r : ℕ) (c : ℚ) (x : OspMod F n) :
    iota0M F n r (c • x) = c • iota0M F n r x := by
  simp only [iota0M, Finset.smul_sum, Pi.smul_apply, map_smul, smul_assoc]

theorem BuAB_mul_aAB_eq_two_F0M (F : FermionIndex) (n r : ℕ) (u : I n) (k : F.K) :
    BPM F n r u * aPM F n r k = (2 : ℚ) • F0M F n r u k := by
  have h := BPM_comm_aPM F n r u k
  unfold F0M
  rw [← h]
  module


theorem iota0_SofM (F : FermionIndex) (n r : ℕ) (p q : F.K) : iota0M F n r (Sof p q)
    = S0M F n r p q := by
  unfold Sof
  split_ifs with h1 h2
  · erw [iota0_eNM]; rfl
  · erw [iota0_negM, iota0_eNM]
    change -(S0M F n r q p) = S0M F n r p q
    unfold S0M
    rw [← smul_neg]
    congr 1
    abel
  · have hpq : p = q := F.key_injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    subst hpq
    rw [iota0_zeroM]
    unfold S0M
    simp

theorem X0_LofM (F : FermionIndex) (n r : ℕ) (u v : I n) : X0M F n r (Lof u v) = L0M F n r u v := by
  by_cases h : Bmn.IKey u ≤ Bmn.IKey v
  · simp only [Lof, h, ↓reduceDIte]; rfl
  · simp only [Lof, h, ↓reduceDIte]
    change L0M F n r v u = L0M F n r u v
    unfold L0M
    rw [add_comm]

/-- `X0 (Fof u i) = F0 u i`, a free `rfl` -- `Fof` needs no sorting (`Basis.lean`), unlike
`Lof`, so no bridging work is needed. -/
theorem X0_FofM (F : FermionIndex) (n r : ℕ) (u : I n) (i : F.K) :
    X0M F n r (Fof u i) = F0M F n r u i := rfl

/-! ## `scomm`'s graded antisymmetry, and `gsign`'s square -/

theorem gsign_sqM (p q : ZMod 2) : gsign p q * gsign p q = 1 := by
  unfold gsign
  split_ifs <;> norm_num

/-- `scomm` is itself graded-antisymmetric, the same law `bracket0Basis_super_skew`
gives `bracket0Basis`. Purely algebraic from `scomm`'s own definition, `gsign_sqM` and
`gsign_symm` (`Coboundary.lean`) -- no dependence on `X,Y`'s kind. Used to get the three
reversed kinds (`SL`,`FL`,`FS`) of `base_realizationM` from the three forward kinds
(`LS`,`LF`,`SF`) for free. -/
theorem scomm_antisymmM {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (x y : AM F n r 0) :
    scomm Y X y x = -(gsign (OspN.parity X) (OspN.parity Y)) • scomm X Y x y := by
  unfold scomm
  rw [gsign_symm (OspN.parity Y) (OspN.parity X), smul_sub, smul_smul,
    show -gsign (OspN.parity X) (OspN.parity Y) * gsign (OspN.parity X) (OspN.parity Y) = -1 from by
      rw [neg_mul, gsign_sqM]]
  rw [neg_one_smul, neg_smul, sub_neg_eq_add]
  abel

/-! ## Swap lemmas: moving one generator past another, additive form -/

theorem BuAB_swapM (F : FermionIndex) (n r : ℕ) (u v : I n) :
    BPM F n r u * BPM F n r v = BPM F n r v * BPM F n r u + J n u v • (1 : AM F n r 0) := by
  have h : BPM F n r u * BPM F n r v - BPM F n r v * BPM F n r u - J n u v • (1 : AM F n r 0)
      = 0 := by
    rw [BPM_comm]; abel
  have h3 : BPM F n r u * BPM F n r v
      = (BPM F n r v * BPM F n r u + J n u v • (1 : AM F n r 0))
        + (BPM F n r u * BPM F n r v - BPM F n r v * BPM F n r u - J n u v • (1 : AM F n r 0)) := by
    abel
  rw [h3, h, add_zero]

theorem aAB_swapM (F : FermionIndex) (n r : ℕ) (i j : F.K) :
    aPM F n r i * aPM F n r j = F.g i j • (1 : AM F n r 0) - aPM F n r j * aPM F n r i := by
  have h : aPM F n r i * aPM F n r j + aPM F n r j * aPM F n r i - F.g i j • (1 : AM F n r 0)
      = 0 := by
    rw [aPM_mul_add_swap]; abel
  have h3 : aPM F n r i * aPM F n r j
      = (F.g i j • (1 : AM F n r 0) - aPM F n r j * aPM F n r i)
        + (aPM F n r i * aPM F n r j + aPM F n r j * aPM F n r i - F.g i j • (1 : AM F n r 0)) := by
    abel
  rw [h3, h, add_zero]

/-! ## Primitive commutators: `L0`/`S0` against a single generator -/

theorem L0_comm_aABM (F : FermionIndex) (n r : ℕ) (u v : I n) (k : F.K) :
    L0M F n r u v * aPM F n r k = aPM F n r k * L0M F n r u v := by
  unfold L0M
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : BPM F n r u * BPM F n r v * aPM F n r k
      = aPM F n r k * (BPM F n r u * BPM F n r v) := by
    rw [mul_assoc, BPM_comm_aPM, ← mul_assoc, BPM_comm_aPM, mul_assoc]
  have h2 : BPM F n r v * BPM F n r u * aPM F n r k
      = aPM F n r k * (BPM F n r v * BPM F n r u) := by
    rw [mul_assoc, BPM_comm_aPM, ← mul_assoc, BPM_comm_aPM, mul_assoc]
  rw [add_mul, mul_add, h1, h2]

theorem S0_comm_BuABM (F : FermionIndex) (n r : ℕ) (i j : F.K) (w : I n) :
    S0M F n r i j * BPM F n r w = BPM F n r w * S0M F n r i j := by
  unfold S0M
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : aPM F n r i * aPM F n r j * BPM F n r w
      = BPM F n r w * (aPM F n r i * aPM F n r j) := by
    rw [mul_assoc, ← BPM_comm_aPM, ← mul_assoc, ← BPM_comm_aPM, mul_assoc]
  have h2 : aPM F n r j * aPM F n r i * BPM F n r w
      = BPM F n r w * (aPM F n r j * aPM F n r i) := by
    rw [mul_assoc, ← BPM_comm_aPM, ← mul_assoc, ← BPM_comm_aPM, mul_assoc]
  rw [sub_mul, mul_sub, h1, h2]

/-- **Adjoint action, `L0` against a generator**: `⟦L⁰_{uv}, B_w⟧ = ½(J_{vw}B_u +
J_{uw}B_v)`, a degree-3 computation (not the full `L,L`
degree-4 computation). -/
theorem L0_comm_BuABM (F : FermionIndex) (n r : ℕ) (u v w : I n) :
    L0M F n r u v * BPM F n r w - BPM F n r w * L0M F n r u v
      = (1 / 2 : ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v) := by
  have huvw : BPM F n r u * BPM F n r v * BPM F n r w - BPM F n r w * (BPM F n r u * BPM F n r v)
      = J n u w • BPM F n r v + J n v w • BPM F n r u := by
    have step1 : BPM F n r u * BPM F n r v * BPM F n r w
        = BPM F n r w * (BPM F n r u * BPM F n r v) + J n u w • BPM F n r v
            + J n v w • BPM F n r u := by
      rw [mul_assoc, BuAB_swapM F n r v w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swapM F n r u w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  have hvuw : BPM F n r v * BPM F n r u * BPM F n r w - BPM F n r w * (BPM F n r v * BPM F n r u)
      = J n v w • BPM F n r u + J n u w • BPM F n r v := by
    have step1 : BPM F n r v * BPM F n r u * BPM F n r w
        = BPM F n r w * (BPM F n r v * BPM F n r u) + J n v w • BPM F n r u
            + J n u w • BPM F n r v := by
      rw [mul_assoc, BuAB_swapM F n r u w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swapM F n r v w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  unfold L0M
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [add_mul, mul_add]
  rw [show BPM F n r u * BPM F n r v * BPM F n r w + BPM F n r v * BPM F n r u * BPM F n r w
        - (BPM F n r w * (BPM F n r u * BPM F n r v) + BPM F n r w * (BPM F n r v * BPM F n r u))
      = (BPM F n r u * BPM F n r v * BPM F n r w - BPM F n r w * (BPM F n r u * BPM F n r v))
        + (BPM F n r v * BPM F n r u * BPM F n r w - BPM F n r w * (BPM F n r v * BPM F n r u))
      from by abel]
  rw [huvw, hvuw]
  module

/-- **Adjoint action, `S0` against a generator**: `⟦S⁰_{ij}, a_k⟧ = g_{jk}a_i −
g_{ik}a_j`, the fermionic (anticommuting) analogue of `L0_comm_BuABM`, using `a`'s
anticommutation (`aAB_swapM`) at each swap instead of `B`'s plain commutation. -/
theorem S0_comm_aABM (F : FermionIndex) (n r : ℕ) (i j k : F.K) :
    S0M F n r i j * aPM F n r k - aPM F n r k * S0M F n r i j
      = F.g j k • aPM F n r i - F.g i k • aPM F n r j := by
  have hikj : aPM F n r i * aPM F n r j * aPM F n r k - aPM F n r k * (aPM F n r i * aPM F n r j)
      = F.g j k • aPM F n r i - F.g i k • aPM F n r j := by
    have step1 : aPM F n r i * aPM F n r j * aPM F n r k
        = aPM F n r k * (aPM F n r i * aPM F n r j)
            + F.g j k • aPM F n r i - F.g i k • aPM F n r j := by
      rw [mul_assoc, aAB_swapM F n r j k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swapM F n r i k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  have hjik : aPM F n r j * aPM F n r i * aPM F n r k - aPM F n r k * (aPM F n r j * aPM F n r i)
      = F.g i k • aPM F n r j - F.g j k • aPM F n r i := by
    have step1 : aPM F n r j * aPM F n r i * aPM F n r k
        = aPM F n r k * (aPM F n r j * aPM F n r i)
            + F.g i k • aPM F n r j - F.g j k • aPM F n r i := by
      rw [mul_assoc, aAB_swapM F n r i k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swapM F n r j k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  unfold S0M
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [sub_mul, mul_sub]
  rw [show aPM F n r i * aPM F n r j * aPM F n r k - aPM F n r j * aPM F n r i * aPM F n r k
        - (aPM F n r k * (aPM F n r i * aPM F n r j) - aPM F n r k * (aPM F n r j * aPM F n r i))
      = (aPM F n r i * aPM F n r j * aPM F n r k - aPM F n r k * (aPM F n r i * aPM F n r j))
        - (aPM F n r j * aPM F n r i * aPM F n r k - aPM F n r k * (aPM F n r j * aPM F n r i))
      from by abel]
  rw [hikj, hjik]
  module

/-! ## From a commutator identity to an explicit sum, generically -/

theorem eq_add_of_sub_eq'M {R : Type*} [AddCommGroup R] {a b c : R} (h : a - b = c) :
    a = b + c := by
  have h3 : a = (b + c) + (a - b - c) := by abel
  have h2 : a - b - c = 0 := by rw [h]; abel
  rw [h3, h2, add_zero]

/-! ## Plain-equality forms of the adjoint-action lemmas, and `F0`/`4L0`/`2S0` identities -/

theorem L0_BuAB_eqM (F : FermionIndex) (n r : ℕ) (u v w : I n) :
    L0M F n r u v * BPM F n r w
      = BPM F n r w * L0M F n r u v
        + (1 / 2 : ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v) :=
  eq_add_of_sub_eq'M (L0_comm_BuABM F n r u v w)

theorem S0_aAB_eqM (F : FermionIndex) (n r : ℕ) (i j k : F.K) :
    S0M F n r i j * aPM F n r k
      = aPM F n r k * S0M F n r i j + (F.g j k • aPM F n r i - F.g i k • aPM F n r j) :=
  eq_add_of_sub_eq'M (S0_comm_aABM F n r i j k)

theorem F0_eq_half_BuAB_mul_aABM (F : FermionIndex) (n r : ℕ) (u : I n) (k : F.K) :
    F0M F n r u k = (1 / 2 : ℚ) • (BPM F n r u * aPM F n r k) := by
  rw [BuAB_mul_aAB_eq_two_F0M, smul_smul]
  norm_num

theorem BuAB_add_comm_eq_four_L0M (F : FermionIndex) (n r : ℕ) (u v : I n) :
    BPM F n r u * BPM F n r v + BPM F n r v * BPM F n r u = (4 : ℚ) • L0M F n r u v := by
  unfold L0M
  rw [smul_smul]
  norm_num

theorem aAB_sub_comm_eq_two_S0M (F : FermionIndex) (n r : ℕ) (i j : F.K) :
    aPM F n r i * aPM F n r j - aPM F n r j * aPM F n r i = (2 : ℚ) • S0M F n r i j := by
  unfold S0M
  rw [smul_smul]
  norm_num

/-! ## `L0`/`S0` against a `B*a`, `B*B`, `a*a`-type product, additive form -/

theorem L0_comm_BuAB_mul_aABM (F : FermionIndex) (n r : ℕ) (u v w : I n) (k : F.K) :
    L0M F n r u v * (BPM F n r w * aPM F n r k) - BPM F n r w * aPM F n r k * L0M F n r u v
      = ((1 / 2 : ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v)) * aPM F n r k := by
  rw [← mul_assoc, L0_BuAB_eqM, add_mul, mul_assoc, L0_comm_aABM, ← mul_assoc]
  abel

theorem S0_comm_BuAB_mul_aABM (F : FermionIndex) (n r : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0M F n r i j * (BPM F n r w * aPM F n r k) - BPM F n r w * aPM F n r k * S0M F n r i j
      = BPM F n r w * (F.g j k • aPM F n r i - F.g i k • aPM F n r j) := by
  rw [← mul_assoc, S0_comm_BuABM, mul_assoc, S0_aAB_eqM, mul_add, ← mul_assoc]
  abel

theorem L0_comm_BuAB_mul_BuABM (F : FermionIndex) (n r : ℕ) (u v w z : I n) :
    L0M F n r u v * (BPM F n r w * BPM F n r z) - BPM F n r w * BPM F n r z * L0M F n r u v
      = ((1 / 2 : ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v)) * BPM F n r z
        + BPM F n r w * ((1 / 2 : ℚ) • (J n v z • BPM F n r u + J n u z • BPM F n r v)) := by
  rw [← mul_assoc, L0_BuAB_eqM, add_mul, mul_assoc, L0_BuAB_eqM, mul_add,
    mul_assoc (BPM F n r w) (BPM F n r z) (L0M F n r u v)]
  abel

theorem S0_comm_aAB_mul_aABM (F : FermionIndex) (n r : ℕ) (i j p q : F.K) :
    S0M F n r i j * (aPM F n r p * aPM F n r q) - aPM F n r p * aPM F n r q * S0M F n r i j
      = (F.g j p • aPM F n r i - F.g i p • aPM F n r j) * aPM F n r q
        + aPM F n r p * (F.g j q • aPM F n r i - F.g i q • aPM F n r j) := by
  rw [← mul_assoc, S0_aAB_eqM, add_mul, mul_assoc, S0_aAB_eqM, mul_add,
    mul_assoc (aPM F n r p) (aPM F n r q) (S0M F n r i j)]
  abel

/-! ## The six forward kind-pairs of base realization -/

theorem base_LSM (F : FermionIndex) (n r : ℕ) (u v : I n) (i j : F.K) :
    L0M F n r u v * S0M F n r i j - S0M F n r i j * L0M F n r u v = 0 := by
  unfold S0M
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul]
  have h1 : L0M F n r u v * (aPM F n r i * aPM F n r j)
      = aPM F n r i * aPM F n r j * L0M F n r u v := by
    rw [← mul_assoc, L0_comm_aABM, mul_assoc, L0_comm_aABM, ← mul_assoc]
  have h2 : L0M F n r u v * (aPM F n r j * aPM F n r i)
      = aPM F n r j * aPM F n r i * L0M F n r u v := by
    rw [← mul_assoc, L0_comm_aABM, mul_assoc, L0_comm_aABM, ← mul_assoc]
  rw [h1, h2, sub_self, smul_zero]

theorem base_LFM (F : FermionIndex) (n r : ℕ) (u v w : I n) (k : F.K) :
    L0M F n r u v * F0M F n r w k - F0M F n r w k * L0M F n r u v
      = (1 / 2 : ℚ) • (J n v w • F0M F n r u k + J n u w • F0M F n r v k) := by
  rw [F0_eq_half_BuAB_mul_aABM, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    L0_comm_BuAB_mul_aABM, F0_eq_half_BuAB_mul_aABM, F0_eq_half_BuAB_mul_aABM]
  simp only [smul_mul_assoc, add_mul]
  module

theorem base_SFM (F : FermionIndex) (n r : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0M F n r i j * F0M F n r w k - F0M F n r w k * S0M F n r i j
      = F.g j k • F0M F n r w i - F.g i k • F0M F n r w j := by
  rw [F0_eq_half_BuAB_mul_aABM, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    S0_comm_BuAB_mul_aABM, F0_eq_half_BuAB_mul_aABM, F0_eq_half_BuAB_mul_aABM]
  simp only [mul_sub, mul_smul_comm]
  module

theorem base_LLM (F : FermionIndex) (n r : ℕ) (u v w z : I n) :
    L0M F n r u v * L0M F n r w z - L0M F n r w z * L0M F n r u v
      = (1 / 2 : ℚ) • (J n v w • L0M F n r u z + J n u w • L0M F n r v z
          + J n v z • L0M F n r u w + J n u z • L0M F n r v w) := by
  have hLwz : L0M F n r w z
      = (1 / 4 : ℚ) • (BPM F n r w * BPM F n r z + BPM F n r z * BPM F n r w) := rfl
  rw [hLwz, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_add, add_mul,
    show L0M F n r u v * (BPM F n r w * BPM F n r z) + L0M F n r u v * (BPM F n r z * BPM F n r w)
        - (BPM F n r w * BPM F n r z * L0M F n r u v + BPM F n r z * BPM F n r w * L0M F n r u v)
      = (L0M F n r u v * (BPM F n r w * BPM F n r z) - BPM F n r w * BPM F n r z * L0M F n r u v)
        + (L0M F n r u v * (BPM F n r z * BPM F n r w) - BPM F n r z * BPM F n r w * L0M F n r u v)
      from by abel,
    L0_comm_BuAB_mul_BuABM, L0_comm_BuAB_mul_BuABM]
  have hcomb :
      ((1/2:ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v)) * BPM F n r z
        + BPM F n r w * ((1/2:ℚ) • (J n v z • BPM F n r u + J n u z • BPM F n r v))
        + (((1/2:ℚ) • (J n v z • BPM F n r u + J n u z • BPM F n r v)) * BPM F n r w
          + BPM F n r z * ((1/2:ℚ) • (J n v w • BPM F n r u + J n u w • BPM F n r v)))
      = (1/2:ℚ) • (J n v w • (BPM F n r u * BPM F n r z + BPM F n r z * BPM F n r u)
          + J n u w • (BPM F n r v * BPM F n r z + BPM F n r z * BPM F n r v)
          + J n v z • (BPM F n r u * BPM F n r w + BPM F n r w * BPM F n r u)
          + J n u z • (BPM F n r v * BPM F n r w + BPM F n r w * BPM F n r v)) := by
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add]
    abel
  rw [hcomb, BuAB_add_comm_eq_four_L0M, BuAB_add_comm_eq_four_L0M,
    BuAB_add_comm_eq_four_L0M, BuAB_add_comm_eq_four_L0M]
  module

theorem base_SSM (F : FermionIndex) (n r : ℕ) (i j k l : F.K) :
    S0M F n r i j * S0M F n r k l - S0M F n r k l * S0M F n r i j
      = F.g j k • S0M F n r i l - F.g i k • S0M F n r j l
        - F.g j l • S0M F n r i k + F.g i l • S0M F n r j k := by
  have hSkl : S0M F n r k l
      = (1 / 2 : ℚ) • (aPM F n r k * aPM F n r l - aPM F n r l * aPM F n r k) := rfl
  rw [hSkl, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul,
    show S0M F n r i j * (aPM F n r k * aPM F n r l) - S0M F n r i j * (aPM F n r l * aPM F n r k)
        - (aPM F n r k * aPM F n r l * S0M F n r i j - aPM F n r l * aPM F n r k * S0M F n r i j)
      = (S0M F n r i j * (aPM F n r k * aPM F n r l) - aPM F n r k * aPM F n r l * S0M F n r i j)
        - (S0M F n r i j * (aPM F n r l * aPM F n r k) - aPM F n r l * aPM F n r k * S0M F n r i j)
      from by abel,
    S0_comm_aAB_mul_aABM, S0_comm_aAB_mul_aABM]
  have hcomb :
      (F.g j k • aPM F n r i - F.g i k • aPM F n r j) * aPM F n r l
        + aPM F n r k * (F.g j l • aPM F n r i - F.g i l • aPM F n r j)
        - ((F.g j l • aPM F n r i - F.g i l • aPM F n r j) * aPM F n r k
          + aPM F n r l * (F.g j k • aPM F n r i - F.g i k • aPM F n r j))
      = F.g j k • (aPM F n r i * aPM F n r l - aPM F n r l * aPM F n r i)
        - F.g i k • (aPM F n r j * aPM F n r l - aPM F n r l * aPM F n r j)
        - F.g j l • (aPM F n r i * aPM F n r k - aPM F n r k * aPM F n r i)
        + F.g i l • (aPM F n r j * aPM F n r k - aPM F n r k * aPM F n r j) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [hcomb, aAB_sub_comm_eq_two_S0M, aAB_sub_comm_eq_two_S0M,
    aAB_sub_comm_eq_two_S0M, aAB_sub_comm_eq_two_S0M]
  module

/-- A pure-ring identity (no commutativity of `X,Y,P,Q` needed): `X*P+Y*Q` is the
"half-sum-plus-half-difference" combination `½[(X+Y)(P+Q)+(X-Y)(P-Q)]`. Used by
`base_FFM` to turn `BuAB u*BuAB v` and `aAB i*aAB j`'s SEPARATE sum/difference facts
into the anticommutator `F0(u,i)*F0(v,j)+F0(v,j)*F0(u,i)` directly, without solving
for `BuAB u*BuAB v` or `aAB i*aAB j` individually. -/
theorem mul_add_mul_eq_halfM (F : FermionIndex) (n r : ℕ) (X Y P Q : AM F n r 0) :
    X * P + Y * Q = (1 / 2 : ℚ) • ((X + Y) * (P + Q) + (X - Y) * (P - Q)) := by
  have expand : (X + Y) * (P + Q) + (X - Y) * (P - Q)
      = (X * P + Y * Q) + (X * P + Y * Q) := by
    rw [add_mul, mul_add, mul_add, sub_mul, mul_sub, mul_sub]
    abel
  rw [expand, ← two_smul ℚ, smul_smul]
  norm_num

theorem base_FFM (F : FermionIndex) (n r : ℕ) (u : I n) (i : F.K) (v : I n) (j : F.K) :
    F0M F n r u i * F0M F n r v j + F0M F n r v j * F0M F n r u i
      = (1 / 4 : ℚ) • (J n u v • S0M F n r i j) + (1 / 2 : ℚ) • (F.g i j • L0M F n r u v) := by
  rw [F0_eq_half_BuAB_mul_aABM, F0_eq_half_BuAB_mul_aABM,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmove1 : BPM F n r u * aPM F n r i * (BPM F n r v * aPM F n r j)
      = BPM F n r u * BPM F n r v * (aPM F n r i * aPM F n r j) := by
    rw [mul_assoc, ← mul_assoc (aPM F n r i), ← BPM_comm_aPM, mul_assoc, ← mul_assoc]
  have hmove2 : BPM F n r v * aPM F n r j * (BPM F n r u * aPM F n r i)
      = BPM F n r v * BPM F n r u * (aPM F n r j * aPM F n r i) := by
    rw [mul_assoc, ← mul_assoc (aPM F n r j), ← BPM_comm_aPM, mul_assoc, ← mul_assoc]
  rw [hmove1, hmove2,
    show (1 / 2 * (1 / 2) : ℚ)
          • (BPM F n r u * BPM F n r v * (aPM F n r i * aPM F n r j))
        + (1 / 2 * (1 / 2) : ℚ)
          • (BPM F n r v * BPM F n r u * (aPM F n r j * aPM F n r i))
      = (1 / 4 : ℚ) • (BPM F n r u * BPM F n r v * (aPM F n r i * aPM F n r j)
          + BPM F n r v * BPM F n r u * (aPM F n r j * aPM F n r i))
      from by rw [show (1 / 2 * (1 / 2) : ℚ) = 1 / 4 from by norm_num, ← smul_add],
    mul_add_mul_eq_halfM F n r (BPM F n r u * BPM F n r v) (BPM F n r v * BPM F n r u)
      (aPM F n r i * aPM F n r j) (aPM F n r j * aPM F n r i),
    BuAB_add_comm_eq_four_L0M, BPM_comm, aPM_mul_add_swap, aAB_sub_comm_eq_two_S0M]
  simp only [smul_smul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
  module

/-- **Lemma 3.2 (the base bracket)**, in the presented `A_0`: the supercommutator of two lifts is
the lift of `[·,·]_0`. -/
theorem base_realizationM (F : FermionIndex) (n r : ℕ) (X Y : OspBasis F n) :
    scomm X Y (X0M F n r X) (X0M F n r Y) = iota0M F n r (bracket0Basis X Y) := by
  match X, Y with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    change L0M F n r u v * L0M F n r w z - gsign 0 0 • (L0M F n r w z * L0M F n r u v)
        = iota0M F n r (bracketLL u v w z)
    rw [gsign_00, one_smul, base_LLM]
    unfold bracketLL
    rw [iota0_addM, iota0_addM, iota0_addM, iota0_smul_ratM, iota0_smul_ratM, iota0_smul_ratM,
      iota0_smul_ratM, iota0_eNM, iota0_eNM, iota0_eNM, iota0_eNM, X0_LofM, X0_LofM, X0_LofM,
        X0_LofM,
      smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  | .inl ⟨(u, v), _⟩, .inr (.inl ⟨(i, j), _⟩) =>
    change L0M F n r u v * S0M F n r i j - gsign 0 0 • (S0M F n r i j * L0M F n r u v)
        = iota0M F n r (0 : OspMod F n)
    rw [gsign_00, one_smul, base_LSM, iota0_zeroM]
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) =>
    change L0M F n r u v * F0M F n r w i - gsign 0 1 • (F0M F n r w i * L0M F n r u v)
        = iota0M F n r (bracketLF u v w i)
    rw [gsign_01, one_smul, base_LFM]
    unfold bracketLF
    rw [iota0_addM, iota0_smul_ratM, iota0_smul_ratM, iota0_eNM, iota0_eNM, X0_FofM, X0_FofM,
      smul_add, smul_smul, smul_smul]
  | .inr (.inl ⟨(i, j), _⟩), .inl ⟨(u, v), _⟩ =>
    change S0M F n r i j * L0M F n r u v - gsign 0 0 • (L0M F n r u v * S0M F n r i j)
        = iota0M F n r (0 : OspMod F n)
    rw [gsign_00, one_smul,
      show S0M F n r i j * L0M F n r u v - L0M F n r u v * S0M F n r i j
          = -(L0M F n r u v * S0M F n r i j - S0M F n r i j * L0M F n r u v) from by abel,
      base_LSM, neg_zero, iota0_zeroM]
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) =>
    change S0M F n r i j * S0M F n r k l - gsign 0 0 • (S0M F n r k l * S0M F n r i j)
        = iota0M F n r (bracketSS i j k l)
    rw [gsign_00, one_smul, base_SSM]
    unfold bracketSS
    rw [iota0_addM, iota0_subM, iota0_subM, iota0_smul_ratM, iota0_smul_ratM, iota0_smul_ratM,
      iota0_smul_ratM, iota0_SofM, iota0_SofM, iota0_SofM, iota0_SofM]
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) =>
    change S0M F n r j k * F0M F n r w i - gsign 0 1 • (F0M F n r w i * S0M F n r j k)
        = iota0M F n r (bracketSF j k w i)
    rw [gsign_01, one_smul, base_SFM]
    unfold bracketSF
    rw [iota0_subM, iota0_smul_ratM, iota0_smul_ratM, iota0_eNM, iota0_eNM, X0_FofM, X0_FofM]
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ =>
    change F0M F n r w i * L0M F n r u v - gsign 1 0 • (L0M F n r u v * F0M F n r w i)
        = iota0M F n r (-bracketLF u v w i)
    rw [gsign_10, one_smul,
      show F0M F n r w i * L0M F n r u v - L0M F n r u v * F0M F n r w i
          = -(L0M F n r u v * F0M F n r w i - F0M F n r w i * L0M F n r u v) from by abel,
      base_LFM, iota0_negM]
    unfold bracketLF
    rw [iota0_addM, iota0_smul_ratM, iota0_smul_ratM, iota0_eNM, iota0_eNM, X0_FofM, X0_FofM,
      smul_add, smul_smul, smul_smul]
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) =>
    change F0M F n r w i * S0M F n r j k - gsign 1 0 • (S0M F n r j k * F0M F n r w i)
        = iota0M F n r (-bracketSF j k w i)
    rw [gsign_10, one_smul,
      show F0M F n r w i * S0M F n r j k - S0M F n r j k * F0M F n r w i
          = -(S0M F n r j k * F0M F n r w i - F0M F n r w i * S0M F n r j k) from by abel,
      base_SFM, iota0_negM]
    unfold bracketSF
    rw [iota0_subM, iota0_smul_ratM, iota0_smul_ratM, iota0_eNM, iota0_eNM, X0_FofM, X0_FofM]
  | .inr (.inr (u, i)), .inr (.inr (v, j)) =>
    change F0M F n r u i * F0M F n r v j - gsign 1 1 • (F0M F n r v j * F0M F n r u i)
        = iota0M F n r (bracketFF u i v j)
    rw [gsign_11, neg_smul, one_smul, sub_neg_eq_add, base_FFM]
    unfold bracketFF
    rw [iota0_addM, iota0_smul_ratM, iota0_smul_ratM, iota0_SofM, iota0_eNM, X0_LofM, smul_smul,
      smul_smul]


end Presented
end OspN
end OspOddDeformations
