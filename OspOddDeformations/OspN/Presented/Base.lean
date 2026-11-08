import OspOddDeformations.OspN.Presented.Realize

/-!
# Lemma 3.2 (the base bracket) in the presented `A_0`

The supercommutators of the lifts `L^0`, `S^0`, `F^0` in the presented `A_0` are the lifts of
`[·,·]_0` (`base_realization`). The proofs are those of the realization (`SourceTensor.lean`,
`base_*`), transcribed: they use only the relations of `A_0`, which hold in the presented algebra by
definition (`BP_comm`, `aP_mul_add_swap`, `BP_comm_aP`). Here `A_0` is also a `ℚ`-algebra, through
`P`.
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

variable {F : FermionIndex} {n : ℕ}

noncomputable instance (β' : I n → F.K → Pmn F n) : Algebra ℚ (Src (jP F n) (gP F n) β') :=
  inferInstanceAs (Algebra ℚ (RingQuot _))

instance (β' : I n → F.K → Pmn F n) : IsScalarTower ℚ (Pmn F n) (Src (jP F n) (gP F n) β') :=
  inferInstanceAs (IsScalarTower ℚ (Pmn F n) (RingQuot _))

/-- `B_u` in `A_0`. -/
noncomputable abbrev BP (F : FermionIndex) (n : ℕ) (u : I n) : AZero F n := b _ _ 0 u
/-- `a_i` in `A_0`. -/
noncomputable abbrev aP (F : FermionIndex) (n : ℕ) (i : F.K) : AZero F n := a _ _ 0 i

theorem algebraMap_rat_eq (β' : I n → F.K → Pmn F n) (q : ℚ) :
    algebraMap (Pmn F n) (Src (jP F n) (gP F n) β') (algebraMap ℚ (Pmn F n) q) = q • 1 := by
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

theorem BP_comm (F : FermionIndex) (n : ℕ) (u v : I n) :
    BP F n u * BP F n v - BP F n v * BP F n u = J n u v • (1 : AZero F n) := by
  rw [b_mul_b, jP, algebraMap_rat_eq]; abel

theorem aP_mul_add_swap (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aP F n i * aP F n j + aP F n j * aP F n i = F.g i j • (1 : AZero F n) := by
  rw [a_mul_a_add, gP, algebraMap_rat_eq]

theorem BP_comm_aP (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    BP F n u * aP F n i = aP F n i * BP F n u := by
  rw [b_mul_a, Pi.zero_apply, Pi.zero_apply, zero_smul, add_zero]

/-- `L^0_{uv}`. -/
noncomputable def L0P (F : FermionIndex) (n : ℕ) (u v : I n) : AZero F n :=
  (1 / 4 : ℚ) • (BP F n u * BP F n v + BP F n v * BP F n u)
/-- `S^0_{ij}`. -/
noncomputable def S0P (F : FermionIndex) (n : ℕ) (i j : F.K) : AZero F n :=
  (1 / 2 : ℚ) • (aP F n i * aP F n j - aP F n j * aP F n i)
/-- `F^0_{u,i}`. -/
noncomputable def F0P (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) : AZero F n :=
  (1 / 4 : ℚ) • (aP F n i * BP F n u + BP F n u * aP F n i)

/-- The lifts in `A_0`, with `ℚ` coefficients. -/
noncomputable def X0P (F : FermionIndex) (n : ℕ) : OspBasis F n → AZero F n
  | .inl ⟨(u, v), _⟩ => L0P F n u v
  | .inr (.inl ⟨(i, j), _⟩) => S0P F n i j
  | .inr (.inr (u, i)) => F0P F n u i

/-- `ι_0` on `𝔤_P`. -/
noncomputable def iota0P (F : FermionIndex) (n : ℕ) (x : OspMod F n) : AZero F n :=
  ∑ X, x X • X0P F n X

theorem q4_smul (β' : I n → F.K → Pmn F n) (y : Src (jP F n) (gP F n) β') :
    q4 F n • y = (1 / 4 : ℚ) • y := algebraMap_smul (Pmn F n) (1 / 4 : ℚ) y
theorem q2_smul (β' : I n → F.K → Pmn F n) (y : Src (jP F n) (gP F n) β') :
    q2 F n • y = (1 / 2 : ℚ) • y := algebraMap_smul (Pmn F n) (1 / 2 : ℚ) y

theorem Xp_zero (X : OspBasis F n) : Xp 0 X = X0P F n X := by
  match X with
  | .inl ⟨(u, v), _⟩ => simp only [Xp, Lp, X0P, L0P, q4_smul]
  | .inr (.inl ⟨(i, j), _⟩) => simp only [Xp, Sp, X0P, S0P, q2_smul]
  | .inr (.inr (u, i)) => simp only [Xp, Fp, X0P, F0P, q4_smul]

theorem iotaP_zero (x : OspMod F n) : iotaP 0 x = iota0P F n x := by
  simp only [iotaP, iota0P, Xp_zero]

/-- The supercommutator with the parities of two basis elements. -/
noncomputable def scomm {A : Type} [Ring A] [Module ℚ A] (X Y : OspBasis F n) (x y : A) : A :=
  x * y - gsign (OspN.parity X) (OspN.parity Y) • (y * x)

/-! ## `ι_0`'s linearity -/

theorem iota0_add (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    iota0P F n (x + y) = iota0P F n x + iota0P F n y := by
  simp only [iota0P, ospMod_add_apply, add_smul, Finset.sum_add_distrib]

theorem iota0_zero (F : FermionIndex) (n : ℕ) : iota0P F n (0 : OspMod F n) = 0 := by
  simp only [iota0P, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

theorem iota0_neg (F : FermionIndex) (n : ℕ) (x : OspMod F n) :
    iota0P F n (-x) = -iota0P F n x := by
  simp only [iota0P, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem iota0_sub (F : FermionIndex) (n : ℕ) (x y : OspMod F n) :
    iota0P F n (x - y) = iota0P F n x - iota0P F n y := by
  simp only [iota0P, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem iota0_eN (F : FermionIndex) (n : ℕ) (X : OspBasis F n) : iota0P F n (eN X) = X0P F n X := by
  unfold iota0P
  rw [Finset.sum_eq_single X]
  · simp [eN]
  · intro Y _ hY
    simp [eN, hY]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem iota0_smul_rat (F : FermionIndex) (n : ℕ) (c : ℚ) (x : OspMod F n) :
    iota0P F n (c • x) = c • iota0P F n x := by
  simp only [iota0P, Finset.smul_sum, Pi.smul_apply, smul_assoc]

theorem BuAB_mul_aAB_eq_two_F0 (F : FermionIndex) (n : ℕ) (u : I n) (k : F.K) :
    BP F n u * aP F n k = (2 : ℚ) • F0P F n u k := by
  have h := BP_comm_aP F n u k
  unfold F0P
  rw [← h]
  module


theorem iota0_Sof (F : FermionIndex) (n : ℕ) (p q : F.K) : iota0P F n (Sof p q) = S0P F n p q := by
  unfold Sof
  split_ifs with h1 h2
  · erw [iota0_eN]; rfl
  · erw [iota0_neg, iota0_eN]
    change -(S0P F n q p) = S0P F n p q
    unfold S0P
    rw [← smul_neg]
    congr 1
    abel
  · have hpq : p = q := F.key_injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    subst hpq
    rw [iota0_zero]
    unfold S0P
    simp

theorem X0_Lof (F : FermionIndex) (n : ℕ) (u v : I n) : X0P F n (Lof u v) = L0P F n u v := by
  by_cases h : Bmn.IKey u ≤ Bmn.IKey v
  · simp only [Lof, h, ↓reduceDIte]; rfl
  · simp only [Lof, h, ↓reduceDIte]
    change L0P F n v u = L0P F n u v
    unfold L0P
    rw [add_comm]

/-- `X0 (Fof u i) = F0 u i`, a free `rfl` -- `Fof` needs no sorting (`Basis.lean`), unlike
`Lof`, so no bridging work is needed. -/
theorem X0_Fof (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) :
    X0P F n (Fof u i) = F0P F n u i := rfl

/-! ## `scomm`'s graded antisymmetry, and `gsign`'s square -/

theorem gsign_sq (p q : ZMod 2) : gsign p q * gsign p q = 1 := by
  unfold gsign
  split_ifs <;> norm_num

/-- `scomm` is itself graded-antisymmetric, the same law `bracket0Basis_super_skew`
gives `bracket0Basis`. Purely algebraic from `scomm`'s own definition, `gsign_sq` and
`gsign_symm` (`Coboundary.lean`) -- no dependence on `X,Y`'s kind. Used to get the three
reversed kinds (`SL`,`FL`,`FS`) of `base_realization` from the three forward kinds
(`LS`,`LF`,`SF`) for free. -/
theorem scomm_antisymm {F : FermionIndex} {n : ℕ} (X Y : OspBasis F n) (x y : AZero F n) :
    scomm Y X y x = -(gsign (OspN.parity X) (OspN.parity Y)) • scomm X Y x y := by
  unfold scomm
  rw [gsign_symm (OspN.parity Y) (OspN.parity X), smul_sub, smul_smul,
    show -gsign (OspN.parity X) (OspN.parity Y) * gsign (OspN.parity X) (OspN.parity Y) = -1 from by
      rw [neg_mul, gsign_sq]]
  rw [neg_one_smul, neg_smul, sub_neg_eq_add]
  abel

/-! ## Swap lemmas: moving one generator past another, additive form -/

theorem BuAB_swap (F : FermionIndex) (n : ℕ) (u v : I n) :
    BP F n u * BP F n v = BP F n v * BP F n u + J n u v • (1 : AZero F n) := by
  have h : BP F n u * BP F n v - BP F n v * BP F n u - J n u v • (1 : AZero F n) = 0 := by
    rw [BP_comm]; abel
  have h3 : BP F n u * BP F n v
      = (BP F n v * BP F n u + J n u v • (1 : AZero F n))
        + (BP F n u * BP F n v - BP F n v * BP F n u - J n u v • (1 : AZero F n)) := by
    abel
  rw [h3, h, add_zero]

theorem aAB_swap (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aP F n i * aP F n j = F.g i j • (1 : AZero F n) - aP F n j * aP F n i := by
  have h : aP F n i * aP F n j + aP F n j * aP F n i - F.g i j • (1 : AZero F n) = 0 := by
    rw [aP_mul_add_swap]; abel
  have h3 : aP F n i * aP F n j
      = (F.g i j • (1 : AZero F n) - aP F n j * aP F n i)
        + (aP F n i * aP F n j + aP F n j * aP F n i - F.g i j • (1 : AZero F n)) := by
    abel
  rw [h3, h, add_zero]

/-! ## Primitive commutators: `L0`/`S0` against a single generator -/

theorem L0_comm_aAB (F : FermionIndex) (n : ℕ) (u v : I n) (k : F.K) :
    L0P F n u v * aP F n k = aP F n k * L0P F n u v := by
  unfold L0P
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : BP F n u * BP F n v * aP F n k = aP F n k * (BP F n u * BP F n v) := by
    rw [mul_assoc, BP_comm_aP, ← mul_assoc, BP_comm_aP, mul_assoc]
  have h2 : BP F n v * BP F n u * aP F n k = aP F n k * (BP F n v * BP F n u) := by
    rw [mul_assoc, BP_comm_aP, ← mul_assoc, BP_comm_aP, mul_assoc]
  rw [add_mul, mul_add, h1, h2]

theorem S0_comm_BuAB (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) :
    S0P F n i j * BP F n w = BP F n w * S0P F n i j := by
  unfold S0P
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1 : aP F n i * aP F n j * BP F n w = BP F n w * (aP F n i * aP F n j) := by
    rw [mul_assoc, ← BP_comm_aP, ← mul_assoc, ← BP_comm_aP, mul_assoc]
  have h2 : aP F n j * aP F n i * BP F n w = BP F n w * (aP F n j * aP F n i) := by
    rw [mul_assoc, ← BP_comm_aP, ← mul_assoc, ← BP_comm_aP, mul_assoc]
  rw [sub_mul, mul_sub, h1, h2]

/-- **Adjoint action, `L0` against a generator**: `⟦L⁰_{uv}, B_w⟧ = ½(J_{vw}B_u +
J_{uw}B_v)`, a degree-3 computation (not the full `L,L`
degree-4 computation). -/
theorem L0_comm_BuAB (F : FermionIndex) (n : ℕ) (u v w : I n) :
    L0P F n u v * BP F n w - BP F n w * L0P F n u v
      = (1 / 2 : ℚ) • (J n v w • BP F n u + J n u w • BP F n v) := by
  have huvw : BP F n u * BP F n v * BP F n w - BP F n w * (BP F n u * BP F n v)
      = J n u w • BP F n v + J n v w • BP F n u := by
    have step1 : BP F n u * BP F n v * BP F n w
        = BP F n w * (BP F n u * BP F n v) + J n u w • BP F n v + J n v w • BP F n u := by
      rw [mul_assoc, BuAB_swap F n v w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swap F n u w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  have hvuw : BP F n v * BP F n u * BP F n w - BP F n w * (BP F n v * BP F n u)
      = J n v w • BP F n u + J n u w • BP F n v := by
    have step1 : BP F n v * BP F n u * BP F n w
        = BP F n w * (BP F n v * BP F n u) + J n v w • BP F n u + J n u w • BP F n v := by
      rw [mul_assoc, BuAB_swap F n u w, mul_add, ← mul_assoc, mul_smul_comm, mul_one,
        BuAB_swap F n v w, add_mul, smul_mul_assoc, one_mul, mul_assoc]
    rw [step1]; abel
  unfold L0P
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [add_mul, mul_add]
  rw [show BP F n u * BP F n v * BP F n w + BP F n v * BP F n u * BP F n w
        - (BP F n w * (BP F n u * BP F n v) + BP F n w * (BP F n v * BP F n u))
      = (BP F n u * BP F n v * BP F n w - BP F n w * (BP F n u * BP F n v))
        + (BP F n v * BP F n u * BP F n w - BP F n w * (BP F n v * BP F n u))
      from by abel]
  rw [huvw, hvuw]
  module

/-- **Adjoint action, `S0` against a generator**: `⟦S⁰_{ij}, a_k⟧ = g_{jk}a_i −
g_{ik}a_j`, the fermionic (anticommuting) analogue of `L0_comm_BuAB`, using `a`'s
anticommutation (`aAB_swap`) at each swap instead of `B`'s plain commutation. -/
theorem S0_comm_aAB (F : FermionIndex) (n : ℕ) (i j k : F.K) :
    S0P F n i j * aP F n k - aP F n k * S0P F n i j
      = F.g j k • aP F n i - F.g i k • aP F n j := by
  have hikj : aP F n i * aP F n j * aP F n k - aP F n k * (aP F n i * aP F n j)
      = F.g j k • aP F n i - F.g i k • aP F n j := by
    have step1 : aP F n i * aP F n j * aP F n k
        = aP F n k * (aP F n i * aP F n j) + F.g j k • aP F n i - F.g i k • aP F n j := by
      rw [mul_assoc, aAB_swap F n j k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swap F n i k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  have hjik : aP F n j * aP F n i * aP F n k - aP F n k * (aP F n j * aP F n i)
      = F.g i k • aP F n j - F.g j k • aP F n i := by
    have step1 : aP F n j * aP F n i * aP F n k
        = aP F n k * (aP F n j * aP F n i) + F.g i k • aP F n j - F.g j k • aP F n i := by
      rw [mul_assoc, aAB_swap F n i k, mul_sub, ← mul_assoc, mul_smul_comm, mul_one,
        aAB_swap F n j k, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
      abel
    rw [step1]; abel
  unfold S0P
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [sub_mul, mul_sub]
  rw [show aP F n i * aP F n j * aP F n k - aP F n j * aP F n i * aP F n k
        - (aP F n k * (aP F n i * aP F n j) - aP F n k * (aP F n j * aP F n i))
      = (aP F n i * aP F n j * aP F n k - aP F n k * (aP F n i * aP F n j))
        - (aP F n j * aP F n i * aP F n k - aP F n k * (aP F n j * aP F n i))
      from by abel]
  rw [hikj, hjik]
  module

/-! ## From a commutator identity to an explicit sum, generically -/

theorem eq_add_of_sub_eq' {R : Type*} [AddCommGroup R] {a b c : R} (h : a - b = c) :
    a = b + c := by
  have h3 : a = (b + c) + (a - b - c) := by abel
  have h2 : a - b - c = 0 := by rw [h]; abel
  rw [h3, h2, add_zero]

/-! ## Plain-equality forms of the adjoint-action lemmas, and `F0`/`4L0`/`2S0` identities -/

theorem L0_BuAB_eq (F : FermionIndex) (n : ℕ) (u v w : I n) :
    L0P F n u v * BP F n w
      = BP F n w * L0P F n u v
        + (1 / 2 : ℚ) • (J n v w • BP F n u + J n u w • BP F n v) :=
  eq_add_of_sub_eq' (L0_comm_BuAB F n u v w)

theorem S0_aAB_eq (F : FermionIndex) (n : ℕ) (i j k : F.K) :
    S0P F n i j * aP F n k
      = aP F n k * S0P F n i j + (F.g j k • aP F n i - F.g i k • aP F n j) :=
  eq_add_of_sub_eq' (S0_comm_aAB F n i j k)

theorem F0_eq_half_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (u : I n) (k : F.K) :
    F0P F n u k = (1 / 2 : ℚ) • (BP F n u * aP F n k) := by
  rw [BuAB_mul_aAB_eq_two_F0, smul_smul]
  norm_num

theorem BuAB_add_comm_eq_four_L0 (F : FermionIndex) (n : ℕ) (u v : I n) :
    BP F n u * BP F n v + BP F n v * BP F n u = (4 : ℚ) • L0P F n u v := by
  unfold L0P
  rw [smul_smul]
  norm_num

theorem aAB_sub_comm_eq_two_S0 (F : FermionIndex) (n : ℕ) (i j : F.K) :
    aP F n i * aP F n j - aP F n j * aP F n i = (2 : ℚ) • S0P F n i j := by
  unfold S0P
  rw [smul_smul]
  norm_num

/-! ## `L0`/`S0` against a `B*a`, `B*B`, `a*a`-type product, additive form -/

theorem L0_comm_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (u v w : I n) (k : F.K) :
    L0P F n u v * (BP F n w * aP F n k) - BP F n w * aP F n k * L0P F n u v
      = ((1 / 2 : ℚ) • (J n v w • BP F n u + J n u w • BP F n v)) * aP F n k := by
  rw [← mul_assoc, L0_BuAB_eq, add_mul, mul_assoc, L0_comm_aAB, ← mul_assoc]
  abel

theorem S0_comm_BuAB_mul_aAB (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0P F n i j * (BP F n w * aP F n k) - BP F n w * aP F n k * S0P F n i j
      = BP F n w * (F.g j k • aP F n i - F.g i k • aP F n j) := by
  rw [← mul_assoc, S0_comm_BuAB, mul_assoc, S0_aAB_eq, mul_add, ← mul_assoc]
  abel

theorem L0_comm_BuAB_mul_BuAB (F : FermionIndex) (n : ℕ) (u v w z : I n) :
    L0P F n u v * (BP F n w * BP F n z) - BP F n w * BP F n z * L0P F n u v
      = ((1 / 2 : ℚ) • (J n v w • BP F n u + J n u w • BP F n v)) * BP F n z
        + BP F n w * ((1 / 2 : ℚ) • (J n v z • BP F n u + J n u z • BP F n v)) := by
  rw [← mul_assoc, L0_BuAB_eq, add_mul, mul_assoc, L0_BuAB_eq, mul_add,
    mul_assoc (BP F n w) (BP F n z) (L0P F n u v)]
  abel

theorem S0_comm_aAB_mul_aAB (F : FermionIndex) (n : ℕ) (i j p q : F.K) :
    S0P F n i j * (aP F n p * aP F n q) - aP F n p * aP F n q * S0P F n i j
      = (F.g j p • aP F n i - F.g i p • aP F n j) * aP F n q
        + aP F n p * (F.g j q • aP F n i - F.g i q • aP F n j) := by
  rw [← mul_assoc, S0_aAB_eq, add_mul, mul_assoc, S0_aAB_eq, mul_add,
    mul_assoc (aP F n p) (aP F n q) (S0P F n i j)]
  abel

/-! ## The six forward kind-pairs of base realization -/

theorem base_LS (F : FermionIndex) (n : ℕ) (u v : I n) (i j : F.K) :
    L0P F n u v * S0P F n i j - S0P F n i j * L0P F n u v = 0 := by
  unfold S0P
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul]
  have h1 : L0P F n u v * (aP F n i * aP F n j) = aP F n i * aP F n j * L0P F n u v := by
    rw [← mul_assoc, L0_comm_aAB, mul_assoc, L0_comm_aAB, ← mul_assoc]
  have h2 : L0P F n u v * (aP F n j * aP F n i) = aP F n j * aP F n i * L0P F n u v := by
    rw [← mul_assoc, L0_comm_aAB, mul_assoc, L0_comm_aAB, ← mul_assoc]
  rw [h1, h2, sub_self, smul_zero]

theorem base_LF (F : FermionIndex) (n : ℕ) (u v w : I n) (k : F.K) :
    L0P F n u v * F0P F n w k - F0P F n w k * L0P F n u v
      = (1 / 2 : ℚ) • (J n v w • F0P F n u k + J n u w • F0P F n v k) := by
  rw [F0_eq_half_BuAB_mul_aAB, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    L0_comm_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB]
  simp only [smul_mul_assoc, add_mul]
  module

theorem base_SF (F : FermionIndex) (n : ℕ) (i j : F.K) (w : I n) (k : F.K) :
    S0P F n i j * F0P F n w k - F0P F n w k * S0P F n i j
      = F.g j k • F0P F n w i - F.g i k • F0P F n w j := by
  rw [F0_eq_half_BuAB_mul_aAB, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    S0_comm_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB]
  simp only [mul_sub, mul_smul_comm]
  module

theorem base_LL (F : FermionIndex) (n : ℕ) (u v w z : I n) :
    L0P F n u v * L0P F n w z - L0P F n w z * L0P F n u v
      = (1 / 2 : ℚ) • (J n v w • L0P F n u z + J n u w • L0P F n v z
          + J n v z • L0P F n u w + J n u z • L0P F n v w) := by
  have hLwz : L0P F n w z
      = (1 / 4 : ℚ) • (BP F n w * BP F n z + BP F n z * BP F n w) := rfl
  rw [hLwz, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_add, add_mul,
    show L0P F n u v * (BP F n w * BP F n z) + L0P F n u v * (BP F n z * BP F n w)
        - (BP F n w * BP F n z * L0P F n u v + BP F n z * BP F n w * L0P F n u v)
      = (L0P F n u v * (BP F n w * BP F n z) - BP F n w * BP F n z * L0P F n u v)
        + (L0P F n u v * (BP F n z * BP F n w) - BP F n z * BP F n w * L0P F n u v)
      from by abel,
    L0_comm_BuAB_mul_BuAB, L0_comm_BuAB_mul_BuAB]
  have hcomb :
      ((1/2:ℚ) • (J n v w • BP F n u + J n u w • BP F n v)) * BP F n z
        + BP F n w * ((1/2:ℚ) • (J n v z • BP F n u + J n u z • BP F n v))
        + (((1/2:ℚ) • (J n v z • BP F n u + J n u z • BP F n v)) * BP F n w
          + BP F n z * ((1/2:ℚ) • (J n v w • BP F n u + J n u w • BP F n v)))
      = (1/2:ℚ) • (J n v w • (BP F n u * BP F n z + BP F n z * BP F n u)
          + J n u w • (BP F n v * BP F n z + BP F n z * BP F n v)
          + J n v z • (BP F n u * BP F n w + BP F n w * BP F n u)
          + J n u z • (BP F n v * BP F n w + BP F n w * BP F n v)) := by
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add]
    abel
  rw [hcomb, BuAB_add_comm_eq_four_L0, BuAB_add_comm_eq_four_L0,
    BuAB_add_comm_eq_four_L0, BuAB_add_comm_eq_four_L0]
  module

theorem base_SS (F : FermionIndex) (n : ℕ) (i j k l : F.K) :
    S0P F n i j * S0P F n k l - S0P F n k l * S0P F n i j
      = F.g j k • S0P F n i l - F.g i k • S0P F n j l
        - F.g j l • S0P F n i k + F.g i l • S0P F n j k := by
  have hSkl : S0P F n k l
      = (1 / 2 : ℚ) • (aP F n k * aP F n l - aP F n l * aP F n k) := rfl
  rw [hSkl, mul_smul_comm, smul_mul_assoc, ← smul_sub, mul_sub, sub_mul,
    show S0P F n i j * (aP F n k * aP F n l) - S0P F n i j * (aP F n l * aP F n k)
        - (aP F n k * aP F n l * S0P F n i j - aP F n l * aP F n k * S0P F n i j)
      = (S0P F n i j * (aP F n k * aP F n l) - aP F n k * aP F n l * S0P F n i j)
        - (S0P F n i j * (aP F n l * aP F n k) - aP F n l * aP F n k * S0P F n i j)
      from by abel,
    S0_comm_aAB_mul_aAB, S0_comm_aAB_mul_aAB]
  have hcomb :
      (F.g j k • aP F n i - F.g i k • aP F n j) * aP F n l
        + aP F n k * (F.g j l • aP F n i - F.g i l • aP F n j)
        - ((F.g j l • aP F n i - F.g i l • aP F n j) * aP F n k
          + aP F n l * (F.g j k • aP F n i - F.g i k • aP F n j))
      = F.g j k • (aP F n i * aP F n l - aP F n l * aP F n i)
        - F.g i k • (aP F n j * aP F n l - aP F n l * aP F n j)
        - F.g j l • (aP F n i * aP F n k - aP F n k * aP F n i)
        + F.g i l • (aP F n j * aP F n k - aP F n k * aP F n j) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  rw [hcomb, aAB_sub_comm_eq_two_S0, aAB_sub_comm_eq_two_S0,
    aAB_sub_comm_eq_two_S0, aAB_sub_comm_eq_two_S0]
  module

/-- A pure-ring identity (no commutativity of `X,Y,P,Q` needed): `X*P+Y*Q` is the
"half-sum-plus-half-difference" combination `½[(X+Y)(P+Q)+(X-Y)(P-Q)]`. Used by
`base_FF` to turn `BuAB u*BuAB v` and `aAB i*aAB j`'s SEPARATE sum/difference facts
into the anticommutator `F0(u,i)*F0(v,j)+F0(v,j)*F0(u,i)` directly, without solving
for `BuAB u*BuAB v` or `aAB i*aAB j` individually. -/
theorem mul_add_mul_eq_half (F : FermionIndex) (n : ℕ) (X Y P Q : AZero F n) :
    X * P + Y * Q = (1 / 2 : ℚ) • ((X + Y) * (P + Q) + (X - Y) * (P - Q)) := by
  have expand : (X + Y) * (P + Q) + (X - Y) * (P - Q)
      = (X * P + Y * Q) + (X * P + Y * Q) := by
    rw [add_mul, mul_add, mul_add, sub_mul, mul_sub, mul_sub]
    abel
  rw [expand, ← two_smul ℚ, smul_smul]
  norm_num

theorem base_FF (F : FermionIndex) (n : ℕ) (u : I n) (i : F.K) (v : I n) (j : F.K) :
    F0P F n u i * F0P F n v j + F0P F n v j * F0P F n u i
      = (1 / 4 : ℚ) • (J n u v • S0P F n i j) + (1 / 2 : ℚ) • (F.g i j • L0P F n u v) := by
  rw [F0_eq_half_BuAB_mul_aAB, F0_eq_half_BuAB_mul_aAB,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmove1 : BP F n u * aP F n i * (BP F n v * aP F n j)
      = BP F n u * BP F n v * (aP F n i * aP F n j) := by
    rw [mul_assoc, ← mul_assoc (aP F n i), ← BP_comm_aP, mul_assoc, ← mul_assoc]
  have hmove2 : BP F n v * aP F n j * (BP F n u * aP F n i)
      = BP F n v * BP F n u * (aP F n j * aP F n i) := by
    rw [mul_assoc, ← mul_assoc (aP F n j), ← BP_comm_aP, mul_assoc, ← mul_assoc]
  rw [hmove1, hmove2,
    show (1 / 2 * (1 / 2) : ℚ)
          • (BP F n u * BP F n v * (aP F n i * aP F n j))
        + (1 / 2 * (1 / 2) : ℚ)
          • (BP F n v * BP F n u * (aP F n j * aP F n i))
      = (1 / 4 : ℚ) • (BP F n u * BP F n v * (aP F n i * aP F n j)
          + BP F n v * BP F n u * (aP F n j * aP F n i))
      from by rw [show (1 / 2 * (1 / 2) : ℚ) = 1 / 4 from by norm_num, ← smul_add],
    mul_add_mul_eq_half F n (BP F n u * BP F n v) (BP F n v * BP F n u)
      (aP F n i * aP F n j) (aP F n j * aP F n i),
    BuAB_add_comm_eq_four_L0, BP_comm, aP_mul_add_swap, aAB_sub_comm_eq_two_S0]
  simp only [smul_smul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
  module

/-- **Lemma 3.2 (the base bracket)**, in the presented `A_0`: the supercommutator of two lifts is
the lift of `[·,·]_0`. -/
theorem base_realization (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (X0P F n X) (X0P F n Y) = iota0P F n (bracket0Basis X Y) := by
  match X, Y with
  | .inl ⟨(u, v), _⟩, .inl ⟨(w, z), _⟩ =>
    change L0P F n u v * L0P F n w z - gsign 0 0 • (L0P F n w z * L0P F n u v)
        = iota0P F n (bracketLL u v w z)
    rw [gsign_00, one_smul, base_LL]
    unfold bracketLL
    rw [iota0_add, iota0_add, iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_smul_rat,
      iota0_smul_rat, iota0_eN, iota0_eN, iota0_eN, iota0_eN, X0_Lof, X0_Lof, X0_Lof, X0_Lof,
      smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  | .inl ⟨(u, v), _⟩, .inr (.inl ⟨(i, j), _⟩) =>
    change L0P F n u v * S0P F n i j - gsign 0 0 • (S0P F n i j * L0P F n u v)
        = iota0P F n (0 : OspMod F n)
    rw [gsign_00, one_smul, base_LS, iota0_zero]
  | .inl ⟨(u, v), _⟩, .inr (.inr (w, i)) =>
    change L0P F n u v * F0P F n w i - gsign 0 1 • (F0P F n w i * L0P F n u v)
        = iota0P F n (bracketLF u v w i)
    rw [gsign_01, one_smul, base_LF]
    unfold bracketLF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof,
      smul_add, smul_smul, smul_smul]
  | .inr (.inl ⟨(i, j), _⟩), .inl ⟨(u, v), _⟩ =>
    change S0P F n i j * L0P F n u v - gsign 0 0 • (L0P F n u v * S0P F n i j)
        = iota0P F n (0 : OspMod F n)
    rw [gsign_00, one_smul,
      show S0P F n i j * L0P F n u v - L0P F n u v * S0P F n i j
          = -(L0P F n u v * S0P F n i j - S0P F n i j * L0P F n u v) from by abel,
      base_LS, neg_zero, iota0_zero]
  | .inr (.inl ⟨(i, j), _⟩), .inr (.inl ⟨(k, l), _⟩) =>
    change S0P F n i j * S0P F n k l - gsign 0 0 • (S0P F n k l * S0P F n i j)
        = iota0P F n (bracketSS i j k l)
    rw [gsign_00, one_smul, base_SS]
    unfold bracketSS
    rw [iota0_add, iota0_sub, iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_smul_rat,
      iota0_smul_rat, iota0_Sof, iota0_Sof, iota0_Sof, iota0_Sof]
  | .inr (.inl ⟨(j, k), _⟩), .inr (.inr (w, i)) =>
    change S0P F n j k * F0P F n w i - gsign 0 1 • (F0P F n w i * S0P F n j k)
        = iota0P F n (bracketSF j k w i)
    rw [gsign_01, one_smul, base_SF]
    unfold bracketSF
    rw [iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof]
  | .inr (.inr (w, i)), .inl ⟨(u, v), _⟩ =>
    change F0P F n w i * L0P F n u v - gsign 1 0 • (L0P F n u v * F0P F n w i)
        = iota0P F n (-bracketLF u v w i)
    rw [gsign_10, one_smul,
      show F0P F n w i * L0P F n u v - L0P F n u v * F0P F n w i
          = -(L0P F n u v * F0P F n w i - F0P F n w i * L0P F n u v) from by abel,
      base_LF, iota0_neg]
    unfold bracketLF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof,
      smul_add, smul_smul, smul_smul]
  | .inr (.inr (w, i)), .inr (.inl ⟨(j, k), _⟩) =>
    change F0P F n w i * S0P F n j k - gsign 1 0 • (S0P F n j k * F0P F n w i)
        = iota0P F n (-bracketSF j k w i)
    rw [gsign_10, one_smul,
      show F0P F n w i * S0P F n j k - S0P F n j k * F0P F n w i
          = -(S0P F n j k * F0P F n w i - F0P F n w i * S0P F n j k) from by abel,
      base_SF, iota0_neg]
    unfold bracketSF
    rw [iota0_sub, iota0_smul_rat, iota0_smul_rat, iota0_eN, iota0_eN, X0_Fof, X0_Fof]
  | .inr (.inr (u, i)), .inr (.inr (v, j)) =>
    change F0P F n u i * F0P F n v j - gsign 1 1 • (F0P F n v j * F0P F n u i)
        = iota0P F n (bracketFF u i v j)
    rw [gsign_11, neg_smul, one_smul, sub_neg_eq_add, base_FF]
    unfold bracketFF
    rw [iota0_add, iota0_smul_rat, iota0_smul_rat, iota0_Sof, iota0_eN, X0_Lof, smul_smul,
      smul_smul]


end Presented
end OspN
end OspOddDeformations
