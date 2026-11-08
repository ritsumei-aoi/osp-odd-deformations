import OspOddDeformations.OspN.Multi.Statements
import OspOddDeformations.OspN.Multi.GRing
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Div

/-!
# The core of `Θ = (𝕀+ΩJ)^{1/2}`, generic in `Ω`

`ThetaSeries.lean` states Thm 5.1's `Θ` and its identity for `OmegaR`. Here the same construction is
made for any antisymmetric family `Om` of entries of `κ`-degree `2`, with matrices over the centre
`Z` of `GRing` (even entries are central), so that Mathlib's commutative matrix algebra applies.
-/

namespace OspOddDeformations
namespace OspN
namespace Multi

open Bmn (I J)
open scoped Matrix

set_option backward.isDefEq.respectTransparency.types false
-- `OspBasis` is a plain `def`, as in `ThetaStarBracket.lean` and `VChiBracket.lean`

variable {F : FermionIndex} {n r : ℕ}

/-- `Q = ΩJ` for a general `Om`. -/
noncomputable def QMatG (Om : I n → I n → GR F n r) (u w : I n) : GR F n r :=
  ∑ z : I n, gmul (Om u z) (JR z w)

/-- `Q^k` for a general `Om`. -/
noncomputable def QPowG (Om : I n → I n → GR F n r) : ℕ → I n → I n → GR F n r
  | 0 => fun u w => if u = w then gone else 0
  | k + 1 => fun u w => ∑ z : I n, gmul (QPowG Om k u z) (QMatG Om z w)

/-- `Σ_{k ≤ ⌊r/2⌋} C(1/2,k) Q^k` for a general `Om`. -/
noncomputable def thetaG (Om : I n → I n → GR F n r) (u w : I n) : GR F n r :=
  ∑ k ∈ Finset.range (r / 2 + 1), Ring.choose (1 / 2 : ℚ) k • QPowG Om k u w

theorem HasCard_QMatG (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u w : I n) :
    HasCard 2 (QMatG Om u w) := by
  unfold QMatG
  exact HasCard.sum _ fun z _ => by simpa using (hOm u z).gmul (HasCard_JR z w)

theorem HasCard_QPowG (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (k : ℕ)
    (u w : I n) : HasCard (2 * k) (QPowG Om k u w) := by
  induction k generalizing u w with
  | zero =>
    simp only [QPowG, Nat.mul_zero]
    split_ifs
    · exact HasCard_gone
    · exact HasCard.zero _
  | succ k ih =>
    simp only [QPowG]
    exact HasCard.sum _ fun z _ => by
      have := (ih u z).gmul (HasCard_QMatG Om hOm z w)
      rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at this

theorem QPowG_eq_zero (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) {k : ℕ}
    (hk : r < 2 * k) (u w : I n) : QPowG Om k u w = 0 :=
  HasCard.of_lt hk (HasCard_QPowG Om hOm k u w)

/-! ## Matrices over the centre -/

/-- The centre of `GRing`; even elements lie in it. -/
noncomputable abbrev ZC (F : FermionIndex) (n r : ℕ) := Subalgebra.center ℚ (GRing F n r)

theorem even_mem_center {a : GR F n r} (ha : IsEvenGR a) :
    (GRing.ofGR a : GRing F n r) ∈ Subalgebra.center ℚ (GRing F n r) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  exact (GRing.mul_comm_of_even (a := GRing.ofGR a) ha b).symm

theorem isEven_JR (u v : I n) : IsEvenGR (JR (F := F) (r := r) u v) :=
  (HasCard_JR u v).isEven (by norm_num)

/-- `Ω` as a matrix over the centre. -/
noncomputable def OmZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    Matrix (I n) (I n) (ZC F n r) :=
  fun u v => ⟨GRing.ofGR (Om u v), even_mem_center ((hOm u v).isEven (by norm_num))⟩

/-- `J` as a matrix over the centre. -/
noncomputable def JZ : Matrix (I n) (I n) (ZC F n r) :=
  fun u v => ⟨GRing.ofGR (JR u v), even_mem_center (isEven_JR u v)⟩

theorem val_mul_apply (A B : Matrix (I n) (I n) (ZC F n r)) (u w : I n) :
    ((A * B) u w).val = ∑ z : I n, (A u z).val * (B z w).val := by
  rw [Matrix.mul_apply]
  exact map_sum (Subalgebra.val _) _ _

theorem toGR_val_mul_apply (A B : Matrix (I n) (I n) (ZC F n r)) (u w : I n) :
    GRing.toGR ((A * B) u w).val =
      ∑ z : I n, gmul (GRing.toGR (A u z).val) (GRing.toGR (B z w).val) := by
  rw [val_mul_apply]; rfl

/-- `Q = ΩJ` over the centre. -/
noncomputable def QZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    Matrix (I n) (I n) (ZC F n r) := OmZ Om hOm * JZ

theorem toGR_QZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u w : I n) :
    GRing.toGR (QZ Om hOm u w).val = QMatG Om u w := by
  rw [QZ, toGR_val_mul_apply]; rfl

theorem toGR_QZ_pow (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (k : ℕ)
    (u w : I n) : GRing.toGR ((QZ Om hOm ^ k) u w).val = QPowG Om k u w := by
  induction k generalizing u w with
  | zero =>
    simp only [pow_zero, QPowG, Matrix.one_apply]
    split_ifs <;> rfl
  | succ k ih =>
    rw [pow_succ, toGR_val_mul_apply]
    simp only [QPowG]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ih, toGR_QZ]

theorem QZ_pow_eq_zero (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) {m : ℕ}
    (hm : r < 2 * m) : QZ Om hOm ^ m = 0 := by
  ext u w
  rw [GRing.ext_iff']
  intro T
  have := congrFun (toGR_QZ_pow Om hOm m u w) T
  rw [QPowG_eq_zero Om hOm hm] at this
  exact this

theorem gmul_JR_JR (u w : I n) :
    ∑ z : I n, gmul (JR (F := F) (r := r) u z) (JR z w) =
      (MvPolynomial.C (if u = w then (-1 : ℚ) else 0) : PmnR F n r) • gone := by
  calc ∑ z : I n, gmul (JR (F := F) (r := r) u z) (JR z w)
      = ∑ z : I n, (MvPolynomial.C (J n u z * J n z w) : PmnR F n r) • gone :=
        Finset.sum_congr rfl fun z _ => by
          rw [gmul_JR_left, JR_eq, smul_smul, map_mul]
    _ = (MvPolynomial.C (∑ z : I n, J n u z * J n z w) : PmnR F n r) • gone := by
        rw [map_sum, Finset.sum_smul]
    _ = _ := by rw [J_mul_J]

theorem JZ_mul_JZ : (JZ : Matrix (I n) (I n) (ZC F n r)) * JZ = -1 := by
  ext u w
  rw [GRing.ext_iff']
  intro T
  rw [toGR_val_mul_apply]
  change (∑ z : I n, gmul (JR u z) (JR z w)) T = _
  rw [gmul_JR_JR]
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : u = w
  · simp only [h, ite_true]
    rw [Subalgebra.coe_neg, Subalgebra.coe_one]
    change (MvPolynomial.C (-1) • gone) T = - gone T
    simp
  · simp only [h, ite_false, neg_zero]
    rw [Subalgebra.coe_zero]
    change (MvPolynomial.C 0 • gone) T = 0
    simp

theorem JR_antisymm (u v : I n) : JR (F := F) (r := r) v u = - JR u v := by
  rw [JR_eq, JR_eq, Bmn.J_antisymm v u, map_neg, neg_smul]

theorem JZ_transpose : (JZ : Matrix (I n) (I n) (ZC F n r))ᵀ = -JZ := by
  ext u v
  change GRing.ofGR (JR v u) = - GRing.ofGR (JR u v)
  rw [JR_antisymm]; rfl

theorem OmZ_transpose (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) : (OmZ Om hOm)ᵀ = -OmZ Om hOm := by
  ext u v
  change GRing.ofGR (Om v u) = - GRing.ofGR (Om u v)
  rw [hA]; rfl

theorem mmul_neg (A B : Matrix (I n) (I n) (ZC F n r)) : A * -B = -(A * B) := Matrix.mul_neg A B
theorem mneg_mul (A B : Matrix (I n) (I n) (ZC F n r)) : -A * B = -(A * B) := Matrix.neg_mul A B
theorem mneg_neg (A : Matrix (I n) (I n) (ZC F n r)) : - -A = A := neg_neg A
theorem mmul_one (A : Matrix (I n) (I n) (ZC F n r)) : A * 1 = A := Matrix.mul_one A
theorem mone_mul (A : Matrix (I n) (I n) (ZC F n r)) : 1 * A = A := Matrix.one_mul A

theorem QZ_mul_JZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    QZ Om hOm * JZ = -OmZ Om hOm := by
  rw [QZ, Matrix.mul_assoc, JZ_mul_JZ, mmul_neg, mmul_one]

theorem JZ_mul_QZ_transpose (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) : JZ * (QZ Om hOm)ᵀ = QZ Om hOm * JZ := by
  rw [QZ_mul_JZ, QZ, Matrix.transpose_mul, JZ_transpose, OmZ_transpose Om hOm hA,
    ← Matrix.mul_assoc, mmul_neg JZ JZ, mmul_neg, mneg_mul, mneg_neg, JZ_mul_JZ, mneg_mul,
    mone_mul]


theorem JZ_mul_QZt_pow (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) (k : ℕ) :
    JZ * ((QZ Om hOm)ᵀ) ^ k = QZ Om hOm ^ k * JZ := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mmul_one, mone_mul]
  | succ k ih =>
    rw [pow_succ' (QZ Om hOm)ᵀ, pow_succ' (QZ Om hOm), ← Matrix.mul_assoc,
      JZ_mul_QZ_transpose Om hOm hA, Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- `Θ = Σ_{k ≤ ⌊r/2⌋} C(1/2,k) Q^k`, as a matrix over the centre. -/
noncomputable def ThZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    Matrix (I n) (I n) (ZC F n r) :=
  ∑ k ∈ Finset.range (r / 2 + 1), Ring.choose (1 / 2 : ℚ) k • QZ Om hOm ^ k

theorem toGR_ThZ (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u w : I n) :
    GRing.toGR (ThZ Om hOm u w).val = thetaG Om u w := by
  unfold ThZ thetaG
  rw [Matrix.sum_apply]
  have : ∀ (s : Finset ℕ) (f : ℕ → ZC F n r),
      GRing.toGR (∑ k ∈ s, f k).val = ∑ k ∈ s, GRing.toGR (f k).val := by
    intro s f
    induction s using Finset.induction with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, ← toGR_QZ_pow Om hOm k u w]
  rfl

theorem JZ_mul_ThZt (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) : JZ * (ThZ Om hOm)ᵀ = ThZ Om hOm * JZ := by
  unfold ThZ
  rw [Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.transpose_pow, JZ_mul_QZt_pow Om hOm hA,
    Matrix.smul_mul]

open Polynomial in
/-- The truncated series `p = Σ_{k<m} C(1/2,k) X^k`; `p² ≡ 1 + X` mod `X^m` (Chu–Vandermonde). -/
noncomputable def sqrtPoly (m : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range m, C (Ring.choose (1 / 2 : ℚ) k) * X ^ k

open Polynomial in
theorem sqrtPoly_coeff (m i : ℕ) :
    (sqrtPoly m).coeff i = if i < m then Ring.choose (1 / 2 : ℚ) i else 0 := by
  unfold sqrtPoly
  rw [finsetSum_coeff]
  simp [coeff_C_mul, coeff_X_pow]

open Polynomial in
theorem sqrtPoly_sq_dvd (m : ℕ) : (X : ℚ[X]) ^ m ∣ sqrtPoly m * sqrtPoly m - (1 + X) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub, coeff_mul]
  have h1 : ∑ x ∈ Finset.antidiagonal d, (sqrtPoly m).coeff x.1 * (sqrtPoly m).coeff x.2
      = Ring.choose (1 : ℚ) d := by
    have := Ring.add_choose_eq (r := (1 / 2 : ℚ)) (s := (1 / 2 : ℚ)) d (Commute.refl _)
    rw [show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num] at this
    rw [this]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_antidiagonal.mp hx
    rw [sqrtPoly_coeff, sqrtPoly_coeff]
    simp only [show x.1 < m from by omega, show x.2 < m from by omega, ite_true]
  rw [h1, sub_eq_zero]
  have h2 : Ring.choose (1 : ℚ) d = ((Nat.choose 1 d : ℕ) : ℚ) := by
    have := Ring.choose_natCast (R := ℚ) 1 d
    simpa using this
  rw [h2]
  rcases d with _ | _ | d
  · simp [coeff_one, coeff_X]
  · simp [coeff_one, coeff_X]
  · rw [Nat.choose_eq_zero_of_lt (by omega : 1 < d + 2)]
    simp [coeff_one, coeff_X]

theorem ThZ_eq_aeval (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    ThZ Om hOm = Polynomial.aeval (QZ Om hOm) (sqrtPoly (r / 2 + 1)) := by
  unfold ThZ sqrtPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Algebra.smul_def]

theorem ThZ_mul_self (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    ThZ Om hOm * ThZ Om hOm = 1 + QZ Om hOm := by
  obtain ⟨g, hg⟩ := sqrtPoly_sq_dvd (r / 2 + 1)
  have hp : sqrtPoly (r / 2 + 1) * sqrtPoly (r / 2 + 1) =
      (1 + Polynomial.X) + Polynomial.X ^ (r / 2 + 1) * g := by
    rw [← hg]; ring
  rw [ThZ_eq_aeval, ← map_mul, hp, map_add, map_mul, map_pow, Polynomial.aeval_X,
    QZ_pow_eq_zero Om hOm (by omega : r < 2 * (r / 2 + 1))]
  simp

theorem thetaG_even (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u w : I n) :
    IsEvenGR (thetaG Om u w) := by
  intro T hT
  unfold thetaG
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h := HasCard_QPowG Om hOm k u w T (fun hc => by omega)
  simp [h]

theorem thetaG_empty (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u w : I n) :
    thetaG Om u w ∅ = if u = w then 1 else 0 := by
  unfold thetaG
  rw [Finset.sum_apply, Finset.sum_eq_single 0]
  · simp only [QPowG, Ring.choose_zero_right, one_smul]
    split_ifs <;> simp [gone]
  · intro k _ hk
    have h := HasCard_QPowG Om hOm k u w ∅ (by simp; omega)
    simp [h]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `ΘJΘᵀ` over the centre. -/
noncomputable def ThJTh (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) :
    Matrix (I n) (I n) (ZC F n r) := ThZ Om hOm * (JZ * (ThZ Om hOm)ᵀ)

theorem thetaJthetaT_eq (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v)) (u v : I n) :
    thetaJthetaT (thetaG Om) u v = GRing.toGR (ThJTh Om hOm u v).val := by
  unfold ThJTh
  rw [toGR_val_mul_apply]
  unfold thetaJthetaT
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [toGR_ThZ, toGR_val_mul_apply, gmul_sum_right]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e : GRing.toGR ((ThZ Om hOm)ᵀ z v).val = thetaG Om v z := toGR_ThZ Om hOm v z
  rw [e]
  rfl

theorem ThJTh_eq (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) : ThJTh Om hOm = JZ - OmZ Om hOm := by
  unfold ThJTh
  rw [JZ_mul_ThZt Om hOm hA, ← Matrix.mul_assoc, ThZ_mul_self, add_mul, mone_mul, QZ_mul_JZ]
  exact (sub_eq_add_neg _ _).symm

theorem thetaG_spec (Om : I n → I n → GR F n r) (hOm : ∀ u v, HasCard 2 (Om u v))
    (hA : ∀ u v, Om v u = -Om u v) :
    (∀ u w, IsEvenGR (thetaG Om u w)) ∧
    (∀ u w, thetaG Om u w ∅ = if u = w then 1 else 0) ∧
    (∀ u v, thetaJthetaT (thetaG Om) u v = JR u v - Om u v) := by
  refine ⟨thetaG_even Om hOm, thetaG_empty Om hOm, fun u v => ?_⟩
  rw [thetaJthetaT_eq Om hOm, ThJTh_eq Om hOm hA]
  rfl

end Multi
end OspN
end OspOddDeformations

