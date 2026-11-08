import OspOddDeformations.OspN.Presented.LiftChange

/-!
# Thm 4.2 (recovery) and Thm 4.3 (uniqueness) in `A_β`, and `[·,·]_β` defined by `ι_β`

First, in `A_0`: the supercommutator of `Φ(X̂) = X^0 + κ ι_0(h̃X)` is computed as in the realization
(`recovery` in `SourceTensor.lean`, transcribed: `scomm_XhatP`). Then, since `Φ` is an isomorphism
(Lemma 3.1) carrying the lifts of `A_β` to these (Prop 4.1), the identity holds in `A_β` itself:
**Thm 4.2** (`recovery`). **Thm 4.3** (`recovery_unique`) follows with Prop 3.3 for the presented
`A_0`.
`ι_β` is injective on `𝔤_R` (`iotaRP_beta_injective`), so the supercommutator of two lifts defines
`[X,Y]_β ∈ 𝔤_R` uniquely, and it is `[X,Y]_0 + κΓ_β(X,Y)` (`bracketBeta_unique`).
-/

namespace OspOddDeformations
namespace OspN
namespace Presented

open Bmn (I J)

/-- `ι_0(x) + κ ι_0(h̃x)`, the image under `Φ` of `ι_β x` (Prop 4.1). -/
noncomputable def iotaBP (F : FermionIndex) (n : ℕ) (x : OspMod F n) : AZero F n :=
  iota0P F n x + κP F n * iota0P F n (hTilde x)

/-! ## The relations with `κ` and with coefficients, in `A_0` -/

theorem κP_sq (F : FermionIndex) (n : ℕ) : κP F n * κP F n = 0 := κ_mul_κ

theorem κP_comm_BP (F : FermionIndex) (n : ℕ) (u : I n) :
    κP F n * BP F n u = gsign 1 0 • (BP F n u * κP F n) := by
  rw [gsign_10, one_smul]; exact κ_mul_b u

theorem κP_comm_aP (F : FermionIndex) (n : ℕ) (i : F.K) :
    κP F n * aP F n i = gsign 1 1 • (aP F n i * κP F n) := by
  rw [gsign_11, neg_one_smul]; exact κ_mul_a i

theorem iota0P_smul_coefP (F : FermionIndex) (n : ℕ) (c : Pmn F n) (x : OspMod F n) :
    iota0P F n (c • x) = coefP F n c * iota0P F n x := iota0P_smul F n c x

theorem iota0P_smul_eN_coefP (F : FermionIndex) (n : ℕ) (c : Pmn F n) (X : OspBasis F n) :
    iota0P F n (c • eN X) = coefP F n c * X0P F n X := iota0P_smul_eN F n c X

theorem coefP_zero (F : FermionIndex) (n : ℕ) : coefP F n 0 = 0 := map_zero _

theorem coefP_comm_BP (F : FermionIndex) (n : ℕ) (c : Pmn F n) (u : I n) :
    coefP F n c * BP F n u = BP F n u * coefP F n c := Algebra.commutes _ _

theorem coefP_comm_aP (F : FermionIndex) (n : ℕ) (c : Pmn F n) (i : F.K) :
    coefP F n c * aP F n i = aP F n i * coefP F n c := Algebra.commutes _ _

theorem κP_comm_coefP (F : FermionIndex) (n : ℕ) (c : Pmn F n) :
    κP F n * coefP F n c = coefP F n c * κP F n := (Algebra.commutes _ _).symm

theorem gsign_one_add (d1 d2 : ZMod 2) : gsign 1 (d1 + d2) = gsign 1 d1 * gsign 1 d2 := by
  have h : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases h d1 with rfl | rfl <;> rcases h d2 with rfl | rfl <;>
    simp only [show (0 : ZMod 2) + 0 = 0 from rfl, show (0 : ZMod 2) + 1 = 1 from rfl,
      show (1 : ZMod 2) + 0 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl] <;>
    norm_num [gsign_00, gsign_01, gsign_10, gsign_11]

/-- The graded-commutation rule against `κP` is multiplicative: if `x` and `y` each
graded-commute with `κP` at degrees `dx`/`dy`, so does `x*y`, at degree `dx+dy`. -/
theorem κP_comm_mul {F : FermionIndex} {n : ℕ} (x y : AZero F n) (dx dy : ZMod 2)
    (hx : κP F n * x = gsign 1 dx • (x * κP F n))
    (hy : κP F n * y = gsign 1 dy • (y * κP F n)) :
    κP F n * (x * y) = gsign 1 (dx + dy) • (x * y * κP F n) := by
  rw [gsign_one_add, ← mul_assoc, hx, smul_mul_assoc, mul_assoc, hy, mul_smul_comm, smul_smul,
    mul_assoc]

/-- Same, for a sum of two terms at the same degree. -/
theorem κP_comm_add {F : FermionIndex} {n : ℕ} (x y : AZero F n) (d : ZMod 2)
    (hx : κP F n * x = gsign 1 d • (x * κP F n))
    (hy : κP F n * y = gsign 1 d • (y * κP F n)) :
    κP F n * (x + y) = gsign 1 d • ((x + y) * κP F n) := by
  rw [mul_add, hx, hy, add_mul, smul_add]

/-- Same, for a `ℚ`-scalar multiple. -/
theorem κP_comm_smul {F : FermionIndex} {n : ℕ} (c : ℚ) (x : AZero F n) (d : ZMod 2)
    (hx : κP F n * x = gsign 1 d • (x * κP F n)) :
    κP F n * (c • x) = gsign 1 d • ((c • x) * κP F n) := by
  rw [mul_smul_comm, hx, smul_comm, ← smul_mul_assoc]

/-- `X0 X` graded-commutes with `κ`, at
degree `OspN.parity X` -- proved by cases on `X`'s kind, unfolding `L0`/`S0`/`F0` into
`BP`/`aP` products and using multiplicativity. -/
theorem κP_comm_X0 (F : FermionIndex) (n : ℕ) (X : OspBasis F n) :
    κP F n * X0P F n X = gsign 1 (OspN.parity X) • (X0P F n X * κP F n) := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    change κP F n * L0P F n u v = gsign 1 0 • (L0P F n u v * κP F n)
    unfold L0P
    refine κP_comm_smul _ _ 0 ?_
    have h1 := κP_comm_mul (BP F n u) (BP F n v) 0 0
      (κP_comm_BP F n u) (κP_comm_BP F n v)
    have h2 := κP_comm_mul (BP F n v) (BP F n u) 0 0
      (κP_comm_BP F n v) (κP_comm_BP F n u)
    simpa using κP_comm_add _ _ 0 h1 h2
  | .inr (.inl ⟨(i, j), _⟩) =>
    change κP F n * S0P F n i j = gsign 1 0 • (S0P F n i j * κP F n)
    unfold S0P
    refine κP_comm_smul _ _ 0 ?_
    have h1 := κP_comm_mul (aP F n i) (aP F n j) 1 1
      (κP_comm_aP F n i) (κP_comm_aP F n j)
    have h2 := κP_comm_mul (aP F n j) (aP F n i) 1 1
      (κP_comm_aP F n j) (κP_comm_aP F n i)
    have h2' : κP F n * (-(aP F n j * aP F n i))
        = gsign 1 (1 + 1) • (-(aP F n j * aP F n i) * κP F n) := by
      rw [mul_neg, h2, neg_mul, smul_neg]
    have h3 := κP_comm_add _ _ (1 + 1) h1 h2'
    have e : (1 + 1 : ZMod 2) = 0 := by decide
    rw [e, ← sub_eq_add_neg] at h3
    exact h3
  | .inr (.inr (u, i)) =>
    change κP F n * F0P F n u i = gsign 1 1 • (F0P F n u i * κP F n)
    unfold F0P
    refine κP_comm_smul _ _ 1 ?_
    have h1 := κP_comm_mul (aP F n i) (BP F n u) 1 0
      (κP_comm_aP F n i) (κP_comm_BP F n u)
    have h2 := κP_comm_mul (BP F n u) (aP F n i) 0 1
      (κP_comm_BP F n u) (κP_comm_aP F n i)
    simpa using κP_comm_add _ _ 1 h1 h2

theorem coefP_comm_mul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : AZero F n)
    (hx : coefP F n c * x = x * coefP F n c) (hy : coefP F n c * y = y * coefP F n c) :
    coefP F n c * (x * y) = (x * y) * coefP F n c := by
  rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]

theorem coefP_comm_add {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x y : AZero F n)
    (hx : coefP F n c * x = x * coefP F n c) (hy : coefP F n c * y = y * coefP F n c) :
    coefP F n c * (x + y) = (x + y) * coefP F n c := by
  rw [mul_add, hx, hy, add_mul]

theorem coefP_comm_neg {F : FermionIndex} {n : ℕ} (c : Pmn F n) (x : AZero F n)
    (hx : coefP F n c * x = x * coefP F n c) :
    coefP F n c * (-x) = (-x) * coefP F n c := by
  rw [mul_neg, hx, neg_mul]

theorem coefP_comm_smul {F : FermionIndex} {n : ℕ} (c : Pmn F n) (r : ℚ) (x : AZero F n)
    (hx : coefP F n c * x = x * coefP F n c) :
    coefP F n c * (r • x) = (r • x) * coefP F n c := by
  rw [mul_smul_comm, hx, smul_mul_assoc]

/-- `coefP` commutes plainly with every `X0`-built element -- the `coefP` analogue of
`κP_comm_X0`, without any sign bookkeeping (a coefficient's own degree is always
`0`). -/
theorem coefP_comm_X0 (F : FermionIndex) (n : ℕ) (c : Pmn F n) (X : OspBasis F n) :
    coefP F n c * X0P F n X = X0P F n X * coefP F n c := by
  match X with
  | .inl ⟨(u, v), _⟩ =>
    change coefP F n c * L0P F n u v = L0P F n u v * coefP F n c
    unfold L0P
    exact coefP_comm_smul c _ _
      (coefP_comm_add c _ _
        (coefP_comm_mul c _ _ (coefP_comm_BP F n c u) (coefP_comm_BP F n c v))
        (coefP_comm_mul c _ _ (coefP_comm_BP F n c v) (coefP_comm_BP F n c u)))
  | .inr (.inl ⟨(i, j), _⟩) =>
    change coefP F n c * S0P F n i j = S0P F n i j * coefP F n c
    unfold S0P
    refine coefP_comm_smul c _ _ ?_
    rw [sub_eq_add_neg]
    exact coefP_comm_add c _ _
      (coefP_comm_mul c _ _ (coefP_comm_aP F n c i) (coefP_comm_aP F n c j))
      (coefP_comm_neg c _
        (coefP_comm_mul c _ _ (coefP_comm_aP F n c j) (coefP_comm_aP F n c i)))
  | .inr (.inr (u, i)) =>
    change coefP F n c * F0P F n u i = F0P F n u i * coefP F n c
    unfold F0P
    exact coefP_comm_smul c _ _
      (coefP_comm_add c _ _
        (coefP_comm_mul c _ _ (coefP_comm_aP F n c i) (coefP_comm_BP F n c u))
        (coefP_comm_mul c _ _ (coefP_comm_BP F n c u) (coefP_comm_aP F n c i)))

/-- `κP`'s graded commutation, lifted from `X0`-built elements (`κP_comm_X0`) to
`iota0` of an arbitrary *OspN.parity-homogeneous* `OspMod` element -- one whose only nonzero
basis-components sit at a single fixed OspN.parity `p`, the generality `hTildeBasis X`
(OspN.parity `OspN.parity X + 1`, `hTildeBasis_apply_eq_zero_of_parity_ne`) needs. -/
theorem κP_comm_iota0_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → OspN.parity Z = p) :
    κP F n * iota0P F n x = gsign 1 p • (iota0P F n x * κP F n) := by
  have hterm : ∀ i : OspBasis F n,
      κP F n * (coefP F n (x i) * X0P F n i)
        = gsign 1 p • (coefP F n (x i) * X0P F n i * κP F n) := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi, coefP_zero]
    · have hpi : OspN.parity i = p := hx i hxi
      calc κP F n * (coefP F n (x i) * X0P F n i)
          = κP F n * coefP F n (x i) * X0P F n i := by rw [mul_assoc]
        _ = coefP F n (x i) * κP F n * X0P F n i := by rw [κP_comm_coefP]
        _ = coefP F n (x i) * (κP F n * X0P F n i) := by rw [mul_assoc]
        _ = coefP F n (x i) * (gsign 1 (OspN.parity i) • (X0P F n i * κP F n)) := by
              rw [κP_comm_X0]
        _ = coefP F n (x i) * (gsign 1 p • (X0P F n i * κP F n)) := by rw [hpi]
        _ = gsign 1 p • (coefP F n (x i) * (X0P F n i * κP F n)) := by rw [mul_smul_comm]
        _ = gsign 1 p • (coefP F n (x i) * X0P F n i * κP F n) := by rw [mul_assoc]
  change κP F n * (∑ i : OspBasis F n, coefP F n (x i) * X0P F n i)
      = gsign 1 p • ((∑ i : OspBasis F n, coefP F n (x i) * X0P F n i) * κP F n)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

theorem gsign_shift_left (p q : ZMod 2) : gsign (p + 1) q = gsign p q * gsign 1 q := by
  rw [gsign_symm (p + 1) q, gsign_shift_right q p, gsign_symm q p, gsign_symm q 1]

/-- `base_realization`, linearized on the right: `bracket0 x (eN Y)` against a
OspN.parity-`p`-homogeneous `x`, pushed through `iota0`. Reduces to `base_realization` termwise
via `bracket0_eN_right` and `iota0`'s own `Pmn`-linearity, moving `coefP` across `X0P F n Y`
with `coefP_comm_X0`. -/
theorem iota0_bracket0_eN_right_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (x : OspMod F n)
    (hx : ∀ Z : OspBasis F n, x Z ≠ 0 → OspN.parity Z = p) (Y : OspBasis F n) :
    iota0P F n (bracket0 x (eN Y))
      = iota0P F n x * X0P F n Y - gsign p (OspN.parity Y) • (X0P F n Y * iota0P F n x) := by
  rw [bracket0_eN_right, iota0P_sum]
  have hterm : ∀ i : OspBasis F n, iota0P F n (x i • bracket0Basis i Y)
      = coefP F n (x i) * X0P F n i * X0P F n Y
        - gsign p (OspN.parity Y) • (X0P F n Y * (coefP F n (x i) * X0P F n i)) := by
    intro i
    by_cases hxi : x i = 0
    · simp [hxi, coefP_zero, iota0_zero]
    · have hpi : OspN.parity i = p := hx i hxi
      have hbr := base_realization F n i Y
      unfold scomm at hbr
      rw [iota0P_smul_coefP, ← hbr, hpi, mul_sub, mul_smul_comm, ← mul_assoc,
        show coefP F n (x i) * (X0P F n Y * X0P F n i) = X0P F n Y * (coefP F n (x i) * X0P F n i)
          from by rw [← mul_assoc, coefP_comm_X0, mul_assoc]]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_mul]; rfl
  · have : (∑ i : OspBasis F n, X0P F n Y * (coefP F n (x i) * X0P F n i))
        = X0P F n Y * iota0P F n x := by rw [← Finset.mul_sum]; rfl
    rw [← Finset.smul_sum, this]

/-- Mirror of `iota0_bracket0_eN_right_homog`, with the basis vector on the left. -/
theorem iota0_bracket0_eN_left_homog {F : FermionIndex} {n : ℕ} (p : ZMod 2) (y : OspMod F n)
    (hy : ∀ Z : OspBasis F n, y Z ≠ 0 → OspN.parity Z = p) (X : OspBasis F n) :
    iota0P F n (bracket0 (eN X) y)
      = X0P F n X * iota0P F n y - gsign (OspN.parity X) p • (iota0P F n y * X0P F n X) := by
  rw [bracket0_eN_left, iota0P_sum]
  have hterm : ∀ j : OspBasis F n, iota0P F n (y j • bracket0Basis X j)
      = X0P F n X * (coefP F n (y j) * X0P F n j)
        - gsign (OspN.parity X) p • (coefP F n (y j) * X0P F n j * X0P F n X) := by
    intro j
    by_cases hyj : y j = 0
    · simp [hyj, coefP_zero, iota0_zero]
    · have hpj : OspN.parity j = p := hy j hyj
      have hbr := base_realization F n X j
      unfold scomm at hbr
      rw [iota0P_smul_coefP, ← hbr, hpj, mul_sub, mul_smul_comm,
        show coefP F n (y j) * (X0P F n X * X0P F n j) = X0P F n X * (coefP F n (y j) * X0P F n j)
          from by rw [← mul_assoc, coefP_comm_X0, mul_assoc],
        ← mul_assoc (coefP F n (y j)) (X0P F n j) (X0P F n X)]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.mul_sum]; rfl
  · have : (∑ j : OspBasis F n, coefP F n (y j) * X0P F n j * X0P F n X)
        = iota0P F n y * X0P F n X := by rw [← Finset.sum_mul]; rfl
    rw [← Finset.smul_sum, this]

/-- The pure-algebra identity underlying both cross-products in `recovery`'s expansion of
`scomm` on `Xhat X = X0 X + κ·(...)`: given `κ` graded-commutes with `P` at sign `α` and
with `p` at sign `σ` (both self-inverse, as every `gsign` value is) and `κ² = 0`, the
`(κp)(κq)` term vanishes and `P(κq)` picks up the sign `α` moving `κ` to the front. -/
theorem expand_kappa_product {F : FermionIndex} {n : ℕ} (P Q p q : AZero F n) (α σ : ℚ)
    (hP : κP F n * P = α • (P * κP F n))
    (hp : κP F n * p = σ • (p * κP F n))
    (hα : α * α = 1) (hσ : σ * σ = 1) :
    (P + κP F n * p) * (Q + κP F n * q)
      = P * Q + κP F n * (α • (P * q) + p * Q) := by
  have hPκ : P * κP F n = α • (κP F n * P) := by rw [hP, smul_smul, hα, one_smul]
  have hpκ : p * κP F n = σ • (κP F n * p) := by rw [hp, smul_smul, hσ, one_smul]
  have hκ2 : κP F n * κP F n = 0 := κP_sq F n
  have expand : (P + κP F n * p) * (Q + κP F n * q)
      = P * Q + P * (κP F n * q) + (κP F n * p) * Q
        + (κP F n * p) * (κP F n * q) := by noncomm_ring
  have h1 : P * (κP F n * q) = α • (κP F n * (P * q)) := by
    rw [← mul_assoc, hPκ, smul_mul_assoc, mul_assoc]
  have h2 : (κP F n * p) * Q = κP F n * (p * Q) := by rw [mul_assoc]
  have h3 : (κP F n * p) * (κP F n * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p, hpκ, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
      hκ2, zero_mul, zero_mul, smul_zero]
  rw [expand, h1, h2, h3, add_zero, ← mul_smul_comm, add_assoc, ← mul_add]

/-- **The recovery computation** (paper Theorem 4.2): for all basis elements
`X Y`, the supercommutator of the *deformed* lifts equals `ι_β` of the undeformed bracket
plus `κ·ι₀` of the explicit `Γ` rule. Proved by expanding `Xhat X = X0 X + κ·ι₀(h̃X)`
(`XhatP_eq`) on both sides of `scomm` (`expand_kappa_product`, twice), reducing
the base term to `base_realization`, and matching the `κ`-coefficient against
`GammaBasis = deltaBasis hTilde` (`Gamma_eq_delta_hTilde_basis`) via the linearized
`base_realization` (`iota0_bracket0_eN_*_homog`) and the `gsign` shift identities. -/
theorem scomm_XhatP (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (XhatP F n X) (XhatP F n Y)
      = iotaBP F n (bracket0Basis X Y) + κP F n * iota0P F n (GammaBasis X Y) := by
  have hXeq : XhatP F n X = X0P F n X + κP F n * iota0P F n (hTildeBasis X) := by
    rw [XhatP_eq, iota0_eN, hTilde_eN]
  have hYeq : XhatP F n Y = X0P F n Y + κP F n * iota0P F n (hTildeBasis Y) := by
    rw [XhatP_eq, iota0_eN, hTilde_eN]
  have hXhom : ∀ Z : OspBasis F n, hTildeBasis X Z ≠ 0 → OspN.parity Z = OspN.parity X + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTildeBasis_apply_eq_zero_of_parity_ne X Z hne)
  have hYhom : ∀ Z : OspBasis F n, hTildeBasis Y Z ≠ 0 → OspN.parity Z = OspN.parity Y + 1 :=
    fun Z hZ => by
      by_contra hne; exact hZ (hTildeBasis_apply_eq_zero_of_parity_ne Y Z hne)
  set A := X0P F n X
  set B := X0P F n Y
  set a := iota0P F n (hTildeBasis X) with ha
  set b := iota0P F n (hTildeBasis Y) with hb
  have hκA : κP F n * A = gsign 1 (OspN.parity X) • (A * κP F n) := κP_comm_X0 F n X
  have hκB : κP F n * B = gsign 1 (OspN.parity Y) • (B * κP F n) := κP_comm_X0 F n Y
  have hκa : κP F n * a = gsign 1 (OspN.parity X + 1) • (a * κP F n) :=
    κP_comm_iota0_homog (OspN.parity X + 1) (hTildeBasis X) hXhom
  have hκb : κP F n * b = gsign 1 (OspN.parity Y + 1) • (b * κP F n) :=
    κP_comm_iota0_homog (OspN.parity Y + 1) (hTildeBasis Y) hYhom
  have hprod1 : (A + κP F n * a) * (B + κP F n * b)
      = A * B + κP F n * (gsign 1 (OspN.parity X) • (A * b) + a * B) :=
    expand_kappa_product A B a b (gsign 1 (OspN.parity X)) (gsign 1 (OspN.parity X + 1)) hκA hκa
      (gsign_sq 1 (OspN.parity X)) (gsign_sq 1 (OspN.parity X + 1))
  have hprod2 : (B + κP F n * b) * (A + κP F n * a)
      = B * A + κP F n * (gsign 1 (OspN.parity Y) • (B * a) + b * A) :=
    expand_kappa_product B A b a (gsign 1 (OspN.parity Y)) (gsign 1 (OspN.parity Y + 1)) hκB hκb
      (gsign_sq 1 (OspN.parity Y)) (gsign_sq 1 (OspN.parity Y + 1))
  have hbase : A * B - gsign (OspN.parity X) (OspN.parity Y) • (B * A)
      = iota0P F n (bracket0Basis X Y) := by
    have := base_realization F n X Y
    unfold scomm at this
    exact this
  have hΓ : iota0P F n (hTilde (bracket0Basis X Y)) + iota0P F n (GammaBasis X Y)
      = iota0P F n (bracket0 (hTildeBasis X) (eN Y))
        + gsign (OspN.parity X) 1 • iota0P F n (bracket0 (eN X) (hTildeBasis Y)) := by
    rw [Gamma_eq_delta_hTilde_basis]
    unfold deltaBasis
    simp only [hTilde_eN]
    rw [bracket0_eN_eN, iota0_sub, iota0_add, iota0_smul_rat]
    abel
  have hRHSa : iota0P F n (bracket0 (hTildeBasis X) (eN Y))
      = a * B - gsign (OspN.parity X + 1) (OspN.parity Y) • (B * a) :=
    iota0_bracket0_eN_right_homog (OspN.parity X + 1) (hTildeBasis X) hXhom Y
  have hRHSb : iota0P F n (bracket0 (eN X) (hTildeBasis Y))
      = A * b - gsign (OspN.parity X) (OspN.parity Y + 1) • (b * A) :=
    iota0_bracket0_eN_left_homog (OspN.parity Y + 1) (hTildeBasis Y) hYhom X
  have e1 : gsign (OspN.parity X) (OspN.parity Y) * gsign 1 (OspN.parity Y)
      = gsign (OspN.parity X + 1) (OspN.parity Y) :=
    (gsign_shift_left (OspN.parity X) (OspN.parity Y)).symm
  have e2 : gsign (OspN.parity X) 1 * gsign (OspN.parity X) (OspN.parity Y + 1)
      = gsign (OspN.parity X) (OspN.parity Y) := by
    rw [gsign_mul_shift_right (OspN.parity Y) (OspN.parity X),
      gsign_symm (OspN.parity Y) (OspN.parity X)]
  have e3 : gsign 1 (OspN.parity X) = gsign (OspN.parity X) 1 := gsign_symm 1 (OspN.parity X)
  have hkey : gsign 1 (OspN.parity X) • (A * b) + a * B
      - gsign (OspN.parity X) (OspN.parity Y) • (gsign 1 (OspN.parity Y) • (B * a) + b * A)
      = iota0P F n (hTilde (bracket0Basis X Y)) + iota0P F n (GammaBasis X Y) := by
    rw [hΓ, hRHSa, hRHSb]
    simp only [smul_sub, smul_add, smul_smul, e1, e2, e3]
    module
  unfold scomm
  rw [hXeq, hYeq, hprod1, hprod2]
  unfold iotaBP
  have hregroup : A * B + κP F n * (gsign 1 (OspN.parity X) • (A * b) + a * B)
        - gsign (OspN.parity X) (OspN.parity Y) • (B * A
          + κP F n * (gsign 1 (OspN.parity Y) • (B * a) + b * A))
      = (A * B - gsign (OspN.parity X) (OspN.parity Y) • (B * A))
        + (κP F n * (gsign 1 (OspN.parity X) • (A * b) + a * B)
          - κP F n * (gsign (OspN.parity X) (OspN.parity Y)
            • (gsign 1 (OspN.parity Y) • (B * a) + b * A)))
      := by
    rw [smul_add,
      show gsign (OspN.parity X) (OspN.parity Y)
            • (κP F n * (gsign 1 (OspN.parity Y) • (B * a) + b * A))
          = κP F n * (gsign (OspN.parity X) (OspN.parity Y)
              • (gsign 1 (OspN.parity Y) • (B * a) + b * A))
        from (mul_smul_comm _ _ _).symm]
    abel
  rw [hregroup, ← mul_sub, hbase, hkey, mul_add]
  abel

/-- `recovery` with `GammaBasis` replaced by `deltaBasis hTilde`
via `Gamma_eq_delta_hTilde_basis`. -/
theorem scomm_XhatP_delta (F : FermionIndex) (n : ℕ) (X Y : OspBasis F n) :
    scomm X Y (XhatP F n X) (XhatP F n Y)
      = iotaBP F n (bracket0Basis X Y) + κP F n * iota0P F n (deltaBasis hTilde X Y) := by
  rw [← Gamma_eq_delta_hTilde_basis]
  exact scomm_XhatP F n X Y

/-! ## In `A_β` -/

section beta

variable (F : FermionIndex) (n : ℕ)

/-- `κ` in `A_β`. -/
noncomputable abbrev κB : ABeta F n := κ _ _ (beta F n)

theorem iotaP_sub (β' : I n → F.K → Pmn F n) (x y : OspMod F n) :
    iotaP β' (x - y) = iotaP β' x - iotaP β' y := by
  simp only [iotaP, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem untwist_rat_smul (q : ℚ) (x : ABeta F n) : untwist F n (q • x) = q • untwist F n x := by
  rw [← algebraMap_smul (Pmn F n) q x, map_smul, algebraMap_smul]

theorem untwist_scomm (X Y : OspBasis F n) (x y : ABeta F n) :
    untwist F n (scomm X Y x y) = scomm X Y (untwist F n x) (untwist F n y) := by
  simp only [scomm, map_sub, map_mul, untwist_rat_smul]

theorem untwist_κB : untwist F n (κB F n) = κP F n := untwist_κ F n

/-- **Thm 4.2 (Recovery)**, in the presented `A_β`: for basis elements `X`, `Y`,
`[ι_β X, ι_β Y] = ι_β([X,Y]_0) + κ ι_β(Γ_β(X,Y))`; no `1` or `κ·1` term occurs. -/
theorem recovery (X Y : OspBasis F n) :
    scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y)
      = iotaP (beta F n) (bracket0Basis X Y) + κB F n * iotaP (beta F n) (GammaBasis X Y) := by
  apply (untwist F n).injective
  rw [untwist_scomm, untwist_Xp, untwist_Xp, scomm_XhatP, map_add, map_mul, untwist_κB,
    untwist_iotaP, untwist_iotaP, mul_add, ← mul_assoc, κP_sq, zero_mul, add_zero]
  rfl

/-- **Thm 4.2**, with `Γ_β = δh̃`. -/
theorem recovery_delta (X Y : OspBasis F n) :
    scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y)
      = iotaP (beta F n) (bracket0Basis X Y)
        + κB F n * iotaP (beta F n) (deltaBasis hTilde X Y) := by
  rw [← Gamma_eq_delta_hTilde_basis]; exact recovery F n X Y

theorem κB_mul_iotaP_injective {x y : OspMod F n}
    (h : κB F n * iotaP (beta F n) x = κB F n * iotaP (beta F n) y) : x = y := by
  have h' := congrArg (untwist F n) h
  simp only [map_mul, untwist_κB, untwist_iotaP, mul_add, ← mul_assoc, κP_sq, zero_mul,
    add_zero] at h'
  apply κ_mul_iotaP_injective
  rw [iotaP_zero, iotaP_zero]
  exact h'

/-- **Thm 4.3 (Uniqueness)**, in the presented `A_β`. -/
theorem recovery_unique (X Y : OspBasis F n) (c' : OspMod F n)
    (h : scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y)
      = iotaP (beta F n) (bracket0Basis X Y) + κB F n * iotaP (beta F n) c') :
    c' = GammaBasis X Y := by
  rw [recovery, add_right_inj] at h
  exact (κB_mul_iotaP_injective F n h).symm

/-- `ι_β` is injective on `𝔤_R` (Section 4.1, "The deformed bracket"). -/
theorem iotaRP_beta_injective : Function.Injective (iotaRP (F := F) (n := n) (beta F n)) := by
  intro x y h
  unfold iotaRP at h
  have hκ := congrArg (fun z => κB F n * z) h
  simp only [mul_add, ← mul_assoc, κ_mul_κ, zero_mul, add_zero] at hκ
  have h0 : falsePart x = falsePart y := κB_mul_iotaP_injective F n hκ
  rw [h0, add_right_inj] at h
  have h1 : truePart x = truePart y := κB_mul_iotaP_injective F n h
  funext ⟨i, b⟩
  cases b
  · exact congrFun h0 i
  · exact congrFun h1 i

/-- `[X,Y]_0 + κ Γ_β(X,Y) ∈ 𝔤_R`. -/
noncomputable def bracketBetaBasis (X Y : OspBasis F n) : RMod F n :=
  iotaR (bracket0Basis X Y) + kappaEmbed (GammaBasis X Y)

theorem iotaRP_bracketBetaBasis (X Y : OspBasis F n) :
    iotaRP (beta F n) (bracketBetaBasis F n X Y)
      = scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y) := by
  have hf : falsePart (bracketBetaBasis F n X Y) = bracket0Basis X Y := by
    funext Z; simp [bracketBetaBasis, falsePart, iotaR, kappaEmbed]
  have ht : truePart (bracketBetaBasis F n X Y) = GammaBasis X Y := by
    funext Z; simp [bracketBetaBasis, truePart, iotaR, kappaEmbed]
  rw [recovery, iotaRP, hf, ht]

/-- **The deformed bracket** (Section 4.1): the supercommutator of two lifts in `A_β` is `ι_β` of a
unique element of `𝔤_R`, `[X,Y]_β`, and `[X,Y]_β = [X,Y]_0 + κ Γ_β(X,Y)`. -/
theorem bracketBeta_unique (X Y : OspBasis F n) :
    (∃! z : RMod F n, iotaRP (beta F n) z = scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y)) ∧
    iotaRP (beta F n) (bracketBetaBasis F n X Y)
      = scomm X Y (Xp (beta F n) X) (Xp (beta F n) Y) :=
  ⟨⟨bracketBetaBasis F n X Y, iotaRP_bracketBetaBasis F n X Y,
    fun _ hz => iotaRP_beta_injective F n (hz.trans (iotaRP_bracketBetaBasis F n X Y).symm)⟩,
   iotaRP_bracketBetaBasis F n X Y⟩

end beta

end Presented
end OspN
end OspOddDeformations
